/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 Framing, OOM Panic Handlers, and Stack Collapse Helpers

Provides isolated basic-block and `__rust_dealloc` combinators (`s3_block_in`, `s3_block_to_call`,
`s3_dealloc`), OOM panic handlers (`+0x1918`, `+0x1930`, `+0x193c`), stack-region collapse lemmas,
and `CliExternsOk` counterparts (`Ext.*`) for Stage 3 of `initiate`.
-/

public section
set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000
namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `SepWPp` framing, sequencing, and OOM trace helpers -/

theorem sepWPp_frame_oom {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hw : SepWPp prog ret s P
      (fun sf Pf => Q sf (Pf ∗ F))
      (fun sf Pf => Qp sf (Pf ∗ F))
      (initOom s0)) :
    SepWPp prog ret s (P ∗ F) Q Qp (initOom s0) := fun R hm hL => by
  have hm' : s.mem ⊨ P ∗ (F ∗ R) := by rwa [sepConj_assoc] at hm
  obtain ⟨sf, hsteps,
      ⟨hpc, hrun, Pf, hm_f, hq⟩ | ⟨hpan, Pf, hm_f, hqp⟩ | ⟨hoom, hm_oom⟩⟩ :=
    hw (F ∗ R) hm' hL
  · rw [← sepConj_assoc] at hm_f
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf ∗ F, hm_f, hq⟩⟩
  · rw [← sepConj_assoc] at hm_f
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, Pf ∗ F, hm_f, hqp⟩)⟩
  · dsimp only [initOom] at hm_oom
    rw [satisfies_pure_sepConj] at hm_oom
    exact hm_oom.1.elim

theorem sepWP_bind_oom {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp Qoom)) :
    SepWPp prog ret s P Q Qp Qoom := fun R hm hL => by
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨_, hf⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem allocFailedIn_of_append {s0 s : State}
    (h : s.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 s := by
  simp [allocFailedIn, h]

theorem memRegion_merge_at (b : BitVec 64) (n k : Nat) (b' : BitVec 64)
    (hb : b' = b + BitVec.ofNat 64 n) (hnk : n + k ≤ 2 ^ 64) :
    memRegion b n ∗ memRegion b' k = memRegion b (n + k) := by
  rw [hb, ← memRegion_split b n k hnk]

theorem pointsTo8_entails_memRegion1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ⊢ memRegion a 1 :=
  pointsTo8_entails_memRegion a b

theorem pointsToBytes_entails_memRegion_len {a : BitVec 64} {bs : List (BitVec 8)} {n : Nat}
    (hlen : bs.length = n) :
    (a ↦ₛ bs) ⊢ memRegion a n :=
  hlen ▸ pointsToBytes_entails_memRegion a bs

theorem sret_err_speOwned (A : RustAlloc) (peer : AddrVal) (ret : BitVec 64)
    (w1 w2 w3 w4 w5 : BitVec 64) :
    (ret ↦₆₄ speWord 10) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
      ((ret + 24#64) ↦₆₄ w3) ∗ ((ret + 32#64) ↦₆₄ w4) ∗ ((ret + 40#64) ↦₆₄ w5) ⊢
      initResAt A ret (.error (.untrustedIdentity peer)) := by
  have h5 :
      ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
        ((ret + 24#64) ↦₆₄ w3) ∗ ((ret + 32#64) ↦₆₄ w4) ∗ ((ret + 40#64) ↦₆₄ w5) ⊢
        memRegion (ret + 8#64) 40 := by
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ w1)
        (sepConj_mono (pointsTo64_entails_memRegion _ w2)
          (sepConj_mono (pointsTo64_entails_memRegion _ w3)
            (sepConj_mono (pointsTo64_entails_memRegion _ w4)
              (pointsTo64_entails_memRegion _ w5))))) ?_
    rw [memRegion_merge_at (ret + 32#64) 8 8 (ret + 40#64) (by bv_omega) (by decide),
      memRegion_merge_at (ret + 24#64) 8 16 (ret + 32#64) (by bv_omega) (by decide),
      memRegion_merge_at (ret + 16#64) 8 24 (ret + 24#64) (by bv_omega) (by decide),
      memRegion_merge_at (ret + 8#64) 8 32 (ret + 16#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right h5) ?_
  dsimp only [initResAt]
  exact Entails.sepExists_right (RunDrop.SpeOwned.plain 10 (by decide)) (Entails.refl _)

theorem initSaved_entails_memRegion96 (s0 : State) :
    initSaved s0 ⊢ memRegion (s0.sp - 0x60#64) 0x60 := by
  let b := s0.sp - 0x60#64
  dsimp only [initSaved]
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (sepConj_mono (pointsTo64_entails_memRegion _ _)
                          (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  rw [memRegion_merge_at (b + 0x50#64) 8 8 (b + 0x58#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x48#64) 8 16 (b + 0x50#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x40#64) 8 24 (b + 0x48#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x38#64) 8 32 (b + 0x40#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x30#64) 8 40 (b + 0x38#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x28#64) 8 48 (b + 0x30#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x20#64) 8 56 (b + 0x28#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x18#64) 8 64 (b + 0x20#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x10#64) 8 72 (b + 0x18#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x08#64) 8 80 (b + 0x10#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x00#64) 8 88 (b + 0x08#64) (by bv_omega) (by decide)]
  simpa only [BitVec.add_zero] using (Entails.refl (memRegion (b + 0x00#64) 96))

theorem initFreshRecAt_collapse (fsp : BitVec 64) :
    initFreshRecAt fsp ⊢ memRegion (fsp + 0x128#64) 0x20 := by
  dsimp only [initFreshRecAt]
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _)))) ?_
  rw [memRegion_merge_at (fsp + 0x138#64) 8 8 (fsp + 0x140#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x130#64) 8 16 (fsp + 0x138#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x128#64) 8 24 (fsp + 0x130#64) (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stage3KeySlotsAt_collapse (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
    (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (hekPk : ekAPk.length = 32) (hekSk : ekASk.length = 32) (hkpk : b.kpk.length = 1568) :
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId ⊢
      memRegion (fsp + 0x298#64) 0x190 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
        memRegion (fsp + 0x438#64) 0x28 := by
  have hopk :
      (match b.opk with
       | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
       | none => memRegion (fsp + 0x439#64) 32) ⊢ memRegion (fsp + 0x439#64) 32 := by
    cases b.opk with
    | none => exact Entails.refl _
    | some pk => exact pointsToBytes_entails_memRegion_len pk.2.bytes.toList_length
  dsimp only [stage3KeySlotsAt]
  refine Entails.trans
    (sepConj_mono (pointsToBytes_entails_memRegion_len hekPk)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsToBytes_entails_memRegion_len kp.identityKey.publicKey.bytes.toList_length)
    (sepConj_mono (pointsToBytes_entails_memRegion_len kp.privateKey.bytes.toList_length)
    (sepConj_mono (pointsToBytes_entails_memRegion_len hekPk)
    (sepConj_mono (pointsToBytes_entails_memRegion_len hekSk)
    (sepConj_mono (pointsToBytes_entails_memRegion_len b.idKey.publicKey.bytes.toList_length)
    (sepConj_mono (pointsToBytes_entails_memRegion_len b.spk.bytes.toList_length)
    (sepConj_mono (pointsToBytes_entails_memRegion_len b.spk.bytes.toList_length)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsToBytes_entails_memRegion_len hkpk)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ _)
    (sepConj_mono hopk
    (sepConj_mono (pointsTo8_entails_memRegion1 _ _)
      (Entails.refl _)))))))))))))))))))) ?_
  rw [memRegion_merge_at (fsp + 0x459#64) 1 6 (fsp + 0x45a#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x439#64) 32 7 (fsp + 0x459#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x438#64) 1 39 (fsp + 0x439#64) (by bv_omega) (by decide)]
  have hleft :
      memRegion (fsp + 0x298#64) 32 ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
        memRegion (fsp + 0x300#64) 4 ∗ memRegion (fsp + 0x304#64) 4 ∗
        memRegion (fsp + 0x308#64) 0x40 ∗ memRegion (fsp + 0x348#64) 32 ∗
        memRegion (fsp + 0x368#64) 32 ∗ memRegion (fsp + 0x388#64) 32 ∗
        memRegion (fsp + 0x3a8#64) 32 ∗ memRegion (fsp + 0x3c8#64) 32 ∗
        memRegion (fsp + 0x3e8#64) 32 ∗ memRegion (fsp + 0x408#64) 32 =
      memRegion (fsp + 0x298#64) 0x190 := by
    rw [memRegion_merge_at (fsp + 0x3e8#64) 32 32 (fsp + 0x408#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x3c8#64) 32 64 (fsp + 0x3e8#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x3a8#64) 32 96 (fsp + 0x3c8#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x388#64) 32 128 (fsp + 0x3a8#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x368#64) 32 160 (fsp + 0x388#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x348#64) 32 192 (fsp + 0x368#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x308#64) 0x40 224 (fsp + 0x348#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x304#64) 4 288 (fsp + 0x308#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x300#64) 4 292 (fsp + 0x304#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x2b8#64) 0x48 296 (fsp + 0x300#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x298#64) 32 368 (fsp + 0x2b8#64) (by bv_omega) (by decide)]
  rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
  exact Entails.of_eq (by rw [← hleft]; ac_rfl)

theorem stack_frame_reassemble {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) (s0 : State) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    memRegion fsp initLocalsSize ∗ memRegion (s0.sp - 0x60#64) 0x60 ∗
      stackAt fsp (stk - cliInitiateFrame) ⊢
      stackAt s0.sp stk := by
  dsimp only
  have hge : cliInitiateFrame ≤ stk := stk_ge_frame hstk
  have h1 :
      memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) initLocalsSize ∗
        memRegion (s0.sp - 0x60#64) 0x60 =
      memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) cliInitiateFrame := by
    rw [memRegion_merge_at (s0.sp - BitVec.ofNat 64 cliInitiateFrame) initLocalsSize 0x60
      (s0.sp - 0x60#64) (by dsimp only [cliInitiateFrame, initLocalsSize]; bv_omega) (by decide)]
  rw [← sepConj_assoc, h1, sepConj_comm]
  dsimp only [stackAt]
  have hbase :
      s0.sp - BitVec.ofNat 64 cliInitiateFrame - BitVec.ofNat 64 (stk - cliInitiateFrame) =
        s0.sp - BitVec.ofNat 64 stk := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add,
      show cliInitiateFrame + (stk - cliInitiateFrame) = stk from by omega]
  have hadd :
      s0.sp - BitVec.ofNat 64 cliInitiateFrame =
        (s0.sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 (stk - cliInitiateFrame) := by
    rw [← hbase, BitVec.sub_add_cancel]
  rw [hbase, memRegion_merge_at (s0.sp - BitVec.ofNat 64 stk) (stk - cliInitiateFrame)
    cliInitiateFrame (s0.sp - BitVec.ofNat 64 cliInitiateFrame) hadd (by omega),
    show stk - cliInitiateFrame + cliInitiateFrame = stk from by omega]
  exact Entails.refl _

/-! ## Extern-parameterized framing, block, and OOM helpers (`Ext.*`) -/

namespace Ext

end Ext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
