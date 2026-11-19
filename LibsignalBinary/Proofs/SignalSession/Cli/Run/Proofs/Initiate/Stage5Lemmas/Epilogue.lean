/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKit -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Fetch

/-!
# Stage 5 Frame Reassembly, Shared Epilogue, and Error Cleanup

Stack-frame collapse (`collapse_initLocals`), shared epilogue (`stage5_epilogue_ok`,
`+0x0350..+0x037c → lr`), and `SessionState` + `pqspk` error unwind (`stage5_err_cleanup_ok`,
`+0x1858 → +0x0350 → lr`).
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688

/-! ## Stack Frame Reassembly and Shared Epilogue (`+0x0350..+0x037c → lr`) -/

theorem sret48_words6_split (out : BitVec 64) :
    memRegion out 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        (out ↦₆₄ w0) ∗ ((out + 0x08#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
        ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5)) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 40) (b' := out + 0x08#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x08#64) (n := 8) (k := 32) (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 24) (b' := out + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 16) (b' := out + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8) (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out,
      ProofLib.memRegion_eight (out + 0x08#64),
      ProofLib.memRegion_eight (out + 0x10#64),
      ProofLib.memRegion_eight (out + 0x18#64),
      ProofLib.memRegion_eight (out + 0x20#64),
      ProofLib.memRegion_eight (out + 0x28#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w4 =>
      Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 =>
      Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 => ?_
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4
        (Entails.sepExists_right w5 (Entails.of_eq (by ac_rfl)))))))
  · refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
      Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 =>
      Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 => ?_
    exact Entails.sepExists_right w5 (Entails.sepExists_right w4 (Entails.sepExists_right w3
      (Entails.sepExists_right w2 (Entails.sepExists_right w1
        (Entails.sepExists_right w0 (Entails.of_eq (by ac_rfl)))))))

theorem ok_words6_to_initResAt (A : RustAlloc) (out : BitVec 64)
    (w1 w2 w3 w4 w5 : BitVec 64) :
    ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 0x08#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
      ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5)) ⊢
      initResAt A out (.ok ()) := by
  dsimp only [initResAt]
  refine sepConj_mono_right ?_
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (pointsTo64_entails_memRegion _ _))))) ?_
  rw [← ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8) (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 16) (b' := out + 0x20#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 24) (b' := out + 0x18#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x08#64) (n := 8) (k := 32) (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem initSaved_entails_memRegion (s0 : State) :
    initSaved s0 ⊢ memRegion (s0.sp - 0x60#64) 0x60 := by
  dsimp only [initSaved]
  let b := s0.sp - 0x60#64
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
  rw [← ProofLib.memRegion_split' (b := b + 0x50#64) (n := 8) (k := 8) (b' := b + 0x58#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := b + 0x48#64) (n := 8) (k := 16) (b' := b + 0x50#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := b + 0x40#64) (n := 8) (k := 24) (b' := b + 0x48#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := b + 0x38#64) (n := 8) (k := 32) (b' := b + 0x40#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := b + 0x30#64) (n := 8) (k := 40) (b' := b + 0x38#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := b + 0x28#64) (n := 8) (k := 48) (b' := b + 0x30#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := b + 0x20#64) (n := 8) (k := 56) (b' := b + 0x28#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := b + 0x18#64) (n := 8) (k := 64) (b' := b + 0x20#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := b + 0x10#64) (n := 8) (k := 72) (b' := b + 0x18#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := b + 0x08#64) (n := 8) (k := 80) (b' := b + 0x10#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := b + 0x00#64) (n := 8) (k := 88) (b' := b + 0x08#64) rfl (by bv_omega) (by decide),
      show b + 0x00#64 = s0.sp - 0x60#64 by dsimp only [b]; bv_omega]
  exact Entails.refl _

theorem reassemble_stackAt_full {B : RunBudgets} {stk : Nat} (s0 : State)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    memRegion fsp initLocalsSize ∗ initSaved s0 ∗ stackAt fsp (stk - cliInitiateFrame) ⊢
      stackAt s0.sp stk := by
  intro fsp
  have hge := stk_ge_frame hstk
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (initSaved_entails_memRegion s0))) ?_
  rw [← sepConj_assoc,
      ← ProofLib.memRegion_split' (b := fsp) (n := initLocalsSize) (k := 0x60)
          (b' := s0.sp - 0x60#64) initLocalsSize_add_saved
          (by dsimp only [fsp, cliInitiateFrame, initLocalsSize]; bv_omega) (by decide)]
  dsimp only [stackAt]
  have hb : fsp - BitVec.ofNat 64 (stk - cliInitiateFrame) = s0.sp - BitVec.ofNat 64 stk := by
    dsimp only [fsp]
    have hsplit : BitVec.ofNat 64 stk =
        BitVec.ofNat 64 cliInitiateFrame + BitVec.ofNat 64 (stk - cliInitiateFrame) := by
      rw [← BitVec.ofNat_add, Nat.add_sub_cancel' hge]
    rw [hsplit]
    bv_omega
  rw [hb, sepConj_comm,
      ← ProofLib.memRegion_split'
          (b := s0.sp - BitVec.ofNat 64 stk)
          (n := stk - cliInitiateFrame) (k := cliInitiateFrame)
          (b' := fsp) (Nat.sub_add_cancel hge).symm
          (by dsimp only [fsp]
              have hsplit : BitVec.ofNat 64 stk =
                  BitVec.ofNat 64 cliInitiateFrame + BitVec.ofNat 64 (stk - cliInitiateFrame) := by
                rw [← BitVec.ofNat_add, Nat.add_sub_cancel' hge]
              rw [hsplit]; bv_omega)
          (by omega)]
  exact Entails.refl _

/-- Named optional-OPK slot inside `stage3KeySlotsAt` so `s5_frame` matches by constant head
rather than per-declaration `match_1` auxiliaries. -/
@[expose] def stage3OpkSlotAt (fsp : BitVec 64) (b : BundleV) : SepProp :=
  match b.opk with
  | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
  | none => memRegion (fsp + 0x439#64) 32

theorem stage3KeySlotsAt_unfold (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
    (pqspkPtr : BitVec 64) (opkId : BitVec 32) :
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId =
      (((fsp + 0x298#64) ↦ₛ ekAPk) ∗
        memRegion (fsp + 0x2b8#64) 0x48 ∗
        ((fsp + 0x300#64) ↦₃₂ (if b.opk.isSome then 1#32 else 0#32)) ∗
        ((fsp + 0x304#64) ↦₃₂ opkId) ∗
        memRegion (fsp + 0x308#64) 0x40 ∗
        ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
        ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
        ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
        ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
        ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗
        ((fsp + 0x438#64) ↦₈ (if b.opk.isSome then 1#32 else 0#32).truncate 8) ∗
        stage3OpkSlotAt fsp b ∗
        ((fsp + 0x459#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x45a#64) 6) := by
  dsimp only [stage3KeySlotsAt, stage3OpkSlotAt]
  rcases b.opk with _ | ⟨_, _⟩ <;> rfl

section EpilogueBlock

private theorem sp_epilogue_add1 (a : BitVec 64) : (a - 7408#64) + 4096#64 = a - 3312#64 := by
  bv_omega
private theorem sp_epilogue_add2 (a : BitVec 64) : (a - 3312#64) + 3216#64 = a - 96#64 := by
  bv_omega
private theorem sp_epilogue_add3 (a : BitVec 64) : (a - 96#64) + 96#64 = a := by
  bv_omega
attribute [local arm64_norm, local wp_norm] sp_epilogue_add1 sp_epilogue_add2 sp_epilogue_add3

end EpilogueBlock

/-! ## Error Cleanup (`+0x1858 → +0x0350 → lr`) -/

theorem state_exists_setMem (st : State) : ∃ m, st = st.setMem m :=
  ⟨st.mem, by cases st; rfl⟩

@[scoped arm64_norm, scoped wp_norm]
theorem state_trace_setMem (s : State) (m : Memory) : (s.setMem m).trace = s.trace := rfl

@[scoped arm64_norm, scoped wp_norm]
theorem state_fs_setMem (s : State) (m : Memory) : (s.setMem m).fs = s.fs := rfl

@[scoped arm64_norm, scoped wp_norm]
theorem calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl

elab "s5_step_done_post" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]))
  let g ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
  let isSetMem := match g.getAppArgs with
    | #[ex, _] => match ex.getAppArgs with
      | #[_, .lam _ _ eq _] => match eq.getAppArgs with
        | #[_, lhs, _] => lhs.consumeMData.isAppOfArity ``State.setMem 2
        | _ => false
      | _ => false
    | _ => false
  if isSetMem then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ⟨⟨_, rfl⟩, rfl⟩))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ⟨state_exists_setMem _, rfl⟩))

macro "s5_step_done" : tactic =>
  `(tactic| (apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); s5_step_done_post))

macro "s5_step_done_pc" pcTac:Lean.Parser.Tactic.tacticSeq : tactic =>
  `(tactic| (apply SepWP.done (by $pcTac) (by wp_norm_lhs); s5_step_done_post))

theorem layoutOk_1568_1 : LayoutOk 1568 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
theorem layoutOk_32_8 : LayoutOk 32 8 := ⟨by decide, ⟨3, rfl⟩, by decide⟩
theorem layoutOk_16_8 : LayoutOk 16 8 := ⟨by decide, ⟨3, rfl⟩, by decide⟩

theorem opk8_truncate_eq (b : Bool) :
    (if b = true then (1#8 : BitVec 8) else 0#8) =
      (if b = true then (1#32 : BitVec 32) else 0#32).truncate 8 := by
  cases b <;> rfl

@[local arm64_norm, local wp_norm]
theorem fsp_err_eqs (sp0 : BitVec 64) :
    let fsp := sp0 - BitVec.ofNat 64 cliInitiateFrame
    fsp + 1465#64 = fsp + 0x5b9#64 ∧
    fsp + 128#64 = fsp + 0x80#64 ∧
    fsp + 1072#64 = fsp + 0x430#64 ∧
    fsp + 1064#64 = fsp + 0x428#64 ∧
    fsp + 320#64 = fsp + 0x140#64 ∧
    fsp + 304#64 = fsp + 0x130#64 ∧
    fsp + 0x130#64 + 8#64 = fsp + 0x138#64 ∧
    fsp + 296#64 = fsp + 0x128#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
