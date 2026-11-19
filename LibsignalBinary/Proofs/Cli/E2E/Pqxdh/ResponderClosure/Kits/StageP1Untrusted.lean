/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1DropSS3A -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Ok
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrustAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Stage P1 Untrusted-Identity Exit on Store Kits

Proves the `is_trusted_identity == Ok(false)` (TOFU mismatch) arm of Stage P1:
`stageP1_untrusted_err_ok_kit` (`entry + 0x6e4#64 → s0.readReg64 .x30`, cloning `peer`, building
`UntrustedIdentityException`, and dropping `p1LoadedRecordAt`) and full entry-to-return
`stageP1_untrusted_ok_kit`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 1. Stack Split & Region Folding Helpers -/

theorem stack_untrustedErr_to_ext (sp : BitVec 64) (hn : untrustedErrCallStack ≤ 2 ^ 64) :
    stackAt sp untrustedErrCallStack =
      memRegion (sp - BitVec.ofNat 64 untrustedErrCallStack)
        (untrustedErrCallStack - extHookStack) ∗
        stackAt sp extHookStack :=
  stackAt_split_of_le sp untrustedErrCallStack extHookStack (Nat.le_max_left _ _) hn

theorem stack_untrustedErr_to_dropSS (sp : BitVec 64) (hn : untrustedErrCallStack ≤ 2 ^ 64) :
    stackAt sp untrustedErrCallStack =
      memRegion (sp - BitVec.ofNat 64 untrustedErrCallStack)
        (untrustedErrCallStack - dropSessionStructureLocal2Stack) ∗
        stackAt sp dropSessionStructureLocal2Stack :=
  stackAt_split_of_le sp untrustedErrCallStack dropSessionStructureLocal2Stack
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn

theorem stack_untrustedErr_to_alloc (sp : BitVec 64) (hn : untrustedErrCallStack ≤ 2 ^ 64) :
    stackAt sp untrustedErrCallStack =
      memRegion (sp - BitVec.ofNat 64 untrustedErrCallStack)
        (untrustedErrCallStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_of_le sp untrustedErrCallStack allocHookStack
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn

theorem stack_stageP1Untrusted_to_p1 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) (sp : BitVec 64)
    (hn : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP1UntrustedCallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP1UntrustedCallStack kit ikit))
        (stageP1UntrustedCallStack kit ikit - stageP1CallStack kit ikit) ∗
        stackAt sp (stageP1CallStack kit ikit) :=
  stackAt_split_of_le sp (stageP1UntrustedCallStack kit ikit) (stageP1CallStack kit ikit)
    (Nat.le_max_left _ _) hn

theorem stack_stageP1Untrusted_to_err {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) (sp : BitVec 64)
    (hn : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP1UntrustedCallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP1UntrustedCallStack kit ikit))
        (stageP1UntrustedCallStack kit ikit - untrustedErrCallStack) ∗
        stackAt sp untrustedErrCallStack :=
  stackAt_split_of_le sp (stageP1UntrustedCallStack kit ikit) untrustedErrCallStack
    (Nat.le_max_right _ _) hn

theorem stringClone_pre_intro {A : RustAlloc} {s : State} {addrA ret : BitVec 64} {g : VecGhost}
    (hx0 : s.readReg64 .x0 = addrA) (hx8 : s.readReg64 .x8 = ret) :
    vecGhostAt A g addrA ∗ memRegion ret 24 ∗ A.pool ∗ stackAt s.sp extHookStack ⊢
      (stringCloneSpec A).pre (addrA, ret, g) s := by
  dsimp only [stringCloneSpec]
  exact Entails.pure_right ⟨hx0, hx8⟩ (Entails.refl _)

theorem cells6_eq (base : BitVec 64) :
    cells base 6 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        (base ↦₆₄ u0) ∗ ((base + 8#64) ↦₆₄ u1) ∗ ((base + 16#64) ↦₆₄ u2) ∗
        ((base + 24#64) ↦₆₄ u3) ∗ ((base + 32#64) ↦₆₄ u4) ∗ ((base + 40#64) ↦₆₄ u5) := by
  dsimp only [cells]
  sep_norm

theorem cells6_fold (base w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ∗
      ((base + 24#64) ↦₆₄ w3) ∗ ((base + 32#64) ↦₆₄ w4) ∗ ((base + 40#64) ↦₆₄ w5) ⊢
      cells base 6 := by
  rw [cells6_eq base]
  exact Entails.sepExists_right w0
    (Entails.sepExists_right w1
      (Entails.sepExists_right w2
        (Entails.sepExists_right w3
          (Entails.sepExists_right w4
            (Entails.sepExists_right w5 (Entails.refl _))))))

theorem sp_a90_rejoin (sp w0 cap ptr len devWord u5 : BitVec 64) :
    ((sp + 0xa90#64) ↦₆₄ w0) ∗
      ((sp + 0xa98#64) ↦₃₂ cap.extractLsb' 0 32) ∗
      ((sp + 0xa9c#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
      ((sp + 0xaa4#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
      ((sp + 0xaac#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
      ((sp + 0xab4#64) ↦₆₄ (u5.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
      ((sp + 0xabc#64) ↦₃₂ u5.extractLsb' 32 32) ⊢
      cells (sp + 0xa90#64) 6 := by
  have h40 := (realign_40 (sp + 0xa98#64) cap ptr len devWord u5).symm
  repeat (simp only [BitVec.add_assoc] at h40); repeat (simp only [BitVec.reduceAdd] at h40)
  have h6 := cells6_fold (sp + 0xa90#64) w0 cap ptr len devWord u5
  repeat (simp only [BitVec.add_assoc] at h6); repeat (simp only [BitVec.reduceAdd] at h6)
  rw [h40]
  exact h6

theorem sp_370_rejoin (sp w0 w1 w2 w3 : BitVec 64) (d4 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ w0) ∗ ((sp + 0x378#64) ↦₆₄ w1) ∗
      ((sp + 0x380#64) ↦₆₄ w2) ∗ ((sp + 0x388#64) ↦₆₄ w3) ∗
      ((sp + 0x390#64) ↦₃₂ d4) ⊢
      memRegion (sp + 0x370#64) 36 := by
  rw [sp370_36_split_eq sp]
  exact Entails.sepExists_right d4
    (Entails.sepExists_right w3
      (Entails.sepExists_right w2
        (Entails.sepExists_right w1
          (Entails.sepExists_right w0 (Entails.refl _)))))

theorem coro_e0_368_fold (coroPtr w0 w1 w2 : BitVec 64) :
    ((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ w2) ∗
      memRegion (coroPtr + 0xf8#64) 344 ⊢
      memRegion (coroPtr + 0xe0#64) 368 := by
  rw [ProofLib.memRegion_split (coroPtr + 0xe0#64) 8 360 (by decide),
      ProofLib.memRegion_split (coroPtr + 0xe0#64 + 8#64) 8 352 (by decide),
      ProofLib.memRegion_split (coroPtr + 0xe0#64 + 8#64 + 8#64) 8 344 (by decide)]
  sep_norm
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))

theorem prevVecAt_unpack (A : RustAlloc) (coroPtr prevCap prevPtr : BitVec 64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (coroPtr + 0xe0#64) prevCap prevPtr [] ⊢
      ⌜prevCap.toNat * 24 < 2 ^ 63⌝ ∗
      ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (if prevCap = 0 then emp
       else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) := by
  dsimp only [vecAt, vecHeader, vecBuf, arrayAt, List.length, Nat.zero_mul, Nat.sub_zero]
  simp only [Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  sep_norm
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm ((coroPtr + 232#64) ↦₆₄ prevPtr),
      sepConj_pure_left_comm ((coroPtr + 224#64) ↦₆₄ prevCap)]
  apply Entails.pure_left; rintro ⟨_, hlt, _⟩
  exact Entails.pure_right hlt (Entails.refl _)

theorem pure_vecGhost_sep_split {A : RustAlloc} {φ : Prop} {g : VecGhost}
    {base : BitVec 64} {tail : SepProp} :
    ∃ R_ss : SepProp,
      (⌜φ⌝ ∗ (vecGhostAt A g base ∗ tail) ⊢
        ⌜g.cap.toNat < 2 ^ 63⌝ ∗ (base ↦₆₄ g.cap) ∗ R_ss) ∧
      ((base ↦₆₄ g.cap) ∗ R_ss ⊢
        ⌜φ⌝ ∗ (vecGhostAt A g base ∗ tail)) := by
  rw [DropSS3.vecGhostAt_eq_srkRest A g base]
  refine ⟨⌜φ⌝ ∗ ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
    DropSS3.srkRest A base g ∗ tail, ?_, ?_⟩
  · apply Entails.pure_left; intro hφ
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hg
    rw [sepConj_assoc]
    exact Entails.pure_right hg.2.1
      (sepConj_mono_right (Entails.pure_right hφ (Entails.pure_right hg (Entails.refl _))))
  · rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hφ
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hg
    rw [← sepConj_assoc]
    exact Entails.pure_right hφ
      (sepConj_mono_left (Entails.pure_right hg (Entails.refl _)))

/-! ## 2. Unified `SessionRecord` Drop (`+0x3588 -> +0x359c`) & Return Epilogue (`+0x359c -> ret`) -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
