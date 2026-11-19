/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1DropSS3A -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Aux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsB
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Stage P2 Matched-Session Unpack Helpers and Shared Error-Return Record Teardown

Defines `prevSessionsEmptyAt` (`p1LoadedRecordAt` unpack and stack split helpers) and proves the
shared error-return record teardown `closure_err_drop_record_tail_ext_ok` (`+0x3588 → s0.readReg64 .x30`
for general `g.prevCap`) along with its `AllocContractsX` generalization.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp eq_of_sep_emp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.SignalSession

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `p1LoadedRecordAt` unpack and stack split helpers -/

/-- Empty `previous_sessions` `Vec` header + optional spare capacity buffer at `coroPtr + 0xe0#64`
extracted from `sessionRecordAt A (coroPtr + 0xe0#64) g r`. -/
@[expose] def prevSessionsEmptyAt (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) (coroPtr + 0xe0#64) g.prevCap g.prevPtr []

theorem sessionRecordAt_some_eq_prev_sess (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hcur : r.currentSession = some sess) :
    sessionRecordAt A (coroPtr + 0xe0#64) g r ⊢
      ∃∗ recG : SessionGhost,
        ⌜g.cur = some recG⌝ ∗
        prevSessionsEmptyAt A coroPtr g ∗
        sessionStateReprAt A (coroPtr + 0xf8#64) recG sess := by
  cases hgc : g.cur with
  | none =>
    simp only [sessionRecordAt, hgc, hcur]
    apply Entails.trans (Q := ⌜False⌝ ∗ prevSessionsEmptyAt A coroPtr g)
    · unfold prevSessionsEmptyAt
      exact Entails.of_eq (by ac_rfl)
    · exact Entails.pure_left fun hf => False.elim hf
  | some recG =>
    refine Entails.sepExists_right recG (Entails.pure_right rfl ?_)
    simp only [sessionRecordAt, hgc, hcur, prevSessionsEmptyAt,
      BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _

theorem prevSessionsEmptyAt_restore_record (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hgc : g.cur = some recG) (hcur : r.currentSession = some sess) :
    prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ⊢
      sessionRecordAt A (coroPtr + 0xe0#64) g r := by
  simp only [sessionRecordAt, hgc, hcur, prevSessionsEmptyAt,
    BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem prevSessionsEmptyAt_unpack (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost) :
    prevSessionsEmptyAt A coroPtr g ⊢
      ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝ ∗
      ((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (if g.prevCap = 0#64 then emp
       else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
         memRegion g.prevPtr (g.prevCap.toNat * 24)) := by
  unfold prevSessionsEmptyAt vecAt vecHeader vecBuf
  dsimp only [List.length_nil, Nat.zero_mul, Nat.sub_zero]
  change
    ((coroPtr + 0xe0#64) ↦₆₄ g.prevCap ∗
      ((coroPtr + 0xe0#64 + 8#64) ↦₆₄ g.prevPtr ∗
        (coroPtr + 0xe0#64 + 16#64) ↦₆₄ 0#64)) ∗
      (⌜0 ≤ g.prevCap.toNat ∧ g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝ ∗
        (if g.prevCap = 0#64 then emp
         else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
           arrayAt (fun (_ : Unit) _ => emp) 24 g.prevPtr [] ∗
           memRegion (g.prevPtr + 0#64) (g.prevCap.toNat * 24))) ⊢ _
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q :=
    ⌜0 ≤ g.prevCap.toNat ∧ g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝ ∗
    (((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗
     ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
     ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
     (if g.prevCap = 0#64 then emp
      else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
        arrayAt (fun (_ : Unit) _ => emp) 24 g.prevPtr [] ∗
        memRegion g.prevPtr (g.prevCap.toNat * 24)))) (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.pure_left fun ⟨_, hcap, hptr⟩ => Entails.pure_right ⟨hcap, hptr⟩ ?_
  by_cases hc : g.prevCap = 0#64
  · simp only [hc, ↓reduceIte]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte, arrayAt, emp_sepConj]
    exact Entails.refl _

theorem prevSessionsEmptyAt_zero (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost)
    (hzero : g.prevCap = 0#64) :
    prevSessionsEmptyAt A coroPtr g ⊢
      ⌜g.prevPtr ≠ 0#64⌝ ∗
      ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) := by
  refine Entails.trans (prevSessionsEmptyAt_unpack A coroPtr g) ?_
  simp only [hzero, ↓reduceIte, sepConj_emp]
  refine Entails.pure_left fun ⟨_, hptr⟩ => Entails.pure_right hptr (Entails.refl _)

theorem stack_root_to_promoteMatch (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - promoteMatchingSessionMatchStack) ∗
        stackAt sp promoteMatchingSessionMatchStack :=
  stackAt_split_of_le sp rootStack promoteMatchingSessionMatchStack (by decide) hn

theorem stack_root_to_alloc (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_of_le sp rootStack allocHookStack (by decide) hn

theorem stack_root_to_dropSS (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - dropSessionStructureLocal2Stack) ∗
        stackAt sp dropSessionStructureLocal2Stack :=
  stackAt_split_of_le sp rootStack dropSessionStructureLocal2Stack (by decide) hn

theorem stack_root_to_growOneSpe (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack :=
  stackAt_split_of_le sp rootStack growOneSpeStack (by decide) hn

theorem stack_dropSS_to_alloc (sp : BitVec 64) (hn : dropSessionStructureLocal2Stack ≤ 2 ^ 64) :
    stackAt sp dropSessionStructureLocal2Stack =
      memRegion (sp - BitVec.ofNat 64 dropSessionStructureLocal2Stack)
        (dropSessionStructureLocal2Stack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_of_le sp dropSessionStructureLocal2Stack allocHookStack (by decide) hn

/-! ## Shared error-return record teardown (`+0x3588 → s0.readReg64 .x30`) -/

theorem coro_e0_3w_344_entails_368 (coroPtr w0 w1 w2 : BitVec 64) :
    ((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
    ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
    ((coroPtr + 0xf0#64) ↦₆₄ w2) ∗
    memRegion (coroPtr + 0xf8#64) 344 ⊢
      memRegion (coroPtr + 0xe0#64) 368 := by
  have h24 :
      ((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ w2) ⊢
        memRegion (coroPtr + 0xe0#64) 24 := by
    rw [ProofLib.memRegion_split (coroPtr + 0xe0#64) 8 16 (by decide),
        ProofLib.memRegion_split (coroPtr + 0xe0#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  rw [ProofLib.memRegion_split (coroPtr + 0xe0#64) 24 344 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q :=
    (((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
     ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
     ((coroPtr + 0xf0#64) ↦₆₄ w2)) ∗
    memRegion (coroPtr + 0xf8#64) 344) (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono_left h24

theorem sp370_4w64_w32_entails_36 (sp w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ w0) ∗
    ((sp + 0x378#64) ↦₆₄ w1) ∗
    ((sp + 0x380#64) ↦₆₄ w2) ∗
    ((sp + 0x388#64) ↦₆₄ w3) ∗
    ((sp + 0x390#64) ↦₃₂ w4) ⊢
      memRegion (sp + 0x370#64) 36 := by
  rw [ProofLib.memRegion_split (sp + 0x370#64) 8 28 (by decide),
      ProofLib.memRegion_split (sp + 0x370#64 + 8#64) 8 20 (by decide),
      ProofLib.memRegion_split (sp + 0x370#64 + 8#64 + 8#64) 8 12 (by decide),
      ProofLib.memRegion_split (sp + 0x370#64 + 8#64 + 8#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo32_entails_memRegion _ _))))

private theorem cap_lt_2_63_ne_neg1 {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    c ≠ 0xffffffffffffffff#64 := by
  bv_omega

theorem sessionStateAt_split_localIk_cap (A : RustAlloc) (ss : BitVec 64)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8))) :
    ∃ R_ss : SepProp,
      (sessionStateAt A ss recG recSt ⊢
        ⌜recG.localIk.cap.toNat < 2 ^ 63⌝ ∗ (ss ↦₆₄ recG.localIk.cap) ∗ R_ss) ∧
      ((ss ↦₆₄ recG.localIk.cap) ∗ R_ss ⊢
        sessionStateAt A ss recG recSt) := by
  have hvg_lt : vecGhostRestAt A recG.localIk ss ⊢
      ⌜recG.localIk.cap.toNat < 2 ^ 63⌝ ∗ vecGhostRestAt A recG.localIk ss := by
    have heq : vecGhostRestAt A recG.localIk ss =
        ⌜recG.localIk.bytes.length ≤ recG.localIk.cap.toNat ∧
          recG.localIk.cap.toNat < 2 ^ 63 ∧ recG.localIk.ptr ≠ 0⌝ ∗
        (((ss + 8#64) ↦₆₄ recG.localIk.ptr) ∗
          ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
          (if recG.localIk.cap = 0 then emp
           else A.live recG.localIk.ptr recG.localIk.cap.toNat 1 ∗
             (recG.localIk.ptr ↦ₛ recG.localIk.bytes) ∗
             memRegion (recG.localIk.ptr + BitVec.ofNat 64 recG.localIk.bytes.length)
               (recG.localIk.cap.toNat - recG.localIk.bytes.length))) := by
      dsimp only [vecGhostRestAt]; ac_rfl
    rw [heq]
    exact Entails.pure_left fun hm =>
      Entails.pure_right hm.2.1 (Entails.pure_right hm (Entails.refl _))
  refine ⟨sessionStateRestAt A ss recG recSt, ?_,
    Entails.of_eq (sessionStateAt_expose_cap A ss recG recSt).symm⟩
  rw [sessionStateAt_expose_cap A ss recG recSt]
  unfold sessionStateRestAt
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvg_lt))) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Stack-parametric `dropSessionStructureLocal2Spec` (`stk = dropSessionStructureLocal2Stack`
equals `dropSessionStructureLocal2Spec A`; `stk = 48 + Getters.dropChainStackX` covers `AllocContractsX`). -/
@[expose] def dropSessionStructureLocal2SpecWithStack (stk : Nat) (A : RustAlloc) :
    Spec DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp stk

abbrev dropSessionStructureLocal2StackX : Nat := 48 + Getters.dropChainStackX

abbrev dropSessionStructureLocal2SpecX (A : RustAlloc) : Spec DropSessionStructureGhost :=
  dropSessionStructureLocal2SpecWithStack dropSessionStructureLocal2StackX A

theorem stack_root_to_dssWith (dssStack : Nat) (sp : BitVec 64)
    (hdss : dssStack ≤ rootStack) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - dssStack) ∗
        stackAt sp dssStack :=
  stackAt_split_of_le sp rootStack dssStack hdss hn

theorem stack_root_to_extHook_m2t (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - extHookStack) ∗
        stackAt sp extHookStack :=
  stackAt_split_of_le sp rootStack extHookStack (by decide) hn

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
