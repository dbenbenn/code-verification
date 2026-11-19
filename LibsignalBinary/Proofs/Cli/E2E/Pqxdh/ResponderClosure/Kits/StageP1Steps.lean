/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrustAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Stage P1 Layouts, Stack Helpers, and Segment Lemmas

Defines Stage P1 stack budgets, the coroutine `SessionRecord` slot `p1LoadedRecordAt` (`coroPtr +
0xe0..0x250`), condition and alignment helpers, and straight-line `SepWP` segment lemmas for
`load_session` (`Some(r)` copy) and `is_trusted_identity` post-poll teardown.
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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Stack budget for Stage P1 Part A (`load_session` shim + poll + `futDrop` + `__rust_dealloc`). -/
@[expose] def loadCallStack {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) : Nat :=
  max kit.loadShimStack (max kit.loadPollStack allocHookStack)

/-- Combined callee stack budget for full Stage P1 (`load_session` followed by
`is_trusted_identity`). -/
@[expose] def stageP1CallStack {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max (loadCallStack kit) (trustCallStack ikit)

/-- Callee stack budget for the untrusted error exit (`+0x06e4 -> ret`), covering both
`<String as Clone>::clone` (`extHookStack`), `drop_in_place::<SessionStructure>`
(`dropSessionStructureLocal2Stack`), and `__rust_dealloc` (`allocHookStack`). -/
@[expose] def untrustedErrCallStack : Nat :=
  max extHookStack (max dropSessionStructureLocal2Stack allocHookStack)

/-- Combined callee stack budget for Stage P1 including the untrusted identity exit path. -/
@[expose] def stageP1UntrustedCallStack {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max (stageP1CallStack kit ikit) untrustedErrCallStack

/-- Coroutine `SessionRecord` slot at `coroPtr + 0xe0..0x250` (368 bytes = 32-byte header +
336-byte body, `0xe0 + 0x170 = 0x250`) after Stage P1 Part A (`load_session`):
- `none`: initialized empty `SessionRecord` header `sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64)`
  plus untouched tail `memRegion (coroPtr + 0x100#64) 336` (fresh-session Path A).
- `some r`: loaded `SessionRecord r` satisfying `Scope r`, moved into `coroPtr + 0xe0#64` as
  `sessionRecordAt A (coroPtr + 0xe0#64) g r` via `+0x04cc..+0x04f8` + `+0x059c` (matched-session
  Path B). -/
@[expose] def p1LoadedRecordAt (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (coroPtr : BitVec 64) :
    Option (SessionRecord (List (BitVec 8))) → SepProp
  | none =>
    sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
    memRegion (coroPtr + 0x100#64) 336
  | some r =>
    ⌜Scope r⌝ ∗ ∃∗ g : RecordGhost, sessionRecordAt A (coroPtr + 0xe0#64) g r

/-! ## 2. Stack, Alignment, Repack, and Condition Helpers -/

theorem stackAt_split_of_le (sp : BitVec 64) (big small : Nat)
    (hle : small ≤ big) (hbig : big ≤ 2 ^ 64) :
    stackAt sp big =
      memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

/-- Proves that `sp0 - 0xcd0#64` preserves 16-byte stack alignment (`0xcd0 = 16 * 205`). -/
theorem sp_sub_cd0_align_std3 {sp0 : BitVec 64} (h : (sp0 &&& 15#64 == 0#64) = true) :
    ((sp0 - 0xcd0#64) &&& 15#64 == 0#64) = true :=
  spAligned_sub sp0 0xcd0#64 h (by decide)

theorem cond_ne_adds64_of_ne_neg3_std3 {w : BitVec 64} (h : w ≠ 0xfffffffffffffffd#64) :
    ConditionHolds CondCode.NE (addsPState64 w 3#64) = true := by
  have hne : w + 3#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_ne_addsPState64]
  exact bne_iff_ne.mpr hne

theorem cond_ne_adds64_of_ne_neg2_std3 {w : BitVec 64} (h : w ≠ 0xfffffffffffffffe#64) :
    ConditionHolds CondCode.NE (addsPState64 w 2#64) = true := by
  have hne : w + 2#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_ne_addsPState64]
  exact bne_iff_ne.mpr hne

theorem cond_eq_adds64_of_ne_neg1_std3 {w : BitVec 64} (h : w ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 w 1#64) = false := by
  have hne : w + 1#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_eq_addsPState64]
  exact beq_eq_false_iff_ne.mpr hne

/-- Split 5 words `p + 0x10 .. p + 0x38` into `(p + 0x10) ↦₃₂`, four `↦₆₄` at `+0x14..+0x34`,
and `(p + 0x34) ↦₃₂` matching `wp_steps` quadword loads/stores. -/
theorem words5_repack_sp3e0 (sp w2 w3 w4 w5 w6 : BitVec 64) :
    ((sp + 0x3f0#64) ↦₆₄ w2) ∗ ((sp + 0x3f8#64) ↦₆₄ w3) ∗ ((sp + 0x400#64) ↦₆₄ w4) ∗
        ((sp + 0x408#64) ↦₆₄ w5) ∗ ((sp + 0x410#64) ↦₆₄ w6) =
      ((sp + 0x3f0#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp + 0x3f4#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((sp + 0x3fc#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((sp + 0x404#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((sp + 0x40c#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
        ((sp + 0x414#64) ↦₃₂ w6.extractLsb' 32 32) := by
  have h := out_repack (sp + 0x3e8#64) w2 w3 w4 w5 w6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

/-- Inverse repack at `coroPtr + 0xe0`: reassemble 5 words `coroPtr + 0xf0 .. coroPtr + 0x118`
from `(coroPtr + 0xf0) ↦₃₂`, four `↦₆₄` at `+0xf4..+0x114`, and `(coroPtr + 0x114) ↦₃₂`. -/
theorem words5_unpack_coro_e0 (coroPtr w2 w3 w4 w5 w6 : BitVec 64) :
    ((coroPtr + 0xf0#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((coroPtr + 0xf4#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((coroPtr + 0xfc#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((coroPtr + 0x104#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((coroPtr + 0x10c#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
        ((coroPtr + 0x114#64) ↦₃₂ w6.extractLsb' 32 32) =
      ((coroPtr + 0xf0#64) ↦₆₄ w2) ∗ ((coroPtr + 0xf8#64) ↦₆₄ w3) ∗
        ((coroPtr + 0x100#64) ↦₆₄ w4) ∗ ((coroPtr + 0x108#64) ↦₆₄ w5) ∗
        ((coroPtr + 0x110#64) ↦₆₄ w6) := by
  have h := out_repack (coroPtr + 0xe8#64) w2 w3 w4 w5 w6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h.symm

/-- Decompose the 336-byte uninitialized slot `coroPtr + 0x100..0x250` into 3 words at
`+0x100..+0x118` and `memRegion (coroPtr + 0x118#64) 312` for `p1_load_some_seg4_wp`. -/
theorem coro_body336_split (coroPtr : BitVec 64) :
    cells (coroPtr + 0xe0#64) 4 ∗ memRegion (coroPtr + 0x100#64) 336 ⊢
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64,
        ((coroPtr + 0xe0#64) ↦₆₄ c0) ∗
        ((coroPtr + 0xe8#64) ↦₆₄ c1) ∗
        ((coroPtr + 0xf0#64) ↦₃₂ c2.extractLsb' 0 32) ∗
        ((coroPtr + 0xf4#64) ↦₆₄ (c3.extractLsb' 0 32 ++ c2.extractLsb' 32 32)) ∗
        ((coroPtr + 0xfc#64) ↦₆₄ (c4.extractLsb' 0 32 ++ c3.extractLsb' 32 32)) ∗
        ((coroPtr + 0x104#64) ↦₆₄ (c5.extractLsb' 0 32 ++ c4.extractLsb' 32 32)) ∗
        ((coroPtr + 0x10c#64) ↦₆₄ (c6.extractLsb' 0 32 ++ c5.extractLsb' 32 32)) ∗
        ((coroPtr + 0x114#64) ↦₃₂ c6.extractLsb' 32 32) ∗
        memRegion (coroPtr + 0x118#64) 312 := by
  rw [ProofLib.memRegion_split (coroPtr + 0x100#64) 8 328 (by decide),
      ProofLib.memRegion_split (coroPtr + 0x100#64 + 8#64) 8 320 (by decide),
      ProofLib.memRegion_split (coroPtr + 0x100#64 + 8#64 + 8#64) 8 312 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  dsimp only [cells]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro c6
  apply Entails.sepExists_elim; intro c5
  apply Entails.sepExists_elim; intro c4
  apply Entails.sepExists_elim; intro c3
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro c0
  refine Entails.sepExists_right c3 (Entails.sepExists_right c2
    (Entails.sepExists_right c1 (Entails.sepExists_right c0
      (Entails.sepExists_right c4 (Entails.sepExists_right c5
        (Entails.sepExists_right c6 ?_))))))
  have hrep := (words5_unpack_coro_e0 coroPtr c1 c0 c4 c5 c6).symm
  refine Entails.of_eq ?_
  calc
    ((coroPtr + 224#64) ↦₆₄ c3) ∗ ((coroPtr + 232#64) ↦₆₄ c2) ∗
        ((coroPtr + 240#64) ↦₆₄ c1) ∗ ((coroPtr + 248#64) ↦₆₄ c0) ∗
        ((coroPtr + 256#64) ↦₆₄ c4) ∗ ((coroPtr + 264#64) ↦₆₄ c5) ∗
        ((coroPtr + 272#64) ↦₆₄ c6) ∗ memRegion (coroPtr + 280#64) 312
      = (((coroPtr + 240#64) ↦₆₄ c1) ∗ ((coroPtr + 248#64) ↦₆₄ c0) ∗
          ((coroPtr + 256#64) ↦₆₄ c4) ∗ ((coroPtr + 264#64) ↦₆₄ c5) ∗
          ((coroPtr + 272#64) ↦₆₄ c6)) ∗
        ((coroPtr + 224#64) ↦₆₄ c3) ∗ ((coroPtr + 232#64) ↦₆₄ c2) ∗
        memRegion (coroPtr + 280#64) 312 := by ac_rfl
    _ = _ := by rw [hrep]; ac_rfl

/-- Collapse `(sp + 0x210..0x234)` back into `memRegion (sp + 0x210#64) 36` and join with
`memRegion (sp + 0xd8#64) 312` into `memRegion (sp + 0xd8#64) 348`. -/
theorem sp_d8_348_rejoin (sp v0 v1 v2 v3 : BitVec 64) (dv4 : BitVec 32) :
    memRegion (sp + 0xd8#64) 312 ∗
      ((sp + 0x210#64) ↦₆₄ v0) ∗ ((sp + 0x218#64) ↦₆₄ v1) ∗
      ((sp + 0x220#64) ↦₆₄ v2) ∗ ((sp + 0x228#64) ↦₆₄ v3) ∗
      ((sp + 0x230#64) ↦₃₂ dv4) ⊢
      memRegion (sp + 0xd8#64) 348 := by
  have hmr : memRegion (sp + 0xd8#64) 348 =
      memRegion (sp + 0xd8#64) 312 ∗ memRegion (sp + 0x210#64) 36 :=
    ProofLib.memRegion_split' (b := sp + 0xd8#64) (n := 312) (k := 36)
      (b' := sp + 0x210#64) rfl (by bv_omega) (by decide)
  rw [hmr,
      ProofLib.memRegion_split (sp + 0x210#64) 8 28 (by decide),
      ProofLib.memRegion_split (sp + 0x210#64 + 8#64) 8 20 (by decide),
      ProofLib.memRegion_split (sp + 0x210#64 + 8#64 + 8#64) 8 12 (by decide),
      ProofLib.memRegion_split (sp + 0x210#64 + 8#64 + 8#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (pointsTo32_entails_memRegion _ _)))))

/-- Unpack the 39 uninspected trailing bytes of `trustPollOutAt` (`Ok(t)`) at `sp + 0x3e9..0x410`
into the subword cells read by `p1_seg6a_any_wp`. -/
theorem trustOut39_split_p1 (sp : BitVec 64) :
    memRegion (sp + 0x3e9#64) 39 ⊢
      ∃∗ d_3e9 : BitVec 32, ∃∗ h_3ed : BitVec 16, ∃∗ b_3ef : BitVec 8,
      ∃∗ w_3f0 : BitVec 64, ∃∗ d_3f8 : BitVec 32, ∃∗ d_3fc : BitVec 32,
      ∃∗ w_400 : BitVec 64, ∃∗ w_408 : BitVec 64,
        ((sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
        ((sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
        ((sp + 0x3ef#64) ↦₈ b_3ef) ∗
        ((sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
        ((sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
        ((sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
        ((sp + 0x400#64) ↦₆₄ w_400) ∗
        ((sp + 0x408#64) ↦₆₄ w_408) := by
  rw [ProofLib.memRegion_split (sp + 0x3e9#64) 4 35 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64) 2 33 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64 + 2#64) 1 32 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64 + 2#64 + 1#64) 8 24 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64 + 2#64 + 1#64 + 8#64) 4 20 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64 + 2#64 + 1#64 + 8#64 + 4#64) 4 16 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64 + 2#64 + 1#64 + 8#64 + 4#64 + 4#64) 8 8
        (by decide),
      ProofLib.memRegion_four, ProofLib.memRegion_two, ProofLib.memRegion_one,
      ProofLib.memRegion_eight, ProofLib.memRegion_four, ProofLib.memRegion_four,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w_408
  apply Entails.sepExists_elim; intro w_400
  apply Entails.sepExists_elim; intro d_3fc
  apply Entails.sepExists_elim; intro d_3f8
  apply Entails.sepExists_elim; intro w_3f0
  apply Entails.sepExists_elim; intro b_3ef
  apply Entails.sepExists_elim; intro h_3ed
  apply Entails.sepExists_elim; intro d_3e9
  exact Entails.sepExists_right d_3e9 (Entails.sepExists_right h_3ed
    (Entails.sepExists_right b_3ef (Entails.sepExists_right w_3f0
      (Entails.sepExists_right d_3f8 (Entails.sepExists_right d_3fc
        (Entails.sepExists_right w_400 (Entails.sepExists_right w_408 (Entails.refl _))))))))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
