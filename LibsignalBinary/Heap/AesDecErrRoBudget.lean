/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
import ProofLib.Hoare.SubroutineOk
import ProofLib.SepLogic.Region

/-!
# Concrete `.rodata` Error-String Strengthening of `aesDecBudgetSpec` (`AesDecErrRoBudget`)

Untrusted sibling contract `aesDecBudgetSpecErrRo` / `cliAesDecBudgetSpecErrRo` for
`signal_crypto::aes_cbc::aes_256_cbc_decrypt` that strengthens the `.none` error return layout of
`aesDecBudgetSpec` (`LibsignalBinary.Heap.SpecBudget`) from an arbitrary non-null pointer + raw
`memRegion (x.ret + 16#64) 8` to the exact two `.rodata` `&'static str` `(ptr, len)` pairs emitted
by the linked `libsignal-session` binary:
- `(0x414561#64, 0x33#64)` (`"ciphertext length must be a non-zero multiple of 16"`, 51 B), or
- `(0x414550#64, 0x11#64)` (`"failed to decrypt"`, 17 B),

so FI-1 (`DecryptTailTrap{507,}PlacedBudget`) can discharge `<&str as Display>::fmt` inside
`alloc::fmt::format::format_inner` (`cliFormatInnerCallSpec`) without modifying `aesDecBudgetSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap.AesDecErrRoBudget

open Arm64 ProofLib SepProp ProofLib.SepLogic
open CryptoGames.CBC (AesKey Block bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (AesDecEnv aesCallPreBudget aesDecBudgetSpec aesDecFnBudgetSpec aesDecWeakBudgetSpec)

/-- Concrete `.rodata` address of `"ciphertext length must be a non-zero multiple of 16"` (51 B)
    in `cliElfImage`. -/
def cliAesDecErrStr1Addr : BitVec 64 := 0x4148b1#64

/-- Concrete `.rodata` address of `"failed to decrypt"` (17 B) in `cliElfImage`. -/
def cliAesDecErrStr2Addr : BitVec 64 := 0x4148a0#64

theorem cliAesDecErrStr1Addr_ne_zero : cliAesDecErrStr1Addr ≠ 0#64 := by decide

theorem cliAesDecErrStr2Addr_ne_zero : cliAesDecErrStr2Addr ≠ 0#64 := by decide

/-- Strengthened budget-threaded contract for `signal_crypto::aes_cbc::aes_256_cbc_decrypt`
    exposing the exact `.rodata` `&'static str` `(ptr, len)` pair written to `[x.ret + 8 .. x.ret + 24)`
    on `none`. Precondition, `onPanic`, `onExit`, and `onOom` are definitionally (`rfl`) equal to
    `aesDecBudgetSpec`. -/
def aesDecBudgetSpecErrRo (D : AesKey → Block → Block)
    (errStr1Addr errStr2Addr : BitVec 64)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := fun (x, st) s => aesCallPreBudget M A lim AesDecEnv x st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AesDecEnv x evs⌝ ∗ x.frame ∗
      (match aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
       | some pt => vecU8 A.repAlloc x.ret pt
       | none => (x.ret ↦₆₄ errTag) ∗
           (∃∗ p : BitVec 64, ∃∗ len : BitVec 64,
             ⌜(p = errStr1Addr ∧ len = 0x33#64) ∨ (p = errStr2Addr ∧ len = 0x11#64)⌝ ∗
             ((x.ret + 8#64) ↦₆₄ p) ∗ ((x.ret + 16#64) ↦₆₄ len))) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

/-- Specialization of `aesDecBudgetSpecErrRo` at the `cliElfImage` `.rodata` addresses
    `cliAesDecErrStr1Addr = 0x414561#64` and `cliAesDecErrStr2Addr = 0x414550#64`. -/
abbrev cliAesDecBudgetSpecErrRo (D : AesKey → Block → Block)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) :=
  aesDecBudgetSpecErrRo D cliAesDecErrStr1Addr cliAesDecErrStr2Addr M A lim

/-- Pack a concrete `(errPtr, errLen)` 24-byte `Err` layout into the disjunction of
    `aesDecBudgetSpecErrRo`. -/
theorem errResultErrRo_pack (ret errStr1Addr errStr2Addr p len : BitVec 64)
    (h : (p = errStr1Addr ∧ len = 0x33#64) ∨ (p = errStr2Addr ∧ len = 0x11#64)) :
    (ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ p) ∗ ((ret + 16#64) ↦₆₄ len) ⊢
      (ret ↦₆₄ errTag) ∗
        (∃∗ q : BitVec 64, ∃∗ l : BitVec 64,
          ⌜(q = errStr1Addr ∧ l = 0x33#64) ∨ (q = errStr2Addr ∧ l = 0x11#64)⌝ ∗
          ((ret + 8#64) ↦₆₄ q) ∗ ((ret + 16#64) ↦₆₄ l)) :=
  sepConj_mono_right
    (Entails.sepExists_right p
      (Entails.sepExists_right len (Entails.pure_right h (Entails.refl _))))

/-- Forget the `.rodata` `(ptr, len)` witness back to `aesDecBudgetSpec`'s `.none` postcondition
    when both `.rodata` string addresses are non-null. -/
theorem aesErrRo_entails_aesErr (ret : BitVec 64)
    {errStr1Addr errStr2Addr : BitVec 64}
    (h1 : errStr1Addr ≠ 0#64) (h2 : errStr2Addr ≠ 0#64) :
    (ret ↦₆₄ errTag) ∗
      (∃∗ p : BitVec 64, ∃∗ len : BitVec 64,
        ⌜(p = errStr1Addr ∧ len = 0x33#64) ∨ (p = errStr2Addr ∧ len = 0x11#64)⌝ ∗
        ((ret + 8#64) ↦₆₄ p) ∗ ((ret + 16#64) ↦₆₄ len)) ⊢
    (ret ↦₆₄ errTag) ∗
      (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((ret + 8#64) ↦₆₄ p)) ∗ memRegion (ret + 16#64) 8 := by
  refine sepConj_mono_right ?_
  refine Entails.sepExists_elim fun p => Entails.sepExists_elim fun len =>
    Entails.pure_left fun hdisj => ?_
  have hp_ne : p ≠ 0 := by
    rcases hdisj with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h1
    · exact h2
  have hp_ex : ((ret + 8#64) ↦₆₄ p) ⊢ ∃∗ q : BitVec 64, ⌜q ≠ 0⌝ ∗ ((ret + 8#64) ↦₆₄ q) :=
    Entails.sepExists_right p (Entails.pure_right hp_ne (Entails.refl _))
  have hm8 : ((ret + 16#64) ↦₆₄ len) ⊢ memRegion (ret + 16#64) 8 := by
    rw [memRegion_eight (ret + 16#64)]
    exact @Entails.sepExists_intro (BitVec 64) (fun q => (ret + 16#64) ↦₆₄ q) len
  exact sepConj_mono hp_ex hm8

theorem aesDecBudgetSpecErrRo_post_entails_aesDecBudgetSpec_post
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    (h1 : errStr1Addr ≠ 0#64) (h2 : errStr2Addr ≠ 0#64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (p : AesCall × M.σ) (s0 sf : State) :
    (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim).post p s0 sf ⊢
      (aesDecBudgetSpec D M A lim).post p s0 sf := by
  rcases p with ⟨x, st⟩
  dsimp only [aesDecBudgetSpecErrRo, aesDecBudgetSpec]
  refine Entails.sepExists_elim fun evs => ?_
  refine Entails.trans ?_ (@Entails.sepExists_intro (List AllocEvent) _ evs)
  cases aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
  | none =>
    exact sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (aesErrRo_entails_aesErr x.ret h1 h2)))
  | some _ =>
    exact Entails.refl _

theorem subroutine_ok_aesDecBudgetSpec_of_errRo
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    (h1 : errStr1Addr ≠ 0#64) (h2 : errStr2Addr ≠ 0#64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim)) :
    subroutine_ok P entry (aesDecBudgetSpec D M A lim) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun p R s0 sf hq =>
    Satisfies.mono
      (sepConj_mono_left (aesDecBudgetSpecErrRo_post_entails_aesDecBudgetSpec_post h1 h2 p s0 sf))
      hq)

theorem hookOk_aesDecBudgetSpec_of_errRo
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    (h1 : errStr1Addr ≠ 0#64) (h2 : errStr2Addr ≠ 0#64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {f : State → State}
    (hok : HookOk f (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim)) :
    HookOk f (aesDecBudgetSpec D M A lim) :=
  HookOk.mono hok (fun _ _ _ hp => hp)
    (fun p R s0 sf _ hq =>
      Satisfies.mono
        (sepConj_mono_left
          (aesDecBudgetSpecErrRo_post_entails_aesDecBudgetSpec_post h1 h2 p s0 sf))
        hq)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he)

theorem hookOk_aesDecBudgetSpec_of_cliErrRo
    {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {f : State → State}
    (hok : HookOk f (cliAesDecBudgetSpecErrRo D M A lim)) :
    HookOk f (aesDecBudgetSpec D M A lim) :=
  hookOk_aesDecBudgetSpec_of_errRo cliAesDecErrStr1Addr_ne_zero cliAesDecErrStr2Addr_ne_zero hok

theorem hookSat_aesDecBudgetSpec_of_errRo
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    (h1 : errStr1Addr ≠ 0#64) (h2 : errStr2Addr ≠ 0#64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {sym : String}
    (hsat : HookSat hooks sym (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim)) :
    HookSat hooks sym (aesDecBudgetSpec D M A lim) := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_aesDecBudgetSpec_of_errRo h1 h2 hok⟩

theorem hookSat_aesDecBudgetSpec_of_cliErrRo
    {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {sym : String}
    (hsat : HookSat hooks sym (cliAesDecBudgetSpecErrRo D M A lim)) :
    HookSat hooks sym (aesDecBudgetSpec D M A lim) :=
  hookSat_aesDecBudgetSpec_of_errRo cliAesDecErrStr1Addr_ne_zero cliAesDecErrStr2Addr_ne_zero hsat

end LibsignalBinary.Heap.AesDecErrRoBudget
