/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P2 Matched-Session Basic Blocks: Part B

`tripleRatchetProgAtExt b ext` basic-block lemmas `p2_matched_to_dealloc_wp` and
`p2_matched_to_remote_ik_wp`, plus `<str as ToOwned>::to_owned` contracts `strToOwnedLocal2Spec` and
`strToOwnedLocal2SpecWithStack`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Symbol name of `<str as alloc::borrow::ToOwned>::to_owned` called on the
remote-identity mismatch error path (`+0x130c`). -/
abbrev strToOwnedLocal2Name : String :=
  "<str as alloc::borrow::ToOwned>::to_owned"

private theorem cond_eq_adds_1_false_m2 {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat
  omega

/-- Stack budget of `<str as ToOwned>::to_owned` (`48` bytes local frame + `allocHookStack`). -/
abbrev strToOwnedLocal2Stack : Nat := 48 + allocHookStack

/-- Contract of `<str as alloc::borrow::ToOwned>::to_owned` (`0x8da5c`) for a non-empty
read-only string slice `(srcPtr ↦ᵣ bs)` (`0 < bs.length`, `bs.length < 2 ^ 63`), writing an owned
`String` (`vecU8 A outPtr bs`) at `outPtr` (`x0`) or panicking via `handle_alloc_error` on OOM. -/
@[expose] def strToOwnedLocal2Spec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  ({ pre := fun (outPtr, srcPtr, bs) s =>
        ⌜s.readReg64 .x0 = outPtr ∧
         s.readReg64 .x1 = srcPtr ∧
         s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
         0 < bs.length ∧
         bs.length < 2 ^ 63⌝ ∗
        memRegion outPtr 24 ∗
        (srcPtr ↦ᵣ bs) ∗
        A.pool ∗
        stackAt s.sp strToOwnedLocal2Stack
     post := fun (outPtr, srcPtr, bs) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        vecU8 A outPtr bs ∗
        (srcPtr ↦ᵣ bs) ∗
        A.pool ∗
        stackAt s0.sp strToOwnedLocal2Stack } : Spec _).allowPanicWhen
    (fun _ s0 sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)

theorem stackAt_strToOwnedLocal2 (sp : BitVec 64) :
    stackAt sp strToOwnedLocal2Stack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 := by
  exact ProofLib.stackAt_split_cells sp allocHookStack 6 (by decide)

/-- Stack budget of `<str as ToOwned>::to_owned` (`48` bytes local frame + `hookStack`). -/
abbrev strToOwnedLocal2StackWith (hookStack : Nat) : Nat := 48 + hookStack

/-- Stack-parametric contract of `<str as alloc::borrow::ToOwned>::to_owned`. -/
@[expose] def strToOwnedLocal2SpecWithStack (hookStack : Nat) (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  ({ pre := fun (outPtr, srcPtr, bs) s =>
        ⌜s.readReg64 .x0 = outPtr ∧
         s.readReg64 .x1 = srcPtr ∧
         s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
         0 < bs.length ∧
         bs.length < 2 ^ 63⌝ ∗
        memRegion outPtr 24 ∗
        (srcPtr ↦ᵣ bs) ∗
        A.pool ∗
        stackAt s.sp (strToOwnedLocal2StackWith hookStack)
     post := fun (outPtr, srcPtr, bs) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        vecU8 A outPtr bs ∗
        (srcPtr ↦ᵣ bs) ∗
        A.pool ∗
        stackAt s0.sp (strToOwnedLocal2StackWith hookStack) } : Spec _).allowPanicWhen
    (fun _ s0 sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)

theorem stackAt_strToOwnedLocal2With (hookStack : Nat) (sp : BitVec 64)
    (h : hookStack ≤ 2 ^ 64 - 48) :
    stackAt sp (strToOwnedLocal2StackWith hookStack) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 := by
  rw [show strToOwnedLocal2StackWith hookStack = hookStack + 8 * 6 by
    unfold strToOwnedLocal2StackWith; omega]
  exact ProofLib.stackAt_split_cells sp hookStack 6 (by omega)

theorem memRegion24_cells3 (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  rw [show (24 : Nat) = 8 * 3 by decide, ProofLib.memRegion_cells a 3 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem vecU8_of_exact_alloc (A : RustAlloc) (outPtr p : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp : p ≠ 0#64) :
    (outPtr ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    ((outPtr + 8#64) ↦₆₄ p) ∗
    ((outPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    A.live p bs.length 1 ∗
    (p ↦ₛ bs) ⊢
      vecU8 A outPtr bs := by
  refine Entails.sepExists_right (BitVec.ofNat 64 bs.length) (Entails.sepExists_right p ?_)
  have hcap_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_nz : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have ht : (BitVec.ofNat 64 bs.length).toNat = (0 : BitVec 64).toNat :=
      congrArg BitVec.toNat h0
    rw [hcap_toNat] at ht
    change bs.length = 0 at ht
    omega
  have _hp' : p ≠ 0 := hp
  unfold vecU8At vecHeader
  simp only [hcap_toNat, hcap_nz, ↓reduceIte, Nat.sub_self, memRegion_zero, sepConj_emp]
  sep_frame

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
