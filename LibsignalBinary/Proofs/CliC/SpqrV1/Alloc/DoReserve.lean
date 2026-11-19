/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrow
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `RawVecInner::do_reserve_and_handle` Proofs for `CliC`

Proves `doReserveStrideRawSpec`, `doReserveRawSpec`, and `doReserveSpec` (plus `AllocContractsX`
variants) for `RawVecInner::reserve::do_reserve_and_handle` in the CLI image.
-/

public section

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DoReserveNorm

end DoReserveNorm

open DoReserveNorm

/-! ## Symbol Names and Capacity Helpers -/

abbrev _root_.CryptoVerification.CliC.SpqrV1.Alloc.doReserve7Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"

private theorem stackAt_doReserve (sp : BitVec 64) :
    stackAt sp doReserveStack =
      stackAt (sp - 64#64) finishGrowStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4144 8 (by decide)
  change stackAt sp doReserveStack =
    stackAt (sp - 64#64) finishGrowStack ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

private def finishGrow8ZeroCellsSpec (A : RustAlloc) : Spec FG8Ghost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp finishGrowStack
  post := fun (out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗
          memRegion p' (new.toNat * stride.toNat)) ∗
      A.pool ∗ stackAt fsp finishGrowStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private def finishGrow8NeCellsSpec (A : RustAlloc) : Spec FG8Ghost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp finishGrowStack
  post := fun (out, cap, ptr, new, align, stride, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * stride.toNat - bs.length)) ∗
      A.pool ∗ stackAt fsp finishGrowStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

end CryptoVerification.SpqrV1.Alloc
