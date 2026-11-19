/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerialize -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.FnOffEq -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerialize -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen -- shake: keep
meta import ProofLib.SepLogic.WP.Apply -- shake: keep
meta import ProofLib.SepLogic.WPp -- shake: keep

/-!
# Budget-Threaded Verification of `<Message>::serialize`

Deterministic allocator event list (`messageSerializeEvents`), envelope (`MessageSerializeEnv`),
and correctness proof for `<spqr::v1::chunked::states::Message>::serialize` (110 instructions)
under `RustCliAllocBudget`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget

open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap (allocHookStack vecU8 vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (MAX_VARINT_BYTES_LEN Message MessagePayload MessageType PolyApi
   encodeVarintLoop encode_chunk encode_varint)
open CryptoVerification.SpqrV1.Poly (chunkAt chunkIndexOff)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost bv_len_add_one vecU8Buf vecU8Buf_eq_open_one vecU8Buf_snoc_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm (false_eq_true')
open CryptoVerification.SpqrV1.Top.EncodeVarint
  (len_beq_cap_false sp_sub_80_aligned spqrEncodeVarintName spqrEncodeVarintStackX)
open CryptoVerification.SpqrV1.Top.MessageSerialize (MessageSerializeGhost encodeVarintLoop_length_le encode_varint_length_le extractLsb_hi_append64 extractLsb_lo_append64 list_eq_unpack64_4_of_len32 memRegion_40_split_1_39 messageAt messagePayloadAt messageSerializeName messageSerializeStackX pointsToBytes_unpack64_4_eq rem40_ult_31_of_gt rem40_ult_31_of_le stackAt_messageSerialize_eq stackAt_spqrEncodeVarint_to_allocHook stackAt_spqrEncodeVarint_to_doReserve vecU8At_eq_header_buf vecU8At_init_40_one vecU8At_sp72_eq vecU8Buf_append_32_eq vecU8Buf_eq_open_32)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   VmPreserved fitsEvents_append rustAllocEvents rustReallocEvents
   subroutine_ok_allocNoOom_of_budgetBase)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomExternSpecWithStackBase subroutine_ok_rustCliAllocNoOom_externWithStackBase)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserve7Name doReserveSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
  (sepWP_seg_rebase_vm sepWPp_seg_rebase_vm)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (memRegion_24 session2ShimSpecWithStack)

open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget (SpqrEncodeVarintEnv spqrEncodeVarintEvents_of_spare spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff noAllocShimSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  false_eq_true' extractLsb_lo_append64 extractLsb_hi_append64

/-! ## 1. Deterministic Allocator Events, Envelope, and Budget Specification -/

/-- Exact deterministic `AllocEvent` list emitted by `<Message>::serialize` on `x`:
    * allocates an initial 40-byte `Vec<u8>` (`rustAllocEvents 40 1`);
    * the two header varints (`epoch` and `index`) and any chunk `index` varint fit inside capacity 40
    without reallocation (`1 + 10 + 10 + 1 + 10 = 32 ≤ 40`);
    * on chunk variants whose encoded prefix `bs4` satisfies `¬ (bs4.length + 32 ≤ 40)`,
    `do_reserve_and_handle [local#7]` grows capacity from `40` to `80`
    (`rustReallocEvents 40 80 1`). -/
@[expose] def messageSerializeEvents (P_api : PolyApi) (x : MessageSerializeGhost P_api) : List AllocEvent :=
  let bs1 := encode_varint x.msg.epoch [1#8]
  let bs2 := encode_varint (x.index.zeroExtend 64) bs1
  let chunkEvs (tag : BitVec 8) (c : P_api.Chunk) : List AllocEvent :=
    let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
    if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
    else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1
  match x.msg.payload with
  | .none | .ct1Ack _ => rustAllocEvents 40 1
  | .hdr c => chunkEvs 1#8 c
  | .ek c => chunkEvs 2#8 c
  | .ekCt1Ack c => chunkEvs 3#8 c
  | .ct1 c => chunkEvs 5#8 c
  | .ct2 c => chunkEvs 6#8 c

/-- Deterministic allocator event envelope of `<spqr::v1::chunked::states::Message>::serialize`. -/
@[expose] def MessageSerializeEnv (P_api : PolyApi) (x : MessageSerializeGhost P_api)
    (evs : List AllocEvent) : Prop :=
  evs = messageSerializeEvents P_api x

theorem messageSerializeEnv_events (P_api : PolyApi) (x : MessageSerializeGhost P_api) :
    MessageSerializeEnv P_api x (messageSerializeEvents P_api x) := rfl

theorem fitsEnv_messageSerialize_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (P_api : PolyApi) (x : MessageSerializeGhost P_api) :
    FitsEnv M lim st (MessageSerializeEnv P_api x) ↔
      FitsEvents M lim st (messageSerializeEvents P_api x) :=
  FitsEnv.eq_iff

private theorem fitsEvents_alloc40_of_messageSerialize {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {P_api : PolyApi} {x : MessageSerializeGhost P_api}
    (h : FitsEvents M lim st (messageSerializeEvents P_api x)) :
    FitsEvents M lim st (rustAllocEvents 40 1) := by
  unfold messageSerializeEvents at h
  cases hpay : x.msg.payload <;> simp only [hpay] at h
  · exact h
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · exact h
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1

/-- Budget-threaded specification of `<spqr::v1::chunked::states::Message>::serialize` (110
    insns) against `Message.serialize` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEnv M
    lim st (MessageSerializeEnv P_api x)`). -/
@[expose] def messageSerializeSpecX (P_api : PolyApi) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (MessageSerializeGhost P_api × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ (s.readReg64 .x1).setWidth 32 = x.index ∧
      s.readReg64 .x8 = x.ret ∧ FitsEnv M lim st (MessageSerializeEnv P_api x)⌝ ∗
      messageAt P_api x.msgA x.msg ∗ memRegion x.ret 24 ∗ A.pool lim st s ∗
      stackAt s.sp messageSerializeStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      messageAt P_api x.msgA x.msg ∗
      vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
      (∃∗ evs : List AllocEvent, ⌜MessageSerializeEnv P_api x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp messageSerializeStackX

private abbrev fetch_withSvc' :=
  LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux.fetch_withSvc

private theorem sepWPp_of_sepWP_mid {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hPm, hcont⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc h hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ := hcont R hPm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

@[expose] def MsgSerializeCS (s0 s : State) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem MsgSerializeCS.trans {s0 s1 s2 : State}
    (h1 : MsgSerializeCS s0 s1) (h2 : MsgSerializeCS s1 s2) :
    MsgSerializeCS s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩

theorem MsgSerializeCS.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) : MsgSerializeCS s1 s2 :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2⟩

attribute [local irreducible] Program.fnAddr

private theorem doReserveEvents_40_32 (v ptr : BitVec 64) (curBs : List (BitVec 8))
    (hlen : curBs.length ≤ 32) :
    doReserveEvents (DoReserveCall.mk v 40#64 ptr curBs 32) = rustReallocEvents 40 80 1 := by
  have hres : TripleRatchet.Alloc.DefsBudget.reserveCap (40#64 : BitVec 64).toNat curBs.length 32 = 80 := by
    unfold TripleRatchet.Alloc.DefsBudget.reserveCap reserveCap
    change max (max (curBs.length + 32) (2 * 40)) 8 = 80; omega
  have hne : (40#64 : BitVec 64) ≠ 0#64 := by decide
  unfold doReserveEvents
  simp only [hne, ↓reduceIte, hres]; rfl

private def poolPostAt (P_api : PolyApi) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (x : MessageSerializeGhost P_api)
    (st0 : M.σ) (sf : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜MessageSerializeEnv P_api x evs⌝ ∗
    A.pool lim (M.stepEvents evs st0) sf

end LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
