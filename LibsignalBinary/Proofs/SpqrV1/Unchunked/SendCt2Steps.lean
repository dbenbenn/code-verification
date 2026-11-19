/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<Ct1SentEkReceived>::send_ct2`: Stepping Helpers and Segments 1, 2, and 4

**Checked by Lean.**

Provides stack/memory splitting helpers and proves fixed-base Segments 1, 2, and 4
for `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`.
-/

public section

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ChainProofs CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L29b
open NextKeyInternalFacts AgreeStateSimp DoReserveNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length ctLabel_length

/-- Specialized `libcrux_hmac::hmac` contract when `key.length < 2^32` and `data.length < 2^32`
are already known at the call site, reducing `onPanic` to `allocFailedIn`. -/
@[expose] def libcruxHmacSafeSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec LibcruxHmacCall where
  pre x s :=
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64 ∧
      x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp extHookStack
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A x.ret (hmacWith F x.key x.data) ∗ A.pool ∗ stackAt s0.sp extHookStack
  onPanic _ s0 sf :=
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem SepWPp.call_allowPanic_mid {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧ (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call hcall hpc hrun hsp_align hlr hpre ?_ ?_ hnext ?_
  · intro sf code R' _ hpost
    rw [hexit_eq.1] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sf _ hm'
    exact Satisfies.mono (sepConj_mono_left (hpan sf)) hm'
  · intro sf R' _ hpost
    rw [hexit_eq.2] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

open Lean Elab Tactic in
elab "wpp_call_sendCt2 " hcall:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_mid $hcall (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_sendCt2: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR'
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm, *]
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_entails_of_trace_eq (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

/-! ## Stack and Memory Splitting Helpers -/

/-- Split `stackAt sp unchunkedSendCt2Stack` (`336 + extHookStack = 16720` bytes) into its frame slots:
- `stackAt (sp - 336#64) extHookStack` (`16384`B below `sp - 336`)
- `memRegion (sp - 336#64) 8` (`[sp1 + 0, sp1 + 8)`)
- 6 cells at `sp - 328#64 .. sp - 288#64` (`[sp1 + 8, sp1 + 56)`: `es.cap, ek.cap, epoch, ct1.cap, ct1.ptr, ct1.len`)
- `memRegion (sp - 280#64) 8` (`[sp1 + 56, sp1 + 64)`)
- `(sp - 272#64) ↦₆₄ s64 ∗ memRegion (sp - 264#64) 120` (`[sp1 + 64, sp1 + 192)`, 128B buffer)
- `memRegion (sp - 144#64) 24` (`[sp1 + 192, sp1 + 216)`, `x29 - 48`, `slice_concat_3` sret)
- `(sp - 120#64) ↦₆₄ e0` (`[sp1 + 216, sp1 + 224)`, `x29 - 24`, `epoch.to_be_bytes()`)
- `memRegion (sp - 112#64) 16` (`[sp1 + 224, sp1 + 240)`)
- 12 callee-save cells at `sp - 96#64 .. sp - 8#64` (`[sp1 + 240, sp1 + 336)`). -/
theorem stackAt_unchunkedSendCt2_split (sp : BitVec 64) :
    stackAt sp unchunkedSendCt2Stack =
      stackAt (sp - 336#64) extHookStack ∗
      memRegion (sp - 336#64) 8 ∗
      (∃∗ l0 : BitVec 64, ∃∗ l1 : BitVec 64, ∃∗ l2 : BitVec 64,
       ∃∗ l3 : BitVec 64, ∃∗ l4 : BitVec 64, ∃∗ l5 : BitVec 64,
        ((sp - 328#64) ↦₆₄ l0) ∗ ((sp - 320#64) ↦₆₄ l1) ∗
        ((sp - 312#64) ↦₆₄ l2) ∗ ((sp - 304#64) ↦₆₄ l3) ∗
        ((sp - 296#64) ↦₆₄ l4) ∗ ((sp - 288#64) ↦₆₄ l5)) ∗
      memRegion (sp - 280#64) 8 ∗
      (∃∗ s64 : BitVec 64, (sp - 272#64) ↦₆₄ s64) ∗
      memRegion (sp - 264#64) 120 ∗
      memRegion (sp - 144#64) 24 ∗
      (∃∗ e0 : BitVec 64, (sp - 120#64) ↦₆₄ e0) ∗
      memRegion (sp - 112#64) 16 ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  change memRegion (sp - BitVec.ofNat 64 16720) 16720 =
    memRegion (sp - 336#64 - BitVec.ofNat 64 16384) 16384 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16720) (n := 16384) (k := 336)
      (b' := sp - 336#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 336#64) (n := 8) (k := 328)
      (b' := sp - 328#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 328#64) (n := 48) (k := 280)
      (b' := sp - 280#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 280#64) (n := 8) (k := 272)
      (b' := sp - 272#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 8) (k := 264)
      (b' := sp - 264#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 264#64) (n := 120) (k := 144)
      (b' := sp - 144#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 144#64) (n := 24) (k := 120)
      (b' := sp - 120#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 112)
      (b' := sp - 112#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 112#64) (n := 16) (k := 96)
      (b' := sp - 96#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16720) 16384 ∗
    (memRegion (sp - 336#64) 8 ∗
      (memRegion (sp - 328#64) (8 * 6) ∗
        (memRegion (sp - 280#64) 8 ∗
          (memRegion (sp - 272#64) 8 ∗
            (memRegion (sp - 264#64) 120 ∗
              (memRegion (sp - 144#64) 24 ∗
                (memRegion (sp - 120#64) 8 ∗
                  (memRegion (sp - 112#64) 16 ∗ memRegion (sp - 96#64) (8 * 12))))))))) = _
  rw [ProofLib.memRegion_cells (sp - 328#64) 6 (by decide),
    ProofLib.memRegion_eight (sp - 272#64),
    ProofLib.memRegion_eight (sp - 120#64),
    ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : sp - 336#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16720 := by bv_kernel
  have hc6 : cells (sp - 328#64) 6 =
      (∃∗ l0 : BitVec 64, ∃∗ l1 : BitVec 64, ∃∗ l2 : BitVec 64,
       ∃∗ l3 : BitVec 64, ∃∗ l4 : BitVec 64, ∃∗ l5 : BitVec 64,
        ((sp - 328#64) ↦₆₄ l0) ∗ ((sp - 320#64) ↦₆₄ l1) ∗
        ((sp - 312#64) ↦₆₄ l2) ∗ ((sp - 304#64) ↦₆₄ l3) ∗
        ((sp - 296#64) ↦₆₄ l4) ∗ ((sp - 288#64) ↦₆₄ l5)) := by
    cells_unfold
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
    cells_unfold
  rw [hsub, hc6, hc12]

theorem fold_sp_272_128 (sp v : BitVec 64) :
    ((sp - 272#64) ↦₆₄ v) ∗ memRegion (sp - 264#64) 120 ⊢ memRegion (sp - 272#64) 128 := by
  rw [ProofLib.memRegion_split' (b := sp - 272#64) (n := 8) (k := 120)
        (b' := sp - 264#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (Drop.pointsTo64_entails_memRegion (sp - 272#64) v)

theorem stackAt_extHook_eq_allocHook (sp0 : BitVec 64) :
    stackAt (sp0 - 336#64) extHookStack =
      memRegion (sp0 - 16720#64) 12288 ∗ stackAt (sp0 - 336#64) allocHookStack := by
  change memRegion ((sp0 - 336#64) - 16384#64) 16384 =
    memRegion (sp0 - 16720#64) 12288 ∗ memRegion ((sp0 - 336#64) - 4096#64) 4096
  have h1 : (sp0 - 336#64) - 16384#64 = sp0 - 16720#64 := by bv_omega
  rw [h1, ProofLib.memRegion_split' (b := sp0 - 16720#64) (n := 12288) (k := 4096)
        (b' := (sp0 - 336#64) - 4096#64) rfl (by bv_omega) (by decide)]

theorem stackAt_extHook_eq_doReserve (sp0 : BitVec 64) :
    stackAt (sp0 - 336#64) extHookStack =
      memRegion (sp0 - 16720#64) 12176 ∗ stackAt (sp0 - 336#64) doReserveStack := by
  change memRegion ((sp0 - 336#64) - 16384#64) 16384 =
    memRegion (sp0 - 16720#64) 12176 ∗ memRegion ((sp0 - 336#64) - 4208#64) 4208
  have h1 : (sp0 - 336#64) - 16384#64 = sp0 - 16720#64 := by bv_omega
  rw [h1, ProofLib.memRegion_split' (b := sp0 - 16720#64) (n := 12176) (k := 4208)
        (b' := (sp0 - 336#64) - 4208#64) rfl (by bv_omega) (by decide)]

/-- Heap portion of `vecU8At A a cap ptr bs`. -/
@[expose] def vecU8HeapAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_cells_heap (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  unfold vecU8At vecHeader vecU8HeapAt
  ac_rfl

/-- Unpack `vecU8 A a bs` into its 3 header words `(a, a+8, a+16)` and `vecU8HeapAt A cap ptr bs`. -/
theorem vecU8_entails_cells_and_heap (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A a cap ptr bs]
  have hb : vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ vecU8HeapAt A cap ptr bs := by
    unfold vecU8HeapAt
    apply Entails.pure_left; intro h
    exact Entails.pure_right h (Entails.pure_right h (Entails.refl _))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hb))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem fold_vecU8At_sp_304 (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : Bytes) :
    ((sp - 304#64) ↦₆₄ cap) ∗ ((sp - 296#64) ↦₆₄ ptr) ∗
      ((sp - 288#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8HeapAt A cap ptr bs ⊢
      vecU8At A (sp - 304#64) cap ptr bs := by
  rw [vecU8At_eq_cells_heap A (sp - 304#64) cap ptr bs]
  have h1 : (sp - 304#64) + 8#64 = sp - 296#64 := by bv_omega
  have h2 : (sp - 304#64) + 16#64 = sp - 288#64 := by bv_omega
  rw [h1, h2]
  exact Entails.of_eq (by ac_rfl)

theorem fold_stA_48_80 (stA v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    ((stA + 48#64) ↦₆₄ v0) ∗ ((stA + 56#64) ↦₆₄ v1) ∗
      ((stA + 64#64) ↦₆₄ v2) ∗ ((stA + 72#64) ↦₆₄ v3) ∗
      ((stA + 80#64) ↦₆₄ v4) ∗ ((stA + 88#64) ↦₆₄ v5) ∗
      ((stA + 96#64) ↦₆₄ v6) ∗ ((stA + 104#64) ↦₆₄ v7) ∗
      ((stA + 112#64) ↦₆₄ v8) ∗ ((stA + 120#64) ↦₆₄ v9) ⊢
      memRegion (stA + 48#64) 80 := by
  have ha1 : (stA + 48#64) + 8#64 = stA + 56#64 := by bv_omega
  have ha2 : (stA + 48#64) + 16#64 = stA + 64#64 := by bv_omega
  have ha3 : (stA + 48#64) + 24#64 = stA + 72#64 := by bv_omega
  have ha4 : (stA + 48#64) + 32#64 = stA + 80#64 := by bv_omega
  have ha5 : (stA + 48#64) + 40#64 = stA + 88#64 := by bv_omega
  have ha6 : (stA + 48#64) + 48#64 = stA + 96#64 := by bv_omega
  have ha7 : (stA + 48#64) + 56#64 = stA + 104#64 := by bv_omega
  have ha8 : (stA + 48#64) + 64#64 = stA + 112#64 := by bv_omega
  have ha9 : (stA + 48#64) + 72#64 = stA + 120#64 := by bv_omega
  change _ ⊢ memRegion (stA + 48#64) (8 * 10)
  rw [ProofLib.memRegion_cells (stA + 48#64) 10 (by decide)]
  dsimp only [cells]
  simp only [BitVec.add_zero, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.of_eq (by ac_rfl)))))))))))

/-- Callee-save slots saved at `sp - 96#64 .. sp - 8#64` by the prologue (`0x5e404..0x5e418`). -/
@[expose] def sendCt2CalleeSavedAt (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

abbrev sendCt2PostQ (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (x : UnchunkedSendCt2Ghost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (unchunkedCt1SentEkReceivedSendCt2Spec A F K b).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev sendCt2PostQp (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (x : UnchunkedSendCt2Ghost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (unchunkedCt1SentEkReceivedSendCt2Spec A F K b).onPanic x s0 sf ∗ R)

theorem SepWPp.of_sepWP_mid {prog : Program} {retPC mid : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun s' P' => SepWPp prog retPC s' P' Q Qp)) :
    SepWPp prog retPC s P Q Qp :=
  SepWPp.of_sepWP h

theorem vecU8HeapAt_expose_nonempty (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 := by
  dsimp only [vecU8HeapAt]
  apply Entails.pure_left; rintro ⟨hle, hmax, hptr_ne⟩
  have hcap_ne : cap ≠ 0 := by
    intro h0; subst h0
    have hle0 : bs.length ≤ 0 := hle
    omega
  simp only [hcap_ne, ↓reduceIte]
  refine Entails.pure_right ⟨hle, hmax, hptr_ne, hcap_ne⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem vecU8HeapAt_expose_of_ne_zero (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap_ne : cap ≠ 0#64) :
    vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 := by
  dsimp only [vecU8HeapAt]
  have hcap_ne' : cap ≠ 0 := hcap_ne
  simp only [hcap_ne', ↓reduceIte]
  exact Entails.of_eq (by ac_rfl)

theorem le_of_not_ule_sub_len {cap : BitVec 64} {len : Nat}
    (hle : len ≤ cap.toNat) (hmax : cap.toNat < 2 ^ 63)
    (h : ¬ (cap - BitVec.ofNat 64 len).ule 127#64 = true) :
    len + 128 ≤ cap.toNat := by
  have hlen_bv : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le] at h
  · rw [hlen_bv] at h
    change ¬ (cap.toNat - len ≤ 127) at h; omega
  · rw [BitVec.le_def, hlen_bv]; exact hle

theorem cap_ne_zero_of_add_128_le {cap : BitVec 64} {len : Nat}
    (h : len + 128 ≤ cap.toNat) : cap ≠ 0#64 := by
  intro h0; subst h0; simp at h

theorem reserveCap_bound_of_ule_sub_len {cap : BitVec 64} {len : Nat}
    (hle : len ≤ cap.toNat) (hlen : len < 2 ^ 32)
    (h : (cap - BitVec.ofNat 64 len).ule 127#64 = true) :
    reserveCap cap.toNat len 128 + 1 ≤ 2 ^ 63 := by
  have hlen_bv : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le] at h
  · rw [hlen_bv] at h
    change cap.toNat - len ≤ 127 at h
    dsimp only [reserveCap]
    omega
  · rw [BitVec.le_def, hlen_bv]; exact hle

theorem reserveCap_ge_add_128 {cap len : Nat}
    (hbound : reserveCap cap len 128 + 1 ≤ 2 ^ 63) :
    len + 128 ≤ (BitVec.ofNat 64 (reserveCap cap len 128)).toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  dsimp only [reserveCap]
  omega

theorem reserveCap_ne_zero_len {cap len : Nat}
    (hbound : reserveCap cap len 128 + 1 ≤ 2 ^ 63) :
    BitVec.ofNat 64 (reserveCap cap len 128) ≠ 0#64 := by
  intro h0
  have h1 := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change reserveCap cap len 128 = 0 at h1
  dsimp only [reserveCap] at h1
  omega

theorem vecU8At_expose_sp_304_of_ne_zero (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap_ne : cap ≠ 0#64) :
    vecU8At A (sp - 304#64) cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 304#64) ↦₆₄ cap) ∗
        ((sp - 296#64) ↦₆₄ ptr) ∗
        ((sp - 288#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by
  rw [vecU8At_eq_cells_heap A (sp - 304#64) cap ptr bs]
  have h1 : (sp - 304#64) + 8#64 = sp - 296#64 := by bv_omega
  have h2 : (sp - 304#64) + 16#64 = sp - 288#64 := by bv_omega
  rw [h1, h2]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_of_ne_zero A cap ptr bs hcap_ne)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem vecU8At_expose_sp_304_cells_heap (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (sp - 304#64) cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 304#64) ↦₆₄ cap) ∗
        ((sp - 296#64) ↦₆₄ ptr) ∗
        ((sp - 288#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  rw [vecU8At_eq_cells_heap A (sp - 304#64) cap ptr bs]
  have h1 : (sp - 304#64) + 8#64 = sp - 296#64 := by bv_omega
  have h2 : (sp - 304#64) + 16#64 = sp - 288#64 := by bv_omega
  rw [h1, h2]
  have hb : vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ vecU8HeapAt A cap ptr bs := by
    unfold vecU8HeapAt
    apply Entails.pure_left; intro h
    exact Entails.pure_right h (Entails.pure_right h (Entails.refl _))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hb))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem call_rustAlloc {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustAllocSpec A))
    (size align : Nat) (hlay : LayoutOk size align)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 Reg.x0).toNat = size) (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        (((if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
             A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size) ∗
          A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := (size, align)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm; rw [hsplit] at hm; dsimp only [rustAllocSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustAllocSpec]; rw [hsp, htrace]
    have hassoc :
        (A.pool ∗ stackAt sp_call allocHookStack ∗
          (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
             A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)) ∗ Frame =
        (((if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
             A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size) ∗
          A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) := by ac_rfl
    rw [hassoc]; exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf

/-- Conditional heap ownership of the working `es` buffer after `0x5e488 → 0x5e628`. -/
@[expose] def sendCt2EsWorkAt (A : RustAlloc) (esPtr esWorkPtr : BitVec 64) (es : Bytes) : SepProp :=
  if issue1275NeedsFlip ((es.drop 1536).take 512) then
    ⌜esWorkPtr ≠ 0#64⌝ ∗ (esPtr ↦ₛ es) ∗
      (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes es) ∗ A.live esWorkPtr 2080 1
  else
    ⌜esWorkPtr = esPtr⌝ ∗ (esPtr ↦ₛ es)

end CryptoVerification.SpqrV1.Unchunked

