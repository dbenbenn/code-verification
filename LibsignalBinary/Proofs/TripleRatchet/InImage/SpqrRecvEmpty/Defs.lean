/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prog -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import ProofLib.SepLogic.WP
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetProofDefs
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof
import ProofLib.Sep
import ProofLib.SepLogic.WPp
public import ProofLib.GenDecodes

/-!
# Layouts, Callees, and Frame-Generic Specs for Empty-State `spqr::recv`

Instruction decodes, stack and result-buffer splits, `spqr::decode_state` and `memcpy` callee
lemmas, and frame-generic specifications (`spqrRecvCodeSpec`, `spqrRecvEmptyCodeSpec`) for
`spqr::recv` on an empty state.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `decodeStateEmptyAt` at `t - 3056` (`sp_f + 0x790`), cut at the words `spqr::recv` reads
before `memcpy` (`+0`, `+8`, `+16`, `+24`) and the `chain` / `inner` words. -/
theorem decodeEmpty_recv_split (t : BitVec 64) :
    decodeStateEmptyAt (t - 3056#64) =
      ((t - 3056#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      (∃∗ a1 : BitVec 64, (t - 3048#64) ↦₆₄ a1) ∗
      (∃∗ a2 : BitVec 64, (t - 3040#64) ↦₆₄ a2) ∗
      (∃∗ a3 : BitVec 64, (t - 3032#64) ↦₆₄ a3) ∗
      memRegion (t - 3024#64) 16 ∗
      ((t - 3008#64) ↦₆₄ pqChainNone) ∗
      memRegion (t - 3000#64) 72 ∗
      ((t - 2928#64) ↦₆₄ pqInnerNone) ∗
      memRegion (t - 2920#64) 216 := by
  unfold decodeStateEmptyAt
  sep_interval_eq

/-- The 48-byte `recv` result buffer `ret`, cut at the four 8-byte words touched on the `Ok` and
`Err` paths (`+0`, `+8`, `+16`, `+24`). -/
theorem ret_48_split (r : BitVec 64) :
    memRegion r 48 =
      (∃∗ r0 : BitVec 64, r ↦₆₄ r0) ∗
      (∃∗ r1 : BitVec 64, (r + 8#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (r + 16#64) ↦₆₄ r2) ∗
      (∃∗ r3 : BitVec 64, (r + 24#64) ↦₆₄ r3) ∗
      memRegion (r + 32#64) 16 := by
  sep_interval_eq

/-- The 320-byte decode payload at `a` as `spqr::recv` reads it (`chain` at `+16`, `inner` at `+96`). -/
@[expose] def pcs (a c i : BitVec 64) : SepProp :=
  memRegion a 16 ∗ ((a + 16#64) ↦₆₄ c) ∗ memRegion (a + 24#64) 72 ∗ ((a + 96#64) ↦₆₄ i) ∗
    memRegion (a + 104#64) 216

theorem pcs_of_bytes (a c i : BitVec 64) (b1 b3 b5 : List (BitVec 8)) (h1 : b1.length = 16)
    (h3 : b3.length = 72) (h5 : b5.length = 216) :
    (a ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ⊢ pcs a c i := by
  simp only [pointsToBytes_append, unpack64_length, h1, h3, BitVec.add_assoc, BitVec.reduceAdd,
    ← pointsTo64_eq_pointsToBytes, pcs]
  sep_interval

theorem bytes_of_pcs (a c i : BitVec 64) :
    pcs a c i ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = 320 ∧ ∃ b1 b3 b5 : List (BitVec 8),
      b1.length = 16 ∧ b3.length = 72 ∧ b5.length = 216 ∧
      bs = b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))⌝ ∗ (a ↦ₛ bs) := by
  unfold pcs
  rw [memRegion_eq_exists_bytes a 16 (by decide), sepExists_sepConj_left]
  refine Entails.sepExists_elim fun b1 => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun h1 => ?_
  rw [memRegion_eq_exists_bytes (a + 24#64) 72 (by decide), sepExists_sepConj_left,
    sepExists_sepConj_right, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun b3 => ?_
  rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
  refine Entails.pure_left fun h3 => ?_
  rw [memRegion_eq_exists_bytes (a + 104#64) 216 (by decide)]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun b5 => ?_
  simp only [sepConj_pure_left_comm]
  refine Entails.pure_left fun h5 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro
    (P := fun bs : List (BitVec 8) => ⌜bs.length = 320 ∧ ∃ b1 b3 b5 : List (BitVec 8),
      b1.length = 16 ∧ b3.length = 72 ∧ b5.length = 216 ∧
      bs = b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))⌝ ∗ (a ↦ₛ bs))
    (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))))
  refine Entails.pure_right ⟨by simp [h1, h3, h5, unpack64_length], b1, b3, b5, h1, h3, h5, rfl⟩ ?_
  simp only [pointsToBytes_append, unpack64_length, h1, h3, BitVec.add_assoc, BitVec.reduceAdd,
    ← pointsTo64_eq_pointsToBytes]
  exact Entails.refl _

theorem pcs_src (t c i : BitVec 64) :
    pcs (t - 3024#64) c i = (memRegion (t - 3024#64) 16 ∗ ((t - 3008#64) ↦₆₄ c) ∗
      memRegion (t - 3000#64) 72 ∗ ((t - 2928#64) ↦₆₄ i) ∗ memRegion (t - 2920#64) 216) := by
  unfold pcs
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub]

theorem pcs_dst (t c i : BitVec 64) :
    pcs (t - 4960#64) c i = (memRegion (t - 4960#64) 16 ∗ ((t - 4944#64) ↦₆₄ c) ∗
      memRegion (t - 4936#64) 72 ∗ ((t - 4864#64) ↦₆₄ i) ∗ memRegion (t - 4856#64) 216) := by
  unfold pcs
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub]

/-- `memcpy(t - 4960, t - 3024, 320)` in `spqr::recv` (`+0x194`). -/
@[expose] def memcpyRecvPcsSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (t, c, i) s0 =>
    ⌜s0.readReg64 .x0 = t - 4960#64 ∧ s0.readReg64 .x1 = t - 3024#64 ∧
      s0.readReg64 .x2 = 320#64⌝ ∗
    memRegion (t - 4960#64) 320 ∗
    (memRegion (t - 3024#64) 16 ∗ ((t - 3008#64) ↦₆₄ c) ∗
      memRegion (t - 3000#64) 72 ∗ ((t - 2928#64) ↦₆₄ i) ∗ memRegion (t - 2920#64) 216)
  post := fun (t, c, i) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = t - 4960#64⌝ ∗
    (memRegion (t - 4960#64) 16 ∗ ((t - 4944#64) ↦₆₄ c) ∗
      memRegion (t - 4936#64) 72 ∗ ((t - 4864#64) ↦₆₄ i) ∗ memRegion (t - 4856#64) 216) ∗
    (memRegion (t - 3024#64) 16 ∗ ((t - 3008#64) ↦₆₄ c) ∗
      memRegion (t - 3000#64) 72 ∗ ((t - 2928#64) ↦₆₄ i) ∗ memRegion (t - 2920#64) 216)

theorem hookMemcpy_recv_pcs_ok : HookOk hookMemcpy memcpyRecvPcsSpec := by
  refine retHook_ok fun ⟨t, c, i⟩ R s0 _ hpre _ => ?_
  simp only [memcpyRecvPcsSpec] at hpre
  rw [← pcs_src, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (bytes_of_pcs _ c i))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  obtain ⟨⟨hlen, b1, b3, b5, h1, h3', h5, rfl⟩, h4⟩ := h3
  have hmem' : s0.mem ⊨ memRegion (t - 4960#64) (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++
      b5)))).length ∗ (((t - 3024#64) ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ∗ R) := by
    rw [hlen, ← sepConj_assoc]; exact h4
  have hsrc_front : s0.mem ⊨ ((t - 3024#64) ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ∗
      (memRegion (t - 4960#64) 320 ∗ R) := by
    rw [sepConj_comm (memRegion _ 320), sepConj_assoc] at h4; exact h4
  obtain ⟨hlen', hread⟩ := (IsBlock.pointsToBytes _ _).read hsrc_front
  have hx2' : (s0.readReg64 .x2).toNat =
      (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))).length := by
    rw [hx2, hlen]; rfl
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx2', hread]
    exact keepsFrozen_writeBytes_of_memRegion _ hlen' hmem'
  · simp only [memcpyRecvPcsSpec, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2', hread]
    rw [← pcs_src, ← pcs_dst, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨rfl, trivial⟩, ?_⟩
    have hw := satisfies_writeBytes _ hlen' hmem'
    rw [← sepConj_assoc] at hw
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5)
      (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5))) hw

/-- `memcpyRecvPcsSpec` augmented with `stackAt sp extHookStack`. -/
@[expose] def memcpyRecvPcsSpecS : Spec (BitVec 64 × BitVec 64 × BitVec 64) :=
  { memcpyRecvPcsSpec with
    pre := fun x s => memcpyRecvPcsSpec.pre x s ∗ stackAt s.sp extHookStack
    post := fun x s0 sf => memcpyRecvPcsSpec.post x s0 sf ∗ stackAt s0.sp extHookStack }

theorem pcs_entails (a c i : BitVec 64) : pcs a c i ⊢ memRegion a 320 := by
  unfold pcs; sep_interval

theorem dst_recv_fold (t c i : BitVec 64) :
    (memRegion (t - 4960#64) 16 ∗ ((t - 4944#64) ↦₆₄ c) ∗
      memRegion (t - 4936#64) 72 ∗ ((t - 4864#64) ↦₆₄ i) ∗ memRegion (t - 4856#64) 216) ⊢
    memRegion (t - 4960#64) 320 := by
  sep_interval

theorem decode_recv_fold (t w d1 d2 d3 c i : BitVec 64) :
    ((t - 3056#64) ↦₆₄ w) ∗ ((t - 3048#64) ↦₆₄ d1) ∗ ((t - 3040#64) ↦₆₄ d2) ∗
      ((t - 3032#64) ↦₆₄ d3) ∗
      (memRegion (t - 3024#64) 16 ∗ ((t - 3008#64) ↦₆₄ c) ∗
        memRegion (t - 3000#64) 72 ∗ ((t - 2928#64) ↦₆₄ i) ∗ memRegion (t - 2920#64) 216) ⊢
    memRegion (t - 3056#64) 352 := by
  sep_interval

/-- The `Ok` result (`([], none)`) written at `ret` on the empty-state path. -/
theorem recv_ok_result_fold (A : RustAlloc) (r : BitVec 64) :
    ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
      ((r + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (r + 32#64) 16) ⊢
    spqrRecvResultAt A r (.ok ([], none)) := by
  have hv : ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗ ((r + 16#64) ↦₆₄ 0#64)) ⊢ vecU8 A r [] := by
    unfold vecU8
    refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
    refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
    simp only [vecU8At, vecHeader, List.length_nil]
    split
    · rw [sepConj_emp, sepConj_comm _ ⌜_⌝]
      refine Entails.pure_right ?_ (Entails.refl _)
      exact ⟨Nat.zero_le _, by decide, by decide⟩
    · exact absurd rfl ‹_›
  simp only [spqrRecvResultAt, spqrRecvKeyAt]
  refine Entails.trans (Entails.of_eq (Q := ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗
      ((r + 16#64) ↦₆₄ 0#64)) ∗ (((r + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      memRegion (r + 32#64) 16)) (by simp only [sepConj_assoc])) ?_
  refine sepConj_mono hv ?_
  refine Entails.trans ?_ (Entails.sepExists_intro true)
  exact Entails.of_eq (by rw [BitVec.add_assoc]; rfl)

/-- The `Err(MsgDecode)` result (`.error false`: word 0 = `-1`, word 8 = `2`) written at `ret`. -/
theorem recv_err_result_fold (A : RustAlloc) (r r2 r3 : BitVec 64) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((r + 8#64) ↦₆₄ 2#64) ∗
      ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗ memRegion (r + 32#64) 16) ⊢
    spqrRecvResultAt A r (.error false) := by
  simp only [spqrRecvResultAt]
  have h8 : ((r + 8#64) ↦₆₄ 2#64) ⊢ ((r + 8#64) ↦₈ 2#8) ∗ memRegion (r + 9#64) 7 := by
    rw [pointsTo64_eq_pointsToBytes]
    change ((r + 8#64) ↦ₛ (2#8 :: [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8])) ⊢ _
    rw [pointsToBytes_cons, show r + 8#64 + 1#64 = r + 9#64 by bv_arith]
    exact sepConj_mono_right (pointsToBytes_entails_memRegion _ _)
  have htail :
      memRegion (r + 9#64) 7 ∗ ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗
        memRegion (r + 32#64) 16 ⊢
      memRegion (r + 9#64) 39 := by sep_interval
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left h8) ?_
  rw [sepConj_assoc]
  refine Entails.trans (sepConj_mono_right htail) ?_
  refine sepConj_mono_left ?_
  refine Entails.trans ?_ (Entails.sepExists_intro 2#8)
  exact Entails.pure_right (by decide) (Entails.refl _)

end CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
