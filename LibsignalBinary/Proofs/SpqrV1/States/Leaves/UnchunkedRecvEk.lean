/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (`0x5dac0`, `99` instructions)

**Checked by Lean.** Verifies that `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` satisfies
`unchunkedCt1SentRecvEkSpec`.
-/

public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

theorem unchunked_recv_ek_elim {F : ShaCompress} {K : MlKem}
    {st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)} {ek : Bytes}
    {res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))}
    (h : st.recv_ek K st.epoch ek = StatesResult.ofError res) :
    (K.validPkBytes st.hdr ek = true →
      res = .ok { epoch := st.epoch, auth := st.auth, es := st.es, ek := ek, ct1 := st.ct1 }) ∧
    (K.validPkBytes st.hdr ek = false →
      res = .error .erroneousDataReceived) := by
  unfold Unchunked.SendCt.Ct1Sent.recv_ek ek_matches_header at h
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  constructor
  · intro hv
    rw [hv] at h
    simp only [↓reduceIte] at h
    cases res with
    | ok v =>
      dsimp only [StatesResult.ofError] at h
      exact congrArg Except.ok (Except.ok.inj h).symm
    | error e =>
      dsimp only [StatesResult.ofError] at h
      nomatch h
  · intro hv
    rw [hv] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases res with
    | ok v =>
      dsimp only [StatesResult.ofError] at h
      nomatch h
    | error e =>
      dsimp only [StatesResult.ofError] at h
      have he : StatesError.err .erroneousDataReceived = StatesError.err e := Except.error.inj h
      exact congrArg Except.error (StatesError.err.inj he).symm

theorem bics_255_eq_zero_iff (v0 : BitVec 64) :
    (BitVec.truncate 32 (255#64 &&& ~~~BitVec.zeroExtend 64 (BitVec.truncate 32 v0)) == 0#32) = true ↔
      v0.setWidth 8 = 0xff#8 := by
  rw [beq_iff_eq]
  bv_slice

/-! ## 2. Stack & `Vec<u8>` Layout Helpers -/

@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_8 (sp : BitVec 64) :
    (sp - 208#64) + 8#64 = sp - 200#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_16 (sp : BitVec 64) :
    (sp - 208#64) + 16#64 = sp - 192#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_24 (sp : BitVec 64) :
    (sp - 208#64) + 24#64 = sp - 184#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_32 (sp : BitVec 64) :
    (sp - 208#64) + 32#64 = sp - 176#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_40 (sp : BitVec 64) :
    (sp - 208#64) + 40#64 = sp - 168#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_48 (sp : BitVec 64) :
    (sp - 208#64) + 48#64 = sp - 160#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_56 (sp : BitVec 64) :
    (sp - 208#64) + 56#64 = sp - 152#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_64 (sp : BitVec 64) :
    (sp - 208#64) + 64#64 = sp - 144#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_72 (sp : BitVec 64) :
    (sp - 208#64) + 72#64 = sp - 136#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_80 (sp : BitVec 64) :
    (sp - 208#64) + 80#64 = sp - 128#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_88 (sp : BitVec 64) :
    (sp - 208#64) + 88#64 = sp - 120#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_96 (sp : BitVec 64) :
    (sp - 208#64) + 96#64 = sp - 112#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_104 (sp : BitVec 64) :
    (sp - 208#64) + 104#64 = sp - 104#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_112 (sp : BitVec 64) :
    (sp - 208#64) + 112#64 = sp - 96#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_120 (sp : BitVec 64) :
    (sp - 208#64) + 120#64 = sp - 88#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_128 (sp : BitVec 64) :
    (sp - 208#64) + 128#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_136 (sp : BitVec 64) :
    (sp - 208#64) + 136#64 = sp - 72#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_144 (sp : BitVec 64) :
    (sp - 208#64) + 144#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_152 (sp : BitVec 64) :
    (sp - 208#64) + 152#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_160 (sp : BitVec 64) :
    (sp - 208#64) + 160#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_168 (sp : BitVec 64) :
    (sp - 208#64) + 168#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_176 (sp : BitVec 64) :
    (sp - 208#64) + 176#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_184 (sp : BitVec 64) :
    (sp - 208#64) + 184#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_192 (sp : BitVec 64) :
    (sp - 208#64) + 192#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_200 (sp : BitVec 64) :
    (sp - 208#64) + 200#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_208_add_208 (sp : BitVec 64) :
    (sp - 208#64) + 208#64 = sp := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_8 (sp : BitVec 64) :
    (sp - 192#64) + 8#64 = sp - 184#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_16 (sp : BitVec 64) :
    (sp - 192#64) + 16#64 = sp - 176#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_24 (sp : BitVec 64) :
    (sp - 192#64) + 24#64 = sp - 168#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_32 (sp : BitVec 64) :
    (sp - 192#64) + 32#64 = sp - 160#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_40 (sp : BitVec 64) :
    (sp - 192#64) + 40#64 = sp - 152#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_48 (sp : BitVec 64) :
    (sp - 192#64) + 48#64 = sp - 144#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_56 (sp : BitVec 64) :
    (sp - 192#64) + 56#64 = sp - 136#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_64 (sp : BitVec 64) :
    (sp - 192#64) + 64#64 = sp - 128#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_72 (sp : BitVec 64) :
    (sp - 192#64) + 72#64 = sp - 120#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_80 (sp : BitVec 64) :
    (sp - 192#64) + 80#64 = sp - 112#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_88 (sp : BitVec 64) :
    (sp - 192#64) + 88#64 = sp - 104#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_96 (sp : BitVec 64) :
    (sp - 192#64) + 96#64 = sp - 96#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_104 (sp : BitVec 64) :
    (sp - 192#64) + 104#64 = sp - 88#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_112 (sp : BitVec 64) :
    (sp - 192#64) + 112#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_192_add_120 (sp : BitVec 64) :
    (sp - 192#64) + 120#64 = sp - 72#64 := by bv_omega

/-- Saved callee-saved registers at `s0.sp - 64#64 .. s0.sp - 8#64` (`8` words = `64`B). -/
@[expose] def unchunkedRecvEkSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem fold_unchunkedRecvEkSavedCells (s0 : State) :
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
    unchunkedRecvEkSavedCells s0 :=
  Entails.refl _

theorem unchunkedRecvEkSavedCells_entails_memRegion_64 (s0 : State) :
    unchunkedRecvEkSavedCells s0 ⊢ memRegion (s0.sp - 64#64) 64 := by
  have heq : unchunkedRecvEkSavedCells s0 =
      wordsAt (s0.sp - 64#64)
        [s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x24, s0.readReg64 .x23,
         s0.readReg64 .x22, s0.readReg64 .x21, s0.readReg64 .x20, s0.readReg64 .x19] := by
    unfold unchunkedRecvEkSavedCells
    simp only [wordsAt_8, arm64_norm]
  rw [heq]
  exact wordsAt_entails_memRegion _ (s0.sp - 64#64) 64 rfl

theorem stackAt_unchunkedRecvEk_split (sp : BitVec 64) :
    stackAt sp unchunkedRecvEkStack =
      stackAt (sp - 208#64) extHookStack ∗
      memRegion (sp - 208#64) 8 ∗
      cells (sp - 200#64) 1 ∗
      memRegion (sp - 192#64) 128 ∗
      cells (sp - 64#64) 8 := by
  change memRegion (sp - 16592#64) 16592 =
    memRegion (sp - 208#64 - 16384#64) 16384 ∗
    memRegion (sp - 208#64) 8 ∗
    cells (sp - 200#64) 1 ∗
    memRegion (sp - 192#64) 128 ∗
    cells (sp - 64#64) 8
  have hsub : sp - 208#64 - 16384#64 = sp - 16592#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_cells (sp - 200#64) 1 (by decide),
      ← ProofLib.memRegion_cells (sp - 64#64) 8 (by decide),
      ProofLib.memRegion_split' (b := sp - 16592#64) (n := 16384) (k := 208) (b' := sp - 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 208#64) (n := 8) (k := 200) (b' := sp - 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 200#64) (n := 8) (k := 192) (b' := sp - 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 192#64) (n := 128) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide)]

theorem stackAt_unchunkedRecvEk_restore (s0 : State) (w8 : BitVec 64) :
    stackAt (s0.sp - 208#64) extHookStack ∗
    memRegion (s0.sp - 208#64) 8 ∗
    ((s0.sp - 200#64) ↦₆₄ w8) ∗
    memRegion (s0.sp - 192#64) 128 ∗
    unchunkedRecvEkSavedCells s0 ⊢
    stackAt s0.sp unchunkedRecvEkStack := by
  have hw8 := ProofLib.pointsTo64_entails_memRegion (s0.sp - 200#64) w8
  have h8 := unchunkedRecvEkSavedCells_entails_memRegion_64 s0
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono hw8 (sepConj_mono_right h8)))) ?_
  change memRegion (s0.sp - 208#64 - 16384#64) 16384 ∗
      (memRegion (s0.sp - 208#64) 8 ∗ (memRegion (s0.sp - 200#64) 8 ∗
        (memRegion (s0.sp - 192#64) 128 ∗ memRegion (s0.sp - 64#64) 64))) ⊢
    memRegion (s0.sp - 16592#64) 16592
  have hsub : s0.sp - 208#64 - 16384#64 = s0.sp - 16592#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_split' (b := s0.sp - 192#64) (n := 128) (k := 64) (b' := s0.sp - 64#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 200#64) (n := 8) (k := 192) (b' := s0.sp - 192#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 208#64) (n := 8) (k := 200) (b' := s0.sp - 200#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 16592#64) (n := 16384) (k := 208) (b' := s0.sp - 208#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- Recombine `(dst ↦₆₄ cap) ∗ ((dst + 8#64) ↦₆₄ ptr) ∗ ((dst + 16#64) ↦₆₄ len) ∗ (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs`
    into `vecU8 A dst bs`. -/
theorem vecU8_of_slice_and_tail (A : RustAlloc) (dst cap ptr : BitVec 64) (bs : Bytes)
    (hle : bs.length ≤ cap.toNat) (hcap_lt : cap.toNat < 2 ^ 63) (hptr_ne : ptr ≠ 0#64) :
    (dst ↦₆₄ cap) ∗ ((dst + 8#64) ↦₆₄ ptr) ∗ ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs ⊢
    vecU8 A dst bs := by
  unfold vecU8 vecU8At vecHeader vecU8Tail
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [sepConj_left_comm (dst ↦₆₄ cap ∗ (dst + 8#64) ↦₆₄ ptr ∗ (dst + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)]
  refine Entails.pure_right ⟨hle, hcap_lt, hptr_ne⟩ ?_
  by_cases hc : cap = 0#64
  · subst hc
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs0
    simp only [beq_self_eq_true, ↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  · have hcb : (cap == 0#64) = false := beq_false_of_ne hc
    have hc0 : cap ≠ 0 := hc
    simp only [hc0, hcb, Bool.false_eq_true, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

/-! ## 3. Framed Call Rule for `validate_pk_bytes` (`0x78c18`) -/

/-- Framed call rule for `mlkemValidatePkSpec K` (`0x78c18`). -/
theorem call_validatePk {K : MlKem} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (mlkemValidatePkSpec K))
    (hdrPtr ekPtr : BitVec 64) (hdr ek : Bytes)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = hdrPtr)
    (hx1 : (s.readReg64 Reg.x1).toNat = hdr.length)
    (hx2 : s.readReg64 Reg.x2 = ekPtr)
    (hx3 : (s.readReg64 Reg.x3).toNat = ek.length)
    (hsplit : P = ((hdrPtr ↦ₛ hdr) ∗ (ekPtr ↦ₛ ek) ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      ((sf.readReg64 .x0).setWidth 8 = 0xff#8 ↔ K.validPkBytes hdr ek = true) →
      SepWP prog target_pc sf
        (((hdrPtr ↦ₛ hdr) ∗ (ekPtr ↦ₛ ek) ∗ stackAt sp_call extHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := ⟨hdrPtr, hdr, ekPtr, ek⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit] at hm
    dsimp only [mlkemValidatePkSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [mlkemValidatePkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hvalid, htr⟩ => ?_
    have hassoc :
        ((hdrPtr ↦ₛ hdr) ∗ ((ekPtr ↦ₛ ek) ∗ stackAt sp_call extHookStack)) ∗ Frame =
        ((hdrPtr ↦ₛ hdr) ∗ (ekPtr ↦ₛ ek) ∗ stackAt sp_call extHookStack) ∗ Frame := by ac_rfl
    rw [hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hvalid

/-! ## 4. Shared Epilogue Lemmas (`entry + 344#64` = `0x5dc18` and `entry + 316#64` = `0x5dbfc`) -/

theorem stackAt_unchunkedRecvEk_tail_split (sp : BitVec 64) :
    stackAt sp unchunkedRecvEkStack =
      memRegion (sp - 16592#64) 12496 ∗ stackAt sp allocHookStack := by
  change memRegion (sp - 16592#64) 16592 =
    memRegion (sp - 16592#64) 12496 ∗ memRegion (sp - 4096#64) 4096
  rw [ProofLib.memRegion_split' (b := sp - 16592#64) (n := 12496) (k := 4096) (b' := sp - 4096#64) rfl (by bv_omega) (by decide)]

/-- Address-independent heap body of `vecU8At A a cap ptr bs`. -/
@[expose] def vecU8Body (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) : SepProp :=
  ⌜ptr ≠ 0 ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
    if cap = 0 then emp
    else memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗ (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1

theorem vecU8_unfold_body (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Body A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader vecU8Body
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem vecU8_fold_body (A : RustAlloc) (a cap ptr : BitVec 64) (bs : Bytes) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    vecU8Body A cap ptr bs ⊢
    vecU8 A a bs := by
  unfold vecU8 vecU8At vecHeader vecU8Body
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem vecU8_unfold_body_24 (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A (a + 24#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a + 24#64) ↦₆₄ cap) ∗ ((a + 32#64) ↦₆₄ ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Body A cap ptr bs := by
  have h1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have h2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  simpa only [h1, h2] using vecU8_unfold_body A (a + 24#64) bs

theorem vecU8_unfold_body_48 (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A (a + 48#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((a + 48#64) ↦₆₄ cap) ∗ ((a + 56#64) ↦₆₄ ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs := by
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have h2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  simpa only [h1, h2] using vecU8_entails_slice_and_tail A (a + 48#64) bs

theorem vecU8_unfold_body_72 (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A (a + 72#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a + 72#64) ↦₆₄ cap) ∗ ((a + 80#64) ↦₆₄ ptr) ∗ ((a + 88#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Body A cap ptr bs := by
  have h1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have h2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  simpa only [h1, h2] using vecU8_unfold_body A (a + 72#64) bs

theorem vecU8_unfold_body_96 (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A (a + 96#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a + 96#64) ↦₆₄ cap) ∗ ((a + 104#64) ↦₆₄ ptr) ∗ ((a + 112#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Body A cap ptr bs := by
  have h1 : (a + 96#64) + 8#64 = a + 104#64 := by bv_omega
  have h2 : (a + 96#64) + 16#64 = a + 112#64 := by bv_omega
  simpa only [h1, h2] using vecU8_unfold_body A (a + 96#64) bs

theorem words3_entails_memRegion_24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  have heq :
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) =
      wordsAt a [w0, w1, w2] := by
    simp only [wordsAt, arm64_norm, sepConj_emp]
  rw [heq]
  exact wordsAt_entails_memRegion [w0, w1, w2] a 24 rfl

theorem words16_entails_memRegion_128 (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
    ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
    ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
    ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) ⊢
    memRegion a 128 := by
  have heq :
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
       ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
       ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
       ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15)) =
      wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] := by
    simp only [wordsAt_16, arm64_norm]
  rw [heq]
  exact wordsAt_entails_memRegion _ a 128 rfl

theorem words16_sub192_entails_memRegion_128
    (sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    ((sp - 192#64) ↦₆₄ w0) ∗ ((sp - 184#64) ↦₆₄ w1) ∗ ((sp - 176#64) ↦₆₄ w2) ∗ ((sp - 168#64) ↦₆₄ w3) ∗
    ((sp - 160#64) ↦₆₄ w4) ∗ ((sp - 152#64) ↦₆₄ w5) ∗ ((sp - 144#64) ↦₆₄ w6) ∗ ((sp - 136#64) ↦₆₄ w7) ∗
    ((sp - 128#64) ↦₆₄ w8) ∗ ((sp - 120#64) ↦₆₄ w9) ∗ ((sp - 112#64) ↦₆₄ w10) ∗ ((sp - 104#64) ↦₆₄ w11) ∗
    ((sp - 96#64) ↦₆₄ w12) ∗ ((sp - 88#64) ↦₆₄ w13) ∗ ((sp - 80#64) ↦₆₄ w14) ∗ ((sp - 72#64) ↦₆₄ w15) ⊢
    memRegion (sp - 192#64) 128 := by
  simpa only [arm64_norm] using
    words16_entails_memRegion_128 (sp - 192#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

theorem fold_unchunkedCt1SentEkReceivedAt (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (ek : Bytes)
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr : BitVec 64)
    (hek_le : ek.length ≤ ekCap.toNat) (hek_lt : ekCap.toNat < 2 ^ 63) (hek_ne : ekPtr ≠ 0#64) :
    (outA ↦₆₄ rkCap) ∗ ((outA + 8#64) ↦₆₄ rkPtr) ∗ ((outA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
    vecU8Body A rkCap rkPtr st.auth.rootKey ∗
    ((outA + 24#64) ↦₆₄ mkCap) ∗ ((outA + 32#64) ↦₆₄ mkPtr) ∗ ((outA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
    vecU8Body A mkCap mkPtr st.auth.macKey ∗
    ((outA + 48#64) ↦₆₄ esCap) ∗ ((outA + 56#64) ↦₆₄ esPtr) ∗ ((outA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
    vecU8Body A esCap esPtr st.es ∗
    ((outA + 72#64) ↦₆₄ ekCap) ∗ ((outA + 80#64) ↦₆₄ ekPtr) ∗ ((outA + 88#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
    (ekPtr ↦ₛ ek) ∗ vecU8Tail A ekCap ekPtr ek ∗
    ((outA + 96#64) ↦₆₄ ct1Cap) ∗ ((outA + 104#64) ↦₆₄ ct1Ptr) ∗ ((outA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
    vecU8Body A ct1Cap ct1Ptr st.ct1 ∗
    ((outA + 120#64) ↦₆₄ st.epoch) ⊢
    unchunkedCt1SentEkReceivedAt A outA
      { epoch := st.epoch, auth := st.auth, es := st.es, ek := ek, ct1 := st.ct1 } := by
  have hrk := vecU8_fold_body A outA rkCap rkPtr st.auth.rootKey
  have hmk :
      ((outA + 24#64) ↦₆₄ mkCap) ∗ ((outA + 32#64) ↦₆₄ mkPtr) ∗ ((outA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
      vecU8Body A mkCap mkPtr st.auth.macKey ⊢
      vecU8 A (outA + 24#64) st.auth.macKey := by
    have h1 : (outA + 24#64) + 8#64 = outA + 32#64 := by bv_omega
    have h2 : (outA + 24#64) + 16#64 = outA + 40#64 := by bv_omega
    simpa only [h1, h2] using vecU8_fold_body A (outA + 24#64) mkCap mkPtr st.auth.macKey
  have hes :
      ((outA + 48#64) ↦₆₄ esCap) ∗ ((outA + 56#64) ↦₆₄ esPtr) ∗ ((outA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
      vecU8Body A esCap esPtr st.es ⊢
      vecU8 A (outA + 48#64) st.es := by
    have h1 : (outA + 48#64) + 8#64 = outA + 56#64 := by bv_omega
    have h2 : (outA + 48#64) + 16#64 = outA + 64#64 := by bv_omega
    simpa only [h1, h2] using vecU8_fold_body A (outA + 48#64) esCap esPtr st.es
  have hek :
      ((outA + 72#64) ↦₆₄ ekCap) ∗ ((outA + 80#64) ↦₆₄ ekPtr) ∗ ((outA + 88#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
      (ekPtr ↦ₛ ek) ∗ vecU8Tail A ekCap ekPtr ek ⊢
      vecU8 A (outA + 72#64) ek := by
    have h1 : (outA + 72#64) + 8#64 = outA + 80#64 := by bv_omega
    have h2 : (outA + 72#64) + 16#64 = outA + 88#64 := by bv_omega
    simpa only [h1, h2] using vecU8_of_slice_and_tail A (outA + 72#64) ekCap ekPtr ek hek_le hek_lt hek_ne
  have hct1 :
      ((outA + 96#64) ↦₆₄ ct1Cap) ∗ ((outA + 104#64) ↦₆₄ ct1Ptr) ∗ ((outA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
      vecU8Body A ct1Cap ct1Ptr st.ct1 ⊢
      vecU8 A (outA + 96#64) st.ct1 := by
    have h1 : (outA + 96#64) + 8#64 = outA + 104#64 := by bv_omega
    have h2 : (outA + 96#64) + 16#64 = outA + 112#64 := by bv_omega
    simpa only [h1, h2] using vecU8_fold_body A (outA + 96#64) ct1Cap ct1Ptr st.ct1
  unfold unchunkedCt1SentEkReceivedAt
  change _ ⊢ (vecU8 A outA st.auth.rootKey ∗ vecU8 A (outA + 24#64) st.auth.macKey) ∗
    vecU8 A (outA + 48#64) st.es ∗ vecU8 A (outA + 72#64) ek ∗
    vecU8 A (outA + 96#64) st.ct1 ∗ ((outA + 120#64) ↦₆₄ st.epoch)
  rw [sepConj_assoc (vecU8 A outA st.auth.rootKey)]
  refine Entails.trans (Entails.of_eq (show _ =
    (((outA ↦₆₄ rkCap) ∗ ((outA + 8#64) ↦₆₄ rkPtr) ∗ ((outA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
      vecU8Body A rkCap rkPtr st.auth.rootKey) ∗
     (((outA + 24#64) ↦₆₄ mkCap) ∗ ((outA + 32#64) ↦₆₄ mkPtr) ∗ ((outA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
      vecU8Body A mkCap mkPtr st.auth.macKey) ∗
     (((outA + 48#64) ↦₆₄ esCap) ∗ ((outA + 56#64) ↦₆₄ esPtr) ∗ ((outA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
      vecU8Body A esCap esPtr st.es) ∗
     (((outA + 72#64) ↦₆₄ ekCap) ∗ ((outA + 80#64) ↦₆₄ ekPtr) ∗ ((outA + 88#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
      (ekPtr ↦ₛ ek) ∗ vecU8Tail A ekCap ekPtr ek) ∗
     (((outA + 96#64) ↦₆₄ ct1Cap) ∗ ((outA + 104#64) ↦₆₄ ct1Ptr) ∗ ((outA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
      vecU8Body A ct1Cap ct1Ptr st.ct1) ∗
     ((outA + 120#64) ↦₆₄ st.epoch)) by ac_rfl)) ?_
  exact sepConj_mono hrk (sepConj_mono hmk (sepConj_mono hes (sepConj_mono hek (sepConj_mono_left hct1))))

theorem memRegion_128_unfold_err (a : BitVec 64) :
    memRegion a 128 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ b8 : BitVec 8,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ b8) ∗ memRegion (a + 9#64) 119 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 120) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 119) (b' := a + 9#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono (cells_1_unfold a) (sepConj_mono_left (byte_1_unfold (a + 8#64)))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b8
  exact Entails.sepExists_right w0 (Entails.sepExists_right b8 (Entails.of_eq (by ac_rfl)))

theorem vecU8_entails_capPtr_dealloc_bound_24 (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A (a + 24#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        ((a + 24#64) ↦₆₄ cap) ∗ ((a + 32#64) ↦₆₄ ptr) ∗ memRegion (a + 40#64) 8 ∗
        vecCapPtrDealloc A cap ptr := by
  have h1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have h2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  simpa only [h1, h2] using vecU8_entails_capPtr_dealloc_bound A (a + 24#64) bs

theorem vecU8_entails_capPtr_dealloc_bound_72 (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A (a + 72#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        ((a + 72#64) ↦₆₄ cap) ∗ ((a + 80#64) ↦₆₄ ptr) ∗ memRegion (a + 88#64) 8 ∗
        vecCapPtrDealloc A cap ptr := by
  have h1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have h2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  simpa only [h1, h2] using vecU8_entails_capPtr_dealloc_bound A (a + 72#64) bs

theorem vecU8_entails_capPtr_dealloc_bound_96 (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A (a + 96#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        ((a + 96#64) ↦₆₄ cap) ∗ ((a + 104#64) ↦₆₄ ptr) ∗ memRegion (a + 112#64) 8 ∗
        vecCapPtrDealloc A cap ptr := by
  have h1 : (a + 96#64) + 8#64 = a + 104#64 := by bv_omega
  have h2 : (a + 96#64) + 16#64 = a + 112#64 := by bv_omega
  simpa only [h1, h2] using vecU8_entails_capPtr_dealloc_bound A (a + 96#64) bs

theorem fold_fiveVec128HeadersAt_err (stA : BitVec 64)
    (rkCap rkPtr mkCap mkPtr hdrCap hdrPtr hdrLen esCap esPtr ct1Cap ct1Ptr epoch : BitVec 64) :
    (stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗ memRegion (stA + 16#64) 8 ∗
    ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗ memRegion (stA + 40#64) 8 ∗
    ((stA + 48#64) ↦₆₄ hdrCap) ∗ ((stA + 56#64) ↦₆₄ hdrPtr) ∗ ((stA + 64#64) ↦₆₄ hdrLen) ∗
    ((stA + 72#64) ↦₆₄ esCap) ∗ ((stA + 80#64) ↦₆₄ esPtr) ∗ memRegion (stA + 88#64) 8 ∗
    ((stA + 96#64) ↦₆₄ ct1Cap) ∗ ((stA + 104#64) ↦₆₄ ct1Ptr) ∗ memRegion (stA + 112#64) 8 ∗
    ((stA + 120#64) ↦₆₄ epoch) ⊢
    fiveVec128HeadersAt stA
      ⟨⟨rkCap, rkPtr⟩, ⟨mkCap, mkPtr⟩, ⟨hdrCap, hdrPtr⟩, ⟨esCap, esPtr⟩, ⟨ct1Cap, ct1Ptr⟩⟩ := by
  unfold fiveVec128HeadersAt; dsimp only
  have h64 := ProofLib.pointsTo64_entails_memRegion (stA + 64#64) hdrLen
  have h120 := ProofLib.pointsTo64_entails_memRegion (stA + 120#64) epoch
  have h112 : memRegion (stA + 112#64) 8 ∗ memRegion (stA + 120#64) 8 = memRegion (stA + 112#64) 16 := by
    rw [← ProofLib.memRegion_split' (b := stA + 112#64) (n := 8) (k := 8) (b' := stA + 120#64) rfl (by bv_omega) (by decide)]
  rw [← h112]
  refine Entails.trans (Entails.of_eq (show _ =
    (((stA + 64#64) ↦₆₄ hdrLen) ∗ ((stA + 120#64) ↦₆₄ epoch) ∗
     ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗ memRegion (stA + 16#64) 8 ∗
      ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗ memRegion (stA + 40#64) 8 ∗
      ((stA + 48#64) ↦₆₄ hdrCap) ∗ ((stA + 56#64) ↦₆₄ hdrPtr) ∗
      ((stA + 72#64) ↦₆₄ esCap) ∗ ((stA + 80#64) ↦₆₄ esPtr) ∗ memRegion (stA + 88#64) 8 ∗
      ((stA + 96#64) ↦₆₄ ct1Cap) ∗ ((stA + 104#64) ↦₆₄ ct1Ptr) ∗ memRegion (stA + 112#64) 8)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h64 (sepConj_mono_left h120)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem stackAt_sub208_extHook_split (sp : BitVec 64) :
    stackAt (sp - 208#64) extHookStack =
      memRegion (sp - 16592#64) 12288 ∗ stackAt (sp - 208#64) allocHookStack := by
  change memRegion (sp - 208#64 - 16384#64) 16384 =
    memRegion (sp - 16592#64) 12288 ∗ memRegion (sp - 208#64 - 4096#64) 4096
  have h1 : sp - 208#64 - 16384#64 = sp - 16592#64 := by bv_omega
  rw [h1, ProofLib.memRegion_split' (b := sp - 16592#64) (n := 12288) (k := 4096)
    (b' := sp - 208#64 - 4096#64) rfl (by bv_omega) (by decide)]

@[expose] def errBranchFrame (A : RustAlloc) {F : ShaCompress} (outA ekA : BitVec 64)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (s0 : State) (w8 : BitVec 64) : SepProp :=
  unchunkedCt1SentRecvEkResAt A outA res ∗ memRegion ekA 24 ∗
  memRegion (s0.sp - 16592#64) 12288 ∗ memRegion (s0.sp - 208#64) 8 ∗
  ((s0.sp - 200#64) ↦₆₄ w8) ∗ memRegion (s0.sp - 192#64) 128 ∗ unchunkedRecvEkSavedCells s0

@[expose, reducible]
def ErrBranchPreserved (s0 s : State) (stA hdrPtr : BitVec 64) : Prop :=
  s.sp = s0.sp - 208#64 ∧ s.readReg64 .x19 = stA ∧ s.readReg64 .x20 = hdrPtr ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem sepWP_post_bridge {prog : Program} {ret : BitVec 64} {s0 s : State} {P : SepProp}
    {Q : State → SepProp} {R : SepProp}
    (h : SepWP prog ret s P (fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ Q sf))) :
    SepWP prog ret s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  unfold SepWP at h ⊢
  intro R' hm
  refine reaches_pc_mono (h R' hm) ?_
  intro sf _ _ ⟨P_f, hmf, hsp, hcs, hent⟩
  exact ⟨P_f, hmf, fun hmR => Satisfies.mono (sepConj_mono_left hent) hmR, hsp, hcs⟩

end CryptoVerification.SpqrV1.States.Leaves
