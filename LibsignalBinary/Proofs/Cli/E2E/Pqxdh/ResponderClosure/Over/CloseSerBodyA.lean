/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `SessionRecord::serialize` with One Previous Session: Field-2 Proof

Proves `serField2_step : SerField2StepStmt img A ext` (`+444 .. +692`), encoding `previous_sessions`
field 2 (`0x12`, varint length, and raw `enc` bytes) from `DoReserveOkX` and `EncodeVarintOkX`.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux
open Proofs.libsignal.Hooks2

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
  vecRest vecU8Buf vecSrcRest vecCopyDone
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Instruction decodes (`+444 .. +664`) -/

theorem sf2_sp_aligned {sp0 : BitVec 64} {s : State}
    (hsp0 : sp0 &&& 15#64 = 0#64) (hsp : s.sp = sp0 - 800#64) :
    s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hsp0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem SerField2Saved.refl (s : State) : SerField2Saved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SerField2Saved.trans {s0 s1 s2 : State}
    (h1 : SerField2Saved s0 s1) (h2 : SerField2Saved s1 s2) : SerField2Saved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.trans h1.2.2.2.2.2⟩

theorem SerField2Saved.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) : SerField2Saved s1 s2 := by
  unfold SerField2Saved
  reg_chain

theorem sf2_lt_of_ofNat {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem sf2_cap_beq_len_false {cap : BitVec 64} {n : Nat} (hlt : n < cap.toNat) :
    (cap == BitVec.ofNat 64 n) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  have hn : n < 2 ^ 64 := Nat.lt_trans hlt cap.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h1
  omega

theorem sf2_cap_eq_ofNat_len {cap : BitVec 64} {n : Nat} (heq : cap.toNat = n) :
    cap = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (heq ▸ cap.isLt)]

theorem sf2_lenField_two (enc : List (BitVec 8)) :
    CryptoVerification.E2E.Record.lenField 2 enc =
      [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length) ++ enc := by
  unfold CryptoVerification.E2E.Record.lenField
  rfl

/-! ## Frame-specialized callee steps -/

theorem sf2_off8 (sp0 : BitVec 64) : sp0 - 432#64 + 8#64 = sp0 - 424#64 :=
  bv_sub_add_lit sp0 432 8

theorem sf2_off16 (sp0 : BitVec 64) : sp0 - 432#64 + 16#64 = sp0 - 416#64 :=
  bv_sub_add_lit sp0 432 16

theorem sf2_vec432_eq (A : RustAlloc) (sp0 cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (sp0 - 432#64) cap ptr bs =
      ((sp0 - 432#64) ↦₆₄ cap) ∗ ((sp0 - 424#64) ↦₆₄ ptr) ∗
        ((sp0 - 416#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf, ← sf2_off8, ← sf2_off16]
  simp only [vecHeader, sepConj_assoc]

theorem sf2_vec432_open_one (A : RustAlloc) (sp0 cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) :
    vecU8At A (sp0 - 432#64) cap ptr bs =
      ∃∗ y : BitVec 8,
        ((sp0 - 432#64) ↦₆₄ cap) ∗ ((sp0 - 424#64) ↦₆₄ ptr) ∗
        ((sp0 - 416#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗ vecRest A cap ptr bs := by
  rw [vecU8At_open_one A (sp0 - 432#64) cap ptr bs hlt, sf2_off8, sf2_off16]

theorem sf2_vec432_close_one (A : RustAlloc) (sp0 cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) (R : SepProp) :
    ((sp0 - 432#64) ↦₆₄ cap) ∗ ((sp0 - 424#64) ↦₆₄ ptr) ∗
      ((sp0 - 416#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗ vecRest A cap ptr bs ∗ R =
      vecU8At A (sp0 - 432#64) cap ptr (bs ++ [byte]) ∗ R := by
  rw [← vecU8At_close_one A (sp0 - 432#64) cap ptr bs byte hlt R, sf2_off8, sf2_off16]

theorem sf2_vec432_slice_eq (A : RustAlloc) (sp0 cap ptr : BitVec 64)
    (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hne : payload ≠ []) :
    vecU8At A (sp0 - 432#64) cap ptr (bs ++ payload) =
      ((sp0 - 432#64) ↦₆₄ cap) ∗ ((sp0 - 424#64) ↦₆₄ ptr) ∗
        ((sp0 - 416#64) ↦₆₄ (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)) ∗
        vecCopyDone A cap ptr bs payload := by
  have h := vecU8At_close_slice A (sp0 - 432#64) cap ptr bs payload hle hcap hptr hne emp
  simp only [sepConj_emp] at h
  rw [sf2_off8, sf2_off16] at h
  exact h.symm

/-! ## Payload copy and loop exit (`+472 .. +692`) -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
