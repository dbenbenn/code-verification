/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderRepr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase

/-!
# Shared Base for 48-Byte `prost::encoding::message::encode` Monomorphizations

Defines symbol names, 48-byte stack-frame layouts, callee wrappers, and `Vec<Vec<u8>>` slice
decompositions shared across `prost::encoding::message::encode::<M, alloc::vec::Vec<u8>>`
for `PolynomialEncoder`, `ChainParams`, `PolynomialDecoder`, and `EpochDirection`.
-/

public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Auth

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Symbol Names & Offsets -/

abbrev encodePolyEncoder1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#1]"

abbrev encodePolyEncoder2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"

abbrev encodeChainParams1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#1]"

abbrev encodeChainParams2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#2]"

abbrev encodePolyDecoder1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#1]"

abbrev encodePolyDecoder2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#2]"

abbrev encodeEpochDirection1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]"

abbrev encodeEpochDirection2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#2]"

theorem cap_toNat_eq_of_beq {cap : BitVec 64} {n : Nat} (hn : n < 2 ^ 64)
    (h : (cap == BitVec.ofNat 64 n) = true) : cap.toNat = n := by
  have heq : cap = BitVec.ofNat 64 n := beq_iff_eq.mp h
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem lt_cap_toNat_of_beq_false {cap : BitVec 64} {n : Nat}
    (hle : n ≤ cap.toNat) (h : (cap == BitVec.ofNat 64 n) = false) :
    n < cap.toNat := by
  have hne : cap.toNat ≠ n := by
    intro heq
    apply Bool.eq_false_iff.mp h
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), heq]
  omega

theorem reserveCap_one_bounds {cap : BitVec 64} {n : Nat} (hcap : cap.toNat = n)
    (hfit : n + 10 < 2 ^ 62) :
    n + 1 ≤ reserveCap cap.toNat n 1 ∧
      reserveCap cap.toNat n 1 + 1 ≤ 2 ^ 63 ∧
      cap.toNat ≤ reserveCap cap.toNat n 1 ∧
      (BitVec.ofNat 64 (reserveCap cap.toNat n 1)).toNat = reserveCap cap.toNat n 1 := by
  refine ⟨by dsimp [reserveCap]; omega, by dsimp [reserveCap]; omega, by dsimp [reserveCap]; omega, ?_⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [reserveCap]; omega)]

theorem protoEncodeKey_varint_1 :
    Proto.encodeKey 1#32 .varint = [8#8] := by decide

theorem protoEncodeKey_varint_2 :
    Proto.encodeKey 2#32 .varint = [16#8] := by decide

theorem protoEncodeKey_varint_4 :
    Proto.encodeKey 4#32 .varint = [32#8] := by decide

theorem protoEncodeKey_lengthDelimited_2 :
    Proto.encodeKey 2#32 .lengthDelimited = [18#8] := by decide

theorem protoEncodeKey_lengthDelimited_3 :
    Proto.encodeKey 3#32 .lengthDelimited = [26#8] := by decide

theorem protoEncodeUint32Field_zero (tag : BitVec 32) :
    Proto.encodeUint32Field tag 0#32 = [] := by
  simp [Proto.encodeUint32Field]

theorem protoEncodeUint32Field_1_of_ne_zero {v : BitVec 32} (h : v ≠ 0#32) :
    Proto.encodeUint32Field 1#32 v = [8#8] ++ LibsignalProtoCodec.encodeVarint (v.zeroExtend 64) := by
  have hbeq : (v == 0#32) = false := beq_false_of_ne h
  simp only [Proto.encodeUint32Field, hbeq, Bool.false_eq_true, ↓reduceIte,
    protoEncodeKey_varint_1, protoEncodeVarint_eq_codec]

theorem protoEncodeUint32Field_2_of_ne_zero {v : BitVec 32} (h : v ≠ 0#32) :
    Proto.encodeUint32Field 2#32 v = [16#8] ++ LibsignalProtoCodec.encodeVarint (v.zeroExtend 64) := by
  have hbeq : (v == 0#32) = false := beq_false_of_ne h
  simp only [Proto.encodeUint32Field, hbeq, Bool.false_eq_true, ↓reduceIte,
    protoEncodeKey_varint_2, protoEncodeVarint_eq_codec]

theorem protoEncodeBoolField_4_false :
    Proto.encodeBoolField 4#32 false = [] := rfl

theorem protoEncodeBoolField_4_true :
    Proto.encodeBoolField 4#32 true = [32#8, 1#8] := by decide

theorem orr_lsl3_two_eq_encodeKey_lengthDelimited (tag : BitVec 32) :
    LibsignalProtoCodec.encodeVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64) =
      Proto.encodeKey tag .lengthDelimited := by
  simp only [Proto.encodeKey, Proto.WireType.toU32, protoEncodeVarint_eq_codec]
  congr 1
  rw [BitVec.or_comm]

/-! ## 48-Byte Stack Frame (`0x30` B) for `ChainParams`, `PolyEncoder`, `PolyDecoder` -/

/-- Total stack budget for 48-byte `message::encode` functions that only call `encode_varint` /
`do_reserve_and_handle`: `48 + (0x30 + resStack)`. -/
abbrev msgEnc48VarintStackOf (resStack : Nat) : Nat :=
  48 + (0x30 + resStack)

/-- Total stack budget for 48-byte `message::encode` functions that call `encode_repeated`:
`48 + encodeRepeatedStackOf resStack`. -/
abbrev msgEnc48RepeatedStackOf (resStack : Nat) : Nat :=
  48 + encodeRepeatedStackOf resStack

/-- Saved register frame at `[sp - 48, sp)` after prologue of a 48-byte `message::encode`
(`stp x29, x30, [sp, #-0x30]!`, `str x21, [sp, #0x10]`, `stp x20, x19, [sp, #0x20]`). -/
@[expose] def msgEnc48SavedFrame (sp fp lr r21 v3 r20 r19 : BitVec 64) : SepProp :=
  ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
    ((sp - 32#64) ↦₆₄ r21) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
    ((sp - 16#64) ↦₆₄ r20) ∗ ((sp - 8#64) ↦₆₄ r19)

theorem stackAt_msgEnc48_varint {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (msgEnc48VarintStackOf resStack) =
      stackAt (sp - 48#64) (0x30 + resStack) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
         ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
          ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
          ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
  have h1 := ProofLib.stackAt_split_cells sp (0x30 + resStack) 6 (by omega)
  have heq : 0x30 + resStack + 8 * 6 = msgEnc48VarintStackOf resStack := by
    dsimp [msgEnc48VarintStackOf]; omega
  rw [heq] at h1
  have hc6 : cells (sp - 48#64) 6 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
    cells_unfold
  rw [h1, hc6]

theorem stackAt_msgEnc48_repeated {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (msgEnc48RepeatedStackOf resStack) =
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
         ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
          ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
          ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
  have h1 := ProofLib.stackAt_split_cells sp (encodeRepeatedStackOf resStack) 6
    (by dsimp [encodeRepeatedStackOf]; omega)
  have heq : encodeRepeatedStackOf resStack + 8 * 6 = msgEnc48RepeatedStackOf resStack := by
    dsimp [msgEnc48RepeatedStackOf]; omega
  rw [heq] at h1
  have hc6 : cells (sp - 48#64) 6 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
    cells_unfold
  rw [h1, hc6]

/-- Split `stackAt sp (encodeRepeatedStackOf resStack)` (`80 + (0x30 + resStack)`) into
`memRegion (sp - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ stackAt sp (0x30 + resStack)`. -/
theorem stackAt_encodeRepeated_eq_varint {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (encodeRepeatedStackOf resStack) =
      memRegion (sp - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
        stackAt sp (0x30 + resStack) := by
  have h := ProofLib.stackAt_split_bottom sp (0x30 + resStack) 80 (by omega)
  have heq : (0x30 + resStack) + 80 = encodeRepeatedStackOf resStack := by
    dsimp [encodeRepeatedStackOf]; omega
  simpa only [heq] using h

/-- Split `stackAt sp (0x30 + resStack)` into
`memRegion (sp - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗ stackAt sp 16`. -/
theorem stackAt_varint_eq_stack16 {resStack : Nat} (hres : resStack + 48 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (0x30 + resStack) =
      memRegion (sp - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗
        stackAt sp 16 := by
  have h := ProofLib.stackAt_split_bottom sp 16 (32 + resStack) (by omega)
  have heq : 16 + (32 + resStack) = 0x30 + resStack := by omega
  simpa only [heq] using h

/-- Callee-saved registers `x22..x28` untouched by 48-byte `message::encode` (`x19..x21, fp, lr`
are saved on stack), together with `StepInv s0 s`. -/
@[expose] def MsgEnc48CalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem MsgEnc48CalleeSaved.refl (s0 : State) : MsgEnc48CalleeSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, StepInv.refl s0⟩

theorem MsgEnc48CalleeSaved.trans {s0 s1 s2 : State}
    (h01 : MsgEnc48CalleeSaved s0 s1) (h12 : MsgEnc48CalleeSaved s1 s2) :
    MsgEnc48CalleeSaved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
    h01.2.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2.2⟩

theorem MsgEnc48CalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : MsgEnc48CalleeSaved s1 s2 :=
  ⟨hcs.2.2.2.1, hcs.2.2.2.2.1, hcs.2.2.2.2.2.1, hcs.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem MsgEnc48CalleeSaved.step {s0 s1 s2 : State}
    (h01 : MsgEnc48CalleeSaved s0 s1)
    (hx22 : s2.readReg64 (Reg.gpr 22#5) = s1.readReg64 (Reg.gpr 22#5))
    (hx23 : s2.readReg64 (Reg.gpr 23#5) = s1.readReg64 (Reg.gpr 23#5))
    (hx24 : s2.readReg64 (Reg.gpr 24#5) = s1.readReg64 (Reg.gpr 24#5))
    (hx25 : s2.readReg64 (Reg.gpr 25#5) = s1.readReg64 (Reg.gpr 25#5))
    (hx26 : s2.readReg64 (Reg.gpr 26#5) = s1.readReg64 (Reg.gpr 26#5))
    (hx27 : s2.readReg64 (Reg.gpr 27#5) = s1.readReg64 (Reg.gpr 27#5))
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInv s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm, calleeSavedVRegs_setPC]) :
    MsgEnc48CalleeSaved s0 s2 :=
  h01.trans ⟨hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs, hinv⟩

attribute [arm64_norm, wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

/-- Wrap a `Spec α` with `⌜MsgEnc48CalleeSaved s0 s⌝` in the precondition. -/
@[expose] def withMsgEnc48CS {α : Type} (s0 : State) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜MsgEnc48CalleeSaved s0 s⌝ ∗ spec.pre x s }

theorem subroutine_ok_withMsgEnc48CS_ext {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withMsgEnc48CS s0 spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s hpc hrun hpre hsp
  rw [withMsgEnc48CS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact (h.to_outcome x R s hpc hrun hpre.2 hsp).mono_outcome fun _ hout => hout

/-- Standard panic postcondition for `message::encode` functions. -/
@[expose] def msgEncOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem stackAt_msgEnc48_varint_eq_bottom {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (msgEnc48VarintStackOf resStack) =
      memRegion (sp - BitVec.ofNat 64 (msgEnc48VarintStackOf resStack)) 48 ∗
        stackAt sp (0x30 + resStack) := by
  have h := ProofLib.stackAt_split_bottom sp (0x30 + resStack) 48 (by omega)
  have heq : (0x30 + resStack) + 48 = msgEnc48VarintStackOf resStack := by
    dsimp [msgEnc48VarintStackOf]; omega
  simpa only [heq] using h

theorem stackAt_msgEnc48_repeated_eq_bottom {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (msgEnc48RepeatedStackOf resStack) =
      memRegion (sp - BitVec.ofNat 64 (msgEnc48RepeatedStackOf resStack)) 48 ∗
        stackAt sp (encodeRepeatedStackOf resStack) := by
  have h := ProofLib.stackAt_split_bottom sp (encodeRepeatedStackOf resStack) 48
    (by dsimp [encodeRepeatedStackOf]; omega)
  have heq : encodeRepeatedStackOf resStack + 48 = msgEnc48RepeatedStackOf resStack := by
    dsimp [msgEnc48RepeatedStackOf]; omega
  simpa only [heq] using h

theorem msgEnc48SavedFrame_entails_cells (sp fp lr r21 v3 r20 r19 : BitVec 64) :
    msgEnc48SavedFrame sp fp lr r21 v3 r20 r19 ⊢
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) :=
  Entails.sepExists_right fp
    (Entails.sepExists_right lr
      (Entails.sepExists_right r21
        (Entails.sepExists_right v3
          (Entails.sepExists_right r20
            (Entails.sepExists_right r19 (Entails.refl _))))))

theorem stackAt_msgEnc48_varint_recombine {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (sp fp lr r21 v3 r20 r19 : BitVec 64) :
    stackAt (sp - 48#64) (0x30 + resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19 ⊢
      stackAt sp (msgEnc48VarintStackOf resStack) := by
  rw [stackAt_msgEnc48_varint hres sp]
  exact sepConj_mono_right (msgEnc48SavedFrame_entails_cells sp fp lr r21 v3 r20 r19)

theorem stackAt_msgEnc48_repeated_recombine {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp fp lr r21 v3 r20 r19 : BitVec 64) :
    stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19 ⊢
      stackAt sp (msgEnc48RepeatedStackOf resStack) := by
  rw [stackAt_msgEnc48_repeated hres sp]
  exact sepConj_mono_right (msgEnc48SavedFrame_entails_cells sp fp lr r21 v3 r20 r19)

theorem vecU8At_eq_repeatedBytesElemAt_uncond (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      repeatedBytesElemAt a ptr bs ∗ Varint.vecU8ElemRestAt A a cap ptr bs := by
  by_cases hcap : cap = 0
  · subst hcap
    unfold vecU8At vecHeader repeatedBytesElemAt Varint.vecU8ElemRestAt
    simp only [↓reduceIte, sepConj_emp]
    have hcongr :
        (⌜bs.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ : SepProp) =
        ⌜bs.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ (ptr ↦ₛ bs) := by
      refine (sepConj_emp _).symm.trans (pure_sepConj_congr fun ⟨hle, _, _⟩ => ?_)
      have hbs : bs = [] := by
        cases bs with
        | nil => rfl
        | cons _ _ =>
          have h0 : (0 : BitVec 64).toNat = 0 := rfl
          rw [h0, List.length_cons] at hle; omega
      rw [hbs, pointsToBytes_nil]
    conv_lhs => rw [hcongr]
    ac_rfl
  · exact Varint.vecU8At_eq_repeatedBytesElemAt A a cap ptr bs (fun h => absurd h hcap)

/-- Remaining ownership of a `Vec<u8>` element at `addr` after extracting `repeatedBytesElemAt addr ptr bs`. -/
@[expose] def vecU8ElemRestAt (A : RustAlloc) (addr ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, Varint.vecU8ElemRestAt A addr cap ptr bs

/-- Remaining ownership of a `Vec<Vec<u8>>` slice at `base` after extracting `repeatedBytesSliceAt base elems`. -/
@[expose] def vecU8SliceRestAt (A : RustAlloc) (base : BitVec 64) :
    List (BitVec 64 × List (BitVec 8)) → SepProp
  | [] => emp
  | (ptr, bs) :: rest =>
      vecU8ElemRestAt A base ptr bs ∗ vecU8SliceRestAt A (base + 24#64) rest

theorem satisfies_vecU8_iff_repeatedBytesElemAt (A : RustAlloc) (addr : BitVec 64)
    (bs : List (BitVec 8)) (R : SepProp) (m : Memory) :
    (m ⊨ vecU8 A addr bs ∗ R) ↔
    ∃ ptr : BitVec 64, m ⊨ (repeatedBytesElemAt addr ptr bs ∗ vecU8ElemRestAt A addr ptr bs) ∗ R := by
  dsimp only [vecU8, vecU8ElemRestAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  constructor
  · rintro ⟨cap, ptr, hm⟩
    rw [vecU8At_eq_repeatedBytesElemAt_uncond A addr cap ptr bs] at hm
    exact ⟨ptr, cap, by convert hm using 1; try ac_rfl⟩
  · rintro ⟨ptr, cap, hm⟩
    refine ⟨cap, ptr, ?_⟩
    rw [vecU8At_eq_repeatedBytesElemAt_uncond A addr cap ptr bs]
    convert hm using 1; try ac_rfl

theorem satisfies_arrayAt_vecU8_iff_repeatedBytesSliceAt (A : RustAlloc) :
    ∀ (bss : List (List (BitVec 8))) (base : BitVec 64) (R : SepProp) (m : Memory),
      (m ⊨ arrayAt (fun bs addr => vecU8 A addr bs) 24 base bss ∗ R) ↔
      ∃ elems : List (BitVec 64 × List (BitVec 8)),
        elems.map Prod.snd = bss ∧
        (m ⊨ (repeatedBytesSliceAt base elems ∗ vecU8SliceRestAt A base elems) ∗ R)
  | [], base, R, m => by
      dsimp only [arrayAt]
      constructor
      · intro hm
        refine ⟨[], rfl, ?_⟩
        dsimp only [repeatedBytesSliceAt, vecU8SliceRestAt]
        rwa [emp_sepConj]
      · rintro ⟨elems, heq, hm⟩
        cases elems with
        | nil =>
            dsimp only [repeatedBytesSliceAt, vecU8SliceRestAt] at hm
            rwa [emp_sepConj] at hm
        | cons _ _ => cases heq
  | bs :: rest, base, R, m => by
      have h24 : (BitVec.ofNat 64 24 : BitVec 64) = 24#64 := rfl
      dsimp only [arrayAt]
      rw [h24, sepConj_assoc, satisfies_vecU8_iff_repeatedBytesElemAt]
      constructor
      · rintro ⟨ptr, hm⟩
        have hm' : m ⊨ arrayAt (fun bs addr => vecU8 A addr bs) 24 (base + 24#64) rest ∗
            ((repeatedBytesElemAt base ptr bs ∗ vecU8ElemRestAt A base ptr bs) ∗ R) := by
          convert hm using 1; ac_rfl
        obtain ⟨elems, heq, hm''⟩ :=
          (satisfies_arrayAt_vecU8_iff_repeatedBytesSliceAt A rest (base + 24#64) _ m).mp hm'
        refine ⟨(ptr, bs) :: elems, congrArg (bs :: ·) heq, ?_⟩
        dsimp only [repeatedBytesSliceAt, vecU8SliceRestAt]
        convert hm'' using 1; ac_rfl
      · rintro ⟨elems_all, heq, hm⟩
        cases elems_all with
        | nil => cases heq
        | cons hd tl =>
            rcases hd with ⟨ptr, bs'⟩
            dsimp only [List.map] at heq
            injection heq with hbs htl
            subst bs'
            dsimp only [repeatedBytesSliceAt, vecU8SliceRestAt] at hm
            refine ⟨ptr, ?_⟩
            have hm' : m ⊨ (repeatedBytesSliceAt (base + 24#64) tl ∗ vecU8SliceRestAt A (base + 24#64) tl) ∗
                ((repeatedBytesElemAt base ptr bs ∗ vecU8ElemRestAt A base ptr bs) ∗ R) := by
              convert hm using 1; ac_rfl
            have hm'' :=
              (satisfies_arrayAt_vecU8_iff_repeatedBytesSliceAt A rest (base + 24#64) _ m).mpr
                ⟨tl, htl, hm'⟩
            convert hm'' using 1; ac_rfl

/-- Full remaining ownership of `Poly.vecVecU8PinnedAt A pin v bss` after extracting
`(v ↦₆₄ pin.cap) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
 repeatedBytesSliceAt pin.ptr elems`. -/
@[expose] def vecVecU8PinnedRestAt (A : RustAlloc) (pin : LibsignalSessionRepr.VecPin)
    (elems : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  let bss := elems.map Prod.snd
  ⌜bss.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
  vecU8SliceRestAt A pin.ptr elems ∗
  (if pin.cap = 0 then emp
   else A.live pin.ptr (pin.cap.toNat * 24) 8 ∗
     memRegion (pin.ptr + BitVec.ofNat 64 (bss.length * 24)) ((pin.cap.toNat - bss.length) * 24))

theorem satisfies_vecVecU8PinnedAt_iff (A : RustAlloc) (pin : LibsignalSessionRepr.VecPin)
    (v : BitVec 64) (bss : List (List (BitVec 8))) (R : SepProp) (m : Memory) :
    (m ⊨ Poly.vecVecU8PinnedAt A pin v bss ∗ R) ↔
    ∃ elems : List (BitVec 64 × List (BitVec 8)),
      elems.map Prod.snd = bss ∧ bss.length * 24 < 2 ^ 63 ∧
      (m ⊨ ((v ↦₆₄ pin.cap) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
        repeatedBytesSliceAt pin.ptr elems ∗
        vecVecU8PinnedRestAt A pin elems) ∗ R) := by
  dsimp only [Poly.vecVecU8PinnedAt, vecAt, vecHeader, vecBuf, vecHeaderBytes]
  by_cases h0 : pin.cap = 0
  · simp only [h0, ↓reduceIte]
    constructor
    · intro hm
      have hm_p : m ⊨ ⌜bss.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          ((v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗ emp ∗ R) := by
        convert hm using 1; ac_rfl
      rw [satisfies_pure_sepConj] at hm_p
      obtain ⟨⟨hle, hlt, hne⟩, hm1⟩ := hm_p
      have hbss : bss = [] := by
        cases bss with
        | nil => rfl
        | cons _ _ =>
          have hz : (0 : BitVec 64).toNat = 0 := rfl
          rw [hz, List.length_cons] at hle; omega
      subst hbss
      refine ⟨[], rfl, by decide, ?_⟩
      dsimp only [vecVecU8PinnedRestAt, List.map, List.length, repeatedBytesSliceAt, vecU8SliceRestAt]
      simp only [h0, ↓reduceIte]
      have hp : (0 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0) = True :=
        eq_true ⟨hle, hlt, hne⟩
      simp only [hp, pure_true, emp_sepConj, sepConj_emp] at hm1 ⊢
      convert hm1 using 1; ac_rfl
    · rintro ⟨elems, heq, _, hm⟩
      dsimp only [vecVecU8PinnedRestAt] at hm
      simp only [h0, ↓reduceIte, heq] at hm
      have hm_p : m ⊨ ⌜bss.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          ((v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
            repeatedBytesSliceAt pin.ptr elems ∗ vecU8SliceRestAt A pin.ptr elems ∗ emp ∗ R) := by
        convert hm using 1; ac_rfl
      rw [satisfies_pure_sepConj] at hm_p
      obtain ⟨⟨hle, hlt, hne⟩, hm1⟩ := hm_p
      have hbss : bss = [] := by
        cases bss with
        | nil => rfl
        | cons _ _ =>
          have hz : (0 : BitVec 64).toNat = 0 := rfl
          rw [hz, List.length_cons] at hle; omega
      subst hbss
      cases elems with
      | nil =>
          dsimp only [repeatedBytesSliceAt, vecU8SliceRestAt] at hm1
          have hp : (([] : List (List (BitVec 8))).length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0) = True :=
            eq_true ⟨hle, hlt, hne⟩
          simp only [hp, pure_true, emp_sepConj, sepConj_emp] at hm1 ⊢
          convert hm1 using 1; ac_rfl
      | cons _ _ => cases heq
  · simp only [h0, ↓reduceIte]
    constructor
    · intro hm
      have hm_p : m ⊨ ⌜bss.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          (arrayAt (fun bs addr => vecU8 A addr bs) 24 pin.ptr bss ∗
            ((v ↦₆₄ pin.cap) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗
              ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              A.live pin.ptr (pin.cap.toNat * 24) 8 ∗
              memRegion (pin.ptr + BitVec.ofNat 64 (bss.length * 24)) ((pin.cap.toNat - bss.length) * 24) ∗ R)) := by
        convert hm using 1; ac_rfl
      rw [satisfies_pure_sepConj] at hm_p
      obtain ⟨⟨hle, hlt, hne⟩, hm2⟩ := hm_p
      have hbss24 : bss.length * 24 < 2 ^ 63 := by omega
      obtain ⟨elems, heq, hm3⟩ :=
        (satisfies_arrayAt_vecU8_iff_repeatedBytesSliceAt A bss pin.ptr _ m).mp hm2
      refine ⟨elems, heq, hbss24, ?_⟩
      dsimp only [vecVecU8PinnedRestAt]
      simp only [h0, ↓reduceIte, heq]
      have hp : (bss.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0) = True :=
        eq_true ⟨hle, hlt, hne⟩
      simp only [hp, pure_true, emp_sepConj]
      convert hm3 using 1; ac_rfl
    · rintro ⟨elems, heq, _, hm⟩
      dsimp only [vecVecU8PinnedRestAt] at hm
      simp only [h0, ↓reduceIte, heq] at hm
      have hm_p : m ⊨ ⌜bss.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          ((repeatedBytesSliceAt pin.ptr elems ∗ vecU8SliceRestAt A pin.ptr elems) ∗
            ((v ↦₆₄ pin.cap) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗
              ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              A.live pin.ptr (pin.cap.toNat * 24) 8 ∗
              memRegion (pin.ptr + BitVec.ofNat 64 (bss.length * 24)) ((pin.cap.toNat - bss.length) * 24) ∗ R)) := by
        convert hm using 1; ac_rfl
      rw [satisfies_pure_sepConj] at hm_p
      obtain ⟨⟨hle, hlt, hne⟩, hm2⟩ := hm_p
      have hm3 :=
        (satisfies_arrayAt_vecU8_iff_repeatedBytesSliceAt A bss pin.ptr _ m).mpr ⟨elems, heq, hm2⟩
      have hp : (bss.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0) = True :=
        eq_true ⟨hle, hlt, hne⟩
      simp only [hp, pure_true, emp_sepConj]
      convert hm3 using 1; ac_rfl

end CryptoVerification.SpqrV1.Prost.MessageEncode

