/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::try_from`: Prologue and Early-Error Branches (`+0x000..+0x0f4`)

Symbolic execution of the prologue on `contractProg img.base ext`: empty input (`+0x04c`),
legacy/unrecognized version (`+0x060..+0x07c`), stack-frame initialization (`+0x080..+0x0b8`),
1-byte empty-body error (`+0x0bc → +0x504`), and non-empty decode-loop entry (`+0x0bc → +0x0f4`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
  bv_sub_add_lit' bv_sub_sub_lit
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
open CryptoVerification.SignalSession.Cli
open RunProofs.Pksm

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

attribute [local irreducible] Program.fetch Program.externAt?

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Layout-Independent Fetch Macro -/

private theorem pl_bv_sub_add_lit (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b =
      x - (BitVec.ofNat 64 a - BitVec.ofNat 64 b) := by bv_omega

private theorem pl_bv_sub_add_lit' (x : BitVec 64) (a b : BitVec 64) :
    x - a + b = x - (a - b) := by bv_omega

private theorem pl_bv_sub_sub_lit (x a b : BitVec 64) :
    x - a - b = x - (a + b) := by bv_omega

private theorem pl_bv_add_sub_lit (x a b : BitVec 64) :
    x + a - b = x + (a - b) := by bv_omega

private theorem pl_bv_add_neg_8 (a : BitVec 64) :
    a + 18446744073709551608#64 = a - 8#64 := by bv_omega
private theorem pl_bv_add_neg_16 (a : BitVec 64) :
    a + 18446744073709551600#64 = a - 16#64 := by bv_omega
private theorem pl_bv_add_neg_24 (a : BitVec 64) :
    a + 18446744073709551592#64 = a - 24#64 := by bv_omega
private theorem pl_bv_add_neg_32 (a : BitVec 64) :
    a + 18446744073709551584#64 = a - 32#64 := by bv_omega
private theorem pl_bv_add_neg_40 (a : BitVec 64) :
    a + 18446744073709551576#64 = a - 40#64 := by bv_omega
private theorem pl_bv_add_neg_48 (a : BitVec 64) :
    a + 18446744073709551568#64 = a - 48#64 := by bv_omega
private theorem pl_bv_add_neg_55 (a : BitVec 64) :
    a + 18446744073709551561#64 = a - 55#64 := by bv_omega
private theorem pl_bv_add_neg_56 (a : BitVec 64) :
    a + 18446744073709551560#64 = a - 56#64 := by bv_omega
private theorem pl_bv_add_neg_64 (a : BitVec 64) :
    a + 18446744073709551552#64 = a - 64#64 := by bv_omega
private theorem pl_bv_add_neg_72 (a : BitVec 64) :
    a + 18446744073709551544#64 = a - 72#64 := by bv_omega
private theorem pl_bv_add_neg_80 (a : BitVec 64) :
    a + 18446744073709551536#64 = a - 80#64 := by bv_omega
private theorem pl_bv_add_neg_87 (a : BitVec 64) :
    a + 18446744073709551529#64 = a - 87#64 := by bv_omega
private theorem pl_bv_add_neg_88 (a : BitVec 64) :
    a + 18446744073709551528#64 = a - 88#64 := by bv_omega
private theorem pl_bv_add_neg_96 (a : BitVec 64) :
    a + 18446744073709551520#64 = a - 96#64 := by bv_omega
private theorem pl_bv_add_neg_104 (a : BitVec 64) :
    a + 18446744073709551512#64 = a - 104#64 := by bv_omega
private theorem pl_bv_add_neg_112 (a : BitVec 64) :
    a + 18446744073709551504#64 = a - 112#64 := by bv_omega
private theorem pl_bv_add_neg_128 (a : BitVec 64) :
    a + 18446744073709551488#64 = a - 128#64 := by bv_omega
private theorem pl_bv_add_neg_136 (a : BitVec 64) :
    a + 18446744073709551480#64 = a - 136#64 := by bv_omega
private theorem pl_bv_add_neg_152 (a : BitVec 64) :
    a + 18446744073709551464#64 = a - 152#64 := by bv_omega
private theorem pl_bv_add_neg_160 (a : BitVec 64) :
    a + 18446744073709551456#64 = a - 160#64 := by bv_omega
private theorem pl_bv_add_neg_168 (a : BitVec 64) :
    a + 18446744073709551448#64 = a - 168#64 := by bv_omega
private theorem pl_bv_add_neg_176 (a : BitVec 64) :
    a + 18446744073709551440#64 = a - 176#64 := by bv_omega
private theorem pl_bv_add_neg_184 (a : BitVec 64) :
    a + 18446744073709551432#64 = a - 184#64 := by bv_omega
private theorem pl_bv_add_neg_186 (a : BitVec 64) :
    a + 18446744073709551430#64 = a - 186#64 := by bv_omega
private theorem pl_bv_add_neg_191 (a : BitVec 64) :
    a + 18446744073709551425#64 = a - 191#64 := by bv_omega
private theorem pl_bv_add_neg_192 (a : BitVec 64) :
    a + 18446744073709551424#64 = a - 192#64 := by bv_omega
private theorem pl_bv_add_neg_196 (a : BitVec 64) :
    a + 18446744073709551420#64 = a - 196#64 := by bv_omega
private theorem pl_bv_add_neg_200 (a : BitVec 64) :
    a + 18446744073709551416#64 = a - 200#64 := by bv_omega
private theorem pl_bv_add_neg_216 (a : BitVec 64) :
    a + 18446744073709551400#64 = a - 216#64 := by bv_omega
private theorem pl_bv_add_neg_512 (a : BitVec 64) :
    a + 18446744073709551104#64 = a - 512#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  pl_bv_sub_add_lit pl_bv_sub_add_lit' pl_bv_sub_sub_lit pl_bv_add_sub_lit BitVec.toNat_zero
  pl_bv_add_neg_8 pl_bv_add_neg_16 pl_bv_add_neg_24 pl_bv_add_neg_32 pl_bv_add_neg_40
  pl_bv_add_neg_48 pl_bv_add_neg_55 pl_bv_add_neg_56 pl_bv_add_neg_64 pl_bv_add_neg_72
  pl_bv_add_neg_80 pl_bv_add_neg_87 pl_bv_add_neg_88 pl_bv_add_neg_96 pl_bv_add_neg_104
  pl_bv_add_neg_112 pl_bv_add_neg_128 pl_bv_add_neg_136 pl_bv_add_neg_152 pl_bv_add_neg_160
  pl_bv_add_neg_168 pl_bv_add_neg_176 pl_bv_add_neg_184 pl_bv_add_neg_186 pl_bv_add_neg_191
  pl_bv_add_neg_192 pl_bv_add_neg_196 pl_bv_add_neg_200 pl_bv_add_neg_216 pl_bv_add_neg_512

private theorem pl_spAligned_sub608 {s : State} (h : s.spAligned = true) :
    ((s.sp - 608#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned, beq_iff_eq] at h
  rw [beq_iff_eq]
  bv_bits

/-! ## Section 1: Pure Arithmetic & Condition Helpers for Version Byte & Length (`< 2 ^ 32`) -/

theorem ofNat64_length_ne_zero_w40 {bs : List (BitVec 8)} (hne : bs ≠ []) (hlt : bs.length < 2 ^ 32) :
    BitVec.ofNat 64 bs.length ≠ 0#64 := by
  have hpos : 0 < bs.length := List.length_pos_of_ne_nil hne
  intro h
  have hto := congrArg BitVec.toNat h
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  rw [BitVec.toNat_ofNat, h0, Nat.mod_eq_of_lt (by omega)] at hto
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem cond_eq_subs1_false_w40 {n : Nat} (hge2 : 2 ≤ n) (hlt : n < 2 ^ 32) :
    ConditionHolds .EQ (subsPState64 (BitVec.ofNat 64 n) 1#64) = false := by
  rw [conditionHolds_eq_subsPState64, beq_eq_false_iff_ne]
  intro h
  have hto := congrArg BitVec.toNat h
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_ofNat, h1, Nat.mod_eq_of_lt (by omega)] at hto
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem cond_eq_len1 :
    ConditionHolds .EQ (subsPState64 1#64 1#64) = true := by
  unfold ConditionHolds subsPState64 AddWithCarry64
  decide

/-! ## Section 2: `sret` (`248` bytes) Splitting Helpers for `ErrAt.errCells_*` -/

theorem memRegion248_split_8_8_8 (sret : BitVec 64) :
    memRegion sret 248 ⊢
      ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w0 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗ ((sret + 16#64) ↦₆₄ w16) ∗
        memRegion (sret + 24#64) 224 := by
  rw [show (248 : Nat) = 8 + (8 + (8 + 224)) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    Prost.memRegion_split (sret + 8#64 + 8#64) 8 224 (by decide),
    ProofLib.memRegion_eight sret,
    ProofLib.memRegion_eight (sret + 8#64),
    ProofLib.memRegion_eight (sret + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem memRegion248_split_8_8_1 (sret : BitVec 64) :
    memRegion sret 248 ⊢
      ∃∗ b16 : BitVec 8, ∃∗ w8 : BitVec 64, ∃∗ w0 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗ ((sret + 16#64) ↦₈ b16) ∗
        memRegion (sret + 17#64) 231 := by
  rw [show (248 : Nat) = 8 + (8 + (1 + 231)) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    Prost.memRegion_split (sret + 8#64 + 8#64) 1 231 (by decide),
    ProofLib.memRegion_eight sret,
    ProofLib.memRegion_eight (sret + 8#64),
    ProofLib.memRegion_one (sret + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

private theorem pl_memRegion248_split16 (sret : BitVec 64) :
    memRegion sret 248 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ memRegion (sret + 16#64) 232 := by
  rw [show (248 : Nat) = 8 + (8 + 232) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    ProofLib.memRegion_eight sret, ProofLib.memRegion_eight (sret + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

/-! ## Section 3: Empty Slice (`x.bytes = []`, `+0x000..+0x024 → +0x04c..+0x05c → +0x504`) -/

attribute [local simp, local arm64_norm, local wp_norm]
  cond_ne_noneCap_add2 cond_eq_noneCap_add1 cond_hi_noneCap_sub1_add3

private theorem memRegion296_split_96_16_184 (sp' : BitVec 64) :
    memRegion sp' 296 ⊢
      ∃∗ s104 : BitVec 64, ∃∗ s96 : BitVec 64,
        memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ ((sp' + 104#64) ↦₆₄ s104) ∗
        memRegion (sp' + 112#64) 184 := by
  rw [show (296 : Nat) = 96 + (16 + 184) by decide,
    Prost.memRegion_split sp' 96 200 (by decide),
    Prost.memRegion_split (sp' + 96#64) 16 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (memRegion16_split8_8' (sp' + 96#64)))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem memRegion296_pack_96_16_184 (sp' s96 s104 : BitVec 64) :
    memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ ((sp' + 104#64) ↦₆₄ s104) ∗
    memRegion (sp' + 112#64) 184 ⊢
      memRegion sp' 296 := by
  rw [show (296 : Nat) = 96 + (8 + (8 + 184)) by decide,
    Prost.memRegion_split sp' 96 200 (by decide),
    Prost.memRegion_split (sp' + 96#64) 8 192 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))

private theorem initCells_to_full_cells (sp' : BitVec 64) :
    ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
    ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
    ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
    ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
    ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
    ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
    ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
    ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ⊢
      ∃∗ u436 : BitVec 32, ∃∗ u428 : BitVec 32, ∃∗ u420 : BitVec 32, ∃∗ u412 : BitVec 32,
      ∃∗ msgLen : BitVec 64, ∃∗ msgPtr : BitVec 64,
      ∃∗ ikLen : BitVec 64, ∃∗ ikPtr : BitVec 64,
      ∃∗ bkLen : BitVec 64, ∃∗ bkPtr : BitVec 64,
      ∃∗ kyberLen : BitVec 64, ∃∗ kyberPtr : BitVec 64,
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
        ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436) := by
  have hm4 (a : BitVec 64) : memRegion a 4 = (∃∗ u : BitVec 32, a ↦₃₂ u) :=
    ProofLib.memRegion_four a
  rw [hm4 (sp' + 412#64), hm4 (sp' + 420#64), hm4 (sp' + 428#64), hm4 (sp' + 436#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 320#64))
      (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 344#64))
        (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 368#64))
          (sepConj_mono_right (sepConj_mono_left (memRegion16_split8_8' (sp' + 392#64)))))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem full_cells_entails_memRegion128 (sp' : BitVec 64)
    (w312 kyberPtr kyberLen w336 bkPtr bkLen w360 ikPtr ikLen w384 msgPtr msgLen : BitVec 64)
    (u408 u412 u416 u420 u424 u428 u432 u436 : BitVec 32) :
    ((sp' + 312#64) ↦₆₄ w312) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
    ((sp' + 328#64) ↦₆₄ kyberLen) ∗
    ((sp' + 336#64) ↦₆₄ w336) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
    ((sp' + 352#64) ↦₆₄ bkLen) ∗
    ((sp' + 360#64) ↦₆₄ w360) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
    ((sp' + 376#64) ↦₆₄ ikLen) ∗
    ((sp' + 384#64) ↦₆₄ w384) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
    ((sp' + 400#64) ↦₆₄ msgLen) ∗
    ((sp' + 408#64) ↦₃₂ u408) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
    ((sp' + 416#64) ↦₃₂ u416) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
    ((sp' + 424#64) ↦₃₂ u424) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
    ((sp' + 432#64) ↦₃₂ u432) ∗ ((sp' + 436#64) ↦₃₂ u436) ⊢
      memRegion (sp' + 312#64) 128 := by
  have hw24 (a w0 w1 w2 : BitVec 64) :
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
    rw [show (24 : Nat) = 8 + (8 + 8) by decide,
      Prost.memRegion_split a 8 16 (by decide),
      Prost.memRegion_split (a + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  have hu8 (a : BitVec 64) (v0 v4 : BitVec 32) :
      (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v4) ⊢ memRegion a 8 := by
    rw [show (8 : Nat) = 4 + 4 by decide, Prost.memRegion_split a 4 4 (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _) (pointsTo32_entails_memRegion _ _)
  have h312 := hw24 (sp' + 312#64) w312 kyberPtr kyberLen
  have h336 := hw24 (sp' + 336#64) w336 bkPtr bkLen
  have h360 := hw24 (sp' + 360#64) w360 ikPtr ikLen
  have h384 := hw24 (sp' + 384#64) w384 msgPtr msgLen
  have h408 := hu8 (sp' + 408#64) u408 u412
  have h416 := hu8 (sp' + 416#64) u416 u420
  have h424 := hu8 (sp' + 424#64) u424 u428
  have h432 := hu8 (sp' + 432#64) u432 u436
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h312 h336 h360 h384 h408 h416 h424 h432
  rw [show (128 : Nat) = 24 + (24 + (24 + (24 + (8 + (8 + (8 + 8)))))) by decide,
    Prost.memRegion_split (sp' + 312#64) 24 104 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64) 24 80 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64) 24 56 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64) 24 32 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q :=
      (((sp' + 312#64) ↦₆₄ w312) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen)) ∗
      (((sp' + 336#64) ↦₆₄ w336) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗ ((sp' + 352#64) ↦₆₄ bkLen)) ∗
      (((sp' + 360#64) ↦₆₄ w360) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen)) ∗
      (((sp' + 384#64) ↦₆₄ w384) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen)) ∗
      (((sp' + 408#64) ↦₃₂ u408) ∗ ((sp' + 412#64) ↦₃₂ u412)) ∗
      (((sp' + 416#64) ↦₃₂ u416) ∗ ((sp' + 420#64) ↦₃₂ u420)) ∗
      (((sp' + 424#64) ↦₃₂ u424) ∗ ((sp' + 428#64) ↦₃₂ u428)) ∗
      (((sp' + 432#64) ↦₃₂ u432) ∗ ((sp' + 436#64) ↦₃₂ u436)))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono h312
    (sepConj_mono h336
      (sepConj_mono h360
        (sepConj_mono h384
          (sepConj_mono h408
            (sepConj_mono h416
              (sepConj_mono h424 h432))))))

private theorem pl_region152_repack (sp' c0 c1 w440 : BitVec 64) :
    ((sp' + 296#64) ↦₆₄ c0) ∗ ((sp' + 304#64) ↦₆₄ c1) ∗
      memRegion (sp' + 312#64) 128 ∗ ((sp' + 440#64) ↦₆₄ w440) ⊢
      memRegion (sp' + 296#64) 152 := by
  rw [show (152 : Nat) = 8 + (8 + (128 + 8)) by decide,
    Prost.memRegion_split (sp' + 296#64) 8 144 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64) 8 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64 + 8#64) 128 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _) (pointsTo64_entails_memRegion _ _)))

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
