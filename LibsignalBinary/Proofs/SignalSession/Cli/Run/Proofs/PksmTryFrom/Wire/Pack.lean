/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.OkBridge -- proof-setup: allow-public-import
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::try_from`: 248-Byte `sret` Pack (`+0x8c0 → +0x970`)

Symbolic execution of the 44-instruction `Ok`-path `sret` pack (`+0x8c0..+0x96c → +0x970`),
assembling `RunCompose.pksmResAt A sret (Pksm.pksmParse (vb :: body))` and the `+0x970`
deallocation-chain frame.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 0. Layout-Independent Fetch Macro & Bit-Level Normalizers -/

private theorem pk_bv_add_neg_8 (x : BitVec 64) : x + 18446744073709551608#64 = x - 8#64 := by bv_omega
private theorem pk_bv_add_neg_16 (x : BitVec 64) : x + 18446744073709551600#64 = x - 16#64 := by bv_omega
private theorem pk_bv_add_neg_24 (x : BitVec 64) : x + 18446744073709551592#64 = x - 24#64 := by bv_omega
private theorem pk_bv_add_neg_32 (x : BitVec 64) : x + 18446744073709551584#64 = x - 32#64 := by bv_omega
private theorem pk_bv_add_neg_40 (x : BitVec 64) : x + 18446744073709551576#64 = x - 40#64 := by bv_omega
private theorem pk_bv_add_neg_48 (x : BitVec 64) : x + 18446744073709551568#64 = x - 48#64 := by bv_omega
private theorem pk_bv_add_neg_55 (x : BitVec 64) : x + 18446744073709551561#64 = x - 55#64 := by bv_omega
private theorem pk_bv_add_neg_56 (x : BitVec 64) : x + 18446744073709551560#64 = x - 56#64 := by bv_omega
private theorem pk_bv_add_neg_64 (x : BitVec 64) : x + 18446744073709551552#64 = x - 64#64 := by bv_omega
private theorem pk_bv_add_neg_72 (x : BitVec 64) : x + 18446744073709551544#64 = x - 72#64 := by bv_omega
private theorem pk_bv_add_neg_80 (x : BitVec 64) : x + 18446744073709551536#64 = x - 80#64 := by bv_omega
private theorem pk_bv_add_neg_87 (x : BitVec 64) : x + 18446744073709551529#64 = x - 87#64 := by bv_omega
private theorem pk_bv_add_neg_88 (x : BitVec 64) : x + 18446744073709551528#64 = x - 88#64 := by bv_omega
private theorem pk_bv_add_neg_96 (x : BitVec 64) : x + 18446744073709551520#64 = x - 96#64 := by bv_omega
private theorem pk_bv_add_neg_104 (x : BitVec 64) : x + 18446744073709551512#64 = x - 104#64 := by bv_omega
private theorem pk_bv_add_neg_112 (x : BitVec 64) : x + 18446744073709551504#64 = x - 112#64 := by bv_omega
private theorem pk_bv_add_neg_128 (x : BitVec 64) : x + 18446744073709551488#64 = x - 128#64 := by bv_omega
private theorem pk_bv_add_neg_136 (x : BitVec 64) : x + 18446744073709551480#64 = x - 136#64 := by bv_omega
private theorem pk_bv_add_neg_152 (x : BitVec 64) : x + 18446744073709551464#64 = x - 152#64 := by bv_omega
private theorem pk_bv_add_neg_160 (x : BitVec 64) : x + 18446744073709551456#64 = x - 160#64 := by bv_omega
private theorem pk_bv_add_neg_168 (x : BitVec 64) : x + 18446744073709551448#64 = x - 168#64 := by bv_omega
private theorem pk_bv_add_neg_176 (x : BitVec 64) : x + 18446744073709551440#64 = x - 176#64 := by bv_omega
private theorem pk_bv_add_neg_184 (x : BitVec 64) : x + 18446744073709551432#64 = x - 184#64 := by bv_omega
private theorem pk_bv_add_neg_186 (x : BitVec 64) : x + 18446744073709551430#64 = x - 186#64 := by bv_omega
private theorem pk_bv_add_neg_191 (x : BitVec 64) : x + 18446744073709551425#64 = x - 191#64 := by bv_omega
private theorem pk_bv_add_neg_192 (x : BitVec 64) : x + 18446744073709551424#64 = x - 192#64 := by bv_omega
private theorem pk_bv_add_neg_196 (x : BitVec 64) : x + 18446744073709551420#64 = x - 196#64 := by bv_omega
private theorem pk_bv_add_neg_200 (x : BitVec 64) : x + 18446744073709551416#64 = x - 200#64 := by bv_omega
private theorem pk_bv_add_neg_216 (x : BitVec 64) : x + 18446744073709551400#64 = x - 216#64 := by bv_omega
private theorem pk_bv_add_neg_512 (x : BitVec 64) : x + 18446744073709551104#64 = x - 512#64 := by bv_omega
private theorem pk_bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem pk_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

private theorem pk_truncate32_zext64_and1 (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x &&& 1#64) = x &&& 1#32 := by
  bv_bits

private theorem pk_mask32_low_0 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 0 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 0 8 v := by bv_bits
private theorem pk_mask32_low_8 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 8 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 8 8 v := by bv_bits
private theorem pk_mask32_low_16 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 16 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 16 8 v := by bv_bits
private theorem pk_mask32_low_24 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 24 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 24 8 v := by bv_bits

private theorem pk_extract8_concat4_0 (d c b a : BitVec 8) :
    BitVec.extractLsb' 0 8 (d ++ c ++ b ++ a) = a := by bv_bits
private theorem pk_extract8_concat4_8 (d c b a : BitVec 8) :
    BitVec.extractLsb' 8 8 (d ++ c ++ b ++ a) = b := by bv_bits
private theorem pk_extract8_concat4_16 (d c b a : BitVec 8) :
    BitVec.extractLsb' 16 8 (d ++ c ++ b ++ a) = c := by bv_bits
private theorem pk_extract8_concat4_24 (d c b a : BitVec 8) :
    BitVec.extractLsb' 24 8 (d ++ c ++ b ++ a) = d := by bv_bits

private theorem pk_extract8_mask32_0 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 8
      (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = a :=
  (pk_mask32_low_0 w (d ++ c ++ b ++ a)).trans (pk_extract8_concat4_0 d c b a)
private theorem pk_extract8_mask32_8 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 8 8
      (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = b :=
  (pk_mask32_low_8 w (d ++ c ++ b ++ a)).trans (pk_extract8_concat4_8 d c b a)
private theorem pk_extract8_mask32_16 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 8
      (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = c :=
  (pk_mask32_low_16 w (d ++ c ++ b ++ a)).trans (pk_extract8_concat4_16 d c b a)
private theorem pk_extract8_mask32_24 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 24 8
      (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = d :=
  (pk_mask32_low_24 w (d ++ c ++ b ++ a)).trans (pk_extract8_concat4_24 d c b a)
private theorem pk_extract8_mask32_32 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 32 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 32 8 w := by bv_bits
private theorem pk_extract8_mask32_40 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 40 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 40 8 w := by bv_bits
private theorem pk_extract8_mask32_48 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 48 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 48 8 w := by bv_bits
private theorem pk_extract8_mask32_56 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 56 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 56 8 w := by bv_bits

private theorem pk_extract8_concat8_0 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 0 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b0 := by bv_bits
private theorem pk_extract8_concat8_8 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 8 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b1 := by bv_bits
private theorem pk_extract8_concat8_16 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 16 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b2 := by bv_bits
private theorem pk_extract8_concat8_24 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 24 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b3 := by bv_bits
private theorem pk_extract8_concat8_32 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 32 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b4 := by bv_bits
private theorem pk_extract8_concat8_40 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 40 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b5 := by bv_bits
private theorem pk_extract8_concat8_48 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 48 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b6 := by bv_bits
private theorem pk_extract8_concat8_56 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 56 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b7 := by bv_bits

attribute [local arm64_norm]
  pk_bv_add_neg_8 pk_bv_add_neg_16 pk_bv_add_neg_24 pk_bv_add_neg_32 pk_bv_add_neg_40
  pk_bv_add_neg_48 pk_bv_add_neg_55 pk_bv_add_neg_56 pk_bv_add_neg_64 pk_bv_add_neg_72
  pk_bv_add_neg_80 pk_bv_add_neg_87 pk_bv_add_neg_88 pk_bv_add_neg_96 pk_bv_add_neg_104
  pk_bv_add_neg_112 pk_bv_add_neg_128 pk_bv_add_neg_136 pk_bv_add_neg_152 pk_bv_add_neg_160
  pk_bv_add_neg_168 pk_bv_add_neg_176 pk_bv_add_neg_184 pk_bv_add_neg_186 pk_bv_add_neg_191
  pk_bv_add_neg_192 pk_bv_add_neg_196 pk_bv_add_neg_200 pk_bv_add_neg_216 pk_bv_add_neg_512
  pk_bv_sub_add_lit' pk_bv_sub_sub_lit
  pk_extract8_mask32_0 pk_extract8_mask32_8 pk_extract8_mask32_16 pk_extract8_mask32_24
  pk_extract8_mask32_32 pk_extract8_mask32_40 pk_extract8_mask32_48 pk_extract8_mask32_56
  pk_extract8_concat8_0 pk_extract8_concat8_8 pk_extract8_concat8_16 pk_extract8_concat8_24
  pk_extract8_concat8_32 pk_extract8_concat8_40 pk_extract8_concat8_48 pk_extract8_concat8_56
  zeroExtend32_lsr4_truncate8

/-! ## 1. Bit-Level Normalization Helpers for `opkTag` and `vb >>> 4` -/

/-- When `opkTag = if opt.isSome then 1#32 else 0#32`, masking `(opkTag.zeroExtend 64) &&& 1#64`
and truncating to 32 bits returns `opkTag`. -/
theorem opkTag_mask64_truncate32_of_ite (opt : Option (BitVec 32)) (opkTag : BitVec 32)
    (h : opkTag = if opt.isSome then 1#32 else 0#32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 opkTag &&& 1#64) = opkTag := by
  subst h
  cases opt <;> simp

@[local simp, local arm64_norm, local wp_norm]
theorem truncate8_zeroExtend64_eq (b : BitVec 8) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 b) = b := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem zeroExtend32_vb_lsr4_setWidth8 (vb : BitVec 8) :
    ((vb.zeroExtend 32) >>> 4).setWidth 8 = vb >>> 4 := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem zeroExtend64_vb_lsr4_setWidth8 (vb : BitVec 8) :
    (((vb.zeroExtend 64).setWidth 32 >>> 4).zeroExtend 64).setWidth 8 = vb >>> 4 := by
  bv_bits

/-! ## 2. Leaf L5 (`+0x8c0 → +0x970` / `2240 → 2416`): 44-Instruction `sret` Pack -/

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
