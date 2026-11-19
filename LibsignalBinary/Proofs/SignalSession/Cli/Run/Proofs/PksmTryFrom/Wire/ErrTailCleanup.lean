/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees -- shake: keep
import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec -- shake: keep

/-!
# `PreKeySignalMessage::try_from`: Shared Epilogue and Loop-Error Deallocation Chain

Stack/frame splitting lemmas, shared epilogue `epilogue_504_raw_wpX` (`+0x504..+0x520 → ret`),
and loop-error `Option<Vec<u8>>` deallocation and `DecodeError` drop steps (`+0x4a4..+0x500 → +0x504`).
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
open CryptoVerification.LibsignalTripleRatchet.Prost hiding memRegion_split
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp

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

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Local kernel-checked BitVec normalizers -/

private theorem et_bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem et_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

private theorem et_bv_add_neg_8 (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem et_bv_add_neg_16 (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem et_bv_add_neg_24 (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem et_bv_add_neg_32 (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem et_bv_add_neg_40 (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem et_bv_add_neg_48 (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem et_bv_add_neg_56 (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem et_bv_add_neg_64 (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem et_bv_add_neg_72 (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem et_bv_add_neg_80 (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem et_bv_add_neg_88 (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem et_bv_add_neg_96 (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem et_bv_add_neg_104 (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem et_bv_add_neg_112 (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem et_bv_add_neg_128 (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem et_bv_add_neg_136 (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem et_bv_add_neg_152 (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem et_bv_add_neg_160 (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem et_bv_add_neg_168 (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem et_bv_add_neg_176 (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem et_bv_add_neg_184 (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem et_bv_add_neg_192 (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem et_bv_add_neg_200 (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem et_bv_add_neg_512 (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit et_bv_sub_add_lit' et_bv_sub_sub_lit BitVec.toNat_zero
  et_bv_add_neg_8 et_bv_add_neg_16 et_bv_add_neg_24 et_bv_add_neg_32 et_bv_add_neg_40
  et_bv_add_neg_48 et_bv_add_neg_56 et_bv_add_neg_64 et_bv_add_neg_72 et_bv_add_neg_80
  et_bv_add_neg_88 et_bv_add_neg_96 et_bv_add_neg_104 et_bv_add_neg_112 et_bv_add_neg_128
  et_bv_add_neg_136 et_bv_add_neg_152 et_bv_add_neg_160 et_bv_add_neg_168 et_bv_add_neg_176
  et_bv_add_neg_184 et_bv_add_neg_192 et_bv_add_neg_200 et_bv_add_neg_512

/-! ## 1. Callee Wrapper, Stack-Split Helpers, and Region Packing Helpers -/

theorem stackAt_skipFieldStackW_dropDecodeError (sp : BitVec 64) :
    stackAt sp (Prost.skipFieldStackX 100) =
      memRegion (sp - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
        (Prost.skipFieldStackX 100 - Prost.dropDecodeErrorStackX) ∗
        stackAt sp Prost.dropDecodeErrorStackX :=
  stackAt_sub_split sp Prost.dropDecodeErrorStackX (Prost.skipFieldStackX 100) (by decide) (by decide)

theorem stackAt_skipFieldStackX_ext (sp : BitVec 64) :
    stackAt sp (Prost.skipFieldStackX 100) =
      memRegion (sp - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
        (Prost.skipFieldStackX 100 - extHookStack) ∗ stackAt sp extHookStack :=
  stackAt_sub_split sp extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)

theorem stackAt_preKeyTryFromSubStack_skipField (sp : BitVec 64) :
    stackAt sp preKeyTryFromSubStack =
      memRegion (sp - BitVec.ofNat 64 preKeyTryFromSubStack)
        (preKeyTryFromSubStack - Prost.skipFieldStackX 100) ∗
        stackAt sp (Prost.skipFieldStackX 100) :=
  stackAt_sub_split sp (Prost.skipFieldStackX 100) preKeyTryFromSubStack (by decide) (by decide)

theorem memRegion248_split16 (sret : BitVec 64) :
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

theorem memRegion296_split104 (sp' : BitVec 64) :
    memRegion sp' 296 =
      memRegion sp' 104 ∗ (∃∗ w104 : BitVec 64, (sp' + 104#64) ↦₆₄ w104) ∗
        memRegion (sp' + 112#64) 184 := by
  rw [show (296 : Nat) = 104 + (8 + 184) by decide,
    Prost.memRegion_split sp' 104 192 (by decide),
    Prost.memRegion_split (sp' + 104#64) 8 184 (by decide),
    ProofLib.memRegion_eight (sp' + 104#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion296_repack104 (sp' w104 : BitVec 64) :
    memRegion sp' 104 ∗ ((sp' + 104#64) ↦₆₄ w104) ∗ memRegion (sp' + 112#64) 184 ⊢
      memRegion sp' 296 := by
  rw [show (296 : Nat) = 104 + (8 + 184) by decide,
    Prost.memRegion_split sp' 104 192 (by decide),
    Prost.memRegion_split (sp' + 104#64) 8 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 104#64) w104))

/-- Reassembling `memRegion (sp' + 312) 128` from the 4 `vecHeader`s and 4 `memRegion _ 8` slots
of `wirePreKeyAt`. -/
theorem wirePreKeyHeaders_entails_memRegion128 (sp' kyberCap kyberPtr kyberLen
    bkCap bkPtr bkLen ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64) :
    vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
      vecHeader (sp' + 336#64) bkCap bkPtr bkLen ∗
      vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
      vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
      memRegion (sp' + 408#64) 8 ∗ memRegion (sp' + 416#64) 8 ∗
      memRegion (sp' + 424#64) 8 ∗ memRegion (sp' + 432#64) 8 ⊢
      memRegion (sp' + 312#64) 128 := by
  rw [show (128 : Nat) = 24 + (24 + (24 + (24 + (8 + (8 + (8 + 8)))))) by decide,
    Prost.memRegion_split (sp' + 312#64) 24 104 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64) 24 80 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64) 24 56 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64) 24 32 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (vecHeader_entails_memRegion24 (sp' + 312#64) kyberCap kyberPtr kyberLen)
    (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 336#64) bkCap bkPtr bkLen)
      (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 360#64) ikCap ikPtr ikLen)
        (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 384#64) msgCap msgPtr msgLen)
          (Entails.refl _))))

theorem memRegion152_repack_16_128_8 (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 312#64) 128 ∗ memRegion (sp' + 440#64) 8 =
      memRegion (sp' + 296#64) 152 := by
  rw [show (152 : Nat) = 16 + (128 + 8) by decide,
    Prost.memRegion_split (sp' + 296#64) 16 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64) 128 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem et_stackAt_preKeyTryFrom_unsplit (sp : BitVec 64) (s0 : State) :
    stackAt (sp - 608#64) preKeyTryFromSubStack ∗
      memRegion (sp - 608#64) 296 ∗
      memRegion (sp - 608#64 + 296#64) 152 ∗
      memRegion (sp - 608#64 + 448#64) 64 ∗
      preKeyCalleeSavedAt (sp - 608#64) s0 ⊢
      stackAt sp preKeyTryFromStack := by
  rw [CryptoVerification.E2E.Pqxdh.ResponderWire.stackAt_preKeyTryFrom_split sp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (preKeyCalleeSavedAt_entails_memRegion96 (sp - 608#64) s0))))

/-! ## 2. Shared Epilogue (`+0x504 .. +0x520` / `1284 .. 1312` → `s0.readReg64 .x30`) -/

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
