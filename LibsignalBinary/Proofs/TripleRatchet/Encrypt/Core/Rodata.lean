/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefs
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.LibsignalTripleRatchet.Encrypt

open Arm64 ProofLib CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Callee and hook address lemmas for `OTR::encrypt` (`0x33e0c`) -/

namespace EncryptCoreFacts

end EncryptCoreFacts

theorem drop_left_sepWPp {prog : Program} {ret : BitVec 64}
    {s : State} {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem rodata_encrypt_placed_sepWPp [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {roSym : String} (hchk : lsroCheck roSym (utf8 "encrypt") = true)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s (((lsmpl.ρ roSym) ↦ᵣ utf8 "encrypt") ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact lsro_intro_chk hro hchk hm

theorem errResultAt_invalidState_placed_pack (A : RustAlloc) (ret : BitVec 64)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) (roPtr : BitVec 64) :
    ((ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      ((ret + 8#64) ↦₆₄ 9223372036854775809#64) ∗
      ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
      ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((ret + 40#64) ↦₆₄ roPtr) ∗
      ((ret + 48#64) ↦₆₄ 7#64) ∗
      memRegion (ret + 56#64) 64 ∗
      vecU8Buf A cap ptr bs ∗
      (roPtr ↦ᵣ utf8 "encrypt")) ⊢
    signalMessageResultAt A (utf8 "encrypt") ret (.error .invalidState) := by
  change ((ret ↦₆₄ errTag) ∗
      ((ret + 8#64) ↦₆₄ speWord 1) ∗
      ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
      ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((ret + 40#64) ↦₆₄ roPtr) ∗
      ((ret + 48#64) ↦₆₄ 7#64) ∗
      memRegion (ret + 56#64) 64 ∗
      vecU8Buf A cap ptr bs ∗
      (roPtr ↦ᵣ utf8 "encrypt")) ⊢
    signalMessageResultAt A (utf8 "encrypt") ret (.error .invalidState)
  unfold signalMessageResultAt errResultAt speAt strRefAt
  have hvec :
      (((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
        ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs) ⊢
      (∃∗ bs' : List (BitVec 8), vecU8 A (ret + 8#64 + 8#64) bs') := by
    refine Entails.sepExists_right bs ?_
    unfold vecU8
    refine Entails.sepExists_right cap ?_
    refine Entails.sepExists_right ptr ?_
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
    exact Entails.refl _
  have hstr :
      (((ret + 40#64) ↦₆₄ roPtr) ∗
        ((ret + 48#64) ↦₆₄ 7#64) ∗
        (roPtr ↦ᵣ utf8 "encrypt")) ⊢
      (∃∗ p : BitVec 64,
        ((ret + 8#64 + 32#64) ↦₆₄ p) ∗
          ((ret + 8#64 + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "encrypt").length) ∗
          (p ↦ᵣ utf8 "encrypt")) := by
    refine Entails.sepExists_right roPtr ?_
    have hlen : BitVec.ofNat 64 (utf8 "encrypt").length = 7#64 := by decide +kernel
    simp only [hlen, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  have hpull :
      ((ret ↦₆₄ errTag) ∗
        ((ret + 8#64) ↦₆₄ speWord 1) ∗
        ((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
        ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ret + 40#64) ↦₆₄ roPtr) ∗
        ((ret + 48#64) ↦₆₄ 7#64) ∗
        memRegion (ret + 56#64) 64 ∗
        vecU8Buf A cap ptr bs ∗
        (roPtr ↦ᵣ utf8 "encrypt")) =
      ((ret ↦₆₄ errTag) ∗
        (((ret + 8#64) ↦₆₄ speWord 1) ∗
          (((ret + 16#64) ↦₆₄ cap) ∗ ((ret + 24#64) ↦₆₄ ptr) ∗
            ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            vecU8Buf A cap ptr bs) ∗
          (((ret + 40#64) ↦₆₄ roPtr) ∗
            ((ret + 48#64) ↦₆₄ 7#64) ∗
            (roPtr ↦ᵣ utf8 "encrypt"))) ∗
        memRegion (ret + 56#64) 64) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono hvec hstr)))

abbrev lsAesEncSym : String :=
  "_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_encrypt"

abbrev lsFormatInnerSym : String :=
  "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner"

abbrev lsSpqrSendCoinsName : String :=
  "spqr::send::<libsignal_cli_ratchet::Coins>"

abbrev lsOtrEncryptRoSym : String :=
  "libsignal_session:.rodata..Lanon.81"

abbrev lsOtrEncryptCoinsRoSym : String :=
  "libsignal_cli_ratchet:.rodata..Lanon.81"

theorem lsroCheck_otrEncryptRoSym : lsroCheck lsOtrEncryptRoSym (utf8 "encrypt") = true := by
  decide +kernel

theorem lsroCheck_otrEncryptCoinsRoSym :
    lsroCheck lsOtrEncryptCoinsRoSym (utf8 "encrypt") = true := by
  decide +kernel

theorem aesEnc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {C : Crypto} {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsAesEncSym) (aesEncSpec C.E A) :=
  keys_ls_hook_ok_of_mem h_aes (by decide) hi hunmut

theorem formatInner_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsFormatInnerSym) (formatInnerSpec A) :=
  keys_ls_hook_ok_of_mem h_fmt (by decide) hi hunmut

theorem dealloc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustDeallocSpec A) :=
  keys_ls_hook_ok_of_mem h_dealloc (by decide) hi hunmut

end CryptoVerification.LibsignalTripleRatchet.Encrypt
