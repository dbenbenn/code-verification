/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop -- proof-setup: allow-public-import
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSlice
import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRef
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Specifications.AsmConstants
import ProofLib.SepLogic.WPp

/-!
# Callee Contracts and `IdentityKey::try_from` Specifications for `PreKeySignalMessage::try_from`

Proves the `Ok` and `Err` specifications of `<IdentityKey as TryFrom<&[u8]>>::try_from`
(preserving exact `speAt` error payloads via `ikErrWords`) and packages all callee contracts
of `PreKeySignalMessage::try_from` into `PksmCallees` from image loading and allocator hooks.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.FindReceiverChainIndex
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## Local kernel-checked BitVec normalizers -/

private theorem bv_sub_add_lit'X (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem bv_sub_sub_litX (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

private theorem bv_add_neg_8X (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem bv_add_neg_16X (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem bv_add_neg_24X (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem bv_add_neg_32X (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem bv_add_neg_40X (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem bv_add_neg_48X (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem bv_add_neg_55X (x : BitVec 64) : x + bv% (2 ^ 64 - 55) = x - 55#64 := by bv_omega
private theorem bv_add_neg_56X (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem bv_add_neg_64X (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem bv_add_neg_72X (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem bv_add_neg_80X (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem bv_add_neg_87X (x : BitVec 64) : x + bv% (2 ^ 64 - 87) = x - 87#64 := by bv_omega
private theorem bv_add_neg_88X (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem bv_add_neg_96X (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem bv_add_neg_104X (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem bv_add_neg_112X (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem bv_add_neg_128X (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem bv_add_neg_136X (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem bv_add_neg_152X (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem bv_add_neg_160X (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem bv_add_neg_168X (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem bv_add_neg_176X (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem bv_add_neg_184X (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem bv_add_neg_186X (x : BitVec 64) : x + bv% (2 ^ 64 - 186) = x - 186#64 := by bv_omega
private theorem bv_add_neg_191X (x : BitVec 64) : x + bv% (2 ^ 64 - 191) = x - 191#64 := by bv_omega
private theorem bv_add_neg_192X (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem bv_add_neg_196X (x : BitVec 64) : x + bv% (2 ^ 64 - 196) = x - 196#64 := by bv_omega
private theorem bv_add_neg_200X (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem bv_add_neg_216X (x : BitVec 64) : x + bv% (2 ^ 64 - 216) = x - 216#64 := by bv_omega
private theorem bv_add_neg_512X (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

private theorem extract8_mask32_0X (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = a := by
  bv_slice
private theorem extract8_mask32_8X (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 8 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = b := by
  bv_slice
private theorem extract8_mask32_16X (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = c := by
  bv_slice
private theorem extract8_mask32_24X (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 24 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = d := by
  bv_slice
private theorem extract8_mask32_32X (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 32 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 32 8 w := by bv_bits
private theorem extract8_mask32_40X (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 40 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 40 8 w := by bv_bits
private theorem extract8_mask32_48X (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 48 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 48 8 w := by bv_bits
private theorem extract8_mask32_56X (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 56 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 56 8 w := by bv_bits

private theorem extract8_concat8_0X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 0 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b0 := by bv_slice
private theorem extract8_concat8_8X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 8 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b1 := by bv_slice
private theorem extract8_concat8_16X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 16 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b2 := by bv_slice
private theorem extract8_concat8_24X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 24 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b3 := by bv_slice
private theorem extract8_concat8_32X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 32 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b4 := by bv_slice
private theorem extract8_concat8_40X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 40 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b5 := by bv_slice
private theorem extract8_concat8_48X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 48 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b6 := by bv_slice
private theorem extract8_concat8_56X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 56 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b7 := by bv_slice

private theorem pointsTo64_eq_extract_bytes8X (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗ ((a + 1#64) ↦₈ w.extractLsb' 8 8) ∗
      ((a + 2#64) ↦₈ w.extractLsb' 16 8) ∗ ((a + 3#64) ↦₈ w.extractLsb' 24 8) ∗
      ((a + 4#64) ↦₈ w.extractLsb' 32 8) ∗ ((a + 5#64) ↦₈ w.extractLsb' 40 8) ∗
      ((a + 6#64) ↦₈ w.extractLsb' 48 8) ∗ ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hw : w = w.extractLsb' 56 8 ++ w.extractLsb' 48 8 ++ w.extractLsb' 40 8 ++
      w.extractLsb' 32 8 ++ w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++
      w.extractLsb' 8 8 ++ w.extractLsb' 0 8 := by bv_bits
  conv => lhs; rw [hw]
  exact pointsTo64_eq_bytes8 a _ _ _ _ _ _ _ _

attribute [local arm64_norm, local wp_norm]
  extract8_mask32_0X extract8_mask32_8X extract8_mask32_16X extract8_mask32_24X
  extract8_mask32_32X extract8_mask32_40X extract8_mask32_48X extract8_mask32_56X
  extract8_concat8_0X extract8_concat8_8X extract8_concat8_16X extract8_concat8_24X
  extract8_concat8_32X extract8_concat8_40X extract8_concat8_48X extract8_concat8_56X
  bv_sub_add_lit'X bv_sub_sub_litX
  bv_add_neg_8X bv_add_neg_16X bv_add_neg_24X bv_add_neg_32X bv_add_neg_40X
  bv_add_neg_48X bv_add_neg_55X bv_add_neg_56X bv_add_neg_64X bv_add_neg_72X
  bv_add_neg_80X bv_add_neg_87X bv_add_neg_88X bv_add_neg_96X bv_add_neg_104X
  bv_add_neg_112X bv_add_neg_128X bv_add_neg_136X bv_add_neg_152X bv_add_neg_160X
  bv_add_neg_168X bv_add_neg_176X bv_add_neg_184X bv_add_neg_186X bv_add_neg_191X
  bv_add_neg_192X bv_add_neg_196X bv_add_neg_200X bv_add_neg_216X bv_add_neg_512X
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue.append64_extract_lo
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue.append64_extract_hi

/-! ## Section 1: `<IdentityKey as TryFrom<&[u8]>>::try_from` Ok & Err Specs and Proofs -/

private theorem cells_12_identityKey_pre (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      memRegion (sp - 48#64) 8 ∗
      memRegion (sp - 40#64) 8 ∗
      (∃∗ w_32 : BitVec 64, (sp - 32#64) ↦₆₄ w_32) ∗
      (∃∗ w_24 : BitVec 64, (sp - 24#64) ↦₆₄ w_24) ∗
      (∃∗ w_16 : BitVec 64, (sp - 16#64) ↦₆₄ w_16) ∗
      memRegion (sp - 8#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp - 96#64) 12 (by decide),
    Prost.memRegion_split (sp - 96#64) 8 88 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64) 40 48 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64) 8 40 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64) 8 32 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [bv_sub_add_lit'X, BitVec.reduceSub]
  rw [ProofLib.memRegion_eight (sp - 32#64),
      ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64)]

private theorem memRegion_40_identityKey_post (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      memRegion (sp - 88#64) 1 ∗
      memRegion_8_bytes_mr_rhs (sp - 87#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 79#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 71#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 63#64) ∗
      memRegion (sp - 55#64) 7 := by
  rw [Prost.memRegion_split (sp - 88#64) 1 39 (by decide),
    Prost.memRegion_split (sp - 88#64 + 1#64) 8 31 (by decide),
    Prost.memRegion_split (sp - 88#64 + 1#64 + 8#64) 8 23 (by decide),
    Prost.memRegion_split (sp - 88#64 + 1#64 + 8#64 + 8#64) 8 15 (by decide),
    Prost.memRegion_split (sp - 88#64 + 1#64 + 8#64 + 8#64 + 8#64) 8 7 (by decide)]
  simp only [bv_sub_add_lit'X, BitVec.reduceSub]
  rw [memRegion_8_bytes_mr (sp - 87#64),
      memRegion_8_bytes_mr (sp - 79#64),
      memRegion_8_bytes_mr (sp - 71#64),
      memRegion_8_bytes_mr (sp - 63#64)]

/-- The `(tag, payload)` words `<IdentityKey as TryFrom<&[u8]>>::try_from` stores via
`stp x8, x9, [x19]` at `out`, `out + 8` on the `Err` arms of `PublicKey::try_from`:
`x8 = speWord 7 / 8 / 9 / 10` for discriminants `0 / 1 / 2 / ≥ 3`, and `x9 = 7` / byte / usize. -/
@[expose] def ikErrWords : SignalProtocolError → BitVec 64 × BitVec 64
  | .noKeyTypeIdentifier => (speWord 7, 7#64)
  | .badKeyType t => (speWord 8, t.zeroExtend 64)
  | .badKeyLength n => (speWord 9, BitVec.ofNat 64 n)
  | .invalidKeyAgreement => (speWord 10, 0#64)
  | _ => (0#64, 0#64)

theorem ikErrWords_fst_ne (e : SignalProtocolError) :
    (ikErrWords e).1 ≠ 0xfffffffffffffffe#64 := by
  unfold ikErrWords; split <;> simp [speWord]

/-- `PublicKey::deserialize` fails with one of the three public-key decode errors. -/
theorem deserialize_error_cases {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : PublicKey.deserialize bs = .error e) :
    e = .noKeyTypeIdentifier ∨ (∃ t, e = .badKeyType t) ∨ ∃ n, e = .badKeyLength n := by
  unfold PublicKey.deserialize at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h; exact Or.inr (Or.inl ⟨_, rfl⟩)
    · split at h
      · cases h
      · cases h; exact Or.inr (Or.inr ⟨_, rfl⟩)

private theorem ik_low8_merge (n : BitVec 64) :
    n &&& (-256#64) ||| n &&& 255#64 = n := by
  rw [← BitVec.and_or_distrib_left, show (-256#64 ||| 255#64) = BitVec.allOnes 64 by decide,
    BitVec.and_allOnes]

private theorem memRegion_40_stp (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      memRegion (a + 16#64) 24 := by
  rw [ProofLib.memRegion_split a 8 32 (by decide), ProofLib.memRegion_split (a + 8#64) 8 24 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_40_ikErr_small (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      memRegion (sp - 88#64) 1 ∗ memRegion (sp - 87#64) 7 ∗ memRegion (sp - 80#64) 1 ∗
      memRegion (sp - 79#64) 1 ∗ memRegion (sp - 78#64) 30 := by
  rw [ProofLib.memRegion_split (sp - 88#64) 1 39 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64) 7 32 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64) 1 31 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64 + 1#64) 1 30 (by decide)]
  simp only [bv_sub_add_lit'X, BitVec.reduceSub]

private theorem memRegion_40_ikErr_len (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      memRegion (sp - 88#64) 1 ∗ memRegion (sp - 87#64) 7 ∗ memRegion (sp - 80#64) 1 ∗
      memRegion (sp - 79#64) 7 ∗ (∃∗ w : BitVec 64, (sp - 72#64) ↦₆₄ w) ∗
      memRegion (sp - 64#64) 16 := by
  rw [ProofLib.memRegion_split (sp - 88#64) 1 39 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64) 7 32 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64) 1 31 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64 + 1#64) 7 24 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64 + 1#64 + 7#64) 8 16 (by decide)]
  simp only [bv_sub_add_lit'X, BitVec.reduceSub]
  rw [ProofLib.memRegion_eight (sp - 72#64)]

private theorem memRegion_31_byte (a : BitVec 64) :
    memRegion a 31 = (∃∗ v : BitVec 8, a ↦₈ v) ∗ memRegion (a + 1#64) 30 := by
  rw [ProofLib.memRegion_split a 1 30 (by decide), ProofLib.memRegion_one]

/-- The two words stored by `stp x8, x9, [a]` plus a
32-byte trailing region (`a + 16 .. a + 48`) entail `speAt A fn a e` for every error `e` of
`PublicKey.deserialize`. -/
theorem ikErrWords_entails_speAt {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : PublicKey.deserialize bs = .error e)
    (A : RustAlloc) (fn : List (BitVec 8)) (a : BitVec 64) :
    (a ↦₆₄ (ikErrWords e).1) ∗ ((a + 8#64) ↦₆₄ (ikErrWords e).2) ∗
      memRegion (a + 16#64) 32 ⊢
    speAt A fn a e := by
  rcases deserialize_error_cases h with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · simp only [ikErrWords, speAt]
    rw [show memRegion (a + asm64% spePayloadOff) (asm% (speSize - spePayloadOff)) =
        memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using
        ProofLib.memRegion_split (a + 8#64) 8 32 (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (a + 8#64) 7#64))
  · simp only [ikErrWords, speAt]
    have hb0 : ((t.zeroExtend 64).extractLsb' 0 8) = t := by bv_bits
    have hzext : ((a + 8#64) ↦₆₄ t.zeroExtend 64) ⊢
        ((a + 8#64) ↦₈ t) ∗ memRegion (a + 9#64) 7 := by
      rw [pointsTo64_eq_pointsToBytes]
      change ((a + 8#64) ↦ₛ ((t.zeroExtend 64).extractLsb' 0 8 ::
        [(t.zeroExtend 64).extractLsb' 8 8, (t.zeroExtend 64).extractLsb' 16 8,
         (t.zeroExtend 64).extractLsb' 24 8, (t.zeroExtend 64).extractLsb' 32 8,
         (t.zeroExtend 64).extractLsb' 40 8, (t.zeroExtend 64).extractLsb' 48 8,
         (t.zeroExtend 64).extractLsb' 56 8])) ⊢ _
      rw [hb0, pointsToBytes_cons, show a + 8#64 + 1#64 = a + 9#64 by bv_omega]
      exact sepConj_mono_right (pointsToBytes_entails_memRegion _ _)
    rw [show memRegion (a + asm64% (spePayloadOff + 1)) (asm% (speSize - (spePayloadOff + 1))) =
        memRegion (a + 9#64) 7 ∗ memRegion (a + 16#64) 32 by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using
        ProofLib.memRegion_split (a + 9#64) 7 32 (by decide)]
    refine sepConj_mono_right ?_
    rw [← sepConj_assoc]
    exact Entails.trans (sepConj_mono_left hzext) (by apply entails_of_eq; ac_rfl)
  · simp only [ikErrWords, speAt]
    exact Entails.refl _

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

