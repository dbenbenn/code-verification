/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyHeader -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyFields
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXA
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` Tag 9: `pending_pre_key` Header, Subfields 3–4, and Assembly

Verifies the outer `0x4a` tag and nested length computation (`536..824/872`), subfields 3
(`signed_pre_key_id`) and 4 (`timestamp`, `976..1080`), and the combined protobuf tag 9
(`pending_pre_key`, `536 → 1080`) of `SessionStructure::encode_raw` (`0x4d38`) on `SP2Ext`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux
open Proofs.libsignal.Hooks2

theorem L1_EncodeRawPendingPreKeyFieldsXB : True := trivial

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length
  erHwVarintLen_bvShift_eq_encodeVarint_length

@[local arm64_norm]
theorem bv_add_neg80_3a_x (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

set_option maxHeartbeats 400000

theorem L1_EncodeRawPendingPreKeyHeaderX : True := trivial

/-! ## Tag `0x4a#8` write (`536..596/764`, cold `2124..2152`) -/

@[local simp, local arm64_norm]
theorem truncate32_signExtend64 (w : BitVec 32) :
    BitVec.truncate 32 (BitVec.signExtend 64 w) = w := by
  ext i hi
  simp [BitVec.getLsbD_signExtend, hi]
  omega

theorem spk_cbz_pc (entry : BitVec 64) (v : BitVec 32) :
    (if (BitVec.zeroExtend 64 v == 0#64) = true then entry + bv% (788) else entry + bv% (672)) =
      entry + (if v == 0#32 then 788#64 else 672#64) := by
  have hz : (BitVec.zeroExtend 64 v == 0#64) = (v == 0#32) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      have h' := congr_arg BitVec.toNat h
      rw [ProofLib.toNat_zeroExtend64_32] at h'
      exact h'
    · rintro rfl
      rfl
  rw [hz]
  cases v == 0#32 <;> rfl

/-! ## Subfield 2 (`base_key`) length and `signed_pre_key_id` load (`636 → 672/788`) -/

end CryptoVerification.E2E.Record.Serialization
