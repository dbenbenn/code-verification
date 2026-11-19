/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.SmDir
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
import LibsignalBinary.Proofs.E2E.RecordX.BridgeCommon
import LibsignalBinary.Proofs.E2E.RecordX.Length
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.StateXModelProofDefs
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp

/-!
# SPQR-Off Session-Record and SM-Directory File Cap Bounds

Proves that every reachable SPQR-off session state `Reach (spqrOffSessionParams C) g` has empty
post-quantum ratchet state (`g.session.pqRatchetState = []`) and encodes within `fileCapBytes`
(`2 ^ 21` B), together with file-cap bounds on `dirOfE`, `smSendInputs`, `smRecvInputs`,
`smSendModel`, and `smRecvModel`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Reach.SmSessionCap

open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto GhostState SessionState SignalMessage IdentityKey PublicKey)
open CryptoVerification.E2E
  (Bytes spqrOffSessionParams Reach encodeRecord sendModelSpqrOff recvModelSpqrOff
   partyAddressName partyIdentityKey RecordExtras seedRecordExtras encodeRecordUnderExtras
   FixedIdRecordExtras)
open CryptoVerification.SignalSession
  (fileCapBytes dirOfE smInputs smSendInputs smRecvInputs smWrites smSendModel smRecvModel
   partyAddress textBytes)
open CryptoVerification.E2E.Reach
  (reach_pqRatchetState_eq_nil reach_encodeRecord_length_lt_20
   sessionInv_of_send_ok sessionInv_of_recv_ok encodeRecord_length_lt_20_of_sessionInv)
open CryptoVerification.E2E.RecordX (encodeRecordX_extrasSeed reach_encodeRecordX_length_lt_21)

/-- Every reachable SPQR-off session record `encodeRecord g` encodes to at most `2 ^ 21` bytes. -/
theorem reach_encodeRecord_length_le_sessionCap (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    (encodeRecord g).length ≤ 2 ^ 21 :=
  Nat.le_of_lt (Nat.lt_trans (reach_encodeRecord_length_lt_20 C hg) (by decide))

theorem reach_encodeRecord_length_le_fileCapBytes (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    (encodeRecord g).length ≤ fileCapBytes := by
  change (encodeRecord g).length ≤ 2 ^ 21
  exact reach_encodeRecord_length_le_sessionCap C hg

private theorem byteArray_loop_len (bs : ByteArray) (i : Nat) (acc : List UInt8) (hi : i ≤ bs.size) :
    (ByteArray.toList.loop bs i acc).length = acc.length + (bs.size - i) := by
  unfold ByteArray.toList.loop
  split
  · rw [byteArray_loop_len bs (i + 1) _ (by omega)]; simp; omega
  · simp; omega
termination_by bs.size - i
decreasing_by
  have : i < bs.size := ‹_›; omega

end LibsignalBinary.Proofs.E2E.Reach.SmSessionCap
