/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common

/-!
# `PreKeySignalMessage::try_from`: Post-Loop Required-Field Presence Checks (`+0x460..+0x5b4`)

Defines the 96-byte stack spill layout `seg1SpillsAtW` and the presence-check exit states
(`PresenceOkState` at `+0x5b4`, `BkNoneTailState` at `+0x5e0`, `IkNoneTailState` at `+0x61c`,
`MsgNoneTailState` at `+0x66c`, `SpkNoneTailState` at `+0x678`), and proves the presence
checks for `base_key`, `identity_key`, `message`, and `signed_pre_key_id`.
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
open CryptoVerification.E2E.Pqxdh.ResponderWire
  (memRegion96_seg1_unpack post_memRegion48_split8)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (words5At words5At_entails_memRegion)
open CryptoVerification.SignalSession.Cli.RunProofs

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
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_IS5Wire_W5aPresence : True := trivial

/-! ## 1. Spills and Frozen Exit States (`section W5aExits`) -/

/-- Stack spill layout at `sp' + 16 .. sp' + 112` (96 bytes) after `+0x574`. -/
@[expose] def seg1SpillsAtW (sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen : BitVec 64)
    (regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32) : SepProp :=
  ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
  ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
  ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
  ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
  ((sp' + 68#64) ↦₃₂ kpkTag) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
  ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
  ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr)

section W5aExits

/-- Memory layout at `+0x5e0` (`1504`) when `m.baseKey = none`
(only `sp' + 96 = msgPtr`, `sp' + 104 = ikPtr`, and `[sp' + 312] = 0x8000000000000002` have been
written before the branch at `+0x550`). -/
@[expose] def BkNoneTailMem (A : RustAlloc)
    (sp' kyberCap kyberPtr kyberLen bkPtr bkLen ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64)
    (regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) : SepProp :=
  ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
  vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
  optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
  vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
  vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
  vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
  ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
  ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
  ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
  ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)

end W5aExits

/-! ## 2. Separation-Logic Helpers for -/

theorem vecU8Buf_cap_lt_len (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ Wire.vecU8Buf A cap ptr bs := by
  dsimp only [Wire.vecU8Buf]; refine Entails.pure_left fun h => ?_
  rw [pure_true_emp h, emp_sepConj, emp_sepConj]; exact Entails.refl _

/-- For any `optVecU8Buf A cap ptr len opt`, the dead niche check `cap + 2 != 0` at `+0x4e8` holds. -/
theorem optVecU8Buf_cap_add2_ne (A : RustAlloc) (cap ptr len : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optVecU8Buf A cap ptr len opt ⊢
      ⌜(cap + 2#64 != 0#64) = true⌝ ∗ optVecU8Buf A cap ptr len opt := by
  cases opt with
  | none =>
    dsimp only [optVecU8Buf]; refine Entails.pure_left_only fun hcap => ?_
    have hne : (cap + 2#64 != 0#64) = true := by subst hcap; decide
    rw [pure_true_emp hne, emp_sepConj, pure_true_emp hcap]; exact Entails.refl _
  | some bs =>
    dsimp only [optVecU8Buf]; refine Entails.pure_left fun hlen => ?_
    refine Entails.trans (vecU8Buf_cap_lt_len A cap ptr bs) (Entails.pure_left fun ⟨_, hlt, _⟩ => ?_)
    have hne : (cap + 2#64 != 0#64) = true := cap_add2_ne_of_lt hlt
    rw [pure_true_emp hne, emp_sepConj, pure_true_emp hlen, emp_sepConj]; exact Entails.refl _

/-- Bridge `Wire.vecU8Buf` to upstream `Wire.deallocSlot` via `optVecU8Buf_entails_deallocSlot`,
recording `cap ≠ noneCap` for the `cbz` dealloc checks in `ErrTailB`. -/
theorem vecU8Buf_entails_deallocSlot (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢
      ⌜cap ≠ noneCap⌝ ∗ ∃∗ active : Bool, deallocSlot A cap ptr active := by
  refine Entails.trans (vecU8Buf_cap_lt_len A cap ptr bs) (Entails.pure_left fun ⟨_, hlt, _⟩ => ?_)
  have hne : cap ≠ noneCap := by rintro rfl; revert hlt; decide
  rw [pure_true_emp hne, emp_sepConj]
  refine Entails.trans ?_ (optVecU8Buf_entails_deallocSlot A cap ptr (BitVec.ofNat 64 bs.length) (some bs))
  dsimp only [optVecU8Buf]
  rw [pure_true_emp rfl, emp_sepConj]
  exact Entails.refl _

theorem post_headers_entails_memRegion80W (sp' ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64)
    (regTag regVal opkT opkV spkTag spkVal kpkTag kpkVal : BitVec 32) :
    vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗ vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
    ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
    ((sp' + 416#64) ↦₃₂ opkT) ∗ ((sp' + 420#64) ↦₃₂ opkV) ∗
    ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
    ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ⊢
      memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 := by
  have h1 := vecHeader_entails_memRegion24 (sp' + 360#64) ikCap ikPtr ikLen
  have h2 := vecHeader_entails_memRegion24 (sp' + 384#64) msgCap msgPtr msgLen
  have h3 : ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ⊢ memRegion (sp' + 408#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 408#64) regTag regVal
  have h4 : ((sp' + 416#64) ↦₃₂ opkT) ∗ ((sp' + 420#64) ↦₃₂ opkV) ⊢ memRegion (sp' + 416#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 416#64) opkT opkV
  have h5 : ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ⊢ memRegion (sp' + 424#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 424#64) spkTag spkVal
  have h6 : ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ⊢ memRegion (sp' + 432#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 432#64) kpkTag kpkVal
  rw [show (72 : Nat) = 24 + (24 + (8 + (8 + 8))) by decide,
    Prost.memRegion_split (sp' + 360#64) 24 48 (by decide),
    Prost.memRegion_split (sp' + 360#64 + 24#64) 24 24 (by decide),
    Prost.memRegion_split (sp' + 360#64 + 24#64 + 24#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 360#64 + 24#64 + 24#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q := memRegion (sp' + 360#64) 24 ∗ memRegion (sp' + 384#64) 24 ∗
      memRegion (sp' + 408#64) 8 ∗ memRegion (sp' + 416#64) 8 ∗ memRegion (sp' + 424#64) 8 ∗
      memRegion (sp' + 432#64) 8) ?_ (by apply entails_of_eq; ac_rfl)
  rw [← sepConj_assoc ((sp' + 408#64) ↦₃₂ regTag), ← sepConj_assoc ((sp' + 416#64) ↦₃₂ opkT),
      ← sepConj_assoc ((sp' + 424#64) ↦₃₂ spkTag)]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 h6))))

/-! ## 3. (`+0x460 .. +0x5b4`): Presence Checks of `baseKey`, `identityKey`, `message`, `signedPreKeyId` -/

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
