/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bSigMsg -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTail
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailC
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Pack
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysPlacedSym

/-!
# `PreKeySignalMessage::try_from`: `+0x8c0` `Ok` Packing, Deallocation, and Epilogue (`PreKey8c0OkW`)

Proves `preKey8c0OkW_proof` (`+0x8c0 → +0x970 → +0x504 → ret`) by chaining
`preKey_pack_8c0_to_970_dealloc_res_wpX`, `deallocChain_970_wpX`, `epilogue_504_wpX`,
and `w8bPack_okPost`.
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
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

/-! ## 1. Pure & Region Helpers -/

/-- `identRegId` of the `registration_id` cells is `m.registrationId.getD 0`. -/
theorem w8bPack_regId {opt : Option (BitVec 32)} {regTag regVal : BitVec 32}
    (h : w8bOptU32Cells opt (regTag, regVal)) :
    identRegId regTag regVal = opt.getD 0#32 := by
  cases opt with
  | none => cases (h : regTag = 0#32); rfl
  | some v => obtain ⟨h1, h2⟩ := (h : regTag = 1#32 ∧ regVal = v); subst h1; subst h2; rfl

/-- The `pre_key_id` cells give Pack's `hopkTag` and `hopkVal`. -/
theorem w8bPack_opk {opt : Option (BitVec 32)} {opkTag opkVal : BitVec 32}
    (h : w8bOptU32Cells opt (opkTag, opkVal)) :
    (opkTag = if opt.isSome then 1#32 else 0#32) ∧ (∀ v, opt = some v → opkVal = v) := by
  cases opt with
  | none => exact ⟨by rw [show opkTag = 0#32 from h]; rfl, fun _ hv => nomatch hv⟩
  | some v =>
    obtain ⟨h1, h2⟩ := (h : opkTag = 1#32 ∧ opkVal = v)
    exact ⟨by rw [show opkTag = 1#32 from h1]; rfl, fun _ hv => by cases hv; exact h2⟩

/-- Unpacks a 32-byte vector into four 64-bit words using kernel-checked `pointsTo64_eq_bytes8`. -/
theorem w8b_exists_words4_of_vector32 (v : List.Vector (BitVec 8) 32) :
    ∃ ik0 ik1 ik2 ik3 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ v.toList) =
        (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  refine ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0,
    b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8,
    b23 ++ b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16,
    b31 ++ b30 ++ b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24,
    fun a => ?_⟩
  change (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]) = _
  rw [ReceiveRatchetFrom.pointsTo64_eq_bytes8 a b0 b1 b2 b3 b4 b5 b6 b7,
    ReceiveRatchetFrom.pointsTo64_eq_bytes8 (a + 8#64) b8 b9 b10 b11 b12 b13 b14 b15,
    ReceiveRatchetFrom.pointsTo64_eq_bytes8 (a + 16#64) b16 b17 b18 b19 b20 b21 b22 b23,
    ReceiveRatchetFrom.pointsTo64_eq_bytes8 (a + 24#64) b24 b25 b26 b27 b28 b29 b30 b31]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- 7-way split of `memRegion sp' 296` for epilogue refolding. -/
theorem w8b_memRegion296_full_split (sp' : BitVec 64) :
    memRegion sp' 296 =
      memRegion sp' 12 ∗
      memRegion (sp' + 12#64) 4 ∗
      memRegion (sp' + 16#64) 96 ∗
      memRegion (sp' + 112#64) 32 ∗
      memRegion (sp' + 144#64) 32 ∗
      memRegion (sp' + 176#64) 112 ∗
      memRegion (sp' + 288#64) 8 := by
  rw [show (296 : Nat) = 12 + (4 + (96 + (32 + (32 + (112 + 8))))) by decide,
    Prost.memRegion_split sp' 12 284 (by decide),
    Prost.memRegion_split (sp' + 12#64) 4 280 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64) 96 184 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64) 32 152 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64 + 32#64) 32 120 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64 + 32#64 + 32#64) 112 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Packs the 96-byte spill region `sp' + 16 .. 112` into `memRegion (sp' + 16) 96`. -/
theorem w8b_spills96_entails_memRegion (sp' : BitVec 64)
    (w16 w20 w24 w28 w48 w52 w56 w60 w68 : BitVec 32)
    (w32 w40 w72 w80 w88 w96 w104 : BitVec 64) :
    ((sp' + 16#64) ↦₃₂ w16) ∗ ((sp' + 20#64) ↦₃₂ w20) ∗
    ((sp' + 24#64) ↦₃₂ w24) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
    ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
    ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 52#64) ↦₃₂ w52) ∗
    ((sp' + 56#64) ↦₃₂ w56) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗
    memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
    ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
    ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
    ((sp' + 104#64) ↦₆₄ w104) ⊢
      memRegion (sp' + 16#64) 96 := by
  rw [show (96 : Nat) =
      4 + (4 + (4 + (4 + (8 + (8 + (4 + (4 +
        (4 + (4 + (4 + (4 + (8 + (8 + (8 + (8 + 8)))))))))))))))
      by decide,
    Prost.memRegion_split (sp' + 16#64) 4 92 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64) 4 88 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64) 4 84 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64) 4 80 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64) 4 60 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64) 4 56 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64) 4 52 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64) 4 48 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64)
      4 44 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64)
      4 40 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64) 8 32 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo32_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono (pointsTo32_entails_memRegion _ _)
                    (sepConj_mono (pointsTo32_entails_memRegion _ _)
                      (sepConj_mono_right
                        (sepConj_mono (pointsTo32_entails_memRegion _ _)
                          (sepConj_mono (pointsTo64_entails_memRegion _ _)
                            (sepConj_mono (pointsTo64_entails_memRegion _ _)
                              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                  (pointsTo64_entails_memRegion _ _))))))))))))))))

/-! ## 2. The Untouched Residue -/

theorem w8bPack_open3 {φ1 φ2 φ3 : Prop} {P1 P2 P3 : Bool → SepProp} {F Q : SepProp}
    (h : ∀ a1 a2 a3 : Bool, φ1 → φ2 → φ3 → (P1 a1 ∗ P2 a2 ∗ P3 a3 ∗ F ⊢ Q)) :
    (⌜φ1⌝ ∗ ∃∗ a1 : Bool, P1 a1) ∗ (⌜φ2⌝ ∗ ∃∗ a2 : Bool, P2 a2) ∗
      (⌜φ3⌝ ∗ ∃∗ a3 : Bool, P3 a3) ∗ F ⊢ Q := by
  refine Entails.trans (Entails.of_eq (Q := ⌜φ1⌝ ∗ ⌜φ2⌝ ∗ ⌜φ3⌝ ∗ (∃∗ a1 : Bool, P1 a1) ∗
    (∃∗ a2 : Bool, P2 a2) ∗ (∃∗ a3 : Bool, P3 a3) ∗ F) (by ac_rfl)) ?_
  refine Entails.pure_left fun h1 => ?_
  refine Entails.pure_left fun h2 => ?_
  refine Entails.pure_left fun h3 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun a3 => ?_
  refine Entails.sepExists_elim fun a2 => ?_
  refine Entails.sepExists_elim fun a1 => ?_
  exact h a1 a2 a3 h1 h2 h3

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
