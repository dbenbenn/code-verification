/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Specifications.AsmConstants
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# `PreKeySignalMessage::try_from`: `IdentityKey::try_from` Stage (`+0x830 → +0x864 / +0x978`)

Symbolic execution of the `IdentityKey::try_from` stage from `+0x830`, computing
`registration_id.unwrap_or_default()` in `w27` and branching to `IdentOkState` (`+0x864`) on
`.ok ipk` or `IdentErrState` (`+0x978`) with exact `speAt` error payload on `.error e`.
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
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `registration_id.unwrap_or_default()` as computed by
`ldr w8, [sp, #0x30]; ldr w9, [sp, #0x34]; tst w8, #1; csel w27, w9, wzr, ne`. -/
@[expose] def identRegId (regTag regVal : BitVec 32) : BitVec 32 :=
  if regTag &&& 1#32 = 0#32 then 0#32 else regVal

theorem identRegId_of_optU32 (regTag regVal : BitVec 32) (o : Option (BitVec 32))
    (h : if o.isSome then regTag = 1#32 ∧ some regVal = o else regTag = 0#32) :
    identRegId regTag regVal = o.getD 0#32 := by
  cases o with
  | none => subst h; rfl
  | some v => rcases h with ⟨rfl, hv⟩; cases hv; rfl

private theorem identRegId_tst (regTag : BitVec 32) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 regTag &&& 4294967297#64) == 0#32) =
      (regTag &&& 1#32 == 0#32) := by
  apply congrArg (· == 0#32)
  bv_bits

private theorem identRegId_csel (regTag regVal : BitVec 32) :
    (if ¬(BitVec.truncate 32 (BitVec.zeroExtend 64 regTag &&& 4294967297#64) == 0#32) = true then
        BitVec.truncate 64 regVal else 0#64) = (identRegId regTag regVal).zeroExtend 64 := by
  rw [identRegId_tst]
  unfold identRegId
  by_cases h : regTag &&& 1#32 = 0#32 <;> simp [h]

/-- The untouched tail `out + 16 .. 40` of the `IdentityKey::try_from` result as words
(`ldur q0, [x24, #8]; ldur q1, [x24, #0x18]` read `sp' + 320 .. 352`). -/
theorem memRegion24_words3 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion32_words4 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) := by
  rw [ProofLib.memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd]

private theorem ik_words3_to_memRegion24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion24_words3 a]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (Entails.sepExists_intro w2))

/-- For any `PublicKey.deserialize ik = .error e`, the 5 words left at `sp' + 312 .. 352` plus the
untouched 8-byte region `sp' + 352 .. 360` pack into `speAt A fn (sp' + 312#64) e`. -/
private theorem ik_errWords5_memRegion8_entails_speAt (A : RustAlloc) (fn : List (BitVec 8))
    {ik : List (BitVec 8)} {e : SignalProtocolError} (hik : PublicKey.deserialize ik = .error e)
    (sp' w2 w3 w4 : BitVec 64) :
    ((sp' + 312#64) ↦₆₄ (ikErrWords e).1) ∗ ((sp' + 320#64) ↦₆₄ (ikErrWords e).2) ∗
      ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
      memRegion (sp' + 352#64) 8 ⊢
      speAt A fn (sp' + 312#64) e := by
  have hm24 := ik_words3_to_memRegion24 (sp' + 328#64) w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm24
  have hm32 :
      ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
        memRegion (sp' + 352#64) 8 ⊢
      memRegion (sp' + 328#64) 32 := by
    rw [show (32 : Nat) = 24 + 8 by decide,
      ProofLib.memRegion_split (sp' + 328#64) 24 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
    exact sepConj_mono_left (by simpa only [sepConj_assoc] using hm24)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hm32)) ?_
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
    ikErrWords_entails_speAt hik A fn (sp' + 312#64)

/-- Companion unpacker for `ErrTailC.e_978_wpE`: under `PublicKey.deserialize ik = .error e`,
`speAt A fn (sp' + 312#64) e` splits back into `memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8`
(since all `PublicKey::deserialize` error variants carry plain trailing bytes at `+16..+48`). -/
theorem speAt_deserialize_err_split_312 {A : RustAlloc} {fn : List (BitVec 8)}
    {ik : List (BitVec 8)} {e : SignalProtocolError} (hik : PublicKey.deserialize ik = .error e)
    (sp' : BitVec 64) :
    speAt A fn (sp' + 312#64) e ⊢
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
  have h16_40 : ∀ a : BitVec 64,
      memRegion a 8 ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 ⊢
        memRegion a 40 ∗ memRegion (a + 40#64) 8 := by
    intro a
    rw [show (32 : Nat) = 24 + 8 by decide,
      ProofLib.memRegion_split (a + 16#64) 24 8 (by decide),
      show (40 : Nat) = 8 + (8 + 24) by decide,
      ProofLib.memRegion_split a 8 (8 + 24) (by decide),
      ProofLib.memRegion_split (a + 8#64) 8 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.refl _
  rcases deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · unfold speAt
    rw [show (40 : Nat) = 8 + 32 by decide,
      ProofLib.memRegion_split (sp' + 312#64 + 8#64) 8 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _))
      (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h16_40 (sp' + 312#64))
  · unfold speAt
    rw [show (39 : Nat) = 7 + 32 by decide,
      ProofLib.memRegion_split (sp' + 312#64 + asm64% (spePayloadOff + 1)) 7 32 (by decide)]
    have hb8 : ((sp' + 320#64) ↦₈ t) ∗ memRegion (sp' + 321#64) 7 ⊢ memRegion (sp' + 320#64) 8 := by
      rw [show (8 : Nat) = 1 + 7 by decide,
        ProofLib.memRegion_split (sp' + 320#64) 1 7 (by decide), ProofLib.memRegion_one]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (Entails.sepExists_intro t)
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm) (sepConj_mono_left hb8))) ?_
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h16_40 (sp' + 312#64)
  · unfold speAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo64_entails_memRegion _ _))) ?_
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h16_40 (sp' + 312#64)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
