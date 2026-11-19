/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBB -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrAt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec

/-!
# `PreKeySignalMessage::try_from`: Missing-Field and Key-Deserialization Error Tails

Proves word-level and exact-`pksmErrE` error entry blocks (`+0x5e0`, `+0x61c`, `+0x66c`,
`+0x678`, `+0x7a8` → `+0x504`) for missing required protobuf fields and `base_key`
`PublicKey::deserialize` errors.
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
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

private theorem etb_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Q' Qp : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hs, ⟨hpc, hrun, Pf, hmf, hQ, hv⟩ | hpan⟩
  · exact ⟨sf, hs, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hQ, hv⟩⟩
  · exact ⟨sf, hs, Or.inr hpan⟩

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
attribute [local simp, local wp_norm] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

/-! ## 1. Word-Level Entry Blocks (`+0x5e0`, `+0x61c`, `+0x66c`, `+0x678`, `+0x7a8`) -/

/-- Register-level `SignalProtocolError` payload invariant at `+0x7a8` (`entry_7a8_wpE`), where
`and x10, x10, #0xff; orr x8, x8, x10; stp x9, x8, [x19, #8]` stores tag word `x9` at `sret + 8`
and payload word `x8 ||| (x10 &&& 255#64)` at `sret + 16`:
- `.noKeyTypeIdentifier`: `x9 = speWord 7` (`x10` is untouched on `disc = 0` at `+0x5c0`);
- `.badKeyType t`: `x9 = speWord 8` and low byte `(x8 ||| (x10 &&& 255#64)).truncate 8 = t`;
- `.badKeyLength n`: `x9 = speWord 9` and `(x8 ||| (x10 &&& 255#64)) = BitVec.ofNat 64 n`;
- `.invalidKeyAgreement`: `x9 = speWord 10`. -/
@[expose] def speWordsOf (e : SignalProtocolError) (x9v x8v x10v : BitVec 64) : Prop :=
  match e with
  | .noKeyTypeIdentifier => x9v = speWord 7
  | .badKeyType t => x9v = speWord 8 ∧ (x8v ||| (x10v &&& 255#64)).truncate 8 = t
  | .badKeyLength n => x9v = speWord 9 ∧ (x8v ||| (x10v &&& 255#64)) = BitVec.ofNat 64 n
  | .invalidKeyAgreement => x9v = speWord 10
  | _ => False

theorem etb_speWordsOf_noKeyType (x8v x10v : BitVec 64) :
    speWordsOf .noKeyTypeIdentifier (speWord 7) x8v x10v := rfl

theorem etb_speWordsOf_badKeyType (t : BitVec 8) :
    speWordsOf (.badKeyType t) (speWord 8) 0#64 (t.zeroExtend 64) :=
  ⟨rfl, by bv_bits⟩

theorem etb_speWordsOf_badKeyLength (n : Nat) :
    speWordsOf (.badKeyLength n) (speWord 9)
      (BitVec.ofNat 64 n &&& (-256#64)) (BitVec.ofNat 64 n) :=
  ⟨rfl, by bv_bits⟩

theorem etb_speWordsOf_invalidKeyAgreement (x8v x10v : BitVec 64) :
    speWordsOf .invalidKeyAgreement (speWord 10) x8v x10v := rfl

private theorem etb_memRegion248_words2 (sret : BitVec 64) :
    memRegion sret 248 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ memRegion (sret + 16#64) 232 := by
  rw [show (248 : Nat) = 8 + (8 + 232) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    ProofLib.memRegion_eight sret,
    ProofLib.memRegion_eight (sret + 8#64),
    sepExists_sepConj_left]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]

private theorem etb_memRegion248_words3 (sret : BitVec 64) :
    memRegion sret 248 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
          memRegion (sret + 24#64) 224 := by
  rw [etb_memRegion248_words2 sret, show (232 : Nat) = 8 + 224 by decide,
    Prost.memRegion_split (sret + 16#64) 8 224 (by decide),
    ProofLib.memRegion_eight (sret + 16#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]

/-- Packs the three words written at `sret .. sret + 24` by `+0x7a8 .. +0x7bc` plus trailing
`memRegion (sret + 24) 224` into exact `pksmErrE A fn sret e`. -/
theorem etb_speWordsOf_entails_pksmErrE (A : RustAlloc) (fn : List (BitVec 8))
    (sret x9v x8v x10v : BitVec 64) (e : SignalProtocolError)
    (hw : speWordsOf e x9v x8v x10v) :
    (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x9v) ∗
      ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗ memRegion (sret + 24#64) 224 ⊢
      pksmErrE A fn sret e := by
  cases e with
  | noKeyTypeIdentifier =>
    subst hw
    have hm : ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗ memRegion (sret + 24#64) 224 ⊢
        memRegion (sret + 16#64) 232 := by
      rw [show (232 : Nat) = 8 + 224 by decide,
        Prost.memRegion_split (sret + 16#64) 8 224 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (pointsTo64_entails_memRegion (sret + 16#64) _)
    exact Entails.trans (sepConj_mono_right (sepConj_mono_right hm))
      (errCells_noKeyType A fn sret)
  | badKeyType t =>
    obtain ⟨rfl, ht⟩ := hw
    exact pksm0c_errCells_badKeyType_word A fn sret (x8v ||| (x10v &&& 255#64)) t ht
  | badKeyLength n =>
    obtain ⟨rfl, hn⟩ := hw
    rw [hn]
    exact errCells_badKeyLength A fn sret n
  | invalidKeyAgreement =>
    subst hw
    have hm : ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗ memRegion (sret + 24#64) 224 ⊢
        memRegion (sret + 16#64) 232 := by
      rw [show (232 : Nat) = 8 + 224 by decide,
        Prost.memRegion_split (sret + 16#64) 8 224 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (pointsTo64_entails_memRegion (sret + 16#64) _)
    exact Entails.trans (sepConj_mono_right (sepConj_mono_right hm))
      (errCells_invalidKeyAgreement A fn sret)
  | _ => exact False.elim hw

/-- Absorbs any heap/rodata residue `R_heap` alongside `pksmErrE A fn sret e` into
`pksmErrE A fn sret e ∗ anyHeap` (for final epilogue close). -/
theorem etb_pksmErrE_absorb_heap (A : RustAlloc) (fn : List (BitVec 8)) (sret : BitVec 64)
    (e : SignalProtocolError) (R_heap F_epi : SepProp) :
    pksmErrE A fn sret e ∗ R_heap ∗ F_epi ⊢
      (pksmErrE A fn sret e ∗ anyHeap) ∗ F_epi := by
  rw [← sepConj_assoc]
  exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap R_heap))

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
