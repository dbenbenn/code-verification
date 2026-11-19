/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPostLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWShared
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: Missing-Field Error Continuations (`PreKeyPresenceErrW`)

Proves `preKeyPresenceErrW_proof` (`+0x460 → +0x5e0` / `+0x61c` / `+0x66c` / `+0x678 → +0x504 → ret`)
when any of `base_key`, `identity_key`, `message`, or `signed_pre_key_id` is `none`.
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
open CryptoVerification.LibsignalTripleRatchet.Wire
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
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

theorem w8b_memRegion296_split96_104 (sp' : BitVec 64) :
    memRegion sp' 296 ⊢
      ∃∗ w104 : BitVec 64, ∃∗ w96 : BitVec 64,
        memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
          memRegion (sp' + 112#64) 184 := by
  rw [show (296 : Nat) = 96 + (8 + (8 + 184)) by decide,
    Prost.memRegion_split sp' 96 200 (by decide),
    Prost.memRegion_split (sp' + 96#64) 8 192 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 184 (by decide),
    ProofLib.memRegion_eight (sp' + 96#64),
    ProofLib.memRegion_eight (sp' + 96#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem w8b_memRegion296_repack96_104 (sp' w96 w104 : BitVec 64) :
    memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
      memRegion (sp' + 112#64) 184 ⊢ memRegion sp' 296 := by
  rw [show (296 : Nat) = 96 + (8 + (8 + 184)) by decide,
    Prost.memRegion_split sp' 96 200 (by decide),
    Prost.memRegion_split (sp' + 96#64) 8 192 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion (sp' + 96#64) w96)
    (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 104#64) w104)))

private theorem w8b_optVecU8Buf_none (A : RustAlloc) (cap ptr len : BitVec 64) :
    optVecU8Buf A cap ptr len none = ⌜cap = noneCap⌝ := rfl

private theorem w8b_optVecU8At_none_entails (A : RustAlloc) (pin : VecPin) (slot : BitVec 64) :
    CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A pin slot none ⊢
      ∃∗ bkp : BitVec 64, ∃∗ bkl : BitVec 64, vecHeader slot noneCap bkp bkl := by
  refine Entails.trans (Wire.optVecU8At_entails_header_buf A pin slot none) ?_
  refine Entails.sepExists_elim fun bkc => Entails.sepExists_elim fun bkp =>
    Entails.sepExists_elim fun bkl => ?_
  rw [w8b_optVecU8Buf_none, sepConj_comm]
  refine Entails.pure_left fun hbkc => ?_
  subst hbkc
  exact Entails.trans
    (Entails.sepExists_intro (P := fun bkl => vecHeader slot noneCap bkp bkl) bkl)
    (Entails.sepExists_intro (P := fun bkp => ∃∗ bkl, vecHeader slot noneCap bkp bkl) bkp)

private theorem w8b_wirePreKeyAt_bk_some_eq (A : RustAlloc) (g : WirePreKeyGhost) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) {bk : List (BitVec 8)} (hbk : m.baseKey = some bk) :
    wirePreKeyAt A g a m =
      (CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.kyberCt a m.kyberCiphertext ∗
        (vecHeader (a + 0x18#64) g.baseKey.cap g.baseKey.ptr (BitVec.ofNat 64 bk.length) ∗
          Wire.vecU8Buf A g.baseKey.cap g.baseKey.ptr bk) ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.identityKey (a + 0x30#64) m.identityKey ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.message (a + 0x48#64) m.message ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x60#64) m.registrationId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x68#64) m.preKeyId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x70#64) m.signedPreKeyId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x78#64) m.kyberPreKeyId) := by
  unfold wirePreKeyAt
  rw [hbk]
  rfl

theorem w8b_memRegion152_of_parts (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 16 ∗
      (memRegion (sp' + 312#64) 48 ∗
        (memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8) ∗
        memRegion (sp' + 440#64) 8) =
      memRegion (sp' + 296#64) 152 := by
  have h80 :
      memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 =
        memRegion (sp' + 360#64) 80 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      (Prost.memRegion_split (sp' + 360#64) 72 8 (by decide)).symm
  have h88 :
      memRegion (sp' + 360#64) 80 ∗ memRegion (sp' + 440#64) 8 =
        memRegion (sp' + 360#64) 88 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      (Prost.memRegion_split (sp' + 360#64) 80 8 (by decide)).symm
  have h136 :
      memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 88 =
        memRegion (sp' + 312#64) 136 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      (Prost.memRegion_split (sp' + 312#64) 48 88 (by decide)).symm
  rw [h80, h88, h136]
  simpa [BitVec.add_assoc, BitVec.reduceAdd] using
    (Prost.memRegion_split (sp' + 296#64) 16 136 (by decide)).symm

theorem w8b_word8_memRegion40_entails_memRegion48 (p w : BitVec 64) :
    (p ↦₆₄ w) ∗ memRegion (p + 8#64) 40 ⊢ memRegion p 48 := by
  rw [show (48 : Nat) = 8 + 40 by decide, Prost.memRegion_split p 8 40 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion p w)

/-- Two consecutive 24-byte `vecHeader`s at `sp' + 312` and `sp' + 336` entail `memRegion (sp' + 312) 48`. -/
theorem w8b_vecHeaders2_entails_memRegion48 (sp' c1 p1 l1 c2 p2 l2 : BitVec 64) :
    vecHeader (sp' + 312#64) c1 p1 l1 ∗ vecHeader (sp' + 336#64) c2 p2 l2 ⊢
      memRegion (sp' + 312#64) 48 := by
  dsimp only [vecHeader]
  rw [ProofLib.memRegion_split (sp' + 312#64) 8 40 (by decide),
    ProofLib.memRegion_split (sp' + 312#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (sp' + 312#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 312#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 312#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))

private theorem w8b_reassoc_61c (S0 S8 P80 P88 P96 Pool Stack W312 M320 P104 Rest : SepProp) :
    S0 ∗ S8 ∗ P80 ∗ P88 ∗ P96 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ (P104 ∗ Rest)) =
      S0 ∗ S8 ∗ P96 ∗ P104 ∗ P80 ∗ P88 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ Rest) := by
  ac_rfl

private theorem w8b_reassoc_66c (S0 S8 P104 P80 P88 Pool Stack W312 M320 P96 Rest : SepProp) :
    S0 ∗ S8 ∗ P104 ∗ P80 ∗ P88 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ (P96 ∗ Rest)) =
      S0 ∗ S8 ∗ P96 ∗ P104 ∗ P80 ∗ P88 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ Rest) := by
  ac_rfl

/-- Regroup `post_ik_none_full_to_61c_wpW` post into `entry_61c_wpX` pre. -/
theorem w8b_open_61c (D1 W0 W8 P80 P88 D2 D3 P96 Pool Stack W312 M320 R : SepProp) :
    (D1 ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ D2 ∗ D3 ∗ P96 ∗ Pool ∗ Stack ∗ W312 ∗ M320) ∗ R =
      D1 ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ D2 ∗ D3 ∗ P96 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ R) := by
  ac_rfl

/-- Regroup `post_msg_none_full_to_66c_wpW` post into `entry_66c_wpX` pre. -/
theorem w8b_open_66c (W0 W8 D1 P104 D2 P80 P88 D3 Pool Stack W312 M320 R : SepProp) :
    (W0 ∗ W8 ∗ D1 ∗ P104 ∗ D2 ∗ P80 ∗ P88 ∗ D3 ∗ Pool ∗ Stack ∗ W312 ∗ M320) ∗ R =
      W0 ∗ W8 ∗ D1 ∗ P104 ∗ D2 ∗ P80 ∗ P88 ∗ D3 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ R) := by
  ac_rfl

/-- Regroup `post_spk_none_full_to_678_wpW` post into `entry_678_wpX` pre. -/
theorem w8b_open_678 (W0 W8 D1 P96 D2 P104 D3 P80 P88 D4 Pool Stack W312 M320 R : SepProp) :
    (W0 ∗ W8 ∗ D1 ∗ P96 ∗ D2 ∗ P104 ∗ D3 ∗ P80 ∗ P88 ∗ D4 ∗ Pool ∗ Stack ∗ W312 ∗ M320) ∗ R =
      W0 ∗ W8 ∗ D1 ∗ P96 ∗ D2 ∗ P104 ∗ D3 ∗ P80 ∗ P88 ∗ D4 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ R) := by
  ac_rfl

/-- Regroup `+0x590` pre for Branch 3 (`msgOpt = none`). -/
theorem w8b_open_msg_none (M48 Pool Stack Ik Pmc Ky Bk W0 W8 P80 P88 P96 P104 Rest : SepProp) :
    (M48 ∗ Pool ∗ Stack) ∗ (Ik ∗ Pmc ∗ Ky ∗ Bk ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ P96 ∗ P104 ∗ Rest) =
      Pmc ∗ ((M48 ∗ (W0 ∗ W8 ∗ Ik ∗ P104 ∗ Bk ∗ P80 ∗ P88 ∗ Ky ∗ Pool ∗ Stack)) ∗ (P96 ∗ Rest)) := by
  ac_rfl

/-- Regroup `+0x590` pre for `msgOpt = some msg` (`post_msg_some_to_5a4_wpW`). -/
theorem w8b_open_msg_some (M48 Pool Stack Ik Pmc Msg Ky Bk W0 W8 P80 P88 P96 P104 Rest : SepProp) :
    (M48 ∗ Pool ∗ Stack) ∗ (Ik ∗ (Pmc ∗ Msg) ∗ Ky ∗ Bk ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ P96 ∗ P104 ∗ Rest) =
      Pmc ∗ ((M48 ∗ Pool ∗ Stack) ∗ (Msg ∗ Ik ∗ Ky ∗ Bk ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ P96 ∗ P104 ∗ Rest)) := by
  ac_rfl

/-- Regroup `+0x5a4` pre for Branch 4 (`spkOpt = none`). -/
theorem w8b_open_spk_none (M48 Pool Stack Msg Ik Ky Bk W0 W8 P80 P88 P96 P104 Rest : SepProp) :
    (M48 ∗ Pool ∗ Stack) ∗ (Msg ∗ Ik ∗ Ky ∗ Bk ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ P96 ∗ P104 ∗ Rest) =
      (M48 ∗ (W0 ∗ W8 ∗ Msg ∗ P96 ∗ Ik ∗ P104 ∗ Bk ∗ P80 ∗ P88 ∗ Ky ∗ Pool ∗ Stack)) ∗ Rest := by
  ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
