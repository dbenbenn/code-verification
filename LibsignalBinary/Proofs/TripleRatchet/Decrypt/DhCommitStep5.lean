/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
import ProofLib.Sep
import ProofLib.SepLogic.WPp

/-!
# DH Step Commit Sub-Segment 5 (`dhCommit_step5`)

Verifies `+0xb98 → +0x3e4`: commits `sender_chain = some ⟨newSenderKey, senderChainKey⟩`, stages
`receiverChainKey` across `sp + 0x2b0..0x2d4`, reassembles stack scratch regions, and branches to
`segConsumeMsgKeyPC`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 15. Sub-Segment 5 Wrapper (`+0xb98 → +0x3e4`) -/

namespace DhCommitFacts

abbrev packLE64 := pack64
abbrev packLE32 := pack32

abbrev sckWord0 (ck : ChainKey) : BitVec 64 := pack64 ((chainKeyBytes ck).take 8)
abbrev sckWord8 (ck : ChainKey) : BitVec 64 := pack64 (((chainKeyBytes ck).drop 8).take 8)
abbrev sckWord16 (ck : ChainKey) : BitVec 32 := pack32 (((chainKeyBytes ck).drop 16).take 4)
abbrev sckWord20 (ck : ChainKey) : BitVec 64 := pack64 (((chainKeyBytes ck).drop 20).take 8)
abbrev sckWord28 (ck : ChainKey) : BitVec 64 := pack64 ((chainKeyBytes ck).drop 28)

theorem pointsToBytes_len4_eq_pointsTo32 (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 4) : (a ↦ₛ bs) = (a ↦₃₂ pack32 bs) :=
  pointsToBytes_4_eq_pointsTo32 a h

theorem pointsToBytes_len16_to_cells (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 16) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 (bs.take 8)) ∗ ((a + 8#64) ↦₆₄ pack64 (bs.drop 8)) :=
  pointsToBytes_16_eq_pointsTo64 a h

theorem pointsToBytes_len32_to_cells (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₆₄ pack64 (bs.take 8)) ∗
      ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
      ((a + 16#64) ↦₆₄ pack64 ((bs.drop 16).take 8)) ∗
      ((a + 24#64) ↦₆₄ pack64 (bs.drop 24)) :=
  pointsToBytes_32_eq_pointsTo64 a h

theorem elim_memRegion_64 {m : Memory} {base : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion base 64 ∗ R) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64,
      m ⊨ (((base ↦₆₄ v0) ∗
            ((base + 8#64) ↦₆₄ v1) ∗
            ((base + 16#64) ↦₆₄ v2) ∗
            ((base + 24#64) ↦₆₄ v3) ∗
            ((base + 32#64) ↦₆₄ v4) ∗
            ((base + 40#64) ↦₆₄ v5) ∗
            ((base + 48#64) ↦₆₄ v6) ∗
            ((base + 56#64) ↦₆₄ v7)) ∗ R) := by
  have h1 := memRegion_split base 32 32 (by decide)
  rw [show (32 + 32 : Nat) = 64 from rfl] at h1
  rw [h1, sepConj_assoc] at h
  obtain ⟨v0, v1, v2, v3, h⟩ := elim_memRegion_32 h
  have h' : m ⊨ memRegion (base + 32#64) 32 ∗
      (((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗ ((base + 16#64) ↦₆₄ v2) ∗
        ((base + 24#64) ↦₆₄ v3)) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h
    ac_rfl
  obtain ⟨v4, v5, v6, v7, h'⟩ := elim_memRegion_32 h'
  refine ⟨v0, v1, v2, v3, v4, v5, v6, v7, ?_⟩
  rw [show base + 32#64 + 8#64 = base + 40#64 from add_assoc_const _ _ _ _,
      show base + 32#64 + 16#64 = base + 48#64 from add_assoc_const _ _ _ _,
      show base + 32#64 + 24#64 = base + 56#64 from add_assoc_const _ _ _ _] at h'
  refine Satisfies.mono (Entails.of_eq ?_) h'
  ac_rfl

theorem elim_memRegion_80 {m : Memory} {base : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion base 80 ∗ R) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64,
      m ⊨ (((base ↦₆₄ v0) ∗
            ((base + 8#64) ↦₆₄ v1) ∗
            ((base + 16#64) ↦₆₄ v2) ∗
            ((base + 24#64) ↦₆₄ v3) ∗
            ((base + 32#64) ↦₆₄ v4) ∗
            ((base + 40#64) ↦₆₄ v5) ∗
            ((base + 48#64) ↦₆₄ v6) ∗
            ((base + 56#64) ↦₆₄ v7) ∗
            ((base + 64#64) ↦₆₄ v8) ∗
            ((base + 72#64) ↦₆₄ v9)) ∗ R) := by
  have h1 := memRegion_split base 64 16 (by decide)
  rw [show (64 + 16 : Nat) = 80 from rfl] at h1
  rw [h1, sepConj_assoc] at h
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, h⟩ := elim_memRegion_64 h
  have h' : m ⊨ memRegion (base + 64#64) 16 ∗
      (((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗ ((base + 16#64) ↦₆₄ v2) ∗
        ((base + 24#64) ↦₆₄ v3) ∗ ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5) ∗
        ((base + 48#64) ↦₆₄ v6) ∗ ((base + 56#64) ↦₆₄ v7)) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h
    ac_rfl
  obtain ⟨v8, v9, h'⟩ := elim_memRegion_16 h'
  refine ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, ?_⟩
  rw [show base + 64#64 + 8#64 = base + 72#64 from add_assoc_const _ _ _ _] at h'
  refine Satisfies.mono (Entails.of_eq ?_) h'
  ac_rfl

theorem elim_memRegion_20 {m : Memory} {base : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion base 20 ∗ R) :
    ∃ (v0 v1 : BitVec 64) (v2 : BitVec 32),
      m ⊨ (((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗ ((base + 16#64) ↦₃₂ v2)) ∗ R) := by
  have h1 := memRegion_split base 16 4 (by decide)
  rw [show (16 + 4 : Nat) = 20 from rfl] at h1
  rw [h1, sepConj_assoc] at h
  obtain ⟨v0, v1, h⟩ := elim_memRegion_16 h
  have h' : m ⊨ memRegion (base + 16#64) 4 ∗ (((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1)) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h
    ac_rfl
  obtain ⟨v2, h'⟩ := elim_memRegion_4 h'
  refine ⟨v0, v1, v2, ?_⟩
  refine Satisfies.mono (Entails.of_eq ?_) h'
  ac_rfl

theorem pointsTo64_2_entails_memRegion (base : BitVec 64) (v0 v1 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1)) ⊢ memRegion base 16 := by
  sep_interval

theorem pointsTo64_4_entails_memRegion (base : BitVec 64) (v0 v1 v2 v3 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗ ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3)) ⊢
      memRegion base 32 := by
  sep_interval

theorem pointsTo64_10_entails_memRegion (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗ ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
     ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5) ∗ ((base + 48#64) ↦₆₄ v6) ∗
     ((base + 56#64) ↦₆₄ v7) ∗ ((base + 64#64) ↦₆₄ v8) ∗ ((base + 72#64) ↦₆₄ v9)) ⊢
      memRegion base 80 := by
  sep_interval

theorem pointsToBytes_rck_take20 (base : BitVec 64) (ck : ChainKey) :
    (((base ↦ₛ (chainKeyBytes ck).take 16) ∗
      ((base + 16#64) ↦ₛ ((chainKeyBytes ck).drop 16).take 4)) =
     (base ↦ₛ (chainKeyBytes ck).take 20)) :=
  (pointsToBytes_chainKey_take20 base ck).symm

theorem zip_map_fst_snd {α β : Type} (xs : List (α × β)) :
    (xs.map Prod.fst).zip (xs.map Prod.snd) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a, b⟩
    simp [ih]

abbrev evictGcs (gcs : List (ChainGhost × ReceiverChain)) :
    List (ChainGhost × ReceiverChain) :=
  evictList gcs

theorem map_snd_evictGcs (gcs : List (ChainGhost × ReceiverChain)) :
    (evictGcs gcs).map Prod.snd = RatchetState.evictReceiverChains (gcs.map Prod.snd) := by
  simp [evictGcs, evictList, RatchetState.evictReceiverChains]

theorem map_snd_zip_append (gs : List ChainGhost) (cs : List ReceiverChain)
    (g : ChainGhost) (c : ReceiverChain) (h : gs.length = cs.length) :
    (gs.zip cs ++ [(g, c)]).map Prod.snd = cs ++ [c] := by
  rw [List.map_append, List.map_snd_zip (by omega)]
  rfl

theorem vecAt_chains_eq (A : RustAlloc) (sp cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    vecAt A 104 8 (chainAt A) (sp + 0x38#64) cap ptr gcs =
      ((sp + 0x38#64) ↦₆₄ cap) ∗
      ((sp + 0x40#64) ↦₆₄ ptr) ∗
      ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
      vecBuf A 104 8 (chainAt A) cap ptr gcs := by
  unfold vecAt vecHeader
  rw [show sp + 0x38#64 + 8#64 = sp + 0x40#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 16#64 = sp + 0x48#64 from add_assoc_const _ _ _ _]
  ac_rfl

theorem reachesOrPanic_mono [LibsignalPlacement] {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Unit}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h1 : ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s P)
    (h2 : ∀ sf, s.mem.KeepsFrozen sf.mem → sf.symtab = s.symtab → P sf → Q sf) :
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q :=
  ReachesOrPanic.seq h1 (fun sf hkf hsym hP => ReachesOrPanic.done (h2 sf hkf hsym hP))

end DhCommitFacts

open DhCommitFacts

/-- Generic Sub-segment 5 (`+0xb98 → +0x3e4`) parameterized over `prog` and `entry`. -/
theorem dhCommit_step5_of_wp [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (img : Unit) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (x : TryDecryptGhost) (pad : List (BitVec 8))
    (sc : SenderChain) (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (senderChainKey : ChainKey) (msgW : BitVec 32)
    (Frame R : SepProp) (s0 s : State)
    (sp : BitVec 64) (hsp_def : sp = s0.sp - 1504#64)
    (_hpad : pad.length = 100)
    (hwp5 : ∀ (sck16 rck16 msgW oldTag oldSck16 v2d0 : BitVec 32)
      (oldSpk0 oldSpk1 oldSpk2 oldSpk3 oldSk0 oldSk1 oldSk2 oldSk3
       oldSck0 oldSck1 oldSck2 oldSck3
       spk0 spk1 spk2 spk3 sk0 sk1 sk2 sk3
       sck0 sck1 sck2 sck3
       rck0 rck1 rck2 rck3
       v2b0 v2b8 v2c0 v2c8
       v450 v458 v460 v468 v470 v478 v480 v488 v490 v498 : BitVec 64),
      SepWP prog (entry + 0x3e4#64) s
        (((sp + 0x8#64) ↦₃₂ sck16) ∗
         ((sp + 0x10#64) ↦₃₂ rck16) ∗
         ((sp + 0x1c#64) ↦₃₂ msgW) ∗
         ((sp + 0x50#64) ↦₃₂ oldTag) ∗
         ((sp + 0x54#64) ↦₆₄ oldSpk0) ∗
         ((sp + 0x5c#64) ↦₆₄ oldSpk1) ∗
         ((sp + 0x64#64) ↦₆₄ oldSpk2) ∗
         ((sp + 0x6c#64) ↦₆₄ oldSpk3) ∗
         ((sp + 0x74#64) ↦₆₄ oldSk0) ∗
         ((sp + 0x7c#64) ↦₆₄ oldSk1) ∗
         ((sp + 0x84#64) ↦₆₄ oldSk2) ∗
         ((sp + 0x8c#64) ↦₆₄ oldSk3) ∗
         ((sp + 0x94#64) ↦₆₄ oldSck0) ∗
         ((sp + 0x9c#64) ↦₆₄ oldSck1) ∗
         ((sp + 0xa4#64) ↦₃₂ oldSck16) ∗
         ((sp + 0xa8#64) ↦₆₄ oldSck2) ∗
         ((sp + 0xb0#64) ↦₆₄ oldSck3) ∗
         ((sp + 0x2b0#64) ↦₆₄ v2b0) ∗
         ((sp + 0x2b8#64) ↦₆₄ v2b8) ∗
         ((sp + 0x2c0#64) ↦₆₄ v2c0) ∗
         ((sp + 0x2c8#64) ↦₆₄ v2c8) ∗
         ((sp + 0x2d0#64) ↦₃₂ v2d0) ∗
         ((sp + 0x400#64) ↦₆₄ spk0) ∗
         ((sp + 0x408#64) ↦₆₄ spk1) ∗
         ((sp + 0x410#64) ↦₆₄ spk2) ∗
         ((sp + 0x418#64) ↦₆₄ spk3) ∗
         ((sp + 0x420#64) ↦₆₄ sk0) ∗
         ((sp + 0x428#64) ↦₆₄ sk1) ∗
         ((sp + 0x430#64) ↦₆₄ sk2) ∗
         ((sp + 0x438#64) ↦₆₄ sk3) ∗
         ((sp + 0x450#64) ↦₆₄ v450) ∗
         ((sp + 0x458#64) ↦₆₄ v458) ∗
         ((sp + 0x460#64) ↦₆₄ v460) ∗
         ((sp + 0x468#64) ↦₆₄ v468) ∗
         ((sp + 0x470#64) ↦₆₄ v470) ∗
         ((sp + 0x478#64) ↦₆₄ v478) ∗
         ((sp + 0x480#64) ↦₆₄ v480) ∗
         ((sp + 0x488#64) ↦₆₄ v488) ∗
         ((sp + 0x490#64) ↦₆₄ v490) ∗
         ((sp + 0x498#64) ↦₆₄ v498) ∗
         ((sp + 0x4c0#64) ↦₆₄ rck2) ∗
         ((sp + 0x4c8#64) ↦₆₄ rck3) ∗
         ((sp + 0x4d0#64) ↦₆₄ rck0) ∗
         ((sp + 0x4d8#64) ↦₆₄ rck1) ∗
         ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
         ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
         ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
         ((sp + 0x4f8#64) ↦₆₄ sck1))
        (fun sf P_f =>
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
          sf.readReg64 .x12 = sp + 0x2c0#64 ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = msgW.zeroExtend 64 ∧
          sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
          sf.readReg64 .x30 = s.readReg64 .x30 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (P_f ⊢
            ((sp + 0x8#64) ↦₃₂ sck16) ∗
            ((sp + 0x10#64) ↦₃₂ rck16) ∗
            ((sp + 0x1c#64) ↦₃₂ msgW) ∗
            ((sp + 0x50#64) ↦₃₂ 1#32) ∗
            ((sp + 0x54#64) ↦₆₄ spk0) ∗
            ((sp + 0x5c#64) ↦₆₄ spk1) ∗
            ((sp + 0x64#64) ↦₆₄ spk2) ∗
            ((sp + 0x6c#64) ↦₆₄ spk3) ∗
            ((sp + 0x74#64) ↦₆₄ sk0) ∗
            ((sp + 0x7c#64) ↦₆₄ sk1) ∗
            ((sp + 0x84#64) ↦₆₄ sk2) ∗
            ((sp + 0x8c#64) ↦₆₄ sk3) ∗
            ((sp + 0x94#64) ↦₆₄ sck0) ∗
            ((sp + 0x9c#64) ↦₆₄ sck1) ∗
            ((sp + 0xa4#64) ↦₃₂ sck16) ∗
            ((sp + 0xa8#64) ↦₆₄ sck2) ∗
            ((sp + 0xb0#64) ↦₆₄ sck3) ∗
            ((sp + 0x2b0#64) ↦₆₄ rck2) ∗
            ((sp + 0x2b8#64) ↦₆₄ rck3) ∗
            ((sp + 0x2c0#64) ↦₆₄ rck0) ∗
            ((sp + 0x2c8#64) ↦₆₄ rck1) ∗
            ((sp + 0x2d0#64) ↦₃₂ rck16) ∗
            ((sp + 0x400#64) ↦₆₄ spk0) ∗
            ((sp + 0x408#64) ↦₆₄ spk1) ∗
            ((sp + 0x410#64) ↦₆₄ spk2) ∗
            ((sp + 0x418#64) ↦₆₄ spk3) ∗
            ((sp + 0x420#64) ↦₆₄ sk0) ∗
            ((sp + 0x428#64) ↦₆₄ sk1) ∗
            ((sp + 0x430#64) ↦₆₄ sk2) ∗
            ((sp + 0x438#64) ↦₆₄ sk3) ∗
            ((sp + 0x450#64) ↦₆₄ spk0) ∗
            ((sp + 0x458#64) ↦₆₄ spk1) ∗
            ((sp + 0x460#64) ↦₆₄ spk2) ∗
            ((sp + 0x468#64) ↦₆₄ spk3) ∗
            ((sp + 0x470#64) ↦₆₄ sk0) ∗
            ((sp + 0x478#64) ↦₆₄ sk1) ∗
            ((sp + 0x480#64) ↦₆₄ sk2) ∗
            ((sp + 0x488#64) ↦₆₄ sk3) ∗
            ((sp + 0x490#64) ↦₆₄ sck0) ∗
            ((sp + 0x498#64) ↦₆₄ sck1) ∗
            ((sp + 0x4c0#64) ↦₆₄ rck2) ∗
            ((sp + 0x4c8#64) ↦₆₄ rck3) ∗
            ((sp + 0x4d0#64) ↦₆₄ rck0) ∗
            ((sp + 0x4d8#64) ↦₆₄ rck1) ∗
            ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
            ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
            ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
            ((sp + 0x4f8#64) ↦₆₄ sck1))))
    (hL : prog.CodeLoaded s.mem)
    (hm : s.mem ⊨
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
      memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x50#64) ↦₃₂ 1#32) ∗
      ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      memRegion (sp + 0x190#64) 104 ∗
      memRegion (sp + 0x1f8#64) 0xb8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x14 ∗
      memRegion (sp + 0x2d4#64) 0xfc ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x450#64) 0x50 ∗
      memRegion (sp + 0x4a0#64) 0x20 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x500#64) 96 ∗
      memRegion (sp + 0x560#64) 0x20 ∗
      (Frame ∗ R)) :
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s
      (fun sf =>
        sf.pc = entry + 0x3e4#64 ∧
        sf.status = .Running ∧
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = msgW.zeroExtend 64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          ((sp + 0x50#64) ↦ₛ optSenderChainBytes (some ⟨newSenderKey, senderChainKey⟩) pad) ∗
          memRegion sp 0x20 ∗
          memRegion (sp + 0x140#64) 0x170 ∗
          ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
          ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20) ∗
          memRegion (sp + 0x2d4#64) 0x2ac ∗
          (Frame ∗ R))) := by
  let _ := hsp_def
  have hrck_mid_len : (((chainKeyBytes receiverChainKey).drop 16).take 4).length = 4 := by
    simp [chainKeyBytes_length]
  have hrck_drop20_len : ((chainKeyBytes receiverChainKey).drop 20).length = 16 := by
    simp [chainKeyBytes_length]
  have hrck_take16_len : ((chainKeyBytes receiverChainKey).take 16).length = 16 := by
    simp [chainKeyBytes_length]
  have h_old_spk := pointsToBytes_len32_to_cells (sp + 0x54#64) sc.ratchetKey.publicKey.bytes.toList (by simp)
  rw [show sp + 0x54#64 + 8#64 = sp + 0x5c#64 from add_assoc_const _ _ _ _,
      show sp + 0x54#64 + 16#64 = sp + 0x64#64 from add_assoc_const _ _ _ _,
      show sp + 0x54#64 + 24#64 = sp + 0x6c#64 from add_assoc_const _ _ _ _] at h_old_spk
  have h_old_sk := pointsToBytes_len32_to_cells (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList (by simp)
  rw [show sp + 0x74#64 + 8#64 = sp + 0x7c#64 from add_assoc_const _ _ _ _,
      show sp + 0x74#64 + 16#64 = sp + 0x84#64 from add_assoc_const _ _ _ _,
      show sp + 0x74#64 + 24#64 = sp + 0x8c#64 from add_assoc_const _ _ _ _] at h_old_sk
  have h_old_sck := pointsToBytes_chainKey_eq_cells (sp + 0x94#64) sc.chainKey
  rw [show sp + 0x94#64 + 8#64 = sp + 0x9c#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 16#64 = sp + 0xa4#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 20#64 = sp + 0xa8#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 28#64 = sp + 0xb0#64 from add_assoc_const _ _ _ _] at h_old_sck
  have h_new_spk := pointsToBytes_len32_to_cells (sp + 0x400#64) newSenderKey.publicKey.bytes.toList (by simp)
  rw [show sp + 0x400#64 + 8#64 = sp + 0x408#64 from add_assoc_const _ _ _ _,
      show sp + 0x400#64 + 16#64 = sp + 0x410#64 from add_assoc_const _ _ _ _,
      show sp + 0x400#64 + 24#64 = sp + 0x418#64 from add_assoc_const _ _ _ _] at h_new_spk
  have h_new_sk := pointsToBytes_len32_to_cells (sp + 0x420#64) newSenderKey.privateKey.bytes.toList (by simp)
  rw [show sp + 0x420#64 + 8#64 = sp + 0x428#64 from add_assoc_const _ _ _ _,
      show sp + 0x420#64 + 16#64 = sp + 0x430#64 from add_assoc_const _ _ _ _,
      show sp + 0x420#64 + 24#64 = sp + 0x438#64 from add_assoc_const _ _ _ _] at h_new_sk
  have h_rck_10 := pointsToBytes_len4_eq_pointsTo32 (sp + 0x10#64) (((chainKeyBytes receiverChainKey).drop 16).take 4) hrck_mid_len
  have h_rck_4c0 := pointsToBytes_len16_to_cells (sp + 0x4c0#64) ((chainKeyBytes receiverChainKey).drop 20) hrck_drop20_len
  rw [show sp + 0x4c0#64 + 8#64 = sp + 0x4c8#64 from add_assoc_const _ _ _ _] at h_rck_4c0
  have h_rck_4d0 := pointsToBytes_len16_to_cells (sp + 0x4d0#64) ((chainKeyBytes receiverChainKey).take 16) hrck_take16_len
  rw [show sp + 0x4d0#64 + 8#64 = sp + 0x4d8#64 from add_assoc_const _ _ _ _] at h_rck_4d0
  have hm_2b0 : s.mem ⊨
      memRegion (sp + 0x2b0#64) 16 ∗
      (memRegion (sp + 0x2c0#64) 20 ∗
       memRegion (sp + 0x450#64) 80 ∗
       memRegion sp 8 ∗
       ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
       memRegion (sp + 0xc#64) 4 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 104 ∗
       memRegion (sp + 0x1f8#64) 0xb8 ∗
       memRegion (sp + 0x2d4#64) 0xfc ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
       ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x4a0#64) 0x20 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
       ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
       ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
       ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x500#64) 96 ∗
       memRegion (sp + 0x560#64) 0x20 ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    ac_rfl
  obtain ⟨v2b0, v2b8, hm_2b0⟩ := elim_memRegion_16 hm_2b0
  rw [show sp + 0x2b0#64 + 8#64 = sp + 0x2b8#64 from add_assoc_const _ _ _ _] at hm_2b0
  have hm_2c0 : s.mem ⊨
      memRegion (sp + 0x2c0#64) 20 ∗
      (memRegion (sp + 0x450#64) 80 ∗
       (((sp + 0x2b0#64) ↦₆₄ v2b0) ∗ ((sp + 0x2b8#64) ↦₆₄ v2b8)) ∗
       memRegion sp 8 ∗
       ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
       memRegion (sp + 0xc#64) 4 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 104 ∗
       memRegion (sp + 0x1f8#64) 0xb8 ∗
       memRegion (sp + 0x2d4#64) 0xfc ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
       ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x4a0#64) 0x20 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
       ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
       ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
       ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x500#64) 96 ∗
       memRegion (sp + 0x560#64) 0x20 ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_2b0
    ac_rfl
  obtain ⟨v2c0, v2c8, v2d0, hm_2c0⟩ := elim_memRegion_20 hm_2c0
  rw [show sp + 0x2c0#64 + 8#64 = sp + 0x2c8#64 from add_assoc_const _ _ _ _,
      show sp + 0x2c0#64 + 16#64 = sp + 0x2d0#64 from add_assoc_const _ _ _ _] at hm_2c0
  have hm_450 : s.mem ⊨
      memRegion (sp + 0x450#64) 80 ∗
      ((((sp + 0x2c0#64) ↦₆₄ v2c0) ∗ ((sp + 0x2c8#64) ↦₆₄ v2c8) ∗ ((sp + 0x2d0#64) ↦₃₂ v2d0)) ∗
       (((sp + 0x2b0#64) ↦₆₄ v2b0) ∗ ((sp + 0x2b8#64) ↦₆₄ v2b8)) ∗
       memRegion sp 8 ∗
       ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
       memRegion (sp + 0xc#64) 4 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 104 ∗
       memRegion (sp + 0x1f8#64) 0xb8 ∗
       memRegion (sp + 0x2d4#64) 0xfc ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
       ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x4a0#64) 0x20 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
       ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
       ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
       ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
       ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
       memRegion (sp + 0x500#64) 96 ∗
       memRegion (sp + 0x560#64) 0x20 ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_2c0
    ac_rfl
  obtain ⟨v450, v458, v460, v468, v470, v478, v480, v488, v490, v498, hm_450⟩ :=
    elim_memRegion_80 hm_450
  rw [show sp + 0x450#64 + 8#64 = sp + 0x458#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 16#64 = sp + 0x460#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 24#64 = sp + 0x468#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 32#64 = sp + 0x470#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 40#64 = sp + 0x478#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 48#64 = sp + 0x480#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 56#64 = sp + 0x488#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 64#64 = sp + 0x490#64 from add_assoc_const _ _ _ _,
      show sp + 0x450#64 + 72#64 = sp + 0x498#64 from add_assoc_const _ _ _ _] at hm_450
  let rck16 := packLE32 (((chainKeyBytes receiverChainKey).drop 16).take 4)
  let oldSpk0 := packLE64 (sc.ratchetKey.publicKey.bytes.toList.take 8)
  let oldSpk1 := packLE64 ((sc.ratchetKey.publicKey.bytes.toList.drop 8).take 8)
  let oldSpk2 := packLE64 ((sc.ratchetKey.publicKey.bytes.toList.drop 16).take 8)
  let oldSpk3 := packLE64 (sc.ratchetKey.publicKey.bytes.toList.drop 24)
  let oldSk0 := packLE64 (sc.ratchetKey.privateKey.bytes.toList.take 8)
  let oldSk1 := packLE64 ((sc.ratchetKey.privateKey.bytes.toList.drop 8).take 8)
  let oldSk2 := packLE64 ((sc.ratchetKey.privateKey.bytes.toList.drop 16).take 8)
  let oldSk3 := packLE64 (sc.ratchetKey.privateKey.bytes.toList.drop 24)
  let oldSck0 := sckWord0 sc.chainKey
  let oldSck1 := sckWord8 sc.chainKey
  let oldSck16 := sckWord16 sc.chainKey
  let oldSck2 := sckWord20 sc.chainKey
  let oldSck3 := sckWord28 sc.chainKey
  let spk0 := packLE64 (newSenderKey.publicKey.bytes.toList.take 8)
  let spk1 := packLE64 ((newSenderKey.publicKey.bytes.toList.drop 8).take 8)
  let spk2 := packLE64 ((newSenderKey.publicKey.bytes.toList.drop 16).take 8)
  let spk3 := packLE64 (newSenderKey.publicKey.bytes.toList.drop 24)
  let sk0 := packLE64 (newSenderKey.privateKey.bytes.toList.take 8)
  let sk1 := packLE64 ((newSenderKey.privateKey.bytes.toList.drop 8).take 8)
  let sk2 := packLE64 ((newSenderKey.privateKey.bytes.toList.drop 16).take 8)
  let sk3 := packLE64 (newSenderKey.privateKey.bytes.toList.drop 24)
  let sck0 := sckWord0 senderChainKey
  let sck1 := sckWord8 senderChainKey
  let sck16 := sckWord16 senderChainKey
  let sck2 := sckWord20 senderChainKey
  let sck3 := sckWord28 senderChainKey
  let rck0 := packLE64 (((chainKeyBytes receiverChainKey).take 16).take 8)
  let rck1 := packLE64 (((chainKeyBytes receiverChainKey).take 16).drop 8)
  let rck2 := packLE64 (((chainKeyBytes receiverChainKey).drop 20).take 8)
  let rck3 := packLE64 (((chainKeyBytes receiverChainKey).drop 20).drop 8)
  have hm_wp : s.mem ⊨
      (((sp + 0x8#64) ↦₃₂ sck16) ∗
       ((sp + 0x10#64) ↦₃₂ rck16) ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦₆₄ oldSpk0) ∗
       ((sp + 0x5c#64) ↦₆₄ oldSpk1) ∗
       ((sp + 0x64#64) ↦₆₄ oldSpk2) ∗
       ((sp + 0x6c#64) ↦₆₄ oldSpk3) ∗
       ((sp + 0x74#64) ↦₆₄ oldSk0) ∗
       ((sp + 0x7c#64) ↦₆₄ oldSk1) ∗
       ((sp + 0x84#64) ↦₆₄ oldSk2) ∗
       ((sp + 0x8c#64) ↦₆₄ oldSk3) ∗
       ((sp + 0x94#64) ↦₆₄ oldSck0) ∗
       ((sp + 0x9c#64) ↦₆₄ oldSck1) ∗
       ((sp + 0xa4#64) ↦₃₂ oldSck16) ∗
       ((sp + 0xa8#64) ↦₆₄ oldSck2) ∗
       ((sp + 0xb0#64) ↦₆₄ oldSck3) ∗
       ((sp + 0x2b0#64) ↦₆₄ v2b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ v2b8) ∗
       ((sp + 0x2c0#64) ↦₆₄ v2c0) ∗
       ((sp + 0x2c8#64) ↦₆₄ v2c8) ∗
       ((sp + 0x2d0#64) ↦₃₂ v2d0) ∗
       ((sp + 0x400#64) ↦₆₄ spk0) ∗
       ((sp + 0x408#64) ↦₆₄ spk1) ∗
       ((sp + 0x410#64) ↦₆₄ spk2) ∗
       ((sp + 0x418#64) ↦₆₄ spk3) ∗
       ((sp + 0x420#64) ↦₆₄ sk0) ∗
       ((sp + 0x428#64) ↦₆₄ sk1) ∗
       ((sp + 0x430#64) ↦₆₄ sk2) ∗
       ((sp + 0x438#64) ↦₆₄ sk3) ∗
       ((sp + 0x450#64) ↦₆₄ v450) ∗
       ((sp + 0x458#64) ↦₆₄ v458) ∗
       ((sp + 0x460#64) ↦₆₄ v460) ∗
       ((sp + 0x468#64) ↦₆₄ v468) ∗
       ((sp + 0x470#64) ↦₆₄ v470) ∗
       ((sp + 0x478#64) ↦₆₄ v478) ∗
       ((sp + 0x480#64) ↦₆₄ v480) ∗
       ((sp + 0x488#64) ↦₆₄ v488) ∗
       ((sp + 0x490#64) ↦₆₄ v490) ∗
       ((sp + 0x498#64) ↦₆₄ v498) ∗
       ((sp + 0x4c0#64) ↦₆₄ rck2) ∗
       ((sp + 0x4c8#64) ↦₆₄ rck3) ∗
       ((sp + 0x4d0#64) ↦₆₄ rck0) ∗
       ((sp + 0x4d8#64) ↦₆₄ rck1) ∗
       ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
       ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
       ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
       ((sp + 0x4f8#64) ↦₆₄ sck1)) ∗
      ((memRegion sp 8 ∗
        memRegion (sp + 0xc#64) 4 ∗
        memRegion (sp + 0x14#64) 8 ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x190#64) 104 ∗
        memRegion (sp + 0x1f8#64) 0xb8 ∗
        memRegion (sp + 0x2d4#64) 0xfc ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        memRegion (sp + 0x3f4#64) 12 ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗
        ((sp + 0x448#64) ↦₆₄ sck1) ∗
        memRegion (sp + 0x4a0#64) 0x20 ∗
        memRegion (sp + 0x500#64) 96 ∗
        memRegion (sp + 0x560#64) 0x20 ∗
        Frame) ∗ R) := by
    rw [h_rck_10, h_old_spk, h_old_sk, h_old_sck, h_new_spk, h_new_sk, h_rck_4c0, h_rck_4d0] at hm_450
    refine Satisfies.mono (Entails.of_eq ?_) hm_450
    ac_rfl
  refine ReachesOrPanic.of_sepWP
    (hwp5 sck16 rck16 msgW 1#32 oldSck16 v2d0
      oldSpk0 oldSpk1 oldSpk2 oldSpk3 oldSk0 oldSk1 oldSk2 oldSk3
      oldSck0 oldSck1 oldSck2 oldSck3
      spk0 spk1 spk2 spk3 sk0 sk1 sk2 sk3
      sck0 sck1 sck2 sck3
      rck0 rck1 rck2 rck3
      v2b0 v2b8 v2c0 v2c8
      v450 v458 v460 v468 v470 v478 v480 v488 v490 v498)
    hm_wp hL ?_
  intro sf Pf hpcf hrunf _hkff _hsymf hLf hmf hpostf
  rcases hpostf with ⟨hspf, hsp_alignf, htrf, hx12f, hx19f, hx20f, hx21f, hx22f,
    hx23f, hx24f, hx25f, hx29f, hx30f, hvregsf, hPf⟩
  have hmf' := Satisfies.mono (sepConj_mono_left hPf) hmf
  have h_sc_54 := pointsToBytes_len32_to_cells (sp + 0x54#64) newSenderKey.publicKey.bytes.toList (by simp)
  rw [show sp + 0x54#64 + 8#64 = sp + 0x5c#64 from add_assoc_const _ _ _ _,
      show sp + 0x54#64 + 16#64 = sp + 0x64#64 from add_assoc_const _ _ _ _,
      show sp + 0x54#64 + 24#64 = sp + 0x6c#64 from add_assoc_const _ _ _ _] at h_sc_54
  have h_sc_74 := pointsToBytes_len32_to_cells (sp + 0x74#64) newSenderKey.privateKey.bytes.toList (by simp)
  rw [show sp + 0x74#64 + 8#64 = sp + 0x7c#64 from add_assoc_const _ _ _ _,
      show sp + 0x74#64 + 16#64 = sp + 0x84#64 from add_assoc_const _ _ _ _,
      show sp + 0x74#64 + 24#64 = sp + 0x8c#64 from add_assoc_const _ _ _ _] at h_sc_74
  have h_sc_94 := pointsToBytes_chainKey_eq_cells (sp + 0x94#64) senderChainKey
  rw [show sp + 0x94#64 + 8#64 = sp + 0x9c#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 16#64 = sp + 0xa4#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 20#64 = sp + 0xa8#64 from add_assoc_const _ _ _ _,
      show sp + 0x94#64 + 28#64 = sp + 0xb0#64 from add_assoc_const _ _ _ _] at h_sc_94
  have h_opt_sc := optSenderChainBytes_some_pointsTo (sp + 0x50#64) ⟨newSenderKey, senderChainKey⟩ pad
  rw [show sp + 0x50#64 + 4#64 = sp + 0x54#64 from add_assoc_const _ _ _ _,
      show sp + 0x50#64 + 36#64 = sp + 0x74#64 from add_assoc_const _ _ _ _,
      show sp + 0x50#64 + 68#64 = sp + 0x94#64 from add_assoc_const _ _ _ _] at h_opt_sc
  have h_sc_entails :
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       (((sp + 0x54#64) ↦₆₄ spk0) ∗ ((sp + 0x5c#64) ↦₆₄ spk1) ∗ ((sp + 0x64#64) ↦₆₄ spk2) ∗ ((sp + 0x6c#64) ↦₆₄ spk3)) ∗
       (((sp + 0x74#64) ↦₆₄ sk0) ∗ ((sp + 0x7c#64) ↦₆₄ sk1) ∗ ((sp + 0x84#64) ↦₆₄ sk2) ∗ ((sp + 0x8c#64) ↦₆₄ sk3)) ∗
       (((sp + 0x94#64) ↦₆₄ sck0) ∗ ((sp + 0x9c#64) ↦₆₄ sck1) ∗ ((sp + 0xa4#64) ↦₃₂ sck16) ∗
        ((sp + 0xa8#64) ↦₆₄ sck2) ∗ ((sp + 0xb0#64) ↦₆₄ sck3))) ⊢
      ((sp + 0x50#64) ↦ₛ optSenderChainBytes (some ⟨newSenderKey, senderChainKey⟩) pad) := by
    rw [← h_sc_54, ← h_sc_74, ← h_sc_94, h_opt_sc]
    exact Entails.of_eq (by ac_rfl)
  have h_rck_2b0 := pointsToBytes_len16_to_cells (sp + 0x2b0#64) ((chainKeyBytes receiverChainKey).drop 20) hrck_drop20_len
  rw [show sp + 0x2b0#64 + 8#64 = sp + 0x2b8#64 from add_assoc_const _ _ _ _] at h_rck_2b0
  have h_rck_2c0 := pointsToBytes_len16_to_cells (sp + 0x2c0#64) ((chainKeyBytes receiverChainKey).take 16) hrck_take16_len
  rw [show sp + 0x2c0#64 + 8#64 = sp + 0x2c8#64 from add_assoc_const _ _ _ _] at h_rck_2c0
  have h_rck_2d0 := pointsToBytes_len4_eq_pointsTo32 (sp + 0x2d0#64) (((chainKeyBytes receiverChainKey).drop 16).take 4) hrck_mid_len
  have h_rck_2c0_20 := pointsToBytes_rck_take20 (sp + 0x2c0#64) receiverChainKey
  rw [show sp + 0x2c0#64 + 16#64 = sp + 0x2d0#64 from add_assoc_const _ _ _ _] at h_rck_2c0_20
  have h_staged_entails :
      ((((sp + 0x2b0#64) ↦₆₄ rck2) ∗ ((sp + 0x2b8#64) ↦₆₄ rck3)) ∗
       (((sp + 0x2c0#64) ↦₆₄ rck0) ∗ ((sp + 0x2c8#64) ↦₆₄ rck1)) ∗
       ((sp + 0x2d0#64) ↦₃₂ rck16)) ⊢
      (((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20)) := by
    rw [← h_rck_2b0, ← h_rck_2c0, ← h_rck_2d0, h_rck_2c0_20]
    exact Entails.refl _
  have h_sp0_20 :
      (memRegion sp 8 ∗
       ((sp + 0x8#64) ↦₃₂ sck16) ∗
       memRegion (sp + 0xc#64) 4 ∗
       ((sp + 0x10#64) ↦₃₂ rck16) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW)) ⊢
      memRegion sp 0x20 := by
    sep_interval
  have h_sp140_2b0 :
      (memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 104 ∗
       memRegion (sp + 0x1f8#64) 0xb8) ⊢
      memRegion (sp + 0x140#64) 0x170 := by
    sep_interval
  have h_sp2d4_580 :
      (memRegion (sp + 0x2d4#64) 0xfc ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       (((sp + 0x400#64) ↦₆₄ spk0) ∗ ((sp + 0x408#64) ↦₆₄ spk1) ∗ ((sp + 0x410#64) ↦₆₄ spk2) ∗ ((sp + 0x418#64) ↦₆₄ spk3)) ∗
       (((sp + 0x420#64) ↦₆₄ sk0) ∗ ((sp + 0x428#64) ↦₆₄ sk1) ∗ ((sp + 0x430#64) ↦₆₄ sk2) ∗ ((sp + 0x438#64) ↦₆₄ sk3)) ∗
       (((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1)) ∗
       (((sp + 0x450#64) ↦₆₄ spk0) ∗ ((sp + 0x458#64) ↦₆₄ spk1) ∗ ((sp + 0x460#64) ↦₆₄ spk2) ∗ ((sp + 0x468#64) ↦₆₄ spk3) ∗
        ((sp + 0x470#64) ↦₆₄ sk0) ∗ ((sp + 0x478#64) ↦₆₄ sk1) ∗ ((sp + 0x480#64) ↦₆₄ sk2) ∗ ((sp + 0x488#64) ↦₆₄ sk3) ∗
        ((sp + 0x490#64) ↦₆₄ sck0) ∗ ((sp + 0x498#64) ↦₆₄ sck1)) ∗
       memRegion (sp + 0x4a0#64) 0x20 ∗
       (((sp + 0x4c0#64) ↦₆₄ rck2) ∗ ((sp + 0x4c8#64) ↦₆₄ rck3) ∗ ((sp + 0x4d0#64) ↦₆₄ rck0) ∗ ((sp + 0x4d8#64) ↦₆₄ rck1)) ∗
       (((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1)) ∗
       memRegion (sp + 0x500#64) 96 ∗
       memRegion (sp + 0x560#64) 0x20) ⊢
      memRegion (sp + 0x2d4#64) 0x2ac := by
    have hrck := chainKeyBytes_length receiverChainKey
    sep_interval
  have hmf_grouped : sf.mem ⊨
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       (((sp + 0x54#64) ↦₆₄ spk0) ∗ ((sp + 0x5c#64) ↦₆₄ spk1) ∗ ((sp + 0x64#64) ↦₆₄ spk2) ∗ ((sp + 0x6c#64) ↦₆₄ spk3)) ∗
       (((sp + 0x74#64) ↦₆₄ sk0) ∗ ((sp + 0x7c#64) ↦₆₄ sk1) ∗ ((sp + 0x84#64) ↦₆₄ sk2) ∗ ((sp + 0x8c#64) ↦₆₄ sk3)) ∗
       (((sp + 0x94#64) ↦₆₄ sck0) ∗ ((sp + 0x9c#64) ↦₆₄ sck1) ∗ ((sp + 0xa4#64) ↦₃₂ sck16) ∗
        ((sp + 0xa8#64) ↦₆₄ sck2) ∗ ((sp + 0xb0#64) ↦₆₄ sck3))) ∗
      (memRegion sp 8 ∗
       ((sp + 0x8#64) ↦₃₂ sck16) ∗
       memRegion (sp + 0xc#64) 4 ∗
       ((sp + 0x10#64) ↦₃₂ rck16) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW)) ∗
      (memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 104 ∗
       memRegion (sp + 0x1f8#64) 0xb8) ∗
      ((((sp + 0x2b0#64) ↦₆₄ rck2) ∗ ((sp + 0x2b8#64) ↦₆₄ rck3)) ∗
       (((sp + 0x2c0#64) ↦₆₄ rck0) ∗ ((sp + 0x2c8#64) ↦₆₄ rck1)) ∗
       ((sp + 0x2d0#64) ↦₃₂ rck16)) ∗
      (memRegion (sp + 0x2d4#64) 0xfc ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       (((sp + 0x400#64) ↦₆₄ spk0) ∗ ((sp + 0x408#64) ↦₆₄ spk1) ∗ ((sp + 0x410#64) ↦₆₄ spk2) ∗ ((sp + 0x418#64) ↦₆₄ spk3)) ∗
       (((sp + 0x420#64) ↦₆₄ sk0) ∗ ((sp + 0x428#64) ↦₆₄ sk1) ∗ ((sp + 0x430#64) ↦₆₄ sk2) ∗ ((sp + 0x438#64) ↦₆₄ sk3)) ∗
       (((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1)) ∗
       (((sp + 0x450#64) ↦₆₄ spk0) ∗ ((sp + 0x458#64) ↦₆₄ spk1) ∗ ((sp + 0x460#64) ↦₆₄ spk2) ∗ ((sp + 0x468#64) ↦₆₄ spk3) ∗
        ((sp + 0x470#64) ↦₆₄ sk0) ∗ ((sp + 0x478#64) ↦₆₄ sk1) ∗ ((sp + 0x480#64) ↦₆₄ sk2) ∗ ((sp + 0x488#64) ↦₆₄ sk3) ∗
        ((sp + 0x490#64) ↦₆₄ sck0) ∗ ((sp + 0x498#64) ↦₆₄ sck1)) ∗
       memRegion (sp + 0x4a0#64) 0x20 ∗
       (((sp + 0x4c0#64) ↦₆₄ rck2) ∗ ((sp + 0x4c8#64) ↦₆₄ rck3) ∗ ((sp + 0x4d0#64) ↦₆₄ rck0) ∗ ((sp + 0x4d8#64) ↦₆₄ rck1)) ∗
       (((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1)) ∗
       memRegion (sp + 0x500#64) 96 ∗
       memRegion (sp + 0x560#64) 0x20) ∗
      (Frame ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmf'
    ac_rfl
  have hmf_final := Satisfies.mono
    (sepConj_mono h_sc_entails
      (sepConj_mono h_sp0_20
        (sepConj_mono h_sp140_2b0
          (sepConj_mono h_staged_entails
            (sepConj_mono_left h_sp2d4_580)))))
    hmf_grouped
  rw [sepConj_assoc ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20)] at hmf_final
  exact ReachesOrPanic.done ⟨hpcf, hrunf, hspf, hsp_alignf, htrf,
    hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx29f, hx30f, hvregsf, hLf, hmf_final⟩

theorem dhCommit_step5_placed [LibsignalPlacement] {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockWp prog entry dropChainEntry)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (x : TryDecryptGhost) (pad : List (BitVec 8))
    (sc : SenderChain) (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (senderChainKey : ChainKey) (msgW : BitVec 32)
    (Frame R : SepProp) (s0 s : State)
    (sp : BitVec 64) (hsp_def : sp = s0.sp - 1504#64)
    (hpad : pad.length = 100)
    (hpc : s.pc = entry + 0xb98#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hL : prog.CodeLoaded s.mem)
    (hm : s.mem ⊨
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
      memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x50#64) ↦₃₂ 1#32) ∗
      ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      memRegion (sp + 0x190#64) 104 ∗
      memRegion (sp + 0x1f8#64) 0xb8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x14 ∗
      memRegion (sp + 0x2d4#64) 0xfc ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x450#64) 0x50 ∗
      memRegion (sp + 0x4a0#64) 0x20 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x500#64) 96 ∗
      memRegion (sp + 0x560#64) 0x20 ∗
      (Frame ∗ R)) :
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s
      (fun sf =>
        sf.pc = entry + 0x3e4#64 ∧
        sf.status = .Running ∧
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = msgW.zeroExtend 64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          ((sp + 0x50#64) ↦ₛ optSenderChainBytes (some ⟨newSenderKey, senderChainKey⟩) pad) ∗
          memRegion sp 0x20 ∗
          memRegion (sp + 0x140#64) 0x170 ∗
          ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
          ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20) ∗
          memRegion (sp + 0x2d4#64) 0x2ac ∗
          (Frame ∗ R))) :=
  dhCommit_step5_of_wp tryDecryptPlacedImg C A ctl S x pad sc receiverChainKey newSenderKey senderChainKey
    msgW Frame R s0 s sp hsp_def hpad
    (fun sck16 rck16 msgW oldTag oldSck16 v2d0
         oldSpk0 oldSpk1 oldSpk2 oldSpk3 oldSk0 oldSk1 oldSk2 oldSk3
         oldSck0 oldSck1 oldSck2 oldSck3 spk0 spk1 spk2 spk3 sk0 sk1 sk2 sk3
         sck0 sck1 sck2 sck3 rck0 rck1 rck2 rck3 v2b0 v2b8 v2c0 v2c8
         v450 v458 v460 v468 v470 v478 v480 v488 v490 v498 =>
      hwp.step5 sp sck16 rck16 msgW oldTag oldSck16 v2d0
        oldSpk0 oldSpk1 oldSpk2 oldSpk3 oldSk0 oldSk1 oldSk2 oldSk3
        oldSck0 oldSck1 oldSck2 oldSck3 spk0 spk1 spk2 spk3 sk0 sk1 sk2 sk3
        sck0 sck1 sck2 sck3 rck0 rck1 rck2 rck3 v2b0 v2b8 v2c0 v2c8
        v450 v458 v460 v468 v470 v478 v480 v488 v490 v498
        s hpc hrun hsp hsp_align hx25)
    hL hm

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
