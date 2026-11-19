/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage 1 Frame Combinators and Early Error Exits

Provides `SepWPp` stepping helpers, 32-byte word pack/unpack lemmas, `cliBundleBody`, prologue and
poll stack-frame split/merge lemmas, and the shared Stage 1 early `Err` exit paths
(`stage1_plain11_exit_ext_ok`, `stage1_untrusted_exit_ext_ok`).
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

theorem sepWPp_drop_left {prog : Program} {tgt : BitVec 64} {s : State}
    {cell P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hnext : SepWPp prog tgt s P Q Qp oom) :
    SepWPp prog tgt s (cell ∗ P) Q Qp oom := by
  intro R hm hL
  exact hnext R (Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm)) hL

theorem sepWPp_exists_left {α : Type} {prog : Program} {tgt : BitVec 64} {s : State}
    {F : α → SepProp} {R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWPp prog tgt s (F x ∗ R) Q Qp oom) :
    SepWPp prog tgt s ((∃∗ x, F x) ∗ R) Q Qp oom := by
  rw [sepExists_sepConj_left]
  exact sepWPp_exists_elim h

theorem sepWPp_exists_pos2 {α : Type} {prog : Program} {tgt : BitVec 64} {s : State}
    {A : SepProp} {F : α → SepProp} {R : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWPp prog tgt s (A ∗ F x ∗ R) Q Qp oom) :
    SepWPp prog tgt s (A ∗ (∃∗ x, F x) ∗ R) Q Qp oom := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  exact sepWPp_exists_elim h

theorem sepWPp_exists_pos3 {α : Type} {prog : Program} {tgt : BitVec 64} {s : State}
    {A B : SepProp} {F : α → SepProp} {R : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWPp prog tgt s (A ∗ B ∗ F x ∗ R) Q Qp oom) :
    SepWPp prog tgt s (A ∗ B ∗ (∃∗ x, F x) ∗ R) Q Qp oom := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  exact sepWPp_exists_elim h

theorem sepWPp_exists_pos4 {α : Type} {prog : Program} {tgt : BitVec 64} {s : State}
    {A B C : SepProp} {F : α → SepProp} {R : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWPp prog tgt s (A ∗ B ∗ C ∗ F x ∗ R) Q Qp oom) :
    SepWPp prog tgt s (A ∗ B ∗ C ∗ (∃∗ x, F x) ∗ R) Q Qp oom := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right,
    sepExists_sepConj_right]
  exact sepWPp_exists_elim h

theorem spAligned_of_sp_eq {s1 s2 : State} (h1 : s1.spAligned = true) (hsp : s2.sp = s1.sp) :
    s2.spAligned = true := by
  simpa only [State.spAligned, hsp] using h1

theorem spAligned_of_frame {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) :
    s.spAligned = true := by
  simp only [State.spAligned, beq_iff_eq] at hal0 ⊢
  rw [hsp, show cliInitiateFrame = 7408 from rfl]
  have hmod0 : s0.sp.toNat % 16 = 0 := by
    have ht := congrArg BitVec.toNat hal0
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (0#64).toNat = 0 from rfl] at ht
    exact ht
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, show (0#64).toNat = 0 from rfl, BitVec.toNat_sub,
    show (7408#64).toNat = 7408 from rfl]
  have hlt : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  omega

theorem cs_x19 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := h.1
theorem cs_x20 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) := h.2.1
theorem cs_x21 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) := h.2.2.1
theorem cs_x22 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) := h.2.2.2.1
theorem cs_x23 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := h.2.2.2.2.1
theorem cs_x24 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := h.2.2.2.2.2.1
theorem cs_x25 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) := h.2.2.2.2.2.2.1
theorem cs_x26 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) := h.2.2.2.2.2.2.2.1
theorem cs_x27 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := h.2.2.2.2.2.2.2.2.1
theorem cs_x28 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := h.2.2.2.2.2.2.2.2.2.1
theorem cs_fp {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 .fp = s.readReg64 .fp := h.2.2.2.2.2.2.2.2.2.2.1
theorem cs_vregs {s sm : State} (h : CalleeSavedPreserved s sm) :
    calleeSavedVRegs sm = calleeSavedVRegs s := h.2.2.2.2.2.2.2.2.2.2.2

theorem bytes32_eq_exists_words4 (p : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 32) :
    (p ↦ₛ bs) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3⌝ ∗
        (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) := by
  obtain ⟨w0, w1, w2, w3, hw, hsep⟩ := exists_unpack64_of_length_32 hlen
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_)))
  refine pure_sepConj_intro hw ?_
  rw [hsep p]
  sep_frame

theorem words4_to_bytes32 (q : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 : BitVec 64}
    (hbs : bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3) :
    (q ↦₆₄ w0) ∗ ((q + 8#64) ↦₆₄ w1) ∗ ((q + 16#64) ↦₆₄ w2) ∗ ((q + 24#64) ↦₆₄ w3) ⊢
      (q ↦ₛ bs) := by
  rw [hbs, List.append_assoc, List.append_assoc,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem memRegion_32_words (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ d3 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d0 : BitVec 64,
        (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) := by
  have split8 : ∀ p n, n ≥ 8 → n ≤ 32 →
      memRegion p n = (∃∗ w : BitVec 64, p ↦₆₄ w) ∗ memRegion (p + 8#64) (n - 8) := by
    intro p n hge _hle
    have hn : n = 8 + (n - 8) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split p 8 (n - 8) (by omega), ProofLib.memRegion_eight]
  rw [split8 a 32 (by decide) (by decide),
      split8 _ 24 (by decide) (by decide),
      split8 _ 16 (by decide) (by decide),
      ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]

theorem boxU8Buf_serialize_unpack (A : RustAlloc) (ptr : BitVec 64) (pk : PublicKey) :
    boxU8Buf A ptr pk.serialize ⊢
      ⌜ptr ≠ 0#64⌝ ∗ A.live ptr 33 1 ∗ (ptr ↦ₛ pk.serialize) := by
  unfold boxU8Buf
  have hne : pk.serialize ≠ [] := by simp [PublicKey.serialize]
  have hlen : pk.serialize.length = 33 := by simp [PublicKey.serialize]
  rw [ite_eq_right_iff.mpr fun h => absurd h hne, hlen]
  exact pure_sepConj_elim fun ⟨hp, _⟩ => pure_sepConj_intro hp (Entails.refl _)

/-- Spatial body of `cliBundleAt` at a fixed `opkId`. -/
@[expose] def cliBundleBody (a : BitVec 64) (b : BundleV) (spkSigPtr kpkSigPtr kpkPtr : BitVec 64)
    (opkId : BitVec 32) : SepProp :=
  let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
  (a ↦₆₄ 64#64) ∗ ((a + 8#64) ↦₆₄ spkSigPtr) ∗ ((a + 16#64) ↦₆₄ 64#64) ∗
    (spkSigPtr ↦ₛ b.spkSig) ∗
    ((a + 24#64) ↦ₛ b.spk.bytes.toList) ∗
    ((a + 56#64) ↦₃₂ b.spkId) ∗ memRegion (a + 60#64) 4 ∗
    ((a + 64#64) ↦₆₄ 64#64) ∗ ((a + 72#64) ↦₆₄ kpkSigPtr) ∗ ((a + 80#64) ↦₆₄ 64#64) ∗
    (kpkSigPtr ↦ₛ b.kpkSig) ∗
    ((a + 88#64) ↦₆₄ kpkPtr) ∗ ((a + 96#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ b.kpk) ∗
    ((a + 104#64) ↦₃₂ b.kpkId) ∗ memRegion (a + 108#64) 4 ∗
    ((a + 112#64) ↦₃₂ opkFlag) ∗ ((a + 116#64) ↦₃₂ opkId) ∗
    ((a + 120#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗ ((a + 152#64) ↦₃₂ b.regId) ∗
    ((a + 156#64) ↦₈ opkFlag.truncate 8) ∗
    (match b.opk with
     | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
     | none => memRegion (a + 157#64) 32) ∗
    ((a + 189#64) ↦₈ b.device) ∗ memRegion (a + 190#64) 2

theorem cliBundleAt_unpack (a : BitVec 64) (b : BundleV)
    (spkSigPtr kpkSigPtr kpkPtr : BitVec 64) :
    cliBundleAt a b spkSigPtr kpkSigPtr kpkPtr =
      ∃∗ opkId : BitVec 32,
        ⌜b.spkSig.length = 64 ∧ b.kpkSig.length = 64 ∧ b.kpk.length = 1568 ∧
          ∀ p, b.opk = some p → opkId = p.1⌝ ∗
        cliBundleBody a b spkSigPtr kpkSigPtr kpkPtr opkId := rfl

theorem cliBundleBody_pack {a : BitVec 64} {b : BundleV}
    {spkSigPtr kpkSigPtr kpkPtr : BitVec 64} {opkId : BitVec 32}
    (h1 : b.spkSig.length = 64) (h2 : b.kpkSig.length = 64) (h3 : b.kpk.length = 1568)
    (hopk : ∀ p, b.opk = some p → opkId = p.1) :
    cliBundleBody a b spkSigPtr kpkSigPtr kpkPtr opkId ⊢
      cliBundleAt a b spkSigPtr kpkSigPtr kpkPtr := by
  rw [cliBundleAt_unpack]
  exact Entails.sepExists_right opkId (pure_sepConj_intro ⟨h1, h2, h3, hopk⟩ (Entails.refl _))

/-- Splits `memRegion fsp initLocalsSize` into individual cells for the `0x0000..0x0098` prologue stores. -/
theorem prologue_locals_split (fsp : BitVec 64) :
    memRegion fsp initLocalsSize ⊢
      ∃∗ l0 : BitVec 64, ∃∗ l80 : BitVec 64, ∃∗ l88 : BitVec 32,
      ∃∗ l90 : BitVec 64, ∃∗ l98 : BitVec 64, ∃∗ la0 : BitVec 64, ∃∗ la8 : BitVec 64,
      ∃∗ lb0 : BitVec 64, ∃∗ lb8 : BitVec 64, ∃∗ lc0 : BitVec 64, ∃∗ lc8 : BitVec 64,
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64, ∃∗ a3 : BitVec 64,
      ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64, ∃∗ a6 : BitVec 64, ∃∗ a7 : BitVec 64,
      ∃∗ a8 : BitVec 32, ∃∗ a9 : BitVec 64, ∃∗ a10 : BitVec 64,
      ∃∗ flag16 : BitVec 16,
      ∃∗ wk0 : BitVec 64, ∃∗ wk1 : BitVec 64, ∃∗ wk2 : BitVec 64,
      ∃∗ probe : BitVec 64,
        (fsp ↦₆₄ l0) ∗ memRegion (fsp + 0x08#64) 0x78 ∗
        ((fsp + 0x80#64) ↦₆₄ l80) ∗ ((fsp + 0x88#64) ↦₃₂ l88) ∗ memRegion (fsp + 0x8c#64) 4 ∗
        ((fsp + 0x90#64) ↦₆₄ l90) ∗ ((fsp + 0x98#64) ↦₆₄ l98) ∗
        ((fsp + 0xa0#64) ↦₆₄ la0) ∗ ((fsp + 0xa8#64) ↦₆₄ la8) ∗
        ((fsp + 0xb0#64) ↦₆₄ lb0) ∗ ((fsp + 0xb8#64) ↦₆₄ lb8) ∗
        ((fsp + 0xc0#64) ↦₆₄ lc0) ∗ ((fsp + 0xc8#64) ↦₆₄ lc8) ∗
        ((fsp + 0xd0#64) ↦₆₄ a0) ∗ ((fsp + 0xd8#64) ↦₆₄ a1) ∗
        ((fsp + 0xe0#64) ↦₆₄ a2) ∗ ((fsp + 0xe8#64) ↦₆₄ a3) ∗
        ((fsp + 0xf0#64) ↦₆₄ a4) ∗ ((fsp + 0xf8#64) ↦₆₄ a5) ∗
        ((fsp + 0x100#64) ↦₆₄ a6) ∗ ((fsp + 0x108#64) ↦₆₄ a7) ∗
        ((fsp + 0x110#64) ↦₃₂ a8) ∗ memRegion (fsp + 0x114#64) 4 ∗
        ((fsp + 0x118#64) ↦₆₄ a9) ∗ ((fsp + 0x120#64) ↦₆₄ a10) ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₁₆ flag16) ∗
        memRegion (fsp + 0x5ba#64) 30 ∗
        ((fsp + 0x5d8#64) ↦₆₄ wk0) ∗ ((fsp + 0x5e0#64) ↦₆₄ wk1) ∗ ((fsp + 0x5e8#64) ↦₆₄ wk2) ∗
        memRegion (fsp + 0x5f0#64) (0xc90 - 0x5f0) ∗
        ((fsp + 0xc90#64) ↦₆₄ probe) ∗
        memRegion (fsp + 0xc98#64) (initLocalsSize - 0xc98) := by
  have hsz : initLocalsSize = 7312 := rfl
  have split8At : ∀ off top, 8 ≤ top - off → top - off ≤ 7312 →
      memRegion (fsp + BitVec.ofNat 64 off) (top - off) =
        (∃∗ w : BitVec 64, (fsp + BitVec.ofNat 64 off) ↦₆₄ w) ∗
          memRegion (fsp + BitVec.ofNat 64 (off + 8)) (top - (off + 8)) := by
    intro off top h1 h2
    have hn : top - off = 8 + (top - (off + 8)) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split _ 8 _ (by omega), ProofLib.memRegion_eight,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  have split4At : ∀ off top, 4 ≤ top - off → top - off ≤ 7312 →
      memRegion (fsp + BitVec.ofNat 64 off) (top - off) =
        (∃∗ w : BitVec 32, (fsp + BitVec.ofNat 64 off) ↦₃₂ w) ∗
          memRegion (fsp + BitVec.ofNat 64 (off + 4)) (top - (off + 4)) := by
    intro off top h1 h2
    have hn : top - off = 4 + (top - (off + 4)) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split _ 4 _ (by omega), ProofLib.memRegion_four,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  have splitGapAt : ∀ off k top, k ≤ top - off → top - off ≤ 7312 →
      memRegion (fsp + BitVec.ofNat 64 off) (top - off) =
        memRegion (fsp + BitVec.ofNat 64 off) k ∗
          memRegion (fsp + BitVec.ofNat 64 (off + k)) (top - (off + k)) := by
    intro off k top h1 h2
    have hn : top - off = k + (top - (off + k)) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split _ k _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  have htop3 : memRegion fsp initLocalsSize ⊢
      memRegion (fsp + BitVec.ofNat 64 0) (0x5b8 - 0) ∗
        (∃∗ flag16 : BitVec 16, (fsp + 0x5b8#64) ↦₁₆ flag16) ∗
        memRegion (fsp + BitVec.ofNat 64 0x5ba) (7312 - 0x5ba) := by
    have hs : memRegion fsp initLocalsSize =
        memRegion (fsp + BitVec.ofNat 64 0) (0x5b8 - 0) ∗
          memRegion (fsp + 0x5b8#64) 2 ∗
          memRegion (fsp + BitVec.ofNat 64 0x5ba) (7312 - 0x5ba) := by
      rw [hsz, show (7312 : Nat) = 0x5b8 + (2 + (7312 - 0x5ba)) by decide,
        memRegion_split fsp 0x5b8 _ (by decide),
        memRegion_split _ 2 _ (by decide)]
      simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
        Nat.reduceSub]
    rw [hs]
    exact sepConj_mono_right (sepConj_mono_left (memRegion_two_pointsTo16 (fsp + 0x5b8#64)))
  refine Entails.trans htop3 ?_
  rw [split8At 0 0x5b8 (by decide) (by decide),
      splitGapAt 0x08 0x78 0x5b8 (by decide) (by decide),
      split8At 0x80 0x5b8 (by decide) (by decide),
      split4At 0x88 0x5b8 (by decide) (by decide),
      splitGapAt 0x8c 4 0x5b8 (by decide) (by decide),
      split8At 0x90 0x5b8 (by decide) (by decide),
      split8At 0x98 0x5b8 (by decide) (by decide),
      split8At 0xa0 0x5b8 (by decide) (by decide),
      split8At 0xa8 0x5b8 (by decide) (by decide),
      split8At 0xb0 0x5b8 (by decide) (by decide),
      split8At 0xb8 0x5b8 (by decide) (by decide),
      split8At 0xc0 0x5b8 (by decide) (by decide),
      split8At 0xc8 0x5b8 (by decide) (by decide),
      split8At 0xd0 0x5b8 (by decide) (by decide),
      split8At 0xd8 0x5b8 (by decide) (by decide),
      split8At 0xe0 0x5b8 (by decide) (by decide),
      split8At 0xe8 0x5b8 (by decide) (by decide),
      split8At 0xf0 0x5b8 (by decide) (by decide),
      split8At 0xf8 0x5b8 (by decide) (by decide),
      split8At 0x100 0x5b8 (by decide) (by decide),
      split8At 0x108 0x5b8 (by decide) (by decide),
      split4At 0x110 0x5b8 (by decide) (by decide),
      splitGapAt 0x114 4 0x5b8 (by decide) (by decide),
      split8At 0x118 0x5b8 (by decide) (by decide),
      split8At 0x120 0x5b8 (by decide) (by decide),
      splitGapAt 0x5ba 30 7312 (by decide) (by decide),
      split8At 0x5d8 7312 (by decide) (by decide),
      split8At 0x5e0 7312 (by decide) (by decide),
      split8At 0x5e8 7312 (by decide) (by decide),
      splitGapAt 0x5f0 (0xc90 - 0x5f0) 7312 (by decide) (by decide),
      split8At 0xc90 7312 (by decide) (by decide)]
  simp only [hsz, BitVec.add_zero, Nat.reduceAdd, Nat.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply Entails.sepExists_elim; intro)
  sep_frame

/-- Merges low prologue scratch cells `[fsp, fsp + 0xd0)` back into `memRegion fsp 0xd0`. -/
theorem prologue_low_d0_merge (fsp : BitVec 64)
    (l0 l80 : BitVec 64) (l88 : BitVec 32)
    (l90 l98 la0 la8 lb0 lb8 lc0 lc8 : BitVec 64) :
    (fsp ↦₆₄ l0) ∗ memRegion (fsp + 0x08#64) 0x78 ∗
      ((fsp + 0x80#64) ↦₆₄ l80) ∗ ((fsp + 0x88#64) ↦₃₂ l88) ∗ memRegion (fsp + 0x8c#64) 4 ∗
      ((fsp + 0x90#64) ↦₆₄ l90) ∗ ((fsp + 0x98#64) ↦₆₄ l98) ∗
      ((fsp + 0xa0#64) ↦₆₄ la0) ∗ ((fsp + 0xa8#64) ↦₆₄ la8) ∗
      ((fsp + 0xb0#64) ↦₆₄ lb0) ∗ ((fsp + 0xb8#64) ↦₆₄ lb8) ∗
      ((fsp + 0xc0#64) ↦₆₄ lc0) ∗ ((fsp + 0xc8#64) ↦₆₄ lc8) ⊢
      memRegion fsp 0xd0 := by
  have m64 := pointsTo64_entails_memRegion
  have m32 := pointsTo32_entails_memRegion
  refine Entails.trans (sepConj_mono (m64 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m32 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _) (m64 _ _))))))))))))) ?_
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x08#64) 8 120 128 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x80#64) 128 8 136 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x88#64) 136 4 140 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x8c#64) 140 4 144 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x90#64) 144 8 152 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x98#64) 152 8 160 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xa0#64) 160 8 168 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xa8#64) 168 8 176 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xb0#64) 176 8 184 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xb8#64) 184 8 192 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xc0#64) 192 8 200 (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge fsp (fsp + 0xc8#64) 200 8 208 (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

/-- Merges upper prologue scratch cells `[fsp + 0x5ba, fsp + initLocalsSize)` back into one `memRegion`. -/
theorem prologue_high_5ba_merge (fsp : BitVec 64)
    (wk0 wk1 wk2 probe : BitVec 64) :
    memRegion (fsp + 0x5ba#64) 30 ∗
      ((fsp + 0x5d8#64) ↦₆₄ wk0) ∗ ((fsp + 0x5e0#64) ↦₆₄ wk1) ∗ ((fsp + 0x5e8#64) ↦₆₄ wk2) ∗
      memRegion (fsp + 0x5f0#64) (0xc90 - 0x5f0) ∗
      ((fsp + 0xc90#64) ↦₆₄ probe) ∗
      memRegion (fsp + 0xc98#64) (initLocalsSize - 0xc98) ⊢
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
  have m64 := pointsTo64_entails_memRegion
  refine Entails.trans (sepConj_mono (Entails.refl _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (m64 _ _) (Entails.refl _))))))) ?_
  rw [← sepConj_assoc, memRegion_merge (fsp + 0x5ba#64) (fsp + 0x5d8#64) 30 8 38 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0x5ba#64) (fsp + 0x5e0#64) 38 8 46 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0x5ba#64) (fsp + 0x5e8#64) 46 8 54 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0x5ba#64) (fsp + 0x5f0#64) 54 1696 1750 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0x5ba#64) (fsp + 0xc90#64) 1750 8 1758 (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge (fsp + 0x5ba#64) (fsp + 0xc98#64) 1758 (initLocalsSize - 0xc98)
    (initLocalsSize - 0x5ba) (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

/-- Splits `[sp + 0x5ba, sp + initLocalsSize)` into future pointer/vtable slots (`+0x5c0`, `+0x5c8`) and an sret region at `sp + 0x1600`. -/
theorem poll_frame_5ba_split (sp : BitVec 64) (outSz : Nat)
    (hout : 0x1600 + outSz ≤ initLocalsSize) :
    memRegion (sp + 0x5ba#64) (initLocalsSize - 0x5ba) =
      memRegion (sp + 0x5ba#64) 6 ∗
        (∃∗ f0 : BitVec 64, (sp + 0x5c0#64) ↦₆₄ f0) ∗
        (∃∗ f1 : BitVec 64, (sp + 0x5c8#64) ↦₆₄ f1) ∗
        memRegion (sp + 0x5d0#64) (0x1600 - 0x5d0) ∗
        memRegion (sp + 0x1600#64) outSz ∗
        memRegion (sp + BitVec.ofNat 64 (0x1600 + outSz)) (initLocalsSize - (0x1600 + outSz)) := by
  have hsz : initLocalsSize = 7312 := rfl
  have h1 : initLocalsSize - 0x5ba = 6 + (initLocalsSize - 0x5c0) := by omega
  have h2 : initLocalsSize - 0x5c0 = 8 + (initLocalsSize - 0x5c8) := by omega
  have h3 : initLocalsSize - 0x5c8 = 8 + (initLocalsSize - 0x5d0) := by omega
  have h4 : initLocalsSize - 0x5d0 = (0x1600 - 0x5d0) + (initLocalsSize - 0x1600) := by omega
  have h5 : initLocalsSize - 0x1600 = outSz + (initLocalsSize - (0x1600 + outSz)) := by omega
  rw [h1, memRegion_split (sp + 0x5ba#64) 6 _ (by omega),
      h2, memRegion_split _ 8 _ (by omega), ProofLib.memRegion_eight,
      h3, memRegion_split _ 8 _ (by omega), ProofLib.memRegion_eight,
      h4, memRegion_split _ (0x1600 - 0x5d0) _ (by omega),
      h5, memRegion_split _ outSz _ (by omega)]
  simp only [Nat.reduceSub, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]

/-- Merges `[sp + 0x5ba, sp + initLocalsSize)` back after `idTrustPoll` / `sessLoadPoll`. -/
theorem poll_frame_5ba_merge (sp : BitVec 64) (f0 f1 : BitVec 64) (outSz : Nat)
    (hout : 0x1600 + outSz ≤ initLocalsSize) :
    memRegion (sp + 0x5ba#64) 6 ∗
      ((sp + 0x5c0#64) ↦₆₄ f0) ∗
      ((sp + 0x5c8#64) ↦₆₄ f1) ∗
      memRegion (sp + 0x5d0#64) (0x1600 - 0x5d0) ∗
      memRegion (sp + 0x1600#64) outSz ∗
      memRegion (sp + BitVec.ofNat 64 (0x1600 + outSz)) (initLocalsSize - (0x1600 + outSz)) ⊢
      memRegion (sp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
  rw [poll_frame_5ba_split sp outSz hout]
  sep_frame

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
