/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.Skeleton -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.BodyDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.CanonKey
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Skeleton
import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.Bridge
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.DeserializeLeaves
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Root
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Callees
import LibsignalBinary.Proofs.E2E.Record.Serialization.Serialize
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From

public section

namespace CryptoVerification.E2E.Bin

open Arm64 ProofLib open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.InMem

variable {C : Crypto} {A : RustAlloc} {S : SpqrModel}

abbrev inMemSavePollOff : BitVec 64 := 0x077cc#64

/-! ## Store Shim Bridges (`0x2ddc0`, `0x2f458`, `0x2f408`) -/

private theorem stackAt_sub_split0 (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)

/-! ## Store Poll-Closure Bridges (`0x077cc`, `0x08ee4`, `0x08ce4`) -/

private theorem mem_zip_of_mem_left :
    ∀ {α β : Type} {xs : List α} {ys : List β} {x : α},
      xs.length = ys.length → x ∈ xs → ∃ y, (x, y) ∈ xs.zip ys
  | _, _, [], [], _, _, hx => by simp at hx
  | _, _, x' :: xs, y' :: ys, x, hlen, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨y', List.mem_cons_self ..⟩
    · obtain ⟨y, hy⟩ := mem_zip_of_mem_left hlen hx
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

theorem binCanonSession_of_canonSession {G0 G : SessionGhost} {s : Session (List (BitVec 8))}
    (h0 : BinCanonSession G0 s) (hG : Record.Serialization.CanonSession G s) :
    BinCanonSession G s := by
  rcases h0 with ⟨_, hwf, _, _, _, hrc_len, hrc_mk, _, halice, hkyber, hpq, henc⟩
  rcases hG with ⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩
  refine ⟨⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩,
    hwf, hlocal, ?_, ?_, hrc_len, hrc_mk, ?_, halice, hkyber, hpq, henc⟩
  · cases hri : s.state.remoteIdentity <;> simpa [hri] using hrem
  · revert hsender
    unfold Record.Serialization.CanonSender
    cases G.sender <;> cases s.state.senderChain <;> intro hsender
    · exact True.intro
    · exact hsender
    · exact hsender
    · exact hsender.1
  · intro cg hcg
    obtain ⟨rc, hmem⟩ := mem_zip_of_mem_left hlen_eq hcg
    have hcc := hzip (cg, rc) hmem
    have hser_len : rc.senderRatchetKey.serialize.length = 33 :=
      PublicKey.serialize_length rc.senderRatchetKey
    exact ⟨hcc.1.trans (by rfl) ▸ hser_len, hcc.2⟩

theorem canonRecord_to_serializationCanon {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (h : CanonRecord g r) :
    Record.Serialization.CanonRecord g r := by
  revert h
  unfold CanonRecord Record.Serialization.CanonRecord Record.Serialization.CanonCur
  cases g.cur <;> cases r.currentSession <;> intro h
  · exact True.intro
  · exact h
  · exact h
  · exact h.toCanonSession

private theorem stackAt_sub_split (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  have hsplit := memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)
  exact hsplit

abbrev deserializeRecordStack : Nat := recordDeserializeStack
abbrev serializationRecordStack : Nat := recordSerializeStack

private theorem stackAt_recordSerialize_split (sp : BitVec 64) :
    stackAt sp recordSerializeStack =
      memRegion (sp - BitVec.ofNat 64 recordSerializeStack)
        (recordSerializeStack - Record.Serialization.serializeStack) ∗
      stackAt sp Record.Serialization.serializeStack :=
  stackAt_sub_split sp Record.Serialization.serializeStack recordSerializeStack (by decide) (by decide)

private theorem memRegion_48_split_32_16 (out : BitVec 64) :
    memRegion out 48 = memRegion out 32 ∗ memRegion (out + 32#64) 16 :=
  memRegion_split out 32 16 (by decide)

abbrev serializationRecordSpec (A : RustAlloc) : Spec RecordSerializeGhost :=
  recordSerializeSpec A

private theorem vecAt_prev_zero_eq (out : BitVec 64) :
    vecAt Record.A0 24 8 (fun (_ : Unit) _ => emp) out 0#64 8#64 [] =
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) := by
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧
      (8#64 : BitVec 64) ≠ 0#64) := by decide
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, sepConj_emp,
    Record.SeedLengthFacts.pure_true_sepConj hpure]

theorem deserOutRecordG_entails_binCanonSession {G0 : SessionGhost} (s : Session (List (BitVec 8)))
    (h0 : BinCanonSession G0 s) (hr : Record.DeserializeGeneral.DeserializeScope ⟨some s⟩) (out : BitVec 64) :
    Record.DeserializeGeneral.deserOutRecordG out ⟨some s⟩ ⊢
      ∃∗ G : SessionGhost, ⌜BinCanonSession G s⌝ ∗
        sessionRecordAt Record.A0 out ⟨0#64, 8#64, some G⟩ ⟨some s⟩ := by
  have hAfter := Record.DeserializeGeneral.ssgAfter_recFields ⟨some s⟩ hr s rfl
  have hRepr := Record.DeserializeGeneral.prostSSG_repr ⟨some s⟩ hr s rfl (out + 0x18#64)
  have hdef :
      Record.DeserializeGeneral.deserOutRecordG out ⟨some s⟩ =
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          Record.DeserializeGeneral.prostSSGAt Record.A0 (out + 0x18#64) (Record.DeserializeGeneral.ssgOf s) := by
    unfold Record.DeserializeGeneral.deserOutRecordG
    rw [hAfter]
    ac_rfl
  rw [hdef]
  refine Entails.trans (sepConj_mono_right hRepr) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun G => ?_
  have h1 :
      (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
        (⌜Record.Serialization.CanonSession G s⌝ ∗ Record.sessionStateReprAt Record.A0 (out + 0x18#64) G s)) =
      (⌜Record.Serialization.CanonSession G s⌝ ∗
        (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          Record.sessionStateReprAt Record.A0 (out + 0x18#64) G s)) := by
    ac_rfl
  rw [h1]
  refine Entails.pure_left fun hcanon => ?_
  refine Entails.sepExists_right G ?_
  refine Entails.pure_right (binCanonSession_of_canonSession h0 hcanon) ?_
  unfold sessionRecordAt
  dsimp only
  rw [vecAt_prev_zero_eq]
  exact Entails.refl _

private theorem stackAt_recordDeserialize_split (sp : BitVec 64) :
    stackAt sp recordDeserializeStack =
      memRegion (sp - BitVec.ofNat 64 recordDeserializeStack)
        (recordDeserializeStack - Record.recDeserializeStack) ∗
      stackAt sp Record.recDeserializeStack :=
  stackAt_sub_split sp Record.recDeserializeStack recordDeserializeStack (by decide) (by decide)

abbrev DeserializeRecordCanonical := RecordCanonical
abbrev deserializeRecordOpenSpec (A : RustAlloc) := recordDeserializeOpenSpec A

end CryptoVerification.E2E.Bin
