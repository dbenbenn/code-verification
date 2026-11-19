/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.AllocWitness -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalSessionProofDefs
import ProofLib.VCGen

public section

namespace CryptoVerification.LibsignalSession.NonVacuityWitness

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-! ## Concrete Ghost Witness -/

@[expose] def pk0 : PublicKey := ⟨⟨List.replicate 32 0#8, by simp⟩⟩

theorem deserialize_pk0_serialize : PublicKey.deserialize pk0.serialize = .ok pk0 := rfl

@[expose] def c0 : ReceiverChain :=
  { senderRatchetKey := pk0
    chainKey := none
    messageKeys := [] }

@[expose] def st0 : RatchetState :=
  { rootKey := 0#256
    senderChain := none
    receiverChains := [c0]
    previousCounter := 0#32
    maxForwardJumps := 25000 }

@[expose] def ck0 : ChainKey :=
  { key := 0#256
    index := 3#32 }

@[expose] def g0 (B : BitVec 64) : ChainGhost :=
  { srk := ⟨33#64, B + 280#64, pk0.serialize⟩
    priv := ⟨0#64, 1#64, []⟩
    mkCap := 0#64
    mkPtr := 8#64
    keys := []
    ck := ⟨0#64, 1#64⟩ }

@[expose] def G0 (B : BitVec 64) : RatchetGhost :=
  { chainsCap := 1#64
    chainsPtr := B + 176#64
    chains := [g0 B]
    senderPad := List.replicate 100 0#8 }

@[expose] def witnessGhost (B : BitVec 64) : ConsumeMessageKeyGhost :=
  { self := B
    G := G0 B
    st := st0
    their := pk0
    theirA := B + 313#64
    ck := ck0
    ckA := B + 345#64
    counter := 5#32
    msgType := .whisper
    ret := B + 381#64 }

theorem witnessGhost_counter_gt (B : BitVec 64) :
    (witnessGhost B).counter.toNat > (witnessGhost B).ck.index.toNat + 1 := by
  dsimp only [witnessGhost, ck0]
  decide

theorem st0_findReceiverChainIndex : st0.findReceiverChainIndex pk0 = some 0 := by
  simp [st0, c0, RatchetState.findReceiverChainIndex, List.findIdx?, List.findIdx?.go]

theorem witnessGhost_findIdx (B : BitVec 64) :
    (witnessGhost B).st.findReceiverChainIndex (witnessGhost B).their = some 0 ∧
    ∃ (h0 : 0 < (witnessGhost B).G.chains.length), ((witnessGhost B).G.chains[0]'h0).mkCap = 0 := by
  refine ⟨st0_findReceiverChainIndex, ⟨by simp [witnessGhost, G0], rfl⟩⟩

set_option linter.unusedSimpArgs false in
theorem witnessGhost_model_ok (F : ShaState → List (BitVec 8) → ShaState) (B : BitVec 64) :
    ∃ k, ((witnessGhost B).model F).1 = .ok k := by
  let ck1 : ChainKey := ⟨bytesToKey32 (Ratchet.chainHmac F ck0.key Ratchet.chainKeySeed), 4#32⟩
  let ck2 : ChainKey := ⟨bytesToKey32 (Ratchet.chainHmac F ck1.key Ratchet.chainKeySeed), 5#32⟩
  refine ⟨ck2.messageKeys F, ?_⟩
  unfold ConsumeMessageKeyGhost.model witnessGhost RatchetState.consumeMessageKey
  have hlt0 : ¬ (5#32 < (3#32 : BitVec 32)) := by decide
  have hlt3 : (3#32 : BitVec 32) < 5#32 := by decide
  have hlt4 : (4#32 : BitVec 32) < 5#32 := by decide
  have hpk : (pk0 == pk0) = true := by decide
  simp [Mut.exec, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    ExceptT.lift, ExceptT.map, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
    StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.set, StateT.map,
    bind, pure, get, getThe, MonadStateOf.get, set, Functor.map,
    st0, c0, ck0, ck1, ck2, hlt0, hlt3, hlt4, hpk,
    RatchetState.advanceChain,
    RatchetState.storeSkippedKey, RatchetState.setReceiverChainKey,
    RatchetState.findReceiverChainIndex, List.findIdx?, List.findIdx?.go,
    ChainKey.nextChainKey, liftE, maxMessageKeys]

/-! ## Loaded Image Bounds -/

theorem mem_of_lookup_eq_some {α : Type} {name : String} {v : α} {xs : List (String × α)}
    (h : Obj.lookup name xs = some v) : ∃ k, (k, v) ∈ xs := by
  unfold Obj.lookup at h
  cases hf : xs.find? (·.1 == name) with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨p.1, List.mem_of_find?_eq_some hf⟩

theorem getD_eq_getElem {α : Type} (xs : List α) (d : α) {i : Nat} (hi : i < xs.length) :
    xs.getD i d = xs[i] := by
  simp [List.getD, hi]

theorem sub_base_add_ofNat (base : BitVec 64) {off : Nat} (hoff : off < 2 ^ 64) :
    (base + BitVec.ofNat 64 off - base).toNat = off := by
  have heq : base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off := by
    bv_omega
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]

theorem sub_base_of_sub_add (base c a : BitVec 64)
    (h : (a - (base + c)).toNat + c.toNat < 2 ^ 64) :
    (a - base).toNat = c.toNat + (a - (base + c)).toNat := by
  have heq : a - base = a - (base + c) + c := by bv_omega
  rw [heq, BitVec.toNat_add, Nat.mod_eq_of_lt h, Nat.add_comm]

theorem satisfies_two_disjoint_memRegions {m : Memory} {b1 : BitVec 64} {n1 : Nat}
    {b2 : BitVec 64} {n2 : Nat}
    (h1 : m.RW b1 n1) (h2 : m.RW b2 n2)
    (hdisj : ∀ a, InRegion b1 n1 a → InRegion b2 n2 a → False) :
    m ⊨ memRegion b1 n1 ∗ memRegion b2 n2 := by
  by_cases hn10 : n1 = 0
  · subst hn10; rw [memRegion_zero, emp_sepConj]; exact ProofLib.satisfies_memRegion m b2 n2 h2
  by_cases hn20 : n2 = 0
  · subst hn20; rw [memRegion_zero, sepConj_emp]; exact ProofLib.satisfies_memRegion m b1 n1 h1
  have hn1 : n1 ≤ 2 ^ 64 := by
    by_contra hgt
    exact hdisj b2 (by unfold InRegion; have := (b2 - b1).isLt; omega)
      (by unfold InRegion; rw [BitVec.sub_self, BitVec.toNat_zero]; omega)
  have hn2 : n2 ≤ 2 ^ 64 := by
    by_contra hgt
    exact hdisj b1 (by unfold InRegion; rw [BitVec.sub_self, BitVec.toNat_zero]; omega)
      (by unfold InRegion; have := (b1 - b2).isLt; omega)
  have hm1 := ProofLib.satisfies_memRegion m b1 n1 h1
  rw [ProofLib.memRegion_eq_exists_bytes b1 n1 hn1, satisfies_sepExists] at hm1
  obtain ⟨bs1, hm1⟩ := hm1
  rw [satisfies_pure_sepConj] at hm1
  obtain ⟨hbs1, hm1⟩ := hm1
  have hm2 := ProofLib.satisfies_memRegion m b2 n2 h2
  rw [ProofLib.memRegion_eq_exists_bytes b2 n2 hn2, satisfies_sepExists] at hm2
  obtain ⟨bs2, hm2⟩ := hm2
  rw [satisfies_pure_sepConj] at hm2
  obtain ⟨hbs2, hm2⟩ := hm2
  have hs1 : ProofLib.SupportedOn 0#64 (fun k => InRegion b1 n1 (BitVec.ofNat 64 k)) m (memRegion b1 n1) := by
    refine ProofLib.SupportedOn.mono (hbs1 ▸ ProofLib.pointsToBytes_entails_memRegion b1 bs1) ?_
    refine ProofLib.SupportedOn.of_pointsToBytes hm1 fun a ha => ?_
    rw [BitVec.sub_zero, BitVec.ofNat_toNat]
    exact hbs1 ▸ ha
  have hs2 : ProofLib.SupportedOn 0#64 (fun k => InRegion b2 n2 (BitVec.ofNat 64 k)) m (memRegion b2 n2) := by
    refine ProofLib.SupportedOn.mono (hbs2 ▸ ProofLib.pointsToBytes_entails_memRegion b2 bs2) ?_
    refine ProofLib.SupportedOn.of_pointsToBytes hm2 fun a ha => ?_
    rw [BitVec.sub_zero, BitVec.ofNat_toNat]
    exact hbs2 ▸ ha
  exact (ProofLib.SupportedOn.sepConj hs1 hs2 fun k hk1 hk2 => hdisj (BitVec.ofNat 64 k) hk1 hk2).satisfies

theorem pk0_serialize_length : pk0.serialize.length = 33 := by decide

theorem srk_vecGhostAt_eq (B : BitVec 64) (hne : B + 280#64 ≠ 0) :
    vecGhostAt A₀ (g0 B).srk (B + 176#64) =
      ((B + 176#64) ↦₆₄ 33#64) ∗ ((B + 184#64) ↦₆₄ (B + 280#64)) ∗
        ((B + 192#64) ↦₆₄ 33#64) ∗ ((B + 280#64) ↦ₛ pk0.serialize) := by
  unfold vecGhostAt vecU8At vecHeader g0 A₀
  simp only [pk0_serialize_length, BitVec.ofNat_eq_ofNat, true_and,
    show (33#64 : BitVec 64).toNat < 2 ^ 63 by decide,
    show (33#64 : BitVec 64).toNat - 33 = 0 by decide,
    memRegion_zero, emp_sepConj, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (33 ≤ (33#64 : BitVec 64).toNat ∧ B + 280#64 ≠ 0#64) ↔ True :=
    iff_true_intro ⟨by decide, hne⟩
  have hif : ¬ ((33#64 : BitVec 64) = 0#64) := by decide
  rw [propext hpure, pure_true, emp_sepConj]
  simp only [hif, ↓reduceIte]
  ac_rfl

theorem priv_vecGhostAt_eq (B : BitVec 64) :
    vecGhostAt A₀ (g0 B).priv (B + 176#64 + 24#64) =
      ((B + 200#64) ↦₆₄ 0#64) ∗ ((B + 208#64) ↦₆₄ 1#64) ∗ ((B + 216#64) ↦₆₄ 0#64) := by
  unfold vecGhostAt vecU8At vecHeader g0
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, true_and,
    show (0#64 : BitVec 64).toNat < 2 ^ 63 by decide,
    ↓reduceIte, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64) ≠ 0#64) ↔ True := by decide
  rw [propext hpure, pure_true, sepConj_emp]

theorem mk_vecAt_eq (B : BitVec 64) :
    vecAt A₀ 104 8 (messageKeyAt A₀) (B + 176#64 + 48#64) (g0 B).mkCap (g0 B).mkPtr
      ((g0 B).keys.zip c0.messageKeys) =
      ((B + 224#64) ↦₆₄ 0#64) ∗ ((B + 232#64) ↦₆₄ 8#64) ∗ ((B + 240#64) ↦₆₄ 0#64) := by
  unfold vecAt vecHeader vecBuf g0 c0
  simp only [List.zip_nil_right, List.length_nil, BitVec.ofNat_eq_ofNat,
    true_and, show (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 by decide,
    ↓reduceIte, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (8#64 : BitVec 64) ≠ 0#64) ↔ True := by decide
  rw [propext hpure, pure_true, sepConj_emp]

theorem ck_optChainKeyAt_eq (B : BitVec 64) :
    optChainKeyAt A₀ (g0 B).ck c0.chainKey (B + 176#64 + 72#64) =
      ((B + 248#64) ↦₆₄ optChainKeyNone) ∗ memRegion (B + 256#64) 24 := by
  unfold optChainKeyAt g0 c0
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem chainAt_g0_c0_eq (B : BitVec 64) (hne280 : B + 280#64 ≠ 0) :
    chainAt A₀ (g0 B, c0) (B + 176#64) =
      ((B + 176#64) ↦₆₄ 33#64) ∗ ((B + 184#64) ↦₆₄ (B + 280#64)) ∗
        ((B + 192#64) ↦₆₄ 33#64) ∗ ((B + 280#64) ↦ₛ pk0.serialize) ∗
        ((B + 200#64) ↦₆₄ 0#64) ∗ ((B + 208#64) ↦₆₄ 1#64) ∗ ((B + 216#64) ↦₆₄ 0#64) ∗
        ((B + 224#64) ↦₆₄ 0#64) ∗ ((B + 232#64) ↦₆₄ 8#64) ∗ ((B + 240#64) ↦₆₄ 0#64) ∗
        ((B + 248#64) ↦₆₄ optChainKeyNone) ∗ memRegion (B + 256#64) 24 := by
  unfold chainAt
  rw [srk_vecGhostAt_eq B hne280, priv_vecGhostAt_eq B, mk_vecAt_eq B, ck_optChainKeyAt_eq B]
  have hpure : (PublicKey.deserialize (g0 B).srk.bytes = .ok c0.senderRatchetKey ∧
      c0.messageKeys.length ≤ maxMessageKeys ∧ (g0 B).keys.length = c0.messageKeys.length ∧
      (g0 B).srk.bytes.length = 33 ∧ (g0 B).priv.bytes = []) ↔ True := by
    simp [g0, c0, deserialize_pk0_serialize, maxMessageKeys]
    decide
  rw [propext hpure, pure_true, emp_sepConj]
  ac_rfl

theorem chains_vecAt_eq (B : BitVec 64) (hne176 : B + 176#64 ≠ 0) :
    vecAt A₀ 104 8 (chainAt A₀) B (G0 B).chainsCap (G0 B).chainsPtr
      ((G0 B).chains.zip st0.receiverChains) =
      (B ↦₆₄ 1#64) ∗ ((B + 8#64) ↦₆₄ (B + 176#64)) ∗ ((B + 16#64) ↦₆₄ 1#64) ∗
        chainAt A₀ (g0 B, c0) (B + 176#64) := by
  unfold vecAt vecHeader vecBuf G0 st0 A₀ arrayAt
  simp only [List.zip_cons_cons, List.zip_nil_right, List.length_singleton,
    BitVec.ofNat_eq_ofNat, true_and,
    show (1#64 : BitVec 64).toNat * 104 < 2 ^ 63 by decide,
    show ((1#64 : BitVec 64).toNat - 1) * 104 = 0 by decide,
    memRegion_zero, emp_sepConj, sepConj_emp]
  have hpure : (1 ≤ (1#64 : BitVec 64).toNat ∧ B + 176#64 ≠ 0#64) ↔ True :=
    iff_true_intro ⟨by decide, hne176⟩
  have hif : ¬ ((1#64 : BitVec 64) = 0#64) := by decide
  rw [propext hpure, pure_true, emp_sepConj]
  simp only [hif, ↓reduceIte]
  unfold arrayAt
  rw [sepConj_emp]
  ac_rfl

theorem ratchetAt_G0_st0_eq (B : BitVec 64) (hne176 : B + 176#64 ≠ 0) (hne280 : B + 280#64 ≠ 0) :
    ratchetAt A₀ B (G0 B) st0 =
      (B ↦₆₄ 1#64) ∗ ((B + 8#64) ↦₆₄ (B + 176#64)) ∗ ((B + 16#64) ↦₆₄ 1#64) ∗
        ((B + 176#64) ↦₆₄ 33#64) ∗ ((B + 184#64) ↦₆₄ (B + 280#64)) ∗
        ((B + 192#64) ↦₆₄ 33#64) ∗ ((B + 280#64) ↦ₛ pk0.serialize) ∗
        ((B + 200#64) ↦₆₄ 0#64) ∗ ((B + 208#64) ↦₆₄ 1#64) ∗ ((B + 216#64) ↦₆₄ 0#64) ∗
        ((B + 224#64) ↦₆₄ 0#64) ∗ ((B + 232#64) ↦₆₄ 8#64) ∗ ((B + 240#64) ↦₆₄ 0#64) ∗
        ((B + 248#64) ↦₆₄ optChainKeyNone) ∗ memRegion (B + 256#64) 24 ∗
        ((B + 24#64) ↦ₛ optSenderChainBytes none (List.replicate 100 0#8)) ∗
        ((B + 128#64) ↦ₛ keyToBytes32 0#256) ∗
        ((B + 160#64) ↦₆₄ BitVec.ofNat 64 25000) ∗
        ((B + 168#64) ↦₃₂ 0#32) ∗ memRegion (B + 172#64) 4 := by
  unfold ratchetAt
  rw [chains_vecAt_eq B hne176, chainAt_g0_c0_eq B hne280]
  have hpure : ((G0 B).chains.length = st0.receiverChains.length ∧
      (G0 B).senderPad.length = 100 ∧ st0.maxForwardJumps < 2 ^ 64) ↔ True := by
    simp [G0, st0]
  rw [propext hpure, pure_true, emp_sepConj]
  dsimp only [G0, st0]
  ac_rfl

theorem split_arena_region (B : BitVec 64) {off k off' rem' rem : Nat}
    (h : decide (off + k = off' ∧ k + rem' = rem ∧ rem ≤ 2 ^ 64) = true) :
    memRegion (B + BitVec.ofNat 64 off) rem =
      memRegion (B + BitVec.ofNat 64 off) k ∗ memRegion (B + BitVec.ofNat 64 off') rem' := by
  obtain ⟨hoff, hrem, hle⟩ := of_decide_eq_true h
  subst hoff; subst hrem
  rw [memRegion_split (B + BitVec.ofNat 64 off) k rem' hle,
    BitVec.add_assoc, ← BitVec.ofNat_add]

@[expose] def bytesOf64 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

@[expose] def bytesOf32 (v : BitVec 32) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8]

theorem pointsTo64_eq_pointsToBytes (a v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦ₛ bytesOf64 v) := by
  unfold pointsTo64 bytesOf64
  simp only [pointsToBytes_cons, pointsToBytes_nil,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]

end CryptoVerification.LibsignalSession.NonVacuityWitness
