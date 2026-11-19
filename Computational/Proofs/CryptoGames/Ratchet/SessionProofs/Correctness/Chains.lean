/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalSim
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.CryptoGames.SM.Theorem7Proof
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionProofDefs

/-!
# Receiver-chain and symmetric-ratchet invariants

**Checked by Lean.**

Defines `storedEpochs`, symmetric chain stepping (`chainKeyValAt`, `msgSeedAt`), skipped-key list
evolution (`pushSkipped`, `advanceKeys`), and the receiver-chain invariant `RcvChainInv` for
`libsignal_corr`.
-/

public section

open OracleComp OracleSpec ENNReal
open CryptoGames.CKA
open CryptoGames.Ratchet
open CryptoGames.LibsignalSession
open CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim
open CryptoGames.SM
open CryptoGames.SM.Construction

namespace CryptoGames.LibsignalSM.Proofs.Correctness

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Stored epochs -/

theorem Party.sendsIn_of_sub_mod_two {P : Party} {e t : ℕ} (hle : e ≤ t)
    (he : P.sendsIn e = false) :
    P.sendsIn t = decide ((t - e) % 2 = 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, t = e + d := ⟨t - e, by omega⟩
  clear hle
  rw [Nat.add_sub_cancel_left]
  induction d with
  | zero =>
    simp [he]
  | succ d ih =>
    rw [← Nat.add_assoc, Party.sendsIn_succ, ih]
    by_cases h : d % 2 = 1
    · have h' : (d + 1) % 2 ≠ 1 := by omega
      simp [h, h']
    · have h' : (d + 1) % 2 = 1 := by omega
      simp [h, h']

/-- The list of ghost epochs of stored receiver chains for party `P` at party epoch `t`. -/
@[expose] def storedEpochs (P : Party) : ℕ → List ℕ
  | 0 => match P with | .A => [0] | .B => []
  | t + 1 =>
    if P.sendsIn (t + 1) then storedEpochs P t
    else
      let l := storedEpochs P t ++ [t + 1]
      l.drop (l.length - maxReceiverChains)

theorem storedEpochs_length_le (P : Party) (t : ℕ) :
    (storedEpochs P t).length ≤ maxReceiverChains := by
  induction t with
  | zero =>
    cases P <;> decide
  | succ t ih =>
    dsimp only [storedEpochs]
    split
    · exact ih
    · simp only [List.length_drop, List.length_append, List.length_singleton, maxReceiverChains]
      omega

theorem storedEpochs_getElem?_from_end (P : Party) (t : ℕ) :
    ∀ e ≤ t, P.sendsIn e = false → (t - e) / 2 < maxReceiverChains →
      (t - e) / 2 < (storedEpochs P t).length ∧
      (storedEpochs P t)[(storedEpochs P t).length - 1 - (t - e) / 2]? = some e := by
  induction t with
  | zero =>
    intro e hle hs hlt
    have he0 : e = 0 := by omega
    subst he0
    cases P
    · decide
    · simp [Party.sendsIn] at hs
  | succ t ih =>
    intro e hle hs hlt
    by_cases het : e = t + 1
    · subst het
      simp only [Nat.sub_self, Nat.zero_div, Nat.sub_zero]
      dsimp only [storedEpochs]
      simp only [hs, Bool.false_eq_true, ↓reduceIte, List.length_drop, List.length_append,
        List.length_singleton, List.getElem?_drop]
      have hlen_le := storedEpochs_length_le P t
      have hpos : 0 < (storedEpochs P t).length + 1 - ((storedEpochs P t).length + 1 - maxReceiverChains) := by
        dsimp only [maxReceiverChains] at hlen_le ⊢; omega
      have hidx : (storedEpochs P t).length + 1 - maxReceiverChains +
          ((storedEpochs P t).length + 1 - ((storedEpochs P t).length + 1 - maxReceiverChains) - 1) =
          (storedEpochs P t).length := by
        dsimp only [maxReceiverChains] at hlen_le ⊢; omega
      refine ⟨hpos, ?_⟩
      rw [hidx, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    · have het_le : e ≤ t := by omega
      have hpar := Party.sendsIn_of_sub_mod_two (Nat.le_of_lt (by omega : e < t + 1)) hs
      dsimp only [storedEpochs]
      by_cases hst1 : P.sendsIn (t + 1) = true
      · simp only [hst1, ↓reduceIte]
        rw [hst1, eq_comm, decide_eq_true_eq] at hpar
        have hdiv : (t + 1 - e) / 2 = (t - e) / 2 := by omega
        rw [hdiv] at hlt ⊢
        exact ih e het_le hs hlt
      · have hst1' : P.sendsIn (t + 1) = false := Bool.eq_false_iff.mpr hst1
        simp only [hst1', Bool.false_eq_true, ↓reduceIte, List.length_drop, List.length_append,
          List.length_singleton, List.getElem?_drop]
        rw [hst1', eq_comm, decide_eq_false_iff_not] at hpar
        have hdiv : (t + 1 - e) / 2 = (t - e) / 2 + 1 := by omega
        have hlt_prev : (t - e) / 2 < maxReceiverChains := by omega
        rcases ih e het_le hs hlt_prev with ⟨hlen_prev, hget_prev⟩
        have hlen_le := storedEpochs_length_le P t
        have hlen_new : (t + 1 - e) / 2 <
            (storedEpochs P t).length + 1 - ((storedEpochs P t).length + 1 - maxReceiverChains) := by
          dsimp only [maxReceiverChains] at hlt hlen_prev hlen_le ⊢; omega
        have hidx : (storedEpochs P t).length + 1 - maxReceiverChains +
            ((storedEpochs P t).length + 1 - ((storedEpochs P t).length + 1 - maxReceiverChains) - 1 -
              (t + 1 - e) / 2) =
            (storedEpochs P t).length - 1 - (t - e) / 2 := by
          dsimp only [maxReceiverChains] at hlt hlen_prev hlen_le ⊢; omega
        have hlt_old : (storedEpochs P t).length - 1 - (t - e) / 2 < (storedEpochs P t).length := by
          omega
        refine ⟨hlen_new, ?_⟩
        rw [hidx, List.getElem?_append_left hlt_old]
        exact hget_prev

/-! ## Symmetric chain stepping -/

@[expose] def chainKeyValAt (F : ShaCompress) (ck0 : BitVec 256) : ℕ → BitVec 256
  | 0 => ck0
  | n + 1 => HKDF.bytesToKey32 (Ratchet.chainHmac F (chainKeyValAt F ck0 n) Ratchet.chainKeySeed)

@[expose] def msgSeedAt (F : ShaCompress) (ck0 : BitVec 256) (n : ℕ) : List (BitVec 8) :=
  Ratchet.chainHmac F (chainKeyValAt F ck0 n) Ratchet.messageKeySeed

theorem bitVec32_ofNat_ne_allOnes {n : ℕ} (hn : n + 1 < 2 ^ 32) :
    BitVec.ofNat 32 n ≠ BitVec.allOnes 32 := by
  intro h
  have hval := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, BitVec.toNat_allOnes] at hval
  omega

/-! ## Skipped-key list -/

@[expose] def pushSkipped (key : MessageKeyGenerator) (keys : List MessageKeyGenerator) :
    List MessageKeyGenerator :=
  let keys' := key :: keys
  if maxMessageKeys < keys'.length then keys'.dropLast else keys'

theorem mem_or_eq_getElem?_last_of_mem {α : Type} :
    ∀ {L : List α} {x : α}, x ∈ L →
      x ∈ L.dropLast ∨ L[L.length - 1]? = some x
  | [], _, hx => by simp at hx
  | [a], x, hx => by
    simp only [List.mem_singleton] at hx
    exact Or.inr (by simp [hx])
  | a :: b :: tl, x, hx => by
    simp only [List.dropLast, List.mem_cons] at hx ⊢
    rcases hx with rfl | hmem
    · exact Or.inl (Or.inl rfl)
    · rcases mem_or_eq_getElem?_last_of_mem (L := b :: tl) (List.mem_cons.mpr hmem) with hdl | hlast
      · exact Or.inl (Or.inr hdl)
      · exact Or.inr (by simpa using hlast)

theorem pushSkipped_subset (key : MessageKeyGenerator) (keys : List MessageKeyGenerator) :
    ∀ mk ∈ pushSkipped key keys, mk = key ∨ mk ∈ keys := by
  intro mk hmk
  dsimp only [pushSkipped] at hmk
  split at hmk
  · exact List.mem_cons.mp (List.dropLast_subset _ hmk)
  · exact List.mem_cons.mp hmk

theorem pushSkipped_pairwise_gt {key : MessageKeyGenerator} {keys : List MessageKeyGenerator}
    (hpw : (keys.map (fun mk => mk.counter.toNat)).Pairwise (· > ·))
    (hgt : ∀ mk ∈ keys, mk.counter.toNat < key.counter.toNat) :
    ((pushSkipped key keys).map (fun mk => mk.counter.toNat)).Pairwise (· > ·) := by
  have hcons : ((key :: keys).map (fun mk => mk.counter.toNat)).Pairwise (· > ·) := by
    simp only [List.map_cons, List.pairwise_cons, List.mem_map]
    refine ⟨?_, hpw⟩
    rintro _ ⟨mk, hmk, rfl⟩
    exact hgt mk hmk
  dsimp only [pushSkipped]
  split
  · exact hcons.sublist (List.Sublist.map _ (List.dropLast_sublist _))
  · exact hcons

@[expose] def advanceKeys (F : ShaCompress) (ck0 : BitVec 256) :
    ℕ → ℕ → List MessageKeyGenerator → List MessageKeyGenerator
  | 0, _, keys => keys
  | fuel + 1, p, keys =>
    advanceKeys F ck0 fuel (p + 1)
      (pushSkipped ⟨msgSeedAt F ck0 p, BitVec.ofNat 32 p⟩ keys)

theorem advanceKeys_wf_and_desc (F : ShaCompress) (ck0 : BitVec 256) :
    ∀ (fuel p : ℕ) (keys : List MessageKeyGenerator),
      p + fuel < 2 ^ 32 →
      (∀ mk ∈ keys,
        mk.counter.toNat < p ∧
        mk = ⟨msgSeedAt F ck0 mk.counter.toNat, BitVec.ofNat 32 mk.counter.toNat⟩) →
      (keys.map (fun mk => mk.counter.toNat)).Pairwise (· > ·) →
      (∀ mk ∈ advanceKeys F ck0 fuel p keys,
        mk.counter.toNat < p + fuel ∧
        mk = ⟨msgSeedAt F ck0 mk.counter.toNat, BitVec.ofNat 32 mk.counter.toNat⟩) ∧
      ((advanceKeys F ck0 fuel p keys).map (fun mk => mk.counter.toNat)).Pairwise (· > ·)
  | 0, p, keys, _, hwf, hpw => by
    simp only [advanceKeys, Nat.add_zero]
    exact ⟨hwf, hpw⟩
  | fuel + 1, p, keys, hlt, hwf, hpw => by
    dsimp only [advanceKeys]
    set key : MessageKeyGenerator := ⟨msgSeedAt F ck0 p, BitVec.ofNat 32 p⟩
    have hp_lt : p < 2 ^ 32 := by omega
    have hkey_toNat : key.counter.toNat = p := by
      dsimp only [key]
      exact Nat.mod_eq_of_lt hp_lt
    have hgt : ∀ mk ∈ keys, mk.counter.toNat < key.counter.toNat := by
      intro mk hmk
      rw [hkey_toNat]
      exact (hwf mk hmk).1
    have hwf' : ∀ mk ∈ pushSkipped key keys,
        mk.counter.toNat < p + 1 ∧
        mk = ⟨msgSeedAt F ck0 mk.counter.toNat, BitVec.ofNat 32 mk.counter.toNat⟩ := by
      intro mk hmk
      rcases pushSkipped_subset key keys mk hmk with rfl | hmem
      · rw [hkey_toNat]
        exact ⟨by omega, rfl⟩
      · rcases hwf mk hmem with ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    have hpw' := pushSkipped_pairwise_gt hpw hgt
    have hih := advanceKeys_wf_and_desc F ck0 fuel (p + 1) (pushSkipped key keys)
      (by omega) hwf' hpw'
    have hadd : p + 1 + fuel = p + (fuel + 1) := by omega
    rw [hadd] at hih
    exact hih

/-! ## Receiver-chain invariant -/

/-- Invariant on a stored `ReceiverChain` for an epoch with initial chain key `ck0` and maximum
accepted 1-based index `maxAcc`. -/
structure RcvChainInv (F : ShaCompress) (ck0 : BitVec 256) (maxAcc : ℕ)
    (c : ReceiverChain) : Prop where
  maxAcc_lt : maxAcc < 2 ^ 32
  ck_eq : c.chainKey = some ⟨chainKeyValAt F ck0 maxAcc, BitVec.ofNat 32 maxAcc⟩
  keys_wf : ∀ mk ∈ c.messageKeys,
    mk.counter.toNat < maxAcc ∧
    mk = ⟨msgSeedAt F ck0 mk.counter.toNat, BitVec.ofNat 32 mk.counter.toNat⟩
  keys_desc : (c.messageKeys.map (fun mk => mk.counter.toNat)).Pairwise (· > ·)

def updateChainAt (s : RatchetState) (idx : ℕ) (c' : ReceiverChain) : RatchetState :=
  { s with receiverChains := s.receiverChains.set idx c' }

theorem findIdx?_senderRatchetKey_set :
    ∀ (l : List ReceiverChain) (idx : ℕ) (c c' : ReceiverChain) (their : PublicKey),
      l[idx]? = some c → c'.senderRatchetKey = c.senderRatchetKey →
      (l.set idx c').findIdx? (fun d => d.senderRatchetKey == their) =
        l.findIdx? (fun d => d.senderRatchetKey == their)
  | [], _, _, _, _, hget, _ => by simp at hget
  | d :: tl, 0, c, c', their, hget, hrk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    simp [List.findIdx?_cons, hrk]
  | d :: tl, idx + 1, c, c', their, hget, hrk => by
    simp only [List.getElem?_cons_succ] at hget
    simp [List.findIdx?_cons, findIdx?_senderRatchetKey_set tl idx c c' their hget hrk]

theorem getElem?_updateChainAt_self {s : RatchetState} {idx : ℕ} {c : ReceiverChain}
    (hget : s.receiverChains[idx]? = some c) (c' : ReceiverChain) :
    (updateChainAt s idx c').receiverChains[idx]? = some c' := by
  have hlt : idx < s.receiverChains.length := (List.getElem?_eq_some_iff.mp hget).1
  exact List.getElem?_set_self hlt

theorem findIdx?_eq_some_getElem? {α : Type} :
    ∀ {l : List α} {p : α → Bool} {pos : ℕ},
      l.findIdx? p = some pos → ∃ x, l[pos]? = some x ∧ p x = true
  | [], _, _, h => by simp at h
  | a :: tl, p, pos, h => by
    simp only [List.findIdx?_cons] at h
    by_cases hpa : p a = true
    · simp only [hpa, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨a, rfl, hpa⟩
    · have hpa' : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpa', Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      rcases h with ⟨pos', hfind, rfl⟩
      rcases findIdx?_eq_some_getElem? hfind with ⟨x, hget, hpx⟩
      exact ⟨x, hget, hpx⟩

theorem Mut.exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match (Mut.exec m s).1 with
      | Except.ok a => Mut.exec (f a) (Mut.exec m s).2
      | Except.error e => (Except.error e, (Mut.exec m s).2) := by
  dsimp only [Mut.exec, bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.bind, StateT.run]
  rcases m s with ⟨r, s'⟩
  cases r <;> rfl

theorem Mut.exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (Except.ok s, s) := rfl

theorem Mut.exec_set {σ : Type} (s s' : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (Except.ok (), s') := rfl

theorem Mut.exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (Except.ok a, s) := rfl

theorem Mut.exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (Except.error e, s) := rfl

theorem Mut.exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

end CryptoGames.LibsignalSM.Proofs.Correctness
