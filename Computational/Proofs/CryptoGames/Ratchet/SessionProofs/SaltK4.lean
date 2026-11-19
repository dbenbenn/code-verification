/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltK3 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.StateInv -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltK1 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltK2 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.CryptoGames.SM.Theorem7Proof

/-!
# Two-step sender seed extraction (`k4Seed`) and corruption-window exclusion

**Checked by Lean.** Defines `k4Seed` for branch K4 of `LibsignalSimC.snapshotMessageKeySeed` (DEV-LS37), proves trace-level completeness of K1–K4, and establishes `knownSeedR_none_no_corr_window`: when `snapshotMessageKeySeed` returns `none` on an accepted non-evicted honest delivery, no snapshot falls inside the active corruption window.-/

public section

open CryptoGames.Ratchet CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.CKA CryptoGames.SM
open CryptoGames.Ratchet.LibsignalSimC (chainKeyAfter chainSeedAt snapshotMessageKeySeed decryptWithKnownSeed)

namespace CryptoGames.LibsignalSM.Proofs.SaltMismatch

open CryptoGames.LibsignalSM.Proofs.Correctness CryptoGames.SM.Construction

/-- Seed extracted by branch K4 of `snapshotMessageKeySeed` via a two-step root-KDF chain from snapshots at epochs `t - 2` and `t`. -/
@[expose] def k4Seed (C : Crypto) (sc_cur? : Option SenderChain) (rc_last? : Option ReceiverChain)
    (rk_prev : LibsignalSession.RootKey) (sc_prev? : Option SenderChain)
    (Y : PublicKey) (n : BitVec 32) : Option (List (BitVec 8)) :=
  sc_cur?.bind fun sc_cur =>
    if sc_cur.ratchetKey.publicKey = Y then
      rc_last?.bind fun rc_last =>
        sc_prev?.bind fun sc_prev =>
          match rootCreateChain C rk_prev rc_last.senderRatchetKey
              sc_prev.ratchetKey.privateKey with
          | .ok (rk1, _) =>
            match rootCreateChain C rk1 rc_last.senderRatchetKey
                sc_cur.ratchetKey.privateKey with
            | .ok (_, ck0) => chainSeedAt C.F ck0 n
            | .error _ => none
          | .error _ => none
    else none

section TraceLemmas

variable {Pt : Type} [Zero Pt] [DecidableEq Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}

theorem k4Seed_eq_some_of_trace (hX : X25519RealizesDh C Dh encPt encT) (hDh : Dh.Commutes)
    (tr : EpochTrace C.F Dh encPt) {t : ℕ} (ht2 : 2 ≤ t) (ht : t ≤ tr.tFront)
    {sc_cur sc_prev : SenderChain} {rc_last : ReceiverChain}
    (hsc_cur : sc_cur.ratchetKey = KeyPair.generate C (tr.x t))
    (hrc_last : rc_last.senderRatchetKey = encT (tr.T (t - 1)))
    (hsc_prev : sc_prev.ratchetKey = KeyPair.generate C (tr.x (t - 2)))
    (n : BitVec 32) :
    k4Seed C (some sc_cur) (some rc_last) (tr.rk (t - 2)) (some sc_prev)
      (encT (tr.T t)) n = some (msgSeedAt C.F (tr.ck t) n.toNat) := by
  have hpk_cur : sc_cur.ratchetKey.publicKey = encT (tr.T t) := by
    rw [hsc_cur, KeyPair_generate_publicKey hX, EpochTrace.T]
  have hsk_cur : sc_cur.ratchetKey.privateKey = ⟨Ratchet.keyToBytesVec32 (clamp256 (tr.x t))⟩ := by
    rw [hsc_cur, KeyPair_generate_privateKey]
  have hsk_prev : sc_prev.ratchetKey.privateKey = ⟨Ratchet.keyToBytesVec32 (clamp256 (tr.x (t - 2)))⟩ := by
    rw [hsc_prev, KeyPair_generate_privateKey]
  have hT_ne : tr.T (t - 1) ≠ 0 := tr.T_ne_zero hX (t - 1)
  have hstep1 : Ratchet.rootKdf C.F (tr.rk (t - 2))
      (encPt (Dh.dh (tr.x (t - 2)) (tr.T (t - 1)))) = (tr.rk (t - 1), tr.ck (t - 1)) := by
    have h := tr.rootKdf_step_symm hDh (e := t - 2) (by omega)
    rwa [show t - 2 + 1 = t - 1 by omega] at h
  have hstep2 : Ratchet.rootKdf C.F (tr.rk (t - 1))
      (encPt (Dh.dh (tr.x t) (tr.T (t - 1)))) = (tr.rk t, tr.ck t) := by
    have h := tr.hStep (t - 1) (by omega)
    rwa [show t - 1 + 1 = t by omega] at h
  unfold k4Seed
  simp only [Option.bind_some, hpk_cur, ↓reduceIte, hrc_last, hsk_prev, hsk_cur,
    rootCreateChain_encT hX hT_ne, hstep1, hstep2]
  exact chainSeedAt_chainKeyValAt C.F (tr.ck t) (Nat.two_pow_pos 32) n (Nat.zero_le _)

theorem k2Seed_eq_some_of_trace (hX : X25519RealizesDh C Dh encPt encT) (hDh : Dh.Commutes)
    (tr : EpochTrace C.F Dh encPt) {e : ℕ} (he : e < tr.tFront)
    {sc : SenderChain} (hsc : sc.ratchetKey = KeyPair.generate C (tr.x e))
    (n : BitVec 32) :
    k2Seed C (tr.rk e) (some sc) (encT (tr.T (e + 1))) n =
      some (msgSeedAt C.F (tr.ck (e + 1)) n.toNat) := by
  have hsk : sc.ratchetKey.privateKey = ⟨Ratchet.keyToBytesVec32 (clamp256 (tr.x e))⟩ := by
    rw [hsc, KeyPair_generate_privateKey]
  have hT_ne : tr.T (e + 1) ≠ 0 := tr.T_ne_zero hX (e + 1)
  have hstep := tr.rootKdf_step_symm hDh he
  unfold k2Seed
  simp only [Option.bind_some, hsk, rootCreateChain_encT hX hT_ne, hstep]
  exact chainSeedAt_chainKeyValAt C.F (tr.ck (e + 1)) (Nat.two_pow_pos 32) n (Nat.zero_le _)

theorem k3Seed_eq_some_of_trace (hX : X25519RealizesDh C Dh encPt encT)
    (tr : EpochTrace C.F Dh encPt) {t j : ℕ} (hj : j < 2 ^ 32)
    {sc : SenderChain} (hrk : sc.ratchetKey = KeyPair.generate C (tr.x t))
    (hck : sc.chainKey = ⟨chainKeyValAt C.F (tr.ck t) j, BitVec.ofNat 32 j⟩)
    {n : BitVec 32} (hle : j ≤ n.toNat) :
    k3Seed C.F sc (encT (tr.T t)) n = some (msgSeedAt C.F (tr.ck t) n.toNat) := by
  have hpk : sc.ratchetKey.publicKey = encT (tr.T t) := by
    rw [hrk, KeyPair_generate_publicKey hX, EpochTrace.T]
  unfold k3Seed
  simp only [hpk, ↓reduceIte, hck, chainSeedAt_chainKeyValAt C.F (tr.ck t) hj n hle]

/-- Invariant relating a corruption snapshot in `snaps` to the epoch trace `tr` and current receiver state `s_Q`. -/
structure SnapInv {PQ : Type} (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (tr : EpochTrace C.F Dh encPt)
    (Q : Party) (s_Q : RatchetState) (maxAcc_Q : ℕ → ℕ)
    (snap : Party × ℕ × GhostState PQ) : Prop where
  sendsIn_eq : snap.1.sendsIn snap.2.1 = true
  le_tFront : snap.2.1 ≤ tr.tFront
  rk_eq : snap.2.2.session.rootKey = tr.rk snap.2.1
  sc_inv : ∃ j < 2 ^ 32,
    snap.2.2.session.senderChain =
      some ⟨KeyPair.generate C (tr.x snap.2.1),
            ⟨chainKeyValAt C.F (tr.ck snap.2.1) j, BitVec.ofNat 32 j⟩⟩
  chains_len : snap.2.2.session.receiverChains.length = (storedEpochs snap.1 snap.2.1).length
  chains_inv : ∀ k (hk : k < (storedEpochs snap.1 snap.2.1).length),
    let ep := (storedEpochs snap.1 snap.2.1)[k]
    ∃ rc maxSnap,
      snap.2.2.session.receiverChains[k]? = some rc ∧
      rc.senderRatchetKey = encT (tr.T ep) ∧
      RcvChainInv C.F (tr.ck ep) maxSnap rc ∧
      (snap.1 = Q →
        maxSnap ≤ maxAcc_Q ep ∧
        ∀ idx c, s_Q.findReceiverChainIndex (encT (tr.T ep)) = some idx →
          s_Q.receiverChains[idx]? = some c →
          ∀ mk ∈ c.messageKeys, mk.counter.toNat < maxSnap → mk ∈ rc.messageKeys)

omit [Zero Pt] [DecidableEq Pt] in
theorem SnapInv.getLast?_senderRatchetKey {PQ : Type}
    {tr : EpochTrace C.F Dh encPt} {Q : Party} {s_Q : RatchetState} {maxAcc_Q : ℕ → ℕ}
    {snap : Party × ℕ × GhostState PQ}
    (hsnap : SnapInv C Dh encPt encT tr Q s_Q maxAcc_Q snap)
    {t : ℕ} (hP : snap.1 = Q.other) (ht_eq : snap.2.1 = t) (ht2 : 2 ≤ t) :
    ∃ rc_last, snap.2.2.session.receiverChains.getLast? = some rc_last ∧
      rc_last.senderRatchetKey = encT (tr.T (t - 1)) := by
  have hsends : Q.other.sendsIn t = true := hP ▸ ht_eq ▸ hsnap.sendsIn_eq
  have hns : Q.other.sendsIn (t - 1) = false := by
    have h1 : (t - 1) + 1 = t := by omega
    rw [← h1, Party.sendsIn_succ] at hsends
    simpa using hsends
  have hdiv : (t - (t - 1)) / 2 < maxReceiverChains := by
    rw [show t - (t - 1) = 1 by omega]; decide
  rcases storedEpochs_getElem?_from_end Q.other t (t - 1) (by omega) hns hdiv with
    ⟨hlen_pos, hget_ep⟩
  rw [show (t - (t - 1)) / 2 = 0 by omega, Nat.sub_zero] at hget_ep
  have hk_lt :
      (storedEpochs snap.1 snap.2.1).length - 1 < (storedEpochs snap.1 snap.2.1).length := by
    rw [hP, ht_eq]; omega
  rcases hsnap.chains_inv ((storedEpochs snap.1 snap.2.1).length - 1) hk_lt with
    ⟨rc_last, _, hget_rc, hrk, _, _⟩
  have hep_eq :
      (storedEpochs snap.1 snap.2.1)[(storedEpochs snap.1 snap.2.1).length - 1] = t - 1 := by
    have hget_ep' : (storedEpochs snap.1 snap.2.1)[(storedEpochs snap.1 snap.2.1).length - 1]? =
        some (t - 1) := by simpa [hP, ht_eq] using hget_ep
    rw [List.getElem?_eq_getElem hk_lt, Option.some.injEq] at hget_ep'
    exact hget_ep'
  have hlast : snap.2.2.session.receiverChains.getLast? =
      snap.2.2.session.receiverChains[snap.2.2.session.receiverChains.length - 1]? := by
    cases hrc : snap.2.2.session.receiverChains with
    | nil =>
      have h0 : (storedEpochs snap.1 snap.2.1).length = 0 := by
        rw [← hsnap.chains_len, hrc]; rfl
      omega
    | cons hd tl =>
      simp [List.getLast?_eq_getElem?]
  rw [hlast, hsnap.chains_len]
  exact ⟨rc_last, hget_rc, hep_eq ▸ hrk⟩

theorem mem_of_findSome?_eq_some {α β : Type} {f : α → Option β} {l : List α} {b : β}
    (h : l.findSome? f = some b) : ∃ x ∈ l, f x = some b := by
  rcases List.findSome?_eq_some_iff.mp h with ⟨l₁, x, l₂, rfl, hx, _⟩
  exact ⟨x, by simp, hx⟩

end TraceLemmas

end CryptoGames.LibsignalSM.Proofs.SaltMismatch
