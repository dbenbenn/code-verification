/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFs -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.CryptoGames.SM.Theorem6Libsignal
import Computational.Proofs.CryptoGames.SM.Theorem8
import Computational.Proofs.SessionCostedHalt
import Computational.Proofs.SessionCostedSim
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp

/-!
# Libsignal Session Security with Prost's Codec

**Checked by Lean.** Proves `libsignal_session_sm_r1_proto`, bounding any `q`-query adversary's
advantage against `libsignalSessionScheme` with prost's codec (`protoSignalCodec`) in the restricted
ACD19 H1 game (DEV-LS1, DEV-LS2, DEV-LS3, DEV-LS4, DEV-LS5, DEV-LS6, DEV-LS7, DEV-LS22, DEV-LS27)
under SPQR-off correctness (`Corr.SpqrOffCorrect`, DEV-LS24). The bound leaves primitive and CKA
advantages uncomposed (DEV-LS30, DEV-LS31) and adds the Fig. 8 H1/authenticity and window terms
(DEV-LS12), evicted-epoch spurious steps (DEV-LS11), epoch-0 signed-pre-key injections (DEV-LS26),
and ratchet-key collisions (DEV-LS18).-/

namespace CryptoVerification.LibsignalSession
public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal


open CryptoVerification.LibsignalProtoCodec
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)

open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst Ratchet LibsignalInst
  LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme
  WireAEAD FSAEAD

/-- Tightened message, SPQR, and address length bounds matching `atomicFsOps` and `atomicFig8Ops` (`AtomicLengthsOk P ℓ → LengthsOk P ℓ`). -/
@[expose] def AtomicLengthsOk {PQ PQC : Type} (P : Params PQ PQC) (ℓ : ℕ) : Prop :=
  ℓ < 10 ^ 6 ∧
    (∀ st rq st' salt msg, P.spqr.send st rq = some (st', salt, msg) → msg.length ≤ 96) ∧
    (∀ a, P.addrAB = some a → a.length ≤ 128) ∧
    (∀ a, P.addrBA = some a → a.length ≤ 128)

theorem AtomicLengthsOk.toLengthsOk {PQ PQC : Type} {P : Params PQ PQC} {ℓ : ℕ}
    (hL : AtomicLengthsOk P ℓ) : LengthsOk P ℓ := by
  have hℓ := hL.1
  refine ⟨by omega, fun st rq st' salt msg hs => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have hm := hL.2.1 st rq st' salt msg hs; omega
  · have ha' := hL.2.2.1 a ha; omega
  · have ha' := hL.2.2.2 a ha; omega

section AtomicShortSim

open LibsignalSM.Proofs.QueryBounds
open LibsignalSM.Proofs.SessionShort (SendMsgsOk)
open LibsignalSM.Proofs.SessionShort.SimAndSM (badSendMsg)

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}

private abbrev QAtomicShort (Pt : Type) (ℓ : ℕ) : (FSpec Pt ℓ).Domain → Prop :=
  fun t => badSendMsg (St := LibsignalSim.Fig8St Pt) (Coins := BitVec 256)
    (C := LibsignalSim.Fig8C Pt) (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) t =
      true

omit [DecidableEq Pt] [Zero Pt] in
private theorem hQu_QAtomicShort : ∀ u : ℕ, ¬ QAtomicShort Pt ℓ (.inl u) := by
  intro _ h; nomatch h

omit [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem atomicShortB_mkPub {P : Params PQ PQC} (hL : AtomicLengthsOk P ℓ)
    (s : LibsignalSim.SimState PQ Pt ℓ) (R : Party) (rq : PQC) (pn : BitVec 32)
    {pq' : PQ} {pub : LibsignalMsgPublicPart}
    (hmk : LibsignalSim.mkPub (P := P) s R rq pn = some (pq', pub)) :
    atomicShortB pub = true := by
  unfold LibsignalSim.mkPub at hmk
  rcases Option.mem_map.mp hmk with ⟨⟨st', salt, msg⟩, hsend, hpair⟩
  obtain ⟨_, rfl⟩ := Prod.mk.inj hpair
  have hmsg : msg.length ≤ 96 := hL.2.1 (s.pq R) rq st' salt msg hsend
  have haddr : (if R == Party.A && s.unackA then P.addrAB else none).all
      (fun a => decide (a.length ≤ 128)) = true := by
    split
    · cases hAB : P.addrAB with
      | none => rfl
      | some a =>
        have ha := hL.2.2.1 a hAB
        simp only [Option.all, decide_eq_true_eq]
        exact ha
    · rfl
  unfold atomicShortB
  rw [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hmsg, haddr⟩

private theorem qb_simSend_QAtomicShort (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ) (qep : ℕ)
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    QB (QAtomicShort Pt ℓ) (LibsignalSim.simSend (P := P) (qep := qep) R m₀ chal r) 0 := by
  unfold LibsignalSim.simSend
  refine qb_bind0 qb_get fun s => ?_
  split
  · exact qb_pure none 0
  · cases s.mir.epMgmt 3 qep R r.isSome with
    | none => exact qb_pure none 0
    | some s₁ =>
      dsimp only
      split
      · exact qb_pure none 0
      · cases r with
        | some rq =>
          simp only [pure_bind]
          refine qb_bind0 (qb_map some (qb_coin hQu_QAtomicShort (BitVec 256))) fun _ => ?_
          cases hmk : LibsignalSim.mkPub (P := P) s R rq
              (if s₁.epoch R ≠ s.mir.epoch R then BitVec.ofNat 32 (s.mir.idx R - 1) else s.pn R) with
          | none => exact qb_pure none 0
          | some p =>
            rcases p with ⟨pq', pub⟩
            have hpub := atomicShortB_mkPub hL s R rq _ hmk
            dsimp only
            cases chal with
            | none =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some _ => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
            | some _ =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some _ => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
        | none =>
          refine qb_bind0 (qb_coin hQu_QAtomicShort PQC) fun rq => ?_
          simp only [pure_bind]
          cases hmk : LibsignalSim.mkPub (P := P) s R rq
              (if s₁.epoch R ≠ s.mir.epoch R then BitVec.ofNat 32 (s.mir.idx R - 1) else s.pn R) with
          | none => exact qb_pure none 0
          | some p =>
            rcases p with ⟨pq', pub⟩
            have hpub := atomicShortB_mkPub hL s R rq _ hmk
            dsimp only
            cases chal with
            | none =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some _ => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
            | some _ =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some _ => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0

omit [SampleableType PQC] in
private theorem qb_simRecv_QAtomicShort (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ) (R : Party) (w : List (BitVec 8))
    (isDel : Bool) :
    QB (QAtomicShort Pt ℓ)
      (LibsignalSim.simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := k) R w
        isDel) 0 := by
  have hQd : ∀ R c, QAtomicShort Pt ℓ (.inr (.inl (.inl (.inr (R, c))))) → 0 < 0 := by
    intro _ _ h; nomatch h
  have hQi : ∀ R c, QAtomicShort Pt ℓ (.inr (.inl (.inr (R, c)))) → 0 < 0 := by
    intro _ _ h; nomatch h
  unfold LibsignalSim.simRecv
  refine qb_bind0 qb_get fun s => ?_
  dsimp only
  refine qb_ite_pure (qb_ite_pure (qb_ite_pure (qb_ite_pure ?_)))
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact qb_pure (some RecvResult.rejected) 0
  | some hp =>
    dsimp only
    refine qb_ite_pure ?_
    cases P.spqr.recv (s.pq R) hp.1.pqRatchet with
    | error _ => exact qb_pure (some RecvResult.rejected) 0
    | ok ps =>
      dsimp only
      cases (s.chains R).findIdx? (fun g => g.key == some hp.1.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine qb_ite_pure ?_
        exact qb_bind_r (qb_fwd 0 hQd hQi R _) fun res =>
          qb_onAnswer qep R w isDel _ _ _ res
      | none =>
        dsimp only
        refine qb_ite_pure (qb_ite_pure ?_)
        refine qb_ite (qb_bind0 (qb_putS _) fun _ => ?_) ?_ <;>
        · split
          · refine qb_ite ?_ ?_
            · refine qb_ite ?_ (qb_bind0 (qb_modify _) fun _ => qb_pure none 0)
              cases decT hp.1.senderRatchetKey with
              | none => exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
              | some _ =>
                refine qb_bind_r (qb_fwd 0 hQd hQi R _) fun _ => ?_
                exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
            · refine qb_bind0 (qb_liftQ_query fun h => ?_) fun _ => ?_
              · simp [QAtomicShort, badSendMsg, atomicShortB, Option.all] at h
              · cases decT hp.1.senderRatchetKey with
                | none => exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
                | some _ =>
                  refine qb_bind_r (qb_fwd 0 hQd hQi R _) fun _ => ?_
                  exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
          · refine qb_ite_pure ?_
            cases decT hp.1.senderRatchetKey with
            | none => exact qb_pure (some RecvResult.rejected) 0
            | some _ =>
              exact qb_bind_r (qb_fwd 0 hQd hQi R _) fun res =>
                qb_onAnswer qep R w isDel none _ _ res

private theorem qb_simImpl_QAtomicShort (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (k : Option ℕ)
    (t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) :
    QB (QAtomicShort Pt ℓ) (LibsignalSim.simImpl P Dh encT decT qep k t) 0 := by
  have hQcorr : ∀ R, QAtomicShort Pt ℓ (.inr (.inr R)) → 0 < 0 := by
    intro _ h; nomatch h
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
  · exact qb_liftQ_query fun h => absurd h (hQu_QAtomicShort n)
  · exact qb_guard (qb_simSend_QAtomicShort P hL qep R m none r)
  · exact qb_guard (qb_simSend_QAtomicShort P hL qep R m₀ (some m₁) r)
  · exact qb_guard (qb_simRecv_QAtomicShort P encT decT qep k R w true)
  · exact qb_guard (qb_simRecv_QAtomicShort P encT decT qep k R w false)
  · exact qb_guard (qb_simCorr P Dh encT 0 hQcorr R)

theorem simRun_sendAtomicShort (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (k : Option ℕ) (A : LibAdv PQ PQC ℓ) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
      (LibsignalSim.simRun P Dh encT decT qep k A) := by
  have haux : IsQueryBoundP (LibsignalSim.simRun P Dh encT decT qep k A)
      (QAtomicShort Pt ℓ) 0 := by
    unfold LibsignalSim.simRun
    rw [← Nat.zero_add 0]
    refine isQueryBoundP_bind
      (isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QAtomicShort ($ᵗ BitVec 256)) fun pqrKey _ => ?_
    have hsim : IsQueryBoundP
        ((simulateQ (LibsignalSim.simImpl P Dh encT decT qep k) A).run
          (LibsignalSim.initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
        (QAtomicShort Pt ℓ) 0 :=
      isQueryBoundP_simulateQ_run_zero A (qb_simImpl_QAtomicShort P hL Dh encT decT qep k) _
    rw [StateT.run'_eq, ← Nat.add_zero 0]
    refine isQueryBoundP_bind ((isQueryBoundP_map_iff _ _ _).mpr hsim) fun b' _ => ?_
    cases k with
    | none => exact isQueryBoundP_pure _ b' 0
    | some _ => exact isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QAtomicShort ($ᵗ Bool)
  exact isQueryBoundP_congr (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) haux

end AtomicShortSim

section Session

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

private theorem probComp_bind_congr_of_support {α β : Type}
    (m : ProbComp α) (f g : α → ProbComp β) (h : ∀ z ∈ support m, f z = g z) :
    m >>= f = m >>= g := by
  induction m using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t cont ih =>
    simp only [bind_assoc]
    congr 1; funext u
    exact ih u fun z hz => h z (by
      simp only [mem_support_bind_iff]
      exact ⟨u, by simp, hz⟩)

end Session

/-! ## Joint satisfiability witness -/

section JointSat

local instance toyZero : Zero Bool := ⟨false⟩

@[expose] def toyDh : DHFun (BitVec 256) Bool := ⟨true, fun _ P => P⟩

@[expose] def toyEncPt : Bool → List (BitVec 8) := fun b => if b then x25519Base else List.replicate 32 0

@[expose] def toyCrypto (F : ShaCompress) : Crypto :=
  ⟨F, fun _ b => b, fun _ b => b, fun _ u => u, fun _ => vec32 x25519Base⟩

@[expose] def toyEncT (P : Bool) : PublicKey := ⟨vec32 (toyEncPt P)⟩

@[expose] def toyDecT (pk : PublicKey) : Option Bool :=
  if pk = toyEncT true then some true else if pk = toyEncT false then some false else none

private theorem atomicLengthsOk_satisfiable (C : Crypto) (idA idB : IdentityKey) :
    let P : Params Unit Unit := ⟨C, protoSignalCodec, spqrOff, idA, idB, none, none⟩
    P.codec = protoSignalCodec ∧ AtomicLengthsOk P 0 ∧ Corr.SpqrOffCorrect P.spqr := by
  refine ⟨rfl, ⟨by decide, ?_, by simp, by simp⟩, ?_⟩
  · intro st rq st' salt msg h
    simp only [spqrOff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    decide
  · refine ⟨fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    intro st r st' salt msg h st₂
    simp only [spqrOff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact ⟨(), rfl⟩

example (F : ShaCompress) (idA idB : IdentityKey) :
    let P : Params Unit Unit := ⟨toyCrypto F, protoSignalCodec, spqrOff, idA, idB, none, none⟩
    let idOf : Party → IdentityKey := fun p => match p with | .A => idA | .B => idB
    P.codec = protoSignalCodec ∧ AtomicLengthsOk P 0 ∧ toyDh.Commutes ∧
      X25519RealizesDh P.C toyDh toyEncPt toyEncT ∧ (∀ T, toyDecT (toyEncT T) = some T) ∧
      Function.Injective toyEncT ∧ (∀ T, toyEncT T ≠ dummyKey) ∧ (∀ x, toyDh.dh x 0 = 0) ∧
      Corr.SpqrOffCorrect P.spqr ∧ (∀ k x, P.C.D k (P.C.E k x) = x) ∧
      (idOf .A = P.idA ∧ idOf .B = P.idB) ∧ 2 * (0 + 1) + 25002 < 2 ^ 32 ∧
      (∀ Q : Bool,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | toyDh.dh x toyDh.base = Q} ≤ 1) := by
  intro P idOf
  obtain ⟨hP, hL, hS⟩ := atomicLengthsOk_satisfiable (toyCrypto F) idA idB
  refine ⟨hP, hL, fun _ _ => rfl, ⟨?_, fun _ => rfl⟩, ?_, ?_, ?_, fun _ => rfl, hS,
    fun _ _ => rfl, ⟨rfl, rfl⟩, by norm_num, fun _ => MeasureTheory.prob_le_one⟩
  · exact
      { enc_injective := by
          intro a b h; cases a <;> cases b <;> simp_all [toyEncPt, x25519Base]
        enc_length := by intro P; cases P <;> simp [toyEncPt, x25519Base]
        enc_zero := rfl
        enc_base := rfl
        base_ne_zero := by decide
        hook := fun _ P => by
          cases P
          · exact (by decide : (vec32 (toyEncPt false)).toList = toyEncPt false)
          · exact (by decide : (vec32 (toyEncPt true)).toList = toyEncPt true)
        pubKey_hook := fun _ => (by decide : (vec32 x25519Base).toList = x25519Base)
        dh_clamp := fun _ _ => rfl
        dh_ne_zero := fun _ _ h => h }
  · intro T; cases T <;> decide
  · intro a b h; cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))
  · intro T; cases T <;> decide

end JointSat

end

end CryptoVerification.LibsignalSession
