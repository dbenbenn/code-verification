/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeShallow
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndAux
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndTrue
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalse
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.E2E.SessionAuthWireEnd

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndMix

public section

open scoped ENNReal
open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.FSAEAD (MakesAtMostQueries RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.FSAEAD.Thm5 (hp)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM.Construction (Header healEpoch fsaeadMultiHeaderAdIface fsClamp)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lChainPRG lAeadR lIdeal)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift lazyInit)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec fsInit fsImpl)
open _root_.CryptoVerification.E2E.Signed.SessionWire (sessQueryAt
  allSessions_hp_eq_hpIdeal_main allSessions_hp_eq_hpIdeal_la)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessPubFsAdv multiSessPubToAD)
open Computational.Proofs.E2E.SessionAuthPubToAD (multiSessPubToAD_isQueryBoundP_sessQueryAt)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb fsAtomicB)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (
  FSMultiBucketAuthState liftFSMultiBucket)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase (
  redFSAuthMultiBucketShallow redFSAuthMultiBucketProg_sess_isQueryBoundP)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeShallow (
  redFSAuthMultiBucketShallow_eval_eq)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndAux (
  PubMultiSpec pubMultiImpl idealSessImpl runPubIdeal LaRouterInv
  PubLaSafe pubQuery_inject_not_accepted_la
  PubFalseHoare pubQuery_tr_false pubQuery_cs_false pubQuery_dl_false pubQuery_ij_false
  evalDist_bind_eq_zero_of_support evalDist_eq_pure_false_of_support_false)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndTrue (
  FSLaSemantics redFSAuthMultiBucket_true_hoare)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseBase (FSFalseSemantics)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalse (
  redFSAuthMultiBucket_false_hoare)

private theorem lift_inr_query_eq {ι₁ ι₂ : Type}
    {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} (q₀ : s₂.Domain) :
    (liftM (OracleSpec.query q₀) : OracleComp (s₁ + s₂) (s₂.Range q₀)) =
      liftM (OracleSpec.query (spec := s₁ + s₂) (Sum.inr q₀)) := rfl

private theorem liftFSMultiBucket_run_query_eq {Pt RSt K I : Type} {ℓ : ℕ} (sIdx : ℕ)
    (q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (h : FSMultiBucketAuthState Pt RSt K I (ℕ × LibsignalCiphertextWithSalt32)) :
    ((liftFSMultiBucket
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
      (E := ℕ × LibsignalCiphertextWithSalt32)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
    (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => Pure.pure (a, h)) := by
  rw [lift_inr_query_eq]
  simp [liftFSMultiBucket, StateT.run_lift]

private def fsLaSemanticsInst {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ) :
    FSLaSemantics (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      Pt (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32 where
  Safe P x := PubLaSafe C ℓ encT idOf N P x
  pure ha := PubLaSafe.pure ha
  bind hx hf := PubLaSafe.bind hx hf
  any x := PubLaSafe.any C ℓ encT idOf N x
  ij_not_accepted sIdx hdr e hs := by
    let q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain :=
      Sum.inr (hdr, e)
    have hq₀ : (_root_.CryptoGames.FSAEAD.injectQuery
        (SenderState := RatchetSenderState (BitVec 256))
        (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256)) hdr e) =
      liftM (OracleSpec.query q₀) := by
      rw [lift_inr_query_eq]; simp [_root_.CryptoGames.FSAEAD.injectQuery, q₀]
    rw [hq₀, liftFSMultiBucket_run_query_eq sIdx q₀ hs]
    exact (pubQuery_inject_not_accepted_la C ℓ encT idOf N sIdx hdr e (fun a => (a, hs))).mono
      fun _ ⟨_, hp, hna⟩ => by subst hp; exact ⟨rfl, hna⟩

private def fsFalseSemanticsInst {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ) :
    FSFalseSemantics (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      Pt (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32 where
  H Pre Post x := PubFalseHoare C ℓ encT idOf N Pre Post x
  pure _ ha := PubFalseHoare.pure ha
  conseq hx hPre hPost := PubFalseHoare.conseq hx hPre hPost
  bind hx hf := PubFalseHoare.bind hx hf
  coin n := PubFalseHoare.query_inl C ℓ encT idOf N n
  tr sIdx hdr m hs := by
    intro Pre
    let q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain :=
      Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (hdr, m)))))
    have hq₀ : (_root_.CryptoGames.FSAEAD.transmitQuery
        (SenderState := RatchetSenderState (BitVec 256))
        (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
        (Ciphertext := ℕ × LibsignalCiphertextWithSalt32) hdr m) =
      liftM (OracleSpec.query q₀) := by
      rw [lift_inr_query_eq]; simp [_root_.CryptoGames.FSAEAD.transmitQuery, q₀]
    rw [hq₀, liftFSMultiBucket_run_query_eq sIdx q₀ hs]
    exact PubFalseHoare.conseq
      (pubQuery_tr_false C ℓ encT idOf N sIdx hdr m (fun a => (a, hs)))
      (fun _ _ h => h)
      fun _ _ _ ⟨ns, sc, hpre, hsc, hbr⟩ => by
        rcases hbr with ⟨hout, hns⟩ | ⟨ct, hout, hns⟩
        · subst hout; exact ⟨rfl, ns, sc, hpre, hsc, Or.inl ⟨rfl, hns⟩⟩
        · subst hout; exact ⟨rfl, ns, sc, hpre, hsc, Or.inr ⟨ct, rfl, hns⟩⟩
  cs sIdx hs := by
    intro Pre
    let q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain :=
      Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))
    have hq₀ : (_root_.CryptoGames.FSAEAD.corruptSenderQuery
        (SenderState := RatchetSenderState (BitVec 256))
        (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
        (AssocData := Header Pt) (Message := LibsignalMsgPublicPart × Plain ℓ)
        (Ciphertext := ℕ × LibsignalCiphertextWithSalt32)) =
      liftM (OracleSpec.query q₀) := by
      rw [lift_inr_query_eq]; simp [_root_.CryptoGames.FSAEAD.corruptSenderQuery, q₀]
    rw [hq₀, liftFSMultiBucket_run_query_eq sIdx q₀ hs]
    exact PubFalseHoare.conseq
      (pubQuery_cs_false C ℓ encT idOf N sIdx () (fun a => (a, hs)))
      (fun _ _ h => h)
      fun _ _ _ ⟨ns, sc, hpre, hns, hbr⟩ => by
        rcases hbr with ⟨hout, hsc⟩ | ⟨w, hout, hsc⟩
        · subst hout; exact ⟨rfl, ns, sc, hpre, hns, Or.inl ⟨rfl, hsc⟩⟩
        · subst hout; exact ⟨rfl, ns, sc, hpre, hns, Or.inr ⟨w, rfl, hsc⟩⟩
  dl sIdx hdr e hs := by
    intro Pre
    let q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain :=
      Sum.inl (Sum.inr (hdr, e))
    have hq₀ : (_root_.CryptoGames.FSAEAD.deliverQuery
        (SenderState := RatchetSenderState (BitVec 256))
        (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
        (Message := LibsignalMsgPublicPart × Plain ℓ) hdr e) =
      liftM (OracleSpec.query q₀) := by
      rw [lift_inr_query_eq]; simp [_root_.CryptoGames.FSAEAD.deliverQuery, q₀]
    rw [hq₀, liftFSMultiBucket_run_query_eq sIdx q₀ hs]
    exact PubFalseHoare.conseq
      (pubQuery_dl_false C ℓ encT idOf N sIdx hdr e (fun a => (a, hs)))
      (fun _ _ h => h)
      fun _ _ _ ⟨_, hout, hpre, hi⟩ => by subst hout; exact ⟨rfl, hpre, hi⟩
  ij sIdx hdr e hs := by
    intro Pre
    let q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain :=
      Sum.inr (hdr, e)
    have hq₀ : (_root_.CryptoGames.FSAEAD.injectQuery
        (SenderState := RatchetSenderState (BitVec 256))
        (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
        (Message := LibsignalMsgPublicPart × Plain ℓ) hdr e) =
      liftM (OracleSpec.query q₀) := by
      rw [lift_inr_query_eq]; simp [_root_.CryptoGames.FSAEAD.injectQuery, q₀]
    rw [hq₀, liftFSMultiBucket_run_query_eq sIdx q₀ hs]
    exact PubFalseHoare.conseq
      (pubQuery_ij_false C ℓ encT idOf N sIdx hdr e (fun a => (a, hs)))
      (fun _ _ h => h)
      fun _ _ _ ⟨_, hout, hpre, hi, hna⟩ => by subst hout; exact ⟨rfl, hpre, hi, hna⟩
  and_prop _ := by
    intro _ _ _ hx rc σ h z hz
    exact hx h.1 rc σ h.2 z hz

private theorem multiSessPubToAD_support_of_runPubIdeal {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (AdvPub : MultiSessPubFsAdv Pt ℓ)
    (h : ∀ w ∈ support (runPubIdeal C ℓ encT idOf N la AdvPub (fun _ => false) (fun _ => none)),
      w.1.1 = false) :
    ∀ z ∈ support
      ((simulateQ (idealSessImpl C ℓ encT idOf N la)
        (multiSessPubToAD protoSignalCodec AdvPub)).run (fun _ => none)),
      z.1 = false := by
  intro z hz
  change z ∈ support
    ((simulateQ (idealSessImpl C ℓ encT idOf N la)
      ((simulateQ pubMultiImpl AdvPub).run' (fun _ => false))).run
      (fun _ => none)) at hz
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, map_eq_bind_pure_comp,
    MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hzw⟩
  simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hzw
  subst hzw
  exact h w hw

attribute [local irreducible]
  Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.redFSAuthMultiBucketProg in
theorem multiSessEndWinProbMix_redFSAuthMultiBucket_eq_zero
    {α : Type} (oa : ProbComp α)
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : α → Party → IdentityKey) (lam : α → Pt)
    (q qR B0 qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (A : α → OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : ∀ o ∈ support oa, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hqR : min (2 * q) (q + 2) ≤ qR) :
    let cut := authHopCutoff maxForwardJumps qR la
    𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT (idOf o)) (lChainPRG C.F) maxForwardJumps
          (hp cut cut la))))
        (multiSessPubToAD protoSignalCodec
          ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
              gMain la tL par).eval (fun _ => A o) ()))).run (fun _ => none)] {true} = 0 := by
  refine evalDist_bind_eq_zero_of_support oa
    (fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT (idOf o)) (lChainPRG C.F) maxForwardJumps
          (hp (authHopCutoff maxForwardJumps qR la) (authHopCutoff maxForwardJumps qR la) la))))
        (multiSessPubToAD protoSignalCodec
          ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
              gMain la tL par).eval (fun _ => A o) ()))).run (fun _ => none))
    fun o ho => ?_
  have hqb0 := redFSAuthMultiBucketProg_sess_isQueryBoundP ℓ Pt C Dh encPt encT (idOf o) (lam o)
    q B0 qep gMain la tL par (A o) (hq o ho)
  set AdvPub : MultiSessPubFsAdv Pt ℓ :=
    (redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
      gMain la tL par).eval (fun _ => A o) ()
  have hqb : ∀ s, AdvPub.IsQueryBoundP (fun t => sessQueryAt s t = true) (min (2 * q) (q + 2)) := by
    intro s
    have hs : AdvPub.IsQueryBoundP
        (fun t => (match t with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
        (min (2 * q) (q + 2)) := hqb0 s
    exact hs.of_imp fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx
  have hqbAd : ∀ s,
      (multiSessPubToAD protoSignalCodec AdvPub).IsQueryBoundP
        (fun t => sessQueryAt s t = true) (min (2 * q) (q + 2)) :=
    fun s => multiSessPubToAD_isQueryBoundP_sessQueryAt protoSignalCodec AdvPub s (min (2 * q) (q + 2)) (hqb s)
  have heval_eq : AdvPub = _ :=
    redFSAuthMultiBucketShallow_eval_eq ℓ Pt C Dh encPt encT (idOf o) (lam o)
      q B0 qep gMain la tL par (A o) (hq o ho)
  cases la with
  | false =>
    have hEq := (allSessions_hp_eq_hpIdeal_main
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT (idOf o))
      (lChainPRG C.F) maxForwardJumps
      (multiSessPubToAD protoSignalCodec AdvPub)
      (fun _ => min (2 * q) (q + 2)) (N := authHopCutoff maxForwardJumps qR false)
      hqbAd (fun _ => by simpa [authHopCutoff] using hqR)).1
    rw [hEq]
    apply evalDist_eq_pure_false_of_support_false
    refine multiSessPubToAD_support_of_runPubIdeal C ℓ encT (idOf o)
      (authHopCutoff maxForwardJumps qR false) false AdvPub fun w hw => ?_
    rw [heval_eq] at hw
    exact redFSAuthMultiBucket_false_hoare
      (fsFalseSemanticsInst C ℓ encT (idOf o) (authHopCutoff maxForwardJumps qR false))
      q qep (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsClamp B0 (fsAtomicB C ℓ encT (idOf o) B0)) (lam o) gMain tL par (A o) (hq o ho)
      (fun _ => false) (fun _ => none) ⟨fun _ => rfl, fun _ => rfl⟩ w hw
  | true =>
    have hCut : ∀ (_ : ℕ),
        min (2 * q) (q + 2) + (maxForwardJumps + 1) ≤ authHopCutoff maxForwardJumps qR true :=
      fun _ => by simp only [authHopCutoff, ↓reduceIte]; exact Nat.add_le_add_right hqR _
    have hEq := (allSessions_hp_eq_hpIdeal_la
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT (idOf o))
      (lChainPRG C.F) maxForwardJumps
      (multiSessPubToAD protoSignalCodec AdvPub)
      (fun _ => min (2 * q) (q + 2)) (N := authHopCutoff maxForwardJumps qR true)
      hqbAd hCut).1
    rw [hEq]
    apply evalDist_eq_pure_false_of_support_false
    refine multiSessPubToAD_support_of_runPubIdeal C ℓ encT (idOf o)
      (authHopCutoff maxForwardJumps qR true) true AdvPub fun w hw => ?_
    rw [heval_eq] at hw
    have hInv0 : LaRouterInv (Pt := Pt) (ℓ := ℓ) (fun _ => none) := fun _ _ h => nomatch h
    exact (redFSAuthMultiBucket_true_hoare
      (fsLaSemanticsInst C ℓ encT (idOf o) (authHopCutoff maxForwardJumps qR true))
      (q + 1) (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsClamp B0 (fsAtomicB C ℓ encT (idOf o) B0)) (lam o) 1 qep gMain tL par (A o)
      (fun _ => false) (fun _ => none) hInv0 w hw).1

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndMix
