/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS3 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperBucketPRNG -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthLazy -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthFS -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMultiBase -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthHooksPot
import Computational.Proofs.E2E.SessionAuthMultiPot
import Computational.Proofs.GameHop.Rnd
import Computational.Proofs.GameHop.StateSim
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.E2E.SessionAuthMultiDec
import Computational.Proofs.E2E.SessionAuthMultiShort
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.FSAEADRed
/-! # Stage-2 Multi-Session Paper `DeliverForge` Hop-3 (`FSMultiSpec`) Bucket Bridges (`[B7]` × `[B8]`) -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti
public section
open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (Header Mode healEpoch sampleT inStage2BucketGen redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketMode PartyState)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF MakesAtMostQueriesDF authOutBucket authOutBucketPaper bucketAuthCfg engRunDFPaperBucket hooksLocalBucket initLocalBucket localAuthDFPaperBucket localAuthDFShiftedDir2Paper localAuthDFShiftedPaper)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart dummyKey lFS lIdeal lAeadR lChainPRG LibsignalCiphertextWithSalt32)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (badSendMsgDF SendMsgsOkDF GuardedSMDFShort)
open _root_.CryptoGames.FSAEAD (encBadMsg)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open _root_.CryptoVerification.LibsignalSession (FsAdv fsAuthCompBoundWith fsCostedRedsInst macForgeryTerm)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (lazyInit sessLift multiSessSpec sessOffRange onSess onAnySess isQueryBoundP_query_bind_pure_zero')
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl fsSpec)
open _root_.CryptoVerification.E2E.Signed.SessionQueries (fsInjQ isQueryBoundP_bind_zero_left)
open _root_.CryptoVerification.E2E.Signed.SessionWireQueries (GuardedMultiInjectShort fsOutsideClass onAnySess_fsOutsideClass_inr_spec)
open Computational.Proofs.E2E.SessionAuthPubToAD (multiSessPubToAD_offRange multiSessPubToAD_decBound multiSessPubToAD_shortAD multiSessPubToAD_oneADClass multiSessPubToAD_guardedShort)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessFsAdv multiSessPubToAD TwoModeMultiSessBounds RouterAdvCompat)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb multiSessEndWinProb multiSess_two_modes_le_sum_fsAuthCompBoundWith_min sum_range_mul_mod_div)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (redFSAuthDFShiftedPaperMultiGen redFSAuthDFShiftedPaperMulti redFSAuthDFShiftedDir2PaperMulti)
private theorem two_mul_evalDist_unif_bool_bind_aux (f : Bool → ProbComp Bool) :
    2 * 𝒟[($ᵗ Bool : ProbComp Bool) >>= f] {true} = 𝒟[f true] {true} + 𝒟[f false] {true} := by
  have hfg : (($ᵗ Bool : ProbComp Bool) >>= f) =
      (do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then f true else f false) := by
    congr 1; ext b; cases b <;> rfl
  rw [hfg, Computational.Proofs.GameHop.Rnd.evalDist_uniformBool_ite_true]
  exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
private theorem simulateQ_sessLift_sampleT_run_eq_aux {ι σ : Type} {G : OracleSpec.{0, 0} ι}
    (sub : QueryImpl G (StateT σ ProbComp)) {α : Type} [SampleableType α] (st : ℕ → σ) :
    (simulateQ (sessLift sub) (sampleT (tspec := multiSessSpec G) α)).run st =
      (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  unfold sampleT; induction ($ᵗ α : ProbComp α) using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind n k ih =>
    change (simulateQ (sessLift sub) ((query (spec := unifSpec + multiSessSpec G) (.inl n)) >>= fun u =>
        liftComp (k u) (unifSpec + multiSessSpec G))).run st = ((query (spec := unifSpec) n >>= k) >>= fun a => pure (a, st))
    rw [simulateQ_bind, StateT.run_bind, simulateQ_HasQuery_query]; simp only [sessLift, bind_assoc]
    exact congrArg (query (spec := unifSpec) n >>= ·) (funext fun u => ih u st)
private theorem sampleT_bind_isQueryBoundP_aux {ι : Type} {G : OracleSpec.{0, 0} ι} {α β : Type} [SampleableType α]
    (Pbad : (unifSpec + G).Domain → Prop) [DecidablePred Pbad] (hInl : ∀ n, ¬ Pbad (.inl n))
    {k : ℕ} (f : α → OracleComp (unifSpec + G) β) (hf : ∀ a, (f a).IsQueryBoundP Pbad k) :
    (sampleT (tspec := G) α >>= f).IsQueryBoundP Pbad k := by
  refine isQueryBoundP_bind_zero_left ?_ hf; unfold sampleT
  exact IsQueryBoundP.liftComp_subSpec (p := fun _ => False) (fun n => ⟨False.elim, fun h => hInl n h⟩)
    (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false ($ᵗ α : ProbComp α) 0)
private theorem sampleT_guardedMultiInjectShort_bind_aux {Pt : Type} {ℓ : ℕ} {α : Type} [SampleableType α]
    (f : α → MultiSessFsAdv Pt ℓ) (hf : ∀ a, GuardedMultiInjectShort (f a)) :
    GuardedMultiInjectShort (sampleT α >>= f) := by
  unfold GuardedMultiInjectShort sampleT
  exact (CryptoGames.GuardedSafe.GuardedSafePost.liftComp_unif
    (tspec := multiSessSpec (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32))
    (fun _ => False.elim) ($ᵗ α : ProbComp α)).bind fun a _ => hf a
section BucketTwoModeHelpers
open _root_.CryptoGames.FSAEAD (encBadMsg queryADOutsideClass transmitQuery challengeQuery corruptSenderQuery deliverQuery injectQuery)
open _root_.CryptoGames.SM (GameState Pos Record Config healedBy specDF)
open _root_.CryptoGames.SM.Engine (Hooks EState VP Ctx HM TComp liftH abortE coinsE vSend vRecv commitE deliverE injectE)
open _root_.CryptoGames.SM.Construction (PartyState sampleT mkParties bucketAuthCfgGen FSMultiSpec FSMultiBook FSMultiDFBucketState liftFSMultiDFBucket lookupMultiDFBucketF regSessMultiDFBucket regSessOptMultiDFBucket rootFSMultiDFBucketPaper hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode isHonestHdrFSMultiDFBucket initFSMultiDFBucketPaper redFSAuthDFPaperMultiBucketGen redFSAuthDFPaperMultiBucketModeGen)
open _root_.CryptoGames.SM.Construction.DeliverForge (transmitEBucket challEBucket corrEPaperBucket deliverForgeE implEDFPaperBucketRaw implEDFPaperBucket implEDFPaperBucketMode engRunDFPaperBucketMode withWinEpDF withWinEpDFMode)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB_imp_shortB)
private def ZeroPost {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (P : spec.Domain → Bool) (Post : α → Prop) (oa : OracleComp spec α) : Prop :=
  oa.IsQueryBoundP (fun x => P x = true) 0 ∧ ∀ z ∈ support oa, Post z
private theorem ZeroPost.pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} {P : spec.Domain → Bool} {Post : α → Prop} {a : α} (ha : Post a) :
    ZeroPost P Post (Pure.pure a : OracleComp spec α) :=
  ⟨isQueryBoundP_pure _ _ 0, fun z hz => by
    simp only [support_pure, Set.mem_singleton_iff] at hz; exact hz ▸ ha⟩
private theorem ZeroPost.bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {P : spec.Domain → Bool} {Mid : α → Prop} {Post : β → Prop} {mx : OracleComp spec α} {f : α → OracleComp spec β}
    (h : ZeroPost P Mid mx) (hf : ∀ a, Mid a → ZeroPost P Post (f a)) : ZeroPost P Post (mx >>= f) := by
  refine ⟨(isQueryBoundP_bind h.1 fun a ha => (hf a (h.2 a ha)).1).mono (by omega), ?_⟩
  intro z hz; rw [mem_support_bind_iff] at hz; obtain ⟨a, ha, hz⟩ := hz; exact (hf a (h.2 a ha)).2 z hz
private theorem ZeroPost.query_false {ι : Type} {spec : OracleSpec.{0, 0} ι} {P : spec.Domain → Bool} (t : spec.Domain) (ht : P t = false) :
    ZeroPost P (fun _ => True) (query (spec := spec) t) := by
  refine ⟨?_, fun _ _ => trivial⟩
  have hq : (query (spec := spec) t : OracleComp spec (spec.Range t)) =
      (query (spec := spec) t >>= fun r => Pure.pure r) := (bind_pure _).symm
  rw [hq]; exact isQueryBoundP_query_bind_pure_zero' t (by simp [ht]) id
private theorem ZeroPost.of_probComp {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} {α : Type}
    {P : (unifSpec + spec₀).Domain → Bool} (hInl : ∀ u, P (.inl u) = false) (oa : ProbComp α) : ZeroPost P (fun _ => True) (liftM oa : OracleComp (unifSpec + spec₀) α) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    change ZeroPost P (fun _ => True) (Pure.pure a); exact ZeroPost.pure trivial
  | query_bind t k ih =>
    change ZeroPost P (fun _ => True)
      ((query (spec := unifSpec + spec₀) (Sum.inl t)) >>= fun u =>
        (liftM (k u) : OracleComp (unifSpec + spec₀) α))
    exact (ZeroPost.query_false (spec := unifSpec + spec₀) (Sum.inl t) (hInl t)).bind fun u _ => ih u
private theorem zeroPost_simulateQ_run_zero_inr {ι₁ ι₂ : Type} {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} {S α : Type}
    (P : (unifSpec + s₂).Domain → Bool) (impl : QueryImpl (unifSpec + s₁) (StateT S (OracleComp (unifSpec + s₂))))
    (hInl : ∀ (u : unifSpec.Domain) (st : S), ZeroPost P (fun _ => True) ((impl (.inl u)).run st)) :
    ∀ (oa : OracleComp (unifSpec + s₁) α), oa.IsQueryBoundP (fun x => x.isRight = true) 0 → ∀ (st : S), ZeroPost P (fun _ => True) ((simulateQ impl oa).run st) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _ _; simp only [simulateQ_pure, StateT.run_pure]; exact ZeroPost.pure trivial
  | query_bind t r ih =>
    intro hq st; simp only [simulateQ_query_bind, StateT.run_bind]; rw [isQueryBoundP_query_bind_iff] at hq; rcases t with u | qr
    · exact (hInl u st).bind fun z _ => ih z.1 (by simpa using hq.2 z.1) z.2
    · simp at hq
private theorem zeroPost_simulateQ_run_fuel_bad {ι₁ ι₂ : Type} {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} {S α : Type}
    (Bad : (unifSpec + s₁).Domain → Bool) (P : (unifSpec + s₂).Domain → Bool) (Inv : ℕ → S → Prop) (impl : QueryImpl (unifSpec + s₁) (StateT S (OracleComp (unifSpec + s₂))))
    (hInl : ∀ (u : unifSpec.Domain) (rem : ℕ) (st : S), Inv rem st → ZeroPost P (fun z => Inv rem z.2) ((impl (.inl u)).run st))
    (hInr : ∀ (qr : s₁.Domain) (rem : ℕ) (st : S), Bad (.inr qr) = false → Inv (rem + 1) st → ZeroPost P (fun z => Inv rem z.2) ((impl (.inr qr)).run st)) :
    ∀ (rem : ℕ) (oa : OracleComp (unifSpec + s₁) α), oa.IsQueryBoundP (fun x => x.isRight = true) rem → oa.IsQueryBoundP (fun x => Bad x = true) 0 → ∀ (st : S), Inv rem st →
        ZeroPost P (fun _ => True) ((simulateQ impl oa).run st) := by
  intro rem oa
  induction oa using OracleComp.inductionOn generalizing rem with
  | pure a =>
    intro _ _ _ _; simp only [simulateQ_pure, StateT.run_pure]; exact ZeroPost.pure trivial
  | query_bind t r ih =>
    intro hq hbad st hst; simp only [simulateQ_query_bind, StateT.run_bind]; rw [isQueryBoundP_query_bind_iff] at hq hbad
    have hnb : ¬ (Bad t = true) := hbad.1.resolve_right (Nat.lt_irrefl 0)
    have hbad_cont : ∀ u, (r u).IsQueryBoundP (fun x => Bad x = true) 0 :=
      fun u => by simpa [hnb] using hbad.2 u
    rcases t with u | qr
    · exact (hInl u rem st hst).bind fun z hz =>
        ih z.1 rem (by simpa using hq.2 z.1) (hbad_cont z.1) z.2 hz
    · rcases rem with _ | rem'
      · simp at hq
      · have hnb' : Bad (.inr qr) = false := Bool.eq_false_iff.mpr hnb
        have hq_cont : ∀ u, (r u).IsQueryBoundP (fun x => x.isRight = true) rem' :=
          fun u => by simpa using hq.2 u
        exact (hInr qr rem' st hnb' hst).bind fun z hz =>
          ih z.1 rem' (hq_cont z.1) (hbad_cont z.1) z.2 hz
@[reducible] private def badBucketQuery {SS RS T M E : Type} (q qep : ℕ) (tL : Option ℕ) (okM : M → Bool) : (unifSpec + FSMultiSpec SS RS T M E).Domain → Bool
  | .inl _ => false
  | .inr ⟨sIdx, q₀⟩ => decide (((qep + 2) - healEpoch tL) * q ≤ sIdx) ||
    encBadMsg (SS := SS) (RS := RS) okM (.inr q₀) ||
    queryADOutsideClass (SS := SS) (RS := RS) (fun h : Header T => h.1)
      (healEpoch tL + sIdx / q) (.inr q₀)
private abbrev badBQ (SS RS T M E : Type) (q qep : ℕ) (tL : Option ℕ) (okM : M → Bool) :=
  badBucketQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) q qep tL okM
private theorem badBucketQuery_inl {SS RS T M E : Type} (q qep : ℕ) (tL : Option ℕ) (okM : M → Bool)
    (u : unifSpec.Domain) : badBQ SS RS T M E q qep tL okM (.inl u) = false := rfl
private def SlotAt (q qep : ℕ) (tL : Option ℕ) (t0 sIdx : ℕ) : Prop :=
  sIdx < ((qep + 2) - healEpoch tL) * q ∧ healEpoch tL + sIdx / q = t0 
private theorem healEpoch_le_of_inStage2BucketGen {Δbucket t0 : ℕ} {tL : Option ℕ} {par : Bool}
    (hΔb : 2 ≤ Δbucket) (hb : inStage2BucketGen Δbucket tL par t0 = true) : healEpoch tL ≤ t0 := by
  rcases tL with _ | l
  · exact Nat.zero_le _
  · unfold inStage2BucketGen at hb; rw [Bool.and_eq_true] at hb
    simp only [_root_.CryptoGames.SM.lastLeakGuessAdmissible, _root_.CryptoGames.SM.healedBy,
      healEpoch, decide_eq_true_eq] at hb ⊢; omega
private theorem slotAt_of_bucket {q Δbucket qep t0 r : ℕ} {tL : Option ℕ} {par : Bool} (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket) (ht_hi : t0 ≤ qep + 1)
    (hbuck : inStage2BucketGen Δbucket tL par t0 = true) (hr : r < q) : SlotAt q qep tL t0 (q * (t0 - healEpoch tL) + r) := by
  have ht_lo : healEpoch tL ≤ t0 := healEpoch_le_of_inStage2BucketGen hΔb hbuck
  set d := t0 - healEpoch tL
  have ht0_eq : healEpoch tL + d = t0 := by omega
  have hd_succ : d + 1 ≤ (qep + 2) - healEpoch tL := by omega
  have hlt : q * d + r < ((qep + 2) - healEpoch tL) * q := calc
    q * d + r < q * d + q := Nat.add_lt_add_left hr (q * d)
    _ = (d + 1) * q := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm d q]
    _ ≤ ((qep + 2) - healEpoch tL) * q := Nat.mul_le_mul_right q hd_succ
  have hdiv : (q * d + r) / q = d := by
    rw [Nat.add_comm (q * d) r, Nat.add_mul_div_left r d hqpos, Nat.div_eq_of_lt hr, Nat.zero_add]
  exact ⟨hlt, by rw [hdiv, ht0_eq]⟩
private def BucketVPInv {Γ T RSt SS RS : Type} (q qep : ℕ) (tL : Option ℕ) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) : Prop :=
  (∀ sIdx, vp.vS = some (.inr sIdx) →
    sIdx < ((qep + 2) - healEpoch tL) * q ∧
    (vp.id.sendsIn (vp.tcur + 1) = false → healEpoch tL + sIdx / q = vp.tcur)) ∧
  (∀ t' sIdx, vp.vR t' = some (.inr sIdx) → SlotAt q qep tL t' sIdx)
private def BucketHInv {T RSt K I E : Type} (q qep : ℕ) (tL : Option ℕ) (rem : ℕ) (h : FSMultiDFBucketState T RSt K I E) : Prop :=
  (∀ t, 1 ≤ t → (h.sessions t).length + rem ≤ q) ∧
  (∀ t c sIdx, h.cache t = some c → c.2.2.2 = some sIdx → SlotAt q qep tL t sIdx)
private theorem BucketHInv.mono {T RSt K I E : Type} {q qep rem₁ rem₂ : ℕ} {tL : Option ℕ}
    {h : FSMultiDFBucketState T RSt K I E} (hle : rem₁ ≤ rem₂) (hH : BucketHInv q qep tL rem₂ h) : BucketHInv q qep tL rem₁ h :=
  ⟨fun t ht => by have := hH.1 t ht; omega, hH.2⟩
private def BucketESInv {Γ T RSt SS RS M E K I : Type} (q qep : ℕ) (tL : Option ℕ) (rem : ℕ)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiDFBucketState T RSt K I E)) : Prop :=
  (∀ P, BucketVPInv q qep tL (es.g.st P)) ∧ BucketHInv q qep tL rem es.h
private theorem BucketESInv.mono {Γ T RSt SS RS M E K I : Type} {q qep rem₁ rem₂ : ℕ} {tL : Option ℕ}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiDFBucketState T RSt K I E)}
    (hle : rem₁ ≤ rem₂) (hes : BucketESInv q qep tL rem₂ es) : BucketESInv q qep tL rem₁ es :=
  ⟨hes.1, hes.2.mono hle⟩
private theorem sendsIn_succ_of_false (p : Party) (t' : ℕ) (hf : p.sendsIn t' = false) : p.sendsIn (t' + 1) = true := by
  cases p <;> simp [Party.sendsIn] at hf ⊢ <;> omega
private theorem epMgmt_st_eq {St M C : Type} {g s₁ : GameState St M C} {Δ qep : ℕ} {P : Party} {bad : Bool} (h : g.epMgmt Δ qep P bad = some s₁) : s₁.st = g.st := by
  unfold GameState.epMgmt at h; split at h
  · split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; dsimp only; split <;> rfl
  · split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; rfl
private theorem bucketVPInv_update {Γ T RSt SS RS : Type} {q qep : ℕ} {tL : Option ℕ} {st : Party → VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)} (hst : ∀ Q, BucketVPInv q qep tL (st Q))
    (P : Party) {vp' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)} (hvp' : BucketVPInv q qep tL vp') (Q : Party) : BucketVPInv q qep tL (Function.update st P vp' Q) := by
  by_cases hQP : Q = P
  · subst hQP; simpa only [Function.update_self] using hvp'
  · simpa only [Function.update_of_ne hQP] using hst Q
private theorem lift_inr_query_eq {ι₁ ι₂ : Type} {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} (q₀ : s₂.Domain) :
    (liftM (OracleSpec.query q₀) : OracleComp (s₁ + s₂) (s₂.Range q₀)) = liftM (OracleSpec.query (spec := s₁ + s₂) (Sum.inr q₀)) := rfl
private theorem liftH_zeroPost {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv T Sv SSv RSv M E α : Type} {P : (unifSpec + tspec).Domain → Bool} {Post : α × HS → Prop}
    {x : HM tspec HS α} {es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS} (hx : ZeroPost P Post (x.run es.h)) : ZeroPost P
      (fun z => Post (z.1, z.2.h) ∧ z.2.g = es.g ∧ z.2.abort = es.abort) ((liftH x).run es) := by
  unfold liftH; exact hx.bind fun ⟨a, h'⟩ hpost => ZeroPost.pure ⟨hpost, rfl, rfl⟩
private theorem sampleT_zeroPost {SS RS T M E : Type} (q qep : ℕ) (tL : Option ℕ) (okM : M → Bool)
    (α : Type) [SampleableType α] : ZeroPost (badBQ SS RS T M E q qep tL okM) (fun _ => True) (sampleT α) :=
  ZeroPost.of_probComp (badBucketQuery_inl q qep tL okM) ($ᵗ α : ProbComp α)
private theorem lift_sampleT_zeroPost {SS RS T M E HS : Type} (q qep : ℕ) (tL : Option ℕ)
    (okM : M → Bool) (α : Type) [SampleableType α] (h : HS) : ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => z.2 = h) ((StateT.lift (sampleT α)).run h) := by
  rw [StateT.run_lift]; exact (sampleT_zeroPost q qep tL okM α).bind fun _ _ => ZeroPost.pure rfl
private theorem liftFSMultiDFBucket_query_zeroPost {SS RS T M E Sig K I : Type} (q qep : ℕ) (tL : Option ℕ) (okM : M → Bool) (sIdx : ℕ)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain) (hq : badBQ SS RS T M E
      q qep tL okM (.inr ⟨sIdx, q₀⟩) = false) (h : FSMultiDFBucketState T Sig K I E) : ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => z.2 = h)
      ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E) sIdx
        (liftM (OracleSpec.query q₀))).run h) := by
  have hstep :
      ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E) sIdx
        (liftM (OracleSpec.query q₀))).run h) =
        (query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inr ⟨sIdx, q₀⟩) >>=
          fun r => Pure.pure (r, h)) := by
    rw [lift_inr_query_eq]; simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hstep]; exact (ZeroPost.query_false (spec := unifSpec + FSMultiSpec SS RS T M E)
    (Sum.inr ⟨sIdx, q₀⟩) hq).bind fun _ _ => ZeroPost.pure rfl
private theorem lookupMultiDFBucketF_zeroPost {SS RS T M E RSt K I : Type} [DecidableEq I] [SampleableType K] (q qep : ℕ) (tL : Option ℕ) (okM : M → Bool)
    (t0 : ℕ) (ik : I) (h : FSMultiDFBucketState T RSt K I E) : ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache)
      ((lookupMultiDFBucketF (SS := SS) (RS := RS) (M := M) t0 ik).run h) := by
  unfold lookupMultiDFBucketF; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (h.fTable t0).lookup ik with
  | some k => simp only [StateT.run_pure]; exact ZeroPost.pure ⟨rfl, rfl⟩
  | none =>
    simp only [StateT.run_bind]
    refine (lift_sampleT_zeroPost q qep tL okM K h).bind fun ⟨_, h1⟩ hh1 => ?_
    dsimp only at hh1; simp only [StateT.run_modify, StateT.run_pure, pure_bind]
    exact ZeroPost.pure ⟨by rw [hh1], by rw [hh1]⟩
private theorem regSessMultiDFBucket_step {T RSt K I E : Type} [DecidableEq I] {q Δbucket qep t0 rem : ℕ} {tL : Option ℕ} {par : Bool} (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket)
    (ht1 : 1 ≤ t0) (ht_hi : t0 ≤ qep + 1) (hbuck : inStage2BucketGen Δbucket tL par t0 = true)
    (ik : I) (h : FSMultiDFBucketState T RSt K I E) (hH : BucketHInv q qep tL (rem + 1) h) : SlotAt q qep tL t0 (regSessMultiDFBucket (q + 1) tL t0 ik h).1 ∧
      BucketHInv q qep tL rem (regSessMultiDFBucket (q + 1) tL t0 ik h).2 := by
  have hlen : (h.sessions t0).length < q := by have := hH.1 t0 ht1; omega
  unfold regSessMultiDFBucket; simp only [Nat.add_sub_cancel]; split_ifs with hmem
  · exact ⟨slotAt_of_bucket hqpos hΔb ht_hi hbuck
      (Nat.lt_trans (List.idxOf_lt_length_of_mem hmem) hlen),
      hH.mono (Nat.le_succ rem)⟩
  · refine ⟨slotAt_of_bucket hqpos hΔb ht_hi hbuck hlen, ⟨fun t ht => ?_, hH.2⟩⟩
    by_cases hEq : t = t0
    · subst hEq; have h1 := hH.1 t ht1; simp only [Function.update_self, List.length_append, List.length_singleton]; omega
    · have h1 := hH.1 t ht
      simp only [Function.update_of_ne hEq]; omega
private theorem regSessOptMultiDFBucket_step {T RSt K I E : Type} [DecidableEq I] {q Δbucket qep t0 rem : ℕ} {tL : Option ℕ} {par : Bool} (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket)
    (ht1 : 1 ≤ t0) (sid : Option I) (hsid : ∀ ik, sid = some ik → t0 ≤ qep + 1 ∧ inStage2BucketGen Δbucket tL par t0 = true)
    (h : FSMultiDFBucketState T RSt K I E) (hH : BucketHInv q qep tL (rem + 1) h) :
    (∀ sIdx, (regSessOptMultiDFBucket (q + 1) tL t0 sid h).1 = some sIdx → SlotAt q qep tL t0 sIdx) ∧
      BucketHInv q qep tL rem (regSessOptMultiDFBucket (q + 1) tL t0 sid h).2 := by
  cases sid with
  | none =>
    exact ⟨fun _ hs => by simp [regSessOptMultiDFBucket] at hs, hH.mono (Nat.le_succ rem)⟩
  | some ik =>
    obtain ⟨ht_hi, hbuck⟩ := hsid ik rfl; obtain ⟨hSlot, hH'⟩ := regSessMultiDFBucket_step hqpos hΔb ht1 ht_hi hbuck ik h hH
    refine ⟨fun sIdx hs => ?_, ?_⟩
    · simp only [regSessOptMultiDFBucket, Option.some.injEq] at hs; exact hs ▸ hSlot
    · simpa [regSessOptMultiDFBucket] using hH'
private theorem rootFSMultiDFBucketPaper_zeroPost {KR RSt K I T SS RS M E : Type} [DecidableEq I] [SampleableType I] [SampleableType K] (q : ℕ) (okM : M → Bool)
    (prng : PRFPRNG KR RSt I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : RSt) (h : FSMultiDFBucketState T RSt K I E) :
    ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
        (∀ ik, z.1.2.2 = some ik → t0 ≤ qep + 1 ∧ inStage2BucketGen Δbucket tL par t0 = true)) ((rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
        prng Δbucket qep tL par t0 pl ik0 σ0).run h) := by
  unfold rootFSMultiDFBucketPaper; dsimp only; split
  · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨rfl, rfl, fun _ hs => by cases hs⟩
  · next h1 =>
    have ht_hi : t0 ≤ qep + 1 := by
      by_cases hlt : qep + 1 < t0
      · simp [hlt] at h1
      · omega
    split
    · next hbuck =>
      split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_zeroPost q qep tL okM I h).bind fun ⟨_, h1'⟩ hh1 => ?_
        refine (lift_sampleT_zeroPost q qep tL okM K h1').bind fun ⟨_, h2'⟩ hh2 => ?_
        dsimp only at hh1 hh2; simp only [StateT.run_pure]
        exact ZeroPost.pure ⟨by rw [hh2, hh1], by rw [hh2, hh1], fun _ _ => ⟨ht_hi, hbuck⟩⟩
      · simp only [StateT.run_bind]
        refine (lookupMultiDFBucketF_zeroPost q qep tL okM t0 ik0 h).bind fun ⟨_, h1'⟩ ⟨hs1, hc1⟩ => ?_
        simp only [StateT.run_pure]; exact ZeroPost.pure ⟨hs1, hc1, fun _ _ => ⟨ht_hi, hbuck⟩⟩
    · split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_zeroPost q qep tL okM I h).bind fun ⟨_, h1'⟩ hh1 => ?_
        refine (lift_sampleT_zeroPost q qep tL okM K h1').bind fun ⟨_, h2'⟩ hh2 => ?_
        dsimp only at hh1 hh2; simp only [StateT.run_pure]
        exact ZeroPost.pure ⟨by rw [hh2, hh1], by rw [hh2, hh1], fun _ hs => by cases hs⟩
      · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨rfl, rfl, fun _ hs => by cases hs⟩
private theorem initFSMultiDFBucketPaper_zero_any {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (L q : ℕ) (okM : M → Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) : ZeroPost (badBQ SS RS T M E q qep tL okM) (fun _ => True)
      ((initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par).run ({} : FSMultiDFBucketState T RSt K I E)) := by
  unfold initFSMultiDFBucketPaper; simp only [StateT.run_bind]
  refine (lift_sampleT_zeroPost q qep tL okM KR ({} : FSMultiDFBucketState T RSt K I E)).bind
    fun ⟨kr, h1⟩ _ => ?_
  refine (lift_sampleT_zeroPost q qep tL okM KC h1).bind fun ⟨_, h2⟩ _ => ?_
  refine (rootFSMultiDFBucketPaper_zeroPost (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
    q okM prng Δbucket qep tL par 0 false lam (prng.init kr) h2).bind fun ⟨⟨_, _, _⟩, _⟩ _ => ?_
  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]; exact ZeroPost.pure trivial
private theorem initFSMultiDFBucketPaper_zeroPost {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (okM : M → Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) {q Δbucket qep : ℕ} {tL : Option ℕ} {par : Bool} (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket) :
    ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => BucketHInv q qep tL q z.2 ∧ ∀ vAB, z.1 = some vAB → BucketVPInv q qep tL vAB.1 ∧ BucketVPInv q qep tL vAB.2)
      ((initFSMultiDFBucketPaper (q + 1) cka prng fs lam Δbucket qep tL par).run ({} : FSMultiDFBucketState T RSt K I E)) := by
  unfold initFSMultiDFBucketPaper; simp only [StateT.run_bind]
  let h0 : FSMultiDFBucketState T RSt K I E := {}
  refine (lift_sampleT_zeroPost q qep tL okM KR h0).bind fun ⟨kr, h1⟩ hh1 => ?_
  refine (lift_sampleT_zeroPost q qep tL okM KC h1).bind fun ⟨kc, h2⟩ hh2 => ?_
  refine (rootFSMultiDFBucketPaper_zeroPost (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
    q okM prng Δbucket qep tL par 0 false lam (prng.init kr) h2).bind
    fun ⟨⟨σ, kVal, sid⟩, h3⟩ ⟨hs3, hc3, hsid⟩ => ?_
  dsimp only at hh1 hh2; simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  have hsess3 : h3.sessions = fun _ => [] := by rw [hs3, hh2, hh1]
  have hcache3 : h3.cache = fun _ => none := by rw [hc3, hh2, hh1]
  have hReg :
      (∀ sIdx, (regSessOptMultiDFBucket (q + 1) tL 0 sid h3).1 = some sIdx →
        SlotAt q qep tL 0 sIdx) ∧
        BucketHInv q qep tL q (regSessOptMultiDFBucket (q + 1) tL 0 sid h3).2 := by
    cases sid with
    | none =>
      refine ⟨fun _ hs => by simp [regSessOptMultiDFBucket] at hs, ⟨fun t _ => ?_, fun t c _ hc => ?_⟩⟩
      · simp [regSessOptMultiDFBucket, hsess3]
      · simp [regSessOptMultiDFBucket, hcache3] at hc
    | some ik =>
      obtain ⟨ht_hi, hbuck⟩ := hsid ik rfl; have h0s : h3.sessions 0 = [] := congrFun hsess3 0
      have hSlot0 : SlotAt q qep tL 0 (q * (0 - healEpoch tL) + 0) :=
        slotAt_of_bucket hqpos hΔb ht_hi hbuck hqpos
      dsimp only [regSessOptMultiDFBucket, regSessMultiDFBucket]
      simp only [h0s, List.not_mem_nil, ↓reduceIte, List.length_nil,
        Nat.add_sub_cancel, List.nil_append, Option.some.injEq]
      refine ⟨fun sIdx hs => hs ▸ hSlot0, ⟨fun t ht => ?_, fun t c _ hc => ?_⟩⟩
      · have ht0 : t ≠ 0 := by omega
        simp [Function.update_of_ne ht0, hsess3]
      · simp [hcache3] at hc
  refine ZeroPost.pure ⟨hReg.2, fun vAB hvAB => ?_⟩
  simp only [Option.some.injEq] at hvAB; subst hvAB
  cases hopt : (regSessOptMultiDFBucket (q + 1) tL 0 sid h3).1 with
  | none =>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro sIdx hs; simp [mkParties] at hs
    · intro t' sIdx hr; simp [mkParties] at hr
    · intro sIdx hs; simp [mkParties] at hs
    · intro t' sIdx hr; simp [mkParties] at hr
  | some sIdx =>
    have hSlot0 : SlotAt q qep tL 0 sIdx := hReg.1 sIdx hopt
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro idx' hs; simp [mkParties] at hs
    · intro t' idx' hr; simp only [mkParties] at hr; split_ifs at hr with ht'; subst ht'; simp only [Option.some.injEq, Sum.inr.injEq] at hr; exact hr ▸ hSlot0
    · intro idx' hs; simp only [mkParties, Option.some.injEq, Sum.inr.injEq] at hs; subst hs; exact ⟨hSlot0.1, fun _ => hSlot0.2⟩
    · intro t' idx' hr; simp [mkParties] at hr
private theorem startSend_zeroPost {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E) {q Δcka Δbucket qep t0 rem : ℕ} {tL : Option ℕ} {par la : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket) (ht1 : 1 ≤ t0) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (γ0 : Γ) (σ0 : RSt) (r0 : Option CCoins) (h : FSMultiDFBucketState T RSt K I E) (hH : BucketHInv q qep tL (rem + 1) h) : ZeroPost (badBQ SS RS T M E q qep tL okM)
      (fun z => BucketHInv q qep tL rem z.2 ∧ ∀ out, z.1 = some out → ∀ sIdx, out.2.2.2 = .inr sIdx → SlotAt q qep tL t0 sIdx)
      (((hooksFSMultiDFBucketPaper (q + 1) cka prng fs Δcka Δbucket qep tL par la).startSend ctx P t0 γ0 σ0 r0).run h) := by
  dsimp only [hooksFSMultiDFBucketPaper]
  have hStep : ∀ (coins : CCoins) (h1 : FSMultiDFBucketState T RSt K I E),
      BucketHInv q qep tL (rem + 1) h1 →
      ZeroPost (badBQ SS RS T M E q qep tL okM)
        (fun (z : Option (Γ × T × RSt × (SS ⊕ ℕ)) × FSMultiDFBucketState T RSt K I E) =>
          BucketHInv q qep tL rem z.2 ∧
            ∀ out, z.1 = some out → ∀ sIdx, out.2.2.2 = Sum.inr sIdx → SlotAt q qep tL t0 sIdx)
        ((do
          let cOut := cka.send γ0 coins
          let (σ', kVal, sid) ← rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
            prng Δbucket qep tL par t0 (_root_.CryptoGames.SM.Construction.postLeakDFBucket tL ctx) cOut.2.2 σ0
          let s1 ← get
          let (optIdx, s2) := regSessOptMultiDFBucket (q + 1) tL t0 sid s1
          set { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
          let ssv : SS ⊕ ℕ := match optIdx with
            | none => .inl (fs.initSender kVal)
            | some sIdx => .inr sIdx
          return some (cOut.1, cOut.2.1, σ', ssv)).run h1) := by
    intro coins h1 hH1; simp only [StateT.run_bind]
    refine (rootFSMultiDFBucketPaper_zeroPost (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
      q okM prng Δbucket qep tL par t0 _ (cka.send γ0 coins).2.2 σ0 h1).bind
      fun ⟨⟨σ', kVal, sid⟩, h2⟩ ⟨hs2, hc2, hsid⟩ => ?_
    simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
    have hH2 : BucketHInv q qep tL (rem + 1) h2 := ⟨hs2 ▸ hH1.1, hc2 ▸ hH1.2⟩
    obtain ⟨hOpt, hH3⟩ := regSessOptMultiDFBucket_step hqpos hΔb ht1 sid hsid h2 hH2
    refine ZeroPost.pure ⟨⟨hH3.1, fun t c sIdx hc hEq => ?_⟩, fun out hout sIdx hssv => ?_⟩
    · by_cases ht : t = t0
      · subst ht; simp only [Function.update_self, Option.some.injEq] at hc; subst hc; exact hOpt sIdx hEq
      · simp only [Function.update_of_ne ht] at hc; exact hH3.2 t c sIdx hc hEq
    · simp only [Option.some.injEq] at hout; subst hout
      cases hopt : (regSessOptMultiDFBucket (q + 1) tL t0 sid h2).1 with
      | none => simp [hopt] at hssv
      | some idx' => simp only [hopt, Sum.inr.injEq] at hssv; exact hssv ▸ hOpt idx' hopt
  rcases r0 with _ | c
  · simp only [StateT.run_bind]
    exact (lift_sampleT_zeroPost q qep tL okM CCoins h).bind fun ⟨coins, h1⟩ hh1 =>
      hStep coins h1 (by dsimp only at hh1; exact hh1 ▸ hH)
  · simp only [StateT.run_bind, StateT.run_pure, pure_bind]; exact hStep c h hH
private theorem startRecv_zeroPost {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E) {q Δcka Δbucket qep t0 rem : ℕ} {tL : Option ℕ} {par la : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket) (ht1 : 1 ≤ t0) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (γ0 : Γ) (σ0 : RSt) (tn0 : T) (h : FSMultiDFBucketState T RSt K I E) (hH : BucketHInv q qep tL (rem + 1) h) : ZeroPost (badBQ SS RS T M E q qep tL okM)
      (fun z => BucketHInv q qep tL rem z.2 ∧ ∀ out, z.1 = some (some out) → ∀ sIdx, out.2.2 = .inr sIdx → SlotAt q qep tL t0 sIdx)
      (((hooksFSMultiDFBucketPaper (q + 1) cka prng fs Δcka Δbucket qep tL par la).startRecv ctx P t0 γ0 σ0 tn0).run h) := by
  dsimp only [hooksFSMultiDFBucketPaper]; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hNoneBranch : ZeroPost (badBQ SS RS T M E q qep tL okM)
      (fun (z : Option (Option (Γ × RSt × (RS ⊕ ℕ))) × FSMultiDFBucketState T RSt K I E) =>
        BucketHInv q qep tL rem z.2 ∧
          ∀ out, z.1 = some (some out) → ∀ sIdx, out.2.2 = Sum.inr sIdx → SlotAt q qep tL t0 sIdx)
      ((if !(qep + 1 < t0) && inStage2BucketGen Δbucket tL par t0 then
          if tL.isSome && (t0 == healEpoch tL) then
            return (none : Option (Option (Γ × RSt × (RS ⊕ ℕ))))
          else if _root_.CryptoGames.SM.Construction.postLeakDFBucket tL ctx then
            let kk := cka.receive γ0 tn0
            let p := prng.up σ0 kk.2
            return some (some (kk.1, p.1, (Sum.inl (fs.initReceiver p.2) : RS ⊕ ℕ)))
          else do
            let kk := cka.receive γ0 tn0
            let _ ← lookupMultiDFBucketF (SS := SS) (RS := RS) (M := M) t0 kk.2
            let s1 ← get
            let (sIdx, s2) := regSessMultiDFBucket (q + 1) tL t0 kk.2 s1
            set s2
            return some (some (kk.1, (prng.up σ0 kk.2).1, (Sum.inr sIdx : RS ⊕ ℕ)))
        else return some none : HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)
          (Option (Option (Γ × RSt × (RS ⊕ ℕ))))).run h) := by
    split
    · next hcond =>
      rw [Bool.and_eq_true] at hcond
      have ht_hi : t0 ≤ qep + 1 := by
        by_cases hlt : qep + 1 < t0
        · simp [hlt] at hcond
        · omega
      have hbuck : inStage2BucketGen Δbucket tL par t0 = true := hcond.2
      split
      · simp only [StateT.run_pure]
        exact ZeroPost.pure ⟨hH.mono (Nat.le_succ rem), fun _ hout => by cases hout⟩
      · split
        · simp only [StateT.run_pure]
          refine ZeroPost.pure ⟨hH.mono (Nat.le_succ rem), fun out hout _ hrsv => ?_⟩
          simp only [Option.some.injEq] at hout; subst hout; simp at hrsv
        · simp only [StateT.run_bind]
          refine (lookupMultiDFBucketF_zeroPost q qep tL okM t0 (cka.receive γ0 tn0).2 h).bind
            fun ⟨_, h1⟩ ⟨hs1, hc1⟩ => ?_
          simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
          have hH1 : BucketHInv q qep tL (rem + 1) h1 := ⟨hs1 ▸ hH.1, hc1 ▸ hH.2⟩
          obtain ⟨hSlot, hH2⟩ :=
            regSessMultiDFBucket_step hqpos hΔb ht1 ht_hi hbuck (cka.receive γ0 tn0).2 h1 hH1
          refine ZeroPost.pure ⟨hH2, fun out hout sIdx hrsv => ?_⟩
          simp only [Option.some.injEq] at hout; subst hout; simp only [Sum.inr.injEq] at hrsv; exact hrsv ▸ hSlot
    · simp only [StateT.run_pure]
      exact ZeroPost.pure ⟨hH.mono (Nat.le_succ rem), fun _ hout => by cases hout⟩
  rcases hc : h.cache t0 with _ | ⟨tCached, σc, kVal, optIdx⟩
  · simpa only [hc] using hNoneBranch
  · by_cases ht : tCached = tn0
    · subst ht; simp only [↓reduceIte, StateT.run_pure]
      refine ZeroPost.pure ⟨hH.mono (Nat.le_succ rem), fun out hout sIdx hrsv => ?_⟩
      simp only [Option.some.injEq] at hout; subst hout; rcases optIdx with _ | idx'
      · simp at hrsv
      · simp only [Sum.inr.injEq] at hrsv; exact hrsv ▸ hH.2 t0 (tCached, σc, kVal, some idx') idx' hc rfl
    · simpa only [hc, ht, ↓reduceIte] using hNoneBranch
private def pairOk {M : Type} (okM : M → Bool) (m : M) : Option (M × M) → Prop
  | none => okM m = true
  | some (m₀, m₁) => okM m₀ = true ∧ okM m₁ = true
private theorem fsSendTailBucket_zeroPost {SS RS T M E Sig K I : Type} (q qep : ℕ) (tL : Option ℕ) (okM : M → Bool) {sIdx : ℕ}
    (hsIdx_cap : ¬ ((qep + 2) - healEpoch tL) * q ≤ sIdx) (hdr : Header T) (hhdr_eq : hdr.1 = healEpoch tL + sIdx / q)
    (m : M) (pair : Option (M × M)) (hm : pairOk okM m pair) (h0 h : FSMultiDFBucketState T Sig K I E) (hse : h.sessions = h0.sessions) (hca : h.cache = h0.cache) :
    ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => z.2.sessions = h0.sessions ∧ z.2.cache = h0.cache ∧
        ∀ v' e, z.1 = some (v', e) → ∀ sIdx', v' = .inr sIdx' → (.inr sIdx : SS ⊕ ℕ) = .inr sIdx')
      ((do
        let e? ← match pair with
          | some (m₀, m₁) =>
            liftFSMultiDFBucket sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
          | none =>
            liftFSMultiDFBucket sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
        match e? with
        | none => return (none : Option ((SS ⊕ ℕ) × E))
        | some e =>
          modify fun (st : FSMultiDFBucketState T Sig K I E) =>
            let b := (st.book sIdx).getD {}
            let cnt' := b.fsCount + 1
            let b' : FSMultiBook T E :=
              { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
            { st with book := Function.update st.book sIdx (some b') }
          return some (.inr sIdx, e)).run h) := by
  rcases pair with _ | ⟨m₀, m₁⟩
  · simp only [StateT.run_bind]; refine (liftFSMultiDFBucket_query_zeroPost q qep tL okM sIdx _
      (by simp [badBQ, badBucketQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hhdr_eq]; exact hm) h).bind
      fun ⟨e?, h2⟩ hh2 => ?_
    dsimp only at hh2; rcases e? with _ | e
    · simp only [StateT.run_pure]
      exact ZeroPost.pure ⟨by rw [hh2]; exact hse, by rw [hh2]; exact hca, fun _ _ hs => by cases hs⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact ZeroPost.pure ⟨by rw [hh2]; exact hse, by rw [hh2]; exact hca, fun _ _ hs _ hv => by
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; rcases hs with ⟨rfl, _⟩; exact hv⟩
  · simp only [StateT.run_bind]; refine (liftFSMultiDFBucket_query_zeroPost q qep tL okM sIdx _
      (by simp [badBQ, badBucketQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hm.1, hm.2, hhdr_eq]) h).bind
      fun ⟨e?, h2⟩ hh2 => ?_
    dsimp only at hh2; rcases e? with _ | e
    · simp only [StateT.run_pure]
      exact ZeroPost.pure ⟨by rw [hh2]; exact hse, by rw [hh2]; exact hca, fun _ _ hs => by cases hs⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact ZeroPost.pure ⟨by rw [hh2]; exact hse, by rw [hh2]; exact hca, fun _ _ hs _ hv => by
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; rcases hs with ⟨rfl, _⟩; exact hv⟩
private theorem fsSend_zeroPost {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] (L q : ℕ) (okM : M → Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t' : ℕ)
    (ssv : SS ⊕ ℕ) (hdr : Header T) (m : M) (pair : Option (M × M)) (h : FSMultiDFBucketState T RSt K I E) (hssv : ∀ sIdx, ssv = .inr sIdx → SlotAt q qep tL hdr.1 sIdx)
    (hm : pairOk okM m pair) : ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
        ∀ v' e, z.1 = some (v', e) → ∀ sIdx, v' = .inr sIdx → ssv = .inr sIdx) (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).fsSend
        ctx P t' ssv hdr m pair).run h) := by
  dsimp only [hooksFSMultiDFBucketPaper]; cases ssv with
  | inl ss =>
    simp only [StateT.run_pure]; exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs _ hv => by
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; rcases hs with ⟨rfl, _⟩; simp at hv⟩
  | inr sIdx =>
    rcases hssv sIdx rfl with ⟨hsIdx_lt, hhdr_eq0⟩
    have hsIdx_cap : ¬ ((qep + 2) - healEpoch tL) * q ≤ sIdx := Nat.not_le_of_gt hsIdx_lt
    have hhdr_eq : hdr.1 = healEpoch tL + sIdx / q := hhdr_eq0.symm
    simp only [StateT.run_bind, StateT.run_get, pure_bind]; split
    · simp only [StateT.run_bind]; refine (liftFSMultiDFBucket_query_zeroPost q qep tL okM sIdx _
        (by simp [badBQ, badBucketQuery, hsIdx_cap, encBadMsg, queryADOutsideClass]) h).bind
        fun ⟨o, h1⟩ hh1 => ?_
      dsimp only at hh1; rcases o with _ | _
      · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
        exact ZeroPost.pure ⟨by rw [hh1], by rw [hh1], fun _ _ hs => by cases hs⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact fsSendTailBucket_zeroPost q qep tL okM hsIdx_cap hdr hhdr_eq m pair hm h _
          (by rw [hh1]) (by rw [hh1])
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact fsSendTailBucket_zeroPost q qep tL okM hsIdx_cap hdr hhdr_eq m pair hm h h rfl rfl
private theorem fsRecvTailBucket_zeroPost {SS RS T M E Sig K I : Type} [DecidableEq T] [DecidableEq E] (q qep : ℕ) (tL : Option ℕ) (okM : M → Bool) {sIdx : ℕ}
    (hsIdx_cap : ¬ ((qep + 2) - healEpoch tL) * q ≤ sIdx) (la : Bool) (matched : Option (ℕ × Header T × E)) (hdr : Header T) (hhdr_eq : hdr.1 = healEpoch tL + sIdx / q)
    (e : E) (rec : Option (Record M (Header T × E))) (h0 h : FSMultiDFBucketState T Sig K I E) (hse : h.sessions = h0.sessions) (hca : h.cache = h0.cache) :
    ZeroPost (badBQ SS RS T M E q qep tL okM) (fun (z : Option (Option ((RS ⊕ ℕ) × ℕ × M)) × FSMultiDFBucketState T Sig K I E) =>
        z.2.sessions = h0.sessions ∧ z.2.cache = h0.cache ∧ ∀ v' i m, z.1 = some (some (v', i, m)) → ∀ sIdx', v' = .inr sIdx' → (.inr sIdx : RS ⊕ ℕ) = .inr sIdx')
      ((do
        let res ← if matched.isSome then
            liftFSMultiDFBucket sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
          else
            liftFSMultiDFBucket sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
        match res with
        | none => return (none : Option (Option ((RS ⊕ ℕ) × ℕ × M)))
        | some .rejected => return some none
        | some (.accepted i mo') =>
          let s1 ← get
          let bk1 := (s1.book sIdx).getD {}
          if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
            modify fun (st : FSMultiDFBucketState T Sig K I E) => { st with lfWin := true }
            return none
          else
            let drop := (matched.map (fun (x : ℕ × Header T × E) => x.1)).getD i
            modify fun (st : FSMultiDFBucketState T Sig K I E) =>
              let b := (st.book sIdx).getD {}
              let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
              { st with book := Function.update st.book sIdx (some b') }
            match mo', rec with
            | some m, _ => return some (some (.inr sIdx, i, m))
            | none, some r => return some (some (.inr sIdx, i, r.msg))
            | none, none => return none).run h) := by
  split_ifs <;> simp only [StateT.run_bind] <;>
    (refine (liftFSMultiDFBucket_query_zeroPost (SS := SS) (RS := RS) q qep tL okM sIdx _
        (by simp [badBQ, badBucketQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hhdr_eq]) h).bind
        fun ⟨res, h2⟩ hh2 => ?_;
     dsimp only at hh2;
     have hse2 : h2.sessions = h0.sessions := by rw [hh2]; exact hse
     have hca2 : h2.cache = h0.cache := by rw [hh2]; exact hca
     rcases res with _ | (_ | ⟨i, mo'⟩);
     · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨hse2, hca2, fun _ _ _ hs => by cases hs⟩
     · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨hse2, hca2, fun _ _ _ hs => by cases hs⟩
     · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
       · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
         exact ZeroPost.pure ⟨hse2, hca2, fun _ _ _ hs => by cases hs⟩
       · simp only [StateT.run_bind, StateT.run_modify, pure_bind]; rcases mo' with _ | m
         · rcases rec with _ | rec0
           · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨hse2, hca2, fun _ _ _ hs => by cases hs⟩
           · simp only [StateT.run_pure]
             exact ZeroPost.pure ⟨hse2, hca2, fun _ _ _ hs _ hv => by
               simp only [Option.some.injEq, Prod.mk.injEq] at hs; rcases hs with ⟨rfl, _, _⟩; exact hv⟩
         · simp only [StateT.run_pure]
           exact ZeroPost.pure ⟨hse2, hca2, fun _ _ _ hs _ hv => by
             simp only [Option.some.injEq, Prod.mk.injEq] at hs; rcases hs with ⟨rfl, _, _⟩; exact hv⟩)
private theorem fsRecv_zeroPost {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] (L q : ℕ) (okM : M → Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t' : ℕ)
    (rsv : RS ⊕ ℕ) (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E)))
    (h : FSMultiDFBucketState T RSt K I E) (hrsv : ∀ sIdx, rsv = .inr sIdx → SlotAt q qep tL hdr.1 sIdx) :
    ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
        ∀ v' i m, z.1 = some (some (v', i, m)) → ∀ sIdx, v' = .inr sIdx → rsv = .inr sIdx) (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).fsRecv
        ctx P t' rsv hdr e rec).run h) := by
  dsimp only [hooksFSMultiDFBucketPaper]; cases rsv with
  | inl rs =>
    simp only [StateT.run_pure]; exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
      cases hfr : fs.receive rs hdr e with
      | none => simp [hfr] at hs
      | some o =>
        simp only [hfr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, _, _⟩; simp at hv⟩
  | inr sIdx =>
    rcases hrsv sIdx rfl with ⟨hsIdx_lt, hhdr_eq0⟩
    have hsIdx_cap : ¬ ((qep + 2) - healEpoch tL) * q ≤ sIdx := Nat.not_le_of_gt hsIdx_lt
    have hhdr_eq : hdr.1 = healEpoch tL + sIdx / q := hhdr_eq0.symm
    simp only [StateT.run_bind, StateT.run_get, pure_bind]; split
    · simp only [StateT.run_bind]; refine (liftFSMultiDFBucket_query_zeroPost q qep tL okM sIdx _
        (by simp [badBQ, badBucketQuery, hsIdx_cap, encBadMsg, queryADOutsideClass]) h).bind
        fun ⟨o, h1⟩ hh1 => ?_
      dsimp only at hh1; rcases o with _ | _
      · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
        exact ZeroPost.pure ⟨by rw [hh1], by rw [hh1], fun _ _ _ hs => by cases hs⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact fsRecvTailBucket_zeroPost (SS := SS) (RS := RS) q qep tL okM hsIdx_cap la _ hdr hhdr_eq e rec
          h _ (by rw [hh1]) (by rw [hh1])
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact fsRecvTailBucket_zeroPost (SS := SS) (RS := RS) q qep tL okM hsIdx_cap la _ hdr hhdr_eq e rec
        h h rfl rfl
private theorem reveal_zeroPost {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] (L q : ℕ) (okM : M → Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (h : FSMultiDFBucketState T RSt K I E) (hvp : BucketVPInv q qep tL vp) : ZeroPost (badBQ SS RS T M E q qep tL okM)
      (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache) (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).reveal ctx P vp).run h) := by
  dsimp only [hooksFSMultiDFBucketPaper]; rcases hvs_eq : vp.vS with _ | (ss | sIdx)
  · split_ifs <;> exact ZeroPost.pure ⟨rfl, rfl⟩
  · split_ifs <;> exact ZeroPost.pure ⟨rfl, rfl⟩
  · have hsIdx_lt : sIdx < ((qep + 2) - healEpoch tL) * q := (hvp.1 sIdx hvs_eq).1
    have hsIdx_cap : ¬ ((qep + 2) - healEpoch tL) * q ≤ sIdx := Nat.not_le_of_gt hsIdx_lt
    simp only [StateT.run_bind]; refine (liftFSMultiDFBucket_query_zeroPost q qep tL okM sIdx _
      (by simp [badBQ, badBucketQuery, hsIdx_cap, encBadMsg, queryADOutsideClass]) h).bind
      fun ⟨o, h1⟩ hh1 => ?_
    dsimp only at hh1; rcases o with _ | ss
    · simp only [StateT.run_pure, pure_bind]; exact ZeroPost.pure ⟨by rw [hh1], by rw [hh1]⟩
    · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
      split_ifs <;> simp only [StateT.run_pure] <;> exact ZeroPost.pure ⟨by rw [hh1], by rw [hh1]⟩
private theorem startRecvMode_zeroPost {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {q Δcka Δbucket qep t0 rem : ℕ} {gMain : Bool} {tL : Option ℕ} {par la : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket) (ht1 : 1 ≤ t0) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (γ0 : Γ) (σ0 : RSt) (tn0 : T) (h : FSMultiDFBucketState T RSt K I E) (hH : BucketHInv q qep tL (rem + 1) h) : ZeroPost (badBQ SS RS T M E q qep tL okM)
      (fun z => BucketHInv q qep tL rem z.2 ∧ ∀ out, z.1 = some (some out) → ∀ sIdx, out.2.2 = .inr sIdx → SlotAt q qep tL t0 sIdx)
      (((hooksFSMultiDFBucketPaperMode (q + 1) cka prng fs Δcka Δbucket qep gMain tL par la).startRecv ctx P t0 γ0 σ0 tn0).run h) := by
  dsimp only [hooksFSMultiDFBucketPaperMode]; cases gMain
  · exact startRecv_zeroPost okM cka prng fs hqpos hΔb ht1 ctx P γ0 σ0 tn0 h hH
  · simp only [↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]; rcases hc : h.cache t0 with _ | ⟨tCached, σc, kVal, optIdx⟩
    · dsimp only; split_ifs <;> simp only [StateT.run_pure] <;>
        exact ZeroPost.pure ⟨hH.mono (Nat.le_succ rem), fun _ hout => by cases hout⟩
    · dsimp only; by_cases ht : tCached = tn0
      · subst ht; simp only [↓reduceIte, StateT.run_pure]
        refine ZeroPost.pure ⟨hH.mono (Nat.le_succ rem), fun out hout sIdx hrsv => ?_⟩
        simp only [Option.some.injEq] at hout; subst hout; rcases optIdx with _ | idx'
        · simp at hrsv
        · simp only [Sum.inr.injEq] at hrsv; exact hrsv ▸ hH.2 t0 (tCached, σc, kVal, some idx') idx' hc rfl
      · simp only [ht, ↓reduceIte]; split_ifs <;> simp only [StateT.run_pure] <;>
          exact ZeroPost.pure ⟨hH.mono (Nat.le_succ rem), fun _ hout => by cases hout⟩
private theorem revealMode_zeroPost {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] (L q : ℕ) (okM : M → Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (h : FSMultiDFBucketState T RSt K I E) (hvp : BucketVPInv q qep tL vp) : ZeroPost (badBQ SS RS T M E q qep tL okM)
      (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache) (((hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la).reveal ctx P vp).run h) := by
  dsimp only [hooksFSMultiDFBucketPaperMode]; cases gMain
  · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs
    · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨rfl, rfl⟩
    · exact reveal_zeroPost L q okM cka prng fs Δcka Δbucket qep tL par la ctx P vp h hvp
  · exact reveal_zeroPost L q okM cka prng fs Δcka Δbucket qep tL par la ctx P vp h hvp
private structure BucketZeroHooks {Γ T RSt SS RS M E CCoins K I : Type} (q qep : ℕ) (tL : Option ℕ) (okM : M → Bool)
    (hk : Hooks (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) : Prop where
  startSend_zp : ∀ {t0 rem : ℕ}, 1 ≤ t0 → ∀ ctx P γ0 σ0 r0 h, BucketHInv q qep tL (rem + 1) h →
    ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => BucketHInv q qep tL rem z.2 ∧
      ∀ out, z.1 = some out → ∀ sIdx, out.2.2.2 = .inr sIdx → SlotAt q qep tL t0 sIdx)
      ((hk.startSend ctx P t0 γ0 σ0 r0).run h)
  startRecv_zp : ∀ {t0 rem : ℕ}, 1 ≤ t0 → ∀ ctx P γ0 σ0 tn0 h, BucketHInv q qep tL (rem + 1) h →
    ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => BucketHInv q qep tL rem z.2 ∧
      ∀ out, z.1 = some (some out) → ∀ sIdx, out.2.2 = .inr sIdx → SlotAt q qep tL t0 sIdx)
      ((hk.startRecv ctx P t0 γ0 σ0 tn0).run h)
  fsSend_zp : ∀ ctx P t' ssv hdr m pair h, (∀ sIdx, ssv = .inr sIdx → SlotAt q qep tL hdr.1 sIdx) →
    pairOk okM m pair → ZeroPost (badBQ SS RS T M E q qep tL okM)
      (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
        ∀ v' e, z.1 = some (v', e) → ∀ sIdx, v' = .inr sIdx → ssv = .inr sIdx)
      ((hk.fsSend ctx P t' ssv hdr m pair).run h)
  fsRecv_zp : ∀ ctx P t' rsv hdr e rec h, (∀ sIdx, rsv = .inr sIdx → SlotAt q qep tL hdr.1 sIdx) →
    ZeroPost (badBQ SS RS T M E q qep tL okM)
      (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
        ∀ v' i m, z.1 = some (some (v', i, m)) → ∀ sIdx, v' = .inr sIdx → rsv = .inr sIdx)
      ((hk.fsRecv ctx P t' rsv hdr e rec).run h)
  reveal_zp : ∀ ctx P vp h, BucketVPInv q qep tL vp →
    ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache)
      ((hk.reveal ctx P vp).run h)
  commit_zp : ∀ ctx P old new h, ZeroPost (badBQ SS RS T M E q qep tL okM)
    (fun z => z.1 = some new ∧ z.2 = h) ((hk.commit ctx P old new).run h)
private theorem paper_zeroHooks {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {q Δcka Δbucket qep : ℕ} {tL : Option ℕ} {par la : Bool} (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket) :
    BucketZeroHooks q qep tL okM (hooksFSMultiDFBucketPaper (q + 1) cka prng fs Δcka Δbucket qep tL par la) where
  startSend_zp ht1 ctx P γ0 σ0 r0 h hH :=
    startSend_zeroPost (Δcka := Δcka) (la := la) okM cka prng fs hqpos hΔb ht1 ctx P γ0 σ0 r0 h hH
  startRecv_zp ht1 ctx P γ0 σ0 tn0 h hH := startRecv_zeroPost okM cka prng fs hqpos hΔb ht1 ctx P γ0 σ0 tn0 h hH
  fsSend_zp := fsSend_zeroPost (q + 1) q okM cka prng fs Δcka Δbucket qep tL par la
  fsRecv_zp := fsRecv_zeroPost (q + 1) q okM cka prng fs Δcka Δbucket qep tL par la
  reveal_zp := reveal_zeroPost (q + 1) q okM cka prng fs Δcka Δbucket qep tL par la
  commit_zp _ _ _ _ _ := by dsimp only [hooksFSMultiDFBucketPaper]; simp only [StateT.run_pure]; exact ZeroPost.pure ⟨rfl, rfl⟩
private theorem paperMode_zeroHooks {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {q Δcka Δbucket qep : ℕ} {gMain : Bool} {tL : Option ℕ} {par la : Bool} (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket) :
    BucketZeroHooks q qep tL okM (hooksFSMultiDFBucketPaperMode (q + 1) cka prng fs Δcka Δbucket qep gMain tL par la) where
  startSend_zp ht1 ctx P γ0 σ0 r0 h hH :=
    startSend_zeroPost (Δcka := Δcka) (la := la) okM cka prng fs hqpos hΔb ht1 ctx P γ0 σ0 r0 h hH
  startRecv_zp ht1 ctx P γ0 σ0 tn0 h hH := startRecvMode_zeroPost okM cka prng fs hqpos hΔb ht1 ctx P γ0 σ0 tn0 h hH
  fsSend_zp := fsSend_zeroPost (q + 1) q okM cka prng fs Δcka Δbucket qep tL par la
  fsRecv_zp := fsRecv_zeroPost (q + 1) q okM cka prng fs Δcka Δbucket qep tL par la
  reveal_zp := revealMode_zeroPost (q + 1) q okM cka prng fs Δcka Δbucket qep gMain tL par la
  commit_zp _ _ _ _ _ := by dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]; simp only [StateT.run_pure]; exact ZeroPost.pure ⟨rfl, rfl⟩
private theorem vSend_zeroPost {Γ CCoins T I RSt K SS RS M E : Type} [Inhabited E] {q qep rem : ℕ} {tL : Option ℕ} {okM : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ)}
    (hzh : BucketZeroHooks q qep tL okM hk) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (m : M) (pair : Option (M × M)) (r : Option CCoins) (h : FSMultiDFBucketState T RSt K I E) (hs : BucketVPInv q qep tL s)
    (hH : BucketHInv q qep tL (rem + 1) h) (hm : pairOk okM m pair) : ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => BucketHInv q qep tL rem z.2 ∧
        ∀ sc, z.1 = some sc → BucketVPInv q qep tL sc.1) ((vSend hk ctx P s m pair r).run h) := by
  unfold vSend; dsimp only; split_ifs with hnsend0
  · simp only [StateT.run_bind, pure_bind]
    refine (hzh.startSend_zp (Nat.succ_pos _) ctx P s.γ s.root r h hH).bind fun ⟨o, h1⟩ ⟨hH1, hss⟩ => ?_
    rcases o with _ | ⟨γ', T', σ', ss⟩
    · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨hH1, fun _ hc => by cases hc⟩
    · simp only [StateT.run_bind]
      refine (hzh.fsSend_zp ctx P (s.tcur + 1) ss (s.tcur + 1, some T') m pair h1
        (fun sIdx hv_eq => hss (γ', T', σ', ss) rfl sIdx hv_eq) hm).bind
        fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
      have hH2 : BucketHInv q qep tL rem h2 := ⟨hse2 ▸ hH1.1, hca2 ▸ hH1.2⟩
      rcases res with _ | ⟨v', e⟩
      · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨hH2, fun _ hc => by cases hc⟩
      · simp only [StateT.run_pure]; refine ZeroPost.pure ⟨hH2, fun sc hc => ?_⟩; simp only [Option.some.injEq] at hc; subst hc; refine ⟨fun sIdx hv' => ?_, hs.2⟩
        simp only [Option.some.injEq] at hv'
        have hSlot := hss (γ', T', σ', ss) rfl sIdx (hv_eq v' e rfl sIdx hv')
        exact ⟨hSlot.1, fun _ => hSlot.2⟩
  · simp only [pure_bind]
    have hnsend : s.id.sendsIn (s.tcur + 1) = false := Bool.eq_false_iff.mpr hnsend0
    have hH0 : BucketHInv q qep tL rem h := hH.mono (Nat.le_succ rem)
    rcases hv : s.vS with _ | v
    · exact ZeroPost.pure ⟨hH0, fun sc hc => by simp only [Option.some.injEq] at hc; subst hc; exact hs⟩
    · simp only [StateT.run_bind]
      refine (hzh.fsSend_zp ctx P s.tcur v (s.tcur, s.curCkaMsg) m pair h
        (fun sIdx hv_eq => ⟨(hs.1 sIdx (hv ▸ hv_eq ▸ rfl)).1, (hs.1 sIdx (hv ▸ hv_eq ▸ rfl)).2 hnsend⟩) hm).bind
        fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
      have hH2 : BucketHInv q qep tL rem h2 := ⟨hse2 ▸ hH0.1, hca2 ▸ hH0.2⟩
      rcases res with _ | ⟨v', e⟩
      · exact ZeroPost.pure ⟨hH2, fun _ hc => by cases hc⟩
      · refine ZeroPost.pure ⟨hH2, fun sc hc => ?_⟩
        simp only [Option.some.injEq] at hc; subst hc; refine ⟨fun sIdx hv' => ?_, hs.2⟩
        simp only [Option.some.injEq] at hv'; exact hs.1 sIdx (hv ▸ (hv_eq v' e rfl sIdx hv') ▸ rfl)
private theorem vRecv_zeroPost {Γ CCoins T I RSt K SS RS M E : Type} [DecidableEq T] {q qep rem : ℕ} {tL : Option ℕ} {okM : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ)}
    (hzh : BucketZeroHooks q qep tL okM hk) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (h : FSMultiDFBucketState T RSt K I E) (hs : BucketVPInv q qep tL s) (hH : BucketHInv q qep tL (rem + 1) h) :
    ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => BucketHInv q qep tL rem z.2 ∧ ∀ stim, z.1 = some (some stim) → BucketVPInv q qep tL stim.1)
      ((vRecv hk ctx P s c rec).run h) := by
  unfold vRecv; dsimp only; split
  · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨hH.mono (Nat.le_succ rem), fun _ hc => by cases hc⟩
  · next hguard =>
    have hsends_false : s.id.sendsIn c.1.1 = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard; exact hguard.1
    split
    · next hEqEp =>
      have ht1 : 1 ≤ c.1.1 := by omega
      cases c.1.2 with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact ZeroPost.pure ⟨hH.mono (Nat.le_succ rem), fun _ hc => by cases hc⟩
      | some Tn =>
        simp only [StateT.run_bind, pure_bind]
        refine (hzh.startRecv_zp ht1 ctx P s.γ s.root Tn h hH).bind fun ⟨o, h1⟩ ⟨hH1, hrs⟩ => ?_
        rcases o with _ | (_ | ⟨γ', σ', rs⟩)
        · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨hH1, fun _ hc => by cases hc⟩
        · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨hH1, fun _ hc => by cases hc⟩
        · simp only [Function.update_self]
          refine (hzh.fsRecv_zp ctx P c.1.1 rs c.1 c.2 rec h1 (hrs (γ', σ', rs) rfl)).bind
            fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
          have hH2 : BucketHInv q qep tL rem h2 := ⟨hse2 ▸ hH1.1, hca2 ▸ hH1.2⟩
          rcases res with _ | (_ | ⟨v', i, m⟩)
          · exact ZeroPost.pure ⟨hH2, fun _ hc => by cases hc⟩
          · exact ZeroPost.pure ⟨hH2, fun _ hc => by cases hc⟩
          · refine ZeroPost.pure ⟨hH2, fun stim hc => ?_⟩
            simp only [Option.some.injEq] at hc; subst hc
            refine ⟨fun sIdx hv => ⟨(hs.1 sIdx hv).1, fun hns => by
              rw [sendsIn_succ_of_false s.id c.1.1 hsends_false] at hns; exact Bool.noConfusion hns⟩,
              fun t'' sIdx hr => ?_⟩
            by_cases ht'' : t'' = c.1.1
            · subst ht''; simp only [Function.update_self, Option.some.injEq] at hr; exact hrs (γ', σ', rs) rfl sIdx (hv_eq v' i m rfl sIdx hr)
            · simp only [Function.update_of_ne ht''] at hr; exact hs.2 t'' sIdx hr
    · simp only [pure_bind]; have hH0 : BucketHInv q qep tL rem h := hH.mono (Nat.le_succ rem); rcases hv : s.vR c.1.1 with _ | v
      · exact ZeroPost.pure ⟨hH0, fun _ hc => by cases hc⟩
      · simp only [StateT.run_bind]
        refine (hzh.fsRecv_zp ctx P c.1.1 v c.1 c.2 rec h (fun sIdx hv_eq => hs.2 c.1.1 sIdx (hv ▸ hv_eq ▸ rfl))).bind
          fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
        have hH2 : BucketHInv q qep tL rem h2 := ⟨hse2 ▸ hH0.1, hca2 ▸ hH0.2⟩
        rcases res with _ | (_ | ⟨v', i, m⟩)
        · exact ZeroPost.pure ⟨hH2, fun _ hc => by cases hc⟩
        · exact ZeroPost.pure ⟨hH2, fun _ hc => by cases hc⟩
        · refine ZeroPost.pure ⟨hH2, fun stim hc => ?_⟩
          simp only [Option.some.injEq] at hc; subst hc; refine ⟨hs.1, fun t'' sIdx hr => ?_⟩; by_cases ht'' : t'' = c.1.1
          · subst ht''; simp only [Function.update_self, Option.some.injEq] at hr; exact hs.2 c.1.1 sIdx (hv ▸ (hv_eq v' i m rfl sIdx hr) ▸ rfl)
          · simp only [Function.update_of_ne ht''] at hr; exact hs.2 t'' sIdx hr
private theorem commitE_zeroPost {Γ CCoins T I RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq M] {q qep rem : ℕ} {tL : Option ℕ} {okM : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ)}
    (hzh : BucketZeroHooks q qep tL okM hk) (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (Pt : Party) (old new : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : Pos)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiDFBucketState T RSt K I E))
    (hs : ∀ Q, BucketVPInv q qep tL (s.st Q)) (hnew : BucketVPInv q qep tL new) (hes : BucketESInv q qep tL rem es) : ZeroPost (badBQ SS RS T M E q qep tL okM)
      (fun z => BucketESInv q qep tL rem z.2 ∧ ∀ s1, z.1 = some s1 → ∀ Q, BucketVPInv q qep tL (s1.st Q)) ((commitE hk s Pt old new pos).run es) := by
  unfold commitE; rw [StateT.run_bind]
  refine (liftH_zeroPost (hzh.commit_zp (s.accept Pt new pos) Pt old new es.h)).bind
    fun ⟨o, es1⟩ ⟨⟨ho, hh1⟩, hg1, _⟩ => ?_
  dsimp only at ho hh1; subst ho; simp only [StateT.run_pure]
  refine ZeroPost.pure ⟨⟨fun Q => hg1 ▸ hes.1 Q, hh1 ▸ hes.2⟩, fun s1 hs1 Q => ?_⟩
  simp only [Option.some.injEq] at hs1; subst hs1; exact bucketVPInv_update (bucketVPInv_update hs Pt hnew) Pt hnew Q
private theorem coinsE_zeroPost {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀} {Γv T Sv SSv RSv M E HS : Type}
    {P : (unifSpec + tspec).Domain → Bool} {Q : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS → Prop} (hInl : ∀ u, P (.inl u) = false) (u : unifSpec.Domain)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (hes : Q es) : ZeroPost P (fun z => Q z.2) ((coinsE u).run es) := by
  unfold coinsE; rw [StateT.run_lift]; exact (ZeroPost.query_false (spec := unifSpec + tspec) (Sum.inl u) (hInl u)).bind fun _ _ => ZeroPost.pure hes
private theorem withWinEpDF_zeroPost {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀} {St Msg Coins C S' : Type} {P : (unifSpec + tspec).Domain → Bool} {Q : S' → Prop}
    (ctEpoch : C → ℕ) (hasWin : S' → Bool) (impl : QueryImpl (unifSpec + specDF St Msg Coins C) (StateT S' (TComp tspec)))
    (t : (unifSpec + specDF St Msg Coins C).Domain) (st : S' × Option ℕ) (h : ZeroPost P (fun z => Q z.2) ((impl t).run st.1)) :
    ZeroPost P (fun z => Q z.2.1) ((withWinEpDF ctEpoch hasWin impl t).run st) := by
  unfold withWinEpDF; dsimp only [StateT.run_mk]; exact h.bind fun ⟨_, _⟩ hs' => ZeroPost.pure hs'
private theorem withWinEpDFMode_zeroPost {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀} {St Msg Coins T' E' VPt HS : Type} {P : (unifSpec + tspec).Domain → Bool}
    {Q : EState VPt Msg (Header T' × E') HS → Prop} (gMain : Bool) (isHonest : HS → Header T' → Bool) (epOf : VPt → ℕ)
    (impl : QueryImpl (unifSpec + specDF St Msg Coins (Header T' × E')) (StateT (EState VPt Msg (Header T' × E') HS) (TComp tspec)))
    (t : (unifSpec + specDF St Msg Coins (Header T' × E')).Domain) (st : EState VPt Msg (Header T' × E') HS × Option ℕ) (h : ZeroPost P (fun z => Q z.2) ((impl t).run st.1)) :
    ZeroPost P (fun z => Q z.2.1) ((withWinEpDFMode gMain isHonest epOf impl t).run st) := by
  unfold withWinEpDFMode; split
  · exact withWinEpDF_zeroPost _ _ impl t st h
  · dsimp only [StateT.run_mk]; exact h.bind fun ⟨_, _⟩ hs' => ZeroPost.pure hs'
private theorem implEDFPaperBucketRaw_inr_zeroPost {Γ CCoins T I RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {okB okM : M → Bool} (hok : ∀ m, okB m = true → okM m = true) {q qep rem : ℕ} {tL : Option ℕ}
    {hk : Hooks (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ)}
    (hzh : BucketZeroHooks q qep tL okM hk) (Δ maxSkip : ℕ) (cfg : Config M) (qr : (specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiDFBucketState T RSt K I E))
    (hnb : badSendMsgDF (St := PartyState Γ T RSt SS RS) (Coins := CCoins) (C := Header T × E) okB (.inr qr) = false)
    (hes : BucketESInv q qep tL (rem + 1) es) :
    ZeroPost (badBQ SS RS T M E q qep tL okM) (fun z => BucketESInv q qep tL rem z.2)
      ((implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr qr)).run es) := by
  rcases qr with ((((q1 | q2) | q3) | q4) | q5) | q6
  · rcases q1 with ⟨Pt, m, r⟩
    have hm : okM m = true := hok m (by simpa [badSendMsgDF] using hnb)
    change ZeroPost _ _ ((transmitEBucket _ Δ qep (Pt, m, r)).run es); unfold transmitEBucket; simp only [StateT.run_bind, StateT.run_get, pure_bind]; split
    · simp only [StateT.run_pure]; exact ZeroPost.pure (hes.mono (Nat.le_succ rem))
    · cases hep : es.g.epMgmt Δ qep Pt r.isSome with
      | none => simp only [StateT.run_pure]; exact ZeroPost.pure (hes.mono (Nat.le_succ rem))
      | some s1 =>
        have hst1 : s1.st = es.g.st := epMgmt_st_eq hep
        dsimp only; rw [StateT.run_bind]
        refine (liftH_zeroPost (vSend_zeroPost hzh s1 Pt (s1.st Pt) m none r es.h (hst1 ▸ hes.1 Pt) hes.2 hm)).bind
          fun ⟨o, es1⟩ ⟨⟨hH1, ho⟩, hg1, _⟩ => ?_
        cases o with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
        | some p =>
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroPost.pure ⟨bucketVPInv_update (fun Q => hst1 ▸ hes.1 Q) Pt (ho p rfl), hH1⟩
  · change ZeroPost _ _ ((challEBucket q2).run es); unfold challEBucket; simp only [StateT.run_pure]; exact ZeroPost.pure (hes.mono (Nat.le_succ rem))
  · rcases q3 with ⟨Pt, c⟩
    change ZeroPost _ _ ((deliverE _ maxSkip cfg (Pt, c)).run es); unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]; split
    · simp only [StateT.run_pure]; exact ZeroPost.pure (hes.mono (Nat.le_succ rem))
    · cases es.g.inTransit Pt.other c with
      | none => simp only [StateT.run_pure]; exact ZeroPost.pure (hes.mono (Nat.le_succ rem))
      | some r =>
        dsimp only; rw [StateT.run_bind]
        refine (liftH_zeroPost (vRecv_zeroPost hzh es.g Pt (es.g.st Pt) c (some r) es.h (hes.1 Pt) hes.2)).bind
          fun ⟨o, es1⟩ ⟨⟨hH1, ho⟩, hg1, _⟩ => ?_
        rcases o with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
        · dsimp only; split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
            exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
        · dsimp only; rw [StateT.run_bind]
          refine (commitE_zeroPost hzh es.g Pt (es.g.st Pt) st' r.pos es1 hes.1 (ho (st', t', i', m') rfl)
            ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩).bind fun ⟨s1?, es2⟩ ⟨hes2, hs1?⟩ => ?_
          cases s1? with
          | none => simp only [StateT.run_pure]; exact ZeroPost.pure hes2
          | some s1 =>
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            refine ZeroPost.pure ⟨fun Q => ?_, hes2.2⟩; dsimp only; split <;> exact hs1? s1 rfl Q
  · rcases q4 with ⟨Pt, c⟩
    change ZeroPost _ _ ((injectE _ Δ qep cfg (Pt, c)).run es); unfold injectE; simp only [StateT.run_bind, StateT.run_get, pure_bind]; split
    · simp only [StateT.run_pure]; exact ZeroPost.pure (hes.mono (Nat.le_succ rem))
    · rw [StateT.run_bind]; refine (liftH_zeroPost (vRecv_zeroPost hzh es.g Pt (es.g.st Pt) c none es.h (hes.1 Pt) hes.2)).bind
        fun ⟨o, es1⟩ ⟨⟨hH1, ho⟩, hg1, _⟩ => ?_
      rcases o with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
      · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
      · dsimp only; split
        · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
        · split
          · rw [StateT.run_bind]
            refine (commitE_zeroPost hzh es.g Pt (es.g.st Pt) st' ⟨Pt.other, t', i'⟩ es1 hes.1
              (ho (st', t', i', m') rfl) ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩).bind fun ⟨s1?, es2⟩ ⟨hes2, hs1?⟩ => ?_
            cases s1? with
            | none => simp only [StateT.run_pure]; exact ZeroPost.pure hes2
            | some s1 =>
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroPost.pure ⟨hs1? s1 rfl, hes2.2⟩
          · split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
              exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
  · change ZeroPost _ _ ((corrEPaperBucket _ q5).run es); unfold corrEPaperBucket; simp only [StateT.run_bind, StateT.run_get, pure_bind]; split
    · simp only [StateT.run_pure]; exact ZeroPost.pure (hes.mono (Nat.le_succ rem))
    · rw [StateT.run_bind]
      refine (liftH_zeroPost (hzh.reveal_zp es.g q5 (es.g.st q5) es.h (hes.1 q5))).bind
        fun ⟨o, es1⟩ ⟨⟨hse1, hca1⟩, hg1, _⟩ => ?_
      have hH1 : BucketHInv q qep tL rem es1.h := ⟨hse1 ▸ (hes.2.mono (Nat.le_succ rem)).1, hca1 ▸ hes.2.2⟩
      cases o with
      | none =>
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
      | some _ =>
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroPost.pure ⟨hes.1, hH1⟩
  · rcases q6 with ⟨Pt, c, c'⟩
    change ZeroPost _ _ ((deliverForgeE _ Δ qep cfg (Pt, c, c')).run es); unfold deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]; split
    · simp only [StateT.run_pure]; exact ZeroPost.pure (hes.mono (Nat.le_succ rem))
    · cases es.g.inTransit Pt.other c with
      | none => simp only [StateT.run_pure]; exact ZeroPost.pure (hes.mono (Nat.le_succ rem))
      | some r =>
        dsimp only; split
        · simp only [StateT.run_pure]; exact ZeroPost.pure (hes.mono (Nat.le_succ rem))
        · rw [StateT.run_bind]; refine (liftH_zeroPost (vRecv_zeroPost hzh es.g Pt (es.g.st Pt) c' none es.h (hes.1 Pt) hes.2)).bind
            fun ⟨o, es1⟩ ⟨⟨hH1, ho⟩, hg1, _⟩ => ?_
          rcases o with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
          · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
          · dsimp only; split
            · simp only [StateT.run_pure]; exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
            · split
              · rw [StateT.run_bind]
                refine (commitE_zeroPost hzh es.g Pt (es.g.st Pt) st' ⟨Pt.other, t', i'⟩ es1 hes.1
                  (ho (st', t', i', m') rfl) ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩).bind fun ⟨s1?, es2⟩ ⟨hes2, hs1?⟩ => ?_
                cases s1? with
                | none => simp only [StateT.run_pure]; exact ZeroPost.pure hes2
                | some s1 =>
                  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact ZeroPost.pure ⟨hs1? s1 rfl, hes2.2⟩
              · split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
                  exact ZeroPost.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
private theorem redFSAuthDFPaperMultiBucket_badBucketQuery_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) {okB okM : M → Bool} (hok : ∀ m, okB m = true → okM m = true) (q Δcka Δbucket qep : ℕ) (hΔb : 2 ≤ Δbucket) (tL : Option ℕ) (par la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (hq : MakesAtMostQueriesDF A q) (hsh : SendMsgsOkDF okB A) :
    (redFSAuthDFPaperMultiBucket (q + 1) cka prng fs lam Δcka Δbucket qep la tL par A).IsQueryBoundP (fun x => badBucketQuery q qep tL okM x = true) 0 := by
  suffices hZ : ZeroPost (badBQ SS RS T M E q qep tL okM) (fun _ => True)
      (redFSAuthDFPaperMultiBucket (q + 1) cka prng fs lam Δcka Δbucket qep la tL par A) from hZ.1
  have hq' : A.IsQueryBoundP (fun x => x.isRight = true) q := hq.of_imp fun x hx => by cases x <;> exact hx
  unfold redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketGen engRunDFPaperBucket implEDFPaperBucket; rw [bind_assoc]
  let hk := hooksFSMultiDFBucketPaper (q + 1) cka prng fs Δcka Δbucket qep tL par la
  let rawImpl := implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
  let impl := withWinEpDF (fun c => c.1.1) (fun es => es.g.win) rawImpl
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · refine (initFSMultiDFBucketPaper_zero_any 1 0 okM cka prng fs lam Δbucket qep tL par).bind fun ⟨vs, h⟩ _ => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · simp only [pure_bind]; exact ZeroPost.pure trivial
    · simp only [bind_assoc]; refine (zeroPost_simulateQ_run_zero_inr (badBQ SS RS T M E 0 qep tL okM) impl
        (fun u st => withWinEpDF_zeroPost (Q := fun _ => True) _ _ rawImpl (.inl u) st
          (coinsE_zeroPost (P := badBQ SS RS T M E 0 qep tL okM) (Q := fun _ => True)
            (badBucketQuery_inl 0 qep tL okM) u st.1 trivial)) A hq' _).bind fun _ _ => ?_
      simp only [pure_bind]; exact ZeroPost.pure trivial
  · refine (initFSMultiDFBucketPaper_zeroPost okM cka prng fs lam hqpos hΔb).bind fun ⟨vs, h⟩ ⟨hH, hvs⟩ => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · simp only [pure_bind]; exact ZeroPost.pure trivial
    · simp only [bind_assoc]; obtain ⟨hvA, hvB⟩ := hvs (vA, vB) rfl
      let es₀ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiDFBucketState T RSt K I E) :=
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
      have hes₀ : BucketESInv q qep tL q es₀ := ⟨fun P => by cases P with | A => exact hvA | B => exact hvB, hH⟩
      refine (zeroPost_simulateQ_run_fuel_bad
        (badSendMsgDF (St := PartyState Γ T RSt SS RS) (Coins := CCoins) (C := Header T × E) okB)
        (badBQ SS RS T M E q qep tL okM) (fun rem st => BucketESInv q qep tL rem st.1) impl
        (fun u rem st hst => withWinEpDF_zeroPost (Q := BucketESInv q qep tL rem) _ _ rawImpl (.inl u) st
          (coinsE_zeroPost (P := badBQ SS RS T M E q qep tL okM) (Q := BucketESInv q qep tL rem)
            (badBucketQuery_inl q qep tL okM) u st.1 hst))
        (fun qr rem st hnb hst => withWinEpDF_zeroPost (Q := BucketESInv q qep tL rem) _ _ rawImpl (.inr qr) st
          (implEDFPaperBucketRaw_inr_zeroPost hok (paper_zeroHooks okM cka prng fs hqpos hΔb)
            (2 + Δcka) fs.maxSkip (bucketAuthCfgGen Δbucket tL par) qr st.1 hnb hst))
        q A hq' hsh (es₀, none) hes₀).bind fun _ _ => ?_
      simp only [pure_bind]; exact ZeroPost.pure trivial
private theorem redFSAuthDFPaperMultiBucketMode_badBucketQuery_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) {okB okM : M → Bool} (hok : ∀ m, okB m = true → okM m = true) (q Δcka Δbucket qep : ℕ) (hΔb : 2 ≤ Δbucket) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (hq : MakesAtMostQueriesDF A q) (hsh : SendMsgsOkDF okB A) :
    (redFSAuthDFPaperMultiBucketMode (q + 1) cka prng fs lam Δcka Δbucket qep gMain la tL par A).IsQueryBoundP (fun x => badBucketQuery q qep tL okM x = true) 0 := by
  suffices hZ : ZeroPost (badBQ SS RS T M E q qep tL okM) (fun _ => True)
      (redFSAuthDFPaperMultiBucketMode (q + 1) cka prng fs lam Δcka Δbucket qep gMain la tL par A) from hZ.1
  have hq' : A.IsQueryBoundP (fun x => x.isRight = true) q := hq.of_imp fun x hx => by cases x <;> exact hx
  unfold redFSAuthDFPaperMultiBucketMode redFSAuthDFPaperMultiBucketModeGen engRunDFPaperBucketMode implEDFPaperBucketMode; rw [bind_assoc]
  let hk := hooksFSMultiDFBucketPaperMode (q + 1) cka prng fs Δcka Δbucket qep gMain tL par la
  let rawImpl := implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
  let impl := withWinEpDFMode gMain isHonestHdrFSMultiDFBucket (fun vp => vp.tcur) rawImpl
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · refine (initFSMultiDFBucketPaper_zero_any 1 0 okM cka prng fs lam Δbucket qep tL par).bind fun ⟨vs, h⟩ _ => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · simp only [pure_bind]; exact ZeroPost.pure trivial
    · simp only [bind_assoc]; refine (zeroPost_simulateQ_run_zero_inr (badBQ SS RS T M E 0 qep tL okM) impl
        (fun u st => withWinEpDFMode_zeroPost (Q := fun _ => True) gMain _ _ rawImpl (.inl u) st
          (coinsE_zeroPost (P := badBQ SS RS T M E 0 qep tL okM) (Q := fun _ => True)
            (badBucketQuery_inl 0 qep tL okM) u st.1 trivial)) A hq' _).bind fun _ _ => ?_
      simp only [pure_bind]; exact ZeroPost.pure trivial
  · refine (initFSMultiDFBucketPaper_zeroPost okM cka prng fs lam hqpos hΔb).bind fun ⟨vs, h⟩ ⟨hH, hvs⟩ => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · simp only [pure_bind]; exact ZeroPost.pure trivial
    · simp only [bind_assoc]; obtain ⟨hvA, hvB⟩ := hvs (vA, vB) rfl
      let es₀ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiDFBucketState T RSt K I E) :=
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
      have hes₀ : BucketESInv q qep tL q es₀ := ⟨fun P => by cases P with | A => exact hvA | B => exact hvB, hH⟩
      refine (zeroPost_simulateQ_run_fuel_bad
        (badSendMsgDF (St := PartyState Γ T RSt SS RS) (Coins := CCoins) (C := Header T × E) okB)
        (badBQ SS RS T M E q qep tL okM) (fun rem st => BucketESInv q qep tL rem st.1) impl
        (fun u rem st hst => withWinEpDFMode_zeroPost (Q := BucketESInv q qep tL rem) gMain _ _ rawImpl (.inl u) st
          (coinsE_zeroPost (P := badBQ SS RS T M E q qep tL okM) (Q := BucketESInv q qep tL rem)
            (badBucketQuery_inl q qep tL okM) u st.1 hst))
        (fun qr rem st hnb hst => withWinEpDFMode_zeroPost (Q := BucketESInv q qep tL rem) gMain _ _ rawImpl (.inr qr) st
          (implEDFPaperBucketRaw_inr_zeroPost hok (paperMode_zeroHooks okM cka prng fs hqpos hΔb)
            (2 + Δcka) fs.maxSkip (bucketAuthCfgGen Δbucket tL par) qr st.1 hnb hst))
        q A hq' hsh (es₀, none) hes₀).bind fun _ _ => ?_
      simp only [pure_bind]; exact ZeroPost.pure trivial
end BucketTwoModeHelpers
section ModeDecHelpers
open _root_.CryptoGames.FSAEAD (transmitQuery challengeQuery corruptSenderQuery deliverQuery injectQuery)
open _root_.CryptoGames.SM (Config specDF)
open _root_.CryptoGames.SM.Engine (Hooks EState VP TComp coinsE)
open _root_.CryptoGames.SM.Construction (PartyState sampleT bucketAuthCfgGen FSMultiSpec FSMultiBook FSMultiDFBucketState liftFSMultiDFBucket lookupMultiDFBucketF rootFSMultiDFBucketPaper hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode isHonestHdrFSMultiDFBucket initFSMultiDFBucketPaper redFSAuthDFPaperMultiBucketModeGen)
open _root_.CryptoGames.SM.Construction.DeliverForge (engRunDFPaperBucketMode implEDFPaperBucketMode implEDFPaperBucketRaw withWinEpDF withWinEpDFMode)
open Computational.Proofs.E2E.SessionAuthHooksPot (PotBound potBound_simulateQ_run ShallowHooksPot coinsE_pot implEDFPaperBucketRaw_inr_pot withWinEpDF_pot)
private theorem query_eq_liftM_dec {ι : Type} {spec : OracleSpec.{0, 0} ι} (t : spec.Domain) :
    (query (spec := spec) t : OracleComp spec (spec.Range t)) = liftM (spec.query t) := rfl
private theorem lift_inr_query_eq_dec {ι₁ ι₂ : Type} {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂}
    (q₀ : s₂.Domain) : (liftM (OracleSpec.query q₀) : OracleComp (s₁ + s₂) (s₂.Range q₀)) = liftM (OracleSpec.query (spec := s₁ + s₂) (Sum.inr q₀)) := rfl
private def fsInjMultiPred {SS RS T M E : Type} : (unifSpec + FSMultiSpec SS RS T M E).Domain → Bool
  | .inl _ => false
  | .inr ⟨_, .inr _⟩ => true
  | .inr ⟨_, .inl _⟩ => false
private theorem fsInjMultiPred_inl {SS RS T M E : Type} (u : unifSpec.Domain) : fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (.inl u) = false := rfl
private theorem sampleT_inj_pot {SS RS T M E : Type} (α : Type) [SampleableType α] (rem : ℕ) : PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem) (sampleT (tspec := FSMultiSpec SS RS T M E) α) rem :=
  PotBound.of_zero_queries fsInjMultiPred_inl ($ᵗ α : ProbComp α) rem
private theorem lift_sampleT_inj_pot {SS RS T M E HS : Type} (α : Type) [SampleableType α] (h : HS) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem) ((StateT.lift (sampleT α)).run h) rem := by
  rw [StateT.run_lift]; exact (sampleT_inj_pot α rem).bind fun _ _ hk => PotBound.pure hk
private theorem liftFSMultiDFBucket_inj_zero {SS RS T M E Sig K I : Type} (sIdx : ℕ) (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (hq : fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (.inr ⟨sIdx, q₀⟩) = false)
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E)) (fun _ => rem)
      ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h) rem := by
  have hstep : ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inr ⟨sIdx, q₀⟩) >>= fun r => Pure.pure (r, h)) := by
    rw [lift_inr_query_eq_dec]; simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hstep]; exact (PotBound.query_zero rem hq).bind fun _ _ hk => PotBound.pure hk
private theorem liftFSMultiDFBucket_inj_le_one {SS RS T M E Sig K I : Type} (sIdx : ℕ) (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) : PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E)) (fun _ => rem)
      ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h) (rem + 1) := by
  have hstep : ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inr ⟨sIdx, q₀⟩) >>= fun r => Pure.pure (r, h)) := by
    rw [lift_inr_query_eq_dec]; simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hstep]; exact (PotBound.query_le_one (m := rem) le_rfl).bind fun _ _ hk => PotBound.pure hk
private theorem lookupMultiDFBucketF_inj {SS RS T M E Sig K I : Type} [DecidableEq I] [SampleableType K] (t0 : ℕ) (ik : I) (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem) ((lookupMultiDFBucketF (SS := SS) (RS := RS) (M := M) t0 ik).run h) rem := by
  unfold lookupMultiDFBucketF; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (h.fTable t0).lookup ik with
  | some _ => exact PotBound.pure le_rfl
  | none =>
    simp only [StateT.run_bind]; exact (lift_sampleT_inj_pot K h rem).bind fun _ _ hk => by
      simp only [StateT.run_modify, StateT.run_pure, pure_bind]; exact PotBound.pure hk
private theorem rootFSMultiDFBucketPaper_inj {KR RSt K I T SS RS M E : Type} [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : RSt) (h : FSMultiDFBucketState T RSt K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E)) (fun _ => rem)
      ((rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
        prng Δbucket qep tL par t0 pl ik0 σ0).run h) rem := by
  unfold rootFSMultiDFBucketPaper; dsimp only; split
  · exact PotBound.pure le_rfl
  · split
    · split
      · simp only [StateT.run_bind]; refine (lift_sampleT_inj_pot I h rem).bind fun ⟨_, h1⟩ _ hm => ?_
        exact ((lift_sampleT_inj_pot K h1 rem).mono (fun _ => le_rfl) hm).bind fun _ _ hm2 => PotBound.pure hm2
      · simp only [StateT.run_bind]; exact (lookupMultiDFBucketF_inj t0 ik0 h rem).bind fun _ _ hm => PotBound.pure hm
    · split
      · simp only [StateT.run_bind]; refine (lift_sampleT_inj_pot I h rem).bind fun ⟨_, h1⟩ _ hm => ?_
        exact ((lift_sampleT_inj_pot K h1 rem).mono (fun _ => le_rfl) hm).bind fun _ _ hm2 => PotBound.pure hm2
      · exact PotBound.pure le_rfl
private theorem fsSendTailBucket_inj {SS RS T M E Sig K I : Type} (sIdx : ℕ) (hdr : Header T) (m : M)
    (pair : Option (M × M)) (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) : PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E)) (fun _ => rem)
      ((do
        let e? ← match pair with
          | some (m₀, m₁) => liftFSMultiDFBucket sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
          | none => liftFSMultiDFBucket sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
        match e? with
        | none => return none
        | some e =>
          modify fun st : FSMultiDFBucketState T Sig K I E =>
            let b0 := (st.book sIdx).getD {}
            let cnt' := b0.fsCount + 1
            let b' : FSMultiBook T E := { b0 with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b0.fsTrans }
            { st with book := Function.update st.book sIdx (some b') }
          return some ((.inr sIdx : SS ⊕ ℕ), e)).run h) rem := by
  rcases pair with _ | ⟨m₀, m₁⟩
  · simp only [StateT.run_bind, transmitQuery, query_eq_liftM_dec]
    refine (liftFSMultiDFBucket_inj_zero sIdx _ rfl h rem).bind fun ⟨o, _⟩ _ hm => ?_
    rcases o with _ | _ <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;> exact PotBound.pure hm
  · simp only [StateT.run_bind, challengeQuery, query_eq_liftM_dec]
    refine (liftFSMultiDFBucket_inj_zero sIdx _ rfl h rem).bind fun ⟨o, _⟩ _ hm => ?_
    rcases o with _ | _ <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;> exact PotBound.pure hm
private theorem hooksFSMultiDFBucketPaperMode_inj_pot {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool) : ShallowHooksPot fsInjMultiPred (fun _ => 0)
      (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la) where
  inl_false := fsInjMultiPred_inl
  startSend_pot _ _ t0 γ0 σ0 r0 h rem := by
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper, Nat.add_zero]; rcases r0 with _ | c
    · simp only [StateT.run_bind]; refine (lift_sampleT_inj_pot CCoins h rem).bind fun ⟨coins, h1⟩ _ hm1 => ?_
      refine ((rootFSMultiDFBucketPaper_inj prng Δbucket qep tL par t0 _ (cka.send γ0 coins).2.2 σ0 h1 rem).mono
        (fun _ => le_rfl) hm1).bind fun _ _ hm2 => ?_
      simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]; exact PotBound.pure hm2
    · simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      refine (rootFSMultiDFBucketPaper_inj prng Δbucket qep tL par t0 _ (cka.send γ0 c).2.2 σ0 h rem).bind fun _ _ hm2 => ?_
      simp only [StateT.run_get, StateT.run_set, pure_bind]; exact PotBound.pure hm2
  startRecv_pot _ _ t0 γ0 σ0 tn0 h rem := by
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper, Nat.add_zero]; cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]; split
      · exact PotBound.pure le_rfl
      · split
        · split
          · exact PotBound.pure le_rfl
          · split
            · exact PotBound.pure le_rfl
            · simp only [StateT.run_bind]
              refine (lookupMultiDFBucketF_inj t0 (cka.receive γ0 tn0).2 h rem).bind fun _ _ hm1 => ?_
              simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]; exact PotBound.pure hm1
        · exact PotBound.pure le_rfl
    · simp only [↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]; rcases h.cache t0 with _ | ⟨tCached, σc, kVal, optIdx⟩
      · dsimp only; split_ifs <;> exact PotBound.pure le_rfl
      · dsimp only; by_cases ht : tCached = tn0
        · subst ht; simp only [↓reduceIte]; exact PotBound.pure le_rfl
        · simp only [ht, ↓reduceIte]; split_ifs <;> exact PotBound.pure le_rfl
  fsSend_pot _ _ _ ssv hdr m pair h rem := by
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper, Nat.add_zero]; rcases ssv with _ | sIdx
    · exact PotBound.pure (by omega)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split
      · simp only [StateT.run_bind, corruptSenderQuery, query_eq_liftM_dec]
        refine (liftFSMultiDFBucket_inj_zero sIdx _ rfl h (rem + 1)).bind fun ⟨o, _⟩ _ hm1 => ?_
        rcases o with _ | _
        · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]; exact PotBound.pure (by omega)
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact (fsSendTailBucket_inj (SS := SS) (RS := RS) sIdx hdr m pair _ rem).mono (fun _ => le_rfl) (by omega)
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact (fsSendTailBucket_inj (SS := SS) (RS := RS) sIdx hdr m pair h rem).mono (fun _ => le_rfl) (by omega)
  fsRecv_pot _ _ _ rsv hdr e rec h rem := by
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper, Nat.add_zero]; rcases rsv with _ | sIdx
    · exact PotBound.pure (by omega)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      let matched : Option (ℕ × Header T × E) := ((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))
      have hTail : ∀ h' : FSMultiDFBucketState T RSt K I E, PotBound fsInjMultiPred (fun _ => rem)
          ((do
            let res ← if matched.isSome then liftFSMultiDFBucket sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
              else liftFSMultiDFBucket sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
            match res with
            | none => return (none : Option (Option ((RS ⊕ ℕ) × ℕ × M)))
            | some .rejected => return some none
            | some (.accepted i mo') =>
              let s1 ← get
              let bk1 := (s1.book sIdx).getD {}
              if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
                modify fun (s : FSMultiDFBucketState T RSt K I E) => { s with lfWin := true }
                return none
              else
                let drop := (matched.map (fun (x : ℕ × Header T × E) => x.1)).getD i
                modify fun (s : FSMultiDFBucketState T RSt K I E) =>
                  let b := (s.book sIdx).getD {}
                  let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
                  { s with book := Function.update s.book sIdx (some b') }
                match mo', rec with
                | some m, _ => return some (some ((.inr sIdx : RS ⊕ ℕ), i, m))
                | none, some r => return some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg))
                | none, none => return none).run h') (rem + 1) := by
        intro h'; split_ifs
        · simp only [StateT.run_bind, deliverQuery, query_eq_liftM_dec]
          refine (liftFSMultiDFBucket_inj_le_one sIdx _ h' rem).bind fun ⟨res, _⟩ _ hm1 => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact PotBound.pure hm1
          · exact PotBound.pure hm1
          · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact PotBound.pure hm1
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind]; rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact PotBound.pure hm1
        · simp only [StateT.run_bind, injectQuery, query_eq_liftM_dec]
          refine (liftFSMultiDFBucket_inj_le_one sIdx _ h' rem).bind fun ⟨res, _⟩ _ hm1 => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact PotBound.pure hm1
          · exact PotBound.pure hm1
          · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact PotBound.pure hm1
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind]; rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact PotBound.pure hm1
      split
      · simp only [StateT.run_bind, corruptSenderQuery, query_eq_liftM_dec]
        refine (liftFSMultiDFBucket_inj_zero sIdx _ rfl h (rem + 1)).bind fun ⟨o, _⟩ _ hm1 => ?_
        rcases o with _ | _
        · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]; exact PotBound.pure (by omega)
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact (hTail _).mono (fun _ => le_rfl) (by omega)
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hTail h
  commit_pot _ _ _ _ _ rem := PotBound.pure le_rfl
  reveal_pot ctx P vp h rem := by
    have hRev : PotBound fsInjMultiPred (fun _ => rem)
        (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).reveal ctx P vp).run h) (rem + 1) := by
      dsimp only [hooksFSMultiDFBucketPaper]; rcases vp.vS with _ | (_ | sIdx)
      · simp only [pure_bind]; split_ifs <;> exact PotBound.pure (by omega)
      · simp only [pure_bind]; split_ifs <;> exact PotBound.pure (by omega)
      · simp only [StateT.run_bind, corruptSenderQuery, query_eq_liftM_dec]
        refine (liftFSMultiDFBucket_inj_zero sIdx _ rfl h (rem + 1)).bind fun ⟨o, _⟩ _ hm1 => ?_
        rcases o with _ | _
        · simp only [StateT.run_pure, pure_bind]; exact PotBound.pure (by omega)
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind]; split_ifs <;> exact PotBound.pure (by omega)
    dsimp only [hooksFSMultiDFBucketPaperMode, Nat.add_zero]; cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs
      · exact PotBound.pure (by omega)
      · exact hRev
    · exact hRev
private theorem initFSMultiDFBucketPaper_inj {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K] (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (rem : ℕ) : PotBound fsInjMultiPred (fun _ => rem)
      ((initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par).run ({} : FSMultiDFBucketState T RSt K I E)) rem := by
  unfold initFSMultiDFBucketPaper; simp only [StateT.run_bind]
  refine (lift_sampleT_inj_pot KR ({} : FSMultiDFBucketState T RSt K I E) rem).bind fun ⟨kr, h1⟩ _ hm1 => ?_
  refine ((lift_sampleT_inj_pot KC h1 rem).mono (fun _ => le_rfl) hm1).bind fun ⟨_, h2⟩ _ hm2 => ?_
  refine ((rootFSMultiDFBucketPaper_inj (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
    prng Δbucket qep tL par 0 false lam (prng.init kr) h2 rem).mono (fun _ => le_rfl) hm2).bind fun _ _ hm3 => ?_
  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]; exact PotBound.pure hm3
private theorem withWinEpDFMode_pot {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St Msg Coins T' E' VPt HS : Type} {P : (unifSpec + tspec).Domain → Bool}
    {pot : EState VPt Msg (Header T' × E') HS → ℕ} (gMain : Bool) (isHonest : HS → Header T' → Bool) (epOf : VPt → ℕ)
    (impl : QueryImpl (unifSpec + specDF St Msg Coins (Header T' × E')) (StateT (EState VPt Msg (Header T' × E') HS) (TComp tspec)))
    (t : (unifSpec + specDF St Msg Coins (Header T' × E')).Domain) (st : EState VPt Msg (Header T' × E') HS × Option ℕ) {rem b : ℕ}
    (h : PotBound P (fun z => rem + pot z.2) ((impl t).run st.1) b) : PotBound P (fun z => rem + pot z.2.1) ((withWinEpDFMode gMain isHonest epOf impl t).run st) b := by
  unfold withWinEpDFMode; split
  · exact withWinEpDF_pot _ _ impl t st h
  · dsimp only [StateT.run_mk]; exact h.bind fun ⟨r', s'⟩ k hk => PotBound.pure (by dsimp only at hk ⊢; exact hk)
private theorem redFSAuthDFPaperMultiBucketMode_dec_onAnySess {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K] (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (q Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFPaperMultiBucketMode L cka prng fs lam Δcka Δbucket qep gMain la tL par A).IsQueryBoundP (fun x => onAnySess fsInjQ x = true) q := by
  suffices hPub : (redFSAuthDFPaperMultiBucketMode L cka prng fs lam Δcka Δbucket qep gMain la tL par A).IsQueryBoundP
      (fun x => fsInjMultiPred x = true) q from
    hPub.of_imp fun x hx => by rcases x with _ | ⟨_, _ | _⟩ <;> exact hx
  have hq' : A.IsQueryBoundP (fun x => x.isRight = true) q := hq.of_imp fun x hx => by cases x <;> exact hx
  unfold redFSAuthDFPaperMultiBucketMode redFSAuthDFPaperMultiBucketModeGen engRunDFPaperBucketMode implEDFPaperBucketMode; rw [bind_assoc]
  let hk := hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la
  let rawImpl := implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
  let impl := withWinEpDFMode gMain isHonestHdrFSMultiDFBucket (fun vp => vp.tcur) rawImpl
  have hkPot := hooksFSMultiDFBucketPaperMode_inj_pot L cka prng fs Δcka Δbucket qep gMain tL par la
  refine ((initFSMultiDFBucketPaper_inj L cka prng fs lam Δbucket qep tL par q).bind
    (post := fun _ => 0) fun ⟨vs, h⟩ m hm => ?_).to_isQueryBoundP
  rcases vs with _ | ⟨vA, vB⟩
  · simp only [pure_bind]; exact PotBound.pure (Nat.zero_le m)
  · simp only [bind_assoc]
    let es₀ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiDFBucketState T RSt K I E) :=
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
    exact ((potBound_simulateQ_run fsInjMultiPred (fun _ => 0) impl
      (fun u st rem => withWinEpDFMode_pot (pot := fun _ => 0) (rem := rem) gMain _ _
        rawImpl (.inl u) st (coinsE_pot (pot := fun _ => 0) fsInjMultiPred_inl u st.1 rem))
      (fun qr st rem => withWinEpDFMode_pot (pot := fun _ => 0) (rem := rem) gMain _ _
        rawImpl (.inr qr) st (implEDFPaperBucketRaw_inr_pot hkPot (2 + Δcka) qep fs.maxSkip _ qr st.1 rem))
      q A hq' (es₀, none)).mono (fun _ => Nat.zero_le _) (by omega)).bind fun _ m2 _ =>
      PotBound.pure (Nat.zero_le m2)
end ModeDecHelpers
section ModeShortHelpers
open _root_.CryptoGames.FSAEAD (transmitQuery challengeQuery corruptSenderQuery deliverQuery injectQuery)
open _root_.CryptoGames.GuardedSafe (GuardedSafePost GuardedSafeS guardedSafeS_pure guardedSafeS_pure_true guardedSafeS_get_bind guardedSafeS_bind_true guardedSafeS_bind_and guardedSafeS_set_true guardedSafeS_modify_true guardedSafeS_lift_true)
open _root_.CryptoGames.SM (Config)
open _root_.CryptoGames.SM.Engine (Hooks EState VP Ctx HM TComp liftH abortE coinsE vSend vRecv commitE deliverE injectE)
open _root_.CryptoGames.SM.Construction (sampleT FSMultiSpec FSMultiDFBucketState hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode isHonestHdrFSMultiDFBucket rootFSMultiDFBucketPaper initFSMultiDFBucketPaper liftFSMultiDFBucket lookupMultiDFBucketF bucketAuthCfgGen redFSAuthDFPaperMultiBucketModeGen)
open _root_.CryptoGames.SM.Construction.DeliverForge (engRunDFPaperBucketMode implEDFPaperBucketMode implEDFPaperBucketRaw transmitEBucket challEBucket corrEPaperBucket deliverForgeE withWinEpDF withWinEpDFMode)
open _root_.CryptoGames.Ratchet.LibsignalInst (fsRespShort fsInjectLong)
open _root_.CryptoVerification.LibsignalSession (signalEncodeFits32_proto)
open _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed (FsSendShort lFS_fsSendShort)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB_imp_shortB)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (smDFRespShort)
local notation "E₀" => ℕ × LibsignalCiphertextWithSalt32
private theorem query_eq_liftM_fg {ι : Type} {spec : OracleSpec.{0, 0} ι} (t : spec.Domain) :
    (query (spec := spec) t : OracleComp spec (spec.Range t)) = liftM (spec.query t) := rfl
private def multiRespShortRaw {SS RS AD Msg : Type} : (t : (unifSpec + OracleSpec.sigma (fun _ : ℕ => _root_.CryptoGames.FSAEAD.spec SS RS AD Msg E₀)).Domain) →
    (unifSpec + OracleSpec.sigma (fun _ : ℕ => _root_.CryptoGames.FSAEAD.spec SS RS AD Msg E₀)).Range t → Prop
  | .inr ⟨_, o⟩, r => fsRespShort (SS := SS) (RS := RS) (AD := AD) (Msg := Msg) (.inr o) r
  | .inl _, _ => True
private def multiInjectLongRaw {SS RS AD Msg : Type} : (unifSpec + OracleSpec.sigma (fun _ : ℕ => _root_.CryptoGames.FSAEAD.spec SS RS AD Msg E₀)).Domain → Prop
  | .inr ⟨_, o⟩ => fsInjectLong (SS := SS) (RS := RS) (AD := AD) (Msg := Msg) (.inr o)
  | .inl _ => False
private abbrev MultiFGSafeS {SS RS T M σ α : Type} (P : α → Prop) (x : StateT σ (TComp (FSMultiSpec SS RS T M E₀)) α) : Prop :=
  GuardedSafeS (multiRespShortRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
    (multiInjectLongRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M)) (fun _ => True) (fun a _ => P a ∧ True) x
private abbrev MultiFGSafeSTrue {SS RS T M σ α : Type} (x : StateT σ (TComp (FSMultiSpec SS RS T M E₀)) α) : Prop :=
  GuardedSafeS (multiRespShortRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
    (multiInjectLongRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M)) (fun _ => True) (fun _ _ => True) x
private theorem multiFGSafePost_sampleT {SS RS T M : Type} (α : Type) [SampleableType α] :
    GuardedSafePost (multiRespShortRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (multiInjectLongRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (fun _ => True) (sampleT (tspec := FSMultiSpec SS RS T M E₀) α) :=
  GuardedSafePost.liftComp_unif (fun _ => not_false) ($ᵗ α)
private theorem multiFGSafeS_lift_sampleT {SS RS T M σ : Type} (α : Type) [SampleableType α] : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) (σ := σ)
      (StateT.lift (sampleT (tspec := FSMultiSpec SS RS T M E₀) α)) :=
  guardedSafeS_lift_true (multiFGSafePost_sampleT α)
private structure MultiHooksFGSafe {HS Γ T RSt SS RS M CCoins Γv Sv SSv RSv : Type}
    (ok : M → Bool) (hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv) : Prop where
  startSend_fg : ∀ ctx P t γ σ r, MultiFGSafeSTrue (hk.startSend ctx P t γ σ r)
  startRecv_fg : ∀ ctx P t γ σ Tn, MultiFGSafeSTrue (hk.startRecv ctx P t γ σ Tn)
  fsSend_fg : ∀ ctx P t ssv h m pair, ok m = true →
    MultiFGSafeS (fun res => ∀ ssv' (e : E₀), res = some (ssv', e) → e.2.1.1.length + 8 < 2 ^ 32) (hk.fsSend ctx P t ssv h m pair)
  fsRecv_fg : ∀ ctx P t rsv h (e : E₀) rec, e.2.1.1.length < 2 ^ 32 → MultiFGSafeSTrue (hk.fsRecv ctx P t rsv h e rec)
  reveal_fg : ∀ ctx P vp, MultiFGSafeSTrue (hk.reveal ctx P vp)
  commit_fg : ∀ ctx P old new, MultiFGSafeSTrue (hk.commit ctx P old new)
private theorem multiFGSafeS_liftH_true {SS RS T M HS Γv Sv SSv RSv α : Type}
    {x : HM (FSMultiSpec SS RS T M E₀) HS α} (hx : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) x) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftH x : StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E₀) HS) (TComp (FSMultiSpec SS RS T M E₀)) α) :=
  fun es _ => by unfold liftH; exact (hx es.h trivial).bind fun _ _ => GuardedSafePost.pure trivial
private theorem multiFGSafeS_liftH_and {SS RS T M HS Γv Sv SSv RSv α : Type} {C : α → Prop}
    {x : HM (FSMultiSpec SS RS T M E₀) HS α} (hx : MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M) C x) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M) C
      (liftH x : StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E₀) HS) (TComp (FSMultiSpec SS RS T M E₀)) α) :=
  fun es _ => by unfold liftH; exact (hx es.h trivial).bind fun p hp => GuardedSafePost.pure ⟨hp.1, trivial⟩
private theorem multiFGSafeS_abortE {SS RS T M HS Γv Sv SSv RSv : Type} : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (abortE : StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E₀) HS) (TComp (FSMultiSpec SS RS T M E₀)) Unit) := by
  unfold abortE; exact guardedSafeS_modify_true _ fun _ _ => trivial
private theorem multiFGSafeS_coinsE {SS RS T M HS Γv Sv SSv RSv : Type} (u : ℕ) : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (coinsE u : StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E₀) HS) (TComp (FSMultiSpec SS RS T M E₀)) _) :=
  fun _ _ => (GuardedSafePost.query not_false).bind fun _ _ => GuardedSafePost.pure trivial
private theorem multiFGSafeS_commitE {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type} [DecidableEq T] [DecidableEq M] {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv} (hSpec : MultiHooksFGSafe ok hk) (s : Ctx Γv T Sv SSv RSv M E₀) (P : Party)
    (old new : VP Γv T Sv SSv RSv) (pos : _root_.CryptoGames.SM.Pos) : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) (commitE hk s P old new pos) := by
  unfold commitE
  refine guardedSafeS_bind_true (multiFGSafeS_liftH_true (hSpec.commit_fg _ P old new)) fun res => ?_
  cases res with
  | none => exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
  | some _ => exact guardedSafeS_pure_true _
private theorem multiFGSafeS_vSend {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type} {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (ctx : Ctx Γv T Sv SSv RSv M E₀) (P : Party) (s : VP Γv T Sv SSv RSv)
    (m : M) (pair : Option (M × M)) (r : Option CCoins) (hm : ok m = true) : MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ vp' (c : Header T × E₀), res = some (vp', c) → c.2.2.1.1.length + 8 < 2 ^ 32)
      (vSend hk ctx P s m pair r) := by
  unfold vSend; have hdef : (default : E₀).2.1.1.length + 8 < 2 ^ 32 := by decide
  by_cases h1 : s.id.sendsIn (s.tcur + 1) = true
  · simp only [h1, ↓reduceIte]
    refine guardedSafeS_bind_true (hSpec.startSend_fg ctx P (s.tcur + 1) s.γ s.root r) fun res => ?_
    rcases res with _ | ⟨γ', T', σ', ss⟩
    · simp only [pure_bind]; exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
    · simp only [pure_bind]
      refine guardedSafeS_bind_and (hSpec.fsSend_fg ctx P (s.tcur + 1) ss (s.tcur + 1, some T') m pair hm) fun res' hres' => ?_
      rcases res' with _ | ⟨v', e⟩
      · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
      · refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩; rintro _ _ ⟨⟩; exact hres' v' e rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind]
    cases s.vS with
    | none => refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩; rintro _ _ ⟨⟩; exact hdef
    | some v =>
      refine guardedSafeS_bind_and (hSpec.fsSend_fg ctx P s.tcur v (s.tcur, s.curCkaMsg) m pair hm) fun res' hres' => ?_
      rcases res' with _ | ⟨v', e⟩
      · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
      · refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩; rintro _ _ ⟨⟩; exact hres' v' e rfl
private theorem multiFGSafeS_vRecv {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type} {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (ctx : Ctx Γv T Sv SSv RSv M E₀) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E₀) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E₀))) (hc : c.2.2.1.1.length < 2 ^ 32) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) (vRecv hk ctx P s c rec) := by
  unfold vRecv; dsimp only; split
  · exact guardedSafeS_pure_true (some none)
  · split
    · cases c.1.2 with
      | none => simp only [pure_bind]; exact guardedSafeS_pure_true (some none)
      | some Tn =>
        refine guardedSafeS_bind_true (hSpec.startRecv_fg ctx P c.1.1 s.γ s.root Tn) fun res => ?_
        rcases res with _ | (_ | ⟨γ', σ', rs⟩)
        · simp only [pure_bind]; exact guardedSafeS_pure_true none
        · simp only [pure_bind]; exact guardedSafeS_pure_true (some none)
        · simp only [pure_bind, Function.update_self]
          refine guardedSafeS_bind_true (hSpec.fsRecv_fg ctx P c.1.1 rs c.1 c.2 rec hc) fun res' => ?_
          rcases res' with _ | (_ | ⟨v', i, m⟩) <;> exact guardedSafeS_pure_true _
    · simp only [pure_bind]; cases s.vR c.1.1 with
      | none => exact guardedSafeS_pure_true (some none)
      | some v =>
        refine guardedSafeS_bind_true (hSpec.fsRecv_fg ctx P c.1.1 v c.1 c.2 rec hc) fun res' => ?_
        rcases res' with _ | (_ | ⟨v', i, m⟩) <;> exact guardedSafeS_pure_true _
private theorem multiFGSafeS_transmitEBucket {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type} {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (Δ qep : ℕ) (q : Party × M × Option CCoins) (hok : ok q.2.1 = true) : MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × E₀, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (transmitEBucket hk Δ qep q) := by
  rcases q with ⟨P, m, r⟩; unfold transmitEBucket; refine guardedSafeS_get_bind fun es _ => ?_; by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]; cases es.g.epMgmt Δ qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      refine guardedSafeS_bind_and (multiFGSafeS_liftH_and (multiFGSafeS_vSend hSpec s₁ P (s₁.st P) m none r hok)) fun res hres => ?_
      rcases res with _ | ⟨st', c⟩
      · exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
        refine guardedSafeS_pure (some c) fun _ _ => ⟨?_, trivial⟩; rintro _ ⟨⟩; exact hres st' c rfl
private theorem multiFGSafeS_challEBucket {SS RS T M HS CCoins Γv Sv SSv RSv : Type} (q : Party × M × M × Option CCoins) : MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × E₀, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (challEBucket q : StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E₀) HS) (TComp (FSMultiSpec SS RS T M E₀)) _) := by
  unfold challEBucket; exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
private theorem multiFGSafeS_deliverE {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type} [DecidableEq T] [DecidableEq M] {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv} (hSpec : MultiHooksFGSafe ok hk) (maxSkip : ℕ) (cfg : Config M)
    (q : Party × (Header T × E₀)) (hc : q.2.2.2.1.1.length < 2 ^ 32) : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) (deliverE hk maxSkip cfg q) := by
  rcases q with ⟨P, c⟩; unfold deliverE; refine guardedSafeS_get_bind fun es _ => ?_; by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]; cases es.g.inTransit P.other c with
    | none => exact guardedSafeS_pure_true none
    | some r =>
      refine guardedSafeS_bind_true (multiFGSafeS_liftH_true (multiFGSafeS_vRecv hSpec es.g P (es.g.st P) c (some r) hc)) fun res => ?_
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
      · by_cases h2 : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r) = true
        · simp only [h2, ↓reduceIte]; exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true _
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]; exact guardedSafeS_pure_true _
      · refine guardedSafeS_bind_true (multiFGSafeS_commitE hSpec es.g P (es.g.st P) st' r.pos) fun s₁? => ?_
        rcases s₁? with _ | s₁
        · exact guardedSafeS_pure_true none
        · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true _
private theorem multiFGSafeS_injectE {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type} [DecidableEq T] [DecidableEq M] {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv} (hSpec : MultiHooksFGSafe ok hk) (Δ qep : ℕ) (cfg : Config M)
    (q : Party × (Header T × E₀)) (hc : q.2.2.2.1.1.length < 2 ^ 32) : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) (injectE hk Δ qep cfg q) := by
  rcases q with ⟨P, c⟩; unfold injectE; dsimp only; refine guardedSafeS_get_bind fun es _ => ?_; split_ifs with h1
  · exact guardedSafeS_pure_true none
  · refine guardedSafeS_bind_true (multiFGSafeS_liftH_true (multiFGSafeS_vRecv hSpec es.g P (es.g.st P) c none hc)) fun res => ?_
    rcases res with _ | (_ | ⟨st', t', i', m'⟩)
    · exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
    · exact guardedSafeS_pure_true _
    · by_cases h2 : qep + 1 < t'
      · simp only [h2, ↓reduceIte]; exact guardedSafeS_pure_true _
      · simp only [h2, ↓reduceIte]; split_ifs
        · refine guardedSafeS_bind_true (multiFGSafeS_commitE hSpec es.g P (es.g.st P) st' ⟨P.other, t', i'⟩) fun s₁? => ?_
          rcases s₁? with _ | s₁
          · exact guardedSafeS_pure_true none
          · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true _
        · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true _
        · exact guardedSafeS_pure_true _
private theorem multiFGSafeS_deliverForgeE {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type} [DecidableEq T] [DecidableEq M] {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv} (hSpec : MultiHooksFGSafe ok hk) (Δ qep : ℕ) (cfg : Config M)
    (q : Party × (Header T × E₀) × (Header T × E₀)) (hc' : q.2.2.2.2.1.1.length < 2 ^ 32) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) (deliverForgeE hk Δ qep cfg q) := by
  rcases q with ⟨P, c, c'⟩; unfold deliverForgeE; dsimp only; refine guardedSafeS_get_bind fun es _ => ?_; by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]; cases es.g.inTransit P.other c with
    | none => exact guardedSafeS_pure_true none
    | some r =>
      by_cases h2 : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [h2, ↓reduceIte]; exact guardedSafeS_pure_true none
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine guardedSafeS_bind_true (multiFGSafeS_liftH_true (multiFGSafeS_vRecv hSpec es.g P (es.g.st P) c' none hc')) fun res => ?_
        rcases res with _ | (_ | ⟨st', t', i', m'⟩)
        · exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
        · exact guardedSafeS_pure_true _
        · by_cases h3 : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
          · simp only [h3, ↓reduceIte]; exact guardedSafeS_pure_true _
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]; split_ifs
            · refine guardedSafeS_bind_true (multiFGSafeS_commitE hSpec es.g P (es.g.st P) st' ⟨P.other, t', i'⟩) fun s₁? => ?_
              rcases s₁? with _ | s₁
              · exact guardedSafeS_pure_true none
              · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true _
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true _
            · exact guardedSafeS_pure_true _
private theorem multiFGSafeS_corrEPaperBucket {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type} {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv} (hSpec : MultiHooksFGSafe ok hk) (P : Party) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) (corrEPaperBucket hk P) := by
  unfold corrEPaperBucket; refine guardedSafeS_get_bind fun es _ => ?_; split
  · exact guardedSafeS_pure_true none
  · refine guardedSafeS_bind_true (multiFGSafeS_liftH_true (hSpec.reveal_fg es.g P (es.g.st P))) fun res => ?_
    cases res with
    | none => exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
    | some st => exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true (some st)
private theorem multiFGSafeS_liftFSMultiDFBucket_query {SS RS T M Sig K I : Type} (sIdx : ℕ) {q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E₀).Domain}
    (hq₀ : ¬ multiInjectLongRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (.inr ⟨sIdx, q₀⟩)) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun a => fsRespShort (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (.inr q₀) a)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (liftM (OracleSpec.query
          (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E₀) (.inr q₀)))) := fun h _ => by
  have hq : ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀)
      (Sig := Sig) (K := K) (I := I) sIdx (liftM (OracleSpec.query
        (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E₀) (.inr q₀)))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E₀) (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hq]; exact (GuardedSafePost.query hq₀).bind fun _ ha => GuardedSafePost.pure ⟨ha, trivial⟩
private theorem multiFGSafeS_liftFSMultiDFBucket_transmit {SS RS T M Sig K I : Type} (sIdx : ℕ) (hdr : Header T) (m : M) : MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun a : Option E₀ => ∀ e, a = some e → e.2.1.1.length + 8 < 2 ^ 32)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)) := fun h _ => by
  unfold transmitQuery; rw [query_eq_liftM_fg]
  exact (multiFGSafeS_liftFSMultiDFBucket_query (q₀ := .inl (.inl (.inl (.inl (.inl (hdr, m))))))
    sIdx not_false h trivial).mono fun ⟨a, _⟩ ⟨ha, _⟩ => ⟨fun e he => by subst he; simpa [fsRespShort] using ha, trivial⟩
private theorem multiFGSafeS_liftFSMultiDFBucket_challenge {SS RS T M Sig K I : Type} (sIdx : ℕ) (hdr : Header T) (m₀ m₁ : M) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun a : Option E₀ => ∀ e, a = some e → e.2.1.1.length + 8 < 2 ^ 32)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)) := fun h _ => by
  unfold challengeQuery; rw [query_eq_liftM_fg]
  exact (multiFGSafeS_liftFSMultiDFBucket_query (q₀ := .inl (.inl (.inl (.inl (.inr (hdr, m₀, m₁))))))
    sIdx not_false h trivial).mono fun ⟨a, _⟩ ⟨ha, _⟩ => ⟨fun e he => by subst he; simpa [fsRespShort] using ha, trivial⟩
private theorem multiFGSafeS_liftFSMultiDFBucket_corrupt {SS RS T M Sig K I : Type} (sIdx : ℕ) : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (corruptSenderQuery (SenderState := SS) (ReceiverState := RS)
          (AssocData := Header T) (Message := M) (Ciphertext := E₀))) := fun h _ => by
  unfold corruptSenderQuery; rw [query_eq_liftM_fg]
  exact (multiFGSafeS_liftFSMultiDFBucket_query (q₀ := .inl (.inl (.inl (.inr ())))) sIdx not_false h trivial).mono fun _ _ => trivial
private theorem multiFGSafeS_liftFSMultiDFBucket_deliver {SS RS T M Sig K I : Type} (sIdx : ℕ) (hdr : Header T) (e : E₀) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) (Message := M) hdr e)) := fun h _ => by
  unfold deliverQuery; rw [query_eq_liftM_fg]; exact (multiFGSafeS_liftFSMultiDFBucket_query (q₀ := .inl (.inr (hdr, e))) sIdx not_false h trivial).mono fun _ _ => trivial
private theorem multiFGSafeS_liftFSMultiDFBucket_inject {SS RS T M Sig K I : Type} (sIdx : ℕ) (hdr : Header T) (e : E₀) (he : e.2.1.1.length < 2 ^ 32) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) (Message := M) hdr e)) := fun h _ => by
  unfold injectQuery; rw [query_eq_liftM_fg]
  exact (multiFGSafeS_liftFSMultiDFBucket_query (q₀ := .inr (hdr, e)) sIdx (fun hlong => hlong he) h trivial).mono fun _ _ => trivial
private theorem multiFGSafeS_lookupMultiDFBucketF {SS RS T M Sig K I : Type} [DecidableEq I] [SampleableType K] (t0 : ℕ) (Ik : I) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (lookupMultiDFBucketF (T := T) (RSt := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (M := M) (E := E₀) t0 Ik) := by
  unfold lookupMultiDFBucketF; refine guardedSafeS_get_bind fun s _ => ?_; dsimp only
  cases (s.fTable t0).lookup Ik with
  | some k => exact guardedSafeS_pure_true k
  | none =>
    refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT K) fun k => ?_
    exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true k
private theorem multiFGSafeS_rootFSMultiDFBucketPaper {KR RSt K I T SS RS M : Type} [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : RSt) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E₀) prng Δbucket qep tL par t0 pl ik0 σ0) := by
  unfold rootFSMultiDFBucketPaper; dsimp only; split
  · exact guardedSafeS_pure_true _
  · split
    · split
      · refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT I) fun _ => ?_
        exact guardedSafeS_bind_true (multiFGSafeS_lift_sampleT K) fun _ => guardedSafeS_pure_true _
      · exact guardedSafeS_bind_true (multiFGSafeS_lookupMultiDFBucketF t0 ik0) fun _ => guardedSafeS_pure_true _
    · split
      · refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT I) fun _ => ?_
        exact guardedSafeS_bind_true (multiFGSafeS_lift_sampleT K) fun _ => guardedSafeS_pure_true _
      · exact guardedSafeS_pure_true _
private theorem hooksFSMultiDFBucketPaperMode_fgSafe {KC Γ CCoins T I KR RSt K SS RS M : Type} {ok : M → Bool}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K] (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs) (Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool) :
    MultiHooksFGSafe ok (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la) where
  startSend_fg _ _ t0 γ0 σ0 r0 := by
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]; rcases r0 with _ | c
    · refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT CCoins) fun coins => ?_
      refine guardedSafeS_bind_true (multiFGSafeS_rootFSMultiDFBucketPaper prng Δbucket qep tL par t0 _ (cka.send γ0 coins).2.2 σ0) fun _ => ?_
      refine guardedSafeS_get_bind fun _ _ => ?_
      exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true _
    · simp only [pure_bind]
      refine guardedSafeS_bind_true (multiFGSafeS_rootFSMultiDFBucketPaper prng Δbucket qep tL par t0 _ (cka.send γ0 c).2.2 σ0) fun _ => ?_
      refine guardedSafeS_get_bind fun _ _ => ?_
      exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true _
  startRecv_fg _ _ t0 γ0 σ0 tn0 := by
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]; cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte]; refine guardedSafeS_get_bind fun _ _ => ?_; split
      · exact guardedSafeS_pure_true _
      · split
        · split
          · exact guardedSafeS_pure_true none
          · split
            · exact guardedSafeS_pure_true _
            · refine guardedSafeS_bind_true (multiFGSafeS_lookupMultiDFBucketF t0 (cka.receive γ0 tn0).2) fun _ => ?_
              refine guardedSafeS_get_bind fun _ _ => ?_
              exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true _
        · exact guardedSafeS_pure_true (some none)
    · simp only [↓reduceIte]; refine guardedSafeS_get_bind fun h _ => ?_; rcases h.cache t0 with _ | ⟨tCached, σc, kVal, optIdx⟩
      · dsimp only; split_ifs <;> exact guardedSafeS_pure_true _
      · dsimp only; by_cases ht : tCached = tn0
        · subst ht; simp only [↓reduceIte]; exact guardedSafeS_pure_true _
        · simp only [ht, ↓reduceIte]; split_ifs <;> exact guardedSafeS_pure_true _
  fsSend_fg _ _ _ ssv hdr m pair hm := by
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]; rcases ssv with ss | sIdx
    · refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩; rintro _ _ ⟨⟩; exact hfs ss hdr m hm
    · refine guardedSafeS_get_bind fun _ _ => ?_; split
      · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_corrupt sIdx) fun r => ?_
        rcases r with _ | _
        · simp only [pure_bind, Bool.not_false, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
        · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rcases pair with _ | ⟨m₀, m₁⟩
          · refine guardedSafeS_bind_and (multiFGSafeS_liftFSMultiDFBucket_transmit sIdx hdr m) fun e? he? => ?_
            rcases e? with _ | e
            · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
                guardedSafeS_pure _ fun _ _ => ⟨by rintro _ _ ⟨⟩; exact he? e rfl, trivial⟩
          · refine guardedSafeS_bind_and (multiFGSafeS_liftFSMultiDFBucket_challenge sIdx hdr m₀ m₁) fun e? he? => ?_
            rcases e? with _ | e
            · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
                guardedSafeS_pure _ fun _ _ => ⟨by rintro _ _ ⟨⟩; exact he? e rfl, trivial⟩
      · simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rcases pair with _ | ⟨m₀, m₁⟩
        · refine guardedSafeS_bind_and (multiFGSafeS_liftFSMultiDFBucket_transmit sIdx hdr m) fun e? he? => ?_
          rcases e? with _ | e
          · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
          · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
              guardedSafeS_pure _ fun _ _ => ⟨by rintro _ _ ⟨⟩; exact he? e rfl, trivial⟩
        · refine guardedSafeS_bind_and (multiFGSafeS_liftFSMultiDFBucket_challenge sIdx hdr m₀ m₁) fun e? he? => ?_
          rcases e? with _ | e
          · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
          · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
              guardedSafeS_pure _ fun _ _ => ⟨by rintro _ _ ⟨⟩; exact he? e rfl, trivial⟩
  fsRecv_fg _ _ _ rsv hdr e rec he := by
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]; rcases rsv with rs | sIdx
    · exact guardedSafeS_pure_true _
    · refine guardedSafeS_get_bind fun _ _ => ?_; split
      · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_corrupt sIdx) fun r => ?_
        rcases r with _ | _
        · simp only [pure_bind, Bool.not_false, ↓reduceIte]; exact guardedSafeS_pure_true none
        · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; split_ifs
          · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_deliver sIdx hdr e) fun res => ?_
            rcases res with _ | (_ | ⟨_, mo'⟩)
            · exact guardedSafeS_pure_true none
            · exact guardedSafeS_pure_true (some none)
            · dsimp only; refine guardedSafeS_get_bind fun _ _ => ?_; split_ifs
              · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true none
              · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
                rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
          · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_inject sIdx hdr e he) fun res => ?_
            rcases res with _ | (_ | ⟨_, mo'⟩)
            · exact guardedSafeS_pure_true none
            · exact guardedSafeS_pure_true (some none)
            · dsimp only; refine guardedSafeS_get_bind fun _ _ => ?_; split_ifs
              · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true none
              · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
                rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
      · simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; split_ifs
        · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_deliver sIdx hdr e) fun res => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact guardedSafeS_pure_true none
          · exact guardedSafeS_pure_true (some none)
          · dsimp only; refine guardedSafeS_get_bind fun _ _ => ?_; split_ifs
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true none
            · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
              rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
        · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_inject sIdx hdr e he) fun res => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact guardedSafeS_pure_true none
          · exact guardedSafeS_pure_true (some none)
          · dsimp only; refine guardedSafeS_get_bind fun _ _ => ?_; split_ifs
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true none
            · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
              rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
  commit_fg _ _ _ new := guardedSafeS_pure_true (some new)
  reveal_fg ctx P vp := by
    have hRev : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
        ((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).reveal ctx P vp) := by
      dsimp only [hooksFSMultiDFBucketPaper]; rcases vp.vS with _ | (_ | sIdx)
      · simp only [pure_bind]; split_ifs <;> exact guardedSafeS_pure_true _
      · simp only [pure_bind]; split_ifs <;> exact guardedSafeS_pure_true _
      · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_corrupt sIdx) fun o => ?_
        rcases o with _ | _
        · simp only [pure_bind]; exact guardedSafeS_pure_true none
        · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          simp only [pure_bind]; split_ifs <;> exact guardedSafeS_pure_true _
    dsimp only [hooksFSMultiDFBucketPaperMode]; cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs
      · exact guardedSafeS_pure_true none
      · exact hRev
    · exact hRev
private theorem multiFGSafeS_initFSMultiDFBucketPaper {KC Γ CCoins T I KR RSt K SS RS M : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K] (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (lam : I) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par) := by
  unfold initFSMultiDFBucketPaper
  refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT KR) fun kr => ?_
  refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT KC) fun _ => ?_
  refine guardedSafeS_bind_true (multiFGSafeS_rootFSMultiDFBucketPaper prng Δbucket qep tL par 0 false lam (prng.init kr)) fun _ => ?_
  refine guardedSafeS_get_bind fun _ _ => ?_
  exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ => guardedSafeS_pure_true _
private theorem guardedMultiInjectShort_of_raw {Pt : Type} {ℓ : ℕ} (c : Computational.Proofs.E2E.SessionAuthBridge.MultiSessPubFsAdv Pt ℓ)
    (h : GuardedSafePost multiRespShortRaw multiInjectLongRaw (fun _ => True) c) : GuardedMultiInjectShort c := by
  induction h with
  | pure _ => exact GuardedSafePost.pure trivial
  | @query_bind q _ hnb _ ih =>
    rcases q with u | ⟨s, ((((_ | _) | _) | _) | _) | ⟨_, _, _⟩⟩ <;>
      exact GuardedSafePost.query_bind hnb fun r hr => ih r hr
private theorem lFS_fsSendShort_atomic {Pt : Type} (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :
    FsSendShort (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) := by
  intro ss hdr m hm
  exact lFS_fsSendShort C protoSignalCodec signalEncodeFits32_proto ℓ (by omega) encT idOf
    maxForwardJumps ss hdr m (atomicShortPubB_imp_shortB hm)
private theorem redFSAuthDFPaperMultiBucketMode_guardedMultiInjectShort {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (L : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool) (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) (hg : GuardedSMDFShort A) : GuardedMultiInjectShort
      (redFSAuthDFPaperMultiBucketMode L (dhScheme Dh) (rootPRNG C.F encPt) (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep gMain la tL par A) := by
  refine guardedMultiInjectShort_of_raw _ ?_
  let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  have hSpec := hooksFSMultiDFBucketPaperMode_fgSafe L (dhScheme Dh) (rootPRNG C.F encPt) fs
    (lFS_fsSendShort_atomic C ℓ hℓ encT idOf) Δcka Δbucket qep gMain tL par la
  have hA := hg.and_isQueryBoundP hsh
  unfold redFSAuthDFPaperMultiBucketMode redFSAuthDFPaperMultiBucketModeGen engRunDFPaperBucketMode implEDFPaperBucketMode; rw [bind_assoc]
  refine (multiFGSafeS_initFSMultiDFBucketPaper L (dhScheme Dh) (rootPRNG C.F encPt) fs lam
    Δbucket qep tL par {} trivial).bind fun ⟨vs, h⟩ _ => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · simp only [pure_bind]; exact GuardedSafePost.pure trivial
  · simp only [bind_assoc]
    let rawImpl := implEDFPaperBucketRaw
      (hooksFSMultiDFBucketPaperMode L (dhScheme Dh) (rootPRNG C.F encPt) fs Δcka Δbucket qep gMain tL par la)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
    let es₀ : EState _ (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × E₀)
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt E₀) :=
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
    refine (GuardedSafePost.simulateQ_run (I := fun _ => True) hA ?_ (s := (es₀, none)) trivial).bind
      fun _ _ => GuardedSafePost.pure trivial
    intro qt hpt ⟨s, winEp⟩ _
    have hstep : GuardedSafePost multiRespShortRaw multiInjectLongRaw
        (fun r => smDFRespShort qt r.1 ∧ True) ((rawImpl qt).run s) := by
      rcases qt with u | (tr | qdf)
      · dsimp only [rawImpl, implEDFPaperBucketRaw]; exact (multiFGSafeS_coinsE u s trivial).mono fun _ _ => ⟨trivial, trivial⟩
      · rcases tr with ((((q | q) | q) | q) | P)
        · have hok_q : atomicShortPubB q.2.1.1 = true := by
            have hnb : ¬ badSendMsgDF (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
                (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
                (.inr (.inl (.inl (.inl (.inl (.inl q)))))) = true := fun hb => hpt (Or.inr hb)
            simpa [badSendMsgDF] using hnb
          dsimp only [rawImpl, implEDFPaperBucketRaw]; exact multiFGSafeS_transmitEBucket hSpec (2 + Δcka) qep q hok_q s trivial
        · dsimp only [rawImpl, implEDFPaperBucketRaw]; exact multiFGSafeS_challEBucket q s trivial
        · dsimp only [rawImpl, implEDFPaperBucketRaw]
          exact (multiFGSafeS_deliverE hSpec fs.maxSkip _ q
            (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono fun _ _ => ⟨trivial, trivial⟩
        · dsimp only [rawImpl, implEDFPaperBucketRaw]
          exact (multiFGSafeS_injectE hSpec (2 + Δcka) qep _ q
            (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono fun _ _ => ⟨trivial, trivial⟩
        · dsimp only [rawImpl, implEDFPaperBucketRaw]; exact (multiFGSafeS_corrEPaperBucket hSpec P s trivial).mono fun _ _ => ⟨trivial, trivial⟩
      · dsimp only [rawImpl, implEDFPaperBucketRaw]
        exact (multiFGSafeS_deliverForgeE hSpec (2 + Δcka) qep _ qdf
          (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono fun _ _ => ⟨trivial, trivial⟩
    unfold withWinEpDFMode; cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte]; dsimp only [StateT.run_mk]; exact hstep.bind fun ⟨r', _⟩ hr => GuardedSafePost.pure ⟨hr.1, trivial⟩
    · simp only [↓reduceIte]; unfold withWinEpDF; dsimp only [StateT.run_mk]; exact hstep.bind fun ⟨r', _⟩ hr => GuardedSafePost.pure ⟨hr.1, trivial⟩
end ModeShortHelpers
section LibsignalBridges
variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
/-- `TwoModeMultiSessBounds` (`M = ((qep + 2) - healEpoch tL) * q`) for `multiSessPubToAD` on
`redFSAuthDFPaperMultiBucket`. -/
theorem redFSAuthDFPaperMultiBucket_twoModeMultiSessBounds
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka Δbucket qep : ℕ) (hΔb : 2 ≤ Δbucket := by omega) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A) :
    TwoModeMultiSessBounds maxForwardJumps (2 * q)
      (((qep + 2) - healEpoch tL) * q) q
      (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la tL par A)) := by
  have hComb : ∀ la,
      (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la tL par A).IsQueryBoundP
        (fun x => badBucketQuery q qep tL
          (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) x = true) 0 :=
    fun la => redFSAuthDFPaperMultiBucket_badBucketQuery_zero
      (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam
      (fun _ hm => Computational.Proofs.ReductionDsl.Fig8Atomic.atomicShortPubB_imp_shortB hm)
      q Δcka Δbucket qep hΔb tL par la A hq hsh
  refine
    { offRange := fun la _ => multiSessPubToAD_offRange protoSignalCodec _ (((qep + 2) - healEpoch tL) * q)
        ((hComb la).of_imp fun x hx => by
          rcases x with _ | ⟨sIdx, q₀⟩; · simp [sessOffRange] at hx
          · simp only [sessOffRange] at hx; simp [badBucketQuery, hx])
      decBound := fun la _ => multiSessPubToAD_decBound protoSignalCodec _ q
        (Computational.Proofs.E2E.SessionAuthMultiDec.redFSAuthDFPaperMultiBucket_dec_onAnySess (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka Δbucket qep tL par la A hq)
      shortAD := fun la _ => multiSessPubToAD_shortAD protoSignalCodec _
        ((hComb la).of_imp fun x hx => by
          rcases x with _ | ⟨sIdx, q₀⟩; · simp [onAnySess] at hx
          · have hbad : encBadMsg (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
                (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
                (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) (.inr q₀) = true := by
              rcases q₀ with (((((⟨_, _⟩ | ⟨_, _, _⟩) | _) | _) | _) | _) <;> exact hx
            simp [badBucketQuery, hbad])
      guardedShort := fun la _ => multiSessPubToAD_guardedShort protoSignalCodec _
        (Computational.Proofs.E2E.SessionAuthMultiShort.redFSAuthDFPaperMultiBucket_guardedMultiInjectShort (q + 1) C Dh encPt encT idOf lam hℓ Δcka Δbucket qep tL par la A hsh hg)
      oneADClass := fun la j _ => ⟨healEpoch tL + j / q, multiSessPubToAD_oneADClass protoSignalCodec _ j (healEpoch tL + j / q)
        ((hComb la).of_imp fun x hx => by
          rcases x with _ | ⟨sIdx, q₀⟩; · simp [onSess] at hx
          · simp only [onSess, Bool.and_eq_true, decide_eq_true_eq] at hx; rcases hx with ⟨rfl, hout⟩
            have hany : onAnySess (fsOutsideClass (fun h : Header Pt => h.1) (healEpoch tL + sIdx / q)) (.inr ⟨sIdx, q₀⟩) = true := hout
            rw [onAnySess_fsOutsideClass_inr_spec (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
              (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))] at hany
            simp [badBucketQuery, hany])⟩ }

/-- `TwoModeMultiSessBounds` (`M = ((qep + 2) - healEpoch tL) * q`) for `multiSessPubToAD` on
each `gMain : Bool` branch of `redFSAuthDFPaperMultiBucketMode`. -/
theorem redFSAuthDFPaperMultiBucketMode_twoModeMultiSessBounds
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka Δbucket qep : ℕ) (hΔb : 2 ≤ Δbucket := by omega)
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A) :
    TwoModeMultiSessBounds maxForwardJumps (2 * q)
      (((qep + 2) - healEpoch tL) * q) q
      (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh)
            (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
            lam Δcka Δbucket qep gMain la tL par A)) := by
  have hComb : ∀ la,
      (redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep gMain la tL par A).IsQueryBoundP
        (fun x => badBucketQuery q qep tL
          (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) x = true) 0 :=
    fun la => redFSAuthDFPaperMultiBucketMode_badBucketQuery_zero
      (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam
      (fun _ hm => Computational.Proofs.ReductionDsl.Fig8Atomic.atomicShortPubB_imp_shortB hm)
      q Δcka Δbucket qep hΔb gMain tL par la A hq hsh
  refine
    { offRange := fun la _ => multiSessPubToAD_offRange protoSignalCodec _ (((qep + 2) - healEpoch tL) * q)
        ((hComb la).of_imp fun x hx => by
          rcases x with _ | ⟨sIdx, q₀⟩; · simp [sessOffRange] at hx
          · simp only [sessOffRange] at hx; simp [badBucketQuery, hx])
      decBound := fun la _ => multiSessPubToAD_decBound protoSignalCodec _ q
        (redFSAuthDFPaperMultiBucketMode_dec_onAnySess (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka Δbucket qep gMain tL par la A hq)
      shortAD := fun la _ => multiSessPubToAD_shortAD protoSignalCodec _
        ((hComb la).of_imp fun x hx => by
          rcases x with _ | ⟨sIdx, q₀⟩; · simp [onAnySess] at hx
          · have hbad : encBadMsg (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
                (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
                (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) (.inr q₀) = true := by
              rcases q₀ with (((((⟨_, _⟩ | ⟨_, _, _⟩) | _) | _) | _) | _) <;> exact hx
            simp [badBucketQuery, hbad])
      guardedShort := fun la _ => multiSessPubToAD_guardedShort protoSignalCodec _
        (redFSAuthDFPaperMultiBucketMode_guardedMultiInjectShort (q + 1) C Dh encPt encT idOf lam hℓ
          Δcka Δbucket qep gMain tL par la A hsh hg)
      oneADClass := fun la j _ => ⟨healEpoch tL + j / q, multiSessPubToAD_oneADClass protoSignalCodec _ j (healEpoch tL + j / q)
        ((hComb la).of_imp fun x hx => by
          rcases x with _ | ⟨sIdx, q₀⟩; · simp [onSess] at hx
          · simp only [onSess, Bool.and_eq_true, decide_eq_true_eq] at hx; rcases hx with ⟨rfl, hout⟩
            have hany : onAnySess (fsOutsideClass (fun h : Header Pt => h.1) (healEpoch tL + sIdx / q)) (.inr ⟨sIdx, q₀⟩) = true := hout
            rw [onAnySess_fsOutsideClass_inr_spec (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
              (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))] at hany
            simp [badBucketQuery, hany])⟩ }

/-- Uniform epoch-class (`k₀ := healEpoch tL + j / q`, independent of `gMain : Bool`) single-AD-class
query bound on `multiSessPubToAD` of `redFSAuthDFPaperMultiBucketMode`, matching the `honeAD`
premise of `localAuthDFPaperBucket_main_add_forgedHdr_le_fsAuthCompBoundWith_of_branches`. -/
theorem redFSAuthDFPaperMultiBucketMode_oneADClass_uniform
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q Δcka Δbucket qep : ℕ) (hΔb : 2 ≤ Δbucket := by omega) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (la : Bool) (j : ℕ) :
    ∃ k₀ : ℕ, ∀ gMain : Bool,
      (multiSessPubToAD protoSignalCodec
        (redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh)
          (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          lam Δcka Δbucket qep gMain la tL par A)).IsQueryBoundP
        (fun t => onSess (fsOutsideClass
          (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true) 0 := by
  refine ⟨healEpoch tL + j / q, fun gMain => ?_⟩
  have hComb := redFSAuthDFPaperMultiBucketMode_badBucketQuery_zero
    (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam
    (fun _ hm => Computational.Proofs.ReductionDsl.Fig8Atomic.atomicShortPubB_imp_shortB hm)
    q Δcka Δbucket qep hΔb gMain tL par la A hq hsh
  exact multiSessPubToAD_oneADClass protoSignalCodec _ j (healEpoch tL + j / q)
    (hComb.of_imp fun x hx => by
      rcases x with _ | ⟨sIdx, q₀⟩; · simp [onSess] at hx
      · simp only [onSess, Bool.and_eq_true, decide_eq_true_eq] at hx; rcases hx with ⟨rfl, hout⟩
        have hany : onAnySess (fsOutsideClass (fun h : Header Pt => h.1) (healEpoch tL + sIdx / q)) (.inr ⟨sIdx, q₀⟩) = true := hout
        rw [onAnySess_fsOutsideClass_inr_spec (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))] at hany
        simp [badBucketQuery, hany])

theorem twoModeMultiSessBounds_coinBool {α : Type} {B qR M qd : ℕ}
    (Adv : Bool → Bool → α → MultiSessFsAdv Pt ℓ)
    (hTrue : TwoModeMultiSessBounds B qR M qd (Adv true))
    (hFalse : TwoModeMultiSessBounds B qR M qd (Adv false))
    (honeAD : ∀ la j o, ∃ k₀ : ℕ, ∀ gMain,
      (Adv gMain la o).IsQueryBoundP
        (fun t => onSess (fsOutsideClass (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true) 0) :
    TwoModeMultiSessBounds B qR M qd (fun la o => sampleT Bool >>= fun gMain => Adv gMain la o) where
  offRange la o := sampleT_bind_isQueryBoundP_aux _ (fun _ => by simp [sessOffRange]) _
    fun gMain => by cases gMain; exact hFalse.offRange la o; exact hTrue.offRange la o
  decBound la o := sampleT_bind_isQueryBoundP_aux _ (fun _ => by simp [onAnySess]) _
    fun gMain => by cases gMain; exact hFalse.decBound la o; exact hTrue.decBound la o
  shortAD la o := sampleT_bind_isQueryBoundP_aux _ (fun _ => by simp [onAnySess]) _
    fun gMain => by cases gMain; exact hFalse.shortAD la o; exact hTrue.shortAD la o
  guardedShort la o := sampleT_guardedMultiInjectShort_bind_aux _
    fun gMain => by cases gMain; exact hFalse.guardedShort la o; exact hTrue.guardedShort la o
  oneADClass la j o := by
    obtain ⟨k₀, hk₀⟩ := honeAD la j o
    exact ⟨k₀, sampleT_bind_isQueryBoundP_aux _ (fun _ => by simp [onSess]) _ (hk₀ ·)⟩

theorem multiSessRealWinProb_add_eq_two_mul_coinBool
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Adv : Bool → Bool → MultiSessFsAdv Pt ℓ) (la : Bool) :
    multiSessRealWinProb C ℓ encT idOf (Adv true) la +
      multiSessRealWinProb C ℓ encT idOf (Adv false) la =
    2 * multiSessRealWinProb C ℓ encT idOf
      (fun la' => sampleT Bool >>= fun gMain => Adv gMain la') la := by
  unfold multiSessRealWinProb
  rw [simulateQ_bind, StateT.run_bind, simulateQ_sessLift_sampleT_run_eq_aux]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]; symm
  exact two_mul_evalDist_unif_bool_bind_aux (fun gMain =>
    (simulateQ (sessLift (lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) (Adv gMain la)).run (fun _ => none) >>= fun x => pure x.1)

theorem multiSessEndWinProb_coinBool_eq_zero
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ)
    (Adv : Bool → Bool → MultiSessFsAdv Pt ℓ) (la : Bool)
    (hTrue : multiSessEndWinProb C ℓ encT idOf qR (Adv true) la = 0)
    (hFalse : multiSessEndWinProb C ℓ encT idOf qR (Adv false) la = 0) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' => sampleT Bool >>= fun gMain => Adv gMain la') la = 0 := by
  have h2 : 2 * multiSessEndWinProb C ℓ encT idOf qR
      (fun la' => sampleT Bool >>= fun gMain => Adv gMain la') la = 0 := by
    unfold multiSessEndWinProb at *; dsimp only at *
    rw [simulateQ_bind, StateT.run_bind, simulateQ_sessLift_sampleT_run_eq_aux]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at *
    rw [two_mul_evalDist_unif_bool_bind_aux, hTrue, hFalse, add_zero]
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
end LibsignalBridges
end
end Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti
