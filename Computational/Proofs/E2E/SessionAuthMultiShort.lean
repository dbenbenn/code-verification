/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.FSAEADRed
/-! # `GuardedMultiInjectShort` Bounds for Stage-2 Multi-Session Reductions -/
set_option autoImplicit false
namespace Computational.Proofs.E2E.SessionAuthMultiShort
public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.FSAEAD (transmitQuery challengeQuery corruptSenderQuery deliverQuery injectQuery)
open _root_.CryptoGames.GuardedSafe (GuardedSafePost GuardedSafeS guardedSafeS_pure
  guardedSafeS_pure_true guardedSafeS_get_bind guardedSafeS_bind_true guardedSafeS_bind_and
  guardedSafeS_set_true guardedSafeS_modify_true guardedSafeS_lift_true)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (Config)
open _root_.CryptoGames.SM.Engine (Hooks Policy EState VP Ctx HM TComp liftH abortE
  coinsE vSend vRecv commitE transmitE challE deliverE injectE injectEGen deliverForgeEGen)
open _root_.CryptoGames.SM.Construction (Header Mode sampleT FSMultiSpec FSMultiState hooksFSMulti
  rootFSMulti initFSMultiRaw liftFSMulti lookupMultiF regSessMulti regSessOptMulti
  FSMultiDFBucketState hooksFSMultiDFBucketPaper rootFSMultiDFBucketPaper initFSMultiDFBucketPaper
  liftFSMultiDFBucket lookupMultiDFBucketF bucketAuthCfgGen runFSMultiDFPaper
  redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketGen)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF implEDFPaper
  implEDFShiftedPaperGen engRunDFPaperBucket implEDFPaperBucket implEDFPaperBucketRaw
  transmitEBucket challEBucket corrEPaperBucket corrEPaper corrEShiftedPaper
  deliverForgeE deliverForgeEB1 injectEB1 withWinEpDF)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart
  LibsignalCiphertextWithSalt32 lFS fsRespShort fsInjectLong)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession (signalEncodeFits32_proto)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (badSendMsgDF SendMsgsOkDF smDFRespShort
  GuardedSMDFShort)
open _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed (FsSendShort lFS_fsSendShort)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open _root_.CryptoVerification.E2E.Signed.SessionWireQueries (GuardedMultiInjectShort)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  runFSMultiDFShiftedPaper redFSAuthDFShiftedPaperMultiGen)

private theorem query_eq_liftM {ι : Type} {spec : OracleSpec.{0, 0} ι} (t : spec.Domain) :
    (query (spec := spec) t : OracleComp spec (spec.Range t)) = liftM (spec.query t) := rfl

/-! ## 2. `GuardedMultiInjectShort` Bounds via Generic `MultiHooksFGSafe` -/

section GuardedShort

local notation "E₀" => ℕ × LibsignalCiphertextWithSalt32

private def multiRespShortRaw {SS RS AD Msg : Type} :
    (t : (unifSpec + OracleSpec.sigma (fun _ : ℕ => _root_.CryptoGames.FSAEAD.spec SS RS AD Msg E₀)).Domain) →
    (unifSpec + OracleSpec.sigma (fun _ : ℕ => _root_.CryptoGames.FSAEAD.spec SS RS AD Msg E₀)).Range t → Prop
  | .inr ⟨_, o⟩, r => fsRespShort (SS := SS) (RS := RS) (AD := AD) (Msg := Msg) (.inr o) r
  | .inl _, _ => True

private def multiInjectLongRaw {SS RS AD Msg : Type} :
    (unifSpec + OracleSpec.sigma (fun _ : ℕ => _root_.CryptoGames.FSAEAD.spec SS RS AD Msg E₀)).Domain → Prop
  | .inr ⟨_, o⟩ => fsInjectLong (SS := SS) (RS := RS) (AD := AD) (Msg := Msg) (.inr o)
  | .inl _ => False

private abbrev MultiFGSafeS {SS RS T M σ α : Type} (P : α → Prop)
    (x : StateT σ (TComp (FSMultiSpec SS RS T M E₀)) α) : Prop :=
  GuardedSafeS (multiRespShortRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
    (multiInjectLongRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
    (fun _ => True) (fun a _ => P a ∧ True) x

private abbrev MultiFGSafeSTrue {SS RS T M σ α : Type}
    (x : StateT σ (TComp (FSMultiSpec SS RS T M E₀)) α) : Prop :=
  GuardedSafeS (multiRespShortRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
    (multiInjectLongRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
    (fun _ => True) (fun _ _ => True) x

private theorem multiFGSafePost_sampleT {SS RS T M : Type} (α : Type) [SampleableType α] :
    GuardedSafePost (multiRespShortRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (multiInjectLongRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (fun _ => True) (sampleT (tspec := FSMultiSpec SS RS T M E₀) α) :=
  GuardedSafePost.liftComp_unif (fun _ => not_false) ($ᵗ α)

private theorem multiFGSafeS_lift_sampleT {SS RS T M σ : Type} (α : Type) [SampleableType α] :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) (σ := σ)
      (StateT.lift (sampleT (tspec := FSMultiSpec SS RS T M E₀) α)) :=
  guardedSafeS_lift_true (multiFGSafePost_sampleT α)

private structure MultiHooksFGSafe
    {HS Γ T RSt SS RS M CCoins Γv Sv SSv RSv : Type}
    (ok : M → Bool)
    (hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv) : Prop where
  startSend_fg : ∀ ctx P t γ σ r, MultiFGSafeSTrue (hk.startSend ctx P t γ σ r)
  startRecv_fg : ∀ ctx P t γ σ Tn, MultiFGSafeSTrue (hk.startRecv ctx P t γ σ Tn)
  fsSend_fg : ∀ ctx P t ssv h m pair, ok m = true →
    MultiFGSafeS (fun res => ∀ ssv' (e : E₀), res = some (ssv', e) → e.2.1.1.length + 8 < 2 ^ 32)
      (hk.fsSend ctx P t ssv h m pair)
  fsRecv_fg : ∀ ctx P t rsv h (e : E₀) rec, e.2.1.1.length < 2 ^ 32 →
    MultiFGSafeSTrue (hk.fsRecv ctx P t rsv h e rec)
  reveal_fg : ∀ ctx P vp, MultiFGSafeSTrue (hk.reveal ctx P vp)
  commit_fg : ∀ ctx P old new, MultiFGSafeSTrue (hk.commit ctx P old new)

private theorem multiFGSafeS_liftH_true {SS RS T M HS Γv Sv SSv RSv α : Type}
    {x : HM (FSMultiSpec SS RS T M E₀) HS α}
    (hx : MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) x) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftH x : StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E₀) HS)
        (TComp (FSMultiSpec SS RS T M E₀)) α) := fun es _ => by
  unfold liftH
  exact (hx es.h trivial).bind fun _ _ => GuardedSafePost.pure trivial

private theorem multiFGSafeS_liftH_and {SS RS T M HS Γv Sv SSv RSv α : Type} {C : α → Prop}
    {x : HM (FSMultiSpec SS RS T M E₀) HS α}
    (hx : MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M) C x) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M) C
      (liftH x : StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E₀) HS)
        (TComp (FSMultiSpec SS RS T M E₀)) α) := fun es _ => by
  unfold liftH
  exact (hx es.h trivial).bind fun p hp => GuardedSafePost.pure ⟨hp.1, trivial⟩

private theorem multiFGSafeS_abortE {SS RS T M HS Γv Sv SSv RSv : Type} :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (abortE : StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E₀) HS)
        (TComp (FSMultiSpec SS RS T M E₀)) Unit) := by
  unfold abortE
  exact guardedSafeS_modify_true _ fun _ _ => trivial

private theorem multiFGSafeS_coinsE {SS RS T M HS Γv Sv SSv RSv : Type} (u : ℕ) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (coinsE u : StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E₀) HS)
        (TComp (FSMultiSpec SS RS T M E₀)) _) :=
  fun _ _ => (GuardedSafePost.query not_false).bind fun _ _ => GuardedSafePost.pure trivial

private theorem multiFGSafeS_commitE {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk)
    (s : Ctx Γv T Sv SSv RSv M E₀) (P : Party)
    (old new : VP Γv T Sv SSv RSv) (pos : _root_.CryptoGames.SM.Pos) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (commitE hk s P old new pos) := by
  unfold commitE
  refine guardedSafeS_bind_true (multiFGSafeS_liftH_true (hSpec.commit_fg _ P old new)) fun res => ?_
  cases res with
  | none => exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
  | some _ => exact guardedSafeS_pure_true _

private theorem multiFGSafeS_vSend {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk)
    (ctx : Ctx Γv T Sv SSv RSv M E₀) (P : Party) (s : VP Γv T Sv SSv RSv)
    (m : M) (pair : Option (M × M)) (r : Option CCoins) (hm : ok m = true) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ vp' (c : Header T × E₀), res = some (vp', c) → c.2.2.1.1.length + 8 < 2 ^ 32)
      (vSend hk ctx P s m pair r) := by
  unfold vSend
  have hdef : (default : E₀).2.1.1.length + 8 < 2 ^ 32 := by decide
  by_cases h1 : s.id.sendsIn (s.tcur + 1) = true
  · simp only [h1, ↓reduceIte]
    refine guardedSafeS_bind_true (hSpec.startSend_fg ctx P (s.tcur + 1) s.γ s.root r) fun res => ?_
    rcases res with _ | ⟨γ', T', σ', ss⟩
    · simp only [pure_bind]; exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
    · simp only [pure_bind]
      refine guardedSafeS_bind_and
        (hSpec.fsSend_fg ctx P (s.tcur + 1) ss (s.tcur + 1, some T') m pair hm) fun res' hres' => ?_
      rcases res' with _ | ⟨v', e⟩
      · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
      · refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
        rintro _ _ ⟨⟩; exact hres' v' e rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind]
    cases s.vS with
    | none =>
      refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
      rintro _ _ ⟨⟩; exact hdef
    | some v =>
      refine guardedSafeS_bind_and
        (hSpec.fsSend_fg ctx P s.tcur v (s.tcur, s.curCkaMsg) m pair hm) fun res' hres' => ?_
      rcases res' with _ | ⟨v', e⟩
      · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
      · refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
        rintro _ _ ⟨⟩; exact hres' v' e rfl

private theorem multiFGSafeS_vRecv {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk)
    (ctx : Ctx Γv T Sv SSv RSv M E₀) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E₀) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E₀)))
    (hc : c.2.2.1.1.length < 2 ^ 32) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (vRecv hk ctx P s c rec) := by
  unfold vRecv
  dsimp only
  split
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
    · simp only [pure_bind]
      cases s.vR c.1.1 with
      | none => exact guardedSafeS_pure_true (some none)
      | some v =>
        refine guardedSafeS_bind_true (hSpec.fsRecv_fg ctx P c.1.1 v c.1 c.2 rec hc) fun res' => ?_
        rcases res' with _ | (_ | ⟨v', i, m⟩) <;> exact guardedSafeS_pure_true _

private theorem multiFGSafeS_transmitE {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (Δ qep : ℕ) (π : Policy)
    (q : Party × M × Option CCoins) (hok : ok q.2.1 = true) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × E₀, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (transmitE hk Δ qep π q) := by
  rcases q with ⟨P, m, r⟩
  unfold transmitE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt Δ qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      by_cases h2 : π.leakDoom es.g s₁ = true
      · simp only [h2, ↓reduceIte]
        exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ =>
          guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine guardedSafeS_bind_and
          (multiFGSafeS_liftH_and (multiFGSafeS_vSend hSpec s₁ P (s₁.st P) m none r hok))
          fun res hres => ?_
        rcases res with _ | ⟨st', c⟩
        · exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ =>
            guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          refine guardedSafeS_pure (some c) fun _ _ => ⟨?_, trivial⟩
          rintro _ ⟨⟩; exact hres st' c rfl

private theorem multiFGSafeS_transmitEBucket {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (Δ qep : ℕ)
    (q : Party × M × Option CCoins) (hok : ok q.2.1 = true) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × E₀, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (transmitEBucket hk Δ qep q) := by
  rcases q with ⟨P, m, r⟩
  unfold transmitEBucket
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt Δ qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      refine guardedSafeS_bind_and
        (multiFGSafeS_liftH_and (multiFGSafeS_vSend hSpec s₁ P (s₁.st P) m none r hok))
        fun res hres => ?_
      rcases res with _ | ⟨st', c⟩
      · exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ =>
          guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
        refine guardedSafeS_pure (some c) fun _ _ => ⟨?_, trivial⟩
        rintro _ ⟨⟩; exact hres st' c rfl

private theorem multiFGSafeS_challE {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (Δ qep : ℕ) (cfg : Config M) (hcm : ∀ t, cfg.challMsg t = none)
    (π : Policy) (q : Party × M × M × Option CCoins)
    (hok₀ : ok q.2.1 = true) (hok₁ : ok q.2.2.1 = true) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × E₀, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (challE hk Δ qep cfg π q) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt Δ qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      by_cases h2 : (!s₁.safeCh Δ P || !cfg.challAllowedIn (s₁.epoch P)) = true
      · simp only [h2, ↓reduceIte]; exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : π.leakDoom es.g s₁ = true
        · simp only [h3, ↓reduceIte]
          exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ =>
            guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          have hm : ok ((cfg.challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀)) = true := by
            rw [hcm]; dsimp only [Option.getD]; cases es.g.b <;> assumption
          refine guardedSafeS_bind_and
            (multiFGSafeS_liftH_and
              (multiFGSafeS_vSend hSpec s₁ P (s₁.st P) _ (some (m₀, m₁)) r hm))
            fun res hres => ?_
          rcases res with _ | ⟨st', c⟩
          · exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ =>
              guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
          · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            refine guardedSafeS_pure (some c) fun _ _ => ⟨?_, trivial⟩
            rintro _ ⟨⟩; exact hres st' c rfl

private theorem multiFGSafeS_challEBucket {SS RS T M HS CCoins Γv Sv SSv RSv : Type}
    (q : Party × M × M × Option CCoins) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × E₀, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (challEBucket q : StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E₀) HS)
        (TComp (FSMultiSpec SS RS T M E₀)) _) := by
  unfold challEBucket
  exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩

private theorem multiFGSafeS_deliverE {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (maxSkip : ℕ) (cfg : Config M)
    (q : Party × (Header T × E₀)) (hc : q.2.2.2.1.1.length < 2 ^ 32) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (deliverE hk maxSkip cfg q) := by
  rcases q with ⟨P, c⟩
  unfold deliverE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.inTransit P.other c with
    | none => exact guardedSafeS_pure_true none
    | some r =>
      refine guardedSafeS_bind_true
        (multiFGSafeS_liftH_true (multiFGSafeS_vRecv hSpec es.g P (es.g.st P) c (some r) hc))
        fun res => ?_
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
      · by_cases h2 : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r) = true
        · simp only [h2, ↓reduceIte]
          exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
            fun _ => guardedSafeS_pure_true _
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          exact guardedSafeS_pure_true _
      · refine guardedSafeS_bind_true (multiFGSafeS_commitE hSpec es.g P (es.g.st P) st' r.pos)
          fun s₁? => ?_
        rcases s₁? with _ | s₁
        · exact guardedSafeS_pure_true none
        · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
            fun _ => guardedSafeS_pure_true _

private theorem multiFGSafeS_injectEGen {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (b1 : Bool) (Δ qep tStar : ℕ) (cfg : Config M)
    (q : Party × (Header T × E₀)) (hc : q.2.2.2.1.1.length < 2 ^ 32) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (injectEGen b1 hk Δ qep tStar cfg q) := by
  rcases q with ⟨P, c⟩
  cases b1 <;> [unfold injectEGen injectE; unfold injectEGen injectEB1]
  all_goals
    dsimp only
    refine guardedSafeS_get_bind fun es _ => ?_
    split_ifs with h1
    · exact guardedSafeS_pure_true none
    · refine guardedSafeS_bind_true
        (multiFGSafeS_liftH_true (multiFGSafeS_vRecv hSpec es.g P (es.g.st P) c none hc))
        fun res => ?_
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
      · exact guardedSafeS_pure_true _
      · by_cases h2 : qep + 1 < t'
        · simp only [h2, ↓reduceIte]; exact guardedSafeS_pure_true _
        · simp only [h2, ↓reduceIte]
          split_ifs
          · refine guardedSafeS_bind_true
              (multiFGSafeS_commitE hSpec es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
              fun s₁? => ?_
            rcases s₁? with _ | s₁
            · exact guardedSafeS_pure_true none
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                fun _ => guardedSafeS_pure_true _
          · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
              fun _ => guardedSafeS_pure_true _
          · exact guardedSafeS_pure_true _

private theorem multiFGSafeS_deliverForgeEGen {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (b1 : Bool) (Δ qep tStar : ℕ) (cfg : Config M)
    (q : Party × (Header T × E₀) × (Header T × E₀)) (hc' : q.2.2.2.2.1.1.length < 2 ^ 32) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (deliverForgeEGen b1 hk Δ qep tStar cfg q) := by
  rcases q with ⟨P, c, c'⟩
  cases b1 <;> [unfold deliverForgeEGen deliverForgeE; unfold deliverForgeEGen deliverForgeEB1]
  all_goals
    dsimp only
    refine guardedSafeS_get_bind fun es _ => ?_
    by_cases h1 : (es.abort || es.g.win) = true
    · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure_true none
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      cases es.g.inTransit P.other c with
      | none => exact guardedSafeS_pure_true none
      | some r =>
        by_cases h2 :
            ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
        · simp only [h2, ↓reduceIte]; exact guardedSafeS_pure_true none
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          refine guardedSafeS_bind_true
            (multiFGSafeS_liftH_true (multiFGSafeS_vRecv hSpec es.g P (es.g.st P) c' none hc'))
            fun res => ?_
          rcases res with _ | (_ | ⟨st', t', i', m'⟩)
          · exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
          · exact guardedSafeS_pure_true _
          · by_cases h3 : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
            · simp only [h3, ↓reduceIte]; exact guardedSafeS_pure_true _
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              split_ifs
              · refine guardedSafeS_bind_true
                  (multiFGSafeS_commitE hSpec es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
                  fun s₁? => ?_
                rcases s₁? with _ | s₁
                · exact guardedSafeS_pure_true none
                · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                    fun _ => guardedSafeS_pure_true _
              · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                  fun _ => guardedSafeS_pure_true _
              · exact guardedSafeS_pure_true _

private theorem multiFGSafeS_corrEPaper {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (π : Policy) (P : Party) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (corrEPaper hk π P) := by
  unfold corrEPaper
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P) = true
    · simp only [h2, ↓reduceIte]
      exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      refine guardedSafeS_bind_true
        (multiFGSafeS_liftH_true (hSpec.reveal_fg es.g P (es.g.st P))) fun res => ?_
      cases res with
      | none => exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
      | some st =>
        exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
          fun _ => guardedSafeS_pure_true (some st)

private theorem multiFGSafeS_corrEShiftedPaper {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (l : ℕ) (π : Policy) (P : Party) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (corrEShiftedPaper l hk π P) := by
  unfold corrEShiftedPaper
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowedPaper P) = true
  · simp only [h1, ↓reduceIte]; exact guardedSafeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 :
        (π.leakDoom es.g (_root_.CryptoGames.SM.Construction.DeliverForge.afterCorrShifted l es.g P) ||
          π.corrDoom es.g P) = true
    · simp only [h2, ↓reduceIte]
      exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      refine guardedSafeS_bind_true
        (multiFGSafeS_liftH_true (hSpec.reveal_fg es.g P (es.g.st P))) fun res => ?_
      cases res with
      | none => exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
      | some st =>
        exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
          fun _ => guardedSafeS_pure_true (some st)

private theorem multiFGSafeS_corrEPaperBucket {SS RS T M HS Γ RSt CCoins Γv Sv SSv RSv : Type}
    {ok : M → Bool}
    {hk : Hooks (FSMultiSpec SS RS T M E₀) HS Γ T RSt SS RS M E₀ CCoins Γv Sv SSv RSv}
    (hSpec : MultiHooksFGSafe ok hk) (P : Party) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (corrEPaperBucket hk P) := by
  unfold corrEPaperBucket
  refine guardedSafeS_get_bind fun es _ => ?_
  split
  · exact guardedSafeS_pure_true none
  · refine guardedSafeS_bind_true
      (multiFGSafeS_liftH_true (hSpec.reveal_fg es.g P (es.g.st P))) fun res => ?_
    cases res with
    | none => exact guardedSafeS_bind_true multiFGSafeS_abortE fun _ => guardedSafeS_pure_true none
    | some st =>
      exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
        fun _ => guardedSafeS_pure_true (some st)

private theorem multiFGSafeS_liftFSMulti_query {SS RS T M Sig K I : Type} (sIdx : ℕ)
    {q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E₀).Domain}
    (hq₀ : ¬ multiInjectLongRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (.inr ⟨sIdx, q₀⟩)) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun a => fsRespShort (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (.inr q₀) a)
      (liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (liftM (OracleSpec.query
          (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E₀) (.inr q₀)))) := fun h _ => by
  have hq : ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀)
      (Sig := Sig) (K := K) (I := I) sIdx (liftM (OracleSpec.query
        (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E₀) (.inr q₀)))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E₀)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    simp [liftFSMulti, StateT.run_lift]
  rw [hq]
  exact (GuardedSafePost.query hq₀).bind fun _ ha => GuardedSafePost.pure ⟨ha, trivial⟩

private theorem multiFGSafeS_liftFSMultiDFBucket_query {SS RS T M Sig K I : Type} (sIdx : ℕ)
    {q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E₀).Domain}
    (hq₀ : ¬ multiInjectLongRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (.inr ⟨sIdx, q₀⟩)) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun a => fsRespShort (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (.inr q₀) a)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (liftM (OracleSpec.query
          (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E₀) (.inr q₀)))) := fun h _ => by
  have hq : ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀)
      (Sig := Sig) (K := K) (I := I) sIdx (liftM (OracleSpec.query
        (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E₀) (.inr q₀)))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E₀)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hq]
  exact (GuardedSafePost.query hq₀).bind fun _ ha => GuardedSafePost.pure ⟨ha, trivial⟩

private theorem multiFGSafeS_liftFSMulti_transmit {SS RS T M Sig K I : Type}
    (sIdx : ℕ) (hdr : Header T) (m : M) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun a : Option E₀ => ∀ e, a = some e → e.2.1.1.length + 8 < 2 ^ 32)
      (liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)) := fun h _ => by
  unfold transmitQuery; rw [query_eq_liftM]
  exact (multiFGSafeS_liftFSMulti_query (q₀ := .inl (.inl (.inl (.inl (.inl (hdr, m))))))
    sIdx not_false h trivial).mono fun ⟨a, _⟩ ⟨ha, _⟩ =>
    ⟨fun e he => by subst he; simpa [fsRespShort] using ha, trivial⟩

private theorem multiFGSafeS_liftFSMulti_challenge {SS RS T M Sig K I : Type}
    (sIdx : ℕ) (hdr : Header T) (m₀ m₁ : M) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun a : Option E₀ => ∀ e, a = some e → e.2.1.1.length + 8 < 2 ^ 32)
      (liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)) := fun h _ => by
  unfold challengeQuery; rw [query_eq_liftM]
  exact (multiFGSafeS_liftFSMulti_query (q₀ := .inl (.inl (.inl (.inl (.inr (hdr, m₀, m₁))))))
    sIdx not_false h trivial).mono fun ⟨a, _⟩ ⟨ha, _⟩ =>
    ⟨fun e he => by subst he; simpa [fsRespShort] using ha, trivial⟩

private theorem multiFGSafeS_liftFSMulti_corrupt {SS RS T M Sig K I : Type} (sIdx : ℕ) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (corruptSenderQuery (SenderState := SS) (ReceiverState := RS)
          (AssocData := Header T) (Message := M) (Ciphertext := E₀))) := fun h _ => by
  unfold corruptSenderQuery; rw [query_eq_liftM]
  exact (multiFGSafeS_liftFSMulti_query (q₀ := .inl (.inl (.inl (.inr ()))))
    sIdx not_false h trivial).mono fun _ _ => trivial

private theorem multiFGSafeS_liftFSMulti_deliver {SS RS T M Sig K I : Type}
    (sIdx : ℕ) (hdr : Header T) (e : E₀) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) (Message := M) hdr e)) := fun h _ => by
  unfold deliverQuery; rw [query_eq_liftM]
  exact (multiFGSafeS_liftFSMulti_query (q₀ := .inl (.inr (hdr, e)))
    sIdx not_false h trivial).mono fun _ _ => trivial

private theorem multiFGSafeS_liftFSMulti_inject {SS RS T M Sig K I : Type}
    (sIdx : ℕ) (hdr : Header T) (e : E₀) (he : e.2.1.1.length < 2 ^ 32) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) (Message := M) hdr e)) := fun h _ => by
  unfold injectQuery; rw [query_eq_liftM]
  exact (multiFGSafeS_liftFSMulti_query (q₀ := .inr (hdr, e))
    sIdx (fun hlong => hlong he) h trivial).mono fun _ _ => trivial

private theorem multiFGSafeS_liftFSMultiDFBucket_transmit {SS RS T M Sig K I : Type}
    (sIdx : ℕ) (hdr : Header T) (m : M) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun a : Option E₀ => ∀ e, a = some e → e.2.1.1.length + 8 < 2 ^ 32)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)) := fun h _ => by
  unfold transmitQuery; rw [query_eq_liftM]
  exact (multiFGSafeS_liftFSMultiDFBucket_query (q₀ := .inl (.inl (.inl (.inl (.inl (hdr, m))))))
    sIdx not_false h trivial).mono fun ⟨a, _⟩ ⟨ha, _⟩ =>
    ⟨fun e he => by subst he; simpa [fsRespShort] using ha, trivial⟩

private theorem multiFGSafeS_liftFSMultiDFBucket_challenge {SS RS T M Sig K I : Type}
    (sIdx : ℕ) (hdr : Header T) (m₀ m₁ : M) :
    MultiFGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun a : Option E₀ => ∀ e, a = some e → e.2.1.1.length + 8 < 2 ^ 32)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)) := fun h _ => by
  unfold challengeQuery; rw [query_eq_liftM]
  exact (multiFGSafeS_liftFSMultiDFBucket_query (q₀ := .inl (.inl (.inl (.inl (.inr (hdr, m₀, m₁))))))
    sIdx not_false h trivial).mono fun ⟨a, _⟩ ⟨ha, _⟩ =>
    ⟨fun e he => by subst he; simpa [fsRespShort] using ha, trivial⟩

private theorem multiFGSafeS_liftFSMultiDFBucket_corrupt {SS RS T M Sig K I : Type} (sIdx : ℕ) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (corruptSenderQuery (SenderState := SS) (ReceiverState := RS)
          (AssocData := Header T) (Message := M) (Ciphertext := E₀))) := fun h _ => by
  unfold corruptSenderQuery; rw [query_eq_liftM]
  exact (multiFGSafeS_liftFSMultiDFBucket_query (q₀ := .inl (.inl (.inl (.inr ()))))
    sIdx not_false h trivial).mono fun _ _ => trivial

private theorem multiFGSafeS_liftFSMultiDFBucket_deliver {SS RS T M Sig K I : Type}
    (sIdx : ℕ) (hdr : Header T) (e : E₀) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) (Message := M) hdr e)) := fun h _ => by
  unfold deliverQuery; rw [query_eq_liftM]
  exact (multiFGSafeS_liftFSMultiDFBucket_query (q₀ := .inl (.inr (hdr, e)))
    sIdx not_false h trivial).mono fun _ _ => trivial

private theorem multiFGSafeS_liftFSMultiDFBucket_inject {SS RS T M Sig K I : Type}
    (sIdx : ℕ) (hdr : Header T) (e : E₀) (he : e.2.1.1.length < 2 ^ 32) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E₀) (Sig := Sig) (K := K) (I := I)
        sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) (Message := M) hdr e)) := fun h _ => by
  unfold injectQuery; rw [query_eq_liftM]
  exact (multiFGSafeS_liftFSMultiDFBucket_query (q₀ := .inr (hdr, e))
    sIdx (fun hlong => hlong he) h trivial).mono fun _ _ => trivial

private theorem multiFGSafeS_lookupMultiF {SS RS T M Sig K I : Type} [DecidableEq I] [SampleableType K]
    (Ik : I) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (lookupMultiF (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (M := M) (E := E₀) Ik) := by
  unfold lookupMultiF
  refine guardedSafeS_get_bind fun s _ => ?_
  cases s.table.lookup Ik with
  | some k => exact guardedSafeS_pure_true k
  | none =>
    refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT K) fun k => ?_
    exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
      fun _ => guardedSafeS_pure_true k

private theorem multiFGSafeS_regSessMulti {SS RS T M Sig K I : Type} [DecidableEq I] (Ik : I) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (regSessMulti (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (M := M) (E := E₀) Ik) := by
  unfold regSessMulti
  refine guardedSafeS_get_bind fun _ _ => ?_
  split
  · exact guardedSafeS_pure_true _
  · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial)
      fun _ => guardedSafeS_pure_true _

private theorem multiFGSafeS_regSessOptMulti {SS RS T M Sig K I : Type} [DecidableEq I] (sid : Option I) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (regSessOptMulti (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (M := M) (E := E₀) sid) := by
  cases sid with
  | none => exact guardedSafeS_pure_true none
  | some Ik =>
    intro h _
    simp only [regSessOptMulti, StateT.run_map]
    exact GuardedSafePost.map _ (multiFGSafeS_regSessMulti Ik h trivial) (fun _ _ => trivial)

private theorem multiFGSafeS_rootFSMulti {KR RSt K I T SS RS M : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t : ℕ) (Ik : I) (σ : RSt) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E₀) prng mo t Ik σ) := by
  unfold rootFSMulti
  split
  · exact guardedSafeS_pure_true _
  · split
    · split
      · refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT I) fun _ => ?_
        refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT K) fun _ => ?_
        exact guardedSafeS_pure_true _
      · exact guardedSafeS_bind_true (multiFGSafeS_lookupMultiF Ik) fun _ => guardedSafeS_pure_true _
    · split
      · exact guardedSafeS_bind_true (multiFGSafeS_lift_sampleT I) fun _ => guardedSafeS_pure_true _
      · exact guardedSafeS_pure_true _

private theorem hooksFSMulti_fgSafe
    {KC Γ CCoins T I KR RSt K SS RS M : Type} {ok : M → Bool}
    [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    MultiHooksFGSafe ok (hooksFSMulti cka prng fs Δcka mo gMain la) where
  startSend_fg _ _ t γ σ r := by
    dsimp only [hooksFSMulti]
    rcases r with _ | c
    · refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT CCoins) fun coins => ?_
      refine guardedSafeS_bind_true (multiFGSafeS_rootFSMulti prng mo t (cka.send γ coins).2.2 σ) fun p => ?_
      refine guardedSafeS_bind_true (multiFGSafeS_regSessOptMulti p.2.2) fun _ => ?_
      exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
        fun _ => guardedSafeS_pure_true _
    · simp only [pure_bind]
      refine guardedSafeS_bind_true (multiFGSafeS_rootFSMulti prng mo t (cka.send γ c).2.2 σ) fun p => ?_
      refine guardedSafeS_bind_true (multiFGSafeS_regSessOptMulti p.2.2) fun _ => ?_
      exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
        fun _ => guardedSafeS_pure_true _
  startRecv_fg _ _ t γ σ Tn := by
    dsimp only [hooksFSMulti]
    refine guardedSafeS_get_bind fun s _ => ?_
    split
    · exact guardedSafeS_pure_true _
    · split
      · exact guardedSafeS_pure_true _
      · split
        · split
          · exact guardedSafeS_pure_true _
          · refine guardedSafeS_bind_true (multiFGSafeS_lookupMultiF (cka.receive γ Tn).2) fun _ => ?_
            exact guardedSafeS_bind_true (multiFGSafeS_regSessMulti (cka.receive γ Tn).2)
              fun _ => guardedSafeS_pure_true _
        · exact guardedSafeS_pure_true _
  fsSend_fg _ _ _ ssv hdr m pair hm := by
    dsimp only [hooksFSMulti]
    rcases ssv with ss | sIdx
    · refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
      rintro _ _ ⟨⟩; exact hfs ss hdr m hm
    · refine guardedSafeS_get_bind fun _ _ => ?_
      split
      · cases la
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine guardedSafeS_bind_true (multiFGSafeS_liftFSMulti_corrupt sIdx) fun r => ?_
          rcases r with _ | _
          · simp only [pure_bind, Bool.not_false, ↓reduceIte]
            exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
          · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rcases pair with _ | ⟨m₀, m₁⟩
            · refine guardedSafeS_bind_and (multiFGSafeS_liftFSMulti_transmit sIdx hdr m) fun e? he? => ?_
              rcases e? with _ | e
              · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
              · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
                  guardedSafeS_pure _ fun _ _ => ⟨by rintro _ _ ⟨⟩; exact he? e rfl, trivial⟩
            · refine guardedSafeS_bind_and (multiFGSafeS_liftFSMulti_challenge sIdx hdr m₀ m₁) fun e? he? => ?_
              rcases e? with _ | e
              · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
              · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
                  guardedSafeS_pure _ fun _ _ => ⟨by rintro _ _ ⟨⟩; exact he? e rfl, trivial⟩
        · simp only [↓reduceIte, pure_bind, Bool.not_false]
          exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
      · simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases pair with _ | ⟨m₀, m₁⟩
        · refine guardedSafeS_bind_and (multiFGSafeS_liftFSMulti_transmit sIdx hdr m) fun e? he? => ?_
          rcases e? with _ | e
          · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
          · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
              guardedSafeS_pure _ fun _ _ => ⟨by rintro _ _ ⟨⟩; exact he? e rfl, trivial⟩
        · refine guardedSafeS_bind_and (multiFGSafeS_liftFSMulti_challenge sIdx hdr m₀ m₁) fun e? he? => ?_
          rcases e? with _ | e
          · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
          · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
              guardedSafeS_pure _ fun _ _ => ⟨by rintro _ _ ⟨⟩; exact he? e rfl, trivial⟩
  fsRecv_fg _ _ _ rsv hdr e rec he := by
    dsimp only [hooksFSMulti]
    rcases rsv with rs | sIdx
    · exact guardedSafeS_pure_true _
    · refine guardedSafeS_get_bind fun _ _ => ?_
      split
      · split
        · simp only [pure_bind, Bool.not_false, ↓reduceIte]
          exact guardedSafeS_pure_true none
        · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMulti_corrupt sIdx) fun r => ?_
          rcases r with _ | _
          · simp only [pure_bind, Bool.not_false, ↓reduceIte]
            exact guardedSafeS_pure_true none
          · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            split_ifs
            · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMulti_deliver sIdx hdr e) fun res => ?_
              rcases res with _ | (_ | ⟨_, mo'⟩)
              · exact guardedSafeS_pure_true none
              · exact guardedSafeS_pure_true (some none)
              · dsimp only
                refine guardedSafeS_get_bind fun _ _ => ?_
                split_ifs
                · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                    fun _ => guardedSafeS_pure_true none
                · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
                  rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
            · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMulti_inject sIdx hdr e he) fun res => ?_
              rcases res with _ | (_ | ⟨_, mo'⟩)
              · exact guardedSafeS_pure_true none
              · exact guardedSafeS_pure_true (some none)
              · dsimp only
                refine guardedSafeS_get_bind fun _ _ => ?_
                split_ifs
                · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                    fun _ => guardedSafeS_pure_true none
                · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
                  rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
      · simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split_ifs
        · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMulti_deliver sIdx hdr e) fun res => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact guardedSafeS_pure_true none
          · exact guardedSafeS_pure_true (some none)
          · dsimp only
            refine guardedSafeS_get_bind fun _ _ => ?_
            split_ifs
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                fun _ => guardedSafeS_pure_true none
            · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
              rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
        · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMulti_inject sIdx hdr e he) fun res => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact guardedSafeS_pure_true none
          · exact guardedSafeS_pure_true (some none)
          · dsimp only
            refine guardedSafeS_get_bind fun _ _ => ?_
            split_ifs
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                fun _ => guardedSafeS_pure_true none
            · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
              rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
  commit_fg _ _ _ new := guardedSafeS_pure_true (some new)
  reveal_fg _ _ vp := by
    dsimp only [hooksFSMulti]
    rcases vp.vS with _ | (_ | sIdx)
    · simp only [pure_bind]; split_ifs <;> exact guardedSafeS_pure_true _
    · simp only [pure_bind]; split_ifs <;> exact guardedSafeS_pure_true _
    · cases la
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine guardedSafeS_bind_true (multiFGSafeS_liftFSMulti_corrupt sIdx) fun o => ?_
        rcases o with _ | _
        · simp only [pure_bind]; exact guardedSafeS_pure_true none
        · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          simp only [pure_bind]; split_ifs <;> exact guardedSafeS_pure_true _
      · simp only [↓reduceIte, pure_bind]; exact guardedSafeS_pure_true none

private theorem multiFGSafeS_lookupMultiDFBucketF {SS RS T M Sig K I : Type}
    [DecidableEq I] [SampleableType K] (t0 : ℕ) (Ik : I) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (lookupMultiDFBucketF (T := T) (RSt := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
        (M := M) (E := E₀) t0 Ik) := by
  unfold lookupMultiDFBucketF
  refine guardedSafeS_get_bind fun s _ => ?_
  dsimp only
  cases (s.fTable t0).lookup Ik with
  | some k => exact guardedSafeS_pure_true k
  | none =>
    refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT K) fun k => ?_
    exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
      fun _ => guardedSafeS_pure_true k

private theorem multiFGSafeS_rootFSMultiDFBucketPaper {KR RSt K I T SS RS M : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : RSt) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E₀)
        prng Δbucket qep tL par t0 pl ik0 σ0) := by
  unfold rootFSMultiDFBucketPaper
  dsimp only
  split
  · exact guardedSafeS_pure_true _
  · split
    · split
      · refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT I) fun _ => ?_
        exact guardedSafeS_bind_true (multiFGSafeS_lift_sampleT K) fun _ => guardedSafeS_pure_true _
      · exact guardedSafeS_bind_true (multiFGSafeS_lookupMultiDFBucketF t0 ik0)
          fun _ => guardedSafeS_pure_true _
    · split
      · refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT I) fun _ => ?_
        exact guardedSafeS_bind_true (multiFGSafeS_lift_sampleT K) fun _ => guardedSafeS_pure_true _
      · exact guardedSafeS_pure_true _

private theorem hooksFSMultiDFBucketPaper_fgSafe
    {KC Γ CCoins T I KR RSt K SS RS M : Type} {ok : M → Bool}
    [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool) :
    MultiHooksFGSafe ok (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la) where
  startSend_fg _ _ t0 γ0 σ0 r0 := by
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases r0 with _ | c
    · refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT CCoins) fun coins => ?_
      refine guardedSafeS_bind_true
        (multiFGSafeS_rootFSMultiDFBucketPaper prng Δbucket qep tL par t0 _ (cka.send γ0 coins).2.2 σ0)
        fun _ => ?_
      refine guardedSafeS_get_bind fun _ _ => ?_
      exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial)
        fun _ => guardedSafeS_pure_true _
    · simp only [pure_bind]
      refine guardedSafeS_bind_true
        (multiFGSafeS_rootFSMultiDFBucketPaper prng Δbucket qep tL par t0 _ (cka.send γ0 c).2.2 σ0)
        fun _ => ?_
      refine guardedSafeS_get_bind fun _ _ => ?_
      exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial)
        fun _ => guardedSafeS_pure_true _
  startRecv_fg _ _ t0 γ0 σ0 tn0 := by
    dsimp only [hooksFSMultiDFBucketPaper]
    refine guardedSafeS_get_bind fun _ _ => ?_
    split
    · exact guardedSafeS_pure_true _
    · split
      · split
        · exact guardedSafeS_pure_true none
        · split
          · exact guardedSafeS_pure_true _
          · refine guardedSafeS_bind_true (multiFGSafeS_lookupMultiDFBucketF t0 (cka.receive γ0 tn0).2)
              fun _ => ?_
            refine guardedSafeS_get_bind fun _ _ => ?_
            exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial)
              fun _ => guardedSafeS_pure_true _
      · exact guardedSafeS_pure_true (some none)
  fsSend_fg _ _ _ ssv hdr m pair hm := by
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases ssv with ss | sIdx
    · refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
      rintro _ _ ⟨⟩; exact hfs ss hdr m hm
    · refine guardedSafeS_get_bind fun _ _ => ?_
      split
      · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_corrupt sIdx) fun r => ?_
        rcases r with _ | _
        · simp only [pure_bind, Bool.not_false, ↓reduceIte]
          exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
        · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rcases pair with _ | ⟨m₀, m₁⟩
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
      · simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases pair with _ | ⟨m₀, m₁⟩
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
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases rsv with rs | sIdx
    · exact guardedSafeS_pure_true _
    · refine guardedSafeS_get_bind fun _ _ => ?_
      split
      · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_corrupt sIdx) fun r => ?_
        rcases r with _ | _
        · simp only [pure_bind, Bool.not_false, ↓reduceIte]
          exact guardedSafeS_pure_true none
        · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          split_ifs
          · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_deliver sIdx hdr e) fun res => ?_
            rcases res with _ | (_ | ⟨_, mo'⟩)
            · exact guardedSafeS_pure_true none
            · exact guardedSafeS_pure_true (some none)
            · dsimp only
              refine guardedSafeS_get_bind fun _ _ => ?_
              split_ifs
              · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                  fun _ => guardedSafeS_pure_true none
              · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
                rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
          · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_inject sIdx hdr e he) fun res => ?_
            rcases res with _ | (_ | ⟨_, mo'⟩)
            · exact guardedSafeS_pure_true none
            · exact guardedSafeS_pure_true (some none)
            · dsimp only
              refine guardedSafeS_get_bind fun _ _ => ?_
              split_ifs
              · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                  fun _ => guardedSafeS_pure_true none
              · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
                rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
      · simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split_ifs
        · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_deliver sIdx hdr e) fun res => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact guardedSafeS_pure_true none
          · exact guardedSafeS_pure_true (some none)
          · dsimp only
            refine guardedSafeS_get_bind fun _ _ => ?_
            split_ifs
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                fun _ => guardedSafeS_pure_true none
            · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
              rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
        · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_inject sIdx hdr e he) fun res => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact guardedSafeS_pure_true none
          · exact guardedSafeS_pure_true (some none)
          · dsimp only
            refine guardedSafeS_get_bind fun _ _ => ?_
            split_ifs
            · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
                fun _ => guardedSafeS_pure_true none
            · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
              rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact guardedSafeS_pure_true _
  commit_fg _ _ _ new := guardedSafeS_pure_true (some new)
  reveal_fg _ _ vp := by
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases vp.vS with _ | (_ | sIdx)
    · simp only [pure_bind]; split_ifs <;> exact guardedSafeS_pure_true _
    · simp only [pure_bind]; split_ifs <;> exact guardedSafeS_pure_true _
    · refine guardedSafeS_bind_true (multiFGSafeS_liftFSMultiDFBucket_corrupt sIdx) fun o => ?_
      rcases o with _ | _
      · simp only [pure_bind]; exact guardedSafeS_pure_true none
      · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
        simp only [pure_bind]; split_ifs <;> exact guardedSafeS_pure_true _

private theorem multiFGSafePost_initFSMultiRaw
    {KC Γ CCoins T I KR RSt K SS RS M : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (lam : I) (mo : Mode) (b : Bool) :
    GuardedSafePost
      (multiRespShortRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (multiInjectLongRaw (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (fun _ => True) (initFSMultiRaw cka prng fs lam mo b) := by
  unfold initFSMultiRaw
  refine (multiFGSafePost_sampleT KR).bind fun kr _ => ?_
  refine (multiFGSafePost_sampleT KC).bind fun _ _ => ?_
  refine (multiFGSafeS_rootFSMulti prng mo 0 lam (prng.init kr)
    ({} : FSMultiState T RSt K I E₀) trivial).bind fun ⟨⟨_, _, sid⟩, h1⟩ _ => ?_
  exact (multiFGSafeS_regSessOptMulti sid h1 trivial).bind fun _ _ => GuardedSafePost.pure trivial

private theorem multiFGSafeS_initFSMultiDFBucketPaper
    {KC Γ CCoins T I KR RSt K SS RS M : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (lam : I)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) :
    MultiFGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par) := by
  unfold initFSMultiDFBucketPaper
  refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT KR) fun kr => ?_
  refine guardedSafeS_bind_true (multiFGSafeS_lift_sampleT KC) fun _ => ?_
  refine guardedSafeS_bind_true
    (multiFGSafeS_rootFSMultiDFBucketPaper prng Δbucket qep tL par 0 false lam (prng.init kr))
    fun _ => ?_
  refine guardedSafeS_get_bind fun _ _ => ?_
  exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial)
    fun _ => guardedSafeS_pure_true _

private theorem guardedMultiInjectShort_of_raw {Pt : Type} {ℓ : ℕ}
    (c : Computational.Proofs.E2E.SessionAuthBridge.MultiSessPubFsAdv Pt ℓ)
    (h : GuardedSafePost multiRespShortRaw multiInjectLongRaw (fun _ => True) c) :
    GuardedMultiInjectShort c := by
  induction h with
  | pure _ => exact GuardedSafePost.pure trivial
  | @query_bind q _ hnb _ ih =>
    rcases q with u | ⟨s, ((((_ | _) | _) | _) | _) | ⟨_, _, _⟩⟩ <;>
      exact GuardedSafePost.query_bind hnb fun r hr => ih r hr

private theorem lFS_fsSendShort_atomic {Pt : Type} (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :
    FsSendShort (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) := by
  intro ss hdr m hm
  exact lFS_fsSendShort C protoSignalCodec signalEncodeFits32_proto ℓ (by omega) encT idOf
    maxForwardJumps ss hdr m (atomicShortPubB_imp_shortB hm)

/-- `GuardedMultiInjectShort` on `redFSAuthDFShiftedPaperMultiGen` over `lFS`. -/
theorem redFSAuthDFShiftedPaperMultiGen_guardedMultiInjectShort
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Δcka qep l t : ℕ) (authH la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A) :
    GuardedMultiInjectShort
      (redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t authH la A) := by
  refine guardedMultiInjectShort_of_raw _ ?_
  let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  let mo : Mode := ⟨authH, some (l - 1), t⟩
  have hSpec := hooksFSMulti_fgSafe (dhScheme Dh) (rootPRNG C.F encPt) fs
    (lFS_fsSendShort_atomic C ℓ hℓ encT idOf) Δcka mo false la
  have hA := hg.and_isQueryBoundP hsh
  unfold redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper
  rw [bind_assoc]
  refine (multiFGSafePost_initFSMultiRaw (dhScheme Dh) (rootPRNG C.F encPt) fs lam mo false).bind
    fun es₀ _ => ?_
  refine (GuardedSafePost.simulateQ_run (I := fun _ => True) hA ?_ trivial).bind
    fun _ _ => GuardedSafePost.pure trivial
  rintro (u | (tr | qdf)) hpt s _
  · dsimp only [implEDFShiftedPaperGen]
    exact (multiFGSafeS_coinsE u s trivial).mono fun _ _ => ⟨trivial, trivial⟩
  · rcases tr with ((((q | q) | q) | q) | P)
    · have hok_q : atomicShortPubB q.2.1.1 = true := by
        have hnb : ¬ badSendMsgDF (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
            (.inr (.inl (.inl (.inl (.inl (.inl q)))))) = true := fun hb => hpt (Or.inr hb)
        simpa [badSendMsgDF] using hnb
      dsimp only [implEDFShiftedPaperGen]
      exact multiFGSafeS_transmitE hSpec (2 + Δcka) qep _ q hok_q s trivial
    · have hok_q : atomicShortPubB q.2.1.1 = true ∧ atomicShortPubB q.2.2.1.1 = true := by
        have hnb : ¬ badSendMsgDF (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
            (.inr (.inl (.inl (.inl (.inl (.inr q)))))) = true := fun hb => hpt (Or.inr hb)
        simpa [badSendMsgDF, Bool.or_eq_true] using hnb
      dsimp only [implEDFShiftedPaperGen]
      exact multiFGSafeS_challE hSpec (2 + Δcka) qep _ (fun _ => rfl) _ q hok_q.1 hok_q.2 s trivial
    · dsimp only [implEDFShiftedPaperGen]
      exact (multiFGSafeS_deliverE hSpec fs.maxSkip _ q
        (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono fun _ _ => ⟨trivial, trivial⟩
    · dsimp only [implEDFShiftedPaperGen]
      exact (multiFGSafeS_injectEGen hSpec (!authH) (2 + Δcka) qep t _ q
        (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono fun _ _ => ⟨trivial, trivial⟩
    · dsimp only [implEDFShiftedPaperGen]
      exact (multiFGSafeS_corrEShiftedPaper hSpec l _ P s trivial).mono fun _ _ => ⟨trivial, trivial⟩
  · dsimp only [implEDFShiftedPaperGen]
    exact (multiFGSafeS_deliverForgeEGen hSpec (!authH) (2 + Δcka) qep t _ qdf
      (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono fun _ _ => ⟨trivial, trivial⟩

/-- `GuardedMultiInjectShort` on `redFSAuthDFPaperMulti` over `lFS`. -/
theorem redFSAuthDFPaperMulti_guardedMultiInjectShort
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A) :
    GuardedMultiInjectShort
      (redFSAuthDFPaperMulti (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la tL t A) := by
  refine guardedMultiInjectShort_of_raw _ ?_
  let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  let mo : Mode := ⟨true, tL, t⟩
  have hSpec := hooksFSMulti_fgSafe (dhScheme Dh) (rootPRNG C.F encPt) fs
    (lFS_fsSendShort_atomic C ℓ hℓ encT idOf) Δcka mo false la
  have hA := hg.and_isQueryBoundP hsh
  unfold redFSAuthDFPaperMulti runFSMultiDFPaper
  rw [bind_assoc]
  refine (multiFGSafePost_initFSMultiRaw (dhScheme Dh) (rootPRNG C.F encPt) fs lam mo false).bind
    fun es₀ _ => ?_
  refine (GuardedSafePost.simulateQ_run (I := fun _ => True) hA ?_ trivial).bind
    fun _ _ => GuardedSafePost.pure trivial
  rintro (u | (tr | qdf)) hpt s _
  · dsimp only [implEDFPaper]
    exact (multiFGSafeS_coinsE u s trivial).mono fun _ _ => ⟨trivial, trivial⟩
  · rcases tr with ((((q | q) | q) | q) | P)
    · have hok_q : atomicShortPubB q.2.1.1 = true := by
        have hnb : ¬ badSendMsgDF (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
            (.inr (.inl (.inl (.inl (.inl (.inl q)))))) = true := fun hb => hpt (Or.inr hb)
        simpa [badSendMsgDF] using hnb
      dsimp only [implEDFPaper]
      exact multiFGSafeS_transmitE hSpec (2 + Δcka) qep _ q hok_q s trivial
    · have hok_q : atomicShortPubB q.2.1.1 = true ∧ atomicShortPubB q.2.2.1.1 = true := by
        have hnb : ¬ badSendMsgDF (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
            (.inr (.inl (.inl (.inl (.inl (.inr q)))))) = true := fun hb => hpt (Or.inr hb)
        simpa [badSendMsgDF, Bool.or_eq_true] using hnb
      dsimp only [implEDFPaper]
      exact multiFGSafeS_challE hSpec (2 + Δcka) qep _ (fun _ => rfl) _ q hok_q.1 hok_q.2 s trivial
    · dsimp only [implEDFPaper]
      exact (multiFGSafeS_deliverE hSpec fs.maxSkip _ q
        (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono fun _ _ => ⟨trivial, trivial⟩
    · dsimp only [implEDFPaper]
      exact (multiFGSafeS_injectEGen hSpec false (2 + Δcka) qep 0 _ q
        (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono fun _ _ => ⟨trivial, trivial⟩
    · dsimp only [implEDFPaper]
      exact (multiFGSafeS_corrEPaper hSpec _ P s trivial).mono fun _ _ => ⟨trivial, trivial⟩
  · dsimp only [implEDFPaper]
    exact (multiFGSafeS_deliverForgeEGen hSpec false (2 + Δcka) qep 0 _ qdf
      (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono fun _ _ => ⟨trivial, trivial⟩

/-- `GuardedMultiInjectShort` on `redFSAuthDFPaperMultiBucket` over `lFS`. -/
theorem redFSAuthDFPaperMultiBucket_guardedMultiInjectShort
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (L : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A) :
    GuardedMultiInjectShort
      (redFSAuthDFPaperMultiBucket L (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la tL par A) := by
  refine guardedMultiInjectShort_of_raw _ ?_
  let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  have hSpec := hooksFSMultiDFBucketPaper_fgSafe L (dhScheme Dh) (rootPRNG C.F encPt) fs
    (lFS_fsSendShort_atomic C ℓ hℓ encT idOf) Δcka Δbucket qep tL par la
  have hA := hg.and_isQueryBoundP hsh
  unfold redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketGen engRunDFPaperBucket
    implEDFPaperBucket
  rw [bind_assoc]
  refine (multiFGSafeS_initFSMultiDFBucketPaper L (dhScheme Dh) (rootPRNG C.F encPt) fs lam
    Δbucket qep tL par {} trivial).bind fun ⟨vs, h⟩ _ => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · simp only [pure_bind]; exact GuardedSafePost.pure trivial
  · simp only [bind_assoc]
    let rawImpl := implEDFPaperBucketRaw
      (hooksFSMultiDFBucketPaper L (dhScheme Dh) (rootPRNG C.F encPt) fs Δcka Δbucket qep tL par la)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
    let es₀ : EState _ (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × E₀)
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt E₀) :=
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
    refine (GuardedSafePost.simulateQ_run (I := fun _ => True) hA ?_ (s := (es₀, none)) trivial).bind
      fun _ _ => GuardedSafePost.pure trivial
    intro qt hpt ⟨s, winEp⟩ _
    unfold withWinEpDF
    dsimp only [StateT.run_mk]
    have hstep : GuardedSafePost multiRespShortRaw multiInjectLongRaw
        (fun r => smDFRespShort qt r.1 ∧ True) ((rawImpl qt).run s) := by
      rcases qt with u | (tr | qdf)
      · dsimp only [rawImpl, implEDFPaperBucketRaw]
        exact (multiFGSafeS_coinsE u s trivial).mono fun _ _ => ⟨trivial, trivial⟩
      · rcases tr with ((((q | q) | q) | q) | P)
        · have hok_q : atomicShortPubB q.2.1.1 = true := by
            have hnb : ¬ badSendMsgDF (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
                (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
                (.inr (.inl (.inl (.inl (.inl (.inl q)))))) = true := fun hb => hpt (Or.inr hb)
            simpa [badSendMsgDF] using hnb
          dsimp only [rawImpl, implEDFPaperBucketRaw]
          exact multiFGSafeS_transmitEBucket hSpec (2 + Δcka) qep q hok_q s trivial
        · dsimp only [rawImpl, implEDFPaperBucketRaw]
          exact multiFGSafeS_challEBucket q s trivial
        · dsimp only [rawImpl, implEDFPaperBucketRaw]
          exact (multiFGSafeS_deliverE hSpec fs.maxSkip _ q
            (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono
            fun _ _ => ⟨trivial, trivial⟩
        · dsimp only [rawImpl, implEDFPaperBucketRaw]
          exact (multiFGSafeS_injectEGen hSpec false (2 + Δcka) qep 0 _ q
            (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono
            fun _ _ => ⟨trivial, trivial⟩
        · dsimp only [rawImpl, implEDFPaperBucketRaw]
          exact (multiFGSafeS_corrEPaperBucket hSpec P s trivial).mono fun _ _ => ⟨trivial, trivial⟩
      · dsimp only [rawImpl, implEDFPaperBucketRaw]
        exact (multiFGSafeS_deliverForgeEGen hSpec false (2 + Δcka) qep 0 _ qdf
          (Decidable.of_not_not fun hnl => hpt (Or.inl hnl)) s trivial).mono
          fun _ _ => ⟨trivial, trivial⟩
    exact hstep.bind fun ⟨r', _⟩ hr => GuardedSafePost.pure ⟨hr.1, trivial⟩

end GuardedShort

end

end Computational.Proofs.E2E.SessionAuthMultiShort
