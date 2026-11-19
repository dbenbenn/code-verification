/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BucketFSAuthEvalHooks
import Computational.Proofs.SessionCostedFig8.BucketFSAuthEvalHooksB
import Computational.Proofs.ReductionDsl.SM.RedFS

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeShallow

public section

open OracleSpec OracleComp
open _root_.ReductionDsl (Ops Ty Env Expr Comp CostedReduction handlerImpl isGameQuery)
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun CKASort CKASamp CKAOp ckaOps ckaSamplers ckaSchemeOps ckaHdrTy
  ckaHdrCtTy ckaPsTy ckaPsEnc)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps prngSamplers prngSMCodec FSHdrTag fsHdrRrTy fsHdrRrEnc)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.SM (Pos Record Config GameState spec MakesAtMostQueries
  authLosingConditionsAvoided partyEnc pGet pGet_eval maxN not_eval and_eval orE orE_eval isSomeE
  letE_eval pair_eval some_eval ite_eval healedByE_eval senderOfE senderOfE_eval)
open _root_.CryptoGames.SM.Engine (Ctx HM TComp EState VP Hooks HooksC HooksCAgrees ConfigEC
  ConfigECAgrees SMEngineInv SMStateBoundedEngine optNatLit vpEnc vpTblTy vpTblEnc cGsTy cGsEnc
  esTy esEnc esMk esG esH esAbort cSafeChE cSafeChE_eval cGsTL cGsEpoch cGsIdx cGsSt cGsWin
  cEpMgmtE cEpMgmtE_eval cRecordE cRecordE_eval cCorrAllowedE cCorrAllowedE_eval cAfterCorrE
  cAfterCorrE_eval cAuthOKE cAuthOKE_eval mkPartiesE mkPartiesE_eval cGsInitE cGsInitE_eval
  cRecTy cRecEnc cRecMsg vpTcurNat vpVS vpVR vpΓ vpRoot realPartyE realPartyE_eval vSend vSendStep1
  vSend_eq_bind vRecv vRecvStep1 vRecv_eq_bind vSendC vSendC_eval deliverE deliverE_inv deliverEC
  deliverEC_eval injectE injectE_inv injectEC injectEC_eval commitE abortE epMgmt_lists_eq
  run_liftH_bind tset_eval_eq_update eval_ret eval_bind eval_bind_ret eval_ite eval_caseOpt
  liftP_eq_liftM)
open _root_.CryptoGames.SM.Construction (PartyState SchemeAdversary Header FSMultiSpec FSMultiBook
  mkParties realParty bucketAuthCfgEC fsClamp healEpoch sampleT fst_eval snd_eval eval_caseOpt_none
  eval_caseOpt_some eval_caseSum_inl eval_caseSum_inr fsTransFindE fsTransFindE_eval fsTransFilterE
  fsTransFilterE_eval rangeListC rangeListC_eval foldr_update_apply)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb fsAtomicB)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (fsaeadMultiBucketIface
  fsMultiBucketSessBookTy fsMultiBucketHsTy fsMultiBucketVpTy fsMultiBucketRedEsTy
  mbHsGetBookAt mbHsSetBookAt mbHsSetLfWin mbHsLfWin mbHsEmptyE
  regSessOptMultiBucketE rootFSMultiBucketAuthC isHonestHdrMultiBucketE
  fsTransFindBucketE fsTransFilterBucketE fsMultiBucketAuthFsSendC fsMultiBucketAuthFsRecvC
  fsMultiBucketAuthCommitC rangeListBucketC isExtMultiBucketEntryE anyExtMultiBucketVRE
  unliftMultiBucketEntryE unliftMultiBucketVRE fsMultiBucketAuthRevealC hooksFSMultiBucketAuthC
  initFSMultiBucketAuthEStateC redFSAuthMultiBucketProg)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (bucketAuthCfg)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (FSMultiBucketAuthState
  FSMultiBucketAuthEState liftFSMultiBucket lookupMultiBucketF regSessMultiBucket
  regSessOptMultiBucket rootFSMultiBucketAuth isHonestHdrMultiBucket hooksFSMultiBucketAuth
  initFSMultiBucketAuth implFSMultiBucketAuth redFSAuthMultiBucket fsMultiBucketHsEnc
  FSMultiBucketHBounded FSMultiBucketHBoundedPost FSMultiBucketStepBounded
  bucketAuthCfgEC_agrees fsBookStep_refl fsBookStep_mono fsBookStep_apply
  hooksFSMultiBucketAuth_startSend_preserve hooksFSMultiBucketAuth_startRecv_preserve
  hooksFSMultiBucketAuth_fsSend_preserve hooksFSMultiBucketAuth_fsRecv_preserve
  hooksFSMultiBucketAuth_reveal_preserve)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthEvalHooks (mbHsGetBookAt_eval
  mbHsSetBookAt_eval mbHsSetLfWin_eval regSessOptMultiBucketE_eval_pair rootFSMultiBucketAuthC_eval
  fsMultiBucketAuthStartSendC_eval isHonestHdrMultiBucketE_eval fsMultiBucketAuthStartRecvC_eval)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthEvalHooksB (fsMultiBucketAuthRevealC_eval
  hooksFSMultiBucketAuthC_agrees)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase (redFSAuthMultiBucketShallow)

section Layer3Bridge

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "SP" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" => prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
  fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "vpMEnc" => vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
  (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  (γvT := Ty.base CKASort.γ) (svT := Ty.base CKASort.sig)
  (ssvT := Ty.sum (Ty.base CKASort.ss) Ty.nat) (rsvT := Ty.sum (Ty.base CKASort.rs) Ty.nat)
local notation "hsMBEnc" => fsMultiBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
  (SS := SS) (RS := RS) (M := M) (T := T) (RSt := RSt) (K := K) (I := I) (E := E)
local notation "SMCodec" => prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHooksC" => hooksFSMultiBucketAuthC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
  (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
  (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
  (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
  (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
  (sampI := sampI) (sampK := sampK)
local notation "mbInitC" => initFSMultiBucketAuthEStateC (ckaInitA := ckaInitA)
  (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
  (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
  (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
  (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
  (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
local notation "mbProg" => redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
  (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
  (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
  (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
  (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
  (sampI := sampI) (sampK := sampK)

private theorem with_comp_env {S' : _root_.ReductionDsl.Sig} {O' : Ops S'} {ι : Type}
    {spec' : OracleSpec ι} {I' : _root_.ReductionDsl.Iface S' spec'} {Γ'' : List (Ty S')}
    {τ : Ty S'} {β : Type} {f : τ.denote → β} {c : Comp O' I' Γ'' τ} {ρ : Env Γ''}
    {rhs : OracleComp spec' β} (h : ∀ ρ', ρ' = ρ → (f <$> c.eval ρ') = rhs) :
    (f <$> c.eval ρ) = rhs := h ρ rfl

private theorem eval_caseSum_inl' {S' : _root_.ReductionDsl.Sig} {O' : Ops S'} {ι : Type}
    {spec' : OracleSpec ι} {I' : _root_.ReductionDsl.Iface S' spec'} {Γ' : List (Ty S')}
    {a b c : Ty S'} {e : Expr O' Γ' (.sum a b)} {lb : Comp O' I' (a :: Γ') c}
    {rb : Comp O' I' (b :: Γ') c} {ρ : Env Γ'} {v : a.denote} (h : e.eval ρ = .inl v) :
    (Comp.caseSum e lb rb).eval ρ = lb.eval (.cons v ρ) := by simp [Comp.eval, h]
private theorem eval_caseSum_inr' {S' : _root_.ReductionDsl.Sig} {O' : Ops S'} {ι : Type}
    {spec' : OracleSpec ι} {I' : _root_.ReductionDsl.Iface S' spec'} {Γ' : List (Ty S')}
    {a b c : Ty S'} {e : Expr O' Γ' (.sum a b)} {lb : Comp O' I' (a :: Γ') c}
    {rb : Comp O' I' (b :: Γ') c} {ρ : Env Γ'} {v : b.denote} (h : e.eval ρ = .inr v) :
    (Comp.caseSum e lb rb).eval ρ = rb.eval (.cons v ρ) := by simp [Comp.eval, h]
private theorem eval_caseOpt_none' {S' : _root_.ReductionDsl.Sig} {O' : Ops S'} {ι : Type}
    {spec' : OracleSpec ι} {I' : _root_.ReductionDsl.Iface S' spec'} {Γ' : List (Ty S')}
    {a c : Ty S'} {e : Expr O' Γ' (.opt a)} {nb : Comp O' I' Γ' c} {sb : Comp O' I' (a :: Γ') c}
    {ρ : Env Γ'} (h : e.eval ρ = none) :
    (Comp.caseOpt e nb sb).eval ρ = nb.eval ρ := by simp [Comp.eval, h]
private theorem eval_caseOpt_some' {S' : _root_.ReductionDsl.Sig} {O' : Ops S'} {ι : Type}
    {spec' : OracleSpec ι} {I' : _root_.ReductionDsl.Iface S' spec'} {Γ' : List (Ty S')}
    {a c : Ty S'} {e : Expr O' Γ' (.opt a)} {nb : Comp O' I' Γ' c} {sb : Comp O' I' (a :: Γ') c}
    {ρ : Env Γ'} {v : a.denote} (h : e.eval ρ = some v) :
    (Comp.caseOpt e nb sb).eval ρ = sb.eval (.cons v ρ) := by simp [Comp.eval, h]

private theorem vSend_preserve_h_only [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type} (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {HPre HMid HPost : HS → Prop} (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (m : M) (pair : Option (M × M)) (r : Option CCoins) (h : HS)
    (hPre : HPre h) (hMid0 : HPre h → HMid h) (hMidPost : ∀ {h1}, HMid h1 → HPost h1)
    (hStart : ∀ t0 γ0 σ0 r0 res, HPre h →
      res ∈ support ((hk.startSend ctx P t0 γ0 σ0 r0).run h) → HMid res.2)
    (hFs : ∀ {h1} t1 v hHdr m' pair' res, HMid h1 →
      res ∈ support ((hk.fsSend ctx P t1 v hHdr m' pair').run h1) → HPost res.2) :
    ∀ res ∈ support ((vSend hk ctx P s m pair r).run h), HPost res.2 := by
  intro ⟨vsRes, h'⟩ hmem
  rw [vSend_eq_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
  have hStep1 : HMid h₁ := by
    unfold vSendStep1 at hmem1
    by_cases hs : s.id.sendsIn (s.tcur + 1)
    · simp only [hs, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem1
      obtain ⟨⟨ssRes, h₁'⟩, hss, hmem1⟩ := hmem1
      have hM := hStart (s.tcur + 1) s.γ s.root r (ssRes, h₁') hPre hss
      rcases ssRes with _ | ⟨γ', T', σ', ss⟩ <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1;
         rcases hmem1 with ⟨_, rfl⟩; exact hM)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      rcases hmem1 with ⟨_, rfl⟩; exact hMid0 hPre
  rcases s₁? with _ | s₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
    rcases hmem2 with ⟨_, rfl⟩; exact hMidPost hStep1
  · rcases hvS1 : s₁.vS with _ | v
    · simp only [hvS1, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨_, rfl⟩; exact hMidPost hStep1
    · simp only [hvS1, StateT.run_bind, mem_support_bind_iff] at hmem2
      obtain ⟨⟨fsRes, h₂⟩, hfs, hmem2⟩ := hmem2
      have hP := hFs s₁.tcur v (s₁.tcur, s₁.curCkaMsg) m pair (fsRes, h₂) hStep1 hfs
      rcases fsRes with _ | ⟨v', e⟩ <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2;
         rcases hmem2 with ⟨_, rfl⟩; exact hP)

private theorem vRecv_preserve_h_only {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type} (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {HPre HMid HPost : HS → Prop} (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (c : Header T × E) (rec : Option (Record M (Header T × E))) (h : HS)
    (hPre : HPre h) (hMid0 : HPre h → HMid h) (hMidPost : ∀ {h1}, HMid h1 → HPost h1)
    (hStart : ∀ t0 γ0 σ0 Tn res, HPre h →
      res ∈ support ((hk.startRecv ctx P t0 γ0 σ0 Tn).run h) → HMid res.2)
    (hFs : ∀ {h1} t1 v hHdr e rec' res, HMid h1 →
      res ∈ support ((hk.fsRecv ctx P t1 v hHdr e rec').run h1) → HPost res.2) :
    ∀ res ∈ support ((vRecv hk ctx P s c rec).run h), HPost res.2 := by
  intro ⟨vrRes, h'⟩ hmem; rw [vRecv_eq_bind] at hmem
  by_cases h1 : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hMidPost (hMid0 hPre)
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
    have hStep1 : HMid h₁ := by
      unfold vRecvStep1 at hmem1
      by_cases h2 : c.1.1 = s.tcur + 1
      · simp only [h2, ↓reduceIte] at hmem1; rcases hTn : c.1.2 with _ | Tn
        · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem1; rcases hmem1 with ⟨_, rfl⟩; exact hMid0 hPre
        · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem1
          obtain ⟨⟨srRes, h₁'⟩, hsr, hmem1⟩ := hmem1
          have hM := hStart (s.tcur + 1) s.γ s.root Tn (srRes, h₁') hPre hsr
          rcases srRes with _ | _ | ⟨γ', σ', rs⟩ <;>
            (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem1; rcases hmem1 with ⟨_, rfl⟩; exact hM)
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem1; rcases hmem1 with ⟨_, rfl⟩; exact hMid0 hPre
    rcases s₁? with _ | _ | s₁
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨_, rfl⟩; exact hMidPost hStep1
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨_, rfl⟩; exact hMidPost hStep1
    · rcases hvR1 : s₁.vR c.1.1 with _ | v
      · simp only [hvR1, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem2; rcases hmem2 with ⟨_, rfl⟩; exact hMidPost hStep1
      · simp only [hvR1, StateT.run_bind, mem_support_bind_iff] at hmem2
        obtain ⟨⟨frRes, h₂⟩, hfr, hmem2⟩ := hmem2
        have hP := hFs c.1.1 v c.1 c.2 rec (frRes, h₂) hStep1 hfr
        rcases frRes with _ | _ | ⟨v', i, m⟩ <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem2; rcases hmem2 with ⟨_, rfl⟩; exact hP)

private theorem commitE_fsMultiBucketAuth_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool)
    (s : GameState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E))
    (P : Party) (old new : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : Pos)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiBucketAuthState T RSt K I E)) :
    (commitE (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la)
      s P old new pos).run es =
      pure (some { s.accept P new pos with st := Function.update (s.accept P new pos).st P new },
        es) := by
  unfold commitE
  simp only [pure_bind, run_liftH_bind, hooksFSMultiBucketAuth, StateT.run_pure]

private theorem implFSMultiBucketAuth_step
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] (L B_q : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) {m : ℕ} (Δcka qep maxSkip : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiBucketAuthState T RSt K I E)) (winEp : Option ℕ)
    (q_sm : (spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B_q (m + 1) es.g) (hPre : FSMultiBucketStepBounded B_q (m + 1) es.h) :
    ∀ res ∈ support ((implFSMultiBucketAuth
        (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la)
        Δcka qep maxSkip gMain tL (.inr q_sm)).run (es, winEp)),
      FSMultiBucketStepBounded B_q m res.2.1.h ∧ SMEngineInv L B_q m res.2.1.g := by
  have hm1B : m + 1 ≤ B_q := by have := hInv.leaks_le; omega
  have hPost0 : FSMultiBucketStepBounded B_q m es.h := hPre.mono (Nat.le_succ m)
  have hInvQ : SMEngineInv L B_q m es.g := hInv.mono (Nat.le_succ m)
  let HPre : FSMultiBucketAuthState T RSt K I E → Prop := FSMultiBucketStepBounded B_q (m + 1)
  let HMid : FSMultiBucketAuthState T RSt K I E → Prop := fun h =>
    (∀ t, (h.fTable t).length + m ≤ B_q + 1) ∧ (∀ t, (h.sessions t).length + m ≤ B_q + 1) ∧
    ∀ idx bk, h.book idx = some bk → bk.fsTrans.length + (m + 1) ≤ B_q
  let HPost : FSMultiBucketAuthState T RSt K I E → Prop := FSMultiBucketStepBounded B_q m
  have hMid0 : HPre es.h → HMid es.h := fun hp =>
    ⟨fun t => by have := hp.1 t; omega, fun t => by have := hp.2.1 t; omega, hp.2.2⟩
  have hMidPost : ∀ {h1}, HMid h1 → HPost h1 := fun hm =>
    ⟨hm.1, hm.2.1, fun idx bk hbk => by have := hm.2.2 idx bk hbk; omega⟩
  let hk := hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la
  let cfg := bucketAuthCfg (M := M) Δcka tL
  have hvSend : ∀ ctx P s msg pair r res,
      res ∈ support ((vSend hk ctx P s msg pair r).run es.h) → HPost res.2 := by
    intro ctx P s msg pair r res hmem
    refine vSend_preserve_h_only hk ctx P s msg pair r es.h hPre hMid0 hMidPost
      (fun t0 γ0 σ0 r0 res' hp hss => ?_) (fun {h1} t1 v hHdr m' pair' res' hm hfs => ?_) res hmem
    · have hP := hooksFSMultiBucketAuth_startSend_preserve L cka prng fs Δcka qep gMain
        tL par la ctx P t0 γ0 σ0 r0 es.h res' hss
      refine ⟨fun t' => by have := hp.1 t'; have := hP.1 t'; omega,
        fun t' => by have := hp.2.1 t'; have := hP.2.1 t'; omega, by rw [hP.2.2]; exact hp.2.2⟩
    · have hP := hooksFSMultiBucketAuth_fsSend_preserve L cka prng fs Δcka qep gMain
        tL par la ctx P t1 v hHdr m' pair' h1 res' hfs
      exact ⟨by rw [hP.1]; exact hm.1, by rw [hP.2.1]; exact hm.2.1,
        fsBookStep_apply hm1B hm.2.2 hP.2.2⟩
  have hvRecv : ∀ ctx P s c rec res,
      res ∈ support ((vRecv hk ctx P s c rec).run es.h) → HPost res.2 := by
    intro ctx P s c rec res hmem
    refine vRecv_preserve_h_only hk ctx P s c rec es.h hPre hMid0 hMidPost
      (fun t0 γ0 σ0 Tn res' hp hsr => ?_) (fun {h1} t1 v hHdr e rec' res' hm hfr => ?_) res hmem
    · have hP := hooksFSMultiBucketAuth_startRecv_preserve L cka prng fs Δcka qep gMain
        tL par la ctx P t0 γ0 σ0 Tn es.h res' hsr
      refine ⟨fun t' => by have := hp.1 t'; have := hP.1 t'; omega,
        fun t' => by have := hp.2.1 t'; have := hP.2.1 t'; omega, by rw [hP.2.2]; exact hp.2.2⟩
    · have hP := hooksFSMultiBucketAuth_fsRecv_preserve L cka prng fs Δcka qep gMain
        tL par la ctx P t1 v hHdr e rec' h1 res' hfr
      exact ⟨by rw [hP.1]; exact hm.1, by rw [hP.2.1]; exact hm.2.1,
        fsBookStep_apply hm1B hm.2.2 (fsBookStep_mono (Nat.zero_le 1) hP.2.2)⟩
  intro ⟨out, es', winEp'⟩ hmem
  rcases q_sm with (((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (out, (es', winEp')) ∈ support ((do
      let (es0, winEp0) : FSMultiBucketAuthEState Γ T RSt SS RS M E K I ← get
      if es0.abort || es0.g.win then return none
      match es0.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => return none
      | some s₁ =>
        let (res, h') ← StateT.lift ((vSend hk s₁ P (s₁.st P) msg none r).run es0.h)
        match res with
        | none => set ({ es0 with h := h', abort := true }, winEp0); return none
        | some (st', ct) =>
          let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, msg, ct⟩
          set ({ es0 with g := s₁.record (2 + Δcka) P st' recE false, h := h' }, winEp0)
          return some ct).run (es, winEp)) at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl, rfl⟩; exact ⟨hPost0, hInvQ⟩
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl, rfl⟩; exact ⟨hPost0, hInvQ⟩
      · simp only [hep, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
        have hPres := hvSend s₁ P (s₁.st P) msg none r (vsRes, h') hvs
        rcases vsRes with _ | ⟨st', ct⟩
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl, rfl⟩; exact ⟨hPres, hInvQ⟩
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl, rfl⟩; exact ⟨hPres, hInv.epMgmt_record hep st' _ false⟩
  · change (out, (es', winEp')) ∈ support ((pure none :
      StateT (FSMultiBucketAuthEState Γ T RSt SS RS M E K I) _ _).run (es, winEp)) at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl, rfl⟩; exact ⟨hPost0, hInvQ⟩
  · change (out, (es', winEp')) ∈ support ((do
      let (es0, winEp0) : FSMultiBucketAuthEState Γ T RSt SS RS M E K I ← get
      let (out, es1) ← StateT.lift ((deliverE hk maxSkip cfg (P, c)).run es0)
      set (es1, winEp0); return out).run (es, winEp)) at hmem
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨⟨out', es1⟩, hmemD, _, hEs, _⟩ := hmem; rw [hEs]
    refine ⟨?_, deliverE_inv hk cfg es (P, c) hInv (out', es1) hmemD⟩
    unfold deliverE abortE at hmemD; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmemD
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmemD; rcases hmemD with ⟨_, rfl⟩; exact hPost0
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmemD
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmemD; rcases hmemD with ⟨_, rfl⟩; exact hPost0
      · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmemD
        obtain ⟨⟨vrRes, h'⟩, hvr, hmemD⟩ := hmemD
        have hPres := hvRecv es.g P (es.g.st P) c (some r) (vrRes, h') hvr
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hmemD; rcases hmemD with ⟨_, rfl⟩; exact hPres
        · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r) <;>
            (simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmemD; rcases hmemD with ⟨_, rfl⟩; exact hPres)
        · simp only [hk, StateT.run_bind, commitE_fsMultiBucketAuth_eq, pure_bind, StateT.run_modify,
            StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmemD
          rcases hmemD with ⟨_, rfl⟩; exact hPres
  · change (out, (es', winEp')) ∈ support ((do
      let (es0, winEp0) : FSMultiBucketAuthEState Γ T RSt SS RS M E K I ← get
      let wasWin := es0.g.win
      let isNewForged :=
        decide (c.1.1 = (es0.g.st P).tcur + 1) && !isHonestHdrMultiBucket es0.h c.1
      let (out, es1) ← StateT.lift ((injectE hk (2 + Δcka) qep cfg (P, c)).run es0)
      let winEp1 :=
        if !wasWin && es1.g.win && (gMain || isNewForged) then some c.1.1 else winEp0
      set (es1, winEp1); return out).run (es, winEp)) at hmem
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨⟨out', es1⟩, hmemI, _, hEs, _⟩ := hmem; rw [hEs]
    refine ⟨?_, injectE_inv hk cfg es (P, c) hInv (out', es1) hmemI⟩
    unfold injectE abortE at hmemI; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmemI
    by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
        !(es.g.safeInj (2 + Δcka)))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmemI; rcases hmemI with ⟨_, rfl⟩; exact hPost0
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        mem_support_bind_iff] at hmemI
      obtain ⟨⟨vrRes, h'⟩, hvr, hmemI⟩ := hmemI
      have hPres := hvRecv es.g P (es.g.st P) c none (vrRes, h') hvr
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hmemI; rcases hmemI with ⟨_, rfl⟩; exact hPres
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmemI
        rcases hmemI with ⟨_, rfl⟩; exact hPres
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmemI; rcases hmemI with ⟨_, rfl⟩; exact hPres
        · simp only [hqep, ↓reduceIte] at hmemI
          by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩
          · simp only [hk, htriv, ↓reduceIte, StateT.run_bind, commitE_fsMultiBucketAuth_eq, pure_bind,
              StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmemI; rcases hmemI with ⟨_, rfl⟩; exact hPres
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmemI
            by_cases hf : cfg.injectFull t' <;>
              (simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
                StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmemI; rcases hmemI with ⟨_, rfl⟩; exact hPres)
  · change (out, (es', winEp')) ∈ support ((do
      let (es0, winEp0) : FSMultiBucketAuthEState Γ T RSt SS RS M E K I ← get
      if es0.abort || es0.g.win || !(es0.g.corrAllowed P) then return none
      let s₁ := es0.g.afterCorr P
      let (res, h') ← StateT.lift ((hk.reveal es0.g P (es0.g.st P)).run es0.h)
      match res with
      | none => set ({ es0 with h := h', abort := true }, winEp0); return none
      | some stOut => set ({ es0 with g := s₁, h := h' }, winEp0); return some stOut).run
        (es, winEp)) at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl, rfl⟩; exact ⟨hPost0, hInvQ⟩
    · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, hrev, hmem⟩ := hmem
      have hP := hooksFSMultiBucketAuth_reveal_preserve L cka prng fs Δcka qep gMain
        tL par la es.g P (es.g.st P) es.h (revRes, h') hrev
      have hFsLe := fsBookStep_apply hm1B hPre.2.2 (fsBookStep_mono (Nat.zero_le 1) hP.2.2)
      have hPres : FSMultiBucketStepBounded B_q m h' :=
        ⟨by rw [hP.1]; exact hPost0.1, by rw [hP.2.1]; exact hPost0.2.1, hFsLe⟩
      rcases revRes with _ | stOut
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl, rfl⟩; exact ⟨hPres, hInvQ⟩
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl, rfl⟩; exact ⟨hPres, hInv.afterCorr P⟩

private theorem rdec_mbHandle_eval
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δcka qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (hDefaultE : defaultE = default)
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hHk : HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      hsMBEnc (FSMultiBucketHBounded L) (HBoundedPost := FSMultiBucketHBoundedPost L)
      (VROk := fun _ => True)
      (mbHooksC L B Δcka qep gMain tL par la)
      (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la))
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiBucketAuthState T RSt K I E))
    (winEp : Option ℕ)
    (q : (spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : FSMultiBucketHBounded L es.h) (hBound : SMStateBoundedEngine L es.g) :
    ((fun p => ((SMCodec).rdec q p.1, p.2)) <$>
      (mbProg L B Δcka qep maxSkip gMain la tL par).handle.eval
        (.cons (esEnc vpMEnc hsMBEnc es, winEp) (.cons ((SMCodec).qenc q) .nil))) =
      Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
        (implFSMultiBucketAuth (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la)
          Δcka qep maxSkip gMain tL (.inr q)).run (es, winEp) := by
  let C := SMCodec
  change ((fun p => (C.rdec q p.1, p.2)) <$>
    (mbProg L B Δcka qep maxSkip gMain la tL par).handle.eval
      (.cons (esEnc vpMEnc hsMBEnc es, winEp) (.cons (C.qenc q) .nil))) = _
  let hkC := mbHooksC L B Δcka qep gMain tL par la
  let hk := hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la
  let cfgC := bucketAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) Δcka tL
  let cfg := bucketAuthCfg (M := M) Δcka tL
  have hCfg := bucketAuthCfgEC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (M := M) Δcka tL
  dsimp only [redFSAuthMultiBucketProg]
  set ρ₀ := Env.cons (t := @fsMultiBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E)
    (esEnc vpMEnc hsMBEnc es, winEp) (.cons (C.qenc q) .nil)
  rw [eval_bind_ret]
  have h0 : (Expr.pair (.fst (Expr.v0 (O := OO)))
      (.pair (.snd .v0) .v1)).eval ρ₀ =
      (esEnc vpMEnc hsMBEnc es, winEp, C.qenc q) := rfl
  erw [h0]; clear h0
  set ρ_top := Env.cons (t := .prod _ (.prod (.opt .nat) C.Q))
    (esEnc vpMEnc hsMBEnc es, winEp, C.qenc q) ρ₀
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change _ = Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
      (do
        let (es0, winEp0) : FSMultiBucketAuthEState Γ T RSt SS RS M E K I ← get
        if es0.abort || es0.g.win then return none
        match es0.g.epMgmt (2 + Δcka) qep P r.isSome with
        | none => return none
        | some s₁ =>
          let (res, h') ← StateT.lift ((vSend hk s₁ P (s₁.st P) m none r).run es0.h)
          match res with
          | none => set ({ es0 with h := h', abort := true }, winEp0); return none
          | some (st', ct) =>
            let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
            set ({ es0 with g := s₁.record (2 + Δcka) P st' recE false, h := h' }, winEp0)
            return some ct).run (es, winEp)
    rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inl' rfl]
    refine with_comp_env fun ρ₁ hρ₁ => ?_
    rw [eval_bind_ret]
    have hArg : (Expr.v0 (O := OO)).eval ρ₁ = (partyEnc P, m, r) := by subst hρ₁; rfl
    rw [hArg]; clear hArg
    set ρ₂ := Env.cons (t := .prod .bool (.prod (.base CKASort.msg) (.opt (.base CKASort.ccoins))))
      (partyEnc P, m, r) ρ₁
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    change _ <$> (Comp.ite _ _ _).eval ρ₂ = _
    rw [eval_ite]
    have hCond1 : (orE (esAbort (.fst (Expr.v5 (O := OO))))
        (cGsWin (esG (.fst .v5)))).eval ρ₂ = (es.abort || es.g.win) := by
      subst hρ₁
      simp [ρ₂, ρ_top, orE_eval, esAbort, cGsWin, esG, esEnc, cGsEnc,
        Expr.eval, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
    rw [hCond1]; clear hCond1
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte]; subst hρ₁
      simp [C, ρ₂, ρ_top, ρ₀, Comp.eval, StateT.run_pure, Prod.map,
        Expr.eval, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]; rw [eval_caseOpt]
      have hIsSome : (isSomeE (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₂ = r.isSome := by
        cases r <;> rfl
      have hEp : (cEpMgmtE (2 + Δcka) qep (esG (.fst (Expr.v5 (O := OO)))) (.fst .v0)
          (isSomeE (.snd (.snd .v0)))).eval ρ₂ =
          (es.g.epMgmt (2 + Δcka) qep P r.isSome).map (cGsEnc vpMEnc) := by
        have := cEpMgmtE_eval vpMEnc (O' := OO) (2 + Δcka) qep
          (esG (.fst .v5)) (.fst .v0) (isSomeE (.snd (.snd .v0)))
          ρ₂ es.g P (by subst hρ₁; rfl) (by subst hρ₁; rfl)
        rw [hIsSome] at this; exact this
      rw [hEp]; clear hEp hIsSome
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · subst hρ₁
        simp [C, ρ₂, ρ_top, ρ₀, Comp.eval, StateT.run_pure, Prod.map,
          Expr.eval, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
      · simp only [Option.map_some]
        set ρ₃ := Env.cons (t := cGsTy (@fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E))
          (cGsEnc vpMEnc s₁) ρ₂
        change _ <$> (Comp.bind (vSendC _ _ _ _ _ _ _ _) _).eval ρ₃ = _
        rw [eval_bind]
        have hStP : (pGet (cGsSt (Expr.v0 (O := OO))) (.fst .v1)).eval ρ₃ = vpMEnc (s₁.st P) :=
          pGet_eval (cGsSt .v0) (.fst .v1) ρ₃ (fun Q => vpMEnc (s₁.st Q)) P rfl rfl
        have hVSend := vSendC_eval hDefaultE hsMBEnc (FSMultiBucketHBounded L) hkC hk hHk
          (esH (.fst .v6)) .v0 (.fst .v1) (pGet (cGsSt .v0) (.fst .v1))
          (.fst (.snd .v1)) .none (.snd (.snd .v1))
          ρ₃ es.h s₁ P (s₁.st P) m none r hHB (by subst hρ₁; rfl) rfl rfl hStP rfl rfl rfl
        rw [hVSend, bind_map_left, StateT.run_bind, StateT.run_lift, bind_assoc, map_bind, map_bind]
        refine bind_congr fun ⟨vsRes, h'⟩ => ?_
        rcases vsRes with _ | ⟨st', ct⟩
        · dsimp only [Prod.map, Option.map_none, id_eq]; rw [eval_caseOpt_none' rfl]; subst hρ₁
          simp [C, ρ₃, ρ₂, ρ_top, ρ₀, Comp.eval, StateT.run_set, Prod.map, esMk, esG, esEnc,
            Expr.eval, Expr.v0, Expr.v7, Env.get_cons_zero, Env.get_cons_succ]
        · dsimp only [Prod.map, Option.map_some, id_eq]; rw [eval_caseOpt_some' rfl]
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure]
          let mVpTy := @fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E
          let mbHsTy := @fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
          let hdrCtTy := ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
          set ρ₄ := Env.cons (t := .prod mVpTy hdrCtTy) (vpMEnc st', ct)
            (Env.cons (t := .prod (.opt (.prod mVpTy hdrCtTy)) mbHsTy)
              (some (vpMEnc st', ct), hsMBEnc h') ρ₃)
          change _ <$> (Comp.ret _).eval ρ₄ = _
          have hEp4 : (pGet (cGsEpoch (Expr.v2 (O := OO))) (.fst .v3)).eval ρ₄ = s₁.epoch P :=
            pGet_eval (cGsEpoch .v2) (.fst .v3) ρ₄ s₁.epoch P rfl rfl
          have hIdx4 : (pGet (cGsIdx (Expr.v2 (O := OO))) (.fst .v3)).eval ρ₄ = s₁.idx P :=
            pGet_eval (cGsIdx .v2) (.fst .v3) ρ₄ s₁.idx P rfl rfl
          have hRecE : (Expr.pair
              (.pair (.fst (Expr.v3 (O := OO)))
                (.pair (pGet (cGsEpoch .v2) (.fst .v3))
                  (.add (pGet (cGsIdx .v2) (.fst .v3)) (.nat 1))))
              (.pair (.fst (.snd .v3)) (.snd .v0))).eval ρ₄ =
              cRecEnc ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ := by
            simp only [Expr.eval, hEp4, hIdx4]; rfl
          have hRecord := cRecordE_eval vpMEnc (O' := OO) L (2 + Δcka)
            (Expr.v2 (O := OO)) (.fst .v3) (.fst .v0)
            (.pair (.pair (.fst .v3)
              (.pair (pGet (cGsEpoch .v2) (.fst .v3))
                (.add (pGet (cGsIdx .v2) (.fst .v3)) (.nat 1))))
              (.pair (.fst (.snd .v3)) (.snd .v0)))
            (.bool false) ρ₄ s₁ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
            ((epMgmt_lists_eq hep).2.2.1 ▸ hBound.comp_le) rfl rfl rfl hRecE
          simp only [eval_ret, esMk, pair_eval, hRecord]; subst hρ₁
          simp [C, ρ₄, ρ₃, ρ₂, ρ_top, ρ₀, esAbort, esEnc, Prod.map,
            Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  · change _ = Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
      (pure none : StateT (FSMultiBucketAuthEState Γ T RSt SS RS M E K I) _ _).run (es, winEp)
    rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inr' rfl]
    refine with_comp_env fun ρ₁ hρ₁ => ?_; subst hρ₁
    simp [C, ρ_top, ρ₀, Comp.eval, StateT.run_pure, Prod.map,
      Expr.eval, Expr.v4, Env.get_cons_zero, Env.get_cons_succ]
  · change _ = Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
      (do
        let (es0, winEp0) : FSMultiBucketAuthEState Γ T RSt SS RS M E K I ← get
        let (out, es') ← StateT.lift ((deliverE hk maxSkip cfg (P, c)).run es0)
        set (es', winEp0); return out).run (es, winEp)
    rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inr' rfl]
    refine with_comp_env fun ρ₁ hρ₁ => ?_; rw [eval_bind]
    have hDel := deliverEC_eval hsMBEnc (FSMultiBucketHBounded L) hkC hk hHk
      L maxSkip cfgC cfg hCfg heqT heqM heqE (.fst .v3) .v0 ρ₁ es P c hHB hBound
      (fun _ _ _ => trivial) (by subst hρ₁; rfl) (by subst hρ₁; rfl)
    rw [hDel, bind_map_left, map_bind]
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
      pure_bind, bind_assoc, map_bind]
    refine bind_congr fun ⟨out, es'⟩ => ?_; subst hρ₁
    rcases out with _ | (_ | m') <;>
      simp [C, ρ_top, ρ₀, _root_.CryptoGames.SM.smRrDec,
        _root_.CryptoGames.SM.smRrEnc, Comp.eval, Prod.map, Expr.eval, Expr.v0, Expr.v4,
        Env.get_cons_zero, Env.get_cons_succ]
  · change _ = Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
      (do
        let (es0, winEp0) : FSMultiBucketAuthEState Γ T RSt SS RS M E K I ← get
        let wasWin := es0.g.win
        let isNewForged :=
          decide (c.1.1 = (es0.g.st P).tcur + 1) && !isHonestHdrMultiBucket es0.h c.1
        let (out, es') ← StateT.lift ((injectE hk (2 + Δcka) qep cfg (P, c)).run es0)
        let winEp' :=
          if !wasWin && es'.g.win && (gMain || isNewForged) then some c.1.1 else winEp0
        set (es', winEp'); return out).run (es, winEp)
    rw [eval_caseSum_inl' rfl, eval_caseSum_inr' rfl]
    refine with_comp_env fun ρ₁ hρ₁ => ?_; rw [eval_bind]
    have hInj := injectEC_eval hsMBEnc (FSMultiBucketHBounded L) hkC hk hHk
      L (2 + Δcka) qep cfgC cfg hCfg heqT heqE (.fst .v2) .v0 ρ₁ es P c hHB hBound
      (fun _ _ _ => trivial) (by subst hρ₁; rfl) (by subst hρ₁; rfl)
    rw [hInj, bind_map_left, map_bind]
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
      pure_bind, bind_assoc, map_bind]
    refine bind_congr fun ⟨out, es'⟩ => ?_
    refine with_comp_env fun ρ₂ hρ₂ => ?_
    have hStP : (pGet (cGsSt (esG (.fst (Expr.v3 (O := OO))))) (.fst .v1)).eval ρ₂ =
        vpMEnc (es.g.st P) :=
      pGet_eval (cGsSt (esG (.fst .v3))) (.fst .v1) ρ₂
        (fun Q => vpMEnc (es.g.st Q)) P (by subst hρ₂; subst hρ₁; rfl) (by subst hρ₂; subst hρ₁; rfl)
    set honExpr := isHonestHdrMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (SS := SS) (RS := RS) (esH (.fst .v3)) (.fst (.snd .v1)) with hHonDef
    set tcurExpr := vpTcurNat (pGet (cGsSt (esG (.fst (Expr.v3 (O := OO))))) (.fst .v1))
      with hTcurDef
    have hHon : honExpr.eval ρ₂ = isHonestHdrMultiBucket es.h c.1 := by
      have hH := isHonestHdrMultiBucketE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (SS := SS) (RS := RS)
        heqT (esH (.fst .v3)) (.fst (.snd .v1)) ρ₂ es.h
        (by simp [hρ₂, hρ₁, ρ_top, esH, esEnc, Expr.eval, Expr.v3,
              Env.get_cons_zero, Env.get_cons_succ])
      have hHdr : (Expr.fst (.snd (Expr.v1 (O := OO)))).eval ρ₂ = c.1 := by
        simp [hρ₂, hρ₁, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
      rw [hHdr] at hH; exact hH
    have hTcur : tcurExpr.eval ρ₂ = (es.g.st P).tcur := by
      simp [hTcurDef, vpTcurNat, hStP, vpTblEnc, vpEnc, Expr.eval]
    simp only [eval_ret, orE_eval, Expr.eval, hTcur, hHon]
    clear hStP hHon hTcur hHonDef hTcurDef honExpr tcurExpr
    subst hρ₂; subst hρ₁
    rcases out with _ | (_ | m') <;>
      simp [C, ρ_top, ρ₀, _root_.CryptoGames.SM.smRrDec,
        _root_.CryptoGames.SM.smRrEnc, cGsWin, esG, esEnc, cGsEnc, Prod.map,
        Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
  · change _ = Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
      (do
        let (es0, winEp0) : FSMultiBucketAuthEState Γ T RSt SS RS M E K I ← get
        if es0.abort || es0.g.win || !(es0.g.corrAllowed P) then return none
        let s₁ := es0.g.afterCorr P
        let (res, h') ← StateT.lift ((hk.reveal es0.g P (es0.g.st P)).run es0.h)
        match res with
        | none => set ({ es0 with h := h', abort := true }, winEp0); return none
        | some stOut => set ({ es0 with g := s₁, h := h' }, winEp0); return some stOut).run
        (es, winEp)
    rw [eval_caseSum_inr' rfl]
    refine with_comp_env fun ρ₁ hρ₁ => ?_
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rw [eval_ite]
    have hCorrOk : (cCorrAllowedE L (esG (.fst (Expr.v1 (O := OO)))) .v0).eval ρ₁ =
        es.g.corrAllowed P :=
      cCorrAllowedE_eval (vpEncFn := vpMEnc) (O' := OO) L (esG (.fst .v1)) .v0 ρ₁ es.g P
        hBound.trans_le hBound.chall_le hBound.comp_le (by subst hρ₁; rfl) (by subst hρ₁; rfl)
    have hRefuse : (orE (esAbort (.fst (Expr.v1 (O := OO))))
        (orE (cGsWin (esG (.fst .v1)))
          (.not (cCorrAllowedE L (esG (.fst .v1)) .v0)))).eval ρ₁ =
        (es.abort || es.g.win || !(es.g.corrAllowed P)) := by
      simp only [orE_eval, not_eval, hCorrOk]; subst hρ₁
      simp [ρ_top, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v1, Bool.or_assoc]
    rw [hRefuse]; clear hRefuse
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
    · simp only [href, ↓reduceIte]; subst hρ₁
      simp [C, ρ_top, ρ₀, Comp.eval, StateT.run_pure, Prod.map,
        Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, eval_bind]
      have hStP : (pGet (cGsSt (esG (.fst (Expr.v1 (O := OO))))) .v0).eval ρ₁ = vpMEnc (es.g.st P) :=
        pGet_eval (cGsSt (esG (.fst .v1))) .v0 ρ₁
          (fun Q => vpMEnc (es.g.st Q)) P (by subst hρ₁; rfl) (by subst hρ₁; rfl)
      have hRev := hHk.reveal_eval (esH (.fst .v1)) (esG (.fst .v1)) .v0
        (pGet (cGsSt (esG (.fst .v1))) .v0) ρ₁ es.h es.g P (es.g.st P) hHB
        (by subst hρ₁; rfl) (by subst hρ₁; rfl) (by subst hρ₁; rfl) hStP
      dsimp only [hkC, hooksFSMultiBucketAuthC] at hRev
      rw [hRev, bind_map_left, StateT.run_bind, StateT.run_lift, bind_assoc, map_bind, map_bind]
      refine bind_congr fun ⟨revRes, h'⟩ => ?_
      rcases revRes with _ | stOut
      · dsimp only [Prod.map, Option.map_none, id_eq]; rw [eval_caseOpt_none' rfl]; subst hρ₁
        simp [C, ρ_top, ρ₀, Comp.eval, StateT.run_set, Prod.map, esMk, esG, esEnc, Expr.eval,
          Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
      · dsimp only [Prod.map, Option.map_some, id_eq]; rw [eval_caseOpt_some' rfl]
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure]
        let mbHsTy := @fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
        let psTy := ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
        set ρ₂ := Env.cons (t := psTy) (ckaPsEnc stOut)
          (Env.cons (t := .prod (.opt psTy) mbHsTy) (some (ckaPsEnc stOut), hsMBEnc h') ρ₁)
        change _ <$> (Comp.ret _).eval ρ₂ = _
        have hAfter := cAfterCorrE_eval (vpEncFn := vpMEnc) (O' := OO) L
          (esG (.fst .v3)) .v2 ρ₂ es.g P hBound.trans_le hBound.comp_u
          (by subst hρ₁; rfl) (by subst hρ₁; rfl)
        simp only [eval_ret, esMk, pair_eval, hAfter]; subst hρ₁
        simp [C, ρ₂, ρ_top, ρ₀, _root_.CryptoGames.CKA.ckaPsDec,
          ckaPsEnc, esAbort, esEnc, Prod.map, Expr.eval, Expr.v0, Expr.v1, Expr.v3,
          Env.get_cons_zero, Env.get_cons_succ]

private theorem simulateQ_implFSMultiBucketAuth_eval
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (hB1 : B_q + 1 ≤ L)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
          (FSMultiBucketAuthState T RSt K I E))
        (winEp : Option ℕ),
        FSMultiBucketStepBounded B_q qAdv es.h → SMEngineInv L B_q qAdv es.g →
        (simulateQ (handlerImpl (C := SMCodec)
            (mbProg L B Δcka qep fs.maxSkip gMain la tL par).handle) oa).run
            (esEnc vpMEnc hsMBEnc es, winEp) =
          (Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
            (simulateQ (implFSMultiBucketAuth
              (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la)
              Δcka qep fs.maxSkip gMain tL) oa).run (es, winEp)) ∧
        ∀ res ∈ support ((simulateQ (implFSMultiBucketAuth
            (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la)
            Δcka qep fs.maxSkip gMain tL) oa).run (es, winEp)),
          SMEngineInv L B_q 0 res.2.1.g := by
  have hHk := hooksFSMultiBucketAuthC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqM := eqM) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng fs L B Δcka qep gMain tL par la
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend heqT heqI heqE
    hSampCCoins hSampI hSampK hFsRecvB
  let hk := hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la
  let C := SMCodec
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es winEp _ hInv
    refine ⟨by simp only [simulateQ_pure, StateT.run_pure, Prod.map, map_pure]; rfl, ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact hInv.mono (Nat.zero_le qAdv)
  | query_bind q mx ih =>
    intro qAdv hq es winEp hHB hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    erw [run_simulateQ_query_bind, run_simulateQ_query_bind, map_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := C)
            (mbProg L B Δcka qep fs.maxSkip gMain la tL par).handle) (.inl n)).run
            (esEnc vpMEnc hsMBEnc es, winEp) =
          (fun u => (u, (esEnc vpMEnc hsMBEnc es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        dsimp only [handlerImpl, redFSAuthMultiBucketProg, fsaeadMultiBucketIface]
        simp [StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (implFSMultiBucketAuth hk Δcka qep fs.maxSkip gMain tL (.inl n)).run (es, winEp) =
          (fun u => (u, (es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        simp [implFSMultiBucketAuth, StateT.run_lift, map_eq_bind_pure_comp]
      erw [hCoinL, hCoinR, bind_map_left, bind_map_left]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es winEp hHB hInv).1, ?_⟩
      intro res hmem
      rw [bind_map_left, mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es winEp hHB hInv).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hStepEval := rdec_mbHandle_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqI := eqI) (lam := lam)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        cka prng fs L B Δcka qep fs.maxSkip gMain la tL par
        hDefaultE heqT heqM heqE hHk es winEp t (hHB.toHBounded hB1) hInv.toBoundedEngine
      have hStep :
          ((handlerImpl (C := C)
            (mbProg L B Δcka qep fs.maxSkip gMain la tL par).handle) (.inr t)).run
            (esEnc vpMEnc hsMBEnc es, winEp) =
          Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
            (implFSMultiBucketAuth hk Δcka qep fs.maxSkip gMain tL (.inr t)).run (es, winEp) := by
        have hLHS :
            ((handlerImpl (C := C)
              (mbProg L B Δcka qep fs.maxSkip gMain la tL par).handle) (.inr t)).run
              (esEnc vpMEnc hsMBEnc es, winEp) =
            ((fun p => (C.rdec t p.1, p.2)) <$>
              (mbProg L B Δcka qep fs.maxSkip gMain la tL par).handle.eval
                (.cons (esEnc vpMEnc hsMBEnc es, winEp) (.cons (C.qenc t) .nil))) := by
          dsimp only [handlerImpl, StateT.run, StateT.mk]
          simp only [map_eq_bind_pure_comp, Function.comp_def]; rfl
        exact hLHS.trans hStepEval
      erw [hStep, bind_map_left]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁, winEp₁⟩ hmem => ?_, ?_⟩
      · have hSt := implFSMultiBucketAuth_step L B_q cka prng fs Δcka qep fs.maxSkip gMain
          tL par la es winEp t hInv hHB (u, es₁, winEp₁) hmem
        exact (ih u (hqm u) es₁ winEp₁ hSt.1 hSt.2).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁, winEp₁⟩, hmem₁, hmem₂⟩ := hmem
        have hSt := implFSMultiBucketAuth_step L B_q cka prng fs Δcka qep fs.maxSkip gMain
          tL par la es winEp t hInv hHB (u, es₁, winEp₁) hmem₁
        exact (ih u (hqm u) es₁ winEp₁ hSt.1 hSt.2).2 res hmem₂

private def initFSMultiBucketAuthRaw
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par b : Bool) :
    TComp (FSMultiSpec SS RS T M E)
      (EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
        (FSMultiBucketAuthState T RSt K I E)) := do
  let kr ← sampleT KR
  let kc ← sampleT KC
  let ((σ, kVal, sid), h₁) ←
    (rootFSMultiBucketAuth (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
      prng Δcka qep tL par 0 false lam (prng.init kr)).run {}
  let (optIdx, h₂) := if gMain then regSessOptMultiBucket L true tL 0 sid h₁ else (none, h₁)
  let ssv0 : SS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initSender kVal)
    | some sIdx => .inr sIdx
  let rsv0 : RS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initReceiver kVal)
    | some sIdx => .inr sIdx
  let pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σ ssv0 rsv0
  return { g := { st := fun | .A => pAB.1 | .B => pAB.2, b := b }, h := h₂, abort := false }

private theorem initFSMultiBucketAuthEStateC_eval
    [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hPrngInit : prngInit = prng.init) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqI : eqI = (· == ·))
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR)) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    {Γ'} (bE : Expr OO Γ' .bool) (ρ : Env Γ') :
    (mbInitC L Δcka qep gMain tL par bE).eval ρ =
      esEnc vpMEnc hsMBEnc <$>
        initFSMultiBucketAuthRaw L cka prng fs lam Δcka qep gMain tL par (bE.eval ρ) := by
  let IIM := @fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
  let mbHsTy := @fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
  unfold initFSMultiBucketAuthEStateC initFSMultiBucketAuthRaw
  rw [eval_bind_ret]
  set b : Bool := bE.eval ρ
  set ρ₁ := Env.cons (t := (.bool : Ty SP)) b ρ
  have hKR : (@Comp.sample _ _ _ OO IIM _ CKASamp.kr .unit).eval ρ₁ =
      (sampleT KR : TComp (FSMultiSpec SS RS T M E) KR) := by
    simp only [Comp.eval, IIM, fsaeadMultiBucketIface, prngSamplers, ckaSamplers, hSampKR, sampleT]
    exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ KR)
  rw [eval_bind, hKR, map_bind]
  refine bind_congr fun kr => ?_
  set ρ₂ := Env.cons (t := (.base .kr : Ty SP)) kr ρ₁
  have hKC : (@Comp.sample _ _ _ OO IIM _ CKASamp.kc .unit).eval ρ₂ =
      (sampleT KC : TComp (FSMultiSpec SS RS T M E) KC) := by
    simp only [Comp.eval, IIM, fsaeadMultiBucketIface, prngSamplers, ckaSamplers, hSampKC, sampleT]
    exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ KC)
  rw [eval_bind, hKC, map_bind]
  refine bind_congr fun kc => ?_
  set ρ₃ := Env.cons (t := (.base .kc : Ty SP)) kc ρ₂
  have hRoot := rootFSMultiBucketAuthC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins)
    prng hPrngUp heqI hSampI hSampK L Δcka qep tL par
    mbHsEmptyE (.nat 0) (.bool false)
    (Expr.op (O := OO) CKAOp.lamI .unit) (Expr.op (O := OO) CKAOp.prngInit .v1)
    ρ₃ ({} : FSMultiBucketAuthState T RSt K I E) rfl (Nat.zero_le L)
  have hT0 : (Expr.nat (O := OO) 0).eval ρ₃ = 0 := rfl
  have hPl0 : (Expr.bool (O := OO) false).eval ρ₃ = false := rfl
  have hLam : (Expr.op (O := OO) CKAOp.lamI .unit).eval ρ₃ = lam := rfl
  have hSig0 : (Expr.op (O := OO) CKAOp.prngInit .v1).eval ρ₃ = prng.init kr := by
    simp [ρ₃, ρ₂, prngOps, ckaOps, hPrngInit, Expr.eval, Expr.v1]
  rw [hT0, hPl0, hLam, hSig0] at hRoot
  rw [eval_bind, hRoot.1, bind_map_left, map_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨σ, kVal, sid⟩, h₁⟩ hmemR => ?_
  dsimp only
  have ⟨_, hSes₁, _⟩ := hRoot.2 ((σ, kVal, sid), h₁) hmemR
  have hSesL₁ : (h₁.sessions 0).length ≤ L := by
    dsimp only at hSes₁
    rw [hSes₁]
    exact Nat.zero_le L
  set ρ₄ := Env.cons
    (t := .prod (.prod (.base CKASort.sig) (.prod (.base CKASort.k) (.opt (.base CKASort.i)))) mbHsTy)
    ((σ, (kVal, sid)), hsMBEnc h₁) ρ₃
  set regCallE := regSessOptMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) L true tL (.snd .v0) (.nat 0) (.snd (.snd (.fst .v0)))
  set regPE : Expr OO _ (.prod (.opt .nat) mbHsTy) :=
    if gMain then regCallE else .pair .none (.snd .v0)
  set regRes : Option ℕ × FSMultiBucketAuthState T RSt K I E :=
    if gMain then regSessOptMultiBucket L true tL 0 sid h₁ else (none, h₁)
  let optIdx := regRes.1; let h₂ := regRes.2
  let ssv0 : SS ⊕ ℕ := match optIdx with | none => .inl (fs.initSender kVal) | some sIdx => .inr sIdx
  let rsv0 : RS ⊕ ℕ := match optIdx with | none => .inl (fs.initReceiver kVal) | some sIdx => .inr sIdx
  have hReg : regPE.eval ρ₄ = (optIdx, hsMBEnc h₂) := by
    cases gMain
    · rfl
    · simp only [regPE, regRes, optIdx, h₂, ↓reduceIte]
      have hR := (regSessOptMultiBucketE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (SS := SS) (RS := RS)
        heqI L true tL (.snd .v0) (.nat 0) (.snd (.snd (.fst .v0))) ρ₄ h₁ rfl hSesL₁).1
      dsimp only [regCallE]; exact hR
  change (Comp.ret _).eval ρ₄ = _; rw [eval_ret]
  set optIdxE : Expr OO _ (.opt .nat) := .fst regPE
  set h2E : Expr OO _ mbHsTy := .snd regPE
  set ssv0E : Expr OO _ (.sum (.base .ss) .nat) :=
    .caseOpt optIdxE (.inl (Expr.op (O := OO) CKAOp.fsInitSender (.fst (.snd (.fst .v0))))) (.inr .v0)
  set rsv0E : Expr OO _ (.sum (.base .rs) .nat) :=
    .caseOpt optIdxE (.inl (Expr.op (O := OO) CKAOp.fsInitReceiver (.fst (.snd (.fst .v0))))) (.inr .v0)
  set pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σ ssv0 rsv0
  have hOptIdxE : optIdxE.eval ρ₄ = optIdx := by simp [optIdxE, hReg, Expr.eval]
  have hh2 : h2E.eval ρ₄ = hsMBEnc h₂ := by simp [h2E, hReg, Expr.eval]
  have hSsv0E : ssv0E.eval ρ₄ = ssv0 := by
    simp only [ssv0E, ssv0, Expr.eval, hOptIdxE, optIdx]
    generalize regRes.1 = oi
    cases oi <;> simp [ρ₄, prngOps, ckaOps, hFsInitS, Expr.eval, Expr.v0, Env.get_cons_zero]
  have hRsv0E : rsv0E.eval ρ₄ = rsv0 := by
    simp only [rsv0E, rsv0, Expr.eval, hOptIdxE, optIdx]
    generalize regRes.1 = oi
    cases oi <;> simp [ρ₄, prngOps, ckaOps, hFsInitR, Expr.eval, Expr.v0, Env.get_cons_zero]
  set mkPE := mkPartiesE (O' := OO) (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .sum (.base .ss) .nat) (rsvT := .sum (.base .rs) .nat)
    (Expr.op (O := OO) CKAOp.ckaInitA .v1) (Expr.op (O := OO) CKAOp.ckaInitB .v1)
    (.fst (.fst .v0)) ssv0E rsv0E
  have hMkP := mkPartiesE_eval (O' := OO) (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .sum (.base .ss) .nat) (rsvT := .sum (.base .rs) .nat)
    (Expr.op (O := OO) CKAOp.ckaInitA .v1) (Expr.op (O := OO) CKAOp.ckaInitB .v1)
    (.fst (.fst .v0)) ssv0E rsv0E ρ₄
  have hMkP' : mkPE.eval ρ₄ = (vpMEnc pAB.1, vpMEnc pAB.2) := by
    rw [hMkP]; simp [hSsv0E, hRsv0E, ρ₄, ρ₃, ρ₂, ρ₁, prngOps, ckaOps, hInitA, hInitB, pAB,
      Prod.map, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  have hGs := cGsInitE_eval vpMEnc (O' := OO) (.fst mkPE) (.snd mkPE) .v3 ρ₄ pAB.1 pAB.2
    (by simp [Expr.eval, hMkP']) (by simp [Expr.eval, hMkP'])
  have hb3 : (Expr.v3 (O := OO)).eval ρ₄ = b := rfl
  simp only [esMk, pair_eval, hGs, hh2, hb3, esEnc, cGsEnc, Expr.eval, pAB,
    ssv0, rsv0, optIdx, h₂, map_pure]

private theorem initFSMultiBucketAuthRaw_inv
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (L B_q qAdv : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par b : Bool)
    (hqB : qAdv ≤ B_q) (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L) :
    ∀ es₀ ∈ support (initFSMultiBucketAuthRaw L cka prng fs lam Δcka qep gMain tL par b),
      FSMultiBucketStepBounded B_q qAdv es₀.h ∧ SMEngineInv L B_q qAdv es₀.g := by
  intro es₀ hmem
  unfold initFSMultiBucketAuthRaw at hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kr, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨⟨⟨σ, kVal, sid⟩, h₁⟩, hmemR, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem; subst hmem
  set regRes := if gMain then regSessOptMultiBucket L true tL 0 sid h₁ else (none, h₁)
  let ssv0 : SS ⊕ ℕ := match regRes.1 with | none => .inl (fs.initSender kVal) | some s => .inr s
  let rsv0 : RS ⊕ ℕ := match regRes.1 with | none => .inl (fs.initReceiver kVal) | some s => .inr s
  let pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σ ssv0 rsv0
  have hSm : SMEngineInv (Msg := M) (C := Header T × E) L B_q qAdv
      { st := fun | .A => pAB.1 | .B => pAB.2, b := b } :=
    (SMEngineInv.init (Msg := M) (C := Header T × E) _ b hB1 hBB).mono hqB
  have hRt := BucketFSAuthShallowBase.rootFSMultiBucketAuth_preserve
    prng Δcka qep tL par 0 false lam (prng.init kr) ({} : FSMultiBucketAuthState T RSt K I E)
    ((σ, kVal, sid), h₁) hmemR
  dsimp only at hRt
  have hReg : regRes.2.fTable = h₁.fTable ∧
      (∀ τ, (regRes.2.sessions τ).length ≤ 1) ∧ regRes.2.book = (fun _ => none) := by
    cases gMain
    · refine ⟨rfl, fun τ => ?_, hRt.2.2⟩
      simp only [regRes, Bool.false_eq_true, ↓reduceIte]; rw [hRt.2.1]; exact Nat.zero_le 1
    · have hP := BucketFSAuthShallowBase.regSessOptMultiBucket_preserve L true tL 0 sid h₁
      refine ⟨hP.1, fun τ => ?_, hP.2.2.trans hRt.2.2⟩
      have h1 := hP.2.1 τ; rw [hRt.2.1] at h1
      change ((regSessOptMultiBucket L true tL 0 sid h₁).2.sessions τ).length ≤ 0 + 1 at h1
      simpa only [regRes, ↓reduceIte, zero_add] using h1
  refine ⟨⟨fun τ => ?_, fun τ => ?_, fun sIdx bk hbk => ?_⟩, hSm⟩
  · dsimp only; rw [hReg.1]
    have hF := hRt.1 τ; change (h₁.fTable τ).length ≤ 0 + 1 at hF; omega
  · dsimp only; have := hReg.2.1 τ; omega
  · dsimp only at hbk; rw [hReg.2.2] at hbk; cases hbk

/-- Evaluation bridge for `redFSAuthMultiBucketProg` to shallow `redFSAuthMultiBucket` on
`fsClamp B fs` whenever `MakesAtMostQueries A qAdv`, `qAdv ≤ B_q`, and `B_q + 1 ≤ L`. -/
private theorem redFSAuthMultiBucketProg_eval_clamp
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR)) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hB1 : B_q + 1 ≤ L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (mbProg L B Δcka qep fs.maxSkip gMain la tL par).eval (fun _ => A) () =
      redFSAuthMultiBucket L cka prng (fsClamp B fs) lam Δcka qep gMain la tL par A := by
  have hBB : B_q * B_q ≤ L * L := Nat.mul_le_mul (by omega) (by omega)
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_); rcases x with _ | _ <;> simp_all [isGameQuery]
  have hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        (fsClamp B fs).receive rs hdr e := by
    intro rs hdr e; simp [hFsRecv, fsClamp]
  have hRHS : redFSAuthMultiBucket L cka prng (fsClamp B fs) lam Δcka qep gMain la tL par A =
      (do
        let es₀ ← initFSMultiBucketAuthRaw L cka prng (fsClamp B fs) lam Δcka qep gMain tL par false
        let (_, es', winEp') ←
          (simulateQ (implFSMultiBucketAuth
            (hooksFSMultiBucketAuth L cka prng (fsClamp B fs) Δcka qep gMain tL par la)
            Δcka qep (fsClamp B fs).maxSkip gMain tL) A).run (es₀, none)
        if la then return es'.h.lfWin
        else match winEp' with
          | none => return false
          | some tWin =>
            return (!es'.abort && es'.g.win &&
              authLosingConditionsAvoided (2 + Δcka) tL tWin es'.g &&
              (decide (Party.senderOf tWin == Party.A) == par))) := by
    unfold redFSAuthMultiBucket initFSMultiBucketAuth initFSMultiBucketAuthRaw
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind]
    exact bind_congr fun _ => bind_congr fun _ => bind_congr fun ⟨⟨_, _, _⟩, _⟩ => rfl
  rw [hRHS]; clear hRHS
  change (CostedReduction.eval
    (mbProg L B Δcka qep (fsClamp B fs).maxSkip gMain la tL par) (fun _ => A) ()) = _
  dsimp only [CostedReduction.eval, CostedReduction.impl, redFSAuthMultiBucketProg]
  have hInit := initFSMultiBucketAuthEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR
    heqI hSampKR hSampKC hSampI hSampK L Δcka qep gMain tL par
    (.bool false) (Env.cons (t := (.unit : Ty SP)) () .nil)
  rw [eval_bind, hInit]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero, bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSMultiBucketAuthRaw L cka prng (fsClamp B fs) lam Δcka qep gMain tL par false)
    fun es₀ hes₀ => ?_
  obtain ⟨hMB₀, hInv₀⟩ := initFSMultiBucketAuthRaw_inv L B_q qAdv cka prng (fsClamp B fs)
    lam Δcka qep gMain tL par false hqB hB1 hBB es₀ hes₀
  obtain ⟨hSim, hSimInv⟩ := simulateQ_implFSMultiBucketAuth_eval
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
    (lam := lam) (sampKR := sampKR) (sampKC := sampKC)
    cka prng (fsClamp B fs) L B B_q Δcka qep gMain la tL par
    hB1 hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK hFsRecvB
    hA' es₀ none hMB₀ hInv₀
  dsimp only [redFSAuthMultiBucketProg] at hSim
  erw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es', winEp'⟩ hes' => ?_
  have hBnd' := (hSimInv (b', es', winEp') hes').toBoundedEngine
  dsimp only [Prod.map, id_eq]
  rw [eval_bind_ret]
  let redEsTy := @fsMultiBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E
  set ρ_f := Env.cons (t := redEsTy) (esEnc vpMEnc hsMBEnc es', winEp')
    (Env.cons (t := (.bool : Ty SP)) b' .nil)
  have hPair : (Expr.pair (.fst (Expr.var (O := OO) .zero))
      (.snd (.var .zero))).eval ρ_f = (esEnc vpMEnc hsMBEnc es', winEp') := rfl
  rw [hPair]; clear hPair
  set ρ_f1 := Env.cons (t := redEsTy) (esEnc vpMEnc hsMBEnc es', winEp') ρ_f
  rw [eval_ite]
  cases la
  · simp only [Expr.eval, Bool.false_eq_true, ↓reduceIte]
    rcases winEp' with _ | tWin
    · rw [eval_caseOpt_none' rfl, eval_ret]; rfl
    · rw [eval_caseOpt_some' rfl]
      set ρ_w := Env.cons (t := (.nat : Ty SP)) tWin ρ_f1
      change (Comp.ret _).eval ρ_w = _; rw [eval_ret]
      have hAuthOK := cAuthOKE_eval (vpEncFn := vpMEnc) (O' := OO) L (2 + Δcka)
        (optNatLit (O' := OO) tL) (.var .zero) (esG (.fst .v1)) ρ_w es'.g
        hBnd'.leaks_le hBnd'.corrs_le rfl
      have htL : (optNatLit (O' := OO) tL).eval ρ_w = tL := by cases tL <;> rfl
      have htWin : (Expr.var (O := OO) .zero).eval ρ_w = tWin := rfl
      rw [htL, htWin] at hAuthOK
      have hSendPar : (Expr.ite (.bool par) (.not (senderOfE (.var .zero)))
          (senderOfE (.var .zero)) : Expr OO _ .bool).eval ρ_w =
          (decide (Party.senderOf tWin == Party.A) == par) := by
        simp only [Expr.eval, senderOfE_eval, ρ_w, Env.get_cons_zero]
        cases par <;> cases Party.senderOf tWin <;> rfl
      generalize hAuthGen : cAuthOKE (O' := OO) L (2 + Δcka) (optNatLit (O' := OO) tL)
        (.var .zero) (esG (.fst .v1)) = authExpr at hAuthOK ⊢
      generalize hParGen : (Expr.ite (.bool par) (.not (senderOfE (.var .zero)))
        (senderOfE (.var .zero)) : Expr OO _ .bool) = parExpr at hSendPar ⊢
      simp only [Expr.eval, hAuthOK, hSendPar]
      clear hAuthOK hAuthGen authExpr hSendPar hParGen parExpr htL htWin
      simp only [ρ_w, ρ_f1, esAbort, esG, cGsWin, esEnc, cGsEnc, Expr.eval, Expr.v1,
        Env.get_cons_zero, Env.get_cons_succ, Bool.and_assoc]
  · simp [ρ_f1, Expr.eval, eval_ret, esH, esEnc, fsMultiBucketHsEnc, mbHsLfWin]

end Layer3Bridge

/-- Libsignal instantiation of `redFSAuthMultiBucketProg_eval_clamp`: evaluates
`redFSAuthMultiBucketShallow` to shallow `BucketFSAuthShallowBase.redFSAuthMultiBucket` on
`dhSchemeFb Dh`, `rootPRNG C.F encPt`, and `fsClamp B0 (fsAtomicB C ℓ encT idOf B0)` for any
`B0 : ℕ` whenever `MakesAtMostQueries A q`. -/
theorem redFSAuthMultiBucketShallow_eval_eq
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep
        gMain la tL par).eval (fun _ => A) ()) =
      redFSAuthMultiBucket (q + 1) (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsClamp B0 (fsAtomicB C ℓ encT idOf B0)) lam 1 qep gMain la tL par A := by
  let _ : Inhabited Pt := ⟨0⟩
  exact redFSAuthMultiBucketProg_eval_clamp
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep gMain la tL par
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    le_rfl A q hq le_rfl

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeShallow
