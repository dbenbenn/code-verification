/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BundlesEval

/-!
# Costed DSL Evaluation Bridge (`redCKAAuthBucketProg_eval_atomic`) for Stage-2 Bucket CKA-/

open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (bucketAuthCfg hooksCKABucket implCKABucket redCKAAuthBucket runCKAAuthBucket)
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun ckaHdrCtTy ckaIface ckaOps ckaPsEnc ckaPsTy ckaSMCodec ckaSMQ ckaSig)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lChainPRG lPubOf)
open CryptoGames.SM (isSomeE isSomeE_eval ite_eval letE_eval not_eval orE orE_eval pGet pGet_eval pair_eval partyEnc validGuessE validGuessE_eval)
open CryptoGames.SM.Construction (CKAState Header PartyState SchemeAdversary bucketAuthCfgEC ckaBucketEsTy ckaCommitC_eval ckaEsTy ckaFsRecvC ckaFsSendC ckaHsEnc ckaHsTy ckaRevealC_eval ckaStartRecvBucketAnsE ckaStartSendC_eval ckaVpEnc ckaVpTy hooksCKA hooksCKABucketC hooksCKA_commit_vR hooksCKA_startRecv_rs initCKA initCKAEStateC_eval initCKARaw initCKARaw_inv initCKARaw_vrInv redCKAAuthBucketProg)
open CryptoGames.SM.Engine (ConfigECAgrees Ctx EState HooksCAgrees HooksVRInv Policy RSReach SMEngineInv SMStateBoundedEngine SMVRInv TComp VP abortE cAfterCorrE cAfterCorrE_eval cAuthOKE_eval cCorrAllowedE cCorrAllowedE_eval cEpMgmtE cEpMgmtE_eval cGsEnc cGsEpoch cGsIdx cGsSt cGsTy cGsWin cRecEnc cRecordE_eval challE coinsE corrE deliverEC_eval epMgmt_lists_eq esAbort esEnc esG esH esMk eval_bind eval_bind_ret eval_caseOpt eval_ite eval_ret implE implE_inv implE_vrInv injectEC_eval optNatLit run_liftH_bind transmitE vSendC_eval vpTblEnc)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open ReductionDsl (Comp CostedReduction Env Expr Iface Ops Sig Ty handlerImpl isGameQuery)

namespace Computational.Proofs.SessionCostedFig8.BucketCKAEval

public section

set_option autoImplicit false
set_option linter.dupNamespace false

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CKA (DHFun CKASort CKAOp ckaSig ckaOps ckaIface ckaSMCodec
  ckaHdrCtTy ckaPsTy ckaSMQ ckaPsEnc)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lPubOf lChainPRG)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoGames.SM (Config authLosingConditionsAvoided smRrEnc partyEnc
  pGet pGet_eval orE orE_eval isSomeE isSomeE_eval validGuessE validGuessE_eval
  letE_eval pair_eval ite_eval not_eval some_eval)
open _root_.CryptoGames.SM.Engine (Policy VP Ctx EState Hooks HooksVRInv SMEngineInv SMVRInv
  SMStateBoundedEngine RSReach TComp HooksC HooksCAgrees ConfigEC ConfigECAgrees
  vpTblTy vpTblEnc esTy esEnc cGsTy cGsEnc cRecEnc optNatLit
  esG esH esAbort esMk cGsWin cGsSt cGsEpoch cGsIdx
  eval_ret eval_bind eval_bind_ret eval_ite eval_caseOpt
  cEpMgmtE cEpMgmtE_eval cRecordE cRecordE_eval epMgmt_lists_eq
  cCorrAllowedE cCorrAllowedE_eval cAfterCorrE cAfterCorrE_eval cAuthOKE cAuthOKE_eval
  vSendC vSendC_eval deliverEC deliverEC_eval injectEC injectEC_eval
  abortE transmitE challE deliverE injectE corrE coinsE implE
  run_liftH_bind implE_inv implE_vrInv)
open _root_.CryptoGames.SM.Construction (PartyState SchemeAdversary Header Mode CKAState
  hooksCKA hooksCKA_startRecv_rs hooksCKA_commit_vR
  initCKA initCKARaw initCKARaw_inv initCKARaw_vrInv
  ckaHsTy ckaHsEnc ckaVpTy ckaVpEnc ckaEsTy ckaBucketEsTy
  ckaStartSendC_eval ckaFsSendC ckaFsRecvC ckaCommitC_eval ckaRevealC ckaRevealC_eval
  initCKAEStateC_eval
  hooksCKABucketC bucketAuthCfgEC ckaStartRecvBucketAnsE redCKAAuthBucketProg)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb aeadAtomic fsAtomicB)
open Computational.Proofs.SessionCostedFig8.Bundles (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesEval (fsAtomicB_receive_rsReach)

section CKABucketAtomicEval

private def noDoomPolicy : Policy := ⟨false, none, 0⟩

@[local simp] private lemma noDoomPolicy_leakDoom {St Msg C : Type}
    (g g' : CryptoGames.SM.GameState St Msg C) :
    noDoomPolicy.leakDoom g g' = false := by
  simp [noDoomPolicy, CryptoGames.SM.Engine.Policy.leakDoom]

@[local simp] private lemma noDoomPolicy_corrDoom {St Msg C : Type}
    (g : CryptoGames.SM.GameState St Msg C) (P : Party) :
    noDoomPolicy.corrDoom g P = false := by
  simp [noDoomPolicy, CryptoGames.SM.Engine.Policy.corrDoom]

private lemma startRecv_hooksCKABucket_eq
    {KC Γ CCoins T I KR Sig K SS RS M E : Type} [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (t : ℕ)
    (γv : Option Γ) (σ : Sig) (Tn : T) :
    (hooksCKABucket cka prng fs Δcka tL).startRecv ctx P t γv σ Tn =
      (hooksCKA cka prng fs Δcka
        ⟨true, tL, if CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t then t else t + 1⟩).startRecv
        ctx P t γv σ Tn := by
  ext h
  simp only [hooksCKABucket, hooksCKA, StateT.run_bind, StateT.run_get, pure_bind]
  cases h.cache t with
  | none =>
    cases hb : CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t
    · simp
    · simp; rfl
  | some pair =>
    rcases pair with ⟨Tc, Ik⟩
    by_cases hTc : Tc = Tn
    · simp [hTc]
    · cases hb : CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t
      · simp [hTc]
      · simp [hTc]; rfl

private lemma hooksCKABucket_startRecv_rs'
    {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ)
    {VROk : RS → Prop} (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Option Γ) (σ0 : RSt) (tn0 : T) (h : CKAState T I)
    (res : Option (Option (Option Γ × RSt × RS)) × CKAState T I)
    (hmem : res ∈ support ((hooksCKABucket cka prng fs Δcka tL).startRecv
      ctx P t0 γ0 σ0 tn0 |>.run h))
    (γ' : Option Γ) (σ' : RSt) (rs : RS) (hEq : res.1 = some (some (γ', σ', rs))) :
    VROk rs := by
  rw [startRecv_hooksCKABucket_eq] at hmem
  exact hooksCKA_startRecv_rs cka prng fs Δcka _ hInitR ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq

private lemma hooksCKABucket_vrInv_fsAtomicB'
    {Pt : Type} [DecidableEq Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka : ℕ) (tL : Option ℕ) :
    HooksVRInv (RSReach maxForwardJumps)
      (hooksCKABucket (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) Δcka tL) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    hooksCKABucket_startRecv_rs' (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) Δcka tL
      (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD
        (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps)
      ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq; subst hEq
    dsimp only [hooksCKABucket, hooksCKA] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact (fsAtomicB_receive_rsReach C ℓ encT idOf B0 _ hVR hmem.1.symm).2
  commit_vR :=
    hooksCKA_commit_vR (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) Δcka ⟨true, tL, 0⟩

private def ckaBucketUpdateWinEp {Γ T Sig SS RS M E I CCoins : Type}
    (es0 es' : EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (qy : (unifSpec + CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (winEp0 : Option ℕ) : Option ℕ :=
  match qy with
  | .inr (.inl (.inr x)) => if !es0.g.win && es'.g.win then some x.2.1.1 else winEp0
  | _ => winEp0

private lemma implCKABucket_run_eq_implE
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (qy : (unifSpec + CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es0 : EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (winEp0 : Option ℕ) :
    (implCKABucket cka prng fs Δcka qep tL qy).run (es0, winEp0) =
      ((implE (hooksCKABucket cka prng fs Δcka tL) (2 + Δcka) qep fs.maxSkip
          (bucketAuthCfg Δcka tL) noDoomPolicy qy).run es0 >>=
        fun res => pure (res.1,
          (res.2, ckaBucketUpdateWinEp es0 res.2 qy winEp0))) := by
  rcases qy with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, coinsE, ckaBucketUpdateWinEp]
    simp [StateT.run_lift]
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, transmitE, ckaBucketUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      cases hep : es0.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => simp
      | some s₁ =>
        simp only [noDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte]
        rw [StateT.run_bind, StateT.run_lift, run_liftH_bind]
        simp only [bind_assoc, pure_bind]
        refine bind_congr fun ⟨res, h'⟩ => ?_
        rcases res with _ | ⟨st', ct⟩ <;> simp [abortE]
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, challE,
      bucketAuthCfg, ckaBucketUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      cases hep : es0.g.epMgmt (2 + Δcka) qep P r.isSome <;> simp
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, ckaBucketUpdateWinEp]
    simp [StateT.run_lift]
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, ckaBucketUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind]
    refine bind_congr fun ⟨out, es'⟩ => rfl
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, corrE, ckaBucketUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win || !es0.g.corrAllowed P) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte,
        noDoomPolicy_leakDoom, noDoomPolicy_corrDoom, Bool.or_self]
      rw [StateT.run_bind, StateT.run_lift, run_liftH_bind]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun ⟨res, h'⟩ => ?_
      cases res <;> simp [abortE]

private lemma runCKAAuthBucket_eq_bind_initCKARaw
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (tL : Option ℕ)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) :
    runCKAAuthBucket cka prng fs lam Δcka qep tL A =
      (do
        let es₀ ← initCKARaw cka prng fs lam ⟨true, tL, 0⟩ false
        let res ← (simulateQ (implCKABucket cka prng fs Δcka qep tL) A).run (es₀, none)
        return some (res.1, res.2.1, res.2.2)) := by
  unfold runCKAAuthBucket initCKA initCKARaw
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine bind_congr fun kr => ?_
  rcases tL with _ | l
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
      bind_map_left]; rfl
  · simp only [StateT.run_pure, pure_bind]; rfl

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool}
  {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "II" =>
  ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

private abbrev vpEncCKA :=
  vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (KR := KR) (RSt := RSt)
    (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := ReductionDsl.Ty.opt (ReductionDsl.Ty.base CryptoGames.CKA.CKASort.γ)) (svT := ReductionDsl.Ty.base CryptoGames.CKA.CKASort.sig)
    (ssvT := ReductionDsl.Ty.base CryptoGames.CKA.CKASort.ss) (rsvT := ReductionDsl.Ty.base CryptoGames.CKA.CKASort.rs)

private lemma eval_caseSum {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b c : Ty S'}
    (e : Expr O' Γ' (.sum a b)) (l : Comp O' I' (a :: Γ') c) (r : Comp O' I' (b :: Γ') c)
    (ρ : Env Γ') :
    (ReductionDsl.Comp.caseSum e l r).eval ρ =
      match e.eval ρ with
      | .inl x => l.eval (.cons x ρ)
      | .inr y => r.eval (.cons y ρ) := rfl

private lemma optNatLit_eval {O' : Ops S} {Γ'} (tL : Option ℕ) (ρ : Env Γ') :
    (optNatLit (O' := O') tL).eval ρ = tL := by
  cases tL <;> rfl

private lemma caseOpt_eval {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a b : Ty S'}
    (e : Expr O' Γ' (.opt a)) (n : Expr O' Γ' b) (s : Expr O' (a :: Γ') b) (ρ : Env Γ') :
    (ReductionDsl.Expr.caseOpt e n s).eval ρ =
      match e.eval ρ with
      | none => n.eval ρ
      | some x => s.eval (.cons x ρ) := rfl

private lemma ckaStartRecvBucketC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (B Δcka : ℕ) (tL : Option ℕ)
    {Γ'} (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : CKAState T I) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (hh : hE.eval ρ = ckaHsEnc h) :
    ((hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka tL).startRecv
        hE ctxE pE tE γvE σE tnE).eval ρ =
      Prod.map id ckaHsEnc <$>
        ((hooksCKABucket cka prng fs Δcka tL).startRecv ctx P
          (tE.eval ρ) (γvE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h := by
  dsimp only [hooksCKABucketC, ckaStartRecvBucketAnsE, hooksCKABucket]
  simp only [eval_ret, pair_eval, letE_eval, hh, StateT.run_bind, StateT.run_get, pure_bind]
  set t : ℕ := tE.eval ρ
  set γv : Option Γ := γvE.eval ρ
  set σ : RSt := σE.eval ρ
  set Tn : T := tnE.eval ρ
  set ρ₁ := ReductionDsl.Env.cons
    (t := .prod ckaHsTy (.prod .nat (.prod (.opt (.base CryptoGames.CKA.CKASort.γ))
      (.prod (.base CryptoGames.CKA.CKASort.sig) (.base CryptoGames.CKA.CKASort.t)))))
    (ckaHsEnc h, t, γv, σ, Tn) ρ
  change (pure ((ReductionDsl.Expr.caseOpt _ _ _).eval ρ₁, ckaHsEnc h) :
      TComp (CryptoGames.CKA.spec Γ CCoins T I) _) = _
  have hHonest :
      (ReductionDsl.Expr.caseOpt (.tget (.fst (ReductionDsl.Expr.v0 (O := OO))) (.fst (.snd .v0))) .none
        (.ite (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
          (.some (.snd .v0)) .none)).eval ρ₁ =
      (match h.cache t with
        | some (Tc, Ik) => if Tc = Tn then some Ik else none
        | none => none) := by
    have hGet : (ReductionDsl.Expr.tget (.fst (ReductionDsl.Expr.v0 (O := OO))) (.fst (.snd .v0))).eval ρ₁ = h.cache t := rfl
    rw [caseOpt_eval, hGet]
    rcases h.cache t with _ | ⟨Tc, Ik⟩
    · rfl
    · simp only [ρ₁, ckaOps, heqT, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, BEq.beq]
      by_cases hEq : Tc = Tn <;> simp [hEq]
  rw [caseOpt_eval, hHonest]
  have hCond :
      (validGuessE (2 + Δcka) (optNatLit (O' := OO) tL) (.fst (.snd (ReductionDsl.Expr.v0 (O := OO))))).eval ρ₁ =
      CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t := by
    rw [validGuessE_eval, optNatLit_eval]; rfl
  rcases h.cache t with _ | ⟨Tc, Ik⟩
  · dsimp only
    rw [ite_eval, hCond]
    by_cases hAdm : CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t = true
    · simp only [hAdm, ↓reduceIte]
      rcases γv with _ | γ
      · simp only [StateT.run_pure, map_pure]; rfl
      · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
        congr 1; congr 1
        simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]
    · simp only [hAdm, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure]; rfl
  · dsimp only
    by_cases hEq : Tc = Tn
    · simp only [hEq, ↓reduceIte]
      rcases γv with _ | γ <;>
      · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
        congr 1; congr 1
        simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2]
    · simp only [hEq, ↓reduceIte]
      rw [ite_eval, hCond]
      by_cases hAdm : CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t = true
      · simp only [hAdm, ↓reduceIte]
        rcases γv with _ | γ
        · simp only [StateT.run_pure, map_pure]; rfl
        · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
          congr 1; congr 1
          simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]
      · simp only [hAdm, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure]; rfl

private lemma hooksCKABucketC_agrees_vr [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B Δcka : ℕ) (tL : Option ℕ)
    {VROk : RS → Prop}
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hInitR : ∀ k, VROk (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROk rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      ckaHsEnc (fun _ => True) (HBoundedPost := fun _ => True) (VROk := VROk)
      (hooksCKABucketC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka tL)
      (hooksCKABucket cka prng fs Δcka tL) where
  hBounded_post _ _ := trivial
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P _ hh _ hp :=
    ckaStartSendC_eval cka prng fs hSend hPrngUp hFsInitS hSampCCoins Δcka ⟨true, tL, 0⟩
      hE ctxE pE tE γE σE rE ρ h ctx P hh hp
  startSend_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_eval hE ctxE pE tE γvE σE tnE ρ h ctx P _ hh _ _ :=
    ckaStartRecvBucketC_eval cka prng fs hRecv hPrngUp hFsInitR heqT B Δcka tL
      hE ctxE pE tE γvE σE tnE ρ h ctx P hh
  startRecv_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_vrOk ctx P t γ σ Tn h _ :=
    hooksCKABucket_startRecv_rs' cka prng fs Δcka tL hInitR ctx P t γ σ Tn h
  fsSend_eval hE _ _ _ ssE hdrE mE _ ρ h _ _ _ hh _ _ := by
    simp [hooksCKABucketC, ckaFsSendC, hooksCKABucket, hooksCKA, ckaOps, hFsSend, hh,
      StateT.run_pure, Prod.map, ReductionDsl.Expr.eval]
  fsRecv_eval hE _ _ _ rsE hdrE eE _ ρ h _ _ _ _ hVR hh _ _ _ := by
    simp only [hooksCKABucketC, ckaFsRecvC, hooksCKABucket, hooksCKA, eval_ret,
      ckaOps, hFsRecv, hh, StateT.run_pure, map_pure, Prod.map, id_eq, ReductionDsl.Expr.eval]
    congr 2
    rcases hrc : fs.receive (rsE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) with _ | ⟨rs', i, m⟩
    · rfl
    · simp [Nat.min_eq_left (hFsB _ _ _ _ _ _ hVR hrc)]
  fsRecv_bounded _ _ _ _ _ _ _ _ _ _ _ := trivial
  commit_eval hE ctxE pE oldE newE ρ h ctx P old new _ hh _ hp hold hnew :=
    ckaCommitC_eval cka prng fs Δcka ⟨true, tL, 0⟩ hE ctxE pE oldE newE ρ h ctx P old new hh hp hold hnew
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh _ hp hvp :=
    ckaRevealC_eval cka prng fs Δcka ⟨true, tL, 0⟩ hE ctxE pE vpE ρ h ctx P vp hh hp hvp

private lemma bucketAuthCfgEC_agrees (Δcka : ℕ) (tL : Option ℕ) :
    ConfigECAgrees
      (bucketAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) Δcka tL)
      (bucketAuthCfg Δcka tL) where
  deliverWin_eq := rfl
  injectFull_eq e ρ := by simp [bucketAuthCfgEC, bucketAuthCfg, validGuessE_eval]
  challOK_eq _ _ := rfl
  challMsg_eq _ b m₀ m₁ ρ := by simp [bucketAuthCfgEC, bucketAuthCfg, ite_eval]

private lemma v0_eval_cons {t : Ty S} {Γ' : List (Ty S)} (v : t.denote) (ρ : Env Γ') :
    (ReductionDsl.Expr.v0 (O := OO)).eval (.cons v ρ) = v := rfl

private lemma snd_eval {t₁ t₂ : Ty S} {Γ' : List (Ty S)} (e : Expr OO Γ' (.prod t₁ t₂)) (ρ : Env Γ') :
    (ReductionDsl.Expr.snd e).eval ρ = (e.eval ρ).2 := rfl

private def ckaBucketStateEnc (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ)
    (s : EState (VP (Option Γ) T RSt SS RS) M (Header T × E) (CKAState T I) × Option ℕ) :
    (redCKAAuthBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL).σ.denote :=
  (esEnc vpEncCKA ckaHsEnc s.1, s.2)

private lemma rdec_redCKAAuthBucket_handle_eval
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType CCoins]
    (hDefaultE : defaultE = default)
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δcka qep : ℕ) (tL : Option ℕ)
    {VROk : RS → Prop}
    (hHk : HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      ckaHsEnc (fun _ => True) (HBoundedPost := fun _ => True) (VROk := VROk)
      (hooksCKABucketC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka tL)
      (hooksCKABucket cka prng fs Δcka tL))
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (es : EState (VP (Option Γ) T RSt SS RS) M (Header T × E) (CKAState T I))
    (winEp : Option ℕ)
    (q : (CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ P t v, (es.g.st P).vR t = some v → VROk v) :
    ((fun p => ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      ((redCKAAuthBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL).handle).eval
        (.cons (ckaBucketStateEnc (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive)
          (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL (es, winEp))
          (.cons ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) .nil))) =
      Prod.map id (ckaBucketStateEnc (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL) <$>
        ((implCKABucket cka prng fs Δcka qep tL (.inr q)).run (es, winEp) :
          OracleComp (unifSpec + CryptoGames.CKA.spec Γ CCoins T I) _) := by
  unfold ckaBucketStateEnc
  let hkC := hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B Δcka tL
  let hk := hooksCKABucket cka prng fs Δcka tL
  have hCfg := bucketAuthCfgEC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) Δcka tL
  rw [implCKABucket_run_eq_implE]
  dsimp only [redCKAAuthBucketProg]
  rw [eval_bind_ret]
  set ρ₀ : Env [ckaBucketEsTy, ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E] :=
    .cons (esEnc vpEncCKA ckaHsEnc es, winEp)
      (.cons ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) .nil)
  have h0 : (ReductionDsl.Expr.pair (.fst (ReductionDsl.Expr.v0 (O := OO))) (.pair (.snd .v0) .v1)).eval ρ₀ =
      (esEnc vpEncCKA ckaHsEnc es, winEp,
        (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) := rfl
  rw [h0]; clear h0
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · -- transmit
    simp only [ckaSMCodec, eval_caseSum, v0_eval_cons, snd_eval]
    rw [eval_bind_ret]
    let txTy : Ty S := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
    let chTy : Ty S := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
    let hdTy : Ty S := .prod .bool (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
    set ρ₁ := ReductionDsl.Env.cons (t := txTy) (partyEnc P, m, r)
      (ReductionDsl.Env.cons (t := txTy) (partyEnc P, m, r)
        (ReductionDsl.Env.cons (t := .sum txTy chTy) (Sum.inl (partyEnc P, m, r))
          (ReductionDsl.Env.cons (t := .sum (.sum txTy chTy) hdTy) (Sum.inl (Sum.inl (partyEnc P, m, r)))
            (ReductionDsl.Env.cons (t := .sum (.sum (.sum txTy chTy) hdTy) hdTy)
              (Sum.inl (Sum.inl (Sum.inl (partyEnc P, m, r))))
              (ReductionDsl.Env.cons
                (t := .prod ckaEsTy (.prod (.opt .nat) (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)))
                (esEnc vpEncCKA ckaHsEnc es, winEp,
                  Sum.inl (Sum.inl (Sum.inl (Sum.inl (partyEnc P, m, r))))) ρ₀)))))
    change _ <$> (ReductionDsl.Comp.ite _ _ _).eval ρ₁ =
      Prod.map id (Prod.map (esEnc vpEncCKA ckaHsEnc) id) <$>
        ((transmitE hk (2 + Δcka) qep noDoomPolicy (P, m, r)).run es >>=
          fun res => pure (res.1, (res.2, winEp)))
    unfold transmitE abortE
    rw [eval_ite]
    have hCond1 : (orE (esAbort (.fst (ReductionDsl.Expr.v5 (O := OO))))
        (cGsWin (esG (.fst .v5)))).eval ρ₁ = (es.abort || es.g.win) := by
      simp [ρ₁, orE_eval, esAbort, cGsWin, esG, esEnc, cGsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v5]
    rw [hCond1]
    by_cases hab : (es.abort || es.g.win)
    · simp only [Bool.or_eq_true] at hab
      rcases hab with hab | hab <;>
        simp [hab, ρ₁, ReductionDsl.Comp.eval, StateT.run_pure, Prod.map, ReductionDsl.Expr.eval, ReductionDsl.Expr.v5]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind]
      rw [eval_caseOpt]
      have hEp : (cEpMgmtE (2 + Δcka) qep (esG (.fst (ReductionDsl.Expr.v5 (O := OO)))) (.fst .v0)
          (isSomeE (.snd (.snd .v0)))).eval ρ₁ =
          (es.g.epMgmt (2 + Δcka) qep P r.isSome).map (cGsEnc vpEncCKA) := by
        have := cEpMgmtE_eval vpEncCKA (O' := OO) (2 + Δcka) qep
          (esG (.fst .v5)) (.fst .v0) (isSomeE (.snd (.snd .v0)))
          ρ₁ es.g P rfl rfl
        simpa [ρ₁, isSomeE_eval, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0] using this
      rw [hEp]
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp [ρ₁, ReductionDsl.Comp.eval, StateT.run_pure, Prod.map, ReductionDsl.Expr.eval, ReductionDsl.Expr.v5]
      · simp only [Option.map_some, noDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte,
          eval_bind]
        set ρ₂ := ReductionDsl.Env.cons (t := cGsTy ckaVpTy) (cGsEnc vpEncCKA s₁) ρ₁
        have hStP : (pGet (cGsSt (ReductionDsl.Expr.v0 (O := OO))) (.fst .v1)).eval ρ₂ =
            vpEncCKA (s₁.st P) :=
          pGet_eval (cGsSt .v0) (.fst .v1) ρ₂ (fun Q => vpEncCKA (s₁.st Q)) P rfl rfl
        have hVSend := vSendC_eval hDefaultE ckaHsEnc (fun _ => True) hkC hk hHk
          (esH (.fst .v6)) .v0 (.fst .v1) (pGet (cGsSt .v0) (.fst .v1))
          (.fst (.snd .v1)) .none (.snd (.snd .v1))
          ρ₂ es.h s₁ P (s₁.st P) m none r trivial rfl rfl rfl hStP rfl rfl rfl
        rw [hVSend, bind_map_left, run_liftH_bind, map_bind, bind_assoc, map_bind]
        refine bind_congr fun ⟨vsRes, h'⟩ => ?_
        rcases vsRes with _ | ⟨st', c⟩
        · simp [ρ₂, ρ₁, ReductionDsl.Comp.eval, StateT.run_modify, Prod.map, esMk, esG, esEnc,
            ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v7]
        · simp only [Prod.map, Option.map_some, id_eq,
            StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
          set ρ₃ := ReductionDsl.Env.cons (t := .prod ckaVpTy (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))
            (vpEncCKA st', c)
            (ReductionDsl.Env.cons
              (t := .prod
                (.opt (.prod ckaVpTy (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) ckaHsTy)
              (some (vpEncCKA st', c), ckaHsEnc h') ρ₂)
          change _ <$> (ReductionDsl.Comp.ret _).eval ρ₃ = _
          have hEp3 : (pGet (cGsEpoch (ReductionDsl.Expr.v2 (O := OO))) (.fst .v3)).eval ρ₃ =
              s₁.epoch P :=
            pGet_eval (cGsEpoch .v2) (.fst .v3) ρ₃ s₁.epoch P rfl rfl
          have hIdx3 : (pGet (cGsIdx (ReductionDsl.Expr.v2 (O := OO))) (.fst .v3)).eval ρ₃ =
              s₁.idx P :=
            pGet_eval (cGsIdx .v2) (.fst .v3) ρ₃ s₁.idx P rfl rfl
          have hRecE : (ReductionDsl.Expr.pair
              (.pair (.fst (ReductionDsl.Expr.v3 (O := OO)))
                (.pair (pGet (cGsEpoch .v2) (.fst .v3))
                  (.add (pGet (cGsIdx .v2) (.fst .v3)) (.nat 1))))
              (.pair (.fst (.snd .v3)) (.snd .v0))).eval ρ₃ =
              cRecEnc ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ := by
            simp only [ReductionDsl.Expr.eval, hEp3, hIdx3]; rfl
          have hRecord := cRecordE_eval vpEncCKA (O' := OO) L (2 + Δcka)
            (ReductionDsl.Expr.v2 (O := OO)) (.fst .v3) (.fst .v0)
            (.pair (.pair (.fst .v3)
              (.pair (pGet (cGsEpoch .v2) (.fst .v3))
                (.add (pGet (cGsIdx .v2) (.fst .v3)) (.nat 1))))
              (.pair (.fst (.snd .v3)) (.snd .v0)))
            (.bool false) ρ₃ s₁ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩
            ((epMgmt_lists_eq hep).2.2.1 ▸ hBound.comp_le)
            rfl rfl rfl hRecE
          simp only [eval_ret, esMk, pair_eval, hRecord, map_pure]
          rfl
  · -- chall
    simp only [ckaSMCodec, eval_caseSum, v0_eval_cons, snd_eval, eval_ret,
      implE, QueryImpl.add_apply, ckaBucketUpdateWinEp]
    unfold challE bucketAuthCfg
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab, StateT.run_pure, ρ₀, Prod.map, ReductionDsl.Expr.eval, ReductionDsl.Expr.v4]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁ <;>
        simp [StateT.run_pure, ρ₀, Prod.map, ReductionDsl.Expr.eval, ReductionDsl.Expr.v4]
  · -- deliver
    simp only [ckaSMCodec, eval_caseSum, eval_bind, eval_ret, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]
    rw [deliverEC_eval ckaHsEnc (fun _ => True) hkC hk hHk L fs.maxSkip
          (bucketAuthCfgEC Δcka tL) (bucketAuthCfg Δcka tL) hCfg heqT heqM heqE
          _ _ _ es P c trivial hBound (hVR P) rfl rfl]
    simp only [implE, ckaBucketUpdateWinEp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rcases res with _ | (_ | m') <;>
      simp [Prod.map, ReductionDsl.Expr.eval, ReductionDsl.Expr.v4]
  · -- inject
    simp only [ckaSMCodec, eval_caseSum, eval_bind, eval_ret, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]
    rw [injectEC_eval ckaHsEnc (fun _ => True) hkC hk hHk L (2 + Δcka) qep
          (bucketAuthCfgEC Δcka tL) (bucketAuthCfg Δcka tL) hCfg heqT heqE
          _ _ _ es P c trivial hBound (hVR P) rfl rfl]
    simp only [implE, ckaBucketUpdateWinEp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rcases res with _ | (_ | m') <;>
      simp [Prod.map, cGsWin, esG, esEnc, cGsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Expr.v3]
  · -- corr
    simp only [ckaSMCodec, eval_caseSum, v0_eval_cons, snd_eval]
    set ρ₁ := ReductionDsl.Env.cons (t := .bool) (partyEnc P)
      (ReductionDsl.Env.cons
        (t := .prod ckaEsTy (.prod (.opt .nat) (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)))
        (esEnc vpEncCKA ckaHsEnc es, winEp, Sum.inr (partyEnc P)) ρ₀)
    change _ <$> (ReductionDsl.Comp.ite _ _ _).eval ρ₁ =
      Prod.map id (Prod.map (esEnc vpEncCKA ckaHsEnc) id) <$>
        ((corrE hk noDoomPolicy P).run es >>=
          fun res => pure (res.1, (res.2, winEp)))
    unfold corrE abortE
    rw [eval_ite]
    have hCorrOk : (cCorrAllowedE L (esG (.fst (ReductionDsl.Expr.v1 (O := OO)))) .v0).eval ρ₁ =
        es.g.corrAllowed P :=
      cCorrAllowedE_eval vpEncCKA (O' := OO) L (esG (.fst .v1)) .v0 ρ₁ es.g P
        hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl
    have hRefuse : (orE (esAbort (.fst (ReductionDsl.Expr.v1 (O := OO))))
        (orE (cGsWin (esG (.fst .v1)))
          (.not (cCorrAllowedE L (esG (.fst .v1)) .v0)))).eval ρ₁ =
        (es.abort || es.g.win || !(es.g.corrAllowed P)) := by
      simp only [orE_eval, not_eval, hCorrOk]
      simp [ρ₁, esAbort, cGsWin, esG, esEnc, cGsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, Bool.or_assoc]
    rw [hRefuse]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
    · simp only [Bool.or_eq_true, Bool.not_eq_true'] at href
      simp [href, ρ₁, ReductionDsl.Comp.eval, StateT.run_pure,
        Prod.map, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]
    · simp only [href, Bool.false_eq_true, ↓reduceIte,
        noDoomPolicy_leakDoom, noDoomPolicy_corrDoom, Bool.or_self]
      have hStP : (pGet (cGsSt (esG (.fst (ReductionDsl.Expr.v1 (O := OO))))) .v0).eval ρ₁ =
          vpEncCKA (es.g.st P) :=
        pGet_eval (cGsSt (esG (.fst .v1))) .v0 ρ₁
          (fun Q => vpEncCKA (es.g.st Q)) P rfl rfl
      have hRev := hHk.reveal_eval (esH (.fst .v1)) (esG (.fst .v1)) .v0
        (pGet (cGsSt (esG (.fst .v1))) .v0) ρ₁ es.h es.g P (es.g.st P) trivial
        rfl rfl rfl hStP
      dsimp only [hkC, hooksCKABucketC] at hRev
      rw [eval_bind, hRev, bind_map_left, run_liftH_bind,
        map_bind, bind_assoc, map_bind]
      refine bind_congr fun ⟨revRes, h'⟩ => ?_
      rcases revRes with _ | st
      · simp [ρ₁, ReductionDsl.Comp.eval, StateT.run_modify,
          Prod.map, esMk, esG, esEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2]
      · simp only [Prod.map, Option.map_some, id_eq,
          StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
        set ρ₂ := ReductionDsl.Env.cons (t := ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E) (ckaPsEnc st)
          (ReductionDsl.Env.cons (t := .prod (.opt (ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E)) ckaHsTy)
            (some (ckaPsEnc st), ckaHsEnc h') ρ₁)
        change _ <$> (ReductionDsl.Comp.ret _).eval ρ₂ = _
        have hAfter2 : (cAfterCorrE L (esG (.fst (ReductionDsl.Expr.v3 (O := OO)))) .v2).eval ρ₂ =
            cGsEnc vpEncCKA (es.g.afterCorr P) :=
          cAfterCorrE_eval vpEncCKA (O' := OO) L (esG (.fst .v3)) .v2 ρ₂ es.g P
            hBound.trans_le hBound.comp_u rfl rfl
        simp only [eval_ret, esMk, pair_eval, hAfter2, map_pure]
        simp [ρ₂, ρ₁, ρ₀, esAbort, esEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v3]

private lemma simulateQ_redCKAAuthBucket_vr_eq
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType CCoins]
    (hDefaultE : defaultE = default)
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hHk : HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      ckaHsEnc (fun _ => True) (HBoundedPost := fun _ => True) (VROk := VROkStep B_q)
      (hooksCKABucketC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka tL)
      (hooksCKABucket cka prng fs Δcka tL))
    (hVRHk : HooksVRInv VROkStep (hooksCKABucket cka prng fs Δcka tL))
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·)) :
    ∀ {α : Type}
      {oa : OracleComp
        (unifSpec + CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)))
        qAdv →
      ∀ (es : EState (VP (Option Γ) T RSt SS RS) M (Header T × E) (CKAState T I))
        (winEp : Option ℕ),
        SMEngineInv L B_q qAdv es.g → SMVRInv VROkStep B_q qAdv es.g →
        (simulateQ
          (handlerImpl (C := ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            ((redCKAAuthBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive)
                (prngInit := prngInit) (prngUp := prngUp)
                (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK)
                L B Δcka qep fs.maxSkip tL).handle)) oa).run
          (ckaBucketStateEnc (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive)
            (prngInit := prngInit) (prngUp := prngUp)
            (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL (es, winEp)) =
          (Prod.map id (ckaBucketStateEnc (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive)
            (prngInit := prngInit) (prngUp := prngUp)
            (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL) <$>
            ((simulateQ (implCKABucket cka prng fs Δcka qep tL) oa).run (es, winEp) :
              OracleComp (unifSpec + CryptoGames.CKA.spec Γ CCoins T I) _)) ∧
        ∀ res ∈ support ((simulateQ (implCKABucket cka prng fs Δcka qep tL) oa).run (es, winEp)),
          SMEngineInv L B_q 0 res.2.1.g := by
  let stEnc := ckaBucketStateEnc (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es winEp hInv _
    refine ⟨by simp only [simulateQ_pure]; rfl, ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact hInv.mono (Nat.zero_le qAdv)
  | query_bind q mx ih =>
    intro qAdv hq es winEp hInv hVR
    rw [isQueryBoundP_query_bind_iff] at hq
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            ((redCKAAuthBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive)
              (prngInit := prngInit) (prngUp := prngUp)
              (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL).handle)) (.inl n)).run
            (stEnc (es, winEp)) =
          (fun u : (unifSpec + CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Range (.inl n) =>
            (u, stEnc (es, winEp))) <$>
            query (spec := unifSpec + CryptoGames.CKA.spec Γ CCoins T I) (.inl n) := by
        simp [handlerImpl, ckaIface, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          ((implCKABucket cka prng fs Δcka qep tL (.inl n)).run (es, winEp) :
            OracleComp (unifSpec + CryptoGames.CKA.spec Γ CCoins T I) _) =
          (fun u : (unifSpec + CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Range (.inl n) =>
            (u, (es, winEp))) <$>
            query (spec := unifSpec + CryptoGames.CKA.spec Γ CCoins T I) (.inl n) := by
        simp [implCKABucket, StateT.run_lift, map_eq_bind_pure_comp]
      refine ⟨?_, ?_⟩
      · rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind,
          hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
        exact bind_congr fun u => (ih u (hq.2 u) es winEp hInv hVR).1
      · intro res hmem
        rw [OracleComp.run_simulateQ_query_bind, hCoinR, bind_map_left, mem_support_bind_iff] at hmem
        obtain ⟨u, _, hmem⟩ := hmem
        exact (ih u (hq.2 u) es winEp hInv hVR).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hVRB : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → VROkStep B_q v :=
        fun P t₀ v hv => hVRHk.mono (Nat.sub_le B_q (m + 1)) (hVR P t₀ v hv)
      have hStep :
          ((handlerImpl (C := ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            ((redCKAAuthBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive)
              (prngInit := prngInit) (prngUp := prngUp)
              (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL).handle)) (.inr t)).run
            (stEnc (es, winEp)) =
          Prod.map id stEnc <$>
            ((implCKABucket cka prng fs Δcka qep tL (.inr t)).run (es, winEp) :
              OracleComp (unifSpec + CryptoGames.CKA.spec Γ CCoins T I) _) := by
        have hStepL := rdec_redCKAAuthBucket_handle_eval hDefaultE cka prng fs L B Δcka qep tL hHk
          heqT heqM heqE es winEp t hInv.toBoundedEngine hVRB
        dsimp only [stEnc]
        simp only [handlerImpl, StateT.run_mk, ckaSMCodec, ← hStepL,
          map_eq_bind_pure_comp, Function.comp_def]
      refine ⟨?_, ?_⟩
      · rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind,
          hStep, bind_map_left, map_bind]
        refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁, winEp₁⟩ hmem => ?_
        rw [implCKABucket_run_eq_implE, mem_support_bind_iff] at hmem
        obtain ⟨⟨u', es'⟩, hmemE, hEq⟩ := hmem
        simp only [support_pure, Set.mem_singleton_iff] at hEq
        rcases Prod.mk.inj hEq with ⟨rfl, hEq2⟩
        rcases Prod.mk.inj hEq2 with ⟨rfl, rfl⟩
        have hInv₁ := implE_inv _ (bucketAuthCfg Δcka tL) noDoomPolicy es t hInv (u, es₁) hmemE
        have hVR₁ := implE_vrInv _ hVRHk (bucketAuthCfg Δcka tL) noDoomPolicy es t hInv hVR (u, es₁) hmemE
        exact (ih u (hqm u) es₁ _ hInv₁ hVR₁).1
      · intro res hmem
        rw [OracleComp.run_simulateQ_query_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁, winEp₁⟩, hmem₁, hmem₂⟩ := hmem
        rw [implCKABucket_run_eq_implE, mem_support_bind_iff] at hmem₁
        obtain ⟨⟨u', es'⟩, hmemE, hEq⟩ := hmem₁
        simp only [support_pure, Set.mem_singleton_iff] at hEq
        rcases Prod.mk.inj hEq with ⟨rfl, hEq2⟩
        rcases Prod.mk.inj hEq2 with ⟨rfl, rfl⟩
        have hInv₁ := implE_inv _ (bucketAuthCfg Δcka tL) noDoomPolicy es t hInv (u, es₁) hmemE
        have hVR₁ := implE_vrInv _ hVRHk (bucketAuthCfg Δcka tL) noDoomPolicy es t hInv hVR (u, es₁) hmemE
        exact (ih u (hqm u) es₁ _ hInv₁ hVR₁).2 res hmem₂

theorem redCKAAuthBucketProg_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksCKABucket cka prng fs Δcka tL))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redCKAAuthBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL).eval (fun _ => A) () =
      redCKAAuthBucket cka prng fs lam Δcka qep tL A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk := hooksCKABucketC_agrees_vr (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs B Δcka tL hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT hSampCCoins (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hInit := initCKAEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR hSampKR hSampKC
    ⟨true, tL, 0⟩ (ReductionDsl.Expr.bool (O := OO) false) (ReductionDsl.Env.cons (t := .unit) () .nil)
  have hVpEq : @ckaVpEnc KC Γ CCoins T I KR RSt K SS RS M E = vpEncCKA := rfl
  let prog := redCKAAuthBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL
  let stEnc := ckaBucketStateEnc (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL
  have hInitP : prog.init.eval (ReductionDsl.Env.cons (t := .unit) () .nil) =
      (fun es₀ => ((() : ReductionDsl.Ty.unit.denote), stEnc (es₀, none))) <$>
        (initCKARaw cka prng fs lam ⟨true, tL, 0⟩ false :
          OracleComp (unifSpec + CryptoGames.CKA.spec Γ CCoins T I) _) := by
    dsimp only [prog, redCKAAuthBucketProg, stEnc, ckaBucketStateEnc]
    rw [eval_bind, hInit, hVpEq]
    simp only [eval_ret, ReductionDsl.Expr.eval, v0_eval_cons,
      bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  change prog.eval (fun _ => A) () =
    (redCKAAuthBucket cka prng fs lam Δcka qep tL A :
      OracleComp (unifSpec + CryptoGames.CKA.spec Γ CCoins T I) Bool)
  unfold ReductionDsl.CostedReduction.eval ReductionDsl.CostedReduction.impl redCKAAuthBucket
  dsimp only
  rw [runCKAAuthBucket_eq_bind_initCKARaw, hInitP, bind_map_left]
  simp only [bind_assoc]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initCKARaw cka prng fs lam ⟨true, tL, 0⟩ false :
      OracleComp (unifSpec + CryptoGames.CKA.spec Γ CCoins T I) _) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initCKARaw_inv cka prng fs lam ⟨true, tL, 0⟩ false hqB hB1 hBB es₀ hes₀
  have hVR₀ := initCKARaw_vrInv (B := B_q) (qAdv := qAdv) cka prng fs lam ⟨true, tL, 0⟩ false
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_redCKAAuthBucket_vr_eq hDefaultE cka prng fs L B B_q Δcka qep tL
    hHk hVRHk heqT heqM heqE hA' es₀ none hInv₀ hVR₀
  change ((simulateQ (handlerImpl (C := ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      prog.handle) A).run (stEnc (es₀, none)) >>=
      fun ⟨b, s'⟩ => prog.finish.eval (.cons s' (.cons (t := .bool) b .nil))) = _
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es', winEp'⟩ hes' => ?_
  have hInv' := hSimInv (b', es', winEp') hes'
  have hBnd' := hInv'.toBoundedEngine
  dsimp only [Prod.map, id_eq, prog, redCKAAuthBucketProg, stEnc, ckaBucketStateEnc]
  rw [eval_bind_ret]
  have hEnvEq : (ReductionDsl.Expr.pair (.fst (ReductionDsl.Expr.v0 (O := OO))) (.snd .v0)).eval
      (ReductionDsl.Env.cons (t := ckaBucketEsTy) (esEnc vpEncCKA ckaHsEnc es', winEp')
        (ReductionDsl.Env.cons (t := .bool) b' .nil)) =
      (esEnc vpEncCKA ckaHsEnc es', winEp') := rfl
  rw [hEnvEq, eval_caseOpt, snd_eval, v0_eval_cons]
  rcases winEp' with _ | tWin
  · simp [eval_ret, ReductionDsl.Expr.eval]
  · simp only [eval_ret, pure_bind]
    set ρ_fin := ReductionDsl.Env.cons (t := .nat) tWin
      (ReductionDsl.Env.cons (t := .prod ckaEsTy (.opt .nat)) (esEnc vpEncCKA ckaHsEnc es', some tWin)
        (ReductionDsl.Env.cons (t := ckaBucketEsTy) (esEnc vpEncCKA ckaHsEnc es', some tWin)
          (ReductionDsl.Env.cons (t := .bool) b' .nil)))
    have hAuth := cAuthOKE_eval vpEncCKA (O' := OO) L (2 + Δcka)
      (optNatLit tL) .v0 (esG (.fst .v1)) ρ_fin es'.g hBnd'.leaks_le hBnd'.corrs_le rfl
    rw [optNatLit_eval, v0_eval_cons] at hAuth
    change pure ((!((esAbort (.fst .v1)).eval ρ_fin) &&
        (cGsWin (esG (.fst .v1))).eval ρ_fin) && _) = _
    rw [hAuth]
    rfl

theorem redCKAAuthBucketProg_eval_atomic
    {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : CryptoGames.SM.MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    (redCKAAuthBucketProg (q + 1) B0 1 qep maxForwardJumps tL :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) () =
      redCKAAuthBucket (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam 1 qep tL A := by
  intro B0
  exact redCKAAuthBucketProg_eval_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksCKABucket_vrInv_fsAtomicB' Dh encPt C ℓ encT idOf B0 1 tL)
    (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD
      (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

end CKABucketAtomicEval

end

end Computational.Proofs.SessionCostedFig8.BucketCKAEval
