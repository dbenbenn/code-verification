/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BucketFSAuthEvalHooks
import Computational.Proofs.ReductionDsl.SM.RedFS

/-!
# Hook Evaluation Lemmas (Part B: `fsSend`, `fsRecv`, `commit`, `reveal`, and `HooksCAgrees`)

Proves the `FSAEAD` channel hook evaluation bridges (`fsMultiBucketAuthFsSendC_eval`,
`fsMultiBucketAuthFsRecvC_eval`, `fsMultiBucketAuthCommitC_eval`, `fsMultiBucketAuthRevealC_eval`)
and packages `HooksCAgrees` (`hooksFSMultiBucketAuthC_agrees`) for `hooksFSMultiBucketAuthC` against
shallow `hooksFSMultiBucketAuth`.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthEvalHooksB

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open _root_.ReductionDsl (Ops Ty Env Expr Comp)
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CKA (CKASort CKAOp ckaOps ckaHdrTy ckaHdrCtTy ckaPsTy ckaPsEnc)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps FSHdrTag fsHdrRrTy fsHdrRrEnc)
open _root_.CryptoGames.SM (Record partyEnc maxN not_eval and_eval orE_eval letE_eval pair_eval
  some_eval ite_eval healedByE_eval)
open _root_.CryptoGames.SM.Engine (Ctx HM TComp VP HooksCAgrees vpTblEnc cGsTy cGsEnc
  cSafeChE cSafeChE_eval cGsTL cGsEpoch cRecTy cRecEnc cRecMsg vpTcurNat vpVS vpVR vpΓ vpRoot
  realPartyE realPartyE_eval tset_eval_eq_update eval_ret eval_bind eval_bind_ret eval_ite)
open _root_.CryptoGames.SM.Construction (Header FSMultiSpec FSMultiBook realParty
  healEpoch fst_eval snd_eval eval_caseOpt_none eval_caseOpt_some eval_caseSum_inl
  eval_caseSum_inr fsTransFindE fsTransFindE_eval fsTransFilterE fsTransFilterE_eval
  rangeListC rangeListC_eval foldr_update_apply)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (fsaeadMultiBucketIface
  fsMultiBucketSessBookTy fsMultiBucketHsTy fsMultiBucketVpTy mbHsGetBookAt mbHsSetBookAt
  mbHsSetLfWin fsTransFindBucketE fsTransFilterBucketE fsMultiBucketAuthFsSendC
  fsMultiBucketAuthFsRecvC fsMultiBucketAuthCommitC rangeListBucketC isExtMultiBucketEntryE
  anyExtMultiBucketVRE unliftMultiBucketEntryE unliftMultiBucketVRE fsMultiBucketAuthRevealC
  hooksFSMultiBucketAuthC)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (FSMultiBucketAuthState
  liftFSMultiBucket hooksFSMultiBucketAuth fsMultiBucketHsEnc FSMultiBucketHBounded
  FSMultiBucketHBoundedPost hooksFSMultiBucketAuth_startSend_preserve
  hooksFSMultiBucketAuth_startRecv_preserve hooksFSMultiBucketAuth_fsRecv_preserve)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthEvalHooks (mbHsGetBookAt_eval
  mbHsSetBookAt_eval mbHsSetLfWin_eval fsMultiBucketAuthStartSendC_eval
  fsMultiBucketAuthStartRecvC_eval)

section BucketHookEvalB

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
local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM" =>
  @fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
local notation "mVpTy" => @fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mBookTy" => @fsMultiBucketSessBookTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => @fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsMBEnc" =>
  fsMultiBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
    (SS := SS) (RS := RS) (M := M)
local notation "vpMEnc" =>
  vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (KR := KR) (RSt := RSt)
    (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := Ty.base CKASort.γ) (svT := Ty.base CKASort.sig)
    (ssvT := Ty.sum (Ty.base CKASort.ss) Ty.nat) (rsvT := Ty.sum (Ty.base CKASort.rs) Ty.nat)

private def liftFSMultiBucketRaw (sIdx : ℕ) {α : Type}
    (x : _root_.CryptoGames.FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    TComp (FSMultiSpec SS RS T M E) α :=
  simulateQ (fun
    | .inl n => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n)
    | .inr q => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inr ⟨sIdx, q⟩)) x

private theorem liftFSMultiBucket_eq (sIdx : ℕ) {α : Type}
    (x : _root_.CryptoGames.FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    (liftFSMultiBucket sIdx x :
      HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E) α) =
      StateT.lift (liftFSMultiBucketRaw sIdx x) := by
  unfold liftFSMultiBucket liftFSMultiBucketRaw
  exact congrArg (fun f => StateT.lift (simulateQ f x)) (by funext z; cases z <;> rfl)

private theorem query_fsMultiB_tr_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat (.prod hdrTy (.base .msg)))) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.tr arg).eval ρ =
      liftFSMultiBucketRaw (arg.eval ρ).1
        (_root_.CryptoGames.FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS)
          (arg.eval ρ).2.1 (arg.eval ρ).2.2) := by
  simp [Comp.eval, fsaeadMultiBucketIface, liftFSMultiBucketRaw,
    _root_.CryptoGames.FSAEAD.transmitQuery]

private theorem query_fsMultiB_ch_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat (.prod hdrTy (.prod (.base .msg) (.base .msg))))) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.ch arg).eval ρ =
      liftFSMultiBucketRaw (arg.eval ρ).1
        (_root_.CryptoGames.FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
          (arg.eval ρ).2.1 (arg.eval ρ).2.2.1 (arg.eval ρ).2.2.2) := by
  simp [Comp.eval, fsaeadMultiBucketIface, liftFSMultiBucketRaw,
    _root_.CryptoGames.FSAEAD.challengeQuery]

private theorem query_fsMultiB_cs_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat .unit)) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.cs arg).eval ρ =
      liftFSMultiBucketRaw (arg.eval ρ).1
        (_root_.CryptoGames.FSAEAD.corruptSenderQuery (SenderState := SS) (ReceiverState := RS)
          (AssocData := Header T) (Message := M) (Ciphertext := E)) := by
  simp [Comp.eval, fsaeadMultiBucketIface, liftFSMultiBucketRaw,
    _root_.CryptoGames.FSAEAD.corruptSenderQuery]

private theorem query_fsMultiB_dl_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat hdrCtTy)) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.dl arg).eval ρ =
      Option.map fsHdrRrEnc <$>
        liftFSMultiBucketRaw (arg.eval ρ).1
          (_root_.CryptoGames.FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS)
            (arg.eval ρ).2.1 (arg.eval ρ).2.2) := by
  simp [Comp.eval, fsaeadMultiBucketIface, liftFSMultiBucketRaw,
    _root_.CryptoGames.FSAEAD.deliverQuery]

private theorem query_fsMultiB_ij_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat hdrCtTy)) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.ij arg).eval ρ =
      Option.map fsHdrRrEnc <$>
        liftFSMultiBucketRaw (arg.eval ρ).1
          (_root_.CryptoGames.FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS)
            (arg.eval ρ).2.1 (arg.eval ρ).2.2) := by
  simp [Comp.eval, fsaeadMultiBucketIface, liftFSMultiBucketRaw,
    _root_.CryptoGames.FSAEAD.injectQuery]

private theorem fsMultiBucketAuthFsSendC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (hFsSend : fsSend = fs.send)
    (L Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.sum (.base .ss) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) (ρ : Env Γ')
    (h : FSMultiBucketAuthState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (hh : hE.eval ρ = hsMBEnc h)
    (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx) (hp : pE.eval ρ = partyEnc P) :
    (fsMultiBucketAuthFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).eval ρ =
      Prod.map id hsMBEnc <$>
        ((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).fsSend ctx P (tE.eval ρ)
          (ssvE.eval ρ) (hdrE.eval ρ) (mE.eval ρ) (pairE.eval ρ)).run h := by
  unfold fsMultiBucketAuthFsSendC hooksFSMultiBucketAuth
  dsimp only
  set ssv : SS ⊕ ℕ := ssvE.eval ρ
  set hdr : Header T := hdrE.eval ρ
  set m : M := mE.eval ρ
  set pair : Option (M × M) := pairE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair pE (.pair ssvE (.pair hdrE (.pair mE pairE)))))).eval
      ρ = (hsMBEnc h, cGsEnc vpMEnc ctx, partyEnc P, ssv, hdr, m, pair) := by
    simp [Expr.eval, hh, hctx, hp, ssv, hdr, m, pair]
  set ρ₁ := Env.cons
    (t := .prod mbHsTy (.prod (cGsTy mVpTy) (.prod .bool (.prod (.sum (.base CKASort.ss) .nat)
      (.prod hdrTy (.prod (.base CKASort.msg)
        (.opt (.prod (.base CKASort.msg) (.base CKASort.msg)))))))))
    (hsMBEnc h, cGsEnc vpMEnc ctx, partyEnc P, ssv, hdr, m, pair) ρ
  rw [eval_bind_ret, h0]
  rcases ssv with ss | sIdx
  · rw [eval_caseSum_inl rfl, eval_ret]
    simp [StateT.run_pure, hFsSend, Prod.map, Expr.eval, Expr.v0, Expr.v1]
  · rw [eval_caseSum_inr rfl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    set ρ₂ := Env.cons (t := .nat) sIdx ρ₁
    set bk := (h.book sIdx).getD {}
    have hSafe : (cSafeChE (2 + Δcka) (.fst (.snd (Expr.v1 (O := OO))))
        (.fst (.snd (.snd .v1)))).eval ρ₂ = ctx.safeCh (2 + Δcka) P :=
      cSafeChE_eval vpMEnc (O' := OO) (2 + Δcka)
        (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) ρ₂ ctx P rfl rfl
    have hBk0 : (mbHsGetBookAt (O := OO) (.fst .v1) .v0).eval ρ₂ =
        (bk.sCorr, bk.fsCount, bk.fsTrans) :=
      mbHsGetBookAt_eval (O' := OO) (.fst .v1) .v0 ρ₂ h rfl
    have hCond : (Expr.and (.not (cSafeChE (2 + Δcka) (.fst (.snd (Expr.v1 (O := OO))))
        (.fst (.snd (.snd .v1))))) (.not (.fst (mbHsGetBookAt (.fst .v1) .v0)))).eval ρ₂ =
        (!(ctx.safeCh (2 + Δcka) P) && !bk.sCorr) := by
      rw [and_eval, not_eval, not_eval, hSafe, fst_eval, hBk0]
    have hSendTrue : ∀ (h₁ : FSMultiBucketAuthState T RSt K I E),
        (Comp.ite (O := OO) (I := IIM) (.not (.fst .v0))
          (.ret (.pair .none (.snd .v0)))
          (.bind
            (.caseOpt (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
              (@Comp.query _ _ _ OO IIM _ FSHdrTag.tr
                (.pair .v1 (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                  (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))))
              (@Comp.query _ _ _ OO IIM _ FSHdrTag.ch
                (.pair .v2 (.pair (.fst (.snd (.snd (.snd (.snd .v3))))) .v0))))
            (.caseOpt .v0
              (.ret (.pair .none (.snd .v1)))
              (.ret (.pair (.some (.pair (Expr.inr (t := .base CKASort.ss) .v3) .v0))
                (mbHsSetBookAt (.snd .v2) .v3
                  (.pair (.fst (mbHsGetBookAt (.snd .v2) .v3))
                    (.pair (.add (.fst (.snd (mbHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                      (.cons (.pair (.add (.fst (.snd (mbHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                        (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) .v0))
                        (.snd (.snd (mbHsGetBookAt (.snd .v2) .v3)))))))))))).eval
          (Env.cons (t := .prod .bool mbHsTy) (true, hsMBEnc h₁) ρ₂) =
        Prod.map id hsMBEnc <$>
          ((do
              let e? ← match pair with
                | some (m₀, m₁) =>
                  liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.challengeQuery
                    (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
                | none =>
                  liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.transmitQuery
                    (SenderState := SS) (ReceiverState := RS) hdr m)
              match e? with
              | none => return none
              | some e =>
                modify fun (s : FSMultiBucketAuthState T RSt K I E) =>
                  let b := (s.book sIdx).getD {}
                  let cnt' := b.fsCount + 1
                  let b' : FSMultiBook T E :=
                    { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
                  { s with book := Function.update s.book sIdx (some b') }
                return some (.inr sIdx, e) :
            HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E)
              (Option ((SS ⊕ ℕ) × E))).run h₁) := by
      intro h₁
      set ρ₃ := Env.cons (t := .prod .bool mbHsTy) (true, hsMBEnc h₁) ρ₂
      rw [eval_ite]
      have hNotOk : (Expr.not (.fst (Expr.v0 (O := OO)))).eval ρ₃ = false := rfl
      rw [hNotOk]
      simp only [Bool.false_eq_true, ↓reduceIte, eval_bind]
      rcases pair with _ | ⟨m₀, m₁⟩
      · rw [eval_caseOpt_none rfl, query_fsMultiB_tr_eval]
        simp only [ρ₃, ρ₂, ρ₁, liftFSMultiBucket_eq, StateT.run_bind, StateT.run_lift,
          bind_assoc, pure_bind, map_bind, Expr.eval, Expr.v1, Expr.v2]
        refine bind_congr fun e? => ?_
        rcases e? with _ | ct
        · rw [eval_caseOpt_none rfl, eval_ret]
          simp [StateT.run_pure, Prod.map, Expr.eval]
        · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
          set ρ₄ := Env.cons (t := .base CKASort.ct) ct
            (Env.cons (t := .opt (.base CKASort.ct)) (some ct) ρ₃)
          have hBk1 := mbHsGetBookAt_eval (.snd (Expr.v2 (O := OO))) .v3 ρ₄ h₁ rfl
          have hIdx4 : (Expr.v3 (O := OO)).eval ρ₄ = sIdx := rfl
          rw [hIdx4] at hBk1
          have hSet := mbHsSetBookAt_eval (.snd (Expr.v2 (O := OO))) .v3
            (.pair (.fst (mbHsGetBookAt (.snd .v2) .v3))
              (.pair (.add (.fst (.snd (mbHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                (.cons (.pair (.add (.fst (.snd (mbHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                  (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) .v0))
                  (.snd (.snd (mbHsGetBookAt (.snd .v2) .v3)))))) ρ₄ h₁ rfl
            (sc := ((h₁.book sIdx).getD {}).sCorr)
            (cnt := ((h₁.book sIdx).getD {}).fsCount + 1)
            (tr := (((h₁.book sIdx).getD {}).fsCount + 1, hdr, ct) :: ((h₁.book sIdx).getD {}).fsTrans)
            (by simp only [Expr.eval, hBk1]; rfl)
          erw [hSet]
          simp [ρ₄, ρ₃, ρ₂, StateT.run_modify, Prod.map, Expr.eval, Expr.v0, Expr.v3]
      · rw [eval_caseOpt_some rfl, query_fsMultiB_ch_eval]
        simp only [ρ₃, ρ₂, ρ₁, liftFSMultiBucket_eq, StateT.run_bind, StateT.run_lift,
          bind_assoc, pure_bind, map_bind, Expr.eval, Expr.v0, Expr.v2, Expr.v3]
        refine bind_congr fun e? => ?_
        rcases e? with _ | ct
        · rw [eval_caseOpt_none rfl, eval_ret]
          simp [StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
        · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
          set ρ₄ := Env.cons (t := .base CKASort.ct) ct
            (Env.cons (t := .opt (.base CKASort.ct)) (some ct) ρ₃)
          have hBk1 := mbHsGetBookAt_eval (.snd (Expr.v2 (O := OO))) .v3 ρ₄ h₁ rfl
          have hIdx4 : (Expr.v3 (O := OO)).eval ρ₄ = sIdx := rfl
          rw [hIdx4] at hBk1
          have hSet := mbHsSetBookAt_eval (.snd (Expr.v2 (O := OO))) .v3
            (.pair (.fst (mbHsGetBookAt (.snd .v2) .v3))
              (.pair (.add (.fst (.snd (mbHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                (.cons (.pair (.add (.fst (.snd (mbHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                  (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) .v0))
                  (.snd (.snd (mbHsGetBookAt (.snd .v2) .v3)))))) ρ₄ h₁ rfl
            (sc := ((h₁.book sIdx).getD {}).sCorr)
            (cnt := ((h₁.book sIdx).getD {}).fsCount + 1)
            (tr := (((h₁.book sIdx).getD {}).fsCount + 1, hdr, ct) :: ((h₁.book sIdx).getD {}).fsTrans)
            (by simp only [Expr.eval, hBk1]; rfl)
          erw [hSet]
          simp [ρ₄, ρ₃, ρ₂, StateT.run_modify, Prod.map, Expr.eval, Expr.v3]
    rw [eval_bind, eval_ite, hCond]
    by_cases hc : (!(ctx.safeCh (2 + Δcka) P) && !bk.sCorr) = true
    · simp only [hc, ↓reduceIte]
      rw [eval_bind, query_fsMultiB_cs_eval]
      have hCsArg : (Expr.pair (O := OO) .v0 .unit).eval ρ₂ = (sIdx, ()) := rfl
      rw [hCsArg]
      simp only [liftFSMultiBucket_eq, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
        map_bind]
      refine bind_congr fun cs? => ?_
      rcases cs? with _ | ss'
      · rw [eval_caseOpt_none rfl, eval_ret, pure_bind]
        simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
      · rw [eval_caseOpt_some rfl, eval_ret, pure_bind]
        dsimp only
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        set ρ_cs := Env.cons (t := .base CKASort.ss) ss'
          (Env.cons (t := .opt (.base CKASort.ss)) (some ss') ρ₂)
        have hBkCs := mbHsGetBookAt_eval (.fst (Expr.v3 (O := OO))) .v2 ρ_cs h rfl
        have hIdxCs : (Expr.v2 (O := OO)).eval ρ_cs = sIdx := rfl
        rw [hIdxCs] at hBkCs
        have hSetCs := mbHsSetBookAt_eval (.fst (Expr.v3 (O := OO))) .v2
          (.pair (.bool true)
            (.pair (.fst (.snd (mbHsGetBookAt (.fst .v3) .v2)))
              (.snd (.snd (mbHsGetBookAt (.fst .v3) .v2))))) ρ_cs h rfl
          (sc := true) (cnt := bk.fsCount) (tr := bk.fsTrans)
          (by simp only [Expr.eval, hBkCs]; rfl)
        let bk' : FSMultiBook T E := { bk with sCorr := true }
        let h' : FSMultiBucketAuthState T RSt K I E :=
          { h with book := Function.update h.book sIdx (some bk') }
        have hPairCs : (Expr.pair (O := OO) (.bool true)
            (mbHsSetBookAt (.fst .v3) .v2
              (.pair (.bool true)
                (.pair (.fst (.snd (mbHsGetBookAt (.fst .v3) .v2)))
                  (.snd (.snd (mbHsGetBookAt (.fst .v3) .v2))))))).eval ρ_cs =
            (true, hsMBEnc h') := by
          rw [pair_eval, hSetCs]; rfl
        rw [hPairCs, hSendTrue h']
        rcases pair with _ | ⟨m₀, m₁⟩ <;>
          simp only [liftFSMultiBucket_eq, StateT.run_bind, StateT.run_lift, bind_assoc, map_bind] <;>
          refine bind_congr fun e? => ?_ <;>
          (rcases e? with _ | e <;> simp [StateT.run_modify, StateT.run_pure, h', bk', bk])
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, eval_ret, StateT.run_bind, StateT.run_pure,
        pure_bind, Bool.not_true]
      have hPair0 : (Expr.pair (O := OO) (.bool true) (.fst .v1)).eval ρ₂ =
          (true, hsMBEnc h) := rfl
      rw [hPair0, hSendTrue h]
      rcases pair with _ | ⟨m₀, m₁⟩ <;>
        simp only [liftFSMultiBucket_eq, StateT.run_bind, StateT.run_lift, bind_assoc, map_bind] <;>
        refine bind_congr fun e? => ?_ <;>
        (rcases e? with _ | e <;> simp [StateT.run_modify, StateT.run_pure])

private theorem fsMultiBucketAuthCommitC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' mVpTy) (ρ : Env Γ')
    (h : FSMultiBucketAuthState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (old new : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (hh : hE.eval ρ = hsMBEnc h) (hnew : newE.eval ρ = vpMEnc new) :
    (fsMultiBucketAuthCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE oldE newE).eval ρ =
      Prod.map (Option.map vpMEnc) hsMBEnc <$>
        ((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).commit ctx P old new).run h := by
  simp [fsMultiBucketAuthCommitC, hooksFSMultiBucketAuth, StateT.run_pure,
    Prod.map, hh, hnew, Expr.eval]

private theorem fsTransFindBucketE_eval [DecidableEq T] [DecidableEq E]
    (heqT : eqT = (· == ·)) (heqE : eqE = (· == ·)) (L : ℕ) {Γ'}
    (trE : Expr OO Γ' (.list (.prod .nat hdrCtTy))) (hcE : Expr OO Γ' hdrCtTy)
    (ρ : Env Γ') (hL : (trE.eval ρ).length ≤ L) :
    (fsTransFindBucketE L trE hcE).eval ρ =
      (trE.eval ρ).find? (fun x => x.2 == hcE.eval ρ) :=
  fsTransFindE_eval heqT heqE L trE hcE ρ hL

private theorem fsTransFilterBucketE_eval (L : ℕ) {Γ'}
    (trE : Expr OO Γ' (.list (.prod .nat hdrCtTy))) (dropE : Expr OO Γ' .nat)
    (ρ : Env Γ') (hL : (trE.eval ρ).length ≤ L) :
    (fsTransFilterBucketE L trE dropE).eval ρ =
      (trE.eval ρ).filter (·.1 != dropE.eval ρ) :=
  fsTransFilterE_eval L trE dropE ρ hL

private theorem fsMultiBucketAuthFsRecvC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (heqT : eqT = (· == ·)) (heqE : eqE = (· == ·))
    (L B Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) = fs.receive rs hdr e)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.sum (.base .rs) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ')
    (h : FSMultiBucketAuthState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (rec_ : Option (Record M (Header T × E)))
    (hHB : FSMultiBucketHBoundedPost L h)
    (hh : hE.eval ρ = hsMBEnc h) (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx)
    (hrec : recE.eval ρ = rec_.map cRecEnc) :
    (fsMultiBucketAuthFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B la Δcka hE ctxE pE tE rsvE hdrE eE recE).eval ρ =
      Prod.map id hsMBEnc <$>
        ((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).fsRecv ctx P
          (tE.eval ρ) (rsvE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) rec_).run h := by
  unfold fsMultiBucketAuthFsRecvC hooksFSMultiBucketAuth
  dsimp only
  set t : ℕ := tE.eval ρ
  set rsv : RS ⊕ ℕ := rsvE.eval ρ
  set hdr : Header T := hdrE.eval ρ
  set e : E := eE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair tE (.pair rsvE (.pair hdrE (.pair eE recE)))))).eval ρ =
      (hsMBEnc h, cGsEnc vpMEnc ctx, t, rsv, hdr, e, rec_.map cRecEnc) := by
    simp [Expr.eval, hh, hctx, hrec, t, rsv, hdr, e]
  rw [eval_bind_ret, h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mbHsTy (.prod (cGsTy mVpTy) (.prod .nat (.prod (.sum (.base CKASort.rs) .nat)
      (.prod hdrTy (.prod (.base CKASort.ct) (.opt cRecTy)))))))
    (hsMBEnc h, cGsEnc vpMEnc ctx, t, rsv, hdr, e, rec_.map cRecEnc) ρ
  rcases rsv with rs | sIdx
  · rw [eval_caseSum_inl rfl]
    dsimp only
    have hOp : (Expr.op (O := OO) (CKAOp.fsReceive B)
        (.pair .v0
          (.pair (.fst (.snd (.snd (.snd (.snd .v1)))))
            (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))))).eval
        (Env.cons (t := .base CKASort.rs) rs ρ₁) =
        fs.receive rs hdr e := by
      simp only [ρ₁, prngOps, ckaOps, Expr.eval, Expr.v0, Expr.v1,
        Env.get_cons_zero, Env.get_cons_succ]
      exact hFsRecvB rs hdr e
    rcases hrc : fs.receive rs hdr e with _ | ⟨rs', i, m⟩
    · rw [eval_caseOpt_none (hOp.trans hrc), eval_ret]
      simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
    · rw [eval_caseOpt_some (hOp.trans hrc), eval_ret]
      simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2,
        Env.get_cons_zero, Env.get_cons_succ]
  · rw [eval_caseSum_inr rfl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    set ρ₂ := Env.cons (t := .nat) sIdx ρ₁
    set bk := (h.book sIdx).getD {}
    have hBkL : bk.fsTrans.length ≤ L := by
      dsimp only [bk]
      rcases hbk : h.book sIdx with _ | b
      · simp
      · exact hHB sIdx b hbk
    have hBk2 : (mbHsGetBookAt (O := OO) (.fst .v1) .v0).eval ρ₂ =
        (bk.sCorr, bk.fsCount, bk.fsTrans) :=
      mbHsGetBookAt_eval (O' := OO) (.fst .v1) .v0 ρ₂ h rfl
    set matched := bk.fsTrans.find? (fun x => x.2 == (hdr, e))
    have hFind2 : (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (O := OO) (.fst .v1) .v0)))
        (.pair (.fst (.snd (.snd (.snd (.snd .v1)))))
          (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))))).eval ρ₂ =
        matched := by
      rw [fsTransFindBucketE_eval heqT heqE L (.snd (.snd (mbHsGetBookAt (.fst .v1) .v0)))
        (.pair (.fst (.snd (.snd (.snd (.snd .v1)))))
          (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))) ρ₂
        (by simp [snd_eval, hBk2, hBkL])]
      rw [snd_eval, snd_eval, hBk2]
      simp [ρ₂, ρ₁, matched, Expr.eval, Expr.v1]
    let okShallow : HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E) Bool :=
      if matched.isNone && !(_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t) && !bk.sCorr then do
        match ← liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.corruptSenderQuery
            (ReceiverState := RS) (AssocData := Header T) (Message := M) (Ciphertext := E)) with
        | none => pure false
        | some _ =>
          modify fun s =>
            { s with book := Function.update s.book sIdx (some { (s.book sIdx).getD {} with sCorr := true }) }
          pure true
      else pure true
    have hOkHB : ∀ ok h₁, (ok, h₁) ∈ support (okShallow.run h) → FSMultiBucketHBoundedPost L h₁ := by
      intro ok h₁ hmem
      dsimp only [okShallow] at hmem
      split_ifs at hmem
      · rw [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨ans, h₀⟩, hans, hmem⟩ := hmem
        simp only [liftFSMultiBucket, StateT.run_lift, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hans
        obtain ⟨_, _, hEq⟩ := hans; cases hEq
        rcases ans with _ | _
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          cases hmem; exact hHB
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem
          cases hmem
          intro idx bk' hbk'
          by_cases hIdx : idx = sIdx
          · subst hIdx
            simp only [Function.update_self, Option.some.injEq] at hbk'
            rw [← hbk']; exact hBkL
          · simp only [Function.update_of_ne hIdx] at hbk'
            exact hHB idx bk' hbk'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        cases hmem; exact hHB
    have hOkEval :
        (Comp.caseOpt (O := OO) (I := IIM)
          (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (.fst .v1) .v0)))
            (.pair (.fst (.snd (.snd (.snd (.snd .v1)))))
              (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))))
          (.ite
            (.and (.not (_root_.CryptoGames.SM.healedByE (cGsTL (.fst (.snd .v1))) (2 + Δcka)
                (.fst (.snd (.snd .v1)))))
              (.not (.fst (mbHsGetBookAt (.fst .v1) .v0))))
            (.bind (@Comp.query _ _ _ OO IIM _ FSHdrTag.cs (.pair .v0 .unit))
              (.caseOpt .v0
                (.ret (.pair (.bool false) (.fst .v2)))
                (.ret (.pair (.bool true)
                  (mbHsSetBookAt (.fst .v3) .v2
                    (.pair (.bool true) (.snd (mbHsGetBookAt (.fst .v3) .v2))))))))
            (.ret (.pair (.bool true) (.fst .v1))))
          (.ret (.pair (.bool true) (.fst .v2)))).eval ρ₂ =
        Prod.map id hsMBEnc <$> (okShallow.run h) := by
      dsimp only [okShallow]
      rcases hM : matched with _ | mrec
      · rw [eval_caseOpt_none (hFind2.trans hM), eval_ite]
        simp only [Option.isNone_none, Bool.true_and]
        have hHealCond :
            (Expr.and (.not (_root_.CryptoGames.SM.healedByE
                (cGsTL (.fst (.snd (Expr.v1 (O := OO))))) (2 + Δcka) (.fst (.snd (.snd .v1)))))
              (.not (.fst (mbHsGetBookAt (.fst .v1) .v0)))).eval ρ₂ =
            (!(_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t) && !bk.sCorr) := by
          simp only [and_eval, not_eval, healedByE_eval, fst_eval, hBk2]
          rfl
        rw [hHealCond]
        by_cases hc : (!(_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t) && !bk.sCorr) = true
        · simp only [hc, ↓reduceIte]
          rw [eval_bind, query_fsMultiB_cs_eval, liftFSMultiBucket_eq]
          simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
          refine bind_congr fun cs? => ?_
          rcases cs? with _ | ss'
          · rw [eval_caseOpt_none rfl, eval_ret]
            simp [ρ₂, ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v2]
          · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
            set ρ_cs := Env.cons (t := .base CKASort.ss) ss'
              (Env.cons (t := .opt (.base CKASort.ss)) (some ss') ρ₂)
            have hBkCs := mbHsGetBookAt_eval (O' := OO) (.fst .v3) .v2 ρ_cs h rfl
            have hIdxCs : (Expr.v2 (O := OO)).eval ρ_cs = sIdx := rfl
            rw [hIdxCs] at hBkCs
            have hSetCs := mbHsSetBookAt_eval (O' := OO) (.fst .v3) .v2
              (.pair (.bool true) (.snd (mbHsGetBookAt (.fst .v3) .v2))) ρ_cs h rfl
              (sc := true) (cnt := bk.fsCount) (tr := bk.fsTrans)
              (by rw [pair_eval, snd_eval, hBkCs]; rfl)
            rw [hIdxCs] at hSetCs
            rw [hSetCs]
            simp [StateT.run_modify, Prod.map, bk, Expr.eval]
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, eval_ret, StateT.run_pure, map_pure]
          rfl
      · rw [eval_caseOpt_some (hFind2.trans hM), eval_ret]
        simp [ρ₂, ρ₁, Option.isNone_some, StateT.run_pure, Prod.map, Expr.eval, Expr.v2]
    rw [eval_bind, hOkEval, bind_map_left, map_bind]
    refine OracleComp.bind_congr_of_forall_mem_support (okShallow.run h) fun ⟨ok, h₁⟩ hokMem => ?_
    have hHB₁ : FSMultiBucketHBoundedPost L h₁ := hOkHB ok h₁ hokMem
    dsimp only [Prod.map, id]
    rcases ok with _ | _
    · rw [eval_ite]
      have hNotFalse : (Expr.not (.fst (Expr.v0 (O := OO)))).eval
          (Env.cons (t := .prod .bool mbHsTy) (false, hsMBEnc h₁) ρ₂) = true := rfl
      rw [hNotFalse]
      simp [eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      set ρ₃ := Env.cons (t := .prod .bool mbHsTy) (true, hsMBEnc h₁) ρ₂
      rw [eval_ite]
      have hNotTrue : (Expr.not (.fst (Expr.v0 (O := OO)))).eval ρ₃ = false := rfl
      rw [hNotTrue]
      simp only [Bool.false_eq_true, ↓reduceIte, eval_bind]
      have hBk3_0 : (mbHsGetBookAt (O := OO) (.fst .v2) .v1).eval ρ₃ =
          (bk.sCorr, bk.fsCount, bk.fsTrans) :=
        mbHsGetBookAt_eval (O' := OO) (.fst .v2) .v1 ρ₃ h rfl
      have hFind3 : (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (O := OO) (.fst .v2) .v1)))
          (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
            (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))).eval ρ₃ = matched := by
        rw [fsTransFindBucketE_eval heqT heqE L (.snd (.snd (mbHsGetBookAt (.fst .v2) .v1)))
          (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
            (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))) ρ₃
          (by simp [snd_eval, hBk3_0, hBkL])]
        rw [snd_eval, snd_eval, hBk3_0]
        simp [ρ₃, ρ₂, ρ₁, matched, Expr.eval, Expr.v2]
      have hQ :
          (Comp.caseOpt (O := OO) (I := IIM)
            (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (.fst .v2) .v1)))
              (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))))
            (@Comp.query _ _ _ OO IIM _ FSHdrTag.ij
              (.pair .v1 (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))))
            (@Comp.query _ _ _ OO IIM _ FSHdrTag.dl
              (.pair .v2 (.pair (.fst (.snd (.snd (.snd (.snd .v3)))))
                (.fst (.snd (.snd (.snd (.snd (.snd .v3)))))))))).eval ρ₃ =
          Option.map fsHdrRrEnc <$>
            liftFSMultiBucketRaw sIdx
              (if matched.isSome then
                _root_.CryptoGames.FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e
              else
                _root_.CryptoGames.FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) hdr e) := by
        rcases hM : matched with _ | mrec
        · rw [eval_caseOpt_none (hFind3.trans hM), query_fsMultiB_ij_eval]; rfl
        · rw [eval_caseOpt_some (hFind3.trans hM), query_fsMultiB_dl_eval]; rfl
      have hLiftQ :
          ((if matched.isSome then
            liftFSMultiBucket sIdx
              (_root_.CryptoGames.FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
          else
            liftFSMultiBucket sIdx
              (_root_.CryptoGames.FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)) :
            HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E) _).run h₁ =
          (·, h₁) <$> liftFSMultiBucketRaw sIdx
            (if matched.isSome then
              _root_.CryptoGames.FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e
            else
              _root_.CryptoGames.FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) hdr e) := by
        cases matched <;> simp [liftFSMultiBucket_eq]
      rw [hQ, bind_map_left, StateT.run_bind, hLiftQ, bind_map_left, map_bind]
      refine bind_congr fun res => ?_
      rcases res with _ | (_ | ⟨msgIdx, mo'⟩)
      · dsimp only [Option.map]
        rw [eval_caseOpt_none rfl, eval_ret]
        simp [ρ₃, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
      · dsimp only [Option.map, fsHdrRrEnc]
        rw [eval_caseOpt_some rfl, eval_caseSum_inl rfl, eval_ret]
        simp [ρ₃, StateT.run_pure, Prod.map, Expr.eval, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
      · dsimp only [Option.map, fsHdrRrEnc]
        rw [eval_caseOpt_some rfl, eval_caseSum_inr rfl, eval_ite]
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        set bk₁ := (h₁.book sIdx).getD {}
        have hBkL₁ : bk₁.fsTrans.length ≤ L := by
          dsimp only [bk₁]
          rcases hbk₁ : h₁.book sIdx with _ | b
          · simp
          · exact hHB₁ sIdx b hbk₁
        set ρ₄ := Env.cons (t := .prod .nat (.opt (.base CKASort.msg))) (msgIdx, mo')
          (Env.cons (t := fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E) (.inr (msgIdx, mo'))
            (Env.cons (t := .opt (fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E))
              (some (.inr (msgIdx, mo'))) ρ₃))
        have hBk4_1 : (mbHsGetBookAt (O := OO) (.snd .v3) .v4).eval ρ₄ =
            (bk₁.sCorr, bk₁.fsCount, bk₁.fsTrans) :=
          mbHsGetBookAt_eval (O' := OO) (.snd .v3) .v4 ρ₄ h₁ rfl
        have hBk4_0 : (mbHsGetBookAt (O := OO) (.fst .v5) .v4).eval ρ₄ =
            (bk.sCorr, bk.fsCount, bk.fsTrans) :=
          mbHsGetBookAt_eval (O' := OO) (.fst .v5) .v4 ρ₄ h rfl
        have hFind4 : (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (O := OO) (.fst .v5) .v4)))
            (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
              (.fst (.snd (.snd (.snd (.snd (.snd .v5)))))))).eval ρ₄ = matched := by
          rw [fsTransFindBucketE_eval heqT heqE L (.snd (.snd (mbHsGetBookAt (.fst .v5) .v4)))
            (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
              (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))) ρ₄
            (by simp [snd_eval, hBk4_0, hBkL])]
          rw [snd_eval, snd_eval, hBk4_0]
          simp [Expr.v5, ρ₄, ρ₃, ρ₂, ρ₁, matched, Expr.eval, Env.get_cons_zero, Env.get_cons_succ]
        have hLfCond :
            (Expr.and (.bool la)
              (.caseOpt
                (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (O := OO) (.fst .v5) .v4)))
                  (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
                    (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
                (.and (.not (.fst (mbHsGetBookAt (.snd .v3) .v4)))
                  (.lt (.fst (.snd (mbHsGetBookAt (.snd .v3) .v4))) (.fst .v0)))
                (.bool false))).eval ρ₄ =
            (((la && matched.isNone) && !bk₁.sCorr) && decide (bk₁.fsCount < msgIdx)) := by
          rw [and_eval]
          simp only [Expr.eval, hFind4, hBk4_1]
          rcases matched with _ | mrec <;> cases la <;> cases bk₁.sCorr <;> rfl
        rw [hLfCond]
        by_cases hLf : (((la && matched.isNone) && !bk₁.sCorr) && decide (bk₁.fsCount < msgIdx)) = true
        · simp only [hLf, ↓reduceIte, eval_ret, pair_eval, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, pure_bind, map_pure, Prod.map]
          rw [mbHsSetLfWin_eval (O' := OO) (.snd .v3) (.bool true) ρ₄ h₁ rfl]
          rfl
        · simp only [hLf, Bool.false_eq_true, ↓reduceIte, eval_ret, pair_eval,
            StateT.run_bind, StateT.run_modify, pure_bind]
          have hDrop : (Expr.caseOpt (O := OO)
              (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (.fst .v5) .v4)))
                (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
                  (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
              (.fst .v0) (.fst .v0)).eval ρ₄ =
              (matched.map (·.1)).getD msgIdx := by
            simp only [Expr.eval, hFind4]
            rcases matched with _ | mrec <;> rfl
          have hFlt := fsTransFilterBucketE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            L (.snd (.snd (mbHsGetBookAt (.snd .v3) .v4)))
            (.caseOpt (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (.fst .v5) .v4)))
                (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
                  (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
              (.fst .v0) (.fst .v0)) ρ₄ (by simp [snd_eval, hBk4_1, hBkL₁])
          rw [hDrop] at hFlt
          have hTrEq : (Expr.snd (.snd (mbHsGetBookAt (O := OO) (.snd .v3) .v4))).eval ρ₄ =
              bk₁.fsTrans := by simp [snd_eval, hBk4_1]
          rw [hTrEq] at hFlt
          have hH4 := mbHsSetBookAt_eval (O' := OO) (.snd .v3) .v4
            (.pair (.fst (mbHsGetBookAt (.snd .v3) .v4))
              (.pair (.fst (.snd (mbHsGetBookAt (.snd .v3) .v4)))
                (fsTransFilterBucketE L (.snd (.snd (mbHsGetBookAt (.snd .v3) .v4)))
                  (.caseOpt (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (.fst .v5) .v4)))
                      (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
                        (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
                    (.fst .v0) (.fst .v0))))) ρ₄ h₁ rfl
            (sc := bk₁.sCorr) (cnt := bk₁.fsCount)
            (tr := bk₁.fsTrans.filter (·.1 != (matched.map (·.1)).getD msgIdx))
            (by simp [pair_eval, fst_eval, snd_eval, hBk4_1, hFlt])
          have hIdx4 : (Expr.v4 (O := OO)).eval ρ₄ = sIdx := rfl
          rw [hIdx4] at hH4
          have hOut :
              (Expr.caseOpt (O := OO) (.snd .v0)
                (Expr.caseOpt (.snd (.snd (.snd (.snd (.snd (.snd .v5))))))
                  .none
                  (.some (.some (.pair (Expr.inr (O := OO) (t := .base CKASort.rs) .v5)
                    (.pair (.fst .v1) (cRecMsg .v0))))))
                (.some (.some (.pair (Expr.inr (O := OO) (t := .base CKASort.rs) .v5)
                  (.pair (.fst .v1) .v0))))).eval ρ₄ =
              (match mo', rec_ with
                | some m, _ => some (some ((.inr sIdx : RS ⊕ ℕ), msgIdx, m))
                | none, some r => some (some ((.inr sIdx : RS ⊕ ℕ), msgIdx, r.msg))
                | none, none => none) := by
            rcases mo' with _ | m
            · rcases rec_ with _ | r <;>
                simp [Expr.v5, ρ₄, ρ₃, ρ₂, ρ₁, cRecMsg, cRecEnc, Expr.eval, Expr.v0, Expr.v1,
                  Env.get_cons_zero, Env.get_cons_succ]
            · simp [Expr.v5, ρ₄, ρ₃, ρ₂, Expr.eval, Expr.v0, Expr.v1,
                Env.get_cons_zero, Env.get_cons_succ]
          rw [hOut, hH4]
          rcases mo' with _ | m
          · rcases rec_ with _ | r <;> rfl
          · rfl

private theorem rangeListBucketC_eval (L : ℕ) {Γ' : List (Ty SP)} (ρ : Env Γ') :
    (rangeListBucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L (Γ' := Γ')).eval ρ =
      pure (List.range L).reverse :=
  rangeListC_eval (O' := OO) (I' := IIM) L ρ

private theorem isExtMultiBucketEntryE_eval {Γ'}
    (entryE : Expr OO Γ' (.opt (.sum (.base .rs) .nat))) (ρ : Env Γ') :
    (isExtMultiBucketEntryE entryE).eval ρ =
      match entryE.eval ρ with
      | some (.inr _) => true
      | _ => false := by
  unfold isExtMultiBucketEntryE
  rcases h1 : entryE.eval ρ with _ | (rs | sIdx) <;> simp [h1, Expr.eval, Expr.v0]

private theorem foldr_ite_true_eq_any {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.foldr (fun x acc => if p x then true else acc) false = l.any p
  | [] => rfl
  | a :: l => by
    simp only [List.foldr_cons, List.any_cons, foldr_ite_true_eq_any p l]
    cases p a <;> rfl

private theorem anyExtMultiBucketVRE_eval (L : ℕ) {Γ'}
    (vRE : Expr OO Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO Γ' (.list .nat)) (ρ : Env Γ')
    (hRng : rngE.eval ρ = (List.range L).reverse) :
    (anyExtMultiBucketVRE L vRE rngE).eval ρ =
      (List.range L).any (fun t =>
        match (vRE.eval ρ) t with
        | some (.inr _) => true
        | _ => false) := by
  unfold anyExtMultiBucketVRE
  rw [letE_eval]
  set vR := vRE.eval ρ
  have h0 : (Expr.pair vRE rngE).eval ρ = (vR, (List.range L).reverse) := by
    simp [Expr.eval, vR, hRng]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (.tbl (.opt (.sum (.base CKASort.rs) .nat))) (.list .nat))
    (vR, (List.range L).reverse) ρ
  have hTake : (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = (List.range L).reverse := by
    change ((List.range L).reverse).take L = (List.range L).reverse; simp
  change List.foldr _ false (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = _
  rw [hTake]
  have hStep :
      (fun (x : ℕ) (acc : Bool) =>
        (Expr.ite (O := OO)
          (isExtMultiBucketEntryE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            (.tget (.fst .v2) .v0))
          (.bool true) .v1).eval
          (Env.cons (t := .nat) x (Env.cons (t := .bool) acc ρ₁))) =
      (fun (x : ℕ) (acc : Bool) =>
        if (match vR x with | some (.inr _) => true | _ => false) then true else acc) := by
    funext x acc; rw [ite_eval, isExtMultiBucketEntryE_eval]; rfl
  rw [hStep, foldr_ite_true_eq_any]; simp

private theorem unliftMultiBucketEntryE_eval {Γ'}
    (entryE : Expr OO Γ' (.opt (.sum (.base .rs) .nat))) (ρ : Env Γ') :
    (unliftMultiBucketEntryE entryE).eval ρ =
      match entryE.eval ρ with
      | some (.inl rs) => some rs
      | _ => none := by
  unfold unliftMultiBucketEntryE
  rcases h1 : entryE.eval ρ with _ | (rs | sIdx) <;> simp [h1, Expr.eval, Expr.v0]

private theorem unliftMultiBucketVRE_eval (L : ℕ) {Γ'}
    (vRE : Expr OO Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO Γ' (.list .nat)) (ρ : Env Γ')
    (hRng : rngE.eval ρ = (List.range L).reverse) :
    (unliftMultiBucketVRE L vRE rngE).eval ρ =
      fun t =>
        if t < L then
          match (vRE.eval ρ) t with
          | some (.inl rs) => some rs
          | _ => none
        else none := by
  unfold unliftMultiBucketVRE
  rw [letE_eval]
  set vR := vRE.eval ρ
  have h0 : (Expr.pair vRE rngE).eval ρ = (vR, (List.range L).reverse) := by
    simp [Expr.eval, vR, hRng]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (.tbl (.opt (.sum (.base CKASort.rs) .nat))) (.list .nat))
    (vR, (List.range L).reverse) ρ
  have hTake : (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = (List.range L).reverse := by
    change ((List.range L).reverse).take L = (List.range L).reverse; simp
  change List.foldr _ (fun _ => none) (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = _
  rw [hTake]
  have hStep :
      (fun (x : ℕ) (acc : ℕ → Option RS) =>
        (Expr.tset (O := OO) .v1 .v0
          (unliftMultiBucketEntryE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            (.tget (.fst .v2) .v0))).eval
          (Env.cons (t := .nat) x
            (Env.cons (t := .tbl (.opt (.base CKASort.rs))) acc ρ₁))) =
      (fun (x : ℕ) (acc : ℕ → Option RS) =>
        Function.update acc x
          (match vR x with | some (.inl rs) => some rs | _ => none)) := by
    funext x acc; rw [tset_eval_eq_update, unliftMultiBucketEntryE_eval]; rfl
  rw [hStep]
  funext t; rw [foldr_update_apply]; simp [List.mem_reverse, List.mem_range]

theorem fsMultiBucketAuthRevealC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) (ρ : Env Γ')
    (h : FSMultiBucketAuthState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (hh : hE.eval ρ = hsMBEnc h) (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx)
    (hvp : vpE.eval ρ = vpMEnc vp) :
    (fsMultiBucketAuthRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L gMain la tL hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) hsMBEnc <$>
        ((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).reveal
          ctx P vp).run h := by
  unfold fsMultiBucketAuthRevealC hooksFSMultiBucketAuth
  dsimp only
  set tH : ℕ := healEpoch tL
  have h0 : (Expr.pair hE (.pair ctxE vpE)).eval ρ =
      (hsMBEnc h, cGsEnc vpMEnc ctx, vpMEnc vp) := by
    simp [Expr.eval, hh, hctx, hvp]
  set ρ₁ := Env.cons (t := .prod mbHsTy (.prod (cGsTy mVpTy) mVpTy))
    (hsMBEnc h, cGsEnc vpMEnc ctx, vpMEnc vp) ρ
  rw [eval_bind_ret, h0, eval_ite]
  have hGuard :
      (Expr.and (.not (.bool gMain))
        (_root_.CryptoGames.SM.orE
          (.not (.lt (vpTcurNat (.snd (.snd (Expr.v0 (O := OO))))) (.nat tH)))
          (.not (.lt (maxN (.fst (cGsEpoch (.fst (.snd .v0)))) (.snd (cGsEpoch (.fst (.snd .v0)))))
            (.nat tH))))).eval ρ₁ =
      (!gMain && (!(decide (vp.tcur < tH)) ||
        !(decide (max (ctx.epoch Party.A) (ctx.epoch Party.B) < tH)))) := by
    rw [and_eval, not_eval, orE_eval, not_eval, not_eval]
    have hE1 : (vpTcurNat (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = vp.tcur := rfl
    have hEpA : (Expr.fst (cGsEpoch (.fst (.snd (Expr.v0 (O := OO)))))).eval ρ₁ =
        ctx.epoch Party.A := rfl
    have hEpB : (Expr.snd (cGsEpoch (.fst (.snd (Expr.v0 (O := OO)))))).eval ρ₁ =
        ctx.epoch Party.B := rfl
    have hMax : (maxN (.fst (cGsEpoch (.fst (.snd (Expr.v0 (O := OO))))))
        (.snd (cGsEpoch (.fst (.snd .v0))))).eval ρ₁ =
        max (ctx.epoch Party.A) (ctx.epoch Party.B) := by
      unfold maxN _root_.CryptoGames.SM.leN
      rw [letE_eval, pair_eval, hEpA, hEpB, ite_eval, not_eval]
      change (if (!decide (ctx.epoch Party.B < ctx.epoch Party.A)) = true then
          ctx.epoch Party.B else ctx.epoch Party.A) =
        max (ctx.epoch Party.A) (ctx.epoch Party.B)
      by_cases hlt : ctx.epoch Party.B < ctx.epoch Party.A <;> simp [hlt] <;> omega
    simp [Expr.eval, hE1, hMax]
  rw [hGuard]
  by_cases hg : (!gMain && (!(decide (vp.tcur < tH)) ||
      !(decide (max (ctx.epoch Party.A) (ctx.epoch Party.B) < tH)))) = true
  · simp only [hg, ↓reduceIte, eval_ret, StateT.run_pure, map_pure, Prod.map]; rfl
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    have hStep2 : ∀ (ssReal : Option SS) (h₁ : FSMultiBucketAuthState T RSt K I E),
        (Comp.caseOpt (O := OO) (I := IIM) (.fst .v0)
          (.ret (.pair .none (.snd .v0)))
          (.bind (rangeListBucketC (sampKR := sampKR) (sampKC := sampKC)
              (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L)
            (.ite (anyExtMultiBucketVRE L (vpVR (.snd (.snd .v3))) .v0)
              (.ret (.pair .none (.snd .v2)))
              (.ret (.pair
                (.some (realPartyE (.snd (.snd .v3)) (vpΓ (.snd (.snd .v3)))
                  (vpRoot (.snd (.snd .v3))) .v1
                  (unliftMultiBucketVRE L (vpVR (.snd (.snd .v3))) .v0)))
                (.snd .v2)))))).eval
          (Env.cons (t := .prod (.opt (.opt (.base CKASort.ss))) mbHsTy)
            (some ssReal, hsMBEnc h₁) ρ₁) =
        Prod.map (Option.map ckaPsEnc) hsMBEnc <$>
          ((if (List.range L).any (fun t => match vp.vR t with | some (.inr _) => true | _ => false)
            then pure none
            else
              let vR' : ℕ → Option RS := fun t =>
                if t < L then
                  match vp.vR t with
                  | some (.inl rs) => some rs
                  | _ => none
                else none
              pure (some (realParty vp vp.γ vp.root ssReal vR')) :
            HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E) _).run h₁) := by
      intro ssReal h₁
      rw [eval_caseOpt_some rfl, eval_bind, rangeListBucketC_eval, pure_bind, eval_ite]
      set ρ₂ := Env.cons (t := .opt (.base CKASort.ss)) ssReal
        (Env.cons (t := .prod (.opt (.opt (.base CKASort.ss))) mbHsTy) (some ssReal, hsMBEnc h₁) ρ₁)
      set ρ₃ := Env.cons (t := .list .nat) (List.range L).reverse ρ₂
      have hAny := anyExtMultiBucketVRE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L (vpVR (.snd (.snd .v3))) .v0 ρ₃ rfl
      have hvR3 : (vpVR (.snd (.snd (Expr.v3 (O := OO))))).eval ρ₃ = vp.vR := rfl
      rw [hvR3] at hAny
      set bAny : Bool := (List.range L).any (fun t =>
        match vp.vR t with
        | some (.inr _) => true
        | _ => false)
      have hAnyB := hAny.trans (show _ = bAny by
        congr 1; funext t; rcases vp.vR t with _ | (_ | _) <;> rfl)
      rw [hAnyB]
      cases bAny
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [eval_ret, pair_eval, some_eval, StateT.run_pure, map_pure]
        have hUnlift := unliftMultiBucketVRE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
          (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          L (vpVR (.snd (.snd .v3))) .v0 ρ₃ rfl
        have hReal := realPartyE_eval (O' := OO)
          (.snd (.snd .v3)) (vpΓ (.snd (.snd .v3))) (vpRoot (.snd (.snd .v3))) .v1
          (unliftMultiBucketVRE L (vpVR (.snd (.snd .v3))) .v0) ρ₃ vp rfl
        rw [hvR3] at hUnlift
        rw [hReal, hUnlift]
        refine congrArg (fun f =>
          pure (some (ckaPsEnc (realParty vp vp.γ vp.root ssReal f)), hsMBEnc h₁)) ?_
        funext t; rcases vp.vR t with _ | (_ | _) <;> rfl
      · simp only [↓reduceIte]; rw [eval_ret, StateT.run_pure, map_pure]; rfl
    rw [eval_bind]
    have hvS : (vpVS (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = vp.vS := rfl
    rcases hvS' : vp.vS with _ | (ss | sIdx)
    · rw [eval_caseOpt_none (hvS.trans hvS'), eval_ret, pure_bind]
      simp only [pure_bind]; exact hStep2 none h
    · rw [eval_caseOpt_some (hvS.trans hvS'), eval_caseSum_inl rfl, eval_ret, pure_bind]
      simp only [pure_bind]; exact hStep2 (some ss) h
    · rw [eval_caseOpt_some (hvS.trans hvS'), eval_caseSum_inr rfl,
        eval_bind, query_fsMultiB_cs_eval]
      simp only [liftFSMultiBucket_eq, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
        map_bind]
      refine bind_congr fun cs? => ?_
      rcases cs? with _ | ss'
      · rw [eval_caseOpt_none rfl, eval_ret, pure_bind, eval_caseOpt_none rfl, eval_ret]
        simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v3]
      · rw [eval_caseOpt_some rfl, eval_ret, pure_bind]
        simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        set ρ_cs := Env.cons (t := .base CKASort.ss) ss'
          (Env.cons (t := .opt (.base CKASort.ss)) (some ss')
            (Env.cons (t := .nat) sIdx
              (Env.cons (t := .sum (.base CKASort.ss) .nat) (.inr sIdx) ρ₁)))
        have hBk := mbHsGetBookAt_eval (O' := OO) (.fst .v4) .v2 ρ_cs h rfl
        have hIdx : (Expr.v2 (O := OO)).eval ρ_cs = sIdx := rfl
        rw [hIdx] at hBk
        have hSet := mbHsSetBookAt_eval (O' := OO) (.fst .v4) .v2
          (.pair (.bool true) (.snd (mbHsGetBookAt (.fst .v4) .v2))) ρ_cs h rfl
          (sc := true) (cnt := ((h.book sIdx).getD {}).fsCount)
          (tr := ((h.book sIdx).getD {}).fsTrans)
          (by rw [pair_eval, snd_eval, hBk]; rfl)
        rw [hIdx] at hSet
        let bk0 : FSMultiBook T E := (h.book sIdx).getD {}
        let bk' : FSMultiBook T E := { bk0 with sCorr := true }
        let h' : FSMultiBucketAuthState T RSt K I E :=
          { h with book := Function.update h.book sIdx (some bk') }
        have hPair : (Expr.pair (O := OO) (.some (.some .v0))
            (mbHsSetBookAt (.fst .v4) .v2
              (.pair (.bool true) (.snd (mbHsGetBookAt (.fst .v4) .v2))))).eval ρ_cs =
            (some (some ss'), hsMBEnc h') := by
          rw [pair_eval, hSet]; rfl
        rw [hPair]
        exact hStep2 (some ss') h'

/-- Hook-level `HooksCAgrees` bundle for `hooksFSMultiBucketAuthC` against shallow
`hooksFSMultiBucketAuth`. -/
theorem hooksFSMultiBucketAuthC_agrees
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·)) (heqE : eqE = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) = fs.receive rs hdr e) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      hsMBEnc (FSMultiBucketHBounded L) (HBoundedPost := FSMultiBucketHBoundedPost L)
      (VROk := fun _ => True)
      (hooksFSMultiBucketAuthC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep gMain tL par la)
      (hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la) where
  hBounded_post _ h := h.2.2
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P hHB hh hctx _ :=
    fsMultiBucketAuthStartSendC_eval cka prng fs hSend hPrngUp hFsInitS heqI
      hSampCCoins hSampI hSampK L Δcka qep gMain tL par la
      hE ctxE pE tE γE σE rE ρ h ctx P hHB hh hctx
  startSend_bounded ctx P t γ σ r h hHB res hmem := by
    have hB := hooksFSMultiBucketAuth_startSend_preserve L cka prng fs Δcka qep gMain tL par la
      ctx P t γ σ r h res hmem
    unfold FSMultiBucketHBoundedPost; rw [hB.2.2]; exact hHB.2.2
  startRecv_eval hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh hctx _ :=
    fsMultiBucketAuthStartRecvC_eval cka prng fs hRecv hPrngUp hFsInitR heqT heqI
      hSampK L Δcka qep gMain tL par la hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh hctx
  startRecv_bounded ctx P t γ σ Tn h hHB res hmem := by
    have hB := hooksFSMultiBucketAuth_startRecv_preserve L cka prng fs Δcka qep gMain tL par la
      ctx P t γ σ Tn h res hmem
    unfold FSMultiBucketHBoundedPost; rw [hB.2.2]; exact hHB.2.2
  startRecv_vrOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ := trivial
  fsSend_eval hE ctxE pE tE ssE hdrE mE pairE ρ h ctx P _ hh hctx hp :=
    fsMultiBucketAuthFsSendC_eval cka prng fs hFsSend L Δcka qep gMain tL par la
      hE ctxE pE tE ssE hdrE mE pairE ρ h ctx P hh hctx hp
  fsRecv_eval hE ctxE pE tE rsE hdrE eE recE ρ h ctx P rec_ hHB _ hh hctx _ hrec :=
    fsMultiBucketAuthFsRecvC_eval cka prng fs heqT heqE L B Δcka qep gMain tL par la hFsRecvB
      hE ctxE pE tE rsE hdrE eE recE ρ h ctx P rec_ hHB hh hctx hrec
  fsRecv_bounded ctx P t0 rsv hdr e rec_ h hHB res hmem := by
    have hB := hooksFSMultiBucketAuth_fsRecv_preserve L cka prng fs Δcka qep gMain tL par la
      ctx P t0 rsv hdr e rec_ h res hmem
    intro idx bk' hbk'
    rcases hB.2.2 idx bk' hbk' with ⟨bk₀, hbk₀, hle⟩ | hle
    · have := hHB idx bk₀ hbk₀; omega
    · omega
  commit_eval hE ctxE pE oldE newE ρ h ctx P old new _ hh _ _ _ hnew :=
    fsMultiBucketAuthCommitC_eval cka prng fs L Δcka qep gMain tL par la
      hE ctxE pE oldE newE ρ h ctx P old new hh hnew
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh hctx _ hvp :=
    fsMultiBucketAuthRevealC_eval cka prng fs L Δcka qep gMain tL par la
      hE ctxE pE vpE ρ h ctx P vp hh hctx hvp

end BucketHookEvalB

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthEvalHooksB
