/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RestrictedReds
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.FSAEADRed -- proof-setup: allow-public-import

/-!
# Short-Message & Guarded-Inject Bounds for `(tL, par)`-Bucket Multi-Session FS-AEAD

Proves `redFSAuthMultiBucketProg_badTrOrCh`, `fsAtomicB_send_short`, and
`redFSAuthMultiBucketProg_guardedMultiInjectShort` for `BucketFSAuthBridge`.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthShort

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.PRFPRNG (prngSMCodec)
open _root_.CryptoGames.SM.Construction (Header)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (redFSAuthMultiBucketProg)

/-- Bad `.tr`/`.ch` query predicate flagging non-`ok` `.tr` plaintexts or any `.ch` query. -/
@[expose] def badTrOrCh {SS RS T M E : Type} (ok : M → Bool) :
    (unifSpec + OracleSpec.sigma (fun _ : ℕ =>
      CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Domain → Bool
  | .inr ⟨_, .inl (.inl (.inl (.inl (.inl ⟨_, m⟩))))⟩ => !ok m
  | .inr ⟨_, .inl (.inl (.inl (.inl (.inr _))))⟩ => true
  | _ => false

private theorem eval_ret' {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T' : OracleSpec ι} {I : ReductionDsl.Iface S T'}
    {Γ' : List (ReductionDsl.Ty S)} {τ : ReductionDsl.Ty S}
    (e : ReductionDsl.Expr O Γ' τ) (ρ : ReductionDsl.Env Γ') :
    (ReductionDsl.Comp.ret (I := I) e).eval ρ = pure (e.eval ρ) := rfl

private theorem eval_ite' {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T' : OracleSpec ι} {I : ReductionDsl.Iface S T'}
    {Γ' : List (ReductionDsl.Ty S)} {τ : ReductionDsl.Ty S}
    (b : ReductionDsl.Expr O Γ' .bool) (c1 c2 : ReductionDsl.Comp O I Γ' τ)
    (ρ : ReductionDsl.Env Γ') :
    (ReductionDsl.Comp.ite b c1 c2).eval ρ = if b.eval ρ then c1.eval ρ else c2.eval ρ := rfl

private theorem eval_caseOpt' {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T' : OracleSpec ι} {I : ReductionDsl.Iface S T'}
    {Γ' : List (ReductionDsl.Ty S)} {α τ : ReductionDsl.Ty S}
    (o : ReductionDsl.Expr O Γ' (.opt α)) (c1 : ReductionDsl.Comp O I Γ' τ)
    (c2 : ReductionDsl.Comp O I (α :: Γ') τ) (ρ : ReductionDsl.Env Γ') :
    (ReductionDsl.Comp.caseOpt o c1 c2).eval ρ =
      match o.eval ρ with | none => c1.eval ρ | some a => c2.eval (.cons a ρ) := rfl

private theorem eval_caseSum' {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T' : OracleSpec ι} {I : ReductionDsl.Iface S T'}
    {Γ' : List (ReductionDsl.Ty S)} {α β τ : ReductionDsl.Ty S}
    (s : ReductionDsl.Expr O Γ' (.sum α β)) (c1 : ReductionDsl.Comp O I (α :: Γ') τ)
    (c2 : ReductionDsl.Comp O I (β :: Γ') τ) (ρ : ReductionDsl.Env Γ') :
    (ReductionDsl.Comp.caseSum s c1 c2).eval ρ =
      match s.eval ρ with | .inl a => c1.eval (.cons a ρ) | .inr b => c2.eval (.cons b ρ) := rfl

private theorem eval_caseSum_inl {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T' : OracleSpec ι} {I : ReductionDsl.Iface S T'}
    {Γ' : List (ReductionDsl.Ty S)} {α β τ : ReductionDsl.Ty S}
    (s : ReductionDsl.Expr O Γ' (.sum α β)) (c1 : ReductionDsl.Comp O I (α :: Γ') τ)
    (c2 : ReductionDsl.Comp O I (β :: Γ') τ) (ρ : ReductionDsl.Env Γ') (a : α.denote)
    (h : s.eval ρ = .inl a) :
    (ReductionDsl.Comp.caseSum s c1 c2).eval ρ = c1.eval (.cons a ρ) := by
  simp [ReductionDsl.Comp.eval, h]

private theorem eval_caseSum_inr {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T' : OracleSpec ι} {I : ReductionDsl.Iface S T'}
    {Γ' : List (ReductionDsl.Ty S)} {α β τ : ReductionDsl.Ty S}
    (s : ReductionDsl.Expr O Γ' (.sum α β)) (c1 : ReductionDsl.Comp O I (α :: Γ') τ)
    (c2 : ReductionDsl.Comp O I (β :: Γ') τ) (ρ : ReductionDsl.Env Γ') (b : β.denote)
    (h : s.eval ρ = .inr b) :
    (ReductionDsl.Comp.caseSum s c1 c2).eval ρ = c2.eval (.cons b ρ) := by
  simp [ReductionDsl.Comp.eval, h]

local macro "step_sum" : tactic =>
  `(tactic| repeat first
    | rw [eval_caseSum_inl _ _ _ _ _ rfl]
    | rw [eval_caseSum_inr _ _ _ _ _ rfl])

local macro "step_eval" : tactic =>
  `(tactic| repeat first
    | rw [eval_caseSum']
    | rw [eval_caseOpt']
    | rw [eval_ite']
    | rw [eval_ret'])

private theorem eval_query_isQueryBoundP_zero {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T' : OracleSpec.{0, 0} ι} {I : ReductionDsl.Iface S T'}
    {Γ' : List (ReductionDsl.Ty S)} (g : I.Tag) (e : ReductionDsl.Expr O Γ' (I.dom g))
    (ρ : ReductionDsl.Env Γ') (P : ι → Prop) [DecidablePred P]
    (h : ¬ P (I.enc g (e.eval ρ))) :
    ((ReductionDsl.Comp.query (I := I) g e).eval ρ).IsQueryBoundP P 0 := by
  dsimp only [ReductionDsl.Comp.eval]
  rw [map_eq_bind_pure_comp, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl h, fun _ => by simp⟩

private theorem eval_query_guardedSafePost {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T' : OracleSpec.{0, 0} ι} {I : ReductionDsl.Iface S T'}
    {Γ' : List (ReductionDsl.Ty S)} {g : I.Tag} {e : ReductionDsl.Expr O Γ' (I.dom g)}
    {ρ : ReductionDsl.Env Γ'}
    {RespOk : (q : ι) → T'.Range q → Prop} {Q : ι → Prop}
    {P : (I.cod g).denote → Prop}
    (hQ : ¬ Q (I.enc g (e.eval ρ)))
    (hP : ∀ u, RespOk (I.enc g (e.eval ρ)) u → P (I.dec g (e.eval ρ) u)) :
    CryptoGames.GuardedSafe.GuardedSafePost RespOk Q P
      ((ReductionDsl.Comp.query (I := I) g e).eval ρ) := by
  dsimp only [ReductionDsl.Comp.eval]
  exact (CryptoGames.GuardedSafe.GuardedSafePost.query (RespOk := RespOk) (Q := Q) hQ).map _ hP

theorem isQueryBoundP_of_imp {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {oa : OracleComp spec α} {p q : ι → Prop} [DecidablePred p] [DecidablePred q] {k : ℕ}
    (hqp : ∀ x, q x → p x) (h : IsQueryBoundP oa p k) : IsQueryBoundP oa q k := by
  induction oa using OracleComp.inductionOn generalizing k with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    by_cases hqt : q t
    · have hpt : p t := hqp t hqt
      have hk : 0 < k := h.1.resolve_left (not_not.mpr hpt)
      refine ⟨Or.inr hk, fun u => ?_⟩
      simp only [hqt, ↓reduceIte]
      exact ih u (by simpa [hpt] using h.2 u)
    · refine ⟨Or.inl hqt, fun u => ?_⟩
      simp only [hqt, ↓reduceIte]
      by_cases hpt : p t
      · have hu : IsQueryBoundP (mx u) p (k - 1) := by simpa [hpt] using h.2 u
        exact (ih u hu).mono (Nat.sub_le k 1)
      · have hu : IsQueryBoundP (mx u) p k := by simpa [hpt] using h.2 u
        exact ih u hu

private theorem isQueryBoundP_bind_zero {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {P : ι → Prop} [DecidablePred P]
    (h1 : oa.IsQueryBoundP P 0) (h2 : ∀ x ∈ support oa, (ob x).IsQueryBoundP P 0) :
    (oa >>= ob).IsQueryBoundP P 0 := by
  simpa using isQueryBoundP_bind h1 h2

theorem encMsgsOk_shortB_of_atomicShortPubB {SS RS AD Ct : Type} {ℓ : ℕ}
    {R : CryptoGames.FSAEAD.Adversary SS RS AD (LibsignalMsgPublicPart × Plain ℓ) Ct}
    (h : CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) R) :
    CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) R := by
  refine isQueryBoundP_of_imp (fun t ht => ?_) h
  rcases t with _ | (((((⟨_, m⟩ | ⟨_, m₀, m₁⟩) | _) | _) | _) | _)
  · cases ht
  · simp only [CryptoGames.FSAEAD.encBadMsg, Bool.not_eq_true'] at ht ⊢
    cases hat : atomicShortPubB m.1
    · rfl
    · rw [atomicShortPubB_imp_shortB hat] at ht; cases ht
  · simp only [CryptoGames.FSAEAD.encBadMsg, Bool.or_eq_true, Bool.not_eq_true'] at ht ⊢
    rcases ht with ht₀ | ht₁
    · left
      cases hat : atomicShortPubB m₀.1
      · rfl
      · rw [atomicShortPubB_imp_shortB hat] at ht₀; cases ht₀
    · right
      cases hat : atomicShortPubB m₁.1
      · rfl
      · rw [atomicShortPubB_imp_shortB hat] at ht₁; cases ht₁
  all_goals cases ht

section GenericBadTrOrCh

variable
  {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

private def wTrCh : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ
  | .tr => 1
  | .ch => 1
  | _ => 0

@[local simp] private theorem wTrCh_cs : wTrCh .cs = 0 := rfl
@[local simp] private theorem wTrCh_dl : wTrCh .dl = 0 := rfl
@[local simp] private theorem wTrCh_ij : wTrCh .ij = 0 := rfl
@[local simp] private theorem wTrCh_cr : wTrCh .cr = 0 := rfl

private theorem comp_safePost_badTrOrCh (ok : M → Bool)
    {Γ' : List (ReductionDsl.Ty (CryptoGames.PRFPRNG.prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    {τ : ReductionDsl.Ty (CryptoGames.PRFPRNG.prngSig KC Γ CCoins T I KR RSt K SS RS M E)}
    (c : ReductionDsl.Comp
      (CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsaeadMultiBucketIface
        (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (KR := KR) (RSt := RSt)
        (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
        sampKR sampKC sampCCoins sampI sampK) Γ' τ)
    (ρ : ReductionDsl.Env Γ')
    (hq : c.queries wTrCh (fun _ => 0) = 0) :
    CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost
      (fun t => badTrOrCh (SS := SS) (RS := RS) (T := T) (E := E) ok t = true)
      (fun _ => True) (c.eval ρ) := by
  apply CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.of_isQueryBoundP
  have h := ReductionDsl.Comp.queryBound_eval
    (fun t => badTrOrCh (SS := SS) (RS := RS) (T := T) (E := E) ok t = true)
    wTrCh (fun _ => 0)
    (fun g x hg => by cases g <;> simp_all [badTrOrCh, wTrCh])
    (fun n => by
      change OracleComp.IsQueryBoundP
        (liftM (OracleSpec.query
          (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ =>
            CryptoGames.FSAEAD.spec SS RS (Header T) M E)) (.inl n))) _ 0
      rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [badTrOrCh]), fun _ => by simp⟩)
    c ρ
  rwa [hq] at h

private theorem fsMultiBucketAuthFsSendC_safePost_badTrOrCh
    (ok : M → Bool) (Δcka : ℕ) (la : Bool)
    {Γ' : List (ReductionDsl.Ty (CryptoGames.PRFPRNG.prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    (hE : ReductionDsl.Expr
      (CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketHsTy
        KC Γ CCoins T I KR RSt K SS RS M E))
    (ctxE : ReductionDsl.Expr _ Γ'
      (_root_.CryptoGames.SM.Engine.cGsTy
        (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketVpTy
          KC Γ CCoins T I KR RSt K SS RS M E)))
    (pE : ReductionDsl.Expr _ Γ' .bool)
    (tE : ReductionDsl.Expr _ Γ' .nat)
    (ssvE : ReductionDsl.Expr _ Γ' (.sum (.base .ss) .nat))
    (hdrE : ReductionDsl.Expr _ Γ' (CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (mE : ReductionDsl.Expr _ Γ' (.base .msg))
    (pairE : ReductionDsl.Expr _ Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (ρ : ReductionDsl.Env Γ')
    (hm : ok (mE.eval ρ) = true)
    (hpair : pairE.eval ρ = none) :
    CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost
      (fun t => badTrOrCh (SS := SS) (RS := RS) (T := T) (E := E) ok t = true)
      (fun _ => True)
      ((Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsSendC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        Δcka la hE ctxE pE tE ssvE hdrE mE pairE).eval ρ) := by
  unfold Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsSendC
  rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
  step_eval
  split
  · exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial
  · next sIdx _ =>
    rw [_root_.CryptoGames.SM.Engine.eval_bind]
    refine CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.bind
      (comp_safePost_badTrOrCh ok _ _ (by simp [ReductionDsl.Comp.queries])) (fun oh _ => ?_)
    step_eval
    split_ifs
    · exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial
    · rw [_root_.CryptoGames.SM.Engine.eval_bind]
      refine CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.bind (P := fun _ => True) ?_
        (fun _ _ => comp_safePost_badTrOrCh ok _ _ (by simp [ReductionDsl.Comp.queries]))
      rw [eval_caseOpt']
      split
      · refine CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.of_isQueryBoundP
          (eval_query_isQueryBoundP_zero _ _ _ _ ?_)
        simp [CryptoGames.PRFPRNG.fsaeadHeaderAdIface, badTrOrCh, ReductionDsl.Expr.eval,
          ReductionDsl.Expr.v1, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_zero,
          ReductionDsl.Env.get_cons_succ, hm]
      · next _ hpOpt =>
        simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, hpair] at hpOpt

theorem redFSAuthMultiBucketProg_badTrOrCh
    [Inhabited T] (ok : M → Bool)
    (L B Δcka qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec
      (_root_.CryptoGames.SM.Construction.PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk ok A) :
    ((redFSAuthMultiBucketProg
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip gMain la tL par).eval (fun _ => A) ()).IsQueryBoundP
      (fun t => badTrOrCh (SS := SS) (RS := RS) (T := T) (E := E) ok t = true) 0 := by
  let R := redFSAuthMultiBucketProg
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    L B Δcka qep maxSkip gMain la tL par
  have hLk : ∀ {Γ'} hE tE ikE,
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.lookupMultiBucketFC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := Γ') L hE tE ikE).queries
        wTrCh (fun _ => 0) = 0 := by
    intros; simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.lookupMultiBucketFC,
      ReductionDsl.Comp.queries]
  have hRt : ∀ {Γ'} hE tE plE ikE σE,
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.rootFSMultiBucketAuthC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := Γ') L Δcka qep tL par hE tE plE ikE σE).queries
        wTrCh (fun _ => 0) = 0 := by
    intros; simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.rootFSMultiBucketAuthC,
      hLk, ReductionDsl.Comp.queries]
  have hSS : ∀ {Γ'} hE ctxE pE tE γE σE rE,
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartSendC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := Γ') L Δcka qep gMain tL par hE ctxE pE tE γE σE
        rE).queries wTrCh (fun _ => 0) = 0 := by
    intros; cases gMain <;>
      simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartSendC,
        hRt, ReductionDsl.Comp.queries]
  have hSR : ∀ {Γ'} hE ctxE pE tE γE σE tnE,
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartRecvC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := Γ') L Δcka qep gMain tL par hE ctxE pE tE γE σE
        tnE).queries wTrCh (fun _ => 0) = 0 := by
    intros; cases gMain <;>
      simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartRecvC,
        hLk, ReductionDsl.Comp.queries]
  apply CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
    (P := fun _ => True)
  unfold ReductionDsl.CostedReduction.eval ReductionDsl.CostedReduction.impl
  refine (comp_safePost_badTrOrCh ok R.init (.cons () .nil) ?_).bind (fun s0 _ => ?_)
  · cases gMain <;>
      simp [R, redFSAuthMultiBucketProg,
        Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.initFSMultiBucketAuthEStateC,
        hRt, ReductionDsl.Comp.queries]
  · have hSim :
        CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost
          (fun t => badTrOrCh (SS := SS) (RS := RS) (T := T) (E := E) ok t = true)
          (fun _ => True)
          ((simulateQ (ReductionDsl.handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
              R.handle) A).run s0.2) := by
      refine CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.simulateQ_run
        (I := fun _ => True)
        (CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.of_isQueryBoundP hsh)
        (fun t hpt st _ => ?_) trivial
      rcases t with u | gq
      · change CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost _ _
          (do let x ← liftM (OracleSpec.query
                (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ =>
                  CryptoGames.FSAEAD.spec SS RS (Header T) M E)) (.inl u))
              return (x, st))
        exact (CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.query
          (by simp [badTrOrCh])).bind (fun _ _ =>
          CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial)
      · change CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost _ _
          (do let p ← R.handle.eval
                (.cons st (.cons ((prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc gq) .nil))
              return ((prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec gq p.1, p.2))
        refine CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.bind (P := fun _ => True) ?_
          (fun _ _ => CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial)
        rcases gq with ((((⟨P, m, r⟩ | q) | q) | q) | P)
        · have hm : ok m = true := by
            simpa [CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.badSendMsg] using hpt
          dsimp only [R, redFSAuthMultiBucketProg, prngSMCodec, CryptoGames.CKA.ckaSMCodec]
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_sum
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_eval
          split_ifs
          · exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial
          · split
            · exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial
            · next s1 _ =>
              rw [_root_.CryptoGames.SM.Engine.eval_bind]
              refine CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.bind
                (P := fun _ => True) ?_ (fun _ _ =>
                  comp_safePost_badTrOrCh ok _ _ (by simp [ReductionDsl.Comp.queries]))
              unfold _root_.CryptoGames.SM.Engine.vSendC
              rw [_root_.CryptoGames.SM.Engine.eval_bind_ret,
                _root_.CryptoGames.SM.Engine.eval_bind]
              refine CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.bind
                (comp_safePost_badTrOrCh ok _ _
                  (by simp [_root_.CryptoGames.SM.Engine.vSendStep1C,
                    Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC,
                    hSS, ReductionDsl.Comp.queries]))
                (fun step1Out _ => ?_)
              step_eval
              split
              · exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial
              · step_eval
                split
                · exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial
                · dsimp only [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC]
                  rw [_root_.CryptoGames.SM.Engine.eval_bind]
                  refine CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.bind
                    (fsMultiBucketAuthFsSendC_safePost_badTrOrCh ok Δcka la _ _ _
                      (_root_.CryptoGames.SM.Engine.vpTcurNat .v1) _ _ _ _ _ ?_ rfl)
                    (fun _ _ => comp_safePost_badTrOrCh ok _ _
                      (by simp [ReductionDsl.Comp.queries]))
                  simpa [ReductionDsl.Expr.eval, ReductionDsl.Expr.v3, ReductionDsl.Expr.v0,
                    ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero,
                    ReductionDsl.Env.get_cons_succ] using hm
        · dsimp only [R, redFSAuthMultiBucketProg, prngSMCodec, CryptoGames.CKA.ckaSMCodec]
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_sum
          rw [eval_ret']
          exact CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.pure trivial
        · dsimp only [R, redFSAuthMultiBucketProg, prngSMCodec, CryptoGames.CKA.ckaSMCodec]
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_sum
          exact comp_safePost_badTrOrCh ok _ _
            (by simp [_root_.CryptoGames.SM.Engine.deliverEC,
              _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
              _root_.CryptoGames.SM.Engine.commitEC,
              Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC,
              Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsRecvC,
              Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthCommitC,
              hSR, ReductionDsl.Comp.queries])
        · dsimp only [R, redFSAuthMultiBucketProg, prngSMCodec, CryptoGames.CKA.ckaSMCodec]
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_sum
          exact comp_safePost_badTrOrCh ok _ _
            (by simp [_root_.CryptoGames.SM.Engine.injectEC,
              _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
              _root_.CryptoGames.SM.Engine.commitEC,
              Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC,
              Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsRecvC,
              Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthCommitC,
              hSR, ReductionDsl.Comp.queries])
        · dsimp only [R, redFSAuthMultiBucketProg, prngSMCodec, CryptoGames.CKA.ckaSMCodec]
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_sum
          exact comp_safePost_badTrOrCh ok _ _
            (by simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthRevealC,
              Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.rangeListBucketC,
              ReductionDsl.Comp.queries])
    exact hSim.bind (fun pOut _ => comp_safePost_badTrOrCh ok R.finish (.cons pOut.2 (.cons pOut.1 .nil))
      (by simp [R, redFSAuthMultiBucketProg, ReductionDsl.Comp.queries]))

end GenericBadTrOrCh

theorem fsAtomicB_send_short {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (B : ℕ) (hℓ : ℓ < 10 ^ 6)
    (v : RatchetSenderState (BitVec 256)) (a : Header Pt)
    (m : LibsignalMsgPublicPart × Plain ℓ) :
    ((Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB C ℓ encT idOf B).send
        v a m).2.2.1.1.length + 8 < 2 ^ 32 := by
  dsimp only [Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB,
    Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomic,
    CryptoGames.FSAEAD.fromAEADPRG, CryptoGames.AEADScheme.movePubPartToAD,
    Computational.Proofs.ReductionDsl.Fig8Atomic.aeadAtomic,
    Computational.Proofs.ReductionDsl.Fig8Atomic.aeadAtomicEnc]
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_right
      ((List.length_take_le _ _).trans ((Nat.sub_le _ _).trans (List.length_take_le _ _))) 8)
    (by omega)

private def wIj : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ
  | .ij => 1
  | _ => 0

@[local simp] private theorem wIj_cs : wIj .cs = 0 := rfl
@[local simp] private theorem wIj_tr : wIj .tr = 0 := rfl
@[local simp] private theorem wIj_ch : wIj .ch = 0 := rfl
@[local simp] private theorem wIj_dl : wIj .dl = 0 := rfl
@[local simp] private theorem wIj_cr : wIj .cr = 0 := rfl

/-- Overlong `.ij` ciphertext predicate on the multi-session FS-AEAD oracle domain. -/
@[expose] def multiInjectLongB {CK MK T M : Type} :
    (unifSpec + OracleSpec.sigma (fun _ : ℕ =>
      CryptoGames.FSAEAD.spec (RatchetSenderState CK) (RatchetReceiverState CK MK)
        (Header T) M (ℕ × LibsignalCiphertextWithSalt32))).Domain → Bool
  | .inr ⟨_, .inr ⟨_, e⟩⟩ => !decide (e.2.1.1.length < 2 ^ 32)
  | _ => false

section GenericGuardedShort

variable
  {KC Γ CCoins T I KR RSt K CK MK M : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → RatchetSenderState CK} {fsInitReceiver : K → RatchetReceiverState CK MK}
  {fsSend : RatchetSenderState CK → Header T → M →
    RatchetSenderState CK × (ℕ × LibsignalCiphertextWithSalt32)}
  {fsReceive : RatchetReceiverState CK MK → Header T → (ℕ × LibsignalCiphertextWithSalt32) →
    Option (RatchetReceiverState CK MK × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool}
  {eqE : (ℕ × LibsignalCiphertextWithSalt32) → (ℕ × LibsignalCiphertextWithSalt32) → Bool}
  {lam : I} {defaultE : ℕ × LibsignalCiphertextWithSalt32}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

private theorem guardedSafePost_of_isQueryBoundP_multiInjectLongB {α : Type}
    {oa : OracleComp
      (unifSpec + OracleSpec.sigma (fun _ : ℕ =>
        CryptoGames.FSAEAD.spec (RatchetSenderState CK) (RatchetReceiverState CK MK)
          (Header T) M (ℕ × LibsignalCiphertextWithSalt32))) α}
    (h : oa.IsQueryBoundP (fun t => multiInjectLongB (CK := CK) (MK := MK) (T := T) (M := M) t = true) 0) :
    CryptoGames.GuardedSafe.GuardedSafePost
      (CryptoVerification.E2E.Signed.SessionWireQueries.multiRespShort
        (CK := CK) (MK := MK) (AD := Header T) (Msg := M))
      (CryptoVerification.E2E.Signed.SessionWireQueries.multiInjectLong
        (CK := CK) (MK := MK) (AD := Header T) (Msg := M))
      (fun _ => True) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => exact CryptoGames.GuardedSafe.GuardedSafePost.pure trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have hnb : ¬ multiInjectLongB (CK := CK) (MK := MK) (T := T) (M := M) t = true :=
      h.1.resolve_right (Nat.not_lt_zero 0)
    have hnl : ¬ CryptoVerification.E2E.Signed.SessionWireQueries.multiInjectLong
        (CK := CK) (MK := MK) (AD := Header T) (Msg := M) t := by
      rcases t with _ | ⟨s, ((((_ | _) | _) | _) | _) | ⟨_, _, e⟩⟩ <;>
        simp_all [multiInjectLongB,
          CryptoVerification.E2E.Signed.SessionWireQueries.multiInjectLong,
          CryptoGames.Ratchet.LibsignalInst.fsInjectLong]
    exact CryptoGames.GuardedSafe.GuardedSafePost.query_bind hnl (fun u _ =>
      ih u (by simpa [hnb] using h.2 u))

private theorem comp_noIj_isQueryBoundP
    {Γ' : List (ReductionDsl.Ty (CryptoGames.PRFPRNG.prngSig KC Γ CCoins T I KR RSt K
      (RatchetSenderState CK) (RatchetReceiverState CK MK) M (ℕ × LibsignalCiphertextWithSalt32)))}
    {τ : ReductionDsl.Ty (CryptoGames.PRFPRNG.prngSig KC Γ CCoins T I KR RSt K
      (RatchetSenderState CK) (RatchetReceiverState CK MK) M (ℕ × LibsignalCiphertextWithSalt32))}
    (c : ReductionDsl.Comp
      (CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsaeadMultiBucketIface
        (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (KR := KR) (RSt := RSt)
        (K := K) (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (M := M) (E := ℕ × LibsignalCiphertextWithSalt32)
        sampKR sampKC sampCCoins sampI sampK) Γ' τ)
    (ρ : ReductionDsl.Env Γ')
    (hq : c.queries wIj (fun _ => 0) = 0) :
    (c.eval ρ).IsQueryBoundP
      (fun t => multiInjectLongB (CK := CK) (MK := MK) (T := T) (M := M) t = true) 0 := by
  have h := ReductionDsl.Comp.queryBound_eval
    (fun t => multiInjectLongB (CK := CK) (MK := MK) (T := T) (M := M) t = true)
    wIj (fun _ => 0)
    (fun g x hg => by cases g <;> simp_all [multiInjectLongB, wIj])
    (fun n => by
      change OracleComp.IsQueryBoundP
        (liftM (OracleSpec.query
          (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ =>
            CryptoGames.FSAEAD.spec (RatchetSenderState CK) (RatchetReceiverState CK MK)
              (Header T) M (ℕ × LibsignalCiphertextWithSalt32))) (.inl n))) _ 0
      rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [multiInjectLongB]), fun _ => by simp⟩)
    c ρ
  rwa [hq] at h

private theorem fsMultiBucketAuthFsSendC_guardedSafePost
    (hFsSendShort : ∀ ss hdr m, (fsSend ss hdr m).2.2.1.1.length + 8 < 2 ^ 32)
    (Δcka : ℕ) (la : Bool)
    {Γ' : List (ReductionDsl.Ty (CryptoGames.PRFPRNG.prngSig KC Γ CCoins T I KR RSt K
      (RatchetSenderState CK) (RatchetReceiverState CK MK) M (ℕ × LibsignalCiphertextWithSalt32)))}
    (hE : ReductionDsl.Expr
      (CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketHsTy
        KC Γ CCoins T I KR RSt K (RatchetSenderState CK) (RatchetReceiverState CK MK) M
        (ℕ × LibsignalCiphertextWithSalt32)))
    (ctxE : ReductionDsl.Expr _ Γ'
      (_root_.CryptoGames.SM.Engine.cGsTy
        (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketVpTy
          KC Γ CCoins T I KR RSt K (RatchetSenderState CK) (RatchetReceiverState CK MK) M
          (ℕ × LibsignalCiphertextWithSalt32))))
    (pE : ReductionDsl.Expr _ Γ' .bool)
    (tE : ReductionDsl.Expr _ Γ' .nat)
    (ssvE : ReductionDsl.Expr _ Γ' (.sum (.base .ss) .nat))
    (hdrE : ReductionDsl.Expr _ Γ'
      (CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K (RatchetSenderState CK)
        (RatchetReceiverState CK MK) M (ℕ × LibsignalCiphertextWithSalt32)))
    (mE : ReductionDsl.Expr _ Γ' (.base .msg))
    (pairE : ReductionDsl.Expr _ Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (ρ : ReductionDsl.Env Γ')
    (hpair : pairE.eval ρ = none) :
    CryptoGames.GuardedSafe.GuardedSafePost
      (CryptoVerification.E2E.Signed.SessionWireQueries.multiRespShort
        (CK := CK) (MK := MK) (AD := Header T) (Msg := M))
      (CryptoVerification.E2E.Signed.SessionWireQueries.multiInjectLong
        (CK := CK) (MK := MK) (AD := Header T) (Msg := M))
      (fun res => ∀ v' ct, res.1 = some (v', ct) → ct.2.1.1.length + 8 < 2 ^ 32)
      ((Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsSendC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        Δcka la hE ctxE pE tE ssvE hdrE mE pairE).eval ρ) := by
  unfold Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsSendC
  rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
  step_eval
  split
  · refine CryptoGames.GuardedSafe.GuardedSafePost.pure ?_
    rintro _ _ hEq
    simp only [ReductionDsl.Expr.eval, Option.some.injEq, Prod.mk.injEq] at hEq
    rcases hEq with ⟨_, rfl⟩
    exact hFsSendShort _ _ _
  · next sIdx _ =>
    rw [_root_.CryptoGames.SM.Engine.eval_bind]
    refine CryptoGames.GuardedSafe.GuardedSafePost.bind
      (guardedSafePost_of_isQueryBoundP_multiInjectLongB
        (comp_noIj_isQueryBoundP _ _ (by simp [ReductionDsl.Comp.queries])))
      (fun oh _ => ?_)
    step_eval
    split_ifs
    · exact CryptoGames.GuardedSafe.GuardedSafePost.pure (by
        rintro _ _ hEq; simp [ReductionDsl.Expr.eval] at hEq)
    · rw [_root_.CryptoGames.SM.Engine.eval_bind]
      refine CryptoGames.GuardedSafe.GuardedSafePost.bind
        (P := fun ctOpt => ∀ ct, ctOpt = some ct → ct.2.1.1.length + 8 < 2 ^ 32)
        ?_ (fun ctOpt hct => ?_)
      · let _ := hpair
        rw [eval_caseOpt']
        split
        · refine eval_query_guardedSafePost
            (I := Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsaeadMultiBucketIface
              sampKR sampKC sampCCoins sampI sampK)
            (g := .tr) ?_ ?_
          · nofun
          · exact fun _ hu ct hEq => hu ct hEq
        · refine eval_query_guardedSafePost
            (I := Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsaeadMultiBucketIface
              sampKR sampKC sampCCoins sampI sampK)
            (g := .ch) ?_ ?_
          · nofun
          · exact fun _ hu ct hEq => hu ct hEq
      · step_eval
        split
        · exact CryptoGames.GuardedSafe.GuardedSafePost.pure (by
            rintro _ _ hEq; simp [ReductionDsl.Expr.eval] at hEq)
        · next ct hOpt =>
          refine CryptoGames.GuardedSafe.GuardedSafePost.pure ?_
          rintro _ _ hEq
          simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero,
            Option.some.injEq, Prod.mk.injEq] at hEq hOpt
          rcases hEq with ⟨_, rfl⟩
          exact hct ct hOpt

private theorem fsMultiBucketAuthFsRecvC_noIj_of_short
    (L B : ℕ) (la : Bool) (Δcka : ℕ)
    {Γ' : List (ReductionDsl.Ty (CryptoGames.PRFPRNG.prngSig KC Γ CCoins T I KR RSt K
      (RatchetSenderState CK) (RatchetReceiverState CK MK) M (ℕ × LibsignalCiphertextWithSalt32)))}
    (hE : ReductionDsl.Expr
      (CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketHsTy
        KC Γ CCoins T I KR RSt K (RatchetSenderState CK) (RatchetReceiverState CK MK) M
        (ℕ × LibsignalCiphertextWithSalt32)))
    (ctxE : ReductionDsl.Expr _ Γ'
      (_root_.CryptoGames.SM.Engine.cGsTy
        (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketVpTy
          KC Γ CCoins T I KR RSt K (RatchetSenderState CK) (RatchetReceiverState CK MK) M
          (ℕ × LibsignalCiphertextWithSalt32))))
    (pE : ReductionDsl.Expr _ Γ' .bool)
    (tE : ReductionDsl.Expr _ Γ' .nat)
    (rsvE : ReductionDsl.Expr _ Γ' (.sum (.base .rs) .nat))
    (hdrE : ReductionDsl.Expr _ Γ'
      (CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K (RatchetSenderState CK)
        (RatchetReceiverState CK MK) M (ℕ × LibsignalCiphertextWithSalt32)))
    (eE : ReductionDsl.Expr _ Γ' (.base .ct))
    (recE : ReductionDsl.Expr _ Γ'
      (.opt (_root_.CryptoGames.SM.Engine.cRecTy (KC := KC) (Γ := Γ) (CCoins := CCoins)
        (T := T) (I := I) (KR := KR) (RSt := RSt) (K := K) (SS := RatchetSenderState CK)
        (RS := RatchetReceiverState CK MK) (M := M) (E := ℕ × LibsignalCiphertextWithSalt32))))
    (ρ : ReductionDsl.Env Γ')
    (he : (eE.eval ρ).2.1.1.length < 2 ^ 32) :
    ((Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsRecvC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B la Δcka hE ctxE pE tE rsvE hdrE eE recE).eval ρ).IsQueryBoundP
      (fun t => multiInjectLongB (CK := CK) (MK := MK) (T := T) (M := M) t = true) 0 := by
  dsimp only [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsRecvC,
    Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.fsMultiBucketAuthFsRecvC]
  rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
  step_eval
  split
  · exact comp_noIj_isQueryBoundP _ _ (by simp [ReductionDsl.Comp.queries])
  · rw [_root_.CryptoGames.SM.Engine.eval_bind]
    refine isQueryBoundP_bind_zero
      (comp_noIj_isQueryBoundP _ _ (by simp [ReductionDsl.Comp.queries]))
      (fun _ _ => ?_)
    rw [eval_ite']
    split_ifs
    · exact comp_noIj_isQueryBoundP _ _ (by simp [ReductionDsl.Comp.queries])
    · rw [_root_.CryptoGames.SM.Engine.eval_bind]
      refine isQueryBoundP_bind_zero ?_ (fun _ _ =>
        comp_noIj_isQueryBoundP _ _ (by simp [ReductionDsl.Comp.queries]))
      rw [eval_caseOpt']
      split
      · refine eval_query_isQueryBoundP_zero _ _ _ _ ?_
        simpa [CryptoGames.PRFPRNG.fsaeadHeaderAdIface, multiInjectLongB,
          ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Expr.v1,
          ReductionDsl.Expr.v0] using he
      · refine eval_query_isQueryBoundP_zero _ _ _ _ ?_
        simp [multiInjectLongB]

private theorem vRecvC_noIj_of_short
    (L B Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    {Γ' : List (ReductionDsl.Ty (CryptoGames.PRFPRNG.prngSig KC Γ CCoins T I KR RSt K
      (RatchetSenderState CK) (RatchetReceiverState CK MK) M (ℕ × LibsignalCiphertextWithSalt32)))}
    (hE : ReductionDsl.Expr
      (CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketHsTy
        KC Γ CCoins T I KR RSt K (RatchetSenderState CK) (RatchetReceiverState CK MK) M
        (ℕ × LibsignalCiphertextWithSalt32)))
    (ctxE : ReductionDsl.Expr _ Γ'
      (_root_.CryptoGames.SM.Engine.cGsTy
        (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketVpTy
          KC Γ CCoins T I KR RSt K (RatchetSenderState CK) (RatchetReceiverState CK MK) M
          (ℕ × LibsignalCiphertextWithSalt32))))
    (pE : ReductionDsl.Expr _ Γ' .bool)
    (sE : ReductionDsl.Expr _ Γ'
      (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketVpTy
        KC Γ CCoins T I KR RSt K (RatchetSenderState CK) (RatchetReceiverState CK MK) M
        (ℕ × LibsignalCiphertextWithSalt32)))
    (cE : ReductionDsl.Expr _ Γ'
      (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K (RatchetSenderState CK)
        (RatchetReceiverState CK MK) M (ℕ × LibsignalCiphertextWithSalt32)))
    (recE : ReductionDsl.Expr _ Γ'
      (.opt (_root_.CryptoGames.SM.Engine.cRecTy (KC := KC) (Γ := Γ) (CCoins := CCoins)
        (T := T) (I := I) (KR := KR) (RSt := RSt) (K := K) (SS := RatchetSenderState CK)
        (RS := RatchetReceiverState CK MK) (M := M) (E := ℕ × LibsignalCiphertextWithSalt32))))
    (ρ : ReductionDsl.Env Γ')
    (he : (cE.eval ρ).2.2.1.1.length < 2 ^ 32) :
    ((_root_.CryptoGames.SM.Engine.vRecvC
        (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC
          (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep gMain tL par la) hE ctxE pE sE cE recE).eval ρ).IsQueryBoundP
      (fun t => multiInjectLongB (CK := CK) (MK := MK) (T := T) (M := M) t = true) 0 := by
  have hLk : ∀ {Γ''} hE' tE' ikE',
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.lookupMultiBucketFC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := Γ'') L hE' tE' ikE').queries
        wIj (fun _ => 0) = 0 := by
    intros; simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.lookupMultiBucketFC,
      ReductionDsl.Comp.queries]
  have hSR : ∀ {Γ''} hE' ctxE' pE' tE' γE' σE' tnE',
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartRecvC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := Γ'') L Δcka qep gMain tL par hE' ctxE' pE' tE'
        γE' σE' tnE').queries wIj (fun _ => 0) = 0 := by
    intros; cases gMain <;>
      simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartRecvC,
        hLk, ReductionDsl.Comp.queries]
  unfold _root_.CryptoGames.SM.Engine.vRecvC
  rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
  step_eval
  split_ifs
  · simp [isQueryBoundP_pure]
  · rw [_root_.CryptoGames.SM.Engine.eval_bind]
    refine isQueryBoundP_bind_zero
      (comp_noIj_isQueryBoundP _ _ ?_)
      (fun _ _ => ?_)
    · simp [_root_.CryptoGames.SM.Engine.vRecvStep1C,
        Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC,
        hSR, ReductionDsl.Comp.queries]
    · step_eval
      split
      · simp [isQueryBoundP_pure]
      · step_eval
        split
        · simp [isQueryBoundP_pure]
        · step_eval
          split
          · simp [isQueryBoundP_pure]
          · dsimp only [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC]
            rw [_root_.CryptoGames.SM.Engine.eval_bind]
            refine isQueryBoundP_bind_zero
              (fsMultiBucketAuthFsRecvC_noIj_of_short L B la Δcka _
                (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
                (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v4)))))))
                _ _ _ _ _ ?_)
              (fun _ _ => comp_noIj_isQueryBoundP _ _ ?_)
            · simpa [ReductionDsl.Expr.eval, ReductionDsl.Expr.v4] using he
            · simp [ReductionDsl.Comp.queries]

set_option maxHeartbeats 400000 in
theorem redFSAuthMultiBucketProg_guardedMultiInjectShort
    [Inhabited T]
    (hFsSendShort : ∀ ss hdr m, (fsSend ss hdr m).2.2.1.1.length + 8 < 2 ^ 32)
    (hDefShort : defaultE.2.1.1.length + 8 < 2 ^ 32)
    (L B Δcka qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec
      (_root_.CryptoGames.SM.Construction.PartyState Γ T RSt
        (RatchetSenderState CK) (RatchetReceiverState CK MK))
      M CCoins (Header T × (ℕ × LibsignalCiphertextWithSalt32))) Bool)
    (hg : CryptoGames.LibsignalSM.Proofs.SessionShort.GuardedSMShort A) :
    CryptoVerification.E2E.Signed.SessionWireQueries.GuardedMultiInjectShort
      ((redFSAuthMultiBucketProg
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip gMain la tL par).eval (fun _ => A) ()) := by
  let R := redFSAuthMultiBucketProg
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    L B Δcka qep maxSkip gMain la tL par
  have hLk : ∀ {Γ'} hE tE ikE,
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.lookupMultiBucketFC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := Γ') L hE tE ikE).queries
        wIj (fun _ => 0) = 0 := by
    intros; simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.lookupMultiBucketFC,
      ReductionDsl.Comp.queries]
  have hRt : ∀ {Γ'} hE tE plE ikE σE,
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.rootFSMultiBucketAuthC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := Γ') L Δcka qep tL par hE tE plE ikE σE).queries
        wIj (fun _ => 0) = 0 := by
    intros; simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.rootFSMultiBucketAuthC,
      hLk, ReductionDsl.Comp.queries]
  have hSS : ∀ {Γ'} hE ctxE pE tE γE σE rE,
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartSendC
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := Γ') L Δcka qep gMain tL par hE ctxE pE tE γE σE
        rE).queries wIj (fun _ => 0) = 0 := by
    intros; cases gMain <;>
      simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartSendC,
        hRt, ReductionDsl.Comp.queries]
  unfold CryptoVerification.E2E.Signed.SessionWireQueries.GuardedMultiInjectShort
    ReductionDsl.CostedReduction.eval ReductionDsl.CostedReduction.impl
  refine (guardedSafePost_of_isQueryBoundP_multiInjectLongB
    (comp_noIj_isQueryBoundP R.init (.cons () .nil) ?_)).bind (fun s0 _ => ?_)
  · cases gMain <;>
      simp [R, redFSAuthMultiBucketProg,
        Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.initFSMultiBucketAuthEStateC,
        hRt, ReductionDsl.Comp.queries]
  · have hSim :
        CryptoGames.GuardedSafe.GuardedSafePost
          (CryptoVerification.E2E.Signed.SessionWireQueries.multiRespShort
            (CK := CK) (MK := MK) (AD := Header T) (Msg := M))
          (CryptoVerification.E2E.Signed.SessionWireQueries.multiInjectLong
            (CK := CK) (MK := MK) (AD := Header T) (Msg := M))
          (fun _ => True)
          ((simulateQ (ReductionDsl.handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K
              (RatchetSenderState CK) (RatchetReceiverState CK MK) M
              (ℕ × LibsignalCiphertextWithSalt32)) R.handle) A).run s0.2) := by
      refine CryptoGames.GuardedSafe.GuardedSafePost.simulateQ_run
        (I := fun _ => True) hg (fun t hpt st _ => ?_) trivial
      rcases t with u | gq
      · change CryptoGames.GuardedSafe.GuardedSafePost _ _ _
          (do let x ← liftM (OracleSpec.query
                (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ =>
                  CryptoGames.FSAEAD.spec (RatchetSenderState CK) (RatchetReceiverState CK MK)
                    (Header T) M (ℕ × LibsignalCiphertextWithSalt32))) (.inl u))
              return (x, st))
        exact (CryptoGames.GuardedSafe.GuardedSafePost.query
          (by simp [CryptoVerification.E2E.Signed.SessionWireQueries.multiInjectLong])).bind
          (fun _ _ => CryptoGames.GuardedSafe.GuardedSafePost.pure
            ⟨by simp [CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.smRespShort], trivial⟩)
      · change CryptoGames.GuardedSafe.GuardedSafePost _ _ _
          (do let p ← R.handle.eval
                (.cons st (.cons ((prngSMCodec KC Γ CCoins T I KR RSt K
                  (RatchetSenderState CK) (RatchetReceiverState CK MK) M
                  (ℕ × LibsignalCiphertextWithSalt32)).qenc gq) .nil))
              return ((prngSMCodec KC Γ CCoins T I KR RSt K
                (RatchetSenderState CK) (RatchetReceiverState CK MK) M
                (ℕ × LibsignalCiphertextWithSalt32)).rdec gq p.1, p.2))
        rcases gq with ((((⟨P, m, r⟩ | q) | ⟨P, hdr, e⟩) | ⟨P, hdr, e⟩) | P)
        · refine CryptoGames.GuardedSafe.GuardedSafePost.bind
            (P := fun p : _ × _ =>
              CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.smRespShort
                (.inr (.inl (.inl (.inl (.inl (P, m, r))))))
                ((prngSMCodec KC Γ CCoins T I KR RSt K (RatchetSenderState CK)
                  (RatchetReceiverState CK MK) M (ℕ × LibsignalCiphertextWithSalt32)).rdec
                  (.inl (.inl (.inl (.inl (P, m, r))))) p.1)) ?_
            (fun p hp => CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨hp, trivial⟩)
          dsimp only [CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.smRespShort,
            R, redFSAuthMultiBucketProg, prngSMCodec, CryptoGames.CKA.ckaSMCodec, id]
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_sum
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret, eval_ite']
          split_ifs
          · rw [eval_ret']
            exact CryptoGames.GuardedSafe.GuardedSafePost.pure (by
              intro c hc; simp [ReductionDsl.Expr.eval] at hc)
          · rw [eval_caseOpt']
            split
            · rw [eval_ret']
              exact CryptoGames.GuardedSafe.GuardedSafePost.pure (by
                intro c hc; simp [ReductionDsl.Expr.eval] at hc)
            · rw [_root_.CryptoGames.SM.Engine.eval_bind]
              refine CryptoGames.GuardedSafe.GuardedSafePost.bind
                (P := fun sendOut : _ × _ => ∀ vp' hc, sendOut.1 = some (vp', hc) →
                  hc.2.2.1.1.length + 8 < 2 ^ 32) ?_
                (fun sendOut hSend => ?_)
              · unfold _root_.CryptoGames.SM.Engine.vSendC
                rw [_root_.CryptoGames.SM.Engine.eval_bind_ret,
                  _root_.CryptoGames.SM.Engine.eval_bind]
                refine CryptoGames.GuardedSafe.GuardedSafePost.bind
                  (guardedSafePost_of_isQueryBoundP_multiInjectLongB
                    (comp_noIj_isQueryBoundP _ _
                      (by simp [_root_.CryptoGames.SM.Engine.vSendStep1C,
                        Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC,
                        hSS, ReductionDsl.Comp.queries])))
                  (fun _ _ => ?_)
                step_eval
                split
                · exact CryptoGames.GuardedSafe.GuardedSafePost.pure (by
                    intro vp' hc hEq; simp [ReductionDsl.Expr.eval] at hEq)
                · step_eval
                  split
                  · refine CryptoGames.GuardedSafe.GuardedSafePost.pure ?_
                    intro vp' hc hEq
                    simp only [ReductionDsl.Expr.eval, Option.some.injEq, Prod.mk.injEq] at hEq
                    rcases hEq with ⟨_, rfl⟩
                    exact hDefShort
                  · dsimp only [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC]
                    rw [_root_.CryptoGames.SM.Engine.eval_bind]
                    refine CryptoGames.GuardedSafe.GuardedSafePost.bind
                      (fsMultiBucketAuthFsSendC_guardedSafePost hFsSendShort Δcka la
                        _ _ _ (_root_.CryptoGames.SM.Engine.vpTcurNat .v1) _ _ _ _ _ rfl)
                      (fun _ hfs => ?_)
                    step_eval
                    split
                    · exact CryptoGames.GuardedSafe.GuardedSafePost.pure (by
                        intro vp' hc hEq; simp [ReductionDsl.Expr.eval] at hEq)
                    · next vct hOpt =>
                      refine CryptoGames.GuardedSafe.GuardedSafePost.pure ?_
                      intro vp' hc hEq
                      simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0,
                        ReductionDsl.Env.get_cons_zero, Option.some.injEq,
                        Prod.mk.injEq] at hEq hOpt
                      rcases hEq with ⟨_, rfl⟩
                      exact hfs vct.1 vct.2 hOpt
              · step_eval
                split
                · exact CryptoGames.GuardedSafe.GuardedSafePost.pure (by
                    intro c hc; simp [ReductionDsl.Expr.eval] at hc)
                · next stCt hOpt =>
                  refine CryptoGames.GuardedSafe.GuardedSafePost.pure ?_
                  intro c hc
                  simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0,
                    ReductionDsl.Env.get_cons_zero] at hc hOpt
                  cases hc
                  exact hSend stCt.1 stCt.2 hOpt
        · refine CryptoGames.GuardedSafe.GuardedSafePost.bind
            (P := fun p : _ × _ =>
              CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.smRespShort
                (.inr (.inl (.inl (.inl (.inr q)))))
                ((prngSMCodec KC Γ CCoins T I KR RSt K (RatchetSenderState CK)
                  (RatchetReceiverState CK MK) M (ℕ × LibsignalCiphertextWithSalt32)).rdec
                  (.inl (.inl (.inl (.inr q)))) p.1)) ?_
            (fun p hp => CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨hp, trivial⟩)
          dsimp only [CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.smRespShort,
            R, redFSAuthMultiBucketProg, prngSMCodec, CryptoGames.CKA.ckaSMCodec, id]
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_sum
          rw [eval_ret']
          exact CryptoGames.GuardedSafe.GuardedSafePost.pure (by intro c hc; cases hc)
        · have he : e.2.1.1.length < 2 ^ 32 :=
            Decidable.of_not_not (by
              simpa [CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.smRecvLong] using hpt)
          refine (guardedSafePost_of_isQueryBoundP_multiInjectLongB ?_).bind (fun _ _ =>
            CryptoGames.GuardedSafe.GuardedSafePost.pure
              ⟨by simp [CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.smRespShort], trivial⟩)
          dsimp only [R, redFSAuthMultiBucketProg, prngSMCodec, CryptoGames.CKA.ckaSMCodec]
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_sum
          rw [_root_.CryptoGames.SM.Engine.eval_bind]
          refine isQueryBoundP_bind_zero ?_ (fun _ _ =>
            comp_noIj_isQueryBoundP _ _ (by simp [ReductionDsl.Comp.queries]))
          unfold _root_.CryptoGames.SM.Engine.deliverEC
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret, eval_ite']
          split_ifs
          · rw [eval_ret']
            simp [isQueryBoundP_pure]
          · rw [eval_caseOpt']
            split
            · rw [eval_ret']
              simp [isQueryBoundP_pure]
            · rw [_root_.CryptoGames.SM.Engine.eval_bind]
              refine isQueryBoundP_bind_zero
                (vRecvC_noIj_of_short L B Δcka qep gMain tL par la _ _ _ _ _ _ _ ?_)
                (fun _ _ => comp_noIj_isQueryBoundP _ _ ?_)
              · simpa [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
                  ReductionDsl.Env.get] using he
              · simp [_root_.CryptoGames.SM.Engine.commitEC,
                  Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC,
                  Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthCommitC,
                  ReductionDsl.Comp.queries]
        · have he : e.2.1.1.length < 2 ^ 32 :=
            Decidable.of_not_not (by
              simpa [CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.smRecvLong] using hpt)
          refine (guardedSafePost_of_isQueryBoundP_multiInjectLongB ?_).bind (fun _ _ =>
            CryptoGames.GuardedSafe.GuardedSafePost.pure
              ⟨by simp [CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.smRespShort], trivial⟩)
          dsimp only [R, redFSAuthMultiBucketProg, prngSMCodec, CryptoGames.CKA.ckaSMCodec]
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_sum
          rw [_root_.CryptoGames.SM.Engine.eval_bind]
          refine isQueryBoundP_bind_zero ?_ (fun _ _ =>
            comp_noIj_isQueryBoundP _ _ (by simp [ReductionDsl.Comp.queries]))
          unfold _root_.CryptoGames.SM.Engine.injectEC
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret, eval_ite']
          split_ifs
          · rw [eval_ret']
            simp [isQueryBoundP_pure]
          · rw [_root_.CryptoGames.SM.Engine.eval_bind]
            refine isQueryBoundP_bind_zero
              (vRecvC_noIj_of_short L B Δcka qep gMain tL par la _ _ _ _ _ _ _ ?_)
              (fun _ _ => comp_noIj_isQueryBoundP _ _ ?_)
            · simpa [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get] using he
            · simp [_root_.CryptoGames.SM.Engine.commitEC,
                Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC,
                Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthCommitC,
                ReductionDsl.Comp.queries]
        · refine (guardedSafePost_of_isQueryBoundP_multiInjectLongB ?_).bind (fun _ _ =>
            CryptoGames.GuardedSafe.GuardedSafePost.pure
              ⟨by simp [CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.smRespShort], trivial⟩)
          dsimp only [R, redFSAuthMultiBucketProg, prngSMCodec, CryptoGames.CKA.ckaSMCodec]
          rw [_root_.CryptoGames.SM.Engine.eval_bind_ret]
          step_sum
          exact comp_noIj_isQueryBoundP _ _
            (by simp [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthRevealC,
              Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.rangeListBucketC,
              ReductionDsl.Comp.queries])
    exact hSim.bind (fun pOut _ => guardedSafePost_of_isQueryBoundP_multiInjectLongB
      (comp_noIj_isQueryBoundP R.finish (.cons pOut.2 (.cons pOut.1 .nil))
        (by simp [R, redFSAuthMultiBucketProg, ReductionDsl.Comp.queries])))

end GenericGuardedShort

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthShort
