/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks
import Computational.Proofs.ReductionDsl.Notation

/-!
# Inactive-Slot `0`-Query Bound for `redFSAuthMultiBucketProg`

Proves `redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero_gen`: every external session slot `idx`
outside `[0, ((qep + 2) - healEpoch tL) * (q + 1))` or mismatching `(gMain, par)` receives `0`
FS-AEAD oracle queries across `redFSAuthMultiBucketProg.eval`.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthCompat

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Env Expr Comp CostedReduction GameCodec handlerImpl isGameQuery)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CKA (CKAOp ckaSMQ ckaHdrTy ckaHdrCtTy)
open _root_.CryptoGames.PRFPRNG (FSHdrTag prngSig prngOps)
open _root_.CryptoGames.SM
  (MakesAtMostQueries partyEnc partyDec sendsInE senderOfE pGet pSet otherE posTy letE_eval
   pair_eval ite_eval some_eval orE_eval sendsInE_eval senderOfE_eval)
open _root_.CryptoGames.SM.Engine
  (HooksC ConfigEC cGsTy cRecTy esTy cGsSt cGsEpoch cGsMk cGsSetStP cGsSetWin esG esH esAbort esMk
   esSetG esSetH cRecPos cEpMgmtE cDeleteE cAcceptE cRecordE cAfterCorrE mkPartiesE cGsInitE vpMk
   vpId vpTcur vpTcurNat vpΓ vpRoot vpVS vpVR vpSetVS vpSetVR vSendStep1C vSendC vRecvStep1C vRecvC
   commitEC deliverEC injectEC eval_bind eval_bind_ret eval_ret)
open _root_.CryptoGames.SM.Construction (Header PartyState healEpoch fsaeadMultiHeaderAdIface)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth
  (fsMultiBucketHsTy fsMultiBucketVpTy mbHsCache mbHsSessionsTbl mbHsBook mbHsMk mbHsEmptyE
   mbHsGetBookAt mbHsSetBookAt mbHsSetCache mbHsSetTableAt mbHsSetSessionsAt mbHsSetLfWin
   sessionsMemBucketE sessionsIdxOfBucketE sessionsLenBucketE sessionsAppendOneBucketE
   validGuessBucketParAuthE lookupMultiBucketFC regSessMultiBucketE regSessOptMultiBucketE
   rootFSMultiBucketAuthC fsMultiBucketAuthStartSendC fsMultiBucketAuthStartRecvC
   fsMultiBucketAuthFsSendC fsMultiBucketAuthFsRecvC fsMultiBucketAuthCommitC rangeListBucketC
   fsMultiBucketAuthRevealC hooksFSMultiBucketAuthC initFSMultiBucketAuthEStateC
   redFSAuthMultiBucketProg)
open Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks
  (PotOKInvFS PotOKInvFS.bind' potInvFS_ret potInvFS_ite potInvFS_caseOpt potInvFS_caseSum
   pGet_eval_st_fs pSet_eval_st_fs cEpMgmtE_some_st_fs cDeleteE_st_fs cAcceptE_st_fs
   cGsSetStP_st_fs cGsSetWin_st_fs cRecordE_st_fs cAfterCorrE_st_fs ite_fst_eq_fs)

section MultiBucketInact

set_option linter.unusedSimpArgs false

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

local notation "SP" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" => prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
  fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM" => fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
  sampKR sampKC sampCCoins sampI sampK
local notation "mVpTy" => @fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => @fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "sesIdxE" => @sessionsIdxOfBucketE KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "sesLenE" => @sessionsLenBucketE KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "sesAppE" => @sessionsAppendOneBucketE KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "sesMemE" => @sessionsMemBucketE KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "regSessMBE" => @regSessMultiBucketE KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "regSessOptMBE" => @regSessOptMultiBucketE KC Γ CCoins T I KR RSt K SS RS M E
  ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "hkMBE" => hooksFSMultiBucketAuthC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)

private abbrev sessPred (j : ℕ) :
    (unifSpec + OracleSpec.sigma (fun _ : ℕ => CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Domain → Prop :=
  fun t => (match t with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true

private theorem multiIface_fwdU_zero (j n : ℕ) :
    ((IIM).fwdU n).IsQueryBoundP (sessPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E) j) 0 := by
  change OracleComp.IsQueryBoundP (liftM (OracleSpec.query
    (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ => CryptoGames.FSAEAD.spec SS RS (Header T) M E)) (.inl n)))
    (sessPred j) 0
  rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [sessPred]), fun _ => by simp⟩

private theorem potInvMultiFS_zero (j : ℕ) {Γ' : List (Ty SP)} {τ : Ty SP}
    (c : Comp OO IIM Γ' τ) (ρ : Env Γ') (hc : c.queries (fun _ => 1) (fun _ => 0) = 0) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun _ => 0) (c.eval ρ) 0 :=
  ⟨fun _k hk => (isQueryBoundP_bind
    (Comp.queryBound_eval (sessPred j) (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j) c ρ)
    (fun a _ => hk a trivial)).mono (by omega)⟩

private theorem potInvMultiFS_query (j : ℕ) (g : (IIM).Tag) {Γ' : List (Ty SP)}
    (argE : Expr OO Γ' ((IIM).dom g)) (ρ : Env Γ') (r K0 : ℕ)
    (hK : (if (argE.eval ρ).1 = j then 1 else 0) + r ≤ K0) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun _ => r) ((Comp.query (I := IIM) g argE).eval ρ) K0 := by
  refine ⟨fun k hk => ?_⟩
  have hQ : ((Comp.query (I := IIM) g argE).eval ρ).IsQueryBoundP (sessPred j)
      (if (argE.eval ρ).1 = j then 1 else 0) := by
    simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    cases g <;> by_cases h : (argE.eval ρ).1 = j <;> simp [sessPred, h]
  exact (isQueryBoundP_bind hQ (fun a _ => hk a trivial)).mono hK

private theorem simulateQ_handlerImpl_zero_step
    {S' : _root_.ReductionDsl.Sig} {O' : _root_.ReductionDsl.Ops S'}
    {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {I' : _root_.ReductionDsl.Iface S' T'}
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec S' G} {σ : Ty S'} {α : Type}
    {P : ι' → Prop} [DecidablePred P] (Inv : ℕ → σ.denote → Prop)
    (hU : ∀ n, (I'.fwdU n).IsQueryBoundP P 0) (h : Comp O' I' [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ (m : ℕ) q s, Inv (m + 1) s →
      PotOKInvFS P (fun x : (Ty.prod C.R σ).denote => Inv m x.2) (fun _ => 0)
        (h.eval (.cons s (.cons q .nil))) 0)
    {mx : OracleComp (unifSpec + G) α} {qAdv : ℕ}
    (hq : mx.IsQueryBoundP (isGameQuery (G := G)) qAdv) (st : σ.denote) (hInv : Inv qAdv st) :
    PotOKInvFS P (fun _ : α × σ.denote => True) (fun _ => 0)
      ((simulateQ (handlerImpl (C := C) h) mx).run st) 0 := by
  induction mx using OracleComp.inductionOn generalizing qAdv st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact ⟨fun k hk => by simpa using hk (a, st) trivial⟩
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq; rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with uq | gq
    · change PotOKInvFS P _ _ ((do let u ← I'.fwdU uq; return (u, st)) >>=
        fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) 0
      rw [bind_assoc]
      refine PotOKInvFS.bind' (m := 0) (r := 0) (hU uq) (fun u => ?_) (Nat.zero_le 0)
      rw [pure_bind]; exact ih u (by simpa [isGameQuery] using hq.2 u) st hInv
    · have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      change PotOKInvFS P _ _ ((do let p ← h.eval (.cons st (.cons (C.qenc gq) .nil)); return (C.rdec gq p.1, p.2)) >>=
        fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) 0
      rw [bind_assoc]
      refine PotOKInvFS.bindPot (hStep m (C.qenc gq) st hInv) (fun p hpInv => ?_)
      rw [pure_bind]; exact ih (C.rdec gq p.1) (by simpa [isGameQuery] using hq.2 (C.rdec gq p.1)) p.2 hpInv

private def ActiveSlot (L qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool) (sIdx : ℕ) : Prop :=
  sIdx < ((qep + 2) - healEpoch tL) * L ∧ decide (sIdx % L = 0) = gMain ∧
    decide (Party.senderOf (healEpoch tL + sIdx / L) == .A) = par

private abbrev InactCond (idx L qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool) : Prop :=
  idx ≥ ((qep + 2) - healEpoch tL) * L ∨
    ¬(decide (idx % L = 0) = gMain ∧ decide (Party.senderOf (healEpoch tL + idx / L) == .A) = par)

private theorem inactive_ne_of_active {L qep : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool}
    {idx sIdx : ℕ} (hinact : InactCond idx L qep gMain tL par)
    (hact : ActiveSlot L qep gMain tL par sIdx) : sIdx ≠ idx := by
  rintro rfl; rcases hinact with hge | hnot
  · exact Nat.not_lt_of_ge hge hact.1
  · exact hnot ⟨hact.2.1, hact.2.2⟩

private theorem potInvMultiFS_query_inactive {L qep : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool}
    (idx : ℕ) (hinact : InactCond idx L qep gMain tL par) (g : (IIM).Tag) {Γ' : List (Ty SP)}
    (argE : Expr OO Γ' ((IIM).dom g)) (ρ : Env Γ')
    (hact : ActiveSlot L qep gMain tL par (argE.eval ρ).1) :
    PotOKInvFS (sessPred idx) (fun _ => True) (fun _ => 0) ((Comp.query (I := IIM) g argE).eval ρ) 0 :=
  potInvMultiFS_query idx g argE ρ 0 0 (by simp [inactive_ne_of_active hinact hact])

private theorem foldr_idx_le {α : Type} (f : α → Bool) (xs : List α) :
    xs.foldr (fun x acc => if f x = true then 0 else acc + 1) 0 ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih => dsimp only [List.foldr, List.length]; split <;> omega

private theorem foldr_len_eq {α : Type} (xs : List α) :
    xs.foldr (fun _ acc => acc + 1) 0 = xs.length := by
  induction xs with | nil => rfl | cons _ xs ih => dsimp only [List.foldr, List.length]; rw [ih]

private theorem foldr_app_len {α : Type} (xs : List α) (y : α) :
    (xs.foldr (fun x acc => x :: acc) [y]).length = xs.length + 1 := by
  induction xs with | nil => rfl | cons _ xs ih => dsimp only [List.foldr, List.length]; rw [ih]

private theorem validGuessBucketParAuthE_active_epoch (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ' : List (Ty SP)} (tE : Expr OO Γ' .nat) (ρ : Env Γ')
    (hvg : (validGuessBucketParAuthE (O := OO) Δcka tL par tE).eval ρ = true) :
    healEpoch tL ≤ tE.eval ρ ∧ decide (Party.senderOf (tE.eval ρ) == .A) = par := by
  unfold validGuessBucketParAuthE at hvg
  have htL : (_root_.CryptoGames.SM.Engine.optNatLit (O' := OO) tL).eval ρ = tL := by cases tL <;> rfl
  simp only [Expr.eval, _root_.CryptoGames.SM.validGuessE_eval, senderOfE_eval, htL, Bool.and_eq_true] at hvg
  refine ⟨?_, ?_⟩
  · rcases tL with _ | l
    · exact Nat.zero_le _
    · simp only [_root_.CryptoGames.SM.lastLeakGuessAdmissible, _root_.CryptoGames.SM.healedBy,
        healEpoch, decide_eq_true_eq] at hvg ⊢; omega
  · have hpar := hvg.2; cases par <;> cases hP : Party.senderOf (tE.eval ρ) <;> simp_all [partyEnc]

private theorem activeSlot_of_reg {q qep t0 localIdx : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool}
    (htTop : qep + 1 < t0 → False) (htH : healEpoch tL ≤ t0)
    (hpar : decide (Party.senderOf t0 == .A) = par)
    (hbound : localIdx + (if gMain then 0 else 1) < q + 1) (hmain : gMain = true → localIdx = 0) :
    ActiveSlot (q + 1) qep gMain tL par ((q + 1) * (t0 - healEpoch tL) + localIdx + (if gMain then 0 else 1)) := by
  have htLe : t0 ≤ qep + 1 := Nat.le_of_not_lt htTop
  have hd : (t0 - healEpoch tL) + 1 ≤ (qep + 2) - healEpoch tL := by omega
  set L := q + 1; set d := t0 - healEpoch tL; set off := if gMain then 0 else 1; set r := localIdx + off
  have hsEq : L * d + localIdx + off = r + L * d := by omega
  have hlt : L * d + localIdx + off < ((qep + 2) - healEpoch tL) * L := by
    have h1 : L * d + r < L * (d + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    have h2 : L * (d + 1) ≤ L * ((qep + 2) - healEpoch tL) := Nat.mul_le_mul_left L hd
    rw [Nat.mul_comm ((qep + 2) - healEpoch tL) L]; omega
  have hmod : (L * d + localIdx + off) % L = r := by
    rw [hsEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbound]
  have hdiv : (L * d + localIdx + off) / L = d := by
    rw [hsEq, Nat.add_mul_div_left _ _ (Nat.succ_pos q), Nat.div_eq_of_lt hbound, Nat.zero_add]
  refine ⟨hlt, ?_, ?_⟩
  · rw [hmod]; cases gMain <;> [simp [r, off]; simp [r, off, hmain rfl]]
  · rw [hdiv, show healEpoch tL + d = t0 by omega]; exact hpar

private theorem mbHsSetSessionsAt_val {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy)
    (tE : Expr OO Γ' .nat) (seE : Expr OO Γ' (.list (.base .i))) (ρ : Env Γ') :
    (mbHsSetSessionsAt hE tE seE).eval ρ =
      ((hE.eval ρ).1, (hE.eval ρ).2.1, (fun j => if j = tE.eval ρ then seE.eval ρ else (hE.eval ρ).2.2.1 j),
        (hE.eval ρ).2.2.2.1, (hE.eval ρ).2.2.2.2) := rfl

private theorem mbHsSetCache_val {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy) (caE : Expr OO Γ' _) (ρ : Env Γ') :
    (mbHsSetCache hE caE).eval ρ =
      (caE.eval ρ, (hE.eval ρ).2.1, (hE.eval ρ).2.2.1, (hE.eval ρ).2.2.2.1, (hE.eval ρ).2.2.2.2) := rfl

@[local simp] private theorem mbHsSetTableAt_fst {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy)
    (tE : Expr OO Γ' .nat) (tbE : Expr OO Γ' _) (ρ : Env Γ') :
    ((mbHsSetTableAt hE tE tbE).eval ρ).1 = (hE.eval ρ).1 := rfl
@[local simp] private theorem mbHsSetTableAt_ses {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy)
    (tE : Expr OO Γ' .nat) (tbE : Expr OO Γ' _) (ρ : Env Γ') :
    ((mbHsSetTableAt hE tE tbE).eval ρ).2.2.1 = (hE.eval ρ).2.2.1 := rfl
@[local simp] private theorem mbHsSetBookAt_fst {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy)
    (sE : Expr OO Γ' .nat) (bE : Expr OO Γ' _) (ρ : Env Γ') :
    ((mbHsSetBookAt hE sE bE).eval ρ).1 = (hE.eval ρ).1 := rfl
@[local simp] private theorem mbHsSetBookAt_ses {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy)
    (sE : Expr OO Γ' .nat) (bE : Expr OO Γ' _) (ρ : Env Γ') :
    ((mbHsSetBookAt hE sE bE).eval ρ).2.2.1 = (hE.eval ρ).2.2.1 := rfl
@[local simp] private theorem mbHsSetLfWin_fst {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy)
    (wE : Expr OO Γ' .bool) (ρ : Env Γ') :
    ((mbHsSetLfWin hE wE).eval ρ).1 = (hE.eval ρ).1 := rfl
@[local simp] private theorem mbHsSetLfWin_ses {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy)
    (wE : Expr OO Γ' .bool) (ρ : Env Γ') :
    ((mbHsSetLfWin hE wE).eval ρ).2.2.1 = (hE.eval ρ).2.2.1 := rfl

private theorem tset_eval_val {α : Ty SP} {Γ' : List (Ty SP)}
    (tblE : Expr OO Γ' (.tbl α)) (iE : Expr OO Γ' .nat) (vE : Expr OO Γ' α) (ρ : Env Γ') :
    (Expr.tset tblE iE vE).eval ρ = (fun j => if j = iE.eval ρ then vE.eval ρ else (tblE.eval ρ) j) := rfl

private theorem regSessMultiBucketE_inact (q qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') :
    let out := (regSessMBE (q + 1) gMain tL hE tE ikE).eval ρ
    out.2.1 = (hE.eval ρ).1 ∧
    (∀ τ, τ ≠ tE.eval ρ → out.2.2.2.1 τ = (hE.eval ρ).2.2.1 τ) ∧
    (∀ τ, (out.2.2.2.1 τ).length ≤ ((hE.eval ρ).2.2.1 τ).length + 1) ∧
    (((qep + 1 < tE.eval ρ → False) ∧ healEpoch tL ≤ tE.eval ρ ∧
      decide (Party.senderOf (tE.eval ρ) == .A) = par ∧
      (if gMain then (hE.eval ρ).2.2.1 (tE.eval ρ) = [] else ((hE.eval ρ).2.2.1 (tE.eval ρ)).length < q)) →
      ActiveSlot (q + 1) qep gMain tL par out.1) := by
  intro out; dsimp only [out, regSessMultiBucketE]
  rw [letE_eval, pair_eval, pair_eval, ite_eval]
  set ρ₁ := Env.cons (t := .prod mbHsTy (.prod .nat (.base .i))) (hE.eval ρ, tE.eval ρ, ikE.eval ρ) ρ
  set sesExpr : Expr OO _ (.list (.base .i)) := .tget (mbHsSessionsTbl (.fst .v0)) (.fst (.snd .v0))
  have hSesE : sesExpr.eval ρ₁ = (hE.eval ρ).2.2.1 (tE.eval ρ) := rfl
  have hIdxLe : ((sesIdxE (q + 1) sesExpr (.snd (.snd .v0))).eval ρ₁ : ℕ) ≤
      ((hE.eval ρ).2.2.1 (tE.eval ρ)).length := by
    unfold sessionsIdxOfBucketE; rw [letE_eval, pair_eval, hSesE]
    simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
    exact Nat.le_trans (foldr_idx_le _ _) (List.length_take_le' _ _)
  have hLenLe : ((sesLenE (q + 1) sesExpr).eval ρ₁ : ℕ) ≤ ((hE.eval ρ).2.2.1 (tE.eval ρ)).length := by
    unfold sessionsLenBucketE
    simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, hSesE, foldr_len_eq]
    exact List.length_take_le' _ _
  have hAppLe : ((sesAppE (q + 1) sesExpr (.snd (.snd .v0))).eval ρ₁).length ≤
      ((hE.eval ρ).2.2.1 (tE.eval ρ)).length + 1 := by
    unfold sessionsAppendOneBucketE
    simp only [Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, hSesE, foldr_app_len]
    exact Nat.add_le_add_right (List.length_take_le' _ _) 1
  cases hm : (sesMemE (q + 1) sesExpr (.snd (.snd .v0))).eval ρ₁
  · simp only [Bool.false_eq_true, ↓reduceIte, pair_eval]; rw [mbHsSetSessionsAt_val]
    have hFst : (Expr.fst (O := OO) .v0).eval ρ₁ = hE.eval ρ := rfl
    have hSndFst : (Expr.fst (O := OO) (.snd .v0)).eval ρ₁ = tE.eval ρ := rfl
    have hLHS : (Expr.add (O := OO) (.add (.mulK (q + 1) (.sub (.fst (.snd .v0)) (.nat (healEpoch tL))))
          (sesLenE (q + 1) sesExpr)) (.nat (if gMain then 0 else 1))).eval ρ₁ =
        (q + 1) * (tE.eval ρ - healEpoch tL) + (sesLenE (q + 1) sesExpr).eval ρ₁ + (if gMain then 0 else 1) := rfl
    rw [hFst, hSndFst, hLHS]
    refine ⟨rfl, fun τ hne => by simp [hne], fun τ => ?_, fun ⟨htTop, htH, hpar, hses⟩ => ?_⟩
    · by_cases hτ : τ = tE.eval ρ <;> [subst hτ; skip] <;> [simpa using hAppLe; simp [hτ]]
    · cases gMain
      · simp only [Bool.false_eq_true, ↓reduceIte] at hses ⊢
        exact activeSlot_of_reg (gMain := false) htTop htH hpar
          (Nat.add_lt_add_right (Nat.lt_of_le_of_lt hLenLe hses) 1) (by intro h; cases h)
      · simp only [↓reduceIte] at hses ⊢
        have h0 : (sesLenE (q + 1) sesExpr).eval ρ₁ = 0 := Nat.eq_zero_of_le_zero (by simpa [hses] using hLenLe)
        exact activeSlot_of_reg (gMain := true) htTop htH hpar (by rw [h0]; exact Nat.succ_pos q) (fun _ => h0)
  · simp only [↓reduceIte, pair_eval]
    have hFst : (Expr.fst (O := OO) .v0).eval ρ₁ = hE.eval ρ := rfl
    have hLHS : (Expr.add (O := OO) (.add (.mulK (q + 1) (.sub (.fst (.snd .v0)) (.nat (healEpoch tL))))
          (sesIdxE (q + 1) sesExpr (.snd (.snd .v0)))) (.nat (if gMain then 0 else 1))).eval ρ₁ =
        (q + 1) * (tE.eval ρ - healEpoch tL) + (sesIdxE (q + 1) sesExpr (.snd (.snd .v0))).eval ρ₁ +
          (if gMain then 0 else 1) := rfl
    rw [hFst, hLHS]
    refine ⟨rfl, fun _ _ => rfl, fun _ => Nat.le_add_right _ 1, fun ⟨htTop, htH, hpar, hses⟩ => ?_⟩
    cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte] at hses ⊢
      exact activeSlot_of_reg (gMain := false) htTop htH hpar
        (Nat.add_lt_add_right (Nat.lt_of_le_of_lt hIdxLe hses) 1) (by intro h; cases h)
    · simp only [↓reduceIte] at hses ⊢
      have h0 : (sesIdxE (q + 1) sesExpr (.snd (.snd .v0))).eval ρ₁ = 0 :=
        Nat.eq_zero_of_le_zero (by simpa [hses] using hIdxLe)
      exact activeSlot_of_reg (gMain := true) htTop htH hpar (by rw [h0]; exact Nat.succ_pos q) (fun _ => h0)

private theorem regSessOptMultiBucketE_inact (q qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat)
    (sidE : Expr OO Γ' (.opt (.base .i))) (ρ : Env Γ') :
    let out := (regSessOptMBE (q + 1) gMain tL hE tE sidE).eval ρ
    out.2.1 = (hE.eval ρ).1 ∧ (sidE.eval ρ = none → out.1 = none ∧ out.2.2.2.1 = (hE.eval ρ).2.2.1) ∧
    (∀ τ, τ ≠ tE.eval ρ → out.2.2.2.1 τ = (hE.eval ρ).2.2.1 τ) ∧
    (∀ τ, (out.2.2.2.1 τ).length ≤ ((hE.eval ρ).2.2.1 τ).length + 1) ∧
    (∀ sIdx, out.1 = some sIdx → (qep + 1 < tE.eval ρ → False) → healEpoch tL ≤ tE.eval ρ →
      decide (Party.senderOf (tE.eval ρ) == .A) = par →
      (if gMain then (hE.eval ρ).2.2.1 (tE.eval ρ) = [] else ((hE.eval ρ).2.2.1 (tE.eval ρ)).length < q) →
      ActiveSlot (q + 1) qep gMain tL par sIdx) := by
  intro out; dsimp only [out, regSessOptMultiBucketE]; simp only [Expr.eval, Expr.v0, Env.get_cons_zero]
  cases hsid : sidE.eval ρ with
  | none => exact ⟨rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => Nat.le_add_right _ 1, fun _ hs _ _ _ _ => by cases hs⟩
  | some ik =>
    have hSub := regSessMultiBucketE_inact q qep gMain tL par
      (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) .v0 (.cons ik (.cons ((hE.pair (tE.pair sidE)).eval ρ) ρ))
    simp only [Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, hsid] at hSub ⊢
    refine ⟨hSub.1, fun (h : (some ik : Option I) = none) => False.elim (by cases h),
      hSub.2.1, hSub.2.2.1, fun sIdx hs htTop htH hpar hses => ?_⟩
    injection hs with hs; subst hs; exact hSub.2.2.2 ⟨htTop, htH, hpar, hses⟩

private def VpAct (q qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool) (vp : (mVpTy).denote) : Prop :=
  (∀ sIdx, vp.2.2.1 = some (.inr sIdx) → ActiveSlot (q + 1) qep gMain tL par sIdx) ∧
  (∀ τ sIdx, vp.2.2.2.1 τ = some (.inr sIdx) → ActiveSlot (q + 1) qep gMain tL par sIdx)

private def CacheAct (q qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool) (h : (mbHsTy).denote) : Prop :=
  ∀ τ e sIdx, h.1 τ = some e → e.2.2.2 = some sIdx → ActiveSlot (q + 1) qep gMain tL par sIdx

private def SessBound (q : ℕ) (gMain : Bool) (m : ℕ) (vpA vpB : (mVpTy).denote) (h : (mbHsTy).denote) : Prop :=
  if gMain then (∀ τ, vpA.2.2.2.2.2.2 < τ → Party.A.sendsIn τ = true → h.2.2.1 τ = []) ∧
    (∀ τ, vpB.2.2.2.2.2.2 < τ → Party.B.sendsIn τ = true → h.2.2.1 τ = [])
  else ∀ τ, (h.2.2.1 τ).length + m ≤ q

private def MbEsInv (q qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (m : ℕ) (es : (esTy mVpTy mbHsTy).denote) : Prop :=
  es.2.2 = false → es.1.1.1.1 = false ∧ es.1.1.2.1 = true ∧ VpAct q qep gMain tL par es.1.1.1 ∧
    VpAct q qep gMain tL par es.1.1.2 ∧ CacheAct q qep gMain tL par es.2.1 ∧
    SessBound q gMain m es.1.1.1 es.1.1.2 es.2.1

private theorem mbEsInv_step_noop {q qep : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool}
    {m : ℕ} {es : (esTy mVpTy mbHsTy).denote} (hInv : MbEsInv q qep gMain tL par (m + 1) es) :
    MbEsInv q qep gMain tL par m es := by
  intro hab; obtain ⟨hAId, hBId, hVpA, hVpB, hCa, hSes⟩ := hInv hab; refine ⟨hAId, hBId, hVpA, hVpB, hCa, ?_⟩
  unfold SessBound at hSes ⊢; cases gMain <;> [(intro τ; have hτ := hSes τ; omega); exact hSes]

private theorem sendsIn_disjoint {t : ℕ} (hA : Party.A.sendsIn t = true) : Party.B.sendsIn t = false := by
  unfold Party.sendsIn at hA ⊢; cases Party.senderOf t <;> simp_all

private theorem lookupMultiBucketFC_inact (idx L : ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') :
    PotOKInvFS (sessPred idx) (fun res => res.2.1 = (hE.eval ρ).1 ∧ res.2.2.2.1 = (hE.eval ρ).2.2.1)
      (fun _ => 0) ((lookupMultiBucketFC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L hE tE ikE).eval ρ) 0 := by
  unfold lookupMultiBucketFC; rw [eval_bind_ret]
  refine potInvFS_caseOpt (fun _ => ?_)
    (fun _ _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v1], by simp [Expr.eval, Expr.v1]⟩ (Nat.le_refl 0))
  rw [eval_bind]; refine PotOKInvFS.bindPot (potInvMultiFS_zero idx _ _ rfl) (fun _ _ =>
    potInvFS_ret ⟨by simp [Expr.eval, Expr.v1], by simp [Expr.eval, Expr.v1]⟩ (Nat.le_refl 0))

private theorem rootFSMultiBucketAuthC_inact (idx L Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig)) (ρ : Env Γ') :
    PotOKInvFS (sessPred idx)
      (fun res => res.2.1 = (hE.eval ρ).1 ∧ res.2.2.2.1 = (hE.eval ρ).2.2.1 ∧
        (∀ ik, res.1.2.2 = some ik → (qep + 1 < tE.eval ρ → False) ∧ healEpoch tL ≤ tE.eval ρ ∧
          decide (Party.senderOf (tE.eval ρ) == .A) = par))
      (fun _ => 0) ((rootFSMultiBucketAuthC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L Δcka qep tL par hE tE plE ikE σE).eval ρ) 0 := by
  unfold rootFSMultiBucketAuthC; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => potInvFS_ret ⟨rfl, rfl, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
    (fun hNotOr => potInvFS_ite (fun hVg => ?_) (fun _ => potInvFS_ite (fun _ => ?_) (fun _ => potInvFS_ite
      (fun _ => ?_) (fun _ => potInvFS_ret ⟨rfl, rfl, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0)))))
  · have htTop : qep + 1 < tE.eval ρ → False := by
      simp only [orE_eval, Bool.or_eq_false_iff, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotOr
      exact of_decide_eq_false hNotOr.2
    have hActEp := validGuessBucketParAuthE_active_epoch Δcka tL par (.fst (.snd (Expr.v0 (O := OO))))
      (.cons ((hE.pair (tE.pair (plE.pair (ikE.pair σE)))).eval ρ) ρ) hVg
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hActEp; refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
    · rw [eval_bind]; refine PotOKInvFS.bindPot (potInvMultiFS_zero idx _ _ rfl) (fun _ _ => ?_)
      rw [eval_bind]; exact PotOKInvFS.bindPot (potInvMultiFS_zero idx _ _ rfl)
        (fun _ _ => potInvFS_ret ⟨rfl, rfl, fun _ _ => ⟨htTop, hActEp.1, hActEp.2⟩⟩ (Nat.le_refl 0))
    · rw [eval_bind]
      have hL := lookupMultiBucketFC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) idx L (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))
        (.fst (.snd (.snd (.snd .v0)))) (.cons ((hE.pair (tE.pair (plE.pair (ikE.pair σE)))).eval ρ) ρ)
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hL
      exact PotOKInvFS.bindPot hL (fun lOut hlOut =>
        potInvFS_ret ⟨hlOut.1, hlOut.2, fun _ _ => ⟨htTop, hActEp.1, hActEp.2⟩⟩ (Nat.le_refl 0))
  · rw [eval_bind]; refine PotOKInvFS.bindPot (potInvMultiFS_zero idx _ _ rfl) (fun _ _ => ?_)
    rw [eval_bind]; exact PotOKInvFS.bindPot (potInvMultiFS_zero idx _ _ rfl)
      (fun _ _ => potInvFS_ret ⟨rfl, rfl, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
  · rw [eval_bind]
    have hL := lookupMultiBucketFC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) idx L (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))
      (.fst (.snd (.snd (.snd .v0)))) (.cons ((hE.pair (tE.pair (plE.pair (ikE.pair σE)))).eval ρ) ρ)
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hL
    exact PotOKInvFS.bindPot hL (fun lOut hlOut =>
      potInvFS_ret ⟨hlOut.1, hlOut.2, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))

private theorem fsMultiBucketAuthStartSendC_inact (idx q Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (hCa : CacheAct q qep gMain tL par (hE.eval ρ))
    (hses : if gMain then (hE.eval ρ).2.2.1 (tE.eval ρ) = [] else ((hE.eval ρ).2.2.1 (tE.eval ρ)).length < q) :
    PotOKInvFS (sessPred idx)
      (fun res => CacheAct q qep gMain tL par res.2 ∧ (∀ τ, τ ≠ tE.eval ρ → res.2.2.2.1 τ = (hE.eval ρ).2.2.1 τ) ∧
        (∀ τ, (res.2.2.2.1 τ).length ≤ ((hE.eval ρ).2.2.1 τ).length + 1) ∧
        (∀ tup sIdx, res.1 = some tup → tup.2.2.2 = .inr sIdx → ActiveSlot (q + 1) qep gMain tL par sIdx))
      (fun _ => 0) ((fsMultiBucketAuthStartSendC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        (q + 1) Δcka qep gMain tL par hE ctxE pE tE γE σE rE).eval ρ) 0 := by
  unfold fsMultiBucketAuthStartSendC; rw [eval_bind_ret, eval_bind]
  refine PotOKInvFS.bindPot (potInvFS_caseOpt (fun _ => potInvMultiFS_zero idx _ _ rfl)
      (fun _ _ => potInvFS_ret trivial (Nat.le_refl 0))) (fun coins _ => ?_); rw [eval_bind]
  have hR := rootFSMultiBucketAuthC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) idx (q + 1) Δcka qep tL par (.fst (Expr.v1 (O := OO))) (.fst (.snd (.snd .v1)))
    (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.postLeakBucketE tL (.fst (.snd .v1)))
    (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))))
    (.fst (.snd (.snd (.snd (.snd .v1)))))
    (.cons coins (.cons ((hE.pair (ctxE.pair (tE.pair (γE.pair (σE.pair rE))))).eval ρ) ρ))
  simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hR
  refine PotOKInvFS.bindPot hR (fun rOut hrOut => potInvFS_ret ?_ (Nat.le_refl 0))
  set ρ₂ := Env.cons rOut (.cons coins (.cons ((hE.pair (ctxE.pair (tE.pair (γE.pair (σE.pair rE))))).eval ρ) ρ))
  have hReg := regSessOptMultiBucketE_inact q qep gMain tL par
    (.snd (Expr.v0 (O := OO))) (.fst (.snd (.snd .v2))) (.snd (.snd (.fst .v0))) ρ₂
  have ht2 : (Expr.fst (O := OO) (.snd (.snd .v2))).eval ρ₂ = tE.eval ρ := rfl
  have hr2 : (Expr.snd (O := OO) .v0).eval ρ₂ = rOut.2 := rfl
  have hsid2 : (Expr.snd (O := OO) (.snd (.fst .v0))).eval ρ₂ = rOut.1.2.2 := rfl
  rw [ht2, hr2, hsid2] at hReg
  have hOptAct : ∀ sIdx, ((regSessOptMBE (q + 1) gMain tL (.snd (Expr.v0 (O := OO)))
        (.fst (.snd (.snd .v2))) (.snd (.snd (.fst .v0)))).eval ρ₂).1 = some sIdx →
      ActiveSlot (q + 1) qep gMain tL par sIdx := by
    intro sIdx hs; cases hsid : rOut.1.2.2 with
    | none => rw [(hReg.2.1 hsid).1] at hs; cases hs
    | some ik => obtain ⟨htTop, htH, hpar⟩ := hrOut.2.2 ik hsid; exact hReg.2.2.2.2 sIdx hs htTop htH hpar (by rwa [hrOut.2.1])
  rw [pair_eval, mbHsSetCache_val, tset_eval_val]
  have hCaReg : (mbHsCache (.snd (regSessOptMBE (q + 1) gMain tL (.snd (Expr.v0 (O := OO)))
      (.fst (.snd (.snd .v2))) (.snd (.snd (.fst .v0)))))).eval ρ₂ = (hE.eval ρ).1 := hReg.1.trans hrOut.1
  refine ⟨?_, fun τ hne => (hReg.2.2.1 τ hne).trans (congrFun hrOut.2.1 τ),
    fun τ => by have h1 := hReg.2.2.2.1 τ; rwa [hrOut.2.1] at h1, ?_⟩
  · intro τ e sIdx hτ he; rw [ht2, hCaReg] at hτ; by_cases hEq : τ = tE.eval ρ
    · subst hEq; simp only [↓reduceIte, some_eval, pair_eval, Option.some.injEq] at hτ; subst hτ; exact hOptAct sIdx he
    · simp only [hEq, ↓reduceIte] at hτ; exact hCa τ e sIdx hτ he
  · intro tup sIdx htup hssv; simp only [some_eval, pair_eval, Option.some.injEq] at htup; subst htup
    dsimp only [Expr.eval] at hssv; split at hssv
    · cases hssv
    · next s' hs' => simp only [Sum.inr.injEq, Expr.eval, Expr.v0, Env.get_cons_zero] at hssv; subst hssv; exact hOptAct s' hs'

private theorem fsMultiBucketAuthFsSendC_inact (idx q Δcka qep : ℕ) (gMain la : Bool)
    (tL : Option ℕ) (par : Bool) (hinact : InactCond idx (q + 1) qep gMain tL par)
    {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (ssvE : Expr OO Γ' (.sum (.base .ss) .nat))
    (hdrE : Expr OO Γ' hdrTy) (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) (ρ : Env Γ')
    (hssv : ∀ sIdx, ssvE.eval ρ = .inr sIdx → ActiveSlot (q + 1) qep gMain tL par sIdx) :
    PotOKInvFS (sessPred idx)
      (fun res => res.2.1 = (hE.eval ρ).1 ∧ res.2.2.2.1 = (hE.eval ρ).2.2.1 ∧
        (∀ vc sIdx, res.1 = some vc → vc.1 = .inr sIdx → ActiveSlot (q + 1) qep gMain tL par sIdx))
      (fun _ => 0) ((fsMultiBucketAuthFsSendC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).eval ρ) 0 := by
  unfold fsMultiBucketAuthFsSendC; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v1],
    by simp [Expr.eval, Expr.v1], fun vc sIdx hvc hs => by
      simp only [some_eval, pair_eval, Option.some.injEq] at hvc; subst hvc; simp [Expr.eval] at hs⟩
    (Nat.le_refl 0)) (fun sIdx hsIdx => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hsIdx; have hAct := hssv sIdx hsIdx; rw [eval_bind]
  refine PotOKInvFS.bindPot (Inv₁ := fun oh => oh.2.1 = (hE.eval ρ).1 ∧ oh.2.2.2.1 = (hE.eval ρ).2.2.1)
    (B₁ := fun _ => 0) ?_ (fun oh hoh => ?_)
  · refine potInvFS_ite (fun _ => ?_)
      (fun _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v1], by simp [Expr.eval, Expr.v1]⟩ (Nat.le_refl 0))
    rw [eval_bind]; exact PotOKInvFS.bindPot
      (potInvMultiFS_query_inactive idx hinact FSHdrTag.cs _ _ (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hAct))
      (fun _ _ => potInvFS_caseOpt
        (fun _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v2], by simp [Expr.eval, Expr.v2]⟩ (Nat.le_refl 0))
        (fun _ _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v3], by simp [Expr.eval, Expr.v3]⟩ (Nat.le_refl 0)))
  · refine potInvFS_ite (fun _ => potInvFS_ret ⟨hoh.1, hoh.2, fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0)) (fun _ => ?_)
    rw [eval_bind]; refine PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => 0) ?_ (fun _ _ => ?_)
    · exact potInvFS_caseOpt
        (fun _ => potInvMultiFS_query_inactive idx hinact FSHdrTag.tr _ _
          (by simpa [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero] using hAct))
        (fun _ _ => potInvMultiFS_query_inactive idx hinact FSHdrTag.ch _ _
          (by simpa [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero] using hAct))
    · refine potInvFS_caseOpt
        (fun _ => potInvFS_ret ⟨hoh.1, hoh.2, fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
        (fun _ _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v2, hoh.1], by simp [Expr.eval, Expr.v2, hoh.2],
          fun vc sIdx' hvc hs' => ?_⟩ (Nat.le_refl 0))
      simp only [Expr.eval, Option.some.injEq] at hvc; subst hvc; simp only [Sum.inr.injEq] at hs'; subst hs'; exact hAct

private theorem vSendStep1C_inact (idx q B Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ)
    (par la : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' mVpTy) (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (hVp : VpAct q qep gMain tL par (sE.eval ρ)) (hCa : CacheAct q qep gMain tL par (hE.eval ρ))
    (hses : (partyDec (sE.eval ρ).1).sendsIn ((sE.eval ρ).2.2.2.2.2.2 + 1) = true →
      if gMain then (hE.eval ρ).2.2.1 ((sE.eval ρ).2.2.2.2.2.2 + 1) = []
      else ((hE.eval ρ).2.2.1 ((sE.eval ρ).2.2.2.2.2.2 + 1)).length < q) :
    PotOKInvFS (sessPred idx)
      (fun res => CacheAct q qep gMain tL par res.2 ∧ (∀ τ, (res.2.2.2.1 τ).length ≤ ((hE.eval ρ).2.2.1 τ).length + 1) ∧
        (∀ s1, res.1 = some s1 → s1.1 = (sE.eval ρ).1 ∧ (sE.eval ρ).2.2.2.2.2.2 ≤ s1.2.2.2.2.2.2 ∧
          VpAct q qep gMain tL par s1 ∧ (gMain = true →
            (∀ τ, s1.2.2.2.2.2.2 < τ → (partyDec s1.1).sendsIn τ = true → res.2.2.2.1 τ = (hE.eval ρ).2.2.1 τ) ∧
            (∀ τ, (partyDec (!s1.1)).sendsIn τ = true → res.2.2.2.1 τ = (hE.eval ρ).2.2.1 τ))))
      (fun _ => 0) ((vSendStep1C (hkMBE (q + 1) B Δcka qep gMain tL par la) hE ctxE pE sE rE).eval ρ) 0 := by
  unfold vSendStep1C; rw [eval_bind_ret]; refine potInvFS_ite (fun hs => ?_) (fun _ => ?_)
  · rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at hs
    simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hs; dsimp only [hooksFSMultiBucketAuthC]; rw [eval_bind]
    have hSS := fsMultiBucketAuthStartSendC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) idx q Δcka qep gMain tL par (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))
      (.fst (.snd (.snd .v0))) (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
      (vpΓ (.fst (.snd (.snd (.snd .v0))))) (vpRoot (.fst (.snd (.snd (.snd .v0))))) (.snd (.snd (.snd (.snd .v0))))
      (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, rE.eval ρ) ρ) hCa (hses hs)
    simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hSS
    refine PotOKInvFS.bindPot hSS (fun ssOut hSSOut => potInvFS_caseOpt
      (fun _ => potInvFS_ret ⟨hSSOut.1, hSSOut.2.2.1, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0)) (fun tup htup => ?_))
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at htup
    refine potInvFS_ret ⟨hSSOut.1, hSSOut.2.2.1, fun s1 hs1 => ?_⟩ (Nat.le_refl 0)
    simp only [Option.some.injEq, vpMk, vpId, vpVR, vpTcurNat, Expr.eval, Expr.v0, Expr.v2,
      Env.get_cons_zero, Env.get_cons_succ] at hs1; subst hs1
    refine ⟨rfl, Nat.le_succ _, ⟨fun sIdx hvs => ?_, hVp.2⟩,
      fun _ => ⟨fun τ hlt _ => hSSOut.2.1 τ (Nat.ne_of_gt hlt), fun τ hOther => ?_⟩⟩
    · simp only [Option.some.injEq] at hvs; exact hSSOut.2.2.2 tup sIdx htup hvs
    · refine hSSOut.2.1 τ (fun hEq => ?_); subst hEq
      cases hb : (sE.eval ρ).1 <;> simp only [hb, partyDec, Bool.not_false, Bool.not_true] at hs hOther
      · exact Bool.noConfusion ((sendsIn_disjoint hs).symm.trans hOther)
      · exact Bool.noConfusion ((sendsIn_disjoint hOther).symm.trans hs)
  · refine potInvFS_ret ⟨hCa, fun _ => Nat.le_add_right _ 1, fun s1 hs1 => ?_⟩ (Nat.le_refl 0)
    simp only [Option.some.injEq, Expr.eval, Expr.v0, Env.get_cons_zero] at hs1; subst hs1
    exact ⟨rfl, Nat.le_refl _, hVp, fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩⟩

private theorem vSendC_inact (idx q B Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ)
    (par la : Bool) (hinact : InactCond idx (q + 1) qep gMain tL par) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' mVpTy) (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (hVp : VpAct q qep gMain tL par (sE.eval ρ)) (hCa : CacheAct q qep gMain tL par (hE.eval ρ))
    (hses : (partyDec (sE.eval ρ).1).sendsIn ((sE.eval ρ).2.2.2.2.2.2 + 1) = true →
      if gMain then (hE.eval ρ).2.2.1 ((sE.eval ρ).2.2.2.2.2.2 + 1) = []
      else ((hE.eval ρ).2.2.1 ((sE.eval ρ).2.2.2.2.2.2 + 1)).length < q) :
    PotOKInvFS (sessPred idx)
      (fun res => CacheAct q qep gMain tL par res.2 ∧ (∀ τ, (res.2.2.2.1 τ).length ≤ ((hE.eval ρ).2.2.1 τ).length + 1) ∧
        (∀ stCt, res.1 = some stCt → stCt.1.1 = (sE.eval ρ).1 ∧ (sE.eval ρ).2.2.2.2.2.2 ≤ stCt.1.2.2.2.2.2.2 ∧
          VpAct q qep gMain tL par stCt.1 ∧ (gMain = true →
            (∀ τ, stCt.1.2.2.2.2.2.2 < τ → (partyDec stCt.1.1).sendsIn τ = true → res.2.2.2.1 τ = (hE.eval ρ).2.2.1 τ) ∧
            (∀ τ, (partyDec (!stCt.1.1)).sendsIn τ = true → res.2.2.2.1 τ = (hE.eval ρ).2.2.1 τ))))
      (fun _ => 0) ((vSendC (hkMBE (q + 1) B Δcka qep gMain tL par la) hE ctxE pE sE mE pairE rE).eval ρ) 0 := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  have h1 := vSendStep1C_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
    (sampK := sampK) idx q B Δcka qep gMain tL par la (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))
    (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ) hVp hCa hses
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at h1
  refine PotOKInvFS.bindPot h1 (fun step1Out hStep1 => potInvFS_caseOpt
    (fun _ => potInvFS_ret ⟨hStep1.1, hStep1.2.1, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0)) (fun s1 hs1 => ?_))
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hs1; obtain ⟨hs1Id, hs1Ge, hs1Vp, hs1Main⟩ := hStep1.2.2 s1 hs1
  refine potInvFS_caseOpt (fun _ => potInvFS_ret ⟨hStep1.1, hStep1.2.1, fun stCt hstCt => by
      simp only [Option.some.injEq, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hstCt
      subst hstCt; exact ⟨hs1Id, hs1Ge, hs1Vp, hs1Main⟩⟩ (Nat.le_refl 0)) (fun v hv => ?_)
  simp only [vpVS, Expr.eval, Expr.v0, Env.get_cons_zero] at hv; dsimp only [hooksFSMultiBucketAuthC]; rw [eval_bind]
  have hFS := fsMultiBucketAuthFsSendC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) idx q Δcka qep gMain la tL par hinact (.snd (Expr.v2 (O := OO))) (.fst (.snd .v3))
    (.fst (.snd (.snd .v3))) (vpTcurNat .v1) .v0 (.pair (vpTcurNat .v1) (vpTcur .v1))
    (.fst (.snd (.snd (.snd (.snd .v3))))) (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
    (.cons v (.cons s1 (.cons step1Out (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ))))
    (fun sIdx hvs => hs1Vp.1 sIdx (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hvs; rw [hv, hvs]))
  simp only [Expr.eval, Expr.v2, Env.get_cons_zero, Env.get_cons_succ] at hFS
  refine PotOKInvFS.bindPot hFS (fun fsOut hFSOut => ?_)
  have hCa2 : CacheAct q qep gMain tL par fsOut.2 := fun τ e sIdx hτ he => hStep1.1 τ e sIdx (hFSOut.1 ▸ hτ) he
  have hLen2 : ∀ τ, (fsOut.2.2.2.1 τ).length ≤ ((hE.eval ρ).2.2.1 τ).length + 1 := fun τ => by rw [hFSOut.2.1]; exact hStep1.2.1 τ
  refine potInvFS_caseOpt (fun _ => potInvFS_ret ⟨hCa2, hLen2, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0)) (fun vc hvc => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hvc
  refine potInvFS_ret ⟨hCa2, hLen2, fun stCt hstCt => ?_⟩ (Nat.le_refl 0)
  simp only [Option.some.injEq, vpSetVS, letE_eval, vpMk, vpId, vpRoot, vpVR, vpΓ, vpTcur, vpTcurNat,
    Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hstCt; subst hstCt
  refine ⟨hs1Id, hs1Ge, ⟨fun sIdx hvs => ?_, hs1Vp.2⟩, fun hg => ?_⟩
  · simp only [Option.some.injEq] at hvs; exact hFSOut.2.2 vc sIdx hvc hvs
  · simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, hFSOut.2.1]; exact hs1Main hg

private theorem fsMultiBucketAuthStartRecvC_inact (idx q Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ') (hCa : CacheAct q qep gMain tL par (hE.eval ρ))
    (hses : gMain = false → ((hE.eval ρ).2.2.1 (tE.eval ρ)).length < q) :
    PotOKInvFS (sessPred idx)
      (fun res => res.2.1 = (hE.eval ρ).1 ∧ (gMain = true → res.2.2.2.1 = (hE.eval ρ).2.2.1) ∧
        (∀ τ, (res.2.2.2.1 τ).length ≤ ((hE.eval ρ).2.2.1 τ).length + 1) ∧
        (∀ tup sIdx, res.1 = some (some tup) → tup.2.2 = .inr sIdx → ActiveSlot (q + 1) qep gMain tL par sIdx))
      (fun _ => 0) ((fsMultiBucketAuthStartRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        (q + 1) Δcka qep gMain tL par hE ctxE pE tE γE σE tnE).eval ρ) 0 := by
  unfold fsMultiBucketAuthStartRecvC; rw [eval_bind_ret]
  set ρ₀ := Env.cons ((hE.pair (ctxE.pair (tE.pair (γE.pair (σE.pair tnE))))).eval ρ) ρ
  refine potInvFS_caseOpt (fun _ => ?_) (fun cEnt hcEnt => ?_)
  · refine potInvFS_ite (fun _ => potInvFS_ite
      (fun _ => potInvFS_ret ⟨rfl, fun _ => rfl, fun _ => Nat.le_add_right _ 1, fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
      (fun _ => potInvFS_ret ⟨rfl, fun _ => rfl, fun _ => Nat.le_add_right _ 1, fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0)))
      (fun hgF => ?_)
    have hgMainF : gMain = false := by simpa [Expr.eval] using hgF
    refine potInvFS_ite (fun hCond1 => ?_)
      (fun _ => potInvFS_ret ⟨rfl, fun _ => rfl, fun _ => Nat.le_add_right _ 1, fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
    have htTop : qep + 1 < tE.eval ρ → False := by
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, ρ₀] at hCond1
      exact hCond1.1
    refine potInvFS_ite
      (fun _ => potInvFS_ret ⟨rfl, fun _ => rfl, fun _ => Nat.le_add_right _ 1, fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
      (fun _ => potInvFS_ite
        (fun _ => potInvFS_ret ⟨rfl, fun _ => rfl, fun _ => Nat.le_add_right _ 1, fun tup sIdx h hs => by
          simp only [some_eval, pair_eval, Option.some.injEq] at h; subst h; simp [Expr.eval] at hs⟩ (Nat.le_refl 0))
        (fun _ => potInvFS_ite (fun hVg => ?_) (fun _ => ?_)))
    · have hActEp := validGuessBucketParAuthE_active_epoch Δcka tL par (.fst (.snd (.snd (Expr.v0 (O := OO))))) ρ₀ hVg
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero, ρ₀] at hActEp; rw [eval_bind]
      have hL := lookupMultiBucketFC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) idx (q + 1) (.fst (Expr.v0 (O := OO))) (.fst (.snd (.snd .v0)))
        (.snd (Expr.op (O := OO) CKAOp.ckaReceive (.pair (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd .v0)))))))) ρ₀
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero, ρ₀] at hL
      refine PotOKInvFS.bindPot hL (fun lOut hlOut => potInvFS_ret ?_ (Nat.le_refl 0))
      set ρ₁ := Env.cons lOut ρ₀
      have hReg := regSessMultiBucketE_inact q qep false tL par (.snd (Expr.v0 (O := OO))) (.fst (.snd (.snd .v1)))
        (.snd (Expr.op (O := OO) CKAOp.ckaReceive (.pair (.fst (.snd (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd (.snd .v1)))))))) ρ₁
      have ht1 : (Expr.fst (O := OO) (.snd (.snd .v1))).eval ρ₁ = tE.eval ρ := rfl
      have hr1 : (Expr.snd (O := OO) .v0).eval ρ₁ = lOut.2 := rfl
      rw [ht1, hr1] at hReg
      refine ⟨hReg.1.trans hlOut.1, fun hg => Bool.noConfusion (hgMainF.symm.trans hg),
        fun τ => by have h1 := hReg.2.2.1 τ; rwa [hlOut.2] at h1, fun tup sIdx htup hs => ?_⟩
      simp only [some_eval, pair_eval, Option.some.injEq] at htup; subst htup
      simp only [Expr.eval, Sum.inr.injEq] at hs; subst hs; rw [hgMainF]
      exact hReg.2.2.2 ⟨htTop, hActEp.1, hActEp.2, by simpa [hlOut.2] using hses hgMainF⟩
    · refine potInvFS_ite (fun _ => ?_)
        (fun _ => potInvFS_ret ⟨rfl, fun _ => rfl, fun _ => Nat.le_add_right _ 1, fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
      rw [eval_bind]
      have hL := lookupMultiBucketFC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) idx (q + 1) (.fst (Expr.v0 (O := OO))) (.fst (.snd (.snd .v0)))
        (.snd (Expr.op (O := OO) CKAOp.ckaReceive (.pair (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd .v0)))))))) ρ₀
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero, ρ₀] at hL
      exact PotOKInvFS.bindPot hL (fun lOut hlOut => potInvFS_ret
        ⟨by simp [Expr.eval, Expr.v0, hlOut.1], fun _ => by simp [Expr.eval, Expr.v0, hlOut.2],
         fun τ => by simp only [Expr.eval, Expr.v0, Env.get_cons_zero, hlOut.2]; exact Nat.le_add_right _ 1,
         fun tup sIdx htup hs => by simp only [Expr.eval, Option.some.injEq] at htup; subst htup; simp at hs⟩ (Nat.le_refl 0))
  · refine potInvFS_ret ⟨by simp [Expr.eval, Expr.v1, ρ₀], fun _ => by simp [Expr.eval, Expr.v1, ρ₀],
      fun _ => by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero, ρ₀]; exact Nat.le_add_right _ 1,
      fun tup sIdx htup hs => ?_⟩ (Nat.le_refl 0)
    simp only [some_eval, pair_eval, Option.some.injEq] at htup; subst htup; dsimp only [Expr.eval] at hcEnt hs
    simp only [mbHsCache, Expr.eval, Expr.v0, Env.get_cons_zero, ρ₀] at hcEnt
    cases hCaAt : (hE.eval ρ).1 (tE.eval ρ) with
    | none => simp [hCaAt] at hcEnt
    | some fullEnt =>
      simp only [hCaAt] at hcEnt; split_ifs at hcEnt with hEqT
      · simp only [Option.some.injEq] at hcEnt; subst hcEnt; split at hs
        · cases hs
        · next s' hs' =>
          simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Sum.inr.injEq] at hs hs'
          subst hs; exact hCa (tE.eval ρ) fullEnt s' hCaAt hs'

private theorem fsMultiBucketAuthFsRecvC_inact (idx q B Δcka qep : ℕ) (gMain la : Bool)
    (tL : Option ℕ) (par : Bool) (hinact : InactCond idx (q + 1) qep gMain tL par)
    {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (rsvE : Expr OO Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO Γ' hdrTy) (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy))
    (ρ : Env Γ') (hrsv : ∀ sIdx, rsvE.eval ρ = .inr sIdx → ActiveSlot (q + 1) qep gMain tL par sIdx) :
    PotOKInvFS (sessPred idx)
      (fun res => res.2.1 = (hE.eval ρ).1 ∧ res.2.2.2.1 = (hE.eval ρ).2.2.1 ∧
        (∀ tup sIdx, res.1 = some (some tup) → tup.1 = .inr sIdx → ActiveSlot (q + 1) qep gMain tL par sIdx))
      (fun _ => 0) ((fsMultiBucketAuthFsRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (q + 1) B la Δcka hE ctxE pE tE rsvE hdrE eE recE).eval ρ) 0 := by
  unfold fsMultiBucketAuthFsRecvC; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => potInvFS_caseOpt
    (fun _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v1], by simp [Expr.eval, Expr.v1], fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
    (fun _ _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v2], by simp [Expr.eval, Expr.v2], fun tup _ htup hs => by
      simp only [some_eval, pair_eval, Option.some.injEq] at htup; subst htup; simp [Expr.eval] at hs⟩ (Nat.le_refl 0)))
    (fun sIdx hsIdx => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hsIdx; have hAct := hrsv sIdx hsIdx; rw [eval_bind]
  refine PotOKInvFS.bindPot (Inv₁ := fun okh => okh.2.1 = (hE.eval ρ).1 ∧ okh.2.2.2.1 = (hE.eval ρ).2.2.1) (B₁ := fun _ => 0)
    ?_ (fun okh hokh => ?_)
  · refine potInvFS_caseOpt (fun _ => ?_)
      (fun _ _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v2], by simp [Expr.eval, Expr.v2]⟩ (Nat.le_refl 0))
    refine potInvFS_ite (fun _ => ?_)
      (fun _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v1], by simp [Expr.eval, Expr.v1]⟩ (Nat.le_refl 0))
    rw [eval_bind]
    exact PotOKInvFS.bindPot
      (potInvMultiFS_query_inactive idx hinact FSHdrTag.cs _ _ (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hAct))
      (fun _ _ => potInvFS_caseOpt
        (fun _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v2], by simp [Expr.eval, Expr.v2]⟩ (Nat.le_refl 0))
        (fun _ _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v3], by simp [Expr.eval, Expr.v3]⟩ (Nat.le_refl 0)))
  · refine potInvFS_ite
      (fun _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v0, hokh.1], by simp [Expr.eval, Expr.v0, hokh.2], fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
      (fun _ => ?_)
    rw [eval_bind]
    refine PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => 0)
      (potInvFS_caseOpt
        (fun _ => potInvMultiFS_query_inactive idx hinact FSHdrTag.ij _ _ (by simpa [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero] using hAct))
        (fun _ _ => potInvMultiFS_query_inactive idx hinact FSHdrTag.dl _ _ (by simpa [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero] using hAct)))
      (fun _ _ => potInvFS_caseOpt
        (fun _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v1, hokh.1], by simp [Expr.eval, Expr.v1, hokh.2], fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
        (fun _ _ => potInvFS_caseSum
          (fun _ _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v3, hokh.1], by simp [Expr.eval, Expr.v3, hokh.2], fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
          (fun _ _ => potInvFS_ite
            (fun _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v3, hokh.1], by simp [Expr.eval, Expr.v3, hokh.2], fun _ _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
            (fun _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v3, hokh.1], by simp [Expr.eval, Expr.v3, hokh.2], fun tup sIdx' htup hs' => ?_⟩ (Nat.le_refl 0)))))
    dsimp only [Expr.eval] at htup; split at htup
    · split at htup
      · cases htup
      · simp only [Option.some.injEq] at htup; subst htup
        simp only [Expr.eval, Expr.v5, Env.get_cons_succ, Env.get_cons_zero, Sum.inr.injEq] at hs'; subst hs'; exact hAct
    · simp only [Option.some.injEq] at htup; subst htup
      simp only [Expr.eval, Expr.v5, Env.get_cons_succ, Env.get_cons_zero, Sum.inr.injEq] at hs'; subst hs'; exact hAct

private theorem vRecvStep1C_inact (idx q B Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ)
    (par la : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' mVpTy) (cE : Expr OO Γ' hdrCtTy) (ρ : Env Γ')
    (hVp : VpAct q qep gMain tL par (sE.eval ρ)) (hCa : CacheAct q qep gMain tL par (hE.eval ρ))
    (hses : gMain = false → ((hE.eval ρ).2.2.1 (cE.eval ρ).1.1).length < q) :
    PotOKInvFS (sessPred idx)
      (fun res => res.2.1 = (hE.eval ρ).1 ∧ (gMain = true → res.2.2.2.1 = (hE.eval ρ).2.2.1) ∧
        (∀ τ, (res.2.2.2.1 τ).length ≤ ((hE.eval ρ).2.2.1 τ).length + 1) ∧
        (∀ s1, res.1 = some (some s1) → s1.1 = (sE.eval ρ).1 ∧ (sE.eval ρ).2.2.2.2.2.2 ≤ s1.2.2.2.2.2.2 ∧ VpAct q qep gMain tL par s1))
      (fun _ => 0) ((vRecvStep1C (hkMBE (q + 1) B Δcka qep gMain tL par la) hE ctxE pE sE cE).eval ρ) 0 := by
  unfold vRecvStep1C; rw [eval_bind_ret]; refine potInvFS_ite (fun hEqT => ?_) (fun _ => ?_)
  · have ht0Ge : (sE.eval ρ).2.2.2.2.2.2 ≤ (cE.eval ρ).1.1 := by
      simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero, decide_eq_true_eq] at hEqT
      exact Nat.le_of_lt (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hEqT.symm)
    refine potInvFS_caseOpt
      (fun _ => potInvFS_ret ⟨rfl, fun _ => rfl, fun _ => Nat.le_add_right _ 1, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
      (fun Tn _ => ?_)
    dsimp only [hooksFSMultiBucketAuthC]; rw [eval_bind]
    have hSR := fsMultiBucketAuthStartRecvC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) idx q Δcka qep gMain tL par (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1))
      (.fst (.snd (.snd .v1))) (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
      (vpΓ (.fst (.snd (.snd (.snd .v1))))) (vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
      (.cons Tn (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ) ρ)) hCa hses
    simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hSR
    refine PotOKInvFS.bindPot hSR (fun srOut hSROut => potInvFS_caseOpt
      (fun _ => potInvFS_ret ⟨hSROut.1, hSROut.2.1, hSROut.2.2.1, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
      (fun opt1 hopt1 => potInvFS_caseOpt
        (fun _ => potInvFS_ret ⟨hSROut.1, hSROut.2.1, hSROut.2.2.1, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
        (fun tup htup => potInvFS_ret ⟨hSROut.1, hSROut.2.1, hSROut.2.2.1, fun s1 hs1 => ?_⟩ (Nat.le_refl 0))))
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hopt1 htup
    dsimp only [Expr.eval] at hs1; injection hs1 with hs1'; injection hs1' with hs1''; subst hs1''
    rw [vpMk, pair_eval, pair_eval, pair_eval, pair_eval, pair_eval, pair_eval, tset_eval_val]
    refine ⟨rfl, ht0Ge, ⟨hVp.1, fun τ sIdx hvr => ?_⟩⟩
    by_cases hτ : τ = (cE.eval ρ).1.1
    · subst hτ; simp only [Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ, ↓reduceIte, Option.some.injEq] at hvr
      exact hSROut.2.2.2 tup sIdx (by rw [hopt1, htup]) hvr
    · simp only [vpVR, Expr.eval, Expr.v4, Env.get_cons_zero, Env.get_cons_succ, hτ, ↓reduceIte] at hvr; exact hVp.2 τ sIdx hvr
  · refine potInvFS_ret ⟨rfl, fun _ => rfl, fun _ => Nat.le_add_right _ 1, fun s1 hs1 => ?_⟩ (Nat.le_refl 0)
    simp only [Option.some.injEq, Expr.eval, Expr.v0, Env.get_cons_zero] at hs1; subst hs1; exact ⟨rfl, Nat.le_refl _, hVp⟩

private theorem vRecvC_inact (idx q B Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ)
    (par la : Bool) (hinact : InactCond idx (q + 1) qep gMain tL par) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' mVpTy) (cE : Expr OO Γ' hdrCtTy) (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ')
    (hVp : VpAct q qep gMain tL par (sE.eval ρ)) (hCa : CacheAct q qep gMain tL par (hE.eval ρ))
    (hses : gMain = false → ((hE.eval ρ).2.2.1 (cE.eval ρ).1.1).length < q) :
    PotOKInvFS (sessPred idx)
      (fun res => CacheAct q qep gMain tL par res.2 ∧ (gMain = true → res.2.2.2.1 = (hE.eval ρ).2.2.1) ∧
        (∀ τ, (res.2.2.2.1 τ).length ≤ ((hE.eval ρ).2.2.1 τ).length + 1) ∧
        (∀ tup, res.1 = some (some tup) → tup.1.1 = (sE.eval ρ).1 ∧
          (sE.eval ρ).2.2.2.2.2.2 ≤ tup.1.2.2.2.2.2.2 ∧ VpAct q qep gMain tL par tup.1))
      (fun _ => 0) ((vRecvC (hkMBE (q + 1) B Δcka qep gMain tL par la) hE ctxE pE sE cE recE).eval ρ) 0 := by
  unfold vRecvC; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => potInvFS_ret ⟨hCa, fun _ => rfl, fun _ => Nat.le_add_right _ 1, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0)) (fun _ => ?_)
  rw [eval_bind]
  have hStep1 := vRecvStep1C_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
    (sampK := sampK) idx q B Δcka qep gMain tL par la (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))
    (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd (.snd .v0)))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ) hVp hCa hses
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hStep1
  refine PotOKInvFS.bindPot hStep1 (fun step1Out hS1 => ?_)
  have hCa1 : CacheAct q qep gMain tL par step1Out.2 := fun τ e sIdx hτ he => hCa τ e sIdx (hS1.1 ▸ hτ) he
  refine potInvFS_caseOpt (fun _ => potInvFS_ret ⟨hCa1, hS1.2.1, hS1.2.2.1, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
    (fun step1In hsIn => potInvFS_caseOpt (fun _ => potInvFS_ret ⟨hCa1, hS1.2.1, hS1.2.2.1, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0)) (fun s1 hs1 => ?_))
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hsIn hs1
  obtain ⟨hs1Id, hs1Ge, hs1Vp⟩ := hS1.2.2.2 s1 (by rw [hsIn, hs1])
  refine potInvFS_caseOpt (fun _ => potInvFS_ret ⟨hCa1, hS1.2.1, hS1.2.2.1, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0)) (fun v hv => ?_)
  simp only [vpVR, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hv; dsimp only [hooksFSMultiBucketAuthC]; rw [eval_bind]
  have hFR := fsMultiBucketAuthFsRecvC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) idx q B Δcka qep gMain la tL par hinact (.snd (Expr.v3 (O := OO))) (.fst (.snd .v4))
    (.fst (.snd (.snd .v4))) (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))) .v0
    (.fst (.fst (.snd (.snd (.snd (.snd .v4)))))) (.snd (.fst (.snd (.snd (.snd (.snd .v4)))))) (.snd (.snd (.snd (.snd (.snd .v4)))))
    (.cons v (.cons s1 (.cons step1In (.cons step1Out (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ)))))
    (fun sIdx hvr => hs1Vp.2 (cE.eval ρ).1.1 sIdx (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hvr; rw [hv, hvr]))
  simp only [Expr.eval, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hFR
  refine PotOKInvFS.bindPot hFR (fun frOut hFROut => ?_)
  have hCa2 : CacheAct q qep gMain tL par frOut.2 := fun τ e sIdx hτ he => hCa1 τ e sIdx (hFROut.1 ▸ hτ) he
  have hMain2 : gMain = true → frOut.2.2.2.1 = (hE.eval ρ).2.2.1 := fun hg => hFROut.2.1.trans (hS1.2.1 hg)
  have hLen2 : ∀ τ, (frOut.2.2.2.1 τ).length ≤ ((hE.eval ρ).2.2.1 τ).length + 1 := fun τ => by rw [hFROut.2.1]; exact hS1.2.2.1 τ
  refine potInvFS_caseOpt (fun _ => potInvFS_ret ⟨hCa2, hMain2, hLen2, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
    (fun frIn hfrIn => potInvFS_caseOpt (fun _ => potInvFS_ret ⟨hCa2, hMain2, hLen2, fun _ h => by simp [Expr.eval] at h⟩ (Nat.le_refl 0))
      (fun outTup houtTup => potInvFS_ret ⟨hCa2, hMain2, hLen2, fun tup htup => ?_⟩ (Nat.le_refl 0)))
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hfrIn houtTup
  dsimp only [Expr.eval] at htup; injection htup with htup'; injection htup' with htup''; subst htup''
  rw [vpSetVR, letE_eval, pair_eval, vpMk, pair_eval, pair_eval, pair_eval, pair_eval, pair_eval, pair_eval, tset_eval_val]
  refine ⟨hs1Id, hs1Ge, ⟨hs1Vp.1, fun τ sIdx hvr => ?_⟩⟩
  by_cases hτ : τ = (cE.eval ρ).1.1
  · subst hτ; simp only [vpVR, Expr.eval, Expr.v0, Expr.v4, Expr.v7, Env.get_cons_zero, Env.get_cons_succ, ↓reduceIte, Option.some.injEq] at hvr
    exact hFROut.2.2 outTup sIdx (by rw [hfrIn, houtTup]) hvr
  · simp only [vpVR, Expr.eval, Expr.v0, Expr.v4, Expr.v7, Env.get_cons_zero, Env.get_cons_succ, hτ, ↓reduceIte] at hvr
    exact hs1Vp.2 τ sIdx hvr

private theorem fsMultiBucketAuthRevealC_inact (idx q qep : ℕ) (gMain la : Bool)
    (tL : Option ℕ) (par : Bool) (hinact : InactCond idx (q + 1) qep gMain tL par)
    {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) (ρ : Env Γ') (hVp : VpAct q qep gMain tL par (vpE.eval ρ)) :
    PotOKInvFS (sessPred idx) (fun res => res.2.1 = (hE.eval ρ).1 ∧ res.2.2.2.1 = (hE.eval ρ).2.2.1)
      (fun _ => 0) ((fsMultiBucketAuthRevealC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (q + 1) gMain la tL hE ctxE pE vpE).eval ρ) 0 := by
  unfold fsMultiBucketAuthRevealC; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => potInvFS_ret ⟨rfl, rfl⟩ (Nat.le_refl 0)) (fun _ => ?_); rw [eval_bind]
  refine PotOKInvFS.bindPot (Inv₁ := fun sh => sh.2.1 = (hE.eval ρ).1 ∧ sh.2.2.2.1 = (hE.eval ρ).2.2.1)
    (B₁ := fun _ => 0) ?_ (fun sh hsh => ?_)
  · refine potInvFS_caseOpt (fun _ => potInvFS_ret ⟨rfl, rfl⟩ (Nat.le_refl 0)) (fun ssv hssv => potInvFS_caseSum
      (fun _ _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v2], by simp [Expr.eval, Expr.v2]⟩ (Nat.le_refl 0)) (fun sIdx hsIdx => ?_))
    simp only [vpVS, Expr.eval, Expr.v0, Env.get_cons_zero] at hssv hsIdx; have hAct := hVp.1 sIdx (by rw [hssv, hsIdx]); rw [eval_bind]
    exact PotOKInvFS.bindPot
      (potInvMultiFS_query_inactive idx hinact FSHdrTag.cs _ _ (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hAct))
      (fun _ _ => potInvFS_caseOpt
        (fun _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v3], by simp [Expr.eval, Expr.v3]⟩ (Nat.le_refl 0))
        (fun _ _ => potInvFS_ret ⟨by simp [Expr.eval, Expr.v4], by simp [Expr.eval, Expr.v4]⟩ (Nat.le_refl 0)))
  · refine potInvFS_caseOpt (fun _ => potInvFS_ret hsh (Nat.le_refl 0)) (fun _ _ => ?_); rw [eval_bind]
    exact PotOKInvFS.bindPot (potInvMultiFS_zero idx _ _ (by simp [rangeListBucketC, Comp.queries]))
      (fun _ _ => potInvFS_ite (fun _ => potInvFS_ret hsh (Nat.le_refl 0)) (fun _ => potInvFS_ret hsh (Nat.le_refl 0)))

private theorem mbEsInv_after_recv {q qep : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool}
    {m : ℕ} {es0 : (esTy mVpTy mbHsTy).denote} {h' : (mbHsTy).denote}
    {p0 : Bool} {st' : (mVpTy).denote} {g' : (cGsTy mVpTy).denote}
    (hes0 : MbEsInv q qep gMain tL par (m + 1) es0) (hCa' : CacheAct q qep gMain tL par h')
    (hMain' : gMain = true → h'.2.2.1 = es0.2.1.2.2.1)
    (hLen' : ∀ τ, (h'.2.2.1 τ).length ≤ (es0.2.1.2.2.1 τ).length + 1)
    (hg' : g'.1 = if p0 then (es0.1.1.1, st') else (st', es0.1.1.2))
    (hstId : st'.1 = (if p0 then es0.1.1.2 else es0.1.1.1).1)
    (hstGe : (if p0 then es0.1.1.2 else es0.1.1.1).2.2.2.2.2.2 ≤ st'.2.2.2.2.2.2)
    (hstVp : VpAct q qep gMain tL par st') : MbEsInv q qep gMain tL par m (g', h', es0.2.2) := by
  intro hab; obtain ⟨hAId, hBId, hVpA, hVpB, _, hSes⟩ := hes0 hab; rw [hg']
  cases p0
  · simp only [Bool.false_eq_true, ↓reduceIte] at hstId hstGe ⊢
    refine ⟨hstId.trans hAId, hBId, hstVp, hVpB, hCa', ?_⟩; unfold SessBound at hSes ⊢; cases hg : gMain
    · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hSes ⊢; intro τ; have h1 := hLen' τ; have h2 := hSes τ; omega
    · simp only [hg, ↓reduceIte] at hSes ⊢; rw [hMain' hg]; exact ⟨fun τ hlt hA => hSes.1 τ (Nat.lt_of_le_of_lt hstGe hlt) hA, hSes.2⟩
  · simp only [↓reduceIte] at hstId hstGe ⊢
    refine ⟨hAId, hstId.trans hBId, hVpA, hstVp, hCa', ?_⟩; unfold SessBound at hSes ⊢; cases hg : gMain
    · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hSes ⊢; intro τ; have h1 := hLen' τ; have h2 := hSes τ; omega
    · simp only [hg, ↓reduceIte] at hSes ⊢; rw [hMain' hg]; exact ⟨hSes.1, fun τ hlt hB => hSes.2 τ (Nat.lt_of_le_of_lt hstGe hlt) hB⟩

private theorem commitEC_inact (idx q B Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ)
    (par la : Bool) {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy mbHsTy))
    (sE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (oldE newE : Expr OO Γ' mVpTy) (posE : Expr OO Γ' posTy) (ρ : Env Γ') :
    PotOKInvFS (sessPred idx)
      (fun p => ∃ accG, p.1 = some accG ∧
        accG.1 = (if pE.eval ρ then ((sE.eval ρ).1.1, newE.eval ρ) else (newE.eval ρ, (sE.eval ρ).1.2)) ∧
        p.2 = ((esE.eval ρ).1, (esE.eval ρ).2.1, (esE.eval ρ).2.2))
      (fun _ => 0) ((commitEC (hkMBE (q + 1) B Δcka qep gMain tL par la) (q + 1) esE sE pE oldE newE posE).eval ρ) 0 := by
  unfold commitEC hooksFSMultiBucketAuthC fsMultiBucketAuthCommitC; dsimp only; rw [eval_bind_ret, eval_bind, eval_ret, pure_bind]
  refine potInvFS_caseOpt (fun hN => by simp [Expr.eval, Expr.v0, Env.get_cons_zero] at hN) (fun new' hNew => potInvFS_ret ?_ (Nat.le_refl 0))
  simp only [Option.some.injEq, Expr.eval, Expr.v0, Env.get_cons_zero] at hNew; subst hNew
  refine ⟨_, rfl, ?_, by simp [esMk, esG, esH, esAbort, Expr.eval, Expr.v0, Expr.v1, Expr.v2]⟩; rw [cGsSetStP_st_fs]
  simp only [Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, cAcceptE_st_fs]; cases pE.eval ρ <;> rfl

private theorem ite_st_eq {P : Prop} {_ : Decidable P} {g1 g2 : (cGsTy mVpTy).denote}
    (h1 : g1.1 = g2.1) : (@ite _ P ‹Decidable P› g1 g2).1 = g2.1 := by
  cases ‹Decidable P› <;> [rfl; exact h1]

private theorem deliverEC_inact (idx q B Δcka qep maxSkip : ℕ) (gMain : Bool) (tL : Option ℕ)
    (par la : Bool) (cfg : ConfigEC OO) (hinact : InactCond idx (q + 1) qep gMain tL par)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy mbHsTy))
    (argE : Expr OO Γ' (.prod .bool hdrCtTy)) (ρ : Env Γ') (m : ℕ)
    (hInv : MbEsInv q qep gMain tL par (m + 1) (esE.eval ρ)) :
    PotOKInvFS (sessPred idx) (fun x => MbEsInv q qep gMain tL par m x.2) (fun _ => 0)
      ((deliverEC (hkMBE (q + 1) B Δcka qep gMain tL par la) (q + 1) maxSkip cfg esE argE).eval ρ) 0 := by
  unfold deliverEC; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => potInvFS_ret (mbEsInv_step_noop hInv) (Nat.le_refl 0))
    (fun hNotOr => potInvFS_caseOpt (fun _ => potInvFS_ret (mbEsInv_step_noop hInv) (Nat.le_refl 0)) (fun r1 _ => ?_))
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE_eval, Bool.or_eq_false_iff, esAbort, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotOr; exact hNotOr.1
  obtain ⟨_, _, hVpA, hVpB, hCa, hSes⟩ := hInv hab; rw [eval_bind]
  have hpVp : VpAct q qep gMain tL par (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
    cases (argE.eval ρ).1 <;> simp [hVpA, hVpB]
  have hses0 : gMain = false → ((esE.eval ρ).2.1.2.2.1 (argE.eval ρ).2.1.1).length < q := by
    intro hg; unfold SessBound at hSes; simp only [hg, Bool.false_eq_true, ↓reduceIte] at hSes; have h1 := hSes (argE.eval ρ).2.1.1; omega
  have hRecv := vRecvC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
    (sampK := sampK) idx q B Δcka qep gMain tL par la hinact (esH (.fst (Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
    (.cons r1 (.cons ((esE.pair argE).eval ρ) ρ))
    (by rw [pGet_eval_st_fs]; dsimp only [cGsSt, esG, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]; exact hpVp) hCa hses0
  simp only [pGet_eval_st_fs, cGsSt, esG, esH, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hRecv
  refine PotOKInvFS.bindPot hRecv (fun recvOut hROut => potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun hab' => by simp [esMk, Expr.eval, Expr.v0] at hab') (Nat.le_refl 0))
    (fun resIn hresIn => potInvFS_caseOpt (fun _ => potInvFS_ret ?_ (Nat.le_refl 0)) (fun tup htup => ?_)))
  · simp only [esSetG, esSetH, letE_eval, esMk, esH, esAbort, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
    exact mbEsInv_after_recv (p0 := (argE.eval ρ).1) (st' := if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)
      hInv hROut.1 hROut.2.1 hROut.2.2.1
      ((ite_st_eq (cGsSetWin_st_fs _ _ _)).trans (by cases (argE.eval ρ).1 <;> simp [esG, Expr.eval, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]))
      rfl (Nat.le_refl _) hpVp
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hresIn htup
    obtain ⟨htId, htGe, htVp⟩ := hROut.2.2.2 tup (by rw [hresIn, htup]); rw [eval_bind]
    refine PotOKInvFS.bindPot (commitEC_inact idx q B Δcka qep gMain tL par la _ _ _ _ _ _ _)
      (fun comOut ⟨accG, hCom1, hCom2, hCom3⟩ => ?_)
    simp only [esSetH, letE_eval, pair_eval, esMk, esG, esAbort, Expr.eval, Expr.v2, Expr.v4, Env.get_cons_zero, Env.get_cons_succ] at hCom3
    refine potInvFS_caseOpt (fun hN => by simp [Expr.eval, Expr.v0, Env.get_cons_zero, hCom1] at hN) (fun sAcc hsAcc => potInvFS_ret ?_ (Nat.le_refl 0))
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero, hCom1, Option.some.injEq] at hsAcc; subst hsAcc
    simp only [esSetG, letE_eval, esMk, esH, esAbort, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]; rw [hCom3]; dsimp only
    exact mbEsInv_after_recv (p0 := (argE.eval ρ).1) (st' := tup.1) hInv hROut.1 hROut.2.1 hROut.2.2.1
      ((ite_st_eq (cGsSetWin_st_fs _ _ _)).trans (by simpa [esG, Expr.eval, Expr.v0, Expr.v4] using hCom2)) htId htGe htVp

private theorem injectEC_inact (idx q B Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ)
    (par la : Bool) (cfg : ConfigEC OO) (hinact : InactCond idx (q + 1) qep gMain tL par)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy mbHsTy))
    (argE : Expr OO Γ' (.prod .bool hdrCtTy)) (ρ : Env Γ') (m : ℕ)
    (hInv : MbEsInv q qep gMain tL par (m + 1) (esE.eval ρ)) :
    PotOKInvFS (sessPred idx) (fun x => MbEsInv q qep gMain tL par m x.2) (fun _ => 0)
      ((injectEC (hkMBE (q + 1) B Δcka qep gMain tL par la) (q + 1) (2 + Δcka) qep cfg esE argE).eval ρ) 0 := by
  unfold injectEC; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => potInvFS_ret (mbEsInv_step_noop hInv) (Nat.le_refl 0)) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE_eval, Bool.or_eq_false_iff, esAbort, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotRef; exact hNotRef.1
  obtain ⟨_, _, hVpA, hVpB, hCa, hSes⟩ := hInv hab; rw [eval_bind]
  have hpVp : VpAct q qep gMain tL par (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
    cases (argE.eval ρ).1 <;> simp [hVpA, hVpB]
  have hses0 : gMain = false → ((esE.eval ρ).2.1.2.2.1 (argE.eval ρ).2.1.1).length < q := by
    intro hg; unfold SessBound at hSes; simp only [hg, Bool.false_eq_true, ↓reduceIte] at hSes; have h1 := hSes (argE.eval ρ).2.1.1; omega
  have hRecv := vRecvC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
    (sampK := sampK) idx q B Δcka qep gMain tL par la hinact (esH (.fst (Expr.v0 (O := OO)))) (esG (.fst .v0))
    (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none (.cons ((esE.pair argE).eval ρ) ρ)
    (by rw [pGet_eval_st_fs]; dsimp only [cGsSt, esG, Expr.eval, Expr.v0, Env.get_cons_zero]; exact hpVp) hCa hses0
  simp only [pGet_eval_st_fs, cGsSt, esG, esH, Expr.eval, Expr.v0, Env.get_cons_zero] at hRecv
  refine PotOKInvFS.bindPot hRecv (fun recvOut hROut => ?_)
  have hNoCommit : ∀ g' : (cGsTy mVpTy).denote, g'.1 = (esE.eval ρ).1.1 →
      MbEsInv q qep gMain tL par m (g', recvOut.2, (esE.eval ρ).2.2) := fun g' hg' =>
    mbEsInv_after_recv (p0 := (argE.eval ρ).1) (st' := if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)
      hInv hROut.1 hROut.2.1 hROut.2.2.1 (by rw [hg']; cases (argE.eval ρ).1 <;> rfl) rfl (Nat.le_refl _) hpVp
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun hab' => by simp [esMk, Expr.eval, Expr.v0] at hab') (Nat.le_refl 0))
    (fun resIn hresIn => potInvFS_caseOpt (fun _ => potInvFS_ret ?_ (Nat.le_refl 0)) (fun tup htup => ?_))
  · simp only [esSetH, letE_eval, pair_eval, esMk, esG, esAbort, Expr.eval, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
    exact hNoCommit (esE.eval ρ).1 rfl
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hresIn htup
    obtain ⟨htId, htGe, htVp⟩ := hROut.2.2.2 tup (by rw [hresIn, htup])
    refine potInvFS_ite (fun _ => potInvFS_ret ?_ (Nat.le_refl 0)) (fun _ => potInvFS_ite (fun _ => ?_) (fun _ => ?_))
    · simp only [esSetH, letE_eval, pair_eval, esMk, esG, esAbort, Expr.eval, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
      exact hNoCommit (esE.eval ρ).1 rfl
    · rw [eval_bind]
      refine PotOKInvFS.bindPot (commitEC_inact idx q B Δcka qep gMain tL par la _ _ _ _ _ _ _)
        (fun comOut ⟨accG, hCom1, hCom2, hCom3⟩ => ?_)
      simp only [esSetH, letE_eval, pair_eval, esMk, esG, esAbort, Expr.eval, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hCom3
      refine potInvFS_caseOpt (fun hN => by simp [Expr.eval, Expr.v0, Env.get_cons_zero, hCom1] at hN) (fun sAcc hsAcc => potInvFS_ret ?_ (Nat.le_refl 0))
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero, hCom1, Option.some.injEq] at hsAcc; subst hsAcc
      simp only [esSetG, letE_eval, pair_eval, esMk, esH, esAbort, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, hCom3]
      exact mbEsInv_after_recv (p0 := (argE.eval ρ).1) (st' := tup.1) hInv hROut.1 hROut.2.1 hROut.2.2.1
        (by simpa [esG, Expr.eval, Expr.v0, Expr.v3] using hCom2) htId htGe htVp
    · refine potInvFS_ret ?_ (Nat.le_refl 0)
      simp only [esSetG, esSetH, letE_eval, pair_eval, esMk, esH, esAbort, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
      refine hNoCommit _ ?_; split_ifs <;> simp [cGsSetWin_st_fs, esG, Expr.eval, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]

private theorem initFSMultiBucketAuthEStateC_inact (idx q Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ' : List (Ty SP)} (bE : Expr OO Γ' .bool) (ρ : Env Γ') :
    PotOKInvFS (sessPred idx) (fun es => MbEsInv q qep gMain tL par q es) (fun _ => 0)
      ((initFSMultiBucketAuthEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) (q + 1) Δcka qep gMain tL par bE).eval ρ) 0 := by
  unfold initFSMultiBucketAuthEStateC; rw [eval_bind_ret, eval_bind]
  refine PotOKInvFS.bindPot (potInvMultiFS_zero idx _ _ rfl) (fun kr _ => ?_); rw [eval_bind]
  refine PotOKInvFS.bindPot (potInvMultiFS_zero idx _ _ rfl) (fun kc _ => ?_); rw [eval_bind]
  set ρ₁ := Env.cons (t := .base CryptoGames.CKA.CKASort.kc) kc (Env.cons (t := .base CryptoGames.CKA.CKASort.kr) kr (.cons (bE.eval ρ) ρ))
  have hR := rootFSMultiBucketAuthC_inact (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) idx (q + 1) Δcka qep tL par (mbHsEmptyE (O := OO)) (.nat 0) (.bool false)
    (Expr.op (O := OO) CKAOp.lamI .unit) (Expr.op (O := OO) CKAOp.prngInit .v1) ρ₁
  have hEmptyCa : ((mbHsEmptyE (O := OO)).eval ρ₁).1 = fun _ => none := rfl
  have hEmptySes : ((mbHsEmptyE (O := OO)).eval ρ₁).2.2.1 = fun _ => [] := rfl
  simp only [Expr.eval] at hR
  refine PotOKInvFS.bindPot (Inv₂ := fun es => MbEsInv q qep gMain tL par q es) hR (fun rOut hrOut => potInvFS_ret ?_ (Nat.le_refl 0))
  set ρ₂ := Env.cons rOut ρ₁; unfold MbEsInv; intro _; cases hg : gMain
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨by simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, partyEnc, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁],
      by simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, partyEnc, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁],
      ⟨fun _ h => by simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁] at h,
       fun τ _ h => by by_cases hτ : τ = 0 <;> simp [hτ, esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, tset_eval_val, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁] at h⟩,
      ⟨fun _ h => by simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁] at h,
       fun _ _ h => by simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁] at h⟩,
      (fun τ e _ hτ _ => by simp only [esMk, pair_eval, Expr.eval, Expr.v0, Env.get_cons_zero, ρ₂] at hτ; rw [hrOut.1, hEmptyCa] at hτ; cases hτ), ?_⟩
    unfold SessBound; simp only [Bool.false_eq_true, ↓reduceIte, esMk, pair_eval, Expr.eval, Expr.v0, Env.get_cons_zero, ρ₂]; intro τ; rw [hrOut.2.1, hEmptySes]; simp
  · simp only [↓reduceIte]
    have hReg := regSessOptMultiBucketE_inact q qep true tL par (.snd (Expr.v0 (O := OO))) (.nat 0) (.snd (.snd (.fst .v0))) ρ₂
    have hr2 : (Expr.snd (O := OO) .v0).eval ρ₂ = rOut.2 := rfl
    have hsid2 : (Expr.snd (O := OO) (.snd (.fst .v0))).eval ρ₂ = rOut.1.2.2 := rfl
    have ht0 : (Expr.nat (O := OO) 0).eval ρ₂ = 0 := rfl
    rw [hr2, hsid2, ht0] at hReg
    have hOptAct : ∀ sIdx, ((regSessOptMBE (q + 1) true tL (.snd (Expr.v0 (O := OO))) (.nat 0) (.snd (.snd (.fst .v0)))).eval ρ₂).1 = some sIdx →
        ActiveSlot (q + 1) qep true tL par sIdx := by
      intro sIdx hs; cases hsid : rOut.1.2.2 with
      | none => rw [(hReg.2.1 hsid).1] at hs; cases hs
      | some ik => obtain ⟨htTop, htH, hpar⟩ := hrOut.2.2 ik hsid; exact hReg.2.2.2.2 sIdx hs htTop htH hpar (by simp [hrOut.2.1, hEmptySes])
    refine ⟨by simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, partyEnc, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁],
      by simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, partyEnc, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁],
      ⟨fun _ h => by simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁] at h,
       fun τ sIdx h => ?_⟩,
      ⟨fun sIdx h => ?_,
       fun _ _ h => by simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁] at h⟩,
      (fun τ e _ hτ _ => by dsimp only [esMk, pair_eval, Expr.eval, Env.get_cons_zero, ρ₂] at hτ; rw [hReg.1, hrOut.1, hEmptyCa] at hτ; cases hτ), ?_⟩
    · by_cases hτ : τ = 0
      · subst hτ; simp only [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, tset_eval_val,
          ↓reduceIte, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, Option.some.injEq, ρ₂, ρ₁] at h
        split at h <;> [cases h; next s' hs' => simp only [Sum.inr.injEq] at h; subst h; exact hOptAct s' hs']
      · simp [hτ, esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, tset_eval_val, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ρ₂, ρ₁] at h
    · simp only [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, pair_eval, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, Option.some.injEq, ρ₂, ρ₁] at h
      split at h <;> [cases h; next s' hs' => simp only [Sum.inr.injEq] at h; subst h; exact hOptAct s' hs']
    · unfold SessBound; simp only [↓reduceIte]; dsimp only [esMk, pair_eval, Expr.eval, Env.get_cons_zero]
      have hGt0 : ∀ τ, 0 < τ → ((regSessOptMBE (q + 1) true tL (.snd (Expr.v0 (O := OO))) (.nat 0) (.snd (.snd (.fst .v0)))).eval ρ₂).2.2.2.1 τ = [] :=
        fun τ hpos => by rw [hReg.2.2.1 τ (Nat.ne_of_gt hpos), hrOut.2.1, hEmptySes]
      exact ⟨fun τ hpos _ => hGt0 τ hpos, fun τ hpos _ => hGt0 τ hpos⟩

/-- Inactive-slot `0`-query bound for `redFSAuthMultiBucketProg`. -/
theorem redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero_gen
    (q B Δcka qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (idx : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : MakesAtMostQueries A q)
    (hinact : idx ≥ ((qep + 2) - healEpoch tL) * (q + 1) ∨
      ¬(decide (idx % (q + 1) = 0) = gMain ∧
        decide (Party.senderOf (healEpoch tL + idx / (q + 1)) == .A) = par)) :
    ((redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        (q + 1) B Δcka qep maxSkip gMain la tL par).eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = idx)) = true) 0 := by
  let R := redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    (q + 1) B Δcka qep maxSkip gMain la tL par
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := _root_.CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) q :=
    hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl])
  change (R.init.eval (.cons () .nil) >>= fun (a, st) =>
      (simulateQ (handlerImpl (C := _) R.handle) A).run st >>= fun (b, st') =>
        R.finish.eval (.cons st' (.cons b .nil))).IsQueryBoundP (sessPred idx) 0
  have hInit : PotOKInvFS (sessPred idx) (fun as => MbEsInv q qep gMain tL par q as.2.1) (fun _ => 0)
      (R.init.eval (.cons (t := .unit) () .nil)) 0 := by
    dsimp only [R, redFSAuthMultiBucketProg]; rw [eval_bind]
    exact PotOKInvFS.bindPot (Inv₁ := fun es => MbEsInv q qep gMain tL par q es)
      (initFSMultiBucketAuthEStateC_inact idx q Δcka qep gMain tL par (.bool false) (.cons (t := .unit) () .nil))
      (fun es hes => potInvFS_ret hes (Nat.le_refl 0))
  suffices hRun : PotOKInvFS (sessPred idx) (fun _ => True) (fun _ => 0)
      (R.init.eval (.cons (t := .unit) () .nil) >>= fun (a, st) =>
        (simulateQ (handlerImpl (C := _) R.handle) A).run st >>= fun (b, st') =>
          R.finish.eval (.cons st' (.cons b .nil))) 0 by
    simpa [bind_pure] using hRun.run (fun b => pure b) (fun _ _ => by simp [isQueryBoundP_pure])
  refine PotOKInvFS.bindPot hInit (fun ⟨a, st⟩ has => ?_)
  refine PotOKInvFS.bindPot
    (simulateQ_handlerImpl_zero_step (σ := R.σ) (P := sessPred idx)
      (fun m (s : R.σ.denote) => MbEsInv q qep gMain tL par m s.1)
      (multiIface_fwdU_zero idx) R.handle ?_ hA' st has)
    (fun bs _ => potInvMultiFS_zero idx R.finish (.cons bs.2 (.cons bs.1 .nil))
      (by simp [R, redFSAuthMultiBucketProg, Comp.queries]))
  intro m qv sv hInv; dsimp only [R, redFSAuthMultiBucketProg] at sv qv ⊢; rw [eval_bind_ret]
  apply potInvFS_caseSum
  · intro _ _; apply potInvFS_caseSum
    · intro _ _; apply potInvFS_caseSum
      · intro _ _; apply potInvFS_caseSum
        · rintro ⟨pSend, m0, r0⟩ _; rw [eval_bind_ret]
          refine potInvFS_ite (fun _ => potInvFS_ret (mbEsInv_step_noop hInv) (Nat.le_refl 0))
            (fun hNotOr => potInvFS_caseOpt (fun _ => potInvFS_ret (mbEsInv_step_noop hInv) (Nat.le_refl 0))
              (fun s1 hs1 => ?_))
          have hab : sv.1.2.2 = false := by
            simp only [orE_eval, Bool.or_eq_false_iff, esAbort, Expr.eval, Expr.v0, Expr.v5,
              Env.get_cons_succ, Env.get_cons_zero] at hNotOr; exact hNotOr.1
          obtain ⟨hAId, hBId, hVpA, hVpB, hCa, hSes⟩ := hInv hab
          have hs1St : s1.1 = sv.1.1.1 := cEpMgmtE_some_st_fs (2 + Δcka) qep (esG (.fst .v5)) (.fst .v0) _ _ hs1
          rw [eval_bind]
          have hpVp : VpAct q qep gMain tL par (if pSend then sv.1.1.1.2 else sv.1.1.1.1) := by
            cases pSend <;> simp [hVpA, hVpB]
          have hsesSend : (partyDec (if pSend then sv.1.1.1.2 else sv.1.1.1.1).1).sendsIn
                ((if pSend then sv.1.1.1.2 else sv.1.1.1.1).2.2.2.2.2.2 + 1) = true →
              if gMain then sv.1.2.1.2.2.1 ((if pSend then sv.1.1.1.2 else sv.1.1.1.1).2.2.2.2.2.2 + 1) = []
              else (sv.1.2.1.2.2.1 ((if pSend then sv.1.1.1.2 else sv.1.1.1.1).2.2.2.2.2.2 + 1)).length < q := by
            intro hs; unfold SessBound at hSes; cases hg : gMain
            · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hSes ⊢
              have h1 := hSes ((if pSend then sv.1.1.1.2 else sv.1.1.1.1).2.2.2.2.2.2 + 1); omega
            · simp only [hg, ↓reduceIte] at hSes ⊢; cases pSend
              · simp only [Bool.false_eq_true, ↓reduceIte, hAId, partyDec] at hs ⊢
                exact hSes.1 _ (Nat.lt_succ_self _) hs
              · simp only [↓reduceIte, hBId, partyDec] at hs ⊢
                exact hSes.2 _ (Nat.lt_succ_self _) hs
          refine PotOKInvFS.bindPot (vSendC_inact (sampKR := sampKR) (sampKC := sampKC)
              (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
              idx q B Δcka qep gMain tL par la hinact _ _ _ _ _ _ _ _ ?_ ?_ ?_) (fun sendOut hSOut => ?_)
          · simp only [pGet_eval_st_fs, cGsSt, hs1St, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
            exact hpVp
          · simp only [esH, Expr.eval, Expr.v6, Expr.v7, Env.get_cons_zero, Env.get_cons_succ]; exact hCa
          · simp only [pGet_eval_st_fs, cGsSt, esH, hs1St, Expr.eval, Expr.v0, Expr.v1, Expr.v6, Expr.v7,
              Env.get_cons_zero, Env.get_cons_succ]; exact hsesSend
          · simp only [pGet_eval_st_fs, cGsSt, esH, hs1St, Expr.eval, Expr.v0, Expr.v1, Expr.v6, Expr.v7,
              Env.get_cons_zero, Env.get_cons_succ] at hSOut
            refine potInvFS_caseOpt
              (fun _ => potInvFS_ret (fun hab' => by simp [esMk, Expr.eval, Expr.v0] at hab') (Nat.le_refl 0))
              (fun stCt hstCt => potInvFS_ret ?_ (Nat.le_refl 0))
            simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hstCt
            obtain ⟨hstId, hstGe, hstVp, hstMain⟩ := hSOut.2.2 stCt hstCt; intro _
            simp only [esMk, pair_eval, cRecordE_st_fs, hs1St, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v7,
              Env.get_cons_zero, Env.get_cons_succ]
            cases pSend
            · simp only [Bool.false_eq_true, ↓reduceIte, hAId] at hstId hstGe hstMain ⊢
              refine ⟨hstId, hBId, hstVp, hVpB, hSOut.1, ?_⟩; unfold SessBound at hSes ⊢
              cases hg : gMain
              · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hSes ⊢
                intro τ; have h1 := hSOut.2.1 τ; have h2 := hSes τ; omega
              · simp only [hg, ↓reduceIte] at hSes ⊢; obtain ⟨hM1, hM2⟩ := hstMain hg
                rw [hstId] at hM1 hM2; simp only [partyDec, Bool.not_false] at hM1 hM2
                exact ⟨fun τ hlt hA => (hM1 τ hlt hA).trans (hSes.1 τ (Nat.lt_of_le_of_lt hstGe hlt) hA),
                  fun τ hlt hB => (hM2 τ hB).trans (hSes.2 τ hlt hB)⟩
            · simp only [↓reduceIte, hBId] at hstId hstGe hstMain ⊢
              refine ⟨hAId, hstId, hVpA, hstVp, hSOut.1, ?_⟩; unfold SessBound at hSes ⊢
              cases hg : gMain
              · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hSes ⊢
                intro τ; have h1 := hSOut.2.1 τ; have h2 := hSes τ; omega
              · simp only [hg, ↓reduceIte] at hSes ⊢; obtain ⟨hM1, hM2⟩ := hstMain hg
                rw [hstId] at hM1 hM2; simp only [partyDec, Bool.not_true] at hM1 hM2
                exact ⟨fun τ hlt hA => (hM2 τ hA).trans (hSes.1 τ hlt hA),
                  fun τ hlt hB => (hM1 τ hlt hB).trans (hSes.2 τ (Nat.lt_of_le_of_lt hstGe hlt) hB)⟩
        · intro _ _; exact potInvFS_ret (mbEsInv_step_noop hInv) (Nat.le_refl 0)
      · intro _ _; rw [eval_bind]
        exact PotOKInvFS.bindPot (deliverEC_inact idx q B Δcka qep maxSkip gMain tL par la _ hinact
            (.fst .v3) .v0 _ m hInv) (fun _ h => potInvFS_ret h (Nat.le_refl 0))
    · intro _ _; rw [eval_bind]
      exact PotOKInvFS.bindPot (injectEC_inact idx q B Δcka qep gMain tL par la _ hinact
          (.fst .v2) .v0 _ m hInv) (fun _ h => potInvFS_ret h (Nat.le_refl 0))
  · intro p0 _; refine potInvFS_ite (fun _ => potInvFS_ret (mbEsInv_step_noop hInv) (Nat.le_refl 0))
      (fun hNotOr => ?_)
    have hab : sv.1.2.2 = false := by
      simp only [orE_eval, Bool.or_eq_false_iff, esAbort, Expr.eval, Expr.v0, Expr.v1,
        Env.get_cons_succ, Env.get_cons_zero] at hNotOr; exact hNotOr.1
    obtain ⟨hAId, hBId, hVpA, hVpB, hCa, hSes⟩ := hInv hab
    have hpVp : VpAct q qep gMain tL par (if p0 then sv.1.1.1.2 else sv.1.1.1.1) := by
      cases p0 <;> simp [hVpA, hVpB]
    rw [eval_bind]
    refine PotOKInvFS.bindPot (fsMultiBucketAuthRevealC_inact (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        idx q qep gMain la tL par hinact _ _ _ _ _ ?_) (fun revOut hRevOut => ?_)
    · simp only [pGet_eval_st_fs, cGsSt, esG, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
      exact hpVp
    · simp only [pGet_eval_st_fs, cGsSt, esG, esH, Expr.eval, Expr.v0, Expr.v1,
        Env.get_cons_zero, Env.get_cons_succ] at hRevOut
      refine potInvFS_caseOpt
        (fun _ => potInvFS_ret (fun hab' => by simp [esMk, Expr.eval, Expr.v0] at hab') (Nat.le_refl 0))
        (fun _ _ => potInvFS_ret ?_ (Nat.le_refl 0))
      intro _; simp only [esMk, pair_eval, cAfterCorrE_st_fs, esG, Expr.eval, Expr.v1, Expr.v2,
        Env.get_cons_succ, Env.get_cons_zero]
      have hCa' : CacheAct q qep gMain tL par revOut.2 := fun τ e sIdx hτ he =>
        hCa τ e sIdx (hRevOut.1 ▸ hτ) he
      refine ⟨hAId, hBId, hVpA, hVpB, hCa', ?_⟩; unfold SessBound at hSes ⊢; rw [hRevOut.2]
      cases hg : gMain
      · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hSes ⊢; intro τ; have h1 := hSes τ; omega
      · simp only [hg, ↓reduceIte] at hSes ⊢; exact hSes

end MultiBucketInact

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthCompat
