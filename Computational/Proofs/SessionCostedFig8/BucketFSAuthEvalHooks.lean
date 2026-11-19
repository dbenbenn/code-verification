/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedFS

/-!
# Hook Evaluation Lemmas (Part A: State Accessors, Root PRNG, `startSend`, `startRecv`)

Proves `Comp.eval` / `Expr.eval` equivalence between the costed `ReductionDsl` expressions in
`BucketPRNGAuthDefs` and the shallow `StateT` hooks in `BucketFSAuthShallowBase` for book/table/cache
accessors, `lookupMultiBucketFC`, `regSess{,Opt}MultiBucketE`, `rootFSMultiBucketAuthC`,
`fsMultiBucketAuthStartSendC`, `isHonestHdrMultiBucketE`, and `fsMultiBucketAuthStartRecvC`.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthEvalHooks

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl (Ops Ty Env Expr Comp)
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CKA (CKASort CKASamp CKAOp ckaOps ckaSamplers ckaHdrTy)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps prngSamplers)
open _root_.CryptoGames.SM (orE validGuessE validGuessE_eval letE_eval pair_eval some_eval
  ite_eval and_eval)
open _root_.CryptoGames.SM.Engine (Ctx HM TComp optNatLit vpTblEnc cGsTy cGsEnc
  tset_eval_eq_update eval_ret eval_bind eval_bind_ret eval_ite eval_caseOpt liftP_eq_liftM)
open _root_.CryptoGames.SM.Construction (Header healEpoch FSMultiSpec sampleT fst_eval snd_eval
  eval_caseOpt_none eval_caseOpt_some sessionsMemE_eval sessionsIdxOfE_eval
  sessionsLenE_eval sessionsAppendOneE_eval)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (fsaeadMultiBucketIface
  fsMultiBucketCacheEntryTy pbaTableEntryTy fsMultiBucketSessBookTy fsMultiBucketHsTy
  fsMultiBucketVpTy postLeak postLeakBucketE pbaTableLookupE mbHsCache mbHsTableTbl
  mbHsSessionsTbl mbHsBook mbHsLfWin mbHsMk mbHsSetCache mbHsSetTableAt mbHsSetSessionsAt
  mbHsSetBookAt mbHsGetBookAt mbHsSetLfWin lookupMultiBucketFC sessionsMemBucketE
  sessionsIdxOfBucketE sessionsLenBucketE sessionsAppendOneBucketE regSessMultiBucketE
  regSessOptMultiBucketE validGuessBucketParAuthE rootFSMultiBucketAuthC
  fsMultiBucketAuthStartSendC isHonestHdrMultiBucketE fsMultiBucketAuthStartRecvC)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (FSMultiBucketAuthState
  lookupMultiBucketF regSessMultiBucket regSessOptMultiBucket validGuessBucketParAuth
  rootFSMultiBucketAuth isHonestHdrMultiBucket hooksFSMultiBucketAuth fsMultiBucketHsEnc
  FSMultiBucketHBounded validGuessBucketParAuthE_eval postLeakBucketE_eval
  lookupMultiBucketF_preserve regSessMultiBucket_preserve regSessOptMultiBucket_preserve
  rootFSMultiBucketAuth_preserve)

section BucketHookEvalA

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

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
local notation "hsMBEnc" =>
  fsMultiBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
    (SS := SS) (RS := RS) (M := M)
local notation "vpMEnc" =>
  vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (KR := KR) (RSt := RSt)
    (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := Ty.base CKASort.γ) (svT := Ty.base CKASort.sig)
    (ssvT := Ty.sum (Ty.base CKASort.ss) Ty.nat) (rsvT := Ty.sum (Ty.base CKASort.rs) Ty.nat)

theorem mbHsGetBookAt_eval {O' : Ops SP} {Γ'}
    (hE : Expr O' Γ' mbHsTy) (sIdxE : Expr O' Γ' .nat) (ρ : Env Γ')
    (h : FSMultiBucketAuthState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (mbHsGetBookAt hE sIdxE).eval ρ =
      let b := (h.book (sIdxE.eval ρ)).getD {}
      (b.sCorr, b.fsCount, b.fsTrans) := by
  unfold mbHsGetBookAt
  simp only [mbHsBook, fsMultiBucketHsEnc, hh, Expr.eval, Expr.v0, Env.get_cons_zero]
  rcases h.book (sIdxE.eval ρ) with _ | ⟨sc, cnt, tr⟩ <;> rfl

theorem mbHsSetBookAt_eval {O' : Ops SP} {Γ'}
    (hE : Expr O' Γ' mbHsTy) (sIdxE : Expr O' Γ' .nat) (entryE : Expr O' Γ' mBookTy) (ρ : Env Γ')
    (h : FSMultiBucketAuthState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h)
    {sc : Bool} {cnt : ℕ} {tr : List (ℕ × Header T × E)}
    (hentry : entryE.eval ρ = (sc, cnt, tr)) :
    (mbHsSetBookAt hE sIdxE entryE).eval ρ =
      hsMBEnc { h with book := Function.update h.book (sIdxE.eval ρ) (some ⟨sc, cnt, tr⟩) } := by
  unfold mbHsSetBookAt mbHsMk
  simp only [pair_eval, tset_eval_eq_update, some_eval, hentry,
    mbHsCache, mbHsTableTbl, mbHsSessionsTbl, mbHsBook, mbHsLfWin,
    fst_eval, snd_eval, hh, fsMultiBucketHsEnc, Prod.mk.injEq, true_and, and_true]
  funext i
  by_cases hi : i = sIdxE.eval ρ <;> simp [Function.update, hi]

theorem mbHsSetCache_eval {O' : Ops SP} {Γ'}
    (hE : Expr O' Γ' mbHsTy)
    (caE : Expr O' Γ' (.tbl (.opt (@fsMultiBucketCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E))))
    (ρ : Env Γ') (h : FSMultiBucketAuthState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (mbHsSetCache hE caE).eval ρ = hsMBEnc { h with cache := caE.eval ρ } := by
  simp [mbHsSetCache, mbHsMk, mbHsTableTbl, mbHsSessionsTbl, mbHsBook, mbHsLfWin,
    fsMultiBucketHsEnc, hh, Expr.eval]

theorem mbHsSetTableAt_eval {O' : Ops SP} {Γ'}
    (hE : Expr O' Γ' mbHsTy) (tE : Expr O' Γ' .nat)
    (tbE : Expr O' Γ' (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (ρ : Env Γ') (h : FSMultiBucketAuthState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (mbHsSetTableAt hE tE tbE).eval ρ =
      hsMBEnc { h with fTable := Function.update h.fTable (tE.eval ρ) (tbE.eval ρ) } := by
  unfold mbHsSetTableAt mbHsMk
  simp only [pair_eval, tset_eval_eq_update, mbHsCache, mbHsTableTbl,
    mbHsSessionsTbl, mbHsBook, mbHsLfWin, fst_eval, snd_eval, hh, fsMultiBucketHsEnc]

theorem mbHsSetSessionsAt_eval {O' : Ops SP} {Γ'}
    (hE : Expr O' Γ' mbHsTy) (tE : Expr O' Γ' .nat)
    (seE : Expr O' Γ' (.list (.base .i)))
    (ρ : Env Γ') (h : FSMultiBucketAuthState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (mbHsSetSessionsAt hE tE seE).eval ρ =
      hsMBEnc { h with sessions := Function.update h.sessions (tE.eval ρ) (seE.eval ρ) } := by
  unfold mbHsSetSessionsAt mbHsMk
  simp only [pair_eval, tset_eval_eq_update, mbHsCache, mbHsTableTbl,
    mbHsSessionsTbl, mbHsBook, mbHsLfWin, fst_eval, snd_eval, hh, fsMultiBucketHsEnc]

theorem mbHsSetLfWin_eval {O' : Ops SP} {Γ'}
    (hE : Expr O' Γ' mbHsTy) (lwE : Expr O' Γ' .bool)
    (ρ : Env Γ') (h : FSMultiBucketAuthState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (mbHsSetLfWin hE lwE).eval ρ = hsMBEnc { h with lfWin := lwE.eval ρ } := by
  simp [mbHsSetLfWin, mbHsMk, mbHsCache, mbHsTableTbl, mbHsSessionsTbl, mbHsBook,
    fsMultiBucketHsEnc, hh, Expr.eval]

private theorem foldr_pba_lookup_eq [DecidableEq I] (ik : I) (l : List (I × K)) :
    l.foldr (fun p acc => if (ik == p.1) = true then some p.2 else acc) none = l.lookup ik := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.foldr_cons, List.lookup_cons, ih]
    cases ik == k <;> rfl

private theorem pbaTableLookupE_eval [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) {Γ'}
    (tblE : Expr OO Γ' (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (hL : (tblE.eval ρ).length ≤ L) :
    (pbaTableLookupE L tblE ikE).eval ρ = (tblE.eval ρ).lookup (ikE.eval ρ) := by
  have htake : (tblE.eval ρ).take L = tblE.eval ρ := List.take_of_length_le hL
  simp only [pbaTableLookupE, prngOps, ckaOps, heqI, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, htake]
  exact foldr_pba_lookup_eq (ikE.eval ρ) (tblE.eval ρ)

theorem lookupMultiBucketFC_eval [DecidableEq I] [SampleableType K]
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) {Γ'} (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (h : FSMultiBucketAuthState T RSt K I E)
    (hh : hE.eval ρ = hsMBEnc h) (hL : (h.fTable (tE.eval ρ)).length ≤ L) :
    (lookupMultiBucketFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE tE ikE).eval ρ =
      Prod.map id hsMBEnc <$>
        (lookupMultiBucketF (T := T) (RSt := RSt) (K := K) (I := I) (SS := SS) (RS := RS)
          (M := M) (E := E) (tE.eval ρ) (ikE.eval ρ)).run h ∧
    ∀ res ∈ support ((lookupMultiBucketF (T := T) (RSt := RSt) (K := K) (I := I)
        (SS := SS) (RS := RS) (M := M) (E := E) (tE.eval ρ) (ikE.eval ρ)).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  refine ⟨?_, lookupMultiBucketF_preserve (tE.eval ρ) (ikE.eval ρ) h⟩
  unfold lookupMultiBucketFC lookupMultiBucketF
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set Ik : I := ikE.eval ρ
  have h0 : (Expr.pair hE (.pair tE ikE)).eval ρ = (hsMBEnc h, t0, Ik) := by
    simp [Expr.eval, hh, t0, Ik]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod mbHsTy (.prod .nat (.base CKASort.i))) (hsMBEnc h, t0, Ik) ρ
  have hTbl : (pbaTableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (.tget (mbHsTableTbl (.fst .v0)) (.fst (.snd .v0)))
      (.snd (.snd .v0))).eval ρ₁ = (h.fTable t0).lookup Ik := by
    rw [pbaTableLookupE_eval heqI L
      (.tget (mbHsTableTbl (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd .v0)) ρ₁
      (by simpa [ρ₁, mbHsTableTbl, fsMultiBucketHsEnc, Expr.eval, Expr.v0] using hL)]
    rfl
  rw [eval_caseOpt, hTbl]
  rcases hlk : (h.fTable t0).lookup Ik with _ | kFound
  · simp only [hlk, eval_bind, StateT.run_bind, StateT.run_get,
      StateT.run_lift, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc, map_bind]
    have hSamp : (@Comp.sample _ _ _ OO IIM _ CKASamp.k .unit).eval ρ₁ =
        (sampleT K : TComp (FSMultiSpec SS RS T M E) K) := by
      simp only [Comp.eval, fsaeadMultiBucketIface, prngSamplers, ckaSamplers, hSampK, sampleT]
      exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ K)
    rw [hSamp]
    refine bind_congr fun kNew => ?_
    rw [eval_ret, pair_eval, mbHsSetTableAt_eval _ _ _ _ h rfl]
    simp [ρ₁, Prod.map, Expr.eval, Expr.v0, Expr.v1, mbHsTableTbl, fsMultiBucketHsEnc]
  · simp [ρ₁, hlk, Comp.eval, StateT.run_bind, StateT.run_get,
      StateT.run_pure, pure_bind, Prod.map, Expr.eval, Expr.v0, Expr.v1]

theorem regSessMultiBucketE_eval_pair [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) (gMain : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (h : FSMultiBucketAuthState T RSt K I E)
    (hh : hE.eval ρ = hsMBEnc h) (hL : (h.sessions (tE.eval ρ)).length ≤ L) :
    (regSessMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L gMain tL hE tE ikE).eval ρ =
      (let p := regSessMultiBucket L gMain tL (tE.eval ρ) (ikE.eval ρ) h
       (p.1, hsMBEnc p.2)) ∧
    let p := regSessMultiBucket L gMain tL (tE.eval ρ) (ikE.eval ρ) h
    p.2.fTable = h.fTable ∧
    (∀ t', (p.2.sessions t').length ≤ (h.sessions t').length + 1) ∧
    p.2.book = h.book := by
  refine ⟨?_, regSessMultiBucket_preserve L gMain tL (tE.eval ρ) (ikE.eval ρ) h⟩
  unfold regSessMultiBucketE
  dsimp only [regSessMultiBucket]
  rw [letE_eval]
  set t0 : ℕ := tE.eval ρ
  set Ik : I := ikE.eval ρ
  have h0 : (Expr.pair hE (.pair tE ikE)).eval ρ = (hsMBEnc h, t0, Ik) := by
    simp [Expr.eval, hh, t0, Ik]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod mbHsTy (.prod .nat (.base CKASort.i))) (hsMBEnc h, t0, Ik) ρ
  set sesExpr : Expr OO _ (.list (.base .i)) :=
    .tget (mbHsSessionsTbl (.fst .v0)) (.fst (.snd .v0))
  have hSesEval : sesExpr.eval ρ₁ = h.sessions t0 := by
    simp [sesExpr, ρ₁, mbHsSessionsTbl, fsMultiBucketHsEnc, Expr.eval, Expr.v0]
  have hSesL : (sesExpr.eval ρ₁).length ≤ L := hSesEval ▸ hL
  have hMem : (sessionsMemBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L sesExpr (.snd (.snd .v0))).eval ρ₁ = decide (Ik ∈ h.sessions t0) := by
    change (_root_.CryptoGames.SM.Construction.sessionsMemE L sesExpr (.snd (.snd .v0))).eval ρ₁ = _
    rw [sessionsMemE_eval heqI L sesExpr (.snd (.snd .v0)) ρ₁ hSesL, hSesEval]; rfl
  have hIdx : (sessionsIdxOfBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L sesExpr (.snd (.snd .v0))).eval ρ₁ = (h.sessions t0).idxOf Ik := by
    change (_root_.CryptoGames.SM.Construction.sessionsIdxOfE L sesExpr (.snd (.snd .v0))).eval ρ₁ = _
    rw [sessionsIdxOfE_eval heqI L sesExpr (.snd (.snd .v0)) ρ₁ hSesL, hSesEval]; rfl
  have hLen : (sessionsLenBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L sesExpr).eval ρ₁ = (h.sessions t0).length := by
    change (_root_.CryptoGames.SM.Construction.sessionsLenE L sesExpr).eval ρ₁ = _
    rw [sessionsLenE_eval L sesExpr ρ₁ hSesL, hSesEval]
  have hApp : (sessionsAppendOneBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L sesExpr (.snd (.snd .v0))).eval ρ₁ = h.sessions t0 ++ [Ik] := by
    change (_root_.CryptoGames.SM.Construction.sessionsAppendOneE L sesExpr (.snd (.snd .v0))).eval ρ₁ = _
    rw [sessionsAppendOneE_eval L sesExpr (.snd (.snd .v0)) ρ₁ hSesL, hSesEval]; rfl
  change (Expr.ite (sessionsMemBucketE L sesExpr (.snd (.snd .v0))) _ _).eval ρ₁ = _
  rw [ite_eval, hMem]
  by_cases hm : Ik ∈ h.sessions t0
  · simp only [hm, decide_true, ↓reduceIte, pair_eval]
    have hFst : ((((Expr.mulK L (Expr.v0.snd.fst.sub (Expr.nat (healEpoch tL)))).add
        (sessionsIdxOfBucketE L sesExpr Expr.v0.snd.snd)).add
        (Expr.nat (if gMain = true then 0 else 1)))).eval ρ₁ =
        L * (t0 - healEpoch tL) + List.idxOf Ik (h.sessions t0) + (if gMain = true then 0 else 1) := by
      change (_ + (sessionsIdxOfBucketE L sesExpr Expr.v0.snd.snd).eval ρ₁) + _ = _
      rw [hIdx]
      simp [ρ₁, Expr.eval, Expr.v0]
    rw [hFst]
    simp [ρ₁, Expr.eval, Expr.v0]
  · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, pair_eval]
    rw [mbHsSetSessionsAt_eval _ _ _ ρ₁ h rfl, hApp]
    simp [ρ₁, hLen, Expr.eval, Expr.v0]

theorem regSessOptMultiBucketE_eval_pair [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) (gMain : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (sidE : Expr OO Γ' (.opt (.base .i)))
    (ρ : Env Γ') (h : FSMultiBucketAuthState T RSt K I E)
    (hh : hE.eval ρ = hsMBEnc h) (hL : (h.sessions (tE.eval ρ)).length ≤ L) :
    (regSessOptMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L gMain tL hE tE sidE).eval ρ =
      (let p := regSessOptMultiBucket L gMain tL (tE.eval ρ) (sidE.eval ρ) h
       (p.1, hsMBEnc p.2)) ∧
    let p := regSessOptMultiBucket L gMain tL (tE.eval ρ) (sidE.eval ρ) h
    p.2.fTable = h.fTable ∧
    (∀ t', (p.2.sessions t').length ≤ (h.sessions t').length + 1) ∧
    p.2.book = h.book := by
  refine ⟨?_, regSessOptMultiBucket_preserve L gMain tL (tE.eval ρ) (sidE.eval ρ) h⟩
  unfold regSessOptMultiBucketE regSessOptMultiBucket
  rw [letE_eval]
  set t0 : ℕ := tE.eval ρ
  rcases hsid : sidE.eval ρ with _ | Ik
  · simp [hsid, hh, Expr.eval, Expr.v0]
  · have h0 : (Expr.pair hE (.pair tE sidE)).eval ρ = (hsMBEnc h, t0, some Ik) := by
      simp [Expr.eval, hh, t0, hsid]
    rw [h0]
    set ρ₁ := Env.cons (t := .base CKASort.i) Ik
      (Env.cons (t := .prod mbHsTy (.prod .nat (.opt (.base CKASort.i))))
        (hsMBEnc h, t0, some Ik) ρ)
    have hReg := (regSessMultiBucketE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) heqI L gMain tL
      (Expr.fst (O := OO) .v1) (.fst (.snd .v1)) .v0 ρ₁ h rfl hL).1
    have ht1 : (Expr.fst (.snd (Expr.v1 (O := OO)))).eval ρ₁ = t0 := rfl
    have hik1 : (Expr.v0 (O := OO)).eval ρ₁ = Ik := rfl
    rw [ht1, hik1] at hReg
    change (Expr.pair (.some (.fst _)) (.snd _)).eval ρ₁ = _
    rw [pair_eval, some_eval, fst_eval, snd_eval, hReg]

theorem rootFSMultiBucketAuthC_eval
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K)
    (hPrngUp : prngUp = prng.up) (heqI : eqI = (· == ·))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig))
    (ρ : Env Γ') (h : FSMultiBucketAuthState T RSt K I E)
    (hh : hE.eval ρ = hsMBEnc h) (hL : (h.fTable (tE.eval ρ)).length ≤ L) :
    (rootFSMultiBucketAuthC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δcka qep tL par hE tE plE ikE σE).eval ρ =
      Prod.map id hsMBEnc <$>
        (rootFSMultiBucketAuth (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
          prng Δcka qep tL par (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σE.eval ρ)).run h ∧
    ∀ res ∈ support ((rootFSMultiBucketAuth (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
        prng Δcka qep tL par (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σE.eval ρ)).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  refine ⟨?_, rootFSMultiBucketAuth_preserve prng Δcka qep tL par
    (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σE.eval ρ) h⟩
  unfold rootFSMultiBucketAuthC rootFSMultiBucketAuth
  dsimp only
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set pl0 : Bool := plE.eval ρ
  set ik0 : I := ikE.eval ρ
  set σ0 : RSt := σE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair plE (.pair ikE σE)))).eval ρ =
      (hsMBEnc h, t0, pl0, ik0, σ0) := by
    simp [Expr.eval, hh, t0, pl0, ik0, σ0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mbHsTy (.prod .nat (.prod .bool (.prod (.base CKASort.i) (.base CKASort.sig)))))
    (hsMBEnc h, t0, pl0, ik0, σ0) ρ
  rw [eval_ite]
  have hc1 : (orE (O' := OO) (.fst (.snd (.snd .v0)))
      (.lt (.nat (qep + 1)) (.fst (.snd .v0)))).eval ρ₁ =
      (pl0 || decide (qep + 1 < t0)) := by
    cases hpl : pl0
    · simp [ρ₁, orE, Expr.eval, Expr.v0, hpl]; rfl
    · simp [ρ₁, orE, Expr.eval, Expr.v0, hpl]
  rw [hc1]
  by_cases h1 : (pl0 || decide (qep + 1 < t0)) = true
  · simp [h1, ρ₁, hPrngUp, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, eval_ite]
    have hc2 := validGuessBucketParAuthE_eval (O' := OO) Δcka tL par (.fst (.snd .v0)) ρ₁
    have ht1 : (Expr.fst (.snd (Expr.v0 (O := OO)))).eval ρ₁ = t0 := rfl
    rw [ht1] at hc2
    rw [hc2]
    have hSampI' : ∀ {Γ''} (ρ'' : Env Γ''),
        (@Comp.sample _ _ _ OO IIM _ CKASamp.i .unit).eval ρ'' =
          (sampleT I : TComp (FSMultiSpec SS RS T M E) I) := fun ρ'' => by
      simp only [Comp.eval, fsaeadMultiBucketIface, prngSamplers, ckaSamplers, hSampI, sampleT]
      exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ I)
    have hSampK' : ∀ {Γ''} (ρ'' : Env Γ''),
        (@Comp.sample _ _ _ OO IIM _ CKASamp.k .unit).eval ρ'' =
          (sampleT K : TComp (FSMultiSpec SS RS T M E) K) := fun ρ'' => by
      simp only [Comp.eval, fsaeadMultiBucketIface, prngSamplers, ckaSamplers, hSampK, sampleT]
      exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ K)
    by_cases h2 : validGuessBucketParAuth Δcka tL par t0 = true
    · simp only [h2, ↓reduceIte]
      have hc3 : (Expr.and (O := OO) (.bool tL.isSome)
          (.eqN (.fst (.snd .v0)) (.nat (healEpoch tL)))).eval ρ₁ =
          (tL.isSome && (t0 == healEpoch tL)) := by
        simp [ρ₁, BEq.beq, Expr.eval, Expr.v0]
      rw [hc3]
      by_cases h3 : (tL.isSome && (t0 == healEpoch tL)) = true
      · simp only [h3, ↓reduceIte, eval_bind, hSampI', StateT.run_bind, StateT.run_lift,
          bind_assoc, pure_bind, map_bind]
        refine bind_congr fun ir => ?_
        simp only [hSampK']
        refine bind_congr fun kSample => ?_
        simp [ρ₁, hPrngUp, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte, eval_bind]
        have hLk := (lookupMultiBucketFC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
          (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) heqI hSampK L
          (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0)))) ρ₁ h rfl hL).1
        rw [hLk, StateT.run_bind, bind_map_left, map_bind]
        refine bind_congr fun ⟨kLookup, h1'⟩ => ?_
        simp [ρ₁, hPrngUp, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      have hc3 : (Expr.and (O := OO) (.bool tL.isSome)
          (.eqN (.fst (.snd .v0)) (.nat (healEpoch tL)))).eval ρ₁ =
          (tL.isSome && (t0 == healEpoch tL)) := by
        simp [ρ₁, BEq.beq, Expr.eval, Expr.v0]
      rw [hc3]
      by_cases h3 : (tL.isSome && (t0 == healEpoch tL)) = true
      · simp only [h3, ↓reduceIte, eval_bind, hSampI', StateT.run_bind, StateT.run_lift,
          bind_assoc, pure_bind, map_bind]
        refine bind_congr fun ir => ?_
        simp only [hSampK']
        refine bind_congr fun kSample => ?_
        simp [ρ₁, hPrngUp, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        have hc4 : (Expr.not (O := OO) (.lt (.fst (.snd .v0)) (.nat (healEpoch tL)))).eval ρ₁ =
            !decide (t0 < healEpoch tL) := rfl
        rw [hc4]
        by_cases h4 : (!decide (t0 < healEpoch tL)) = true
        · simp only [h4, ↓reduceIte, eval_bind]
          have hLk := (lookupMultiBucketFC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
            (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) heqI hSampK L
            (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0)))) ρ₁ h rfl hL).1
          rw [hLk, StateT.run_bind, bind_map_left, map_bind]
          refine bind_congr fun ⟨kLookup, h1'⟩ => ?_
          simp [ρ₁, hPrngUp, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
        · simp [h4, ρ₁, hPrngUp, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]

theorem fsMultiBucketAuthStartSendC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hSend : ckaSend = cka.send)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (heqI : eqI = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : FSMultiBucketAuthState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (hHB : FSMultiBucketHBounded L h) (hh : hE.eval ρ = hsMBEnc h)
    (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx) :
    (fsMultiBucketAuthStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δcka qep gMain tL par hE ctxE pE tE γE σE rE).eval ρ =
      Prod.map id hsMBEnc <$>
        ((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).startSend ctx P
          (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (rE.eval ρ)).run h := by
  unfold fsMultiBucketAuthStartSendC
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set γ0 : Γ := γE.eval ρ
  set σ0 : RSt := σE.eval ρ
  set r0 : Option CCoins := rE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair tE (.pair γE (.pair σE rE))))).eval ρ =
      (hsMBEnc h, cGsEnc vpMEnc ctx, t0, γ0, σ0, r0) := by
    simp [Expr.eval, hh, hctx, t0, γ0, σ0, r0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mbHsTy (.prod (cGsTy mVpTy) (.prod .nat (.prod (.base CKASort.γ)
      (.prod (.base CKASort.sig) (.opt (.base CKASort.ccoins)))))))
    (hsMBEnc h, cGsEnc vpMEnc ctx, t0, γ0, σ0, r0) ρ
  have hStep1 :
      (Comp.caseOpt (O := OO) (I := IIM) (.snd (.snd (.snd (.snd (.snd .v0)))))
        (@Comp.sample _ _ _ OO IIM _ CKASamp.ccoins .unit)
        (.ret .v0)).eval ρ₁ =
      (match r0 with
        | some c => pure c
        | none => (sampleT CCoins : TComp (FSMultiSpec SS RS T M E) CCoins)) := by
    rcases r0 with _ | c
    · simp only [ρ₁, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero,
        fsaeadMultiBucketIface, prngSamplers, ckaSamplers, hSampCCoins, sampleT]
      exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ CCoins)
    · rfl
  have hRHS :
      ((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).startSend
        ctx P t0 γ0 σ0 r0).run h =
      ((match r0 with
          | some c => pure c
          | none => (sampleT CCoins : TComp (FSMultiSpec SS RS T M E) CCoins)) >>=
        fun coins =>
          (do
            let cOut := cka.send γ0 coins
            let (σ', kVal, sid) ← rootFSMultiBucketAuth (SS := SS) (RS := RS) (M := M) (E := E)
              prng Δcka qep tL par t0 (postLeak tL ctx) cOut.2.2 σ0
            let s1 ← (get : HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E) _)
            let (optIdx, s2) := regSessOptMultiBucket L gMain tL t0 sid s1
            set { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
            let ssv : SS ⊕ ℕ := match optIdx with
              | none => .inl (fs.initSender kVal)
              | some sIdx => .inr sIdx
            return some (cOut.1, cOut.2.1, σ', ssv)).run h) := by
    unfold hooksFSMultiBucketAuth; dsimp only
    rcases r0 with _ | c
    · dsimp only; rw [StateT.run_bind, StateT.run_lift, bind_assoc]; simp only [pure_bind]; rfl
    · dsimp only; rw [StateT.run_bind, StateT.run_pure, pure_bind]; rfl
  rw [eval_bind, hStep1, hRHS, map_bind]
  refine bind_congr fun coins => ?_
  set ρ₂ := Env.cons (t := .base CKASort.ccoins) coins ρ₁
  have hPl := postLeakBucketE_eval (O' := OO) vpTblEnc tL (.fst (.snd .v1)) ρ₂ ctx rfl
  have hRoot := rootFSMultiBucketAuthC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins)
    prng hPrngUp heqI hSampI hSampK L Δcka qep tL par
    (.fst .v1) (.fst (.snd (.snd .v1))) (postLeakBucketE tL (.fst (.snd .v1)))
    (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))))
    (.fst (.snd (.snd (.snd (.snd .v1))))) ρ₂ h rfl (hHB.1 t0)
  have hIkEval : (Expr.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend
      (.pair (.fst (.snd (.snd (.snd .v1)))) .v0)))).eval ρ₂ = (cka.send γ0 coins).2.2 := by
    simp [ρ₂, ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1]
  have htEval : (Expr.fst (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ = t0 := rfl
  have hσEval : (Expr.fst (.snd (.snd (.snd (.snd (Expr.v1 (O := OO))))))).eval ρ₂ = σ0 := rfl
  rw [hIkEval, htEval, hσEval, hPl] at hRoot
  rw [eval_bind, hRoot.1, StateT.run_bind, bind_map_left, map_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨σ', kVal, sid⟩, h₁⟩ hmemRoot => ?_
  have ⟨_, hSes₁, _⟩ := hRoot.2 ((σ', kVal, sid), h₁) hmemRoot
  have hSesL₁ : (h₁.sessions t0).length ≤ L := hSes₁ ▸ hHB.2.1 t0
  set ρ₃ := Env.cons
    (t := .prod (.prod (.base CKASort.sig) (.prod (.base CKASort.k) (.opt (.base CKASort.i))))
      mbHsTy)
    ((σ', kVal, sid), hsMBEnc h₁) ρ₂
  have hReg := (regSessOptMultiBucketE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) heqI L gMain tL
    (.snd .v0) (.fst (.snd (.snd .v2))) (.snd (.snd (.fst .v0))) ρ₃ h₁ rfl hSesL₁).1
  have ht3 : (Expr.fst (.snd (.snd (Expr.v2 (O := OO))))).eval ρ₃ = t0 := rfl
  have hsid3 : (Expr.snd (.snd (.fst (Expr.v0 (O := OO))))).eval ρ₃ = sid := rfl
  rw [ht3, hsid3] at hReg
  set p := regSessOptMultiBucket L gMain tL t0 sid h₁
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
    pure_bind, map_pure, Prod.map, id_eq]
  change (Comp.ret _).eval ρ₃ = _
  have hRegFst : (Expr.fst (regSessOptMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L gMain tL (.snd .v0) (.fst (.snd (.snd .v2))) (.snd (.snd (.fst .v0))))).eval ρ₃ = p.1 := by
    rw [fst_eval, hReg]
  have hRegSnd : (Expr.snd (regSessOptMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L gMain tL (.snd .v0) (.fst (.snd (.snd .v2))) (.snd (.snd (.fst .v0))))).eval ρ₃ = hsMBEnc p.2 := by
    rw [snd_eval, hReg]
  rw [eval_ret, pair_eval, mbHsSetCache_eval _ _ ρ₃ p.2 hRegSnd]
  congr 1
  · congr 1
    · have hCaseOpt : ∀ {α β} (e : Expr OO _ (.opt α)) (n : Expr OO _ β) (s : Expr OO (α :: _) β),
          (Expr.caseOpt e n s).eval ρ₃ =
            match e.eval ρ₃ with | none => n.eval ρ₃ | some x => s.eval (Env.cons x ρ₃) :=
        fun e _ _ => by cases h : e.eval ρ₃ <;> simp [Expr.eval, h]
      rw [some_eval, pair_eval, pair_eval, pair_eval, hCaseOpt, hRegFst]
      rcases p.1 with _ | sIdx <;>
        simp [ρ₃, ρ₂, ρ₁, hSend, hFsInitS, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
    · congr 1; simp only [tset_eval_eq_update]
      have hca : (mbHsCache (.snd (regSessOptMultiBucketE (ckaInitA := ckaInitA)
          (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
          (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
          (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
          (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
          (defaultE := defaultE) L gMain tL (.snd .v0) (.fst (.snd (.snd .v2)))
          (.snd (.snd (.fst .v0)))))).eval ρ₃ = p.2.cache := by
        unfold mbHsCache; rw [fst_eval, hRegSnd]; rfl
      have hkEval : (Expr.fst (.snd (.snd (Expr.v2 (O := OO))))).eval ρ₃ = t0 := rfl
      have hvEval : (Expr.some (.pair
          (.fst (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd (.snd .v2)))) .v1))))
          (.pair (.fst (.fst .v0))
            (.pair (.fst (.snd (.fst .v0)))
              (.fst (regSessOptMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                L gMain tL (.snd .v0) (.fst (.snd (.snd .v2))) (.snd (.snd (.fst .v0))))))))).eval ρ₃ =
          some ((cka.send γ0 coins).2.1, σ', kVal, p.1) := by
        rw [some_eval, pair_eval, pair_eval, pair_eval, hRegFst]
        simp [ρ₃, ρ₂, ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
      rw [hca, hkEval, hvEval]

theorem isHonestHdrMultiBucketE_eval [DecidableEq T] (heqT : eqT = (· == ·))
    {Γ'} (hE : Expr OO Γ' mbHsTy) (hdrE : Expr OO Γ' hdrTy) (ρ : Env Γ')
    (h : FSMultiBucketAuthState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (isHonestHdrMultiBucketE hE hdrE).eval ρ =
      isHonestHdrMultiBucket h (hdrE.eval ρ) := by
  unfold isHonestHdrMultiBucketE isHonestHdrMultiBucket
  rw [letE_eval]
  rcases hhdr : hdrE.eval ρ with ⟨t0, _ | tn0⟩
  · simp [hhdr, hh, Expr.eval, Expr.v0]
  · rcases hca : h.cache t0 with _ | ⟨tCached, σc, kVal, optIdx⟩
    · simp [hhdr, hh, hca, mbHsCache, fsMultiBucketHsEnc, Expr.eval, Expr.v0, Expr.v1]
    · simp [hhdr, hh, hca, mbHsCache, fsMultiBucketHsEnc, heqT, BEq.beq,
        Expr.eval, Expr.v0, Expr.v1]

theorem fsMultiBucketAuthStartRecvC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : FSMultiBucketAuthState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (hHB : FSMultiBucketHBounded L h) (hh : hE.eval ρ = hsMBEnc h)
    (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx) :
    (fsMultiBucketAuthStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δcka qep gMain tL par hE ctxE pE tE γE σE tnE).eval ρ =
      Prod.map id hsMBEnc <$>
        ((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).startRecv ctx P
          (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h := by
  unfold fsMultiBucketAuthStartRecvC hooksFSMultiBucketAuth
  dsimp only
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set γ0 : Γ := γE.eval ρ
  set σ0 : RSt := σE.eval ρ
  set Tn : T := tnE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair tE (.pair γE (.pair σE tnE))))).eval ρ =
      (hsMBEnc h, cGsEnc vpMEnc ctx, t0, γ0, σ0, Tn) := by
    simp [Expr.eval, hh, hctx, t0, γ0, σ0, Tn]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mbHsTy (.prod (cGsTy mVpTy) (.prod .nat (.prod (.base CKASort.γ)
      (.prod (.base CKASort.sig) (.base CKASort.t))))))
    (hsMBEnc h, cGsEnc vpMEnc ctx, t0, γ0, σ0, Tn) ρ
  have hPl1 := postLeakBucketE_eval (O' := OO) vpTblEnc tL (.fst (.snd .v0)) ρ₁ ctx rfl
  have htL1 : (optNatLit (O' := OO) tL).eval ρ₁ = tL := by cases tL <;> rfl
  have hAdmiss1 : (Expr.and (.not (.lt (.nat (qep + 1)) (.fst (.snd (.snd (Expr.v0 (O := OO)))))))
      (validGuessE (2 + Δcka) (optNatLit tL) (.fst (.snd (.snd .v0))))).eval ρ₁ =
      (Bool.not (decide (qep + 1 < t0)) &&
        _root_.CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t0) := by
    rw [and_eval, validGuessE_eval, htL1]; rfl
  have hHealEq1 : (Expr.and (.bool tL.isSome)
      (.eqN (.fst (.snd (.snd (Expr.v0 (O := OO))))) (.nat (healEpoch tL)))).eval ρ₁ =
      (tL.isSome && (t0 == healEpoch tL)) := by
    by_cases htH : t0 = healEpoch tL <;> simp [ρ₁, htH, Expr.eval, Expr.v0]
  set honest : Option (RSt × K × Option ℕ) :=
    match h.cache t0 with
    | some (Tc, σc, kVal, optIdx) => if Tc = Tn then some (σc, kVal, optIdx) else none
    | none => none
  have hHonEval :
      (Expr.caseOpt (O := OO) (.tget (mbHsCache (.fst .v0)) (.fst (.snd (.snd .v0)))) .none
        (.ite (Expr.op (O := OO) CKAOp.eqT
            (.pair (.fst .v0) (.snd (.snd (.snd (.snd (.snd .v1)))))))
          (.some (.snd .v0))
          .none)).eval ρ₁ = honest := by
    rcases hcache : h.cache t0 with _ | ⟨Tc, σc, kVal, optIdx⟩
    · dsimp only [honest]; rw [hcache]
      simp [ρ₁, hcache, mbHsCache, fsMultiBucketHsEnc, Expr.eval, Expr.v0]
    · dsimp only [honest]; rw [hcache]
      by_cases hEq : Tc = Tn
      · simp [hEq, ρ₁, hcache, heqT, mbHsCache, fsMultiBucketHsEnc, Expr.eval, Expr.v0, Expr.v1]
      · simp [hEq, ρ₁, hcache, heqT, mbHsCache, fsMultiBucketHsEnc, Expr.eval, Expr.v0, Expr.v1]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  change _ = Prod.map id hsMBEnc <$> StateT.run (match honest with
    | some (σc, kVal, optIdx) => _
    | none => _) h
  rcases hhon : honest with _ | ⟨σc, kVal, optIdx⟩
  · rw [eval_caseOpt_none (hHonEval.trans hhon)]
    dsimp only
    rw [eval_ite]
    cases gMain
    · simp only [Expr.eval, Bool.false_eq_true, ↓reduceIte]
      rw [eval_ite, hAdmiss1]
      by_cases hc1 : (Bool.not (decide (qep + 1 < t0)) &&
          _root_.CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t0) = true
      · simp only [hc1, ↓reduceIte]
        rw [eval_ite, hHealEq1]
        by_cases hc2 : (tL.isSome && (t0 == healEpoch tL)) = true
        · simp [hc2, ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
          rw [eval_ite, hPl1]
          by_cases hcPl : postLeak tL ctx = true
          · simp [hcPl, ρ₁, hRecv, hPrngUp, hFsInitR, StateT.run_pure, Comp.eval, Prod.map,
              Expr.eval, Expr.v0]
          · simp only [hcPl, Bool.false_eq_true, ↓reduceIte]
            rw [eval_ite, validGuessBucketParAuthE_eval]
            have ht1 : (Expr.fst (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = t0 := rfl
            rw [ht1]
            by_cases hcPar : validGuessBucketParAuth Δcka tL par t0 = true
            · simp only [hcPar, ↓reduceIte]
              have hLk := lookupMultiBucketFC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
                (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI)
                heqI hSampK L (.fst .v0) (.fst (.snd (.snd .v0)))
                (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd .v0))))))))
                ρ₁ h rfl (hHB.1 t0)
              have hKk2 : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd (.snd .v0))))
                    (.snd (.snd (.snd (.snd (.snd .v0)))))))).eval ρ₁ =
                  (cka.receive γ0 Tn).2 := by
                simp [ρ₁, hRecv, Expr.eval, Expr.v0]
              rw [hKk2, ht1] at hLk
              rw [eval_bind, hLk.1, StateT.run_bind, bind_map_left, map_bind]
              refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨k', h₁⟩ hmemLk => ?_
              have ⟨_, hSes₁, _⟩ := hLk.2 (k', h₁) hmemLk
              have hSesL₁ : (h₁.sessions t0).length ≤ L := hSes₁ ▸ hHB.2.1 t0
              set ρ₂ := Env.cons (t := .prod (.base CKASort.k) mbHsTy) (k', hsMBEnc h₁) ρ₁
              have hReg := (regSessMultiBucketE_eval_pair (ckaInitA := ckaInitA)
                (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
                (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
                (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
                (eqT := eqT) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                heqI L false tL (.snd .v0) (.fst (.snd (.snd .v1)))
                (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd (.snd .v1))))
                    (.snd (.snd (.snd (.snd (.snd .v1)))))))) ρ₂ h₁ rfl hSesL₁).1
              have hKk2' : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd (.snd .v1))))
                    (.snd (.snd (.snd (.snd (.snd .v1)))))))).eval ρ₂ =
                  (cka.receive γ0 Tn).2 := by
                simp [ρ₂, ρ₁, hRecv, Expr.eval, Expr.v1]
              have ht2 : (Expr.fst (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ = t0 := rfl
              rw [hKk2', ht2] at hReg
              simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                pure_bind, map_pure, Prod.map, id_eq]
              change (Comp.ret _).eval ρ₂ = _
              set p := regSessMultiBucket L false tL t0 (cka.receive γ0 Tn).2 h₁
              have hRegFst : (Expr.fst (regSessMultiBucketE (ckaInitA := ckaInitA)
                  (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
                  (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
                  (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
                  (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                  (lam := lam) (defaultE := defaultE)
                  L false tL (.snd .v0) (.fst (.snd (.snd .v1)))
                  (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                    (.pair (.fst (.snd (.snd (.snd .v1))))
                      (.snd (.snd (.snd (.snd (.snd .v1)))))))))).eval ρ₂ = p.1 := by
                rw [fst_eval, hReg]
              have hRegSnd : (Expr.snd (regSessMultiBucketE (ckaInitA := ckaInitA)
                  (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
                  (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
                  (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
                  (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                  (lam := lam) (defaultE := defaultE)
                  L false tL (.snd .v0) (.fst (.snd (.snd .v1)))
                  (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                    (.pair (.fst (.snd (.snd (.snd .v1))))
                      (.snd (.snd (.snd (.snd (.snd .v1)))))))))).eval ρ₂ = hsMBEnc p.2 := by
                rw [snd_eval, hReg]
              have hInr : (Expr.inr (t := .base CKASort.rs)
                  (.fst (regSessMultiBucketE (ckaInitA := ckaInitA)
                    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
                    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
                    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
                    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                    (lam := lam) (defaultE := defaultE)
                    L false tL (.snd .v0) (.fst (.snd (.snd .v1)))
                    (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                      (.pair (.fst (.snd (.snd (.snd .v1))))
                        (.snd (.snd (.snd (.snd (.snd .v1))))))))))).eval ρ₂ = Sum.inr p.1 :=
                congrArg Sum.inr hRegFst
              rw [eval_ret, pair_eval, some_eval, some_eval, pair_eval, pair_eval, hInr, hRegSnd]
              simp [ρ₂, ρ₁, hRecv, hPrngUp, Expr.eval, Expr.v1]
            · simp only [hcPar, Bool.false_eq_true, ↓reduceIte]
              rw [eval_ite]
              have hGeH : (Expr.not (.lt (.fst (.snd (.snd (Expr.v0 (O := OO)))))
                  (.nat (healEpoch tL)))).eval ρ₁ = Bool.not (decide (t0 < healEpoch tL)) := rfl
              rw [hGeH]
              by_cases hcGeH : t0 < healEpoch tL
              · simp [hcGeH, ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
              · simp only [hcGeH, decide_false, Bool.not_false, ↓reduceIte]
                have hLk := lookupMultiBucketFC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                  (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                  (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                  (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
                  (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
                  (sampCCoins := sampCCoins) (sampI := sampI)
                  heqI hSampK L (.fst .v0) (.fst (.snd (.snd .v0)))
                  (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                    (.pair (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd .v0))))))))
                  ρ₁ h rfl (hHB.1 t0)
                have hKk2 : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
                    (.pair (.fst (.snd (.snd (.snd .v0))))
                      (.snd (.snd (.snd (.snd (.snd .v0)))))))).eval ρ₁ =
                    (cka.receive γ0 Tn).2 := by
                  simp [ρ₁, hRecv, Expr.eval, Expr.v0]
                rw [hKk2, ht1] at hLk
                rw [eval_bind, hLk.1, StateT.run_bind, bind_map_left, map_bind]
                refine bind_congr fun ⟨k', h₁⟩ => ?_
                simp [ρ₁, hRecv, hPrngUp, hFsInitR, StateT.run_pure, eval_ret, Prod.map,
                  Expr.eval, Expr.v0, Expr.v1]
      · simp [hc1, ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
    · simp only [Expr.eval, ↓reduceIte]
      rw [eval_ite, and_eval, hAdmiss1, hHealEq1]
      by_cases hcMain : ((Bool.not (decide (qep + 1 < t0)) &&
          _root_.CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t0) &&
          (tL.isSome && (t0 == healEpoch tL))) = true
      · simp [hcMain, ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
      · simp [hcMain, ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
  · rw [eval_caseOpt_some (hHonEval.trans hhon), eval_ret]
    dsimp only
    simp only [StateT.run_pure]
    cases optIdx <;>
      simp [ρ₁, hRecv, hFsInitR, Prod.map, Expr.eval, Expr.v0, Expr.v1]

end BucketHookEvalA

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthEvalHooks
