/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFs -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds

/-!
# Generic Weighted AST-Size Bound for `BucketPRNGAuth.redFSAuthMultiBucketProg`-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthCostB

public section

set_option autoImplicit false

open _root_.ReductionDsl (Sig Ty Var Ops Iface Expr Comp bits)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.SM.Construction (Header healEpoch)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_pos bits_succ_le)
open Computational.Proofs.SessionCostedFig8.Bundles (compSizeW ckaOpS ckaSampS exprSizeW
  exprSizeW_renameM compSizeW_renameM)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFs (fsMultiQueryS fsMultiQueryS_apply)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (
  exprSizeW_var exprSizeW_v0 exprSizeW_v1 exprSizeW_v2 exprSizeW_v3
  exprSizeW_v4 exprSizeW_v5 exprSizeW_v6 exprSizeW_v7 exprSizeW_unit
  exprSizeW_bool exprSizeW_nat exprSizeW_none exprSizeW_nil exprSizeW_add
  exprSizeW_sub exprSizeW_mulK exprSizeW_divK exprSizeW_modK exprSizeW_lt
  exprSizeW_eqN exprSizeW_not exprSizeW_and exprSizeW_ite exprSizeW_pair
  exprSizeW_fst exprSizeW_snd exprSizeW_inl exprSizeW_inr exprSizeW_some
  exprSizeW_caseOpt exprSizeW_caseSum exprSizeW_letE exprSizeW_op exprSizeW_cons
  exprSizeW_len exprSizeW_take exprSizeW_appendL exprSizeW_findB exprSizeW_anyB
  exprSizeW_mapB exprSizeW_foldrB exprSizeW_tconst exprSizeW_tget exprSizeW_tset
  compSizeW_ret compSizeW_bind compSizeW_ite compSizeW_caseOpt compSizeW_caseSum
  compSizeW_sample compSizeW_query compSizeW_iter bits_zero bits_one
  bits_two bits_three bits_four optNatLit_sizeW HooksSizeBounded
  cInTransitE_sizeW_le vSendC_sizeW_le vRecvC_sizeW_le commitEC_sizeW_le)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (
  redFSAuthMultiBucketProg postLeakBucketE pbaTableLookupE pbaTableEntryTy mbHsCache
  mbHsTableTbl mbHsSessionsTbl mbHsBook mbHsLfWin mbHsMk mbHsSetCache mbHsSetTableAt
  mbHsSetSessionsAt mbHsSetBookAt mbHsGetBookAt mbHsSetLfWin mbHsEmptyE lookupMultiBucketFC
  sessionsMemBucketE sessionsIdxOfBucketE sessionsLenBucketE sessionsAppendOneBucketE
  regSessMultiBucketE regSessOptMultiBucketE validGuessBucketParAuthE rootFSMultiBucketAuthC
  fsMultiBucketAuthStartSendC isHonestHdrMultiBucketE fsMultiBucketAuthStartRecvC
  fsTransFindBucketE fsTransFilterBucketE fsMultiBucketAuthFsSendC fsMultiBucketAuthFsRecvC
  fsMultiBucketAuthCommitC rangeListBucketC isExtMultiBucketEntryE anyExtMultiBucketVRE
  unliftMultiBucketEntryE unliftMultiBucketVRE fsMultiBucketAuthRevealC hooksFSMultiBucketAuthC
  initFSMultiBucketAuthEStateC fsMultiBucketVpTy fsMultiBucketHsTy fsMultiBucketRedEsTy
  fsaeadMultiBucketIface)

section GenericCkaSizeW

set_option linter.unusedSimpArgs false


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

local notation "S_cka" => _root_.CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  _root_.CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM_cka" =>
  @fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "mVpT" => @fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsT" => @fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E

private theorem postLeakBucketE_sizeW_le (B0 : ℕ) (tL : Option ℕ) {vpT : Ty S_cka} {Γ'}
    (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) :
    exprSizeW (ckaOpS B0) (postLeakBucketE tL ctx) ≤
      exprSizeW (ckaOpS B0) ctx + bits (tL.getD 0) + 25 := by
  cases tL <;> ·
    simp only [postLeakBucketE, _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.Engine.optNatLit, Option.getD,
      exprSizeW_renameM, exprSizeW_letE, exprSizeW_caseOpt, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some, exprSizeW_not,
      exprSizeW_lt, exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd]
    omega

private theorem validGuessBucketParAuthE_sizeW_le (B0 : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (tE : Expr OO_cka Γ' .nat) :
    exprSizeW (ckaOpS B0) (validGuessBucketParAuthE 1 tL par tE) ≤
      8 * exprSizeW (ckaOpS B0) tE + 4 * bits (tL.getD 0) + 120 := by
  cases tL <;> cases par <;> ·
    simp only [validGuessBucketParAuthE, _root_.CryptoGames.SM.validGuessE,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.optNatEqE,
      _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxN,
      _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.receiverOfE,
      _root_.CryptoGames.SM.senderOfE, _root_.CryptoGames.SM.Engine.optNatLit, Option.getD,
      exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_some, exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN,
      exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_caseOpt, exprSizeW_letE, bits_zero, bits_one, bits_two, bits_three, bits_four,
      Nat.reduceAdd]
    omega

private theorem pbaTableLookupE_sizeW_le (B0 L : ℕ) {Γ'}
    (tblE : Expr OO_cka Γ' (.list (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.pbaTableEntryTy
      KC Γ CCoins T I KR RSt K SS RS M E)))
    (ikE : Expr OO_cka Γ' (.base .i)) :
    exprSizeW (ckaOpS B0) (pbaTableLookupE L tblE ikE) ≤
      exprSizeW (ckaOpS B0) tblE + exprSizeW (ckaOpS B0) ikE + bits L + 400 := by
  simp only [pbaTableLookupE, ckaOpS, exprSizeW_renameM,
    exprSizeW_letE, exprSizeW_pair, exprSizeW_foldrB, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_none, exprSizeW_some,
    exprSizeW_ite, exprSizeW_op, Nat.reduceAdd]
  omega

private theorem lookupMultiBucketFC_sizeW_le (B0 L qep qR : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT) (tE : Expr OO_cka Γ' .nat) (ikE : Expr OO_cka Γ' (.base .i)) :
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
      (lookupMultiBucketFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE tE ikE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) ikE +
        bits L + 600 := by
  let Γ0 := Ty.prod mbHsT (.prod .nat (.base .i)) :: Γ'
  have hlk := pbaTableLookupE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ0)
    (.tget (mbHsTableTbl (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd .v0))
  simp only [mbHsTableTbl, exprSizeW_tget, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0,
    Nat.reduceAdd] at hlk
  simp only [lookupMultiBucketFC, mbHsSetTableAt, mbHsMk, mbHsCache, mbHsTableTbl,
    mbHsSessionsTbl, mbHsBook, mbHsLfWin, ckaSampS, exprSizeW_renameM, compSizeW_renameM,
    compSizeW_bind, compSizeW_ret, compSizeW_caseOpt, compSizeW_sample,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_var,
    exprSizeW_unit, exprSizeW_cons, exprSizeW_tget, exprSizeW_tset, Nat.reduceAdd]
  omega

private theorem regSessMultiBucketE_sizeW_le (B0 L : ℕ) (gMain : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT) (tE : Expr OO_cka Γ' .nat) (ikE : Expr OO_cka Γ' (.base .i)) :
    exprSizeW (ckaOpS B0)
      (regSessMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L gMain tL hE tE ikE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) ikE) +
        6 * bits L + 2 * bits (healEpoch tL) + 2500 := by
  cases gMain <;> ·
    simp only [regSessMultiBucketE, sessionsMemBucketE, sessionsIdxOfBucketE,
      sessionsLenBucketE, sessionsAppendOneBucketE, mbHsSetSessionsAt, mbHsMk, mbHsCache,
      mbHsTableTbl, mbHsSessionsTbl, mbHsBook, mbHsLfWin, _root_.CryptoGames.SM.orE,
      ckaOpS, exprSizeW_renameM, Bool.false_eq_true, ↓reduceIte,
      exprSizeW_letE, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_ite,
      exprSizeW_foldrB, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_nil, exprSizeW_cons, exprSizeW_add,
      exprSizeW_sub, exprSizeW_mulK, exprSizeW_op, exprSizeW_tget, exprSizeW_tset,
      bits_zero, bits_one, Nat.reduceAdd]
    omega

private theorem regSessOptMultiBucketE_sizeW_le (B0 L : ℕ) (gMain : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT) (tE : Expr OO_cka Γ' .nat)
    (sidE : Expr OO_cka Γ' (.opt (.base .i))) :
    exprSizeW (ckaOpS B0)
      (regSessOptMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L gMain tL hE tE sidE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) sidE) +
        12 * bits L + 4 * bits (healEpoch tL) + 5200 := by
  let Γ0 : List (Ty S_cka) := .base .i :: .prod mbHsT (.prod .nat (.opt (.base .i))) :: Γ'
  have hreg := regSessMultiBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L gMain tL (Γ' := Γ0)
    (.fst .v1) (.fst (.snd .v1)) .v0
  simp only [exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd] at hreg
  simp only [regSessOptMultiBucketE, exprSizeW_renameM,
    exprSizeW_letE, exprSizeW_pair, exprSizeW_caseOpt, exprSizeW_none, exprSizeW_some,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd]
  omega

private theorem rootFSMultiBucketAuthC_sizeW_le (B0 L qep qR : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ'} (hE : Expr OO_cka Γ' mbHsT) (tE : Expr OO_cka Γ' .nat) (plE : Expr OO_cka Γ' .bool)
    (ikE : Expr OO_cka Γ' (.base .i)) (σE : Expr OO_cka Γ' (.base .sig)) :
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
      (rootFSMultiBucketAuthC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 1 qep tL par hE tE plE ikE σE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) plE +
        exprSizeW (ckaOpS B0) ikE + exprSizeW (ckaOpS B0) σE +
        2 * bits L + 3 * bits qep + 4 * bits (tL.getD 0) + 3 * bits (healEpoch tL) + 5000 := by
  have hbq1 := bits_succ_le qep
  let Γ0 : List (Ty S_cka) :=
    .prod mbHsT (.prod .nat (.prod .bool (.prod (.base .i) (.base .sig)))) :: Γ'
  have hvg := validGuessBucketParAuthE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))
  have hlk := lookupMultiBucketFC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR (Γ' := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0))))
  simp only [exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, Nat.reduceAdd] at hvg hlk
  simp only [rootFSMultiBucketAuthC, _root_.CryptoGames.SM.orE, ckaOpS, ckaSampS,
    exprSizeW_renameM, compSizeW_renameM,
    compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_sample,
    exprSizeW_letE, exprSizeW_caseOpt,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
    exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
    exprSizeW_some, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_op, bits_zero, bits_one, Nat.reduceAdd]
  omega

private theorem validGuessE3_sizeW_le (B0 : ℕ) (tL : Option ℕ) {Γ'} (tE : Expr OO_cka Γ' .nat) :
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.validGuessE 3 (_root_.CryptoGames.SM.Engine.optNatLit tL) tE) ≤
      8 * exprSizeW (ckaOpS B0) tE + 4 * bits (tL.getD 0) + 100 := by
  cases tL <;> ·
    simp only [_root_.CryptoGames.SM.validGuessE, _root_.CryptoGames.SM.healedByE,
      _root_.CryptoGames.SM.optNatEqE, _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN,
      _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.receiverOfE,
      _root_.CryptoGames.SM.Engine.optNatLit, Option.getD, exprSizeW_renameM,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_some, exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
      exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_caseOpt, exprSizeW_letE, bits_zero, bits_one, bits_two, bits_three, bits_four,
      Nat.reduceAdd]
    omega

private theorem fsTransFindBucketE_sizeW_le (B0 L : ℕ) {Γ'}
    (trE : Expr OO_cka Γ' (.list (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketTransEntryTy
      KC Γ CCoins T I KR RSt K SS RS M E)))
    (hcE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprSizeW (ckaOpS B0)
      (fsTransFindBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L trE hcE) ≤
      exprSizeW (ckaOpS B0) trE + exprSizeW (ckaOpS B0) hcE + bits L + 1000 := by
  simp only [fsTransFindBucketE, _root_.CryptoGames.SM.Engine.hdrCtEqE,
    _root_.CryptoGames.SM.Engine.optTEqE, ckaOpS, exprSizeW_renameM,
    exprSizeW_letE, exprSizeW_pair, exprSizeW_findB, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_bool, exprSizeW_eqN, exprSizeW_and, exprSizeW_caseOpt, exprSizeW_op, Nat.reduceAdd]
  omega

private theorem fsTransFilterBucketE_sizeW_le (B0 L : ℕ) {Γ'}
    (trE : Expr OO_cka Γ' (.list (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketTransEntryTy
      KC Γ CCoins T I KR RSt K SS RS M E)))
    (dropE : Expr OO_cka Γ' .nat) :
    exprSizeW (ckaOpS B0) (fsTransFilterBucketE L trE dropE) ≤
      exprSizeW (ckaOpS B0) trE + exprSizeW (ckaOpS B0) dropE + bits L + 100 := by
  simp only [fsTransFilterBucketE, exprSizeW_renameM,
    exprSizeW_letE, exprSizeW_pair, exprSizeW_foldrB, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_nil, exprSizeW_cons,
    exprSizeW_eqN, exprSizeW_not, exprSizeW_ite, Nat.reduceAdd]
  omega

private theorem rangeListBucketC_sizeW_le (B0 L qep qR : ℕ) {Γ' : List (Ty S_cka)} :
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
      (rangeListBucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L (Γ' := Γ')) ≤ bits L + 30 := by
  simp only [rangeListBucketC, compSizeW_bind, compSizeW_iter, compSizeW_ret,
    exprSizeW_pair, exprSizeW_nat, exprSizeW_nil, exprSizeW_add, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_cons, exprSizeW_v0, bits_zero, bits_one, Nat.reduceAdd]
  omega

private theorem anyExtMultiBucketVRE_sizeW_le (B0 L : ℕ) {Γ'}
    (vRE : Expr OO_cka Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO_cka Γ' (.list .nat)) :
    exprSizeW (ckaOpS B0)
      (anyExtMultiBucketVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L vRE rngE) ≤
      exprSizeW (ckaOpS B0) vRE + exprSizeW (ckaOpS B0) rngE + bits L + 100 := by
  simp only [anyExtMultiBucketVRE, isExtMultiBucketEntryE, exprSizeW_renameM,
    exprSizeW_letE, exprSizeW_pair, exprSizeW_foldrB, exprSizeW_ite, exprSizeW_caseOpt,
    exprSizeW_caseSum, exprSizeW_tget, exprSizeW_fst, exprSizeW_snd, exprSizeW_bool,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, Nat.reduceAdd]
  omega

private theorem unliftMultiBucketVRE_sizeW_le (B0 L : ℕ) {Γ'}
    (vRE : Expr OO_cka Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO_cka Γ' (.list .nat)) :
    exprSizeW (ckaOpS B0)
      (unliftMultiBucketVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L vRE rngE) ≤
      exprSizeW (ckaOpS B0) vRE + exprSizeW (ckaOpS B0) rngE + bits L + 150 := by
  simp only [unliftMultiBucketVRE, unliftMultiBucketEntryE, exprSizeW_renameM,
    exprSizeW_letE, exprSizeW_pair, exprSizeW_foldrB, exprSizeW_caseOpt, exprSizeW_caseSum,
    exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset, exprSizeW_none, exprSizeW_some,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    Nat.reduceAdd]
  omega

private theorem fsMultiBucketAuthRevealC_sizeW_le (B0 L qep qR : ℕ) (gMain la : Bool)
    (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpT))
    (pE : Expr OO_cka Γ' .bool) (vpE : Expr OO_cka Γ' mVpT) :
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
      (fsMultiBucketAuthRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L gMain la tL hE ctxE pE vpE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) vpE +
        16 * bits (qep + qR + B0 + 1) + 3 * bits L + 2 * bits (healEpoch tL) + 17000 := by
  let tupT : Ty S_cka := .prod mbHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpT) mVpT)
  let Γ0 : List (Ty S_cka) :=
    .opt (.base .ss) :: .prod (.opt (.opt (.base .ss))) mbHsT :: tupT :: Γ'
  let Γ1 : List (Ty S_cka) := .list .nat :: Γ0
  have hrng := rangeListBucketC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR (Γ' := Γ0)
  have hany := anyExtMultiBucketVRE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
    (_root_.CryptoGames.SM.Engine.vpVR (.snd (.snd .v3))) .v0
  have hunl := unliftMultiBucketVRE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
    (_root_.CryptoGames.SM.Engine.vpVR (.snd (.snd .v3))) .v0
  simp only [_root_.CryptoGames.SM.Engine.vpVR, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_v0, exprSizeW_v3, Nat.reduceAdd] at hany hunl
  simp only [fsMultiBucketAuthRevealC, _root_.CryptoGames.SM.Engine.vpTcurNat,
    _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
    _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpRoot,
    _root_.CryptoGames.SM.Engine.vpId, _root_.CryptoGames.SM.Engine.vpTcur,
    _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk,
    _root_.CryptoGames.SM.Engine.cGsEpoch, _root_.CryptoGames.SM.maxN,
    _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.orE,
    mbHsGetBookAt, mbHsSetBookAt, mbHsMk, mbHsCache, mbHsTableTbl, mbHsSessionsTbl, mbHsBook,
    mbHsLfWin, fsMultiQueryS_apply, exprSizeW_renameM, compSizeW_renameM,
    compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
    compSizeW_query,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
    exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_var, exprSizeW_unit, exprSizeW_bool,
    exprSizeW_nat, exprSizeW_none,
    exprSizeW_nil, exprSizeW_some, exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_tget, exprSizeW_tset,
    bits_zero, bits_one, bits_two, Nat.reduceAdd]
  omega

private theorem hooksFSMultiBucketAuthC_sr_sizeBounded (B0 L qep qR : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool) :
    HooksSizeBounded B0 ckaSampS (fsMultiQueryS qep qR B0)
      { hooksFSMultiBucketAuthC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B0 1 qep gMain tL par la with
        startSend := fun h _ _ _ _ _ _ => .ret (.pair .none h)
        reveal := fun h _ _ _ => .ret (.pair .none h) }
      (24 * bits L + 4 * bits qep + 16 * bits (tL.getD 0) + 18 * bits (healEpoch tL) + 20000)
      (48 * bits (qep + qR + B0 + 1) + 39000)
      (48 * bits (qep + qR + B0 + 1) + 5 * bits B0 + 5 * bits L + 45000) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Γ' hE ctxE pE tE γE σE rE
    simp only [compSizeW_ret, exprSizeW_pair, exprSizeW_none, Nat.reduceAdd]
    omega
  · intro Γ' hE ctxE pE tE γE σE tnE
    have hbq1 := bits_succ_le qep
    let tupT : Ty S_cka :=
      .prod mbHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpT)
        (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.base .t)))))
    let Γ0 : List (Ty S_cka) := tupT :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.base .k) mbHsT :: Γ0
    have hpl := postLeakBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL (vpT := mVpT) (Γ' := Γ0) (.fst (.snd .v0))
    have hvg3 := validGuessE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL (Γ' := Γ0) (.fst (.snd (.snd .v0)))
    have hvgP := validGuessBucketParAuthE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd (.snd .v0)))
    have hlk := lookupMultiBucketFC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L qep qR (Γ' := Γ0)
      (.fst .v0) (.fst (.snd (.snd .v0)))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd .v0))))))))
    have hreg := regSessMultiBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L false tL (Γ' := Γ1)
      (.snd .v0) (.fst (.snd (.snd .v1)))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd (.snd .v1))))))))
    simp only [ckaOpS, exprSizeW_fst, exprSizeW_snd, exprSizeW_pair, exprSizeW_op,
      exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd] at hpl hvg3 hvgP hlk hreg
    dsimp only [hooksFSMultiBucketAuthC]
    simp only [fsMultiBucketAuthStartRecvC, mbHsCache, ckaOpS, exprSizeW_renameM,
      compSizeW_renameM, compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1,
      exprSizeW_v2, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some,
      exprSizeW_inl, exprSizeW_inr, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and,
      exprSizeW_ite, exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tget, Nat.reduceAdd]
    omega
  · intro Γ' hE ctxE pE tE ssvE hdrE mE pairE
    dsimp only [hooksFSMultiBucketAuthC]
    simp only [fsMultiBucketAuthFsSendC, _root_.CryptoGames.SM.Engine.cSafeChE,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.pGet,
      _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cGsEpoch,
      mbHsGetBookAt, mbHsSetBookAt, mbHsMk, mbHsCache, mbHsTableTbl, mbHsSessionsTbl, mbHsBook,
      mbHsLfWin, ckaOpS, fsMultiQueryS_apply, exprSizeW_renameM, compSizeW_renameM,
      compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
      compSizeW_query,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
      exprSizeW_v3, exprSizeW_v4, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_nil, exprSizeW_some, exprSizeW_inl, exprSizeW_inr, exprSizeW_cons,
      exprSizeW_add, exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_op, exprSizeW_tget, exprSizeW_tset,
      bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
    omega
  · intro Γ' hE ctxE pE tE rsvE hdrE eE recE
    let hdrT := _root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
    let tupT : Ty S_cka :=
      .prod mbHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpT)
        (.prod .nat (.prod (.sum (.base .rs) .nat) (.prod hdrT
          (.prod (.base .ct) (.opt _root_.CryptoGames.SM.Engine.cRecTy))))))
    let rrT : Ty S_cka := .sum .unit (.prod .nat (.opt (.base .msg)))
    let Γ_inr : List (Ty S_cka) := .nat :: tupT :: Γ'
    let Γ_ok : List (Ty S_cka) := .prod .bool mbHsT :: Γ_inr
    let Γ_res : List (Ty S_cka) := .prod .nat (.opt (.base .msg)) :: rrT :: .opt rrT :: Γ_ok
    have htf0 := fsTransFindBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_inr)
      (.snd (.snd (mbHsGetBookAt (.fst .v1) .v0)))
      (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))))
    have htf_ok := fsTransFindBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_ok)
      (.snd (.snd (mbHsGetBookAt (.fst .v2) .v1)))
      (.pair (.fst (.snd (.snd (.snd (.snd .v2))))) (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))
    have htf1 := fsTransFindBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_res)
      (.snd (.snd (mbHsGetBookAt (.fst .v5) .v4)))
      (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5)))))))
    have htflt := fsTransFilterBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_res)
      (.snd (.snd (mbHsGetBookAt (.snd .v3) .v4)))
      (.caseOpt (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (.fst .v5) .v4)))
        (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
        (.fst .v0) (.fst .v0))
    simp only [mbHsGetBookAt, mbHsBook, exprSizeW_renameM,
      exprSizeW_caseOpt, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
      exprSizeW_var,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_nil, exprSizeW_tget, bits_zero, Nat.reduceAdd]
      at htf0 htf_ok htf1 htflt
    simp only [hooksFSMultiBucketAuthC, fsMultiBucketAuthFsRecvC,
      _root_.CryptoGames.SM.Engine.cRecMsg,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.pGet,
      _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cGsEpoch,
      mbHsGetBookAt, mbHsSetBookAt, mbHsSetLfWin, mbHsMk, mbHsCache, mbHsTableTbl,
      mbHsSessionsTbl, mbHsBook, mbHsLfWin, ckaOpS, fsMultiQueryS_apply,
      exprSizeW_renameM, compSizeW_renameM,
      compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
      compSizeW_query,
      exprSizeW_letE, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1,
      exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_var, exprSizeW_unit,
      exprSizeW_bool,
      exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_some, exprSizeW_inl, exprSizeW_inr,
      exprSizeW_add, exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_caseOpt,
      exprSizeW_op, exprSizeW_tget, exprSizeW_tset,
      bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
    generalize bits B0 = bB at *
    omega
  · intro Γ' hE ctxE pE oldE newE
    simp only [hooksFSMultiBucketAuthC, fsMultiBucketAuthCommitC,
      compSizeW_ret, exprSizeW_pair, exprSizeW_some, Nat.reduceAdd]
    omega
  · intro Γ' hE ctxE pE vpE
    simp only [compSizeW_ret, exprSizeW_pair, exprSizeW_none, Nat.reduceAdd]
    omega

private theorem hooksFSMultiBucketAuthC_cm_sizeBounded (B0 L qep qR : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool) :
    HooksSizeBounded B0 ckaSampS (fsMultiQueryS qep qR B0)
      { hooksFSMultiBucketAuthC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 1 qep gMain tL par la with
        startSend := fun h _ _ _ _ _ _ => .ret (.pair .none h)
        startRecv := fun h _ _ _ _ _ _ => .ret (.pair .none h)
        reveal := fun h _ _ _ => .ret (.pair .none h) }
      10 (48 * bits (qep + qR + B0 + 1) + 39000)
      (48 * bits (qep + qR + B0 + 1) + 5 * bits B0 + 5 * bits L + 45000) := by
  have hsr := hooksFSMultiBucketAuthC_sr_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR gMain tL par la
  refine ⟨fun _ _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ => ?_, hsr.fsSend_le, hsr.fsRecv_le,
    fun _ _ _ _ _ => ?_, fun _ _ _ _ => ?_⟩
  · simp only [compSizeW_ret, exprSizeW_pair, exprSizeW_none, Nat.reduceAdd]; omega
  · simp only [compSizeW_ret, exprSizeW_pair, exprSizeW_none, Nat.reduceAdd]; omega
  · simp only [hooksFSMultiBucketAuthC, fsMultiBucketAuthCommitC,
      compSizeW_ret, exprSizeW_pair, exprSizeW_some, Nat.reduceAdd]; omega
  · simp only [compSizeW_ret, exprSizeW_pair, exprSizeW_none, Nat.reduceAdd]; omega

private theorem hooksFSMultiBucketAuthC_sizeBounded (B0 L qep qR : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool) :
    HooksSizeBounded B0 ckaSampS (fsMultiQueryS qep qR B0)
      (hooksFSMultiBucketAuthC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 qep gMain tL par la)
      (16 * bits (qep + qR + B0 + 1) + 90 * bits L + 4 * bits qep + 16 * bits (tL.getD 0) +
        35 * bits (healEpoch tL) + 50000)
      (48 * bits (qep + qR + B0 + 1) + 39000)
      (48 * bits (qep + qR + B0 + 1) + 5 * bits B0 + 5 * bits L + 45000) := by
  have hsr := hooksFSMultiBucketAuthC_sr_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR gMain tL par la
  refine ⟨?_, fun hE ctxE pE tE γE σE tnE => (hsr.startRecv_le hE ctxE pE tE γE σE tnE).trans (by omega),
    hsr.fsSend_le, hsr.fsRecv_le,
    fun hE ctxE pE oldE newE => (hsr.commit_le hE ctxE pE oldE newE).trans (by omega), ?_⟩
  · intro Γ' hE ctxE pE tE γE σE rE
    let tupT : Ty S_cka :=
      .prod mbHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpT)
        (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.opt (.base .ccoins))))))
    let Γ0 : List (Ty S_cka) := .base .ccoins :: tupT :: Γ'
    let Γ1 : List (Ty S_cka) :=
      .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsT :: Γ0
    have hpl := postLeakBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL (vpT := mVpT) (Γ' := Γ0) (.fst (.snd .v1))
    have hrt := rootFSMultiBucketAuthC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L qep qR tL par (Γ' := Γ0)
      (.fst .v1) (.fst (.snd (.snd .v1)))
      (postLeakBucketE tL (.fst (.snd .v1)))
      (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend
        (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))))
      (.fst (.snd (.snd (.snd (.snd .v1)))))
    have hreg := regSessOptMultiBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L gMain tL (Γ' := Γ1)
      (.snd .v0) (.fst (.snd (.snd .v2))) (.snd (.snd (.fst .v0)))
    simp only [ckaOpS, exprSizeW_fst, exprSizeW_snd, exprSizeW_pair, exprSizeW_op,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, Nat.reduceAdd] at hpl hrt hreg
    simp only [hooksFSMultiBucketAuthC, fsMultiBucketAuthStartSendC, mbHsSetCache, mbHsMk,
      mbHsCache, mbHsTableTbl, mbHsSessionsTbl, mbHsBook, mbHsLfWin, ckaOpS, ckaSampS,
      exprSizeW_renameM, compSizeW_bind, compSizeW_ret, compSizeW_caseOpt, compSizeW_sample,
      exprSizeW_letE, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1,
      exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_unit, exprSizeW_some, exprSizeW_inl,
      exprSizeW_inr, exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tset, Nat.reduceAdd]
    omega
  · intro Γ' hE ctxE pE vpE
    exact (fsMultiBucketAuthRevealC_sizeW_le B0 L qep qR gMain la tL hE ctxE pE vpE).trans
      (by omega)

private theorem cEpMgmtE3_sizeW_le {vpT : Ty S_cka} (B0 qep : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p bad : Expr OO_cka Γ' .bool) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cEpMgmtE (2 + 1) qep s p bad) ≤
      20 * (exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) p + exprSizeW (ckaOpS B0) bad) +
        4 * bits qep + 1000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cEpMgmtE, _root_.CryptoGames.SM.Engine.cSafeChE,
    _root_.CryptoGames.SM.Engine.cLeakE, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.healedByE,
    _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet, _root_.CryptoGames.SM.boolEq,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some, exprSizeW_cons,
    exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and,
    exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt,
    exprSizeW_letE, bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
  omega

private theorem cRecordE3_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr OO_cka Γ' .bool) (st' : Expr OO_cka Γ' vpT)
    (r : Expr OO_cka Γ' _root_.CryptoGames.SM.Engine.cRecTy)
    (isChall : Expr OO_cka Γ' .bool) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cRecordE L (2 + 1) s p st' r isChall) ≤
      20 * (exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) p + exprSizeW (ckaOpS B0) st' +
        exprSizeW (ckaOpS B0) r + exprSizeW (ckaOpS B0) isChall) + 4 * bits L + 1000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cRecordE, _root_.CryptoGames.SM.Engine.cSafeChE,
    _root_.CryptoGames.SM.Engine.cCompInsertE, _root_.CryptoGames.SM.Engine.cCompSetE,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_cons, exprSizeW_add, exprSizeW_lt,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_tget, exprSizeW_tset, bits_three, Nat.reduceAdd]
  omega

private theorem cTrivialE3_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (pos : Expr OO_cka Γ' _root_.CryptoGames.SM.posTy) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cTrivialE L (2 + 1) s pos) ≤
      8 * (exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) pos) + 4 * bits L + 500 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cTrivialE, _root_.CryptoGames.SM.Engine.cCompContainsE,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsTrans,
    _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cRecPos,
    _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.orE,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.posEq, _root_.CryptoGames.SM.boolEq,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_add, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    exprSizeW_anyB, exprSizeW_tget, bits_three, Nat.reduceAdd]
  omega

private theorem cCorrAllowedE_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr OO_cka Γ' .bool) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cCorrAllowedE L s p) ≤
      8 * (exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) p) + 4 * bits L + 500 := by
  simp only [_root_.CryptoGames.SM.Engine.cCorrAllowedE,
    _root_.CryptoGames.SM.Engine.cCompContainsE, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsComp,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.pGet,
    _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_var,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_letE, exprSizeW_anyB, exprSizeW_tget, Nat.reduceAdd]
  omega

private theorem cAfterCorrE_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr OO_cka Γ' .bool) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cAfterCorrE L s p) ≤
      40 * (exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) p) + 20 * bits L + 8000 := by
  simp only [_root_.CryptoGames.SM.Engine.cAfterCorrE, _root_.CryptoGames.SM.Engine.cLeakE,
    _root_.CryptoGames.SM.Engine.cCompInsertE, _root_.CryptoGames.SM.Engine.cCompSetE,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet,
    _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    exprSizeW_bool, exprSizeW_some, exprSizeW_cons, exprSizeW_lt,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_foldrB, exprSizeW_tget, exprSizeW_tset,
    Nat.reduceAdd]
  omega

private theorem cAuthOKE3_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (tLStar : Expr OO_cka Γ' (.opt .nat)) (tStar : Expr OO_cka Γ' .nat)
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cAuthOKE L (2 + 1) tLStar tStar s) ≤
      8 * (exprSizeW (ckaOpS B0) tLStar + exprSizeW (ckaOpS B0) tStar + exprSizeW (ckaOpS B0) s) +
        10 * bits L + 500 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cAuthOKE, _root_.CryptoGames.SM.Engine.cCanonE,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.validGuessE, _root_.CryptoGames.SM.healedByE,
    _root_.CryptoGames.SM.optNatEqE, _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.receiverOfE,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some, exprSizeW_add,
    exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    exprSizeW_anyB, exprSizeW_foldrB, bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
  omega

private theorem isHonestHdrMultiBucketE_sizeW_le (B0 : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT)
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprSizeW (ckaOpS B0) (isHonestHdrMultiBucketE hE hdrE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) hdrE) + 500 := by
  simp only [isHonestHdrMultiBucketE, mbHsCache, ckaOpS, exprSizeW_renameM,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_pair,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op,
    exprSizeW_tget, Nat.reduceAdd]
  omega

private theorem deliverEC_bucket_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho_sr Ho_cm Hs Hr L maxSkip : ℕ) (tL : Option ℕ)
    (hhk_sr : HooksSizeBounded B0 sS qS { hk with
      startSend := fun h _ _ _ _ _ _ => .ret (.pair .none h),
      reveal := fun h _ _ _ => .ret (.pair .none h) } Ho_sr Hs Hr)
    (hhk_cm : HooksSizeBounded B0 sS qS { hk with
      startSend := fun h _ _ _ _ _ _ => .ret (.pair .none h),
      startRecv := fun h _ _ _ _ _ _ => .ret (.pair .none h),
      reveal := fun h _ _ _ => .ret (.pair .none h) } Ho_cm Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (_root_.CryptoGames.SM.Engine.esTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compSizeW (ckaOpS B0) sS qS
      (_root_.CryptoGames.SM.Engine.deliverEC hk L maxSkip
        (_root_.CryptoGames.SM.Construction.bucketAuthCfgEC 1 tL) es arg) ≤
      6 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) arg) +
        Ho_sr + Ho_cm + Hr + 9 * bits L + 5 * bits maxSkip + 6000 := by
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := _root_.CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_dl0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  have hit := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_dl0)
    (_root_.CryptoGames.SM.Engine.esG (.fst .v0)) (_root_.CryptoGames.SM.otherE (.fst (.snd .v0)))
    (.snd (.snd .v0))
  have hvr := vRecvC_sizeW_le _ Ho_sr Hs Hr hhk_sr (Γ' := _root_.CryptoGames.SM.Engine.cRecTy :: Γ_dl0)
    (_root_.CryptoGames.SM.Engine.esH (.fst .v1)) (_root_.CryptoGames.SM.Engine.esG (.fst .v1))
    (.fst (.snd .v1))
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd .v1)) (.some .v0)
  have hcm := commitEC_sizeW_le _ Ho_cm Hs Hr L hhk_cm
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: _root_.CryptoGames.SM.Engine.cRecTy :: Γ_dl0)
    (_root_.CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (_root_.CryptoGames.SM.Engine.cRecPos .v3)
  change compSizeW (ckaOpS B0) sS qS (_root_.CryptoGames.SM.Engine.vRecvC hk _ _ _ _ _ _) ≤ _ at hvr
  change compSizeW (ckaOpS B0) sS qS (_root_.CryptoGames.SM.Engine.commitEC hk L _ _ _ _ _ _) ≤ _ at hcm
  simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
    _root_.CryptoGames.SM.Engine.esSetH, _root_.CryptoGames.SM.Engine.esMk,
    _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.pGet,
    _root_.CryptoGames.SM.otherE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3,
    exprSizeW_v4, exprSizeW_var, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_some, exprSizeW_letE, Nat.reduceAdd] at hit hvr hcm
  simp only [_root_.CryptoGames.SM.Engine.deliverEC, _root_.CryptoGames.SM.Engine.cCompContainsE,
    _root_.CryptoGames.SM.Engine.cChallContainsE, _root_.CryptoGames.SM.Engine.cMustBeCorrectE,
    _root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG,
    _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.esAbort,
    _root_.CryptoGames.SM.Engine.esSetG, _root_.CryptoGames.SM.Engine.esSetH,
    _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSetWin,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cRecMsg,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.otherE,
    _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxAccGet, _root_.CryptoGames.SM.posEq,
    _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch,
    _root_.CryptoGames.SM.posIdx, ckaOpS, exprSizeW_renameM, compSizeW_renameM,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_mulK, exprSizeW_divK,
    exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
    exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
    exprSizeW_len, exprSizeW_take, exprSizeW_appendL, exprSizeW_findB, exprSizeW_anyB,
    exprSizeW_mapB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Bool.false_eq_true, ↓reduceIte,
    Nat.reduceAdd]
  omega

private theorem injectEC_bucket_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho_sr Ho_cm Hs Hr L qep : ℕ) (tL : Option ℕ)
    (hhk_sr : HooksSizeBounded B0 sS qS { hk with
      startSend := fun h _ _ _ _ _ _ => .ret (.pair .none h),
      reveal := fun h _ _ _ => .ret (.pair .none h) } Ho_sr Hs Hr)
    (hhk_cm : HooksSizeBounded B0 sS qS { hk with
      startSend := fun h _ _ _ _ _ _ => .ret (.pair .none h),
      startRecv := fun h _ _ _ _ _ _ => .ret (.pair .none h),
      reveal := fun h _ _ _ => .ret (.pair .none h) } Ho_cm Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (_root_.CryptoGames.SM.Engine.esTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compSizeW (ckaOpS B0) sS qS
      (_root_.CryptoGames.SM.Engine.injectEC hk L (2 + 1) qep
        (_root_.CryptoGames.SM.Construction.bucketAuthCfgEC 1 tL) es arg) ≤
      6 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) arg) +
        Ho_sr + Ho_cm + Hr + 10 * bits L + 4 * bits qep + 6 * bits (tL.getD 0) + 6000 := by
  have hbq1 := bits_succ_le qep
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := _root_.CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_ij0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  let Γ_ij1 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0
  have hit := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij0)
    (_root_.CryptoGames.SM.Engine.esG (.fst .v0)) (_root_.CryptoGames.SM.otherE (.fst (.snd .v0)))
    (.snd (.snd .v0))
  have hvr := vRecvC_sizeW_le _ Ho_sr Hs Hr hhk_sr (Γ' := Γ_ij0)
    (_root_.CryptoGames.SM.Engine.esH (.fst .v0)) (_root_.CryptoGames.SM.Engine.esG (.fst .v0))
    (.fst (.snd .v0))
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v0))) (.fst (.snd .v0)))
    (.snd (.snd .v0)) .none
  have htrv := cTrivialE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij1)
    (_root_.CryptoGames.SM.Engine.esG (.fst .v3))
    (.pair (_root_.CryptoGames.SM.otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_sizeW_le _ Ho_cm Hs Hr L hhk_cm (Γ' := Γ_ij1)
    (_root_.CryptoGames.SM.Engine.esSetH (.fst .v3) (.snd .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3))
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0)
    (.pair (_root_.CryptoGames.SM.otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  change compSizeW (ckaOpS B0) sS qS (_root_.CryptoGames.SM.Engine.vRecvC hk _ _ _ _ _ _) ≤ _ at hvr
  change compSizeW (ckaOpS B0) sS qS (_root_.CryptoGames.SM.Engine.commitEC hk L _ _ _ _ _ _) ≤ _ at hcm
  have hvg := validGuessE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (Γ' := Γ_ij1) (.fst (.snd .v0))
  simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
    _root_.CryptoGames.SM.Engine.esSetH, _root_.CryptoGames.SM.Engine.esMk,
    _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_none, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_letE, Nat.reduceAdd] at hit hvr htrv hcm hvg
  simp only [_root_.CryptoGames.SM.Engine.injectEC,
    _root_.CryptoGames.SM.Construction.bucketAuthCfgEC,
    _root_.CryptoGames.SM.Engine.cSafeInjE, _root_.CryptoGames.SM.healedByE,
    _root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG,
    _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.esAbort,
    _root_.CryptoGames.SM.Engine.esSetG, _root_.CryptoGames.SM.Engine.esSetH,
    _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSetWin,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.otherE,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.minN,
    exprSizeW_renameM, compSizeW_renameM,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_some, exprSizeW_inl, exprSizeW_inr, exprSizeW_add,
    exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
  omega

private theorem initFSMultiBucketAuthEStateC_sizeW_le (B0 L qep qR : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ'} (bE : Expr OO_cka Γ' .bool) :
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
      (initFSMultiBucketAuthEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 1 qep gMain tL par bE) ≤
      exprSizeW (ckaOpS B0) bE +
        65 * bits L + 4 * bits qep + 6 * bits (tL.getD 0) + 25 * bits (healEpoch tL) + 40000 := by
  let Γ0 : List (Ty S_cka) := .base .kc :: .base .kr :: .bool :: Γ'
  let Γ1 : List (Ty S_cka) :=
    .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsT :: Γ0
  have hrt := rootFSMultiBucketAuthC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR tL par (Γ' := Γ0)
    mbHsEmptyE (.nat 0) (.bool false)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.lamI .unit)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.prngInit .v1)
  have hreg := regSessOptMultiBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L true tL (Γ' := Γ1)
    (.snd .v0) (.nat 0) (.snd (.snd (.fst .v0)))
  simp only [mbHsEmptyE, mbHsMk, ckaOpS, exprSizeW_pair, exprSizeW_tconst, exprSizeW_none,
    exprSizeW_nil, exprSizeW_bool, exprSizeW_nat, exprSizeW_op, exprSizeW_unit,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, bits_zero, Nat.reduceAdd] at hrt hreg
  cases gMain <;> ·
    simp only [initFSMultiBucketAuthEStateC, _root_.CryptoGames.SM.Engine.mkPartiesE,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk,
      _root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.vpMk,
      mbHsEmptyE, mbHsMk, ↓reduceIte, Bool.false_eq_true,
      ckaOpS, ckaSampS, exprSizeW_renameM, compSizeW_renameM,
      compSizeW_bind, compSizeW_ret, compSizeW_sample,
      exprSizeW_letE, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1,
      exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_nil, exprSizeW_some, exprSizeW_inl, exprSizeW_inr,
      exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tconst, exprSizeW_tset, bits_zero, Nat.reduceAdd]
    omega

/-- Generic weighted AST-size bound for `redFSAuthMultiBucketProg`. -/
theorem redFSAuthMultiBucketProg_generic_sizeW_le
    (B0 L qep qR maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    let R := redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 qep maxSkip gMain la tL par
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.finish ≤
        280 * bits (qep + qR + B0 + 1) + 12 * bits B0 + 290 * bits L + 45 * bits qep +
          130 * bits (tL.getD 0) + 140 * bits (healEpoch tL) + 10 * bits maxSkip + 410000 := by
  let Ho := 16 * bits (qep + qR + B0 + 1) + 90 * bits L + 4 * bits qep + 16 * bits (tL.getD 0) +
    35 * bits (healEpoch tL) + 50000
  let Ho_sr := 24 * bits L + 4 * bits qep + 16 * bits (tL.getD 0) + 18 * bits (healEpoch tL) + 20000
  let Ho_cm := 10
  let Hs := 48 * bits (qep + qR + B0 + 1) + 39000
  let Hr := 48 * bits (qep + qR + B0 + 1) + 5 * bits B0 + 5 * bits L + 45000
  have hhk : HooksSizeBounded B0 ckaSampS (fsMultiQueryS qep qR B0)
      (hooksFSMultiBucketAuthC L B0 1 qep gMain tL par la) Ho Hs Hr :=
    hooksFSMultiBucketAuthC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L qep qR gMain tL par la
  have hhk_sr := hooksFSMultiBucketAuthC_sr_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR gMain tL par la
  have hhk_cm := hooksFSMultiBucketAuthC_cm_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR gMain tL par la
  have hIF :
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
          (redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
            (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
            L B0 1 qep maxSkip gMain la tL par).init +
        compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
          (redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
            (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
            L B0 1 qep maxSkip gMain la tL par).finish ≤
        78 * bits L + 4 * bits qep + 15 * bits (tL.getD 0) + 25 * bits (healEpoch tL) + 42000 := by
    have hinit := initFSMultiBucketAuthEStateC_sizeW_le (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L qep qR gMain tL par
      (Γ' := [.unit]) (.bool false)
    let Γf : List (Ty S_cka) :=
      .nat :: .prod (_root_.CryptoGames.SM.Engine.esTy mVpT mbHsT) (.opt .nat) ::
        [@fsMultiBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E, .bool]
    have haok := cAuthOKE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 L (Γ' := Γf)
      (_root_.CryptoGames.SM.Engine.optNatLit tL) .v0 (_root_.CryptoGames.SM.Engine.esG (.fst .v1))
    simp only [_root_.CryptoGames.SM.Engine.esG, optNatLit_sizeW, exprSizeW_bool, exprSizeW_fst,
      exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd] at hinit haok
    simp only [redFSAuthMultiBucketProg, mbHsLfWin, _root_.CryptoGames.SM.Engine.esAbort,
      _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
      _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.senderOfE,
      exprSizeW_renameM, compSizeW_renameM,
      compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_unit, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_none, exprSizeW_modK, exprSizeW_eqN, exprSizeW_not, exprSizeW_and,
      exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, bits_one, bits_two,
      Nat.reduceAdd]
    (try split_ifs at haok) <;> omega
  have hH :
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
          (redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
            (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
            L B0 1 qep maxSkip gMain la tL par).handle ≤
        190 * bits (qep + qR + B0 + 1) + 10 * bits B0 + 210 * bits L + 25 * bits qep +
          60 * bits (tL.getD 0) + 80 * bits (healEpoch tL) + 10 * bits maxSkip + 315000 := by
    let esT := _root_.CryptoGames.SM.Engine.esTy mVpT mbHsT
    let stT := @fsMultiBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E
    let qT := _root_.CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
    let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
    let Γh0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [stT, qT]
    let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
    let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
    let dlQ : Ty S_cka := .prod .bool hdrCtT
    let Γ_tr0 : List (Ty S_cka) :=
      trQ :: .sum trQ chQ :: .sum (.sum trQ chQ) dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_tr1 : List (Ty S_cka) := trQ :: Γ_tr0
    let Γ_tr2 : List (Ty S_cka) := _root_.CryptoGames.SM.Engine.cGsTy mVpT :: Γ_tr1
    let Γ_tr3 : List (Ty S_cka) :=
      .prod mVpT hdrCtT :: .prod (.opt (.prod mVpT hdrCtT)) mbHsT :: Γ_tr2
    let Γ_dl : List (Ty S_cka) :=
      dlQ :: .sum (.sum trQ chQ) dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_ij0 : List (Ty S_cka) := dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_cr : List (Ty S_cka) := .bool :: Γh0
    have hepm := cEpMgmtE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 qep (Γ' := Γ_tr1)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v5)) (.fst .v0)
      (_root_.CryptoGames.SM.isSomeE (.snd (.snd .v0)))
    have hvs := vSendC_sizeW_le
      (hooksFSMultiBucketAuthC L B0 1 qep gMain tL par la) Ho Hs Hr hhk (Γ' := Γ_tr2)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v6)) .v0 (.fst .v1)
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
      (.fst (.snd .v1)) .none (.snd (.snd .v1))
    have hrec := cRecordE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 L (Γ' := Γ_tr3)
      .v2 (.fst .v3) (.fst .v0)
      (.pair (.pair (.fst .v3) (.pair (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
        (.add (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
        (.pair (.fst (.snd .v3)) (.snd .v0)))
      (.bool false)
    have hdl := deliverEC_bucket_sizeW_le
      (hooksFSMultiBucketAuthC L B0 1 qep gMain tL par la) Ho_sr Ho_cm Hs Hr L maxSkip tL
      hhk_sr hhk_cm (Γ' := Γ_dl) (.fst .v3) .v0
    have hhh := isHonestHdrMultiBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0
      (Γ' := .prod (.opt (_root_.CryptoGames.CKA.ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E)) esT :: Γ_ij0)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v3)) (.fst (.snd .v1))
    have hij := injectEC_bucket_sizeW_le
      (hooksFSMultiBucketAuthC L B0 1 qep gMain tL par la) Ho_sr Ho_cm Hs Hr L qep tL
      hhk_sr hhk_cm (Γ' := Γ_ij0) (.fst .v2) .v0
    have hca := cCorrAllowedE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 L (Γ' := Γ_cr)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v1)) .v0
    let psT := _root_.CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
    have hac := cAfterCorrE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 L
      (Γ' := psT :: .prod (.opt psT) mbHsT :: Γ_cr)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v3)) .v2
    have hrv := fsMultiBucketAuthRevealC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L qep qR gMain la tL (Γ' := Γ_cr)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v1))
      (_root_.CryptoGames.SM.Engine.esG (.fst .v1)) .v0
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v1))) .v0)
    simp only [Ho, Ho_sr, Ho_cm, Hs, Hr, _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
      _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.pGet,
      _root_.CryptoGames.SM.isSomeE, exprSizeW_renameM, exprSizeW_letE,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3,
      exprSizeW_v4, exprSizeW_v5, exprSizeW_v6, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_add, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_caseOpt, bits_one, Nat.reduceAdd]
      at hepm hvs hrec hdl hhh hij hca hac hrv
    simp only [redFSAuthMultiBucketProg, _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
      _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsWin,
      _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.vpTcurNat,
      _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.pGet,
      exprSizeW_renameM, compSizeW_renameM,
      compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
      exprSizeW_letE, exprSizeW_caseOpt,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
      exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_some, exprSizeW_inl, exprSizeW_inr, exprSizeW_add, exprSizeW_eqN, exprSizeW_not,
      exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, bits_one,
      Nat.reduceAdd]
    generalize bits (qep + qR + B0 + 1) = bQ at *
    generalize bits B0 = bB at *
    generalize bits L = bL at *
    generalize bits qep = bq at *
    generalize bits (tL.getD 0) = bTL at *
    generalize bits (healEpoch tL) = bTH at *
    generalize bits maxSkip = bSk at *
    omega
  dsimp only
  omega

end GenericCkaSizeW

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthCostB
