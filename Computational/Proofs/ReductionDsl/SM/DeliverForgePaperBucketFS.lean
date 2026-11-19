/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Notation
import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Stage-2 Multi-Session Paper `DeliverForge` FS-AEAD Reductions (`[B7]` × `[B8]`)

Defines Stage-2 direct-boolean-output multi-session paper FS-AEAD `CostedReduction` programs over
`fsaeadMultiHeaderAdIface` (`fsaeadMultiHeaderAdDFIface`):
- `redFSAuthDFPaperMultiProg`: single target epoch `(tL, t)` (`B_fs` unshifted `B2` / `B3`)
- `redFSAuthDFPaperMultiBucketProgGen` / `redFSAuthDFPaperMultiBucketProg`: `(tL, par)` bucket
  (`B_fs_u`, `Δbucket = 3 + Δcka`) under `cCorrAllowedPaperE` and `bucketParPaperAuthCfgEC`

Together with query, decryption-query, and `totalCost` bounds.-/

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open ReductionDsl OracleSpec OracleComp
open scoped Computational.Proofs.ReductionDsl.Notation

namespace CryptoGames.SM.Construction

open Engine Engine.RedPRNG CKA PRFPRNG

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E

section HooksFSMultiCDFPaper

variable
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

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM" =>
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "mVpTy" => fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mEsTy" => fsMultiEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbEsTy" => fsMultiDFBucketEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbRedEsTy" => fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E

/-! ### Single-Epoch Stage-2 `redFSAuthDFPaperMultiProg` -/

/-- Stage-2 multi-session `redFSAuthDFPaper` program (`[B7]`, single target epoch `t`) over
`SM.specDF`, `prngOps`, `fsaeadMultiHeaderAdIface`, and `prngSMCodecDF`. -/
@[expose] def redFSAuthDFPaperMultiProg (L B Δcka qep maxSkip : ℕ) (la : Bool)
    (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO IIM
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := mEsTy
  init := rdsl [_] do
    es ← initFSMultiEStateC L (raw ⟨true, tL, t⟩) false
    return ((), es)
  handle := rdsl [st, q] do
    implECDFPaper (raw (hooksFSMultiC L B Δcka ⟨true, tL, t⟩ false la)) L (raw (2 + Δcka)) qep
      maxSkip (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) st q
  finish := rdsl [st, _] do
    return (finishFSMultiE L (raw (2 + Δcka)) (raw (⟨true, tL, t⟩ : Mode).policy) (raw la) st)

@[simp] theorem implECDF_hooksFSMultiC_queries (L B Δcka qep maxSkip : ℕ) (mo : Mode)
    (gMain la : Bool) (cfg : ConfigEC OO) (pol : Policy) {Γ'}
    (es : Expr OO Γ' mEsTy)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDF (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
      L (2 + Δcka) qep maxSkip cfg pol es q).queries
      (fun _ => 1) (fun _ => 0) = if la then 1 else 2 := by
  cases la <;>
    simp [implECDF, implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
      deliverForgeEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSMultiC,
      fsMultiCommitC, fsMultiRevealC, Comp.queries]

@[simp] theorem implECDF_hooksFSMultiC_decQueries (L B Δcka qep maxSkip : ℕ) (mo : Mode)
    (gMain la : Bool) (cfg : ConfigEC OO) (pol : Policy) {Γ'}
    (es : Expr OO Γ' mEsTy)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDF (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
      L (2 + Δcka) qep maxSkip cfg pol es q).queries
      fsHdrDecWt (fun _ => 0) = 1 := by
  cases la <;>
    simp [implECDF, implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
      deliverForgeEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSMultiC,
      fsMultiFsRecvC, fsMultiCommitC, fsMultiRevealC, fsHdrDecWt, Comp.queries]

@[simp] theorem redFSAuthDFPaperMultiProg_totalQueries_eq (L B Δcka qep maxSkip : ℕ) (la : Bool)
    (tL : Option ℕ) (t qAdv : ℕ) :
    (redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip la tL t).totalQueries (fun _ => 1) (fun _ => 0) qAdv =
      qAdv * (if la then 1 else 2) := by
  cases la <;>
    simp [CostedReduction.totalQueries, redFSAuthDFPaperMultiProg, initFSMultiEStateC,
      implECDFPaper, implECPaper, transmitEC, challEC, deliverEC, injectEC, corrECPaper,
      deliverForgeEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSMultiC,
      fsMultiFsSendC, fsMultiFsRecvC, fsMultiCommitC, fsMultiRevealC, Comp.queries]

theorem redFSAuthDFPaperMultiProg_totalQueries (L B Δcka qep maxSkip : ℕ) (la : Bool)
    (tL : Option ℕ) (t qAdv : ℕ) :
    (redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip la tL t).totalQueries (fun _ => 1) (fun _ => 0) qAdv ≤ qAdv * 2 := by
  rw [redFSAuthDFPaperMultiProg_totalQueries_eq]
  (cases la <;> simp); omega

@[simp] theorem redFSAuthDFPaperMultiProg_totalDecQueries (L B Δcka qep maxSkip : ℕ) (la : Bool)
    (tL : Option ℕ) (t qAdv : ℕ) :
    (redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip la tL t).totalQueries fsHdrDecWt (fun _ => 0) qAdv = qAdv := by
  cases la <;>
    simp [CostedReduction.totalQueries, redFSAuthDFPaperMultiProg, initFSMultiEStateC,
      implECDFPaper, implECPaper, transmitEC, challEC, deliverEC, injectEC, corrECPaper,
      deliverForgeEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSMultiC,
      fsMultiFsSendC, fsMultiFsRecvC, fsMultiCommitC, fsMultiRevealC, fsHdrDecWt, Comp.queries]

theorem redFSAuthDFPaperMultiProg_totalCost (L B Δcka qep maxSkip : ℕ) (la : Bool)
    (tL : Option ℕ) (t qAdv : ℕ) :
    let P := redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip la tL t
    P.totalCost qAdv = P.init.cost + qAdv * (P.handle.cost + 13) + P.finish.cost := by
  intro P
  have hCodec : (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).codecCost = 13 := rfl
  have hUCost : (fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).uCost = 1 := rfl
  dsimp only [CostedReduction.totalCost]
  change P.init.cost + qAdv * max (fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).uCost
      (P.handle.cost + (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).codecCost) +
      P.finish.cost = _
  rw [hCodec, hUCost, max_eq_right (by omega)]

/-! ### `(tL, par)`-Bucket Stage-2 `hooksFSMultiDFBucketPaperC` and `redFSAuthDFPaperMultiBucketProg` -/

/-- `postLeak` expression in `ReductionDsl`: `O(1)` check on `cGsTL ctxE`. -/
@[expose] def postLeakDFBucketE {O' : Ops S} {vpT : Ty S} {Γ'} (tL : Option ℕ)
    (ctxE : Expr O' Γ' (cGsTy vpT)) : Expr O' Γ' .bool :=
  rdslExpr =>
    match cGsTL ctxE with
    | none => false
    | some cur => ltOptE (optNatLit (raw tL)) cur

@[expose] def rootFSMultiDFBucketPaperC (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (tE : Expr OO Γ' .nat)
    (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i))
    (σE : Expr OO Γ' (.base .sig)) :
    Comp OO IIM Γ'
      (.prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, t0, ik0, σ0, pl0) ← return (hE, tE, ikE, σE, plE)
    let pIk := Expr.op (O := OO) CKAOp.prngUp (σ0, ik0)
    if orE pl0 (nat (qep + 1) < t0) then
      return ((pIk.1, pIk.2, none), h0)
    else if validGuessBucketParPaperE (raw Δbucket) (raw tL) (raw par) t0 then
      if bool tL.isSome && (t0 == nat tH) then
        ir ← sample (O := OO) (I := IIM) CKASamp.i ()
        kSample ← sample (O := OO) (I := IIM) CKASamp.k ()
        let pIr := Expr.op (O := OO) CKAOp.prngUp (σ0, ir)
        return ((pIr.1, kSample, some ir), h0)
      else
        (kLookup, h1) ← lookupMultiDFBucketFC L h0 t0 ik0
        return ((pIk.1, kLookup, some ik0), h1)
    else if bool tL.isSome && (t0 == nat tH) then
      ir ← sample (O := OO) (I := IIM) CKASamp.i ()
      kSample ← sample (O := OO) (I := IIM) CKASamp.k ()
      let pIr := Expr.op (O := OO) CKAOp.prngUp (σ0, ir)
      return ((pIr.1, kSample, none), h0)
    else
      return ((pIk.1, pIk.2, none), h0)

@[expose] def fsMultiDFBucketPaperStartSendC (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO IIM Γ'
      (.prod (.opt (.prod (.base .γ)
        (.prod (.base .t) (.prod (.base .sig) (.sum (.base .ss) .nat)))))
        mbHsTy) :=
  rdsl do
    (h0, t0, γ0, σ0, r0, pl0) ← return (hE, tE, γE, σE, rE, postLeakDFBucketE (raw tL) ctxE)
    coins ←
      match r0 with
      | none => sample (O := OO) (I := IIM) CKASamp.ccoins ()
      | some c => return c
    let cOut := Expr.op (O := OO) CKAOp.ckaSend (γ0, coins)
    ((σ', kVal, sid), h1) ← rootFSMultiDFBucketPaperC L Δbucket qep tL par h0 t0 pl0 cOut.2.2 σ0
    let regP := regSessOptMultiDFBucketE L (raw tL) h1 t0 sid
    let optIdx := regP.1
    let h2 := regP.2
    let tMsg := cOut.2.1
    let cache' := tset (fsMultiDFBucketHsCache h2) t0 (some (tMsg, σ', kVal, optIdx))
    let h3 := fsMultiDFBucketHsSetCache h2 cache'
    let ssv : Expr OO _ (.sum (.base .ss) .nat) :=
      match optIdx with
      | none => .inl (Expr.op (O := OO) CKAOp.fsInitSender kVal)
      | some sIdx => .inr sIdx
    return (some (cOut.1, tMsg, σ', ssv), h3)

@[expose] def fsMultiDFBucketPaperStartRecvC (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO IIM Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.base .sig) (.sum (.base .rs) .nat)))))
        mbHsTy) :=
  rdsl do
    (h0, t0, γ0, σ0, tn0, pl0) ← return (hE, tE, γE, σE, tnE, postLeakDFBucketE (raw tL) ctxE)
    let honest :=
      match tget (fsMultiDFBucketHsCache h0) t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none =>
      if !(nat (qep + 1) < t0) && validGuessBucketParPaperE (raw Δbucket) (raw tL) (raw par) t0 then
        if bool tL.isSome && (t0 == nat (healEpoch tL)) then
          return (none, h0)
        else if pl0 then
          let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
          let p := Expr.op (O := OO) CKAOp.prngUp (σ0, kk.2)
          let rs := Expr.op (O := OO) CKAOp.fsInitReceiver p.2
          return (some (some (kk.1, p.1, .inl rs)), h0)
        else
          let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
          (_k', h1) ← lookupMultiDFBucketFC L h0 t0 kk.2
          let regP := regSessMultiDFBucketE L (raw tL) h1 t0 kk.2
          let sIdx := regP.1
          let h2 := regP.2
          let σ' := (Expr.op (O := OO) CKAOp.prngUp (σ0, kk.2)).1
          return (some (some (kk.1, σ', .inr sIdx)), h2)
      else
        return (some none, h0)
    | some (σc, kVal, optIdx) =>
      let γ' := (Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)).1
      let rsv : Expr OO _ (.sum (.base .rs) .nat) :=
        match optIdx with
        | none => .inl (Expr.op (O := OO) CKAOp.fsInitReceiver kVal)
        | some sIdx => .inr sIdx
      return (some (some (γ', σc, rsv)), h0)

@[expose] def fsMultiDFBucketPaperFsRecvC (L B : ℕ) (la : Bool) (Δcka : ℕ := 1) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct))
    (recE : Expr OO Γ' (.opt cRecTy)) :
    Comp OO IIM Γ'
      (.prod (.opt (.opt (.prod (.sum (.base .rs) .nat) (.prod .nat (.base .msg))))) mbHsTy) :=
  rdsl do
    (h0, ctx0, t0, rsv0, hdr0, e0, rec0) ← return (hE, ctxE, tE, rsvE, hdrE, eE, recE)
    match rsv0 with
    | .inl rs =>
      match Expr.op (O := OO) (CKAOp.fsReceive B) (rs, hdr0, e0) with
      | none => return (some none, h0)
      | some (rs', idxMsg) =>
        return (some (some (.inl rs', idxMsg)), h0)
    | .inr sIdx =>
      let bk0 := fsMultiDFBucketHsGetBookAt h0 sIdx
      let sCorr0 := bk0.1
      let trs0 := bk0.2.2
      let matched := fsTransFindE L trs0 (hdr0, e0)
      (ok, h1) ←
        match matched with
        | some _ => return (true, h0)
        | none =>
          if !(_root_.CryptoGames.SM.healedByE (cGsTL ctx0) (raw (2 + Δcka)) t0) && !sCorr0 then
            csOpt ← query (O := OO) (I := IIM) FSHdrTag.cs (sIdx, ())
            match csOpt with
            | none => return (false, h0)
            | some _ => return (true, fsMultiDFBucketHsSetBookAt h0 sIdx (true, bk0.2))
          else
            return (true, h0)
      if !ok then
        return (none, h1)
      else
        resOpt ←
          match matched with
          | none => query (O := OO) (I := IIM) FSHdrTag.ij (sIdx, (hdr0, e0))
          | some _ => query (O := OO) (I := IIM) FSHdrTag.dl (sIdx, (hdr0, e0))
        match resOpt with
        | none => return (none, h1)
        | some resSum =>
          match resSum with
          | .inl _ => return (some none, h1)
          | .inr (msgIdx, mo') =>
            let bk1 := fsMultiDFBucketHsGetBookAt h1 sIdx
            let sCorr1 := bk1.1
            let cnt1 := bk1.2.1
            let trs1 := bk1.2.2
            let isLookaheadInj :=
              match matched with
              | none => (!sCorr1) && (cnt1 < msgIdx)
              | some _ => false
            if bool la && isLookaheadInj then
              return (none, fsMultiDFBucketHsSetLfWin h1 true)
            else
              let drop :=
                match matched with
                | none => msgIdx
                | some entry => entry.1
              let trs' := fsTransFilterE L trs1 drop
              let h4 := fsMultiDFBucketHsSetBookAt h1 sIdx (sCorr1, (cnt1, trs'))
              let outE :=
                match mo' with
                | none =>
                  match rec0 with
                  | none => none
                  | some r => some (some (.inr sIdx, msgIdx, cRecMsg r))
                | some msg => some (some (.inr sIdx, msgIdx, msg))
              return (outE, h4)

/-- Costed multi-session `(tL, par)`-bucket `HooksC` bundle for `redFSAuthDFPaperMultiBucketProg*`. -/
@[expose] def hooksFSMultiDFBucketPaperC (L B Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool) :
    HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) mbHsTy where
  startSend := fsMultiDFBucketPaperStartSendC L Δbucket qep tL par
  startRecv := fsMultiDFBucketPaperStartRecvC L Δbucket qep tL par
  fsSend := fsMultiDFBucketFsSendC Δcka la
  fsRecv := fsMultiDFBucketPaperFsRecvC L B la Δcka
  commit := fsMultiDFBucketCommitC
  reveal := fsMultiDFBucketRevealC L la

/-- Costed initialization of `mbEsTy` for `(tL, par)`-bucket `redFSAuthDFPaperMultiBucketProg*`. -/
@[expose] def initFSMultiDFBucketPaperEStateC (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ'} (bE : Expr OO Γ' .bool) :
    Comp OO IIM Γ' mbEsTy :=
  rdsl do
    b0 ← return bE
    kr ← sample (O := OO) (I := IIM) CKASamp.kr ()
    kc ← sample (O := OO) (I := IIM) CKASamp.kc ()
    ((σ, kVal, sid), h1) ←
      rootFSMultiDFBucketPaperC L Δbucket qep tL par fsMultiDFBucketHsEmptyE 0 false
        (Expr.op (O := OO) CKAOp.lamI ())
        (Expr.op (O := OO) CKAOp.prngInit kr)
    let regP := regSessOptMultiDFBucketE L (raw tL) h1 0 sid
    let optIdx := regP.1
    let h2 := regP.2
    let ssv0 : Expr OO _ (.sum (.base .ss) .nat) :=
      match optIdx with
      | none => .inl (Expr.op (O := OO) CKAOp.fsInitSender kVal)
      | some sIdx => .inr sIdx
    let rsv0 : Expr OO _ (.sum (.base .rs) .nat) :=
      match optIdx with
      | none => .inl (Expr.op (O := OO) CKAOp.fsInitReceiver kVal)
      | some sIdx => .inr sIdx
    let pAB := mkPartiesE
      (Expr.op (O := OO) CKAOp.ckaInitA kc)
      (Expr.op (O := OO) CKAOp.ckaInitB kc)
      σ ssv0 rsv0
    return (esMk (cGsInitE (vpT := mVpTy) pAB.1 pAB.2 b0) h2 false)

/-- Stage-2 `(tL, par)`-bucket multi-session `redFSAuthDFPaper` program (`[B7]` × `[B8]`,
`B_fs_u`, parameterized by `Δbucket`) over `SM.specDF`, `prngOps`, `fsaeadMultiHeaderAdIface`,
and `prngSMCodecDF` under `cCorrAllowedPaperE` and `bucketParPaperAuthCfgEC`. -/
@[expose] def redFSAuthDFPaperMultiBucketProgGen (L B Δcka Δbucket qep maxSkip : ℕ) (la : Bool)
    (tL : Option ℕ) (par : Bool) :
    CostedReduction OO IIM
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := mbRedEsTy
  init := rdsl [_] do
    es ← initFSMultiDFBucketPaperEStateC L Δbucket qep tL par false
    return ((), (es, none))
  handle := rdsl [st, qArg] do
    (es0, winEp0, q0) ← return (st.1, st.2, qArg)
    match q0 with
    | .inl qBase =>
      match qBase with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if orE (esAbort es0) (cGsWin (esG es0)) then
          return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
        else
          match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
          | none => return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
          | some s1 =>
            (res, h') ← vSendC (raw (hooksFSMultiDFBucketPaperC L B Δcka Δbucket qep tL par la))
              (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
            match res with
            | none => return (.inl (inl (inl (inl (inl none)))), (esMk (esG es0) h' true, winEp0))
            | some (st', ct) =>
              let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
              let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
              return (.inl (inl (inl (inl (inl (some ct))))), (esMk g' h' (esAbort es0), winEp0))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (inl (inl (inl (inr none)))), (es0, winEp0))
      | .inl (.inl (.inr x)) =>
        (out, es') ← deliverEC (raw (hooksFSMultiDFBucketPaperC L B Δcka Δbucket qep tL par la))
          L maxSkip (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
        return (.inl (inl (inl (inr out))), (es', winEp0))
      | .inl (.inr x) =>
        let wasWin := cGsWin (esG es0)
        (out, es') ← injectEC (raw (hooksFSMultiDFBucketPaperC L B Δcka Δbucket qep tL par la))
          L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
        let winEp' := if !wasWin && cGsWin (esG es') then some x.2.1.1 else winEp0
        return (.inl (inl (inr out)), (es', winEp'))
      | .inr p0 =>
        let s0 := esG es0
        if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedPaperE (raw L) s0 p0))) then
          return (.inl (inr none), (es0, winEp0))
        else
          let s1 := cAfterCorrE (raw L) s0 p0
          (res, h') ← fsMultiDFBucketRevealC L la (esH es0) s0 p0 (pGet (cGsSt s0) p0)
          match res with
          | none => return (.inl (inr none), (esMk s0 h' true, winEp0))
          | some stOut =>
            return (.inl (inr (some stOut)), (esMk s1 h' (esAbort es0), winEp0))
    | .inr x =>
      let wasWin := cGsWin (esG es0)
      (out, es') ← deliverForgeEC (raw (hooksFSMultiDFBucketPaperC L B Δcka Δbucket qep tL par la))
        L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
      let winEp' := if !wasWin && cGsWin (esG es') then some x.2.2.1.1 else winEp0
      return (.inr out, (es', winEp'))
  finish := rdsl [st, _] do
    (es0, winEp0) ← return (st.1, st.2)
    if bool la then
      return (fsMultiDFBucketHsLfWin (esH es0))
    else
      match winEp0 with
      | none => return false
      | some tWin =>
        return ((!(esAbort es0) && cGsWin (esG es0)) &&
          cAuthOKE (raw L) (raw (2 + Δcka)) (optNatLit (raw tL)) tWin (esG es0))

/-- Default Stage-2 `(tL, par)`-bucket `redFSAuthDFPaperMultiBucketProg`
(matching `DeliverForge.lean`'s `redFSAuthDFMultiBucketProg` argument list). -/
abbrev redFSAuthDFPaperMultiBucketProg (L B Δcka Δbucket qep maxSkip : ℕ) (la : Bool)
    (tL : Option ℕ) (par : Bool) :
    CostedReduction OO IIM
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool :=
  redFSAuthDFPaperMultiBucketProgGen L B Δcka Δbucket qep maxSkip la tL par

/-! ### Query, Decryption-Query, and `totalCost` Bounds for `(tL, par)` Bucket -/

@[simp] theorem rootFSMultiDFBucketPaperC_queries (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (w : FSHdrTag → ℕ) {Γ'} (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat)
    (plE : Expr OO Γ' .bool) (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig)) :
    (rootFSMultiDFBucketPaperC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δbucket qep tL par hE tE plE ikE σE).queries w
      (fun _ => 0) = 0 := by
  simp [rootFSMultiDFBucketPaperC, lookupMultiDFBucketFC, Comp.queries]

@[simp] theorem fsMultiDFBucketPaperStartSendC_queries (L Δbucket qep : ℕ) (tL : Option ℕ)
    (par : Bool) (w : FSHdrTag → ℕ) {Γ'} (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    (fsMultiDFBucketPaperStartSendC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L Δbucket qep tL par hE ctxE pE tE γE σE rE).queries w (fun _ => 0) = 0 := by
  simp [fsMultiDFBucketPaperStartSendC, Comp.queries]

@[simp] theorem fsMultiDFBucketPaperStartRecvC_queries (L Δbucket qep : ℕ) (tL : Option ℕ)
    (par : Bool) (w : FSHdrTag → ℕ) {Γ'} (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig)) (tnE : Expr OO Γ' (.base .t)) :
    (fsMultiDFBucketPaperStartRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L Δbucket qep tL par hE ctxE pE tE γE σE tnE).queries w (fun _ => 0) = 0 := by
  simp [fsMultiDFBucketPaperStartRecvC, lookupMultiDFBucketFC, Comp.queries]

@[simp] theorem initFSMultiDFBucketPaperEStateC_queries (L Δbucket qep : ℕ) (tL : Option ℕ)
    (par : Bool) (w : FSHdrTag → ℕ) {Γ'} (bE : Expr OO Γ' .bool) :
    (initFSMultiDFBucketPaperEStateC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L Δbucket qep tL par bE).queries w (fun _ => 0) = 0 := by
  simp [initFSMultiDFBucketPaperEStateC, Comp.queries]

theorem redFSAuthDFPaperMultiBucketProgGen_totalQueries (L B Δcka Δbucket qep maxSkip : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    (redFSAuthDFPaperMultiBucketProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip la tL par).totalQueries (fun _ => 1) (fun _ => 0) qAdv ≤
      qAdv * 2 := by
  simp only [CostedReduction.totalQueries, redFSAuthDFPaperMultiBucketProgGen,
    initFSMultiDFBucketPaperEStateC_queries, Comp.queries, zero_add, add_zero]
  apply Nat.mul_le_mul_left qAdv
  cases la <;>
    simp [deliverEC, injectEC, deliverForgeEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C,
      commitEC, hooksFSMultiDFBucketPaperC, fsMultiDFBucketFsSendC,
      fsMultiDFBucketPaperFsRecvC, fsMultiDFBucketRevealC, Comp.queries]

theorem redFSAuthDFPaperMultiBucketProg_totalQueries (L B Δcka Δbucket qep maxSkip : ℕ) (la : Bool)
    (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    (redFSAuthDFPaperMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip la tL par).totalQueries (fun _ => 1) (fun _ => 0) qAdv ≤
      qAdv * 2 :=
  redFSAuthDFPaperMultiBucketProgGen_totalQueries L B Δcka Δbucket qep maxSkip la tL par qAdv

theorem redFSAuthDFPaperMultiBucketProg_totalDecQueries (L B Δcka Δbucket qep maxSkip : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    (redFSAuthDFPaperMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip la tL par).totalQueries fsHdrDecWt (fun _ => 0) qAdv = qAdv := by
  cases la <;>
    simp [redFSAuthDFPaperMultiBucketProg, CostedReduction.totalQueries,
      redFSAuthDFPaperMultiBucketProgGen, deliverEC, injectEC, deliverForgeEC, vSendC,
      vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSMultiDFBucketPaperC,
      fsMultiDFBucketFsSendC, fsMultiDFBucketPaperFsRecvC, fsMultiDFBucketRevealC,
      fsHdrDecWt, Comp.queries]

theorem redFSAuthDFPaperMultiBucketProg_totalCost (L B Δcka Δbucket qep maxSkip : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    let P := redFSAuthDFPaperMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip la tL par
    P.totalCost qAdv = P.init.cost + qAdv * (P.handle.cost + 13) + P.finish.cost := by
  intro P
  have hCodec : (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).codecCost = 13 := rfl
  have hUCost : (fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).uCost = 1 := rfl
  dsimp only [CostedReduction.totalCost]
  change P.init.cost + qAdv * max (fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).uCost
      (P.handle.cost + (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).codecCost) +
      P.finish.cost = _
  rw [hCodec, hUCost, max_eq_right (by omega)]

end HooksFSMultiCDFPaper

/-! ### Shallow Stage-2 Multi-Session Paper FS-AEAD Reductions & Evaluation Bridges -/

section ShallowFSMultiDFPaper

/-- Generic-`Δbucket` Stage-2 `(tL, par)` bucket membership (`DeliverForge.inStage2Bucket` when
`Δbucket = 3 + Δcka`). -/
@[expose] def inStage2BucketGen (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) : Bool :=
  lastLeakGuessAdmissible Δbucket tL t && (DeliverForge.partyPar (Party.senderOf t) == par)

/-- Generic-`Δbucket` Stage-2 `(tL, par)` bucket `Config` (`DeliverForge.bucketAuthCfg` when
`Δbucket = 3 + Δcka`). -/
@[expose] def bucketAuthCfgGen {Msg : Type} (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) :
    Config Msg where
  deliverWin := false
  injectFull t' := inStage2BucketGen Δbucket tL par t'
  challAllowedIn _ := false
  challMsg _ := none

/-- Shallow Stage-2 multi-session paper runner over `FSMultiSpec` (`mo = ⟨true, tL, t⟩`). -/
@[expose] def runFSMultiDFPaper
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (mo : Mode) (la b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E)
      (Bool × EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
        (FSMultiState T RSt K I E)) := do
  let es₀ ← initFSMultiRaw cka prng fs lam mo b
  (simulateQ (DeliverForge.implEDFPaper
    (hooksFSMulti cka prng fs Δcka mo false la) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
    A).run es₀

/-- Shallow Stage-2 multi-session paper FS-AEAD reduction (`B_fs`, single target `(tL, t)`). -/
@[expose] def redFSAuthDFPaperMulti
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (la : Bool)
    (tL : Option ℕ) (t : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool := do
  let (_, es) ← runFSMultiDFPaper cka prng fs lam Δcka qep ⟨true, tL, t⟩ la false A
  return (if la then es.h.lfWin else authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy es)

/-- Shallow hook state for `(tL, par)`-bucket multi-session `hooksFSMultiDFBucketPaper`. -/
structure FSMultiDFBucketState (T Sig K I E : Type) where
  cache : ℕ → Option (T × Sig × K × Option ℕ) := fun _ => none
  fTable : ℕ → List (I × K) := fun _ => []
  sessions : ℕ → List I := fun _ => []
  book : ℕ → Option (FSMultiBook T E) := fun _ => none
  lfWin : Bool := false

/-- Lift a single-session FS-AEAD query at session index `sIdx` into
`HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T Sig K I E)`. -/
@[expose] def liftFSMultiDFBucket {Sig K I : Type} (sIdx : ℕ) {α : Type}
    (x : FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T Sig K I E) α :=
  let liftImpl : QueryImpl (unifSpec + FSAEAD.spec SS RS (Header T) M E)
      (TComp (FSMultiSpec SS RS T M E)) := fun
    | .inl n => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n)
    | .inr q => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inr ⟨sIdx, q⟩)
  StateT.lift (simulateQ liftImpl x)

/-- Lazily sample `F_{t0}(ik)` in `HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)`. -/
@[expose] def lookupMultiDFBucketF [DecidableEq I] [SampleableType K] (t0 : ℕ) (ik : I) :
    HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) K := do
  let tb0 := (← get).fTable t0
  match tb0.lookup ik with
  | some k => return k
  | none =>
    let k ← StateT.lift (sampleT K)
    modify fun s => { s with fTable := Function.update s.fTable t0 ((ik, k) :: tb0) }
    return k

/-- Register or look up session `ik` in epoch `t0`'s bucket block `(L - 1) * (t0 - healEpoch tL) + ·`. -/
@[expose] def regSessMultiDFBucket [DecidableEq I] (L : ℕ) (tL : Option ℕ) (t0 : ℕ) (ik : I)
    (s : FSMultiDFBucketState T RSt K I E) : ℕ × FSMultiDFBucketState T RSt K I E :=
  let ses0 := s.sessions t0
  let base := (L - 1) * (t0 - healEpoch tL)
  if ik ∈ ses0 then
    (base + ses0.idxOf ik, s)
  else
    (base + ses0.length, { s with sessions := Function.update s.sessions t0 (ses0 ++ [ik]) })

/-- Optional wrapper around `regSessMultiDFBucket`. -/
@[expose] def regSessOptMultiDFBucket [DecidableEq I] (L : ℕ) (tL : Option ℕ) (t0 : ℕ)
    (sid : Option I) (s : FSMultiDFBucketState T RSt K I E) :
    Option ℕ × FSMultiDFBucketState T RSt K I E :=
  match sid with
  | none => (none, s)
  | some ik =>
    let (idx, s') := regSessMultiDFBucket L tL t0 ik s
    (some idx, s')

/-- True once a post-`tL` state corruption (`corr`) has occurred in `ctx`. -/
@[expose] def postLeakDFBucket {St Msg C : Type} (tL : Option ℕ) (ctx : GameState St Msg C) : Bool :=
  match ctx.tL with
  | none => false
  | some cur => ltOpt tL cur

/-- Shallow root-ratchet step for `(tL, par)`-bucket `hooksFSMultiDFBucketPaper`. -/
@[expose] def rootFSMultiDFBucketPaper [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : RSt) :
    HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) (RSt × K × Option I) := do
  let tH := healEpoch tL
  let pIk := prng.up σ0 ik0
  if pl || qep + 1 < t0 then
    return (pIk.1, pIk.2, none)
  else if inStage2BucketGen Δbucket tL par t0 then
    if tL.isSome && (t0 == tH) then
      let ir ← StateT.lift (sampleT I)
      let kSample ← StateT.lift (sampleT K)
      return ((prng.up σ0 ir).1, kSample, some ir)
    else
      let kLookup ← lookupMultiDFBucketF t0 ik0
      return (pIk.1, kLookup, some ik0)
  else if tL.isSome && (t0 == tH) then
    let ir ← StateT.lift (sampleT I)
    let kSample ← StateT.lift (sampleT K)
    return ((prng.up σ0 ir).1, kSample, none)
  else
    return (pIk.1, pIk.2, none)

/-- Shallow `Hooks` bundle for `(tL, par)`-bucket multi-session `redFSAuthDFPaperMultiBucketGen`. -/
@[expose] def hooksFSMultiDFBucketPaper
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) :
    Hooks (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)
      Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ) where
  startSend ctx _ t0 γ0 σ0 r0 := do
    let pl := postLeakDFBucket tL ctx
    let coins ← match r0 with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let cOut := cka.send γ0 coins
    let (σ', kVal, sid) ← rootFSMultiDFBucketPaper prng Δbucket qep tL par t0 pl cOut.2.2 σ0
    let s1 ← get
    let (optIdx, s2) := regSessOptMultiDFBucket L tL t0 sid s1
    set { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
    let ssv : SS ⊕ ℕ := match optIdx with
      | none => .inl (fs.initSender kVal)
      | some sIdx => .inr sIdx
    return some (cOut.1, cOut.2.1, σ', ssv)
  startRecv ctx _ t0 γ0 σ0 tn0 := do
    let pl := postLeakDFBucket tL ctx
    let honest := match (← get).cache t0 with
      | some (tCached, σc, kVal, optIdx) => if tCached = tn0 then some (σc, kVal, optIdx) else none
      | none => none
    match honest with
    | some (σc, kVal, optIdx) =>
      let rsv : RS ⊕ ℕ := match optIdx with
        | none => .inl (fs.initReceiver kVal)
        | some sIdx => .inr sIdx
      return some (some ((cka.receive γ0 tn0).1, σc, rsv))
    | none =>
      if !(qep + 1 < t0) && inStage2BucketGen Δbucket tL par t0 then
        if tL.isSome && (t0 == healEpoch tL) then
          return none
        else if pl then
          let kk := cka.receive γ0 tn0
          let p := prng.up σ0 kk.2
          return some (some (kk.1, p.1, .inl (fs.initReceiver p.2)))
        else
          let kk := cka.receive γ0 tn0
          let _ ← lookupMultiDFBucketF t0 kk.2
          let s1 ← get
          let (sIdx, s2) := regSessMultiDFBucket L tL t0 kk.2 s1
          set s2
          return some (some (kk.1, (prng.up σ0 kk.2).1, .inr sIdx))
      else
        return some none
  fsSend ctx P _ ssv h m pair := do
    match ssv with
    | .inl ss =>
      let o := fs.send ss h m
      return some (.inl o.1, o.2)
    | .inr sIdx =>
      let s ← get
      let bk := (s.book sIdx).getD {}
      let ok ← if !(ctx.safeCh (2 + Δcka) P) && !bk.sCorr then do
          match ← liftFSMultiDFBucket sIdx (FSAEAD.corruptSenderQuery (ReceiverState := RS)
              (AssocData := Header T) (Message := M) (Ciphertext := E)) with
          | none => pure false
          | some _ =>
            modify fun s =>
              let b := (s.book sIdx).getD {}
              { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
            pure true
        else pure true
      if !ok then return none
      let e? ← match pair with
        | some (m₀, m₁) =>
          liftFSMultiDFBucket sIdx (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
            h m₀ m₁)
        | none =>
          liftFSMultiDFBucket sIdx (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS) h m)
      match e? with
      | none => return none
      | some e =>
        modify fun s =>
          let b := (s.book sIdx).getD {}
          let cnt' := b.fsCount + 1
          let b' : FSMultiBook T E := { b with fsCount := cnt', fsTrans := (cnt', h, e) :: b.fsTrans }
          { s with book := Function.update s.book sIdx (some b') }
        return some (.inr sIdx, e)
  fsRecv ctx _ t0 rsv h e rec := do
    match rsv with
    | .inl rs => return some ((fs.receive rs h e).map fun o => (.inl o.1, o.2.1, o.2.2))
    | .inr sIdx =>
      let s ← get
      let bk := (s.book sIdx).getD {}
      let matched := bk.fsTrans.find? (fun x => x.2 == (h, e))
      let ok ← if matched.isNone && !(SM.healedBy ctx.tL (2 + Δcka) t0) && !bk.sCorr then do
          match ← liftFSMultiDFBucket sIdx (FSAEAD.corruptSenderQuery (ReceiverState := RS)
              (AssocData := Header T) (Message := M) (Ciphertext := E)) with
          | none => pure false
          | some _ =>
            modify fun s =>
              let b := (s.book sIdx).getD {}
              { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
            pure true
        else pure true
      if !ok then return none
      let res ← if matched.isSome then
          liftFSMultiDFBucket sIdx (FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) h e)
        else
          liftFSMultiDFBucket sIdx (FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) h e)
      match res with
      | none => return none
      | some .rejected => return some none
      | some (.accepted i mo') =>
        let s1 ← get
        let bk1 := (s1.book sIdx).getD {}
        if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
          modify fun s => { s with lfWin := true }
          return none
        else
          let drop := (matched.map (·.1)).getD i
          modify fun s =>
            let b := (s.book sIdx).getD {}
            let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
            { s with book := Function.update s.book sIdx (some b') }
          match mo', rec with
          | some m, _ => return some (some (.inr sIdx, i, m))
          | none, some r => return some (some (.inr sIdx, i, r.msg))
          | none, none => return none
  commit _ _ _ new := pure (some new)
  reveal _ _ vp := do
    let vS? : Option (Option SS) ← match vp.vS with
      | none => pure (some none)
      | some (.inl ss) => pure (some (some ss))
      | some (.inr sIdx) => do
        match ← liftFSMultiDFBucket sIdx (FSAEAD.corruptSenderQuery (ReceiverState := RS)
            (AssocData := Header T) (Message := M) (Ciphertext := E)) with
        | none => pure none
        | some ss =>
          modify fun s =>
            let b := (s.book sIdx).getD {}
            { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
          pure (some (some ss))
    match vS? with
    | none => return none
    | some ssReal =>
      if (List.range L).any (fun t => match vp.vR t with | some (.inr _) => true | _ => false) then
        return none
      else
        let vR' : ℕ → Option RS := fun t =>
          if t < L then
            match vp.vR t with
            | some (.inl rs) => some rs
            | _ => none
          else none
        return some (realParty vp vp.γ vp.root ssReal vR')

/-- Shallow initialization for `(tL, par)`-bucket `runFSMultiDFBucketPaper`. -/
@[expose] def initFSMultiDFBucketPaper
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δbucket qep : ℕ)
    (tL : Option ℕ) (par : Bool) :
    HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)
      (Option (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) × VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))) := do
  let kr ← StateT.lift (sampleT KR)
  let kc ← StateT.lift (sampleT KC)
  let (σ, kVal, sid) ← rootFSMultiDFBucketPaper prng Δbucket qep tL par 0 false lam (prng.init kr)
  let s1 ← get
  let (optIdx, s2) := regSessOptMultiDFBucket L tL 0 sid s1
  set s2
  let ssv0 : SS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initSender kVal)
    | some sIdx => .inr sIdx
  let rsv0 : RS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initReceiver kVal)
    | some sIdx => .inr sIdx
  return some (mkParties (cka.initA kc) (cka.initB kc) σ ssv0 rsv0)

/-- Shallow Stage-2 `(tL, par)`-bucket multi-session paper FS-AEAD reduction (`B_fs_u`,
parameterized by `L` and `Δbucket`). -/
@[expose] def redFSAuthDFPaperMultiBucketGen
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka Δbucket qep : ℕ) (la : Bool)
    (tL : Option ℕ) (par : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool := do
  let r ← DeliverForge.engRunDFPaperBucket
    (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
    (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
    (initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par) {} false A
  return match r with
    | none => false
    | some (_, st) =>
      if la then st.1.h.lfWin else DeliverForge.authOutBucket (2 + Δcka) tL st

/-- Default shallow Stage-2 `(tL, par)`-bucket multi-session paper FS-AEAD reduction (`B_fs_u`). -/
abbrev redFSAuthDFPaperMultiBucket
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka Δbucket qep : ℕ) (la : Bool)
    (tL : Option ℕ) (par : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool :=
  redFSAuthDFPaperMultiBucketGen L cka prng fs lam Δcka Δbucket qep la tL par A

private def fsBookStep (k : ℕ) (b0 b1 : ℕ → Option (FSMultiBook T E)) : Prop :=
  ∀ idx bk', b1 idx = some bk' →
    (∃ bk₀, b0 idx = some bk₀ ∧ bk'.fsTrans.length ≤ bk₀.fsTrans.length + k) ∨
      bk'.fsTrans.length ≤ k

private theorem fsBookStep_refl (k : ℕ) {b0 b1 : ℕ → Option (FSMultiBook T E)} (hEq : b1 = b0) :
    fsBookStep k b0 b1 := by
  intro idx bk' hbk'
  exact Or.inl ⟨bk', by rw [← hEq]; exact hbk', Nat.le_add_right _ _⟩

private theorem fsBookStep_mono {k1 k2 : ℕ} (hk : k1 ≤ k2)
    {b0 b1 : ℕ → Option (FSMultiBook T E)} (h : fsBookStep k1 b0 b1) :
    fsBookStep k2 b0 b1 := by
  intro idx bk' hbk'
  rcases h idx bk' hbk' with ⟨bk₀, hbk₀, hle⟩ | hle
  · exact Or.inl ⟨bk₀, hbk₀, by omega⟩
  · exact Or.inr (by omega)

private theorem fsBookStep_trans {k1 k2 : ℕ}
    {b0 b1 b2 : ℕ → Option (FSMultiBook T E)}
    (h01 : fsBookStep k1 b0 b1) (h12 : fsBookStep k2 b1 b2) :
    fsBookStep (k1 + k2) b0 b2 := by
  intro idx bk₂ hbk₂
  rcases h12 idx bk₂ hbk₂ with ⟨bk₁, hbk₁, hle₁⟩ | hle₂
  · rcases h01 idx bk₁ hbk₁ with ⟨bk₀, hbk₀, hle₀⟩ | hle₁'
    · exact Or.inl ⟨bk₀, hbk₀, by omega⟩
    · exact Or.inr (by omega)
  · exact Or.inr (by omega)

private theorem fsBookStep_update_sCorr (b : ℕ → Option (FSMultiBook T E)) (sIdx : ℕ) :
    fsBookStep 0 b (Function.update b sIdx (some { (b sIdx).getD {} with sCorr := true })) := by
  intro idx bk' hbk'
  by_cases hEq : idx = sIdx
  · subst hEq
    rw [Function.update_self, Option.some.injEq] at hbk'
    subst hbk'
    rcases hb : b idx with _ | bk₀
    · exact Or.inr (by simp)
    · exact Or.inl ⟨bk₀, rfl, by simp⟩
  · rw [Function.update_of_ne hEq] at hbk'
    exact Or.inl ⟨bk', hbk', le_rfl⟩

private theorem fsBookStep_update_cons (b : ℕ → Option (FSMultiBook T E)) (sIdx : ℕ)
    (h : Header T) (e : E) :
    fsBookStep 1 b (Function.update b sIdx
      (some { (b sIdx).getD {} with
        fsCount := ((b sIdx).getD {}).fsCount + 1
        fsTrans := (((b sIdx).getD {}).fsCount + 1, h, e) :: ((b sIdx).getD {}).fsTrans })) := by
  intro idx bk' hbk'
  by_cases hEq : idx = sIdx
  · subst hEq
    rw [Function.update_self, Option.some.injEq] at hbk'
    subst hbk'
    rcases hb : b idx with _ | bk₀
    · exact Or.inr (by simp)
    · exact Or.inl ⟨bk₀, rfl, by simp⟩
  · rw [Function.update_of_ne hEq] at hbk'
    exact Or.inl ⟨bk', hbk', Nat.le_add_right _ _⟩

private theorem fsBookStep_update_filter (b : ℕ → Option (FSMultiBook T E)) (sIdx : ℕ)
    (p : (ℕ × Header T × E) → Bool) :
    fsBookStep 0 b (Function.update b sIdx
      (some { (b sIdx).getD {} with fsTrans := ((b sIdx).getD {}).fsTrans.filter p })) := by
  intro idx bk' hbk'
  by_cases hEq : idx = sIdx
  · subst hEq
    rw [Function.update_self, Option.some.injEq] at hbk'
    subst hbk'
    rcases hb : b idx with _ | bk₀
    · exact Or.inr (by simp)
    · exact Or.inl ⟨bk₀, rfl, by simpa using List.length_filter_le p bk₀.fsTrans⟩
  · rw [Function.update_of_ne hEq] at hbk'
    exact Or.inl ⟨bk', hbk', le_rfl⟩

private theorem fsBookStep_apply {B q : ℕ} {b0 b1 : ℕ → Option (FSMultiBook T E)}
    (hq1 : q + 1 ≤ B)
    (hInv : ∀ idx bk, b0 idx = some bk → bk.fsTrans.length + (q + 1) ≤ B)
    (hStep : fsBookStep 1 b0 b1) :
    ∀ idx bk', b1 idx = some bk' → bk'.fsTrans.length + q ≤ B := by
  intro idx bk' hbk'
  rcases hStep idx bk' hbk' with ⟨bk₀, hbk₀, hle⟩ | hle
  · have := hInv idx bk₀ hbk₀; omega
  · omega

private theorem vSend_preserve_generic [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {HPre HMid HPost : HS → Prop}
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (h : HS) (hPre : HPre h) (hMid0 : HPre h → HMid h)
    (hMidPost : ∀ {h1}, HMid h1 → HPost h1)
    (hStart : ∀ t0 γ0 σ0 r0 res, HPre h →
      res ∈ support ((hk.startSend ctx P t0 γ0 σ0 r0).run h) → HMid res.2)
    (hFs : ∀ {h1} t1 v hHdr m' pair' res, HMid h1 →
      res ∈ support ((hk.fsSend ctx P t1 v hHdr m' pair').run h1) → HPost res.2) :
    ∀ res ∈ support ((vSend hk ctx P s m pair r).run h),
      HPost res.2 ∧
      (∀ st' c, res.1 = some (st', c) →
        s.tcur ≤ st'.tcur ∧ st'.tcur ≤ s.tcur + 1 ∧ st'.vR = s.vR) := by
  intro ⟨vsRes, h'⟩ hmem
  rw [vSend_eq_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
  have hStep1 : HMid h₁ ∧
      (∀ s₁, s₁? = some s₁ → s.tcur ≤ s₁.tcur ∧ s₁.tcur ≤ s.tcur + 1 ∧ s₁.vR = s.vR) := by
    unfold vSendStep1 at hmem1
    split_ifs at hmem1
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem1
      obtain ⟨⟨ssRes, h₁'⟩, hss, hmem1⟩ := hmem1
      have hM := hStart (s.tcur + 1) s.γ s.root r (ssRes, h₁') hPre hss
      rcases ssRes with _ | ⟨γ', T', σ', ss⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩
        exact ⟨hM, fun _ h => by cases h⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩
        exact ⟨hM, fun s₁ hs₁ => by cases hs₁; exact ⟨Nat.le_succ _, le_rfl, rfl⟩⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      rcases hmem1 with ⟨rfl, rfl⟩
      exact ⟨hMid0 hPre, fun s₁ hs₁ => by cases hs₁; exact ⟨le_rfl, Nat.le_succ _, rfl⟩⟩
  rcases s₁? with _ | s₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
    rcases hmem2 with ⟨rfl, rfl⟩
    exact ⟨hMidPost hStep1.1, fun _ _ h => by cases h⟩
  · have hs₁ := hStep1.2 s₁ rfl
    rcases hvS : s₁.vS with _ | v
    · simp only [hvS, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      exact ⟨hMidPost hStep1.1, fun st' c hEq => by cases hEq; exact hs₁⟩
    · simp only [hvS] at hmem2
      rw [StateT.run_bind, mem_support_bind_iff] at hmem2
      obtain ⟨⟨fsRes, h₂⟩, hfs, hmem2⟩ := hmem2
      have hP := hFs s₁.tcur v (s₁.tcur, s₁.curCkaMsg) m pair (fsRes, h₂) hStep1.1 hfs
      rcases fsRes with _ | ⟨v', e⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl⟩
        exact ⟨hP, fun _ _ h => by cases h⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl⟩
        exact ⟨hP, fun st' c hEq => by cases hEq; exact hs₁⟩

private theorem vRecv_preserve_generic
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {HPre HMid HPost : HS → Prop}
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (h : HS) (hvR : ∀ t, s.tcur < t → s.vR t = none)
    (hPre : HPre h) (hMid0 : HPre h → HMid h)
    (hMidPost : ∀ {h1}, HMid h1 → HPost h1)
    (hStart : ∀ t0 γ0 σ0 Tn res, HPre h →
      res ∈ support ((hk.startRecv ctx P t0 γ0 σ0 Tn).run h) → HMid res.2)
    (hFs : ∀ {h1} t1 v hHdr e rec' res, HMid h1 →
      res ∈ support ((hk.fsRecv ctx P t1 v hHdr e rec').run h1) → HPost res.2) :
    ∀ res ∈ support ((vRecv hk ctx P s c rec).run h),
      HPost res.2 ∧
      (∀ st' t' i' m', res.1 = some (some (st', t', i', m')) →
        st'.tcur ≤ s.tcur + 1 ∧ (∀ t, st'.tcur < t → st'.vR t = none)) := by
  intro ⟨vrRes, h'⟩ hmem
  rw [vRecv_eq_bind] at hmem
  by_cases h1 : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hMidPost (hMid0 hPre), fun _ _ _ _ h => by cases h⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
    have htle : c.1.1 ≤ s.tcur + 1 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1
      omega
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
    have hStep1 : HMid h₁ ∧
        (∀ s₁, s₁? = some (some s₁) →
          c.1.1 ≤ s₁.tcur ∧ s₁.tcur ≤ s.tcur + 1 ∧
          (∀ t, s₁.tcur < t → s₁.vR t = none)) := by
      unfold vRecvStep1 at hmem1
      by_cases h2 : c.1.1 = s.tcur + 1
      · simp only [h2, ↓reduceIte] at hmem1
        rcases hTn : c.1.2 with _ | Tn
        · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem1
          rcases hmem1 with ⟨rfl, rfl⟩
          exact ⟨hMid0 hPre, fun _ h => by cases h⟩
        · simp only [hTn] at hmem1
          rw [StateT.run_bind, mem_support_bind_iff] at hmem1
          obtain ⟨⟨srRes, h₁'⟩, hsr, hmem1⟩ := hmem1
          have hM := hStart (s.tcur + 1) s.γ s.root Tn (srRes, h₁') hPre hsr
          rcases srRes with _ | _ | ⟨γ', σ', rs⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩
            exact ⟨hM, fun _ h => by cases h⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩
            exact ⟨hM, fun _ h => by cases h⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩
            refine ⟨hM, fun s₁ hs₁ => ?_⟩
            cases hs₁
            refine ⟨by omega, le_rfl, fun t ht => ?_⟩
            dsimp only at ht ⊢
            rw [Function.update_of_ne (by omega)]
            exact hvR t (by omega)
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩
        refine ⟨hMid0 hPre, fun s₁ hs₁ => ?_⟩
        cases hs₁
        exact ⟨by omega, Nat.le_succ _, hvR⟩
    rcases s₁? with _ | _ | s₁
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      exact ⟨hMidPost hStep1.1, fun _ _ _ _ h => by cases h⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      exact ⟨hMidPost hStep1.1, fun _ _ _ _ h => by cases h⟩
    · have hs₁ := hStep1.2 s₁ rfl
      rcases hvR1 : s₁.vR c.1.1 with _ | v
      · simp only [hvR1, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl⟩
        exact ⟨hMidPost hStep1.1, fun _ _ _ _ h => by cases h⟩
      · simp only [hvR1] at hmem2
        rw [StateT.run_bind, mem_support_bind_iff] at hmem2
        obtain ⟨⟨frRes, h₂⟩, hfr, hmem2⟩ := hmem2
        have hP := hFs c.1.1 v c.1 c.2 rec (frRes, h₂) hStep1.1 hfr
        rcases frRes with _ | _ | ⟨v', i, m⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
          rcases hmem2 with ⟨rfl, rfl⟩
          exact ⟨hP, fun _ _ _ _ h => by cases h⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
          rcases hmem2 with ⟨rfl, rfl⟩
          exact ⟨hP, fun _ _ _ _ h => by cases h⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
          rcases hmem2 with ⟨rfl, rfl⟩
          refine ⟨hP, fun st' t' i' m' hEq => ?_⟩
          cases hEq
          refine ⟨hs₁.2.1, fun t ht => ?_⟩
          dsimp only at ht ⊢
          rw [Function.update_of_ne (by omega)]
          exact hs₁.2.2 t ht

private theorem lookupMultiF_preserve [DecidableEq I] [SampleableType K]
    (Ik : I) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((lookupMultiF (SS := SS) (RS := RS) (M := M) Ik).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold lookupMultiF at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hlk : h.table.lookup Ik with _ | k
  · simp only [hlk] at hmem
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨kNew, h0⟩, hk, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
    obtain ⟨_, _, hEq1⟩ := hk
    cases hEq1
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact ⟨by simp, rfl, rfl⟩
  · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

private theorem regSessMulti_preserve [DecidableEq I]
    (Ik : I) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((regSessMulti (SS := SS) (RS := RS) (M := M) Ik).run h),
      res.2.table = h.table ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold regSessMulti at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact ⟨rfl, Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hmem
    cases hmem
    exact ⟨rfl, by simp, rfl⟩

private theorem regSessOptMulti_preserve [DecidableEq I]
    (sid : Option I) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((regSessOptMulti (SS := SS) (RS := RS) (M := M) sid).run h),
      res.2.table = h.table ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  rcases sid with _ | Ik
  · simp only [regSessOptMulti, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact ⟨rfl, Nat.le_add_right _ _, rfl⟩
  · rw [regSessOptMulti, StateT.run_map, map_eq_bind_pure_comp] at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨res0, hmem0, hEq⟩ := hmem
    simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hEq
    cases hEq
    exact regSessMulti_preserve Ik h res0 hmem0

private theorem rootFSMulti_preserve [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t : ℕ) (Ik : I) (σ : RSt)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((rootFSMulti (SS := SS) (RS := RS) (M := M) prng mo t Ik σ).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold rootFSMulti at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨Ir, h0⟩, hIr, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hIr
    obtain ⟨_, _, hEq1⟩ := hIr; cases hEq1
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨k, h1⟩, hk, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
    obtain ⟨_, _, hEq2⟩ := hk; cases hEq2
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨k, h1'⟩, hlk, hmem⟩ := hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact lookupMultiF_preserve Ik h (k, h') hlk
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨Ir, h0⟩, hIr, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hIr
    obtain ⟨_, _, hEq1⟩ := hIr; cases hEq1
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

private theorem hooksFSMulti_startSend_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t : ℕ) (γ : Γ) (σ : RSt) (r : Option CCoins)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P t γ σ r).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMulti at hmem
  dsimp only at hmem
  have hBody : ∀ coins,
      (out, h') ∈ support ((do
        let (σ', k, sid) ← rootFSMulti (SS := SS) (RS := RS) (M := M) prng mo t (cka.send γ coins).2.2 σ
        let optIdx ← regSessOptMulti sid
        modify fun (s : FSMultiState T RSt K I E) =>
          { s with cache := Function.update s.cache t (some ((cka.send γ coins).2.1, σ', k, optIdx)) }
        let ssv : SS ⊕ ℕ := match optIdx with
          | none => .inl (fs.initSender k)
          | some sIdx => .inr sIdx
        return some ((cka.send γ coins).1, (cka.send γ coins).2.1, σ', ssv)).run h) →
      h'.table.length ≤ h.table.length + 1 ∧
      h'.sessions.length ≤ h.sessions.length + 1 ∧
      h'.book = h.book := by
    intro coins hm
    rw [StateT.run_bind, mem_support_bind_iff] at hm
    obtain ⟨⟨⟨σ', k, sid⟩, h1⟩, hrt, hm⟩ := hm
    have hP1 := rootFSMulti_preserve prng mo t (cka.send γ coins).2.2 σ h ((σ', k, sid), h1) hrt
    rw [StateT.run_bind, mem_support_bind_iff] at hm
    obtain ⟨⟨optIdx, h2⟩, hrs, hm⟩ := hm
    have hP2 := regSessOptMulti_preserve sid h1 (optIdx, h2) hrs
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hm
    cases hm
    exact ⟨by dsimp only at hP1 hP2 ⊢; rw [hP2.1]; exact hP1.1,
      by dsimp only at hP1 hP2 ⊢; rw [← hP1.2.1]; exact hP2.2.1,
      by dsimp only at hP1 hP2 ⊢; rw [hP2.2.2, hP1.2.2]⟩
  rcases r with _ | c
  · dsimp only at hmem
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, h0⟩, hc, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hc
    obtain ⟨_, _, hEq⟩ := hc; cases hEq
    exact hBody coins hmem
  · dsimp only at hmem
    rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem
    exact hBody c hmem

private theorem hooksFSMulti_startRecv_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t : ℕ) (γ : Γ) (σ : RSt) (Tn : T)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).startRecv ctx P t γ σ Tn).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMulti at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hcache : h.cache t with _ | ⟨Tc, σc, k, optIdx⟩
  · simp only [hcache] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      cases hmem; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      cases hmem; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨kLk, h1⟩, hlk, hmem⟩ := hmem
      rw [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨sIdx, h2⟩, hrs, hmem⟩ := hmem
      have hP1 := lookupMultiF_preserve (cka.receive γ Tn).2 h (kLk, h1) hlk
      have hP2 := regSessMulti_preserve (cka.receive γ Tn).2 h1 (sIdx, h2) hrs
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      cases hmem
      exact ⟨by dsimp only at hP1 hP2 ⊢; rw [hP2.1]; exact hP1.1,
        by dsimp only at hP1 hP2 ⊢; rw [← hP1.2.1]; exact hP2.2.1,
        by dsimp only at hP1 hP2 ⊢; rw [hP2.2.2, hP1.2.2]⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      cases hmem; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
  · by_cases hTc : Tc = Tn
    · simp only [hcache, hTc, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      cases hmem; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · simp only [hcache, hTc, ↓reduceIte] at hmem
      split_ifs at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        cases hmem; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        cases hmem; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
      · rw [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨kLk, h1⟩, hlk, hmem⟩ := hmem
        rw [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨sIdx, h2⟩, hrs, hmem⟩ := hmem
        have hP1 := lookupMultiF_preserve (cka.receive γ Tn).2 h (kLk, h1) hlk
        have hP2 := regSessMulti_preserve (cka.receive γ Tn).2 h1 (sIdx, h2) hrs
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        cases hmem
        exact ⟨by dsimp only at hP1 hP2 ⊢; rw [hP2.1]; exact hP1.1,
          by dsimp only at hP1 hP2 ⊢; rw [← hP1.2.1]; exact hP2.2.1,
          by dsimp only at hP1 hP2 ⊢; rw [hP2.2.2, hP1.2.2]⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        cases hmem; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩

private theorem hooksFSMulti_fsSend_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t : ℕ) (ssv : SS ⊕ ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).fsSend
        ctx P t ssv hdr m pair).run h),
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      fsBookStep 1 h.book res.2.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMulti at hmem
  dsimp only at hmem
  rcases ssv with ss | sIdx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact ⟨rfl, rfl, fsBookStep_refl 1 rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    have hTail : ∀ (h1 : FSMultiState T RSt K I E),
        (h1.table = h.table ∧ h1.sessions = h.sessions ∧ fsBookStep 0 h.book h1.book) →
        (out, h') ∈ support ((do
          let e? ← match pair with
            | some (m₀, m₁) =>
              liftFSMulti sIdx (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
                hdr m₀ m₁)
            | none =>
              liftFSMulti sIdx (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS)
                hdr m)
          match e? with
          | none => return none
          | some e =>
            modify fun (s : FSMultiState T RSt K I E) =>
              let b := (s.book sIdx).getD {}
              let cnt' := b.fsCount + 1
              let b' : FSMultiBook T E := { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
              { s with book := Function.update s.book sIdx (some b') }
            return some ((.inr sIdx : SS ⊕ ℕ), e)).run h1) →
        h'.table = h.table ∧ h'.sessions = h.sessions ∧ fsBookStep 1 h.book h'.book := by
      intro h1 hStep1 hm
      have hAfterQ : ∀ (e? : Option E),
          (out, h') ∈ support ((match e? with
            | none => pure none
            | some e => do
              modify fun (s : FSMultiState T RSt K I E) =>
                let b := (s.book sIdx).getD {}
                let cnt' := b.fsCount + 1
                let b' : FSMultiBook T E := { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
                { s with book := Function.update s.book sIdx (some b') }
              pure (some ((.inr sIdx : SS ⊕ ℕ), e)) :
            HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h1) →
          h'.table = h.table ∧ h'.sessions = h.sessions ∧ fsBookStep 1 h.book h'.book := by
        intro e? hm2
        rcases e? with _ | e
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm2
          cases hm2
          exact ⟨hStep1.1, hStep1.2.1, fsBookStep_mono (Nat.zero_le 1) hStep1.2.2⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hm2
          cases hm2
          exact ⟨hStep1.1, hStep1.2.1,
            by simpa using fsBookStep_trans hStep1.2.2 (fsBookStep_update_cons h1.book sIdx hdr e)⟩
      rcases pair with _ | ⟨m₀, m₁⟩ <;>
        (dsimp only at hm; rw [StateT.run_bind, mem_support_bind_iff] at hm;
         obtain ⟨⟨e?, h2⟩, he, hm⟩ := hm;
         simp only [liftFSMulti, StateT.run_lift, mem_support_bind_iff, support_pure,
           Set.mem_singleton_iff] at he;
         obtain ⟨_, _, hEq⟩ := he; cases hEq;
         exact hAfterQ e? hm)
    by_cases hCond : (!(ctx.safeCh (2 + Δcka) P) && !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hCond, ↓reduceIte] at hmem
      by_cases hla : la = true
      · simp only [hla, ↓reduceIte, Bool.not_false, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem
        cases hmem; exact ⟨rfl, rfl, fsBookStep_refl 1 rfl⟩
      · simp only [hla, Bool.false_eq_true, ↓reduceIte] at hmem
        rw [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨ans, h0⟩, hans, hmem⟩ := hmem
        simp only [liftFSMulti, StateT.run_lift, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hans
        obtain ⟨_, _, hEq⟩ := hans; cases hEq
        rcases ans with _ | _
        · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hmem
          cases hmem; exact ⟨rfl, rfl, fsBookStep_refl 1 rfl⟩
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
          refine hTail _ ?_ hmem
          exact ⟨rfl, rfl, fsBookStep_update_sCorr h.book sIdx⟩
    · simp only [hCond, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hmem
      exact hTail h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem

private theorem hooksFSMulti_fsRecv_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t : ℕ) (rsv : RS ⊕ ℕ) (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E)))
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).fsRecv
        ctx P t rsv hdr e rec).run h),
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      fsBookStep 0 h.book res.2.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMulti at hmem
  dsimp only at hmem
  rcases rsv with rs | sIdx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    set matched : Option (ℕ × Header T × E) :=
      ((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))
    have hTail : ∀ (la' : Bool) (h1 : FSMultiState T RSt K I E),
        (h1.table = h.table ∧ h1.sessions = h.sessions ∧ fsBookStep 0 h.book h1.book) →
        (out, h') ∈ support ((do
          let res ← if matched.isSome then
              liftFSMulti sIdx (FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
            else
              liftFSMulti sIdx (FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
          match res with
          | none => return none
          | some .rejected => return some none
          | some (.accepted i mo') =>
            let s1 ← get
            let bk1 := (s1.book sIdx).getD {}
            if la' && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
              modify fun (s : FSMultiState T RSt K I E) => { s with lfWin := true }
              return none
            else
              let drop := (matched.map fun (x : ℕ × Header T × E) => x.1).getD i
              modify fun (s : FSMultiState T RSt K I E) =>
                let b := (s.book sIdx).getD {}
                let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
                { s with book := Function.update s.book sIdx (some b') }
              match mo', rec with
              | some m, _ => return some (some ((.inr sIdx : RS ⊕ ℕ), i, m))
              | none, some r => return some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg))
              | none, none => return none).run h1) →
        h'.table = h.table ∧ h'.sessions = h.sessions ∧ fsBookStep 0 h.book h'.book := by
      intro la' h1 hStep1 hm
      have hAfterRes : ∀ (res : Option (FSAEAD.ReceiveResult M)),
          (out, h') ∈ support ((match res with
            | none => pure none
            | some .rejected => pure (some none)
            | some (.accepted i mo') => do
              let s1 ← get
              let bk1 := (s1.book sIdx).getD {}
              if la' && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
                modify fun (s : FSMultiState T RSt K I E) => { s with lfWin := true }
                pure none
              else
                let drop := (matched.map fun (x : ℕ × Header T × E) => x.1).getD i
                modify fun (s : FSMultiState T RSt K I E) =>
                  let b := (s.book sIdx).getD {}
                  let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
                  { s with book := Function.update s.book sIdx (some b') }
                match mo', rec with
                | some m, _ => pure (some (some ((.inr sIdx : RS ⊕ ℕ), i, m)))
                | none, some r => pure (some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg)))
                | none, none => pure none :
            HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h1) →
          h'.table = h.table ∧ h'.sessions = h.sessions ∧ fsBookStep 0 h.book h'.book := by
        intro res hm2
        rcases res with _ | _ | ⟨i, mo'⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm2
          cases hm2; exact hStep1
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm2
          cases hm2; exact hStep1
        · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hm2
          split_ifs at hm2
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hm2
            cases hm2; exact hStep1
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hm2
            have hBk := fsBookStep_trans hStep1.2.2
              (fsBookStep_update_filter h1.book sIdx
                (·.1 != (matched.map fun (x : ℕ × Header T × E) => x.1).getD i))
            rcases mo' with _ | m <;> rcases rec with _ | r <;>
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm2 <;>
              (cases hm2; exact ⟨hStep1.1, hStep1.2.1, by simpa using hBk⟩)
      split_ifs at hm <;>
        (rw [StateT.run_bind, mem_support_bind_iff] at hm;
         obtain ⟨⟨res, h2⟩, hq, hm⟩ := hm;
         simp only [liftFSMulti, StateT.run_lift, mem_support_bind_iff, support_pure,
           Set.mem_singleton_iff] at hq;
         obtain ⟨_, _, hEq⟩ := hq; cases hEq;
         exact hAfterRes res hm)
    by_cases hCond : (matched.isNone && !(SM.healedBy ctx.tL (2 + Δcka) t) &&
        !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hCond, ↓reduceIte] at hmem
      by_cases hla : la = true
      · simp only [hla, ↓reduceIte, Bool.not_false, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem
        cases hmem; exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
      · simp only [hla, Bool.false_eq_true, ↓reduceIte] at hmem
        rw [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨ans, h0⟩, hans, hmem⟩ := hmem
        simp only [liftFSMulti, StateT.run_lift, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hans
        obtain ⟨_, _, hEq⟩ := hans; cases hEq
        rcases ans with _ | _
        · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hmem
          cases hmem; exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
          refine hTail false _ ?_ hmem
          exact ⟨rfl, rfl, fsBookStep_update_sCorr h.book sIdx⟩
    · simp only [hCond, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hmem
      exact hTail la h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem

private theorem hooksFSMulti_reveal_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).reveal ctx P vp).run h),
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      fsBookStep 0 h.book res.2.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMulti at hmem
  dsimp only at hmem
  have hTail : ∀ (vS? : Option (Option SS)) (h1 : FSMultiState T RSt K I E),
      (h1.table = h.table ∧ h1.sessions = h.sessions ∧ fsBookStep 0 h.book h1.book) →
      (out, h') ∈ support ((match vS? with
        | none => pure none
        | some vS =>
          if (match vp.vR mo.tStar with | some (.inr _) => true | _ => false) = true then
            pure none
          else
            pure (some (realParty vp vp.γ vp.root vS fun t =>
              match vp.vR t with | some (.inl rs) => some rs | _ => none)) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h1) →
      h'.table = h.table ∧ h'.sessions = h.sessions ∧ fsBookStep 0 h.book h'.book := by
    intro vS? h1 hStep1 hm
    rcases vS? with _ | vS
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm
      cases hm; exact hStep1
    · split_ifs at hm <;>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm <;>
        (cases hm; exact hStep1)
  rcases hvS : vp.vS with _ | (ss | sIdx) <;> simp only [hvS] at hmem
  · rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem
    exact hTail (some none) h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem
  · rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem
    exact hTail (some (some ss)) h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem
  · by_cases hla : la = true
    · simp only [hla, ↓reduceIte, StateT.run_pure, pure_bind] at hmem
      exact hTail none h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem
    · simp only [hla, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨ans, h0⟩, hans, hmem⟩ := hmem
      simp only [liftFSMulti, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hans
      obtain ⟨_, _, hEq⟩ := hans; cases hEq
      rcases ans with _ | ss
      · rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem
        exact hTail none h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
        refine hTail (some (some ss)) _ ?_ hmem
        exact ⟨rfl, rfl, fsBookStep_update_sCorr h.book sIdx⟩

private theorem hooksFSMultiL_reveal_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (hvR : ∀ t, L ≤ t → vp.vR t = none) :
    (hooksFSMultiL cka prng fs L Δcka mo gMain la).reveal ctx P vp =
      (hooksFSMulti cka prng fs Δcka mo gMain la).reveal ctx P vp := by
  unfold hooksFSMultiL hooksFSMulti
  rcases hvS : vp.vS with _ | (ss | sIdx)
  · simp only [hvS, pure_bind]
    rcases hst : vp.vR mo.tStar with _ | (_ | _) <;> simp only [↓reduceIte, Bool.false_eq_true]
    all_goals
      congr 1; congr 1; congr 1; funext t
      by_cases ht : t < L
      · simp only [ht, ↓reduceIte]
      · simp only [ht, ↓reduceIte, hvR t (by omega)]
  · simp only [hvS, pure_bind]
    rcases hst : vp.vR mo.tStar with _ | (_ | _) <;> simp only [↓reduceIte, Bool.false_eq_true]
    all_goals
      congr 1; congr 1; congr 1; funext t
      by_cases ht : t < L
      · simp only [ht, ↓reduceIte]
      · simp only [ht, ↓reduceIte, hvR t (by omega)]
  · simp only [hvS]
    by_cases hla : la = true
    · simp only [hla, ↓reduceIte, pure_bind]
    · simp only [hla, Bool.false_eq_true, ↓reduceIte]
      congr 1; funext ans; rcases ans with _ | ss
      · simp only [pure_bind]
      · simp only [pure_bind]
        congr 1; funext _
        rcases hst : vp.vR mo.tStar with _ | (_ | _) <;> simp only [↓reduceIte, Bool.false_eq_true]
        all_goals
          congr 1; congr 1; congr 1; funext t
          by_cases ht : t < L
          · simp only [ht, ↓reduceIte]
          · simp only [ht, ↓reduceIte, hvR t (by omega)]

private theorem implEDFPaper_hooksFSMultiL_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hVR : ∀ P t, L ≤ t → (es.g.st P).vR t = none) :
    (DeliverForge.implEDFPaper (hooksFSMultiL cka prng fs L Δcka mo gMain la)
        Δ qep maxSkip cfg π (.inr q)).run es =
      (DeliverForge.implEDFPaper (hooksFSMulti cka prng fs Δcka mo gMain la)
        Δ qep maxSkip cfg π (.inr q)).run es := by
  rcases q with ((((tr | ch) | dl) | ij) | P) | arg
  · rfl
  · rfl
  · rfl
  · rfl
  · change (DeliverForge.corrEPaper _ π P).run es = (DeliverForge.corrEPaper _ π P).run es
    unfold DeliverForge.corrEPaper
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href : (es.abort || es.g.win || !es.g.corrAllowedPaper P)
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte]
      by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
      · simp [hdoom]
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
          hooksFSMultiL_reveal_eq cka prng fs L Δcka mo gMain la es.g P (es.g.st P) (hVR P)]
  · rfl

private theorem commitE_fsMulti_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (old new : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : Pos) :
    (commitE (hooksFSMulti cka prng fs Δcka mo gMain la) s P old new pos).run es =
      pure (some { s.accept P new pos with st := Function.update (s.accept P new pos).st P new },
        es) := by
  unfold commitE
  simp only [pure_bind, run_liftH_bind, hooksFSMulti, StateT.run_pure]

private theorem implEDFPaper_fsMulti_inv
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (q_df : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ res ∈ support
      ((DeliverForge.implEDFPaper (hooksFSMulti cka prng fs Δcka mo gMain la)
        Δ qep maxSkip cfg π (.inr q_df)).run es),
      FSMultiEngineInv L B q res.2 := by
  have hInvQ : FSMultiEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hq1B : q + 1 ≤ B := by have := hInv.tcur_le .A; omega
  let HPre : FSMultiState T RSt K I E → Prop := fun h =>
    h.table.length + (q + 1) ≤ B + 1 ∧
    h.sessions.length + (q + 1) ≤ B + 1 ∧
    ∀ idx bk, h.book idx = some bk → bk.fsTrans.length + (q + 1) ≤ B
  let HMid : FSMultiState T RSt K I E → Prop := fun h =>
    h.table.length + q ≤ B + 1 ∧
    h.sessions.length + q ≤ B + 1 ∧
    ∀ idx bk, h.book idx = some bk → bk.fsTrans.length + (q + 1) ≤ B
  let HPost : FSMultiState T RSt K I E → Prop := fun h =>
    h.table.length + q ≤ B + 1 ∧
    h.sessions.length + q ≤ B + 1 ∧
    ∀ idx bk, h.book idx = some bk → bk.fsTrans.length + q ≤ B
  have hPre₀ : HPre es.h := ⟨hInv.table_le, hInv.sessions_le, hInv.fsTrans_le⟩
  have hMid0 : HPre es.h → HMid es.h := fun hp =>
    ⟨by have := hp.1; omega, by have := hp.2.1; omega, hp.2.2⟩
  have hMidPost : ∀ {h1}, HMid h1 → HPost h1 := fun hm =>
    ⟨hm.1, hm.2.1, fun idx bk hbk => by have := hm.2.2 idx bk hbk; omega⟩
  have hvSend : ∀ ctx P s m pair r res,
      res ∈ support ((vSend (hooksFSMulti cka prng fs Δcka mo gMain la) ctx P s m pair r).run es.h) →
      HPost res.2 ∧ (∀ st' c, res.1 = some (st', c) →
        s.tcur ≤ st'.tcur ∧ st'.tcur ≤ s.tcur + 1 ∧ st'.vR = s.vR) := by
    intro ctx P s m pair r res hmem
    refine vSend_preserve_generic (hooksFSMulti cka prng fs Δcka mo gMain la)
      ctx P s m pair r es.h hPre₀ hMid0 hMidPost
      (fun t0 γ0 σ0 r0 res' hp hss => ?_)
      (fun {h1} t1 v hHdr m' pair' res' hm hfs => ?_) res hmem
    · have hP := hooksFSMulti_startSend_preserve cka prng fs Δcka mo gMain la ctx P t0 γ0 σ0 r0 es.h res' hss
      refine ⟨by have := hp.1; have := hP.1; omega,
        by have := hp.2.1; have := hP.2.1; omega, ?_⟩
      rw [hP.2.2]; exact hp.2.2
    · have hP := hooksFSMulti_fsSend_preserve cka prng fs Δcka mo gMain la ctx P t1 v hHdr m' pair' h1 res' hfs
      refine ⟨by rw [hP.1]; exact hm.1, by rw [hP.2.1]; exact hm.2.1,
        fsBookStep_apply hq1B hm.2.2 hP.2.2⟩
  have hvRecv : ∀ ctx P s c rec res, (∀ t, s.tcur < t → s.vR t = none) →
      res ∈ support ((vRecv (hooksFSMulti cka prng fs Δcka mo gMain la) ctx P s c rec).run es.h) →
      HPost res.2 ∧ (∀ st' t' i' m', res.1 = some (some (st', t', i', m')) →
        st'.tcur ≤ s.tcur + 1 ∧ (∀ t, st'.tcur < t → st'.vR t = none)) := by
    intro ctx P s c rec res hvR hmem
    refine vRecv_preserve_generic (hooksFSMulti cka prng fs Δcka mo gMain la)
      ctx P s c rec es.h hvR hPre₀ hMid0 hMidPost
      (fun t0 γ0 σ0 Tn res' hp hsr => ?_)
      (fun {h1} t1 v hHdr e rec' res' hm hfr => ?_) res hmem
    · have hP := hooksFSMulti_startRecv_preserve cka prng fs Δcka mo gMain la ctx P t0 γ0 σ0 Tn es.h res' hsr
      refine ⟨by have := hp.1; have := hP.1; omega,
        by have := hp.2.1; have := hP.2.1; omega, ?_⟩
      rw [hP.2.2]; exact hp.2.2
    · have hP := hooksFSMulti_fsRecv_preserve cka prng fs Δcka mo gMain la ctx P t1 v hHdr e rec' h1 res' hfr
      refine ⟨by rw [hP.1]; exact hm.1, by rw [hP.2.1]; exact hm.2.1,
        fsBookStep_apply hq1B hm.2.2 (fsBookStep_mono (Nat.zero_le 1) hP.2.2)⟩
  intro ⟨out, es'⟩ hmem
  have hSm := implEDFPaper_inv (hooksFSMulti cka prng fs Δcka mo gMain la) cfg π es q_df hInv.sm
    (out, es') hmem
  rcases q_df with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (out, es') ∈ support ((transmitE _ Δ qep π (P, m, r)).run es) at hmem
    unfold transmitE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hep] at hmem
        by_cases hdoom : π.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
            mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          have hPres := hvSend s₁ P (s₁.st P) m none r (vsRes, h') hvs
          have hSt₁ : s₁.st = es.g.st := Engine.epMgmt_st_eq hep
          rcases vsRes with _ | ⟨st', c⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            have hst' := hPres.2 st' c rfl
            rw [hSt₁] at hst'
            refine ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, fun Q => ?_, fun Q t ht => ?_⟩
            · dsimp only [SM.GameState.record]; rw [hSt₁]
              by_cases hQ : Q = P
              · subst hQ; rw [Function.update_self]; have := hInv.tcur_le Q; have := hst'.2.1; omega
              · rw [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
            · dsimp only [SM.GameState.record] at ht ⊢; rw [hSt₁] at ht ⊢
              by_cases hQ : Q = P
              · subst hQ; rw [Function.update_self] at ht ⊢; rw [hst'.2.2]
                exact hInv.vR_none_of_gt Q t (by have := hst'.1; omega)
              · rw [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht
  · change (out, es') ∈ support ((challE _ Δ qep cfg π (P, m₀, m₁, r)).run es) at hmem
    unfold challE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hep] at hmem
        by_cases hch : (!(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)))
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInvQ
        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hdoom : π.leakDoom es.g s₁
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
              hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
            have hPres := hvSend s₁ P (s₁.st P) _ (some (m₀, m₁)) r (vsRes, h') hvs
            have hSt₁ : s₁.st = es.g.st := Engine.epMgmt_st_eq hep
            rcases vsRes with _ | ⟨st', c⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩
              exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩
              have hst' := hPres.2 st' c rfl
              rw [hSt₁] at hst'
              refine ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, fun Q => ?_, fun Q t ht => ?_⟩
              · dsimp only [SM.GameState.record]; rw [hSt₁]
                by_cases hQ : Q = P
                · subst hQ; rw [Function.update_self]; have := hInv.tcur_le Q; have := hst'.2.1; omega
                · rw [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
              · dsimp only [SM.GameState.record] at ht ⊢; rw [hSt₁] at ht ⊢
                by_cases hQ : Q = P
                · subst hQ; rw [Function.update_self] at ht ⊢; rw [hst'.2.2]
                  exact hInv.vR_none_of_gt Q t (by have := hst'.1; omega)
                · rw [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht
  · change (out, es') ∈ support ((deliverE _ maxSkip cfg (P, c)).run es) at hmem
    unfold deliverE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hPres := hvRecv es.g P (es.g.st P) c (some r) (vrRes, h')
          (hInv.vR_none_of_gt P) hvr
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r)
          · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
          · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [StateT.run_bind, commitE_fsMulti_eq, pure_bind, StateT.run_modify,
            StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          have hst' := hPres.2 st' t' i' m' rfl
          refine ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, fun Q => ?_, fun Q t ht => ?_⟩
          · split_ifs <;> dsimp only [SM.GameState.accept] <;>
              (by_cases hQ : Q = P
               · subst hQ; simp only [Function.update_self]
                 have := hInv.tcur_le Q; have := hst'.1; omega
               · simp only [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q)
          · split_ifs at ht ⊢ <;> dsimp only [SM.GameState.accept] at ht ⊢ <;>
              (by_cases hQ : Q = P
               · subst hQ; simp only [Function.update_self] at ht ⊢; exact hst'.2 t ht
               · simp only [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht)
  · change (out, es') ∈ support ((injectE _ Δ qep cfg (P, c)).run es) at hmem
    unfold injectE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      have hPres := hvRecv es.g P (es.g.st P) c none (vrRes, h') (hInv.vR_none_of_gt P) hvr
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [hqep, ↓reduceIte] at hmem
          by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMulti_eq, pure_bind,
              StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            have hst' := hPres.2 st' t' i' m' rfl
            refine ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, fun Q => ?_, fun Q t ht => ?_⟩
            · dsimp only [SM.GameState.accept]
              by_cases hQ : Q = P
              · subst hQ; simp only [Function.update_self]
                have := hInv.tcur_le Q; have := hst'.1; omega
              · simp only [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
            · dsimp only [SM.GameState.accept] at ht ⊢
              by_cases hQ : Q = P
              · subst hQ; simp only [Function.update_self] at ht ⊢; exact hst'.2 t ht
              · simp only [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases hf : cfg.injectFull t'
            · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩
              exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
            · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩
              exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
  · change (out, es') ∈ support ((DeliverForge.corrEPaper _ π P).run es) at hmem
    unfold DeliverForge.corrEPaper abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨⟨revRes, h'⟩, hrev, hmem⟩ := hmem
        have hP := hooksFSMulti_reveal_preserve cka prng fs Δcka mo gMain la es.g P (es.g.st P)
          es.h (revRes, h') hrev
        have hFsLe := fsBookStep_apply hq1B hInv.fsTrans_le (fsBookStep_mono (Nat.zero_le 1) hP.2.2)
        rcases revRes with _ | st
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm, by dsimp only; rw [hP.1]; exact hInvQ.table_le,
            by dsimp only; rw [hP.2.1]; exact hInvQ.sessions_le,
            hFsLe, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm, by dsimp only; rw [hP.1]; exact hInvQ.table_le,
            by dsimp only; rw [hP.2.1]; exact hInvQ.sessions_le,
            hFsLe, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
  · change (out, es') ∈ support ((DeliverForge.deliverForgeE _ Δ qep cfg (P, c, c')).run es) at hmem
    unfold DeliverForge.deliverForgeE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [htr] at hmem
        by_cases hbad :
            ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
        · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInvQ
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte,
            run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
          have hPres := hvRecv es.g P (es.g.st P) c' none (vrRes, h')
            (hInv.vR_none_of_gt P) hvr
          rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
          · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
            · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩
              exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
              · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMulti_eq, pure_bind,
                  StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩
                have hst' := hPres.2 st' t' i' m' rfl
                refine ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, fun Q => ?_, fun Q t ht => ?_⟩
                · dsimp only [SM.GameState.accept]
                  by_cases hQ : Q = P
                  · subst hQ; simp only [Function.update_self]
                    have := hInv.tcur_le Q; have := hst'.1; omega
                  · simp only [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
                · dsimp only [SM.GameState.accept] at ht ⊢
                  by_cases hQ : Q = P
                  · subst hQ; simp only [Function.update_self] at ht ⊢; exact hst'.2 t ht
                  · simp only [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                by_cases hf : cfg.injectFull t'
                · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                    pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩
                  exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
                · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩
                  exact ⟨hSm, hPres.1.1, hPres.1.2.1, hPres.1.2.2, hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩

private theorem simulateQ_implECDFPaper_fsMulti_eq
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
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (mo : Mode) (gMain la : Bool)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) = fs.receive rs hdr e) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)),
        FSMultiEngineInv L B_q qAdv es →
        (simulateQ
          (handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFPaper
              (hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
                (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
              L (2 + Δcka) qep fs.maxSkip
              (modeCfgEC (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
                fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) mo)
              mo.policy .v0 .v1)) oa).run
          (esEnc
            (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
              (M := M) (E := E))
            (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
              (M := M)) es) =
          (Prod.map id
            (esEnc
              (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                (M := M) (E := E))
              (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
                (M := M))) <$>
            (simulateQ (DeliverForge.implEDFPaper (hooksFSMulti cka prng fs Δcka mo gMain la)
              (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run es) ∧
        ∀ res ∈ support ((simulateQ (DeliverForge.implEDFPaper
            (hooksFSMulti cka prng fs Δcka mo gMain la)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run es),
          FSMultiEngineInv L B_q 0 res.2 := by
  let OO' := prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .sum (.base .ss) .nat) (rsvT := .sum (.base .rs) .nat)
  let hsE := fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  have hVp : (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)) = vpE := rfl
  have hHk := hooksFSMultiC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    cka prng fs L B Δcka mo gMain la hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqE hSampCCoins hSampI hSampK hFsRecvB
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es hInv
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact hInv.mono (Nat.zero_le qAdv)
  | query_bind q mx ih =>
    intro qAdv hq es hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFPaper
              (hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
                (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
              L (2 + Δcka) qep fs.maxSkip (modeCfgEC OO' mo) mo.policy .v0 .v1)) (.inl n)).run
            (esEnc vpE hsE es) =
          (fun u => (u, esEnc vpE hsE es)) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        simp [handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (DeliverForge.implEDFPaper (hooksFSMulti cka prng fs Δcka mo gMain la)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inl n)).run es =
          (fun u => (u, es)) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        simp [DeliverForge.implEDFPaper, coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      rw [hVp]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => ?_, ?_⟩
      · simpa [hVp] using (ih u (hq.2 u) es hInv).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨u, _, hmem⟩ := hmem
        exact (ih u (hq.2 u) es hInv).2 res hmem
    | inr t_df =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hHB : FSMultiHBounded L es.h := hInv.toFSMultiHBounded
      have hStepL := rdecDF_implECDFPaper_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam)
        hDefaultE hsE (FSMultiHBounded L)
        (hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
        (hooksFSMultiL cka prng fs L Δcka mo gMain la) hHk
        L (2 + Δcka) qep fs.maxSkip (modeCfgEC OO' mo) mo.cfg (modeCfgEC_agrees mo)
        heqT heqM heqE mo.policy .v0 .v1
        (.cons (esEnc vpE hsE es)
          (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t_df) .nil))
        es t_df hHB hInv.sm.toBoundedEngine (fun _ _ _ _ => trivial) rfl rfl
      rw [implEDFPaper_hooksFSMultiL_eq cka prng fs L (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
        Δcka mo gMain la es t_df hInv.vR_none_of_le_L] at hStepL
      have hStep :
          ((handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFPaper
              (hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
                (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
              L (2 + Δcka) qep fs.maxSkip (modeCfgEC OO' mo) mo.policy .v0 .v1)) (.inr t_df)).run
            (esEnc vpE hsE es) =
          Prod.map id (esEnc vpE hsE) <$>
            (DeliverForge.implEDFPaper (hooksFSMulti cka prng fs Δcka mo gMain la)
              (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inr t_df)).run es := by
        dsimp only [vpE, hsE] at hStepL ⊢
        simp only [handlerImpl, StateT.run_mk, prngSMCodecDF, ← hStepL,
          map_eq_bind_pure_comp, Function.comp_def]
      rw [hVp]
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁⟩ hmem => ?_, ?_⟩
      · have hInv₁ := implEDFPaper_fsMulti_inv cka prng fs mo.cfg mo.policy Δcka mo gMain la
          es t_df hInv (u, es₁) hmem
        simpa [hVp] using (ih u (hqm u) es₁ hInv₁).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁⟩, hmem₁, hmem₂⟩ := hmem
        have hInv₁ := implEDFPaper_fsMulti_inv cka prng fs mo.cfg mo.policy Δcka mo gMain la
          es t_df hInv (u, es₁) hmem₁
        exact (ih u (hqm u) es₁ hInv₁).2 res hmem₂

/-- Evaluation bridge for `redFSAuthDFPaperMultiProg` on `fsClamp B fs`. -/
theorem redFSAuthDFPaperMultiProg_eval_clamp
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
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (la : Bool) (tL : Option ℕ) (t : ℕ)
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
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip la tL t).eval (fun _ => A) () =
      redFSAuthDFPaperMulti cka prng (fsClamp B fs) lam Δcka qep la tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hInit := initFSMultiEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L ⟨true, tL, t⟩ (.bool false)
    (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redFSAuthDFPaperMultiProg CostedReduction.impl
    redFSAuthDFPaperMulti runFSMultiDFPaper
  dsimp only
  rw [eval_bind, hInit]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSMultiRaw cka prng (fsClamp B fs) lam ⟨true, tL, t⟩ false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initFSMultiRaw_inv cka prng (fsClamp B fs) lam ⟨true, tL, t⟩ false
    hqB hB1 hBB es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_implECDFPaper_fsMulti_eq
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    cka prng (fsClamp B fs) L B B_q Δcka qep ⟨true, tL, t⟩ false la
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  dsimp only [Expr.v0] at hSim
  rw [hms] at hSim
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hmem' => ?_
  have hInv' := hSimInv (b', es') hmem'
  simp only [Prod.map, id_eq]
  congr 1
  exact finishFSMultiE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    L B_q (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy la .v0
    (Env.cons (esEnc fsMultiVpEnc fsMultiHsEnc es') (Env.cons (t := .bool) b' .nil))
    es' hInv'.sm rfl

private theorem deliverForgeE_fsClamp_multi_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q q Δcka qep : ℕ)
    (mo : Mode) (gMain la : Bool)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiState T RSt K I (ℕ × C)))
    (arg : Party × (Header T × (ℕ × C)) × (Header T × (ℕ × C)))
    (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q (q + 1) es.g) :
    (DeliverForge.deliverForgeE
        (hooksFSMulti cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la)
        (2 + Δcka) qep mo.cfg arg).run es =
      (DeliverForge.deliverForgeE
        (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
        (2 + Δcka) qep mo.cfg arg).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases arg with ⟨P, c, c'⟩
  unfold DeliverForge.deliverForgeE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    rcases htr : es.g.inTransit P.other c with _ | r
    · rfl
    · dsimp only
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte]
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
        rw [vRecv_fsClamp_multi_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo gMain la hkB
          es.g P (es.g.st P) c' none es.h (hVR P)]
        rfl

private theorem implEDFPaper_fsClamp_multi_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q q Δcka qep : ℕ)
    (mo : Mode) (gMain la : Bool)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiState T RSt K I (ℕ × C)))
    (t : (SM.specDF (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q (q + 1) es.g) :
    (DeliverForge.implEDFPaper
        (hooksFSMulti cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t)).run es =
      (DeliverForge.implEDFPaper
        (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t)).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · change (transmitE _ _ _ _ (P, m, r)).run es = (transmitE _ _ _ _ (P, m, r)).run es
    unfold transmitE vSend hooksFSMulti fsClamp
    rfl
  · change (challE _ _ _ _ _ (P, m₀, m₁, r)).run es =
      (challE _ _ _ _ _ (P, m₀, m₁, r)).run es
    unfold challE vSend hooksFSMulti fsClamp
    rfl
  · change (deliverE _ maxSkip mo.cfg (P, c)).run es = (deliverE _ maxSkip mo.cfg (P, c)).run es
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind]
        rw [vRecv_fsClamp_multi_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo gMain la hkB
          es.g P (es.g.st P) c (some r) es.h (hVR P)]
        rfl
  · change (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es =
      (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka)))
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
      rw [vRecv_fsClamp_multi_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo gMain la hkB
        es.g P (es.g.st P) c none es.h (hVR P)]
      rfl
  · change (DeliverForge.corrEPaper _ mo.policy P).run es =
      (DeliverForge.corrEPaper _ mo.policy P).run es
    unfold DeliverForge.corrEPaper hooksFSMulti fsClamp
    rfl
  · exact deliverForgeE_fsClamp_multi_eq cka prng ae G maxSkip B B_q q Δcka qep mo gMain la
      hB es arg hVR

private theorem simulateQ_implEDFPaper_multi_fsClamp_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka qep : ℕ)
    (mo : Mode) (gMain la : Bool)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    {α : Type} {oa : OracleComp (unifSpec + SM.specDF
      (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
      M CCoins (Header T × (ℕ × C))) α}
    {q : ℕ}
    (hoa : oa.IsQueryBoundP
      (isGameQuery (G := SM.specDF
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) q)
    (es : EState (VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiState T RSt K I (ℕ × C)))
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q q es.g) :
    (simulateQ (DeliverForge.implEDFPaper
        (hooksFSMulti cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es =
      (simulateQ (DeliverForge.implEDFPaper
        (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es := by
  induction oa using OracleComp.inductionOn generalizing q es with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    rcases qy with n | t_df
    · have hCoinL :
          (DeliverForge.implEDFPaper
            (hooksFSMulti cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la)
            (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inl n)).run es =
          (fun u => (u, es)) <$>
            query (spec := unifSpec + FSMultiSpec (FSAEAD.RatchetSenderState K)
              (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) (.inl n) := by
        simp [DeliverForge.implEDFPaper, coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (DeliverForge.implEDFPaper
            (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
            (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inl n)).run es =
          (fun u => (u, es)) <$>
            query (spec := unifSpec + FSMultiSpec (FSAEAD.RatchetSenderState K)
              (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) (.inl n) := by
        simp [DeliverForge.implEDFPaper, coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u (hmx u) es hInv hVR
    · have hqp : 0 < q := hq0.resolve_left (by simp [isGameQuery])
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [implEDFPaper_fsClamp_multi_eq cka prng ae G maxSkip B B_q q' Δcka qep
        mo gMain la hB es t_df hVR]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      have hInv' := implEDFPaper_inv
        (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
        mo.cfg mo.policy es t_df hInv (u, es') hmem
      have hVR' := implEDFPaper_vrInv
        (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
        (hooksFSMulti_vrInv_fromAEADPRG cka prng ae G maxSkip Δcka mo gMain la)
        mo.cfg mo.policy es t_df hInv hVR (u, es') hmem
      exact ih u (hmx u) es' hInv' hVR'

/-- `fsClamp B` removal for `redFSAuthDFPaperMulti` on `FSAEAD.fromAEADPRG`. -/
theorem redFSAuthDFPaperMulti_fsClamp_fromAEADPRG {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka qep : ℕ)
    (lam : I) (la : Bool) (tL : Option ℕ) (t : ℕ)
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    redFSAuthDFPaperMulti cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        lam Δcka qep la tL t A =
      redFSAuthDFPaperMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka qep la tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  unfold redFSAuthDFPaperMulti runFSMultiDFPaper
  have hInitEq :
      initFSMultiRaw cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) lam ⟨true, tL, t⟩ false =
        initFSMultiRaw cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam ⟨true, tL, t⟩ false := rfl
  have hms1 : (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)).maxSkip = maxSkip := rfl
  have hms2 : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hInitEq, hms1, hms2, bind_assoc, bind_assoc]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have ⟨hInv₀, hVR₀⟩ :
      SMEngineInv L B_q qAdv es₀.g ∧ SMVRInv (FSVROkMultiStep maxSkip) B_q qAdv es₀.g := by
    unfold initFSMultiRaw at hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨kr, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨kc, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨⟨⟨σ, k, sid⟩, h₁⟩, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨⟨optIdx, h₂⟩, _, hes₀⟩ := hes₀
    simp only [support_pure, Set.mem_singleton_iff] at hes₀
    subst hes₀
    refine ⟨(SMEngineInv.init _ false hB1 hBB).mono hqB, fun P t₀ v hv => ?_⟩
    cases P <;> simp only [mkParties] at hv
    · by_cases ht0 : t₀ = 0
      · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv
        subst hv
        rcases optIdx with _ | sIdx
        · exact (RSReach.init ae G maxSkip k).mono (Nat.zero_le _)
        · trivial
      · simp [ht0] at hv
    · cases hv
  rw [simulateQ_implEDFPaper_multi_fsClamp_eq cka prng ae G maxSkip L B B_q Δcka qep
    ⟨true, tL, t⟩ false la hFsB hA' es₀ hInv₀ hVR₀]

/-- Combined evaluation + `fsClamp` removal bridge for `redFSAuthDFPaperMultiProg` on
`FSAEAD.fromAEADPRG`. -/
theorem redFSAuthDFPaperMultiProg_eval_fromAEADPRG {MK C : Type}
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → FSAEAD.RatchetSenderState K}
    {fsInitReceiver : K → FSAEAD.RatchetReceiverState K MK}
    {fsSend : FSAEAD.RatchetSenderState K → Header T → M →
      FSAEAD.RatchetSenderState K × (ℕ × C)}
    {fsReceive : FSAEAD.RatchetReceiverState K MK → Header T → (ℕ × C) →
      Option (FSAEAD.RatchetReceiverState K MK × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool}
    {eqM : M → M → Bool} {eqE : (ℕ × C) → (ℕ × C) → Bool}
    {lam : I} {defaultE : ℕ × C}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka qep : ℕ)
    (la : Bool) (tL : Option ℕ) (t : ℕ)
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = (FSAEAD.fromAEADPRG ae G maxSkip).initSender)
    (hFsInitR : fsInitReceiver = (FSAEAD.fromAEADPRG ae G maxSkip).initReceiver)
    (hFsSend : fsSend = (FSAEAD.fromAEADPRG ae G maxSkip).send)
    (hFsRecv : fsReceive = (FSAEAD.fromAEADPRG ae G maxSkip).receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR)) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip la tL t).eval (fun _ => A) () =
      redFSAuthDFPaperMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka qep la tL t A := by
  have heqE' : eqE = fun x1 x2 : ℕ × C => @BEq.beq (ℕ × C) instBEqOfDecidableEq x1 x2 := by
    cases heqE
    funext ⟨a1, c1⟩ ⟨a2, c2⟩
    by_cases ha : a1 = a2 <;> by_cases hc : c1 = c2 <;> simp [BEq.beq, ha, hc]
  have h1 := redFSAuthDFPaperMultiProg_eval_clamp (lam := lam) cka prng
    (FSAEAD.fromAEADPRG ae G maxSkip) L B B_q Δcka qep la tL t
    hInitA hInitB hSend hRecv hPrngInit hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqI heqM heqE' hDefaultE hSampKR hSampKC hSampCCoins hSampI hSampK
    hB1 hBB A qAdv hA hqB
  have hms : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hms] at h1
  exact h1.trans (redFSAuthDFPaperMulti_fsClamp_fromAEADPRG cka prng ae G maxSkip
    L B B_q Δcka qep lam la tL t hFsB hB1 hBB A qAdv hA hqB)

/-! #### `(tL, par)`-Bucket Evaluation Bridge (`redFSAuthDFPaperMultiBucketProgGen_eval_clamp`) -/

private def fsMultiDFBucketHsEnc (h : FSMultiDFBucketState T RSt K I E) :
    (fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  (h.cache, h.fTable, h.sessions,
   (fun sIdx => (h.book sIdx).map fun b => (b.sCorr, b.fsCount, b.fsTrans)),
   h.lfWin)

private def FSMultiDFBucketHBounded (L : ℕ) (h : FSMultiDFBucketState T RSt K I E) : Prop :=
  (∀ t, (h.fTable t).length ≤ L) ∧
  (∀ t, (h.sessions t).length ≤ L) ∧
  ∀ sIdx bk, h.book sIdx = some bk → bk.fsTrans.length ≤ L

private def FSMultiDFBucketHBoundedPost (L : ℕ) (h : FSMultiDFBucketState T RSt K I E) : Prop :=
  ∀ sIdx bk, h.book sIdx = some bk → bk.fsTrans.length ≤ L

private def FSMultiDFBucketStepBounded (B_q q : ℕ)
    (h : FSMultiDFBucketState T RSt K I E) : Prop :=
  (∀ t, (h.fTable t).length + q ≤ B_q + 1) ∧
  (∀ t, (h.sessions t).length + q ≤ B_q + 1) ∧
  ∀ sIdx bk, h.book sIdx = some bk → bk.fsTrans.length + q ≤ B_q

private theorem FSMultiDFBucketStepBounded.mono {B_q m₁ m₂ : ℕ}
    {h : FSMultiDFBucketState T RSt K I E} (hm : m₁ ≤ m₂)
    (hB : FSMultiDFBucketStepBounded B_q m₂ h) :
    FSMultiDFBucketStepBounded B_q m₁ h :=
  ⟨fun t => by have := hB.1 t; omega,
   fun t => by have := hB.2.1 t; omega,
   fun sIdx bk hbk => by have := hB.2.2 sIdx bk hbk; omega⟩

private theorem FSMultiDFBucketStepBounded.toHBounded {L B_q q : ℕ}
    {h : FSMultiDFBucketState T RSt K I E} (hB1 : B_q + 1 ≤ L)
    (hB : FSMultiDFBucketStepBounded B_q q h) :
    FSMultiDFBucketHBounded L h :=
  ⟨fun t => by have := hB.1 t; omega,
   fun t => by have := hB.2.1 t; omega,
   fun sIdx bk hbk => by have := hB.2.2 sIdx bk hbk; omega⟩

private theorem validGuessBucketParPaperE_eval {S' : Sig} {O' : Ops S'} (Δbucket : ℕ)
    (tL : Option ℕ) (par : Bool) {Γ'} (tE : Expr O' Γ' .nat) (ρ : Env Γ') :
    (validGuessBucketParPaperE Δbucket tL par tE).eval ρ =
      inStage2BucketGen Δbucket tL par (tE.eval ρ) := by
  unfold validGuessBucketParPaperE inStage2BucketGen
  have htL : (optNatLit (O' := O') tL).eval ρ = tL := by cases tL <;> rfl
  simp only [Expr.eval, validGuessE_eval, senderOfE_eval, htL]
  congr 1
  cases par <;> cases Party.senderOf (tE.eval ρ) <;> rfl

private theorem bucketParPaperAuthCfgEC_agrees
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) :
    ConfigECAgrees
      (bucketParPaperAuthCfgEC Δbucket tL par :
        ConfigEC (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
          fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE))
      (bucketAuthCfgGen (Msg := M) Δbucket tL par) where
  deliverWin_eq := rfl
  injectFull_eq t' ρ := validGuessBucketParPaperE_eval Δbucket tL par t' ρ
  challOK_eq _ _ := rfl
  challMsg_eq _ _ _ _ _ := rfl

private theorem lookupMultiDFBucketF_preserve [DecidableEq I] [SampleableType K]
    (t0 : ℕ) (ik : I) (h : FSMultiDFBucketState T RSt K I E) :
    ∀ res ∈ support ((lookupMultiDFBucketF (SS := SS) (RS := RS) (M := M) t0 ik).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold lookupMultiDFBucketF at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hlk : (h.fTable t0).lookup ik with _ | k
  · simp only [hlk] at hmem
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨kNew, h0⟩, hk, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
    obtain ⟨_, _, hEq1⟩ := hk; cases hEq1
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    refine ⟨fun τ => ?_, rfl, rfl⟩
    by_cases hτ : τ = t0 <;> simp [Function.update, hτ]
  · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact ⟨fun _ => Nat.le_add_right _ _, rfl, rfl⟩

private theorem regSessMultiDFBucket_preserve [DecidableEq I]
    (L : ℕ) (tL : Option ℕ) (t0 : ℕ) (ik : I) (h : FSMultiDFBucketState T RSt K I E) :
    (regSessMultiDFBucket L tL t0 ik h).2.fTable = h.fTable ∧
    (∀ τ, ((regSessMultiDFBucket L tL t0 ik h).2.sessions τ).length ≤ (h.sessions τ).length + 1) ∧
    (regSessMultiDFBucket L tL t0 ik h).2.book = h.book := by
  dsimp only [regSessMultiDFBucket]
  split_ifs
  · exact ⟨rfl, fun _ => Nat.le_add_right _ _, rfl⟩
  · refine ⟨rfl, fun τ => ?_, rfl⟩
    by_cases hτ : τ = t0 <;> simp [Function.update, hτ]

private theorem regSessOptMultiDFBucket_preserve [DecidableEq I]
    (L : ℕ) (tL : Option ℕ) (t0 : ℕ) (sid : Option I) (h : FSMultiDFBucketState T RSt K I E) :
    (regSessOptMultiDFBucket L tL t0 sid h).2.fTable = h.fTable ∧
    (∀ τ, ((regSessOptMultiDFBucket L tL t0 sid h).2.sessions τ).length ≤ (h.sessions τ).length + 1) ∧
    (regSessOptMultiDFBucket L tL t0 sid h).2.book = h.book := by
  rcases sid with _ | ik
  · exact ⟨rfl, fun _ => Nat.le_add_right _ _, rfl⟩
  · exact regSessMultiDFBucket_preserve L tL t0 ik h

private theorem rootFSMultiDFBucketPaper_preserve [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : RSt) (h : FSMultiDFBucketState T RSt K I E) :
    ∀ res ∈ support ((rootFSMultiDFBucketPaper (SS := SS) (RS := RS) (M := M)
        prng Δbucket qep tL par t0 pl ik0 σ0).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  dsimp only [rootFSMultiDFBucketPaper] at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl, rfl⟩
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ir, h0⟩, hIr, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hIr
    obtain ⟨_, _, hEq1⟩ := hIr; cases hEq1
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨kSample, h1⟩, hk, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
    obtain ⟨_, _, hEq2⟩ := hk; cases hEq2
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl, rfl⟩
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨kLookup, h1⟩, hlk, hmem⟩ := hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact lookupMultiDFBucketF_preserve t0 ik0 h (kLookup, h') hlk
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ir, h0⟩, hIr, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hIr
    obtain ⟨_, _, hEq1⟩ := hIr; cases hEq1
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨kSample, h1⟩, hk, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
    obtain ⟨_, _, hEq2⟩ := hk; cases hEq2
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl, rfl⟩

private theorem hooksFSMultiDFBucketPaper_startSend_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σ0 : RSt) (r0 : Option CCoins)
    (h : FSMultiDFBucketState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).startSend
        ctx P t0 γ0 σ0 r0).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      (∀ τ, (res.2.sessions τ).length ≤ (h.sessions τ).length + 1) ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMultiDFBucketPaper at hmem
  dsimp only at hmem
  have hBody : ∀ coins,
      (out, h') ∈ support ((do
        let cOut := cka.send γ0 coins
        let (σ', kVal, sid) ← rootFSMultiDFBucketPaper (SS := SS) (RS := RS) (M := M) (E := E)
          prng Δbucket qep tL par t0 (postLeakDFBucket tL ctx) cOut.2.2 σ0
        let s1 ← (get : HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) _)
        let (optIdx, s2) := regSessOptMultiDFBucket L tL t0 sid s1
        set { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
        let ssv : SS ⊕ ℕ := match optIdx with
          | none => .inl (fs.initSender kVal)
          | some sIdx => .inr sIdx
        return some (cOut.1, cOut.2.1, σ', ssv)).run h) →
      (∀ τ, (h'.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      (∀ τ, (h'.sessions τ).length ≤ (h.sessions τ).length + 1) ∧
      h'.book = h.book := by
    intro coins hm
    rw [StateT.run_bind, mem_support_bind_iff] at hm
    obtain ⟨⟨⟨σ', kVal, sid⟩, h1⟩, hrt, hm⟩ := hm
    have hP1 := rootFSMultiDFBucketPaper_preserve prng Δbucket qep tL par
      t0 (postLeakDFBucket tL ctx) (cka.send γ0 coins).2.2 σ0 h ((σ', kVal, sid), h1) hrt
    have hP2 := regSessOptMultiDFBucket_preserve L tL t0 sid h1
    simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hm
    cases hm
    exact ⟨fun τ => by dsimp only at hP1 hP2 ⊢; rw [hP2.1]; exact hP1.1 τ,
      fun τ => by dsimp only at hP1 hP2 ⊢; rw [← hP1.2.1]; exact hP2.2.1 τ,
      by dsimp only at hP1 hP2 ⊢; rw [hP2.2.2, hP1.2.2]⟩
  rcases r0 with _ | c
  · dsimp only at hmem
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, h0⟩, hc, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hc
    obtain ⟨_, _, hEq⟩ := hc; cases hEq
    exact hBody coins hmem
  · dsimp only at hmem
    rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem
    exact hBody c hmem

private theorem hooksFSMultiDFBucketPaper_startRecv_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σ0 : RSt) (tn0 : T)
    (h : FSMultiDFBucketState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).startRecv
        ctx P t0 γ0 σ0 tn0).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      (∀ τ, (res.2.sessions τ).length ≤ (h.sessions τ).length + 1) ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMultiDFBucketPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have hNoneBranch :
      (out, h') ∈ support ((
        if !(qep + 1 < t0) && inStage2BucketGen Δbucket tL par t0 then
          if tL.isSome && (t0 == healEpoch tL) then
            return none
          else if postLeakDFBucket tL ctx then
            let kk := cka.receive γ0 tn0
            let p := prng.up σ0 kk.2
            return some (some (kk.1, p.1, (Sum.inl (fs.initReceiver p.2) : RS ⊕ ℕ)))
          else do
            let kk := cka.receive γ0 tn0
            let _ ← lookupMultiDFBucketF t0 kk.2
            let s1 ← get
            let (sIdx, s2) := regSessMultiDFBucket L tL t0 kk.2 s1
            set s2
            return some (some (kk.1, (prng.up σ0 kk.2).1, (Sum.inr sIdx : RS ⊕ ℕ)))
        else
          return some none :
        HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) _).run h) →
      (∀ τ, (h'.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      (∀ τ, (h'.sessions τ).length ≤ (h.sessions τ).length + 1) ∧
      h'.book = h.book := by
    intro hm
    split_ifs at hm
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm
      cases hm; exact ⟨fun _ => Nat.le_add_right _ _, fun _ => Nat.le_add_right _ _, rfl⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm
      cases hm; exact ⟨fun _ => Nat.le_add_right _ _, fun _ => Nat.le_add_right _ _, rfl⟩
    · rw [StateT.run_bind, mem_support_bind_iff] at hm
      obtain ⟨⟨kLk, h1⟩, hlk, hm⟩ := hm
      have hP1 := lookupMultiDFBucketF_preserve t0 (cka.receive γ0 tn0).2 h (kLk, h1) hlk
      have hP2 := regSessMultiDFBucket_preserve L tL t0 (cka.receive γ0 tn0).2 h1
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hm
      cases hm
      exact ⟨fun τ => by dsimp only at hP1 hP2 ⊢; rw [hP2.1]; exact hP1.1 τ,
        fun τ => by dsimp only at hP1 hP2 ⊢; rw [← hP1.2.1]; exact hP2.2.1 τ,
        by dsimp only at hP1 hP2 ⊢; rw [hP2.2.2, hP1.2.2]⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm
      cases hm; exact ⟨fun _ => Nat.le_add_right _ _, fun _ => Nat.le_add_right _ _, rfl⟩
  rcases hcache : h.cache t0 with _ | ⟨tCached, σc, kVal, optIdx⟩
  · simp only [hcache] at hmem; exact hNoneBranch hmem
  · by_cases hTc : tCached = tn0
    · simp only [hcache, hTc, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      cases hmem; exact ⟨fun _ => Nat.le_add_right _ _, fun _ => Nat.le_add_right _ _, rfl⟩
    · simp only [hcache, hTc, ↓reduceIte] at hmem; exact hNoneBranch hmem

private theorem hooksFSMultiDFBucketPaper_fsSend_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t0 : ℕ) (ssv : SS ⊕ ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiDFBucketState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).fsSend
        ctx P t0 ssv hdr m pair).run h),
      res.2.fTable = h.fTable ∧
      res.2.sessions = h.sessions ∧
      fsBookStep 1 h.book res.2.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMultiDFBucketPaper at hmem
  dsimp only at hmem
  rcases ssv with ss | sIdx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨rfl, rfl, fsBookStep_refl 1 rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    have hTail : ∀ (h1 : FSMultiDFBucketState T RSt K I E),
        (h1.fTable = h.fTable ∧ h1.sessions = h.sessions ∧ fsBookStep 0 h.book h1.book) →
        (out, h') ∈ support ((do
          let e? ← match pair with
            | some (m₀, m₁) =>
              liftFSMultiDFBucket sIdx (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
                hdr m₀ m₁)
            | none =>
              liftFSMultiDFBucket sIdx (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS)
                hdr m)
          match e? with
          | none => return none
          | some e =>
            modify fun (s : FSMultiDFBucketState T RSt K I E) =>
              let b := (s.book sIdx).getD {}
              let cnt' := b.fsCount + 1
              let b' : FSMultiBook T E := { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
              { s with book := Function.update s.book sIdx (some b') }
            return some ((.inr sIdx : SS ⊕ ℕ), e)).run h1) →
        h'.fTable = h.fTable ∧ h'.sessions = h.sessions ∧ fsBookStep 1 h.book h'.book := by
      intro h1 hStep1 hm
      have hAfterQ : ∀ (e? : Option E),
          (out, h') ∈ support ((match e? with
            | none => pure none
            | some e => do
              modify fun (s : FSMultiDFBucketState T RSt K I E) =>
                let b := (s.book sIdx).getD {}
                let cnt' := b.fsCount + 1
                let b' : FSMultiBook T E := { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
                { s with book := Function.update s.book sIdx (some b') }
              pure (some ((.inr sIdx : SS ⊕ ℕ), e)) :
            HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) _).run h1) →
          h'.fTable = h.fTable ∧ h'.sessions = h.sessions ∧ fsBookStep 1 h.book h'.book := by
        intro e? hm2
        rcases e? with _ | e
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm2
          cases hm2; exact ⟨hStep1.1, hStep1.2.1, fsBookStep_mono (Nat.zero_le 1) hStep1.2.2⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hm2
          cases hm2
          exact ⟨hStep1.1, hStep1.2.1,
            by simpa using fsBookStep_trans hStep1.2.2 (fsBookStep_update_cons h1.book sIdx hdr e)⟩
      rcases pair with _ | ⟨m₀, m₁⟩ <;>
        (dsimp only at hm; rw [StateT.run_bind, mem_support_bind_iff] at hm;
         obtain ⟨⟨e?, h2⟩, he, hm⟩ := hm;
         simp only [liftFSMultiDFBucket, StateT.run_lift, mem_support_bind_iff, support_pure,
           Set.mem_singleton_iff] at he;
         obtain ⟨_, _, hEq⟩ := he; cases hEq;
         exact hAfterQ e? hm)
    by_cases hCond : (!(ctx.safeCh (2 + Δcka) P) && !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hCond, ↓reduceIte] at hmem
      rw [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨ans, h0⟩, hans, hmem⟩ := hmem
      simp only [liftFSMultiDFBucket, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hans
      obtain ⟨_, _, hEq⟩ := hans; cases hEq
      rcases ans with _ | _
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem
        cases hmem; exact ⟨rfl, rfl, fsBookStep_refl 1 rfl⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
        refine hTail _ ?_ hmem
        exact ⟨rfl, rfl, fsBookStep_update_sCorr h.book sIdx⟩
    · simp only [hCond, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hmem
      exact hTail h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem

private theorem hooksFSMultiDFBucketPaper_fsRecv_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t0 : ℕ) (rsv : RS ⊕ ℕ) (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E)))
    (h : FSMultiDFBucketState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).fsRecv
        ctx P t0 rsv hdr e rec).run h),
      res.2.fTable = h.fTable ∧
      res.2.sessions = h.sessions ∧
      fsBookStep 0 h.book res.2.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMultiDFBucketPaper at hmem
  dsimp only at hmem
  rcases rsv with rs | sIdx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    set matched : Option (ℕ × Header T × E) :=
      ((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))
    have hTail : ∀ (h1 : FSMultiDFBucketState T RSt K I E),
        (h1.fTable = h.fTable ∧ h1.sessions = h.sessions ∧ fsBookStep 0 h.book h1.book) →
        (out, h') ∈ support ((do
          let res ← if matched.isSome then
              liftFSMultiDFBucket sIdx (FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
            else
              liftFSMultiDFBucket sIdx (FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
          match res with
          | none => return none
          | some .rejected => return some none
          | some (.accepted i mo') =>
            let s1 ← get
            let bk1 := (s1.book sIdx).getD {}
            if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
              modify fun (s : FSMultiDFBucketState T RSt K I E) => { s with lfWin := true }
              return none
            else
              let drop := (matched.map Prod.fst).getD i
              modify fun (s : FSMultiDFBucketState T RSt K I E) =>
                let b := (s.book sIdx).getD {}
                let b' : FSMultiBook T E :=
                  { b with fsTrans := b.fsTrans.filter (fun x => x.1 != drop) }
                { s with book := Function.update s.book sIdx (some b') }
              match mo', rec with
              | some m, _ => return some (some ((.inr sIdx : RS ⊕ ℕ), i, m))
              | none, some r => return some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg))
              | none, none => return none).run h1) →
        h'.fTable = h.fTable ∧ h'.sessions = h.sessions ∧ fsBookStep 0 h.book h'.book := by
      intro h1 hStep1 hm
      have hAfterRes : ∀ (res : Option (FSAEAD.ReceiveResult M)),
          (out, h') ∈ support ((match res with
            | none => pure none
            | some .rejected => pure (some none)
            | some (.accepted i mo') => do
              let s1 ← get
              let bk1 := (s1.book sIdx).getD {}
              if ((la && matched.isNone && !bk1.sCorr) && decide (bk1.fsCount < i)) = true then
                modify fun (s : FSMultiDFBucketState T RSt K I E) => { s with lfWin := true }
                pure none
              else
                let drop := (matched.map Prod.fst).getD i
                modify fun (s : FSMultiDFBucketState T RSt K I E) =>
                  let b := (s.book sIdx).getD {}
                  let b' : FSMultiBook T E :=
                    { b with fsTrans := b.fsTrans.filter (fun x => x.1 != drop) }
                  { s with book := Function.update s.book sIdx (some b') }
                match mo', rec with
                | some m, _ => pure (some (some ((.inr sIdx : RS ⊕ ℕ), i, m)))
                | none, some r => pure (some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg)))
                | none, none => pure none :
            HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) _).run h1) →
          h'.fTable = h.fTable ∧ h'.sessions = h.sessions ∧ fsBookStep 0 h.book h'.book := by
        intro res hm2
        rcases res with _ | _ | ⟨i, mo'⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm2
          cases hm2; exact hStep1
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm2
          cases hm2; exact hStep1
        · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hm2
          split_ifs at hm2
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hm2
            cases hm2; exact hStep1
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hm2
            have hFlt := fsBookStep_update_filter h1.book sIdx
              (fun x => x.1 != (matched.map Prod.fst).getD i)
            have hBk : fsBookStep 0 h.book
                (Function.update h1.book sIdx
                  (some { (h1.book sIdx).getD {} with
                    fsTrans := ((h1.book sIdx).getD {}).fsTrans.filter
                      (fun x => x.1 != (matched.map Prod.fst).getD i) })) := by
              simpa using fsBookStep_trans hStep1.2.2 hFlt
            rcases mo' with _ | m <;> rcases rec with _ | r <;>
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm2 <;>
              (cases hm2; exact ⟨hStep1.1, hStep1.2.1, hBk⟩)
      split_ifs at hm <;>
        (dsimp only at hm; rw [StateT.run_bind, mem_support_bind_iff] at hm;
         obtain ⟨⟨res, h2⟩, hq, hm⟩ := hm;
         simp only [liftFSMultiDFBucket, StateT.run_lift, mem_support_bind_iff, support_pure,
           Set.mem_singleton_iff] at hq;
         obtain ⟨_, _, hEq⟩ := hq; cases hEq;
         exact hAfterRes res hm)
    by_cases hCond : ((matched.isNone && !(SM.healedBy ctx.tL (2 + Δcka) t0)) &&
        !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hCond, ↓reduceIte] at hmem
      rw [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨ans, h0⟩, hans, hmem⟩ := hmem
      simp only [liftFSMultiDFBucket, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hans
      obtain ⟨_, _, hEq⟩ := hans; cases hEq
      rcases ans with _ | _
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem
        cases hmem; exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
        refine hTail _ ?_ hmem
        exact ⟨rfl, rfl, fsBookStep_update_sCorr h.book sIdx⟩
    · simp only [hCond, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hmem
      exact hTail h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem

private theorem hooksFSMultiDFBucketPaper_reveal_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (h : FSMultiDFBucketState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).reveal
        ctx P vp).run h),
      res.2.fTable = h.fTable ∧
      res.2.sessions = h.sessions ∧
      fsBookStep 0 h.book res.2.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMultiDFBucketPaper at hmem
  dsimp only at hmem
  have hTail : ∀ (vS? : Option (Option SS)) (h1 : FSMultiDFBucketState T RSt K I E),
      (h1.fTable = h.fTable ∧ h1.sessions = h.sessions ∧ fsBookStep 0 h.book h1.book) →
      (out, h') ∈ support ((match vS? with
        | none => pure none
        | some ssReal =>
          if (List.range L).any (fun t => match vp.vR t with | some (.inr _) => true | _ => false) then
            pure none
          else
            let vR' : ℕ → Option RS := fun t =>
              if t < L then match vp.vR t with | some (.inl rs) => some rs | _ => none else none
            pure (some (realParty vp vp.γ vp.root ssReal vR')) :
        HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) _).run h1) →
      h'.fTable = h.fTable ∧ h'.sessions = h.sessions ∧ fsBookStep 0 h.book h'.book := by
    intro vS? h1 hStep1 hm
    rcases vS? with _ | ssReal
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm
      cases hm; exact hStep1
    · split_ifs at hm <;>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hm <;>
        (cases hm; exact hStep1)
  rcases hvS : vp.vS with _ | (ss | sIdx) <;> simp only [hvS] at hmem
  · rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem
    exact hTail (some none) h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem
  · rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem
    exact hTail (some (some ss)) h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ans, h0⟩, hans, hmem⟩ := hmem
    simp only [liftFSMultiDFBucket, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hans
    obtain ⟨_, _, hEq⟩ := hans; cases hEq
    rcases ans with _ | ss
    · rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem
      exact hTail none h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hmem
    · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
      refine hTail (some (some ss)) _ ?_ hmem
      exact ⟨rfl, rfl, fsBookStep_update_sCorr h.book sIdx⟩

section BucketEvalHelpers1

variable
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
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
local notation "mVpTy" => fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mBookTy" => fsMultiDFSessBookTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsMBEnc" =>
  fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
    (SS := SS) (RS := RS) (M := M)

private theorem fsMultiDFBucketHsGetBookAt_eval {O'} {Γ'}
    (hE : Expr O' Γ' mbHsTy) (sIdxE : Expr O' Γ' .nat) (ρ : Env Γ')
    (h : FSMultiDFBucketState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (fsMultiDFBucketHsGetBookAt hE sIdxE).eval ρ =
      let b := (h.book (sIdxE.eval ρ)).getD {}
      (b.sCorr, b.fsCount, b.fsTrans) := by
  unfold fsMultiDFBucketHsGetBookAt
  simp only [fsMultiDFBucketHsBook, fsMultiDFBucketHsEnc, hh, Expr.eval, Expr.v0, Env.get_cons_zero]
  rcases h.book (sIdxE.eval ρ) with _ | ⟨sc, cnt, tr⟩ <;> rfl

private theorem fsMultiDFBucketHsSetBookAt_eval {O'} {Γ'}
    (hE : Expr O' Γ' mbHsTy) (sIdxE : Expr O' Γ' .nat) (entryE : Expr O' Γ' mBookTy) (ρ : Env Γ')
    (h : FSMultiDFBucketState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h)
    {sc : Bool} {cnt : ℕ} {tr : List (ℕ × Header T × E)}
    (hentry : entryE.eval ρ = (sc, cnt, tr)) :
    (fsMultiDFBucketHsSetBookAt hE sIdxE entryE).eval ρ =
      hsMBEnc { h with book := Function.update h.book (sIdxE.eval ρ) (some ⟨sc, cnt, tr⟩) } := by
  unfold fsMultiDFBucketHsSetBookAt fsMultiDFBucketHsMk
  simp only [pair_eval, tset_eval_eq_update, some_eval, hentry,
    fsMultiDFBucketHsCache, fsMultiDFBucketHsTableTbl, fsMultiDFBucketHsSessionsTbl,
    fsMultiDFBucketHsBook, fsMultiDFBucketHsLfWin,
    fst_eval, snd_eval, hh, fsMultiDFBucketHsEnc, Prod.mk.injEq, true_and, and_true]
  funext i
  by_cases hi : i = sIdxE.eval ρ <;> simp [Function.update, hi]

private theorem fsMultiDFBucketHsSetCache_eval {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (caE : Expr OO Γ' (.tbl (.opt (fsMultiDFCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E))))
    (ρ : Env Γ') (h : FSMultiDFBucketState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (fsMultiDFBucketHsSetCache hE caE).eval ρ = hsMBEnc { h with cache := caE.eval ρ } := by
  simp [fsMultiDFBucketHsSetCache, fsMultiDFBucketHsMk, fsMultiDFBucketHsTableTbl,
    fsMultiDFBucketHsSessionsTbl, fsMultiDFBucketHsBook, fsMultiDFBucketHsLfWin,
    fsMultiDFBucketHsEnc, hh, Expr.eval]

private theorem fsMultiDFBucketHsSetTableAt_eval {Γ'}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat)
    (tbE : Expr OO Γ' (.list (fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (ρ : Env Γ') (h : FSMultiDFBucketState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (fsMultiDFBucketHsSetTableAt hE tE tbE).eval ρ =
      hsMBEnc { h with fTable := Function.update h.fTable (tE.eval ρ) (tbE.eval ρ) } := by
  unfold fsMultiDFBucketHsSetTableAt fsMultiDFBucketHsMk
  simp only [pair_eval, tset_eval_eq_update, fsMultiDFBucketHsCache, fsMultiDFBucketHsTableTbl,
    fsMultiDFBucketHsSessionsTbl, fsMultiDFBucketHsBook, fsMultiDFBucketHsLfWin,
    fst_eval, snd_eval, hh, fsMultiDFBucketHsEnc]

private theorem fsMultiDFBucketHsSetSessionsAt_eval {Γ'}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat)
    (seE : Expr OO Γ' (.list (.base .i)))
    (ρ : Env Γ') (h : FSMultiDFBucketState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (fsMultiDFBucketHsSetSessionsAt hE tE seE).eval ρ =
      hsMBEnc { h with sessions := Function.update h.sessions (tE.eval ρ) (seE.eval ρ) } := by
  unfold fsMultiDFBucketHsSetSessionsAt fsMultiDFBucketHsMk
  simp only [pair_eval, tset_eval_eq_update, fsMultiDFBucketHsCache, fsMultiDFBucketHsTableTbl,
    fsMultiDFBucketHsSessionsTbl, fsMultiDFBucketHsBook, fsMultiDFBucketHsLfWin,
    fst_eval, snd_eval, hh, fsMultiDFBucketHsEnc]

private theorem fsMultiDFBucketHsSetLfWin_eval {Γ'}
    (hE : Expr OO Γ' mbHsTy) (lwE : Expr OO Γ' .bool)
    (ρ : Env Γ') (h : FSMultiDFBucketState T RSt K I E) (hh : hE.eval ρ = hsMBEnc h) :
    (fsMultiDFBucketHsSetLfWin hE lwE).eval ρ = hsMBEnc { h with lfWin := lwE.eval ρ } := by
  simp [fsMultiDFBucketHsSetLfWin, fsMultiDFBucketHsMk, fsMultiDFBucketHsCache,
    fsMultiDFBucketHsTableTbl, fsMultiDFBucketHsSessionsTbl, fsMultiDFBucketHsBook,
    fsMultiDFBucketHsEnc, hh, Expr.eval]

private theorem lookupMultiDFBucketFC_eval [DecidableEq I] [SampleableType K]
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) {Γ'} (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (h : FSMultiDFBucketState T RSt K I E)
    (hh : hE.eval ρ = hsMBEnc h) (hL : (h.fTable (tE.eval ρ)).length ≤ L) :
    (lookupMultiDFBucketFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE tE ikE).eval ρ =
      Prod.map id hsMBEnc <$>
        (lookupMultiDFBucketF (T := T) (RSt := RSt) (K := K) (I := I) (SS := SS) (RS := RS)
          (M := M) (E := E) (tE.eval ρ) (ikE.eval ρ)).run h ∧
    ∀ res ∈ support ((lookupMultiDFBucketF (T := T) (RSt := RSt) (K := K) (I := I)
        (SS := SS) (RS := RS) (M := M) (E := E) (tE.eval ρ) (ikE.eval ρ)).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  refine ⟨?_, lookupMultiDFBucketF_preserve (tE.eval ρ) (ikE.eval ρ) h⟩
  unfold lookupMultiDFBucketFC lookupMultiDFBucketF
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set Ik : I := ikE.eval ρ
  have h0 : (Expr.pair hE (.pair tE ikE)).eval ρ = (hsMBEnc h, t0, Ik) := by
    simp [Expr.eval, hh, t0, Ik]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod mbHsTy (.prod .nat (.base CKASort.i))) (hsMBEnc h, t0, Ik) ρ
  have hTbl : (tableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (.tget (fsMultiDFBucketHsTableTbl (.fst .v0)) (.fst (.snd .v0)))
      (.snd (.snd .v0))).eval ρ₁ = (h.fTable t0).lookup Ik := by
    rw [tableLookupE_eval heqI L
      (.tget (fsMultiDFBucketHsTableTbl (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd .v0)) ρ₁
      (by simpa [ρ₁, fsMultiDFBucketHsTableTbl, fsMultiDFBucketHsEnc, Expr.eval, Expr.v0] using hL)]
    rfl
  rw [eval_caseOpt, hTbl]
  rcases hlk : (h.fTable t0).lookup Ik with _ | kFound
  · simp only [hlk, eval_bind, StateT.run_bind, StateT.run_get,
      StateT.run_lift, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc, map_bind]
    have hSamp : (@Comp.sample _ _ _ OO IIM _ CKASamp.k .unit).eval ρ₁ =
        (sampleT K : TComp (FSMultiSpec SS RS T M E) K) := by
      simp only [Comp.eval, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampK, sampleT]
      exact Engine.liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ K)
    rw [hSamp]
    refine bind_congr fun kNew => ?_
    rw [eval_ret, pair_eval, fsMultiDFBucketHsSetTableAt_eval _ _ _ _ h rfl]
    simp [ρ₁, Prod.map, Expr.eval, Expr.v0, Expr.v1, fsMultiDFBucketHsTableTbl,
      fsMultiDFBucketHsEnc]
  · simp [ρ₁, hlk, Comp.eval, StateT.run_bind, StateT.run_get,
      StateT.run_pure, pure_bind, Prod.map, Expr.eval, Expr.v0, Expr.v1]

private theorem regSessMultiDFBucketE_eval_pair [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (h : FSMultiDFBucketState T RSt K I E)
    (hh : hE.eval ρ = hsMBEnc h) (hL : (h.sessions (tE.eval ρ)).length ≤ L) :
    (regSessMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L tL hE tE ikE).eval ρ =
      (let p := regSessMultiDFBucket L tL (tE.eval ρ) (ikE.eval ρ) h
       (p.1, hsMBEnc p.2)) ∧
    let p := regSessMultiDFBucket L tL (tE.eval ρ) (ikE.eval ρ) h
    p.2.fTable = h.fTable ∧
    (∀ t', (p.2.sessions t').length ≤ (h.sessions t').length + 1) ∧
    p.2.book = h.book := by
  refine ⟨?_, regSessMultiDFBucket_preserve L tL (tE.eval ρ) (ikE.eval ρ) h⟩
  unfold regSessMultiDFBucketE
  dsimp only [regSessMultiDFBucket]
  rw [letE_eval]
  set t0 : ℕ := tE.eval ρ
  set Ik : I := ikE.eval ρ
  have h0 : (Expr.pair hE (.pair tE ikE)).eval ρ = (hsMBEnc h, t0, Ik) := by
    simp [Expr.eval, hh, t0, Ik]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod mbHsTy (.prod .nat (.base CKASort.i))) (hsMBEnc h, t0, Ik) ρ
  set sesExpr : Expr OO _ (.list (.base .i)) :=
    .tget (fsMultiDFBucketHsSessionsTbl (.fst .v0)) (.fst (.snd .v0))
  have hSesEval : sesExpr.eval ρ₁ = h.sessions t0 := by
    simp [sesExpr, ρ₁, fsMultiDFBucketHsSessionsTbl, fsMultiDFBucketHsEnc, Expr.eval, Expr.v0]
  have hSesL : (sesExpr.eval ρ₁).length ≤ L := hSesEval ▸ hL
  have hMem : (sessionsMemE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L sesExpr (.snd (.snd .v0))).eval ρ₁ = decide (Ik ∈ h.sessions t0) := by
    rw [sessionsMemE_eval heqI L sesExpr (.snd (.snd .v0)) ρ₁ hSesL, hSesEval]; rfl
  have hIdx : (sessionsIdxOfE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L sesExpr (.snd (.snd .v0))).eval ρ₁ = (h.sessions t0).idxOf Ik := by
    rw [sessionsIdxOfE_eval heqI L sesExpr (.snd (.snd .v0)) ρ₁ hSesL, hSesEval]; rfl
  have hLen : (sessionsLenE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L sesExpr).eval ρ₁ = (h.sessions t0).length := by
    rw [sessionsLenE_eval L sesExpr ρ₁ hSesL, hSesEval]
  have hApp : (sessionsAppendOneE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L sesExpr (.snd (.snd .v0))).eval ρ₁ = h.sessions t0 ++ [Ik] := by
    rw [sessionsAppendOneE_eval L sesExpr (.snd (.snd .v0)) ρ₁ hSesL, hSesEval]; rfl
  change (Expr.ite (sessionsMemE L sesExpr (.snd (.snd .v0))) _ _).eval ρ₁ = _
  rw [ite_eval, hMem]
  by_cases hm : Ik ∈ h.sessions t0
  · simp only [hm, decide_true, ↓reduceIte, pair_eval]
    rw [Expr.eval, hIdx]
    simp [ρ₁, Expr.eval, Expr.v0]
  · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, pair_eval]
    rw [fsMultiDFBucketHsSetSessionsAt_eval _ _ _ ρ₁ h rfl, hApp, Expr.eval, hLen]
    simp [ρ₁, Expr.eval, Expr.v0]

end BucketEvalHelpers1

private theorem regSessOptMultiDFBucketE_eval_pair
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (tE : Expr _ Γ' .nat) (sidE : Expr _ Γ' (.opt (.base .i)))
    (ρ : Env Γ') (h : FSMultiDFBucketState T RSt K I E)
    (hh : hE.eval ρ = fsMultiDFBucketHsEnc h)
    (hL : (h.sessions (tE.eval ρ)).length ≤ L) :
    (regSessOptMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L tL hE tE sidE).eval ρ =
      (let p := regSessOptMultiDFBucket L tL (tE.eval ρ) (sidE.eval ρ) h
       (p.1, fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
         (SS := SS) (RS := RS) (M := M) p.2)) ∧
    let p := regSessOptMultiDFBucket L tL (tE.eval ρ) (sidE.eval ρ) h
    p.2.fTable = h.fTable ∧
    (∀ t', (p.2.sessions t').length ≤ (h.sessions t').length + 1) ∧
    p.2.book = h.book := by
  refine ⟨?_, regSessOptMultiDFBucket_preserve L tL (tE.eval ρ) (sidE.eval ρ) h⟩
  unfold regSessOptMultiDFBucketE regSessOptMultiDFBucket
  rw [letE_eval]
  set t0 : ℕ := tE.eval ρ
  rcases hsid : sidE.eval ρ with _ | Ik
  · simp [hsid, hh, Expr.eval, Expr.v0]
  · let OO := prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
    have h0 : (Expr.pair hE (.pair tE sidE)).eval ρ = (fsMultiDFBucketHsEnc h, t0, some Ik) := by
      simp [Expr.eval, hh, t0, hsid]
    rw [h0]
    set ρ₁ := Env.cons (t := .base CKASort.i) Ik
      (Env.cons (t := .prod (fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        (.prod .nat (.opt (.base CKASort.i))))
        (fsMultiDFBucketHsEnc h, t0, some Ik) ρ)
    have hReg := (regSessMultiDFBucketE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) heqI L tL
      (Expr.fst (O := OO) .v1) (.fst (.snd .v1)) .v0 ρ₁ h rfl hL).1
    have ht1 : (Expr.fst (.snd (Expr.v1 (O := OO)))).eval ρ₁ = t0 := rfl
    have hik1 : (Expr.v0 (O := OO)).eval ρ₁ = Ik := rfl
    rw [ht1, hik1] at hReg
    change (Expr.pair (.some (.fst _)) (.snd _)).eval ρ₁ = _
    rw [pair_eval, some_eval, fst_eval, snd_eval, hReg]

private theorem postLeakDFBucketE_eval {O' : Ops S} {VP : Type} {vpT : Ty S}
    (vpEnc : VP → vpT.denote) (tL : Option ℕ) {Γ'}
    (ctxE : Expr O' Γ' (cGsTy vpT)) (ρ : Env Γ')
    (ctx : GameState VP M (Header T × E))
    (hctx : ctxE.eval ρ = cGsEnc vpEnc ctx) :
    (postLeakDFBucketE tL ctxE).eval ρ = postLeakDFBucket tL ctx := by
  unfold postLeakDFBucketE postLeakDFBucket
  have hc : (cGsTL ctxE).eval ρ = ctx.tL := by
    simp [cGsTL, hctx, cGsEnc, Expr.eval]
  cases htl : ctx.tL with
  | none => simp [Expr.eval, hc, htl]
  | some cur =>
    have htL : ∀ {Γ''} (ρ' : Env Γ''), (optNatLit (O' := O') tL).eval ρ' = tL := fun _ => by
      cases tL <;> rfl
    simp [Expr.eval, Expr.v0, hc, htl, ltOptE_eval, htL]

private theorem rootFSMultiDFBucketPaperC_eval
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
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K)
    (hPrngUp : prngUp = prng.up) (heqI : eqI = (· == ·))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (tE : Expr _ Γ' .nat) (plE : Expr _ Γ' .bool)
    (ikE : Expr _ Γ' (.base .i)) (σE : Expr _ Γ' (.base .sig))
    (ρ : Env Γ') (h : FSMultiDFBucketState T RSt K I E)
    (hh : hE.eval ρ = fsMultiDFBucketHsEnc h) (hL : (h.fTable (tE.eval ρ)).length ≤ L) :
    (rootFSMultiDFBucketPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L Δbucket qep tL par hE tE plE ikE σE).eval ρ =
      Prod.map id
        (fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
          (SS := SS) (RS := RS) (M := M)) <$>
        (rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
          prng Δbucket qep tL par (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σE.eval ρ)).run h ∧
    ∀ res ∈ support ((rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
        prng Δbucket qep tL par (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σE.eval ρ)).run h),
      (∀ t', (res.2.fTable t').length ≤ (h.fTable t').length + 1) ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  refine ⟨?_, rootFSMultiDFBucketPaper_preserve prng Δbucket qep tL par
    (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σE.eval ρ) h⟩
  let OO := prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
  let IIM := fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
  unfold rootFSMultiDFBucketPaperC
  dsimp only [rootFSMultiDFBucketPaper]
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set Ik : I := ikE.eval ρ
  set σ0 : RSt := σE.eval ρ
  set pl : Bool := plE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair ikE (.pair σE plE)))).eval ρ =
      (fsMultiDFBucketHsEnc h, t0, Ik, σ0, pl) := by
    simp [Expr.eval, hh, t0, Ik, σ0, pl]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    (.prod .nat (.prod (.base CKASort.i) (.prod (.base CKASort.sig) .bool))))
    (fsMultiDFBucketHsEnc h, t0, Ik, σ0, pl) ρ
  have hSampIComp : ∀ {Γ''} (ρ' : Env Γ''),
      (@Comp.sample _ _ _ OO IIM Γ'' CKASamp.i .unit).eval ρ' =
        (sampleT I : TComp (FSMultiSpec SS RS T M E) I) := by
    intro Γ'' ρ'
    simp only [IIM, Comp.eval, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampI, sampleT]
    exact Engine.liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ I)
  have hSampKComp : ∀ {Γ''} (ρ' : Env Γ''),
      (@Comp.sample _ _ _ OO IIM Γ'' CKASamp.k .unit).eval ρ' =
        (sampleT K : TComp (FSMultiSpec SS RS T M E) K) := by
    intro Γ'' ρ'
    simp only [IIM, Comp.eval, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampK, sampleT]
    exact Engine.liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ K)
  have hLk : (lookupMultiDFBucketFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))).eval ρ₁ =
      Prod.map id
        (fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
          (SS := SS) (RS := RS) (M := M)) <$>
        (lookupMultiDFBucketF (T := T) (RSt := RSt) (K := K) (I := I) (SS := SS) (RS := RS)
          (M := M) (E := E) t0 Ik).run h :=
    (lookupMultiDFBucketFC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI)
      heqI hSampK L (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) ρ₁ h rfl hL).1
  rw [eval_ite]
  have hlt1 : (orE (.snd (.snd (.snd (.snd (Expr.v0 (O := OO))))))
      (.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := OO)))))).eval ρ₁ =
      (pl || decide (qep + 1 < t0)) := by
    simp only [ρ₁, orE, Expr.eval, Expr.v0, Env.get_cons_zero]
    cases pl <;> rfl
  rw [hlt1]
  by_cases hgt : (pl || decide (qep + 1 < t0)) = true
  · simp [ρ₁, hgt, Comp.eval, StateT.run_pure, hPrngUp, Prod.map, Expr.eval, Expr.v0]
  · simp only [hgt, Bool.false_eq_true, ↓reduceIte]
    rw [eval_ite]
    have hvg : (validGuessBucketParPaperE (O' := OO) Δbucket tL par (.fst (.snd .v0))).eval ρ₁ =
        inStage2BucketGen Δbucket tL par t0 :=
      validGuessBucketParPaperE_eval Δbucket tL par (.fst (.snd .v0)) ρ₁
    rw [hvg]
    have hcondH : (Expr.and (.bool tL.isSome)
        (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat (healEpoch tL)))).eval ρ₁ =
        (tL.isSome && (t0 == healEpoch tL)) := by
      by_cases htH : t0 = healEpoch tL <;> simp [ρ₁, htH, Expr.eval, Expr.v0]
    by_cases hIn : inStage2BucketGen Δbucket tL par t0 = true
    · simp only [hIn, ↓reduceIte]
      rw [eval_ite, hcondH]
      by_cases htH : (tL.isSome && (t0 == healEpoch tL)) = true
      · simp only [htH, ↓reduceIte, eval_bind, hSampIComp, StateT.run_bind,
          StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, map_bind]
        refine bind_congr fun ir => ?_
        simp only [hSampKComp]
        refine bind_congr fun kSample => ?_
        simp [ρ₁, Comp.eval, hPrngUp, Prod.map, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
      · simp only [htH, Bool.false_eq_true, ↓reduceIte]
        rw [eval_bind, hLk, StateT.run_bind, bind_map_left, map_bind]
        refine bind_congr fun ⟨kLookup, h1⟩ => ?_
        simp [ρ₁, Comp.eval, StateT.run_pure, hPrngUp, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · simp only [hIn, Bool.false_eq_true, ↓reduceIte]
      rw [eval_ite, hcondH]
      by_cases htH : (tL.isSome && (t0 == healEpoch tL)) = true
      · simp only [htH, ↓reduceIte, eval_bind, hSampIComp, StateT.run_bind,
          StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, map_bind]
        refine bind_congr fun ir => ?_
        simp only [hSampKComp]
        refine bind_congr fun kSample => ?_
        simp [ρ₁, Comp.eval, hPrngUp, Prod.map, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
      · simp [ρ₁, htH, Comp.eval, StateT.run_pure, hPrngUp, Prod.map, Expr.eval, Expr.v0]

section BucketEvalHelpers2

variable
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
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
local notation "mVpTy" => fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsMBEnc" =>
  fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
    (SS := SS) (RS := RS) (M := M)
local notation "vpMEnc" =>
  fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)

private theorem fsMultiDFBucketPaperStartSendC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
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
    (L Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : FSMultiDFBucketState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (hHB : FSMultiDFBucketHBounded L h) (hh : hE.eval ρ = hsMBEnc h)
    (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx) :
    (fsMultiDFBucketPaperStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket qep tL par hE ctxE pE tE γE σE rE).eval ρ =
      Prod.map id hsMBEnc <$>
        ((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).startSend ctx P
          (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (rE.eval ρ)).run h := by
  unfold fsMultiDFBucketPaperStartSendC
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set γ0 : Γ := γE.eval ρ
  set σ0 : RSt := σE.eval ρ
  set r0 : Option CCoins := rE.eval ρ
  set pl : Bool := postLeakDFBucket tL ctx
  have hpl : (postLeakDFBucketE tL ctxE).eval ρ = pl :=
    postLeakDFBucketE_eval vpMEnc tL ctxE ρ ctx hctx
  have h0 : (Expr.pair hE (.pair tE (.pair γE (.pair σE (.pair rE (postLeakDFBucketE tL ctxE)))))).eval ρ =
      (hsMBEnc h, t0, γ0, σ0, r0, pl) := by
    simp [Expr.eval, hh, hpl, t0, γ0, σ0, r0, pl]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mbHsTy (.prod .nat (.prod (.base CKASort.γ)
      (.prod (.base CKASort.sig) (.prod (.opt (.base CKASort.ccoins)) .bool)))))
    (hsMBEnc h, t0, γ0, σ0, r0, pl) ρ
  have hStep1 :
      (Comp.caseOpt (O := OO) (I := IIM) (.fst (.snd (.snd (.snd (.snd .v0)))))
        (@Comp.sample _ _ _ OO IIM _ CKASamp.ccoins .unit)
        (.ret .v0)).eval ρ₁ =
      (match r0 with
        | some c => pure c
        | none => (sampleT CCoins : TComp (FSMultiSpec SS RS T M E) CCoins)) := by
    rcases r0 with _ | c
    · simp only [ρ₁, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero,
        fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampCCoins, sampleT]
      exact Engine.liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ CCoins)
    · rfl
  have hRHS :
      ((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).startSend
        ctx P t0 γ0 σ0 r0).run h =
      ((match r0 with
          | some c => pure c
          | none => (sampleT CCoins : TComp (FSMultiSpec SS RS T M E) CCoins)) >>=
        fun coins =>
          (do
            let cOut := cka.send γ0 coins
            let (σ', kVal, sid) ← rootFSMultiDFBucketPaper (SS := SS) (RS := RS) (M := M) (E := E)
              prng Δbucket qep tL par t0 pl cOut.2.2 σ0
            let s1 ← (get : HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) _)
            let (optIdx, s2) := regSessOptMultiDFBucket L tL t0 sid s1
            set { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
            let ssv : SS ⊕ ℕ := match optIdx with
              | none => .inl (fs.initSender kVal)
              | some sIdx => .inr sIdx
            return some (cOut.1, cOut.2.1, σ', ssv)).run h) := by
    unfold hooksFSMultiDFBucketPaper; dsimp only
    rcases r0 with _ | c
    · dsimp only; rw [StateT.run_bind, StateT.run_lift, bind_assoc]
      refine bind_congr fun _ => ?_
      rw [pure_bind]
    · dsimp only; rw [StateT.run_bind, StateT.run_pure, pure_bind]
      symm; rw [pure_bind]
  rw [eval_bind, hStep1, hRHS, map_bind]
  refine bind_congr fun coins => ?_
  set ρ₂ := Env.cons (t := .base CKASort.ccoins) coins ρ₁
  have hRoot := rootFSMultiDFBucketPaperC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins)
    prng hPrngUp heqI hSampI hSampK L Δbucket qep tL par (.fst .v1) (.fst (.snd .v1))
    (.snd (.snd (.snd (.snd (.snd .v1)))))
    (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
    (.fst (.snd (.snd (.snd .v1)))) ρ₂ h rfl (hHB.1 t0)
  have hIkEval : (Expr.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend
      (.pair (.fst (.snd (.snd .v1))) .v0)))).eval ρ₂ = (cka.send γ0 coins).2.2 := by
    simp [ρ₂, ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1]
  have htEval : (Expr.fst (.snd (Expr.v1 (O := OO)))).eval ρ₂ = t0 := rfl
  have hplEval : (Expr.snd (.snd (.snd (.snd (.snd (Expr.v1 (O := OO))))))).eval ρ₂ = pl := rfl
  have hσEval : (Expr.fst (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₂ = σ0 := rfl
  rw [hIkEval, htEval, hplEval, hσEval] at hRoot
  rw [eval_bind, hRoot.1, StateT.run_bind, bind_map_left, map_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨σ', kVal, sid⟩, h₁⟩ hmemRoot => ?_
  have ⟨_, hSes₁, _⟩ := hRoot.2 ((σ', kVal, sid), h₁) hmemRoot
  have hSesL₁ : (h₁.sessions t0).length ≤ L := hSes₁ ▸ hHB.2.1 t0
  set ρ₃ := Env.cons
    (t := .prod (.prod (.base CKASort.sig) (.prod (.base CKASort.k) (.opt (.base CKASort.i))))
      mbHsTy)
    ((σ', kVal, sid), hsMBEnc h₁) ρ₂
  have hReg := (regSessOptMultiDFBucketE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) heqI L tL
    (.snd .v0) (.fst (.snd .v2)) (.snd (.snd (.fst .v0))) ρ₃ h₁ rfl hSesL₁).1
  have ht3 : (Expr.fst (.snd (Expr.v2 (O := OO)))).eval ρ₃ = t0 := rfl
  have hsid3 : (Expr.snd (.snd (.fst (Expr.v0 (O := OO))))).eval ρ₃ = sid := rfl
  rw [ht3, hsid3] at hReg
  set p := regSessOptMultiDFBucket L tL t0 sid h₁
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
    pure_bind, map_pure, Prod.map, id_eq]
  change (Comp.ret _).eval ρ₃ = _
  have hRegFst : (Expr.fst (regSessOptMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L tL (.snd .v0) (.fst (.snd .v2)) (.snd (.snd (.fst .v0))))).eval ρ₃ = p.1 := by
    rw [fst_eval, hReg]
  have hRegSnd : (Expr.snd (regSessOptMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L tL (.snd .v0) (.fst (.snd .v2)) (.snd (.snd (.fst .v0))))).eval ρ₃ = hsMBEnc p.2 := by
    rw [snd_eval, hReg]
  rw [eval_ret, pair_eval, fsMultiDFBucketHsSetCache_eval _ _ ρ₃ p.2 hRegSnd]
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
      have hca : (fsMultiDFBucketHsCache (.snd (regSessOptMultiDFBucketE (ckaInitA := ckaInitA)
          (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
          (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
          (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
          (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
          (defaultE := defaultE) L tL (.snd .v0) (.fst (.snd .v2))
          (.snd (.snd (.fst .v0)))))).eval ρ₃ = p.2.cache := by
        unfold fsMultiDFBucketHsCache; rw [fst_eval, hRegSnd]; rfl
      have hkEval : (Expr.fst (.snd (Expr.v2 (O := OO)))).eval ρ₃ = t0 := rfl
      have hvEval : (Expr.some (.pair
          (.fst (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v2))) .v1))))
          (.pair (.fst (.fst .v0))
            (.pair (.fst (.snd (.fst .v0)))
              (.fst (regSessOptMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                L tL (.snd .v0) (.fst (.snd .v2)) (.snd (.snd (.fst .v0))))))))).eval ρ₃ =
          some ((cka.send γ0 coins).2.1, σ', kVal, p.1) := by
        rw [some_eval, pair_eval, pair_eval, pair_eval, hRegFst]
        simp [ρ₃, ρ₂, ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
      rw [hca, hkEval, hvEval]

private theorem fsMultiDFBucketPaperStartRecvC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
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
    (L Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : FSMultiDFBucketState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (hHB : FSMultiDFBucketHBounded L h) (hh : hE.eval ρ = hsMBEnc h)
    (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx) :
    (fsMultiDFBucketPaperStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket qep tL par hE ctxE pE tE γE σE tnE).eval ρ =
      Prod.map id hsMBEnc <$>
        ((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).startRecv ctx P
          (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h := by
  unfold fsMultiDFBucketPaperStartRecvC hooksFSMultiDFBucketPaper
  dsimp only
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set γ0 : Γ := γE.eval ρ
  set σ0 : RSt := σE.eval ρ
  set Tn : T := tnE.eval ρ
  set pl : Bool := postLeakDFBucket tL ctx
  have hpl : (postLeakDFBucketE tL ctxE).eval ρ = pl :=
    postLeakDFBucketE_eval vpMEnc tL ctxE ρ ctx hctx
  have h0 : (Expr.pair hE (.pair tE (.pair γE (.pair σE (.pair tnE (postLeakDFBucketE tL ctxE)))))).eval ρ =
      (hsMBEnc h, t0, γ0, σ0, Tn, pl) := by
    simp [Expr.eval, hh, hpl, t0, γ0, σ0, Tn, pl]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mbHsTy (.prod .nat (.prod (.base CKASort.γ)
      (.prod (.base CKASort.sig) (.prod (.base CKASort.t) .bool)))))
    (hsMBEnc h, t0, γ0, σ0, Tn, pl) ρ
  have hNoneBranch :
      (Comp.ite (O := OO) (I := IIM)
        (.and (.not (.lt (.nat (qep + 1)) (.fst (.snd .v0))))
          (validGuessBucketParPaperE Δbucket tL par (.fst (.snd .v0))))
        (.ite (.and (.bool tL.isSome) (.eqN (.fst (.snd .v0)) (.nat (healEpoch tL))))
          (.ret (.pair .none (.fst .v0)))
          (.ite (.snd (.snd (.snd (.snd (.snd .v0)))))
            (.ret (.pair
              (.some (.some (.pair
                (.fst (Expr.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0))))))))
                (.pair
                  (.fst (Expr.op (O := OO) CKAOp.prngUp
                    (.pair (.fst (.snd (.snd (.snd .v0))))
                      (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                        (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0)))))))))))
                  (Expr.inl (u := .nat)
                    (Expr.op (O := OO) CKAOp.fsInitReceiver
                      (.snd (Expr.op (O := OO) CKAOp.prngUp
                        (.pair (.fst (.snd (.snd (.snd .v0))))
                          (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                            (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0)))))))))))))))))
              (.fst .v0)))
            (.bind
              (lookupMultiDFBucketFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L (.fst .v0) (.fst (.snd .v0))
                (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0)))))))))
              (.ret (.pair
                (.some (.some (.pair
                  (.fst (Expr.op (O := OO) CKAOp.ckaReceive
                    (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1))))))))
                  (.pair
                    (.fst (Expr.op (O := OO) CKAOp.prngUp
                      (.pair (.fst (.snd (.snd (.snd .v1))))
                        (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                          (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1)))))))))))
                    (Expr.inr (t := .base CKASort.rs) (.fst (regSessMultiDFBucketE L tL (.snd .v0)
                      (.fst (.snd .v1))
                      (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                        (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1)))))))))))))))
                (.snd (regSessMultiDFBucketE L tL (.snd .v0) (.fst (.snd .v1))
                  (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                    (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1)))))))))))))))
        (.ret (.pair (.some .none) (.fst .v0)))).eval ρ₁ =
      Prod.map id hsMBEnc <$>
        ((if (!(decide (qep + 1 < t0)) && inStage2BucketGen Δbucket tL par t0) = true then
            if (tL.isSome && (t0 == healEpoch tL)) = true then pure none
            else if pl = true then
              let kk := cka.receive γ0 Tn
              let p := prng.up σ0 kk.2
              pure (some (some (kk.1, p.1, (Sum.inl (fs.initReceiver p.2) : RS ⊕ ℕ))))
            else do
              let kk := cka.receive γ0 Tn
              let _ ← lookupMultiDFBucketF t0 kk.2
              let s1 ← get
              let (sIdx, s2) := regSessMultiDFBucket L tL t0 kk.2 s1
              set s2
              pure (some (some (kk.1, (prng.up σ0 kk.2).1, (Sum.inr sIdx : RS ⊕ ℕ))))
          else pure (some none) :
          HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) _).run h) := by
    rw [eval_ite]
    have hCond1 : (Expr.and (.not (.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := OO))))))
        (validGuessBucketParPaperE Δbucket tL par (.fst (.snd .v0)))).eval ρ₁ =
        (!(decide (qep + 1 < t0)) && inStage2BucketGen Δbucket tL par t0) := by
      rw [and_eval, validGuessBucketParPaperE_eval]; rfl
    rw [hCond1]
    by_cases hc1 : (!(decide (qep + 1 < t0)) && inStage2BucketGen Δbucket tL par t0) = true
    · simp only [hc1, ↓reduceIte]
      rw [eval_ite]
      have hCond2 : (Expr.and (.bool tL.isSome)
          (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat (healEpoch tL)))).eval ρ₁ =
          (tL.isSome && (t0 == healEpoch tL)) := by
        by_cases htH : t0 = healEpoch tL <;> simp [ρ₁, htH, Expr.eval, Expr.v0]
      rw [hCond2]
      by_cases hc2 : (tL.isSome && (t0 == healEpoch tL)) = true
      · simp [hc2, ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        rw [eval_ite]
        have hCond3 : (Expr.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := OO))))))).eval ρ₁ = pl := rfl
        rw [hCond3]
        by_cases hc3 : pl = true
        · simp [hc3, ρ₁, StateT.run_pure, Comp.eval, hRecv, hPrngUp, hFsInitR, Prod.map,
            Expr.eval, Expr.v0]
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte]
          have hLk := lookupMultiDFBucketFC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
            (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI)
            heqI hSampK L (.fst .v0) (.fst (.snd .v0))
            (.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0)))))))) ρ₁ h rfl (hHB.1 t0)
          have hKk2 : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0)))))))).eval ρ₁ =
              (cka.receive γ0 Tn).2 := by
            simp [ρ₁, hRecv, Expr.eval, Expr.v0]
          have ht1 : (Expr.fst (.snd (Expr.v0 (O := OO)))).eval ρ₁ = t0 := rfl
          rw [hKk2, ht1] at hLk
          rw [eval_bind, hLk.1, StateT.run_bind, bind_map_left, map_bind]
          refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨k', h₁⟩ hmemLk => ?_
          have ⟨_, hSes₁, _⟩ := hLk.2 (k', h₁) hmemLk
          have hSesL₁ : (h₁.sessions t0).length ≤ L := hSes₁ ▸ hHB.2.1 t0
          set ρ₂ := Env.cons (t := .prod (.base CKASort.k) mbHsTy) (k', hsMBEnc h₁) ρ₁
          have hReg := (regSessMultiDFBucketE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
            (lam := lam) (defaultE := defaultE) heqI L tL (.snd .v0) (.fst (.snd .v1))
            (.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1)))))))) ρ₂ h₁ rfl hSesL₁).1
          have hKk2' : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1)))))))).eval ρ₂ =
              (cka.receive γ0 Tn).2 := by
            simp [ρ₂, ρ₁, hRecv, Expr.eval, Expr.v1]
          have ht2 : (Expr.fst (.snd (Expr.v1 (O := OO)))).eval ρ₂ = t0 := rfl
          rw [hKk2', ht2] at hReg
          simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
            pure_bind, map_pure, Prod.map, id_eq]
          change (Comp.ret _).eval ρ₂ = _
          set p := regSessMultiDFBucket L tL t0 (cka.receive γ0 Tn).2 h₁
          have hRegFst : (Expr.fst (regSessMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              L tL (.snd .v0) (.fst (.snd .v1))
              (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1)))))))))).eval ρ₂ = p.1 := by
            rw [fst_eval, hReg]
          have hRegSnd : (Expr.snd (regSessMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              L tL (.snd .v0) (.fst (.snd .v1))
              (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1)))))))))).eval ρ₂ = hsMBEnc p.2 := by
            rw [snd_eval, hReg]
          rw [eval_ret, pair_eval, some_eval, some_eval, pair_eval, pair_eval, inr_eval,
            hRegFst, hRegSnd]
          simp [ρ₂, ρ₁, hRecv, hPrngUp, Expr.eval, Expr.v1]
    · simp [hc1, ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hcache : h.cache t0 with _ | ⟨Tc, σc, kVal, optIdx⟩
  · have hHonNone :
        (Expr.caseOpt (O := OO) (.tget (fsMultiDFBucketHsCache (.fst .v0)) (.fst (.snd .v0))) .none
          (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.fst (.snd (.snd (.snd (.snd .v1)))))))
            (.some (.snd .v0))
            .none)).eval ρ₁ = none := by
      simp [ρ₁, hcache, fsMultiDFBucketHsCache, fsMultiDFBucketHsEnc, Expr.eval, Expr.v0]
    rw [eval_caseOpt_none hHonNone]
    exact hNoneBranch
  · by_cases hEq : Tc = Tn
    · have hHonSome :
          (Expr.caseOpt (O := OO) (.tget (fsMultiDFBucketHsCache (.fst .v0)) (.fst (.snd .v0))) .none
            (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.fst (.snd (.snd (.snd (.snd .v1)))))))
              (.some (.snd .v0))
              .none)).eval ρ₁ = some (σc, kVal, optIdx) := by
        simp [ρ₁, hcache, hEq, heqT, fsMultiDFBucketHsCache, fsMultiDFBucketHsEnc,
          Expr.eval, Expr.v0, Expr.v1]
      rw [eval_caseOpt_some hHonSome, eval_ret]
      simp only [hEq, ↓reduceIte, StateT.run_pure]
      cases optIdx <;>
        simp [ρ₁, hRecv, hFsInitR, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · have hHonNone :
          (Expr.caseOpt (O := OO) (.tget (fsMultiDFBucketHsCache (.fst .v0)) (.fst (.snd .v0))) .none
            (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.fst (.snd (.snd (.snd (.snd .v1)))))))
              (.some (.snd .v0))
              .none)).eval ρ₁ = none := by
        simp [ρ₁, hcache, hEq, heqT, fsMultiDFBucketHsCache, fsMultiDFBucketHsEnc,
          Expr.eval, Expr.v0, Expr.v1]
      rw [eval_caseOpt_none hHonNone]
      simp only [hEq, ↓reduceIte]
      exact hNoneBranch

private def liftFSMultiDFBucketRaw (sIdx : ℕ) {α : Type}
    (x : FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    TComp (FSMultiSpec SS RS T M E) α :=
  simulateQ (fun
    | .inl n => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n)
    | .inr q => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inr ⟨sIdx, q⟩)) x

private theorem liftFSMultiDFBucket_eq (sIdx : ℕ) {α : Type}
    (x : FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    liftFSMultiDFBucket (T := T) (Sig := RSt) (K := K) (I := I) sIdx x =
      StateT.lift (liftFSMultiDFBucketRaw sIdx x) := rfl

private theorem query_fsMultiDFB_tr_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat (.prod hdrTy (.base .msg)))) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.tr arg).eval ρ =
      liftFSMultiDFBucketRaw (arg.eval ρ).1
        (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS)
          (arg.eval ρ).2.1 (arg.eval ρ).2.2) := by
  simp [Comp.eval, fsaeadMultiHeaderAdIface, liftFSMultiDFBucketRaw, FSAEAD.transmitQuery]

private theorem query_fsMultiDFB_ch_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat (.prod hdrTy (.prod (.base .msg) (.base .msg))))) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.ch arg).eval ρ =
      liftFSMultiDFBucketRaw (arg.eval ρ).1
        (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
          (arg.eval ρ).2.1 (arg.eval ρ).2.2.1 (arg.eval ρ).2.2.2) := by
  simp [Comp.eval, fsaeadMultiHeaderAdIface, liftFSMultiDFBucketRaw, FSAEAD.challengeQuery]

private theorem query_fsMultiDFB_cs_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat .unit)) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.cs arg).eval ρ =
      liftFSMultiDFBucketRaw (arg.eval ρ).1
        (FSAEAD.corruptSenderQuery (SenderState := SS) (ReceiverState := RS)
          (AssocData := Header T) (Message := M) (Ciphertext := E)) := by
  simp [Comp.eval, fsaeadMultiHeaderAdIface, liftFSMultiDFBucketRaw, FSAEAD.corruptSenderQuery]

private theorem query_fsMultiDFB_dl_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat hdrCtTy)) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.dl arg).eval ρ =
      Option.map fsHdrRrEnc <$>
        liftFSMultiDFBucketRaw (arg.eval ρ).1
          (FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS)
            (arg.eval ρ).2.1 (arg.eval ρ).2.2) := by
  simp [Comp.eval, fsaeadMultiHeaderAdIface, liftFSMultiDFBucketRaw, FSAEAD.deliverQuery]

private theorem query_fsMultiDFB_ij_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat hdrCtTy)) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.ij arg).eval ρ =
      Option.map fsHdrRrEnc <$>
        liftFSMultiDFBucketRaw (arg.eval ρ).1
          (FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS)
            (arg.eval ρ).2.1 (arg.eval ρ).2.2) := by
  simp [Comp.eval, fsaeadMultiHeaderAdIface, liftFSMultiDFBucketRaw, FSAEAD.injectQuery]

private theorem fsMultiDFBucketFsSendC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hFsSend : fsSend = fs.send)
    (L Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.sum (.base .ss) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) (ρ : Env Γ')
    (h : FSMultiDFBucketState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (hh : hE.eval ρ = hsMBEnc h)
    (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx) (hp : pE.eval ρ = partyEnc P) :
    (fsMultiDFBucketFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).eval ρ =
      Prod.map id hsMBEnc <$>
        ((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).fsSend ctx P
          (tE.eval ρ) (ssvE.eval ρ) (hdrE.eval ρ) (mE.eval ρ) (pairE.eval ρ)).run h := by
  unfold fsMultiDFBucketFsSendC hooksFSMultiDFBucketPaper
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
    have hBk0 : (fsMultiDFBucketHsGetBookAt (O := OO) (.fst .v1) .v0).eval ρ₂ =
        (bk.sCorr, bk.fsCount, bk.fsTrans) :=
      fsMultiDFBucketHsGetBookAt_eval (.fst .v1) .v0 ρ₂ h rfl
    have hCond : (Expr.and (.not (cSafeChE (2 + Δcka) (.fst (.snd (Expr.v1 (O := OO))))
        (.fst (.snd (.snd .v1))))) (.not (.fst (fsMultiDFBucketHsGetBookAt (.fst .v1) .v0)))).eval ρ₂ =
        (!(ctx.safeCh (2 + Δcka) P) && !bk.sCorr) := by
      rw [and_eval, not_eval, not_eval, hSafe, fst_eval, hBk0]
    have hSendTrue : ∀ (h₁ : FSMultiDFBucketState T RSt K I E),
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
              (.ret (.pair (.some (.pair (Expr.inr (O := OO) (t := .base CKASort.ss) .v3) .v0))
                (fsMultiDFBucketHsSetBookAt (.snd .v2) .v3
                  (.pair (.fst (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3))
                    (.pair (.add (.fst (.snd (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                      (.cons (.pair (.add (.fst (.snd (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                        (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) .v0))
                        (.snd (.snd (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3)))))))))))).eval
          (Env.cons (t := .prod .bool mbHsTy) (true, hsMBEnc h₁) ρ₂) =
        Prod.map id hsMBEnc <$>
          ((do
              let e? ← match pair with
                | some (m₀, m₁) =>
                  liftFSMultiDFBucket sIdx (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
                    hdr m₀ m₁)
                | none =>
                  liftFSMultiDFBucket sIdx (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS)
                    hdr m)
              match e? with
              | none => return none
              | some e =>
                modify fun (s : FSMultiDFBucketState T RSt K I E) =>
                  let b := (s.book sIdx).getD {}
                  let cnt' := b.fsCount + 1
                  let b' : FSMultiBook T E := { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
                  { s with book := Function.update s.book sIdx (some b') }
                return some (.inr sIdx, e) :
            HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)
              (Option ((SS ⊕ ℕ) × E))).run h₁) := by
      intro h₁
      set ρ₃ := Env.cons (t := .prod .bool mbHsTy) (true, hsMBEnc h₁) ρ₂
      rw [eval_ite]
      have hNotOk : (Expr.not (.fst (Expr.v0 (O := OO)))).eval ρ₃ = false := rfl
      rw [hNotOk]
      simp only [Bool.false_eq_true, ↓reduceIte, eval_bind]
      rcases pair with _ | ⟨m₀, m₁⟩
      · rw [eval_caseOpt_none rfl, query_fsMultiDFB_tr_eval]
        simp only [liftFSMultiDFBucket_eq, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          map_bind]
        refine bind_congr fun e? => ?_
        rcases e? with _ | ct
        · rw [eval_caseOpt_none rfl, eval_ret]
          simp [ρ₃, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
        · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
          set ρ₄ := Env.cons (t := .base CKASort.ct) ct
            (Env.cons (t := .opt (.base CKASort.ct)) (some ct) ρ₃)
          have hBk1 := fsMultiDFBucketHsGetBookAt_eval (O' := OO) (.snd .v2) .v3 ρ₄ h₁ rfl
          have hIdx4 : (Expr.v3 (O := OO)).eval ρ₄ = sIdx := rfl
          rw [hIdx4] at hBk1
          have hSet := fsMultiDFBucketHsSetBookAt_eval (O' := OO) (.snd .v2) .v3
            (.pair (.fst (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3))
              (.pair (.add (.fst (.snd (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                (.cons (.pair (.add (.fst (.snd (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                  (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) .v0))
                  (.snd (.snd (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3)))))) ρ₄ h₁ rfl
            (sc := ((h₁.book sIdx).getD {}).sCorr)
            (cnt := ((h₁.book sIdx).getD {}).fsCount + 1)
            (tr := (((h₁.book sIdx).getD {}).fsCount + 1, hdr, ct) :: ((h₁.book sIdx).getD {}).fsTrans)
            (by
              rw [pair_eval, pair_eval]
              refine Prod.ext (by rw [fst_eval, hBk1]) (Prod.ext ?_ ?_)
              · change ((fsMultiDFBucketHsGetBookAt (O := OO) (.snd .v2) .v3).eval ρ₄).2.1 + 1 = _
                rw [hBk1]
              · change (((fsMultiDFBucketHsGetBookAt (O := OO) (.snd .v2) .v3).eval ρ₄).2.1 + 1, hdr, ct) ::
                    ((fsMultiDFBucketHsGetBookAt (O := OO) (.snd .v2) .v3).eval ρ₄).2.2 = _
                rw [hBk1])
          rw [hSet]
          simp [ρ₄, ρ₃, ρ₂, StateT.run_modify, Prod.map, Expr.eval, Expr.v0, Expr.v3]
      · rw [eval_caseOpt_some rfl, query_fsMultiDFB_ch_eval]
        simp only [liftFSMultiDFBucket_eq, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          map_bind]
        refine bind_congr fun e? => ?_
        rcases e? with _ | ct
        · rw [eval_caseOpt_none rfl, eval_ret]
          simp [ρ₃, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
        · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
          set ρ₄ := Env.cons (t := .base CKASort.ct) ct
            (Env.cons (t := .opt (.base CKASort.ct)) (some ct) ρ₃)
          have hBk1 := fsMultiDFBucketHsGetBookAt_eval (O' := OO) (.snd .v2) .v3 ρ₄ h₁ rfl
          have hIdx4 : (Expr.v3 (O := OO)).eval ρ₄ = sIdx := rfl
          rw [hIdx4] at hBk1
          have hSet := fsMultiDFBucketHsSetBookAt_eval (O' := OO) (.snd .v2) .v3
            (.pair (.fst (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3))
              (.pair (.add (.fst (.snd (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                (.cons (.pair (.add (.fst (.snd (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                  (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) .v0))
                  (.snd (.snd (fsMultiDFBucketHsGetBookAt (.snd .v2) .v3)))))) ρ₄ h₁ rfl
            (sc := ((h₁.book sIdx).getD {}).sCorr)
            (cnt := ((h₁.book sIdx).getD {}).fsCount + 1)
            (tr := (((h₁.book sIdx).getD {}).fsCount + 1, hdr, ct) :: ((h₁.book sIdx).getD {}).fsTrans)
            (by
              rw [pair_eval, pair_eval]
              refine Prod.ext (by rw [fst_eval, hBk1]) (Prod.ext ?_ ?_)
              · change ((fsMultiDFBucketHsGetBookAt (O := OO) (.snd .v2) .v3).eval ρ₄).2.1 + 1 = _
                rw [hBk1]
              · change (((fsMultiDFBucketHsGetBookAt (O := OO) (.snd .v2) .v3).eval ρ₄).2.1 + 1, hdr, ct) ::
                    ((fsMultiDFBucketHsGetBookAt (O := OO) (.snd .v2) .v3).eval ρ₄).2.2 = _
                rw [hBk1])
          rw [hSet]
          simp [ρ₄, ρ₃, ρ₂, StateT.run_modify, Prod.map, Expr.eval, Expr.v0, Expr.v3]
    rw [eval_bind, eval_ite, hCond]
    by_cases hc : (!(ctx.safeCh (2 + Δcka) P) && !bk.sCorr) = true
    · simp only [hc, ↓reduceIte]
      rw [eval_bind, query_fsMultiDFB_cs_eval, liftFSMultiDFBucket_eq]
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
      refine bind_congr fun cs? => ?_
      rcases cs? with _ | ss'
      · rw [eval_caseOpt_none rfl, eval_ret, pure_bind]
        simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
      · rw [eval_caseOpt_some rfl, eval_ret, pure_bind]
        simp only [StateT.run_bind, StateT.run_modify, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        set ρ_cs := Env.cons (t := .base CKASort.ss) ss'
          (Env.cons (t := .opt (.base CKASort.ss)) (some ss') ρ₂)
        have hBkCs := fsMultiDFBucketHsGetBookAt_eval (O' := OO) (.fst .v3) .v2 ρ_cs h rfl
        have hIdxCs : (Expr.v2 (O := OO)).eval ρ_cs = sIdx := rfl
        rw [hIdxCs] at hBkCs
        have hSetCs := fsMultiDFBucketHsSetBookAt_eval (O' := OO) (.fst .v3) .v2
          (.pair (.bool true)
            (.pair (.fst (.snd (fsMultiDFBucketHsGetBookAt (.fst .v3) .v2)))
              (.snd (.snd (fsMultiDFBucketHsGetBookAt (.fst .v3) .v2))))) ρ_cs h rfl
          (sc := true) (cnt := bk.fsCount) (tr := bk.fsTrans)
          (by rw [pair_eval, pair_eval, fst_eval, snd_eval, snd_eval, snd_eval, hBkCs]; rfl)
        let bk' : FSMultiBook T E := { bk with sCorr := true }
        let h' : FSMultiDFBucketState T RSt K I E :=
          { h with book := Function.update h.book sIdx (some bk') }
        have hPairCs : (Expr.pair (O := OO) (.bool true)
            (fsMultiDFBucketHsSetBookAt (.fst .v3) .v2
              (.pair (.bool true)
                (.pair (.fst (.snd (fsMultiDFBucketHsGetBookAt (.fst .v3) .v2)))
                  (.snd (.snd (fsMultiDFBucketHsGetBookAt (.fst .v3) .v2))))))).eval ρ_cs =
            (true, hsMBEnc h') := by
          rw [pair_eval, hSetCs]; rfl
        rw [hPairCs]
        exact hSendTrue h'
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, eval_ret, pure_bind]
      have hPair0 : (Expr.pair (O := OO) (.bool true) (.fst .v1)).eval ρ₂ =
          (true, hsMBEnc h) := rfl
      rw [hPair0]
      exact hSendTrue h

private theorem fsMultiDFBucketFsRecvC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (heqT : eqT = (· == ·))
    (heqE : eqE = (· == ·))
    (L B Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.sum (.base .rs) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ')
    (h : FSMultiDFBucketState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (rec_ : Option (Record M (Header T × E)))
    (hHB : FSMultiDFBucketHBoundedPost L h)
    (hh : hE.eval ρ = hsMBEnc h) (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx)
    (hrec : recE.eval ρ = rec_.map cRecEnc) :
    (fsMultiDFBucketPaperFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B la Δcka hE ctxE pE tE rsvE hdrE eE recE).eval ρ =
      Prod.map id hsMBEnc <$>
        ((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).fsRecv ctx P
          (tE.eval ρ) (rsvE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) rec_).run h := by
  have hCaseOpt : ∀ {Γ0 a b} (e0 : Expr OO Γ0 (.opt a))
      (n0 : Expr OO Γ0 b) (s0 : Expr OO (a :: Γ0) b) (ρ0 : Env Γ0),
      (Expr.caseOpt e0 n0 s0).eval ρ0 =
        match e0.eval ρ0 with
        | none => n0.eval ρ0
        | some x => s0.eval (Env.cons x ρ0) := by
    intro _ _ _ e0 _ _ ρ0
    conv_lhs => unfold Expr.eval
    cases e0.eval ρ0 <;> rfl
  have hRunIfLift : ∀ {α β : Type} (sIdx : ℕ) (c : Bool)
      (q1 q2 : FSAEAD.AdversaryComp SS RS (Header T) M E α)
      (k : α → HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) β)
      (s0 : FSMultiDFBucketState T RSt K I E),
      Prod.map id hsMBEnc <$>
        (if c then do let res ← liftFSMultiDFBucket sIdx q1; k res
         else do let res ← liftFSMultiDFBucket sIdx q2; k res).run s0 =
      ((if c then liftFSMultiDFBucketRaw sIdx q1 else liftFSMultiDFBucketRaw sIdx q2) >>=
        fun res => Prod.map id hsMBEnc <$> (k res).run s0) := by
    intro α β sIdx c q1 q2 k s0
    cases c <;>
      simp [liftFSMultiDFBucket_eq, StateT.run_bind, StateT.run_lift, map_bind]
  unfold fsMultiDFBucketPaperFsRecvC hooksFSMultiDFBucketPaper
  dsimp only
  set t0 : ℕ := tE.eval ρ
  set rsv : RS ⊕ ℕ := rsvE.eval ρ
  set hdr : Header T := hdrE.eval ρ
  set e : E := eE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair tE (.pair rsvE (.pair hdrE (.pair eE recE)))))).eval ρ =
      (hsMBEnc h, cGsEnc vpMEnc ctx, t0, rsv, hdr, e, rec_.map cRecEnc) := by
    simp [Expr.eval, hh, hctx, hrec, t0, rsv, hdr, e]
  set ρ₁ := Env.cons
    (t := .prod mbHsTy (.prod (cGsTy mVpTy) (.prod .nat (.prod (.sum (.base CKASort.rs) .nat)
      (.prod hdrTy (.prod (.base CKASort.ct) (.opt cRecTy)))))))
    (hsMBEnc h, cGsEnc vpMEnc ctx, t0, rsv, hdr, e, rec_.map cRecEnc) ρ
  rw [eval_bind_ret, h0]; clear h0 hh hctx hrec
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
      simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
  · rw [eval_caseSum_inr rfl]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    set ρ₂ := Env.cons (t := .nat) sIdx ρ₁
    set bk := (h.book sIdx).getD {}
    have hBkL : bk.fsTrans.length ≤ L := by
      dsimp only [bk]
      rcases hbk : h.book sIdx with _ | b
      · simp
      · exact hHB sIdx b hbk
    have hBk0 : (fsMultiDFBucketHsGetBookAt (O := OO) (.fst .v1) .v0).eval ρ₂ =
        (bk.sCorr, bk.fsCount, bk.fsTrans) :=
      fsMultiDFBucketHsGetBookAt_eval (.fst .v1) .v0 ρ₂ h rfl
    set matched := bk.fsTrans.find? (fun x => x.2 == (hdr, e))
    have hFind0 : (fsTransFindE L (.snd (.snd (fsMultiDFBucketHsGetBookAt (O := OO) (.fst .v1) .v0)))
        (.pair (.fst (.snd (.snd (.snd (.snd .v1)))))
          (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))))).eval ρ₂ = matched := by
      rw [fsTransFindE_eval heqT heqE L _ _ ρ₂ (by simp [snd_eval, hBk0, hBkL])]
      rw [snd_eval, snd_eval, hBk0]
      simp [ρ₂, ρ₁, matched, Expr.eval, Expr.v1]
    have hTL0 : (cGsTL (O' := OO) (.fst (.snd .v1))).eval ρ₂ = ctx.tL := rfl
    have hT0 : (Expr.fst (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ = t0 := rfl
    have hCond : (Expr.and (O := OO)
        (.not (_root_.CryptoGames.SM.healedByE (cGsTL (.fst (.snd .v1))) (2 + Δcka)
          (.fst (.snd (.snd .v1)))))
        (.not (.fst (fsMultiDFBucketHsGetBookAt (.fst .v1) .v0)))).eval ρ₂ =
        (!SM.healedBy ctx.tL (2 + Δcka) t0 && !bk.sCorr) := by
      rw [and_eval, not_eval, not_eval, _root_.CryptoGames.SM.healedByE_eval, hTL0, hT0,
        fst_eval, hBk0]
    generalize hcRest : Comp.ite (O := OO) (I := IIM) (.not (.fst .v0))
      (.ret (.pair .none (.snd .v0))) _ = cRest
    let mTail : HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)
        (Option (Option ((RS ⊕ ℕ) × ℕ × M))) := do
      let res ← if matched.isSome then
          liftFSMultiDFBucket sIdx
            (FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
        else
          liftFSMultiDFBucket sIdx
            (FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
      match res with
      | none => return none
      | some .rejected => return some none
      | some (.accepted i mo') =>
        let s1 ← get
        let bk1 := (s1.book sIdx).getD {}
        if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
          modify fun (s : FSMultiDFBucketState T RSt K I E) => { s with lfWin := true }
          return none
        else
          let drop := (matched.map (·.1)).getD i
          modify fun (s : FSMultiDFBucketState T RSt K I E) =>
            let b := (s.book sIdx).getD {}
            let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
            { s with book := Function.update s.book sIdx (some b') }
          match mo', rec_ with
          | some m, _ => return some (some ((.inr sIdx : RS ⊕ ℕ), i, m))
          | none, some r => return some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg))
          | none, none => return none
    change _ = Prod.map id hsMBEnc <$>
      ((do
        let ok ← if matched.isNone && !(SM.healedBy ctx.tL (2 + Δcka) t0) && !bk.sCorr then do
            match ← liftFSMultiDFBucket sIdx (FSAEAD.corruptSenderQuery (ReceiverState := RS)
                (AssocData := Header T) (Message := M) (Ciphertext := E)) with
            | none => pure false
            | some _ =>
              modify fun (s : FSMultiDFBucketState T RSt K I E) =>
                let b := (s.book sIdx).getD {}
                { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
              pure true
          else pure true
        if !ok then return none
        mTail :
        HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)
          (Option (Option ((RS ⊕ ℕ) × ℕ × M)))).run h)
    generalize hmTail : mTail = mTailG
    have hRecvTrue : ∀ (h₁ : FSMultiDFBucketState T RSt K I E),
        ((h₁.book sIdx).getD {}).fsTrans = bk.fsTrans →
        cRest.eval (Env.cons (t := .prod .bool mbHsTy) (true, hsMBEnc h₁) ρ₂) =
          Prod.map id hsMBEnc <$> mTailG.run h₁ := by
      intro h₁ hTr₁
      rw [← hmTail]
      dsimp only [mTail]
      set ρ₃ := Env.cons (t := .prod .bool mbHsTy) (true, hsMBEnc h₁) ρ₂
      rw [← hcRest, eval_ite]
      have hNotOk : (Expr.not (.fst (Expr.v0 (O := OO)))).eval ρ₃ = false := rfl
      rw [hNotOk]
      simp only [Bool.false_eq_true, ↓reduceIte, eval_bind]
      have hBk0_3 : (fsMultiDFBucketHsGetBookAt (O := OO) (.fst .v2) .v1).eval ρ₃ =
          (bk.sCorr, bk.fsCount, bk.fsTrans) :=
        fsMultiDFBucketHsGetBookAt_eval (.fst .v2) .v1 ρ₃ h rfl
      have hFind3 : (fsTransFindE L (.snd (.snd (fsMultiDFBucketHsGetBookAt (O := OO) (.fst .v2) .v1)))
          (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
            (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))).eval ρ₃ = matched := by
        rw [fsTransFindE_eval heqT heqE L _ _ ρ₃ (by rw [snd_eval, snd_eval, hBk0_3]; exact hBkL),
          snd_eval, snd_eval, hBk0_3]
        rfl
      have hQ3 :
          (Comp.caseOpt (O := OO) (I := IIM)
            (fsTransFindE L (.snd (.snd (fsMultiDFBucketHsGetBookAt (.fst .v2) .v1)))
              (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))))
            (@Comp.query _ _ _ OO IIM _ FSHdrTag.ij
              (.pair .v1
                (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                  (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))))
            (@Comp.query _ _ _ OO IIM _ FSHdrTag.dl
              (.pair .v2
                (.pair (.fst (.snd (.snd (.snd (.snd .v3)))))
                  (.fst (.snd (.snd (.snd (.snd (.snd .v3)))))))))).eval ρ₃ =
          Option.map fsHdrRrEnc <$>
            (if matched.isSome = true then
              liftFSMultiDFBucketRaw sIdx
                (FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
             else
              liftFSMultiDFBucketRaw sIdx
                (FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)) := by
        rcases hM : matched with _ | mrec
        · rw [eval_caseOpt_none (hFind3.trans hM), query_fsMultiDFB_ij_eval]; rfl
        · rw [eval_caseOpt_some (hFind3.trans hM), query_fsMultiDFB_dl_eval]; rfl
      rw [hQ3, bind_map_left, hRunIfLift]
      refine bind_congr fun res => ?_
      rcases res with _ | (_ | ⟨msgIdx, mo'⟩)
      · dsimp only [Option.map]
        rw [eval_caseOpt_none rfl, eval_ret, StateT.run_pure, map_pure]
        rfl
      · dsimp only [Option.map, fsHdrRrEnc]
        rw [eval_caseOpt_some rfl, eval_caseSum_inl rfl, eval_ret, StateT.run_pure, map_pure]
        rfl
      · dsimp only [Option.map, fsHdrRrEnc]
        rw [eval_caseOpt_some rfl, eval_caseSum_inr rfl, eval_ite]
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        set bk1 := (h₁.book sIdx).getD {}
        have hBk1L : bk1.fsTrans.length ≤ L := by
          dsimp only [bk1]; rw [hTr₁]; exact hBkL
        set ρ₄ := Env.cons (t := .prod .nat (.opt (.base CKASort.msg))) (msgIdx, mo')
          (Env.cons (t := fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E) (.inr (msgIdx, mo'))
            (Env.cons (t := .opt (fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E))
              (some (.inr (msgIdx, mo'))) ρ₃))
        have hBk1_4 : (fsMultiDFBucketHsGetBookAt (O := OO) (.snd .v3) .v4).eval ρ₄ =
            (bk1.sCorr, bk1.fsCount, bk1.fsTrans) :=
          fsMultiDFBucketHsGetBookAt_eval (.snd .v3) .v4 ρ₄ h₁ rfl
        have hBk0_4 : (fsMultiDFBucketHsGetBookAt (O := OO) (.fst .v5) .v4).eval ρ₄ =
            (bk.sCorr, bk.fsCount, bk.fsTrans) :=
          fsMultiDFBucketHsGetBookAt_eval (.fst .v5) .v4 ρ₄ h rfl
        have hFind4 : (fsTransFindE L (.snd (.snd (fsMultiDFBucketHsGetBookAt (O := OO) (.fst .v5) .v4)))
            (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
              (.fst (.snd (.snd (.snd (.snd (.snd .v5)))))))).eval ρ₄ = matched := by
          rw [fsTransFindE_eval heqT heqE L _ _ ρ₄ (by rw [snd_eval, snd_eval, hBk0_4]; exact hBkL),
            snd_eval, snd_eval, hBk0_4]
          rfl
        have hLfCond :
            (Expr.and (O := OO) (.bool la)
              (.caseOpt
                (fsTransFindE L (.snd (.snd (fsMultiDFBucketHsGetBookAt (.fst .v5) .v4)))
                  (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
                    (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
                (.and (.not (.fst (fsMultiDFBucketHsGetBookAt (.snd .v3) .v4)))
                  (.lt (.fst (.snd (fsMultiDFBucketHsGetBookAt (.snd .v3) .v4))) (.fst .v0)))
                (.bool false))).eval ρ₄ =
            (la && matched.isNone && !bk1.sCorr && decide (bk1.fsCount < msgIdx)) := by
          rw [and_eval, hCaseOpt, hFind4]
          rcases matched with _ | _
          · have hMsg0 : (Expr.fst (Expr.v0 (O := OO))).eval ρ₄ = msgIdx := rfl
            have hLt4 : (Expr.lt (O := OO) (.fst (.snd (fsMultiDFBucketHsGetBookAt (.snd .v3) .v4)))
                (.fst .v0)).eval ρ₄ = decide (bk1.fsCount < msgIdx) := by
              change decide (((fsMultiDFBucketHsGetBookAt (O := OO) (.snd .v3) .v4).eval ρ₄).2.1 <
                (Expr.fst (Expr.v0 (O := OO))).eval ρ₄) = _
              rw [hBk1_4, hMsg0]
            rw [and_eval, not_eval, fst_eval, hBk1_4, hLt4]
            cases la <;> cases bk1.sCorr <;> rfl
          · cases la <;> rfl
        rw [hLfCond]
        by_cases hLf : (la && matched.isNone && !bk1.sCorr && decide (bk1.fsCount < msgIdx)) = true
        · simp only [hLf, ↓reduceIte, eval_ret, pair_eval, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, pure_bind, map_pure, Prod.map]
          rw [fsMultiDFBucketHsSetLfWin_eval (.snd .v3) (.bool true) ρ₄ h₁ rfl]
          rfl
        · simp only [hLf, Bool.false_eq_true, ↓reduceIte, eval_ret, pair_eval,
            StateT.run_bind, StateT.run_modify, pure_bind]
          have hDrop4 : (Expr.caseOpt (O := OO)
              (fsTransFindE L (.snd (.snd (fsMultiDFBucketHsGetBookAt (.fst .v5) .v4)))
                (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
                  (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
              (.fst .v0) (.fst .v0)).eval ρ₄ = (matched.map (·.1)).getD msgIdx := by
            rw [hCaseOpt, hFind4]
            rcases matched with _ | _ <;> rfl
          have hFlt4 := fsTransFilterE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            L (.snd (.snd (fsMultiDFBucketHsGetBookAt (.snd .v3) .v4)))
            (.caseOpt (fsTransFindE L (.snd (.snd (fsMultiDFBucketHsGetBookAt (.fst .v5) .v4)))
                (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
                  (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
              (.fst .v0) (.fst .v0)) ρ₄ (by rw [snd_eval, snd_eval, hBk1_4]; exact hBk1L)
          rw [hDrop4] at hFlt4
          have hTrEq4 : (Expr.snd (.snd (fsMultiDFBucketHsGetBookAt (O := OO) (.snd .v3) .v4))).eval ρ₄ =
              bk1.fsTrans := by rw [snd_eval, snd_eval, hBk1_4]
          rw [hTrEq4] at hFlt4
          have hH4 := fsMultiDFBucketHsSetBookAt_eval (O' := OO) (.snd .v3) .v4
            (.pair (.fst (fsMultiDFBucketHsGetBookAt (.snd .v3) .v4))
              (.pair (.fst (.snd (fsMultiDFBucketHsGetBookAt (.snd .v3) .v4)))
                (fsTransFilterE L (.snd (.snd (fsMultiDFBucketHsGetBookAt (.snd .v3) .v4)))
                  (.caseOpt (fsTransFindE L (.snd (.snd (fsMultiDFBucketHsGetBookAt (.fst .v5) .v4)))
                      (.pair (.fst (.snd (.snd (.snd (.snd .v5)))))
                        (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
                    (.fst .v0) (.fst .v0))))) ρ₄ h₁ rfl
            (sc := bk1.sCorr) (cnt := bk1.fsCount)
            (tr := bk1.fsTrans.filter (·.1 != (matched.map (·.1)).getD msgIdx))
            (by rw [pair_eval, fst_eval, pair_eval, fst_eval, snd_eval, hFlt4, hBk1_4])
          have hIdx4 : (Expr.v4 (O := OO)).eval ρ₄ = sIdx := rfl
          rw [hIdx4] at hH4
          have hOut4 :
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
            · rcases rec_ with _ | r <;> rfl
            · rfl
          rw [hOut4, hH4]
          rcases mo' with _ | m
          · rcases rec_ with _ | r <;> (rw [StateT.run_pure, map_pure]; rfl)
          · rw [StateT.run_pure, map_pure]; rfl
    rw [eval_bind]
    obtain hM | ⟨mrec, hM⟩ : matched = none ∨ ∃ mrec, matched = some mrec := by
      cases matched <;> simp
    · have hIsNone : matched.isNone = true := by rw [hM]; rfl
      rw [eval_caseOpt_none (hFind0.trans hM), eval_ite, hCond]
      simp only [hIsNone, Bool.true_and]
      by_cases hc : (!SM.healedBy ctx.tL (2 + Δcka) t0 && !bk.sCorr) = true
      · simp only [hc, ↓reduceIte, eval_bind, query_fsMultiDFB_cs_eval, liftFSMultiDFBucket_eq,
          StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind,
          Expr.eval, Expr.v0]
        refine bind_congr fun cs? => ?_
        rcases cs? with _ | ss'
        · rw [eval_caseOpt_none rfl, eval_ret, pure_bind, ← hcRest, eval_ite]
          change (Comp.ret (O := OO) (I := IIM) (.pair .none (.snd .v0))).eval
            (Env.cons (t := .prod .bool mbHsTy) (false, hsMBEnc h) ρ₂) = _
          rw [eval_ret]
          simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, map_pure]
          rfl
        · rw [eval_caseOpt_some rfl, eval_ret, pure_bind]
          simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          set ρ_cs := Env.cons (t := .base CKASort.ss) ss'
            (Env.cons (t := .opt (.base CKASort.ss)) (some ss') ρ₂)
          have hBkCs := fsMultiDFBucketHsGetBookAt_eval (O' := OO) (.fst .v3) .v2 ρ_cs h rfl
          have hIdxCs : (Expr.v2 (O := OO)).eval ρ_cs = sIdx := rfl
          rw [hIdxCs] at hBkCs
          have hSetCs := fsMultiDFBucketHsSetBookAt_eval (O' := OO) (.fst .v3) .v2
            (.pair (.bool true) (.snd (fsMultiDFBucketHsGetBookAt (.fst .v3) .v2))) ρ_cs h rfl
            (sc := true) (cnt := bk.fsCount) (tr := bk.fsTrans)
            (by rw [pair_eval, snd_eval, hBkCs]; rfl)
          let bk' : FSMultiBook T E := { bk with sCorr := true }
          let h' : FSMultiDFBucketState T RSt K I E :=
            { h with book := Function.update h.book sIdx (some bk') }
          have hPairCs : (Expr.pair (O := OO) (.bool true)
              (fsMultiDFBucketHsSetBookAt (.fst .v3) .v2
                (.pair (.bool true) (.snd (fsMultiDFBucketHsGetBookAt (.fst .v3) .v2))))).eval ρ_cs =
              (true, hsMBEnc h') := by
            rw [pair_eval, hSetCs]; rfl
          rw [hPairCs]
          exact hRecvTrue h' (by simp only [h', bk', bk, Function.update_self, Option.getD_some])
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, eval_ret, pure_bind,
          Bool.not_true]
        have hPair0 : (Expr.pair (O := OO) (.bool true) (.fst .v1)).eval ρ₂ =
            (true, hsMBEnc h) := rfl
        rw [hPair0]
        exact hRecvTrue h rfl
    · have hIsNone : matched.isNone = false := by rw [hM]; rfl
      rw [eval_caseOpt_some (hFind0.trans hM), eval_ret, pure_bind]
      simp only [hIsNone, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        pure_bind, Bool.not_true]
      have hPair0 : (Expr.pair (O := OO) (.bool true) (.fst .v2)).eval
          (Env.cons (t := .prod .nat hdrCtTy) mrec ρ₂) = (true, hsMBEnc h) := rfl
      rw [hPair0]
      exact hRecvTrue h rfl

private theorem isExtMultiDFEntryE_eval {Γ'}
    (entryE : Expr OO Γ' (.opt (.sum (.base .rs) .nat))) (ρ : Env Γ') :
    (isExtMultiDFEntryE entryE).eval ρ =
      match entryE.eval ρ with
      | some (.inr _) => true
      | _ => false := by
  unfold isExtMultiDFEntryE
  rcases h1 : entryE.eval ρ with _ | (rs | sIdx) <;>
    simp [h1, Expr.eval, Expr.v0]

private theorem foldr_ite_true_eq_any {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.foldr (fun x acc => if p x then true else acc) false = l.any p
  | [] => rfl
  | a :: l => by
    simp only [List.foldr_cons, List.any_cons, foldr_ite_true_eq_any p l]
    cases p a <;> rfl

private theorem anyExtMultiDFVRE_eval (L : ℕ) {Γ'}
    (vRE : Expr OO Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO Γ' (.list .nat)) (ρ : Env Γ')
    (hRng : rngE.eval ρ = (List.range L).reverse) :
    (anyExtMultiDFVRE L vRE rngE).eval ρ =
      (List.range L).any (fun t =>
        match (vRE.eval ρ) t with
        | some (.inr _) => true
        | _ => false) := by
  unfold anyExtMultiDFVRE
  rw [letE_eval]
  set vR := vRE.eval ρ
  have h0 : (Expr.pair vRE rngE).eval ρ = (vR, (List.range L).reverse) := by
    simp [Expr.eval, vR, hRng]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (.tbl (.opt (.sum (.base CKASort.rs) .nat))) (.list .nat))
    (vR, (List.range L).reverse) ρ
  have hTake : (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = (List.range L).reverse := by
    change ((List.range L).reverse).take L = (List.range L).reverse
    simp
  change List.foldr _ false (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = _
  rw [hTake]
  have hStep :
      (fun (x : ℕ) (acc : Bool) =>
        (Expr.ite (O := OO)
          (isExtMultiDFEntryE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            (.tget (.fst .v2) .v0))
          (.bool true) .v1).eval
          (Env.cons (t := .nat) x (Env.cons (t := .bool) acc ρ₁))) =
      (fun (x : ℕ) (acc : Bool) =>
        if (match vR x with | some (.inr _) => true | _ => false) then true else acc) := by
    funext x acc
    rw [ite_eval, isExtMultiDFEntryE_eval]
    rfl
  rw [hStep, foldr_ite_true_eq_any]
  simp

private theorem unliftMultiDFEntryE_eval {Γ'}
    (entryE : Expr OO Γ' (.opt (.sum (.base .rs) .nat))) (ρ : Env Γ') :
    (unliftMultiDFEntryE entryE).eval ρ =
      match entryE.eval ρ with
      | some (.inl rs) => some rs
      | _ => none := by
  unfold unliftMultiDFEntryE
  rcases h1 : entryE.eval ρ with _ | (rs | sIdx) <;>
    simp [h1, Expr.eval, Expr.v0]

private theorem unliftMultiDFVRE_eval (L : ℕ) {Γ'}
    (vRE : Expr OO Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO Γ' (.list .nat)) (ρ : Env Γ')
    (hRng : rngE.eval ρ = (List.range L).reverse) :
    (unliftMultiDFVRE L vRE rngE).eval ρ =
      fun t =>
        if t < L then
          match (vRE.eval ρ) t with
          | some (.inl rs) => some rs
          | _ => none
        else none := by
  unfold unliftMultiDFVRE
  rw [letE_eval]
  set vR := vRE.eval ρ
  have h0 : (Expr.pair vRE rngE).eval ρ = (vR, (List.range L).reverse) := by
    simp [Expr.eval, vR, hRng]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (.tbl (.opt (.sum (.base CKASort.rs) .nat))) (.list .nat))
    (vR, (List.range L).reverse) ρ
  have hTake : (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = (List.range L).reverse := by
    change ((List.range L).reverse).take L = (List.range L).reverse
    simp
  change List.foldr _ (fun _ => none) (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = _
  rw [hTake]
  have hStep :
      (fun (x : ℕ) (acc : ℕ → Option RS) =>
        (Expr.tset (O := OO) .v1 .v0
          (unliftMultiDFEntryE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
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
    funext x acc
    rw [tset_eval_eq_update, unliftMultiDFEntryE_eval]
    rfl
  rw [hStep]
  funext t
  rw [foldr_update_apply]
  simp [List.mem_reverse, List.mem_range]

private theorem fsMultiDFBucketRevealC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) (ρ : Env Γ')
    (h : FSMultiDFBucketState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (hh : hE.eval ρ = hsMBEnc h) (hvp : vpE.eval ρ = vpMEnc vp) :
    (fsMultiDFBucketRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L la hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) hsMBEnc <$>
        ((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).reveal
          ctx P vp).run h := by
  unfold fsMultiDFBucketRevealC hooksFSMultiDFBucketPaper
  dsimp only
  have h0 : (Expr.pair hE vpE).eval ρ = (hsMBEnc h, vpMEnc vp) := by
    simp [Expr.eval, hh, hvp]
  set ρ₁ := Env.cons (t := .prod mbHsTy mVpTy) (hsMBEnc h, vpMEnc vp) ρ
  rw [eval_bind_ret, h0]
  have hStep2 : ∀ (ssReal : Option SS) (h₁ : FSMultiDFBucketState T RSt K I E),
      (Comp.caseOpt (O := OO) (I := IIM) (.fst .v0)
        (.ret (.pair .none (.snd .v0)))
        (.bind (rangeListC (O' := OO) (I' := IIM) L)
          (.ite (anyExtMultiDFVRE L (vpVR (.snd .v3)) .v0)
            (.ret (.pair .none (.snd .v2)))
            (.ret (.pair
              (.some (realPartyE (.snd .v3) (vpΓ (.snd .v3)) (vpRoot (.snd .v3)) .v1
                (unliftMultiDFVRE L (vpVR (.snd .v3)) .v0)))
              (.snd .v2)))))).eval
        (Env.cons (t := .prod (.opt (.opt (.base CKASort.ss))) mbHsTy)
          (some ssReal, hsMBEnc h₁) ρ₁) =
      Prod.map (Option.map ckaPsEnc) hsMBEnc <$>
        ((if (List.range L).any (fun t => match vp.vR t with | some (.inr _) => true | _ => false)
          then
            pure none
          else
            let vR' : ℕ → Option RS := fun t =>
              if t < L then
                match vp.vR t with
                | some (.inl rs) => some rs
                | _ => none
              else none
            pure (some (realParty vp vp.γ vp.root ssReal vR')) :
          HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E) _).run h₁) := by
    intro ssReal h₁
    rw [eval_caseOpt_some rfl, eval_bind, rangeListC_eval, pure_bind, eval_ite]
    set ρ₂ := Env.cons (t := .opt (.base CKASort.ss)) ssReal
      (Env.cons (t := .prod (.opt (.opt (.base CKASort.ss))) mbHsTy) (some ssReal, hsMBEnc h₁) ρ₁)
    set ρ₃ := Env.cons (t := .list .nat) (List.range L).reverse ρ₂
    have hAny := anyExtMultiDFVRE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (vpVR (.snd .v3)) .v0 ρ₃ rfl
    have hvR3 : (vpVR (.snd (Expr.v3 (O := OO)))).eval ρ₃ = vp.vR := rfl
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
      have hUnlift := unliftMultiDFVRE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L (vpVR (.snd .v3)) .v0 ρ₃ rfl
      have hReal := realPartyE_eval (O' := OO)
        (.snd .v3) (vpΓ (.snd .v3)) (vpRoot (.snd .v3)) .v1
        (unliftMultiDFVRE L (vpVR (.snd .v3)) .v0) ρ₃ vp rfl
      rw [hvR3] at hUnlift
      rw [hReal, hUnlift]
      refine congrArg (fun f =>
        pure (some (ckaPsEnc (realParty vp vp.γ vp.root ssReal f)), hsMBEnc h₁)) ?_
      funext t; rcases vp.vR t with _ | (_ | _) <;> rfl
    · simp only [↓reduceIte]
      rw [eval_ret, StateT.run_pure, map_pure]
      rfl
  rw [eval_bind]
  have hvS : (vpVS (.snd (Expr.v0 (O := OO)))).eval ρ₁ = vp.vS := rfl
  rcases hvS' : vp.vS with _ | (ss | sIdx)
  · rw [eval_caseOpt_none (hvS.trans hvS'), eval_ret, pure_bind]
    simp only [pure_bind]
    exact hStep2 none h
  · rw [eval_caseOpt_some (hvS.trans hvS'), eval_caseSum_inl rfl, eval_ret, pure_bind]
    simp only [pure_bind]
    exact hStep2 (some ss) h
  · rw [eval_caseOpt_some (hvS.trans hvS'), eval_caseSum_inr rfl,
      eval_bind, query_fsMultiDFB_cs_eval]
    simp only [liftFSMultiDFBucket_eq, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
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
      have hBk := fsMultiDFBucketHsGetBookAt_eval (O' := OO) (.fst .v4) .v2 ρ_cs h rfl
      have hIdx : (Expr.v2 (O := OO)).eval ρ_cs = sIdx := rfl
      rw [hIdx] at hBk
      have hSet := fsMultiDFBucketHsSetBookAt_eval (O' := OO) (.fst .v4) .v2
        (.pair (.bool true) (.snd (fsMultiDFBucketHsGetBookAt (.fst .v4) .v2))) ρ_cs h rfl
        (sc := true) (cnt := ((h.book sIdx).getD {}).fsCount)
        (tr := ((h.book sIdx).getD {}).fsTrans)
        (by rw [pair_eval, snd_eval, hBk]; rfl)
      rw [hIdx] at hSet
      let bk0 : FSMultiBook T E := (h.book sIdx).getD {}
      let bk' : FSMultiBook T E := { bk0 with sCorr := true }
      let h' : FSMultiDFBucketState T RSt K I E :=
        { h with book := Function.update h.book sIdx (some bk') }
      have hPair : (Expr.pair (O := OO) (.some (.some .v0))
          (fsMultiDFBucketHsSetBookAt (.fst .v4) .v2
            (.pair (.bool true) (.snd (fsMultiDFBucketHsGetBookAt (.fst .v4) .v2))))).eval ρ_cs =
          (some (some ss'), hsMBEnc h') := by
        rw [pair_eval, hSet]; rfl
      rw [hPair]
      exact hStep2 (some ss') h'

end BucketEvalHelpers2

private theorem hooksFSMultiDFBucketPaperC_agrees
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
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·)) (heqE : eqE = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
        (SS := SS) (RS := RS) (M := M))
      (FSMultiDFBucketHBounded L) (HBoundedPost := FSMultiDFBucketHBoundedPost L)
      (VROk := fun _ => True)
      (hooksFSMultiDFBucketPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep tL par la)
      (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la) where
  hBounded_post _ h := h.2.2
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P hHB hh hctx _ :=
    fsMultiDFBucketPaperStartSendC_eval cka prng fs hSend hPrngUp hFsInitS heqI
      hSampCCoins hSampI hSampK L Δcka Δbucket qep tL par la
      hE ctxE pE tE γE σE rE ρ h ctx P hHB hh hctx
  startSend_bounded ctx P t γ σ r h hHB res hmem := by
    have hB := hooksFSMultiDFBucketPaper_startSend_preserve L cka prng fs Δcka Δbucket qep tL par la
      ctx P t γ σ r h res hmem
    unfold FSMultiDFBucketHBoundedPost; rw [hB.2.2]; exact hHB.2.2
  startRecv_eval hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh hctx _ :=
    fsMultiDFBucketPaperStartRecvC_eval cka prng fs hRecv hPrngUp hFsInitR heqT heqI
      hSampK L Δcka Δbucket qep tL par la hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh hctx
  startRecv_bounded ctx P t γ σ Tn h hHB res hmem := by
    have hB := hooksFSMultiDFBucketPaper_startRecv_preserve L cka prng fs Δcka Δbucket qep tL par la
      ctx P t γ σ Tn h res hmem
    unfold FSMultiDFBucketHBoundedPost; rw [hB.2.2]; exact hHB.2.2
  startRecv_vrOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ := trivial
  fsSend_eval hE ctxE pE tE ssE hdrE mE pairE ρ h ctx P _ hh hctx hp :=
    fsMultiDFBucketFsSendC_eval cka prng fs hFsSend L Δcka Δbucket qep tL par la
      hE ctxE pE tE ssE hdrE mE pairE ρ h ctx P hh hctx hp
  fsRecv_eval hE ctxE pE tE rsE hdrE eE recE ρ h ctx P rec_ hHB _ hh hctx _ hrec :=
    fsMultiDFBucketFsRecvC_eval cka prng fs heqT heqE L B Δcka Δbucket qep tL par la hFsRecvB
      hE ctxE pE tE rsE hdrE eE recE ρ h ctx P rec_ hHB hh hctx hrec
  fsRecv_bounded ctx P t rsv hdr e rec_ h hHB res hmem := by
    have hB := hooksFSMultiDFBucketPaper_fsRecv_preserve L cka prng fs Δcka Δbucket qep tL par la
      ctx P t rsv hdr e rec_ h res hmem
    intro idx bk' hbk'
    rcases hB.2.2 idx bk' hbk' with ⟨bk₀, hbk₀, hle⟩ | hle
    · exact le_trans (by omega) (hHB idx bk₀ hbk₀)
    · omega
  commit_eval hE _ _ _ newE ρ h _ _ _ new _ hh _ _ _ hnew := by
    simp [hooksFSMultiDFBucketPaperC, fsMultiDFBucketCommitC, hooksFSMultiDFBucketPaper, hh, hnew,
      StateT.run_pure, Prod.map, Expr.eval]
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh _ _ hvp :=
    fsMultiDFBucketRevealC_eval cka prng fs L Δcka Δbucket qep tL par la
      hE ctxE pE vpE ρ h ctx P vp hh hvp

private theorem vRecv_preserve_h_only
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {HPre HMid HPost : HS → Prop}
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (h : HS) (hPre : HPre h) (hMid0 : HPre h → HMid h)
    (hMidPost : ∀ {h1}, HMid h1 → HPost h1)
    (hStart : ∀ t0 γ0 σ0 Tn res, HPre h →
      res ∈ support ((hk.startRecv ctx P t0 γ0 σ0 Tn).run h) → HMid res.2)
    (hFs : ∀ {h1} t1 v hHdr e rec' res, HMid h1 →
      res ∈ support ((hk.fsRecv ctx P t1 v hHdr e rec').run h1) → HPost res.2) :
    ∀ res ∈ support ((vRecv hk ctx P s c rec).run h), HPost res.2 := by
  intro ⟨vrRes, h'⟩ hmem
  rw [vRecv_eq_bind] at hmem
  by_cases h1 : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hMidPost (hMid0 hPre)
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
    have hStep1 : HMid h₁ := by
      unfold vRecvStep1 at hmem1
      by_cases h2 : c.1.1 = s.tcur + 1
      · simp only [h2, ↓reduceIte] at hmem1
        rcases hTn : c.1.2 with _ | Tn
        · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem1
          rcases hmem1 with ⟨_, rfl⟩; exact hMid0 hPre
        · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem1
          obtain ⟨⟨srRes, h₁'⟩, hsr, hmem1⟩ := hmem1
          have hM := hStart (s.tcur + 1) s.γ s.root Tn (srRes, h₁') hPre hsr
          rcases srRes with _ | _ | ⟨γ', σ', rs⟩ <;>
            (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem1; rcases hmem1 with ⟨_, rfl⟩; exact hM)
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨_, rfl⟩; exact hMid0 hPre
    rcases s₁? with _ | _ | s₁
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨_, rfl⟩; exact hMidPost hStep1
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨_, rfl⟩; exact hMidPost hStep1
    · rcases hvR1 : s₁.vR c.1.1 with _ | v
      · simp only [hvR1, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨_, rfl⟩; exact hMidPost hStep1
      · simp only [hvR1, StateT.run_bind, mem_support_bind_iff] at hmem2
        obtain ⟨⟨frRes, h₂⟩, hfr, hmem2⟩ := hmem2
        have hP := hFs c.1.1 v c.1 c.2 rec (frRes, h₂) hStep1 hfr
        rcases frRes with _ | _ | ⟨v', i, m⟩ <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem2; rcases hmem2 with ⟨_, rfl⟩; exact hP)

private theorem commitE_fsMultiDFBucket_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (s : GameState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E))
    (P : Party) (old new : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : Pos)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiDFBucketState T RSt K I E)) :
    (commitE (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
      s P old new pos).run es =
      pure (some { s.accept P new pos with st := Function.update (s.accept P new pos).st P new },
        es) := by
  unfold commitE
  simp only [pure_bind, run_liftH_bind, hooksFSMultiDFBucketPaper, StateT.run_pure]

private theorem implEDFPaperBucketRaw_stepBounded
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L B_q : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {m Δ qep maxSkip : ℕ} (cfg : Config M) (Δcka Δbucket : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiDFBucketState T RSt K I E))
    (q_df : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B_q (m + 1) es.g)
    (hPre : FSMultiDFBucketStepBounded B_q (m + 1) es.h) :
    ∀ res ∈ support ((DeliverForge.implEDFPaperBucketRaw
      (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
      Δ qep maxSkip cfg (.inr q_df)).run es),
      FSMultiDFBucketStepBounded B_q m res.2.h := by
  have hm1B : m + 1 ≤ B_q := by
    have := hInv.leaks_le
    omega
  have hPost0 : FSMultiDFBucketStepBounded B_q m es.h := hPre.mono (Nat.le_succ m)
  let HPre : FSMultiDFBucketState T RSt K I E → Prop := FSMultiDFBucketStepBounded B_q (m + 1)
  let HMid : FSMultiDFBucketState T RSt K I E → Prop := fun h =>
    (∀ t, (h.fTable t).length + m ≤ B_q + 1) ∧
    (∀ t, (h.sessions t).length + m ≤ B_q + 1) ∧
    ∀ idx bk, h.book idx = some bk → bk.fsTrans.length + (m + 1) ≤ B_q
  let HPost : FSMultiDFBucketState T RSt K I E → Prop := FSMultiDFBucketStepBounded B_q m
  have hMid0 : HPre es.h → HMid es.h := fun hp =>
    ⟨fun t => by have := hp.1 t; omega,
     fun t => by have := hp.2.1 t; omega,
     hp.2.2⟩
  have hMidPost : ∀ {h1}, HMid h1 → HPost h1 := fun hm =>
    ⟨hm.1, hm.2.1, fun idx bk hbk => by have := hm.2.2 idx bk hbk; omega⟩
  have hvSend : ∀ ctx P s msg pair r res,
      res ∈ support ((vSend (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
        ctx P s msg pair r).run es.h) → HPost res.2 := by
    intro ctx P s msg pair r res hmem
    refine (vSend_preserve_generic
      (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
      ctx P s msg pair r es.h hPre hMid0 hMidPost
      (fun t0 γ0 σ0 r0 res' hp hss => ?_)
      (fun {h1} t1 v hHdr m' pair' res' hm hfs => ?_) res hmem).1
    · have hP := hooksFSMultiDFBucketPaper_startSend_preserve L cka prng fs Δcka Δbucket qep
        tL par la ctx P t0 γ0 σ0 r0 es.h res' hss
      refine ⟨fun t' => by have := hp.1 t'; have := hP.1 t'; omega,
        fun t' => by have := hp.2.1 t'; have := hP.2.1 t'; omega, ?_⟩
      rw [hP.2.2]; exact hp.2.2
    · have hP := hooksFSMultiDFBucketPaper_fsSend_preserve L cka prng fs Δcka Δbucket qep
        tL par la ctx P t1 v hHdr m' pair' h1 res' hfs
      refine ⟨by rw [hP.1]; exact hm.1, by rw [hP.2.1]; exact hm.2.1,
        fsBookStep_apply hm1B hm.2.2 hP.2.2⟩
  have hvRecv : ∀ ctx P s c rec res,
      res ∈ support ((vRecv (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
        ctx P s c rec).run es.h) → HPost res.2 := by
    intro ctx P s c rec res hmem
    refine vRecv_preserve_h_only
      (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
      ctx P s c rec es.h hPre hMid0 hMidPost
      (fun t0 γ0 σ0 Tn res' hp hsr => ?_)
      (fun {h1} t1 v hHdr e rec' res' hm hfr => ?_) res hmem
    · have hP := hooksFSMultiDFBucketPaper_startRecv_preserve L cka prng fs Δcka Δbucket qep
        tL par la ctx P t0 γ0 σ0 Tn es.h res' hsr
      refine ⟨fun t' => by have := hp.1 t'; have := hP.1 t'; omega,
        fun t' => by have := hp.2.1 t'; have := hP.2.1 t'; omega, ?_⟩
      rw [hP.2.2]; exact hp.2.2
    · have hP := hooksFSMultiDFBucketPaper_fsRecv_preserve L cka prng fs Δcka Δbucket qep
        tL par la ctx P t1 v hHdr e rec' h1 res' hfr
      refine ⟨by rw [hP.1]; exact hm.1, by rw [hP.2.1]; exact hm.2.1,
        fsBookStep_apply hm1B hm.2.2 (fsBookStep_mono (Nat.zero_le 1) hP.2.2)⟩
  intro ⟨out, es'⟩ hmem
  rcases q_df with ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (out, es') ∈ support ((DeliverForge.transmitEBucket _ Δ qep (P, msg, r)).run es) at hmem
    unfold DeliverForge.transmitEBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hPost0
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hPost0
      · simp only [hep, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
        have hPres := hvSend s₁ P (s₁.st P) msg none r (vsRes, h') hvs
        rcases vsRes with _ | ⟨st', ct⟩ <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
           rcases hmem with ⟨_, rfl⟩; exact hPres)
  · change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hPost0
  · change (out, es') ∈ support ((deliverE _ maxSkip cfg (P, c)).run es) at hmem
    unfold deliverE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hPost0
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hPost0
      · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hPres := hvRecv es.g P (es.g.st P) c (some r) (vrRes, h') hvr
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hPres
        · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r) <;>
            (simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
              StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; exact hPres)
        · simp only [StateT.run_bind, commitE_fsMultiDFBucket_eq, pure_bind, StateT.run_modify,
            StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hPres
  · change (out, es') ∈ support ((injectE _ Δ qep cfg (P, c)).run es) at hmem
    unfold injectE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hPost0
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      have hPres := hvRecv es.g P (es.g.st P) c none (vrRes, h') hvr
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hPres
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hPres
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hPres
        · simp only [hqep, ↓reduceIte] at hmem
          by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMultiDFBucket_eq, pure_bind,
              StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hPres
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases hf : cfg.injectFull t' <;>
              (simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
               rcases hmem with ⟨_, rfl⟩; exact hPres)
  · change (out, es') ∈ support ((DeliverForge.corrEPaperBucket _ P).run es) at hmem
    unfold DeliverForge.corrEPaperBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hPost0
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, hrev, hmem⟩ := hmem
      have hP := hooksFSMultiDFBucketPaper_reveal_preserve L cka prng fs Δcka Δbucket qep
        tL par la es.g P (es.g.st P) es.h (revRes, h') hrev
      have hFsLe := fsBookStep_apply hm1B hPre.2.2 (fsBookStep_mono (Nat.zero_le 1) hP.2.2)
      rcases revRes with _ | st <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         rcases hmem with ⟨_, rfl⟩;
         exact ⟨by dsimp only; rw [hP.1]; exact hPost0.1,
           by dsimp only; rw [hP.2.1]; exact hPost0.2.1, hFsLe⟩)
  · change (out, es') ∈ support ((DeliverForge.deliverForgeE _ Δ qep cfg (P, c, c')).run es) at hmem
    unfold DeliverForge.deliverForgeE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hPost0
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hPost0
      · simp only [htr] at hmem
        by_cases hbad :
            ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
        · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hPost0
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte,
            run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
          have hPres := hvRecv es.g P (es.g.st P) c' none (vrRes, h') hvr
          rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hPres
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hPres
          · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
            · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hPres
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
              · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMultiDFBucket_eq,
                  pure_bind, StateT.run_modify, StateT.run_pure, support_pure,
                  Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hPres
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                by_cases hf : cfg.injectFull t' <;>
                  (simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                    StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
                    Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
                   rcases hmem with ⟨_, rfl⟩; exact hPres)

private theorem deliverE_win_eq_of_deliverWin_false' {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type} [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {maxSkip : ℕ} (cfg : Config M) (hCfgWin : cfg.deliverWin = false)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E)) :
    ∀ res ∈ support ((deliverE hk maxSkip cfg arg).run es),
      res.2.g.win = es.g.win := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  unfold deliverE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hin : es.g.inTransit P.other c with _ | r
    · simp only [hin, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [hin, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h₁⟩, _, hmem⟩ := hmem
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · dsimp only at hmem
        simp only [hCfgWin, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · dsimp only at hmem
        rw [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨cmRes, es₁⟩, hcm, hmem⟩ := hmem
        have hcmWin : es₁.g.win = es.g.win ∧ ∀ s₁, cmRes = some s₁ → s₁.win = es.g.win := by
          unfold commitE abortE at hcm
          rw [run_liftH_bind, mem_support_bind_iff] at hcm
          obtain ⟨⟨ans, h₂⟩, _, hcm⟩ := hcm
          rcases ans with _ | new'
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcm
            obtain ⟨hcm1, hcm2⟩ := hcm; subst hcm2
            exact ⟨rfl, fun _ hs => by rw [hcm1] at hs; cases hs⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcm
            obtain ⟨hcm1, hcm2⟩ := hcm; subst hcm2
            refine ⟨rfl, fun _ hs => ?_⟩
            rw [hcm1] at hs; cases hs
            dsimp only
            simp [SM.GameState.accept, SM.GameState.delete]
        rcases cmRes with _ | s₁
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hcmWin.1
        · simp only [hCfgWin, Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hcmWin.2 s₁ rfl

private theorem implEDFPaperBucketRaw_inv_sm [DecidableEq T] [DecidableEq M] [DecidableEq E]
    [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      SMEngineInv L B q res.2.g := by
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es) at hmem
    unfold DeliverForge.transmitEBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hep, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, _, hmem⟩ := hmem
        rcases vsRes with _ | ⟨st', c⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInvQ
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv.epMgmt_record hep st' _ false
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · exact deliverE_inv hk cfg es (P, c) hInv
  · exact injectE_inv hk cfg es (P, c) hInv
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.corrEPaperBucket hk P).run es) at hmem
    unfold DeliverForge.corrEPaperBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv.afterCorr P
  · exact deliverForgeE_inv hk cfg es arg hInv

private theorem eval_caseSum_inl' {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b c : Ty S'}
    {e : Expr O' Γ' (.sum a b)} {lb : Comp O' I' (a :: Γ') c} {rb : Comp O' I' (b :: Γ') c}
    {ρ : Env Γ'} {v : a.denote} (h : e.eval ρ = .inl v) :
    (Comp.caseSum e lb rb).eval ρ = lb.eval (.cons v ρ) := by
  simp [Comp.eval, h]

private theorem eval_caseSum_inr' {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b c : Ty S'}
    {e : Expr O' Γ' (.sum a b)} {lb : Comp O' I' (a :: Γ') c} {rb : Comp O' I' (b :: Γ') c}
    {ρ : Env Γ'} {v : b.denote} (h : e.eval ρ = .inr v) :
    (Comp.caseSum e lb rb).eval ρ = rb.eval (.cons v ρ) := by
  simp [Comp.eval, h]

private theorem eval_caseOpt_none' {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a c : Ty S'}
    {e : Expr O' Γ' (.opt a)} {nb : Comp O' I' Γ' c} {sb : Comp O' I' (a :: Γ') c}
    {ρ : Env Γ'} (h : e.eval ρ = none) :
    (Comp.caseOpt e nb sb).eval ρ = nb.eval ρ := by
  simp [Comp.eval, h]

private theorem eval_caseOpt_some' {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a c : Ty S'}
    {e : Expr O' Γ' (.opt a)} {nb : Comp O' I' Γ' c} {sb : Comp O' I' (a :: Γ') c}
    {ρ : Env Γ'} {v : a.denote} (h : e.eval ρ = some v) :
    (Comp.caseOpt e nb sb).eval ρ = sb.eval (.cons v ρ) := by
  simp [Comp.eval, h]

private def bucketHandleDFPaperLocalC
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S}
    (hkC : HooksC (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ)
    (cfgC : ConfigEC (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE))
    {Γ'}
    (st : Expr (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat)))
    (q : Expr (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) I' Γ'
      (.prod (ckaSMRDF KC Γ CCoins T I KR RSt K SS RS M E)
        (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
          (.opt .nat))) :=
  rdsl do
    (es0, winEp0, q0) ← return (st.1, st.2, q)
    match q0 with
    | .inl qBase =>
      match qBase with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if orE (esAbort es0) (cGsWin (esG es0)) then
          return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
        else
          match cEpMgmtE (raw Δ) (raw qep) (esG es0) p0 (isSomeE r0) with
          | none => return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
          | some s1 =>
            (res, h') ← vSendC hkC (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
            match res with
            | none =>
              return (.inl (inl (inl (inl (inl none)))), (esMk (esG es0) h' true, winEp0))
            | some (st', ct) =>
              let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
              let g' := cRecordE (raw L) (raw Δ) s1 p0 st' recE false
              return (.inl (inl (inl (inl (inl (some ct))))), (esMk g' h' (esAbort es0), winEp0))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (inl (inl (inl (inr none)))), (es0, winEp0))
      | .inl (.inl (.inr x)) =>
        (out, es') ← deliverEC hkC L maxSkip cfgC es0 x
        return (.inl (inl (inl (inr out))), (es', winEp0))
      | .inl (.inr x) =>
        let wasWin := cGsWin (esG es0)
        (out, es') ← injectEC hkC L Δ qep cfgC es0 x
        let winEp' := if !wasWin && cGsWin (esG es') then some x.2.1.1 else winEp0
        return (.inl (inl (inr out)), (es', winEp'))
      | .inr p0 =>
        let s0 := esG es0
        if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedPaperE (raw L) s0 p0))) then
          return (.inl (inr none), (es0, winEp0))
        else
          let s1 := cAfterCorrE (raw L) s0 p0
          (res, h') ← hkC.reveal (esH es0) s0 p0 (pGet (cGsSt s0) p0)
          match res with
          | none => return (.inl (inr none), (esMk s0 h' true, winEp0))
          | some stOut =>
            return (.inl (inr (some stOut)), (esMk s1 h' (esAbort es0), winEp0))
    | .inr x =>
      let wasWin := cGsWin (esG es0)
      (out, es') ← deliverForgeEC hkC L Δ qep cfgC es0 x
      let winEp' := if !wasWin && cGsWin (esG es') then some x.2.2.1.1 else winEp0
      return (.inr out, (es', winEp'))

private theorem rdecDF_bucketHandleDFPaperLocalC_eval
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    (hkC : HooksC (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := fun _ => True)
      hkC hk)
    (L Δ qep maxSkip : ℕ)
    (cfgC : ConfigEC (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE))
    (cfg : Config M) (hCfg : ConfigECAgrees cfgC cfg) (hCfgWin : cfg.deliverWin = false)
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    {Γ'}
    (st : Expr (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat)))
    (qE : Expr _ Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (winEp : Option ℕ)
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hst : st.eval ρ = (esEnc vpTblEnc hsEncFn es, winEp))
    (hq : qE.eval ρ = (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) :
    ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      (bucketHandleDFPaperLocalC hkC L Δ qep maxSkip cfgC st qE).eval ρ) =
      Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
        (DeliverForge.implEDFPaperBucket hk Δ qep maxSkip cfg (.inr q)).run (es, winEp) := by
  let OO := ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
  have hSelfNoFlip : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
  unfold bucketHandleDFPaperLocalC DeliverForge.implEDFPaperBucket DeliverForge.withWinEpDF
  dsimp only [StateT.run_mk]
  rw [eval_bind_ret]
  have h0 : (Expr.pair (.fst st) (.pair (.snd st) qE)).eval ρ =
      (esEnc vpTblEnc hsEncFn es, winEp,
       (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) := by
    simp [Expr.eval, hst, hq]
  rw [h0]; clear h0
  rcases q with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inl' rfl,
      eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_bind_ret, eval_ite, orE_eval]
    change ((fun p => _) <$> (if (es.abort || es.g.win) = true then _ else _)) =
      Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
        (do
          let (r_1, s') ← (DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es
          pure (r_1, s', if (!es.g.win && s'.g.win) = true then none else winEp))
    unfold DeliverForge.transmitEBucket abortE
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, eval_ret, StateT.run_pure, pure_bind, map_pure,
        hSelfNoFlip, Bool.false_eq_true]
      rfl
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rw [eval_caseOpt, cEpMgmtE_eval vpTblEnc (O' := OO) Δ qep _ _ _ _ es.g P rfl rfl]
      have hR : ∀ {Γ''} (e : Expr OO Γ'' (.opt (.base CKASort.ccoins))) (ρ'' : Env Γ''),
          e.eval ρ'' = r → (isSomeE e).eval ρ'' = r.isSome := by
        intro Γ'' e ρ'' hr; unfold isSomeE; dsimp only [Expr.eval]; rw [hr]; cases r <;> rfl
      rw [hR _ _ rfl]; clear hR
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [Option.map_none, eval_ret, StateT.run_pure, pure_bind, map_pure,
          hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
        rfl
      · simp only [Option.map_some]
        have hw1 : s₁.win = es.g.win := by
          unfold SM.GameState.epMgmt at hep
          by_cases h1 : P.sendsIn (es.g.epoch P + 1)
          · by_cases h2 : qep < es.g.epoch P + 1
            · simp [h1, h2] at hep
            · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hep
              subst hep
              by_cases h3 : (r.isSome && !(es.g.safeCh Δ P)) = true <;>
                simp [h3, SM.GameState.leak]
          · by_cases h2 : qep < es.g.epoch P
            · simp [h1, h2] at hep
            · simp only [h1, Bool.false_eq_true, h2, ↓reduceIte, Option.some.injEq] at hep
              subst hep; rfl
        rw [eval_bind, vSendC_eval hDefaultE hsEncFn HBounded hkC hk hHk
          _ _ _ _ _ _ _ _ es.h s₁ P (s₁.st P) m none r hHB
          rfl rfl rfl (by cases P <;> rfl) rfl rfl rfl]
        rw [bind_map_left, map_bind, run_liftH_bind, bind_assoc, map_bind]
        refine bind_congr fun ⟨vsRes, h'⟩ => ?_
        rcases vsRes with _ | ⟨st', ct⟩
        · dsimp only [Option.map_none, Prod.map_apply, id_eq]
          rw [eval_caseOpt_none' rfl]
          simp only [eval_ret, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, map_pure, hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
          rfl
        · dsimp only [Option.map_some, Prod.map_apply, id_eq]
          rw [eval_caseOpt_some' rfl]
          have hNoFlip : (!es.g.win &&
              (s₁.record Δ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false).win) = false := by
            simp [SM.GameState.record, hw1]
          simp only [eval_ret, map_pure, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, hNoFlip, Bool.false_eq_true, ↓reduceIte, esMk, pair_eval]
          rw [cRecordE_eval vpTblEnc (O' := OO) L Δ _ _ _ _ _ _ s₁ P st'
            ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
            ((epMgmt_lists_eq hep).2.2.1 ▸ hBound.comp_le)
            rfl rfl rfl (by cases P <;> rfl)]
          rfl
  · rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inl' rfl,
      eval_caseSum_inl' rfl, eval_caseSum_inr' rfl]
    change _ = Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
      (do
        let (r_1, s') ← (DeliverForge.challEBucket (P, m₀, m₁, r)).run es
        pure (r_1, s', if (!es.g.win && s'.g.win) = true then none else winEp))
    simp only [DeliverForge.challEBucket, eval_ret, StateT.run_pure, pure_bind, map_pure,
      hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
    rfl
  · rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inl' rfl,
      eval_caseSum_inr' rfl, eval_bind]
    rw [deliverEC_eval hsEncFn HBounded hkC hk hHk L maxSkip cfgC cfg hCfg heqT heqM heqE
          _ _ _ es P c hHB hBound (fun _ _ _ => trivial) rfl rfl]
    change _ = Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
      (do
        let (r_1, s') ← (deliverE hk maxSkip cfg (P, c)).run es
        pure (r_1, s', if (!es.g.win && s'.g.win) = true then none else winEp))
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine OracleComp.bind_congr_of_forall_mem_support
      ((deliverE hk maxSkip cfg (P, c)).run es) fun ⟨out, es'⟩ hmem => ?_
    have hwinEq := deliverE_win_eq_of_deliverWin_false' hk cfg hCfgWin es (P, c) (out, es') hmem
    have hNoFlip : (!es.g.win && es'.g.win) = false := by rw [hwinEq]; cases es.g.win <;> rfl
    rcases out with _ | (_ | m') <;>
      simp only [eval_ret, pure_bind, hNoFlip, Bool.false_eq_true, ↓reduceIte] <;> rfl
  · rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inr' rfl, eval_bind]
    rw [injectEC_eval hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg heqT heqE
          _ _ _ es P c hHB hBound (fun _ _ _ => trivial) rfl rfl]
    change _ = Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
      (do
        let (r_1, s') ← (injectE hk Δ qep cfg (P, c)).run es
        pure (r_1, s', if (!es.g.win && s'.g.win) = true then some c.1.1 else winEp))
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨out, es'⟩ => ?_
    rcases out with _ | (_ | m') <;>
      (simp only [eval_ret, pure_bind, Function.comp_apply]; rfl)
  · rw [eval_caseSum_inl' rfl, eval_caseSum_inr' rfl, eval_ite, orE_eval, orE_eval, not_eval,
      cCorrAllowedPaperE_eval vpTblEnc (O' := OO) L _ _ _ es.g P hBound.chall_le rfl rfl]
    change ((fun p => _) <$>
      (if (es.abort || (es.g.win || !es.g.corrAllowedPaper P)) = true then _ else _)) =
      Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
        (do
          let (r_1, s') ← (DeliverForge.corrEPaperBucket hk P).run es
          pure (r_1, s', if (!es.g.win && s'.g.win) = true then none else winEp))
    rw [← Bool.or_assoc]
    unfold DeliverForge.corrEPaperBucket abortE
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, eval_ret, StateT.run_pure, pure_bind, map_pure,
        hSelfNoFlip, Bool.false_eq_true]
      rfl
    · simp only [href, Bool.false_eq_true, ↓reduceIte, eval_bind]
      rw [hHk.reveal_eval _ _ _ _ _ es.h es.g P (es.g.st P) hHB rfl rfl rfl (by cases P <;> rfl),
        bind_map_left, map_bind, run_liftH_bind, bind_assoc, map_bind]
      refine bind_congr fun ⟨revRes, h'⟩ => ?_
      rcases revRes with _ | stOut
      · dsimp only [Option.map_none, Prod.map_apply, id_eq]
        rw [eval_caseOpt_none' rfl]
        simp only [eval_ret, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, map_pure, hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
        rfl
      · dsimp only [Option.map_some, Prod.map_apply, id_eq]
        rw [eval_caseOpt_some' rfl]
        have hNoFlip : (!es.g.win && (es.g.afterCorr P).win) = false := by
          simp [SM.GameState.afterCorr, SM.GameState.leak]
        simp only [eval_ret, map_pure, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, hNoFlip, Bool.false_eq_true, ↓reduceIte, esMk, pair_eval]
        rw [cAfterCorrE_eval vpTblEnc (O' := OO) L _ _ _ es.g P
          hBound.trans_le hBound.comp_u rfl rfl]
        simp [Expr.eval, Expr.v0, Expr.v1, Expr.v4, esAbort, esEnc]
  · rw [eval_caseSum_inr' rfl, eval_bind]
    rw [deliverForgeEC_eval hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg heqT heqE
          _ _ _ es P c c' hHB hBound (fun _ _ _ => trivial) rfl rfl]
    change _ = Prod.map id (Prod.map (esEnc vpTblEnc hsEncFn) id) <$>
      (do
        let (r_1, s') ← (DeliverForge.deliverForgeE hk Δ qep cfg (P, c, c')).run es
        pure (r_1, s', if (!es.g.win && s'.g.win) = true then some c'.1.1 else winEp))
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨out, es'⟩ => ?_
    rcases out with _ | (_ | m') <;>
      (simp only [eval_ret, pure_bind, Function.comp_apply]; rfl)

private theorem mem_support_withWinEpDF' {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {St Msg Coins C S' : Type} (ctEpoch : C → ℕ) (hasWin : S' → Bool)
    (impl : QueryImpl (unifSpec + SM.specDF St Msg Coins C) (StateT S' (TComp TSpec)))
    (q : (unifSpec + SM.specDF St Msg Coins C).Domain)
    (s : S') (winEp : Option ℕ) (u : (unifSpec + SM.specDF St Msg Coins C).Range q)
    (s₁ : S') (winEp₁ : Option ℕ)
    (hmem : (u, (s₁, winEp₁)) ∈
      support ((DeliverForge.withWinEpDF ctEpoch hasWin impl q).run (s, winEp))) :
    (u, s₁) ∈ support ((impl q).run s) := by
  unfold DeliverForge.withWinEpDF at hmem
  dsimp only [StateT.run_mk] at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨r', s'⟩, hr, hp⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, _⟩
  exact hr

private theorem simulateQ_implEDFPaperBucket_multi_eval
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
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
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
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
          (FSMultiDFBucketState T RSt K I E))
        (winEp : Option ℕ),
        FSMultiDFBucketStepBounded B_q qAdv es.h → SMEngineInv L B_q qAdv es.g →
        (simulateQ
          (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (bucketHandleDFPaperLocalC
              (hooksFSMultiDFBucketPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep tL par la)
              L (2 + Δcka) qep fs.maxSkip (bucketParPaperAuthCfgEC Δbucket tL par) .v0 .v1)) oa).run
          (esEnc
            (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
              (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E))
            (fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
              (SS := SS) (RS := RS) (M := M)) es, winEp) =
          (Prod.map id (Prod.map (esEnc
            (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
              (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E))
            (fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
              (SS := SS) (RS := RS) (M := M))) id) <$>
            (simulateQ (DeliverForge.implEDFPaperBucket
              (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
              (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)) oa).run (es, winEp)) ∧
        ∀ res ∈ support ((simulateQ (DeliverForge.implEDFPaperBucket
            (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
            (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)) oa).run (es, winEp)),
          SMEngineInv L B_q 0 res.2.1.g := by
  have hHk := hooksFSMultiDFBucketPaperC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqM := eqM) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng fs L B Δcka Δbucket qep tL par la
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend heqT heqI heqE
    hSampCCoins hSampI hSampK hFsRecvB
  have hCfg := bucketParPaperAuthCfgEC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (M := M) Δbucket tL par
  let hsEncFn := fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let vpMEnc := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let hk := hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la
  let handleComp := bucketHandleDFPaperLocalC
    (hooksFSMultiDFBucketPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep tL par la)
    L (2 + Δcka) qep fs.maxSkip (bucketParPaperAuthCfgEC Δbucket tL par)
    (Γ' := [fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E,
      ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es winEp _ hInv
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact hInv.mono (Nat.zero_le qAdv)
  | query_bind q mx ih =>
    intro qAdv hq es winEp hHB hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp)
            (.inl n)).run (esEnc vpMEnc hsEncFn es, winEp) =
          (fun u => (u, (esEnc vpMEnc hsEncFn es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        simp [handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (DeliverForge.implEDFPaperBucket hk (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfgGen Δbucket tL par) (.inl n)).run (es, winEp) =
          (fun u => (u, (es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        simp [DeliverForge.implEDFPaperBucket, DeliverForge.withWinEpDF,
          DeliverForge.implEDFPaperBucketRaw, coinsE, StateT.run_mk, StateT.run_lift,
          map_eq_bind_pure_comp, bind_assoc]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es winEp hHB hInv).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es winEp hHB hInv).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hStepEval := rdecDF_bucketHandleDFPaperLocalC_eval hDefaultE hsEncFn
        (FSMultiDFBucketHBounded L) _ hk hHk L (2 + Δcka) qep fs.maxSkip
        (bucketParPaperAuthCfgEC Δbucket tL par) (bucketAuthCfgGen Δbucket tL par)
        hCfg rfl heqT heqM heqE .v0 .v1
        (.cons (esEnc vpMEnc hsEncFn es, winEp)
          (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))
        es winEp t (hHB.toHBounded hB1) hInv.toBoundedEngine rfl rfl
      have hStep :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp)
            (.inr t)).run (esEnc vpMEnc hsEncFn es, winEp) =
          Prod.map id (Prod.map (esEnc vpMEnc hsEncFn) id) <$>
            (DeliverForge.implEDFPaperBucket hk (2 + Δcka) qep fs.maxSkip
              (bucketAuthCfgGen Δbucket tL par) (.inr t)).run (es, winEp) := by
        have hLHS :
            ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp)
              (.inr t)).run (esEnc vpMEnc hsEncFn es, winEp) =
            ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec t p.1, p.2)) <$>
              handleComp.eval (.cons (esEnc vpMEnc hsEncFn es, winEp)
                (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))) := by
          simp only [handlerImpl, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def]
        exact hLHS.trans hStepEval
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁, winEp₁⟩ hmem => ?_, ?_⟩
      · have hmemRaw := mem_support_withWinEpDF' (fun c : Header T × E => c.1.1)
          (fun es => es.g.win)
          (DeliverForge.implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfgGen Δbucket tL par))
          (.inr t) es winEp u es₁ winEp₁ hmem
        exact (ih u (hqm u) es₁ winEp₁
          (implEDFPaperBucketRaw_stepBounded L B_q cka prng fs
            (bucketAuthCfgGen Δbucket tL par) Δcka Δbucket tL par la es t hInv hHB (u, es₁) hmemRaw)
          (implEDFPaperBucketRaw_inv_sm hk (bucketAuthCfgGen Δbucket tL par)
            es t hInv (u, es₁) hmemRaw)).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁, winEp₁⟩, hmem₁, hmem₂⟩ := hmem
        have hmemRaw := mem_support_withWinEpDF' (fun c : Header T × E => c.1.1)
          (fun es => es.g.win)
          (DeliverForge.implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfgGen Δbucket tL par))
          (.inr t) es winEp u es₁ winEp₁ hmem₁
        exact (ih u (hqm u) es₁ winEp₁
          (implEDFPaperBucketRaw_stepBounded L B_q cka prng fs
            (bucketAuthCfgGen Δbucket tL par) Δcka Δbucket tL par la es t hInv hHB (u, es₁) hmemRaw)
          (implEDFPaperBucketRaw_inv_sm hk (bucketAuthCfgGen Δbucket tL par)
            es t hInv (u, es₁) hmemRaw)).2 res hmem₂

private def initFSMultiDFBucketPaperRaw
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δbucket qep : ℕ)
    (tL : Option ℕ) (par b : Bool) :
    TComp (FSMultiSpec SS RS T M E)
      (EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
        (FSMultiDFBucketState T RSt K I E)) := do
  let kr ← sampleT KR
  let kc ← sampleT KC
  let ((σ, kVal, sid), h₁) ←
    (rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
      prng Δbucket qep tL par 0 false lam (prng.init kr)).run {}
  let (optIdx, h₂) := regSessOptMultiDFBucket L tL 0 sid h₁
  let ssv0 : SS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initSender kVal)
    | some sIdx => .inr sIdx
  let rsv0 : RS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initReceiver kVal)
    | some sIdx => .inr sIdx
  let pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σ ssv0 rsv0
  return { g := { st := fun | .A => pAB.1 | .B => pAB.2, b := b }, h := h₂, abort := false }

private theorem engRunDFPaperBucket_initFSMultiDFBucketPaper_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    DeliverForge.engRunDFPaperBucket
      (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
      (initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par) {} b A =
      (do
        let es₀ ← initFSMultiDFBucketPaperRaw L cka prng fs lam Δbucket qep tL par b
        let res ← (simulateQ (DeliverForge.implEDFPaperBucket
          (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)) A).run (es₀, none)
        return some res) := by
  unfold DeliverForge.engRunDFPaperBucket initFSMultiDFBucketPaper initFSMultiDFBucketPaperRaw
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure,
    bind_assoc, pure_bind]
  refine bind_congr fun kr => bind_congr fun kc => bind_congr fun ⟨⟨σ, kVal, sid⟩, h₁⟩ => ?_
  rfl

private theorem initFSMultiDFBucketPaperEStateC_eval
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
    (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ'} (bE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' .bool)
    (ρ : Env Γ') :
    (initFSMultiDFBucketPaperEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket qep tL par bE).eval ρ =
      esEnc vpTblEnc
        (fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
          (SS := SS) (RS := RS) (M := M)) <$>
        initFSMultiDFBucketPaperRaw L cka prng fs lam Δbucket qep tL par (bE.eval ρ) := by
  let OO := prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
  let IIM := fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
  let mbHsTy := fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
  let vpMEnc := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let hsBEnc := fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  unfold initFSMultiDFBucketPaperEStateC initFSMultiDFBucketPaperRaw
  rw [eval_bind_ret]
  set b : Bool := bE.eval ρ
  set ρ₁ := Env.cons (t := (.bool : Ty S)) b ρ
  have hKR : (@Comp.sample _ _ _ OO IIM _ CKASamp.kr .unit).eval ρ₁ =
      (sampleT KR : TComp (FSMultiSpec SS RS T M E) KR) := by
    simp only [Comp.eval, IIM, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampKR, sampleT]
    exact Engine.liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ KR)
  rw [eval_bind, hKR, map_bind]
  refine bind_congr fun kr => ?_
  set ρ₂ := Env.cons (t := (.base .kr : Ty S)) kr ρ₁
  have hKC : (@Comp.sample _ _ _ OO IIM _ CKASamp.kc .unit).eval ρ₂ =
      (sampleT KC : TComp (FSMultiSpec SS RS T M E) KC) := by
    simp only [Comp.eval, IIM, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampKC, sampleT]
    exact Engine.liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ KC)
  rw [eval_bind, hKC, map_bind]
  refine bind_congr fun kc => ?_
  set ρ₃ := Env.cons (t := (.base .kc : Ty S)) kc ρ₂
  have hRoot := rootFSMultiDFBucketPaperC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins)
    prng hPrngUp heqI hSampI hSampK L Δbucket qep tL par
    fsMultiDFBucketHsEmptyE (.nat 0) (.bool false)
    (Expr.op (O := OO) CKAOp.lamI .unit) (Expr.op (O := OO) CKAOp.prngInit .v1)
    ρ₃ ({} : FSMultiDFBucketState T RSt K I E) rfl (Nat.zero_le L)
  have hT0 : (Expr.nat (O := OO) 0).eval ρ₃ = 0 := rfl
  have hPl0 : (Expr.bool (O := OO) false).eval ρ₃ = false := rfl
  have hLam : (Expr.op (O := OO) CKAOp.lamI .unit).eval ρ₃ = lam := rfl
  have hSig0 : (Expr.op (O := OO) CKAOp.prngInit .v1).eval ρ₃ = prng.init kr := by
    simp [ρ₃, ρ₂, OO, hPrngInit, Expr.eval, Expr.v1]
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
    ((σ, (kVal, sid)), hsBEnc h₁) ρ₃
  have hReg := (regSessOptMultiDFBucketE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (SS := SS) (RS := RS)
    heqI L tL (.snd .v0) (.nat 0) (.snd (.snd (.fst .v0)))
    ρ₄ h₁ rfl hSesL₁).1
  have hT0' : (Expr.nat (O := OO) 0).eval ρ₄ = 0 := rfl
  have hSid : (Expr.snd (.snd (.fst (Expr.v0 (O := OO))))).eval ρ₄ = sid := rfl
  rw [hT0', hSid] at hReg
  set optIdx := (regSessOptMultiDFBucket L tL 0 sid h₁).1
  set h₂ := (regSessOptMultiDFBucket L tL 0 sid h₁).2
  change (Comp.ret _).eval ρ₄ = _
  rw [eval_ret]
  set optIdxE : Expr OO _ (.opt .nat) :=
    .fst (regSessOptMultiDFBucketE L tL (.snd .v0) (.nat 0) (.snd (.snd (.fst .v0))))
  set h2E : Expr OO _ mbHsTy :=
    .snd (regSessOptMultiDFBucketE L tL (.snd .v0) (.nat 0) (.snd (.snd (.fst .v0))))
  set ssv0E : Expr OO _ (.sum (.base .ss) .nat) :=
    .caseOpt optIdxE (.inl (Expr.op (O := OO) CKAOp.fsInitSender (.fst (.snd (.fst .v0)))))
      (.inr .v0)
  set rsv0E : Expr OO _ (.sum (.base .rs) .nat) :=
    .caseOpt optIdxE (.inl (Expr.op (O := OO) CKAOp.fsInitReceiver (.fst (.snd (.fst .v0)))))
      (.inr .v0)
  set ssv0 : SS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initSender kVal)
    | some sIdx => .inr sIdx
  set rsv0 : RS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initReceiver kVal)
    | some sIdx => .inr sIdx
  set pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σ ssv0 rsv0
  have hOptIdxE : optIdxE.eval ρ₄ = optIdx := by simp [optIdxE, hReg, optIdx, Expr.eval]
  have hh2 : h2E.eval ρ₄ = hsBEnc h₂ := by simp [h2E, hReg, h₂, hsBEnc, Expr.eval]
  have hSsv0E : ssv0E.eval ρ₄ = ssv0 := by
    rcases hOpt : optIdx with _ | sIdx <;>
      simp [ssv0E, ssv0, hOptIdxE, hOpt, ρ₄, OO, hFsInitS, Expr.eval, Expr.v0]
  have hRsv0E : rsv0E.eval ρ₄ = rsv0 := by
    rcases hOpt : optIdx with _ | sIdx <;>
      simp [rsv0E, rsv0, hOptIdxE, hOpt, ρ₄, OO, hFsInitR, Expr.eval, Expr.v0]
  have hMkP := mkPartiesE_eval (O' := OO)
    (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .sum (.base .ss) .nat) (rsvT := .sum (.base .rs) .nat)
    (Expr.op (O := OO) CKAOp.ckaInitA .v1)
    (Expr.op (O := OO) CKAOp.ckaInitB .v1)
    (.fst (.fst .v0)) ssv0E rsv0E ρ₄
  have hMkP' :
      (mkPartiesE (O' := OO)
        (γvT := .base .γ) (svT := .base .sig)
        (ssvT := .sum (.base .ss) .nat) (rsvT := .sum (.base .rs) .nat)
        (Expr.op (O := OO) CKAOp.ckaInitA .v1)
        (Expr.op (O := OO) CKAOp.ckaInitB .v1)
        (.fst (.fst .v0)) ssv0E rsv0E).eval ρ₄ =
        (vpMEnc pAB.1, vpMEnc pAB.2) := by
    rw [hMkP]
    simp [hSsv0E, hRsv0E, ρ₄, ρ₃, ρ₂, ρ₁, OO, hInitA, hInitB, pAB, vpMEnc, fsMultiVpEnc,
      Prod.map, Expr.eval, Expr.v0, Expr.v1]
  have hGs := cGsInitE_eval vpMEnc (O' := OO)
    (.fst (mkPartiesE
      (Expr.op (O := OO) CKAOp.ckaInitA .v1)
      (Expr.op (O := OO) CKAOp.ckaInitB .v1)
      (.fst (.fst .v0)) ssv0E rsv0E))
    (.snd (mkPartiesE
      (Expr.op (O := OO) CKAOp.ckaInitA .v1)
      (Expr.op (O := OO) CKAOp.ckaInitB .v1)
      (.fst (.fst .v0)) ssv0E rsv0E))
    .v3 ρ₄ pAB.1 pAB.2
    (by simp [Expr.eval, hMkP']) (by simp [Expr.eval, hMkP'])
  have hb3 : (Expr.v3 (O := OO)).eval ρ₄ = b := rfl
  simp only [esMk, pair_eval, hGs, hh2, hb3, esEnc, cGsEnc, Expr.eval, pAB, ssv0, rsv0,
    vpMEnc, fsMultiVpEnc, map_pure]
  cases optIdx <;> rfl

private theorem initFSMultiDFBucketPaperRaw_inv
    [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (L B_q qAdv : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δbucket qep : ℕ)
    (tL : Option ℕ) (par b : Bool)
    (hqB : qAdv ≤ B_q) (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L) :
    ∀ es₀ ∈ support (initFSMultiDFBucketPaperRaw L cka prng fs lam Δbucket qep tL par b),
      FSMultiDFBucketStepBounded B_q qAdv es₀.h ∧ SMEngineInv L B_q qAdv es₀.g := by
  intro es₀ hmem
  unfold initFSMultiDFBucketPaperRaw at hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kr, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨⟨⟨σ, kVal, sid⟩, h₁⟩, hmemR, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem
  subst hmem
  let ssv0 : SS ⊕ ℕ := match (regSessOptMultiDFBucket L tL 0 sid h₁).1 with
    | none => .inl (fs.initSender kVal)
    | some sIdx => .inr sIdx
  let rsv0 : RS ⊕ ℕ := match (regSessOptMultiDFBucket L tL 0 sid h₁).1 with
    | none => .inl (fs.initReceiver kVal)
    | some sIdx => .inr sIdx
  let g₀ : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E :=
    { st := fun P => match P with
        | .A => (mkParties (cka.initA kc) (cka.initB kc) σ ssv0 rsv0).1
        | .B => (mkParties (cka.initA kc) (cka.initB kc) σ ssv0 rsv0).2
      b := b }
  have hSm : SMEngineInv L B_q qAdv g₀ := (SMEngineInv.init _ b hB1 hBB).mono hqB
  have hRt : (∀ t', (h₁.fTable t').length ≤ 1) ∧
      h₁.sessions = (fun _ => []) ∧ h₁.book = (fun _ => none) := by
    unfold rootFSMultiDFBucketPaper at hmemR
    dsimp only at hmemR
    split_ifs at hmemR
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemR
      cases hmemR; exact ⟨fun _ => Nat.zero_le 1, rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmemR
      obtain ⟨_, _, _, _, hEq⟩ := hmemR; cases hEq
      exact ⟨fun _ => Nat.zero_le 1, rfl, rfl⟩
    · rw [StateT.run_bind, mem_support_bind_iff] at hmemR
      obtain ⟨⟨kLk, h1'⟩, hlk, hmemR⟩ := hmemR
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemR
      cases hmemR
      unfold lookupMultiDFBucketF at hlk
      simp only [StateT.run_bind, StateT.run_get, pure_bind, List.lookup] at hlk
      simp only [StateT.run_lift, StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hlk
      obtain ⟨_, _, hEq⟩ := hlk; cases hEq
      refine ⟨fun t' => ?_, rfl, rfl⟩
      by_cases ht0 : t' = 0 <;> simp [Function.update, ht0]
    · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmemR
      obtain ⟨_, _, _, _, hEq⟩ := hmemR; cases hEq
      exact ⟨fun _ => Nat.zero_le 1, rfl, rfl⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemR
      cases hmemR; exact ⟨fun _ => Nat.zero_le 1, rfl, rfl⟩
  have hReg : (regSessOptMultiDFBucket L tL 0 sid h₁).2.fTable = h₁.fTable ∧
      (∀ t', ((regSessOptMultiDFBucket L tL 0 sid h₁).2.sessions t').length ≤ 1) ∧
      (regSessOptMultiDFBucket L tL 0 sid h₁).2.book = (fun _ => none) := by
    rcases sid with _ | ik
    · exact ⟨rfl, fun t' => by simp [regSessOptMultiDFBucket, hRt.2.1], hRt.2.2⟩
    · dsimp only [regSessOptMultiDFBucket, regSessMultiDFBucket]
      simp only [hRt.2.1, List.length_nil]
      refine ⟨rfl, fun t' => ?_, hRt.2.2⟩
      by_cases ht0 : t' = 0 <;> simp [Function.update, ht0]
  refine ⟨⟨fun t' => ?_, fun t' => ?_, fun sIdx bk hbk => ?_⟩, hSm⟩
  · dsimp only; rw [hReg.1]; have := hRt.1 t'; omega
  · dsimp only; have := hReg.2.1 t'; omega
  · dsimp only at hbk; rw [hReg.2.2] at hbk; cases hbk

private def bucketFinishPaperMultiE
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)}
    (L Δ : ℕ) (la : Bool) (tL : Option ℕ)
    {Γ'}
    (st : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) I' Γ' .bool :=
  rdsl do
    (es0, winEp0) ← return (st.1, st.2)
    if bool la then
      return (fsMultiDFBucketHsLfWin (esH es0))
    else
      match winEp0 with
      | none => return false
      | some tWin =>
        return ((!(esAbort es0) && cGsWin (esG es0)) &&
          cAuthOKE (raw L) (raw Δ) (optNatLit (raw tL)) tWin (esG es0))

private theorem bucketFinishPaperMultiE_eval
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)}
    [DecidableEq M]
    (L Δ : ℕ) (la : Bool) (tL : Option ℕ)
    {Γ'}
    (st : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ')
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiDFBucketState T RSt K I E))
    (winEp : Option ℕ)
    (hLeaks : es.g.leaks.length ≤ L) (hCorrs : es.g.corrs.length ≤ L)
    (hst : st.eval ρ = (esEnc
      (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E))
      (fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
        (SS := SS) (RS := RS) (M := M)) es, winEp)) :
    (bucketFinishPaperMultiE (I' := I') L Δ la tL st).eval ρ =
      pure (if la then es.h.lfWin else DeliverForge.authOutBucket Δ tL (es, winEp)) := by
  let OO := prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
  let vpMEnc := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let hsBEnc := fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  unfold bucketFinishPaperMultiE DeliverForge.authOutBucket authOut
  rw [eval_bind_ret]
  have h0 : (Expr.pair (.fst st) (.snd st)).eval ρ = (esEnc vpMEnc hsBEnc es, winEp) := by
    simp [Expr.eval, hst, vpMEnc, hsBEnc]
  rw [h0]; clear h0
  rw [eval_ite]
  cases la
  · simp only [Expr.eval, Bool.false_eq_true, ↓reduceIte]
    rcases winEp with _ | tWin
    · rw [eval_caseOpt_none' rfl]; rfl
    · rw [eval_caseOpt_some' rfl]
      set ρ₂ := Env.cons (t := .nat) tWin
        (Env.cons (t := fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E)
          (esEnc vpMEnc hsBEnc es, some tWin) ρ)
      change (Comp.ret _).eval ρ₂ = _
      rw [eval_ret]
      congr 1
      have hAuth := cAuthOKE_eval (vpEncFn := vpMEnc) (O' := OO) L Δ
        (optNatLit tL) .v0 (esG (.fst .v1)) ρ₂ es.g hLeaks hCorrs rfl
      have htL : (optNatLit (O' := OO) tL).eval ρ₂ = tL := by cases tL <;> rfl
      have hAb : (esAbort (O' := OO) (.fst .v1)).eval ρ₂ = es.abort := rfl
      have hW : (cGsWin (O' := OO) (esG (.fst .v1))).eval ρ₂ = es.g.win := rfl
      have hV0 : (Expr.v0 (O := OO)).eval ρ₂ = tWin := rfl
      simp only [Expr.eval, hAb, hW, hAuth, htL, hV0]
  · simp [Expr.eval, Expr.v0, eval_ret, esH, esEnc, hsBEnc, fsMultiDFBucketHsEnc,
      fsMultiDFBucketHsLfWin]

/-- Evaluation bridge for `redFSAuthDFPaperMultiBucketProgGen` on `fsClamp B fs`. -/
theorem redFSAuthDFPaperMultiBucketProgGen_eval_clamp
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
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka Δbucket qep : ℕ) (la : Bool) (tL : Option ℕ) (par : Bool)
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
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthDFPaperMultiBucketProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep fs.maxSkip la tL par).eval (fun _ => A) () =
      redFSAuthDFPaperMultiBucketGen L cka prng (fsClamp B fs) lam Δcka Δbucket qep la tL par A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hInit := initFSMultiDFBucketPaperEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L Δbucket qep tL par (.bool false)
    (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redFSAuthDFPaperMultiBucketProgGen CostedReduction.impl
    redFSAuthDFPaperMultiBucketGen
  dsimp only
  rw [eval_bind, hInit, engRunDFPaperBucket_initFSMultiDFBucketPaper_eq]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSMultiDFBucketPaperRaw L cka prng (fsClamp B fs) lam Δbucket qep tL par false)
    fun es₀ hes₀ => ?_
  have ⟨hHB₀, hInv₀⟩ := initFSMultiDFBucketPaperRaw_inv L B_q qAdv cka prng (fsClamp B fs)
    lam Δbucket qep tL par false hqB hB1 hBB es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_implEDFPaperBucket_multi_eval
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    cka prng (fsClamp B fs) L B B_q Δcka Δbucket qep tL par la hB1
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ none hHB₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  rw [hms] at hSim
  let IIM := fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
  let vpMEnc := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let hsBEnc := fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  change (do
    let x ← (simulateQ (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      (bucketHandleDFPaperLocalC
        (hooksFSMultiDFBucketPaperC L B Δcka Δbucket qep tL par la)
        L (2 + Δcka) qep fs.maxSkip (bucketParPaperAuthCfgEC Δbucket tL par) .v0 .v1)) A).run
      (esEnc vpMEnc hsBEnc es₀, none)
    (bucketFinishPaperMultiE (I' := IIM) L (2 + Δcka) la tL .v0).eval
      (Env.cons x.2 (Env.cons (t := .bool) x.1 .nil))) = _
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es', winEp'⟩ hes' => ?_
  have hBnd' := (hSimInv (b', (es', winEp')) hes').toBoundedEngine
  have hOut := bucketFinishPaperMultiE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (I' := IIM) L (2 + Δcka) la tL .v0
    (Env.cons (t := fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E)
      (esEnc vpMEnc hsBEnc es', winEp') (Env.cons (t := .bool) b' .nil))
    es' winEp' hBnd'.leaks_le hBnd'.corrs_le rfl
  simpa [Prod.map] using hOut

private theorem hooksFSMultiDFBucketPaper_startRecv_step {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party) (t0 : ℕ) (γ0 : Γ) (σ0 : RSt) (tn0 : T)
    (h : FSMultiDFBucketState T RSt K I (ℕ × C)) (res)
    (hmem : res ∈ support
      (((hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep tL par la).startRecv ctx P t0 γ0 σ0 tn0).run h))
    (γ' : Γ) (σ' : RSt) (rsv : FSAEAD.RatchetReceiverState K MK ⊕ ℕ)
    (hEq : res.1 = some (some (γ', σ', rsv))) :
    FSVROkMultiStep maxSkip 0 rsv := by
  rcases res with ⟨ans, h'⟩
  dsimp only at hEq
  subst hEq
  unfold hooksFSMultiDFBucketPaper at hmem; dsimp only at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have hNonHon :
      (some (some (γ', σ', rsv)), h') ∈ support
        ((if (!(decide (qep + 1 < t0)) && inStage2BucketGen Δbucket tL par t0) = true then
            if (tL.isSome && (t0 == healEpoch tL)) = true then pure none
            else if postLeakDFBucket tL ctx = true then
              let kk := cka.receive γ0 tn0
              let p := prng.up σ0 kk.2
              pure (some (some (kk.1, p.1, Sum.inl ((FSAEAD.fromAEADPRG ae G maxSkip).initReceiver p.2))))
            else do
              let kk := cka.receive γ0 tn0
              let _ ← lookupMultiDFBucketF t0 kk.2
              let s1 ← get
              let (sIdx, s2) := regSessMultiDFBucket L tL t0 kk.2 s1
              set s2
              pure (some (some (kk.1, (prng.up σ0 kk.2).1, Sum.inr sIdx)))
          else pure (some none) :
          HM (FSMultiSpec (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
            T M (ℕ × C)) _ _).run h) →
      FSVROkMultiStep maxSkip 0 rsv := by
    intro hmem'
    by_cases hc1 : (!(decide (qep + 1 < t0)) && inStage2BucketGen Δbucket tL par t0) = true
    · simp only [hc1, ↓reduceIte] at hmem'
      by_cases hc2 : (tL.isSome && (t0 == healEpoch tL)) = true
      · simp [hc2] at hmem'
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hmem'
        by_cases hc3 : postLeakDFBucket tL ctx = true
        · simp only [hc3, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem'
          rcases hmem' with ⟨⟨_, _, hrsv⟩, _⟩
          subst hrsv
          exact RSReach.init ae G maxSkip _
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
            StateT.run_set, StateT.run_pure, pure_bind, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem'
          obtain ⟨⟨_, h₁⟩, _, ⟨_, _, hrsv⟩, _⟩ := hmem'
          subst hrsv
          trivial
    · simp [hc1] at hmem'
  rcases hcache : h.cache t0 with _ | ⟨Tc, σc, k, optIdx⟩
  · simp only [hcache] at hmem; exact hNonHon hmem
  · by_cases hTc : Tc = tn0
    · simp only [hcache, hTc, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨⟨_, _, hrsv⟩, _⟩
      subst hrsv
      rcases optIdx with _ | sIdx
      · exact RSReach.init ae G maxSkip k
      · trivial
    · simp only [hcache, hTc, ↓reduceIte] at hmem
      exact hNonHon hmem

private theorem vRecvStep1_hooksFSMultiDFBucketPaper_vrOk {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party)
    (s : VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ))
    (c : Header T × (ℕ × C))
    (h : FSMultiDFBucketState T RSt K I (ℕ × C))
    (hVR : ∀ t v, s.vR t = some v → FSVROkMultiStep maxSkip k v) :
    ∀ res ∈ support
      ((vRecvStep1 (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep tL par la) ctx P s c).run h),
      ∀ s₁, res.1 = some (some s₁) → ∀ t v, s₁.vR t = some v → FSVROkMultiStep maxSkip k v := by
  intro ⟨s₁?, h₁⟩ hmem s₁ hs₁ t₀ v₀ hv₀
  unfold vRecvStep1 at hmem
  by_cases ht : c.1.1 = s.tcur + 1
  · simp only [ht, ↓reduceIte] at hmem
    rcases hTn : c.1.2 with _ | Tn
    · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, _⟩; cases hs₁
    · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨srRes, h'⟩, hsr, hmem⟩ := hmem
      rcases srRes with _ | _ | ⟨γ', σ', rs⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩; cases hs₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩; cases hs₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        cases hs₁
        by_cases ht₀ : t₀ = s.tcur + 1
        · subst ht₀
          simp only [Function.update_self, Option.some.injEq] at hv₀
          subst hv₀
          exact (hooksFSMultiDFBucketPaper_startRecv_step L cka prng ae G maxSkip Δcka Δbucket qep
            tL par la ctx P (s.tcur + 1) s.γ s.root Tn h
            (some (some (γ', σ', rs)), h₁) hsr γ' σ' rs rfl).mono (Nat.zero_le k)
        · simp only [Function.update_of_ne ht₀] at hv₀
          exact hVR t₀ v₀ hv₀
  · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, _⟩
    cases hs₁
    exact hVR t₀ v₀ hv₀

private theorem hooksFSMultiDFBucketPaper_fsRecv_fsClamp_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B k Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (hB : (k + 1) * (maxSkip + 1) ≤ B)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party) (t : ℕ) (rsv : FSAEAD.RatchetReceiverState K MK ⊕ ℕ)
    (hdr : Header T) (e : ℕ × C) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSMultiDFBucketState T RSt K I (ℕ × C))
    (hVR : FSVROkMultiStep maxSkip k rsv) :
    ((hooksFSMultiDFBucketPaper L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        Δcka Δbucket qep tL par la).fsRecv ctx P t rsv hdr e rec_).run h =
      ((hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        Δcka Δbucket qep tL par la).fsRecv ctx P t rsv hdr e rec_).run h := by
  dsimp only [hooksFSMultiDFBucketPaper]
  rcases rsv with rs | sIdx
  · dsimp only
    rw [fsClamp_receive_fromAEADPRG ae G maxSkip B k hB hVR hdr e]
  · rfl

private theorem vRecv_fsClamp_multiDFBucket_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B k Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool)
    (hB : (k + 1) * (maxSkip + 1) ≤ B)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party)
    (s : VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ))
    (c : Header T × (ℕ × C)) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSMultiDFBucketState T RSt K I (ℕ × C))
    (hVR : ∀ t v, s.vR t = some v → FSVROkMultiStep maxSkip k v) :
    (vRecv (hooksFSMultiDFBucketPaper L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        Δcka Δbucket qep tL par la) ctx P s c rec_).run h =
      (vRecv (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        Δcka Δbucket qep tL par la) ctx P s c rec_).run h := by
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1))
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hStep1 :
        vRecvStep1
          (hooksFSMultiDFBucketPaper L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
            Δcka Δbucket qep tL par la) ctx P s c =
        vRecvStep1
          (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
            Δcka Δbucket qep tL par la) ctx P s c := rfl
    rw [hStep1]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨s₁?, h₁⟩ hmem => ?_
    have hVR₁ := vRecvStep1_hooksFSMultiDFBucketPaper_vrOk L cka prng ae G maxSkip k
      Δcka Δbucket qep tL par la ctx P s c h hVR (s₁?, h₁) hmem
    rcases s₁? with _ | (_ | s₁)
    · rfl
    · rfl
    · rcases hvRc : s₁.vR c.1.1 with _ | v
      · simp only [hvRc]
      · simp only [hvRc, StateT.run_bind]
        rw [hooksFSMultiDFBucketPaper_fsRecv_fsClamp_eq L cka prng ae G maxSkip B k
          Δcka Δbucket qep tL par la hB ctx P c.1.1 v c.1 c.2 rec_ h₁ (hVR₁ s₁ rfl c.1.1 v hvRc)]

private theorem hooksFSMultiDFBucketPaper_vrInv_fromAEADPRG {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) :
    HooksVRInv (FSVROkMultiStep maxSkip)
      (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        Δcka Δbucket qep tL par la) where
  mono hle hv := hv.mono hle
  startRecv_step :=
    hooksFSMultiDFBucketPaper_startRecv_step L cka prng ae G maxSkip Δcka Δbucket qep tL par la
  fsRecv_step {k} ctx _ t0 rsv hdr e rec_ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    unfold hooksFSMultiDFBucketPaper at hmem; dsimp only at hmem
    rcases rsv with rs | sIdx
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨hmap, _⟩
      rcases hrc : (FSAEAD.fromAEADPRG ae G maxSkip).receive rs hdr e with _ | ⟨rs', i, m⟩
      · simp [hrc] at hmap
      · simp only [hrc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
        rcases hmap with ⟨rfl, rfl, rfl⟩
        exact (RSReach.receive ae G maxSkip _ hVR hrc).2
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      generalize List.find? _ ((h.book sIdx).getD {}).fsTrans = matched at hmem
      by_cases hCond : ((matched.isNone && !(SM.healedBy ctx.tL (2 + Δcka) t0)) &&
          !((h.book sIdx).getD {}).sCorr) = true
      · simp only [hCond, ↓reduceIte] at hmem
        rw [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨csAns, h₀⟩, _, hmem⟩ := hmem
        rcases csAns with _ | _
        · simp at hmem
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            (rw [StateT.run_bind, mem_support_bind_iff] at hmem;
             obtain ⟨⟨qres, h₁⟩, _, hmem⟩ := hmem;
             rcases qres with _ | (_ | ⟨i, mo'⟩) <;> [simp at hmem; simp at hmem; skip];
             simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem;
             split_ifs at hmem <;> [simp [StateT.run_modify] at hmem; skip];
             simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
             rcases mo' with _ | m <;> rcases rec_ with _ | r <;>
               simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                 Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at hmem <;>
               first | exact False.elim hmem | (rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial))
      · simp only [hCond, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hmem
        split_ifs at hmem <;>
          (rw [StateT.run_bind, mem_support_bind_iff] at hmem;
           obtain ⟨⟨qres, h₁⟩, _, hmem⟩ := hmem;
           rcases qres with _ | (_ | ⟨i, mo'⟩) <;> [simp at hmem; simp at hmem; skip];
           simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem;
           split_ifs at hmem <;> [simp [StateT.run_modify] at hmem; skip];
           simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
           rcases mo' with _ | m <;> rcases rec_ with _ | r <;>
             simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
               Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at hmem <;>
             first | exact False.elim hmem | (rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial))
  commit_vR _ _ _ _ _ _ hmem _ hEq := by
    simp only [hooksFSMultiDFBucketPaper, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      at hmem
    subst hmem; cases hEq; rfl

private theorem vSend_hooksFSMultiDFBucketPaper_fsClamp_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (B Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) :
    vSend (hooksFSMultiDFBucketPaper L cka prng (fsClamp B fs) Δcka Δbucket qep tL par la) =
      vSend (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la) := by
  have h1 : (hooksFSMultiDFBucketPaper L cka prng (fsClamp B fs) Δcka Δbucket qep tL par la).startSend =
      (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).startSend := rfl
  have h2 : (hooksFSMultiDFBucketPaper L cka prng (fsClamp B fs) Δcka Δbucket qep tL par la).fsSend =
      (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).fsSend := rfl
  unfold vSend
  rw [h1, h2]

private theorem implEDFPaperBucketRaw_fsClamp_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q q Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) (cfg : Config M)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiDFBucketState T RSt K I (ℕ × C)))
    (t : (SM.specDF (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q (q + 1) es.g) :
    (DeliverForge.implEDFPaperBucketRaw
        (hooksFSMultiDFBucketPaper L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
          Δcka Δbucket qep tL par la)
        (2 + Δcka) qep maxSkip cfg (.inr t)).run es =
      (DeliverForge.implEDFPaperBucketRaw
        (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep tL par la)
        (2 + Δcka) qep maxSkip cfg (.inr t)).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (DeliverForge.transmitEBucket _ (2 + Δcka) qep (P, m, r)).run es =
      (DeliverForge.transmitEBucket _ (2 + Δcka) qep (P, m, r)).run es
    unfold DeliverForge.transmitEBucket
    rw [vSend_hooksFSMultiDFBucketPaper_fsClamp_eq]
  · change (DeliverForge.challEBucket (P, m₀, m₁, r)).run es =
      (DeliverForge.challEBucket (P, m₀, m₁, r)).run es
    rfl
  · change (deliverE _ maxSkip cfg (P, c)).run es = (deliverE _ maxSkip cfg (P, c)).run es
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind]
        rw [vRecv_fsClamp_multiDFBucket_eq L cka prng ae G maxSkip B (B_q - (q + 1))
          Δcka Δbucket qep tL par la hkB es.g P (es.g.st P) c (some r) es.h (hVR P)]
        rfl
  · change (injectE _ (2 + Δcka) qep cfg (P, c)).run es =
      (injectE _ (2 + Δcka) qep cfg (P, c)).run es
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka)))
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
      rw [vRecv_fsClamp_multiDFBucket_eq L cka prng ae G maxSkip B (B_q - (q + 1))
        Δcka Δbucket qep tL par la hkB es.g P (es.g.st P) c none es.h (hVR P)]
      rfl
  · change (DeliverForge.corrEPaperBucket _ P).run es =
      (DeliverForge.corrEPaperBucket _ P).run es
    have hrev :
        (hooksFSMultiDFBucketPaper L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
          Δcka Δbucket qep tL par la).reveal =
        (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep tL par la).reveal := rfl
    unfold DeliverForge.corrEPaperBucket
    rw [hrev]
  · change (DeliverForge.deliverForgeE _ (2 + Δcka) qep cfg (P, c, c')).run es =
      (DeliverForge.deliverForgeE _ (2 + Δcka) qep cfg (P, c, c')).run es
    unfold DeliverForge.deliverForgeE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · rfl
      · dsimp only
        by_cases hbad :
            ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
        · simp only [hbad, ↓reduceIte]
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
          rw [vRecv_fsClamp_multiDFBucket_eq L cka prng ae G maxSkip B (B_q - (q + 1))
            Δcka Δbucket qep tL par la hkB es.g P (es.g.st P) c' none es.h (hVR P)]
          rfl

private theorem implEDFPaperBucketRaw_inv [DecidableEq T] [DecidableEq M] [DecidableEq E]
    [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      SMEngineInv L B q res.2.g := by
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es) at hmem
    unfold DeliverForge.transmitEBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hep, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, _, hmem⟩ := hmem
        rcases vsRes with _ | ⟨st', c⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInvQ
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact hInv.epMgmt_record hep st' _ false
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · exact deliverE_inv hk cfg es (P, c) hInv
  · exact injectE_inv hk cfg es (P, c) hInv
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.corrEPaperBucket hk P).run es) at hmem
    unfold DeliverForge.corrEPaperBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact hInv.afterCorr P
  · exact deliverForgeE_inv hk cfg es arg hInv

private theorem implEDFPaperBucketRaw_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E]
    [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      SMVRInv VROkStep B q res.2.g := by
  have hVRQ : SMVRInv VROkStep B q es.g :=
    SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.transmitEBucket hk Δ qep (P, m, r)).run es) at hmem
    unfold DeliverForge.transmitEBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [hep, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
        rcases vsRes with _ | ⟨st', ct⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          have hst_eq := Engine.epMgmt_st_eq hep
          have hvR_eq := vSend_vR_eq hk s₁ P (s₁.st P) m none r es.h (some (st', ct), h') hvs
            st' ct rfl
          intro Q t₀ v₀ hv₀
          simp only [SM.GameState.record] at hv₀
          by_cases hQP : Q = P
          · subst hQP
            simp only [Function.update_self, hvR_eq, hst_eq] at hv₀
            exact hVRQ Q t₀ v₀ hv₀
          · simp only [Function.update_of_ne hQP, hst_eq] at hv₀
            exact hVRQ Q t₀ v₀ hv₀
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hVRQ
  · exact implE_vrInv hk hVRHk (Δ := Δ) (qep := qep) (maxSkip := maxSkip) cfg
      (⟨false, none, 0⟩ : Mode).policy es (.inl (.inl (.inr (P, c)))) hInv hVR
  · exact implE_vrInv hk hVRHk (Δ := Δ) (qep := qep) (maxSkip := maxSkip) cfg
      (⟨false, none, 0⟩ : Mode).policy es (.inl (.inr (P, c))) hInv hVR
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((DeliverForge.corrEPaperBucket hk P).run es) at hmem
    unfold DeliverForge.corrEPaperBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
  · exact deliverForgeE_vrInv hk hVRHk cfg es arg hInv hVR

private theorem simulateQ_implEDFPaperBucket_multi_fsClamp_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) (cfg : Config M)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    {α : Type} {oa : OracleComp (unifSpec + SM.specDF
      (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
      M CCoins (Header T × (ℕ × C))) α}
    {q : ℕ}
    (hoa : oa.IsQueryBoundP
      (isGameQuery (G := SM.specDF
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) q)
    (st : EState (VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiDFBucketState T RSt K I (ℕ × C)) × Option ℕ)
    (hInv : SMEngineInv L B_q q st.1.g)
    (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q q st.1.g) :
    (simulateQ (DeliverForge.implEDFPaperBucket
        (hooksFSMultiDFBucketPaper L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
          Δcka Δbucket qep tL par la)
        (2 + Δcka) qep maxSkip cfg) oa).run st =
      (simulateQ (DeliverForge.implEDFPaperBucket
        (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep tL par la)
        (2 + Δcka) qep maxSkip cfg) oa).run st := by
  induction oa using OracleComp.inductionOn generalizing q st with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rcases st with ⟨es, winEp⟩
    rw [isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    rcases qy with n | t_df
    · have hCoinL :
          (DeliverForge.implEDFPaperBucket
            (hooksFSMultiDFBucketPaper L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
              Δcka Δbucket qep tL par la)
            (2 + Δcka) qep maxSkip cfg (.inl n)).run (es, winEp) =
          (fun u => (u, (es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec (FSAEAD.RatchetSenderState K)
              (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) (.inl n) := by
        simp [DeliverForge.implEDFPaperBucket, DeliverForge.withWinEpDF,
          DeliverForge.implEDFPaperBucketRaw, coinsE, StateT.run_mk, StateT.run_lift,
          map_eq_bind_pure_comp, bind_assoc]
      have hCoinR :
          (DeliverForge.implEDFPaperBucket
            (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka Δbucket qep tL par la)
            (2 + Δcka) qep maxSkip cfg (.inl n)).run (es, winEp) =
          (fun u => (u, (es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec (FSAEAD.RatchetSenderState K)
              (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) (.inl n) := by
        simp [DeliverForge.implEDFPaperBucket, DeliverForge.withWinEpDF,
          DeliverForge.implEDFPaperBucketRaw, coinsE, StateT.run_mk, StateT.run_lift,
          map_eq_bind_pure_comp, bind_assoc]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u (hmx u) (es, winEp) hInv hVR
    · have hqp : 0 < q := hq0.resolve_left (by simp [isGameQuery])
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hStep :
          (DeliverForge.implEDFPaperBucket
            (hooksFSMultiDFBucketPaper L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
              Δcka Δbucket qep tL par la)
            (2 + Δcka) qep maxSkip cfg (.inr t_df)).run (es, winEp) =
          (DeliverForge.implEDFPaperBucket
            (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka Δbucket qep tL par la)
            (2 + Δcka) qep maxSkip cfg (.inr t_df)).run (es, winEp) := by
        simp only [DeliverForge.implEDFPaperBucket, DeliverForge.withWinEpDF, StateT.run_mk]
        rw [implEDFPaperBucketRaw_fsClamp_eq L cka prng ae G maxSkip B B_q q' Δcka Δbucket qep
          tL par la cfg hB es t_df hVR]
      rw [hStep]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, ⟨es', winEp'⟩⟩ hmem => ?_
      simp only [DeliverForge.implEDFPaperBucket, DeliverForge.withWinEpDF, StateT.run_mk,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨⟨u₁, es₁⟩, hmem₁, huEq, hesEq, hwEq⟩ := hmem
      subst huEq hesEq hwEq
      have hInv' := implEDFPaperBucketRaw_inv
        (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep tL par la) cfg es t_df hInv (u, es') hmem₁
      have hVR' := implEDFPaperBucketRaw_vrInv
        (hooksFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep tL par la)
        (hooksFSMultiDFBucketPaper_vrInv_fromAEADPRG L cka prng ae G maxSkip Δcka Δbucket qep
          tL par la) cfg es t_df hInv hVR (u, es') hmem₁
      exact ih u (hmx u) (es', _) hInv' hVR'

/-- `fsClamp B` removal for `redFSAuthDFPaperMultiBucketGen` on `FSAEAD.fromAEADPRG`. -/
theorem redFSAuthDFPaperMultiBucketGen_fsClamp_fromAEADPRG {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka Δbucket qep : ℕ)
    (lam : I) (la : Bool) (tL : Option ℕ) (par : Bool)
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    redFSAuthDFPaperMultiBucketGen L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        lam Δcka Δbucket qep la tL par A =
      redFSAuthDFPaperMultiBucketGen L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka Δbucket qep la tL par A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  unfold redFSAuthDFPaperMultiBucketGen DeliverForge.engRunDFPaperBucket
  have hInitEq :
      initFSMultiDFBucketPaper L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        lam Δbucket qep tL par =
      initFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δbucket qep tL par := rfl
  have hms1 : (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)).maxSkip = maxSkip := rfl
  have hms2 : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hInitEq, hms1, hms2, bind_assoc, bind_assoc]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h₀⟩ hmem₀ => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  dsimp only [bind_assoc, pure_bind]
  unfold initFSMultiDFBucketPaper at hmem₀
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure,
    pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem₀
  obtain ⟨⟨kr, _⟩, _, ⟨kc, _⟩, _, ⟨⟨σ, kVal, sid⟩, h₁⟩, _, hEq⟩ := hmem₀
  cases hEq
  let ssv0 : FSAEAD.RatchetSenderState K ⊕ ℕ :=
    match (regSessOptMultiDFBucket L tL 0 sid h₁).1 with
    | none => .inl ((FSAEAD.fromAEADPRG ae G maxSkip).initSender kVal)
    | some sIdx => .inr sIdx
  let rsv0 : FSAEAD.RatchetReceiverState K MK ⊕ ℕ :=
    match (regSessOptMultiDFBucket L tL 0 sid h₁).1 with
    | none => .inl ((FSAEAD.fromAEADPRG ae G maxSkip).initReceiver kVal)
    | some sIdx => .inr sIdx
  let g₀ : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C) :=
    { st := fun P => match P with
        | .A => (mkParties (cka.initA kc) (cka.initB kc) σ ssv0 rsv0).1
        | .B => (mkParties (cka.initA kc) (cka.initB kc) σ ssv0 rsv0).2
      b := false }
  have hInv₀ : SMEngineInv L B_q qAdv g₀ := (SMEngineInv.init _ false hB1 hBB).mono hqB
  have hVR₀ : SMVRInv (FSVROkMultiStep maxSkip) B_q qAdv g₀ := by
    intro P t₀ v hv
    cases P <;> simp only [g₀, mkParties] at hv
    · by_cases ht0 : t₀ = 0
      · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv
        subst hv
        dsimp only [rsv0]
        rcases (regSessOptMultiDFBucket L tL 0 sid h₁).1 with _ | sIdx
        · exact (RSReach.init ae G maxSkip kVal).mono (Nat.zero_le _)
        · trivial
      · simp [ht0] at hv
    · cases hv
  simp only [bind_assoc, pure_bind]
  exact congrArg (· >>= _) (simulateQ_implEDFPaperBucket_multi_fsClamp_eq L cka prng ae G maxSkip
    B B_q Δcka Δbucket qep tL par la (bucketAuthCfgGen Δbucket tL par) hFsB hA'
    ({ g := g₀, h := (regSessOptMultiDFBucket L tL 0 sid h₁).2 }, none) hInv₀ hVR₀)

/-- Combined evaluation + `fsClamp` removal bridge for `redFSAuthDFPaperMultiBucketProg` on
`FSAEAD.fromAEADPRG`. -/
theorem redFSAuthDFPaperMultiBucketProg_eval_fromAEADPRG {MK C : Type}
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → FSAEAD.RatchetSenderState K}
    {fsInitReceiver : K → FSAEAD.RatchetReceiverState K MK}
    {fsSend : FSAEAD.RatchetSenderState K → Header T → M →
      FSAEAD.RatchetSenderState K × (ℕ × C)}
    {fsReceive : FSAEAD.RatchetReceiverState K MK → Header T → (ℕ × C) →
      Option (FSAEAD.RatchetReceiverState K MK × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool}
    {eqM : M → M → Bool} {eqE : (ℕ × C) → (ℕ × C) → Bool}
    {lam : I} {defaultE : ℕ × C}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka Δbucket qep : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool)
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = (FSAEAD.fromAEADPRG ae G maxSkip).initSender)
    (hFsInitR : fsInitReceiver = (FSAEAD.fromAEADPRG ae G maxSkip).initReceiver)
    (hFsSend : fsSend = (FSAEAD.fromAEADPRG ae G maxSkip).send)
    (hFsRecv : fsReceive = (FSAEAD.fromAEADPRG ae G maxSkip).receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR)) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthDFPaperMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep maxSkip la tL par).eval (fun _ => A) () =
      redFSAuthDFPaperMultiBucket L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka Δbucket qep la tL par A := by
  have heqE' : eqE = fun x1 x2 : ℕ × C => @BEq.beq (ℕ × C) instBEqOfDecidableEq x1 x2 := by
    cases heqE
    funext ⟨a1, c1⟩ ⟨a2, c2⟩
    by_cases ha : a1 = a2 <;> by_cases hc : c1 = c2 <;> simp [BEq.beq, ha, hc]
  have h1 := redFSAuthDFPaperMultiBucketProgGen_eval_clamp (lam := lam) cka prng
    (FSAEAD.fromAEADPRG ae G maxSkip) L B B_q Δcka Δbucket qep la tL par
    hInitA hInitB hSend hRecv hPrngInit hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqI heqM heqE' hDefaultE hSampKR hSampKC hSampCCoins hSampI hSampK
    hB1 hBB A qAdv hA hqB
  have hms : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hms] at h1
  exact h1.trans (redFSAuthDFPaperMultiBucketGen_fsClamp_fromAEADPRG cka prng ae G maxSkip
    L B B_q Δcka Δbucket qep lam la tL par hFsB hB1 hBB A qAdv hA hqB)

end ShallowFSMultiDFPaper

/-! ### Mode-Split (`gMain : Bool`) and Coin-Averaged (`CKASamp.bit`) `(tL, par)`-Bucket Reductions -/

/-- Pure check whether header `hdr` at epoch `hdr.1` carries the cached honest CKA public value
in `FSMultiDFBucketState`. -/
@[expose] def isHonestHdrFSMultiDFBucket [DecidableEq T]
    (h : FSMultiDFBucketState T RSt K I E) (hdr : Header T) : Bool :=
  match h.cache hdr.1, hdr.2 with
  | some (Tc, _, _, _), some Tn => Tc == Tn
  | _, _ => false

section HooksFSMultiCDFPaperMode

variable
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

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM" =>
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "mVpTy" => fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbEsTy" => fsMultiDFBucketEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbRedEsTy" => fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E

/-- Costed check whether `hdrE` matches the honest sender's cached CKA header in
`fsMultiDFBucketHsCache hE`. -/
@[expose] def isHonestHdrMultiDFBucketE {Γ'}
    (hE : Expr OO Γ' mbHsTy) (hdrE : Expr OO Γ' hdrTy) : Expr OO Γ' .bool :=
  rdslExpr =>
    letE (hE, hdrE) fun (h0, hdr0) =>
      match hdr0.2 with
      | none => false
      | some tn0 =>
        match tget (fsMultiDFBucketHsCache h0) hdr0.1 with
        | none => false
        | some (tCached, _) => Expr.op (O := OO) CKAOp.eqT (tCached, tn0)

/-- Costed `startRecv` for `Main` (`gMain = true`): rejects forged headers (`honest = none`). -/
@[expose] def fsMultiDFBucketPaperMainStartRecvC (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (_ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (_σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO IIM Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.base .sig) (.sum (.base .rs) .nat)))))
        mbHsTy) :=
  rdsl do
    (h0, t0, γ0, tn0) ← return (hE, tE, γE, tnE)
    let honest :=
      match tget (fsMultiDFBucketHsCache h0) t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none =>
      if !(nat (qep + 1) < t0) && validGuessBucketParPaperE (raw Δbucket) (raw tL) (raw par) t0 &&
          (bool tL.isSome && (t0 == nat (healEpoch tL))) then
        return (none, h0)
      else
        return (some none, h0)
    | some (σc, kVal, optIdx) =>
      let γ' := (Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)).1
      let rsv : Expr OO _ (.sum (.base .rs) .nat) :=
        match optIdx with
        | none => .inl (Expr.op (O := OO) CKAOp.fsInitReceiver kVal)
        | some sIdx => .inr sIdx
      return (some (some (γ', σc, rsv)), h0)

/-- Mode-parameterized costed `startRecv` (`gMain = true` → `Main`, `gMain = false` → `ForgedHdr`). -/
@[expose] def fsMultiDFBucketPaperModeStartRecvC (L Δbucket qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO IIM Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.base .sig) (.sum (.base .rs) .nat)))))
        mbHsTy) :=
  if gMain then
    fsMultiDFBucketPaperMainStartRecvC Δbucket qep tL par hE ctxE pE tE γE σE tnE
  else
    fsMultiDFBucketPaperStartRecvC L Δbucket qep tL par hE ctxE pE tE γE σE tnE

/-- Costed `reveal` for `ForgedHdr` (`gMain = false`): aborts whenever
`!(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL)`. -/
@[expose] def fsMultiDFBucketForgedHdrRevealC (L : ℕ) (la : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' mVpTy) :
    Comp OO IIM Γ' (.prod (.opt psTy) mbHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, ctx0, p0, vp0) ← return (hE, ctxE, pE, vpE)
    let e := vpTcurNat vp0
    let epAB := cGsEpoch ctx0
    let eMax := maxN epAB.1 epAB.2
    if orE (!(e < nat tH)) (!(eMax < nat tH)) then
      return (none, h0)
    else
      fsMultiDFBucketRevealC L (raw la) h0 ctx0 p0 vp0

/-- Mode-parameterized costed `reveal` (`gMain = true` → `Main`, `gMain = false` → `ForgedHdr`). -/
@[expose] def fsMultiDFBucketModeRevealC (L : ℕ) (gMain la : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' mVpTy) :
    Comp OO IIM Γ' (.prod (.opt psTy) mbHsTy) :=
  if gMain then
    fsMultiDFBucketRevealC L la hE ctxE pE vpE
  else
    fsMultiDFBucketForgedHdrRevealC L la tL hE ctxE pE vpE

/-- Mode-parameterized costed `HooksC` bundle (`gMain = true` → `Main`, `gMain = false` → `ForgedHdr`). -/
@[expose] def hooksFSMultiDFBucketPaperModeC (L B Δcka Δbucket qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool) :
    HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) mbHsTy where
  startSend := fsMultiDFBucketPaperStartSendC L Δbucket qep tL par
  startRecv := fsMultiDFBucketPaperModeStartRecvC L Δbucket qep gMain tL par
  fsSend := fsMultiDFBucketFsSendC Δcka la
  fsRecv := fsMultiDFBucketPaperFsRecvC L B la Δcka
  commit := fsMultiDFBucketCommitC
  reveal := fsMultiDFBucketModeRevealC L gMain la tL

/-- Mode-parameterized step handler for `(tL, par)`-bucket `redFSAuthDFPaperMultiBucketModeProgGen`. -/
@[expose] def bucketModeHandleDFPaperC (L B Δcka Δbucket qep maxSkip : ℕ) (gMain la : Bool)
    (tL : Option ℕ) (par : Bool) {Γ'}
    (stE : Expr OO Γ' mbRedEsTy)
    (qArgE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp OO IIM Γ' (.prod (ckaSMRDF KC Γ CCoins T I KR RSt K SS RS M E) mbRedEsTy) :=
  rdsl do
    (es0, winEp0, q0) ← return (stE.1, stE.2, qArgE)
    match q0 with
    | .inl qBase =>
      match qBase with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if orE (esAbort es0) (cGsWin (esG es0)) then
          return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
        else
          match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
          | none => return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
          | some s1 =>
            (res, h') ← vSendC (raw (hooksFSMultiDFBucketPaperModeC L B Δcka Δbucket qep gMain tL par la))
              (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
            match res with
            | none => return (.inl (inl (inl (inl (inl none)))), (esMk (esG es0) h' true, winEp0))
            | some (st', ct) =>
              let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
              let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
              return (.inl (inl (inl (inl (inl (some ct))))), (esMk g' h' (esAbort es0), winEp0))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (inl (inl (inl (inr none)))), (es0, winEp0))
      | .inl (.inl (.inr x)) =>
        (out, es') ← deliverEC (raw (hooksFSMultiDFBucketPaperModeC L B Δcka Δbucket qep gMain tL par la))
          L maxSkip (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
        return (.inl (inl (inl (inr out))), (es', winEp0))
      | .inl (.inr x) =>
        let wasWin := cGsWin (esG es0)
        let isNewForged :=
          (x.2.1.1 == vpTcurNat (pGet (cGsSt (esG es0)) x.1) + 1) &&
            !(isHonestHdrMultiDFBucketE (esH es0) x.2.1)
        (out, es') ← injectEC (raw (hooksFSMultiDFBucketPaperModeC L B Δcka Δbucket qep gMain tL par la))
          L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
        let winEp' :=
          if !wasWin && cGsWin (esG es') && orE (bool gMain) isNewForged then
            some x.2.1.1
          else winEp0
        return (.inl (inl (inr out)), (es', winEp'))
      | .inr p0 =>
        let s0 := esG es0
        if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedPaperE (raw L) s0 p0))) then
          return (.inl (inr none), (es0, winEp0))
        else
          let s1 := cAfterCorrE (raw L) s0 p0
          (res, h') ← fsMultiDFBucketModeRevealC L (raw gMain) (raw la) (raw tL)
            (esH es0) s0 p0 (pGet (cGsSt s0) p0)
          match res with
          | none => return (.inl (inr none), (esMk s0 h' true, winEp0))
          | some stOut =>
            return (.inl (inr (some stOut)), (esMk s1 h' (esAbort es0), winEp0))
    | .inr x =>
      let wasWin := cGsWin (esG es0)
      (out, es') ← deliverForgeEC (raw (hooksFSMultiDFBucketPaperModeC L B Δcka Δbucket qep gMain tL par la))
        L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
      let winEp' := if !wasWin && cGsWin (esG es') && bool gMain then some x.2.2.1.1 else winEp0
      return (.inr out, (es', winEp'))

/-- Mode-parameterized (`gMain : Bool`) Stage-2 `(tL, par)`-bucket `redFSAuthDFPaper` program. -/
@[expose] def redFSAuthDFPaperMultiBucketModeProgGen (L B Δcka Δbucket qep maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    CostedReduction OO IIM
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := mbRedEsTy
  init := rdsl [_] do
    es ← initFSMultiDFBucketPaperEStateC L Δbucket qep tL par false
    return ((), (es, none))
  handle := rdsl [st, qArg] do
    bucketModeHandleDFPaperC L B Δcka Δbucket qep maxSkip (raw gMain) (raw la) (raw tL) (raw par)
      st qArg
  finish := rdsl [st, _] do
    (es0, winEp0) ← return (st.1, st.2)
    if bool la then
      return (fsMultiDFBucketHsLfWin (esH es0))
    else
      match winEp0 with
      | none => return false
      | some tWin =>
        return ((!(esAbort es0) && cGsWin (esG es0)) &&
          cAuthOKE (raw L) (raw (2 + Δcka)) (optNatLit (raw tL)) tWin (esG es0))

/-- Default mode-parameterized (`gMain : Bool`) Stage-2 `(tL, par)`-bucket program. -/
abbrev redFSAuthDFPaperMultiBucketModeProg (L B Δcka Δbucket qep maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    CostedReduction OO IIM
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool :=
  redFSAuthDFPaperMultiBucketModeProgGen L B Δcka Δbucket qep maxSkip gMain la tL par

/-- Coin-averaged (`gMain ← CKASamp.bit ()` at `init`) Stage-2 `(tL, par)`-bucket program (`B_fs_u`). -/
@[expose] def redFSAuthDFPaperMultiBucketCoinProgGen (L B Δcka Δbucket qep maxSkip : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool) :
    CostedReduction OO IIM
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := .prod .bool mbRedEsTy
  init := rdsl [_] do
    gMain ← sample (O := OO) (I := IIM) CKASamp.bit ()
    es ← initFSMultiDFBucketPaperEStateC L Δbucket qep tL par false
    return ((), (gMain, (es, none)))
  handle := rdsl [st, qArg] do
    (gMain0, st0, q0) ← return (st.1, st.2, qArg)
    if gMain0 then
      (out, st') ← bucketModeHandleDFPaperC L B Δcka Δbucket qep maxSkip (raw true) (raw la)
        (raw tL) (raw par) st0 q0
      return (out, (gMain0, st'))
    else
      (out, st') ← bucketModeHandleDFPaperC L B Δcka Δbucket qep maxSkip (raw false) (raw la)
        (raw tL) (raw par) st0 q0
      return (out, (gMain0, st'))
  finish := rdsl [st, _] do
    (es0, winEp0) ← return (st.2.1, st.2.2)
    if bool la then
      return (fsMultiDFBucketHsLfWin (esH es0))
    else
      match winEp0 with
      | none => return false
      | some tWin =>
        return ((!(esAbort es0) && cGsWin (esG es0)) &&
          cAuthOKE (raw L) (raw (2 + Δcka)) (optNatLit (raw tL)) tWin (esG es0))

/-- Default coin-averaged (`gMain ← CKASamp.bit ()`) Stage-2 `(tL, par)`-bucket program (`B_fs_u`). -/
abbrev redFSAuthDFPaperMultiBucketCoinProg (L B Δcka Δbucket qep maxSkip : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool) :
    CostedReduction OO IIM
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool :=
  redFSAuthDFPaperMultiBucketCoinProgGen L B Δcka Δbucket qep maxSkip la tL par

@[simp] theorem fsMultiDFBucketPaperMainStartRecvC_queries (Δbucket qep : ℕ) (tL : Option ℕ)
    (par : Bool) (w : FSHdrTag → ℕ) {Γ'} (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig)) (tnE : Expr OO Γ' (.base .t)) :
    (fsMultiDFBucketPaperMainStartRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      Δbucket qep tL par hE ctxE pE tE γE σE tnE).queries w (fun _ => 0) = 0 := by
  simp [fsMultiDFBucketPaperMainStartRecvC, Comp.queries]

@[simp] theorem fsMultiDFBucketPaperModeStartRecvC_queries (L Δbucket qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) (w : FSHdrTag → ℕ) {Γ'} (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig)) (tnE : Expr OO Γ' (.base .t)) :
    (fsMultiDFBucketPaperModeStartRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L Δbucket qep gMain tL par hE ctxE pE tE γE σE tnE).queries w (fun _ => 0) = 0 := by
  cases gMain <;> simp [fsMultiDFBucketPaperModeStartRecvC]

theorem redFSAuthDFPaperMultiBucketModeProgGen_totalQueries (L B Δcka Δbucket qep maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    (redFSAuthDFPaperMultiBucketModeProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip gMain la tL par).totalQueries (fun _ => 1) (fun _ => 0) qAdv ≤
      qAdv * 2 := by
  simp only [CostedReduction.totalQueries, redFSAuthDFPaperMultiBucketModeProgGen,
    initFSMultiDFBucketPaperEStateC_queries, Comp.queries, zero_add, add_zero]
  apply Nat.mul_le_mul_left qAdv
  cases gMain <;> cases la <;>
    simp [bucketModeHandleDFPaperC, deliverEC, injectEC, deliverForgeEC, vSendC, vSendStep1C,
      vRecvC, vRecvStep1C, commitEC, hooksFSMultiDFBucketPaperModeC, fsMultiDFBucketFsSendC,
      fsMultiDFBucketPaperFsRecvC, fsMultiDFBucketModeRevealC, fsMultiDFBucketForgedHdrRevealC,
      fsMultiDFBucketRevealC, Comp.queries]

theorem redFSAuthDFPaperMultiBucketModeProg_totalQueries (L B Δcka Δbucket qep maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    (redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip gMain la tL par).totalQueries (fun _ => 1) (fun _ => 0) qAdv ≤
      qAdv * 2 :=
  redFSAuthDFPaperMultiBucketModeProgGen_totalQueries L B Δcka Δbucket qep maxSkip gMain la tL par qAdv

theorem redFSAuthDFPaperMultiBucketModeProg_totalDecQueries (L B Δcka Δbucket qep maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    (redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip gMain la tL par).totalQueries fsHdrDecWt (fun _ => 0) qAdv =
      qAdv := by
  cases gMain <;> cases la <;>
    simp [redFSAuthDFPaperMultiBucketModeProg, CostedReduction.totalQueries,
      redFSAuthDFPaperMultiBucketModeProgGen, bucketModeHandleDFPaperC, deliverEC, injectEC,
      deliverForgeEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
      hooksFSMultiDFBucketPaperModeC, fsMultiDFBucketFsSendC, fsMultiDFBucketPaperFsRecvC,
      fsMultiDFBucketModeRevealC, fsMultiDFBucketForgedHdrRevealC, fsMultiDFBucketRevealC,
      fsHdrDecWt, Comp.queries]

theorem redFSAuthDFPaperMultiBucketModeProg_totalCost (L B Δcka Δbucket qep maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    let P := redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip gMain la tL par
    P.totalCost qAdv = P.init.cost + qAdv * (P.handle.cost + 13) + P.finish.cost := by
  intro P
  have hCodec : (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).codecCost = 13 := rfl
  have hUCost : (fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).uCost = 1 := rfl
  dsimp only [CostedReduction.totalCost]
  change P.init.cost + qAdv * max (fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).uCost
      (P.handle.cost + (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).codecCost) +
      P.finish.cost = _
  rw [hCodec, hUCost, max_eq_right (by omega)]

theorem redFSAuthDFPaperMultiBucketCoinProgGen_totalQueries (L B Δcka Δbucket qep maxSkip : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    (redFSAuthDFPaperMultiBucketCoinProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip la tL par).totalQueries (fun _ => 1) (fun _ => 0) qAdv ≤
      qAdv * 2 := by
  simp only [CostedReduction.totalQueries, redFSAuthDFPaperMultiBucketCoinProgGen,
    initFSMultiDFBucketPaperEStateC_queries, Comp.queries, zero_add, add_zero]
  apply Nat.mul_le_mul_left qAdv
  cases la <;>
    simp [bucketModeHandleDFPaperC, deliverEC, injectEC, deliverForgeEC, vSendC, vSendStep1C,
      vRecvC, vRecvStep1C, commitEC, hooksFSMultiDFBucketPaperModeC, fsMultiDFBucketFsSendC,
      fsMultiDFBucketPaperFsRecvC, fsMultiDFBucketModeRevealC, fsMultiDFBucketForgedHdrRevealC,
      fsMultiDFBucketRevealC, Comp.queries]

theorem redFSAuthDFPaperMultiBucketCoinProg_totalQueries (L B Δcka Δbucket qep maxSkip : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    (redFSAuthDFPaperMultiBucketCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip la tL par).totalQueries (fun _ => 1) (fun _ => 0) qAdv ≤
      qAdv * 2 :=
  redFSAuthDFPaperMultiBucketCoinProgGen_totalQueries L B Δcka Δbucket qep maxSkip la tL par qAdv

theorem redFSAuthDFPaperMultiBucketCoinProg_totalDecQueries (L B Δcka Δbucket qep maxSkip : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    (redFSAuthDFPaperMultiBucketCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip la tL par).totalQueries fsHdrDecWt (fun _ => 0) qAdv =
      qAdv := by
  cases la <;>
    simp [redFSAuthDFPaperMultiBucketCoinProg, CostedReduction.totalQueries,
      redFSAuthDFPaperMultiBucketCoinProgGen, bucketModeHandleDFPaperC, deliverEC, injectEC,
      deliverForgeEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
      hooksFSMultiDFBucketPaperModeC, fsMultiDFBucketFsSendC, fsMultiDFBucketPaperFsRecvC,
      fsMultiDFBucketModeRevealC, fsMultiDFBucketForgedHdrRevealC, fsMultiDFBucketRevealC,
      fsHdrDecWt, Comp.queries]

theorem redFSAuthDFPaperMultiBucketCoinProg_totalCost (L B Δcka Δbucket qep maxSkip : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool) (qAdv : ℕ) :
    let P := redFSAuthDFPaperMultiBucketCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip la tL par
    P.totalCost qAdv = P.init.cost + qAdv * (P.handle.cost + 13) + P.finish.cost := by
  intro P
  have hCodec : (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).codecCost = 13 := rfl
  have hUCost : (fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).uCost = 1 := rfl
  dsimp only [CostedReduction.totalCost]
  change P.init.cost + qAdv * max (fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).uCost
      (P.handle.cost + (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).codecCost) +
      P.finish.cost = _
  rw [hCodec, hUCost, max_eq_right (by omega)]

private theorem isHonestHdrMultiDFBucketE_eval [DecidableEq T]
    (heqT : eqT = (· == ·)) {Γ'}
    (hE : Expr OO Γ' mbHsTy) (hdrE : Expr OO Γ' hdrTy) (ρ : Env Γ')
    (h : FSMultiDFBucketState T RSt K I E) (hdr : Header T)
    (hh : hE.eval ρ = fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
      (SS := SS) (RS := RS) (M := M) h)
    (hhdr : hdrE.eval ρ = hdr) :
    (isHonestHdrMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) hE hdrE).eval ρ =
      isHonestHdrFSMultiDFBucket h hdr := by
  unfold isHonestHdrMultiDFBucketE isHonestHdrFSMultiDFBucket
  rw [letE_eval]
  have h0 : (Expr.pair hE hdrE).eval ρ =
      (fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
        (SS := SS) (RS := RS) (M := M) h, hdr) := by
    simp [Expr.eval, hh, hhdr]
  rw [h0]
  rcases hdr with ⟨t0, _ | tn0⟩ <;>
    rcases hcache : h.cache t0 with _ | ⟨Tc, σc, kVal, optIdx⟩ <;>
    simp [hcache, heqT, fsMultiDFBucketHsCache, fsMultiDFBucketHsEnc, prngOps, ckaOps,
      Expr.eval, Expr.v0, Expr.v1]

end HooksFSMultiCDFPaperMode

section ShallowFSMultiDFPaperMode

/-- Mode-parameterized shallow `Hooks` bundle (`gMain = true` → `Main`, `gMain = false` → `ForgedHdr`). -/
@[expose] def hooksFSMultiDFBucketPaperMode
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool) :
    Hooks (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)
      Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ) :=
  { hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la with
    startRecv :=
      if gMain then
        fun _ _ t0 γ0 _ tn0 => do
          let honest := match (← get).cache t0 with
            | some (tCached, σc, kVal, optIdx) =>
              if tCached = tn0 then some (σc, kVal, optIdx) else none
            | none => none
          match honest with
          | some (σc, kVal, optIdx) =>
            let rsv : RS ⊕ ℕ := match optIdx with
              | none => .inl (fs.initReceiver kVal)
              | some sIdx => .inr sIdx
            return some (some ((cka.receive γ0 tn0).1, σc, rsv))
          | none =>
            if !(qep + 1 < t0) && inStage2BucketGen Δbucket tL par t0 &&
                (tL.isSome && (t0 == healEpoch tL)) then
              return none
            else
              return some none
      else
        (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).startRecv
    reveal :=
      if gMain then
        (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).reveal
      else
        fun ctx P vp =>
          if !(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL) then
            pure none
          else
            (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).reveal ctx P vp }

/-- Mode-parameterized (`gMain : Bool`) shallow Stage-2 `(tL, par)`-bucket reduction. -/
@[expose] def redFSAuthDFPaperMultiBucketModeGen
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka Δbucket qep : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool := do
  let r ← DeliverForge.engRunDFPaperBucketMode
    (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
    (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par) gMain isHonestHdrFSMultiDFBucket
    (initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par) {} false A
  return match r with
    | none => false
    | some (_, st) =>
      if la then st.1.h.lfWin else DeliverForge.authOutBucket (2 + Δcka) tL st

/-- Default mode-parameterized (`gMain : Bool`) shallow Stage-2 `(tL, par)`-bucket reduction. -/
abbrev redFSAuthDFPaperMultiBucketMode
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka Δbucket qep : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool :=
  redFSAuthDFPaperMultiBucketModeGen L cka prng fs lam Δcka Δbucket qep gMain la tL par A

/-- Coin-averaged (`gMain ← sampleT Bool`) shallow Stage-2 `(tL, par)`-bucket reduction (`B_fs_u`). -/
@[expose] def redFSAuthDFPaperMultiBucketCoinGen
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka Δbucket qep : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool := do
  let gMain ← sampleT Bool
  redFSAuthDFPaperMultiBucketModeGen L cka prng fs lam Δcka Δbucket qep gMain la tL par A

/-- Default coin-averaged (`gMain ← sampleT Bool`) shallow Stage-2 `(tL, par)`-bucket reduction. -/
abbrev redFSAuthDFPaperMultiBucketCoin
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka Δbucket qep : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool :=
  redFSAuthDFPaperMultiBucketCoinGen L cka prng fs lam Δcka Δbucket qep la tL par A

section ModeEvalHelpers

variable
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

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM" =>
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "mVpTy" => fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbRedEsTy" => fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "vpMEnc" =>
  fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
local notation "hsMBEnc" =>
  fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)

private theorem fsMultiDFBucketPaperMainStartRecvC_eval
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (L Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : FSMultiDFBucketState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party)
    (hh : hE.eval ρ = hsMBEnc h) :
    (fsMultiDFBucketPaperMainStartRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      Δbucket qep tL par hE ctxE pE tE γE σE tnE).eval ρ =
      Prod.map id hsMBEnc <$>
        ((hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep true tL par la).startRecv
          ctx P (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h := by
  unfold fsMultiDFBucketPaperMainStartRecvC hooksFSMultiDFBucketPaperMode
  simp only [↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
  set t0 := tE.eval ρ
  set γ0 := γE.eval ρ
  set tn0 := tnE.eval ρ
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair tE (.pair γE tnE))).eval ρ = (hsMBEnc h, t0, γ0, tn0) := by
    simp [Expr.eval, hh, t0, γ0, tn0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mbHsTy (.prod .nat (.prod (.base CKASort.γ) (.base CKASort.t))))
    (hsMBEnc h, t0, γ0, tn0) ρ
  have hNoneBranch :
      (Comp.ite (O := OO) (I := IIM)
        (t := .prod (.opt (.opt (.prod (.base CKASort.γ)
          (.prod (.base CKASort.sig) (.sum (.base CKASort.rs) .nat))))) mbHsTy)
        (.and (.and (.not (.lt (.nat (qep + 1)) (.fst (.snd .v0))))
            (validGuessBucketParPaperE Δbucket tL par (.fst (.snd .v0))))
          (.and (.bool tL.isSome) (.eqN (.fst (.snd .v0)) (.nat (healEpoch tL)))))
        (.ret (.pair .none (.fst .v0)))
        (.ret (.pair (.some .none) (.fst .v0)))).eval ρ₁ =
      Prod.map id hsMBEnc <$>
        ((if ((!(decide (qep + 1 < t0)) && inStage2BucketGen Δbucket tL par t0) &&
            (tL.isSome && (t0 == healEpoch tL))) = true then
            pure none
          else
            pure (some none) :
          HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)
            (Option (Option (Γ × RSt × (RS ⊕ ℕ))))).run h) := by
    rw [eval_ite]
    have hCond :
        (Expr.and (O := OO)
          (.and (.not (.lt (.nat (qep + 1)) (.fst (.snd .v0))))
            (validGuessBucketParPaperE Δbucket tL par (.fst (.snd .v0))))
          (.and (.bool tL.isSome) (.eqN (.fst (.snd .v0)) (.nat (healEpoch tL))))).eval ρ₁ =
        ((!(decide (qep + 1 < t0)) && inStage2BucketGen Δbucket tL par t0) &&
          (tL.isSome && (t0 == healEpoch tL))) := by
      rw [and_eval, and_eval, validGuessBucketParPaperE_eval]
      by_cases htH : t0 = healEpoch tL <;> simp [ρ₁, htH, Expr.eval, Expr.v0]
    rw [hCond]
    by_cases hc :
        ((!(decide (qep + 1 < t0)) && inStage2BucketGen Δbucket tL par t0) &&
          (tL.isSome && (t0 == healEpoch tL))) = true <;>
      simp [hc, ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
  rcases hcache : h.cache t0 with _ | ⟨Tc, σc, kVal, optIdx⟩
  · have hHonNone :
        (Expr.caseOpt (O := OO) (.tget (fsMultiDFBucketHsCache (.fst .v0)) (.fst (.snd .v0))) .none
          (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd .v1)))))
            (.some (.snd .v0))
            .none)).eval ρ₁ = none := by
      simp [ρ₁, hcache, fsMultiDFBucketHsCache, fsMultiDFBucketHsEnc, Expr.eval, Expr.v0]
    rw [eval_caseOpt_none hHonNone]
    exact hNoneBranch
  · by_cases hEq : Tc = tn0
    · have hHonSome :
          (Expr.caseOpt (O := OO) (.tget (fsMultiDFBucketHsCache (.fst .v0)) (.fst (.snd .v0))) .none
            (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd .v1)))))
              (.some (.snd .v0))
              .none)).eval ρ₁ = some (σc, kVal, optIdx) := by
        simp [ρ₁, hcache, hEq, heqT, prngOps, ckaOps, fsMultiDFBucketHsCache,
          fsMultiDFBucketHsEnc, Expr.eval, Expr.v0, Expr.v1]
      rw [eval_caseOpt_some hHonSome, eval_ret]
      simp only [hEq, ↓reduceIte, StateT.run_pure]
      cases optIdx <;>
        simp [ρ₁, hRecv, hFsInitR, prngOps, ckaOps, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · have hHonNone :
          (Expr.caseOpt (O := OO) (.tget (fsMultiDFBucketHsCache (.fst .v0)) (.fst (.snd .v0))) .none
            (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd .v1)))))
              (.some (.snd .v0))
              .none)).eval ρ₁ = none := by
        simp [ρ₁, hcache, hEq, heqT, prngOps, ckaOps, fsMultiDFBucketHsCache,
          fsMultiDFBucketHsEnc, Expr.eval, Expr.v0, Expr.v1]
      rw [eval_caseOpt_none hHonNone]
      simp only [hEq, ↓reduceIte]
      exact hNoneBranch

private theorem fsMultiDFBucketForgedHdrRevealC_eval
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    {Γ'} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) (ρ : Env Γ')
    (h : FSMultiDFBucketState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (hh : hE.eval ρ = hsMBEnc h) (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx)
    (hp : pE.eval ρ = partyEnc P) (hvp : vpE.eval ρ = vpMEnc vp) :
    (fsMultiDFBucketForgedHdrRevealC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L la tL hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) hsMBEnc <$>
        ((hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep false tL par la).reveal
          ctx P vp).run h := by
  unfold fsMultiDFBucketForgedHdrRevealC hooksFSMultiDFBucketPaperMode
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair ctxE (.pair pE vpE))).eval ρ =
      (hsMBEnc h, cGsEnc vpMEnc ctx, partyEnc P, vpMEnc vp) := by
    simp [Expr.eval, hh, hctx, hp, hvp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mbHsTy (.prod (cGsTy mVpTy) (.prod .bool mVpTy)))
    (hsMBEnc h, cGsEnc vpMEnc ctx, partyEnc P, vpMEnc vp) ρ
  rw [eval_ite, orE_eval]
  have hCond :
      ((Expr.not (O := OO) (.lt (vpTcurNat (.snd (.snd (.snd .v0)))) (.nat (healEpoch tL)))).eval ρ₁ ||
        (Expr.not (O := OO) (.lt (maxN (.fst (cGsEpoch (.fst (.snd .v0))))
          (.snd (cGsEpoch (.fst (.snd .v0))))) (.nat (healEpoch tL)))).eval ρ₁) =
      (!(decide (vp.tcur < healEpoch tL)) ||
        !(decide (max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL))) := by
    simp [ρ₁, vpTcurNat, cGsEpoch, cGsEnc, fsMultiVpEnc, vpTblEnc, vpEnc, maxN_eval,
      Expr.eval, Expr.v0]
  rw [hCond]
  by_cases hc :
      (!(decide (vp.tcur < healEpoch tL)) ||
        !(decide (max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL))) = true
  · simp only [hc, ↓reduceIte]
    simp [ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact fsMultiDFBucketRevealC_eval cka prng fs L Δcka Δbucket qep tL par la
      (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))) ρ₁
      h ctx P vp rfl rfl

private theorem hooksFSMultiDFBucketPaperMode_startRecv_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σ0 : RSt) (tn0 : T)
    (h : FSMultiDFBucketState T RSt K I E) :
    ∀ res ∈ support
      (((hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la).startRecv
          ctx P t0 γ0 σ0 tn0).run h),
      (∀ t, (res.2.fTable t).length ≤ (h.fTable t).length + 1) ∧
      (∀ t, (res.2.sessions t).length ≤ (h.sessions t).length + 1) ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  cases gMain
  · exact hooksFSMultiDFBucketPaper_startRecv_preserve L cka prng fs Δcka Δbucket qep tL par la
      ctx P t0 γ0 σ0 tn0 h (out, h') hmem
  · unfold hooksFSMultiDFBucketPaperMode at hmem
    simp only [↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    have hEqH : h' = h := by
      rcases hcache : h.cache t0 with _ | ⟨Tc, σc, kVal, optIdx⟩
      · simp only [hcache] at hmem
        split_ifs at hmem <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
           exact hmem.2)
      · simp only [hcache] at hmem
        by_cases hEq : Tc = tn0
        · simp only [hEq, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          exact hmem.2
        · simp only [hEq, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             exact hmem.2)
    subst hEqH
    exact ⟨fun t => Nat.le_succ _, fun t => Nat.le_succ _, rfl⟩

private theorem hooksFSMultiDFBucketPaperMode_reveal_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (h : FSMultiDFBucketState T RSt K I E) :
    ∀ res ∈ support
      (((hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la).reveal
          ctx P vp).run h),
      res.2.fTable = h.fTable ∧
      res.2.sessions = h.sessions ∧
      fsBookStep 0 h.book res.2.book := by
  intro ⟨out, h'⟩ hmem
  cases gMain
  · unfold hooksFSMultiDFBucketPaperMode at hmem
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
    · exact hooksFSMultiDFBucketPaper_reveal_preserve L cka prng fs Δcka Δbucket qep tL par la
        ctx P vp h (out, h') hmem
  · exact hooksFSMultiDFBucketPaper_reveal_preserve L cka prng fs Δcka Δbucket qep tL par la
      ctx P vp h (out, h') hmem

private theorem hooksFSMultiDFBucketPaperModeC_agrees
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·)) (heqE : eqE = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      hsMBEnc
      (FSMultiDFBucketHBounded L) (HBoundedPost := FSMultiDFBucketHBoundedPost L)
      (VROk := fun _ => True)
      (hooksFSMultiDFBucketPaperModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep gMain tL par la)
      (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la) := by
  have hBase := hooksFSMultiDFBucketPaperC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqM := eqM) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng fs L B Δcka Δbucket qep tL par la
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend heqT heqI heqE
    hSampCCoins hSampI hSampK hFsRecvB
  refine
    { hBounded_post := hBase.hBounded_post
      startSend_eval := hBase.startSend_eval
      startSend_bounded := hBase.startSend_bounded
      startRecv_eval := fun hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh hctx hp => ?_
      startRecv_bounded := fun ctx P t γ σ Tn h hHB res hmem => ?_
      startRecv_vrOk := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
      fsSend_eval := hBase.fsSend_eval
      fsRecv_eval := hBase.fsRecv_eval
      fsRecv_bounded := hBase.fsRecv_bounded
      commit_eval := hBase.commit_eval
      reveal_eval := fun hE ctxE pE vpE ρ h ctx P vp hHB hh hctx hp hvp => ?_ }
  · cases gMain
    · exact hBase.startRecv_eval hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh hctx hp
    · exact fsMultiDFBucketPaperMainStartRecvC_eval cka prng fs hRecv hFsInitR heqT
        L Δcka Δbucket qep tL par la hE ctxE pE tE γE σE tnE ρ h ctx P hh
  · have hB := hooksFSMultiDFBucketPaperMode_startRecv_preserve L cka prng fs Δcka Δbucket qep
      gMain tL par la ctx P t γ σ Tn h res hmem
    unfold FSMultiDFBucketHBoundedPost; rw [hB.2.2]; exact hHB.2.2
  · cases gMain
    · exact fsMultiDFBucketForgedHdrRevealC_eval cka prng fs L Δcka Δbucket qep tL par la
        hE ctxE pE vpE ρ h ctx P vp hh hctx hp hvp
    · exact hBase.reveal_eval hE ctxE pE vpE ρ h ctx P vp hHB hh hctx hp hvp

private theorem implEDFPaperBucketMode_inr_run
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)
      Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (Δ qep maxSkip : ℕ) (cfg : Config M) (gMain : Bool)
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiDFBucketState T RSt K I E))
    (winEp : Option ℕ) :
    (DeliverForge.implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain
        isHonestHdrFSMultiDFBucket (.inr q)).run (es, winEp) =
      (do
        let (r_1, s') ← (DeliverForge.implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr q)).run es
        let winEp' :=
          if (!es.g.win && s'.g.win) = true then
            match q with
            | .inl (.inl (.inr (P, c))) =>
              if (gMain || (decide (c.1.1 = (es.g.st P).tcur + 1) &&
                  !isHonestHdrFSMultiDFBucket es.h c.1)) = true then
                some c.1.1
              else winEp
            | .inr (_, _, c') =>
              if gMain = true then some c'.1.1 else winEp
            | _ =>
              if gMain = true then none else winEp
          else winEp
        pure (r_1, (s', winEp'))) := by
  cases gMain <;>
    rcases q with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩ <;>
    simp only [DeliverForge.implEDFPaperBucketMode, DeliverForge.withWinEpDFMode,
      DeliverForge.withWinEpDF, DeliverForge.dfQueryTargetEpoch, StateT.run_mk, ↓reduceIte,
      Bool.false_eq_true, Bool.true_or, Bool.false_or]

private theorem mem_support_withWinEpDFMode' {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {St Msg Coins T' E' VPt HS : Type}
    (gMain : Bool) (isHonestHdr : HS → Header T' → Bool) (epOf : VPt → ℕ)
    (impl : QueryImpl (unifSpec + SM.specDF St Msg Coins (Header T' × E'))
      (StateT (EState VPt Msg (Header T' × E') HS) (TComp TSpec)))
    (q : (unifSpec + SM.specDF St Msg Coins (Header T' × E')).Domain)
    (es0 es' : EState VPt Msg (Header T' × E') HS) (winEp0 winEp' : Option ℕ)
    (u : (unifSpec + SM.specDF St Msg Coins (Header T' × E')).Range q)
    (hmem : (u, (es', winEp')) ∈
      support ((DeliverForge.withWinEpDFMode gMain isHonestHdr epOf impl q).run (es0, winEp0))) :
    (u, es') ∈ support ((impl q).run es0) := by
  cases gMain
  · unfold DeliverForge.withWinEpDFMode at hmem
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk, mem_support_bind_iff] at hmem
    obtain ⟨⟨r', s'⟩, hr, hp⟩ := hmem
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, _⟩
    exact hr
  · unfold DeliverForge.withWinEpDFMode at hmem
    simp only [↓reduceIte] at hmem
    exact mem_support_withWinEpDF' _ _ impl q es0 winEp0 u es' winEp' hmem

private theorem rdecDF_bucketModeHandleDFPaperC_eval
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δcka Δbucket qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
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
        fs.receive rs hdr e)
    {Γ'}
    (st : Expr OO Γ' mbRedEsTy)
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ')
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiDFBucketState T RSt K I E))
    (winEp : Option ℕ)
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : FSMultiDFBucketHBounded L es.h) (hBound : SMStateBoundedEngine L es.g)
    (hst : st.eval ρ = (esEnc vpMEnc hsMBEnc es, winEp))
    (hq : qE.eval ρ = (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) :
    ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      (bucketModeHandleDFPaperC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep fs.maxSkip gMain la tL par st qE).eval ρ) =
      Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
        (DeliverForge.implEDFPaperBucketMode
          (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
          gMain isHonestHdrFSMultiDFBucket (.inr q)).run (es, winEp) := by
  have hHk := hooksFSMultiDFBucketPaperModeC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqM := eqM) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng fs L B Δcka Δbucket qep gMain tL par la
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend heqT heqI heqE
    hSampCCoins hSampI hSampK hFsRecvB
  have hCfg := bucketParPaperAuthCfgEC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (M := M) Δbucket tL par
  let hkC := hooksFSMultiDFBucketPaperModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep gMain tL par la
  let hk := hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la
  let cfg := bucketAuthCfgGen (Msg := M) Δbucket tL par
  let vpTEnc := @vpTblEnc KC Γ CCoins T I KR RSt K SS RS M E
    (.base CKASort.γ) (.base CKASort.sig) (.sum (.base CKASort.ss) .nat) (.sum (.base CKASort.rs) .nat)
  have hSelfNoFlip : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
  rw [implEDFPaperBucketMode_inr_run]
  unfold bucketModeHandleDFPaperC
  rw [eval_bind_ret]
  have h0 : (Expr.pair (.fst st) (.pair (.snd st) qE)).eval ρ =
      (esEnc vpMEnc hsMBEnc es, winEp,
       (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) := by
    simp [Expr.eval, hst, hq]
  rw [h0]; clear h0
  rcases q with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inl' rfl,
      eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_bind_ret, eval_ite, orE_eval]
    change ((fun p => _) <$> (if (es.abort || es.g.win) = true then _ else _)) =
      Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
        (do
          let (r_1, s') ← (DeliverForge.transmitEBucket hk (2 + Δcka) qep (P, m, r)).run es
          pure (r_1, s',
            if (!es.g.win && s'.g.win) = true then (if gMain = true then none else winEp) else winEp))
    unfold DeliverForge.transmitEBucket abortE
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, eval_ret, StateT.run_pure, pure_bind, map_pure,
        hSelfNoFlip, Bool.false_eq_true]
      rfl
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rw [eval_caseOpt, cEpMgmtE_eval vpTEnc (O' := OO) (2 + Δcka) qep _ _ _ _ es.g P rfl rfl]
      have hR : ∀ {Γ''} (e : Expr OO Γ'' (.opt (.base CKASort.ccoins))) (ρ'' : Env Γ''),
          e.eval ρ'' = r → (isSomeE e).eval ρ'' = r.isSome := by
        intro Γ'' e ρ'' hr; unfold isSomeE; dsimp only [Expr.eval]; rw [hr]; cases r <;> rfl
      rw [hR _ _ rfl]; clear hR
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [Option.map_none, eval_ret, StateT.run_pure, pure_bind, map_pure,
          hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
        rfl
      · simp only [Option.map_some]
        have hw1 : s₁.win = es.g.win := by
          unfold SM.GameState.epMgmt at hep
          by_cases h1 : P.sendsIn (es.g.epoch P + 1)
          · by_cases h2 : qep < es.g.epoch P + 1
            · simp [h1, h2] at hep
            · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hep
              subst hep
              by_cases h3 : (r.isSome && !(es.g.safeCh (2 + Δcka) P)) = true <;>
                simp [h3, SM.GameState.leak]
          · by_cases h2 : qep < es.g.epoch P
            · simp [h1, h2] at hep
            · simp only [h1, Bool.false_eq_true, h2, ↓reduceIte, Option.some.injEq] at hep
              subst hep; rfl
        rw [eval_bind, vSendC_eval hDefaultE hsMBEnc (FSMultiDFBucketHBounded L) hkC hk hHk
          _ _ _ _ _ _ _ _ es.h s₁ P (s₁.st P) m none r hHB
          rfl rfl rfl (by cases P <;> rfl) rfl rfl rfl]
        rw [bind_map_left, map_bind, run_liftH_bind, bind_assoc, map_bind]
        refine bind_congr fun ⟨vsRes, h'⟩ => ?_
        rcases vsRes with _ | ⟨st', ct⟩
        · dsimp only [Option.map_none, Prod.map_apply, id_eq]
          rw [eval_caseOpt_none' rfl]
          simp only [eval_ret, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, map_pure, hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
          rfl
        · dsimp only [Option.map_some, Prod.map_apply, id_eq]
          rw [eval_caseOpt_some' rfl]
          have hNoFlip : (!es.g.win &&
              (s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false).win) = false := by
            simp [SM.GameState.record, hw1]
          simp only [eval_ret, map_pure, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, hNoFlip, Bool.false_eq_true, ↓reduceIte, esMk, pair_eval]
          rw [cRecordE_eval vpTEnc (O' := OO) L (2 + Δcka) _ _ _ _ _ _ s₁ P st'
            ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
            ((epMgmt_lists_eq hep).2.2.1 ▸ hBound.comp_le)
            rfl rfl rfl (by cases P <;> rfl)]
          rfl
  · rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inl' rfl,
      eval_caseSum_inl' rfl, eval_caseSum_inr' rfl]
    change _ = Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
      (do
        let (r_1, s') ← (DeliverForge.challEBucket (P, m₀, m₁, r)).run es
        pure (r_1, s',
          if (!es.g.win && s'.g.win) = true then (if gMain = true then none else winEp) else winEp))
    simp only [DeliverForge.challEBucket, eval_ret, StateT.run_pure, pure_bind, map_pure,
      hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
    rfl
  · rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inl' rfl,
      eval_caseSum_inr' rfl, eval_bind]
    rw [deliverEC_eval hsMBEnc (FSMultiDFBucketHBounded L) hkC hk hHk L fs.maxSkip
          (bucketParPaperAuthCfgEC Δbucket tL par) cfg hCfg heqT heqM heqE
          _ _ _ es P c hHB hBound (fun _ _ _ => trivial) rfl rfl]
    change _ = Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
      (do
        let (r_1, s') ← (deliverE hk fs.maxSkip cfg (P, c)).run es
        pure (r_1, s',
          if (!es.g.win && s'.g.win) = true then (if gMain = true then none else winEp) else winEp))
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine OracleComp.bind_congr_of_forall_mem_support
      ((deliverE hk fs.maxSkip cfg (P, c)).run es) fun ⟨out, es'⟩ hmem => ?_
    have hwinEq := deliverE_win_eq_of_deliverWin_false' hk cfg rfl es (P, c) (out, es') hmem
    have hNoFlip : (!es.g.win && es'.g.win) = false := by rw [hwinEq]; cases es.g.win <;> rfl
    rcases out with _ | (_ | m') <;>
      simp only [eval_ret, pure_bind, hNoFlip, Bool.false_eq_true, ↓reduceIte] <;> rfl
  · rw [eval_caseSum_inl' rfl, eval_caseSum_inl' rfl, eval_caseSum_inr' rfl, eval_bind]
    rw [injectEC_eval hsMBEnc (FSMultiDFBucketHBounded L) hkC hk hHk L (2 + Δcka) qep
          (bucketParPaperAuthCfgEC Δbucket tL par) cfg hCfg heqT heqE
          _ _ _ es P c hHB hBound (fun _ _ _ => trivial) rfl rfl]
    change _ = Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
      (do
        let (r_1, s') ← (injectE hk (2 + Δcka) qep cfg (P, c)).run es
        pure (r_1, s',
          if (!es.g.win && s'.g.win) = true then
            if (gMain || (decide (c.1.1 = (es.g.st P).tcur + 1) &&
                !isHonestHdrFSMultiDFBucket es.h c.1)) = true then
              some c.1.1
            else winEp
          else winEp))
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨out, es'⟩ => ?_
    have hWinCond : ∀ {t0_fst t2 t3 t4_snd : Ty S} {Γ_tail : List (Ty S)}
        (ρ_i : Env (
          .prod t0_fst (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
            (.base CKASort.γ) (.base CKASort.sig)
            (.sum (.base CKASort.ss) .nat) (.sum (.base CKASort.rs) .nat)) mbHsTy) ::
          .prod .bool (.prod (.prod .nat (.opt (.base CKASort.t))) (.base CKASort.ct)) ::
          t2 :: t3 ::
          .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
            (.base CKASort.γ) (.base CKASort.sig)
            (.sum (.base CKASort.ss) .nat) (.sum (.base CKASort.rs) .nat)) mbHsTy) t4_snd :: Γ_tail)),
        (esH (O' := OO) (.fst .v4)).eval ρ_i = hsMBEnc es.h →
        (esG (O' := OO) (.fst .v4)).eval ρ_i = cGsEnc vpMEnc es.g →
        (esG (O' := OO) (.snd .v0)).eval ρ_i = cGsEnc vpMEnc es'.g →
        (Expr.v1 (O := OO)).eval ρ_i = (partyEnc P, c) →
        (Expr.and (O := OO)
          (.and (.not (cGsWin (esG (.fst .v4)))) (cGsWin (esG (.snd .v0))))
          (orE (.bool gMain)
            (.and (.eqN (.fst (.fst (.snd .v1)))
                (.add (vpTcurNat (pGet (cGsSt (esG (.fst .v4))) (.fst .v1))) (.nat 1)))
              (.not (isHonestHdrMultiDFBucketE (esH (.fst .v4)) (.fst (.snd .v1))))))).eval ρ_i =
        ((!es.g.win && es'.g.win) &&
          (gMain || (decide (c.1.1 = (es.g.st P).tcur + 1) &&
            !isHonestHdrFSMultiDFBucket es.h c.1))) :=
      fun ρ_i hh_i hg0_i hg1_i hx_i => by
        rw [and_eval, and_eval, not_eval, orE_eval, and_eval, not_eval]
        have hHon := isHonestHdrMultiDFBucketE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          heqT (esH (.fst .v4)) (.fst (.snd .v1)) ρ_i es.h c.1 hh_i
          (by simp [Expr.eval, hx_i])
        rw [hHon]
        have hTcur :
            (vpTcurNat (pGet (cGsSt (esG (.fst .v4))) (.fst (Expr.v1 (O := OO))))).eval ρ_i =
            (es.g.st P).tcur := by
          cases P <;>
            simp [vpTcurNat, pGet, cGsSt, hg0_i, hx_i, cGsEnc, fsMultiVpEnc, vpTblEnc,
              vpEnc, partyEnc, Expr.eval, Expr.v0, Env.get_cons_zero]
        have hEqEp :
            (Expr.eqN (.fst (.fst (.snd (Expr.v1 (O := OO)))))
              (.add (vpTcurNat (pGet (cGsSt (esG (.fst .v4))) (.fst .v1))) (.nat 1))).eval ρ_i =
            decide (c.1.1 = (es.g.st P).tcur + 1) := by
          change decide (((Expr.fst (.fst (.snd (Expr.v1 (O := OO))))).eval ρ_i) =
            (vpTcurNat (pGet (cGsSt (esG (.fst .v4))) (.fst .v1))).eval ρ_i + 1) = _
          rw [hTcur]
          simp [Expr.eval, hx_i]
        rw [hEqEp]
        simp [cGsWin, hg0_i, hg1_i, cGsEnc, Expr.eval]
    have hIfAnd : ∀ {α : Type} (b1 b2 : Bool) (thn els : α),
        (if (b1 && b2) = true then thn else els) =
        (if b1 = true then if b2 = true then thn else els else els) :=
      fun b1 b2 _ _ => by cases b1 <;> cases b2 <;> rfl
    rcases out with _ | (_ | m') <;>
      (simp only [eval_ret, pure_bind, Function.comp_apply, pair_eval, ite_eval];
       rw [hWinCond _ rfl rfl rfl rfl, hIfAnd];
       rfl)
  · rw [eval_caseSum_inl' rfl, eval_caseSum_inr' rfl, eval_ite, orE_eval, orE_eval, not_eval,
      cCorrAllowedPaperE_eval vpTEnc (O' := OO) L _ _ _ es.g P hBound.chall_le rfl rfl]
    change ((fun p => _) <$>
      (if (es.abort || (es.g.win || !es.g.corrAllowedPaper P)) = true then _ else _)) =
      Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
        (do
          let (r_1, s') ← (DeliverForge.corrEPaperBucket hk P).run es
          pure (r_1, s',
            if (!es.g.win && s'.g.win) = true then (if gMain = true then none else winEp) else winEp))
    rw [← Bool.or_assoc]
    unfold DeliverForge.corrEPaperBucket abortE
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, eval_ret, StateT.run_pure, pure_bind, map_pure,
        hSelfNoFlip, Bool.false_eq_true]
      rfl
    · simp only [href, Bool.false_eq_true, ↓reduceIte, eval_bind]
      change ((fun p => _) <$>
        (((hooksFSMultiDFBucketPaperModeC L B Δcka Δbucket qep gMain tL par la).reveal
          (esH (.fst .v2)) (esG (.fst .v2)) .v0 (pGet (cGsSt (esG (.fst .v2))) .v0)).eval _ >>= _)) = _
      rw [hHk.reveal_eval _ _ _ _ _ es.h es.g P (es.g.st P) hHB rfl rfl rfl (by cases P <;> rfl),
        bind_map_left, map_bind, run_liftH_bind, bind_assoc, map_bind]
      refine bind_congr fun ⟨revRes, h'⟩ => ?_
      rcases revRes with _ | stOut
      · dsimp only [Option.map_none, Prod.map_apply, id_eq]
        rw [eval_caseOpt_none' rfl]
        simp only [eval_ret, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, map_pure, hSelfNoFlip, Bool.false_eq_true, ↓reduceIte]
        rfl
      · dsimp only [Option.map_some, Prod.map_apply, id_eq]
        rw [eval_caseOpt_some' rfl]
        have hNoFlip : (!es.g.win && (es.g.afterCorr P).win) = false := by
          simp [SM.GameState.afterCorr, SM.GameState.leak]
        simp only [eval_ret, map_pure, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, hNoFlip, Bool.false_eq_true, ↓reduceIte, esMk, pair_eval]
        rw [cAfterCorrE_eval vpTEnc (O' := OO) L _ _ _ es.g P
          hBound.trans_le hBound.comp_u rfl rfl]
        simp [Expr.eval, Expr.v0, Expr.v1, Expr.v4, esAbort, esEnc, vpTEnc]
  · rw [eval_caseSum_inr' rfl, eval_bind]
    rw [deliverForgeEC_eval hsMBEnc (FSMultiDFBucketHBounded L) hkC hk hHk L (2 + Δcka) qep
          (bucketParPaperAuthCfgEC Δbucket tL par) cfg hCfg heqT heqE
          _ _ _ es P c c' hHB hBound (fun _ _ _ => trivial) rfl rfl]
    change _ = Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
      (do
        let (r_1, s') ← (DeliverForge.deliverForgeE hk (2 + Δcka) qep cfg (P, c, c')).run es
        pure (r_1, s',
          if (!es.g.win && s'.g.win) = true then
            if gMain = true then some c'.1.1 else winEp
          else winEp))
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨out, es'⟩ => ?_
    have hWinDF : ∀ {t0_fst t1 t2_snd : Ty S} {Γ_tail : List (Ty S)}
        (ρ_d : Env (
          .prod t0_fst (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
            (.base CKASort.γ) (.base CKASort.sig)
            (.sum (.base CKASort.ss) .nat) (.sum (.base CKASort.rs) .nat)) mbHsTy) ::
          t1 ::
          .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
            (.base CKASort.γ) (.base CKASort.sig)
            (.sum (.base CKASort.ss) .nat) (.sum (.base CKASort.rs) .nat)) mbHsTy) t2_snd :: Γ_tail)),
        (esG (O' := OO) (.fst .v2)).eval ρ_d = cGsEnc vpMEnc es.g →
        (esG (O' := OO) (.snd .v0)).eval ρ_d = cGsEnc vpMEnc es'.g →
        (Expr.and (O := OO)
          (.and (.not (cGsWin (esG (.fst .v2)))) (cGsWin (esG (.snd .v0))))
          (.bool gMain)).eval ρ_d =
        ((!es.g.win && es'.g.win) && gMain) := fun ρ_d hg0_d hg1_d => by
      simp [cGsWin, hg0_d, hg1_d, cGsEnc, Expr.eval]
    have hIfDF : ∀ {α : Type} (tBranch eBranch : α),
        (if ((!es.g.win && es'.g.win) && gMain) = true then tBranch else eBranch) =
        (if (!es.g.win && es'.g.win) = true then
          if gMain = true then tBranch else eBranch
        else eBranch) := fun _ _ => by
      cases (!es.g.win && es'.g.win) <;> cases gMain <;> rfl
    rcases out with _ | (_ | m') <;>
      (simp only [eval_ret, pure_bind, Function.comp_apply, pair_eval, ite_eval];
       rw [hWinDF _ rfl rfl, hIfDF];
       rfl)

private theorem commitE_fsMultiDFBucketMode_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool) :
    commitE (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la) =
      commitE (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la) := rfl

private theorem implEDFPaperBucketRaw_mode_stepBounded
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L B_q : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {m Δ qep maxSkip : ℕ} (cfg : Config M) (Δcka Δbucket : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiDFBucketState T RSt K I E))
    (q_df : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B_q (m + 1) es.g)
    (hPre : FSMultiDFBucketStepBounded B_q (m + 1) es.h) :
    ∀ res ∈ support ((DeliverForge.implEDFPaperBucketRaw
      (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
      Δ qep maxSkip cfg (.inr q_df)).run es),
      FSMultiDFBucketStepBounded B_q m res.2.h := by
  have hm1B : m + 1 ≤ B_q := by have := hInv.leaks_le; omega
  have hPost0 : FSMultiDFBucketStepBounded B_q m es.h := hPre.mono (Nat.le_succ m)
  let HPre : FSMultiDFBucketState T RSt K I E → Prop := FSMultiDFBucketStepBounded B_q (m + 1)
  let HMid : FSMultiDFBucketState T RSt K I E → Prop := fun h =>
    (∀ t, (h.fTable t).length + m ≤ B_q + 1) ∧
    (∀ t, (h.sessions t).length + m ≤ B_q + 1) ∧
    ∀ idx bk, h.book idx = some bk → bk.fsTrans.length + (m + 1) ≤ B_q
  let HPost : FSMultiDFBucketState T RSt K I E → Prop := FSMultiDFBucketStepBounded B_q m
  have hMid0 : HPre es.h → HMid es.h := fun hp =>
    ⟨fun t => by have := hp.1 t; omega, fun t => by have := hp.2.1 t; omega, hp.2.2⟩
  have hMidPost : ∀ {h1}, HMid h1 → HPost h1 := fun hm =>
    ⟨hm.1, hm.2.1, fun idx bk hbk => by have := hm.2.2 idx bk hbk; omega⟩
  have hvSend : ∀ ctx P s msg pair r res,
      res ∈ support ((vSend (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
        ctx P s msg pair r).run es.h) → HPost res.2 := by
    intro ctx P s msg pair r res hmem
    refine (vSend_preserve_generic
      (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
      ctx P s msg pair r es.h hPre hMid0 hMidPost
      (fun t0 γ0 σ0 r0 res' hp hss => ?_)
      (fun {h1} t1 v hHdr m' pair' res' hm hfs => ?_) res hmem).1
    · have hP := hooksFSMultiDFBucketPaper_startSend_preserve L cka prng fs Δcka Δbucket qep
        tL par la ctx P t0 γ0 σ0 r0 es.h res' hss
      refine ⟨fun t' => by have := hp.1 t'; have := hP.1 t'; omega,
        fun t' => by have := hp.2.1 t'; have := hP.2.1 t'; omega, ?_⟩
      rw [hP.2.2]; exact hp.2.2
    · have hP := hooksFSMultiDFBucketPaper_fsSend_preserve L cka prng fs Δcka Δbucket qep
        tL par la ctx P t1 v hHdr m' pair' h1 res' hfs
      refine ⟨by rw [hP.1]; exact hm.1, by rw [hP.2.1]; exact hm.2.1,
        fsBookStep_apply hm1B hm.2.2 hP.2.2⟩
  have hvRecv : ∀ ctx P s c rec res,
      res ∈ support ((vRecv (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
        ctx P s c rec).run es.h) → HPost res.2 := by
    intro ctx P s c rec res hmem
    refine vRecv_preserve_h_only
      (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
      ctx P s c rec es.h hPre hMid0 hMidPost
      (fun t0 γ0 σ0 Tn res' hp hsr => ?_)
      (fun {h1} t1 v hHdr e rec' res' hm hfr => ?_) res hmem
    · have hP := hooksFSMultiDFBucketPaperMode_startRecv_preserve L cka prng fs Δcka Δbucket qep
        gMain tL par la ctx P t0 γ0 σ0 Tn es.h res' hsr
      refine ⟨fun t' => by have := hp.1 t'; have := hP.1 t'; omega,
        fun t' => by have := hp.2.1 t'; have := hP.2.1 t'; omega, ?_⟩
      rw [hP.2.2]; exact hp.2.2
    · have hP := hooksFSMultiDFBucketPaper_fsRecv_preserve L cka prng fs Δcka Δbucket qep
        tL par la ctx P t1 v hHdr e rec' h1 res' hfr
      refine ⟨by rw [hP.1]; exact hm.1, by rw [hP.2.1]; exact hm.2.1,
        fsBookStep_apply hm1B hm.2.2 (fsBookStep_mono (Nat.zero_le 1) hP.2.2)⟩
  intro ⟨out, es'⟩ hmem
  rcases q_df with ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (out, es') ∈ support ((DeliverForge.transmitEBucket _ Δ qep (P, msg, r)).run es) at hmem
    unfold DeliverForge.transmitEBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hPost0
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hPost0
      · simp only [hep, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
        have hPres := hvSend s₁ P (s₁.st P) msg none r (vsRes, h') hvs
        rcases vsRes with _ | ⟨st', ct⟩ <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
           rcases hmem with ⟨_, rfl⟩; exact hPres)
  · change (out, es') ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hPost0
  · change (out, es') ∈ support ((deliverE _ maxSkip cfg (P, c)).run es) at hmem
    unfold deliverE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hPost0
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hPost0
      · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hPres := hvRecv es.g P (es.g.st P) c (some r) (vrRes, h') hvr
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hPres
        · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r) <;>
            (simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
              StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; exact hPres)
        · simp only [StateT.run_bind, commitE_fsMultiDFBucketMode_eq, commitE_fsMultiDFBucket_eq,
            pure_bind, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hPres
  · change (out, es') ∈ support ((injectE _ Δ qep cfg (P, c)).run es) at hmem
    unfold injectE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hPost0
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      have hPres := hvRecv es.g P (es.g.st P) c none (vrRes, h') hvr
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hPres
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hPres
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hPres
        · simp only [hqep, ↓reduceIte] at hmem
          by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMultiDFBucketMode_eq,
              commitE_fsMultiDFBucket_eq, pure_bind, StateT.run_modify, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hPres
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases hf : cfg.injectFull t' <;>
              (simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
               rcases hmem with ⟨_, rfl⟩; exact hPres)
  · change (out, es') ∈ support ((DeliverForge.corrEPaperBucket _ P).run es) at hmem
    unfold DeliverForge.corrEPaperBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hPost0
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, hrev, hmem⟩ := hmem
      have hP := hooksFSMultiDFBucketPaperMode_reveal_preserve L cka prng fs Δcka Δbucket qep
        gMain tL par la es.g P (es.g.st P) es.h (revRes, h') hrev
      have hFsLe := fsBookStep_apply hm1B hPre.2.2 (fsBookStep_mono (Nat.zero_le 1) hP.2.2)
      rcases revRes with _ | st <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         rcases hmem with ⟨_, rfl⟩;
         exact ⟨by dsimp only; rw [hP.1]; exact hPost0.1,
           by dsimp only; rw [hP.2.1]; exact hPost0.2.1, hFsLe⟩)
  · change (out, es') ∈ support ((DeliverForge.deliverForgeE _ Δ qep cfg (P, c, c')).run es) at hmem
    unfold DeliverForge.deliverForgeE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hPost0
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hPost0
      · simp only [htr] at hmem
        by_cases hbad :
            ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
        · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hPost0
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte,
            run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
          have hPres := hvRecv es.g P (es.g.st P) c' none (vrRes, h') hvr
          rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hPres
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hPres
          · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
            · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hPres
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
              · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMultiDFBucketMode_eq,
                  commitE_fsMultiDFBucket_eq, pure_bind, StateT.run_modify, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hPres
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                by_cases hf : cfg.injectFull t' <;>
                  (simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                    StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
                    Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
                   rcases hmem with ⟨_, rfl⟩; exact hPres)

private theorem simulateQ_implEDFPaperBucketMode_multi_eval
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka Δbucket qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
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
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
          (FSMultiDFBucketState T RSt K I E))
        (winEp : Option ℕ),
        FSMultiDFBucketStepBounded B_q qAdv es.h → SMEngineInv L B_q qAdv es.g →
        (simulateQ
          (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (bucketModeHandleDFPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK)
              L B Δcka Δbucket qep fs.maxSkip gMain la tL par .v0 .v1)) oa).run
          (esEnc vpMEnc hsMBEnc es, winEp) =
          (Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
            (simulateQ (DeliverForge.implEDFPaperBucketMode
              (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
              (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
              gMain isHonestHdrFSMultiDFBucket) oa).run (es, winEp)) ∧
        ∀ res ∈ support ((simulateQ (DeliverForge.implEDFPaperBucketMode
            (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
            (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
            gMain isHonestHdrFSMultiDFBucket) oa).run (es, winEp)),
          SMEngineInv L B_q 0 res.2.1.g := by
  let hk := hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la
  let handleComp := bucketModeHandleDFPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    L B Δcka Δbucket qep fs.maxSkip gMain la tL par
    (Γ' := [mbRedEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es winEp _ hInv
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact hInv.mono (Nat.zero_le qAdv)
  | query_bind q mx ih =>
    intro qAdv hq es winEp hHB hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp)
            (.inl n)).run (esEnc vpMEnc hsMBEnc es, winEp) =
          (fun u => (u, (esEnc vpMEnc hsMBEnc es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        simp [handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (DeliverForge.implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfgGen Δbucket tL par) gMain isHonestHdrFSMultiDFBucket (.inl n)).run
            (es, winEp) =
          (fun u => (u, (es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        cases gMain <;>
          simp [DeliverForge.implEDFPaperBucketMode, DeliverForge.withWinEpDFMode,
            DeliverForge.withWinEpDF, DeliverForge.implEDFPaperBucketRaw, coinsE,
            StateT.run_mk, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es winEp hHB hInv).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es winEp hHB hInv).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hStepEval := rdecDF_bucketModeHandleDFPaperC_eval
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
        (lam := lam) (sampKR := sampKR) (sampKC := sampKC)
        cka prng fs L B Δcka Δbucket qep gMain la tL par
        hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
        heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK hFsRecvB .v0 .v1
        (.cons (esEnc vpMEnc hsMBEnc es, winEp)
          (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))
        es winEp t (hHB.toHBounded hB1) hInv.toBoundedEngine rfl rfl
      have hStep :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp)
            (.inr t)).run (esEnc vpMEnc hsMBEnc es, winEp) =
          Prod.map id (Prod.map (esEnc vpMEnc hsMBEnc) id) <$>
            (DeliverForge.implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip
              (bucketAuthCfgGen Δbucket tL par) gMain isHonestHdrFSMultiDFBucket (.inr t)).run
              (es, winEp) := by
        have hLHS :
            ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp)
              (.inr t)).run (esEnc vpMEnc hsMBEnc es, winEp) =
            ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec t p.1, p.2)) <$>
              handleComp.eval (.cons (esEnc vpMEnc hsMBEnc es, winEp)
                (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))) := by
          simp only [handlerImpl, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def]
        exact hLHS.trans hStepEval
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁, winEp₁⟩ hmem => ?_, ?_⟩
      · have hmemRaw := mem_support_withWinEpDFMode' gMain isHonestHdrFSMultiDFBucket
          (fun vp => vp.tcur)
          (DeliverForge.implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfgGen Δbucket tL par))
          (.inr t) es es₁ winEp winEp₁ u hmem
        exact (ih u (hqm u) es₁ winEp₁
          (implEDFPaperBucketRaw_mode_stepBounded L B_q cka prng fs
            (bucketAuthCfgGen Δbucket tL par) Δcka Δbucket gMain tL par la es t hInv hHB
            (u, es₁) hmemRaw)
          (implEDFPaperBucketRaw_inv_sm hk (bucketAuthCfgGen Δbucket tL par)
            es t hInv (u, es₁) hmemRaw)).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁, winEp₁⟩, hmem₁, hmem₂⟩ := hmem
        have hmemRaw := mem_support_withWinEpDFMode' gMain isHonestHdrFSMultiDFBucket
          (fun vp => vp.tcur)
          (DeliverForge.implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfgGen Δbucket tL par))
          (.inr t) es es₁ winEp winEp₁ u hmem₁
        exact (ih u (hqm u) es₁ winEp₁
          (implEDFPaperBucketRaw_mode_stepBounded L B_q cka prng fs
            (bucketAuthCfgGen Δbucket tL par) Δcka Δbucket gMain tL par la es t hInv hHB
            (u, es₁) hmemRaw)
          (implEDFPaperBucketRaw_inv_sm hk (bucketAuthCfgGen Δbucket tL par)
            es t hInv (u, es₁) hmemRaw)).2 res hmem₂

private theorem engRunDFPaperBucketMode_initFSMultiDFBucketPaper_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    DeliverForge.engRunDFPaperBucketMode
      (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par) gMain isHonestHdrFSMultiDFBucket
      (initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par) {} b A =
      (do
        let es₀ ← initFSMultiDFBucketPaperRaw L cka prng fs lam Δbucket qep tL par b
        let res ← (simulateQ (DeliverForge.implEDFPaperBucketMode
          (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
          gMain isHonestHdrFSMultiDFBucket) A).run (es₀, none)
        return some res) := by
  unfold DeliverForge.engRunDFPaperBucketMode initFSMultiDFBucketPaper initFSMultiDFBucketPaperRaw
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure,
    bind_assoc, pure_bind]
  refine bind_congr fun kr => bind_congr fun kc => bind_congr fun ⟨⟨σ, kVal, sid⟩, h₁⟩ => ?_
  rfl

end ModeEvalHelpers

/-- Evaluation bridge for `redFSAuthDFPaperMultiBucketModeProgGen` on `fsClamp B fs`. -/
theorem redFSAuthDFPaperMultiBucketModeProgGen_eval_clamp
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
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka Δbucket qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
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
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthDFPaperMultiBucketModeProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep fs.maxSkip gMain la tL par).eval (fun _ => A) () =
      redFSAuthDFPaperMultiBucketModeGen L cka prng (fsClamp B fs) lam Δcka Δbucket qep
        gMain la tL par A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hInit := initFSMultiDFBucketPaperEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L Δbucket qep tL par (.bool false)
    (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redFSAuthDFPaperMultiBucketModeProgGen CostedReduction.impl
    redFSAuthDFPaperMultiBucketModeGen
  dsimp only
  rw [eval_bind, hInit, engRunDFPaperBucketMode_initFSMultiDFBucketPaper_eq]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSMultiDFBucketPaperRaw L cka prng (fsClamp B fs) lam Δbucket qep tL par false)
    fun es₀ hes₀ => ?_
  have ⟨hHB₀, hInv₀⟩ := initFSMultiDFBucketPaperRaw_inv L B_q qAdv cka prng (fsClamp B fs)
    lam Δbucket qep tL par false hqB hB1 hBB es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_implEDFPaperBucketMode_multi_eval
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    cka prng (fsClamp B fs) L B B_q Δcka Δbucket qep gMain la tL par hB1
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ none hHB₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  rw [hms] at hSim
  let IIM := fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
  let vpMEnc := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let hsBEnc := fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  change (do
    let x ← (simulateQ (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      (bucketModeHandleDFPaperC
        L B Δcka Δbucket qep fs.maxSkip gMain la tL par .v0 .v1)) A).run
      (esEnc vpMEnc hsBEnc es₀, none)
    (bucketFinishPaperMultiE (I' := IIM) L (2 + Δcka) la tL .v0).eval
      (Env.cons x.2 (Env.cons (t := .bool) x.1 .nil))) = _
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es', winEp'⟩ hes' => ?_
  have hBnd' := (hSimInv (b', (es', winEp')) hes').toBoundedEngine
  have hOut := bucketFinishPaperMultiE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (I' := IIM) L (2 + Δcka) la tL .v0
    (Env.cons (t := fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E)
      (esEnc vpMEnc hsBEnc es', winEp') (Env.cons (t := .bool) b' .nil))
    es' winEp' hBnd'.leaks_le hBnd'.corrs_le rfl
  simpa [Prod.map] using hOut

private theorem hooksFSMultiDFBucketPaperMode_startRecv_step {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party) (t0 : ℕ) (γ0 : Γ) (σ0 : RSt) (tn0 : T)
    (h : FSMultiDFBucketState T RSt K I (ℕ × C)) (res)
    (hmem : res ∈ support
      (((hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep gMain tL par la).startRecv ctx P t0 γ0 σ0 tn0).run h))
    (γ' : Γ) (σ' : RSt) (rsv : FSAEAD.RatchetReceiverState K MK ⊕ ℕ)
    (hEq : res.1 = some (some (γ', σ', rsv))) :
    FSVROkMultiStep maxSkip 0 rsv := by
  cases gMain
  · exact hooksFSMultiDFBucketPaper_startRecv_step L cka prng ae G maxSkip Δcka Δbucket qep
      tL par la ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rsv hEq
  · rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    unfold hooksFSMultiDFBucketPaperMode at hmem
    simp only [↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hcache : h.cache t0 with _ | ⟨Tc, σc, k, optIdx⟩
    · simp only [hcache] at hmem
      split_ifs at hmem <;> simp [StateT.run_pure] at hmem
    · by_cases hTc : Tc = tn0
      · simp only [hcache, hTc, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨⟨_, _, hrsv⟩, _⟩
        subst hrsv
        rcases optIdx with _ | sIdx
        · exact RSReach.init ae G maxSkip k
        · trivial
      · simp only [hcache, hTc, ↓reduceIte] at hmem
        split_ifs at hmem <;> simp [StateT.run_pure] at hmem

private theorem vRecvStep1_hooksFSMultiDFBucketPaperMode_vrOk {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party)
    (s : VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ))
    (c : Header T × (ℕ × C))
    (h : FSMultiDFBucketState T RSt K I (ℕ × C))
    (hVR : ∀ t v, s.vR t = some v → FSVROkMultiStep maxSkip k v) :
    ∀ res ∈ support
      ((vRecvStep1 (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep gMain tL par la) ctx P s c).run h),
      ∀ s₁, res.1 = some (some s₁) → ∀ t v, s₁.vR t = some v → FSVROkMultiStep maxSkip k v := by
  intro ⟨s₁?, h₁⟩ hmem s₁ hs₁ t₀ v₀ hv₀
  unfold vRecvStep1 at hmem
  by_cases ht : c.1.1 = s.tcur + 1
  · simp only [ht, ↓reduceIte] at hmem
    rcases hTn : c.1.2 with _ | Tn
    · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, _⟩; cases hs₁
    · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨srRes, h'⟩, hsr, hmem⟩ := hmem
      rcases srRes with _ | _ | ⟨γ', σ', rs⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩; cases hs₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩; cases hs₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        cases hs₁
        by_cases ht₀ : t₀ = s.tcur + 1
        · subst ht₀
          simp only [Function.update_self, Option.some.injEq] at hv₀
          subst hv₀
          exact (hooksFSMultiDFBucketPaperMode_startRecv_step L cka prng ae G maxSkip Δcka Δbucket qep
            gMain tL par la ctx P (s.tcur + 1) s.γ s.root Tn h
            (some (some (γ', σ', rs)), h₁) hsr γ' σ' rs rfl).mono (Nat.zero_le k)
        · simp only [Function.update_of_ne ht₀] at hv₀
          exact hVR t₀ v₀ hv₀
  · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, _⟩
    cases hs₁
    exact hVR t₀ v₀ hv₀

private theorem vRecv_fsClamp_multiDFBucketMode_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B k Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (hB : (k + 1) * (maxSkip + 1) ≤ B)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party)
    (s : VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ))
    (c : Header T × (ℕ × C)) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSMultiDFBucketState T RSt K I (ℕ × C))
    (hVR : ∀ t v, s.vR t = some v → FSVROkMultiStep maxSkip k v) :
    (vRecv (hooksFSMultiDFBucketPaperMode L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        Δcka Δbucket qep gMain tL par la) ctx P s c rec_).run h =
      (vRecv (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        Δcka Δbucket qep gMain tL par la) ctx P s c rec_).run h := by
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1))
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hStep1 :
        vRecvStep1
          (hooksFSMultiDFBucketPaperMode L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
            Δcka Δbucket qep gMain tL par la) ctx P s c =
        vRecvStep1
          (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
            Δcka Δbucket qep gMain tL par la) ctx P s c := by
      unfold vRecvStep1; cases gMain <;> rfl
    rw [hStep1]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨s₁?, h₁⟩ hmem => ?_
    have hVR₁ := vRecvStep1_hooksFSMultiDFBucketPaperMode_vrOk L cka prng ae G maxSkip k
      Δcka Δbucket qep gMain tL par la ctx P s c h hVR (s₁?, h₁) hmem
    rcases s₁? with _ | (_ | s₁)
    · rfl
    · rfl
    · rcases hvRc : s₁.vR c.1.1 with _ | v
      · simp only [hvRc]
      · simp only [hvRc, StateT.run_bind]
        exact congrArg (· >>= _) (hooksFSMultiDFBucketPaper_fsRecv_fsClamp_eq L cka prng ae G
          maxSkip B k Δcka Δbucket qep tL par la hB ctx P c.1.1 v c.1 c.2 rec_ h₁
          (hVR₁ s₁ rfl c.1.1 v hvRc))

private theorem hooksFSMultiDFBucketPaperMode_vrInv_fromAEADPRG {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool) :
    HooksVRInv (FSVROkMultiStep maxSkip)
      (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        Δcka Δbucket qep gMain tL par la) :=
  let hBase := hooksFSMultiDFBucketPaper_vrInv_fromAEADPRG L cka prng ae G maxSkip
    Δcka Δbucket qep tL par la
  { mono := fun hle hv => hv.mono hle
    startRecv_step := hooksFSMultiDFBucketPaperMode_startRecv_step L cka prng ae G maxSkip
      Δcka Δbucket qep gMain tL par la
    fsRecv_step := hBase.fsRecv_step
    commit_vR := hBase.commit_vR }

private theorem implEDFPaperBucketRaw_mode_fsClamp_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q q Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool) (cfg : Config M)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiDFBucketState T RSt K I (ℕ × C)))
    (t : (SM.specDF (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q (q + 1) es.g) :
    (DeliverForge.implEDFPaperBucketRaw
        (hooksFSMultiDFBucketPaperMode L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
          Δcka Δbucket qep gMain tL par la)
        (2 + Δcka) qep maxSkip cfg (.inr t)).run es =
      (DeliverForge.implEDFPaperBucketRaw
        (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep gMain tL par la)
        (2 + Δcka) qep maxSkip cfg (.inr t)).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (DeliverForge.transmitEBucket _ (2 + Δcka) qep (P, m, r)).run es =
      (DeliverForge.transmitEBucket _ (2 + Δcka) qep (P, m, r)).run es
    have hvS :
        vSend (hooksFSMultiDFBucketPaperMode L cka prng
          (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka Δbucket qep gMain tL par la) =
        vSend (hooksFSMultiDFBucketPaperMode L cka prng
          (FSAEAD.fromAEADPRG ae G maxSkip) Δcka Δbucket qep gMain tL par la) :=
      vSend_hooksFSMultiDFBucketPaper_fsClamp_eq L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        B Δcka Δbucket qep tL par la
    unfold DeliverForge.transmitEBucket
    rw [hvS]
  · change (DeliverForge.challEBucket (P, m₀, m₁, r)).run es =
      (DeliverForge.challEBucket (P, m₀, m₁, r)).run es
    rfl
  · change (deliverE _ maxSkip cfg (P, c)).run es = (deliverE _ maxSkip cfg (P, c)).run es
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind]
        rw [vRecv_fsClamp_multiDFBucketMode_eq L cka prng ae G maxSkip B (B_q - (q + 1))
          Δcka Δbucket qep gMain tL par la hkB es.g P (es.g.st P) c (some r) es.h (hVR P)]
        rfl
  · change (injectE _ (2 + Δcka) qep cfg (P, c)).run es =
      (injectE _ (2 + Δcka) qep cfg (P, c)).run es
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka)))
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
      rw [vRecv_fsClamp_multiDFBucketMode_eq L cka prng ae G maxSkip B (B_q - (q + 1))
        Δcka Δbucket qep gMain tL par la hkB es.g P (es.g.st P) c none es.h (hVR P)]
      rfl
  · change (DeliverForge.corrEPaperBucket _ P).run es =
      (DeliverForge.corrEPaperBucket _ P).run es
    have hrev :
        (hooksFSMultiDFBucketPaperMode L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
          Δcka Δbucket qep gMain tL par la).reveal =
        (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep gMain tL par la).reveal := by
      cases gMain <;> rfl
    unfold DeliverForge.corrEPaperBucket
    rw [hrev]
  · change (DeliverForge.deliverForgeE _ (2 + Δcka) qep cfg (P, c, c')).run es =
      (DeliverForge.deliverForgeE _ (2 + Δcka) qep cfg (P, c, c')).run es
    unfold DeliverForge.deliverForgeE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · rfl
      · dsimp only
        by_cases hbad :
            ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
        · simp only [hbad, ↓reduceIte]
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
          rw [vRecv_fsClamp_multiDFBucketMode_eq L cka prng ae G maxSkip B (B_q - (q + 1))
            Δcka Δbucket qep gMain tL par la hkB es.g P (es.g.st P) c' none es.h (hVR P)]
          rfl

private theorem simulateQ_implEDFPaperBucketMode_multi_fsClamp_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool) (cfg : Config M)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    {α : Type} {oa : OracleComp (unifSpec + SM.specDF
      (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
      M CCoins (Header T × (ℕ × C))) α}
    {q : ℕ}
    (hoa : oa.IsQueryBoundP
      (isGameQuery (G := SM.specDF
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) q)
    (st : EState (VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiDFBucketState T RSt K I (ℕ × C)) × Option ℕ)
    (hInv : SMEngineInv L B_q q st.1.g)
    (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q q st.1.g) :
    (simulateQ (DeliverForge.implEDFPaperBucketMode
        (hooksFSMultiDFBucketPaperMode L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
          Δcka Δbucket qep gMain tL par la)
        (2 + Δcka) qep maxSkip cfg gMain isHonestHdrFSMultiDFBucket) oa).run st =
      (simulateQ (DeliverForge.implEDFPaperBucketMode
        (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep gMain tL par la)
        (2 + Δcka) qep maxSkip cfg gMain isHonestHdrFSMultiDFBucket) oa).run st := by
  induction oa using OracleComp.inductionOn generalizing q st with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rcases st with ⟨es, winEp⟩
    rw [isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    rcases qy with n | t_df
    · have hCoinL :
          (DeliverForge.implEDFPaperBucketMode
            (hooksFSMultiDFBucketPaperMode L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
              Δcka Δbucket qep gMain tL par la)
            (2 + Δcka) qep maxSkip cfg gMain isHonestHdrFSMultiDFBucket (.inl n)).run (es, winEp) =
          (fun u => (u, (es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec (FSAEAD.RatchetSenderState K)
              (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) (.inl n) := by
        cases gMain <;>
          simp [DeliverForge.implEDFPaperBucketMode, DeliverForge.withWinEpDFMode,
            DeliverForge.withWinEpDF, DeliverForge.implEDFPaperBucketRaw, coinsE,
            StateT.run_mk, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc]
      have hCoinR :
          (DeliverForge.implEDFPaperBucketMode
            (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka Δbucket qep gMain tL par la)
            (2 + Δcka) qep maxSkip cfg gMain isHonestHdrFSMultiDFBucket (.inl n)).run (es, winEp) =
          (fun u => (u, (es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec (FSAEAD.RatchetSenderState K)
              (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) (.inl n) := by
        cases gMain <;>
          simp [DeliverForge.implEDFPaperBucketMode, DeliverForge.withWinEpDFMode,
            DeliverForge.withWinEpDF, DeliverForge.implEDFPaperBucketRaw, coinsE,
            StateT.run_mk, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u (hmx u) (es, winEp) hInv hVR
    · have hqp : 0 < q := hq0.resolve_left (by simp [isGameQuery])
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hStep :
          (DeliverForge.implEDFPaperBucketMode
            (hooksFSMultiDFBucketPaperMode L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
              Δcka Δbucket qep gMain tL par la)
            (2 + Δcka) qep maxSkip cfg gMain isHonestHdrFSMultiDFBucket (.inr t_df)).run (es, winEp) =
          (DeliverForge.implEDFPaperBucketMode
            (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka Δbucket qep gMain tL par la)
            (2 + Δcka) qep maxSkip cfg gMain isHonestHdrFSMultiDFBucket (.inr t_df)).run (es, winEp) := by
        rw [implEDFPaperBucketMode_inr_run, implEDFPaperBucketMode_inr_run,
          implEDFPaperBucketRaw_mode_fsClamp_eq L cka prng ae G maxSkip B B_q q' Δcka Δbucket qep
            gMain tL par la cfg hB es t_df hVR]
      rw [hStep]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, ⟨es', winEp'⟩⟩ hmem => ?_
      have hmem₁ := mem_support_withWinEpDFMode' gMain isHonestHdrFSMultiDFBucket (fun s => s.tcur)
        (DeliverForge.implEDFPaperBucketRaw
          (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
            Δcka Δbucket qep gMain tL par la)
          (2 + Δcka) qep maxSkip cfg) (.inr t_df) es es' winEp winEp' u hmem
      have hInv' := implEDFPaperBucketRaw_inv
        (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep gMain tL par la) cfg es t_df hInv (u, es') hmem₁
      have hVR' := implEDFPaperBucketRaw_vrInv
        (hooksFSMultiDFBucketPaperMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka Δbucket qep gMain tL par la)
        (hooksFSMultiDFBucketPaperMode_vrInv_fromAEADPRG L cka prng ae G maxSkip Δcka Δbucket qep
          gMain tL par la) cfg es t_df hInv hVR (u, es') hmem₁
      exact ih u (hmx u) (es', winEp') hInv' hVR'

/-- `fsClamp B` removal for `redFSAuthDFPaperMultiBucketModeGen` on `FSAEAD.fromAEADPRG`. -/
theorem redFSAuthDFPaperMultiBucketModeGen_fsClamp_fromAEADPRG {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka Δbucket qep : ℕ)
    (lam : I) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    redFSAuthDFPaperMultiBucketModeGen L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        lam Δcka Δbucket qep gMain la tL par A =
      redFSAuthDFPaperMultiBucketModeGen L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka Δbucket qep gMain la tL par A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  unfold redFSAuthDFPaperMultiBucketModeGen DeliverForge.engRunDFPaperBucketMode
  have hInitEq :
      initFSMultiDFBucketPaper L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        lam Δbucket qep tL par =
      initFSMultiDFBucketPaper L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δbucket qep tL par := rfl
  have hms1 : (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)).maxSkip = maxSkip := rfl
  have hms2 : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hInitEq, hms1, hms2, bind_assoc, bind_assoc]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h₀⟩ hmem₀ => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  dsimp only [bind_assoc, pure_bind]
  unfold initFSMultiDFBucketPaper at hmem₀
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure,
    pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem₀
  obtain ⟨⟨kr, _⟩, _, ⟨kc, _⟩, _, ⟨⟨σ, kVal, sid⟩, h₁⟩, _, hEq⟩ := hmem₀
  cases hEq
  let ssv0 : FSAEAD.RatchetSenderState K ⊕ ℕ :=
    match (regSessOptMultiDFBucket L tL 0 sid h₁).1 with
    | none => .inl ((FSAEAD.fromAEADPRG ae G maxSkip).initSender kVal)
    | some sIdx => .inr sIdx
  let rsv0 : FSAEAD.RatchetReceiverState K MK ⊕ ℕ :=
    match (regSessOptMultiDFBucket L tL 0 sid h₁).1 with
    | none => .inl ((FSAEAD.fromAEADPRG ae G maxSkip).initReceiver kVal)
    | some sIdx => .inr sIdx
  let g₀ : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C) :=
    { st := fun P => match P with
        | .A => (mkParties (cka.initA kc) (cka.initB kc) σ ssv0 rsv0).1
        | .B => (mkParties (cka.initA kc) (cka.initB kc) σ ssv0 rsv0).2
      b := false }
  have hInv₀ : SMEngineInv L B_q qAdv g₀ := (SMEngineInv.init _ false hB1 hBB).mono hqB
  have hVR₀ : SMVRInv (FSVROkMultiStep maxSkip) B_q qAdv g₀ := by
    intro P t₀ v hv
    cases P <;> simp only [g₀, mkParties] at hv
    · by_cases ht0 : t₀ = 0
      · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv
        subst hv
        dsimp only [rsv0]
        rcases (regSessOptMultiDFBucket L tL 0 sid h₁).1 with _ | sIdx
        · exact (RSReach.init ae G maxSkip kVal).mono (Nat.zero_le _)
        · trivial
      · simp [ht0] at hv
    · cases hv
  simp only [bind_assoc, pure_bind]
  exact congrArg (· >>= _) (simulateQ_implEDFPaperBucketMode_multi_fsClamp_eq L cka prng ae G maxSkip
    B B_q Δcka Δbucket qep gMain tL par la (bucketAuthCfgGen Δbucket tL par) hFsB hA'
    ({ g := g₀, h := (regSessOptMultiDFBucket L tL 0 sid h₁).2 }, none) hInv₀ hVR₀)

/-- Combined evaluation + `fsClamp` removal bridge for `redFSAuthDFPaperMultiBucketModeProg` on
`FSAEAD.fromAEADPRG`. -/
theorem redFSAuthDFPaperMultiBucketModeProg_eval_fromAEADPRG {MK C : Type}
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → FSAEAD.RatchetSenderState K}
    {fsInitReceiver : K → FSAEAD.RatchetReceiverState K MK}
    {fsSend : FSAEAD.RatchetSenderState K → Header T → M →
      FSAEAD.RatchetSenderState K × (ℕ × C)}
    {fsReceive : FSAEAD.RatchetReceiverState K MK → Header T → (ℕ × C) →
      Option (FSAEAD.RatchetReceiverState K MK × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool}
    {eqM : M → M → Bool} {eqE : (ℕ × C) → (ℕ × C) → Bool}
    {lam : I} {defaultE : ℕ × C}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka Δbucket qep : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = (FSAEAD.fromAEADPRG ae G maxSkip).initSender)
    (hFsInitR : fsInitReceiver = (FSAEAD.fromAEADPRG ae G maxSkip).initReceiver)
    (hFsSend : fsSend = (FSAEAD.fromAEADPRG ae G maxSkip).send)
    (hFsRecv : fsReceive = (FSAEAD.fromAEADPRG ae G maxSkip).receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR)) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep maxSkip gMain la tL par).eval (fun _ => A) () =
      redFSAuthDFPaperMultiBucketMode L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka Δbucket qep gMain la tL par A := by
  have heqE' : eqE = fun x1 x2 : ℕ × C => @BEq.beq (ℕ × C) instBEqOfDecidableEq x1 x2 := by
    cases heqE
    funext ⟨a1, c1⟩ ⟨a2, c2⟩
    by_cases ha : a1 = a2 <;> by_cases hc : c1 = c2 <;> simp [BEq.beq, ha, hc]
  have h1 := redFSAuthDFPaperMultiBucketModeProgGen_eval_clamp (lam := lam) cka prng
    (FSAEAD.fromAEADPRG ae G maxSkip) L B B_q Δcka Δbucket qep gMain la tL par
    hInitA hInitB hSend hRecv hPrngInit hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqI heqM heqE' hDefaultE hSampKR hSampKC hSampCCoins hSampI hSampK
    hB1 hBB A qAdv hA hqB
  have hms : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hms] at h1
  exact h1.trans (redFSAuthDFPaperMultiBucketModeGen_fsClamp_fromAEADPRG cka prng ae G maxSkip
    L B B_q Δcka Δbucket qep lam gMain la tL par hFsB hB1 hBB A qAdv hA hqB)

private def coinModeHandleDFPaperC
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
    (L B Δcka Δbucket qep maxSkip : ℕ) (la : Bool) (tL : Option ℕ) (par : Bool)
    {Γ'}
    (st : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (.prod .bool (fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (qArg : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
        sampKR sampKC sampCCoins sampI sampK) Γ'
      (.prod (ckaSMRDF KC Γ CCoins T I KR RSt K SS RS M E)
        (.prod .bool (fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E))) :=
  rdsl do
    (gMain0, st0, q0) ← return (st.1, st.2, qArg)
    if gMain0 then
      (out, st') ← bucketModeHandleDFPaperC L B Δcka Δbucket qep maxSkip (raw true) (raw la)
        (raw tL) (raw par) st0 q0
      return (out, (gMain0, st'))
    else
      (out, st') ← bucketModeHandleDFPaperC L B Δcka Δbucket qep maxSkip (raw false) (raw la)
        (raw tL) (raw par) st0 q0
      return (out, (gMain0, st'))

private theorem simulateQ_coinHandle_multi_eval
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
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka Δbucket qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
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
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
          (FSMultiDFBucketState T RSt K I E))
        (winEp : Option ℕ),
        FSMultiDFBucketStepBounded B_q qAdv es.h →
        SMEngineInv L B_q qAdv es.g →
        ((simulateQ (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (coinModeHandleDFPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK)
              L B Δcka Δbucket qep fs.maxSkip la tL par .v0 .v1))
          oa).run
          (gMain, (esEnc
            (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
              (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E))
            (fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
              (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)) es, winEp)) =
          (Prod.map id (fun p => (gMain, (esEnc
            (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
              (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E))
            (fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
              (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)) p.1, p.2))) <$>
            (simulateQ (DeliverForge.implEDFPaperBucketMode
              (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
              (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
              gMain isHonestHdrFSMultiDFBucket) oa).run (es, winEp))) ∧
        ∀ res ∈ support ((simulateQ (DeliverForge.implEDFPaperBucketMode
            (hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la)
            (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
            gMain isHonestHdrFSMultiDFBucket) oa).run (es, winEp)),
          SMEngineInv L B_q 0 res.2.1.g := by
  let OO := prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
  let mbRedEsTy := fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E
  let vpMEnc := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let hsMBEnc := fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let hk := hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la
  let coinHandle := coinModeHandleDFPaperC
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep fs.maxSkip la tL par
    (Γ' := [.prod .bool mbRedEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es winEp _ hInv
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact hInv.mono (Nat.zero_le qAdv)
  | query_bind q mx ih =>
    intro qAdv hq es winEp hHB hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) coinHandle)
            (.inl n)).run (gMain, (esEnc vpMEnc hsMBEnc es, winEp)) =
          (fun u => (u, (gMain, (esEnc vpMEnc hsMBEnc es, winEp)))) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        simp [handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (DeliverForge.implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfgGen Δbucket tL par) gMain isHonestHdrFSMultiDFBucket (.inl n)).run
            (es, winEp) =
          (fun u => (u, (es, winEp))) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        cases gMain <;>
          simp [DeliverForge.implEDFPaperBucketMode, DeliverForge.withWinEpDFMode,
            DeliverForge.withWinEpDF, DeliverForge.implEDFPaperBucketRaw, coinsE,
            StateT.run_mk, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es winEp hHB hInv).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es winEp hHB hInv).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      set ρ₀ := Env.cons (t := .prod .bool mbRedEsTy)
        (gMain, (esEnc vpMEnc hsMBEnc es, winEp))
        (Env.cons (t := ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)
          ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil)
      set ρ₁ := Env.cons
        (t := .prod .bool (.prod mbRedEsTy (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)))
        (gMain, (esEnc vpMEnc hsMBEnc es, winEp),
         (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) ρ₀
      have hBranch :
          coinHandle.eval ρ₀ =
            ((fun x => (x.1, (gMain, x.2))) <$>
              (bucketModeHandleDFPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK)
                L B Δcka Δbucket qep fs.maxSkip gMain la tL par
                (.fst (.snd .v0)) (.snd (.snd .v0))).eval ρ₁) := by
        dsimp only [coinHandle, coinModeHandleDFPaperC]
        rw [eval_bind_ret]
        have hEnv :
            (Expr.pair (O := OO) (.fst .v0) (.pair (.snd .v0) .v1)).eval ρ₀ =
              (gMain, (esEnc vpMEnc hsMBEnc es, winEp),
               (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) := rfl
        rw [hEnv, eval_ite]
        have hg0 : (Expr.fst (O := OO) .v0).eval ρ₁ = gMain := rfl
        rw [hg0]
        cases gMain <;>
          simp [eval_bind, eval_ret, map_eq_bind_pure_comp, Expr.eval, Expr.v0, Expr.v1, ρ₁]
      have hStepEval := rdecDF_bucketModeHandleDFPaperC_eval
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
        (lam := lam) (sampKR := sampKR) (sampKC := sampKC)
        cka prng fs L B Δcka Δbucket qep gMain la tL par
        hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
        heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK hFsRecvB
        (.fst (.snd .v0)) (.snd (.snd .v0)) ρ₁
        es winEp t (hHB.toHBounded hB1) hInv.toBoundedEngine rfl rfl
      have hStep :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) coinHandle)
            (.inr t)).run (gMain, (esEnc vpMEnc hsMBEnc es, winEp)) =
          (fun p => (p.1, (gMain, (esEnc vpMEnc hsMBEnc p.2.1, p.2.2)))) <$>
            (DeliverForge.implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip
              (bucketAuthCfgGen Δbucket tL par) gMain isHonestHdrFSMultiDFBucket (.inr t)).run
              (es, winEp) := by
        have hLHS :
            ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) coinHandle)
              (.inr t)).run (gMain, (esEnc vpMEnc hsMBEnc es, winEp)) =
            ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec t p.1, p.2)) <$>
              coinHandle.eval ρ₀) := by
          dsimp only [handlerImpl, StateT.run_mk, ρ₀, mbRedEsTy]
          simp only [map_eq_bind_pure_comp]
          refine bind_congr fun _ => rfl
        have hMid :
            ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec t p.1, p.2)) <$>
              coinHandle.eval ρ₀) =
            Prod.map id (fun s => (gMain, s)) <$>
              (((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec t p.1, p.2)) <$>
                (bucketModeHandleDFPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                  (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                  (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                  (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                  (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                  (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                  (sampI := sampI) (sampK := sampK)
                  L B Δcka Δbucket qep fs.maxSkip gMain la tL par
                  (.fst (.snd .v0)) (.snd (.snd .v0))).eval ρ₁)) := by
          rw [hBranch]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, id_eq]
        rw [hLHS, hMid, hStepEval]
        simp only [map_eq_bind_pure_comp, bind_assoc]
        refine bind_congr fun ⟨_, _, _⟩ => rfl
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁, winEp₁⟩ hmem => ?_, ?_⟩
      · have hmemRaw := mem_support_withWinEpDFMode' gMain isHonestHdrFSMultiDFBucket
          (fun vp => vp.tcur)
          (DeliverForge.implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfgGen Δbucket tL par))
          (.inr t) es es₁ winEp winEp₁ u hmem
        exact (ih u (hqm u) es₁ winEp₁
          (implEDFPaperBucketRaw_mode_stepBounded L B_q cka prng fs
            (bucketAuthCfgGen Δbucket tL par) Δcka Δbucket gMain tL par la es t hInv hHB
            (u, es₁) hmemRaw)
          (implEDFPaperBucketRaw_inv_sm hk (bucketAuthCfgGen Δbucket tL par)
            es t hInv (u, es₁) hmemRaw)).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁, winEp₁⟩, hmem₁, hmem₂⟩ := hmem
        have hmemRaw := mem_support_withWinEpDFMode' gMain isHonestHdrFSMultiDFBucket
          (fun vp => vp.tcur)
          (DeliverForge.implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfgGen Δbucket tL par))
          (.inr t) es es₁ winEp winEp₁ u hmem₁
        exact (ih u (hqm u) es₁ winEp₁
          (implEDFPaperBucketRaw_mode_stepBounded L B_q cka prng fs
            (bucketAuthCfgGen Δbucket tL par) Δcka Δbucket gMain tL par la es t hInv hHB
            (u, es₁) hmemRaw)
          (implEDFPaperBucketRaw_inv_sm hk (bucketAuthCfgGen Δbucket tL par)
            es t hInv (u, es₁) hmemRaw)).2 res hmem₂

/-- Evaluation bridge for `redFSAuthDFPaperMultiBucketCoinProgGen` on `fsClamp B fs`. -/
theorem redFSAuthDFPaperMultiBucketCoinProgGen_eval_clamp
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
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka Δbucket qep : ℕ) (la : Bool) (tL : Option ℕ) (par : Bool)
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
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthDFPaperMultiBucketCoinProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep fs.maxSkip la tL par).eval (fun _ => A) () =
      redFSAuthDFPaperMultiBucketCoinGen L cka prng (fsClamp B fs) lam Δcka Δbucket qep
        la tL par A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  let OO := prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
  let IIM := fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
  let vpMEnc := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let hsBEnc := fsMultiDFBucketHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let coinProg := redFSAuthDFPaperMultiBucketCoinProgGen
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep fs.maxSkip la tL par
  change coinProg.eval (fun _ => A) () = _
  unfold CostedReduction.eval CostedReduction.impl redFSAuthDFPaperMultiBucketCoinGen
  have hInitEval :
      coinProg.init.eval (Env.cons (t := (.unit : Ty S)) () .nil) =
        (do
          let gMain ← (sampleT Bool : TComp (FSMultiSpec SS RS T M E) Bool)
          let es₀ ← initFSMultiDFBucketPaperRaw L cka prng (fsClamp B fs) lam Δbucket qep tL par false
          pure ((), (gMain, (esEnc vpMEnc hsBEnc es₀, none)))) := by
    dsimp only [coinProg, redFSAuthDFPaperMultiBucketCoinProgGen]
    have hBit :
        (@Comp.sample _ _ _ OO IIM _ CKASamp.bit .unit).eval
          (Env.cons (t := (.unit : Ty S)) () .nil) =
          (sampleT Bool : TComp (FSMultiSpec SS RS T M E) Bool) := by
      simp only [Comp.eval, IIM, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, sampleT]
      exact Engine.liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ Bool)
    rw [eval_bind, hBit]
    refine bind_congr fun gMain => ?_
    have hInitEs := initFSMultiDFBucketPaperEStateC_eval
      (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
      cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
      hSampKR hSampKC hSampI hSampK L Δbucket qep tL par (.bool false)
      (Env.cons (t := .bool) gMain (Env.cons (t := (.unit : Ty S)) () .nil))
    rw [eval_bind, hInitEs, bind_map_left]
    refine bind_congr fun es₀ => ?_
    rw [eval_ret]
    rfl
  dsimp only
  rw [hInitEval]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun gMain => ?_
  unfold redFSAuthDFPaperMultiBucketModeGen
  rw [engRunDFPaperBucketMode_initFSMultiDFBucketPaper_eq]
  simp only [bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSMultiDFBucketPaperRaw L cka prng (fsClamp B fs) lam Δbucket qep tL par false)
    fun es₀ hes₀ => ?_
  have ⟨hHB₀, hInv₀⟩ := initFSMultiDFBucketPaperRaw_inv L B_q qAdv cka prng (fsClamp B fs)
    lam Δbucket qep tL par false hqB hB1 hBB es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_coinHandle_multi_eval
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    cka prng (fsClamp B fs) L B B_q Δcka Δbucket qep gMain la tL par hB1
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ none hHB₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  rw [hms] at hSim
  dsimp only [TComp]
  change (do
    let x ← (simulateQ (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      (coinModeHandleDFPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep fs.maxSkip la tL par .v0 .v1)) A).run
      (gMain, (esEnc vpMEnc hsBEnc es₀, none))
    (bucketFinishPaperMultiE (I' := IIM) L (2 + Δcka) la tL (.snd .v0)).eval
      (Env.cons x.2 (Env.cons (t := .bool) x.1 .nil))) = _
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es', winEp'⟩ hes' => ?_
  have hBnd' := (hSimInv (b', (es', winEp')) hes').toBoundedEngine
  have hOut := bucketFinishPaperMultiE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (I' := IIM) L (2 + Δcka) la tL (.snd .v0)
    (Env.cons (t := .prod .bool (fsMultiDFBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E))
      (gMain, (esEnc vpMEnc hsBEnc es', winEp')) (Env.cons (t := .bool) b' .nil))
    es' winEp' hBnd'.leaks_le hBnd'.corrs_le rfl
  simpa [Prod.map] using hOut

/-- `fsClamp B` removal for `redFSAuthDFPaperMultiBucketCoinGen` on `FSAEAD.fromAEADPRG`. -/
theorem redFSAuthDFPaperMultiBucketCoinGen_fsClamp_fromAEADPRG {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka Δbucket qep : ℕ)
    (lam : I) (la : Bool) (tL : Option ℕ) (par : Bool)
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    redFSAuthDFPaperMultiBucketCoinGen L cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        lam Δcka Δbucket qep la tL par A =
      redFSAuthDFPaperMultiBucketCoinGen L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka Δbucket qep la tL par A := by
  unfold redFSAuthDFPaperMultiBucketCoinGen
  exact bind_congr fun gMain =>
    redFSAuthDFPaperMultiBucketModeGen_fsClamp_fromAEADPRG cka prng ae G maxSkip
      L B B_q Δcka Δbucket qep lam gMain la tL par hFsB hB1 hBB A qAdv hA hqB

/-- Combined evaluation + `fsClamp` removal bridge for `redFSAuthDFPaperMultiBucketCoinProg` on
`FSAEAD.fromAEADPRG`. -/
theorem redFSAuthDFPaperMultiBucketCoinProg_eval_fromAEADPRG {MK C : Type}
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → FSAEAD.RatchetSenderState K}
    {fsInitReceiver : K → FSAEAD.RatchetReceiverState K MK}
    {fsSend : FSAEAD.RatchetSenderState K → Header T → M →
      FSAEAD.RatchetSenderState K × (ℕ × C)}
    {fsReceive : FSAEAD.RatchetReceiverState K MK → Header T → (ℕ × C) →
      Option (FSAEAD.RatchetReceiverState K MK × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool}
    {eqM : M → M → Bool} {eqE : (ℕ × C) → (ℕ × C) → Bool}
    {lam : I} {defaultE : ℕ × C}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka Δbucket qep : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool)
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = (FSAEAD.fromAEADPRG ae G maxSkip).initSender)
    (hFsInitR : fsInitReceiver = (FSAEAD.fromAEADPRG ae G maxSkip).initReceiver)
    (hFsSend : fsSend = (FSAEAD.fromAEADPRG ae G maxSkip).send)
    (hFsRecv : fsReceive = (FSAEAD.fromAEADPRG ae G maxSkip).receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR)) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthDFPaperMultiBucketCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep maxSkip la tL par).eval (fun _ => A) () =
      redFSAuthDFPaperMultiBucketCoin L cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka Δbucket qep la tL par A := by
  have heqE' : eqE = fun x1 x2 : ℕ × C => @BEq.beq (ℕ × C) instBEqOfDecidableEq x1 x2 := by
    cases heqE
    funext ⟨a1, c1⟩ ⟨a2, c2⟩
    by_cases ha : a1 = a2 <;> by_cases hc : c1 = c2 <;> simp [BEq.beq, ha, hc]
  have h1 := redFSAuthDFPaperMultiBucketCoinProgGen_eval_clamp (lam := lam) cka prng
    (FSAEAD.fromAEADPRG ae G maxSkip) L B B_q Δcka Δbucket qep la tL par
    hInitA hInitB hSend hRecv hPrngInit hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqI heqM heqE' hDefaultE hSampKR hSampKC hSampCCoins hSampI hSampK
    hB1 hBB A qAdv hA hqB
  have hms : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hms] at h1
  exact h1.trans (redFSAuthDFPaperMultiBucketCoinGen_fsClamp_fromAEADPRG cka prng ae G maxSkip
    L B B_q Δcka Δbucket qep lam la tL par hFsB hB1 hBB A qAdv hA hqB)

end ShallowFSMultiDFPaperMode

end CryptoGames.SM.Construction
