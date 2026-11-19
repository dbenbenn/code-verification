/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.PureAuxMacroLift -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.MacroLift -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.Theorem1 -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.RedCKA -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.RedPRNG -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.RedFS -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.QuerySubsumes -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound -- proof-setup: allow-public-import
public import Computational.Specifications.Session.StatementComposed -- proof-setup: allow-public-import


/-!
# Sort Mappings and `PureAuxAdapters` for Figure 8 (`SM`) Atomic Reductions-/

namespace Computational.Proofs.SessionCostedFig8.BundlesAdapters

public section

set_option autoImplicit false
set_option linter.dupNamespace false

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface Env Expr Comp CostedReduction bits
  UniformSamplerTag AtomicUnifBase SMTag SMTagDF CKATag PRNGTag FSAEADTag
  atomicSig atomicFig8Ops BV256 IdKey PlainT PtT
  ckaStT ckaStV ckaStOfV fsSendStT fsSendStV fsSendStOfV fsRecvStT fsRecvStV fsRecvStOfV
  lpubT lpubV lpubOfV lctT lctV lctOfV fig8StT fig8StV fig8StOfV fig8CtT fig8CtV fig8CtOfV
  smRrT smRrEnc smRrDec fsRrEnc
  fig8SmIface fig8SmIfaceDF fig8SmCodec fig8SmCodecDF
  ckaTargetIface prngTargetIface fsaeadHeaderIface)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal callMacroAux callMacroAux_size
  guardRed)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv PureAuxAdapters
  PureAuxBundle coinSimEquiv_liftP callPureMacroAux compilePureAuxExpr compilePureAuxComp
  callAdaptR compilePureAuxRed bits_mono)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb fsAtomicB
  idKeyLitExpr idKeyLitExpr_cost idKeyLitExpr_size
  partyToBool_eq_partyEnc boolToParty_eq_partyDec
  ckaStOfV_ckaStV fsSendStOfV_fsSendStV fsRecvStOfV_fsRecvStV
  lpubOfV_lpubV lctOfV_lctV fig8StOfV_fig8StV fig8CtOfV_fig8CtV
  eqPtExpr eqPtExpr_eval eqPtExpr_size eqMExpr eqMExpr_eval eqMExpr_size
  eqEExpr eqEExpr_eval eqEExpr_size
  defaultEExpr defaultEExpr_eval defaultEExpr_size lamIExpr lamIExpr_eval lamIExpr_size
  smEqCtExpr smEqCtExpr_eval smEqCtExpr_size smBlankExpr smBlankExpr_eval smBlankExpr_size
  ckaInitAExpr ckaInitAExpr_eval ckaInitAExpr_size
  ckaInitBExpr ckaInitBExpr_eval ckaInitBExpr_size
  ckaSendExpr ckaSendExpr_eval ckaSendExpr_size ckaRecvExpr ckaRecvExpr_eval ckaRecvExpr_size
  prngInitExpr prngInitExpr_eval prngInitExpr_size prngUpExpr prngUpExpr_eval prngUpExpr_size
  fsInitSendExpr fsInitSendExpr_size fsInitRecvExpr fsInitRecvExpr_eval fsInitRecvExpr_size
  fsSendExpr fsSendExpr_eval fsSendExpr_size fsRecvExpr fsRecvExpr_eval fsRecvExpr_size)
open Computational.Proofs.SessionCostedFig8.QuerySubsumes (QuerySubsumes)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun CKASort ckaSig CKAOp ckaOps ckaSchemeOps CKASamp ckaSamplers ckaIface
  ckaSMCodec ckaSMCodecDF ckaPsTy ckaPsDec)
open CryptoGames.PRFPRNG (prngSig prngIface fsaeadHeaderAdIface FSHdrTag fsHdrRrEnc)
open CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32 lPubOf)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec
  maxForwardJumps)
open CryptoGames.LibsignalSM (lBlank)
open CryptoGames.SM (SMSort smSig SMOp smOps SMSamp smIface smIfaceDF smCodec smCodecDF
  partyEnc partyDec)
open CryptoVerification.LibsignalSession (Fig8CostedReds)


section SortAndAdapters

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

local notation "S₂" => atomicSig ℓ Pt
local notation "O₂" => atomicFig8Ops ℓ Pt C Dh encPt encT lam

@[expose, reducible] def fig8MsgT : Ty S₂ := .prod lpubT PlainT

@[expose, reducible] def fSortSM : SMSort → Ty S₂
  | .key => .unit
  | .st => fig8StT
  | .st2 => .unit
  | .msg => fig8MsgT ℓ Pt
  | .coins => BV256
  | .rcoins => .unit
  | .ct => fig8CtT

@[expose] def toDenSM :
    (b : SMSort) →
      (smSig Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt)).den b →
      (fSortSM ℓ Pt b).denote
  | .key, () => ()
  | .st, s => fig8StV s
  | .st2, () => ()
  | .msg, (pub, m) => (lpubV pub, m)
  | .coins, r => r
  | .rcoins, () => ()
  | .ct, c => fig8CtV c

@[expose, reducible] def fSortCKA : CKASort → Ty S₂
  | .kc | .ccoins | .kr | .sig | .k => BV256
  | .γ => ckaStT
  | .t | .i => PtT
  | .ss => fsSendStT
  | .rs => fsRecvStT
  | .msg => fig8MsgT ℓ Pt
  | .ct => lctT

@[expose] def toDenCKA :
    (b : CKASort) →
      (ckaSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).den b →
      (fSortCKA ℓ Pt b).denote
  | .kc, x | .ccoins, x | .kr, x | .sig, x | .k, x => x
  | .γ, γ => ckaStV γ
  | .t, x | .i, x => x
  | .ss, ss => fsSendStV ss
  | .rs, rs => fsRecvStV rs
  | .msg, (pub, m) => (lpubV pub, m)
  | .ct, c => lctV c

@[expose, reducible] def fig8SrcQT : Ty S₂ :=
  .sum
    (.sum
      (.sum
        (.sum
          (.prod .bool (.prod (fig8MsgT ℓ Pt) (.opt BV256)))
          (.prod .bool (.prod (fig8MsgT ℓ Pt) (.prod (fig8MsgT ℓ Pt) (.opt BV256)))))
        (.prod .bool fig8CtT))
      (.prod .bool fig8CtT))
    .bool

@[expose, reducible] def fig8SrcRT : Ty S₂ :=
  .sum
    (.sum
      (.sum
        (.sum (.opt fig8CtT) (.opt fig8CtT))
        (.opt (smRrT (fig8MsgT ℓ Pt))))
      (.opt (smRrT (fig8MsgT ℓ Pt))))
    (.opt fig8StT)

@[expose, reducible] def fig8SrcQDFT : Ty S₂ :=
  .sum (fig8SrcQT ℓ Pt) (.prod .bool (.prod fig8CtT fig8CtT))

@[expose, reducible] def fig8SrcRDFT : Ty S₂ :=
  .sum (fig8SrcRT ℓ Pt) (.opt (smRrT (fig8MsgT ℓ Pt)))

@[expose] def fig8SplitIn : Expr O₂ [.unit] (.prod .unit (.prod IdKey IdKey)) :=
  .pair .unit
    (.pair (idKeyLitExpr ℓ Pt C Dh encPt encT lam (idOf .A))
           (idKeyLitExpr ℓ Pt C Dh encPt encT lam (idOf .B)))

theorem fig8SplitIn_eval :
    (fig8SplitIn ℓ Pt C Dh encPt encT idOf lam).eval (.cons () .nil) = ((), (idOf .A, idOf .B)) := by
  simp [fig8SplitIn, Expr.eval]

theorem fig8SplitIn_cost : (fig8SplitIn ℓ Pt C Dh encPt encT idOf lam).cost ≤ 200 := by
  have hA := idKeyLitExpr_cost ℓ Pt C Dh encPt encT lam (Γ := [.unit]) (idOf .A)
  have hB := idKeyLitExpr_cost ℓ Pt C Dh encPt encT lam (Γ := [.unit]) (idOf .B)
  simp only [fig8SplitIn, Expr.cost]
  omega

theorem fig8SplitIn_size : (fig8SplitIn ℓ Pt C Dh encPt encT idOf lam).size ≤ 75 := by
  simp only [fig8SplitIn, idKeyLitExpr_size, Expr.size]
  omega

@[expose] def fig8AdaptQ : Expr O₂ [(fig8SmCodec ℓ Pt).Q] (fig8SrcQT ℓ Pt) :=
  .caseSum (.var .zero)
    (.inl (.inl (.inl (.inl (.var .zero)))))
    (.caseSum (.var .zero)
      (.inl (.inl (.inl (.inr (.var .zero)))))
      (.caseSum (.var .zero)
        (.inl (.inl (.inr (.var .zero))))
        (.caseSum (.var .zero)
          (.inl (.inr (.var .zero)))
          (.inr (.var .zero)))))

theorem fig8AdaptQ_cost : (fig8AdaptQ ℓ Pt C Dh encPt encT lam).cost ≤ 35 := by
  simp only [fig8AdaptQ, Expr.cost]; omega

theorem fig8AdaptQ_size : (fig8AdaptQ ℓ Pt C Dh encPt encT lam).size ≤ 45 := by
  simp only [fig8AdaptQ, Expr.size]; omega

@[expose] def fig8AdaptR : Expr O₂ [fig8SrcRT ℓ Pt, (fig8SmCodec ℓ Pt).Q] (fig8SmCodec ℓ Pt).R :=
  let r0 {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SrcRT ℓ Pt) := .var .zero
  let onTr {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SmCodec ℓ Pt).R :=
    .caseSum r0
      (.caseSum (.var .zero)
        (.caseSum (.var .zero)
          (.caseSum (.var .zero) (.inl (.var .zero)) (.inl .none))
          (.inl .none))
        (.inl .none))
      (.inl .none)
  let onCh {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SmCodec ℓ Pt).R :=
    .caseSum r0
      (.caseSum (.var .zero)
        (.caseSum (.var .zero)
          (.caseSum (.var .zero) (.inl .none) (.inl (.var .zero)))
          (.inl .none))
        (.inl .none))
      (.inl .none)
  let onDl {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SmCodec ℓ Pt).R :=
    .caseSum r0
      (.caseSum (.var .zero)
        (.caseSum (.var .zero) (.inr (.inl .none)) (.inr (.inl (.var .zero))))
        (.inr (.inl .none)))
      (.inr (.inl .none))
  let onIj {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SmCodec ℓ Pt).R :=
    .caseSum r0
      (.caseSum (.var .zero) (.inr (.inl .none)) (.inr (.inl (.var .zero))))
      (.inr (.inl .none))
  let onCr {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SmCodec ℓ Pt).R :=
    .caseSum r0 (.inr (.inr .none)) (.inr (.inr (.var .zero)))
  .caseSum (.var (.succ .zero))
    (.letE (.var (.succ .zero)) onTr)
    (.caseSum (.var .zero)
      (.letE (.var (.succ (.succ .zero))) onCh)
      (.caseSum (.var .zero)
        (.letE (.var (.succ (.succ (.succ .zero)))) onDl)
        (.caseSum (.var .zero)
          (.letE (.var (.succ (.succ (.succ (.succ .zero))))) onIj)
          (.letE (.var (.succ (.succ (.succ (.succ .zero))))) onCr))))

theorem fig8AdaptR_cost : (fig8AdaptR ℓ Pt C Dh encPt encT lam).cost ≤ 120 := by
  simp only [fig8AdaptR, Expr.cost]; omega

theorem fig8AdaptR_size : (fig8AdaptR ℓ Pt C Dh encPt encT lam).size ≤ 150 := by
  simp only [fig8AdaptR, Expr.size]; omega

@[expose] def fig8AdaptQDF : Expr O₂ [(fig8SmCodecDF ℓ Pt).Q] (fig8SrcQDFT ℓ Pt) :=
  .caseSum (.var .zero)
    (.inl (.inl (.inl (.inl (.inl (.var .zero))))))
    (.caseSum (.var .zero)
      (.inl (.inl (.inl (.inl (.inr (.var .zero))))))
      (.caseSum (.var .zero)
        (.inl (.inl (.inl (.inr (.var .zero)))))
        (.caseSum (.var .zero)
          (.inl (.inl (.inr (.var .zero))))
          (.caseSum (.var .zero)
            (.inl (.inr (.var .zero)))
            (.inr (.var .zero))))))

theorem fig8AdaptQDF_cost : (fig8AdaptQDF ℓ Pt C Dh encPt encT lam).cost ≤ 45 := by
  simp only [fig8AdaptQDF, Expr.cost]; omega

theorem fig8AdaptQDF_size : (fig8AdaptQDF ℓ Pt C Dh encPt encT lam).size ≤ 60 := by
  simp only [fig8AdaptQDF, Expr.size]; omega

@[expose] def fig8AdaptRDF : Expr O₂ [fig8SrcRDFT ℓ Pt, (fig8SmCodecDF ℓ Pt).Q] (fig8SmCodecDF ℓ Pt).R :=
  let rTop {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SrcRDFT ℓ Pt) := .var .zero
  let onTr {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop
      (.caseSum (.var .zero)
        (.caseSum (.var .zero)
          (.caseSum (.var .zero)
            (.caseSum (.var .zero) (.inl (.var .zero)) (.inl .none))
            (.inl .none))
          (.inl .none))
        (.inl .none))
      (.inl .none)
  let onCh {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop
      (.caseSum (.var .zero)
        (.caseSum (.var .zero)
          (.caseSum (.var .zero)
            (.caseSum (.var .zero) (.inl .none) (.inl (.var .zero)))
            (.inl .none))
          (.inl .none))
        (.inl .none))
      (.inl .none)
  let onDl {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop
      (.caseSum (.var .zero)
        (.caseSum (.var .zero)
          (.caseSum (.var .zero) (.inr (.inl .none)) (.inr (.inl (.var .zero))))
          (.inr (.inl .none)))
        (.inr (.inl .none)))
      (.inr (.inl .none))
  let onIj {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop
      (.caseSum (.var .zero)
        (.caseSum (.var .zero) (.inr (.inl .none)) (.inr (.inl (.var .zero))))
        (.inr (.inl .none)))
      (.inr (.inl .none))
  let onCr {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop (.caseSum (.var .zero) (.inr (.inr .none)) (.inr (.inr (.var .zero))))
      (.inr (.inr .none))
  let onDf {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop (.inr (.inl .none)) (.inr (.inl (.var .zero)))
  .caseSum (.var (.succ .zero))
    (.letE (.var (.succ .zero)) onTr)
    (.caseSum (.var .zero)
      (.letE (.var (.succ (.succ .zero))) onCh)
      (.caseSum (.var .zero)
        (.letE (.var (.succ (.succ (.succ .zero)))) onDl)
        (.caseSum (.var .zero)
          (.letE (.var (.succ (.succ (.succ (.succ .zero))))) onIj)
          (.caseSum (.var .zero)
            (.letE (.var (.succ (.succ (.succ (.succ (.succ .zero)))))) onCr)
            (.letE (.var (.succ (.succ (.succ (.succ (.succ .zero)))))) onDf)))))

theorem fig8AdaptRDF_cost : (fig8AdaptRDF ℓ Pt C Dh encPt encT lam).cost ≤ 155 := by
  simp only [fig8AdaptRDF, Expr.cost]; omega

theorem fig8AdaptRDF_size : (fig8AdaptRDF ℓ Pt C Dh encPt encT lam).size ≤ 200 := by
  simp only [fig8AdaptRDF, Expr.size]; omega

omit [DecidableEq Pt] [Zero Pt] in
private theorem fig8StOfV_toVal_ckaPsTy
    (ps : (ckaPsTy (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).denote) :
    fig8StOfV (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
      (ckaPsTy (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) ps) =
      ckaPsDec ps := by
  rcases ps with ⟨p, rk, vs?, vrTbl, γ, cur?, tc⟩
  dsimp only [toVal, fSortCKA, toDenCKA, fig8StOfV, ckaPsDec]
  rw [boolToParty_eq_partyDec, ckaStOfV_ckaStV]
  have hvs : Option.map (fsSendStOfV (ℓ := ℓ) (Pt := Pt))
      (Option.map (fun x => fsSendStV (ℓ := ℓ) (Pt := Pt) x) vs?) = vs? := by
    cases vs? <;> simp [fsSendStOfV_fsSendStV]
  have hvr : (fun t => Option.map (fsRecvStOfV (ℓ := ℓ) (Pt := Pt))
      (Option.map (fun x => fsRecvStV (ℓ := ℓ) (Pt := Pt) x) (vrTbl t))) = vrTbl := by
    funext t; cases vrTbl t <;> simp [fsRecvStOfV_fsRecvStV]
  have hcur : Option.map (fun x => x) cur? = cur? := by
    cases cur? <;> rfl
  rw [hvs, hvr, hcur]

@[expose, reducible] def smToFig8Adapters :
    PureAuxAdapters (fSortSM ℓ Pt) O₂
      (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (fig8SmCodec ℓ Pt) (.prod IdKey IdKey)
      .unit .unit .bool .bool .unit .unit .bool .bool where
  splitIn := fig8SplitIn ℓ Pt C Dh encPt encT idOf lam
  adaptAIn := .unit
  adaptQ := fig8AdaptQ ℓ Pt C Dh encPt encT lam
  adaptR := fig8AdaptR ℓ Pt C Dh encPt encT lam
  adaptAOut := .var .zero
  adaptOut := .var .zero

@[expose, reducible] def smDFToFig8Adapters :
    PureAuxAdapters (fSortSM ℓ Pt) O₂
      (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) (.prod IdKey IdKey)
      .unit .unit .bool .bool .unit .unit .bool .bool where
  splitIn := fig8SplitIn ℓ Pt C Dh encPt encT idOf lam
  adaptAIn := .unit
  adaptQ := fig8AdaptQDF ℓ Pt C Dh encPt encT lam
  adaptR := fig8AdaptRDF ℓ Pt C Dh encPt encT lam
  adaptAOut := .var .zero
  adaptOut := .var .zero

@[expose, reducible] def ckaToFig8Adapters :
    PureAuxAdapters (fSortCKA ℓ Pt) O₂
      (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (fig8SmCodec ℓ Pt) (.prod IdKey IdKey)
      .unit .unit .bool .bool .unit .unit .bool .bool where
  splitIn := fig8SplitIn ℓ Pt C Dh encPt encT idOf lam
  adaptAIn := .unit
  adaptQ := fig8AdaptQ ℓ Pt C Dh encPt encT lam
  adaptR := fig8AdaptR ℓ Pt C Dh encPt encT lam
  adaptAOut := .var .zero
  adaptOut := .var .zero

@[expose, reducible] def ckaDFToFig8Adapters :
    PureAuxAdapters (fSortCKA ℓ Pt) O₂
      (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (fig8SmCodecDF ℓ Pt) (.prod IdKey IdKey)
      .unit .unit .bool .bool .unit .unit .bool .bool where
  splitIn := fig8SplitIn ℓ Pt C Dh encPt encT idOf lam
  adaptAIn := .unit
  adaptQ := fig8AdaptQDF ℓ Pt C Dh encPt encT lam
  adaptR := fig8AdaptRDF ℓ Pt C Dh encPt encT lam
  adaptAOut := .var .zero
  adaptOut := .var .zero

private def decodeSrcR
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₂ : (fig8SrcRT ℓ Pt).denote) :
    (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Range t :=
  match t with
  | .inl (.inl (.inl (.inl _))) =>
    match r₂ with
    | .inl (.inl (.inl (.inl r))) => r.map (fig8CtOfV (ℓ := ℓ) (Pt := Pt))
    | _ => none
  | .inl (.inl (.inl (.inr _))) =>
    match r₂ with
    | .inl (.inl (.inl (.inr r))) => r.map (fig8CtOfV (ℓ := ℓ) (Pt := Pt))
    | _ => none
  | .inl (.inl (.inr _)) =>
    match r₂ with
    | .inl (.inl (.inr r)) =>
      r.map (ReductionDsl.smRrDec (ℓ := ℓ) (Pt := Pt) (msgT := fig8MsgT ℓ Pt)
        fun x => (lpubOfV (ℓ := ℓ) (Pt := Pt) x.1, x.2))
    | _ => none
  | .inl (.inr _) =>
    match r₂ with
    | .inl (.inr r) =>
      r.map (ReductionDsl.smRrDec (ℓ := ℓ) (Pt := Pt) (msgT := fig8MsgT ℓ Pt)
        fun x => (lpubOfV (ℓ := ℓ) (Pt := Pt) x.1, x.2))
    | _ => none
  | .inr _ =>
    match r₂ with
    | .inr r => r.map (fig8StOfV (ℓ := ℓ) (Pt := Pt))
    | _ => none

private theorem fig8SmCodec_rdec_adaptR
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₂ : (fig8SrcRT ℓ Pt).denote) :
    (fig8SmCodec ℓ Pt).rdec t
      ((fig8AdaptR ℓ Pt C Dh encPt encT lam).eval
        (.cons r₂ (.cons ((fig8SmCodec ℓ Pt).qenc t) .nil))) =
      decodeSrcR ℓ Pt t r₂ := by
  rcases t with (((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · rcases r₂ with (((r | _) | _) | _) | _ <;> rfl
  · rcases r₂ with (((_ | r) | _) | _) | _ <;> rfl
  · rcases r₂ with ((_ | r) | _) | _ <;> rfl
  · rcases r₂ with (_ | r) | _ <;> rfl
  · rcases r₂ with _ | r <;> rfl

private def decodeSrcRDF
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₂ : (fig8SrcRDFT ℓ Pt).denote) :
    (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Range t :=
  match t with
  | .inl t' =>
    match r₂ with
    | .inl r₂' => decodeSrcR ℓ Pt t' r₂'
    | .inr _ =>
      match t' with
      | .inl (.inl (.inl (.inl _))) => none
      | .inl (.inl (.inl (.inr _))) => none
      | .inl (.inl (.inr _)) => none
      | .inl (.inr _) => none
      | .inr _ => none
  | .inr _ =>
    match r₂ with
    | .inr r =>
      r.map (ReductionDsl.smRrDec (ℓ := ℓ) (Pt := Pt) (msgT := fig8MsgT ℓ Pt)
        fun x => (lpubOfV (ℓ := ℓ) (Pt := Pt) x.1, x.2))
    | .inl _ => none

private theorem fig8SmCodecDF_rdec_adaptRDF
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₂ : (fig8SrcRDFT ℓ Pt).denote) :
    (fig8SmCodecDF ℓ Pt).rdec t
      ((fig8AdaptRDF ℓ Pt C Dh encPt encT lam).eval
        (.cons r₂ (.cons ((fig8SmCodecDF ℓ Pt).qenc t) .nil))) =
      decodeSrcRDF ℓ Pt t r₂ := by
  rcases t with
    ((((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p) | ⟨p, c1, c2⟩
  · rcases r₂ with ((((r | _) | _) | _) | _) | _ <;> rfl
  · rcases r₂ with ((((_ | r) | _) | _) | _) | _ <;> rfl
  · rcases r₂ with (((_ | r) | _) | _) | _ <;> rfl
  · rcases r₂ with ((_ | r) | _) | _ <;> rfl
  · rcases r₂ with (_ | r) | _ <;> rfl
  · rcases r₂ with _ | r <;> rfl

theorem fig8AdaptQ_eval_sm
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain) :
    (fig8AdaptQ ℓ Pt C Dh encPt encT lam).eval (.cons ((fig8SmCodec ℓ Pt).qenc t) .nil) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).Q
        ((smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).qenc t) := by
  rcases t with (((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · dsimp only [fig8AdaptQ, fig8SmCodec, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl

theorem fig8AdaptR_eval_sm
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₁ : (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).R.denote) :
    (fig8SmCodec ℓ Pt).rdec t
      ((fig8AdaptR ℓ Pt C Dh encPt encT lam).eval
        (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
          (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) Unit (Fig8C Pt)).R r₁)
          (.cons ((fig8SmCodec ℓ Pt).qenc t) .nil))) =
      (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt)).rdec t r₁ := by
  rw [fig8SmCodec_rdec_adaptR]
  rcases t with (((_ | _) | _) | _) | _ <;> rcases r₁ with ((((r | r) | r) | r) | r) <;> try rfl
  · cases r <;> simp [decodeSrcR, toVal, toDenSM, fig8CtOfV_fig8CtV]
  · cases r <;> simp [decodeSrcR, toVal, toDenSM, fig8CtOfV_fig8CtV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcR, toVal, toDenSM, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcR, toVal, toDenSM, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · cases r <;> simp [decodeSrcR, toVal, toDenSM, fig8StOfV_fig8StV]

theorem fig8AdaptQDF_eval_sm
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain) :
    (fig8AdaptQDF ℓ Pt C Dh encPt encT lam).eval (.cons ((fig8SmCodecDF ℓ Pt).qenc t) .nil) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).Q
        ((smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).qenc t) := by
  rcases t with
    ((((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p) | ⟨p, c1, c2⟩
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl

theorem fig8AdaptRDF_eval_sm
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₁ : (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).R.denote) :
    (fig8SmCodecDF ℓ Pt).rdec t
      ((fig8AdaptRDF ℓ Pt C Dh encPt encT lam).eval
        (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
          (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) Unit (Fig8C Pt)).R r₁)
          (.cons ((fig8SmCodecDF ℓ Pt).qenc t) .nil))) =
      (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt)).rdec t r₁ := by
  rw [fig8SmCodecDF_rdec_adaptRDF]
  rcases t with ((((_ | _) | _) | _) | _) | _ <;>
    rcases r₁ with (((((r | r) | r) | r) | r) | r) <;> try rfl
  · cases r <;> simp [decodeSrcRDF, decodeSrcR, toVal, toDenSM, fig8CtOfV_fig8CtV]
  · cases r <;> simp [decodeSrcRDF, decodeSrcR, toVal, toDenSM, fig8CtOfV_fig8CtV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, decodeSrcR, toVal, toDenSM, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, decodeSrcR, toVal, toDenSM, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · cases r <;> simp [decodeSrcRDF, decodeSrcR, toVal, toDenSM, fig8StOfV_fig8StV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, toVal, toDenSM, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]

theorem fig8AdaptQ_eval_cka
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain) :
    (fig8AdaptQ ℓ Pt C Dh encPt encT lam).eval (.cons ((fig8SmCodec ℓ Pt).qenc t) .nil) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).Q
        ((ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).qenc t) := by
  rcases t with (((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, ⟨ep, t?⟩, c⟩) | ⟨p, ⟨ep, t?⟩, c⟩) | p
  · dsimp only [fig8AdaptQ, fig8SmCodec, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, ckaSMCodec, fig8CtV, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases t? <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, ckaSMCodec, fig8CtV, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases t? <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl

theorem fig8AdaptR_eval_cka
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₁ : (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).R.denote) :
    (fig8SmCodec ℓ Pt).rdec t
      ((fig8AdaptR ℓ Pt C Dh encPt encT lam).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
          (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).R r₁)
          (.cons ((fig8SmCodec ℓ Pt).qenc t) .nil))) =
      (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).rdec t r₁ := by
  rw [fig8SmCodec_rdec_adaptR]
  rcases t with (((_ | _) | _) | _) | _ <;> rcases r₁ with ((((r | r) | r) | r) | r) <;> try rfl
  · rcases r with _ | ⟨⟨ep, t?⟩, c⟩ <;> [rfl; (cases t? <;> simp [decodeSrcR, fig8CtOfV, toVal, toDenCKA, lctOfV_lctV])]
  · rcases r with _ | ⟨⟨ep, t?⟩, c⟩ <;> [rfl; (cases t? <;> simp [decodeSrcR, fig8CtOfV, toVal, toDenCKA, lctOfV_lctV])]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcR, toVal, toDenCKA, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcR, toVal, toDenCKA, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ps
    · rfl
    · dsimp only [decodeSrcR, ckaSMCodec, Option.map]
      exact congrArg some (fig8StOfV_toVal_ckaPsTy ℓ Pt ps)

theorem fig8AdaptQDF_eval_cka
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain) :
    (fig8AdaptQDF ℓ Pt C Dh encPt encT lam).eval (.cons ((fig8SmCodecDF ℓ Pt).qenc t) .nil) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).Q
        ((ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).qenc t) := by
  rcases t with
    ((((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, ⟨ep, t?⟩, c⟩) | ⟨p, ⟨ep, t?⟩, c⟩) | p) |
      ⟨p, ⟨⟨ep1, t1?⟩, c1⟩, ⟨⟨ep2, t2?⟩, c2⟩⟩
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, fig8CtV, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases t? <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, fig8CtV, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases t? <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, fig8CtV, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases t1? <;> cases t2? <;> rfl

theorem fig8AdaptRDF_eval_cka
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₁ : (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).R.denote) :
    (fig8SmCodecDF ℓ Pt).rdec t
      ((fig8AdaptRDF ℓ Pt C Dh encPt encT lam).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
          (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).R r₁)
          (.cons ((fig8SmCodecDF ℓ Pt).qenc t) .nil))) =
      (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).rdec t r₁ := by
  rw [fig8SmCodecDF_rdec_adaptRDF]
  rcases t with ((((_ | _) | _) | _) | _) | _ <;>
    rcases r₁ with (((((r | r) | r) | r) | r) | r) <;> try rfl
  · rcases r with _ | ⟨⟨ep, t?⟩, c⟩ <;> [rfl; (cases t? <;> simp [decodeSrcRDF, decodeSrcR, fig8CtOfV, toVal, toDenCKA, lctOfV_lctV])]
  · rcases r with _ | ⟨⟨ep, t?⟩, c⟩ <;> [rfl; (cases t? <;> simp [decodeSrcRDF, decodeSrcR, fig8CtOfV, toVal, toDenCKA, lctOfV_lctV])]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, decodeSrcR, toVal, toDenCKA, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, decodeSrcR, toVal, toDenCKA, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ps
    · rfl
    · dsimp only [decodeSrcRDF, decodeSrcR, ckaSMCodecDF, ckaSMCodec, Option.map]
      exact congrArg some (fig8StOfV_toVal_ckaPsTy ℓ Pt ps)
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, toVal, toDenCKA, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]

end SortAndAdapters

end

end Computational.Proofs.SessionCostedFig8.BundlesAdapters
