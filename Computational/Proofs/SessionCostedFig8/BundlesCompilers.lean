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

public import Computational.Proofs.SessionCostedFig8.BundlesAdapters -- proof-setup: allow-public-import

/-!
# Single-Session Atomic `PureAuxBundle` Compilers for Figure 8 (`SM`) Reductions-/

namespace Computational.Proofs.SessionCostedFig8.BundlesCompilers

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

open Computational.Proofs.SessionCostedFig8.BundlesAdapters (fig8MsgT fSortSM toDenSM fSortCKA toDenCKA fig8SrcQT fig8SrcRT fig8SrcQDFT fig8SrcRDFT fig8SplitIn fig8SplitIn_eval fig8SplitIn_cost fig8SplitIn_size fig8AdaptQ fig8AdaptQ_cost fig8AdaptQ_size fig8AdaptR fig8AdaptR_cost fig8AdaptR_size fig8AdaptQDF fig8AdaptQDF_cost fig8AdaptQDF_size fig8AdaptRDF fig8AdaptRDF_cost fig8AdaptRDF_size smToFig8Adapters smDFToFig8Adapters ckaToFig8Adapters ckaDFToFig8Adapters fig8AdaptQ_eval_sm fig8AdaptR_eval_sm fig8AdaptQDF_eval_sm fig8AdaptRDF_eval_sm fig8AdaptQ_eval_cka fig8AdaptR_eval_cka fig8AdaptQDF_eval_cka fig8AdaptRDF_eval_cka)

section Bundles

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

local notation "S₂" => atomicSig ℓ Pt
local notation "O₂" => atomicFig8Ops ℓ Pt C Dh encPt encT lam

@[expose, reducible] def sampBV256Atomic : ProbComp (BitVec 256) :=
  ($ᵗ (BitVec 256) : ProbComp (BitVec 256))

@[expose, reducible] def fig8SmOpsShallow :
    Ops (smSig Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)) :=
  smOps
    (Key := Unit) (St := Fig8St Pt) (St₂ := Unit)
    (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (RCoins := Unit)
    (C := Fig8C Pt)
    (init := fun _ _ => none)
    (send := fun _ _ _ => none)
    (receive := fun _ _ _ => none)
    (eqMsg := @BEq.beq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq)
    (eqCt := @BEq.beq (Fig8C Pt) instBEqOfDecidableEq)
    (blank := lBlank ℓ)
    (injOK := fun _ => true)
    (stOK := fun _ _ => true)
    (φ := fun _ => none)

@[expose] def smOpMacro :
    (o : SMOp) →
      Expr O₂
        [mapTy (fSortSM ℓ Pt) ((fig8SmOpsShallow ℓ Pt).dom o), .prod IdKey IdKey]
        (mapTy (fSortSM ℓ Pt) ((fig8SmOpsShallow ℓ Pt).cod o))
  | .init => .none
  | .send => .none
  | .receive _ => .none
  | .eqMsg => eqMExpr ℓ Pt C Dh encPt encT lam
  | .eqCt => smEqCtExpr ℓ Pt C Dh encPt encT lam
  | .blank => smBlankExpr ℓ Pt C Dh encPt encT lam
  | .injOK => .bool true
  | .stOK => .bool true
  | .relabelSt => .none

@[expose] def smSampMacro :
    (s : SMSamp) →
      Comp O₂ (fig8SmIface ℓ Pt)
        [mapTy (fSortSM ℓ Pt) ((smIface Unit (Fig8St Pt) Unit
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt)).smp.sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortSM ℓ Pt) ((smIface Unit (Fig8St Pt) Unit
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt)).smp.sTy s))
  | .bit => Comp.sample (O := O₂) (I := fig8SmIface ℓ Pt) UniformSamplerTag.bool .unit
  | .key => .ret .none
  | .coins => .ret .none
  | .rcoins => .ret .none

@[expose] def smDFSampMacro :
    (s : SMSamp) →
      Comp O₂ (fig8SmIfaceDF ℓ Pt)
        [mapTy (fSortSM ℓ Pt) ((smIfaceDF Unit (Fig8St Pt) Unit
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt)).smp.sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortSM ℓ Pt) ((smIfaceDF Unit (Fig8St Pt) Unit
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt)).smp.sTy s))
  | .bit => Comp.sample (O := O₂) (I := fig8SmIfaceDF ℓ Pt) UniformSamplerTag.bool .unit
  | .key => .ret .none
  | .coins => .ret .none
  | .rcoins => .ret .none

@[expose, reducible] def smPureAuxBundle :
    PureAuxBundle
      (smSig Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt))
      S₂
      (fig8SmOpsShallow ℓ Pt)
      O₂
      (smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt))
      (fig8SmIface ℓ Pt)
      (.prod IdKey IdKey) where
  fSort := fSortSM ℓ Pt
  opMacro := smOpMacro ℓ Pt C Dh encPt encT lam
  sampMacro := smSampMacro ℓ Pt C Dh encPt encT lam
  queryMacro
    | .tr => Comp.query (O := O₂) (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.tr (.var .zero)
    | .ch => Comp.query (O := O₂) (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.ch (.var .zero)
    | .dl => Comp.query (O := O₂) (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.dl (.var .zero)
    | .ij => Comp.query (O := O₂) (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.ij (.var .zero)
    | .cr => Comp.query (O := O₂) (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.cr (.var .zero)

@[expose, reducible] def smDFPureAuxBundle :
    PureAuxBundle
      (smSig Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt))
      S₂
      (fig8SmOpsShallow ℓ Pt)
      O₂
      (smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt))
      (fig8SmIfaceDF ℓ Pt)
      (.prod IdKey IdKey) where
  fSort := fSortSM ℓ Pt
  opMacro := smOpMacro ℓ Pt C Dh encPt encT lam
  sampMacro := smDFSampMacro ℓ Pt C Dh encPt encT lam
  queryMacro
    | .tr => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.tr (.var .zero)
    | .ch => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.ch (.var .zero)
    | .dl => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.dl (.var .zero)
    | .ij => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.ij (.var .zero)
    | .cr => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.cr (.var .zero)
    | .df => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.df (.var .zero)


@[expose, reducible] def fig8CkaOpsShallow (B0 : ℕ) :
    Ops (ckaSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) :=
  ckaSchemeOps (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) lam

@[expose] def ckaOpMacro (B0 : ℕ) :
    (o : CKAOp) →
      Expr O₂
        [mapTy (fSortCKA ℓ Pt) ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).dom o),
         .prod IdKey IdKey]
        (mapTy (fSortCKA ℓ Pt) ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).cod o))
  | .ckaInitA => ckaInitAExpr ℓ Pt C Dh encPt encT lam
  | .ckaInitB => ckaInitBExpr ℓ Pt C Dh encPt encT lam
  | .ckaSend => ckaSendExpr ℓ Pt C Dh encPt encT lam
  | .ckaReceive => ckaRecvExpr ℓ Pt C Dh encPt encT lam
  | .prngInit => prngInitExpr ℓ Pt C Dh encPt encT lam
  | .prngUp => prngUpExpr ℓ Pt C Dh encPt encT lam
  | .fsInitSender => fsInitSendExpr ℓ Pt C Dh encPt encT lam
  | .fsInitReceiver => fsInitRecvExpr ℓ Pt C Dh encPt encT lam
  | .fsSend => fsSendExpr ℓ Pt C Dh encPt encT lam
  | .fsReceive B => fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B
  | .eqT => eqPtExpr ℓ Pt C Dh encPt encT lam
  | .eqI => eqPtExpr ℓ Pt C Dh encPt encT lam
  | .eqM => eqMExpr ℓ Pt C Dh encPt encT lam
  | .eqE => eqEExpr ℓ Pt C Dh encPt encT lam
  | .lamI => lamIExpr ℓ Pt C Dh encPt encT lam
  | .defaultE => defaultEExpr ℓ Pt C Dh encPt encT lam

@[expose] def ckaSampMacro (sampBV : ProbComp (BitVec 256)) :
    (s : CKASamp) →
      Comp O₂ (ckaTargetIface ℓ Pt)
        [mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sTy s))
  | .bit => Comp.sample (O := O₂) (I := ckaTargetIface ℓ Pt) UniformSamplerTag.bool .unit
  | .kr | .kc | .ccoins | .k =>
      Comp.sample (O := O₂) (I := ckaTargetIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.bv256) .unit
  | .i =>
      Comp.sample (O := O₂) (I := ckaTargetIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.pt) .unit

@[expose] def prngSampMacro (sampBV : ProbComp (BitVec 256)) :
    (s : CKASamp) →
      Comp O₂ (prngTargetIface ℓ Pt)
        [mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sTy s))
  | .bit => Comp.sample (O := O₂) (I := prngTargetIface ℓ Pt) UniformSamplerTag.bool .unit
  | .kr | .kc | .ccoins | .k =>
      Comp.sample (O := O₂) (I := prngTargetIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.bv256) .unit
  | .i =>
      Comp.sample (O := O₂) (I := prngTargetIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.pt) .unit

@[expose] def fsSampMacro (sampBV : ProbComp (BitVec 256)) :
    (s : CKASamp) →
      Comp O₂ (fsaeadHeaderIface ℓ Pt)
        [mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sTy s))
  | .bit => Comp.sample (O := O₂) (I := fsaeadHeaderIface ℓ Pt) UniformSamplerTag.bool .unit
  | .kr | .kc | .ccoins | .k =>
      Comp.sample (O := O₂) (I := fsaeadHeaderIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.bv256) .unit
  | .i =>
      Comp.sample (O := O₂) (I := fsaeadHeaderIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.pt) .unit

@[expose, reducible] def ckaPureAuxBundle (B0 : ℕ) (sampBV : ProbComp (BitVec 256)) :
    PureAuxBundle
      (ckaSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      S₂
      (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      O₂
      (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        sampBV sampBV sampBV ($ᵗ Pt) sampBV)
      (ckaTargetIface ℓ Pt)
      (.prod IdKey IdKey) where
  fSort := fSortCKA ℓ Pt
  opMacro := ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0
  sampMacro := ckaSampMacro ℓ Pt C Dh encPt encT lam sampBV
  queryMacro
    | .send => Comp.query (O := O₂) (I := ckaTargetIface ℓ Pt) ReductionDsl.CKATag.send (.var .zero)
    | .sendBad => Comp.query (O := O₂) (I := ckaTargetIface ℓ Pt) ReductionDsl.CKATag.sendBad (.var .zero)
    | .chall => Comp.query (O := O₂) (I := ckaTargetIface ℓ Pt) ReductionDsl.CKATag.chall (.var .zero)
    | .receive => Comp.query (O := O₂) (I := ckaTargetIface ℓ Pt) ReductionDsl.CKATag.receive (.var .zero)
    | .corr => Comp.query (O := O₂) (I := ckaTargetIface ℓ Pt) ReductionDsl.CKATag.corr (.var .zero)

@[expose, reducible] def prngPureAuxBundle (B0 : ℕ) (sampBV : ProbComp (BitVec 256)) :
    PureAuxBundle
      (prngSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      S₂
      (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      O₂
      (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        sampBV sampBV sampBV ($ᵗ Pt) sampBV)
      (prngTargetIface ℓ Pt)
      (.prod IdKey IdKey) where
  fSort := fSortCKA ℓ Pt
  opMacro := ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0
  sampMacro := prngSampMacro ℓ Pt C Dh encPt encT lam sampBV
  queryMacro
    | .process => Comp.query (O := O₂) (I := prngTargetIface ℓ Pt) ReductionDsl.PRNGTag.process (.var .zero)
    | .challPrng => Comp.query (O := O₂) (I := prngTargetIface ℓ Pt) ReductionDsl.PRNGTag.challPrng (.var .zero)
    | .challPrf => Comp.query (O := O₂) (I := prngTargetIface ℓ Pt) ReductionDsl.PRNGTag.challPrf (.var .zero)
    | .corr => Comp.query (O := O₂) (I := prngTargetIface ℓ Pt) ReductionDsl.PRNGTag.corr (.var .zero)

@[expose, reducible] def fsPureAuxBundle (B0 : ℕ) (sampBV : ProbComp (BitVec 256)) :
    PureAuxBundle
      (prngSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      S₂
      (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      O₂
      (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        sampBV sampBV sampBV ($ᵗ Pt) sampBV)
      (fsaeadHeaderIface ℓ Pt)
      (.prod IdKey IdKey) where
  fSort := fSortCKA ℓ Pt
  opMacro := ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0
  sampMacro := fsSampMacro ℓ Pt C Dh encPt encT lam sampBV
  queryMacro
    | .tr => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.tr (.var .zero)
    | .ch => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.ch (.var .zero)
    | .cs => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.cs (.var .zero)
    | .cr => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.cr (.var .zero)
    | .dl => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.dl (.var .zero)
    | .ij => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.ij (.var .zero)


omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem smRrEnc_eq_toVal_smRrEnc (rr : CryptoGames.SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ)) :
    ReductionDsl.smRrEnc (msgT := fig8MsgT ℓ Pt) (fun (pub, m) => (lpubV pub, m)) rr =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        (CryptoGames.SM.smRrTy Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt))
        (CryptoGames.SM.smRrEnc rr) := by
  rcases rr with _ | ⟨t, i, _ | ⟨pub, m⟩⟩ <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem fsRrEnc_eq_toVal_fsHdrRrEnc
    (rr : CryptoGames.FSAEAD.ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) :
    ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := fig8MsgT ℓ Pt)
        (fun (pub, m) => (lpubV pub, m)) rr =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        (CryptoGames.PRFPRNG.fsHdrRrTy (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        (fsHdrRrEnc rr) := by
  rcases rr with _ | ⟨i, _ | ⟨pub, m⟩⟩ <;> rfl

theorem sampBV256Atomic_evalDistEq :
    sampBV256Atomic =ᵈ ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) := by
  simpa only [id_map] using
    @SampleableType.map_uniformSample_evalDistEq_of_bijective
      (BitVec 256) (BitVec 256) inferInstance inferInstance
      id Function.bijective_id

omit [Zero Pt] [SampleableType Pt] in
private theorem fig8C_beq_eq_dec (c1 c2 : Fig8C Pt) :
    (c1 == c2) = @BEq.beq (Fig8C Pt) instBEqOfDecidableEq c1 c2 :=
  Bool.eq_iff_iff.mpr (beq_iff_eq.trans decide_eq_true_iff.symm)

omit [SampleableType Pt] in
theorem smOpMacro_eval (o : SMOp)
    (z : ((fig8SmOpsShallow ℓ Pt).dom o).denote) :
    (smOpMacro ℓ Pt C Dh encPt encT lam o).eval
      (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt) ((fig8SmOpsShallow ℓ Pt).dom o) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt) ((fig8SmOpsShallow ℓ Pt).cod o)
        ((fig8SmOpsShallow ℓ Pt).eval o z) := by
  cases o with
  | init | send | receive _ | injOK | stOK | relabelSt => rfl
  | eqMsg =>
    rcases z with ⟨⟨p1, m1⟩, ⟨p2, m2⟩⟩
    exact eqMExpr_eval ℓ Pt C Dh encPt encT lam idOf (p1, m1) (p2, m2)
  | eqCt =>
    rcases z with ⟨c1, c2⟩
    dsimp only [smOpMacro, fig8SmOpsShallow, smOps, toVal, toDenSM]
    rw [smEqCtExpr_eval ℓ Pt C Dh encPt encT lam idOf c1 c2, fig8C_beq_eq_dec]
  | blank =>
    rcases z with ⟨p, m⟩
    exact smBlankExpr_eval ℓ Pt C Dh encPt encT lam idOf (p, m)

private theorem liftP_congr {ι : Type} {T : OracleSpec.{0, 0} ι} {S₁' S₂' : Sig}
    (I₂ : Iface S₂' T) (I₁ : Iface S₁' T) (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    {α : Type} (p : ProbComp α) : I₂.liftP p = I₁.liftP p := by
  unfold Iface.liftP
  rw [funext hFwdU]

private theorem env_get_zero {S' : Sig} {a : Ty S'} {Γ : List (Ty S')}
    (x : a.denote) (ρ : Env Γ) : (Env.cons x ρ).get .zero = x := rfl

theorem smPureAuxBundle_samp_eval
    (s : SMSamp)
    (z : ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).smp.sDom s).denote) :
    ((smPureAuxBundle ℓ Pt C Dh encPt encT lam).sampMacro s).eval
      (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).smp.sDom s) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).smp.sTy s) <$>
        (smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).liftP
          ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) Unit (Fig8C Pt)).smp.samp s z) := by
  cases s with
  | bit =>
    change (fig8SmIface ℓ Pt).liftP ($ᵗ Bool) = (id : Bool → Bool) <$> _
    rw [id_map]
    exact liftP_congr (fig8SmIface ℓ Pt) _ (fun _ => rfl) _
  | key | coins | rcoins => rfl

theorem smDFPureAuxBundle_samp_eval
    (s : SMSamp)
    (z : ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).smp.sDom s).denote) :
    ((smDFPureAuxBundle ℓ Pt C Dh encPt encT lam).sampMacro s).eval
      (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).smp.sDom s) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).smp.sTy s) <$>
        (smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).liftP
          ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) Unit (Fig8C Pt)).smp.samp s z) := by
  cases s with
  | bit =>
    change (fig8SmIfaceDF ℓ Pt).liftP ($ᵗ Bool) = (id : Bool → Bool) <$> _
    rw [id_map]
    exact liftP_congr (fig8SmIfaceDF ℓ Pt) _ (fun _ => rfl) _
  | key | coins | rcoins => rfl

theorem smPureAuxBundle_query_eval
    (g : (smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).Tag)
    (z : ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).dom g).denote) :
    ((smPureAuxBundle ℓ Pt C Dh encPt encT lam).queryMacro g).eval
      (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).dom g) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).cod g) <$>
        ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
              (BitVec 256) (Fig8C Pt))
            ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
              (BitVec 256) Unit (Fig8C Pt)).enc g z)) :
            OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
              (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) _)) := by
  cases g with
  | tr =>
    rcases z with ⟨p, ⟨pub, m⟩, _ | r⟩ <;>
      (dsimp only [smPureAuxBundle, Comp.eval, Expr.eval, Option.map, fig8SmIface,
        smIface, toVal, toDenSM]
       simp only [env_get_zero, Functor.map_map]
       rw [boolToParty_eq_partyDec, lpubOfV_lpubV])
  | ch =>
    rcases z with ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, _ | r⟩ <;>
      (dsimp only [smPureAuxBundle, Comp.eval, Expr.eval, Option.map, fig8SmIface,
        smIface, toVal, toDenSM]
       simp only [env_get_zero, Functor.map_map]
       rw [boolToParty_eq_partyDec, lpubOfV_lpubV pub0, lpubOfV_lpubV pub1])
  | dl | ij =>
    rcases z with ⟨p, c⟩
    dsimp only [smPureAuxBundle, Comp.eval, Expr.eval, fig8SmIface, smIface,
      toVal, toDenSM]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec, fig8CtOfV_fig8CtV]
    congr 1; funext r; cases r <;> simp [toVal, toDenSM, smRrEnc_eq_toVal_smRrEnc]
  | cr =>
    dsimp only [smPureAuxBundle, Comp.eval, Expr.eval, fig8SmIface, smIface,
      toVal, toDenSM]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec]

theorem smDFPureAuxBundle_query_eval
    (g : (smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).Tag)
    (z : ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).dom g).denote) :
    ((smDFPureAuxBundle ℓ Pt C Dh encPt encT lam).queryMacro g).eval
      (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).dom g) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).cod g) <$>
        ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
              (BitVec 256) (Fig8C Pt))
            ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
              (BitVec 256) Unit (Fig8C Pt)).enc g z)) :
            OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
              (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) _)) := by
  cases g with
  | tr =>
    rcases z with ⟨p, ⟨pub, m⟩, _ | r⟩ <;>
      (dsimp only [smDFPureAuxBundle, Comp.eval, Expr.eval, Option.map, fig8SmIfaceDF,
        smIfaceDF, toVal, toDenSM]
       simp only [env_get_zero, Functor.map_map]
       rw [boolToParty_eq_partyDec, lpubOfV_lpubV])
  | ch =>
    rcases z with ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, _ | r⟩ <;>
      (dsimp only [smDFPureAuxBundle, Comp.eval, Expr.eval, Option.map, fig8SmIfaceDF,
        smIfaceDF, toVal, toDenSM]
       simp only [env_get_zero, Functor.map_map]
       rw [boolToParty_eq_partyDec, lpubOfV_lpubV pub0, lpubOfV_lpubV pub1])
  | dl | ij =>
    rcases z with ⟨p, c⟩
    dsimp only [smDFPureAuxBundle, Comp.eval, Expr.eval, fig8SmIfaceDF, smIfaceDF,
      toVal, toDenSM]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec, fig8CtOfV_fig8CtV]
    congr 1; funext r; cases r <;> simp [toVal, toDenSM, smRrEnc_eq_toVal_smRrEnc]
  | cr =>
    dsimp only [smDFPureAuxBundle, Comp.eval, Expr.eval, fig8SmIfaceDF, smIfaceDF,
      toVal, toDenSM]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec]
  | df =>
    rcases z with ⟨p, c1, c2⟩
    dsimp only [smDFPureAuxBundle, Comp.eval, Expr.eval, fig8SmIfaceDF, smIfaceDF,
      toVal, toDenSM]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec, fig8CtOfV_fig8CtV c1, fig8CtOfV_fig8CtV c2]
    congr 1; funext r; cases r <;> simp [toVal, toDenSM, smRrEnc_eq_toVal_smRrEnc]

omit [SampleableType Pt] in
theorem ckaOpMacro_eval (B0 : ℕ) (o : CKAOp)
    (z : ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).dom o).denote) :
    (ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0 o).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).dom o) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).cod o)
        ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).eval o z) := by
  cases o with
  | ckaInitA => exact ckaInitAExpr_eval ℓ Pt C Dh encPt encT lam idOf z
  | ckaInitB => exact ckaInitBExpr_eval ℓ Pt C Dh encPt encT lam idOf z
  | prngInit => exact prngInitExpr_eval ℓ Pt C Dh encPt encT lam idOf z
  | lamI => exact lamIExpr_eval ℓ Pt C Dh encPt encT lam idOf
  | ckaSend =>
    rcases z with ⟨γ, x⟩
    exact ckaSendExpr_eval ℓ Pt C Dh encPt encT lam idOf γ x
  | ckaReceive =>
    rcases z with ⟨γ, t⟩
    exact ckaRecvExpr_eval ℓ Pt C Dh encPt encT lam idOf γ t
  | prngUp =>
    rcases z with ⟨σ, I⟩
    exact prngUpExpr_eval ℓ Pt C Dh encPt encT lam idOf σ I
  | fsInitSender => rfl
  | fsInitReceiver => exact fsInitRecvExpr_eval ℓ Pt C Dh encPt encT lam idOf B0 z
  | fsSend =>
    rcases z with ⟨ss, ⟨ep, _ | T⟩, p, m⟩
    · exact fsSendExpr_eval ℓ Pt C Dh encPt encT lam idOf B0 ss (ep, none) p m
    · exact fsSendExpr_eval ℓ Pt C Dh encPt encT lam idOf B0 ss (ep, some T) p m
  | fsReceive B =>
    rcases z with ⟨rs, ⟨ep, _ | T⟩, c⟩
    · have hr := fsRecvExpr_eval ℓ Pt C Dh encPt encT lam idOf B0 B rs (ep, none) c
      dsimp only [ckaOpMacro, fig8CkaOpsShallow, ckaSchemeOps, ckaOps, toVal, toDenCKA, Option.map]
      rw [hr]
      rcases (fsAtomicB C ℓ encT idOf B0).receive rs (ep, none) c with _ | ⟨rs', idx, p, m⟩ <;> rfl
    · have hr := fsRecvExpr_eval ℓ Pt C Dh encPt encT lam idOf B0 B rs (ep, some T) c
      dsimp only [ckaOpMacro, fig8CkaOpsShallow, ckaSchemeOps, ckaOps, toVal, toDenCKA, Option.map]
      rw [hr]
      rcases (fsAtomicB C ℓ encT idOf B0).receive rs (ep, some T) c with _ | ⟨rs', idx, p, m⟩ <;> rfl
  | eqT | eqI =>
    rcases z with ⟨a, b⟩
    exact eqPtExpr_eval ℓ Pt C Dh encPt encT lam idOf a b
  | eqM =>
    rcases z with ⟨⟨p1, m1⟩, ⟨p2, m2⟩⟩
    exact eqMExpr_eval ℓ Pt C Dh encPt encT lam idOf (p1, m1) (p2, m2)
  | eqE =>
    rcases z with ⟨e1, e2⟩
    exact eqEExpr_eval ℓ Pt C Dh encPt encT lam idOf e1 e2
  | defaultE =>
    exact defaultEExpr_eval ℓ Pt C Dh encPt encT lam idOf

theorem ckaPureAuxBundle_samp_eval_atomic (B0 : ℕ) (s : CKASamp)
    (z : ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sDom s).denote) :
    ((ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV256Atomic).sampMacro s).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sTy s) <$>
        (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).liftP
          ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.samp s z) := by
  cases s <;>
    exact (liftP_congr (ckaTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm

theorem ckaPureAuxBundle_samp_coinSimEquiv (B0 : ℕ) (s : CKASamp)
    (z : ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      (((ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)))
      (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply CoinSimEquiv.of_eq
    exact (liftP_congr (ckaTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    change CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      ((ckaTargetIface ℓ Pt).liftP sampBV256Atomic) (id <$> _)
    rw [id_map, ← liftP_congr (ckaTargetIface ℓ Pt) _ (fun _ => rfl)]
    exact coinSimEquiv_liftP (ckaTargetIface ℓ Pt) sampBV256Atomic_evalDistEq

theorem prngPureAuxBundle_samp_eval_atomic (B0 : ℕ) (s : CKASamp)
    (z : ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sDom s).denote) :
    ((prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV256Atomic).sampMacro s).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sTy s) <$>
        (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).liftP
          ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.samp s z) := by
  cases s <;>
    exact (liftP_congr (prngTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm

theorem prngPureAuxBundle_samp_coinSimEquiv (B0 : ℕ) (s : CKASamp)
    (z : ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    CoinSimEquiv (prngTargetIface ℓ Pt).fwdU
      (((prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)))
      (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply CoinSimEquiv.of_eq
    exact (liftP_congr (prngTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    change CoinSimEquiv (prngTargetIface ℓ Pt).fwdU
      ((prngTargetIface ℓ Pt).liftP sampBV256Atomic) (id <$> _)
    rw [id_map, ← liftP_congr (prngTargetIface ℓ Pt) _ (fun _ => rfl)]
    exact coinSimEquiv_liftP (prngTargetIface ℓ Pt) sampBV256Atomic_evalDistEq

theorem fsPureAuxBundle_samp_eval_atomic (B0 : ℕ) (s : CKASamp)
    (z : ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sDom s).denote) :
    ((fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV256Atomic).sampMacro s).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sTy s) <$>
        (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).liftP
          ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.samp s z) := by
  cases s <;>
    exact (liftP_congr (fsaeadHeaderIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm

theorem fsPureAuxBundle_samp_coinSimEquiv (B0 : ℕ) (s : CKASamp)
    (z : ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      (((fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)))
      (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply CoinSimEquiv.of_eq
    exact (liftP_congr (fsaeadHeaderIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    change CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      ((fsaeadHeaderIface ℓ Pt).liftP sampBV256Atomic) (id <$> _)
    rw [id_map, ← liftP_congr (fsaeadHeaderIface ℓ Pt) _ (fun _ => rfl)]
    exact coinSimEquiv_liftP (fsaeadHeaderIface ℓ Pt) sampBV256Atomic_evalDistEq

theorem ckaPureAuxBundle_query_eval (B0 : ℕ) (sampBV : ProbComp (BitVec 256))
    (g : (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).Tag)
    (z : ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).dom g).denote) :
    ((ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV).queryMacro g).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ <$>
        ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV sampBV sampBV ($ᵗ Pt) sampBV).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + CryptoGames.CKA.spec (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
              (BitVec 256) Pt Pt)
            ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
              (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              sampBV sampBV sampBV ($ᵗ Pt) sampBV).enc g z)) :
            OracleComp (unifSpec + CryptoGames.CKA.spec
              (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) _)) := by
  cases g with
  | send | chall | receive =>
    dsimp only [ckaPureAuxBundle, Comp.eval, Expr.eval, ckaTargetIface, ckaIface,
      toVal, toDenCKA]
    simp only [env_get_zero, Functor.map_map]
    congr 1; funext r; cases r <;> rfl
  | sendBad =>
    rcases z with ⟨p, r⟩
    dsimp only [ckaPureAuxBundle, Comp.eval, Expr.eval, ckaTargetIface, ckaIface,
      toVal, toDenCKA]
    simp only [env_get_zero, Functor.map_map]
    congr 1; funext x; cases x <;> rfl
  | corr =>
    dsimp only [ckaPureAuxBundle, Comp.eval, Expr.eval, ckaTargetIface, ckaIface,
      toVal, toDenCKA]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec]

theorem prngPureAuxBundle_query_eval (B0 : ℕ) (sampBV : ProbComp (BitVec 256))
    (g : (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).Tag)
    (z : ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).dom g).denote) :
    ((prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV).queryMacro g).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ <$>
        ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV sampBV sampBV ($ᵗ Pt) sampBV).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + CryptoGames.PRFPRNG.spec (BitVec 256) Pt (BitVec 256))
            ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
              (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              sampBV sampBV sampBV ($ᵗ Pt) sampBV).enc g z)) :
            OracleComp (unifSpec + CryptoGames.PRFPRNG.spec (BitVec 256) Pt (BitVec 256)) _)) := by
  cases g with
  | process | challPrng =>
    cases z <;>
      (dsimp only [prngPureAuxBundle, Comp.eval, Expr.eval, Option.map, prngTargetIface,
        prngIface, toVal, toDenCKA]
       simp only [env_get_zero, Functor.map_map]
       congr 1; funext r; cases r <;> rfl)
  | challPrf | corr =>
    dsimp only [prngPureAuxBundle, Comp.eval, Expr.eval, prngTargetIface, prngIface,
      toVal, toDenCKA]
    simp only [env_get_zero, Functor.map_map]
    congr 1; funext r; cases r <;> rfl

theorem fsPureAuxBundle_query_eval (B0 : ℕ) (sampBV : ProbComp (BitVec 256))
    (g : (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).Tag)
    (z : ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).dom g).denote) :
    ((fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV).queryMacro g).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ <$>
        ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV sampBV sampBV ($ᵗ Pt) sampBV).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256))
              (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
              (ℕ × LibsignalCiphertextWithSalt32))
            ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
              (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              sampBV sampBV sampBV ($ᵗ Pt) sampBV).enc g z)) :
            OracleComp (unifSpec + CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256))
              (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
              (ℕ × LibsignalCiphertextWithSalt32)) _)) := by
  cases g with
  | tr =>
    rcases z with ⟨⟨ep, _ | T⟩, pub, m⟩ <;>
      (dsimp only [fsPureAuxBundle, Comp.eval, Expr.eval, Option.map, fsaeadHeaderIface,
        fsaeadHeaderAdIface, toVal, toDenCKA]
       simp only [env_get_zero, Functor.map_map]
       rw [lpubOfV_lpubV])
  | ch =>
    rcases z with ⟨⟨ep, _ | T⟩, ⟨pub0, m0⟩, ⟨pub1, m1⟩⟩ <;>
      (dsimp only [fsPureAuxBundle, Comp.eval, Expr.eval, Option.map, fsaeadHeaderIface,
        fsaeadHeaderAdIface, toVal, toDenCKA]
       simp only [env_get_zero, Functor.map_map]
       rw [lpubOfV_lpubV pub0, lpubOfV_lpubV pub1])
  | cs =>
    dsimp only [fsPureAuxBundle, Comp.eval, Expr.eval, fsaeadHeaderIface,
      fsaeadHeaderAdIface, toVal, toDenCKA]
    simp only [Functor.map_map]
  | cr =>
    dsimp only [fsPureAuxBundle, Comp.eval, Expr.eval, fsaeadHeaderIface,
      fsaeadHeaderAdIface, toVal, toDenCKA]
    simp only [Functor.map_map]
  | dl | ij =>
    rcases z with ⟨⟨ep, _ | T⟩, c⟩ <;>
      (dsimp only [fsPureAuxBundle, Comp.eval, Expr.eval, Option.map, fsaeadHeaderIface,
        fsaeadHeaderAdIface, toVal, toDenCKA]
       simp only [env_get_zero, Functor.map_map]
       rw [lctOfV_lctV]
       congr 1; funext r; rcases r with _ | (_ | ⟨idx, _ | ⟨pub, m⟩⟩) <;> rfl)

@[expose] def compileSmAtomic
    (R : CostedReduction (fig8SmOpsShallow ℓ Pt)
      (smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (fig8SmIface ℓ Pt)
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (smPureAuxBundle ℓ Pt C Dh encPt encT lam)
      (smToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

@[expose] def compileSmDFAtomic
    (R : CostedReduction (fig8SmOpsShallow ℓ Pt)
      (smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (fig8SmIfaceDF ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (smDFPureAuxBundle ℓ Pt C Dh encPt encT lam)
      (smDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

@[expose] def compileCkaAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

@[expose] def compileCkaDFAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

@[expose] def compilePrngAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (prngTargetIface ℓ Pt)
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

@[expose] def compilePrngDFAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

@[expose] def compileFsAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

@[expose] def compileFsDFAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

end Bundles

end

end Computational.Proofs.SessionCostedFig8.BundlesCompilers
