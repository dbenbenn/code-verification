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
public import Computational.Proofs.SessionCostedFig8.BundlesCompilers -- proof-setup: allow-public-import

/-!
# `QuerySubsumes` Lift Helpers and Weighted AST Size Bounds (`compSizeW`) for Figure 8 (`SM`)-/

namespace Computational.Proofs.SessionCostedFig8.BundlesAuxSize

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
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (sampBV256Atomic fig8SmOpsShallow smOpMacro smSampMacro smDFSampMacro smPureAuxBundle smDFPureAuxBundle fig8CkaOpsShallow ckaOpMacro ckaSampMacro prngSampMacro fsSampMacro ckaPureAuxBundle prngPureAuxBundle fsPureAuxBundle smRrEnc_eq_toVal_smRrEnc fsRrEnc_eq_toVal_fsHdrRrEnc sampBV256Atomic_evalDistEq smOpMacro_eval smPureAuxBundle_samp_eval smDFPureAuxBundle_samp_eval smPureAuxBundle_query_eval smDFPureAuxBundle_query_eval ckaOpMacro_eval ckaPureAuxBundle_samp_eval_atomic ckaPureAuxBundle_samp_coinSimEquiv prngPureAuxBundle_samp_eval_atomic prngPureAuxBundle_samp_coinSimEquiv fsPureAuxBundle_samp_eval_atomic fsPureAuxBundle_samp_coinSimEquiv ckaPureAuxBundle_query_eval prngPureAuxBundle_query_eval fsPureAuxBundle_query_eval compileSmAtomic compileSmDFAtomic compileCkaAtomic compileCkaDFAtomic compilePrngAtomic compilePrngDFAtomic compileFsAtomic compileFsDFAtomic)

section QuerySubsumesLiftP

private theorem liftP_congr {ι : Type} {T : OracleSpec.{0, 0} ι} {S₁' S₂' : Sig}
    (I₂ : Iface S₂' T) (I₁ : Iface S₁' T) (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    {α : Type} (p : ProbComp α) : I₂.liftP p = I₁.liftP p := by
  unfold Iface.liftP
  rw [funext hFwdU]

private theorem querySubsumes_pure_liftP_of_mem_support
    {κ : Type} {G : OracleSpec.{0, 0} κ} {S₁' : Sig}
    (I₁ : Iface S₁' (unifSpec + G))
    (hFwd₁ : ∀ n, I₁.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    {β γ : Type} (f : β → γ) (p₂ : ProbComp β) {y : β} (hy : y ∈ support p₂) :
    QuerySubsumes (pure (f y) : OracleComp (unifSpec + G) γ) (f <$> I₁.liftP p₂) := by
  induction p₂ using OracleComp.inductionOn with
  | pure b =>
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [Iface.liftP, simulateQ_pure, map_pure]
    exact .ret (f y)
  | query_bind n mx ih =>
    rw [mem_support_bind_iff] at hy
    obtain ⟨u, _, hy⟩ := hy
    have hStep : f <$> I₁.liftP (liftM (OracleSpec.query n) >>= mx) =
        liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= fun v => f <$> I₁.liftP (mx v) := by
      simp [Iface.liftP, hFwd₁, map_bind]
    rw [hStep]
    exact .coin_r _ n _ u (ih u hy)

private theorem querySubsumes_liftP_of_forall_mem_support
    {κ : Type} {G : OracleSpec.{0, 0} κ} {S₂' : Sig}
    (I₂ : Iface S₂' (unifSpec + G))
    (hFwd₂ : ∀ n, I₂.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    {β γ : Type} (f : β → γ) (p₁ : ProbComp β)
    {oa₂ : OracleComp (unifSpec + G) γ}
    (h : ∀ x ∈ support p₁, QuerySubsumes (pure (f x)) oa₂) :
    QuerySubsumes (f <$> I₂.liftP p₁) oa₂ := by
  induction p₁ using OracleComp.inductionOn with
  | pure b =>
    simp only [Iface.liftP, simulateQ_pure, map_pure]
    exact h b (by simp)
  | query_bind n mx ih =>
    have hStep : f <$> I₂.liftP (liftM (OracleSpec.query n) >>= mx) =
        liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= fun u => f <$> I₂.liftP (mx u) := by
      simp [Iface.liftP, hFwd₂, map_bind]
    rw [hStep]
    exact .coin_l n _ oa₂ fun u => ih u fun x hx =>
      h x (by rw [mem_support_bind_iff]; exact ⟨u, by simp, hx⟩)

theorem querySubsumes_liftP_of_support_subset
    {κ : Type} {G : OracleSpec.{0, 0} κ} {S₁' S₂' : Sig}
    (I₂ : Iface S₂' (unifSpec + G)) (I₁ : Iface S₁' (unifSpec + G))
    (hFwd₂ : ∀ n, I₂.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    (hFwd₁ : ∀ n, I₁.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    {β : Type} {p₁ p₂ : ProbComp β} (hsup : ∀ x ∈ support p₁, x ∈ support p₂) :
    QuerySubsumes (I₂.liftP p₁) ((fun x => x) <$> I₁.liftP p₂) := by
  have h := querySubsumes_liftP_of_forall_mem_support I₂ hFwd₂ id p₁ fun x hx =>
    querySubsumes_pure_liftP_of_mem_support I₁ hFwd₁ id p₂ (hsup x hx)
  rwa [id_map] at h

theorem fsPureAuxBundle_samp_querySubsumes
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B0 : ℕ) (s : CKASamp)
    (z : ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    QuerySubsumes
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
    apply QuerySubsumes.of_eq
    exact (liftP_congr (fsaeadHeaderIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    exact
      querySubsumes_liftP_of_support_subset (fsaeadHeaderIface ℓ Pt)
        (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => by simp)

end QuerySubsumesLiftP

section PureAuxSize

@[simp] theorem callPureMacroAux_size {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {a b : Ty S₂} (e : Expr O₂ [a, auxT] b) :
    (callPureMacroAux f auxT Γ e).size = e.size :=
  Expr.renameM_size _ e

@[simp] theorem callAdaptR_size {S₂ : Sig} {O₂ : Ops S₂} {r₁T q₂T r₂T a b c d e : Ty S₂}
    (adR : Expr O₂ [r₁T, q₂T] r₂T) :
    (callAdaptR (a := a) (b := b) (c := c) (d := d) (e := e) adR).size = adR.size :=
  Expr.renameM_size _ adR

/-- Weighted AST node/bit size of `Expr O Γ t` with custom per-operator size weight `opS`. -/
@[expose] def exprSizeW {S : Sig} {O : Ops S} (opS : O.Op → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .none | _, _, .nil => 1
  | _, _, .nat n => bits n
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b
  | _, _, .and a b | _, _, .pair a b | _, _, .cons a b | _, _, .take a b
  | _, _, .tget a b | _, _, .letE a b => exprSizeW opS a + exprSizeW opS b + 1
  | _, _, .mulK k a | _, _, .divK k a | _, _, .modK k a => exprSizeW opS a + bits k + 1
  | _, _, .not a | _, _, .fst a | _, _, .snd a | _, _, .inl a | _, _, .inr a
  | _, _, .some a | _, _, .len a | _, _, .tconst a => exprSizeW opS a + 1
  | _, _, .ite c a b | _, _, .caseOpt c a b | _, _, .caseSum c a b | _, _, .tset c a b =>
    exprSizeW opS c + exprSizeW opS a + exprSizeW opS b + 1
  | _, _, .op o a => exprSizeW opS a + opS o
  | _, _, .appendL K a b => exprSizeW opS a + exprSizeW opS b + bits K + 1
  | _, _, .findB K l p | _, _, .anyB K l p | _, _, .mapB K l p =>
    exprSizeW opS l + exprSizeW opS p + bits K + 1
  | _, _, .foldrB K l z f =>
    exprSizeW opS l + exprSizeW opS z + exprSizeW opS f + bits K + 1

/-- Weighted AST node/bit size of `Comp O I Γ t` with custom op, sampler, and query size weights. -/
@[expose] def compSizeW {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => exprSizeW opS e + 1
  | _, _, .bind c k => compSizeW opS sS qS c + compSizeW opS sS qS k + 1
  | _, _, .ite b c d | _, _, .caseOpt b c d | _, _, .caseSum b c d =>
    exprSizeW opS b + compSizeW opS sS qS c + compSizeW opS sS qS d + 1
  | _, _, .sample s e => exprSizeW opS e + sS s
  | _, _, .query g e => exprSizeW opS e + qS g
  | _, _, .iter n e body | _, _, .findM n e body | _, _, .anyM n e body | _, _, .mapM n e body =>
    exprSizeW opS e + compSizeW opS sS qS body + bits n + 1
  | _, _, .consumeFirstM K l p mk =>
    exprSizeW opS l + compSizeW opS sS qS p + exprSizeW opS mk + bits K + 1
  | _, _, .foldM K l z f =>
    exprSizeW opS l + exprSizeW opS z + compSizeW opS sS qS f + bits K + 1

@[simp] theorem exprSizeW_renameM {S : Sig} {O : Ops S} (opS : O.Op → ℕ)
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, ReductionDsl.Var Γ u → ReductionDsl.Var Δ u)
    {t : Ty S} (e : Expr O Γ t) :
    exprSizeW opS (Expr.renameM ξ e) = exprSizeW opS e := by
  induction e generalizing Δ <;> simp [Expr.renameM, exprSizeW, *]

@[simp] theorem compSizeW_renameM {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ)
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, ReductionDsl.Var Γ u → ReductionDsl.Var Δ u)
    {t : Ty S} (c : Comp O I Γ t) :
    compSizeW opS sS qS (Comp.renameM ξ c) = compSizeW opS sS qS c := by
  induction c generalizing Δ <;> simp [Comp.renameM, compSizeW, *]

theorem compilePureAuxExpr_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (opS : O₁.Op → ℕ) (hOp : ∀ o, (M.opMacro o).size + 1 ≤ opS o)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureAuxExpr M e).size ≤ exprSizeW opS e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    simp only [compilePureAuxExpr, Expr.size, exprSizeW]; omega
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | tget _ _ ih1 ih2 | letE _ _ ih1 ih2 =>
    simp only [compilePureAuxExpr, Expr.size, exprSizeW]; omega
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [compilePureAuxExpr, Expr.size, exprSizeW]; omega
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb
  | foldrB _ _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp only [compilePureAuxExpr, Expr.size, exprSizeW]; omega
  | op o _ iha =>
    have ho := hOp o
    simp only [compilePureAuxExpr, Expr.size, callPureMacroAux_size, exprSizeW]; omega
  | findB _ _ _ ihl ihp | anyB _ _ _ ihl ihp | mapB _ _ _ ihl ihp =>
    simp only [compilePureAuxExpr, Expr.size, exprSizeW]; omega

theorem compilePureAuxComp_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (opS : O₁.Op → ℕ) (sS : I₁.smp.Samp → ℕ) (qS : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ opS o)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ sS s)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ qS g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureAuxComp M c).size ≤ compSizeW opS sS qS c := by
  induction c with
  | ret e =>
    have he := compilePureAuxExpr_size_le M opS hOp e
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega
  | bind _ _ ihc ihk =>
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := compilePureAuxExpr_size_le M opS hOp b
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega
  | sample s e =>
    have he := compilePureAuxExpr_size_le M opS hOp e
    have hs := hSamp s
    simp only [compilePureAuxComp, Comp.size, callMacroAux_size, compSizeW]; omega
  | query g e =>
    have he := compilePureAuxExpr_size_le M opS hOp e
    have hq := hQuery g
    simp only [compilePureAuxComp, Comp.size, callMacroAux_size, compSizeW]; omega
  | iter _ e _ ihb | findM _ e _ ihb | anyM _ e _ ihb | mapM _ e _ ihb =>
    have he := compilePureAuxExpr_size_le M opS hOp e
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega
  | consumeFirstM _ l _ mk ihp =>
    have hl := compilePureAuxExpr_size_le M opS hOp l
    have hmk := compilePureAuxExpr_size_le M opS hOp mk
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega
  | foldM _ l z _ ihf =>
    have hl := compilePureAuxExpr_size_le M opS hOp l
    have hz := compilePureAuxExpr_size_le M opS hOp z
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega

theorem compilePureAuxRed_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {G : OracleSpec κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : ReductionDsl.GameCodec S₁ G} {C₂ : ReductionDsl.GameCodec S₂ G} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAuxAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (opS : O₁.Op → ℕ) (sS : I₁.smp.Samp → ℕ) (qS : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ opS o)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ sS s)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ qS g) :
    (compilePureAuxRed M A R).size ≤
      compSizeW opS sS qS R.init + compSizeW opS sS qS R.handle + compSizeW opS sS qS R.finish +
        A.splitIn.size + A.adaptAIn.size + A.adaptQ.size + A.adaptR.size +
        A.adaptAOut.size + A.adaptOut.size + 74 := by
  have hi := compilePureAuxComp_size_le M opS sS qS hOp hSamp hQuery R.init
  have hh := compilePureAuxComp_size_le M opS sS qS hOp hSamp hQuery R.handle
  have hf := compilePureAuxComp_size_le M opS sS qS hOp hSamp hQuery R.finish
  simp only [CostedReduction.size, compilePureAuxRed, Comp.size, Comp.renameM_size,
    Expr.renameM_size, callAdaptR_size, Expr.size]
  omega

theorem exprSizeW_le_mul_size {S : Sig} {O : Ops S} (opS : O.Op → ℕ)
    (K : ℕ) (hK : 2 ≤ K) (hOp : ∀ o, opS o ≤ K)
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    exprSizeW opS e ≤ K * e.size := by
  induction e with
  | var _ | unit | bool _ | none | nil =>
    simp only [exprSizeW, Expr.size]; omega
  | nat _ =>
    simp only [exprSizeW, Expr.size]; nlinarith
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | tget _ _ ih1 ih2 | letE _ _ ih1 ih2 =>
    simp only [exprSizeW, Expr.size]; nlinarith
  | mulK k _ ih | divK k _ ih | modK k _ ih =>
    have hk := _root_.ReductionDsl.one_le_bits k
    simp only [exprSizeW, Expr.size]; nlinarith
  | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [exprSizeW, Expr.size]; nlinarith
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb
  | foldrB _ _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp only [exprSizeW, Expr.size]; nlinarith
  | op o _ iha =>
    have ho := hOp o
    simp only [exprSizeW, Expr.size]; nlinarith
  | findB _ _ _ ihl ihp | anyB _ _ _ ihl ihp | mapB _ _ _ ihl ihp =>
    simp only [exprSizeW, Expr.size]; nlinarith

theorem compSizeW_le_mul_size {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ)
    (K : ℕ) (hK : 2 ≤ K)
    (hOp : ∀ o, opS o ≤ K) (hSamp : ∀ s, sS s ≤ K) (hQuery : ∀ g, qS g ≤ K)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compSizeW opS sS qS c ≤ K * c.size := by
  induction c with
  | ret e =>
    have he := exprSizeW_le_mul_size opS K hK hOp e
    simp only [compSizeW, Comp.size]; nlinarith
  | bind _ _ ihc ihk =>
    simp only [compSizeW, Comp.size]; nlinarith
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := exprSizeW_le_mul_size opS K hK hOp b
    simp only [compSizeW, Comp.size]; nlinarith
  | sample s e =>
    have he := exprSizeW_le_mul_size opS K hK hOp e
    have hs := hSamp s
    simp only [compSizeW, Comp.size]; nlinarith
  | query g e =>
    have he := exprSizeW_le_mul_size opS K hK hOp e
    have hq := hQuery g
    simp only [compSizeW, Comp.size]; nlinarith
  | iter _ e _ ihb | findM _ e _ ihb | anyM _ e _ ihb | mapM _ e _ ihb =>
    have he := exprSizeW_le_mul_size opS K hK hOp e
    simp only [compSizeW, Comp.size]; nlinarith
  | consumeFirstM _ l _ mk ihp =>
    have hl := exprSizeW_le_mul_size opS K hK hOp l
    have hmk := exprSizeW_le_mul_size opS K hK hOp mk
    simp only [compSizeW, Comp.size]; nlinarith
  | foldM _ l z _ ihf =>
    have hl := exprSizeW_le_mul_size opS K hK hOp l
    have hz := exprSizeW_le_mul_size opS K hK hOp z
    simp only [compSizeW, Comp.size]; nlinarith

@[expose] def smOpS : SMOp → ℕ := fun _ => 125
@[expose] def smSampS : SMSamp → ℕ := fun _ => 10
@[expose] def smQueryS {Tag : Type} : Tag → ℕ := fun _ => 10

@[expose] def ckaOpS (B0 : ℕ) : CKAOp → ℕ
  | .fsReceive B => 3 * bits B0 + 2 * bits B + 1205
  | _ => 305

@[expose] def ckaSampS : CKASamp → ℕ := fun _ => 10
@[expose] def ckaQueryS {Tag : Type} : Tag → ℕ := fun _ => 10

theorem smOpMacro_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (lam : Pt) (o : SMOp) :
    (smOpMacro ℓ Pt C Dh encPt encT lam o).size + 1 ≤ smOpS o := by
  have h1 := eqMExpr_size ℓ Pt C Dh encPt encT lam
  have h2 := smEqCtExpr_size ℓ Pt C Dh encPt encT lam
  have h3 := smBlankExpr_size ℓ Pt C Dh encPt encT lam
  cases o <;> simp only [smOpMacro, smOpS, Expr.size] <;> omega

theorem ckaOpMacro_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (B0 : ℕ) (o : CKAOp) :
    (ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0 o).size + 1 ≤ ckaOpS B0 o := by
  have h1 := ckaInitAExpr_size ℓ Pt C Dh encPt encT lam
  have h2 := ckaInitBExpr_size ℓ Pt C Dh encPt encT lam
  have h3 := ckaSendExpr_size ℓ Pt C Dh encPt encT lam
  have h4 := ckaRecvExpr_size ℓ Pt C Dh encPt encT lam
  have h5 := prngInitExpr_size ℓ Pt C Dh encPt encT lam
  have h6 := prngUpExpr_size ℓ Pt C Dh encPt encT lam
  have h7 := fsInitSendExpr_size ℓ Pt C Dh encPt encT lam
  have h8 := fsInitRecvExpr_size ℓ Pt C Dh encPt encT lam
  have h9 := fsSendExpr_size ℓ Pt C Dh encPt encT lam
  have h10 := eqPtExpr_size ℓ Pt C Dh encPt encT lam
  have h11 := eqMExpr_size ℓ Pt C Dh encPt encT lam
  have h12 := eqEExpr_size ℓ Pt C Dh encPt encT lam
  have h13 := lamIExpr_size ℓ Pt C Dh encPt encT lam
  have h14 := defaultEExpr_size ℓ Pt C Dh encPt encT lam
  cases o with
  | fsReceive B =>
    have h15 := fsRecvExpr_size ℓ Pt C Dh encPt encT lam B0 B
    simp only [ckaOpMacro, ckaOpS]; omega
  | _ => simp only [ckaOpMacro, ckaOpS]; omega

end PureAuxSize

end

end Computational.Proofs.SessionCostedFig8.BundlesAuxSize
