/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthWireQueries
import Computational.Proofs.E2E.SignedThm5Gen
public import Computational.Proofs.SessionCostedFs
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRedBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.WireHop
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.GameHop.Rnd

/-!
# Multi-session direct-output (`advBit`) FS-AEAD game-level bridge (`[B7]`)

Combines the two-mode (`la = false` main-chain and `la = true` lookahead) multi-session libsignal
FS-AEAD session hybrids (`SessionWireQueries.sessionHybrid_fs_real_to_ideal_mix_le_of_adv`) and
the ideal-endpoint zero-output theorems (`SessionWire.allSessions_hp_eq_hpIdeal_main`,
`SessionWire.allSessions_hp_eq_hpIdeal_la`) into `fsAuthCompBoundMix` / `fsAuthCompBound` +
`4 * (qd * macForgeryProb C.F)` via `FSAEAD.Thm5.slotToHybridHopIndex` reindexing.-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.SessionAuthBridge

open scoped ENNReal
open OracleSpec OracleComp
open _root_.CryptoGames _root_.CryptoGames.FSAEAD _root_.CryptoGames.FSAEAD.Thm5
open _root_.CryptoGames.Ratchet _root_.CryptoGames.Ratchet.LibsignalInst
  _root_.CryptoGames.LibsignalSession
open _root_.CryptoGames.LibsignalSM.Proofs.SaltHopKeyed
  _root_.CryptoGames.LibsignalSM.Proofs.WireHop
open _root_.CryptoVerification.E2E.Signed _root_.CryptoVerification.E2E.Signed.FSMix
open _root_.CryptoVerification.E2E.Signed.SessionRouter
open _root_.CryptoVerification.E2E.Signed.SessionFS
  _root_.CryptoVerification.E2E.Signed.SessionHybrid
open _root_.CryptoVerification.E2E.Signed.SessionFSMix
  _root_.CryptoVerification.E2E.Signed.SessionMac
open _root_.CryptoVerification.E2E.Signed.SessionWire
  _root_.CryptoVerification.E2E.Signed.SessionQueries
open _root_.CryptoVerification.E2E.Signed.SessionWireQueries
open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out (advBit hRunOut multiRunOut
  cumulativeChainPrgReductionOut multiSlotOtccaReductionOut)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB ValidCoinSim CoinSimEquiv
  compCoinImpl simulateQ_compCoinImpl_run prgAdvantage_congr prfAdvantage_congr
  wireOtccaAdvantage_congr)
open Computational.Proofs.GameHop.Rnd (evalDistEq_bind_right_of_mem_support)
open _root_.CryptoVerification.LibsignalSession (fsCostedRedsInst fsAuthCompBound
  fsAuthCompBoundMix fsAuthPrgMix fsAuthSWMix chainPRGTermAuth saltPRFTermAuth wireOtccaTermAuth
  fsSlotCount fsAuthCompBoundWith fsAuthCompBoundWith_inst_eq fsAeadAuthMixtureCompBound_inst_eq
  pubToAD FsAdv signalRoundTripShort_proto signalEncodeFits32_proto)
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD

/-- Per-mode hybrid cutoff `N`: `qR` for main mode (`la = false`) and `qR + (maxSkip + 1)` for
lookahead mode (`la = true`). -/
@[expose] def authHopCutoff (maxSkip qR : ℕ) (la : Bool) : ℕ :=
  if la then qR + (maxSkip + 1) else qR

/-- Multi-session AD-level FS-AEAD adversary type over libsignal headers and ciphertexts. -/
abbrev MultiSessFsAdv (Pt : Type) (ℓ : ℕ) : Type :=
  OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) Bool

/-- Multi-session public-part FS-AEAD adversary type (`fsSpec` per session). -/
abbrev MultiSessPubFsAdv (Pt : Type) (ℓ : ℕ) : Type :=
  OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
    (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32)) Bool

/-- Lift single-session `pubToAD codec` (`FSAEAD.pubRed`) session-by-session to a multi-session
public-part FS-AEAD adversary. -/
@[expose] def multiSessPubToAD {Pt : Type} (codec : SignalMessageProtoCodec) {ℓ : ℕ}
    (AdvPub : MultiSessPubFsAdv Pt ℓ) : MultiSessFsAdv Pt ℓ :=
  let tag (s : ℕ) : QueryImpl
      (unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)))
    | .inl n => query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inl n)
    | .inr q => query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inr ⟨s, q⟩)
  let impl : QueryImpl
      (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
        (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32))
      (StateT (ℕ → Bool) (OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32))))
    | .inl n => StateT.lift (query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inl n))
    | .inr ⟨s, q⟩ => StateT.mk fun st => do
        let r ← simulateQ (tag s)
          ((FSAEAD.pubRedImpl
            (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (AD := Header Pt) (M := Plain ℓ)
            (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf codec c.2) (.inr q)).run (st s))
        return (r.1, Function.update st s r.2)
  (simulateQ impl AdvPub).run' (fun _ => false)

section
variable {ℓ : ℕ}

/-- Hypotheses packaging the query and AD-well-formedness conditions on a two-mode (`la : Bool`)
multi-session FS-AEAD adversary family `Adv : Bool → α → MultiSessFsAdv Pt ℓ`. -/
structure TwoModeMultiSessBounds {Pt : Type} [DecidableEq Pt] {α : Type}
    (maxSkip qR M qd : ℕ) (Adv : Bool → α → MultiSessFsAdv Pt ℓ) : Prop where
  offRange : ∀ la o, (Adv la o).IsQueryBoundP (fun t => sessOffRange M t = true) 0
  decBound : ∀ la o, (Adv la o).IsQueryBoundP (fun t => onAnySess fsInjQ t = true) qd
  shortAD : ∀ la o, (Adv la o).IsQueryBoundP (fun t => onAnySess (fsEncBadAD shortOk) t = true) 0
  guardedShort : ∀ la o, GuardedMultiInjectShort (Adv la o)
  oneADClass : ∀ la j o, ∃ k₀, (Adv la o).IsQueryBoundP
    (fun t => onSess (fsOutsideClass
      (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true) 0

end

/-- Compatibility of a single-session public-part `FsAdv` family `A : Bool → Bool → ℕ → α → FsAdv Pt ℓ`
with the router adversaries `lSessAdv` (`stage = false`) and `lWireSessAdv` (`stage = true`) of
`Adv`. -/
structure RouterAdvCompat {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip qR M : ℕ)
    (Adv : Bool → α → MultiSessFsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → α → FsAdv Pt ℓ) : Prop where
  saltCompat : ∀ la j, j < M → ∀ o ∈ support oa,
    CoinSimEquiv
      (fun n => query (spec := unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      (pubToAD codec (A false la j o))
      (lSessAdv C codec ℓ encT idOf maxSkip (authHopCutoff maxSkip qR la) la (Adv la) o j)
  wireCompat : ∀ la j, j < M → ∀ o ∈ support oa,
    CoinSimEquiv
      (fun n => query (spec := unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      (pubToAD codec (A true la j o))
      (lWireSessAdv C codec ℓ encT idOf maxSkip (authHopCutoff maxSkip qR la) la (Adv la)
        (hp (authHopCutoff maxSkip qR la) (authHopCutoff maxSkip qR la) la) o j)

private theorem evalDistEq_simulateQ_liftM {κ : Type} {H : OracleSpec.{0, 0} κ}
    {σ : Type} (impl : QueryImpl (unifSpec + H) (StateT σ ProbComp))
    (himpl : ValidCoinSim (fun n => query (spec := unifSpec + H) (.inl n)) impl)
    {α : Type} (p : ProbComp α) :
    ∀ (s : σ),
      (simulateQ impl (liftM p : OracleComp (unifSpec + H) α)).run s =ᵈ
        (p >>= fun a => pure (a, s)) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    intro s
    simp
  | query_bind n k ih =>
    intro s
    change (simulateQ impl
        ((query (spec := unifSpec + H) (.inl n)) >>= fun u =>
          (liftM (k u) : OracleComp (unifSpec + H) α))).run s =ᵈ _
    rw [simulateQ_bind, StateT.run_bind]
    refine ((himpl.coin_eq n s).bind fun z => ih z.1 z.2).trans ?_
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl

private theorem coinSimEquiv_liftM_bind_of_support {κ α β : Type} {H : OracleSpec.{0, 0} κ}
    (oa : ProbComp α) (D₁ D₂ : α → OracleComp (unifSpec + H) β)
    (hD : ∀ o ∈ support oa,
      CoinSimEquiv (fun n => query (spec := unifSpec + H) (.inl n)) (D₁ o) (D₂ o)) :
    CoinSimEquiv (fun n => query (spec := unifSpec + H) (.inl n))
      ((liftM oa : OracleComp (unifSpec + H) α) >>= D₁)
      ((liftM oa : OracleComp (unifSpec + H) α) >>= D₂) := ⟨by
  intro σ impl himpl s
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  have hL : ((simulateQ impl (liftM oa : OracleComp (unifSpec + H) α)).run s >>=
      fun z => (simulateQ impl (D₁ z.1)).run z.2) =ᵈ
      (oa >>= fun o => (simulateQ impl (D₁ o)).run s) := by
    refine ((evalDistEq_simulateQ_liftM impl himpl oa s).bind fun _ => EvalDistEq.rfl).trans ?_
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl
  have hR : ((simulateQ impl (liftM oa : OracleComp (unifSpec + H) α)).run s >>=
      fun z => (simulateQ impl (D₂ z.1)).run z.2) =ᵈ
      (oa >>= fun o => (simulateQ impl (D₂ o)).run s) := by
    refine ((evalDistEq_simulateQ_liftM impl himpl oa s).bind fun _ => EvalDistEq.rfl).trans ?_
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl
  have hM : (oa >>= fun o => (simulateQ impl (D₁ o)).run s) =ᵈ
      (oa >>= fun o => (simulateQ impl (D₂ o)).run s) :=
    evalDistEq_bind_right_of_mem_support oa fun o ho => (hD o ho).run_eq impl himpl s
  exact hL.trans (hM.trans hR.symm)⟩

private theorem coinSimEquiv_simulateQ_run {κ ι σ₁ α : Type}
    {G : OracleSpec.{0, 0} κ} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    (h : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T)))
    (hInl : ∀ (n : ℕ) (s₁ : σ₁), (h (.inl n)).run s₁ = (fwdU n >>= fun u => pure (u, s₁)))
    {oa₁ oa₂ : OracleComp (unifSpec + G) α}
    (hoa : CoinSimEquiv (fun n => query (spec := unifSpec + G) (.inl n)) oa₁ oa₂)
    (s₁ : σ₁) :
    CoinSimEquiv fwdU ((simulateQ h oa₁).run s₁) ((simulateQ h oa₂).run s₁) := ⟨by
  intro σ₂ impl himpl s₂
  have hv : ValidCoinSim (fun n => query (spec := unifSpec + G) (.inl n))
      (compCoinImpl h impl) := ⟨by
    intro n ⟨s₁', s₂'⟩
    rw [simulateQ_HasQuery_query]
    change (do
      let z ← (simulateQ impl ((h (.inl n)).run s₁')).run s₂'
      pure (z.1.1, (z.1.2, z.2))) =ᵈ
      ((query (m := ProbComp) (spec := unifSpec) n) >>= fun u => pure (u, (s₁', s₂')))
    rw [hInl n s₁', simulateQ_bind, StateT.run_bind]
    refine (((himpl.coin_eq n s₂').bind fun w => by
      simp only [simulateQ_pure, StateT.run_pure]
      exact EvalDistEq.rfl).bind fun _ => EvalDistEq.rfl).trans ?_
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl⟩
  rw [simulateQ_compCoinImpl_run h impl oa₁ s₁ s₂,
    simulateQ_compCoinImpl_run h impl oa₂ s₁ s₂]
  exact (hoa.run_eq (compCoinImpl h impl) hv (s₁, s₂)).map _⟩

private theorem cumulativeChainPrgReductionOut_evalDistEq
    {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip j : ℕ)
    (F : Bool → HState CK MK AD M C → Bool)
    {B₁ B₂ : RatchetAdversary CK MK AD M C}
    (hB : CoinSimEquiv (fun n => query (spec := unifSpec + fsSpec CK MK AD M C) (.inl n)) B₁ B₂)
    (mt : CK × MK) :
    cumulativeChainPrgReductionOut ideal ae G maxSkip j F B₁ mt =ᵈ
      cumulativeChainPrgReductionOut ideal ae G maxSkip j F B₂ mt := by
  unfold cumulativeChainPrgReductionOut hRunOut
  rw [← _root_.CryptoGames.FSAEAD.Thm5.Costed.multiImplWith_zero_none ideal ae G maxSkip
    (hp (j / 2) 0 (isLookaheadHop j)) (DG G) rfl]
  refine EvalDistEq.rfl.bind fun b => ?_
  have hrun := (coinSimEquiv_simulateQ_run
    (fun n => query (spec := unifSpec) n)
    (multiImplWith ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j))
      0 (DG G) (none : Option (SpecialOps AD M C ProbComp)))
    (fun n s => by
      rw [_root_.CryptoGames.FSAEAD.Thm5.Costed.multiImplWith_inl_run]
      simp [map_eq_bind_pure_comp])
    hB (hInit b (.mat (j / 2) mt))).evalDistEq_unifSpec
  exact hrun.bind fun _ => EvalDistEq.rfl

private theorem multiSlotOtccaReductionOut_coinSimEquiv
    {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip N : ℕ) (la : Bool)
    (F : Bool → HState CK MK AD M C → Bool)
    {B₁ B₂ : RatchetAdversary CK MK AD M C}
    (hB : CoinSimEquiv (fun n => query (spec := unifSpec + fsSpec CK MK AD M C) (.inl n)) B₁ B₂) :
    CoinSimEquiv (fun n => query (spec := IndexedOtccaSpec AD M C) (.inl n))
      (multiSlotOtccaReductionOut ideal ae G maxSkip N la F B₁)
      (multiSlotOtccaReductionOut ideal ae G maxSkip N la F B₂) := by
  unfold multiSlotOtccaReductionOut multiRunOut
  refine coinSimEquiv_liftM_bind_of_support ($ᵗ Bool) _ _ fun b _ => ?_
  refine (coinSimEquiv_simulateQ_run
    (fun n => query (spec := IndexedOtccaSpec AD M C) (.inl n))
    (multiImplWith ideal ae G maxSkip (hp N 0 la) N (DG G)
      (some (otOpsWith ideal)))
    (fun n s => by
      rw [_root_.CryptoGames.FSAEAD.Thm5.Costed.multiImplWith_inl_run]
      rfl)
    hB (hInit b .unknown)).bind fun _ => CoinSimEquiv.refl _

private theorem slotSaltRed_coinSimEquiv {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N k : ℕ)
    {B₁ B₂ : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32}
    (hB : CoinSimEquiv (fun n => query (spec := IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      B₁ B₂) :
    CoinSimEquiv (fun n => query (spec := IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      (slotSaltRed C codec ℓ encT idOf N k B₁)
      (slotSaltRed C codec ℓ encT idOf N k B₂) := by
  unfold slotSaltRed
  refine coinSimEquiv_liftM_bind_of_support _ _ _ fun K₀ _ => ?_
  refine coinSimEquiv_liftM_bind_of_support _ _ _ fun ks _ => ?_
  exact (coinSimEquiv_simulateQ_run
    (fun n => query (spec := IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
    _ (fun _ _ => rfl) hB _).map Prod.fst

private theorem slotWireRed_coinSimEquiv {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : ℕ)
    {B₁ B₂ : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32}
    (hB : CoinSimEquiv (fun n => query (spec := IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      B₁ B₂) :
    CoinSimEquiv (fun n => query (spec := IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      (slotWireRed C codec ℓ encT idOf k B₁)
      (slotWireRed C codec ℓ encT idOf k B₂) := by
  unfold slotWireRed
  exact (coinSimEquiv_simulateQ_run
    (fun n => query (spec := IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
    _ (fun _ _ => rfl) hB _).map Prod.fst

private theorem lSaltRed_coinSimEquiv {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {B₁ B₂ : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32}
    (hB : CoinSimEquiv (fun n => query (spec := IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      B₁ B₂) :
    CoinSimEquiv (fun n => query (spec := unifSpec + prfSpec Salt32 DerivedMessageKeys) (.inl n))
      (lSaltRed C codec ℓ encT idOf B₁)
      (lSaltRed C codec ℓ encT idOf B₂) := by
  unfold lSaltRed
  refine coinSimEquiv_liftM_bind_of_support _ _ _ fun b _ => ?_
  simp only [StateT.run']
  exact ((coinSimEquiv_simulateQ_run
    (fun n => query (spec := unifSpec + prfSpec Salt32 DerivedMessageKeys) (.inl n))
    _ (fun _ _ => rfl) hB none).map Prod.fst).bind fun _ => CoinSimEquiv.refl _

private theorem lWireRed_coinSimEquiv {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    {B₁ B₂ : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32}
    (hB : CoinSimEquiv (fun n => query (spec := IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      B₁ B₂) :
    CoinSimEquiv (fun n => query (spec := LibsignalWireOracleSpec ℓ) (.inl n))
      (lWireRed C codec ℓ encT idOf j B₁)
      (lWireRed C codec ℓ encT idOf j B₂) := by
  rw [lWireRed_eq, lWireRed_eq]
  exact (coinSimEquiv_simulateQ_run
    (fun n => query (spec := LibsignalWireOracleSpec ℓ) (.inl n))
    (wRedImpl C codec ℓ encT idOf j) (fun _ _ => rfl) hB ([], [], false, false)).bind
    fun _ => CoinSimEquiv.refl _

private theorem mode_session_sum_eq {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip qR : ℕ)
    (Adv : Bool → α → MultiSessFsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → α → FsAdv Pt ℓ)
    {M : ℕ} (hcompat : RouterAdvCompat C codec ℓ encT oa idOf maxSkip qR M Adv A)
    (la : Bool) {j : ℕ} (hj : j < M) :
    let N := authHopCutoff maxSkip qR la
    (lSaltPre C codec ℓ encT oa idOf maxSkip N la (Adv la) j +
      ∑ k ∈ Finset.range N, 2 * (lSaltPRF32 C.F).prfAdvantage
        (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
          (slotSaltRed C codec ℓ encT (idOf o) N k
            (lSaltD C codec ℓ encT idOf maxSkip N la (Adv la) j o)))) +
      ∑ k ∈ Finset.range N, (lWire C codec ℓ).wireOtccaAdvantage
        (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
          (slotWireRed C codec ℓ encT (idOf o) k
            (lWireE C codec ℓ encT idOf maxSkip N la (Adv la) (hp N N la) j o))) =
      ∑ k ∈ Finset.range N,
        (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
          (fun o => A false (isLookaheadHop (2 * k + la.toNat)) j o) (2 * k + la.toNat) +
          fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
            (fun o => A false (isLookaheadHop (2 * k + la.toNat)) j o)
            (fun o => A true (isLookaheadHop (2 * k + la.toNat)) j o) (2 * k + la.toNat)) := by
  dsimp only [lSaltPre]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hdiv : (2 * k + la.toNat) / 2 = k := by
    cases la <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have hla : isLookaheadHop (2 * k + la.toNat) = la := by
    cases la <;> simp [isLookaheadHop, Nat.add_mod]
  have hcut_eq : (if la then qR + (maxSkip + 1) else qR) = authHopCutoff maxSkip qR la := rfl
  unfold fsAuthPrgMix fsAuthSWMix
  rw [hla, hdiv]
  dsimp only
  rw [hcut_eq, add_assoc]
  refine congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) (congrArg (2 * ·) ?_) ?_)
  · refine prgAdvantage_congr (lChainPRG C.F k) fun mt => ?_
    exact evalDistEq_bind_right_of_mem_support oa fun o ho =>
      cumulativeChainPrgReductionOut_evalDistEq
        (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
        (lChainPRG C.F) maxSkip (2 * k + la.toNat) advBit
        (hcompat.saltCompat la j hj o ho).symm mt
  · exact prfAdvantage_congr (lSaltPRF32 C.F)
      (coinSimEquiv_liftM_bind_of_support oa _ _ fun o ho =>
        lSaltRed_coinSimEquiv C codec ℓ encT (idOf o)
          (slotSaltRed_coinSimEquiv C codec ℓ encT (idOf o) (authHopCutoff maxSkip qR la) k
            (multiSlotOtccaReductionOut_coinSimEquiv
              (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
              (lChainPRG C.F) maxSkip (authHopCutoff maxSkip qR la) la advBit
              (hcompat.saltCompat la j hj o ho).symm)))
  · exact wireOtccaAdvantage_congr (lWire C codec ℓ)
      (coinSimEquiv_liftM_bind_of_support oa _ _ fun o ho =>
        lWireRed_coinSimEquiv C codec ℓ encT (idOf o) 0
          (slotWireRed_coinSimEquiv C codec ℓ encT (idOf o) k
            (multiSlotOtccaReductionOut_coinSimEquiv
              (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
              (lChainPRG C.F) maxSkip (authHopCutoff maxSkip qR la) la advBit
              (hcompat.wireCompat la j hj o ho).symm)))

/-- Two-mode multi-session FS-AEAD hybrid bound into `fsAuthCompBoundMix`.
When both ideal endpoints (`hp qR qR false` for `la = false` and
`hp (qR + (maxSkip + 1)) (qR + (maxSkip + 1)) true` for `la = true`) output `true` with probability
`0`, twice the sum of the two real-hybrid (`hp 0 0 false` and `hp 0 0 true`) acceptance
probabilities is bounded by `∑ j < M, fsAuthCompBoundMix … (A · · j ·) + 4 * (qd * macForgeryProb)`. -/
theorem sessionHybrid_two_modes_le_sum_fsAuthCompBoundMix
    {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip qR M qd : ℕ)
    (Adv : Bool → α → MultiSessFsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → α → FsAdv Pt ℓ)
    (hrt : SignalRoundTripShort codec) (hfit : SignalEncodeFits32 codec)
    (hℓ : ℓ + 16 < 2 ^ 31 + 16) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey)
    (hcut : qR + (maxSkip + 1) ≤ 2 ^ 32)
    (hbds : TwoModeMultiSessBounds maxSkip qR M qd Adv)
    (hcompat : RouterAdvCompat C codec ℓ encT oa idOf maxSkip qR M Adv A)
    (hendFalse : 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
      (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
        (lChainPRG C.F) maxSkip (hp qR qR false)))) (Adv false o)).run (fun _ => none)] {true} = 0)
    (hendTrue : 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
      (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
        (lChainPRG C.F) maxSkip (hp (qR + (maxSkip + 1)) (qR + (maxSkip + 1)) true))))
      (Adv true o)).run (fun _ => none)] {true} = 0) :
    2 * (𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
            (lChainPRG C.F) maxSkip (hp 0 0 false)))) (Adv false o)).run (fun _ => none)] {true} +
        𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
            (lChainPRG C.F) maxSkip (hp 0 0 true)))) (Adv true o)).run (fun _ => none)] {true}) ≤
      (∑ j ∈ Finset.range M,
        fsAuthCompBoundMix C codec ℓ encT oa idOf maxSkip qR (fun stage la o => A stage la j o)) +
      4 * ((qd : ℝ≥0∞) * macForgeryProb C.F) := by
  have hqR32 : qR ≤ 2 ^ 32 := by omega
  have hFalse := sessionHybrid_fs_real_to_ideal_mix_le_of_adv C codec ℓ encT oa idOf maxSkip
    qR false (Adv false) hrt hfit hℓ hinj hdum hqR32 M (hbds.offRange false)
    (hbds.decBound false) (hbds.shortAD false) (hbds.guardedShort false)
    (hbds.oneADClass false)
  have hTrue := sessionHybrid_fs_real_to_ideal_mix_le_of_adv C codec ℓ encT oa idOf maxSkip
    (qR + (maxSkip + 1)) true (Adv true) hrt hfit hℓ hinj hdum hcut M (hbds.offRange true)
    (hbds.decBound true) (hbds.shortAD true) (hbds.guardedShort true)
    (hbds.oneADClass true)
  rw [MeasureTheory.Measure.boolDist, hendFalse, ENNReal.absDiff_zero_right] at hFalse
  rw [MeasureTheory.Measure.boolDist, hendTrue, ENNReal.absDiff_zero_right] at hTrue
  have hEqFalse :
      (∑ j ∈ Finset.range M,
        (lSaltPre C codec ℓ encT oa idOf maxSkip qR false (Adv false) j +
          ∑ k ∈ Finset.range qR, 2 * (lSaltPRF32 C.F).prfAdvantage
            (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
              (slotSaltRed C codec ℓ encT (idOf o) qR k
                (lSaltD C codec ℓ encT idOf maxSkip qR false (Adv false) j o))))) +
      (qd : ℝ≥0∞) * macForgeryProb C.F +
      ∑ j ∈ Finset.range M,
        ∑ k ∈ Finset.range qR, (lWire C codec ℓ).wireOtccaAdvantage
          (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
            (slotWireRed C codec ℓ encT (idOf o) k
              (lWireE C codec ℓ encT idOf maxSkip qR false (Adv false) (hp qR qR false) j o))) =
      (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range qR,
        (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
          (fun o => A false (isLookaheadHop (2 * k)) j o) (2 * k) +
          fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
            (fun o => A false (isLookaheadHop (2 * k)) j o)
            (fun o => A true (isLookaheadHop (2 * k)) j o) (2 * k))) +
      (qd : ℝ≥0∞) * macForgeryProb C.F := by
    rw [add_right_comm, ← Finset.sum_add_distrib]
    refine congrArg (· + (qd : ℝ≥0∞) * macForgeryProb C.F) (Finset.sum_congr rfl fun j hj => ?_)
    simpa [authHopCutoff] using mode_session_sum_eq C codec ℓ encT oa idOf maxSkip qR Adv A
      hcompat false (Finset.mem_range.mp hj)
  have hEqTrue :
      (∑ j ∈ Finset.range M,
        (lSaltPre C codec ℓ encT oa idOf maxSkip (qR + (maxSkip + 1)) true (Adv true) j +
          ∑ k ∈ Finset.range (qR + (maxSkip + 1)), 2 * (lSaltPRF32 C.F).prfAdvantage
            (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
              (slotSaltRed C codec ℓ encT (idOf o) (qR + (maxSkip + 1)) k
                (lSaltD C codec ℓ encT idOf maxSkip (qR + (maxSkip + 1)) true (Adv true) j o))))) +
      (qd : ℝ≥0∞) * macForgeryProb C.F +
      ∑ j ∈ Finset.range M,
        ∑ k ∈ Finset.range (qR + (maxSkip + 1)), (lWire C codec ℓ).wireOtccaAdvantage
          (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
            (slotWireRed C codec ℓ encT (idOf o) k
              (lWireE C codec ℓ encT idOf maxSkip (qR + (maxSkip + 1)) true (Adv true)
                (hp (qR + (maxSkip + 1)) (qR + (maxSkip + 1)) true) j o))) =
      (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range (qR + (maxSkip + 1)),
        (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
          (fun o => A false (isLookaheadHop (2 * k + 1)) j o) (2 * k + 1) +
          fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
            (fun o => A false (isLookaheadHop (2 * k + 1)) j o)
            (fun o => A true (isLookaheadHop (2 * k + 1)) j o) (2 * k + 1))) +
      (qd : ℝ≥0∞) * macForgeryProb C.F := by
    rw [add_right_comm, ← Finset.sum_add_distrib]
    refine congrArg (· + (qd : ℝ≥0∞) * macForgeryProb C.F) (Finset.sum_congr rfl fun j hj => ?_)
    simpa [authHopCutoff] using mode_session_sum_eq C codec ℓ encT oa idOf maxSkip qR Adv A
      hcompat true (Finset.mem_range.mp hj)
  rw [hEqFalse] at hFalse
  rw [hEqTrue] at hTrue
  have hCombine :
      (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range qR,
        (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
          (fun o => A false (isLookaheadHop (2 * k)) j o) (2 * k) +
          fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
            (fun o => A false (isLookaheadHop (2 * k)) j o)
            (fun o => A true (isLookaheadHop (2 * k)) j o) (2 * k))) +
      (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range (qR + (maxSkip + 1)),
        (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
          (fun o => A false (isLookaheadHop (2 * k + 1)) j o) (2 * k + 1) +
          fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
            (fun o => A false (isLookaheadHop (2 * k + 1)) j o)
            (fun o => A true (isLookaheadHop (2 * k + 1)) j o) (2 * k + 1))) =
      ∑ j ∈ Finset.range M, ∑ s ∈ Finset.range (slotCount maxSkip qR),
        (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
          (fun o => A false (isLookaheadHop (slotToHybridHopIndex qR s)) j o)
          (slotToHybridHopIndex qR s) +
          fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
            (fun o => A false (isLookaheadHop (slotToHybridHopIndex qR s)) j o)
            (fun o => A true (isLookaheadHop (slotToHybridHopIndex qR s)) j o)
            (slotToHybridHopIndex qR s)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (sum_range_hopIdx
      (fun m => fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
          (fun o => A false (isLookaheadHop m) j o) m +
        fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
          (fun o => A false (isLookaheadHop m) j o)
          (fun o => A true (isLookaheadHop m) j o) m) maxSkip qR).symm
  calc 2 * (𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
            (lChainPRG C.F) maxSkip (hp 0 0 false)))) (Adv false o)).run (fun _ => none)] {true} +
        𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
            (lChainPRG C.F) maxSkip (hp 0 0 true)))) (Adv true o)).run (fun _ => none)] {true})
      ≤ 2 * (((∑ j ∈ Finset.range M, ∑ k ∈ Finset.range qR,
            (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
              (fun o => A false (isLookaheadHop (2 * k)) j o) (2 * k) +
              fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
                (fun o => A false (isLookaheadHop (2 * k)) j o)
                (fun o => A true (isLookaheadHop (2 * k)) j o) (2 * k))) +
          (qd : ℝ≥0∞) * macForgeryProb C.F) +
        ((∑ j ∈ Finset.range M, ∑ k ∈ Finset.range (qR + (maxSkip + 1)),
            (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
              (fun o => A false (isLookaheadHop (2 * k + 1)) j o) (2 * k + 1) +
              fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
                (fun o => A false (isLookaheadHop (2 * k + 1)) j o)
                (fun o => A true (isLookaheadHop (2 * k + 1)) j o) (2 * k + 1))) +
          (qd : ℝ≥0∞) * macForgeryProb C.F)) := by
        gcongr
    _ = 2 * ((∑ j ∈ Finset.range M, ∑ k ∈ Finset.range qR,
            (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
              (fun o => A false (isLookaheadHop (2 * k)) j o) (2 * k) +
              fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
                (fun o => A false (isLookaheadHop (2 * k)) j o)
                (fun o => A true (isLookaheadHop (2 * k)) j o) (2 * k))) +
          (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range (qR + (maxSkip + 1)),
            (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip
              (fun o => A false (isLookaheadHop (2 * k + 1)) j o) (2 * k + 1) +
              fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR
                (fun o => A false (isLookaheadHop (2 * k + 1)) j o)
                (fun o => A true (isLookaheadHop (2 * k + 1)) j o) (2 * k + 1)))) +
        4 * ((qd : ℝ≥0∞) * macForgeryProb C.F) := by
        ring
    _ = (∑ j ∈ Finset.range M,
          fsAuthCompBoundMix C codec ℓ encT oa idOf maxSkip qR (fun stage la o => A stage la j o)) +
        4 * ((qd : ℝ≥0∞) * macForgeryProb C.F) := by
        rw [hCombine, Finset.mul_sum]
        rfl

private theorem fsAuthCompBoundMix_pure_eq {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (qR qd : ℕ)
    (A : Bool → Bool → FsAdv Pt ℓ) :
    fsAuthCompBoundMix C codec ℓ encT (pure ()) (fun _ => idOf) maxForwardJumps qR
        (fun stage la _ => A stage la) =
      fsAuthCompBound C codec ℓ encT idOf qR qd A := by
  unfold fsAuthCompBoundMix fsAuthCompBound
  have hslot : slotCount maxForwardJumps qR = fsSlotCount qR := rfl
  rw [hslot]
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun k _ => ?_)
  dsimp only
  unfold fsAuthPrgMix chainPRGTermAuth fsAuthSWMix saltPRFTermAuth wireOtccaTermAuth
  have hprg : prgAvg (pure ()) (fun (_ : Unit) =>
      cumulativeChainPrgReductionOut (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (slotToHybridHopIndex qR k) advBit
        (pubToAD codec (A false (isLookaheadHop (slotToHybridHopIndex qR k))))) =
      cumulativeChainPrgReductionOut (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (slotToHybridHopIndex qR k) advBit
        (pubToAD codec (A false (isLookaheadHop (slotToHybridHopIndex qR k)))) := by
    funext mt
    exact pure_bind () _
  rw [hprg]
  dsimp only [prfAvg, wireAvg, Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth]
  simp only [liftM_pure, pure_bind]

/-- **Point-mass (`oa = pure ()`, `maxSkip = maxForwardJumps`) two-mode multi-session FS-AEAD
hybrid bound into `fsAuthCompBound`.** -/
theorem sessionHybrid_two_modes_le_sum_fsAuthCompBound
    {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (qR M qd : ℕ)
    (Adv : Bool → MultiSessFsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → FsAdv Pt ℓ)
    (hrt : SignalRoundTripShort codec) (hfit : SignalEncodeFits32 codec)
    (hℓ : ℓ + 16 < 2 ^ 31 + 16) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey)
    (hcut : qR + (maxForwardJumps + 1) ≤ 2 ^ 32)
    (hbds : TwoModeMultiSessBounds maxForwardJumps qR M qd (fun la (_ : Unit) => Adv la))
    (hcompat : RouterAdvCompat C codec ℓ encT (pure ()) (fun _ => idOf) maxForwardJumps qR M
      (fun la (_ : Unit) => Adv la) (fun stage la j _ => A stage la j))
    (hendFalse : 𝒟[Prod.fst <$> (simulateQ (sessLift
      (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp qR qR false)))) (Adv false)).run
      (fun _ => none)] {true} = 0)
    (hendTrue : 𝒟[Prod.fst <$> (simulateQ (sessLift
      (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp (qR + (maxForwardJumps + 1))
          (qR + (maxForwardJumps + 1)) true)))) (Adv true)).run (fun _ => none)] {true} = 0) :
    2 * (𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))) (Adv false)).run
          (fun _ => none)] {true} +
        𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))) (Adv true)).run
          (fun _ => none)] {true}) ≤
      (∑ j ∈ Finset.range M,
        fsAuthCompBound C codec ℓ encT idOf qR qd (fun stage la => A stage la j)) +
      4 * ((qd : ℝ≥0∞) * macForgeryProb C.F) := by
  have hMix := sessionHybrid_two_modes_le_sum_fsAuthCompBoundMix C codec ℓ encT (pure ())
    (fun _ => idOf) maxForwardJumps qR M qd (fun la _ => Adv la) (fun stage la j _ => A stage la j)
    hrt hfit hℓ hinj hdum hcut hbds hcompat
    (by simpa only [pure_bind] using hendFalse)
    (by simpa only [pure_bind] using hendTrue)
  simp only [pure_bind] at hMix
  refine hMix.trans (le_of_eq (congrArg (· + 4 * ((qd : ℝ≥0∞) * macForgeryProb C.F)) ?_))
  exact Finset.sum_congr rfl fun j _ =>
    fsAuthCompBoundMix_pure_eq C codec ℓ encT idOf qR qd (fun stage la => A stage la j)

/-- **Costed mixture corollary (`protoSignalCodec`, `maxSkip = 25000`) into
`CryptoVerification.E2E.fsAeadAuthMixtureCompBound`.** -/
theorem sessionHybrid_two_modes_le_sum_fsAeadAuthMixtureCompBound
    {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey) (qR M qd : ℕ)
    (Adv : Bool → α → MultiSessFsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → α → FsAdv Pt ℓ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hcut : qR + (25000 + 1) ≤ 2 ^ 32)
    (hbds : TwoModeMultiSessBounds 25000 qR M qd Adv)
    (hcompat : RouterAdvCompat C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT
      oa idOf 25000 qR M Adv A)
    (hA : ∀ j < M, ∀ stage la o, FSAEAD.MakesAtMostQueries (A stage la j o) qR)
    (hshort : ∀ j < M, ∀ stage la o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
        (A stage la j o))
    (hendFalse : 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
      (lazyInit fsInit (fsImpl (lIdeal C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT)
        (lAeadR C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT (idOf o))
        (lChainPRG C.F) 25000 (hp qR qR false)))) (Adv false o)).run (fun _ => none)] {true} = 0)
    (hendTrue : 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
      (lazyInit fsInit (fsImpl (lIdeal C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT)
        (lAeadR C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT (idOf o))
        (lChainPRG C.F) 25000 (hp (qR + (25000 + 1)) (qR + (25000 + 1)) true))))
      (Adv true o)).run (fun _ => none)] {true} = 0) :
    2 * (𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl (lIdeal C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT)
            (lAeadR C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT (idOf o))
            (lChainPRG C.F) 25000 (hp 0 0 false)))) (Adv false o)).run (fun _ => none)] {true} +
        𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl (lIdeal C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT)
            (lAeadR C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT (idOf o))
            (lChainPRG C.F) 25000 (hp 0 0 true)))) (Adv true o)).run (fun _ => none)] {true}) ≤
      (∑ j ∈ Finset.range M,
        CryptoVerification.E2E.fsAeadAuthMixtureCompBound
          C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ oa qR
          (fun o => fsCostedRedsInst C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ
            encT (idOf o) qR)
          (fun stage la o => A stage la j o)) +
      4 * ((qd : ℝ≥0∞) * macForgeryProb C.F) := by
  refine (sessionHybrid_two_modes_le_sum_fsAuthCompBoundMix C
    CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT oa idOf 25000 qR M qd Adv A
    signalRoundTripShort_proto signalEncodeFits32_proto (by omega) hinj hdum hcut hbds hcompat
    hendFalse hendTrue).trans (le_of_eq (congrArg (· + 4 * ((qd : ℝ≥0∞) * macForgeryProb C.F)) ?_))
  exact Finset.sum_congr rfl fun j hj =>
    (fsAeadAuthMixtureCompBound_inst_eq C ℓ encT oa idOf qR hℓ hinj
      (fun stage la o => A stage la j o)
      (hA j (Finset.mem_range.mp hj))
      (hshort j (Finset.mem_range.mp hj))).symm

/-- Costed point-mass corollary (`protoSignalCodec`) into `fsAuthCompBoundWith`. -/
theorem sessionHybrid_two_modes_le_sum_fsAuthCompBoundWith
    {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (qR M qd : ℕ)
    (Adv : Bool → MultiSessFsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → FsAdv Pt ℓ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hcut : qR + (maxForwardJumps + 1) ≤ 2 ^ 32)
    (hbds : TwoModeMultiSessBounds maxForwardJumps qR M qd (fun la (_ : Unit) => Adv la))
    (hcompat : RouterAdvCompat C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT
      (pure ()) (fun _ => idOf) maxForwardJumps qR M
      (fun la (_ : Unit) => Adv la) (fun stage la j _ => A stage la j))
    (hA : ∀ j < M, ∀ stage la, FSAEAD.MakesAtMostQueries (A stage la j) qR)
    (hshort : ∀ j < M, ∀ stage la,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
        (A stage la j))
    (hendFalse : 𝒟[Prod.fst <$> (simulateQ (sessLift
      (lazyInit fsInit (fsImpl (lIdeal C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT)
        (lAeadR C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp qR qR false)))) (Adv false)).run
      (fun _ => none)] {true} = 0)
    (hendTrue : 𝒟[Prod.fst <$> (simulateQ (sessLift
      (lazyInit fsInit (fsImpl (lIdeal C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT)
        (lAeadR C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp (qR + (maxForwardJumps + 1))
          (qR + (maxForwardJumps + 1)) true)))) (Adv true)).run (fun _ => none)] {true} = 0) :
    2 * (𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl (lIdeal C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT)
            (lAeadR C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))) (Adv false)).run
          (fun _ => none)] {true} +
        𝒟[Prod.fst <$> (simulateQ (sessLift
          (lazyInit fsInit (fsImpl (lIdeal C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT)
            (lAeadR C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))) (Adv true)).run
          (fun _ => none)] {true}) ≤
      (∑ j ∈ Finset.range M,
        fsAuthCompBoundWith C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ qR
          (fsCostedRedsInst C CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT idOf qR)
          (fun stage la => A stage la j)) +
      4 * ((qd : ℝ≥0∞) * macForgeryProb C.F) := by
  refine (sessionHybrid_two_modes_le_sum_fsAuthCompBound C
    CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT idOf qR M qd Adv A
    signalRoundTripShort_proto signalEncodeFits32_proto (by omega) hinj hdum hcut hbds hcompat
    hendFalse hendTrue).trans (le_of_eq (congrArg (· + 4 * ((qd : ℝ≥0∞) * macForgeryProb C.F)) ?_))
  exact Finset.sum_congr rfl fun j hj =>
    (fsAuthCompBoundWith_inst_eq C ℓ encT idOf qR qd hℓ hinj
      (fun stage la => A stage la j)
      (hA j (Finset.mem_range.mp hj))
      (hshort j (Finset.mem_range.mp hj))).symm

end Computational.Proofs.E2E.SessionAuthBridge
