/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalSim
public import Computational.Specifications.Session.ACD19.SM.Theorem8And12Statements
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs

/-!
# Adversary types, cost budgets and costed reduction bundles for the libsignal session bound

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `saltPRFTerm`, `wireOtccaTerm`, `multiSlotAdv` and `pubToAD`; the ones they use are part of
what you must read to trust the result. Those four are checked by Lean.
`Refine.SimProg`, `chainPRGTerm`, `fsShortBound`, `fsCompBound`, `fig8ShortBound` and their
`…With` forms are in `Computational/Proofs/SpecLemmas/Session/ACD19/Ratchet/LibsignalBound.lean`,
checked by Lean. See `Computational/docs/TRUSTED_BASE.md`.

This file defines the adversary types, the message-blanking map of ACD19 Lemma 18 (Alwen, Coretti,
Dodis, ePrint 2018/1037), the per-slot advantage terms of the symmetric-ratchet FS-AEAD bound, the
explicit syntactic step-cost budgets, and the `ReductionDsl` costed reduction bundles used by
`libsignal_session_sm_r1_proto`.

Every reduction in the session and E2E bounds is represented as a first-order
`ReductionDsl.CostedReduction` or `ReductionDsl.TwoStageCostedReduction` over `atomicSig ℓ Pt`
(`AtomicOps.lean`, `TargetCodecs.lean`), where every base sort carries an explicit 32-byte block
measure `sz` and multi-step chain iterations, skipped-key scans, and protobuf wire codecs are
accounted at primitive granularity. `GRedBounded` and `GTwoStageBounded` enforce single-execution
step-cost budgets (`ratchetCostBudget`, `fsRatchetCostBudget`, `ratchetFsAdapterBudget`), program
size, target query counts, operator/sampler size-honesty, and run-local state and output bounds,
while `GRedCostByKind` and `GRed2CostByKind` refine step-cost and target-query accounting when game
queries are split by kind (online vs. offline random-oracle queries).

Under the bucket-partitioned authenticity, `DeliverForge` parity-bucket, and switch-back privacy
reductions, the 8-byte MAC-forgery part of the per-session bound scales as
`O(qep · q · macForgeryProb)`: `4 * macForgeryTerm C q = 4 * q * macForgeryProb` is charged once
per chain or bucket across privacy (`qep + 2` challenge-epoch triples via `redFSPriv` and
`2 * redFSPrivCoin`), authenticity (`qep + 1` last-leak `tL` buckets, split into honest-header and
forged-header modes for `8 * macForgeryTerm C q` per bucket), and `DeliverForge` (`2 * qep + 1`
shifted boundary cells plus `≤ 2 * max 1 qep` unshifted `(tL, par)` buckets), with
`macForgeryProb ≥ 2⁻⁶⁴` for an 8-byte MAC tag. Compared with the earlier per-`(t, tL, j)` cell
bound, this bucket-partitioned bound is formally incomparable: it drops the MAC-forgery term from
`O(qep² · q² · macForgeryProb)` to `O(qep · q · macForgeryProb)` in exchange for up to `1.95×` more
PRF-PRNG terms, up to `1.74×` more FS-AEAD terms (for `q ≥ 1`; `2.33×` at `q = 0, qep = 1`), and a
re-indexed, enlarged reduction family under `ratchetCostBudget q (qep + 1)` (see DEV-LS31 and
DEV-C14 in `Computational/docs/DEVIATIONS.md`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

/-- `A` makes at most `q` queries to the Fig. 3 CKA oracles (its own coins are unrestricted). -/
def CryptoGames.CKA.MakesAtMostQueries {State Coins Msg CKey : Type}
    (A : CryptoGames.CKA.Adversary State Coins Msg CKey) (q : ℕ) : Prop :=
  A.IsQueryBoundP (· matches .inr _) q

/-- `A` makes at most `q` queries to the PRF-PRNG oracles (its own coins are unrestricted). -/
def CryptoGames.PRFPRNG.MakesAtMostQueries {State I Out : Type}
    (A : CryptoGames.PRFPRNG.Adversary State I Out) (q : ℕ) : Prop :=
  A.IsQueryBoundP (· matches .inr _) q

namespace CryptoGames.LibsignalSM

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD

/-! ## Adversaries and the blanking map -/

section Types

/-- Adversary against the Fig. 8 instance `lFig8` (messages `LibsignalMsgPublicPart × Plain ℓ`). -/
abbrev Fig8Adv (Pt : Type) (ℓ : ℕ) :=
  SM.Adversary (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt)

/-- Adversary against `libsignalSessionScheme` with fixed-length plaintexts `Plain ℓ`, SPQR send
coins `PQC`, and wire-byte ciphertexts.

**DEV-LS27 (formalization): one message length per session.** ACD19 Def. 8 allows arbitrary message
lengths and requires `|m₀| = |m₁|` only on challenges. Here every session message has `ℓ` bytes
(`Plain ℓ`, matching primitive-level DEV-AEAD2), as the wire format reveals the AES-CBC block
count. -/
abbrev LibAdv (PQ PQC : Type) (ℓ : ℕ) :=
  SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))

/-- Blanking map for ACD19 Lemma 18 on `lFig8`: keeps the public message part and zeroes the
plaintext (`ThmB.privRedB`; DEV-LS13). -/
def lBlank (ℓ : ℕ) (m : LibsignalMsgPublicPart × Plain ℓ) : LibsignalMsgPublicPart × Plain ℓ := (m.1, default)

end Types

end CryptoGames.LibsignalSM

namespace CryptoVerification.LibsignalSession

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD

/-! ## Symmetric-ratchet FS-AEAD bound terms -/

section Bounds

variable {Pt : Type} [DecidableEq Pt]

/-- Per-message AEAD ciphertext pairing wire `(ser, tag)` with the 32-byte SPQR salt. -/
abbrev LCt := LibsignalCiphertextWithSalt32

abbrev FsAdv (Pt : Type) (ℓ : ℕ) :=
  FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) LCt

/-- Active hybrid slot count `2 * qR + (maxForwardJumps + 1)` of ACD19 Theorem 5 for a `qR`-query
FS-AEAD adversary: at most `qR` main-chain slots and `qR + maxForwardJumps + 1` lookahead-chain
slots bounded by the skip window (DEV-LS10). -/
def fsSlotCount (qR : ℕ) : ℕ := 2 * qR + (maxForwardJumps + 1)

/-- Adapter moving the public message part into associated data (`FSAEAD.pubRed`; DEV-LS13). -/
def pubToAD (codec : SignalMessageProtoCodec) {ℓ : ℕ} (R : FsAdv Pt ℓ) :=
  FSAEAD.pubRed (fun c : ℕ × LCt => lPubOf codec c.2) R

/-- Multi-slot OT-CCA reduction of ACD19 Theorem 5 on the main (`la = false`) or lookahead
(`la = true`) chain with ideal ciphertexts `lIdeal`. -/
def multiSlotAdv (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (qR : ℕ) (la : Bool) (R : FsAdv Pt ℓ) :=
  FSAEAD.Thm5.multiSlotOtccaReduction (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) (lChainPRG C.F)
    maxForwardJumps (if la then qR + (maxForwardJumps + 1) else qR) la (pubToAD codec R)

/-- Slot `j` salt-PRF advantage of `lSaltRed ∘ slotSaltRed` against the message-key HKDF queried at
SPQR salts (`lSaltPRF32`; DEV-LS25). -/
noncomputable def saltPRFTerm (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (qR : ℕ) (R : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  let la := FSAEAD.Thm5.isLookaheadHop j
  (lSaltPRF32 C.F).prfAdvantage
    (lSaltRed C codec ℓ encT idOf
      (slotSaltRed C codec ℓ encT idOf
        (if la then qR + (maxForwardJumps + 1) else qR) (j / 2)
        (multiSlotAdv C codec ℓ encT idOf qR la R)))

/-- Slot `j` wire-AEAD OT-CCA advantage of `lWireRed 0 ∘ slotWireRed` against `lWire` at challenge
salt `0` (`_qd` is unused after hoisting the MAC-forgery bad event to the chain level). -/
noncomputable def wireOtccaTerm (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (qR _qd : ℕ) (R : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  let la := FSAEAD.Thm5.isLookaheadHop j
  (lWire C codec ℓ).wireOtccaAdvantage
    (lWireRed C codec ℓ encT idOf 0
      (slotWireRed C codec ℓ encT idOf (j / 2)
        (multiSlotAdv C codec ℓ encT idOf qR la R)))

/-- Per-chain MAC-forgery term `qd * macForgeryProb C.F` over at most `qd` decryptions (DEV-LS23),
charged twice per chain (`4 * macForgeryTerm C qd` per FS-AEAD instance). -/
noncomputable def macForgeryTerm (C : Crypto) (qd : ℕ) : ℝ≥0∞ := qd * macForgeryProb C.F

variable [Zero Pt] [SampleableType Pt]

/-! ## Costed reduction bundles and budgets -/

/-- Quadratic syntactic step-cost budget across session-layer reductions (`maxForwardJumps = 25000`). -/
def ratchetCostBudget (q qep : ℕ) : ℕ :=
  2 ^ 12 * (q + 1) ^ 2 * (maxForwardJumps + ReductionDsl.bits qep)

/-- Step-cost budget for the five single-slot and adapter reductions in `FsCostedReds` that perform
no `maxForwardJumps`-step chain iterations. -/
def ratchetFsAdapterBudget (qR qep : ℕ) : ℕ :=
  2 ^ 24 * (qR + 1) + 2 ^ 10 * (qR + 1) ^ 2 + 2 ^ 12 * (qR + 1) * ReductionDsl.bits qep

/-- Step-cost budget for the four two-stage FS-AEAD hybrid reductions (`prgRedZero`, `multiRed`,
`prgRedAuth`, `multiRedAuth`). -/
def fsRatchetCostBudget (q qep : ℕ) : ℕ :=
  min (ratchetCostBudget q qep)
    (2 ^ 14 * (q + 1) ^ 2 + 2 ^ 15 * (q + 1) * (maxForwardJumps + ReductionDsl.bits qep))

/-- Sequential evaluation of both stages of a unit-challenge `TwoStageCostedReduction` at query fuel
`fuel` and default output `dflt`. -/
def evalTwoStage1 {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut out : ReductionDsl.Ty S}
    (R : ReductionDsl.TwoStageCostedReduction O I G C rIn aIn aOut .unit .unit out)
    (fuel : ℕ) (dflt : aOut.denote)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) :
    OracleComp T out.denote := do
  let (_, m) ← R.eval1 A x fuel dflt
  R.eval2 m () fuel dflt

/-- Recursive block, bit, and list size bound on a `ReductionDsl` value (`ReductionDsl.ValFits`). -/
abbrev CostedFits {S : ReductionDsl.Sig} (B : ℕ) : (t : ReductionDsl.Ty S) → t.denote → Prop :=
  _root_.ReductionDsl.ValFits B

/-- Operator size-honesty obligation: each operator `o` increases the size bound by at most `O.cost o`. -/
abbrev CostedOpsSizeHonest {S : ReductionDsl.Sig}
    (O : ReductionDsl.Ops S) : Prop :=
  _root_.ReductionDsl.OpsSizeHonest O

/-- Sampler size-honesty obligation: each sampler `s` outputs values bounded by `X.sCost s`. -/
abbrev CostedSampSizeHonest {S : ReductionDsl.Sig}
    (X : ReductionDsl.Samplers S) : Prop :=
  _root_.ReductionDsl.SampSizeHonest X

/-- Step-cost, program-size, target-query, operator/sampler size-honesty, and run-local output/state
block-size bounds for a 1-stage `CostedReduction` at source query bound `q`, target query bound
`qOut`, and step-cost budget `costBudget`. Size bounds are quantified per run via `supportWhen
(I.AnswerFits B)` so interfaces with unbounded `Bytes` or `.nat` fields remain satisfiable. -/
def GRedBounded {S : ReductionDsl.Sig}
    {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut out : ReductionDsl.Ty S}
    (R : ReductionDsl.CostedReduction O I G C rIn aIn aOut out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ) : Prop :=
  R.totalCost q ≤ costBudget ∧
  R.size ≤ ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget ∧
  R.totalQueries wTag wSamp q ≤ qOut ∧
  CostedOpsSizeHonest O ∧
  CostedSampSizeHonest I.smp ∧
  ∀ (B : ℕ),
    (∀ v : aOut.denote, CostedFits B aOut v) →
    ∀ (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote),
      (∀ a, (A a).IsQueryBoundP (fun t => t.isRight = true) q) →
      (∀ a, ReductionDsl.AllGameQueriesFit B C (A a)) →
      ∀ (x : rIn.denote), CostedFits B rIn x →
        let widthB := 2 * (costBudget + q + 1) * (B + 1)
        (∀ y ∈ ReductionDsl.supportWhen (I.AnswerFits B) (R.eval A x), CostedFits widthB out y) ∧
        (∀ r0 ∈ ReductionDsl.supportWhen (I.AnswerFits B) (R.init.eval (.cons x .nil)),
          ∀ r1 ∈ ReductionDsl.supportWhen (I.AnswerFits B) ((simulateQ R.impl (A r0.1)).run r0.2),
            CostedFits widthB R.σ r1.2)

/-- Block-size bound on a two-stage mid-state. -/
@[reducible] def CostedMidFits {S : ReductionDsl.Sig} {κ : Type} {G : OracleSpec κ} {α : Type}
    (B : ℕ) (π σ ch : ReductionDsl.Ty S) :
    ReductionDsl.Mid G α π.denote σ.denote ch.denote → Prop
  | .done _ s => CostedFits B σ s
  | .paused _ c p s _ => CostedFits B ch c ∧ CostedFits B π p ∧ CostedFits B σ s

/-- Step-cost, program-size, target-query, operator/sampler size-honesty, and run-local mid-state
and output block-size bounds for a `TwoStageCostedReduction` at fuel `q`, target query bound `qOut`,
and step-cost budget `costBudget`. -/
def GTwoStageBounded {S : ReductionDsl.Sig}
    {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut ch rIn2 out : ReductionDsl.Ty S}
    (R : ReductionDsl.TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ) : Prop :=
  R.totalCost q ≤ costBudget ∧
  R.size ≤ ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget ∧
  R.totalQueries wTag wSamp q ≤ qOut ∧
  CostedOpsSizeHonest O ∧
  CostedSampSizeHonest I.smp ∧
  ∀ (B : ℕ),
    (∀ v : aOut.denote, CostedFits B aOut v) →
    ∀ (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote),
      (∀ a, ReductionDsl.AllGameQueriesFit B C (A a)) →
      ∀ (x : rIn.denote), CostedFits B rIn x →
        ∀ (dflt : aOut.denote),
          let widthB := 2 * (costBudget + 2 * q + 1) * (B + 1)
          ∀ cm ∈ ReductionDsl.supportWhen (I.AnswerFits B) (R.eval1 A x q dflt),
            CostedFits widthB ch cm.1 ∧
            CostedMidFits widthB R.π R.σ ch cm.2 ∧
            ∀ (y : rIn2.denote), CostedFits B rIn2 y →
              ∀ z ∈ ReductionDsl.supportWhen (I.AnswerFits B) (R.eval2 cm.2 y q dflt),
                CostedFits widthB out z

/-- Per-kind step-cost and target-query bound for a 1-stage `CostedReduction` whose game queries
are partitioned by `kind : κ → Fin n` with per-kind budgets `qKind`: each query pays only its own
kind's handler cost (`CostBoundedByKind`), and total target queries over `(List.ofFn qKind).sum`
source queries are at most `qOut`. Paired alongside `GRedBounded` for size-honesty and run-local
value-size bounds. -/
def GRedCostByKind {S : ReductionDsl.Sig}
    {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut out : ReductionDsl.Ty S}
    (R : ReductionDsl.CostedReduction O I G C rIn aIn aOut out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ) (qOut costBudget : ℕ) : Prop :=
  R.CostBoundedByKind kind qKind costBudget ∧
  R.totalQueries wTag wSamp (List.ofFn qKind).sum ≤ qOut

/-- Per-kind step-cost and target-query bound for a `TwoStageCostedReduction` under query partition
`kind` and budgets `qKind`, requiring `CostBoundedByKind` across both stages, zero pre-challenge
target queries (`init`, `handlePre`, `chDone`), and at most `qOut` total target queries. Paired
alongside `GRed2Bounded` for size-honesty and run-local value-size bounds. -/
def GRed2CostByKind {S : ReductionDsl.Sig}
    {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut ch rIn2 out : ReductionDsl.Ty S}
    (R : ReductionDsl.TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ) (qOut costBudget : ℕ) : Prop :=
  R.CostBoundedByKind kind qKind costBudget ∧
  R.init.queries wTag wSamp + R.handlePre.queries wTag wSamp + R.chDone.queries wTag wSamp = 0 ∧
  R.totalQueries wTag wSamp (List.ofFn qKind).sum ≤ qOut

omit [Zero Pt] [SampleableType Pt] in
/-- Costed reduction programs for ACD19 Theorem 5 (`pubRed`, two-stage `prgRedZero` / `multiRed`,
and direct-output `prgRedAuth` / `multiRedAuth`) and the per-message AEAD salt and wire hops on
libsignal's symmetric ratchet (`fsShortBound`). -/
structure FsCostedReds (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) where
  /-- Public-header projection reduction `FSAEAD.pubRed` (`DEV-LS13`). -/
  pubRed :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFsOps ℓ Pt C encT)
      (ReductionDsl.fsaeadPubTargetIface ℓ Pt)
      (FSAEAD.spec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt))
      (ReductionDsl.fsaeadPubCodec ℓ Pt) .unit .unit .bool .bool
  /-- Cumulative chain-PRG reduction `FSAEAD.Thm5.cumulativeChainPrgReduction` at hop index `j`. -/
  prgRedZero : (j : ℕ) →
    ReductionDsl.TwoStageCostedReduction
      (ReductionDsl.atomicFsOps ℓ Pt C encT)
      (ReductionDsl.coinOnlyBaseIface ℓ Pt)
      (FSAEAD.spec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) (ℕ × LCt))
      (ReductionDsl.fsaeadRatchetCodec ℓ Pt)
      (.prod ReductionDsl.BV256 ReductionDsl.BV256) .unit .bool .unit .unit .bool
  /-- Multi-slot OT-CCA reduction `FSAEAD.Thm5.multiSlotOtccaReduction` for chain `la : Bool`. -/
  multiRed : (la : Bool) →
    ReductionDsl.TwoStageCostedReduction
      (ReductionDsl.atomicFsOps ℓ Pt C encT)
      (ReductionDsl.slotOtccaTargetIface ℓ Pt)
      (FSAEAD.spec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) (ℕ × LCt))
      (ReductionDsl.fsaeadRatchetCodec ℓ Pt) .unit .unit .bool .unit .unit .bool
  /-- Multi-to-single-slot salt-PRF wrapper `slotSaltRed` at hop index `j`. -/
  slotSaltRed : (j : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFsOps ℓ Pt C encT)
      (ReductionDsl.slotOtccaTargetIface ℓ Pt)
      (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
      (ReductionDsl.slotOtccaCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Single-slot salt-PRF reduction `lSaltRed`. -/
  lSaltRed :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFsOps ℓ Pt C encT)
      (ReductionDsl.saltPrfTargetIface ℓ Pt)
      (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
      (ReductionDsl.slotOtccaCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Multi-to-single-slot wire-OT-CCA wrapper `slotWireRed` at hop index `j`. -/
  slotWireRed : (j : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFsOps ℓ Pt C encT)
      (ReductionDsl.slotOtccaTargetIface ℓ Pt)
      (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
      (ReductionDsl.slotOtccaCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Single-slot wire-OT-CCA reduction `lWireRed 0`. -/
  lWireRed :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFsOps ℓ Pt C encT)
      (ReductionDsl.wireOtccaTargetIface ℓ Pt)
      (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
      (ReductionDsl.slotOtccaCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Direct-output cumulative chain-PRG reduction at hop index `j` for multi-session authenticity
  and `DeliverForge` telescopes (returning the `FsAdv`'s `Bool` output directly rather than `hOut`,
  so internal-session wins and lookahead flags propagate across external-session encryption hops). -/
  prgRedAuth : (j : ℕ) →
    ReductionDsl.TwoStageCostedReduction
      (ReductionDsl.atomicFsOps ℓ Pt C encT)
      (ReductionDsl.coinOnlyBaseIface ℓ Pt)
      (FSAEAD.spec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) (ℕ × LCt))
      (ReductionDsl.fsaeadRatchetCodec ℓ Pt)
      (.prod ReductionDsl.BV256 ReductionDsl.BV256) .unit .bool .unit .unit .bool
  /-- Direct-output multi-slot OT-CCA reduction for chain `la : Bool` in multi-session authenticity
  and `DeliverForge` telescopes (returning the `FsAdv`'s `Bool` output directly rather than `hOut`). -/
  multiRedAuth : (la : Bool) →
    ReductionDsl.TwoStageCostedReduction
      (ReductionDsl.atomicFsOps ℓ Pt C encT)
      (ReductionDsl.slotOtccaTargetIface ℓ Pt)
      (FSAEAD.spec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) (ℕ × LCt))
      (ReductionDsl.fsaeadRatchetCodec ℓ Pt) .unit .unit .bool .unit .unit .bool

omit [Zero Pt] [SampleableType Pt] in
/-- Cost, program-size, query-count, and run-local size bounds for an `FsCostedReds` bundle at
ratchet query bound `qR` and epoch cap `qep`: `ratchetFsAdapterBudget qR qep` on the five
lightweight adapter/single-slot reductions and `fsRatchetCostBudget qR qep` on the four two-stage
hybrid reductions (`prgRedZero`, `multiRed`, `prgRedAuth`, `multiRedAuth`). -/
def fsCostedBounds {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR qep : ℕ) (R : FsCostedReds C codec ℓ encT idOf) : Prop :=
  let B_adapt := ratchetFsAdapterBudget qR qep
  let B_hyb := fsRatchetCostBudget qR qep
  GRedBounded R.pubRed (fun _ => 1) (fun _ => 0) qR qR B_adapt ∧
  (∀ j < fsSlotCount qR,
    GTwoStageBounded (R.prgRedZero (FSAEAD.Thm5.slotToHybridHopIndex qR j)) Empty.elim (fun _ => 0) qR 0 B_hyb) ∧
  (∀ la : Bool,
    GTwoStageBounded (R.multiRed la) (fun _ => 1) (fun _ => 0) qR qR B_hyb) ∧
  (∀ j < fsSlotCount qR,
    GRedBounded (R.slotSaltRed (FSAEAD.Thm5.slotToHybridHopIndex qR j)) (fun _ => 1) (fun _ => 0) qR qR B_adapt) ∧
  GRedBounded R.lSaltRed (fun _ => 1) (fun _ => 0) qR qR B_adapt ∧
  (∀ j < fsSlotCount qR,
    GRedBounded (R.slotWireRed (FSAEAD.Thm5.slotToHybridHopIndex qR j)) (fun _ => 1) (fun _ => 0) qR qR B_adapt) ∧
  GRedBounded R.lWireRed (fun _ => 1) (fun _ => 0) qR qR B_adapt ∧
  (∀ j < fsSlotCount qR,
    GTwoStageBounded (R.prgRedAuth (FSAEAD.Thm5.slotToHybridHopIndex qR j)) Empty.elim (fun _ => 0) qR 0 B_hyb) ∧
  (∀ la : Bool,
    GTwoStageBounded (R.multiRedAuth la) (fun _ => 1) (fun _ => 0) qR qR B_hyb)

omit [Zero Pt] [SampleableType Pt] in
def pubToADCosted {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (R : FsCostedReds C codec ℓ encT idOf) (A : FsAdv Pt ℓ) :=
  R.pubRed.eval (fun _ => A) ()

omit [Zero Pt] [SampleableType Pt] in
def multiSlotAdvCosted {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR : ℕ) (R : FsCostedReds C codec ℓ encT idOf) (la : Bool) (A : FsAdv Pt ℓ) :=
  evalTwoStage1 (R.multiRed la) qR false (fun _ => pubToADCosted R A) ()

omit [Zero Pt] [SampleableType Pt] in
/-- `multiSlotAdv` evaluated via `R.multiRedAuth` and `R.pubRed` at query fuel `qR`
(direct-output authenticity form). -/
def multiSlotAdvAuthCosted {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR : ℕ) (R : FsCostedReds C codec ℓ encT idOf) (la : Bool) (A : FsAdv Pt ℓ) :=
  evalTwoStage1 (R.multiRedAuth la) qR false (fun _ => pubToADCosted R A) ()

omit [Zero Pt] [SampleableType Pt] in
/-- Slot `j` chain-PRG advantage evaluated via `R.prgRedZero` and `R.pubRed` at query fuel `qR`. -/
noncomputable def chainPRGTermCosted (C : Crypto) {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR : ℕ) (R : FsCostedReds C codec ℓ encT idOf) (A : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  (lChainPRG C.F (j / 2)).prgAdvantage
    (fun mt => evalTwoStage1 (R.prgRedZero j) qR false (fun _ => pubToADCosted R A) mt)

omit [Zero Pt] [SampleableType Pt] in
/-- Slot `j` chain-PRG advantage evaluated via `R.prgRedAuth` and `R.pubRed` at query fuel `qR`
(direct-output authenticity form). -/
noncomputable def chainPRGTermAuthCosted (C : Crypto) {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR : ℕ) (R : FsCostedReds C codec ℓ encT idOf) (A : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  (lChainPRG C.F (j / 2)).prgAdvantage
    (fun mt => evalTwoStage1 (R.prgRedAuth j) qR false (fun _ => pubToADCosted R A) mt)

omit [Zero Pt] [SampleableType Pt] in
/-- Slot `j` salt-PRF advantage evaluated on an `FsCostedReds` bundle. -/
noncomputable def saltPRFTermCosted (C : Crypto) {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR : ℕ) (R : FsCostedReds C codec ℓ encT idOf) (A : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  let la := FSAEAD.Thm5.isLookaheadHop j
  (lSaltPRF32 C.F).prfAdvantage
    (R.lSaltRed.eval
      (fun _ => (R.slotSaltRed j).eval (fun _ => multiSlotAdvCosted qR R la A) ()) ())

omit [Zero Pt] [SampleableType Pt] in
/-- Slot `j` salt-PRF advantage evaluated via `R.multiRedAuth` on an `FsCostedReds` bundle
(direct-output authenticity form). -/
noncomputable def saltPRFTermAuthCosted (C : Crypto) {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR : ℕ) (R : FsCostedReds C codec ℓ encT idOf) (A : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  let la := FSAEAD.Thm5.isLookaheadHop j
  (lSaltPRF32 C.F).prfAdvantage
    (R.lSaltRed.eval
      (fun _ => (R.slotSaltRed j).eval (fun _ => multiSlotAdvAuthCosted qR R la A) ()) ())

omit [Zero Pt] [SampleableType Pt] in
/-- Slot `j` wire-AEAD OT-CCA advantage evaluated on an `FsCostedReds` bundle. -/
noncomputable def wireOtccaTermCosted (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR : ℕ) (R : FsCostedReds C codec ℓ encT idOf) (A : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  let la := FSAEAD.Thm5.isLookaheadHop j
  (lWire C codec ℓ).wireOtccaAdvantage
    (R.lWireRed.eval
      (fun _ => (R.slotWireRed j).eval (fun _ => multiSlotAdvCosted qR R la A) ()) ())

omit [Zero Pt] [SampleableType Pt] in
/-- Slot `j` wire-AEAD OT-CCA advantage evaluated via `R.multiRedAuth` on an `FsCostedReds` bundle
(direct-output authenticity form). -/
noncomputable def wireOtccaTermAuthCosted (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR : ℕ) (R : FsCostedReds C codec ℓ encT idOf) (A : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  let la := FSAEAD.Thm5.isLookaheadHop j
  (lWire C codec ℓ).wireOtccaAdvantage
    (R.lWireRed.eval
      (fun _ => (R.slotWireRed j).eval (fun _ => multiSlotAdvAuthCosted qR R la A) ()) ())

/-- Costed reduction programs for ACD19 Theorem 1 (`challSim`), Lemma 18 (`privRedB`),
bucket-partitioned Theorem 8 (`redCKAAuth`, `redPRNGAuth`, `redFSAuth`), and switch-back
Theorem 12 (`redCKAPriv`, `redCKAPrivU`, `redPRNGPriv`, `redFSPriv`, `redFSPrivCoin`) on the
Fig. 8 SM instance (`fig8MixShortAuthV1`, `fig8MixShortPrivV1`). -/
structure Fig8CostedReds (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) where
  /-- Thm 1 authenticity reduction `Thm1.challSim` (`Δ_SM = 3`). -/
  challSim :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.fig8SmIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Lemma 18 blanked privacy reduction `ThmB.privRedB` (`Δ_SM = 3`) at epoch `i`. -/
  privRedB : (i : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.fig8SmIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Thm 8 CKA authenticity reduction `redCKAAuth` for last-leak bucket `tL`. -/
  redCKAAuth : (tL : Option ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.ckaTargetIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Thm 8 coin-averaged (honest-header / forged-header) PRF-PRNG authenticity reduction
  `redPRNGAuth` at `(tL, t)`. -/
  redPRNGAuth : (tL : Option ℕ) → (t : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.prngTargetIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Thm 8 computational FS-AEAD authenticity reduction `redFSAuth` at `(stage, la, j, tL, t)`:
  `j = 0` is the honest-header mode and `1 ≤ j ≤ q` is the forged-header mode at session `j - 1`;
  `stage = false` is the chain-PRG and salt-PRF hop (`lFS → slotSaltImpl false`), `stage = true`
  is the wire OT-CCA hop (`slotSaltImplNF false → slotSaltImpl true`); `la = false` is the `win`
  branch and `la = true` is the lookahead `lf` branch. -/
  redFSAuth : (stage : Bool) → (la : Bool) → (j : ℕ) → (tL : Option ℕ) → (t : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.fsaeadHeaderIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Thm 12 forward-CKA privacy reduction `redCKAPriv` at `(tL, i)`. -/
  redCKAPriv : (tL : Option ℕ) → (i : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.ckaTargetIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Thm 12 reverse-CKA switch-back privacy reduction `redCKAPrivU` at `(tL, i)`. -/
  redCKAPrivU : (tL : Option ℕ) → (i : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.ckaTargetIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Thm 12 PRF-PRNG privacy reduction `redPRNGPriv` at `(tL, i)`. -/
  redPRNGPriv : (tL : Option ℕ) → (i : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.prngTargetIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Thm 12 `tL`-free FS-AEAD privacy reduction `redFSPrivUni` at challenge epoch `i`. -/
  redFSPriv : (i : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.fsaeadHeaderIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Thm 12 `tL`-free FS-AEAD coin-privacy reduction `redFSPrivUniCoin` at challenge epoch `i`. -/
  redFSPrivCoin : (i : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.fsaeadHeaderIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt)
      .unit .unit .bool .bool

/-- Step-cost, program-size, query-count, run-local size-honesty, and semantic target-query bounds
for a `Fig8CostedReds` bundle `R` at SM query bound `q` and epoch cap `qep`. -/
def fig8CostedBounds {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt}
    (q qep : ℕ) (R : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam) : Prop :=
  let B := ratchetCostBudget q qep
  GRedBounded R.challSim (fun _ => 1) (fun _ => 0) q q B ∧
  (∀ i < qep + 1,
    GRedBounded (R.privRedB i) (fun _ => 1) (fun _ => 0) q q B) ∧
  (∀ tL ∈ admissibleLastLeakGuesses (2 + 1) (qep + 1),
    GRedBounded (R.redCKAAuth tL) (fun _ => 1) (fun _ => 0) q (2 * q) B) ∧
  (∀ tL ∈ admissibleLastLeakGuesses (2 + 1) (qep + 1),
    ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
      GRedBounded (R.redPRNGAuth tL t) (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B) ∧
  (∀ tL ∈ admissibleLastLeakGuesses (2 + 1) (qep + 1),
    ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∀ j < q + 1, ∀ stage la : Bool,
      GRedBounded (R.redFSAuth stage la j tL t) (fun _ => 1) (fun _ => 0) q (2 * q) B) ∧
  (∀ i < qep + 1, ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    GRedBounded (R.redCKAPriv tL i) (fun _ => 1) (fun _ => 0) q (2 * q) B) ∧
  (∀ i < qep + 1, ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    GRedBounded (R.redCKAPrivU tL i) (fun _ => 1) (fun _ => 0) q (2 * q) B) ∧
  (∀ i < qep + 1, ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    GRedBounded (R.redPRNGPriv tL i) (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B) ∧
  (∀ i < qep + 1,
    GRedBounded (R.redFSPriv i) (fun _ => 1) (fun _ => 0) q (2 * q) B) ∧
  (∀ i < qep + 1,
    GRedBounded (R.redFSPrivCoin i) (fun _ => 1) (fun _ => 0) q (2 * q) B) ∧
  (∀ tL ∈ admissibleLastLeakGuesses (2 + 1) (qep + 1),
    ∀ A : Fig8Adv Pt ℓ, SM.MakesAtMostQueries A q →
      CKA.MakesAtMostQueries ((R.redCKAAuth tL).eval (fun _ => A) ()) (min (2 * q) (q + 2))) ∧
  (∀ i < qep + 1, ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    ∀ A : Fig8Adv Pt ℓ, SM.MakesAtMostQueries A q →
      CKA.MakesAtMostQueries ((R.redCKAPriv tL i).eval (fun _ => A) ()) (min (2 * q) (q + 2))) ∧
  (∀ i < qep + 1, ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    ∀ A : Fig8Adv Pt ℓ, SM.MakesAtMostQueries A q →
      CKA.MakesAtMostQueries ((R.redCKAPrivU tL i).eval (fun _ => A) ()) (min (2 * q) (q + 2))) ∧
  (∀ tL ∈ admissibleLastLeakGuesses (2 + 1) (qep + 1),
    ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
      ∀ A : Fig8Adv Pt ℓ, SM.MakesAtMostQueries A q →
        PRFPRNG.MakesAtMostQueries ((R.redPRNGAuth tL t).eval (fun _ => A) ())
          (min (2 + 2 * q) (q + 3))) ∧
  (∀ i < qep + 1, ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    ∀ A : Fig8Adv Pt ℓ, SM.MakesAtMostQueries A q →
      PRFPRNG.MakesAtMostQueries ((R.redPRNGPriv tL i).eval (fun _ => A) ())
        (min (2 + 2 * q) (min (q + 3) (2 * qep + 2)))) ∧
  (∀ tL ∈ admissibleLastLeakGuesses (2 + 1) (qep + 1),
    ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∀ j < q + 1, ∀ stage la : Bool,
      ∀ A : Fig8Adv Pt ℓ, SM.MakesAtMostQueries A q →
        FSAEAD.MakesAtMostQueries ((R.redFSAuth stage la j tL t).eval (fun _ => A) ())
          (min (2 * q) (q + 2))) ∧
  (∀ i < qep + 1,
    ∀ A : Fig8Adv Pt ℓ, SM.MakesAtMostQueries A q →
      FSAEAD.MakesAtMostQueries ((R.redFSPriv i).eval (fun _ => A) ())
        (min (2 * q) (q + 2))) ∧
  (∀ i < qep + 1,
    ∀ A : Fig8Adv Pt ℓ, SM.MakesAtMostQueries A q →
      FSAEAD.MakesAtMostQueries ((R.redFSPrivCoin i).eval (fun _ => A) ())
        (min (2 * q) (q + 2)))

end Bounds

end CryptoVerification.LibsignalSession
