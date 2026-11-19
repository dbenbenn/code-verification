/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SignedFSStages
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltHopKeyed
import Computational.Proofs.E2E.ComposedPrefixHelpers

/-!
# Session hybrid with one global MAC hop (libsignal instance, game level)

The per-session Theorem 5 chain pays the MAC-forgery term `qd · μ` once per session, with the
static bound `qd = q`, so summing over `q` sessions costs `q² · μ`. This file states the
linear-MAC alternative at the game level: a hybrid over sessions in which the MAC hop is taken
once across all sessions simultaneously.

The two hybrid chains are abstract families of games `Hs j` (salt side) and `Hw j` (wire side):

* `Hs 0` is the real multi-session game and `Hw q` the ideal one.
* Step `Hs j → Hs (j+1)` moves session `j` from the real world to the slot-salt world (uniform keys
  and salts, HMAC still checked). It is paid by one per-session adversary `D j` through its
  salt-PRF terms (`FSMix.salt_mix`), plus a slack `pre j` for whatever links `Hs j` to `D j`'s
  `multiOtBranch false` world (for example its chain-PRG hops).
* The single MAC hop `Hs q → Hw 0` uses one multi-session adversary `A` whose OT-CCA slots are keyed
  by an arbitrary slot selector `sk` (for example, (session, chain index)). The cost is
  `qd · macForgeryProb`, where `qd` bounds the decryptions of `A` summed over all sessions
  (`mac_mix_keyed`, built on `SaltHop.multiSaltFlagNF_flag_le_aux`).
* Step `Hw j → Hw (j+1)` moves session `j` from the post-MAC world to the ideal world. It is paid by
  a second per-session adversary `E j` through its wire OT-CCA terms (`FSMix.wire_mix`), plus a
  slack `post j`.

Nothing here touches the trusted specification. The endpoint hypotheses (`hDL`, `hDR`, `hAL`, `hAR`,
`hEL`, `hER`) are discharged by concrete simulation reductions in `SessionAuthFSMix`,
`SessionAuthMac`, and `SessionAuthWire`.-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed.SessionHybrid

open CryptoGames CryptoGames.LibsignalSM.Proofs
open CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSession
open CryptoGames.LibsignalSM.Proofs.SaltHopKeyed CryptoGames.LibsignalSM.Proofs.WireHop
open CryptoGames.FSAEAD.Thm5
open CryptoVerification.E2E.Signed.FSMix

/-! ## Generic telescoping over two chains joined by one hop -/

/-- Two hybrid chains joined by one hop. If `Hs 0, …, Hs q` and `Hw 0, …, Hw q` have adjacent
distances `saltT j` and `wireT j`, and `Hs q` is within `macT` of `Hw 0`, then the ends are within
`∑ saltT + macT + ∑ wireT`. -/
theorem boolDist_two_chains_le (Hs Hw : ℕ → ProbComp Bool) (q : ℕ)
    (saltT wireT : ℕ → ℝ≥0∞) (macT : ℝ≥0∞)
    (hs : ∀ j < q, 𝒟[Hs j].boolDist 𝒟[Hs (j + 1)] ≤ saltT j)
    (hmac : 𝒟[Hs q].boolDist 𝒟[Hw 0] ≤ macT)
    (hw : ∀ j < q, 𝒟[Hw j].boolDist 𝒟[Hw (j + 1)] ≤ wireT j) :
    𝒟[Hs 0].boolDist 𝒟[Hw q] ≤
      (∑ j ∈ Finset.range q, saltT j) + macT + ∑ j ∈ Finset.range q, wireT j := by
  have h1 : 𝒟[Hs 0].boolDist 𝒟[Hs q] ≤ ∑ j ∈ Finset.range q, saltT j :=
    (Measure.boolDist_le_sum_range (fun j => 𝒟[Hs j]) q).trans
      (Finset.sum_le_sum fun j hj => hs j (Finset.mem_range.mp hj))
  have h3 : 𝒟[Hw 0].boolDist 𝒟[Hw q] ≤ ∑ j ∈ Finset.range q, wireT j :=
    (Measure.boolDist_le_sum_range (fun j => 𝒟[Hw j]) q).trans
      (Finset.sum_le_sum fun j hj => hw j (Finset.mem_range.mp hj))
  refine (Measure.boolDist_triangle 𝒟[Hs 0] 𝒟[Hs q] 𝒟[Hw q]).trans ?_
  refine (add_le_add h1 ((Measure.boolDist_triangle 𝒟[Hs q] 𝒟[Hw 0] 𝒟[Hw q]).trans
    (add_le_add hmac h3))).trans ?_
  rw [add_assoc]

/-! ## The global MAC hop on mixtures, keyed by an arbitrary slot selector -/

section Mac

open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD

variable {Pt : Type} [DecidableEq Pt] {α κ : Type} [DecidableEq κ] (C : Crypto)
  (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)

/-- Per-adversary one-sided keyed MAC bound: `mac_apply_le` with slots keyed by `sk`. -/
theorem mac_apply_le_keyed (hfit : SignalEncodeFits32 codec) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (idO : Party → IdentityKey) (sk : ℕ × (Header Pt × LibsignalMsgPublicPart) → κ)
    (B₀ : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32)
    {qd : ℕ} (hB : MakesAtMostDecQueries B₀ qd)
    (hshort : AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) B₀)
    (hdec : GuardedOTDecShort B₀) (x : Bool) :
    𝒟[Prod.fst <$> (simulateQ (slotLiftK sk (slotSaltImpl C codec ℓ encT idO false)) B₀).run
        (fun _ => {})] {x} ≤
      𝒟[Prod.fst <$> (simulateQ (slotLiftK sk (slotSaltImplNF C codec ℓ encT idO false)) B₀).run
        (fun _ => {})] {x} + (qd : ℝ≥0∞) * macForgeryProb C.F := by
  rw [← evalDist_multiSaltFlagNF_out_eq_slotLift_slotSaltImplNF_aux C codec ℓ encT idO sk B₀
    (fun _ => {}) false MSaltTableInv.init]
  simp only [map_eq_bind_pure_comp]
  exact (slotLift_slotSaltImpl_false_le_multiSaltFlagNF C codec ℓ encT idO sk B₀ pure x
    (fun _ => {})).trans
    (add_le_add le_rfl
      (multiSaltFlagNF_flag_le_aux C codec hfit ℓ hℓ encT idO sk hdec qd (fun _ => {})
        MSaltTableInv.init hshort hB))

/-- Global MAC hop on mixtures. One multi-session adversary `A o` whose slots are keyed by
`sk o` (for example (session, chain index)). The cost is `qd · macForgeryProb`, where `qd` bounds
the decryptions of `A o` summed over all slots, so over all sessions. -/
theorem mac_mix_keyed (hfit : SignalEncodeFits32 codec) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (sk : α → ℕ × (Header Pt × LibsignalMsgPublicPart) → κ)
    (A : α → OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32)
    {qd : ℕ} (hB : ∀ o, MakesAtMostDecQueries (A o) qd)
    (hshort : ∀ o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) (A o))
    (hdec : ∀ o, GuardedOTDecShort (A o)) :
    𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLiftK (sk o)
        (slotSaltImpl C codec ℓ encT (idOf o) false)) (A o)).run (fun _ => {})].boolDist
      𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLiftK (sk o)
        (slotSaltImplNF C codec ℓ encT (idOf o) false)) (A o)).run (fun _ => {})] ≤
      (qd : ℝ≥0∞) * macForgeryProb C.F := by
  refine Measure.boolDist_le_of_apply_le _ _ fun x => ?_
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral]
  calc _ ≤ ∫⁻ o, (𝒟[Prod.fst <$> (simulateQ (slotLiftK (sk o)
          (slotSaltImplNF C codec ℓ encT (idOf o) false)) (A o)).run (fun _ => {})] {x} +
          (qd : ℝ≥0∞) * macForgeryProb C.F) ∂𝒟[oa] :=
        lintegral_mono fun o =>
          mac_apply_le_keyed C codec ℓ encT hfit hℓ (idOf o) (sk o) (A o) (hB o) (hshort o)
            (hdec o) x
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

end Mac

/-! ## Per-session steps over abstract adversaries `D j` (salt side) and `E j` (wire side) -/

section Steps

open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD

variable {Pt : Type} [DecidableEq Pt] {α : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
  (ℓ : ℕ) (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)

/-- Salt-side session step. If the left hybrid is within `pre` of `D`'s `multiOtBranch false`
world and the right hybrid *is* `D`'s slot-salt world (both as `oa`-mixtures), the step costs
`pre` plus `D`'s salt-PRF terms, exactly as in `fsAeadMixtureBound`. -/
theorem salt_session_step (N : ℕ)
    (D : α → OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32)
    (hoff : ∀ o, (D o).IsQueryBoundP (fun t => multiOffRange N t = true) 0)
    (HL HR : ProbComp Bool) (pre : ℝ≥0∞)
    (hL : 𝒟[HL].boolDist 𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT)
      (lAeadR C codec ℓ encT (idOf o)) false N (D o)] ≤ pre)
    (hR : 𝒟[HR] = 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ
      encT (idOf o) false)) (D o)).run (fun _ => {})]) :
    𝒟[HL].boolDist 𝒟[HR] ≤
      pre + ∑ k ∈ Finset.range N, 2 * (lSaltPRF32 C.F).prfAdvantage
        (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
          (slotSaltRed C codec ℓ encT (idOf o) N k (D o))) := by
  rw [hR]
  exact (Measure.boolDist_triangle _ _ _).trans
    (add_le_add hL (salt_mix C codec ℓ encT oa idOf D N hoff))

/-- Wire-side session step. If the left hybrid *is* `E`'s post-MAC world and the right hybrid
is within `post` of `E`'s `multiOtBranch true` world (both as `oa`-mixtures), the step costs `E`'s
wire OT-CCA terms plus `post`, exactly as in `fsAeadMixtureBound`. -/
theorem wire_session_step (hrt : SignalRoundTripShort codec) (hℓ : ℓ + 16 < rustLenBound)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) {N : ℕ} (hN : N ≤ 2 ^ 32)
    (E : α → OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32)
    (hoff : ∀ o, (E o).IsQueryBoundP (fun t => multiOffRange N t = true) 0)
    (hcls : ∀ o, AEADScheme.OTAllQueriesInOneADClass lCls (E o))
    (hshort : ∀ o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) (E o))
    (HL HR : ProbComp Bool) (post : ℝ≥0∞)
    (hL : 𝒟[HL] = 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLift (slotSaltImplNF C codec ℓ
      encT (idOf o) false)) (E o)).run (fun _ => {})])
    (hR : 𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT)
      (lAeadR C codec ℓ encT (idOf o)) true N (E o)].boolDist 𝒟[HR] ≤ post) :
    𝒟[HL].boolDist 𝒟[HR] ≤
      (∑ k ∈ Finset.range N, (lWire C codec ℓ).wireOtccaAdvantage
        (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
          (slotWireRed C codec ℓ encT (idOf o) k (E o)))) + post := by
  rw [hL]
  exact (Measure.boolDist_triangle _ _ _).trans
    (add_le_add (wire_mix C codec ℓ encT oa idOf E hrt hℓ hinj hdum hN hoff hcls hshort) hR)

end Steps

/-! ## The session hybrid with one global MAC hop -/

section Hybrid

open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD

variable {Pt : Type} [DecidableEq Pt] {α κ : Type} [DecidableEq κ] (C : Crypto)
  (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (oa : ProbComp α)
  (idOf : α → Party → IdentityKey)

/-- Session hybrid with one global MAC hop.

`Hs` and `Hw` are the salt-side and wire-side hybrid chains over `q` sessions (`Hs 0` real,
`Hw q` ideal). Session `j`'s salt step is paid by `D j` (salt-PRF terms plus slack `pre j`), its
wire step by `E j` (wire OT-CCA terms plus slack `post j`), and the join `Hs q → Hw 0` by one MAC
hop on the multi-session adversary `A`, keyed by `sk`.

The MAC term `qd · macForgeryProb` appears once, with `qd` the decryption bound of `A` across all
sessions. The per-session chains pay none. -/
theorem sessionHybrid_mix_le (hrt : SignalRoundTripShort codec) (hfit : SignalEncodeFits32 codec)
    (hℓ : ℓ + 16 < 2 ^ 31 + 16) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey)
    (q : ℕ) (Hs Hw : ℕ → ProbComp Bool)
    -- salt side
    (Ns : ℕ → ℕ)
    (D : ℕ → α → OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32)
    (hoffD : ∀ j o, (D j o).IsQueryBoundP (fun t => multiOffRange (Ns j) t = true) 0)
    (pre : ℕ → ℝ≥0∞)
    (hDL : ∀ j < q, 𝒟[Hs j].boolDist 𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT)
      (lAeadR C codec ℓ encT (idOf o)) false (Ns j) (D j o)] ≤ pre j)
    (hDR : ∀ j < q, 𝒟[Hs (j + 1)] = 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ
      (slotLift (slotSaltImpl C codec ℓ encT (idOf o) false)) (D j o)).run (fun _ => {})])
    -- the single MAC hop
    (sk : α → ℕ × (Header Pt × LibsignalMsgPublicPart) → κ)
    (A : α → OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32)
    {qd : ℕ} (hqdA : ∀ o, MakesAtMostDecQueries (A o) qd)
    (hshortA : ∀ o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) (A o))
    (hdecA : ∀ o, GuardedOTDecShort (A o))
    (hAL : 𝒟[Hs q] = 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLiftK (sk o)
      (slotSaltImpl C codec ℓ encT (idOf o) false)) (A o)).run (fun _ => {})])
    (hAR : 𝒟[Hw 0] = 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLiftK (sk o)
      (slotSaltImplNF C codec ℓ encT (idOf o) false)) (A o)).run (fun _ => {})])
    -- wire side
    (Nw : ℕ → ℕ) (hNw : ∀ j, Nw j ≤ 2 ^ 32)
    (E : ℕ → α → OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32)
    (hoffE : ∀ j o, (E j o).IsQueryBoundP (fun t => multiOffRange (Nw j) t = true) 0)
    (hclsE : ∀ j o, AEADScheme.OTAllQueriesInOneADClass lCls (E j o))
    (hshortE : ∀ j o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) (E j o))
    (post : ℕ → ℝ≥0∞)
    (hEL : ∀ j < q, 𝒟[Hw j] = 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ
      (slotLift (slotSaltImplNF C codec ℓ encT (idOf o) false)) (E j o)).run (fun _ => {})])
    (hER : ∀ j < q, 𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT)
      (lAeadR C codec ℓ encT (idOf o)) true (Nw j) (E j o)].boolDist 𝒟[Hw (j + 1)] ≤ post j) :
    𝒟[Hs 0].boolDist 𝒟[Hw q] ≤
      (∑ j ∈ Finset.range q,
        (pre j + ∑ k ∈ Finset.range (Ns j), 2 * (lSaltPRF32 C.F).prfAdvantage
          (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
            (slotSaltRed C codec ℓ encT (idOf o) (Ns j) k (D j o))))) +
      (qd : ℝ≥0∞) * macForgeryProb C.F +
      ∑ j ∈ Finset.range q,
        ((∑ k ∈ Finset.range (Nw j), (lWire C codec ℓ).wireOtccaAdvantage
          (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
            (slotWireRed C codec ℓ encT (idOf o) k (E j o)))) + post j) := by
  have hℓ_rust : ℓ + 16 < rustLenBound := by unfold rustLenBound; omega
  refine boolDist_two_chains_le Hs Hw q _ _ _ (fun j hj => ?_) ?_ (fun j hj => ?_)
  · exact salt_session_step C codec ℓ encT oa idOf (Ns j) (D j) (hoffD j) (Hs j) (Hs (j + 1))
      (pre j) (hDL j hj) (hDR j hj)
  · rw [hAL, hAR]
    exact mac_mix_keyed C codec ℓ encT hfit hℓ oa idOf sk A hqdA hshortA hdecA
  · exact wire_session_step C codec ℓ encT oa idOf hrt hℓ_rust hinj hdum (hNw j) (E j) (hoffE j)
      (hclsE j) (hshortE j) (Hw j) (Hw (j + 1)) (post j) (hEL j hj) (hER j hj)

end Hybrid

end CryptoVerification.E2E.Signed.SessionHybrid
