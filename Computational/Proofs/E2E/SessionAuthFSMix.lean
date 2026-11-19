/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthFS
public import Computational.Proofs.E2E.SessionAuthHybrid

/-!
# The FS-AEAD session hybrid on mixtures

**Checked by Lean. Not trusted.** No theorem of `Computational/Theorems/` unfolds a definition of
this file, and Lean's kernel checks every proof in it.

`E2E/SessionAuthFS.lean` links one FS-AEAD session of the router to the output-mode Theorem 5 hops
for a fixed AEAD and slot world. The libsignal session hybrid (`SessionHybrid.sessionHybrid_mix_le`)
for the linear multi-session MAC bound needs this on mixtures over a sampled prefix `o ← oa`,
because the AEAD (`lAeadR … (idOf o)`) and the slot-salt world depend on `o`. This file supplies
that:

* `hopOut_mix_eq`, `chainOut_mix_le`, `fsSession_mix_le`: the chain-PRG hops on mixtures. As in
  `Thm5Mix.hop_mix_eq`, each hop is an equality with the advantage of one averaged PRG
  distinguisher `prgAvg oa …`, so no advantage is averaged after the fact.
* `fsHyb`: the router hybrid on mixtures (sessions `< j` on the slot side, the rest on the real
  side). `fsHyb_step_le` and `fsHyb_succ_eq` are the two salt-side endpoint conditions of
  `sessionHybrid_mix_le`, for the session adversary `fsSessAdv … j`.
* `multiSlotOtccaReductionOut_offRange`: the output-mode reduction asks no off-range query (the
  `hoffD` condition), whatever its output.
* `sessionHybrid_fs_mix_le`: `sessionHybrid_mix_le` with its salt side discharged for the libsignal
  instance. The remaining hypotheses are the single MAC hop (its left endpoint stated against the
  all-slot world) and the wire side.-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal CryptoGames.Lazy
open CryptoGames CryptoGames.FSAEAD CryptoGames.FSAEAD.Thm5

namespace CryptoVerification.E2E.Signed.SessionFSMix

open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out

open CryptoVerification.E2E.Signed CryptoVerification.E2E.Signed.SessionRouter
open CryptoVerification.E2E.Signed.SessionFS

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Chain-PRG hops on mixtures, output "the adversary's bit" -/

section Hops

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  {α : Type} (oa : ProbComp α) (ae : α → AEADScheme MK (ℕ × AD) M C)
  (F : Bool → HState CK MK AD M C → Bool) (B : α → RatchetAdversary CK MK AD M C)

/-- One averaged chain-PRG hop is an equality (output `F`): the distance between the mixtures of
hybrids `k` and `k + 1` is the PRG advantage of the one averaged distinguisher
`prgAvg oa (fun o => cumulativeChainPrgReductionOut … (2k+la) F (B o))`. -/
theorem hopOut_mix_eq (la : Bool) (k : ℕ) :
    𝒟[oa >>= fun o => hRunOut ideal (ae o) G maxSkip (hp k 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) F (B o) .unknown].boolDist
      𝒟[oa >>= fun o => hRunOut ideal (ae o) G maxSkip (hp (k + 1) 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) F (B o) .unknown] =
      (G ((2 * k + la.toNat) / 2)).prgAdvantage
        (prgAvg oa fun o =>
          cumulativeChainPrgReductionOut ideal (ae o) G maxSkip (2 * k + la.toNat) F (B o)) := by
  have h1 : (2 * k + la.toNat) / 2 = k := by
    cases la <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have h2 : isLookaheadHop (2 * k + la.toNat) = la := by
    cases la <;> simp [isLookaheadHop, Nat.add_mod]
  have hR : ∀ o, 𝒟[hRunOut ideal (ae o) G maxSkip (hp k 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) F (B o) .unknown] =
      𝒟[(G k).prgRealExperiment
        (cumulativeChainPrgReductionOut ideal (ae o) G maxSkip (2 * k + la.toNat) F (B o))] := by
    intro o
    have := hybZero_eq_prgRealOut ideal (ae o) G maxSkip F (B o) (2 * k + la.toNat)
    rw [h1, h2] at this
    exact this
  have hI : ∀ o, 𝒟[hRunOut ideal (ae o) G maxSkip (hp (k + 1) 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) F (B o) .unknown] =
      𝒟[PRGScheme.prgIdealExperiment
        (cumulativeChainPrgReductionOut ideal (ae o) G maxSkip (2 * k + la.toNat) F (B o))] := by
    intro o
    have := prgIdeal_eq_hybZero_succOut ideal (ae o) G maxSkip F (B o) (2 * k + la.toNat)
    rw [h1, h2] at this
    exact this.symm
  rw [h1, evalDist_bind_congr oa _ _ hR, evalDist_bind_congr oa _ _ hI, PRGScheme.prgAdvantage,
    prgReal_avg, prgIdeal_avg]

/-- Chain-PRG hops `0 → N` on mixtures (output `F`). -/
theorem chainOut_mix_le (la : Bool) (N : ℕ) :
    𝒟[oa >>= fun o => hRunOut ideal (ae o) G maxSkip (hp 0 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) F (B o) .unknown].boolDist
      𝒟[oa >>= fun o => hRunOut ideal (ae o) G maxSkip (hp N 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) F (B o) .unknown] ≤
      ∑ k ∈ Finset.range N,
        (G ((2 * k + la.toNat) / 2)).prgAdvantage
          (prgAvg oa fun o =>
            cumulativeChainPrgReductionOut ideal (ae o) G maxSkip (2 * k + la.toNat) F (B o)) :=
  (Measure.boolDist_le_sum_range
    (fun k => 𝒟[oa >>= fun o => hRunOut ideal (ae o) G maxSkip (hp k 0 la) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) F (B o) .unknown]) N).trans
    (le_of_eq (Finset.sum_congr rfl fun k _ => hopOut_mix_eq ideal G maxSkip oa ae F B la k))

/-- One FS-AEAD session on mixtures. The real-side session (Thm 5 start `hp 0 0 la`, fresh
hidden bit) is within the `N` averaged chain-PRG terms of `multiOtBranch false` against the
multi-slot OT-CCA reduction (output "the adversary's bit"), both as `oa`-mixtures. -/
theorem fsSession_mix_le (la : Bool) (N : ℕ) :
    𝒟[oa >>= fun o => fsInit >>= fun s =>
        Prod.fst <$> (simulateQ (fwd (fsImpl ideal (ae o) G maxSkip (hp 0 0 la))) (B o)).run s].boolDist
      𝒟[oa >>= fun o => multiOtBranch ideal (ae o) false N
        (multiSlotOtccaReductionOut ideal (ae o) G maxSkip N la advBit (B o))] ≤
      ∑ k ∈ Finset.range N,
        (G ((2 * k + la.toNat) / 2)).prgAdvantage
          (prgAvg oa fun o =>
            cumulativeChainPrgReductionOut ideal (ae o) G maxSkip (2 * k + la.toNat) advBit (B o)) := by
  have hL : ∀ o, 𝒟[fsInit >>= fun s =>
        Prod.fst <$> (simulateQ (fwd (fsImpl ideal (ae o) G maxSkip (hp 0 0 la))) (B o)).run s] =
      𝒟[hRunOut ideal (ae o) G maxSkip (hp 0 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) advBit (B o) .unknown] := fun o => by
    rw [fsInit_bind_run]
  have hR : ∀ o, 𝒟[multiOtBranch ideal (ae o) false N
        (multiSlotOtccaReductionOut ideal (ae o) G maxSkip N la advBit (B o))] =
      𝒟[hRunOut ideal (ae o) G maxSkip (hp N 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) advBit (B o) .unknown] := fun o =>
    multiOtBranch_false_eq_hRunOut ideal (ae o) G maxSkip advBit outKeyFree_advBit N la (B o)
  rw [evalDist_bind_congr oa _ _ hL, evalDist_bind_congr oa _ _ hR]
  exact chainOut_mix_le ideal G maxSkip oa ae advBit B la N

/-- The slot-side session on mixtures is the multi-slot OT-CCA reduction run against the slot
world, as an `oa`-mixture. -/
theorem fsSlot_mix_eq (N : ℕ) (la : Bool) {S : Type}
    (O : α → QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))
    (initS : α → ProbComp (ℕ → S)) :
    (oa >>= fun o => fsSlotInit (initS o) >>= fun s =>
        Prod.fst <$> (simulateQ (fwd (fsSlotImpl ideal (ae o) G maxSkip N la (O o))) (B o)).run s) =
      (oa >>= fun o => initS o >>= fun σ => Prod.fst <$> (simulateQ (slotLift (O o))
        (multiSlotOtccaReductionOut ideal (ae o) G maxSkip N la advBit (B o))).run σ) :=
  bind_congr fun o => fsSlotInit_bind_run ideal (ae o) G maxSkip (O o) N la (initS o) (B o)

end Hops

/-! ## The router hybrid on mixtures -/

section Router

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  {α : Type} (oa : ProbComp α) (ae : α → AEADScheme MK (ℕ × AD) M C)
  (N : ℕ) (la : Bool) {S : Type}
  (O : α → QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))
  (initS : α → ProbComp (ℕ → S))
  (Adv : α → OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) Bool)

/-- Router hybrid `j` on mixtures. Sample `o ← oa`, then run the multi-session adversary
`Adv o` with sessions `< j` on the slot side (`fsSlotImpl … (O o)`, states from `initS o`) and
sessions `≥ j` on the real side (Thm 5 start `hp 0 0 la`), every session started lazily. -/
@[expose] def fsHyb (j : ℕ) : ProbComp Bool := do
  let o ← oa
  Prod.fst <$> (simulateQ (hybSess
    (lazyInit fsInit (fsImpl ideal (ae o) G maxSkip (hp 0 0 la)))
    (lazyInit (fsSlotInit (initS o)) (fsSlotImpl ideal (ae o) G maxSkip N la (O o))) j)
    (Adv o)).run ((fun _ => none), (fun _ => none))

/-- Hybrid `j` is session `j`'s session adversary against a fresh real-side session. -/
theorem fsHyb_left (j : ℕ) :
    𝒟[fsHyb ideal G maxSkip oa ae N la O initS Adv j] =
      𝒟[oa >>= fun o => fsInit >>= fun s => Prod.fst <$>
        (simulateQ (fwd (fsImpl ideal (ae o) G maxSkip (hp 0 0 la)))
          (fsSessAdv ideal (ae o) G maxSkip (hp 0 0 la) N la (O o) (initS o) (Adv o) j)).run s] := by
  unfold fsHyb
  refine evalDist_bind_congr oa _ _ fun o => ?_
  rw [← (lazyInit_run_none fsInit (fsImpl ideal (ae o) G maxSkip (hp 0 0 la)) _).evalDist_eq]
  exact congrArg evalDist (sessAdv_left_eq
    (lazyInit fsInit (fsImpl ideal (ae o) G maxSkip (hp 0 0 la)))
    (lazyInit (fsSlotInit (initS o)) (fsSlotImpl ideal (ae o) G maxSkip N la (O o)))
    (Adv o) (fun _ => none) (fun _ => none) j).symm

/-- Hybrid `j + 1` is session `j`'s session adversary against a fresh slot-side session. -/
theorem fsHyb_right (j : ℕ) :
    𝒟[fsHyb ideal G maxSkip oa ae N la O initS Adv (j + 1)] =
      𝒟[oa >>= fun o => fsSlotInit (initS o) >>= fun s => Prod.fst <$>
        (simulateQ (fwd (fsSlotImpl ideal (ae o) G maxSkip N la (O o)))
          (fsSessAdv ideal (ae o) G maxSkip (hp 0 0 la) N la (O o) (initS o) (Adv o) j)).run s] := by
  unfold fsHyb
  refine evalDist_bind_congr oa _ _ fun o => ?_
  rw [← (lazyInit_run_none (fsSlotInit (initS o))
    (fsSlotImpl ideal (ae o) G maxSkip N la (O o)) _).evalDist_eq]
  exact congrArg evalDist (sessAdv_right_eq
    (lazyInit fsInit (fsImpl ideal (ae o) G maxSkip (hp 0 0 la)))
    (lazyInit (fsSlotInit (initS o)) (fsSlotImpl ideal (ae o) G maxSkip N la (O o)))
    (Adv o) (fun _ => none) (fun _ => none) j).symm

/-- Salt-side left endpoint (`hDL`). Hybrid `j` is within the `N` averaged chain-PRG terms of
`multiOtBranch false` against `D j = multiSlotOtccaReductionOut … (fsSessAdv … j)`. -/
theorem fsHyb_step_le (j : ℕ) :
    𝒟[fsHyb ideal G maxSkip oa ae N la O initS Adv j].boolDist
      𝒟[oa >>= fun o => multiOtBranch ideal (ae o) false N
        (multiSlotOtccaReductionOut ideal (ae o) G maxSkip N la advBit
          (fsSessAdv ideal (ae o) G maxSkip (hp 0 0 la) N la (O o) (initS o) (Adv o) j))] ≤
      ∑ k ∈ Finset.range N,
        (G ((2 * k + la.toNat) / 2)).prgAdvantage
          (prgAvg oa fun o =>
            cumulativeChainPrgReductionOut ideal (ae o) G maxSkip (2 * k + la.toNat) advBit
              (fsSessAdv ideal (ae o) G maxSkip (hp 0 0 la) N la (O o) (initS o) (Adv o) j)) := by
  rw [fsHyb_left]
  exact fsSession_mix_le ideal G maxSkip oa ae
    (fun o => fsSessAdv ideal (ae o) G maxSkip (hp 0 0 la) N la (O o) (initS o) (Adv o) j) la N

/-- Salt-side right endpoint (`hDR`). Hybrid `j + 1` is `D j` run against the slot world, as an
`oa`-mixture. -/
theorem fsHyb_succ_eq (j : ℕ) :
    𝒟[fsHyb ideal G maxSkip oa ae N la O initS Adv (j + 1)] =
      𝒟[oa >>= fun o => initS o >>= fun σ => Prod.fst <$> (simulateQ (slotLift (O o))
        (multiSlotOtccaReductionOut ideal (ae o) G maxSkip N la advBit
          (fsSessAdv ideal (ae o) G maxSkip (hp 0 0 la) N la (O o) (initS o) (Adv o) j))).run σ] := by
  rw [fsHyb_right, fsSlot_mix_eq]

/-- Hybrid `0` is "every session runs the real side". -/
theorem fsHyb_zero :
    𝒟[fsHyb ideal G maxSkip oa ae N la O initS Adv 0] =
      𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl ideal (ae o) G maxSkip (hp 0 0 la)))) (Adv o)).run
          (fun _ => none)] := by
  unfold fsHyb
  refine evalDist_bind_congr oa _ _ fun o => ?_
  rw [hybSess_zero, Functor.map_map]

/-- Hybrid `q` is "every session runs the slot side", when every `Adv o` uses only sessions `< q`. -/
theorem fsHyb_of_offRange (q : ℕ)
    (hoff : ∀ o, (Adv o).IsQueryBoundP (fun t => sessOffRange q t = true) 0) :
    𝒟[fsHyb ideal G maxSkip oa ae N la O initS Adv q] =
      𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit (fsSlotInit (initS o)) (fsSlotImpl ideal (ae o) G maxSkip N la (O o))))
          (Adv o)).run (fun _ => none)] := by
  unfold fsHyb
  refine evalDist_bind_congr oa _ _ fun o => ?_
  rw [hybSess_eq_sessLift_of_offRange _ _ q (Adv o) (hoff o), Functor.map_map]

end Router

/-! ## The output-mode multi-slot reduction stays in range -/

section OffRange

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

/-- `multiSlotOtccaReductionOut` asks no off-range query, whatever its output `F`: it maps a
function over the same run as `multiSlotOtccaReduction`, which `multiRedWith_offRange` bounds. -/
theorem multiSlotOtccaReductionOut_offRange (N : ℕ) (la : Bool)
    (F : Bool → HState CK MK AD M C → Bool) (A : RatchetAdversary CK MK AD M C) :
    (multiSlotOtccaReductionOut ideal ae G maxSkip N la F A).IsQueryBoundP
      (fun t => multiOffRange N t = true) 0 := by
  have h := multiRedWith_offRange ideal ae G maxSkip N la A
  unfold multiSlotOtccaReduction multiRunWith at h
  unfold multiSlotOtccaReductionOut multiRunOut
  simp only [bind_pure_comp, ← map_bind, isQueryBoundP_map_iff] at h ⊢
  exact h

end OffRange

/-! ## The libsignal instance: the salt side discharged -/

section Libsignal

open CryptoGames.LibsignalSM.Proofs CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
open CryptoGames.LibsignalSession CryptoGames.LibsignalSM.Proofs.SaltHop
open CryptoGames.LibsignalSM.Proofs.WireHop CryptoVerification.E2E.Signed.FSMix
open CryptoVerification.E2E.Signed.SessionHybrid
open CryptoGames.LibsignalSM.Proofs.SaltHopKeyed CryptoGames.LibsignalSM.Proofs.WireHop
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD

variable {Pt : Type} [DecidableEq Pt] {α κ : Type} [DecidableEq κ] (C : Crypto)
  (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (oa : ProbComp α)
  (idOf : α → Party → IdentityKey) (maxSkip N : ℕ) (la : Bool)
  (Adv : α → OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) Bool)

/-- Session `j`'s session adversary in the libsignal chain (sessions `< j` on the slot-salt side,
the rest on the real side, all inside the adversary). -/
abbrev lSessAdv (o : α) (j : ℕ) :
    RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
      LibsignalCiphertextWithSalt32 :=
  fsSessAdv (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o)) (lChainPRG C.F) maxSkip
    (hp 0 0 la) N la (slotSaltImpl C codec ℓ encT (idOf o) false)
    (pure fun _ => ({} : SaltSlotSt Pt)) (Adv o) j

/-- Session `j`'s salt-side reduction `D j`: the multi-slot OT-CCA reduction (output "the
adversary's bit") of its session adversary. -/
abbrev lSaltD (j : ℕ) (o : α) :
    OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32 :=
  multiSlotOtccaReductionOut (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
    (lChainPRG C.F) maxSkip N la advBit (lSessAdv C codec ℓ encT idOf maxSkip N la Adv o j)

/-- Session `j`'s chain-PRG terms: one averaged distinguisher per chain position. -/
noncomputable abbrev lSaltPre (j : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range N, (lChainPRG C.F ((2 * k + la.toNat) / 2)).prgAdvantage
    (prgAvg oa fun o => cumulativeChainPrgReductionOut (lIdeal C codec ℓ encT)
      (lAeadR C codec ℓ encT (idOf o)) (lChainPRG C.F) maxSkip (2 * k + la.toNat) advBit
      (lSessAdv C codec ℓ encT idOf maxSkip N la Adv o j))

/-- The libsignal FS-AEAD session hybrid with one global MAC hop, salt side discharged.

Start: every session of `Adv o` runs the real side (Thm 5 start `hp 0 0 la`). The salt side of
`sessionHybrid_mix_le` is paid by the router hybrid `fsHyb`: session `j` costs its `N` averaged
chain-PRG terms (`lSaltPre j`) and the salt-PRF terms of `lSaltD j`. The join is one MAC hop for an
adversary `A` whose keyed slot-salt world is the all-slot world (`hAL`, needs `Adv` to stay in
sessions `< q`). The wire side is unchanged from `sessionHybrid_mix_le`. -/
theorem sessionHybrid_fs_mix_le (hrt : SignalRoundTripShort codec)
    (hfit : SignalEncodeFits32 codec) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (q : ℕ) (Hw : ℕ → ProbComp Bool)
    (hoffAdv : ∀ o, (Adv o).IsQueryBoundP (fun t => sessOffRange q t = true) 0)
    -- the single MAC hop
    (sk : α → ℕ × (Header Pt × LibsignalMsgPublicPart) → κ)
    (A : α → OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32)
    {qd : ℕ} (hqdA : ∀ o, MakesAtMostDecQueries (A o) qd)
    (hshortA : ∀ o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) (A o))
    (hdecA : ∀ o, GuardedOTDecShort (A o))
    (hAL : 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit (fsSlotInit (pure fun _ => ({} : SaltSlotSt Pt)))
          (fsSlotImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o)) (lChainPRG C.F)
            maxSkip N la (slotSaltImpl C codec ℓ encT (idOf o) false)))) (Adv o)).run
          (fun _ => none)] =
      𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLiftK (sk o)
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
    𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip (hp 0 0 la)))) (Adv o)).run (fun _ => none)].boolDist
        𝒟[Hw q] ≤
      (∑ j ∈ Finset.range q,
        (lSaltPre C codec ℓ encT oa idOf maxSkip N la Adv j +
          ∑ k ∈ Finset.range N, 2 * (lSaltPRF32 C.F).prfAdvantage
            (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
              (slotSaltRed C codec ℓ encT (idOf o) N k
                (lSaltD C codec ℓ encT idOf maxSkip N la Adv j o))))) +
      (qd : ℝ≥0∞) * macForgeryProb C.F +
      ∑ j ∈ Finset.range q,
        ((∑ k ∈ Finset.range (Nw j), (lWire C codec ℓ).wireOtccaAdvantage
          (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
            (slotWireRed C codec ℓ encT (idOf o) k (E j o)))) + post j) := by
  have h := sessionHybrid_mix_le C codec ℓ encT oa idOf hrt hfit hℓ hinj hdum q
    (fsHyb (lIdeal C codec ℓ encT) (lChainPRG C.F) maxSkip oa
      (fun o => lAeadR C codec ℓ encT (idOf o)) N la
      (fun o => slotSaltImpl C codec ℓ encT (idOf o) false)
      (fun _ => pure fun _ => ({} : SaltSlotSt Pt)) Adv) Hw
    (fun _ => N) (lSaltD C codec ℓ encT idOf maxSkip N la Adv)
    (fun j o => multiSlotOtccaReductionOut_offRange _ _ _ _ N la advBit _)
    (lSaltPre C codec ℓ encT oa idOf maxSkip N la Adv)
    (fun j _ => fsHyb_step_le _ _ _ oa _ N la _ _ Adv j)
    (fun j _ => (fsHyb_succ_eq _ _ _ oa _ N la _ _ Adv j).trans (by simp only [pure_bind]))
    sk A hqdA hshortA hdecA
    ((fsHyb_of_offRange _ _ _ oa _ N la _ _ Adv q hoffAdv).trans hAL) hAR
    Nw hNw E hoffE hclsE hshortE post hEL hER
  rwa [fsHyb_zero] at h

end Libsignal

end CryptoVerification.E2E.Signed.SessionFSMix
