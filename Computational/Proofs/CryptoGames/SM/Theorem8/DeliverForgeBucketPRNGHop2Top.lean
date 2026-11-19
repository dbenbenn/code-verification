/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGHop2TopHooks
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import VCVio.OracleComp.EvalDist.Measure

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec ENNReal MeasureTheory
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Construction

namespace CryptoGames.SM.Construction.DeliverForge

section TopCoupling

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

private theorem resolveCorrRoot_eq_of_syncTopRaw
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    {esL : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketState T Sig K I)}
    (hsync : SyncTopRaw prng Δcka qep tL esP sp esL) (P : Party) (s : Sig)
    (hres : resolveCorrRoot esP.h (esL.g.epoch P) (esP.g.st P).root = some s) :
    s = (esL.g.st P).root := by
  cases hrP : (esP.g.st P).root with
  | some σ0 =>
    rw [hrP, resolveCorrRoot] at hres
    exact (hsync.vp_rel P).root_eq s (Option.some.inj hres ▸ hrP)
  | none =>
    rw [hrP, resolveCorrRoot] at hres
    cases hcr : esP.h.corrRoot with
    | none => simp [hcr] at hres
    | some p =>
      rcases p with ⟨eC, σC⟩; rw [hcr] at hres; dsimp only at hres
      split at hres
      · rename_i h_eq; rw [beq_iff_eq] at h_eq; injection hres with hs
        exact hs.symm.trans ((hsync.corrRoot_rel eC σC hcr).2.1 P h_eq)
      · cases hres

private theorem postLeak_epMgmt_of_sendsIn_false {St Msg C : Type}
    {Δ qep : ℕ} {P : Party} {bad : Bool} {g s₁ : SM.GameState St Msg C}
    (hns : P.sendsIn (g.epoch P + 1) = false) (hep : g.epMgmt Δ qep P bad = some s₁) :
    s₁ = g := by
  unfold SM.GameState.epMgmt at hep; simp only [hns, Bool.false_eq_true, ↓reduceIte] at hep
  split at hep <;> simp at hep; exact hep.symm

end TopCoupling

end CryptoGames.SM.Construction.DeliverForge
