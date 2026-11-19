/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepPows -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import VCVio.EvalDist.Monad.Basic

/-!
# Send-branch evaluation for the `Auth` Gap-DH DSL

Proves that `fgSendC` and `fg2SendC` evaluate to the shallow `fgAuthStep` send branches under
`authRespToVal`, `fgSimToVal`, and `AgBnd`.
-/

public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

section SendEval

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  [h₃ : Ext Γ₃ Δ] (env : Env Δ) (st : FgAuthSimState S) (U V : Bytes) (useDh1 : Bool)
  (t sIdx : Nat)

/-! ## Helpers -/

theorem agS_step_opk (uf : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput)
    (m0 m1 : Bytes) :
    fgAuthStep useDh1 t sIdx S K U V (.sendOPK uf i b m0 m1) st =
      if b.opkB?.isNone then pure (.noneResp, st)
      else fgRunSendAuthGdh useDh1 t S K U (.sendOPK uf i) uf b m0 m1 st := by
  simp only [fgAuthStep]

theorem agS_step_noopk (uf : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput)
    (m0 m1 : Bytes) :
    fgAuthStep useDh1 t sIdx S K U V (.sendNoOPK uf i b m0 m1) st =
      if b.opkB?.isSome then pure (.noneResp, st)
      else fgRunSendAuthGdh useDh1 t S K U (.sendNoOPK uf i) uf b m0 m1 st := by
  simp only [fgAuthStep]

theorem agS_usedS (s : AuthState S) :
    (authStateToVal s).2.2.2.2.2.2.1 = s.usedSendSessions.map sessionIdToVal := rfl
theorem agS_prin (s : AuthState S) :
    (authStateToVal s).2.2.1 = s.principals.map (Prod.map id principalEntryToVal) := rfl
theorem agS_spks (s : AuthState S) :
    (authStateToVal s).2.2.2.1 = s.spkBundles.map (Prod.map id spkBundleEntryToVal) := rfl
theorem agS_secb (s : AuthState S) : (authStateToVal s).1 = s.secb := rfl

@[simp] theorem agS_base (st : FgAuthSimState S) :
    (fgSimToVal st).1 = authStateToVal st.base := rfl
@[simp] theorem agS_pows (st : FgAuthSimState S) :
    (fgSimToVal st).2.2.2.2.2.2 = st.advKeyPows := rfl
@[simp] theorem agS_fgL (st : FgAuthSimState S) :
    (fgSimToVal st).2.1 = st.fgL.map fgPatchEntryToVal := rfl
@[simp] theorem agS_rootL (st : FgAuthSimState S) :
    (fgSimToVal st).2.2.1 = st.fgRootL.map rootEntryToVal := rfl

theorem agS_peel {m : Type → Type} [Monad m] [LawfulMonad m] {α α' γ δ : Type}
    (F : γ → δ) {x : m α} {x' : m α'} (h : α' → α) {g : α → m δ} {g' : α' → m γ}
    (hx : x = h <$> x') (hg : ∀ a, g (h a) = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx; simp only [bind_map_left, map_bind, hg]

theorem agS_peelS {m : Type → Type} [Monad m] [LawfulMonad m] {α γ δ : Type}
    (F : γ → δ) {x x' : m α} {g : α → m δ} {g' : α → m γ}
    (hx : x = x') (hg : ∀ a, g a = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx; rw [map_bind]; exact congrArg _ (funext hg)

theorem agS_ite {m : Type → Type} [Functor m] {γ δ : Type} (F : γ → δ) {c c' : Prop}
    [Decidable c] [Decidable c'] {a b : m δ} {a' b' : m γ} (hc : c ↔ c')
    (h1 : c' → a = F <$> a') (h2 : ¬ c' → b = F <$> b') :
    (if c then a else b) = F <$> (if c' then a' else b') := by
  by_cases h : c'
  · simp only [hc.mpr h, h, ↓reduceIte]; exact h1 h
  · have h' : ¬ c := fun h' => h (hc.mp h')
    simp only [h, h', ↓reduceIte]; exact h2 h

theorem agS_pure {m : Type → Type} [Monad m] [LawfulMonad m] {γ δ : Type} (F : γ → δ)
    {a : δ} {a' : γ} (h : a = F a') : (pure a : m δ) = F <$> pure a' := by
  rw [map_pure, h]

theorem agS_embedPrim_eq {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (mx : OracleComp PrimBaseSpec α) :
    FgGapDh.embedPrim (spec := spec) mx = Security.embedPrim (spec := spec) mx := rfl

theorem agS_sigV_congr {pk pk' m m' sg sg' : Bytes} (h1 : pk = pk') (h2 : m = m') (h3 : sg = sg') :
    (query (spec := PrimBaseSpec + gapDhOracleSpec)
      (Sum.inl (Sum.inr (PrimQuery.sigVerify pk m sg))) :
      OracleComp _ Bool) = FgGapDh.primGdhQ (.sigVerify pk' m' sg') := by subst h1 h2 h3; rfl

theorem agS_kem_congr {pk pk' c c' : Bytes} (h1 : pk = pk') (h2 : c = c') :
    query (spec := PrimBaseSpec + gapDhOracleSpec) (Sum.inl (Sum.inr (PrimQuery.kemEncaps pk c))) =
      FgGapDh.primGdhQ (.kemEncaps pk' c') := by subst h1 h2; rfl

theorem agS_x25519_congr {a a' c c' : Bytes} (h1 : a = a') (h2 : c = c') :
    query (spec := PrimBaseSpec + gapDhOracleSpec) (Sum.inl (Sum.inr (PrimQuery.x25519 a c))) =
      FgGapDh.primGdhQ (.x25519 a' c') := by subst h1 h2; rfl

theorem agS_aead_congr {mk mk' : MessageKeys} {ad ad' pt pt' : Bytes}
    (h1 : mk = mk') (h2 : ad = ad') (h3 : pt = pt') :
    query (spec := PrimBaseSpec + gapDhOracleSpec)
      (Sum.inl (Sum.inr (PrimQuery.aeadEnc mk ad pt))) =
      FgGapDh.primGdhQ (.aeadEnc mk' ad' pt') := by subst h1 h2 h3; rfl

theorem agS_optRT (o : Option FgPoS) : Option.map valToFgPos (Option.map fgPosToVal o) = o := by
  cases o with
  | none => rfl
  | some p => cases p <;> rfl

theorem agS_pure_ite {m : Type → Type} [Monad m] [LawfulMonad m] {γ δ : Type} (F : γ → δ)
    {c : Prop} [Decidable c] {a : δ} {a1 a2 : γ} (h : a = F (if c then a1 else a2)) :
    (pure a : m δ) = F <$> (if c then pure a1 else pure a2) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h ⊢; rw [map_pure, h]
  · simp only [hc, ↓reduceIte] at h ⊢; rw [map_pure, h]

/-! ## Send evaluation -/

end SendEval

end SignalPqxdh.Security.ReductionDsl.AuthHs
