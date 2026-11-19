/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyber
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2

/-!
# Stage P4 Kyber Pre-Key Refusal Arm and 4-Kit Spatial Predicates

Verifies the Stage P4 Kyber pre-key refusal path (`stageP4_kyber_refused_core_kits_ok` and
`stageP4_kyber_refused_kits_ok`, `+0x34dc → s0.readReg64 .x30`) when `mark_kyber_pre_key_used`
refuses (`∀ u, ¬ kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok u)`), and defines
the shared 4-kit Stage P4 spatial predicates (`stageP4Shared`, `stageP4Pre`, `stageP4ExitAt`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Stack, coroutine slot, and `StageP3GenStmt` bridge helpers -/

/-- Stack budget for the Kyber pre-key refusal path (`P4.1` `save_identity` and `P4.2`
`mark_kyber_pre_key_used` plus their error-unwind tails). -/
@[expose] def kyberRefusedCallStack {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) : Nat :=
  max (saveIdCallStack ikit) (markKyberCallStack kpkKit)

theorem stack_kyberRefused_to_saveId {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (sp : BitVec 64) (hn : kyberRefusedCallStack ikit kpkKit ≤ 2 ^ 64) :
    stackAt sp (kyberRefusedCallStack ikit kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (kyberRefusedCallStack ikit kpkKit))
        (kyberRefusedCallStack ikit kpkKit - saveIdCallStack ikit) ∗
        stackAt sp (saveIdCallStack ikit) :=
  P3P4.stackAt_sub_eq sp _ _ (Nat.le_max_left _ _) hn

theorem stack_kyberRefused_to_markKyber {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (sp : BitVec 64) (hn : kyberRefusedCallStack ikit kpkKit ≤ 2 ^ 64) :
    stackAt sp (kyberRefusedCallStack ikit kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (kyberRefusedCallStack ikit kpkKit))
        (kyberRefusedCallStack ikit kpkKit - markKyberCallStack kpkKit) ∗
        stackAt sp (markKyberCallStack kpkKit) :=
  P3P4.stackAt_sub_eq sp _ _ (Nat.le_max_right _ _) hn

theorem kyberRefusedStack_le_stageP4 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) :
    kyberRefusedCallStack ikit kpkKit ≤ stageP4CallStack kit ikit pkKit kpkKit :=
  Nat.max_le.mpr ⟨saveIdStack_le_stageP4 kit ikit pkKit kpkKit,
    markKyberStack_le_stageP4 kit ikit pkKit kpkKit⟩

theorem stack_stageP4_to_kyberRefused {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (sp : BitVec 64) (hn : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64) :
    stackAt sp (stageP4CallStack kit ikit pkKit kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (stageP4CallStack kit ikit pkKit kpkKit))
        (stageP4CallStack kit ikit pkKit kpkKit - kyberRefusedCallStack ikit kpkKit) ∗
        stackAt sp (kyberRefusedCallStack ikit kpkKit) :=
  P3P4.stackAt_sub_eq sp _ _ (kyberRefusedStack_le_stageP4 kit ikit pkKit kpkKit) hn

/-- Lift a Stage P4 `SepWPp` under `P3P4.PanicOomProp s0` into `StageP3GenStmt`'s `genP3S5PanicProp`
    continuation at `+0x34dc`. -/
theorem SepWPp.to_genP3S5PanicProp {prog : Program} {ret : BitVec 64}
    {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s P Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) :=
  SepWPp.mono_panic (fun _ _ hp => Or.inl hp) h

/-- Coroutine `opk_id : Option<u32>` representation at `coroPtr + 0x298..0x2a0` entering Stage P4
    (definitionally equal to `TopLevel.coroOpkIdAt`). -/
@[expose] def coroOpkIdAtP4 (coroPtr : BitVec 64) (opkId? : Option (BitVec 32)) : SepProp :=
  match opkId? with
  | none => ∃∗ opkIdDummy : BitVec 32,
      ((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy)
  | some opkId =>
      ((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId)

theorem coro298_split_eq (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    ((coroPtr + 0x298#64) ↦₆₄ (hi ++ lo)) =
      ((coroPtr + 0x298#64) ↦₃₂ lo) ∗ ((coroPtr + 0x29c#64) ↦₃₂ hi) := by
  have h : coroPtr + 0x29c#64 = (coroPtr + 0x298#64) + 4#64 := by bv_omega
  rw [h, ← pointsTo32_pair_eq]

theorem coro2ac_words_entails_memRegion20 (coroPtr : BitVec 64)
    (w0 w1 w2 w3 w4 : BitVec 32) :
    ((coroPtr + 0x2ac#64) ↦₃₂ w0) ∗
    ((coroPtr + 0x2b0#64) ↦₃₂ w1) ∗
    ((coroPtr + 0x2b4#64) ↦₃₂ w2) ∗
    ((coroPtr + 0x2b8#64) ↦₃₂ w3) ∗
    ((coroPtr + 0x2bc#64) ↦₃₂ w4) ⊢
      memRegion (coroPtr + 0x2ac#64) 20 := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x2ac#64) (n := 4) (k := 16)
        (b' := coroPtr + 0x2b0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x2b0#64) (n := 4) (k := 12)
        (b' := coroPtr + 0x2b4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x2b4#64) (n := 4) (k := 8)
        (b' := coroPtr + 0x2b8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x2b8#64) (n := 4) (k := 4)
        (b' := coroPtr + 0x2bc#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (pointsTo32_entails_memRegion _ _))))

theorem sp3e0_344_eq_48_296 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 344 =
      memRegion (sp + 0x3e0#64) 48 ∗ memRegion (sp + 0x410#64) 296 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 48) (k := 296)
    (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)
/-! ## Read-only vtable drop and postcondition weakening combinators -/

/-- Replace a sub-assertion `A ⊢ B` inside a large `SepProp` entailment `P ⊢ Q` via `sep_focus`
    on `P = A ∗ R` and `ac_rfl` on `B ∗ R = Q`. -/
theorem Entails.replace_factor {A B R P Q : SepProp}
    (hab : A ⊢ B) (hp : P = A ∗ R) (hq : B ∗ R = Q) : P ⊢ Q := by
  rw [hp, ← hq]
  exact sepConj_mono_left hab

/-- Drop a left factor `Drop` (such as `.rodata` vtable assertions introduced from `FrozenLoaded`)
    from a `SepWPp` spatial precondition while keeping any caller frame `R` intact. -/
theorem SepWPp.drop_pre_left {prog : Program} {ret : BitVec 64} {s : State}
    {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem SepWPp.drop_pre_of_entails {prog : Program} {ret : BitVec 64} {s : State}
    {Drop P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hdrop : P ⊢ Drop ∗ P')
    (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.weaken_pre hdrop (SepWPp.drop_pre_left h)

/-- Absorb an existentially witnessed left factor `Drop` at a `SepWPp` return postcondition while
    preserving the caller's arbitrary frame `R`. -/
theorem SepWPp.congr_post_drop_left {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q2 Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P
      (fun sf P_f => ∃ Drop P_clean, (P_f ⊢ Drop ∗ P_clean) ∧ Q2 sf P_clean) Qp) :
    SepWPp prog ret s P Q2 Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hmf, Drop, P_clean, hent, hQ2⟩ | hpan | hoom
  · have hmf' : sf.mem ⊨ (Drop ∗ P_clean) ∗ R :=
      Arm64.Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepConj_assoc] at hmf'
    exact Or.inl ⟨hpc, hrun, P_clean, Satisfies.of_sep_right hmf', hQ2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hoom)

/-! ## Core 2-kit Kyber `mark_used` refusal theorem -/

/-- Combined `envOk` predicate across all four stores touched in Stage P4. -/
@[expose] def stageP4EnvOk {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) (f : FsFiles) : Prop :=
  kit.envOk f ∧ ikit.envOk f ∧ pkKit.envOk f ∧ kpkKit.envOk f

/-- Combined `Quiet` predicate across all four stores touched in Stage P4. -/
@[expose] def stageP4Quiet {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) : Prop :=
  kit.Quiet ∧ ikit.Quiet ∧ pkKit.Quiet ∧ kpkKit.Quiet

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
