/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveId -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P4.1 Dispatch Proof: `save_identity`

Composes `p4_seg1a_ext_wp`, `saveShim`, `p4_seg1b_ext_wp`, `savePoll`, `p4_seg1c_gen_ext_wp`,
`saveFutDrop`, and the `+0x2ec` continuations into `stageP4_saveIdentity_dispatch_kits`
(`+0x34dc → kyberMarkUsedShimAddr` on `Ok c`, and `+0x34dc → s0.readReg64 .x30` on `Err ()`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

theorem _root_.CryptoVerification.LibsignalPublicApi.StoreKit.FsAt.of_steps_nil
    {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s s' : State}
    (h : FsAt envOk Q P s) (hst : Steps P s s') (htr : s'.trace = s.trace) :
    FsAt envOk Q P s' :=
  FsAt.of_steps_nil h hst htr

/-- Frame a residual spatial resource `F` onto a `SepWPp` proof ending at `ret` under `PanicOomProp s0`. -/
theorem SepWPp.frame_ret_oom {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P T F : SepProp} {Q1 Q : State → SepProp → Prop}
    (h1 : SepWPp prog ret s T Q1 (PanicOomProp s0))
    (hP : P = T ∗ F)
    (hpost : ∀ sf P1, sf.pc = ret → sf.status = .Running →
      Q1 sf P1 → Q sf (P1 ∗ F)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hst, ⟨hpc, hrun, P1, hm1, hQ1⟩ | ⟨hpan, Ppan, hmpan, hQpan⟩ | hex⟩ :=
    h1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    exact ⟨sf, hst, Or.inl ⟨hpc, hrun, P1 ∗ F, hm1, hpost sf P1 hpc hrun hQ1⟩⟩
  · rw [← sepConj_assoc] at hmpan
    refine ⟨sf, hst, Or.inr (Or.inl ⟨hpan, Ppan ∗ F, hmpan, fun R' hm' => ?_⟩)⟩
    rw [sepConj_assoc] at hm'
    have h2 := hQpan (F ∗ R') hm'
    rw [← sepConj_assoc] at h2
    exact Satisfies.mono (sepConj_mono_left (by
      rw [sepConj_assoc]; exact sepConj_mono_right (entails_anyHeap _))) h2
  · exact (not_satisfies_false_sepConj hex.2).elim

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
