/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# Stage 3 PQXDH Step A (`+0x0760 → +0x0858`: `secrets` Alloc + `DH1`)

Advances from `AtStage3` (`+0x0760`) + `stage3Mem` across `__rust_alloc(192, 1)` (handling OOM via
`oom_1918_ok`) and `DH1 = X25519(ikASk, spkB)` (handling zero-DH via `unwind_1548_ok`) to `+0x0858`
with `F_X25519 ++ dh1` written at `secretsPtr` (`len = 64`, `cap = 192`).
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

private theorem dh1_oom_jmp {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (h : SepWP prog mid s emp
      (fun s' q => q = emp ∧ s'.pc = mid ∧ s'.status = .Running ∧ s'.trace = s.trace))
    (hoom : ∀ s' : State, s'.pc = mid → s'.status = .Running → s'.trace = s.trace →
      SepWPp prog ret s' P Q Qp Qoom) : SepWPp prog ret s P Q Qp Qoom := fun R hm hL => by
  rcases h.elim (by rwa [emp_sepConj] : s.mem ⊨ emp ∗ (P ∗ R)) hL with
    ⟨s', hst, ⟨-, -, _, hq, rfl, hpc', hrun', htr'⟩ | ⟨_, hf⟩⟩
  · rw [emp_sepConj] at hq
    obtain ⟨sf, hst', hout⟩ := hoom s' hpc' hrun' htr' R hq (hst.codeLoaded hL)
    exact ⟨sf, hst.trans hst', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

private theorem s3_loc_split (fsp : BitVec 64) :
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) =
      memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗ memRegion (fsp + 0x930#64) 8 ∗
      memRegion (fsp + 0x938#64) 0x20 ∗ memRegion (fsp + 0x958#64) 0x48 ∗
      memRegion (fsp + 0x9a0#64) 0x20 ∗ memRegion (fsp + 0x9c0#64) 0xc40 ∗
      memRegion (fsp + 0x1600#64) 24 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
      memRegion (fsp + 0x1c60#64) 8 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
      memRegion (fsp + 0x1c70#64) 8 ∗ memRegion (fsp + 0x1c78#64) 0x18 := by
  simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
  rw [← memRegion_merge_at (fsp + 0x5ba#64) (0x930 - 0x5ba) 0x1360 (fsp + 0x930#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x930#64) 8 0x1358 (fsp + 0x938#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x938#64) 0x20 0x1338 (fsp + 0x958#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x958#64) 0x48 0x12f0 (fsp + 0x9a0#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x9a0#64) 0x20 0x12d0 (fsp + 0x9c0#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x9c0#64) 0xc40 0x690 (fsp + 0x1600#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1600#64) 24 0x678 (fsp + 0x1618#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1618#64) 0x648 0x30 (fsp + 0x1c60#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c60#64) 8 0x28 (fsp + 0x1c68#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c68#64) 8 0x20 (fsp + 0x1c70#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by bv_omega) (by decide)]

private theorem s3_sec_split (secretsPtr : BitVec 64) :
    memRegion secretsPtr 192 =
      memRegion secretsPtr 32 ∗ memRegion (secretsPtr + 32#64) 32 ∗
      memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
      memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 := by
  rw [← memRegion_merge_at secretsPtr 32 160 (secretsPtr + 32#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 32#64) 32 128 (secretsPtr + 64#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 64#64) 32 96 (secretsPtr + 96#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 96#64) 32 64 (secretsPtr + 128#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 128#64) 32 32 (secretsPtr + 160#64) (by bv_omega) (by decide)]

set_option Elab.async false

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
