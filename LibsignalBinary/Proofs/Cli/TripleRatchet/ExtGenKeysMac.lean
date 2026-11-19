/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
public import LibsignalBinary.Proofs.TripleRatchet.Statements -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceExt
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

/-!
# Stacked `generate_keys`, `compute_mac`, and `verify_mac_with_addresses`

Proves stacked `extHookStack` contracts for `SignalMessage::compute_mac` (`17424` B),
`SignalMessage::verify_mac_with_addresses` (`17712` B), and `MessageKeyGenerator::generate_keys`
(`17856` B).
-/

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtGenKeysMac

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SignalSession

/-- Stack depth of `MessageKeyGenerator::generate_keys` when calling stacked `Hkdf::extract`
(`extractStackExt = 17360` B below its 496-byte frame, total `17856` B). -/
abbrev generateKeysStackExt : Nat := 496 + extractStackExt

@[expose] def generateKeysSpecExt (F : ShaCompress) (A : RustAlloc) : Spec GenerateKeysGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.genA ∧ s.readReg64 .x1 = x.pqrKeyA ∧ s.readReg64 .x8 = x.ret ∧
      x.g.seed.length = 32⌝ ∗
      mkgAt A x.genA x.g ∗ spqrRecvKeyAt A x.pqrKeyA x.pqrKey ∗ memRegion x.ret 84 ∗
      A.pool ∗ stackAt s.sp generateKeysStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.genA 40 ∗ memRegion x.pqrKeyA 24 ∗
      messageKeysAt x.ret (x.g.generateKeys F x.pqrKey) ∗
      A.pool ∗ stackAt s0.sp generateKeysStackExt

theorem fnFrame_split_generateKeysExt_pre (sp : BitVec 64) :
    stackAt sp generateKeysStackExt =
      stackAt (sp - 496#64) extractStackExt ∗
        ProofLib.cells (sp - 496#64) 10 ∗ ProofLib.cells (sp - 416#64) 4 ∗
        ProofLib.cells (sp - 384#64) 14 ∗ memRegion (sp - 272#64) 176 ∗
        ProofLib.cells (sp - 96#64) 12 := by
  change memRegion (sp - BitVec.ofNat 64 17856) 17856 =
    memRegion (sp - 496#64 - BitVec.ofNat 64 17360) 17360 ∗
      ProofLib.cells (sp - 496#64) 10 ∗ ProofLib.cells (sp - 416#64) 4 ∗
      ProofLib.cells (sp - 384#64) 14 ∗ memRegion (sp - 272#64) 176 ∗
      ProofLib.cells (sp - 96#64) 12
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 17856) (n := 17360) (k := 496)
      (b' := sp - 496#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 496#64) (n := 80) (k := 416) (b' := sp - 416#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 416#64) (n := 32) (k := 384) (b' := sp - 384#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 384#64) (n := 112) (k := 272) (b' := sp - 272#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 176) (k := 96) (b' := sp - 96#64) rfl
      (by bv_omega) (by decide),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 496#64) 10 (by decide) :
      memRegion (sp - 496#64) 80 = ProofLib.cells (sp - 496#64) 10),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 416#64) 4 (by decide) :
      memRegion (sp - 416#64) 32 = ProofLib.cells (sp - 416#64) 4),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 384#64) 14 (by decide) :
      memRegion (sp - 384#64) 112 = ProofLib.cells (sp - 384#64) 14),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = ProofLib.cells (sp - 96#64) 12)]
  have hsub : sp - 496#64 - BitVec.ofNat 64 17360 = sp - BitVec.ofNat 64 17856 := by bv_kernel
  rw [hsub]

theorem fnFrame_split_generateKeysExt_post (sp : BitVec 64) :
    stackAt sp generateKeysStackExt =
      stackAt (sp - 496#64) extractStackExt ∗
        ProofLib.cells (sp - 496#64) 10 ∗ ProofLib.cells (sp - 416#64) 8 ∗
        memRegion (sp - 352#64) 80 ∗ ProofLib.cells (sp - 272#64) 4 ∗
        ProofLib.cells (sp - 240#64) 4 ∗ ProofLib.cells (sp - 208#64) 14 ∗
        ProofLib.cells (sp - 96#64) 12 := by
  change memRegion (sp - BitVec.ofNat 64 17856) 17856 =
    memRegion (sp - 496#64 - BitVec.ofNat 64 17360) 17360 ∗
      ProofLib.cells (sp - 496#64) 10 ∗ ProofLib.cells (sp - 416#64) 8 ∗
      memRegion (sp - 352#64) 80 ∗ ProofLib.cells (sp - 272#64) 4 ∗
      ProofLib.cells (sp - 240#64) 4 ∗ ProofLib.cells (sp - 208#64) 14 ∗
      ProofLib.cells (sp - 96#64) 12
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 17856) (n := 17360) (k := 496)
      (b' := sp - 496#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 496#64) (n := 80) (k := 416) (b' := sp - 416#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 416#64) (n := 64) (k := 352) (b' := sp - 352#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 352#64) (n := 80) (k := 272) (b' := sp - 272#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 32) (k := 240) (b' := sp - 240#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 240#64) (n := 32) (k := 208) (b' := sp - 208#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 208#64) (n := 112) (k := 96) (b' := sp - 96#64) rfl
      (by bv_omega) (by decide),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 496#64) 10 (by decide) :
      memRegion (sp - 496#64) 80 = ProofLib.cells (sp - 496#64) 10),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 416#64) 8 (by decide) :
      memRegion (sp - 416#64) 64 = ProofLib.cells (sp - 416#64) 8),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 272#64) 4 (by decide) :
      memRegion (sp - 272#64) 32 = ProofLib.cells (sp - 272#64) 4),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 240#64) 4 (by decide) :
      memRegion (sp - 240#64) 32 = ProofLib.cells (sp - 240#64) 4),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 208#64) 14 (by decide) :
      memRegion (sp - 208#64) 112 = ProofLib.cells (sp - 208#64) 14),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = ProofLib.cells (sp - 96#64) 12)]
  have hsub : sp - 496#64 - BitVec.ofNat 64 17360 = sp - BitVec.ofNat 64 17856 := by bv_kernel
  rw [hsub]

section GenerateKeysStacked

open CryptoVerification.LibsignalTripleRatchet.Keys.GenerateKeysFacts

attribute [-arm64_norm]
  _root_.CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  _root_.CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  _root_.CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_sub_lit bv_sub_add_lit bv_add_neg64
attribute [local simp, local arm64_norm] hkdfExtract_length' whisperMessageKeys_length lt_32_18
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

private theorem stackAt_extract_expand_split' (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 336 ∗ stackAt sp expandMultiInfoStackExt := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 336 ∗ memRegion (sp - 17024#64) 17024
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 336) (k := 17024)
    (b' := sp - 17024#64) rfl (by bv_omega) (by decide)

private theorem stackAt_extract_extHook_split' (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 976 ∗ stackAt sp extHookStack := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 976 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 976) (k := 16384)
    (b' := sp - 16384#64) rfl (by bv_omega) (by decide)

end GenerateKeysStacked

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtGenKeysMac
