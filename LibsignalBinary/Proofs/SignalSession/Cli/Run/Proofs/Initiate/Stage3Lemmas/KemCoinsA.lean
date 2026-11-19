/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 KEM Seed Unroll Part A (`+0x0b6c → +0x0c48`: `pqspk` Copy + Draws `0..6`)

Copies `pqspk` (`1568` bytes) to `[fsp + 0x9c0, fsp + 0xfe0)`, splits the scratch 32-bit word slots
at `[fsp + 0x08, fsp + 0x6c)`, and proves unrolled coin draws `0..6`.
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

private theorem scratch120_split (fsp : BitVec 64) :
    memRegion fsp 0x78 =
      memRegion fsp 8 ∗ memRegion (fsp + 0x68#64) 4 ∗ memRegion (fsp + 0x60#64) 4 ∗
      memRegion (fsp + 0x5c#64) 4 ∗ memRegion (fsp + 0x58#64) 4 ∗ memRegion (fsp + 0x54#64) 4 ∗
      memRegion (fsp + 0x50#64) 4 ∗ memRegion (fsp + 0x4c#64) 4 ∗ memRegion (fsp + 0x48#64) 4 ∗
      memRegion (fsp + 0x44#64) 4 ∗ memRegion (fsp + 0x40#64) 4 ∗ memRegion (fsp + 0x3c#64) 4 ∗
      memRegion (fsp + 0x38#64) 4 ∗ memRegion (fsp + 0x34#64) 4 ∗ memRegion (fsp + 0x30#64) 4 ∗
      memRegion (fsp + 0x2c#64) 4 ∗ memRegion (fsp + 0x28#64) 4 ∗ memRegion (fsp + 0x24#64) 4 ∗
      memRegion (fsp + 0x20#64) 4 ∗ memRegion (fsp + 0x1c#64) 4 ∗ memRegion (fsp + 0x18#64) 4 ∗
      memRegion (fsp + 0x14#64) 4 ∗ memRegion (fsp + 0x10#64) 4 ∗ memRegion (fsp + 0x0c#64) 4 ∗
      memRegion (fsp + 0x08#64) 4 ∗ memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
      memRegion (fsp + 0x70#64) 8 := by
  rw [← memRegion_merge_at fsp 8 112 (fsp + 0x08#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x08#64) 4 108 (fsp + 0x0c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x0c#64) 4 104 (fsp + 0x10#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x10#64) 4 100 (fsp + 0x14#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x14#64) 4 96 (fsp + 0x18#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x18#64) 4 92 (fsp + 0x1c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c#64) 4 88 (fsp + 0x20#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x20#64) 4 84 (fsp + 0x24#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x24#64) 4 80 (fsp + 0x28#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x28#64) 4 76 (fsp + 0x2c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x2c#64) 4 72 (fsp + 0x30#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x30#64) 4 68 (fsp + 0x34#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x34#64) 4 64 (fsp + 0x38#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x38#64) 4 60 (fsp + 0x3c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x3c#64) 4 56 (fsp + 0x40#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x40#64) 4 52 (fsp + 0x44#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x44#64) 4 48 (fsp + 0x48#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x48#64) 4 44 (fsp + 0x4c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x4c#64) 4 40 (fsp + 0x50#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x50#64) 4 36 (fsp + 0x54#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x54#64) 4 32 (fsp + 0x58#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x58#64) 4 28 (fsp + 0x5c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x5c#64) 4 24 (fsp + 0x60#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x60#64) 4 20 (fsp + 0x64#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x64#64) 4 16 (fsp + 0x68#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x68#64) 4 12 (fsp + 0x6c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x6c#64) 4 8 (fsp + 0x70#64) (by bv_omega) (by decide)]
  ac_rfl

private theorem kem_locals_9c0 (fsp : BitVec 64) :
    memRegion (fsp + 0x9c0#64) 0xc40 =
      memRegion (fsp + 0x9c0#64) 1568 ∗ memRegion (fsp + 0xfe0#64) 32 ∗
      memRegion (fsp + 0x1000#64) 0x600 := by
  rw [← memRegion_merge_at (fsp + 0x9c0#64) 1568 1568 (fsp + 0xfe0#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0xfe0#64) 32 0x600 (fsp + 0x1000#64) (by bv_omega) (by decide)]

private theorem kem_locals_1600 (fsp : BitVec 64) :
    memRegion (fsp + 0x1600#64) 24 =
      memRegion (fsp + 0x1600#64) 4 ∗ memRegion (fsp + 0x1604#64) 20 := by
  rw [← memRegion_merge_at (fsp + 0x1600#64) 4 20 (fsp + 0x1604#64) (by bv_omega) (by decide)]

private theorem mem4_elim_word {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {B R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ z : BitVec 32, SepWPp prog ret s (B ∗ ((a ↦₃₂ z) ∗ R)) Q Qp oom) :
    SepWPp prog ret s ((memRegion a 4 ∗ B) ∗ R) Q Qp oom := by
  rw [sepConj_assoc, ProofLib.memRegion_four a, sepExists_sepConj_left]
  exact sepWPp_exists_elim_oom fun z =>
    sepWPp_conseq_oom
      (Entails.of_eq (by rw [← sepConj_assoc, sepConj_comm (a ↦₃₂ z) B, sepConj_assoc])) (h z)

private theorem mem8_elim_word {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {B R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ z : BitVec 64, SepWPp prog ret s (B ∗ ((a ↦₆₄ z) ∗ R)) Q Qp oom) :
    SepWPp prog ret s ((memRegion a 8 ∗ B) ∗ R) Q Qp oom := by
  rw [sepConj_assoc, ProofLib.memRegion_eight a, sepExists_sepConj_left]
  exact sepWPp_exists_elim_oom fun z =>
    sepWPp_conseq_oom
      (Entails.of_eq (by rw [← sepConj_assoc, sepConj_comm (a ↦₆₄ z) B, sepConj_assoc])) (h z)

private theorem s3_repack_kpk {A : RustAlloc} (fsp : BitVec 64) (x : InitGhost)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64)
    (opkId : BitVec 32) :
    ((let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
      ((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
      ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
      memRegion (fsp + 0x308#64) 0x40 ∗
      ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
      ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
      ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
      ((fsp + 0x3e8#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      A.live pqspkPtr 1568 1 ∗
      ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
      (match x.bundle.opk with
       | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
       | none => memRegion (fsp + 0x439#64) 32) ∗
      ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) ∗
     (pqspkPtr ↦ₛ x.bundle.kpk)) =
    stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId := by
  (try dsimp only [stage3KeySlotsAt]); ac_rfl

set_option Elab.async false

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
