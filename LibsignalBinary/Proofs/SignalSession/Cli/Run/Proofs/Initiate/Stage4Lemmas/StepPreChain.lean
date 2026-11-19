/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage2
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Cells
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import Lean
import Lean.Elab.SyntheticMVars
import Lean.Meta.Reduce
import ProofLib.GenDecodes
import ProofLib.GenPlacedFetches
import ProofLib.ProgramReflection
import ProofLib.SepLogic.CodeLookup
import ProofLib.SepLogic.WP.ControlTactics
import ProofLib.VCGen
import ProofLib
import ProofLib.FsTrace
import ProofLib.Placed.Multi
import ProofLib.ProgramReflection.Variant.TrapTransfer
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExit
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage 4 Segment 1: `ephA` Draw/Clamp and `<RootKey>::create_chain` (`+4260 → +4576 / +4508`)

Executes `+4260 → +4496` (`hkSlotBytes` unpack, `coins_fill` `160..192`, X25519 scalar clamp,
`derive_public_key_bytes`, `StaticSecret::drop`, and `<RootKey>::create_chain`), then dispatches
`+4496 → +4576` on `.ok (rk1, ck1)` and `+4496 → +4508` on `.error .invalidKeyAgreement`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local arm64_norm, local wp_norm] cliInitiateFrame_eq BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for attrName in [`arm64_norm, `wp_norm] do
    let some ext ← Lean.Meta.Simp.getSimprocExtension? attrName
      | throwError "unknown simproc extension `{attrName}`"
    for declName in [``BitVec.reduceSub, ``BitVec.reduceNeg] do
      Lean.Meta.Simp.addSimprocAttrCore ext declName .local (post := true)

s4_clean_sp_attrs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  Keys.clamp_byte0_norm Keys.clamp_byte0_norm32
  Keys.clamp_byte31_bfxil_norm Keys.clamp_byte31_bfxil_norm'

/-- Total outcome dichotomy for `<RootKey>::create_chain`: every X25519 agreement output produces
either `.ok (rk1, ck1)` or `.error .invalidKeyAgreement`. -/
theorem rootCreateChain_ok_or_err (C : Crypto) (rk : RootKey)
    (their : PublicKey) (our : PrivateKey) :
    (∃ rk1 ck1, rootCreateChain C rk their our = .ok (rk1, ck1)) ∨
      rootCreateChain C rk their our = .error .invalidKeyAgreement := by
  rcases hdh : calculateAgreement C.X their our with _ | ss
  · right
    exact Keys.rootCreateChain_of_calculateAgreement_none C rk their our hdh
  · left
    exact ⟨_, _, Keys.rootCreateChain_of_calculateAgreement_some C rk their our ss hdh⟩

theorem stage4EphVec_len (coins : List (BitVec 8)) :
    (((padCoins coins).toList.drop 160).take 32).length = 32 := by
  simp; decide

/-- 32-byte coin slice at offset `160..192` drawn for `ephA`. -/
abbrev stage4EphVec (coins : List (BitVec 8)) : List.Vector (BitVec 8) 32 :=
  ⟨((padCoins coins).toList.drop 160).take 32, stage4EphVec_len coins⟩

private theorem prechain_4260_mem_unpack (fsp : BitVec 64) (Rest : SepProp) :
    memRegion (fsp + 2192#64) 24 ∗ memRegion (fsp + 2224#64) 32 ∗
    memRegion (fsp + 2256#64) 36 ∗ memRegion (fsp + 2304#64) 32 ∗
    memRegion (fsp + 5632#64) 32 ∗ Rest =
    ∃∗ u2192_0 : BitVec 64, ∃∗ u2192_1 : BitVec 64, ∃∗ u2192_2 : BitVec 64,
    ∃∗ u2224_0 : BitVec 64, ∃∗ u2224_1 : BitVec 64, ∃∗ u2224_2 : BitVec 64, ∃∗ u2224_3 : BitVec 64,
    ∃∗ u2256_0 : BitVec 64, ∃∗ u2256_1 : BitVec 64, ∃∗ u2256_2 : BitVec 64, ∃∗ u2256_3 : BitVec 64,
    ∃∗ u2288 : BitVec 32,
    ∃∗ u2304_0 : BitVec 64, ∃∗ u2304_1 : BitVec 64, ∃∗ u2304_2 : BitVec 64, ∃∗ u2304_3 : BitVec 64,
    ∃∗ u5632_0 : BitVec 64, ∃∗ u5632_1 : BitVec 64, ∃∗ u5632_2 : BitVec 64, ∃∗ u5632_3 : BitVec 64,
      ((fsp + 2192#64) ↦₆₄ u2192_0) ∗ ((fsp + 2200#64) ↦₆₄ u2192_1) ∗ ((fsp + 2208#64) ↦₆₄ u2192_2) ∗
      ((fsp + 2224#64) ↦₆₄ u2224_0) ∗ ((fsp + 2232#64) ↦₆₄ u2224_1) ∗
      ((fsp + 2240#64) ↦₆₄ u2224_2) ∗ ((fsp + 2248#64) ↦₆₄ u2224_3) ∗
      ((fsp + 2256#64) ↦₆₄ u2256_0) ∗ ((fsp + 2264#64) ↦₆₄ u2256_1) ∗
      ((fsp + 2272#64) ↦₆₄ u2256_2) ∗ ((fsp + 2280#64) ↦₆₄ u2256_3) ∗ ((fsp + 2288#64) ↦₃₂ u2288) ∗
      ((fsp + 2304#64) ↦₆₄ u2304_0) ∗ ((fsp + 2312#64) ↦₆₄ u2304_1) ∗
      ((fsp + 2320#64) ↦₆₄ u2304_2) ∗ ((fsp + 2328#64) ↦₆₄ u2304_3) ∗
      ((fsp + 5632#64) ↦₆₄ u5632_0) ∗ ((fsp + 5640#64) ↦₆₄ u5632_1) ∗
      ((fsp + 5648#64) ↦₆₄ u5632_2) ∗ ((fsp + 5656#64) ↦₆₄ u5632_3) ∗ Rest := by
  rw [cells3_eq_memRegion24 (fsp + 2192#64), cells4_eq_memRegion32 (fsp + 2224#64),
      cells4_4_eq_memRegion36 (fsp + 2256#64), cells4_eq_memRegion32 (fsp + 2304#64),
      cells4_eq_memRegion32 (fsp + 5632#64)]
  s4_exists_eq

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
