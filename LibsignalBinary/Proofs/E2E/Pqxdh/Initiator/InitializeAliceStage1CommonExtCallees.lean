/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.Leaves -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1CommonExtA -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1CommonExtB
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.CodeLayout

/-!
# Contract-Backed Initiator Callee Proofs (`tripleRatchetProgAtExt`)

Proves contract-backed `subroutine_ok` specifications on `tripleRatchetProgAtExt` for
`spqr_chain_params`, `<SessionState>::set_unacknowledged_kyber_pre_key_id`,
`<SessionState>::set_kyber_ciphertext`, `<kem::Ciphertext>::serialize`,
`<PrivateKey>::derive_public_key_bytes`, `<StaticSecret as Drop>::drop`, and
`<RootKey>::create_chain`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.HMAC CryptoGames.HKDF
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.Initiator

section StackSplits

private theorem stackAt_extract_split_calcExt (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 752 ∗ stackAt sp initAliceCalcStackExt :=
  initAlice_stackAt_split sp 752 initAliceCalcStackExt (by decide)

private theorem stackAt_extract_split_expandExt (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 336 ∗ stackAt sp expandMultiInfoStackExt :=
  initAlice_stackAt_split sp 336 expandMultiInfoStackExt (by decide)

private theorem stackAt_extract_split_allocExt (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 13264 ∗ stackAt sp allocHookStack :=
  initAlice_stackAt_split sp 13264 allocHookStack (by decide)

private theorem stackAt_kemSerialize48_ext (sp : BitVec 64) :
    stackAt sp tryCloneFromRefStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  LibsignalTripleRatchet.stackAt_split_cells sp 4096 6 (by decide)

private theorem memRegion_1569_split_ext (a : BitVec 64) :
    memRegion a 1569 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
    memRegion_split a 1 1568 (by decide), memRegion_one]

end StackSplits

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWPp_pure_mid_extCallees {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post postP : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) post postP) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) post postP := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

/-- `<StaticSecret as Drop>::drop` stub spec at `pqxdhHookStackExt` (`16384` B). -/
@[expose] def initAliceStaticDropExtSpec : Spec (BitVec 64) :=
  SignalSession.CliExt.zeroizeSpec

/-- Stack budget of `<RootKey>::create_chain` on `tripleRatchetProgAtExt`:
`576 + extractStackExt = 576 + 17360 = 17936` B. -/
@[simp, arm64_norm]
abbrev pqxdhCreateChainStackExt : Nat := 576 + extractStackExt

namespace Initiator

abbrev pqxdhCreateChainStackExt := Pqxdh.pqxdhCreateChainStackExt
end Initiator

end CryptoVerification.E2E.Pqxdh
