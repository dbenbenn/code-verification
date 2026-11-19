/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStores.Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli.RunProofs.Helpers

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] exists_two_pow_one exists_two_pow_eight
attribute [local wp_norm, local arm64_norm]
  sub_32_of_add_32 sub_24_of_add_32 sub_8_of_add_32
  add_32_sub_32 add_32_sub_32_assoc add_32_sub_24 add_32_sub_24_assoc
  add_32_sub_8 add_32_sub_8_assoc
  add_32_neg_32 add_32_neg_32_assoc add_32_neg_24 add_32_neg_24_assoc
  add_32_neg_8 add_32_neg_8_assoc add_one_sub_one
attribute [local simp, local wp_norm, local arm64_norm]
  reg_x0_eq reg_x1_eq reg_x2_eq reg_x19_eq reg_x20_eq reg_x21_eq reg_x22_eq
  reg_x23_eq reg_x24_eq reg_x25_eq reg_x26_eq reg_x27_eq reg_x28_eq
  reg_fp_eq reg_lr_eq

/-- Symbol name of `core::ptr::drop_glue::<signal_session::stores::Stores>`. -/
abbrev cliDropStoresName : String := "core::ptr::drop_glue::<libsignal_cli::stores::Stores>"

/-- Symbol name of `core::ptr::drop_glue::<signal_session::stores::IdentityFiles>` (shared with `KyberFiles` at `+0x78`). -/
abbrev cliDropIdentityFilesName : String :=
  "core::ptr::drop_glue::<libsignal_cli::stores::IdentityFiles>"

structure DropStoresGhost where
  a : BitVec 64
  g : StoresGhost

@[expose] def dropStoresSpec (A : RustAlloc) (stk : Nat) : Spec DropStoresGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ storesAt A x.a x.g ∗ A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 320 ∗ A.pool ∗ stackAt s0.sp stk

structure DropDirPairGhost where
  a : BitVec 64
  d0 : DirGhost
  d1 : DirGhost

@[expose] def dropDirPairSpec (A : RustAlloc) (stk : Nat) : Spec DropDirPairGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ dirAt A x.a x.d0 ∗ dirAt A (x.a + 0x28#64) x.d1 ∗
      A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 80 ∗ A.pool ∗ stackAt s0.sp stk

/-! ## Exact-stack proofs (`48 + extHookStack` and `96 + extHookStack`) -/

private def dropDirPairRawSpec (A : RustAlloc) : Spec DropDirPairGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ dirRawAt A x.a x.d0.changed ∗
      dirRawAt A (x.a + 0x28#64) x.d1.changed ∗ A.pool ∗ stackAt s.sp idExactStk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 80 ∗ A.pool ∗ stackAt s0.sp idExactStk

private def dropStoresRawSpec (A : RustAlloc) : Spec DropStoresGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      dirAt A x.a x.g.identity.own ∗ dirAt A (x.a + 0x28#64) x.g.identity.peers ∗
      dirRawAt A (x.a + 0x50#64) x.g.signed.changed ∗
      dirAt A (x.a + 0x78#64) x.g.kyber.oneTime ∗ dirAt A (x.a + 0xa0#64) x.g.kyber.lastResort ∗
      dirRawAt A (x.a + 0xc8#64) x.g.oneTime.changed ∗
      dirRawAt A (x.a + 0xf0#64) x.g.sessions.changed ∗
      dirRawAt A (x.a + 0x118#64) x.g.pub.changed ∗
      A.pool ∗ stackAt s.sp storesExactStk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 320 ∗ A.pool ∗ stackAt s0.sp storesExactStk

end CryptoVerification.SignalSession.Cli.RunProofs
