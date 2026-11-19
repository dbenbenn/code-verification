/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Ext-Generic `WithStoresVT` Specifications and Environments

Defines `OtrEncryptOkT_ext`, `EncCalleesT_ext`, `EncEnv_ext`, `EncEnvT_ext` (carrying
`scopeTsZero`), `withStoresEncSpecVT_ext`, `EncFsCtx_ext`, `SegExit_ext`, and `h45_SegExitVT_ext`
on `tripleRatchetProgAtExt` without importing `signalSessionCliCode`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt



open CryptoVerification.Cli.LibsignalPublicApi (encryptWithStoresName)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

namespace WithStoresVT

abbrev shimSpecExt : Spec Unit :=
  { pre := fun _ _ => emp
    post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ }

abbrev memcpySpecExt : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  { pre := (libcMemcpySpec allocHookStack).pre
    post := fun (dst, src, bs) s0 sf =>
      ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
        (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack }

abbrev memcpyROSpecExt : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withStack
    { pre := fun (dst, src, bs) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
          bs.length ≤ 2 ^ 64⌝ ∗ memRegion dst bs.length ∗ (src ↦ᵣ bs)
      post := fun (dst, src, bs) s0 sf =>
        ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) }
    allocHookStack

abbrev durationSinceEpochSpecExt : Spec (BitVec 64 × BitVec 64) :=
  { pre := fun (p, ret) s =>
      ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧
        s.readReg64 .x1 = 0#64 ∧ (s.readReg64 .x2).setWidth 32 = 0#32⌝ ∗
        (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₃₂ 0#32) ∗ memRegion (p + 12#64) 4 ∗
        memRegion ret 24 ∗ stackAt s.sp 16384
    post := fun (p, ret) s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗
        memRegion p 16 ∗
        ((∃∗ w2 : BitVec 64, ∃∗ w0 : BitVec 64,
          (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2))) ∗
        stackAt s0.sp 16384 }

/-- Contract-backed hook bundle for CLI `MessageEncrypt` on `tripleRatchetProgAtExt img.base ext`. -/
structure EncHooksExt (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S ext where
  shim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" shimSpecExt
  memcpy : HookSat ext "memcpy" memcpySpecExt
  memcpyRO : HookSat ext "memcpy" memcpyROSpecExt
  timeAdd : HookSat ext timeAddHookName timeAddSpec
  durationSinceEpoch : HookSat ext durationSinceHookName durationSinceEpochSpecExt

end WithStoresVT

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
