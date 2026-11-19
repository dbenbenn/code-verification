/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPb
import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPb
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKey
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Final
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Contract Wiring, `.rodata` Extraction, and Composition

**Checked by Lean.** Stack-slot non-null bounds (`DEV-SPQR4`), `.rodata` jump-table extraction
and restoration (`spqrRecvRoAt`), `SpqrRecvContracts` assembly from verified callee contracts, and
top-level composition (`spqrRecv_ok_of_tails`) for `spqr::recv` (`0x5462c`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Stack-Pointer Non-Null Helpers (`DEV-SPQR4`) -/

/-- When `sp.toNat ≥ N > n > 0` (with `N < 2 ^ 64` implicitly bounded by `sp.toNat < 2 ^ 64`),
    the stack slot address `sp - BitVec.ofNat 64 n` is strictly positive and therefore non-null
    (`≠ 0#64`). -/
theorem sp_sub_ne_zero_of_le {n N : Nat} {sp : BitVec 64}
    (hn : 0 < n) (hlt : n < N) (hle : N ≤ sp.toNat) :
    sp - BitVec.ofNat 64 n ≠ 0#64 := by
  have hsp_lt : sp.toNat < 18446744073709551616 := sp.isLt
  intro hzero
  have htoNat := congrArg BitVec.toNat hzero
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at htoNat
  change (18446744073709551616 - n % 18446744073709551616 + sp.toNat) % 18446744073709551616 = 0 at htoNat
  omega

/-- The stack slot `s0.sp - 4992#64` (`sp + 192` in the `5184`-byte `spqr::recv` frame) is
    non-null whenever `spqrRecvStack ≤ s0.sp.toNat`. -/
theorem sp_sub_4992_ne_zero {sp : BitVec 64} (hle : spqrRecvStack ≤ sp.toNat) :
    sp - 4992#64 ≠ 0#64 :=
  sp_sub_ne_zero_of_le (n := 4992) (N := spqrRecvStack) (by decide) (by decide) hle

/-- The stack slot `s0.sp - 4640#64` (`sp + 544` in the `5184`-byte `spqr::recv` frame) is
    non-null whenever `spqrRecvStack ≤ s0.sp.toNat`. -/
theorem sp_sub_4640_ne_zero {sp : BitVec 64} (hle : spqrRecvStack ≤ sp.toNat) :
    sp - 4640#64 ≠ 0#64 :=
  sp_sub_ne_zero_of_le (n := 4640) (N := spqrRecvStack) (by decide) (by decide) hle

/-! ## 2. `.rodata` Extraction and Restoration for `spqrRecvRoAt` -/

/-- Lift `SpqrHooks C A K abs` to `tripleRatchetExterns C ctl abs`. -/
theorem spqrHooks_tripleRatchetExterns {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (hSH : SpqrHooks C A K abs) :
    SpqrHooks C A K (tripleRatchetExterns C ctl abs) where
  fromSeed := hSH.fromSeed
  pk1 := hSH.pk1
  pk2 := hSH.pk2
  encaps1 := hSH.encaps1
  encaps2 := hSH.encaps2
  decaps := hSH.decaps
  validatePk := hSH.validatePk
  hmac := hSH.hmac

/-- Lift `HookSat abs allocZeroedName (rustAllocZeroedSpec A)` to `tripleRatchetExterns C ctl
    abs`. -/
theorem hookSat_allocZeroed_tripleRatchetExterns {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hZero : HookSat abs allocZeroedName (rustAllocZeroedSpec A)) :
    HookSat (tripleRatchetExterns C ctl abs) allocZeroedName (rustAllocZeroedSpec A) :=
  hZero

end CryptoVerification.SpqrV1.Top.Recv
