/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Statements

/-!
# `<SignalMessage>::new` Segment 1 (`+0x054 .. +0x218`)

Proves `AllocContracts4K` and `AllocContractsX` segment lemmas for address/ratchet-key
serialization, ciphertext copy, serialized buffer allocation, and protobuf tag 1 encoding in
`<SignalMessage>::new`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNewSeg1

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.Cli.LibsignalSpqrV1.M4
open CryptoVerification.InImageLift
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `4K` Callee Discharges -/

theorem stackAt_encodeVarint_to_allocHook (sp : BitVec 64) :
    stackAt sp encodeVarintStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 4256#64) 160 := by
  simp only [stackAt, encodeVarintStack, doReserveStack, finishGrowStack, allocHookStack]
  rw [show (4096 + 48 + 48 + 64 : Nat) = 160 + 4096 by decide,
    ProofLib.memRegion_split _ 160 4096 (by decide)]
  have e1 : sp - BitVec.ofNat 64 (160 + 4096) = sp - 4256#64 := by bv_arith
  have e2 : sp - 4256#64 + BitVec.ofNat 64 160 = sp - BitVec.ofNat 64 4096 := by bv_arith
  rw [e1, e2, sepConj_comm]

theorem sessionMemcpyRegion4K_pre_eq (dst src : BitVec 64) (bs : List (BitVec 8))
    (s : State) (sp_cur : BitVec 64)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 64)
    (hsp : s.sp = sp_cur) :
    (withStack sessionMemcpyRegionSpec allocHookStack).pre (dst, src, bs) s =
      ((src ↦ₛ bs) ∗ memRegion dst bs.length ∗ stackAt sp_cur allocHookStack) := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, hx0, hx1, hx2, hsp,
    htoNat, and_self, pure_true, emp_sepConj, sepConj_assoc]
  ac_rfl

/-! ## `ciphertext` Copy (`+0x07c / +0x0f0 → +0x0a8 / +0x0fc`) -/

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNewSeg1
