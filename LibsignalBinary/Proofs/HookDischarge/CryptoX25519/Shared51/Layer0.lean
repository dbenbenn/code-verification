/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs -- proof-setup: allow-public-import
import ProofLib.SepLogic.ByteRegion
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase

/-!
# Constant-time leaf helper (`subtle::black_box::<u8>`)

Proves `black_box_u8_ok : BlackBoxU8Ok` (`Blk00`, 5 insns) for `x25519CliMultiLib`.
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Layer0

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl x25519Leaf_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  blackBoxU8Spec BlackBoxU8Ok)

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 00 x25519CliMultiLib X25519CliPlacement 5 rebase rho sub

public section

/-- `subtle::black_box::<u8>` (`Blk00`, 5 insns). -/
theorem black_box_u8_ok : BlackBoxU8Ok := by
  intro _
  apply x25519Leaf_ok x25519CliPC00 x25519CliPl00
  intro b hb hbase
  wp_init
  have hst : stackFrame s0 16 =
      ((∃∗ v : BitVec 8, (s0.sp - 4#64) ↦₈ v) ∗
        (memRegion (s0.sp - 16#64) 12 ∗ memRegion (s0.sp - 3#64) 3)) := by
    change memRegion (s0.sp - 16#64) 16 = _
    rw [memRegion_split3 (s0.sp - 16#64) 16 12 1 (by decide) (by decide), memRegion_one]
    have h1 : s0.sp - 16#64 + 12#64 = s0.sp - 4#64 := by bv_arith
    have h2 : s0.sp - 16#64 + 13#64 = s0.sp - 3#64 := by bv_arith
    rw [h1, h2]
  rw [hst]
  wp_pull_exists
  wp_steps
  refine SepWP.weaken_pre (P' := stackFrame s0 16)
    (by rw [hst]; exact sepConj_mono_left (Entails.sepExists_right _ (Entails.refl _))) ?_
  clear hst
  wp_done

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Layer0
