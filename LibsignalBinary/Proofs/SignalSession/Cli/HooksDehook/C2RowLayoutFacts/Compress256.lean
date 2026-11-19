/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen

/-!
# `Placeable`, `GhostRowSpecOk`, `RoDataAt`, and Hull Glue for `sha2::sha256::compress256`

Discharges the concrete placement, `GhostRowSpecOk`, `.rodata` `K32`, and `.text.lib2`
hull/return-address guards for `lsCompress256Sym` (`sha2::sha256::compress256`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (lsCompress256Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
  (compress256Block compress256K32Data compress256Lib sha2K32Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells (sha256KBytes)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays
  (compress256ByteLen compress256Ghost compress256Ghost_rowSpecOk compress256Placement
   keepR_compress256)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (GhostRowSpecOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3LsRetAddr624_lt_firstExternStub isLinkedPanicAddr isLinkedPanicAddr_false_of_mid keepLib2Text
   keepLib2Text_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2Compress256Addr c2Compress256ByteLen c2Compress256K32Addr c2FirstExternStubAddr
   c2Lib2DehookedSyms c2Lib2TextHi c2Lib2TextLo)

/-- Concrete `Obj.Placement` for `compress256Lib` (`base := c2Compress256Addr`,
    `ρ sha2K32Sym := c2Compress256K32Addr`). -/
@[expose] def c2Compress256Pl : Obj.Placement :=
  compress256Placement c2Compress256Addr c2Compress256K32Addr

theorem c2Compress256Pl_base : c2Compress256Pl.base = c2Compress256Addr :=
  rfl

theorem c2Compress256Pl_k32 : c2Compress256Pl.ρ sha2K32Sym = c2Compress256K32Addr := by
  simp [c2Compress256Pl, compress256Placement]

theorem c2_checkCompress256Placeable_ok :
    compress256Block.checkPlaceable c2Compress256Pl = true := by
  decide +kernel

theorem c2_compress256Lib_placeable :
    compress256Lib.Placeable c2Compress256Pl where
  text := CodeBlock.placeable_of_checkPlaceable c2_checkCompress256Placeable_ok
  data_nodup := by decide
  data_ok := by
    intro d hd
    simp only [compress256Lib, List.mem_singleton] at hd
    subst hd
    refine ⟨by decide, by decide, ?_, ?_⟩
    · dsimp only [compress256K32Data]; rw [c2Compress256Pl_k32]; decide
    · dsimp only [compress256K32Data]; rw [c2Compress256Pl_k32]; decide +kernel
  data_relocs_ok := by
    intro d hd r hr
    simp only [compress256Lib, List.mem_singleton] at hd
    subst hd
    cases hr

theorem keepR_compress256_c2_sub_keepLib2Text {pc : BitVec 64}
    (hk : keepR_compress256 c2Compress256Pl pc = true) :
    keepLib2Text pc = true := by
  unfold keepR_compress256 c2Compress256Pl compress256Placement compress256ByteLen at hk
  have hlt : (pc - c2Compress256Addr).toNat < 7636 := of_decide_eq_true hk
  have hlo : c2Lib2TextLo.toNat ≤ c2Compress256Addr.toNat := by decide
  have hhi : c2Compress256Addr.toNat + 7636 ≤ c2Lib2TextHi.toNat := by decide
  have htop : c2Lib2TextHi.toNat < 2 ^ 64 := by decide
  unfold keepLib2Text
  apply decide_eq_true
  have hpc_eq : pc = c2Compress256Addr + (pc - c2Compress256Addr) := by bv_omega
  have hpc_nat : pc.toNat = c2Compress256Addr.toNat + (pc - c2Compress256Addr).toNat := by
    conv => lhs; rw [hpc_eq]
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

theorem keepR_compress256_c2_sub_rxProg {pc : BitVec 64}
    (hk : keepR_compress256 c2Compress256Pl pc = true) :
    progKeep f3TrialRxProg pc = true :=
  keepLib2Text_sub_rxProg (keepR_compress256_c2_sub_keepLib2Text hk)

theorem keepR_compress256_c2_noPanic {pc : BitVec 64}
    (hk : keepR_compress256 c2Compress256Pl pc = true) :
    isLinkedPanicAddr pc = false := by
  unfold keepR_compress256 c2Compress256Pl compress256Placement compress256ByteLen at hk
  have hlt : (pc - c2Compress256Addr).toNat < 7636 := of_decide_eq_true hk
  have hlo : 0x47ac2c ≤ c2Compress256Addr.toNat := by decide
  have hhi : c2Compress256Addr.toNat + 7636 ≤ 0x4cb070 := by decide
  have hpc_eq : pc = c2Compress256Addr + (pc - c2Compress256Addr) := by bv_omega
  have hpc_nat : pc.toNat = c2Compress256Addr.toNat + (pc - c2Compress256Addr).toNat := by
    conv => lhs; rw [hpc_eq]
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact isLinkedPanicAddr_false_of_mid (by omega) (by omega)

theorem c2_compress256_hKeep [LibsignalPlacement]
    (hLs : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt
      CryptoVerification.SignalSession.cliElfBytes CryptoVerification.lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr624 lr) :
    keepR_compress256 c2Compress256Pl lr = false := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hlr
  have hlo : c2FirstExternStubAddr.toNat ≤ c2Lib2TextLo.toNat := by decide
  cases hk : keepR_compress256 c2Compress256Pl lr
  · rfl
  · have hlib2 := keepR_compress256_c2_sub_keepLib2Text hk
    unfold keepLib2Text at hlib2
    rw [decide_eq_true_eq] at hlib2
    omega

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256
