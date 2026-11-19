/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.ConsumerBridges -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase -- proof-setup: allow-public-import
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `x25519CliMultiLib` Placement, RX Code-Walk, `.rodata`, and Hull Facts

Supplies the concrete zero-hook stock-ELF `Obj.MultiPlacement` (`c2X25519Mpl`) for all 19 code
blocks and 3 `.rodata` tables of `x25519CliMultiLib` (`<PublicKey as From<&StaticSecret>>::from`
and `StaticSecret::diffie_hellman`), discharging every field of
`X25519GhostReplays.C2X25519LayoutFacts`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (cliElfBytes libsignalSessionLib lsDiffieHellmanSym lsPubFromSecretSym)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.ConsumerBridges
  (X25519CliRoOk diffieHellmanSym pubFromSecretSym x25519MultiKeep)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
  (ed25519BasepointTableBytes ed25519_basepoint_table fe51MontA24Bytes fe51OneBytes
   fe51_mont_a24 fe51_one)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (checkMultiBlockWalk checkProgCodeSubslice_of_multiBlockWalk
   codeLoaded_of_multiBlockWalk rGetD_map_some_eq_getElem? resolve_lsExtern_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_keepLib2Text_of_sub_lt c2_noPanic_of_band_sub_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3CodeInv_roDataAt_of_checkSegSlice f3LsRetAddr624_lt_firstExternStub isLinkedPanicAddr
   keepLib2Text keepLib2Text_sub_rxProg keepTextBPre)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3TrialRxWordTree)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BlackBoxAddr c2Compress256K32Addr c2DurationSinceCst16Addr c2FirstExternStubAddr
   c2Lib2TextHi c2Lib2TextLo c2SharedSecretDropAddr c2Zeroize32Addr wp4HandleErrorAddr)

/-- Stock-ELF entry address of `<StaticSecret>::diffie_hellman` (`lsDiffieHellmanSym`, `B17`,
    `0x481d7c`). -/
@[expose] def c2DiffieHellmanAddr : BitVec 64 := c2SharedSecretDropAddr - 52#64

/-- Stock-ELF entry address of `<PublicKey as From<&StaticSecret>>::from` (`lsPubFromSecretSym`,
    `B18`, `0x481db4`). -/
@[expose] def c2PubFromSecretAddr : BitVec 64 := c2SharedSecretDropAddr + 4#64

/-- Concrete zero-hook stock-ELF `Obj.MultiPlacement` for the 19 blocks and 3 `.rodata` tables of
    `x25519CliMultiLib`. -/
@[expose] def c2X25519Mpl : Obj.MultiPlacement where
  base i :=
    match i with
    |  0 => c2BlackBoxAddr
    |  1 => c2Zeroize32Addr + 252#64
    |  2 => c2BlackBoxAddr + 8992#64
    |  3 => c2Zeroize32Addr - 6372#64
    |  4 => c2Zeroize32Addr + 3716#64
    |  5 => c2BlackBoxAddr + 3752#64
    |  6 => c2BlackBoxAddr + 7312#64
    |  7 => c2Zeroize32Addr - 8448#64
    |  8 => c2SharedSecretDropAddr - 2372#64
    |  9 => c2Zeroize32Addr - 2664#64
    | 10 => c2Zeroize32Addr - 7872#64
    | 11 => c2Zeroize32Addr - 8968#64
    | 12 => c2Zeroize32Addr - 2220#64
    | 13 => c2Zeroize32Addr + 3048#64
    | 14 => c2Zeroize32Addr - 3972#64
    | 15 => c2Zeroize32Addr + 3880#64
    | 16 => c2BlackBoxAddr + 7244#64
    | 17 => c2SharedSecretDropAddr - 52#64
    | 18 => c2SharedSecretDropAddr + 4#64
    | _  => 0#64
  ρ sym :=
    if sym == "curve25519_dalek:.rodata..Lanon.0" then
      c2DurationSinceCst16Addr + 3152#64
    else if sym == "curve25519_dalek:.rodata..Lanon.35" then
      c2DurationSinceCst16Addr + 3488#64
    else if sym == "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN" then
      c2DurationSinceCst16Addr + 11256#64
    else if sym == "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.5" then
      c2DurationSinceCst16Addr + 3192#64
    else if sym == "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.65" then
      c2Compress256K32Addr - 1048#64
    else if sym == "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" then
      0x47a2a4#64
    else 0#64

set_option maxRecDepth 4000000 in
/-- Full `Placeable` witness for `x25519CliMultiLib` at `c2X25519Mpl`. -/
theorem c2_x25519_placeable : x25519CliMultiLib.Placeable c2X25519Mpl :=
  x25519CliMultiLib.placeable_of_checkPlaceable (by rfl_kernel)

theorem c2_x25519_resolve_pubFromSecret {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsPubFromSecretSym = c2X25519Mpl.base 18 :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsPubFromSecretSym).trans (by rfl_kernel)

theorem c2_x25519_resolve_diffieHellman {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsDiffieHellmanSym = c2X25519Mpl.base 17 :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsDiffieHellmanSym).trans (by rfl_kernel)

theorem c2_x25519_resolve_pubFromSecret_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsPubFromSecretSym =
      x25519CliMultiLib.fnAddr c2X25519Mpl pubFromSecretSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsPubFromSecretSym).trans (by rfl_kernel)

theorem c2_x25519_resolve_diffieHellman_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsDiffieHellmanSym =
      x25519CliMultiLib.fnAddr c2X25519Mpl diffieHellmanSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsDiffieHellmanSym).trans (by rfl_kernel)

theorem c2_x25519_resolve_pubFromSecret_base18 {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsPubFromSecretSym = c2PubFromSecretAddr :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsPubFromSecretSym).trans (by rfl_kernel)

theorem c2_x25519_resolve_diffieHellman_base17 {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsDiffieHellmanSym = c2DiffieHellmanAddr :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsDiffieHellmanSym).trans (by rfl_kernel)

/-! ## RX Block-Walk and `CodeLoaded` Discharges (19 Blocks) -/

set_option maxRecDepth 2000000 in
private theorem c2_x25519_allBlocksWalk_ok :
    ((List.range x25519CliMultiLib.blocks.length).all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes
        (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
        x25519CliMultiLib c2X25519Mpl j) = true := by
  rfl_kernel

theorem c2_x25519_rx_blocks :
    ∀ i < x25519CliMultiLib.blocks.length,
      checkProgCodeSubslice f3TrialRxProg (x25519CliMultiLib.blockProgram c2X25519Mpl i) = true :=
  fun i hi =>
    checkProgCodeSubslice_of_multiBlockWalk rfl rfl rfl
      (List.all_eq_true.mp c2_x25519_allBlocksWalk_ok i (List.mem_range.mpr hi))

theorem c2_x25519_codeLoaded_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    x25519CliMultiLib.CodeLoaded c2X25519Mpl m :=
  fun i hi =>
    codeLoaded_of_multiBlockWalk hInv.rxCode rfl rfl rfl
      (List.all_eq_true.mp c2_x25519_allBlocksWalk_ok i (List.mem_range.mpr hi))

/-! ## `.rodata` Slices (3 Tables, Including 30,720-B Basepoint Table) -/

private noncomputable def checkX25519RoAll (elf : Process.ElfImage) : Bool :=
  match ProofLib.Placed.Split.rGetD (elf.segments.map some) f3StdLayout.roSegIdx none with
  | none => false
  | some seg =>
    let roLen := ProofLib.Placed.Split.rLen seg.bytes
    decide (seg.perm.rwx = Perm.ro) &&
    checkSegSlice seg roLen (fe51_one c2X25519Mpl) fe51OneBytes &&
    checkSegSlice seg roLen (fe51_mont_a24 c2X25519Mpl) fe51MontA24Bytes &&
    checkSegSlice seg roLen (ed25519_basepoint_table c2X25519Mpl) ed25519BasepointTableBytes

set_option maxRecDepth 4000000 in
private theorem c2_x25519_roSlices_ok : checkX25519RoAll f3PatchedElf = true := by
  rfl_kernel

private theorem c2_x25519_ro_triple :
    ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length (fe51_one c2X25519Mpl) fe51OneBytes = true ∧
      checkSegSlice seg seg.bytes.length (fe51_mont_a24 c2X25519Mpl) fe51MontA24Bytes = true ∧
      checkSegSlice seg seg.bytes.length
        (ed25519_basepoint_table c2X25519Mpl) ed25519BasepointTableBytes = true := by
  have h := c2_x25519_roSlices_ok
  unfold checkX25519RoAll at h
  rw [rGetD_map_some_eq_getElem?] at h
  cases hseg : f3PatchedElf.segments[f3StdLayout.roSegIdx]? with
  | none => rw [hseg] at h; cases h
  | some seg =>
    rw [hseg] at h
    dsimp only at h
    simp only [ProofLib.Placed.Split.rLen_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨hperm, h1⟩, h2⟩, h3⟩
    exact ⟨seg, rfl, hperm, h1, h2, h3⟩

theorem c2_x25519_ro_fe51_one :
    ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length (fe51_one c2X25519Mpl) fe51OneBytes = true := by
  obtain ⟨seg, hseg, hperm, h1, _, _⟩ := c2_x25519_ro_triple
  exact ⟨seg, hseg, hperm, h1⟩

theorem c2_x25519_ro_fe51_mont_a24 :
    ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length (fe51_mont_a24 c2X25519Mpl) fe51MontA24Bytes = true := by
  obtain ⟨seg, hseg, hperm, _, h2, _⟩ := c2_x25519_ro_triple
  exact ⟨seg, hseg, hperm, h2⟩

theorem c2_x25519_ro_ed25519_basepoint_table :
    ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length
        (ed25519_basepoint_table c2X25519Mpl) ed25519BasepointTableBytes = true := by
  obtain ⟨seg, hseg, hperm, _, _, h3⟩ := c2_x25519_ro_triple
  exact ⟨seg, hseg, hperm, h3⟩

theorem c2_x25519_roOk_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    X25519CliRoOk c2X25519Mpl m :=
  { ro_fe51_one := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ c2_x25519_ro_fe51_one
    ro_fe51_mont_a24 := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ c2_x25519_ro_fe51_mont_a24
    ro_ed25519_basepoint_table :=
      f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ c2_x25519_ro_ed25519_basepoint_table }

/-! ## `.text.lib2` Hull Inclusions & `LsRetAddr624` Guard -/

set_option maxRecDepth 400000 in
private theorem c2_x25519_blocks_in_lib2 :
    ((List.range x25519CliMultiLib.blocks.length).all fun j =>
      let b := (c2X25519Mpl.base j).toNat
      let len := (x25519CliMultiLib.blockLib j).text.code.length
      Nat.beq (len % 4) 0 &&
      Nat.ble 0x47ac2c b &&
      Nat.ble (b + len) 0x4cb070) = true := by
  rfl_kernel

theorem c2_x25519_pubFromSecret_keepLib2Text :
    keepLib2Text c2PubFromSecretAddr = true := by
  decide

theorem c2_x25519_pubFromSecret_rxRegion {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    keepTextBPre (libsignalSessionLib.resolve mpl lsPubFromSecretSym) = true ∨
      keepLib2Text (libsignalSessionLib.resolve mpl lsPubFromSecretSym) = true := by
  rw [c2_x25519_resolve_pubFromSecret_base18 hLs]
  exact Or.inr c2_x25519_pubFromSecret_keepLib2Text

theorem c2_x25519_diffieHellman_keepLib2Text :
    keepLib2Text c2DiffieHellmanAddr = true := by
  decide

theorem c2_x25519_keep_sub_keepLib2Text {pc : BitVec 64}
    (hk : x25519MultiKeep c2X25519Mpl pc = true) :
    keepLib2Text pc = true := by
  unfold x25519MultiKeep at hk
  rw [List.any_eq_true] at hk
  obtain ⟨j, hj_mem, hkp⟩ := hk
  have hbnd := List.all_eq_true.mp c2_x25519_blocks_in_lib2 j hj_mem
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hbnd
  rcases hbnd with ⟨⟨hal, hlo⟩, hhi⟩
  unfold progKeep at hkp
  rw [decide_eq_true_eq] at hkp
  have hplen : (x25519CliMultiLib.blockProgram c2X25519Mpl j).code.length =
      (x25519CliMultiLib.blockLib j).text.code.length :=
    CodeBlock.length_patched_of_aligned _ hal
  have hbase : (x25519CliMultiLib.blockProgram c2X25519Mpl j).base = c2X25519Mpl.base j := rfl
  rw [hbase, hplen] at hkp
  have hlo' : c2Lib2TextLo.toNat ≤ (c2X25519Mpl.base j).toNat :=
    Nat.le_trans (by decide : c2Lib2TextLo.toNat ≤ 0x47ac2c) hlo
  have hhi' : (c2X25519Mpl.base j).toNat + (x25519CliMultiLib.blockLib j).text.code.length ≤
      c2Lib2TextHi.toNat :=
    Nat.le_trans hhi (by decide : 0x4cb070 ≤ c2Lib2TextHi.toNat)
  exact c2_keepLib2Text_of_sub_lt hkp hlo' hhi'

theorem c2_x25519_keep_noPanic {pc : BitVec 64}
    (hk : x25519MultiKeep c2X25519Mpl pc = true) :
    isLinkedPanicAddr pc = false := by
  unfold x25519MultiKeep at hk
  rw [List.any_eq_true] at hk
  obtain ⟨j, hj_mem, hkp⟩ := hk
  have hbnd := List.all_eq_true.mp c2_x25519_blocks_in_lib2 j hj_mem
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hbnd
  rcases hbnd with ⟨⟨hal, hlo⟩, hhi⟩
  unfold progKeep at hkp
  rw [decide_eq_true_eq] at hkp
  have hplen : (x25519CliMultiLib.blockProgram c2X25519Mpl j).code.length =
      (x25519CliMultiLib.blockLib j).text.code.length :=
    CodeBlock.length_patched_of_aligned _ hal
  have hbase : (x25519CliMultiLib.blockProgram c2X25519Mpl j).base = c2X25519Mpl.base j := rfl
  rw [hbase, hplen] at hkp
  exact c2_noPanic_of_band_sub_lt hkp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hlo, hhi⟩)))))
    (Nat.lt_of_le_of_lt hhi (by decide))

theorem c2_x25519_keep_sub_rxRegion {pc : BitVec 64}
    (hk : x25519MultiKeep c2X25519Mpl pc = true) :
    keepTextBPre pc = true ∨ keepLib2Text pc = true :=
  Or.inr (c2_x25519_keep_sub_keepLib2Text hk)

theorem c2_x25519_keep_sub_rxProg {pc : BitVec 64}
    (hk : x25519MultiKeep c2X25519Mpl pc = true) :
    progKeep f3TrialRxProg pc = true :=
  keepLib2Text_sub_rxProg (c2_x25519_keep_sub_keepLib2Text hk)

theorem c2_x25519_keep_lr_false [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr624 lr) :
    x25519MultiKeep c2X25519Mpl lr = false := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hlr
  have hlo : c2FirstExternStubAddr.toNat ≤ c2Lib2TextLo.toNat := by decide
  cases hk : x25519MultiKeep c2X25519Mpl lr
  · rfl
  · have hlib2 := c2_x25519_keep_sub_keepLib2Text hk
    unfold keepLib2Text at hlib2
    rw [decide_eq_true_eq] at hlib2
    omega

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519
