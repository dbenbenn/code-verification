/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockEnc
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
import ProofLib.BV
import Arm64.Trusted.ISA.Eval
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Pure.CipherEquiv

/-!
# Permission-Preserving Step Rules, Bitvector Helpers & Encryption Wrappers (`CbcEnc.StepHelpers`)
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open CryptoGames.CBC
  (Block bytesToBlock blockToBytesLE bytesToBlock_blockToBytesLE blockToBytesLE_bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (Blocks4 aes256KeyScheduleFs aes256EncryptFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing (Blocks4.Wf)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (fsKeys256At blocks4Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockEnc
  (aes256EncryptSpec blocks4Bytes_aes256EncryptFs_single)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (bytesToU128LE armv8ExpandKey armv8Encrypt15 roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc
  (encrypt15InplaceSpec pointsTo128_eq_pointsToBytes u128ToBytesLE_bytesToU128LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Pure.CipherEquiv
  (u128ToBytesLE_armv8Encrypt15_bytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (bytesToBlock_xor_16)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs (length_blockToBytesLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
  (CbcPreserved spAligned_of_eq allocHookStack_split_208 byte16Cells16 byte16At
   pointsToBytes_16_eq_byte16At byte16At_eq_pointsTo128 inPad6Cells inPad6_zero_eq_pointsToBytes)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

/-! ## 1. Permission-Preserving `STP Wt`, `STR Qt`, `STP Qt` & `BL` Step Lemmas -/

theorem step_stp32_perm {prog : Program} {target_pc pc ea ea2 : BitVec 64}
    {v1 v2 : BitVec 32} {s s' : State} {P P1 P2 : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.stp .W32 rt1 rt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 4#64 = ea2)
    (hv1 : s.readReg32 rt1 = v1) (hv2 : s.readReg32 rt2 = v2)
    (hstore1 : SepStore32 ea v1 P P1) (hstore2 : SepStore32 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W32 rt1 rt2 addr) := hpc.symm ▸ hfetch
  have htrunc1 : (s.readReg64 rt1).truncate 32 = v1 := hv1
  have htrunc2 : (s.readReg64 rt2).truncate 32 = v2 := hv2
  let m1 := s.mem.write32 ea v1; let m2 := m1.write32 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 4 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 4 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write32 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W32 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      hea2, htrunc1, htrunc2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 ((Memory.perm_write32 m1 ea2 v2).trans (Memory.perm_write32 s.mem ea v1))) hm2

theorem step_strSimd128_64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : (s.readVReg128 vt).extractLsb' 0 64 = v1)
    (hv2 : (s.readVReg128 vt).extractLsb' 64 64 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.strSimd .Q128 vt addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  have hcan16 : s.mem.canWrite ea 16 = true := Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.strSimd .Q128 vt addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized,
      Memory.write128, applyWriteback, State.advancePC, State.setPC, State.setMem,
      State.writeReg64, hsp, haddr, hea2, hv1, hv2, hcan16, SimdMemSize.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2

theorem step_stpSimd128_64_perm {prog : Program}
    {target_pc pc ea ea2 ea3 ea4 v1 v2 v3 v4 : BitVec 64}
    {s s' : State} {P P1 P2 P3 P4 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt1 vt2 : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hea3 : ea + 16#64 = ea3) (hea4 : ea3 + 8#64 = ea4)
    (hv1 : (s.readVReg128 vt1).extractLsb' 0 64 = v1)
    (hv2 : (s.readVReg128 vt1).extractLsb' 64 64 = v2)
    (hv3 : (s.readVReg128 vt2).extractLsb' 0 64 = v3)
    (hv4 : (s.readVReg128 vt2).extractLsb' 64 64 = v4)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hstore3 : SepStore64 ea3 v3 P2 P3) (hstore4 : SepStore64 ea4 v4 P3 P4)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P4 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stpSimd .Q128 vt1 vt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  let m3 := m2.write64 ea3 v3; let m4 := m3.write64 ea4 v4
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hm3 : m3 ⊨ P3 ∗ R := hstore3.store hm2; have hm4 : m4 ⊨ P4 ∗ R := hstore4.store hm3
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  have hcan3 : m2.canWrite ea3 8 = true := hstore3.writable hm2
  have hcan4 : m3.canWrite ea4 8 = true := hstore4.writable hm3
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
      Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan3
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
      Memory.canWrite_congr (Memory.perm_write64 _ _ _),
      Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan4
  have hcan_lo : s.mem.canWrite ea 16 = true := Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  have hcan_hi : s.mem.canWrite ea3 16 = true := Memory.canWrite_16_of_8_8 hcan3 (hea4.symm ▸ hcan4)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stpSimd .Q128 vt1 vt2 addr) s = s'.setMem m4 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized,
      Memory.write128, applyWriteback, State.advancePC, State.setPC, State.setMem,
      State.writeReg64, hsp, haddr, hea2, hea3, hea4, hv1, hv2, hv3, hv4,
      hcan_lo, hcan_hi, SimdMemSize.bytes, hpc, m1, m2, m3, m4]
  rw [hstep]
  have hp4 : m4.perm = s.mem.perm :=
    (Memory.perm_write64 m3 ea4 v4).trans
      ((Memory.perm_write64 m2 ea3 v3).trans
        ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1)))
  exact SepWP.to_reaches_pc (hnext m4 hp4) hm4

theorem step_bl_cbc {α : Type} {P : Program} {pc_bl calleeAddr target_pc : BitVec 64}
    {spec : Spec α} (hf : P.fetch pc_bl = some (.bl (calleeAddr - pc_bl)))
    (hcall : subroutine_ok P calleeAddr spec) (x : α)
    {s : State} {Pre F PreSpatial PostSpatial : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hent : Pre ⊢ PreSpatial ∗ F)
    (hpre_call : ∀ s_call, s_call = P.evalInst (.bl (calleeAddr - pc_bl)) (s.setPC pc_bl) →
      PreSpatial ⊢ spec.pre x s_call)
    (hpost_call : ∀ s_call sf, s_call = P.evalInst (.bl (calleeAddr - pc_bl)) (s.setPC pc_bl) →
      sf.sp = s.sp → spec.post x s_call sf ⊢ ⌜CbcPreserved s_call sf⌝ ∗ PostSpatial)
    (hno_panic : ∀ s_call sf, spec.onPanic x s_call sf = ⌜False⌝ := by intros; rfl)
    (hno_exit : ∀ c s_call sf, spec.onExit x c s_call sf = ⌜False⌝ := by intros; rfl)
    (hno_oom : ∀ s_call sf, spec.onOom x s_call sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State, sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → CbcPreserved s sf →
      SepWP P target_pc sf (PostSpatial ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  let s_call := P.evalInst (.bl (calleeAddr - pc_bl)) (s.setPC pc_bl)
  have hmem_sc : s_call.mem = s.mem := by
    simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  have hpc_sc : s_call.pc = calleeAddr := by
    simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]; bv_omega
  have hrun_sc : s_call.status = .Running := by
    simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hrun]
  have hsp_sc_eq : s_call.sp = s.sp := by
    simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  have hsp_sc : s_call.spAligned = true := by simp only [State.spAligned, hsp_sc_eq]; exact hsp_al
  have hlr_sc : s_call.readReg64 Reg.lr = pc_bl + 4#64 := by
    simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  have hp_sc : CbcPreserved s s_call := CbcPreserved.of_proj_perm
    (by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]) (by simp [hmem_sc])
  have hcs_sc : CalleeSavedPreserved s s_call := by
    rw [CalleeSavedPreserved.iff_regs]
    simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  apply SepWP.step_pure hpc hrun hf rfl hmem_sc
  refine SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc_sc hrun_sc hsp_sc hlr_sc
    ?_ ?_ ?_ ?_ ?_
  · intro R hm
    have hent_all := Entails.trans hent (sepConj_mono_left (hpre_call s_call rfl))
    exact Satisfies.mono (by rw [← sepConj_assoc]; exact sepConj_mono_left hent_all) hm
  · intro R' sf _; rw [hno_panic]; exact not_satisfies_false_sepConj
  · intro R' c sf _; rw [hno_exit]; exact not_satisfies_false_sepConj
  · intro sf hpc_f hrun_f hsp_f hcs_f
    have hsp_f' : sf.sp = s.sp := hsp_f.trans hsp_sc_eq
    refine SepWP.weaken_pre (sepConj_mono_left (hpost_call s_call sf rfl hsp_f')) ?_
    rw [sepConj_assoc]; apply SepWP.pure_elim; intro hp_f
    exact hnext sf hpc_f hrun_f hsp_f' (hcs_sc.trans hcs_f) (hp_sc.trans hp_f)
  · intro R' sf _ ho; rw [hno_oom] at ho; exact (not_satisfies_false_sepConj ho).elim

/-! ## 2. Bitvector, XOR-Block & Single-Block Encryption Call Wrappers -/

theorem u_eq_ofNat_of_lt40 {u : BitVec 64} {n : Nat}
    (hu : u.toNat = n) (_hn : n < 2 ^ 40) : u = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; rw [hu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem u_lsr40_zero {n : Nat} (hn : n < 2 ^ 40) :
    (BitVec.ofNat 64 n) >>> 40 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), Nat.shiftRight_eq_div_pow]; omega

theorem u_lsr4_eq {n : Nat} (hn : n < 2 ^ 40) :
    (BitVec.ofNat 64 n) >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem u_and15_eq {n : Nat} (hn : n < 2 ^ 40) :
    (BitVec.ofNat 64 n) &&& 15#64 = BitVec.ofNat 64 (n % 16) := by
  have hn64 : n < 2 ^ 64 := by omega
  have hr64 : n % 16 < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hr64,
    show (15 : Nat) % 2 ^ 64 = 15 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod n 4

theorem fullLen_and_eq {n : Nat} (hn : n < 2 ^ 40) :
    (BitVec.ofNat 64 n) &&& 0x7ffffffffffffff0#64 = BitVec.ofNat 64 (16 * (n / 16)) := by
  have h40 := u_lsr40_zero hn
  have hsh : ((BitVec.ofNat 64 n) >>> 4) <<< 4 = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [u_lsr4_eq hn]
    have hq64 : n / 16 < 2 ^ 64 := by omega
    have h16q : (n / 16) * 2 ^ 4 < 2 ^ 64 := by omega
    have hrhs : 16 * (n / 16) < 2 ^ 64 := by omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq64,
        Nat.shiftLeft_eq, Nat.mod_eq_of_lt h16q, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrhs]; omega
  rw [← hsh]; generalize BitVec.ofNat 64 n = u at h40 ⊢; revert h40; bv_bits

theorem ctLen_adds_eq {n : Nat} (hn : n < 2 ^ 40) :
    BitVec.ofNat 64 (16 * (n / 16)) + 16#64 = BitVec.ofNat 64 ((n / 16 + 1) * 16) := by
  have h1 : 16 * (n / 16) < 2 ^ 64 := by omega
  have h2 : 16 * (n / 16) + 16 < 2 ^ 64 := by omega
  have h3 : (n / 16 + 1) * 16 < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3, show (16 : Nat) % 2 ^ 64 = 16 from rfl]; omega

theorem zext32_zext64_eq (a : BitVec 8) : (a.zeroExtend 32).zeroExtend 64 = a.zeroExtend 64 := by bv_bits
theorem trunc32_zext64_eq (a : BitVec 8) : (a.zeroExtend 64).truncate 32 = a.zeroExtend 32 := by bv_bits
theorem xor_zext_byte (a b : BitVec 8) :
    ((((a.zeroExtend 64).truncate 32 ^^^ (b.zeroExtend 64).truncate 32).zeroExtend 64).truncate 8) =
      a ^^^ b := by bv_bits
theorem extractLsb_append64_lo (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
theorem extractLsb_append64_hi (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

private theorem list_getD_16_eq {l : List (BitVec 8)} (hl : l.length = 16) :
    [l.getD 0 0#8, l.getD 1 0#8, l.getD 2 0#8, l.getD 3 0#8,
     l.getD 4 0#8, l.getD 5 0#8, l.getD 6 0#8, l.getD 7 0#8,
     l.getD 8 0#8, l.getD 9 0#8, l.getD 10 0#8, l.getD 11 0#8,
     l.getD 12 0#8, l.getD 13 0#8, l.getD 14 0#8, l.getD 15 0#8] = l := by
  rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_,
    _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp_all

theorem byte16Cells16_xor_eq (p : BitVec 64) {bs : List (BitVec 8)}
    (hbs : bs.length = 16) (prev : Block) :
    let ps := blockToBytesLE prev
    byte16Cells16 p
      (bs.getD 0 0#8 ^^^ ps.getD 0 0#8) (bs.getD 1 0#8 ^^^ ps.getD 1 0#8)
      (bs.getD 2 0#8 ^^^ ps.getD 2 0#8) (bs.getD 3 0#8 ^^^ ps.getD 3 0#8)
      (bs.getD 4 0#8 ^^^ ps.getD 4 0#8) (bs.getD 5 0#8 ^^^ ps.getD 5 0#8)
      (bs.getD 6 0#8 ^^^ ps.getD 6 0#8) (bs.getD 7 0#8 ^^^ ps.getD 7 0#8)
      (bs.getD 8 0#8 ^^^ ps.getD 8 0#8) (bs.getD 9 0#8 ^^^ ps.getD 9 0#8)
      (bs.getD 10 0#8 ^^^ ps.getD 10 0#8) (bs.getD 11 0#8 ^^^ ps.getD 11 0#8)
      (bs.getD 12 0#8 ^^^ ps.getD 12 0#8) (bs.getD 13 0#8 ^^^ ps.getD 13 0#8)
      (bs.getD 14 0#8 ^^^ ps.getD 14 0#8) (bs.getD 15 0#8 ^^^ ps.getD 15 0#8) =
    byte16At p (blockToBytesLE (bytesToBlock bs ^^^ prev)) := by
  intro ps
  let zs : List (BitVec 8) :=
    [bs.getD 0 0#8 ^^^ ps.getD 0 0#8, bs.getD 1 0#8 ^^^ ps.getD 1 0#8,
     bs.getD 2 0#8 ^^^ ps.getD 2 0#8, bs.getD 3 0#8 ^^^ ps.getD 3 0#8,
     bs.getD 4 0#8 ^^^ ps.getD 4 0#8, bs.getD 5 0#8 ^^^ ps.getD 5 0#8,
     bs.getD 6 0#8 ^^^ ps.getD 6 0#8, bs.getD 7 0#8 ^^^ ps.getD 7 0#8,
     bs.getD 8 0#8 ^^^ ps.getD 8 0#8, bs.getD 9 0#8 ^^^ ps.getD 9 0#8,
     bs.getD 10 0#8 ^^^ ps.getD 10 0#8, bs.getD 11 0#8 ^^^ ps.getD 11 0#8,
     bs.getD 12 0#8 ^^^ ps.getD 12 0#8, bs.getD 13 0#8 ^^^ ps.getD 13 0#8,
     bs.getD 14 0#8 ^^^ ps.getD 14 0#8, bs.getD 15 0#8 ^^^ ps.getD 15 0#8]
  have hblk : bytesToBlock zs = bytesToBlock bs ^^^ prev := by
    dsimp only [zs]
    rw [bytesToBlock_xor_16, list_getD_16_eq hbs, list_getD_16_eq (length_blockToBytesLE prev),
        bytesToBlock_blockToBytesLE]
  have hle : blockToBytesLE (bytesToBlock bs ^^^ prev) = zs := by
    rw [← hblk, blockToBytesLE_bytesToBlock zs rfl]
  rw [hle]; rfl

theorem byte16Cells16_xor_comm_eq (p : BitVec 64) {bs : List (BitVec 8)}
    (hbs : bs.length = 16) (prev : Block) :
    let ps := blockToBytesLE prev
    byte16Cells16 p
      (ps.getD 0 0#8 ^^^ bs.getD 0 0#8) (ps.getD 1 0#8 ^^^ bs.getD 1 0#8)
      (ps.getD 2 0#8 ^^^ bs.getD 2 0#8) (ps.getD 3 0#8 ^^^ bs.getD 3 0#8)
      (ps.getD 4 0#8 ^^^ bs.getD 4 0#8) (ps.getD 5 0#8 ^^^ bs.getD 5 0#8)
      (ps.getD 6 0#8 ^^^ bs.getD 6 0#8) (ps.getD 7 0#8 ^^^ bs.getD 7 0#8)
      (ps.getD 8 0#8 ^^^ bs.getD 8 0#8) (ps.getD 9 0#8 ^^^ bs.getD 9 0#8)
      (ps.getD 10 0#8 ^^^ bs.getD 10 0#8) (ps.getD 11 0#8 ^^^ bs.getD 11 0#8)
      (ps.getD 12 0#8 ^^^ bs.getD 12 0#8) (ps.getD 13 0#8 ^^^ bs.getD 13 0#8)
      (ps.getD 14 0#8 ^^^ bs.getD 14 0#8) (ps.getD 15 0#8 ^^^ bs.getD 15 0#8) =
    byte16At p (blockToBytesLE (bytesToBlock bs ^^^ prev)) := by
  intro ps; simp only [BitVec.xor_comm (ps.getD _ 0#8)]; exact byte16Cells16_xor_eq p hbs prev

theorem call_hw_encrypt_single {P : Program}
    {pc_bl hwEncryptAddr target_pc sp : BitVec 64}
    {key : List (BitVec 8)} (hkey : key.length = 32) (b0 : Block)
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc_bl = some (.bl (hwEncryptAddr - pc_bl)))
    (hHwEnc : subroutine_ok P hwEncryptAddr encrypt15InplaceSpec)
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 (.gpr 0#5) = sp + 0xc90#64)
    (hx1 : s.readReg64 (.gpr 1#5) = sp + 0x7d0#64)
    (hx2 : s.readReg64 (.gpr 2#5) = sp + 0x7d0#64)
    (hnext : ∀ sf : State, sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = sp →
      CalleeSavedPreserved s sf → CbcPreserved s sf →
      SepWP P target_pc sf
        ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey key) ∗
          ((sp + 0x7d0#64) ↦₁₂₈
            bytesToU128LE (blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b0)))) ∗ F)
        post oom) :
    SepWP P target_pc s
      ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey key) ∗
        byte16At (sp + 0x7d0#64) (blockToBytesLE b0)) ∗ F) post oom := by
  let blk := bytesToU128LE (blockToBytesLE b0)
  have hout_eq :
      ((sp + 0x7d0#64) ↦₁₂₈ armv8Encrypt15 (armv8ExpandKey key) blk) =
        ((sp + 0x7d0#64) ↦₁₂₈
          bytesToU128LE (blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b0))) := by
    rw [pointsTo128_eq_pointsToBytes, pointsTo128_eq_pointsToBytes,
        u128ToBytesLE_armv8Encrypt15_bytes hkey (length_blockToBytesLE b0),
        bytesToBlock_blockToBytesLE, u128ToBytesLE_bytesToU128LE (length_blockToBytesLE _)]
  refine step_bl_cbc hf hHwEnc
    (sp + 0xc90#64, sp + 0x7d0#64, armv8ExpandKey key, blk)
    hpc hrun (spAligned_of_eq hsp hsp_al) (F := F)
    (PreSpatial := roundKeys15At (sp + 0xc90#64) (armv8ExpandKey key) ∗ ((sp + 0x7d0#64) ↦₁₂₈ blk))
    (PostSpatial := roundKeys15At (sp + 0xc90#64) (armv8ExpandKey key) ∗
      ((sp + 0x7d0#64) ↦₁₂₈
        bytesToU128LE (blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b0))))
    ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
  · rw [byte16At_eq_pointsTo128 (sp + 0x7d0#64) (length_blockToBytesLE b0)]; exact Entails.refl _
  · intro s_call hsc; dsimp only [encrypt15InplaceSpec]
    have hx0c : s_call.readReg64 .x0 = sp + 0xc90#64 := by
      rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx0
    have hx1c : s_call.readReg64 .x1 = sp + 0x7d0#64 := by
      rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx1
    have hx2c : s_call.readReg64 .x2 = sp + 0x7d0#64 := by
      rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx2
    exact Entails.pure_right ⟨hx0c, hx1c, hx2c⟩ (Entails.refl _)
  · intro _ _ _ _; dsimp only [encrypt15InplaceSpec]
    refine Entails.pure_left fun ⟨hp, _⟩ => ?_
    rw [hout_eq]; exact Entails.pure_right (CbcPreserved.of_pure hp) (Entails.refl _)
  · intro sf hpc_f hrun_f hsp_f hcs_f hp_f
    exact hnext sf hpc_f hrun_f (hsp_f.trans hsp) hcs_f hp_f

theorem call_aes256_encrypt_single {P : Program}
    {pc_bl encryptAddr target_pc sp : BitVec 64}
    {key : List (BitVec 8)} (hkey : key.length = 32) (b0 : Block)
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc_bl = some (.bl (encryptAddr - pc_bl)))
    (hEnc : subroutine_ok P encryptAddr aes256EncryptSpec)
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 (.gpr 0#5) = sp + 0xc90#64)
    (hx1 : s.readReg64 (.gpr 1#5) = sp + 0x106c#64)
    (hx8 : s.readReg64 (.gpr 8#5) = sp + 0x7d0#64)
    (hnext : ∀ sf : State, sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = sp →
      CalleeSavedPreserved s sf → CbcPreserved s sf →
      SepWP P target_pc sf
        ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs key) ∗
          byte16At (sp + 0x106c#64) (blockToBytesLE b0) ∗
          inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64 ∗
          byte16At (sp + 0x7d0#64)
            (blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b0)) ∗
          memRegion (sp + 0x7e0#64) 48 ∗ stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s
      ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs key) ∗
        byte16At (sp + 0x106c#64) (blockToBytesLE b0) ∗
        inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64 ∗
        memRegion (sp + 0x7d0#64) 64 ∗ stackAt sp allocHookStack) ∗ F) post oom := by
  let z16 : List (BitVec 8) := List.replicate 16 0#8
  let bs : Blocks4 := ⟨blockToBytesLE b0, z16, z16, z16⟩
  have hwf : Blocks4.Wf bs := ⟨length_blockToBytesLE b0, rfl, rfl, rfl⟩
  have hin_eq : bytesAt false (sp + 0x106c#64) (blocks4Bytes bs) =
      byte16At (sp + 0x106c#64) (blockToBytesLE b0) ∗
        inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64 := by
    simp only [bytesAt, Bool.false_eq_true, ↓reduceIte]; dsimp only [blocks4Bytes, bs, z16]
    rw [List.append_assoc, List.append_assoc,
        pointsToBytes_append (sp + 0x106c#64) (blockToBytesLE b0), length_blockToBytesLE,
        pointsToBytes_16_eq_byte16At (sp + 0x106c#64) (length_blockToBytesLE b0),
        ← List.append_assoc, show BitVec.ofNat 64 16 = 16#64 from rfl,
        ← inPad6_zero_eq_pointsToBytes (sp + 0x106c#64)]
  refine step_bl_cbc hf hEnc
    (false, sp + 0x7d0#64, sp + 0xc90#64, sp + 0x106c#64, aes256KeyScheduleFs key, bs)
    hpc hrun (spAligned_of_eq hsp hsp_al) (F := stackFrameAt (sp - 208#64) 3888 ∗ F)
    (PreSpatial := fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs key) ∗
      bytesAt false (sp + 0x106c#64) (blocks4Bytes bs) ∗ memRegion (sp + 0x7d0#64) 64 ∗ stackFrameAt sp 208)
    (PostSpatial := fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs key) ∗
      byte16At (sp + 0x106c#64) (blockToBytesLE b0) ∗
      inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64 ∗
      byte16At (sp + 0x7d0#64) (blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b0)) ∗
      memRegion (sp + 0x7e0#64) 48 ∗ stackFrameAt sp 208)
    ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
  · rw [hin_eq, allocHookStack_split_208 sp]; exact Entails.of_eq (by sep_ac_rfl)
  · intro s_call hsc; dsimp only [aes256EncryptSpec]
    have hx0c : s_call.readReg64 .x0 = sp + 0xc90#64 := by
      rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx0
    have hx1c : s_call.readReg64 .x1 = sp + 0x106c#64 := by
      rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx1
    have hx8c : s_call.readReg64 .x8 = sp + 0x7d0#64 := by
      rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx8
    have hspc : s_call.sp = sp := by
      rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hsp
    rw [hspc]; exact Entails.pure_right ⟨hx0c, hx1c, hx8c, hwf⟩ (Entails.refl _)
  · intro s_call sf hsc _; dsimp only [aes256EncryptSpec]
    have hspc : s_call.sp = sp := by
      rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hsp
    rw [hspc]
    refine Entails.pure_left fun hp => Entails.pure_right (CbcPreserved.of_pure hp) ?_
    rcases blocks4Bytes_aes256EncryptFs_single hkey b0 (b1 := z16) (b2 := z16) (b3 := z16) rfl rfl rfl
      with ⟨htake, hdrop⟩
    have hsplit : ((sp + 0x7d0#64) ↦ₛ blocks4Bytes (aes256EncryptFs (aes256KeyScheduleFs key) bs)) ⊢
        byte16At (sp + 0x7d0#64) (blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b0)) ∗
          memRegion (sp + 0x7e0#64) 48 := by
      let outBs := blocks4Bytes (aes256EncryptFs (aes256KeyScheduleFs key) bs)
      change ((sp + 0x7d0#64) ↦ₛ outBs) ⊢ _
      have hsp_bs : outBs = outBs.take 16 ++ outBs.drop 16 := (List.take_append_drop 16 outBs).symm
      have hlen16 : (outBs.take 16).length = 16 := by
        change ((blocks4Bytes (aes256EncryptFs (aes256KeyScheduleFs key) bs)).take 16).length = 16
        rw [htake, length_blockToBytesLE]
      conv => lhs; rw [hsp_bs]
      rw [pointsToBytes_append, hlen16, show (sp + 0x7d0#64) + BitVec.ofNat 64 16 = sp + 0x7e0#64 by bv_omega,
          show outBs.take 16 = blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b0) from htake,
          pointsToBytes_16_eq_byte16At (sp + 0x7d0#64) (length_blockToBytesLE _)]
      refine sepConj_mono_right ?_
      have hlen48 : (outBs.drop 16).length = 48 := hdrop
      rw [← hlen48]; exact pointsToBytes_entails_memRegion _ _
    rw [hin_eq]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsplit))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hpc_f hrun_f hsp_f hcs_f hp_f
    refine SepWP.weaken_pre ?_ (hnext sf hpc_f hrun_f (hsp_f.trans hsp) hcs_f hp_f)
    rw [allocHookStack_split_208 sp]; exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers
