/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib

/-!
# Additional NEON / AdvSIMD `SepWP` Memory Step Lemmas (`SimdSteps`)

`SepWP` step lemmas for the 7 AdvSIMD memory-access shapes emitted by `rustc 1.98.1`
(`aarch64-unknown-linux-musl`) across `libcrux-ml-kem` `0.0.10` and `libcrux-sha3` `0.0.10`
beyond `ProofLib.SepLogic.WP.StepsSimd`:

1. `step_strSimd8`: `STR Bt, [addr]` (`strSimd .B8`, 12 sites in `serialize_1`).
2. `step_strSimd16`: `STR Ht, [addr]` (`strSimd .H16`, 48 sites in `serialize_10`).
3. `step_simdLd1Single32`: `LD1 {Vt.S}[lane], [Xn]` (`simdLdSt1Single`, `opcode = 0x4#3`, `size = 0x0#2`, 14 sites in `deserialize_10`).
4. `step_simdLd1Single64`: `LD1 {Vt.D}[lane], [Xn]` (`simdLdSt1Single`, `opcode = 0x4#3`, `sBit = false`, `size = 0x1#2`, 31 sites in `load_block`).
5. `step_simdLd2_2d`: `LD2 {Vt.2D, Vt+1.2D}, [Xn]` (`simdLdStMulti true true 0x3#2 2`, 9 sites in `squeeze2`).
6. `step_simdLd1r_2d`: `LD1R {Vt.2D}, [Xn]` (`simdLd1r true 0x3#2`, 72 sites in `keccak2` round constants).
7. `step_simdLd1r_4h`: `LD1R {Vt.4H}, [Xn]` (`simdLd1r false 0x1#2`, 672 sites in NTT/INTT `ZETA_TABLE` loads).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps

open Arm64 ProofLib

/-! ## 1. `STR Bt, [addr]` (`strSimd .B8`) and `STR Ht, [addr]` (`strSimd .H16`) -/

/-- 8-bit SIMD scalar store (`STR Bt, [addr]`) via `SepStore8`. -/
theorem step_strSimd8 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .B8 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readVReg128 vt).truncate 8 = val)
    (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.strSimd .B8 vt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write8 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 1 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.strSimd .B8 vt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      SimdMemSize.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

/-- 16-bit SIMD scalar store (`STR Ht, [addr]`) via `SepStore16`. -/
theorem step_strSimd16 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 16}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .H16 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readVReg128 vt).truncate 16 = val)
    (hstore : SepStore16 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.strSimd .H16 vt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write16 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 2 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.strSimd .H16 vt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      SimdMemSize.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

/-! ## 2. `LD1 {Vt.S}[lane], [Xn]` and `LD1 {Vt.D}[lane], [Xn]` (`simdLdSt1Single`) -/

/-- 32-bit single-lane load (`LD1 {Vt.S}[lane], [Xn]`, `opcode = 0x4#3`, `size = 0x0#2`,
    `postIdx = false`) via `SepLoad32`. -/
theorem step_simdLd1Single32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {q sBit : Bool} {rm : BitVec 5} {rn : Reg} {vt : BitVec 5}
    {ea : BitVec 64} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.simdLdSt1Single true q false rm 0x4#3 sBit 0x0#2 rn vt))
    (hsp : checkRegSPAligned s rn = true)
    (hea : s.readReg64 rn = ea)
    (hload : SepLoad32 ea P v)
    (hexec : (s.writeVReg128 vt (setSimdLane (s.readVReg128 vt) 32
      (simdLdSt1SingleLaneIdx q 0x4#3 sBit 0x0#2) (v.zeroExtend 128))).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc =
      some (.simdLdSt1Single true q false rm 0x4#3 sBit 0x0#2 rn vt) := hpc.symm ▸ hfetch
  have hread : s.mem.read32 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 4 = true := hload.readable hm
  have hvalid : validSimdLdSt1Single 0x4#3 sBit 0x0#2 = true := by
    cases sBit <;> decide
  have hzext : ((v.zeroExtend 64 : BitVec 64).zeroExtend 128 : BitVec 128) = v.zeroExtend 128 := by
    bv_bits
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.simdLdSt1Single true q false rm 0x4#3 sBit 0x0#2 rn vt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, hvalid, hsp, hea, hcan, hread, hzext,
      Memory.readSized, MemWidth.bytes, State.advancePC, State.setPC, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; rfl
  apply hnext R
  rwa [hmem]

/-- 64-bit single-lane load (`LD1 {Vt.D}[lane], [Xn]`, `opcode = 0x4#3`, `sBit = false`,
    `size = 0x1#2`, `postIdx = false`) via `SepLoad64`. -/
theorem step_simdLd1Single64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {q : Bool} {rm : BitVec 5} {rn : Reg} {vt : BitVec 5}
    {ea : BitVec 64} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.simdLdSt1Single true q false rm 0x4#3 false 0x1#2 rn vt))
    (hsp : checkRegSPAligned s rn = true)
    (hea : s.readReg64 rn = ea)
    (hload : SepLoad64 ea P v)
    (hexec : (s.writeVReg128 vt (setSimdLane (s.readVReg128 vt) 64
      (simdLdSt1SingleLaneIdx q 0x4#3 false 0x1#2) (v.zeroExtend 128))).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc =
      some (.simdLdSt1Single true q false rm 0x4#3 false 0x1#2 rn vt) := hpc.symm ▸ hfetch
  have hread : s.mem.read64 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 8 = true := hload.readable hm
  have hvalid : validSimdLdSt1Single 0x4#3 false 0x1#2 = true := by decide
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.simdLdSt1Single true q false rm 0x4#3 false 0x1#2 rn vt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, hvalid, hsp, hea, hcan, hread,
      Memory.readSized, MemWidth.bytes, State.advancePC, State.setPC, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; rfl
  apply hnext R
  rwa [hmem]

/-! ## 3. `LD2 {Vt.2D, Vt+1.2D}, [Xn]` (`simdLdStMulti true true 0x3#2 2`) -/

private theorem canRead_32_of_16_16 {m : Memory} {a : BitVec 64}
    (h1 : m.canRead a 16 = true) (h2 : m.canRead (a + 16#64) 16 = true) :
    m.canRead a 32 = true := by
  simp only [Memory.canRead, Bool.and_eq_true] at h1 h2 ⊢
  refine ⟨?_, ?_⟩
  · rw [show (32 : Nat) = 16 + 16 from rfl, Memory.allPerm_add]
    exact Bool.and_eq_true_iff.mpr ⟨h1.1, h2.1⟩
  · rw [show (32 : Nat) = 16 + 16 from rfl, Memory.allNoLazyFree_add]
    exact Bool.and_eq_true_iff.mpr ⟨h1.2, h2.2⟩

/-- 2-structure deinterleaving 64-bit load (`LD2 {Vt.2D, Vt+1.2D}, [Xn]`, `postIdx = false`)
    via four `SepLoad64` reads (`ea`, `ea + 8`, `ea + 16`, `ea + 24`):
    sets `Vt := v3 ++ v1` (even 64-bit elements) and `Vt+1 := v4 ++ v2` (odd 64-bit elements). -/
theorem step_simdLd2_2d {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rn : Reg} {rm vt : BitVec 5}
    {ea ea8 ea16 ea24 : BitVec 64} {v1 v2 v3 v4 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.simdLdStMulti true true 0x3#2 2 rn false rm vt))
    (hsp : checkRegSPAligned s rn = true)
    (hea : s.readReg64 rn = ea)
    (hea8 : ea + 8#64 = ea8)
    (hea16 : ea + 16#64 = ea16)
    (hea24 : ea16 + 8#64 = ea24)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea8 P v2)
    (hload3 : SepLoad64 ea16 P v3)
    (hload4 : SepLoad64 ea24 P v4)
    (hexec : ((s.writeVReg128 vt
        (simdDeinterleaveReg true 0x3#2 2 0 (v2 ++ v1) (v4 ++ v3) 0#128 0#128)).writeVReg128
        (vt + 1#5)
        (simdDeinterleaveReg true 0x3#2 2 1 (v2 ++ v1) (v4 ++ v3) 0#128 0#128)).setPC
        (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc =
      some (.simdLdStMulti true true 0x3#2 2 rn false rm vt) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read64 ea = v1 := hload1.load hm
  have hread2 : s.mem.read64 ea8 = v2 := hload2.load hm
  have hread3 : s.mem.read64 ea16 = v3 := hload3.load hm
  have hread4 : s.mem.read64 ea24 = v4 := hload4.load hm
  have hcan0 : s.mem.canRead ea 16 = true :=
    Memory.canRead_16_of_8_8 (hload1.readable hm) (hea8.symm ▸ hload2.readable hm)
  have hcan16 : s.mem.canRead ea16 16 = true :=
    Memory.canRead_16_of_8_8 (hload3.readable hm) (hea24.symm ▸ hload4.readable hm)
  have hcan32 : s.mem.canRead ea 32 = true :=
    canRead_32_of_16_16 hcan0 (hea16.symm ▸ hcan16)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.simdLdStMulti true true 0x3#2 2 rn false rm vt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, SimdMemSize.ofQ, SimdMemSize.bytes,
      Memory.readSimdSized, Memory.read128, hsp, hea, hea8, hea16, hea24,
      hread1, hread2, hread3, hread4, hcan32, State.advancePC, State.setPC, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; rfl
  apply hnext R
  rwa [hmem]

/-- Algebraic simplification of `simdDeinterleaveReg true 0x3#2 2 0 (v2 ++ v1) (v4 ++ v3) 0 0 = v3 ++ v1`. -/
@[simp, arm64_norm, wp_norm]
theorem simdDeinterleaveReg_2d_0 (v1 v2 v3 v4 : BitVec 64) :
    simdDeinterleaveReg true 0x3#2 2 0 (v2 ++ v1) (v4 ++ v3) 0#128 0#128 = v3 ++ v1 := by
  change (0#128 ||| (((v2 ++ v1) >>> 0 &&& (1#128 <<< 64 - 1#128)) <<< 0)) |||
      (((v4 ++ v3) >>> 0 &&& (1#128 <<< 64 - 1#128)) <<< 64) = v3 ++ v1
  bv_bits

/-- Algebraic simplification of `simdDeinterleaveReg true 0x3#2 2 1 (v2 ++ v1) (v4 ++ v3) 0 0 = v4 ++ v2`. -/
@[simp, arm64_norm, wp_norm]
theorem simdDeinterleaveReg_2d_1 (v1 v2 v3 v4 : BitVec 64) :
    simdDeinterleaveReg true 0x3#2 2 1 (v2 ++ v1) (v4 ++ v3) 0#128 0#128 = v4 ++ v2 := by
  change (0#128 ||| (((v2 ++ v1) >>> 64 &&& (1#128 <<< 64 - 1#128)) <<< 0)) |||
      (((v4 ++ v3) >>> 64 &&& (1#128 <<< 64 - 1#128)) <<< 64) = v4 ++ v2
  bv_bits

/-! ## 4. `LD1R {Vt.2D}, [Xn]` and `LD1R {Vt.4H}, [Xn]` (`simdLd1r`) -/

/-- 64-bit broadcast load (`LD1R {Vt.2D}, [Xn]`, `q = true`, `size = 0x3#2`, `postIdx = false`)
    via `SepLoad64`. -/
theorem step_simdLd1r_2d {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rn : Reg} {rm vt : BitVec 5}
    {ea : BitVec 64} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.simdLd1r true 0x3#2 rn false rm vt))
    (hsp : checkRegSPAligned s rn = true)
    (hea : s.readReg64 rn = ea)
    (hload : SepLoad64 ea P v)
    (hexec : (s.writeVReg128 vt (v ++ v)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc =
      some (.simdLd1r true 0x3#2 rn false rm vt) := hpc.symm ▸ hfetch
  have hread : s.mem.read64 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 8 = true := hload.readable hm
  have hrep : mapLanes 64 0#128 (fun _ => (v.zeroExtend 128 : BitVec 128)) 2 = v ++ v := by
    simp only [mapLanes, laneMask_64]
    bv_bits
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.simdLd1r true 0x3#2 rn false rm vt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, MemWidth.ofBits, MemWidth.bytes, Memory.readSized,
      hsp, hea, hcan, hread, hrep, State.advancePC, State.setPC, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; rfl
  apply hnext R
  rwa [hmem]

/-- 16-bit 4-lane broadcast load (`LD1R {Vt.4H}, [Xn]`, `q = false`, `size = 0x1#2`,
    `postIdx = false`) via `SepLoad16`: sets low 64 bits to `v ++ v ++ v ++ v` and zeros high 64 bits. -/
theorem step_simdLd1r_4h {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rn : Reg} {rm vt : BitVec 5}
    {ea : BitVec 64} {v : BitVec 16}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.simdLd1r false 0x1#2 rn false rm vt))
    (hsp : checkRegSPAligned s rn = true)
    (hea : s.readReg64 rn = ea)
    (hload : SepLoad16 ea P v)
    (hexec : (s.writeVReg128 vt ((v ++ v ++ v ++ v).zeroExtend 128)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc =
      some (.simdLd1r false 0x1#2 rn false rm vt) := hpc.symm ▸ hfetch
  have hread : s.mem.read16 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 2 = true := hload.readable hm
  have hzext : ((v.zeroExtend 64 : BitVec 64).zeroExtend 128 : BitVec 128) = v.zeroExtend 128 := by
    bv_bits
  have hrep : mapLanes 16 0#128 (fun _ => (v.zeroExtend 128 : BitVec 128)) 4 =
      (v ++ v ++ v ++ v).zeroExtend 128 := by
    simp only [mapLanes, laneMask_16]
    bv_bits
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.simdLd1r false 0x1#2 rn false rm vt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, MemWidth.ofBits, MemWidth.bytes, Memory.readSized,
      hsp, hea, hcan, hread, hzext, hrep, State.advancePC, State.setPC, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; rfl
  apply hnext R
  rwa [hmem]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
