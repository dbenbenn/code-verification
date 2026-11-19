/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import ProofLib.Hoare.Model
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.OpcodeSafety

/-!
# Multi-Block `NonSyscallPreserved` Lifting

Defines `mlkemKeep` and `stripS` preservation helpers for `mlkemMultiLib` (`MlKemRoOk`, `Memory`
equality), and proves `mlkemBlockOk_withNonSyscallPreserved` and
`mlkemBlockConstOk_withNonSyscallPreserved` via `OpcodeSafety.mlkemMultiLib_blocks_all_svc0`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockConstOk
  MlKemBlockOk
  MlKemBlockSafeOk
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.OpcodeSafety (mlkemMultiLib_blocks_all_svc0)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)

/-- Execute-keep mask covering all 32 blocks of `mlkemMultiLib` under `mpl`. -/
@[expose] def mlkemKeep (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  (List.range mlkemMultiLib.blocks.length).any fun k =>
    progKeep (mlkemMultiLib.blockProgram mpl k) a

@[simp] theorem stripS_mem (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).mem = stripExecOutside keep s.mem := by cases s; rfl

@[simp] theorem stripS_readReg64 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS keep s).readReg64 r = s.readReg64 r := by cases s; rfl

@[simp] theorem stripS_readReg32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS keep s).readReg32 r = s.readReg32 r := by cases s; rfl

@[simp] theorem stripS_readVReg128 (keep : BitVec 64 → Bool) (s : State) (r : BitVec 5) :
    (stripS keep s).readVReg128 r = s.readVReg128 r := by cases s; rfl

@[simp] theorem stripS_sp (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sp = s.sp := by cases s; rfl

@[simp] theorem stripS_pc (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).pc = s.pc := by cases s; rfl

@[simp] theorem stripS_regs (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).regs = s.regs := by cases s; rfl

@[simp] theorem stripS_vregs (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).vregs = s.vregs := by cases s; rfl

@[simp] theorem stripS_status (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).status = s.status := by cases s; rfl

@[simp] theorem stripS_spAligned (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).spAligned = s.spAligned := by cases s; rfl

theorem strip_readBytes (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (addr : BitVec 64) (len : Nat),
      (stripExecOutside keep m).readBytes addr len = m.readBytes addr len
  | _, 0 => rfl
  | addr, n + 1 => by
    simp only [Memory.readBytes, strip_read8, strip_readBytes keep m (addr + 1#64) n]

theorem roDataAt_stripExecOutside (keep : BitVec 64 → Bool) {m : Memory}
    {addr : BitVec 64} {bytes : List (BitVec 8)} (hro : RoDataAt m addr bytes) :
    RoDataAt (stripExecOutside keep m) addr bytes := by
  refine ⟨fun a ha => ?_, (strip_readBytes keep m addr bytes.length).trans hro.2⟩
  obtain ⟨hp, hlf⟩ := hro.1 a ha
  refine ⟨?_, (strip_isLazyFree keep m a).trans hlf⟩
  rw [strip_perm, hp]
  unfold stripPerm Perm.ro
  cases keep a <;> rfl

theorem mlkemRoOk_stripExecOutside (keep : BitVec 64 → Bool) {mpl : MultiPlacement}
    {m : Memory} (hro : MlKemRoOk mpl m) :
    MlKemRoOk mpl (stripExecOutside keep m) :=
  ⟨roDataAt_stripExecOutside keep hro.zetaTable,
   roDataAt_stripExecOutside keep hro.keccakRc,
   roDataAt_stripExecOutside keep hro.cst16_0,
   roDataAt_stripExecOutside keep hro.cst16_1,
   roDataAt_stripExecOutside keep hro.cst16_2,
   roDataAt_stripExecOutside keep hro.cst16_3,
   roDataAt_stripExecOutside keep hro.cst16_4,
   roDataAt_stripExecOutside keep hro.cst16_5,
   roDataAt_stripExecOutside keep hro.cst16_6,
   roDataAt_stripExecOutside keep hro.cst16_7,
   roDataAt_stripExecOutside keep hro.cst16_8⟩

theorem stripExecOutside_eq_iff_of_perm_eq (keep : BitVec 64 → Bool) {m0 mf : Memory}
    (hperm : mf.perm = m0.perm) :
    stripExecOutside keep mf = stripExecOutside keep m0 ↔ mf = m0 := by
  refine ⟨fun hstrip => Memory.ext (funext fun a => ?_), fun h => h ▸ rfl⟩
  have hcell := congrFun (congrArg Memory.cells hstrip) a
  have hpa := congrFun hperm a
  dsimp only [stripExecOutside, Memory.perm] at hcell hpa
  rcases hcf : mf.cells a with _ | ⟨_ | pf, bf⟩ <;>
    rcases hc0 : m0.cells a with _ | ⟨_ | p0, b0⟩ <;>
    simp only [hcf, hc0] at hcell hpa
  · rfl
  · cases hcell
  · cases hcell
  · cases hcell
  · exact congrArg some (congrArg (Prod.mk none) (Prod.mk.inj (Option.some.inj hcell)).2)
  · cases (Prod.mk.inj (Option.some.inj hcell)).1
  · cases hcell
  · cases (Prod.mk.inj (Option.some.inj hcell)).1
  · obtain ⟨hsp, hb⟩ := Prod.mk.inj (Option.some.inj hcell)
    have hsp' : stripPerm (keep a) pf = stripPerm (keep a) p0 := Option.some.inj hsp
    have hrwx : pf.rwx = p0.rwx := Option.some.inj hpa
    subst hb
    have hpeq : pf = p0 := by
      rcases pf with ⟨r1, w1, x1, lf1, an1⟩
      rcases p0 with ⟨r0, w0, x0, lf0, an0⟩
      by_cases hk : keep a = true <;> cases x1 <;> cases x0 <;>
        simp_all [stripPerm, Perm.rwx]
    subst hpeq
    rfl

private theorem mlkemKeep_of_inBlock {mpl : MultiPlacement} {k : Nat}
    (hk : k < mlkemMultiLib.blocks.length) {a : BitVec 64}
    (hin : progKeep (mlkemMultiLib.blockProgram mpl k) a = true) :
    mlkemKeep mpl a = true := by
  unfold mlkemKeep
  rw [List.any_eq_true]
  exact ⟨k, List.mem_range.mpr hk, hin⟩

theorem strip_codeLoaded_mlkem {mpl : MultiPlacement} {m : Memory}
    (hcl : mlkemMultiLib.CodeLoaded mpl m) :
    mlkemMultiLib.CodeLoaded mpl (stripExecOutside (mlkemKeep mpl) m) := by
  intro k hk
  have hL := hcl k hk
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  let Pk := mlkemMultiLib.blockProgram mpl k
  have hno := hL.no_wrap
  have hsub : Pk.base + BitVec.ofNat 64 i - Pk.base = BitVec.ofNat 64 i := by bv_omega
  have hin : (Pk.base + BitVec.ofNat 64 i - Pk.base).toNat < Pk.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hi
  have hkp : progKeep Pk (Pk.base + BitVec.ofNat 64 i) = true := decide_eq_true hin
  have hmk : mlkemKeep mpl (Pk.base + BitVec.ofNat 64 i) = true :=
    mlkemKeep_of_inBlock hk hkp
  rw [strip_read8, strip_perm_of_keep hmk, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem externAt?_mlkemBlockProgram_none (mpl : MultiPlacement) (j : Nat)
    (pc : BitVec 64) :
    (mlkemMultiLib.blockProgram mpl j).externAt? pc = none := by
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program,
    Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0, Option.or_none]

private theorem fetch_in_mlkem_not_svc0 {mpl : MultiPlacement}
    (hpl : mlkemMultiLib.Placeable mpl)
    {m0 m : Memory} (hcl0 : mlkemMultiLib.CodeLoaded mpl m0) (hkf : m0.KeepsFrozen m)
    {pc : BitVec 64} {inst : Instr}
    (hk : mlkemKeep mpl pc = true)
    (hfm : Program.pureMem.fetchMem m pc = some inst) :
    inst.isSvc0 = false := by
  unfold mlkemKeep at hk
  rw [List.any_eq_true] at hk
  obtain ⟨k, hk_mem, hkp⟩ := hk
  have hk_lt : k < mlkemMultiLib.blocks.length := List.mem_range.mp hk_mem
  have hcl_m : (mlkemMultiLib.blockProgram mpl k).CodeLoaded m :=
    (hcl0 k hk_lt).of_keepsFrozen hkf
  have hal_pc : pc.toNat % 4 = 0 := by
    unfold Program.fetchMem at hfm
    by_cases h4 : pc.toNat % 4 = 0
    · exact h4
    · simp [h4] at hfm
  let Pk := mlkemMultiLib.blockProgram mpl k
  have hPk_al : Pk.base.toNat % 4 = 0 := hcl_m.aligned
  have hPk_nw : Pk.base.toNat + Pk.code.length ≤ 2 ^ 64 := hcl_m.no_wrap
  have hin : (pc - Pk.base).toNat < Pk.code.length := of_decide_eq_true hkp
  have hPk_len4 : Pk.code.length % 4 = 0 := by
    have hbt := (hpl.blocks_ok k hk_lt).len_aligned
    have hplen : ((mlkemMultiLib.blockLib k).text.patched
        (mlkemMultiLib.blockPlacement mpl k)).length =
        (mlkemMultiLib.blockLib k).text.code.length :=
      CodeBlock.length_patched_of_aligned _
        (by rw [mlkemMultiLib.blockLib_text hk_lt]; exact hbt)
    change ((mlkemMultiLib.blockLib k).text.patched
      (mlkemMultiLib.blockPlacement mpl k)).length % 4 = 0
    rw [hplen, mlkemMultiLib.blockLib_text hk_lt]
    exact hbt
  let off := (pc - Pk.base).toNat
  have hpc_eq : pc = Pk.base + BitVec.ofNat 64 off := by dsimp [off]; bv_omega
  have hoff_nat : off = pc.toNat - Pk.base.toNat := by
    change (pc - Pk.base).toNat < Pk.code.length at hin
    dsimp [off]; bv_omega
  have hoff_lt : off < Pk.code.length := hin
  have hoff4 : off % 4 = 0 := by omega
  have hoff_end : off + 4 ≤ Pk.code.length := by omega
  have hoff_end' : off + 4 ≤ (mlkemMultiLib.blockProgram mpl k).code.length := hoff_end
  have hrw : Pk.readWordOff off = some (m.read32 pc) := by
    have hb0 := hcl_m.byte_eq off (by omega)
    have hb1 := hcl_m.byte_eq (off + 1) (by omega)
    have hb2 := hcl_m.byte_eq (off + 2) (by omega)
    have hb3 := hcl_m.byte_eq (off + 3) (by omega)
    have ha0 : pc + 0#64 = Pk.base + BitVec.ofNat 64 off := by rw [hpc_eq]; bv_omega
    have ha1 : pc + 1#64 = Pk.base + BitVec.ofNat 64 (off + 1) := by rw [hpc_eq]; bv_omega
    have ha2 : pc + 2#64 = Pk.base + BitVec.ofNat 64 (off + 2) := by rw [hpc_eq]; bv_omega
    have ha3 : pc + 3#64 = Pk.base + BitVec.ofNat 64 (off + 3) := by rw [hpc_eq]; bv_omega
    unfold Program.readWordOff
    simp only [hoff4, ne_eq, not_true_eq_false, ↓reduceIte]
    have hd0 : Pk.code.drop off =
        Pk.code[off]'(by omega) :: Pk.code[off + 1]'(by omega) ::
        Pk.code[off + 2]'(by omega) :: Pk.code[off + 3]'(by omega) :: Pk.code.drop (off + 4) := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
        List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    rw [hd0]
    dsimp only [Memory.read32]
    rw [ha0, hb0, ha1, hb1, ha2, hb2, ha3, hb3]
  have hdec : decode (m.read32 pc) = some inst := by
    unfold Program.fetchMem at hfm
    split at hfm
    · simp at hfm
    · split at hfm
      · simp at hfm
      · split at hfm
        · simp at hfm
        · exact hfm
  have hfetch_Pk : Pk.fetch (Pk.base + BitVec.ofNat 64 off) = some inst := by
    have hf := Program.fetch_of_readWordOff (prog := Pk) (off := off) (by omega)
      (by simp [Pk, MultiPlacedLib.blockProgram, PlacedLib.program, Program.hookAtOff?]) hrw
    rwa [hdec] at hf
  have hps_svc : (mlkemMultiLib.blockLib k).text.patchSafe svc0Pat = true := by
    rw [mlkemMultiLib.blockLib_text hk_lt]
    exact (List.all_eq_true.mp mlkemMultiLib_blocks_all_svc0)
      mlkemMultiLib.blocks[k] (List.getElem_mem hk_lt)
  have hall_svc := PlacedLib.program_noSvc0_of_patchSafe hps_svc
    (mlkemMultiLib.blockPlacement mpl k)
  have hi := Program.fetch_of_allInstrs hall_svc _ _ hfetch_Pk
  simpa using hi

private theorem step_lift_stripS_mlkem {mpl : MultiPlacement} {j : Nat}
    (hpl : mlkemMultiLib.Placeable mpl)
    {m0 : Memory} (hcl0 : mlkemMultiLib.CodeLoaded mpl m0)
    {s s2' : State} (hkf : m0.KeepsFrozen s.mem)
    (hstep : Step (mlkemMultiLib.blockProgram mpl j) (stripS (mlkemKeep mpl) s) s2')
    (hnot_halt : s2'.status ≠ .Halted) :
    ∃ inst : Instr,
      (mlkemMultiLib.blockProgram mpl j).fetchMem s.mem s.pc = some inst ∧
      inst.isSvc0 = false ∧
      Step (mlkemMultiLib.blockProgram mpl j) s (execInst inst s) ∧
      s2' = stripS (mlkemKeep mpl) (execInst inst s) ∧
      ProofLib.NonSyscallPreserved s (execInst inst s) ∧
      m0.KeepsFrozen (execInst inst s).mem := by
  let P := mlkemMultiLib.blockProgram mpl j
  cases hstep with
  | halt_unmapped _ _ _ => exact False.elim (hnot_halt rfl)
  | extern _ h_ext _ _ =>
    rw [externAt?_mlkemBlockProgram_none] at h_ext
    cases h_ext
  | extern_fault _ h_ext _ =>
    rw [externAt?_mlkemBlockProgram_none] at h_ext
    cases h_ext
  | exec hrun' hfetch' =>
    rename_i inst
    have hrun : s.status = .Running := by simpa using hrun'
    rw [stripS_pc, stripS_mem] at hfetch'
    unfold Program.fetchMem at hfetch'
    rw [externAt?_mlkemBlockProgram_none] at hfetch'
    by_cases hce' : (stripExecOutside (mlkemKeep mpl) s.mem).canExec s.pc 4 = true
    · have hr32 : (stripExecOutside (mlkemKeep mpl) s.mem).read32 s.pc = s.mem.read32 s.pc := by
        simp [Memory.read32, strip_read8]
      have hx4 :
          ((stripExecOutside (mlkemKeep mpl) s.mem).perm s.pc).x = true ∧
          ((stripExecOutside (mlkemKeep mpl) s.mem).perm (s.pc + 1#64)).x = true ∧
          ((stripExecOutside (mlkemKeep mpl) s.mem).perm (s.pc + 2#64)).x = true ∧
          ((stripExecOutside (mlkemKeep mpl) s.mem).perm (s.pc + 3#64)).x = true := by
        simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
      obtain ⟨hx0, hk0⟩ := strip_perm_x_imp hx4.1
      obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
      obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
      obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
      have hce : s.mem.canExec s.pc 4 = true := by
        simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hce', Bool.not_true, hr32]
        at hfetch'
      have hfetch_pm : Program.pureMem.fetchMem s.mem s.pc = some inst := by
        unfold Program.fetchMem
        have hpure_ext : Program.pureMem.externAt? s.pc = none := rfl
        simp only [hpure_ext, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hce, Bool.not_true]
        exact hfetch'
      have hfetch_P : P.fetchMem s.mem s.pc = some inst := by
        unfold Program.fetchMem
        rw [externAt?_mlkemBlockProgram_none]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hce, Bool.not_true]
        exact hfetch'
      have hns : inst.isSvc0 = false :=
        fetch_in_mlkem_not_svc0 hpl hcl0 hkf hk0 hfetch_pm
      have heval_P : P.evalInst inst s = execInst inst s :=
        evalInst_eq_execInst_of_not_isSvc0 hns s
      have heval_P' :
          P.evalInst inst (stripS (mlkemKeep mpl) s) = execInst inst (stripS (mlkemKeep mpl) s) :=
        evalInst_eq_execInst_of_not_isSvc0 hns (stripS (mlkemKeep mpl) s)
      have hstep_s : Step P s (execInst inst s) :=
        heval_P ▸ Step.exec hrun hfetch_P
      refine ⟨inst, hfetch_P, hns, hstep_s, ?_,
        ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hns s,
        hkf.trans hstep_s.keepsFrozen⟩
      rw [heval_P', execInst_stripS hns (mlkemKeep mpl) s]
    · simp [hce'] at hfetch'

theorem steps_lift_stripS_mlkem {mpl : MultiPlacement} {j : Nat}
    (hpl : mlkemMultiLib.Placeable mpl)
    {m0 : Memory} (hcl0 : mlkemMultiLib.CodeLoaded mpl m0) :
    ∀ {s s' sf' : State},
      s' = stripS (mlkemKeep mpl) s →
      m0.KeepsFrozen s.mem →
      Steps (mlkemMultiLib.blockProgram mpl j) s' sf' →
      sf'.status ≠ .Halted →
      ∃ sf : State,
        sf' = stripS (mlkemKeep mpl) sf ∧
        Steps (mlkemMultiLib.blockProgram mpl j) s sf ∧
        ProofLib.NonSyscallPreserved s sf := by
  intro s s' sf' hs' hkf hsteps hnh
  induction hsteps generalizing s with
  | refl _ =>
    subst hs'
    exact ⟨s, rfl, Steps.refl s, ProofLib.NonSyscallPreserved.refl s⟩
  | @step s1' s2' sf' hstep hrest ih =>
    subst hs'
    have hnh2 : s2'.status ≠ .Halted := by
      cases hrest with
      | refl _ => exact hnh
      | step hs _ => rw [hs.status_running]; decide
    obtain ⟨inst, _, _, hstep_s, hs2_eq, hnsp1, hkf2⟩ :=
      step_lift_stripS_mlkem hpl hcl0 hkf hstep hnh2
    obtain ⟨sf, hsf_eq, hsteps_rest, hnsp_rest⟩ := ih hs2_eq hkf2 hnh
    exact ⟨sf, hsf_eq, Steps.step hstep_s hsteps_rest, hnsp1.trans hnsp_rest⟩

theorem steps_diverge_stripS_mlkem {mpl : MultiPlacement} {j : Nat}
    (hpl : mlkemMultiLib.Placeable mpl)
    {m0 : Memory} (hcl0 : mlkemMultiLib.CodeLoaded mpl m0) :
    ∀ {s u : State},
      Steps (mlkemMultiLib.blockProgram mpl j) s u →
      m0.KeepsFrozen s.mem →
      (∀ u', Steps (mlkemMultiLib.blockProgram mpl j) (stripS (mlkemKeep mpl) s) u' →
        u'.status = .Running ∧ ∃ v', Step (mlkemMultiLib.blockProgram mpl j) u' v') →
      u.status = .Running ∧ ∃ v, Step (mlkemMultiLib.blockProgram mpl j) u v := by
  intro s u hsteps
  induction hsteps with
  | refl s =>
    intro hkf hall'
    obtain ⟨hrun', v', hv'⟩ := hall' _ (Steps.refl _)
    have hrun_v' : v'.status = .Running := (hall' v' (Steps.step hv' (Steps.refl _))).1
    obtain ⟨inst, _, _, hstep_s, _, _, _⟩ :=
      step_lift_stripS_mlkem hpl hcl0 hkf hv' (by rw [hrun_v']; decide)
    exact ⟨by simpa using hrun', execInst inst s, hstep_s⟩
  | @step s s1 u hstep0 hrest ih =>
    intro hkf hall'
    obtain ⟨_, v', hv'⟩ := hall' _ (Steps.refl _)
    have hrun_v' : v'.status = .Running := (hall' v' (Steps.step hv' (Steps.refl _))).1
    obtain ⟨inst, hfetch_P, hns, _, hv'_eq, _, hkf1⟩ :=
      step_lift_stripS_mlkem hpl hcl0 hkf hv' (by rw [hrun_v']; decide)
    have hs1_eq : s1 = execInst inst s := by
      cases hstep0 with
      | halt_unmapped _ hfn _ => rw [hfetch_P] at hfn; cases hfn
      | extern _ hex _ _ => rw [externAt?_mlkemBlockProgram_none] at hex; cases hex
      | extern_fault _ hex _ => rw [externAt?_mlkemBlockProgram_none] at hex; cases hex
      | exec _ hfm =>
        rw [hfetch_P] at hfm
        injection hfm with hinst
        subst hinst
        exact evalInst_eq_execInst_of_not_isSvc0 hns s
    subst hs1_eq
    exact ih hkf1 fun u' hu' => hall' u' (Steps.step (hv'_eq ▸ hv') hu')

/-- Lift any `MlKemBlockOk j spec` (`j < 32`) to `withNonSyscallPreserved`. -/
theorem mlkemBlockOk_withNonSyscallPreserved {j : Nat} {α : Type}
    {spec : MultiPlacement → Spec α}
    (hok : MlKemBlockOk j spec)
    (hj : j < mlkemMultiLib.blocks.length := by decide)
    (hpan : ∀ mpl, (spec mpl).onPanic = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hex : ∀ mpl, (spec mpl).onExit = fun _ _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hoom : ∀ mpl, (spec mpl).onOom = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (h_pre : ∀ (mpl : MultiPlacement) (x : α) (R : SepProp) (s0 : State),
      (s0.mem ⊨ (spec mpl).pre x s0 ∗ R) →
      (s0.mem ⊨ (spec mpl).pre x (stripS (mlkemKeep mpl) s0) ∗ R) := by
        intro mpl x R s0 h; dsimp at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
    (h_post : ∀ (mpl : MultiPlacement) (x : α) (R : SepProp) (s0 sf : State),
      ProofLib.NonSyscallPreserved s0 sf →
      (sf.mem ⊨ (spec mpl).post x (stripS (mlkemKeep mpl) s0) (stripS (mlkemKeep mpl) sf) ∗ R) →
      (sf.mem ⊨ (spec mpl).post x s0 sf ∗ R) := by
        intro mpl x R s0 sf hnsp h; dsimp at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h) :
    MlKemBlockOk j (fun mpl => withNonSyscallPreserved (spec mpl)) := by
  intro _
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp _hLj
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved] at hpre
  rw [sepConj_comm ((spec mlkemMpl).pre x s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_spec⟩ := hpre
  let keep := mlkemKeep mlkemMpl
  have hpre_s0' := h_pre mlkemMpl x R s0 hpre_spec
  obtain ⟨R_view, hpre_strip, hunstrip⟩ := strip_frame keep hpre_s0'
  let s0' := stripS keep s0
  have hcl_strip : mlkemMultiLib.CodeLoaded mlkemMpl s0'.mem :=
    strip_codeLoaded_mlkem hcl0
  have hpre' : s0'.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl (spec mlkemMpl)).pre x s0' ∗ R_view := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl_strip]
    exact hpre_strip
  obtain ⟨sf', hsteps_blk, hout'⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hok x R_view s0'
      (by simpa [s0'] using hpc)
      (by simpa [s0'] using hrun)
      hpre'
      (by simpa [s0'] using hsp))
    (hcl_strip j hj)
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · obtain ⟨sf, hsf_eq, hsteps_P, hnsp⟩ :=
      steps_lift_stripS_mlkem MlKemPlacement.placeable hcl0 rfl
        (Memory.KeepsFrozen.refl s0.mem) hsteps_blk
        (by rw [hret'.2.2]; decide)
    refine ⟨sf, hsteps_P, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
      rw [hsf_eq] at hr_pc hr_sp hr_st
      exact ⟨by simpa [s0'] using hr_pc, by simpa [s0'] using hr_sp, by simpa using hr_st⟩
    · rw [hsf_eq] at hcc'
      rcases hcc' with ⟨hsp_cc, hcs⟩
      exact ⟨by simpa [s0'] using hsp_cc, by cases s0; cases sf; exact hcs⟩
    · rw [hsf_eq] at hpost'
      dsimp only [MultiPlacedLib.withCodeLoaded] at hpost'
      have hpost_strip : sf.mem ⊨
          (spec mlkemMpl).post x (stripS keep s0) (stripS keep sf) ∗ R :=
        hunstrip (fun a => congrFun hnsp.2.1 a) hpost'
      have hpost_sf := h_post mlkemMpl x R s0 sf hnsp hpost_strip
      dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved]
      rwa [sepConj_assoc, pure_sepConj_of_true hnsp]
  · dsimp only [MultiPlacedLib.withCodeLoaded] at hp
    rw [hpan mlkemMpl] at hp
    exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [MultiPlacedLib.withCodeLoaded] at he
    rw [hex mlkemMpl] at he
    exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [MultiPlacedLib.withCodeLoaded] at ho
    rw [hoom mlkemMpl] at ho
    exact False.elim (not_satisfies_false_sepConj ho)

/-- Lift any placement-independent `MlKemBlockConstOk j spec` (`j < 32`) to
    `withNonSyscallPreserved`. -/
theorem mlkemBlockConstOk_withNonSyscallPreserved {j : Nat} {α : Type}
    {spec : Spec α}
    (hok : MlKemBlockConstOk j spec)
    (hj : j < mlkemMultiLib.blocks.length := by decide)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre : ∀ (mpl : MultiPlacement) (x : α) (R : SepProp) (s0 : State),
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      (s0.mem ⊨ spec.pre x (stripS (mlkemKeep mpl) s0) ∗ R) := by
        intro mpl x R s0 h; dsimp at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
    (h_post : ∀ (mpl : MultiPlacement) (x : α) (R : SepProp) (s0 sf : State),
      ProofLib.NonSyscallPreserved s0 sf →
      (sf.mem ⊨ spec.post x (stripS (mlkemKeep mpl) s0) (stripS (mlkemKeep mpl) sf) ∗ R) →
      (sf.mem ⊨ spec.post x s0 sf ∗ R) := by
        intro mpl x R s0 sf hnsp h; dsimp at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h) :
    MlKemBlockConstOk j (withNonSyscallPreserved spec) :=
  mlkemBlockOk_withNonSyscallPreserved (spec := fun _ => spec) hok hj
    (fun _ => hpan) (fun _ => hex) (fun _ => hoom) h_pre h_post

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
