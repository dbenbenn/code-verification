/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted
public import ProofLib
public import ProofLib.Placed.Multi
public import ProofLib.Placed.OpcodeExclusion
public import ProofLib.Hoare.TraceEq
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MulSpecs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Field -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
import ProofLib.Hoare.Model
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbBridge

/-!
# Consumer-Contract & Algebraic Pipeline Bridges (`ConsumerBridges`)

Bridges the `dalekCliMultiLib` subroutine contracts (`InternalSpecs`, `CurveSpecs`, `MulSpecs`) to
consumer-ready `MultiPlacedLib.subroutineOk` and `CliExt` contracts with `Spec.withTraceEq`,
`keepsFs`, `withVmPreserved`, and pure `withRoOk (DalekCliRoOk mpl)` `.rodata` preconditions, plus:
- the 32-bit `w0` (`rust_bool`) contract and proof for `EdwardsPoint::is_torsion_free` (`B19`),
- `dalekEdNegBytes` / `dalekEdNegVec` limb-bound and `EdExtPoint` negation soundness, and
- the algebraic pipeline soundness bridges for `<PublicKey>::is_canonical` and XEdDSA
  `verify_signature_multipart`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Process (ElfImage ProcessInputs)
open ProofLib
open Arm64.Obj (MultiPlacement MultiPlacedLib Placement PlacedLib CodeBlock SymDataInfo
  HoldsBytes ElfMaps bytesLE lookupBlockSym msrTpidrEl0Pat svc0Pat)
open VerifiedLibraries.Common (
  p25519 edOrderL fpNeg leBytesToNat natToLeBytes
  EdPoint EdExtPoint edZero edBasepoint edOnCurve edAdd edSub edSmul
  edExtZero edExtToAffine edExtOfAffine encodeEd decodeEdDalek
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (
  dalekCliMultiLib dalekCliData00 dalekCliData01 dalekCliData02 dalekCliData03
  dalekCliData04 dalekCliData05 dalekCliData06 dalekCliData07 dalekCliData08
  dalekCliData09 dalekCliData10 dalekCliData00Bytes
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  ed25519_basepoint_table_ref fe51_one fe51_edwards_d fe51_minus_one fe51_sqrt_m1
  sc52_l sc52_rr fe51_edwards_d2 basepoint_order odd_multiples_basepoint ed25519_basepoint_table
  fe51OneBytes fe51EdwardsDBytes fe51MinusOneBytes fe51SqrtM1Bytes
  sc52LBytes sc52RRBytes fe51EdwardsD2Bytes basepointOrderBytes
  oddMultiplesBasepointBytes ed25519BasepointTableBytes
  fe51Val fe51ValOfBytes
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl dbase DalekBlockOk DalekBlockConstOk
  dalekSubroutineOk_of_blockOk dalekSubroutineOk_of_constBlockOk
  dalekCaller_ok DalekBase dalekBlockPlacement_ρ
  resolve_blk01 resolve_blk02 resolve_blk19 resolve_blk30 resolve_blk33
  resolve_ro01 resolve_ro08 resolve_ro10
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (
  fe51OneBytes_length fe51EdwardsDBytes_length fe51MinusOneBytes_length fe51SqrtM1Bytes_length
  sc52LBytes_length sc52RRBytes_length fe51EdwardsD2Bytes_length basepointOrderBytes_length
  oddMultiplesBasepointBytes_length ed25519BasepointTableBytes_length bytesLE8_length
  sc52LBytes_length sc52RRBytes_length
  basepointOrderBytes_val basepointOrderBytes_getD31
  fe51One_readLE_0 fe51One_readLE_8 fe51One_readLE_16 fe51One_readLE_24 fe51One_readLE_32
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded
  memcpySpec MemcpyOk memcpyRoSpec MemcpyRoOk blackBoxU8Spec BlackBoxU8Ok
  scalarFromBytesModOrderSpec ScalarFromBytesModOrderOk
  scalarFromBytesModOrderWideSpec ScalarFromBytesModOrderWideOk
  scalarMulSpec ScalarMulRefOk ScalarMulValOk
  scalarAddSpec ScalarAddRefOk ScalarAddValOk
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  decodeU255 montToEdwards isCanonicalX25519 lowOrderUs
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes edExtNeg
  edPointEq edVarBaseMul edDoubleScalarMulBasepoint
  edwardsPointCtEqSpec EdwardsPointCtEqOk
  edwardsPointCompressSpec EdwardsPointCompressOk
  compressedEdwardsYDecompressSpec CompressedEdwardsYDecompressOk
  montgomeryPointToEdwardsSpec MontgomeryPointToEdwardsOk
  vartimeDoubleScalarMulBasepointSpec VartimeDoubleScalarMulBasepointOk
  edwardsBasepointTableMulBaseSpec EdwardsBasepointTableMulBaseOk
  scalarMulBasepointTableSpec ScalarMulBasepointTableOk
  readLE_congr_off
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MulSpecs (
  edwardsPointMulScalarSpec EdwardsPointMulScalarOk
  edwardsPointMulScalarRoSpec EdwardsPointMulScalarRoOk
  edwardsPointIsTorsionFreeSpec EdwardsPointIsTorsionFreeOk
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (
  packFe51Bytes packFe51Bytes_length
  readLE_packFe51Bytes_0 readLE_packFe51Bytes_8 readLE_packFe51Bytes_16
  readLE_packFe51Bytes_24 readLE_packFe51Bytes_32
  readLE_append_right8
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Field (
  p25519_pos
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  EdExtValid edExtToAffine_edExtZero edExtValid_edExtZero
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (
  decodeEdDalek_encodeEd
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational (
  montToEdwards_some_onCurve montToEdwards_some_edToMontU edSmul_eight_eq_edZero_iff_lowOrderUs
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.DsmbBridge (
  dsmb_compress_eq
)
open LibsignalBinary.Heap (FdsHiFrame PoolPreserved VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (
  RoDataAt withRoData withRoDataSep SpecSimulates
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (pureByteFunctionSpec inputAfter)

/-! ## 1. Static `dalekCliMultiLib` Opcode-Exclusion, Extern-Freeness, & Trace/FS/VM Lifting -/

theorem dalekCliMultiLib_blocks_all_svc0 :
    (dalekCliMultiLib.blocks.all fun b => b.patchSafe svc0Pat) = true := by
  decide +kernel

/-- Every block of `dalekCliMultiLib` is statically free of `SVC #0` under arbitrary call/ADRP/ADD
    relocation patching. -/
theorem dalekCliMultiLib_patchSafe_svc0 :
    ∀ k (hk : k < dalekCliMultiLib.blocks.length),
      dalekCliMultiLib.blocks[k].patchSafe svc0Pat = true := by
  intro k hk
  exact List.all_eq_true.mp dalekCliMultiLib_blocks_all_svc0 dalekCliMultiLib.blocks[k]
    (List.getElem_mem hk)

theorem dalekCliMultiLib_blocks_all_msr :
    (dalekCliMultiLib.blocks.all fun b => b.patchSafe msrTpidrEl0Pat) = true := by
  decide +kernel

/-- Every block of `dalekCliMultiLib` is statically free of `MSR TPIDR_EL0, Xt` under arbitrary
    relocation patching. -/
theorem dalekCliMultiLib_patchSafe_msr :
    ∀ k (hk : k < dalekCliMultiLib.blocks.length),
      dalekCliMultiLib.blocks[k].patchSafe msrTpidrEl0Pat = true := by
  intro k hk
  exact List.all_eq_true.mp dalekCliMultiLib_blocks_all_msr dalekCliMultiLib.blocks[k]
    (List.getElem_mem hk)

private theorem dalekCliMultiLib_blocks_all_externs_empty :
    (dalekCliMultiLib.blocks.all fun b => b.externs.isEmpty) = true := by
  decide +kernel

theorem dalekCliMultiLib_block_externs_nil (i : Nat)
    (hi : i < dalekCliMultiLib.blocks.length) :
    (dalekCliMultiLib.blockLib i).text.externs = [] := by
  have hempty : dalekCliMultiLib.blocks[i].externs = [] := by
    have h := List.all_eq_true.mp dalekCliMultiLib_blocks_all_externs_empty
      dalekCliMultiLib.blocks[i] (List.getElem_mem hi)
    exact List.isEmpty_iff.mp h
  rw [dalekCliMultiLib.blockLib_text hi]
  exact hempty

/-- Every block of `dalekCliMultiLib` has `.externs = []`, so `blockProgram` has `externAt? = none`
    at all PCs for every extern map `externs`. -/
theorem dalekCliMultiLib_externAt_none (mpl : MultiPlacement) (i : Nat)
    (hi : i < dalekCliMultiLib.blocks.length)
    (externs : String → Option (State → State)) (pc : BitVec 64) :
    (dalekCliMultiLib.blockProgram mpl i externs).externAt? pc = none := by
  have hblk := dalekCliMultiLib_block_externs_nil i hi
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program,
    Program.externAt?, Program.hookAtOff?]
  rw [hblk]
  simp

/-- Every address inside the 37 code blocks of `dalekCliMultiLib` under `mpl` is unhooked in `P`. -/
@[expose] def DalekBlocksHookFree (P : Program) (mpl : MultiPlacement) : Prop :=
  ∀ k (hk : k < dalekCliMultiLib.blocks.length) (off : Nat),
    off < dalekCliMultiLib.blocks[k].code.length →
    P.externAt? (mpl.base k + BitVec.ofNat 64 off) = none

/-- Keep predicate covering all 37 placed blocks of `dalekCliMultiLib` under `mpl`. -/
@[expose] def dalekMultiKeep (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  (List.range dalekCliMultiLib.blocks.length).any fun k =>
    ProofLib.progKeep (dalekCliMultiLib.blockProgram mpl k) a

private theorem strip_codeLoaded_dalek {mpl : MultiPlacement} {m : Memory}
    (hcl : dalekCliMultiLib.CodeLoaded mpl m) :
    dalekCliMultiLib.CodeLoaded mpl (stripExecOutside (dalekMultiKeep mpl) m) := by
  intro j hj
  have hL := hcl j hj
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  let Pj := dalekCliMultiLib.blockProgram mpl j
  have hsub : Pj.base + BitVec.ofNat 64 k - Pj.base = BitVec.ofNat 64 k := by bv_omega
  have hin : (Pj.base + BitVec.ofNat 64 k - Pj.base).toNat < Pj.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hk
  have hkp : progKeep Pj (Pj.base + BitVec.ofNat 64 k) = true := by
    unfold progKeep; exact decide_eq_true hin
  have hmk : dalekMultiKeep mpl (Pj.base + BitVec.ofNat 64 k) = true := by
    unfold dalekMultiKeep
    rw [List.any_eq_true]
    exact ⟨j, List.mem_range.mpr hj, hkp⟩
  have hp_eq : (stripExecOutside (dalekMultiKeep mpl) m).perm (Pj.base + BitVec.ofNat 64 k) =
      m.perm (Pj.base + BitVec.ofNat 64 k) := by
    rw [strip_perm, hmk]
    cases m.perm (Pj.base + BitVec.ofNat 64 k) with
    | none => rfl
    | some p => cases p; rfl
  rw [strip_read8, hp_eq, strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem vmPreserved_of_nonSyscall_tpidr {s0 sf : State}
    (hnsp : ProofLib.NonSyscallPreserved s0 sf) (htp : sf.tpidrEl0 = s0.tpidrEl0) :
    VmPreserved s0 sf := by
  have hpool : PoolPreserved s0 sf := ⟨hnsp.2.2.2.1, hnsp.2.2.1, htp⟩
  have hfds : FdsHiFrame s0 sf := fun fd _ _ => by rw [hnsp.2.2.2.2.2.2]
  exact ⟨hpool, hnsp.2.2.2.2.1, fun a => congrFun hnsp.2.1 a, hfds⟩

private theorem fetch_in_dalek_not_svc0_msr {mpl : MultiPlacement}
    (hpl : dalekCliMultiLib.Placeable mpl)
    {m0 m : Memory} (hcl0 : dalekCliMultiLib.CodeLoaded mpl m0) (hkf : m0.KeepsFrozen m)
    {pc : BitVec 64} {inst : Instr}
    (hk : dalekMultiKeep mpl pc = true)
    (hfm : Program.pureMem.fetchMem m pc = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  unfold dalekMultiKeep at hk
  rw [List.any_eq_true] at hk
  obtain ⟨j, hj_mem, hkp⟩ := hk
  have hj : j < dalekCliMultiLib.blocks.length := List.mem_range.mp hj_mem
  have hcl_m : (dalekCliMultiLib.blockProgram mpl j).CodeLoaded m := (hcl0 j hj).of_keepsFrozen hkf
  have hal_pc : pc.toNat % 4 = 0 := by
    unfold Program.fetchMem at hfm
    by_cases h4 : pc.toNat % 4 = 0
    · exact h4
    · simp [h4] at hfm
  let Pj := dalekCliMultiLib.blockProgram mpl j
  have hPj_al : Pj.base.toNat % 4 = 0 := hcl_m.aligned
  have hPj_nw : Pj.base.toNat + Pj.code.length ≤ 2 ^ 64 := hcl_m.no_wrap
  have hin : (pc - Pj.base).toNat < Pj.code.length := by
    unfold progKeep at hkp; exact of_decide_eq_true hkp
  have hPj_len4 : Pj.code.length % 4 = 0 := by
    have hbt := (hpl.blocks_ok j hj).len_aligned
    have hplen : ((dalekCliMultiLib.blockLib j).text.patched
        (dalekCliMultiLib.blockPlacement mpl j)).length =
        (dalekCliMultiLib.blockLib j).text.code.length :=
      CodeBlock.length_patched_of_aligned _
        (by rw [dalekCliMultiLib.blockLib_text hj]; exact hbt)
    change ((dalekCliMultiLib.blockLib j).text.patched
      (dalekCliMultiLib.blockPlacement mpl j)).length % 4 = 0
    rw [hplen, dalekCliMultiLib.blockLib_text hj]
    exact hbt
  let off := (pc - Pj.base).toNat
  have hpc_eq : pc = Pj.base + BitVec.ofNat 64 off := by dsimp [off]; bv_omega
  have hpc_ge : Pj.base.toNat ≤ pc.toNat := by
    change (pc - Pj.base).toNat < Pj.code.length at hin; bv_omega
  have hoff_nat : off = pc.toNat - Pj.base.toNat := by dsimp [off]; bv_omega
  have hoff_lt : off < Pj.code.length := hin
  have hPj_len_eq : (dalekCliMultiLib.blockProgram mpl j).code.length = Pj.code.length := rfl
  have hoff4 : off % 4 = 0 := by omega
  have hrw : Pj.readWordOff off = some (m.read32 pc) := by
    have hb0 := hcl_m.byte_eq off (by omega)
    have hb1 := hcl_m.byte_eq (off + 1) (by omega)
    have hb2 := hcl_m.byte_eq (off + 2) (by omega)
    have hb3 := hcl_m.byte_eq (off + 3) (by omega)
    have ha0 : pc + 0#64 = Pj.base + BitVec.ofNat 64 off := by rw [hpc_eq]; bv_omega
    have ha1 : pc + 1#64 = Pj.base + BitVec.ofNat 64 (off + 1) := by rw [hpc_eq]; bv_omega
    have ha2 : pc + 2#64 = Pj.base + BitVec.ofNat 64 (off + 2) := by rw [hpc_eq]; bv_omega
    have ha3 : pc + 3#64 = Pj.base + BitVec.ofNat 64 (off + 3) := by rw [hpc_eq]; bv_omega
    unfold Program.readWordOff
    simp only [hoff4, ne_eq, not_true_eq_false, ↓reduceIte]
    have hd0 : Pj.code.drop off =
        Pj.code[off]'(by omega) :: Pj.code[off + 1]'(by omega) ::
        Pj.code[off + 2]'(by omega) :: Pj.code[off + 3]'(by omega) :: Pj.code.drop (off + 4) := by
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
  have hfetch_Pj : Pj.fetch (Pj.base + BitVec.ofNat 64 off) = some inst := by
    have hf := Program.fetch_of_readWordOff (prog := Pj) (off := off) (by omega)
      (by simp [Pj, MultiPlacedLib.blockProgram, PlacedLib.program, Program.hookAtOff?]) hrw
    rwa [hdec] at hf
  have hps_svc : (dalekCliMultiLib.blockLib j).text.patchSafe svc0Pat = true := by
    rw [dalekCliMultiLib.blockLib_text hj]
    exact dalekCliMultiLib_patchSafe_svc0 j hj
  have hps_msr : (dalekCliMultiLib.blockLib j).text.patchSafe msrTpidrEl0Pat = true := by
    rw [dalekCliMultiLib.blockLib_text hj]
    exact dalekCliMultiLib_patchSafe_msr j hj
  have hall_svc := PlacedLib.program_noSvc0_of_patchSafe hps_svc
    (dalekCliMultiLib.blockPlacement mpl j)
  have hall_msr := PlacedLib.program_noMsrTpidrEl0_of_patchSafe hps_msr
    (dalekCliMultiLib.blockPlacement mpl j)
  exact ⟨by have hi := Program.fetch_of_allInstrs hall_svc _ _ hfetch_Pj; simpa using hi,
    by have hi := Program.fetch_of_allInstrs hall_msr _ _ hfetch_Pj; simpa using hi⟩

private theorem steps_pureMem_lift_stripS_vm (keep : BitVec 64 → Bool) {P : Program}
    {m0 : Memory}
    (hext_P : ∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none)
    (h_pure : ∀ (m : Memory) (pc : BitVec 64) (inst : Instr),
      m0.KeepsFrozen m →
      keep pc = true →
      Program.pureMem.fetchMem m pc = some inst →
      inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false) :
    ∀ {s0 s' sf' : State},
      s' = stripS keep s0 →
      m0.KeepsFrozen s0.mem →
      Steps Program.pureMem s' sf' →
      sf'.status = .Running →
      ∃ sf : State,
        sf' = stripS keep sf ∧
        Steps P s0 sf ∧
        ProofLib.NonSyscallPreserved s0 sf ∧
        sf.tpidrEl0 = s0.tpidrEl0 := by
  intro s0 s' sf' hs' hkf hsteps hrun_f
  induction hsteps generalizing s0 with
  | refl _ =>
    subst hs'
    exact ⟨s0, rfl, Steps.refl s0, ProofLib.NonSyscallPreserved.refl s0, rfl⟩
  | @step s1' s2' sf' hstep hrest ih =>
    subst hs'
    have hrun2' : s2'.status = .Running := by
      cases hrest with
      | refl _ => exact hrun_f
      | step hs _ => exact hs.status_running
    cases hstep with
    | halt_unmapped _ _ _ => simp at hrun2'
    | extern _ h_ext _ _ => nomatch h_ext
    | extern_fault _ h_ext _ => nomatch h_ext
    | exec hrun1' hfetch' =>
      rename_i inst
      have hrun1 : s0.status = .Running := by cases s0; exact hrun1'
      have hpc_eq : (stripS keep s0).pc = s0.pc := by cases s0; rfl
      have hmem_eq : (stripS keep s0).mem = stripExecOutside keep s0.mem := by cases s0; rfl
      rw [hpc_eq, hmem_eq] at hfetch'
      unfold Program.fetchMem at hfetch'
      by_cases hce' : (stripExecOutside keep s0.mem).canExec s0.pc 4 = true
      · have hr32 : (stripExecOutside keep s0.mem).read32 s0.pc = s0.mem.read32 s0.pc := by
          simp [Memory.read32, strip_read8]
        simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr32] at hfetch'
        have hx4 :
            ((stripExecOutside keep s0.mem).perm s0.pc).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 1#64)).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 2#64)).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 3#64)).x = true := by
          simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
        obtain ⟨hx0, hk0⟩ := strip_perm_x_imp hx4.1
        obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
        obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
        obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
        have hce : s0.mem.canExec s0.pc 4 = true := by
          simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
        have hpure_ext : Program.pureMem.externAt? s0.pc = none := rfl
        have hfetch_pm : Program.pureMem.fetchMem s0.mem s0.pc = some inst := by
          unfold Program.fetchMem
          rw [hpure_ext] at hfetch' ⊢
          simpa [hce] using hfetch'
        have hfetch_P : P.fetchMem s0.mem s0.pc = some inst := by
          unfold Program.fetchMem
          rw [hext_P s0.pc hk0]
          unfold Program.fetchMem at hfetch_pm
          rw [hpure_ext] at hfetch_pm
          exact hfetch_pm
        obtain ⟨hns, hmsr⟩ := h_pure s0.mem s0.pc inst hkf hk0 hfetch_pm
        rw [evalInst_pureMem] at hrest hrun2' ih
        have heval_P : P.evalInst inst s0 = execInst inst s0 :=
          evalInst_eq_execInst_of_not_isSvc0 hns s0
        have hstep_s0 : Step P s0 (execInst inst s0) :=
          heval_P ▸ Step.exec hrun1 hfetch_P
        have hstep_pm : Step Program.pureMem s0 (execInst inst s0) :=
          evalInst_pureMem inst s0 ▸ Step.exec hrun1 hfetch_pm
        have hcomm : execInst inst (stripS keep s0) = stripS keep (execInst inst s0) :=
          execInst_stripS hns keep s0
        have hnsp1 : ProofLib.NonSyscallPreserved s0 (execInst inst s0) :=
          ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hns s0
        have htp1 : (execInst inst s0).tpidrEl0 = s0.tpidrEl0 :=
          execInst_tpidrEl0_of_not_isMsrTpidrEl0 hmsr s0
        have hkf2 : m0.KeepsFrozen (execInst inst s0).mem := hkf.trans hstep_pm.keepsFrozen
        obtain ⟨sf, hsf_eq, hsteps_rest, hnsp_rest, htp_rest⟩ := ih hcomm hkf2 hrun_f
        exact ⟨sf, hsf_eq, Steps.step hstep_s0 hsteps_rest, hnsp1.trans hnsp_rest,
          htp_rest.trans htp1⟩
      · simp [hce'] at hfetch'

/-- Lift any `subroutine_ok` proved on `dalekCliMultiLib.blockProgram mpl i` to
    `Spec.withTraceEq (keepsFs (withVmPreserved spec))` on `dalekCliMultiLib.blockProgram mpl i externs`
    for arbitrary `externs`. -/
theorem dalek_blockProgram_withTraceEq_keepsFs_withVmPreserved {α : Type}
    {mpl : MultiPlacement} {i : Nat} {entry : BitVec 64} {spec : Spec α}
    {externs : String → Option (State → State)}
    (hi : i < dalekCliMultiLib.blocks.length)
    (hpl : dalekCliMultiLib.Placeable mpl)
    (hsub : subroutine_ok (dalekCliMultiLib.blockProgram mpl i) entry
      (dalekCliMultiLib.withCodeLoaded mpl spec))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok (dalekCliMultiLib.blockProgram mpl i externs) entry
      (dalekCliMultiLib.withCodeLoaded mpl
        (Spec.withTraceEq (keepsFs (withVmPreserved spec)))) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp _hLi
  dsimp only [MultiPlacedLib.withCodeLoaded, Spec.withTraceEq, keepsFs, withVmPreserved] at hpre
  rw [sepConj_comm (spec.pre x s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_spec⟩ := hpre
  let keep := dalekMultiKeep mpl
  obtain ⟨R_view, hpre_strip, hunstrip⟩ := ProofLib.strip_frame keep hpre_spec
  let s0' := stripS keep s0
  have hcl_strip : dalekCliMultiLib.CodeLoaded mpl s0'.mem := by
    have hm : s0'.mem = stripExecOutside keep s0.mem := by cases s0; rfl
    rw [hm]; exact strip_codeLoaded_dalek hcl0
  have hpre' : s0'.mem ⊨ (dalekCliMultiLib.withCodeLoaded mpl spec).pre x s0' ∗ R_view := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl_strip]
    have hs0_eq : s0' = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
    rw [hs0_eq, h_pre_mem]
    simpa [State.setMem] using hpre_strip
  have hLi_strip : (dalekCliMultiLib.blockProgram mpl i).CodeLoaded s0'.mem :=
    hcl_strip i hi
  obtain ⟨sf', hsteps_blk, hout'⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hsub x R_view s0' (by cases s0; exact hpc) (by cases s0; exact hrun)
      hpre' (by cases s0; exact hsp))
    hLi_strip
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have hsteps_pm' : Steps Program.pureMem s0' sf' :=
      Steps.of_sameHooks (P := Program.pureMem) (Q := dalekCliMultiLib.blockProgram mpl i)
        (fun pc => dalekCliMultiLib_externAt_none mpl i hi _ pc) rfl hsteps_blk
    obtain ⟨sf, hsf_eq, hsteps_P, hnsp, htp⟩ :=
      steps_pureMem_lift_stripS_vm keep
        (fun pc _ => dalekCliMultiLib_externAt_none mpl i hi externs pc)
        (fun m pc inst hkf hk hfm => fetch_in_dalek_not_svc0_msr hpl hcl0 hkf hk hfm)
        rfl (Memory.KeepsFrozen.refl s0.mem) hsteps_pm' hret'.2.2
    refine ⟨sf, hsteps_P, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
      rw [hsf_eq] at hr_pc hr_sp hr_st
      exact ⟨by cases s0; cases sf; exact hr_pc,
        by cases s0; cases sf; exact hr_sp,
        by cases sf; exact hr_st⟩
    · rw [hsf_eq] at hcc'
      rcases hcc' with ⟨hsp_cc, hcs⟩
      exact ⟨by cases s0; cases sf; exact hsp_cc, by cases s0; cases sf; exact hcs⟩
    · rw [hsf_eq] at hpost'
      dsimp only [MultiPlacedLib.withCodeLoaded] at hpost'
      have hs0_set : s0' = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
      have hsf_set : stripS keep sf = sf.setMem (stripExecOutside keep sf.mem) := by
        cases sf; rfl
      rw [hs0_set, hsf_set, h_post_mem] at hpost'
      have hpost_sf : sf.mem ⊨ spec.post x s0 sf ∗ R :=
        hunstrip (fun a => congrFun hnsp.2.1 a) (by simpa [State.setMem] using hpost')
      have hvm : VmPreserved s0 sf := vmPreserved_of_nonSyscall_tpidr hnsp htp
      dsimp only [MultiPlacedLib.withCodeLoaded, Spec.withTraceEq, keepsFs, withVmPreserved]
      simp only [sepConj_assoc]
      rw [satisfies_pure_sepConj]
      refine ⟨hnsp.1, ?_⟩
      rw [satisfies_pure_sepConj]
      refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hvm, hpost_sf⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded] at hp
    rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [MultiPlacedLib.withCodeLoaded] at he
    rw [hex] at he; exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [MultiPlacedLib.withCodeLoaded] at ho
    rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-- Export any `DalekBlockOk j spec` to `dalekCliMultiLib.subroutineOk sym` with `Spec.withTraceEq`,
    `keepsFs`, and `withVmPreserved` under any extern table `externs`. -/
theorem dalekSubroutineOk_withTraceEq_keepsFs_vmPreserved {j : Nat} (sym : String)
    {α : Type} {spec : MultiPlacement → Spec α}
    (hok : DalekBlockOk j spec)
    (externs : String → Option (State → State) := fun _ => none)
    (hexp : sym ∈ dalekCliMultiLib.exports := by decide +kernel)
    (hsym : lookupBlockSym sym dalekCliMultiLib.blocks = some (j, 0) := by decide +kernel)
    (hj : j < dalekCliMultiLib.blocks.length := by decide +kernel)
    (hpan : ∀ mpl, (spec mpl).onPanic = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hex : ∀ mpl, (spec mpl).onExit = fun _ _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hoom : ∀ mpl, (spec mpl).onOom = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (h_pre_mem : ∀ mpl x (s : State) (m : Memory),
      (spec mpl).pre x (s.setMem m) = (spec mpl).pre x s := by
      intro _ _ s _; cases s; rfl)
    (h_post_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
      (spec mpl).post x (s0.setMem m0) (sf.setMem mf) = (spec mpl).post x s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl) :
    dalekCliMultiLib.subroutineOk sym
      (fun mpl => Spec.withTraceEq (keepsFs (withVmPreserved (spec mpl)))) externs := by
  refine ⟨hexp, j, 0, hsym, fun mpl hpl => ?_⟩
  let _ : DalekCliPlacement := ⟨mpl, hpl⟩
  have hfn : dalekCliMultiLib.fnAddr mpl sym = mpl.base j := by
    simp [MultiPlacedLib.fnAddr, hsym]
  rw [hfn]
  exact dalek_blockProgram_withTraceEq_keepsFs_withVmPreserved hj hpl hok
    (hpan mpl) (hex mpl) (hoom mpl) (h_pre_mem mpl) (h_post_mem mpl)

/-- Placement-independent specialization of `dalekSubroutineOk_withTraceEq_keepsFs_vmPreserved`. -/
theorem dalekSubroutineOk_const_withTraceEq_keepsFs_vmPreserved {j : Nat} (sym : String)
    {α : Type} {spec : Spec α}
    (hok : DalekBlockConstOk j spec)
    (externs : String → Option (State → State) := fun _ => none)
    (hexp : sym ∈ dalekCliMultiLib.exports := by decide +kernel)
    (hsym : lookupBlockSym sym dalekCliMultiLib.blocks = some (j, 0) := by decide +kernel)
    (hj : j < dalekCliMultiLib.blocks.length := by decide +kernel)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by
      intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    dalekCliMultiLib.subroutineOk sym
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved spec))) externs :=
  dalekSubroutineOk_withTraceEq_keepsFs_vmPreserved sym (spec := fun _ => spec) hok externs
    hexp hsym hj (fun _ => hpan) (fun _ => hex) (fun _ => hoom)
    (fun _ => h_pre_mem) (fun _ => h_post_mem)

/-! ## 2. Pure `.rodata` Image Facts (`DalekCliRoOk`) & `InElf` Supply -/

/-- Adjoin a pure memory predicate `⌜RoOk s0.mem⌝` to `spec.pre`. -/
@[expose] def withRoOk {α : Type} (RoOk : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜RoOk s0.mem⌝ ∗ spec.pre x s0 }

/-- All 11 `.rodata` / `.data.rel.ro` entries of `dalekCliMultiLib` hold at their placed addresses
    in `m` with `Perm.ro` (and `lazyFree = false`). -/
structure DalekCliRoOk (mpl : MultiPlacement) (m : Memory) : Prop where
  ro_basepoint_table_ref :
    RoDataAt m (ed25519_basepoint_table_ref mpl) (bytesLE 8 (ed25519_basepoint_table mpl))
  ro_fe51_one : RoDataAt m (fe51_one mpl) fe51OneBytes
  ro_fe51_edwards_d : RoDataAt m (fe51_edwards_d mpl) fe51EdwardsDBytes
  ro_fe51_minus_one : RoDataAt m (fe51_minus_one mpl) fe51MinusOneBytes
  ro_fe51_sqrt_m1 : RoDataAt m (fe51_sqrt_m1 mpl) fe51SqrtM1Bytes
  ro_sc52_l : RoDataAt m (sc52_l mpl) sc52LBytes
  ro_sc52_rr : RoDataAt m (sc52_rr mpl) sc52RRBytes
  ro_fe51_edwards_d2 : RoDataAt m (fe51_edwards_d2 mpl) fe51EdwardsD2Bytes
  ro_basepoint_order : RoDataAt m (basepoint_order mpl) basepointOrderBytes
  ro_odd_multiples_basepoint : RoDataAt m (odd_multiples_basepoint mpl) oddMultiplesBasepointBytes
  ro_ed25519_basepoint_table : RoDataAt m (ed25519_basepoint_table mpl) ed25519BasepointTableBytes

private theorem dalekCliData00_drop8 : dalekCliData00Bytes.drop 8 = [] := by decide +kernel

set_option maxRecDepth 200000 in
private theorem dalekCli_patchedData_00 (mpl : MultiPlacement) :
    dalekCliMultiLib.patchedData mpl dalekCliData00 =
      bytesLE 8 (ed25519_basepoint_table mpl) := by
  simp only [dalekCliData00, MultiPlacedLib.patchedData, List.foldl_cons, List.foldl_nil,
    List.replicate_zero, List.append_nil, MultiPlacedLib.patchDataReloc, resolve_ro10,
    Obj.addSignedAddr, List.take_zero, List.nil_append,
    Nat.zero_add, dalekCliData00_drop8, ed25519_basepoint_table]
  rfl

/-- Load-time `HoldsBytes ... Perm.ro` for all `dalekCliMultiLib.data` entries supplies
    `DalekCliRoOk mpl m` on any memory `m` with `m₀.KeepsFrozen m`. -/
theorem dalekCliRoOk_of_holdsBytes_keepsFrozen {mpl : MultiPlacement} {m₀ m : Memory}
    (hhold : ∀ d ∈ dalekCliMultiLib.data,
      HoldsBytes m₀ (mpl.ρ d.sym) (dalekCliMultiLib.patchedData mpl d) (fun _ => Perm.ro))
    (hkf : m₀.KeepsFrozen m) :
    DalekCliRoOk mpl m := by
  have hd_eq : dalekCliMultiLib.data =
      [dalekCliData00, dalekCliData01, dalekCliData02, dalekCliData03, dalekCliData04,
       dalekCliData05, dalekCliData06, dalekCliData07, dalekCliData08, dalekCliData09,
       dalekCliData10] := rfl
  rw [hd_eq] at hhold
  simp only [List.forall_mem_cons] at hhold
  rcases hhold with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩
  simp only [dalekCli_patchedData_00] at h0
  simp only [dalekCliData01, dalekCliData02, dalekCliData03, dalekCliData04,
    dalekCliData05, dalekCliData06, dalekCliData07, dalekCliData08, dalekCliData09, dalekCliData10,
    MultiPlacedLib.patchedData, List.foldl_nil, List.replicate_zero,
    List.append_nil] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact
    { ro_basepoint_table_ref := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h0 hkf)
      ro_fe51_one := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h1 hkf)
      ro_fe51_edwards_d := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h2 hkf)
      ro_fe51_minus_one := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h3 hkf)
      ro_fe51_sqrt_m1 := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h4 hkf)
      ro_sc52_l := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h5 hkf)
      ro_sc52_rr := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h6 hkf)
      ro_fe51_edwards_d2 := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h7 hkf)
      ro_basepoint_order := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h8 hkf)
      ro_odd_multiples_basepoint := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h9 hkf)
      ro_ed25519_basepoint_table := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h10 hkf) }

/-- `ElfMaps ... (· == Perm.ro)` for all `dalekCliMultiLib.data` entries supplies
    `DalekCliRoOk mpl m` on any memory `m` preserving frozen bytes from `img.loadState inputs = .ok s0`. -/
theorem dalekCliRoOk_of_elfMaps_keepsFrozen {img : ElfImage} {mpl : MultiPlacement}
    {inputs : ProcessInputs} {s0 : State} {m : Memory}
    (hmap : ∀ d ∈ dalekCliMultiLib.data,
      ElfMaps img (mpl.ρ d.sym) (dalekCliMultiLib.patchedData mpl d) (fun p => p == Perm.ro))
    (hload : img.loadState inputs = .ok s0)
    (hkf : s0.mem.KeepsFrozen m) :
    DalekCliRoOk mpl m :=
  dalekCliRoOk_of_holdsBytes_keepsFrozen
    (fun d hd => ElfMaps.holdsBytes hload (p := Perm.ro) (fun q hq => by simpa using hq) (hmap d hd))
    hkf

/-- Absorb a separating `withRoDataSep addr bytes` wrapper into `withRoOk RoOk` whenever `RoOk`
    implies `RoDataAt m addr bytes`. -/
theorem specSimulates_absorb_roDataSep {α : Type} {RoOk : Memory → Prop}
    {addr : BitVec 64} {bytes : List (BitVec 8)} {spec : Spec α}
    (hlen : bytes.length ≤ 2 ^ 64)
    (hro : ∀ m, RoOk m → RoDataAt m addr bytes) :
    SpecSimulates (withRoDataSep addr bytes (withRoOk RoOk spec)) (withRoOk RoOk spec) := by
  have h1 : SpecSimulates (withRoDataSep addr bytes (withRoOk RoOk spec))
      (withRoData addr bytes (withRoOk RoOk spec)) :=
    SpecSimulates.withRoData_of_sep hlen
  refine h1.trans fun x R s0 hpre => ?_
  dsimp only [withRoOk] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hroOk, hpre⟩ := hpre
  refine ⟨x, R, ?_, fun _ hout => hout⟩
  dsimp only [withRoData, withRoOk]
  simp only [sepConj_assoc]
  rw [satisfies_pure_sepConj]
  refine ⟨hro s0.mem hroOk, ?_⟩
  rw [satisfies_pure_sepConj]
  exact ⟨hroOk, hpre⟩

/-! ## 3. `fe51Point4Bounded` Monotonicity & `dalekEdNegBytes` Soundness -/

theorem fe51LimbsBoundedAt_mono {bs : List (BitVec 8)} {off b1 b2 : Nat}
    (h : fe51LimbsBoundedAt bs off b1) (hle : b1 ≤ b2) :
    fe51LimbsBoundedAt bs off b2 := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  exact ⟨Nat.lt_of_lt_of_le h0 hle, Nat.lt_of_lt_of_le h1 hle,
    Nat.lt_of_lt_of_le h2 hle, Nat.lt_of_lt_of_le h3 hle, Nat.lt_of_lt_of_le h4 hle⟩

theorem fe51Point4Bounded_mono {bs : List (BitVec 8)} {b1 b2 : Nat}
    (h : fe51Point4Bounded bs b1) (hle : b1 ≤ b2) :
    fe51Point4Bounded bs b2 := by
  rcases h with ⟨hlen, h0, h1, h2, h3⟩
  exact ⟨hlen, fe51LimbsBoundedAt_mono h0 hle, fe51LimbsBoundedAt_mono h1 hle,
    fe51LimbsBoundedAt_mono h2 hle, fe51LimbsBoundedAt_mono h3 hle⟩

/-- Pure `Scalar::from_bytes_mod_order` vector function (`32` bytes → `32` bytes). -/
@[expose] def dalekScalarModVec (v : List.Vector (BitVec 8) 32) : List.Vector (BitVec 8) 32 :=
  ⟨natToLeBytes 32 (leBytesToNat v.toList % edOrderL), by simp [natToLeBytes]⟩

/-- Pure `Scalar::from_bytes_mod_order_wide` vector function (`64` bytes → `32` bytes). -/
@[expose] def dalekScalarWideVec (v : List.Vector (BitVec 8) 64) : List.Vector (BitVec 8) 32 :=
  ⟨natToLeBytes 32 (leBytesToNat v.toList % edOrderL), by simp [natToLeBytes]⟩

/-- Exact 5-limb `FieldElement51::neg` (`16 * p25519 - a`, followed by weak reduction) on the
    40-byte field element at byte offset `off` in `bs`. Matches `DalekEdNeg.fe51NegBytesAt`. -/
@[expose] def fe51NegBytesAt (bs : List (BitVec 8)) (off : Nat) : List (BitVec 8) :=
  let l0 := ByteSlice.readLE bs off 8
  let l1 := ByteSlice.readLE bs (off + 8) 8
  let l2 := ByteSlice.readLE bs (off + 16) 8
  let l3 := ByteSlice.readLE bs (off + 24) 8
  let l4 := ByteSlice.readLE bs (off + 32) 8
  let d0 := 36028797018963664#64 - l0
  let d1 := 36028797018963952#64 - l1
  let d2 := 36028797018963952#64 - l2
  let d3 := 36028797018963952#64 - l3
  let d4 := 36028797018963952#64 - l4
  let r0 := (d0 &&& 2251799813685247#64) + (d4 >>> 51) * 19#64
  let r1 := (d1 &&& 2251799813685247#64) + (d0 >>> 51)
  let r2 := (d2 &&& 2251799813685247#64) + (d1 >>> 51)
  let r3 := (d3 &&& 2251799813685247#64) + (d2 >>> 51)
  let r4 := (d4 &&& 2251799813685247#64) + (d3 >>> 51)
  packFe51Bytes r0 r1 r2 r3 r4

/-- Exact byte-level action of `curve25519-dalek`'s `<EdwardsPoint as Neg>::neg`, matching
    `DalekEdNeg.dalekEdNegBytes` definitionally (`rfl`). -/
@[expose] def dalekEdNegBytes (bs : List (BitVec 8)) : List (BitVec 8) :=
  fe51NegBytesAt bs 0 ++
    packFe51Bytes
      (ByteSlice.readLE bs 40 8) (ByteSlice.readLE bs 48 8)
      (ByteSlice.readLE bs 56 8) (ByteSlice.readLE bs 64 8)
      (ByteSlice.readLE bs 72 8) ++
    packFe51Bytes
      (ByteSlice.readLE bs 80 8) (ByteSlice.readLE bs 88 8)
      (ByteSlice.readLE bs 96 8) (ByteSlice.readLE bs 104 8)
      (ByteSlice.readLE bs 112 8) ++
    fe51NegBytesAt bs 120

theorem fe51NegBytesAt_length (bs : List (BitVec 8)) (off : Nat) :
    (fe51NegBytesAt bs off).length = 40 :=
  packFe51Bytes_length _ _ _ _ _

theorem dalekEdNegBytes_length (bs : List (BitVec 8)) :
    (dalekEdNegBytes bs).length = 160 := by
  simp only [dalekEdNegBytes, List.length_append, fe51NegBytesAt_length, packFe51Bytes_length]

/-- Vector wrapper for `dalekEdNegBytes` (`160` bytes → `160` bytes). -/
@[expose] def dalekEdNegVec (v : List.Vector (BitVec 8) 160) : List.Vector (BitVec 8) 160 :=
  ⟨dalekEdNegBytes v.toList, dalekEdNegBytes_length v.toList⟩

private theorem readLE_append40_left {xs ys : List (BitVec 8)} (hxs : xs.length = 40)
    (k : Nat) (hk : k + 8 ≤ 40) :
    ByteSlice.readLE (xs ++ ys) k 8 = ByteSlice.readLE xs k 8 := by
  apply readLE_congr_off
  intro i hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega)]

private theorem readLE_append40_right {xs ys : List (BitVec 8)} (hxs : xs.length = 40)
    (off : Nat) :
    ByteSlice.readLE (xs ++ ys) (40 + off) 8 = ByteSlice.readLE ys off 8 := by
  apply readLE_congr_off
  intro i _hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  congr 2
  omega

private theorem bv64_sub_const_toNat {c l : BitVec 64} (hle : l.toNat ≤ c.toNat) :
    (c - l).toNat = c.toNat - l.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)

private theorem bv64_and_mask51_toNat (d : BitVec 64) :
    (d &&& 2251799813685247#64).toNat = d.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and]
  change d.toNat &&& (2 ^ 51 - 1) = d.toNat % 2 ^ 51
  exact Nat.and_two_pow_sub_one_eq_mod d.toNat 51

private theorem bv64_ushr51_toNat (d : BitVec 64) :
    (d >>> 51).toNat = d.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bv64_mul19_toNat {x : BitVec 64} (hx : x.toNat ≤ 16) :
    (x * 19#64).toNat = x.toNat * 19 := by
  rw [BitVec.toNat_mul]
  change (x.toNat * 19) % 2 ^ 64 = x.toNat * 19
  exact Nat.mod_eq_of_lt (by omega)

private theorem bv64_add_small_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem fe51NegNat_linear
    (n0 n1 n2 n3 n4 q0 m0 q1 m1 q2 m2 q3 m3 q4 m4 : Nat)
    (hn0 : n0 < 2 ^ 54) (hn1 : n1 < 2 ^ 54) (hn2 : n2 < 2 ^ 54)
    (hn3 : n3 < 2 ^ 54) (hn4 : n4 < 2 ^ 54)
    (hm0 : m0 < 2 ^ 51) (hm1 : m1 < 2 ^ 51) (hm2 : m2 < 2 ^ 51)
    (hm3 : m3 < 2 ^ 51) (hm4 : m4 < 2 ^ 51)
    (hd0 : 2 ^ 51 * q0 + m0 = 36028797018963664 - n0)
    (hd1 : 2 ^ 51 * q1 + m1 = 36028797018963952 - n1)
    (hd2 : 2 ^ 51 * q2 + m2 = 36028797018963952 - n2)
    (hd3 : 2 ^ 51 * q3 + m3 = 36028797018963952 - n3)
    (hd4 : 2 ^ 51 * q4 + m4 = 36028797018963952 - n4) :
    m0 + q4 * 19 < 2 ^ 52 ∧
    m1 + q0 < 2 ^ 52 ∧
    m2 + q1 < 2 ^ 52 ∧
    m3 + q2 < 2 ^ 52 ∧
    m4 + q3 < 2 ^ 52 ∧
    q4 ≤ 16 ∧
    ((m0 + q4 * 19) + (m1 + q0) * 2 ^ 51 + (m2 + q1) * 2 ^ 102 +
      (m3 + q2) * 2 ^ 153 + (m4 + q3) * 2 ^ 204) +
      (n0 + n1 * 2 ^ 51 + n2 * 2 ^ 102 + n3 * 2 ^ 153 + n4 * 2 ^ 204) =
      (16 - q4) * p25519 := by
  unfold p25519
  omega

private theorem mod_neg_of_add_mul_p25519 (R V k : Nat) (hsum : R + V = k * p25519) :
    R % p25519 = fpNeg (V % p25519) := by
  have hp_pos : 0 < p25519 := p25519_pos
  have hmod_sum : (R + V) % p25519 = 0 := by
    rw [hsum, Nat.mul_mod_left]
  unfold fpNeg
  set r := R % p25519
  set v := V % p25519
  have hr : r < p25519 := Nat.mod_lt R hp_pos
  have hv : v < p25519 := Nat.mod_lt V hp_pos
  rw [Nat.mod_eq_of_lt hv]
  have hadd_mod : (r + v) % p25519 = 0 := by
    dsimp only [r, v]
    rw [← Nat.add_mod, hmod_sum]
  by_cases hv0 : v = 0
  · rw [hv0] at hadd_mod ⊢
    rw [Nat.add_zero, Nat.mod_eq_of_lt hr] at hadd_mod
    rw [hadd_mod, Nat.sub_zero, Nat.mod_self]
  · have hge : p25519 ≤ r + v := by
      by_contra hlt
      have hm : (r + v) % p25519 = r + v := Nat.mod_eq_of_lt (by omega)
      omega
    have hsub_lt : r + v - p25519 < p25519 := by omega
    have hsplit : r + v = (r + v - p25519) + p25519 := by omega
    rw [hsplit, Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt] at hadd_mod
    have hr_eq : r = p25519 - v := by omega
    rw [hr_eq, Nat.mod_eq_of_lt (by omega)]

private theorem bv64_neg_sub_limb {c l : BitVec 64} (hle : l.toNat ≤ c.toNat) :
    2 ^ 51 * ((c - l).toNat / 2 ^ 51) + (c - l).toNat % 2 ^ 51 = c.toNat - l.toNat := by
  rw [Nat.div_add_mod, bv64_sub_const_toNat hle]

private theorem fe51NegLimbs_bounded_and_val (l0 l1 l2 l3 l4 : BitVec 64)
    (h0 : l0.toNat < 2 ^ 54) (h1 : l1.toNat < 2 ^ 54) (h2 : l2.toNat < 2 ^ 54)
    (h3 : l3.toNat < 2 ^ 54) (h4 : l4.toNat < 2 ^ 54) :
    let d0 := 36028797018963664#64 - l0
    let d1 := 36028797018963952#64 - l1
    let d2 := 36028797018963952#64 - l2
    let d3 := 36028797018963952#64 - l3
    let d4 := 36028797018963952#64 - l4
    let r0 := (d0 &&& 2251799813685247#64) + (d4 >>> 51) * 19#64
    let r1 := (d1 &&& 2251799813685247#64) + (d0 >>> 51)
    let r2 := (d2 &&& 2251799813685247#64) + (d1 >>> 51)
    let r3 := (d3 &&& 2251799813685247#64) + (d2 >>> 51)
    let r4 := (d4 &&& 2251799813685247#64) + (d3 >>> 51)
    let out := packFe51Bytes r0 r1 r2 r3 r4
    fe51LimbsBounded out (2 ^ 52) ∧
    fe51ValOfBytes out % p25519 = fpNeg (fe51Val l0 l1 l2 l3 l4 % p25519) := by
  have hle54_0 : l0.toNat ≤ (36028797018963664#64).toNat :=
    Nat.le_of_lt (Nat.lt_of_lt_of_le h0 (by decide))
  have hle54_1 : l1.toNat ≤ (36028797018963952#64).toNat :=
    Nat.le_of_lt (Nat.lt_of_lt_of_le h1 (by decide))
  have hle54_2 : l2.toNat ≤ (36028797018963952#64).toNat :=
    Nat.le_of_lt (Nat.lt_of_lt_of_le h2 (by decide))
  have hle54_3 : l3.toNat ≤ (36028797018963952#64).toNat :=
    Nat.le_of_lt (Nat.lt_of_lt_of_le h3 (by decide))
  have hle54_4 : l4.toNat ≤ (36028797018963952#64).toNat :=
    Nat.le_of_lt (Nat.lt_of_lt_of_le h4 (by decide))
  have hpow51 : 0 < 2 ^ 51 := by decide
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hq4, hsum⟩ := fe51NegNat_linear
    l0.toNat l1.toNat l2.toNat l3.toNat l4.toNat
    ((36028797018963664#64 - l0).toNat / 2 ^ 51) ((36028797018963664#64 - l0).toNat % 2 ^ 51)
    ((36028797018963952#64 - l1).toNat / 2 ^ 51) ((36028797018963952#64 - l1).toNat % 2 ^ 51)
    ((36028797018963952#64 - l2).toNat / 2 ^ 51) ((36028797018963952#64 - l2).toNat % 2 ^ 51)
    ((36028797018963952#64 - l3).toNat / 2 ^ 51) ((36028797018963952#64 - l3).toNat % 2 ^ 51)
    ((36028797018963952#64 - l4).toNat / 2 ^ 51) ((36028797018963952#64 - l4).toNat % 2 ^ 51)
    h0 h1 h2 h3 h4
    (Nat.mod_lt _ hpow51) (Nat.mod_lt _ hpow51) (Nat.mod_lt _ hpow51)
    (Nat.mod_lt _ hpow51) (Nat.mod_lt _ hpow51)
    (bv64_neg_sub_limb hle54_0) (bv64_neg_sub_limb hle54_1) (bv64_neg_sub_limb hle54_2)
    (bv64_neg_sub_limb hle54_3) (bv64_neg_sub_limb hle54_4)
  intro d0 d1 d2 d3 d4 r0 r1 r2 r3 r4 out
  have hd4_div : (d4 >>> 51).toNat ≤ 16 := by rw [bv64_ushr51_toNat]; exact hq4
  have hr0 : r0.toNat = d0.toNat % 2 ^ 51 + (d4.toNat / 2 ^ 51) * 19 := by
    dsimp only [r0]
    rw [bv64_add_small_toNat (by
      rw [bv64_and_mask51_toNat, bv64_mul19_toNat hd4_div, bv64_ushr51_toNat]
      exact Nat.lt_trans hb0 (by decide)),
      bv64_and_mask51_toNat, bv64_mul19_toNat hd4_div, bv64_ushr51_toNat]
  have hr1 : r1.toNat = d1.toNat % 2 ^ 51 + d0.toNat / 2 ^ 51 := by
    dsimp only [r1]
    rw [bv64_add_small_toNat (by
      rw [bv64_and_mask51_toNat, bv64_ushr51_toNat]; exact Nat.lt_trans hb1 (by decide)),
      bv64_and_mask51_toNat, bv64_ushr51_toNat]
  have hr2 : r2.toNat = d2.toNat % 2 ^ 51 + d1.toNat / 2 ^ 51 := by
    dsimp only [r2]
    rw [bv64_add_small_toNat (by
      rw [bv64_and_mask51_toNat, bv64_ushr51_toNat]; exact Nat.lt_trans hb2 (by decide)),
      bv64_and_mask51_toNat, bv64_ushr51_toNat]
  have hr3 : r3.toNat = d3.toNat % 2 ^ 51 + d2.toNat / 2 ^ 51 := by
    dsimp only [r3]
    rw [bv64_add_small_toNat (by
      rw [bv64_and_mask51_toNat, bv64_ushr51_toNat]; exact Nat.lt_trans hb3 (by decide)),
      bv64_and_mask51_toNat, bv64_ushr51_toNat]
  have hr4 : r4.toNat = d4.toNat % 2 ^ 51 + d3.toNat / 2 ^ 51 := by
    dsimp only [r4]
    rw [bv64_add_small_toNat (by
      rw [bv64_and_mask51_toNat, bv64_ushr51_toNat]; exact Nat.lt_trans hb4 (by decide)),
      bv64_and_mask51_toNat, bv64_ushr51_toNat]
  refine ⟨?_, ?_⟩
  · dsimp only [out, fe51LimbsBounded]
    rw [packFe51Bytes_length, readLE_packFe51Bytes_0, readLE_packFe51Bytes_8,
      readLE_packFe51Bytes_16, readLE_packFe51Bytes_24, readLE_packFe51Bytes_32,
      hr0, hr1, hr2, hr3, hr4]
    exact ⟨rfl, hb0, hb1, hb2, hb3, hb4⟩
  · dsimp only [out, fe51ValOfBytes, fe51ValAt, fe51Val]
    rw [readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
      readLE_packFe51Bytes_24, readLE_packFe51Bytes_32,
      hr0, hr1, hr2, hr3, hr4]
    exact mod_neg_of_add_mul_p25519 _ _ (16 - d4.toNat / 2 ^ 51) hsum

private theorem fe51NegBytesAt_bounded_and_val {bs : List (BitVec 8)} {off : Nat}
    (hb : fe51LimbsBoundedAt bs off (2 ^ 54)) :
    fe51LimbsBounded (fe51NegBytesAt bs off) (2 ^ 52) ∧
    fe51ValOfBytes (fe51NegBytesAt bs off) % p25519 = fpNeg (fe51ValAt bs off % p25519) := by
  rcases hb with ⟨h0, h1, h2, h3, h4⟩
  exact fe51NegLimbs_bounded_and_val
    (ByteSlice.readLE bs off 8) (ByteSlice.readLE bs (off + 8) 8)
    (ByteSlice.readLE bs (off + 16) 8) (ByteSlice.readLE bs (off + 24) 8)
    (ByteSlice.readLE bs (off + 32) 8) h0 h1 h2 h3 h4

section IrreducibleNegHelpers
attribute [local irreducible] fe51NegBytesAt packFe51Bytes

/-- `dalekEdNegBytes` preserves `< 2 ^ 52` limb bounds when `X` and `T` are `< 2 ^ 54` and `Y` and
    `Z` are `< 2 ^ 52` (in particular whenever `fe51Point4Bounded bs (2 ^ 52)` holds). -/
theorem dalekEdNegBytes_bounded {bs : List (BitVec 8)}
    (hb : fe51Point4Bounded bs (2 ^ 52)) :
    fe51Point4Bounded (dalekEdNegBytes bs) (2 ^ 52) := by
  rcases hb with ⟨_hlen, hx, hy, hz, ht⟩
  have hx' := (fe51NegBytesAt_bounded_and_val (fe51LimbsBoundedAt_mono hx (by decide))).1
  have ht' := (fe51NegBytesAt_bounded_and_val (fe51LimbsBoundedAt_mono ht (by decide))).1
  let c0 := fe51NegBytesAt bs 0
  let c1 := packFe51Bytes (ByteSlice.readLE bs 40 8) (ByteSlice.readLE bs 48 8)
    (ByteSlice.readLE bs 56 8) (ByteSlice.readLE bs 64 8) (ByteSlice.readLE bs 72 8)
  let c2 := packFe51Bytes (ByteSlice.readLE bs 80 8) (ByteSlice.readLE bs 88 8)
    (ByteSlice.readLE bs 96 8) (ByteSlice.readLE bs 104 8) (ByteSlice.readLE bs 112 8)
  let c3 := fe51NegBytesAt bs 120
  have heq : dalekEdNegBytes bs = c0 ++ (c1 ++ (c2 ++ c3)) := by
    dsimp only [dalekEdNegBytes, c0, c1, c2, c3]
    simp only [List.append_assoc]
  have hc0 : c0.length = 40 := fe51NegBytesAt_length bs 0
  have hc1 : c1.length = 40 := packFe51Bytes_length _ _ _ _ _
  have hc2 : c2.length = 40 := packFe51Bytes_length _ _ _ _ _
  refine ⟨dalekEdNegBytes_length bs, ?_, ?_, ?_, ?_⟩
  · rw [heq]; dsimp only [fe51LimbsBoundedAt]; simp only [Nat.zero_add]
    rw [readLE_append40_left hc0 0 (by decide), readLE_append40_left hc0 8 (by decide),
      readLE_append40_left hc0 16 (by decide), readLE_append40_left hc0 24 (by decide),
      readLE_append40_left hc0 32 (by decide)]
    exact hx'.2
  · rw [heq]; dsimp only [fe51LimbsBoundedAt]
    rw [show (40 : Nat) = 40 + 0 from rfl, readLE_append40_right hc0 0,
      readLE_append40_right hc0 8, readLE_append40_right hc0 16,
      readLE_append40_right hc0 24, readLE_append40_right hc0 32,
      readLE_append40_left hc1 0 (by decide), readLE_append40_left hc1 8 (by decide),
      readLE_append40_left hc1 16 (by decide), readLE_append40_left hc1 24 (by decide),
      readLE_append40_left hc1 32 (by decide)]
    dsimp only [c1]
    rw [readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
      readLE_packFe51Bytes_24, readLE_packFe51Bytes_32]
    exact hy
  · rw [heq]; dsimp only [fe51LimbsBoundedAt]
    have h80 : ∀ k, ByteSlice.readLE (c0 ++ (c1 ++ (c2 ++ c3))) (80 + k) 8 =
        ByteSlice.readLE (c2 ++ c3) k 8 := fun k => by
      rw [show 80 + k = 40 + (40 + k) by omega,
        readLE_append40_right hc0 (40 + k), readLE_append40_right hc1 k]
    rw [show (80 : Nat) = 80 + 0 from rfl, h80 0,
      show 80 + 0 + 8 = 80 + 8 from rfl, h80 8,
      show 80 + 0 + 16 = 80 + 16 from rfl, h80 16,
      show 80 + 0 + 24 = 80 + 24 from rfl, h80 24,
      show 80 + 0 + 32 = 80 + 32 from rfl, h80 32,
      readLE_append40_left hc2 0 (by decide), readLE_append40_left hc2 8 (by decide),
      readLE_append40_left hc2 16 (by decide), readLE_append40_left hc2 24 (by decide),
      readLE_append40_left hc2 32 (by decide)]
    dsimp only [c2]
    rw [readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
      readLE_packFe51Bytes_24, readLE_packFe51Bytes_32]
    exact hz
  · rw [heq]; dsimp only [fe51LimbsBoundedAt]
    have h120 : ∀ k, ByteSlice.readLE (c0 ++ (c1 ++ (c2 ++ c3))) (120 + k) 8 =
        ByteSlice.readLE c3 k 8 := fun k => by
      rw [show 120 + k = 40 + (40 + (40 + k)) by omega,
        readLE_append40_right hc0 _, readLE_append40_right hc1 _, readLE_append40_right hc2 k]
    rw [show (120 : Nat) = 120 + 0 from rfl, h120 0,
      show 120 + 0 + 8 = 120 + 8 from rfl, h120 8,
      show 120 + 0 + 16 = 120 + 16 from rfl, h120 16,
      show 120 + 0 + 24 = 120 + 24 from rfl, h120 24,
      show 120 + 0 + 32 = 120 + 32 from rfl, h120 32]
    exact ht'.2

/-- `dalekEdNegBytes` computes `edExtNeg (edExtOfBytes bs)` on any `< 2 ^ 54` limb-bounded point. -/
theorem dalekEdNegBytes_edExtOfBytes {bs : List (BitVec 8)}
    (hb : fe51Point4Bounded bs (2 ^ 54)) :
    edExtOfBytes (dalekEdNegBytes bs) = edExtNeg (edExtOfBytes bs) := by
  rcases hb with ⟨_hlen, hx, _hy, _hz, ht⟩
  have hx_val := (fe51NegBytesAt_bounded_and_val hx).2
  have ht_val := (fe51NegBytesAt_bounded_and_val ht).2
  let c0 := fe51NegBytesAt bs 0
  let c1 := packFe51Bytes (ByteSlice.readLE bs 40 8) (ByteSlice.readLE bs 48 8)
    (ByteSlice.readLE bs 56 8) (ByteSlice.readLE bs 64 8) (ByteSlice.readLE bs 72 8)
  let c2 := packFe51Bytes (ByteSlice.readLE bs 80 8) (ByteSlice.readLE bs 88 8)
    (ByteSlice.readLE bs 96 8) (ByteSlice.readLE bs 104 8) (ByteSlice.readLE bs 112 8)
  let c3 := fe51NegBytesAt bs 120
  have heq : dalekEdNegBytes bs = c0 ++ (c1 ++ (c2 ++ c3)) := by
    dsimp only [dalekEdNegBytes, c0, c1, c2, c3]
    simp only [List.append_assoc]
  have hc0 : c0.length = 40 := fe51NegBytesAt_length bs 0
  have hc1 : c1.length = 40 := packFe51Bytes_length _ _ _ _ _
  have hc2 : c2.length = 40 := packFe51Bytes_length _ _ _ _ _
  dsimp only [edExtOfBytes, edExtNeg]
  rw [heq]
  have hX : fe51ValAt (c0 ++ (c1 ++ (c2 ++ c3))) 0 = fe51ValOfBytes c0 := by
    dsimp only [fe51ValAt, fe51ValOfBytes]; simp only [Nat.zero_add]
    rw [readLE_append40_left hc0 0 (by decide), readLE_append40_left hc0 8 (by decide),
      readLE_append40_left hc0 16 (by decide), readLE_append40_left hc0 24 (by decide),
      readLE_append40_left hc0 32 (by decide)]
  have hY : fe51ValAt (c0 ++ (c1 ++ (c2 ++ c3))) 40 = fe51ValAt bs 40 := by
    dsimp only [fe51ValAt]
    rw [show (40 : Nat) = 40 + 0 from rfl, readLE_append40_right hc0 0,
      readLE_append40_right hc0 8, readLE_append40_right hc0 16,
      readLE_append40_right hc0 24, readLE_append40_right hc0 32,
      readLE_append40_left hc1 0 (by decide), readLE_append40_left hc1 8 (by decide),
      readLE_append40_left hc1 16 (by decide), readLE_append40_left hc1 24 (by decide),
      readLE_append40_left hc1 32 (by decide)]
    dsimp only [c1]
    rw [readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
      readLE_packFe51Bytes_24, readLE_packFe51Bytes_32]
  have hZ : fe51ValAt (c0 ++ (c1 ++ (c2 ++ c3))) 80 = fe51ValAt bs 80 := by
    dsimp only [fe51ValAt]
    have h80 : ∀ k, ByteSlice.readLE (c0 ++ (c1 ++ (c2 ++ c3))) (80 + k) 8 =
        ByteSlice.readLE (c2 ++ c3) k 8 := fun k => by
      rw [show 80 + k = 40 + (40 + k) by omega,
        readLE_append40_right hc0 (40 + k), readLE_append40_right hc1 k]
    rw [show (80 : Nat) = 80 + 0 from rfl, h80 0,
      show 80 + 0 + 8 = 80 + 8 from rfl, h80 8,
      show 80 + 0 + 16 = 80 + 16 from rfl, h80 16,
      show 80 + 0 + 24 = 80 + 24 from rfl, h80 24,
      show 80 + 0 + 32 = 80 + 32 from rfl, h80 32,
      readLE_append40_left hc2 0 (by decide), readLE_append40_left hc2 8 (by decide),
      readLE_append40_left hc2 16 (by decide), readLE_append40_left hc2 24 (by decide),
      readLE_append40_left hc2 32 (by decide)]
    dsimp only [c2]
    rw [readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
      readLE_packFe51Bytes_24, readLE_packFe51Bytes_32]
  have hT : fe51ValAt (c0 ++ (c1 ++ (c2 ++ c3))) 120 = fe51ValOfBytes c3 := by
    dsimp only [fe51ValAt, fe51ValOfBytes]
    have h120 : ∀ k, ByteSlice.readLE (c0 ++ (c1 ++ (c2 ++ c3))) (120 + k) 8 =
        ByteSlice.readLE c3 k 8 := fun k => by
      rw [show 120 + k = 40 + (40 + (40 + k)) by omega,
        readLE_append40_right hc0 _, readLE_append40_right hc1 _, readLE_append40_right hc2 k]
    rw [show (120 : Nat) = 120 + 0 from rfl, h120 0,
      show 120 + 0 + 8 = 120 + 8 from rfl, h120 8,
      show 120 + 0 + 16 = 120 + 16 from rfl, h120 16,
      show 120 + 0 + 24 = 120 + 24 from rfl, h120 24,
      show 120 + 0 + 32 = 120 + 32 from rfl, h120 32]
  rw [hX, hY, hZ, hT, hx_val, ht_val]
  simp only [Nat.mod_mod]

end IrreducibleNegHelpers

/-! ## 4. Consumer `CliExt` Pure-Byte-Function Bridges (`B01`, `B02`) -/

private theorem scalarMod_simulates_cliExt (byVal : Bool) :
    SpecSimulates (Spec.withTraceEq scalarFromBytesModOrderSpec)
      (pureByteFunctionSpec dalekScalarModVec byVal) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨inA, v, ret⟩ R s0 hpre
  dsimp only [pureByteFunctionSpec, CryptoVerification.SignalSession.CliExt.withStack] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8⟩, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes ret 32 (by decide),
    stackAt_shrink s0.sp extHookStack 208 (by decide) (by decide),
    stackAt_eq_stackFrameAt s0.sp 208 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨out_bs, hpre⟩ := hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (inA ↦ₛ v.toList) ⌜out_bs.length = 32⌝, satisfies_pure_sepConj] at hpre
  obtain ⟨hout_len, hpre⟩ := hpre
  refine ⟨(ret, inA, out_bs, v.toList),
    memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 208) ∗ R, ?_, ?_⟩
  · dsimp only [Spec.withTraceEq, scalarFromBytesModOrderSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hout_len, v.2⟩, Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret hcc hpost
    dsimp only [Spec.withTraceEq, scalarFromBytesModOrderSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hpost⟩ := hpost
    have hsf_frame : stackFrame sf 208 = stackFrameAt s0.sp 208 := by
      unfold stackFrame
      rw [hcc.1]
      exact stackAt_eq_stackFrameAt s0.sp 208 (by decide)
    rw [hsf_frame] at hpost
    dsimp only [pureByteFunctionSpec, CryptoVerification.SignalSession.CliExt.withStack,
      dalekScalarModVec, List.Vector.toList]
    rw [stackAt_shrink s0.sp extHookStack 208 (by decide) (by decide),
      stackAt_eq_stackFrameAt s0.sp 208 (by decide)]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    cases byVal
    · simp only [inputAfter, Bool.false_eq_true, ↓reduceIte]
      exact Satisfies.mono (by sep_entail) hpost
    · simp only [inputAfter, ↓reduceIte]
      have hin_reg : (inA ↦ₛ v.toList) ⊢ memRegion inA 32 :=
        pointsToBytes_entails_memRegion_of_length v.2
      have hreord : sf.mem ⊨ (inA ↦ₛ v.toList) ∗
          (ret ↦ₛ natToLeBytes 32 (leBytesToNat v.toList % edOrderL)) ∗
          memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 208) ∗
          stackFrameAt s0.sp 208 ∗ R :=
        Satisfies.mono (by sep_entail) hpost
      have hfolded := Satisfies.mono (sepConj_mono hin_reg (Entails.refl _)) hreord
      exact Satisfies.mono (by sep_entail) hfolded

private theorem map_nonReturn_outcome {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    {y : β} {R : SepProp} {s0 sf : State}
    (hpan : spec₂.onPanic = (spec₁.onPanic |> fun _ => spec₂.onPanic) := rfl)
    (hout : sf.status = .Panicked ∧ sf.mem ⊨ spec₂.onPanic y s0 sf ∗ R ∨
      (∃ c, sf.status = .Exited c ∧ sf.mem ⊨ spec₂.onExit y c s0 sf ∗ R) ∨
      sf.status = .OutOfMemory ∧ sf.mem ⊨ spec₂.onOom y s0 sf ∗ R) :
    SubroutineOutcome (withVmPreserved spec₂) y R s0 sf := by
  let _ := hpan
  exact Or.inr hout

theorem specSimulates_withVmPreserved {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (withVmPreserved spec₁) (withVmPreserved spec₂) := by
  intro y R s0 hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  refine ⟨x, R₁, hpre₁, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hp, hm_p⟩ | ⟨c, he, hm_e⟩ | ⟨ho, hm_o⟩
  · dsimp only [withVmPreserved] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    obtain ⟨hvm, hp⟩ := hp
    rcases hm sf (Or.inl ⟨hret, hcc, hp⟩) with ⟨hret₂, hcc₂, hp₂⟩ | hout₂
    · refine Or.inl ⟨hret₂, hcc₂, ?_⟩
      dsimp only [withVmPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hvm, hp₂⟩
    · exact map_nonReturn_outcome (spec₁ := spec₁) rfl hout₂
  · rcases hm sf (Or.inr (Or.inl ⟨hp, hm_p⟩)) with ⟨hret₂, _, _⟩ | hout₂
    · nomatch hp.symm.trans hret₂.2.2
    · exact map_nonReturn_outcome (spec₁ := spec₁) rfl hout₂
  · rcases hm sf (Or.inr (Or.inr (Or.inl ⟨c, he, hm_e⟩))) with ⟨hret₂, _, _⟩ | hout₂
    · nomatch he.symm.trans hret₂.2.2
    · exact map_nonReturn_outcome (spec₁ := spec₁) rfl hout₂
  · rcases hm sf (Or.inr (Or.inr (Or.inr ⟨ho, hm_o⟩))) with ⟨hret₂, _, _⟩ | hout₂
    · nomatch ho.symm.trans hret₂.2.2
    · exact map_nonReturn_outcome (spec₁ := spec₁) rfl hout₂

theorem specSimulates_keepsFs {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (keepsFs spec₁) (keepsFs spec₂) := by
  intro y R s0 hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  refine ⟨x, R₁, hpre₁, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hp, hm_p⟩ | ⟨c, he, hm_e⟩ | ⟨ho, hm_o⟩
  · dsimp only [keepsFs] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    obtain ⟨hfs, hp⟩ := hp
    rcases hm sf (Or.inl ⟨hret, hcc, hp⟩) with ⟨hret₂, hcc₂, hp₂⟩ | hout₂
    · refine Or.inl ⟨hret₂, hcc₂, ?_⟩
      dsimp only [keepsFs]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hfs, hp₂⟩
    · exact Or.inr hout₂
  · rcases hm sf (Or.inr (Or.inl ⟨hp, hm_p⟩)) with ⟨hret₂, _, _⟩ | hout₂
    · nomatch hp.symm.trans hret₂.2.2
    · exact Or.inr hout₂
  · rcases hm sf (Or.inr (Or.inr (Or.inl ⟨c, he, hm_e⟩))) with ⟨hret₂, _, _⟩ | hout₂
    · nomatch he.symm.trans hret₂.2.2
    · exact Or.inr hout₂
  · rcases hm sf (Or.inr (Or.inr (Or.inr ⟨ho, hm_o⟩))) with ⟨hret₂, _, _⟩ | hout₂
    · nomatch ho.symm.trans hret₂.2.2
    · exact Or.inr hout₂

private theorem specSimulates_comm_traceEq_keepsFs_vm {α : Type} (spec : Spec α) :
    SpecSimulates
      (Spec.withTraceEq (keepsFs (withVmPreserved spec)))
      (keepsFs (withVmPreserved (Spec.withTraceEq spec))) := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hm_p⟩ | ⟨c, he, hm_e⟩ | ⟨ho, hm_o⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.withTraceEq, keepsFs, withVmPreserved] at hpost ⊢
    exact Satisfies.mono (by sep_entail) hpost
  · exact Or.inr (Or.inl ⟨hp, hm_p⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hm_e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hm_o⟩))

/-- Consumer `CliExt` discharge for `Scalar::from_bytes_mod_order` (`B01`): satisfies
    `keepsFs (withVmPreserved (pureByteFunctionSpec dalekScalarModVec byVal))` under any
    extern table `externs`. -/
theorem scalarFromBytesModOrder_cliExt_subroutineOk_of
    (hok : ScalarFromBytesModOrderOk) (byVal : Bool)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order"
      (fun _ => keepsFs (withVmPreserved (pureByteFunctionSpec dalekScalarModVec byVal)))
      externs := by
  have htr := dalekSubroutineOk_const_withTraceEq_keepsFs_vmPreserved
    "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order" hok externs
  refine SpecSimulates.multiSubroutineOk (fun _ => ?_) htr
  exact (specSimulates_comm_traceEq_keepsFs_vm scalarFromBytesModOrderSpec).trans
    (specSimulates_keepsFs (specSimulates_withVmPreserved (scalarMod_simulates_cliExt byVal)))

private theorem specSimulates_withRoOk_idem {α : Type} {RoOk : Memory → Prop} {spec : Spec α} :
    SpecSimulates (withRoOk RoOk (withRoOk RoOk spec)) (withRoOk RoOk spec) := by
  intro x R s0 hpre
  dsimp only [withRoOk] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro, hpre⟩ := hpre
  refine ⟨x, R, ?_, fun _ hout => hout⟩
  dsimp only [withRoOk]
  simp only [sepConj_assoc]
  rw [satisfies_pure_sepConj]
  refine ⟨hro, ?_⟩
  rw [satisfies_pure_sepConj]
  exact ⟨hro, hpre⟩

private theorem specSimulates_withRoOk_map {α β : Type} {RoOk : Memory → Prop}
    {spec₁ : Spec α} {spec₂ : Spec β} (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (withRoOk RoOk spec₁) (withRoOk RoOk spec₂) := by
  intro y R s0 hpre
  dsimp only [withRoOk] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro, hpre⟩ := hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  refine ⟨x, R₁, ?_, hm⟩
  dsimp only [withRoOk]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hro, hpre₁⟩

private theorem scalarWide_simulates_cliExt (mpl : MultiPlacement) (byVal : Bool) :
    SpecSimulates (Spec.withTraceEq (scalarFromBytesModOrderWideSpec mpl))
      (withRoOk (DalekCliRoOk mpl) (pureByteFunctionSpec dalekScalarWideVec byVal)) := by
  let S₀ := withRoOk (DalekCliRoOk mpl) (pureByteFunctionSpec dalekScalarWideVec byVal)
  let S₁ := withRoDataSep (sc52_rr mpl) sc52RRBytes S₀
  have hcore : SpecSimulates (Spec.withTraceEq (scalarFromBytesModOrderWideSpec mpl))
      (withRoDataSep (sc52_l mpl) sc52LBytes (withRoOk (DalekCliRoOk mpl) S₁)) := by
    refine SpecSimulates.of_map ?_
    rintro ⟨inA, v, ret⟩ R s0 hpre
    dsimp only [S₁, S₀, withRoDataSep, withRoOk, pureByteFunctionSpec,
      CryptoVerification.SignalSession.CliExt.withStack] at hpre
    simp only [sepConj_assoc] at hpre
    rw [sepConj_left_comm (sc52_l mpl ↦ᵣ sc52LBytes) ⌜DalekCliRoOk mpl s0.mem⌝,
      satisfies_pure_sepConj] at hpre
    obtain ⟨_hro1, hpre⟩ := hpre
    rw [sepConj_left_comm (sc52_rr mpl ↦ᵣ sc52RRBytes) ⌜DalekCliRoOk mpl s0.mem⌝,
      sepConj_left_comm (sc52_l mpl ↦ᵣ sc52LBytes) ⌜DalekCliRoOk mpl s0.mem⌝,
      satisfies_pure_sepConj] at hpre
    obtain ⟨_hro2, hpre⟩ := hpre
    rw [sepConj_left_comm (sc52_rr mpl ↦ᵣ sc52RRBytes) ⌜_ ∧ _⌝,
      sepConj_left_comm (sc52_l mpl ↦ᵣ sc52LBytes) ⌜_ ∧ _⌝,
      satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx8⟩, hpre⟩ := hpre
    rw [memRegion_eq_exists_bytes ret 32 (by decide),
      stackAt_shrink s0.sp extHookStack 448 (by decide) (by decide),
      stackAt_eq_stackFrameAt s0.sp 448 (by decide)] at hpre
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
    obtain ⟨out_bs, hpre⟩ := hpre
    simp only [sepConj_assoc] at hpre
    rw [sepConj_left_comm (inA ↦ₛ v.toList) ⌜out_bs.length = 32⌝,
      sepConj_left_comm (sc52_rr mpl ↦ᵣ sc52RRBytes) ⌜out_bs.length = 32⌝,
      sepConj_left_comm (sc52_l mpl ↦ᵣ sc52LBytes) ⌜out_bs.length = 32⌝,
      satisfies_pure_sepConj] at hpre
    obtain ⟨hout_len, hpre⟩ := hpre
    refine ⟨(ret, inA, out_bs, v.toList),
      memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 448) ∗ R, ?_, ?_⟩
    · dsimp only [Spec.withTraceEq, scalarFromBytesModOrderWideSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx8, hx0, hout_len, v.2⟩, Satisfies.mono (by sep_entail) hpre⟩
    · intro sf _hret hcc hpost
      dsimp only [Spec.withTraceEq, scalarFromBytesModOrderWideSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨htr, hpost⟩ := hpost
      have hsf_frame : stackFrame sf 448 = stackFrameAt s0.sp 448 := by
        unfold stackFrame
        rw [hcc.1]
        exact stackAt_eq_stackFrameAt s0.sp 448 (by decide)
      rw [hsf_frame] at hpost
      dsimp only [S₁, S₀, withRoDataSep, withRoOk, pureByteFunctionSpec,
        CryptoVerification.SignalSession.CliExt.withStack, dalekScalarWideVec,
        List.Vector.toList]
      rw [stackAt_shrink s0.sp extHookStack 448 (by decide) (by decide),
        stackAt_eq_stackFrameAt s0.sp 448 (by decide)]
      simp only [sepConj_assoc]
      rw [sepConj_left_comm (sc52_rr mpl ↦ᵣ sc52RRBytes) ⌜sf.trace = s0.trace⌝,
        sepConj_left_comm (sc52_l mpl ↦ᵣ sc52LBytes) ⌜sf.trace = s0.trace⌝,
        satisfies_pure_sepConj]
      refine ⟨htr, ?_⟩
      cases byVal
      · simp only [inputAfter, Bool.false_eq_true, ↓reduceIte]
        exact Satisfies.mono (by sep_entail) hpost
      · simp only [inputAfter, ↓reduceIte]
        have hin_reg : (inA ↦ₛ v.toList) ⊢ memRegion inA 64 :=
          pointsToBytes_entails_memRegion_of_length v.2
        have hreord : sf.mem ⊨ (inA ↦ₛ v.toList) ∗
            (sc52_l mpl ↦ᵣ sc52LBytes) ∗ (sc52_rr mpl ↦ᵣ sc52RRBytes) ∗
            (ret ↦ₛ natToLeBytes 32 (leBytesToNat v.toList % edOrderL)) ∗
            memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 448) ∗
            stackFrameAt s0.sp 448 ∗ R :=
          Satisfies.mono (by sep_entail) hpost
        have hfolded := Satisfies.mono (sepConj_mono hin_reg (Entails.refl _)) hreord
        exact Satisfies.mono (by sep_entail) hfolded
  have habs_l :
      SpecSimulates (withRoDataSep (sc52_l mpl) sc52LBytes (withRoOk (DalekCliRoOk mpl) S₁))
        (withRoOk (DalekCliRoOk mpl) S₁) :=
    specSimulates_absorb_roDataSep (by rw [sc52LBytes_length]; decide) (fun _ h => h.ro_sc52_l)
  have habs_rr : SpecSimulates S₁ S₀ :=
    specSimulates_absorb_roDataSep (by rw [sc52RRBytes_length]; decide) (fun _ h => h.ro_sc52_rr)
  exact hcore.trans (habs_l.trans ((specSimulates_withRoOk_map habs_rr).trans specSimulates_withRoOk_idem))

/-- Consumer `CliExt` discharge for `Scalar::from_bytes_mod_order_wide` (`B02`): satisfies
    `withRoOk (DalekCliRoOk mpl) (keepsFs (withVmPreserved (pureByteFunctionSpec dalekScalarWideVec byVal)))`
    under any extern table `externs`. -/
theorem scalarFromBytesModOrderWide_cliExt_subroutineOk_of
    (hok : ScalarFromBytesModOrderWideOk) (byVal : Bool)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide"
      (fun mpl =>
        withRoOk (DalekCliRoOk mpl)
          (keepsFs (withVmPreserved (pureByteFunctionSpec dalekScalarWideVec byVal))))
      externs := by
  have htr := dalekSubroutineOk_withTraceEq_keepsFs_vmPreserved
    "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide" hok externs
  refine SpecSimulates.multiSubroutineOk (fun mpl => ?_) htr
  have h1 := (specSimulates_comm_traceEq_keepsFs_vm (scalarFromBytesModOrderWideSpec mpl)).trans
    (specSimulates_keepsFs (specSimulates_withVmPreserved (scalarWide_simulates_cliExt mpl byVal)))
  exact h1

/-- Export `subtle::black_box::<u8>` (`B00`) as a `dalekCliMultiLib.subroutineOk` contract. -/
theorem blackBoxU8_subroutineOk_of (hok : BlackBoxU8Ok)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "subtle::black_box::<u8>"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved blackBoxU8Spec))) externs :=
  dalekSubroutineOk_const_withTraceEq_keepsFs_vmPreserved "subtle::black_box::<u8>" hok externs

/-- Export `memcpy` (`B36`, mutable source) as a `dalekCliMultiLib.subroutineOk` contract. -/
theorem memcpy_subroutineOk_of (hok : MemcpyOk)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "memcpy"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved memcpySpec))) externs :=
  dalekSubroutineOk_const_withTraceEq_keepsFs_vmPreserved "memcpy" hok externs

/-- Export `memcpy` (`B36`, read-only source) as a `dalekCliMultiLib.subroutineOk` contract. -/
theorem memcpyRo_subroutineOk_of (hok : MemcpyRoOk)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "memcpy"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved memcpyRoSpec))) externs :=
  dalekSubroutineOk_const_withTraceEq_keepsFs_vmPreserved "memcpy" hok externs

/-- Export `<MontgomeryPoint>::to_edwards` (`B08`) as a `dalekCliMultiLib.subroutineOk` contract. -/
theorem montgomeryPointToEdwards_subroutineOk_of (hok : MontgomeryPointToEdwardsOk)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards"
      (fun mpl => Spec.withTraceEq (keepsFs (withVmPreserved (montgomeryPointToEdwardsSpec mpl))))
      externs :=
  dalekSubroutineOk_withTraceEq_keepsFs_vmPreserved
    "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards" hok externs

/-- Export `<EdwardsPoint>::compress` (`B14`) as a `dalekCliMultiLib.subroutineOk` contract. -/
theorem edwardsPointCompress_subroutineOk_of (hok : EdwardsPointCompressOk)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::edwards::EdwardsPoint>::compress"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved edwardsPointCompressSpec))) externs :=
  dalekSubroutineOk_const_withTraceEq_keepsFs_vmPreserved
    "<curve25519_dalek::edwards::EdwardsPoint>::compress" hok externs

/-- Export `<EdwardsPoint>::vartime_double_scalar_mul_basepoint` (`B17`) as a
    `dalekCliMultiLib.subroutineOk` contract. -/
theorem vartimeDoubleScalarMulBasepoint_subroutineOk_of (hok : VartimeDoubleScalarMulBasepointOk)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk
      "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint"
      (fun mpl =>
        Spec.withTraceEq (keepsFs (withVmPreserved (vartimeDoubleScalarMulBasepointSpec mpl))))
      externs :=
  dalekSubroutineOk_withTraceEq_keepsFs_vmPreserved
    "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint" hok externs

/-- Export `<EdwardsPoint>::is_torsion_free` (`B19`) as a `dalekCliMultiLib.subroutineOk` contract. -/
theorem edwardsPointIsTorsionFree_subroutineOk_of (hok : EdwardsPointIsTorsionFreeOk)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free"
      (fun mpl => Spec.withTraceEq (keepsFs (withVmPreserved (edwardsPointIsTorsionFreeSpec mpl))))
      externs :=
  dalekSubroutineOk_withTraceEq_keepsFs_vmPreserved
    "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free" hok externs

/-- Export `<&Scalar as Mul<&EdwardsBasepointTable>>::mul` (`B27`) as a
    `dalekCliMultiLib.subroutineOk` contract. -/
theorem scalarMulBasepointTable_subroutineOk_of (hok : ScalarMulBasepointTableOk)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk
      "<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul<&curve25519_dalek::edwards::EdwardsBasepointTable>>::mul"
      (fun mpl => Spec.withTraceEq (keepsFs (withVmPreserved (scalarMulBasepointTableSpec mpl))))
      externs :=
  dalekSubroutineOk_withTraceEq_keepsFs_vmPreserved
    "<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul<&curve25519_dalek::edwards::EdwardsBasepointTable>>::mul"
    hok externs

/-- Export `<Scalar as Mul>::mul` (`B34`) as a `dalekCliMultiLib.subroutineOk` contract. -/
theorem scalarMulVal_subroutineOk_of (hok : ScalarMulValOk)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved scalarMulSpec))) externs :=
  dalekSubroutineOk_const_withTraceEq_keepsFs_vmPreserved
    "<curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul" hok externs

/-- Export `<Scalar as Add>::add` (`B35`) as a `dalekCliMultiLib.subroutineOk` contract. -/
theorem scalarAddVal_subroutineOk_of (hok : ScalarAddValOk)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved scalarAddSpec))) externs :=
  dalekSubroutineOk_const_withTraceEq_keepsFs_vmPreserved
    "<curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add" hok externs

/-! ## 5. Algebraic Pipeline Soundness Bridges (`<PublicKey>::is_canonical` & XEdDSA) -/

/-- Pipeline 1A (`<PublicKey>::is_canonical`): for any 32-byte input `u_bs` with
    `leBytesToNat u_bs < p25519`, lifting via `montToEdwards u_bs 0` and testing
    `edSmul edOrderL P == edZero` computes `isCanonicalX25519 u_bs` identically. -/
theorem pipeline1_isCanonicalX25519_eq {u_bs : List (BitVec 8)}
    (hlen : u_bs.length = 32) (hlt : leBytesToNat u_bs < p25519) :
    (match montToEdwards u_bs 0 with
     | none => false
     | some P => edSmul edOrderL P == edZero) = isCanonicalX25519 u_bs := by
  simp [isCanonicalX25519, hlen, hlt]
  rfl

/-- Pipeline 1B (8-torsion / RFC 7748 low-order `u`-coordinate characterization): whenever
    `montToEdwards u_bs sign = some P`, `[8]P = edZero` iff `decodeU255 u_bs % p25519 ∈ lowOrderUs`. -/
theorem pipeline1_edSmul_eight_eq_edZero_iff_lowOrderUs {u_bs : List (BitVec 8)} {sign : Nat}
    {P : EdPoint} (hmont : montToEdwards u_bs sign = some P) :
    edSmul 8 P = edZero ↔ decodeU255 u_bs % p25519 ∈ lowOrderUs := by
  have hon := montToEdwards_some_onCurve hmont
  have hu := montToEdwards_some_edToMontU hmont
  rw [edSmul_eight_eq_edZero_iff_lowOrderUs hon, hu]

/-- Pipeline 2 (XEdDSA `verify_signature_multipart` core equation): lifting `pk_bs` with `sign` via
    `montToEdwards`, negating the extended point via `dalekEdNegBytes`, running
    `edDoubleScalarMulBasepoint h_bs negA_bs s_bs`, and compressing via `encodeEd` yields
    `encodeEd ([s]B - [h]A)`. -/
theorem pipeline2_xeddsa_verify_compress_eq
    {pk_bs pt_bs h_bs s_bs : List (BitVec 8)} {sign : Nat} {Apt : EdPoint}
    (hmont : montToEdwards pk_bs sign = some Apt)
    (hpt_bnd : fe51Point4Bounded pt_bs (2 ^ 52))
    (hpt_eq : edExtOfBytes pt_bs = edExtOfAffine Apt)
    (hh_len : h_bs.length = 32) (hh_lt : leBytesToNat h_bs < edOrderL)
    (hs_len : s_bs.length = 32) (hs_lt : leBytesToNat s_bs < edOrderL) :
    encodeEd (edExtToAffine (edDoubleScalarMulBasepoint h_bs (dalekEdNegBytes pt_bs) s_bs)) =
      encodeEd (edSub (edSmul (leBytesToNat s_bs) edBasepoint) (edSmul (leBytesToNat h_bs) Apt)) := by
  have hApt_curve : edOnCurve Apt = true := montToEdwards_some_onCurve hmont
  have hApt_dec : ∃ ed_pk_bs : List (BitVec 8), decodeEdDalek ed_pk_bs = some Apt :=
    ⟨encodeEd Apt, decodeEdDalek_encodeEd hApt_curve⟩
  have hneg_bnd : fe51Point4Bounded (dalekEdNegBytes pt_bs) (2 ^ 52) :=
    dalekEdNegBytes_bounded hpt_bnd
  have hneg_eq : edExtOfBytes (dalekEdNegBytes pt_bs) = edExtNeg (edExtOfAffine Apt) := by
    rw [dalekEdNegBytes_edExtOfBytes (fe51Point4Bounded_mono hpt_bnd (by decide)), hpt_eq]
  exact dsmb_compress_eq h_bs (dalekEdNegBytes pt_bs) s_bs Apt
    hh_len hh_lt hs_len hs_lt hApt_dec hneg_bnd hneg_eq

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges
