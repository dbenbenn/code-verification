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
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs
public import LibsignalBinary.Heap.Iface -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalPqxdh.Model -- proof-setup: allow-public-import
import ProofLib.Hoare.Model
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretMath
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder

/-!
# Consumer-Contract & Algebraic Satisfaction Bridges (`ConsumerBridges`)

Bridges the `x25519CliMultiLib` subroutine contracts (`Shared51.InternalSpecs`) for
`StaticSecret::diffie_hellman` (`Blk17`) and `<PublicKey as From<&StaticSecret>>::from` (`Blk18`)
to consumer-ready `SpecSimulates` and `MultiPlacedLib.subroutineOk` contracts with
`withProcessPreserved`, `withProcessAllocPreserved`, `Spec.withTraceEq`, `keepsFs`,
`withVmPreserved`, and pure `withRoOk (X25519CliRoOk mpl)` `.rodata` preconditions, together with
pure algebraic satisfaction lemmas for `(x25519Ref, x25519PubFromSecretRef)`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.ConsumerBridges

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Process (ElfImage ProcessInputs)
open ProofLib
open Arm64.Obj (MultiPlacement MultiPlacedLib Placement PlacedLib CodeBlock SymDataInfo
  WordPat HoldsBytes ElfMaps lookupBlockSym msrTpidrEl0Pat svc0Pat)
open VerifiedLibraries.Common (
  p25519 edOrderL leBytesToNat natToLeBytes clampScalarBytes clampScalar
  EdPoint edZero edBasepoint edOnCurve edAdd edNeg edSmul
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (
  x25519CliMultiLib x25519CliData00 x25519CliData01 x25519CliData02
  x25519CliMultiLib_patchSafe_svc0 x25519CliMultiLib_patchSafe_msr
  x25519CliMultiLib_blocks_all_externs_empty
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement X25519BlockOk X25519BlockConstOk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  decodeU255 x25519Ladder x25519 x25519Basepoint x25519Pubkey
  x25519_length x25519Pubkey_length
  x25519Ref x25519PubFromSecretRef
  x25519Ref_toList x25519PubFromSecretRef_toList
  clampScalarBytes_ratchet_clampScalar clampScalar_ratchet_clampScalar
  x25519Ref_clampScalar_eq x25519PubFromSecretRef_clampScalar_eq
  montToEdwards isCanonicalX25519 lowOrderUs
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  fe51_one fe51_mont_a24 ed25519_basepoint_table
  fe51OneBytes fe51MontA24Bytes ed25519BasepointTableBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables (
  fe51OneBytes_length fe51MontA24Bytes_length ed25519BasepointTableBytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  clampScalarBytes_length_of_eq32
  staticSecretDiffieHellmanSpec StaticSecretDiffieHellmanOk
  publicKeyFromSecretSpec PublicKeyFromStaticSecretOk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  p25519_pos
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.PointCodec (
  leBytesToNat_nil leBytesToNat_cons leBytesToNat_natToLeBytes_of_lt edOrderL_pos
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  edOnCurve_edBasepoint edOnCurve_edZero edAdd_comm edAdd_edZero edZero_edAdd edAdd_edNeg_self
  edAdd_assoc edOnCurve_edNeg
  edNatSmul edNatSmul_zero edNatSmul_succ edOnCurve_edNatSmul edNatSmul_edZero
  edNatSmul_add edNatSmul_mul edSmul_eq_edNatSmul edOrderL_lt_two_pow_256
  edNatSmul_mod_edOrderL_edBasepoint
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  edToMontU edToMontU_lt montToEdwards_some_onCurve montToEdwards_some_edToMontU
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretMath (
  x25519Pubkey_not_lowOrder x25519PubFromSecretRef_not_lowOrder
  isCanonicalX25519_x25519Pubkey
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder (
  x25519Ladder_edToMontU clampScalar_lt_two_pow_255
  x25519_uCoord_congr x25519Pubkey_eq_edNatSmul
  x25519_comm x25519Ref_comm
  x25519_eq_zero_iff_lowOrder x25519Ref_eq_zero_iff_lowOrder
  x25519_pub_ne_zero
  isCanonicalX25519_x25519
  edToMontU_edNeg_of_onCurve edToMontU_edSmul_edBasepoint_eq_iff
)
open LibsignalBinary.Heap (AllocCallPreserved FdsHiFrame PoolPreserved VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (
  RoDataAt withRoData withRoDataSep SpecSimulates
)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (dhSpec pureByteFunctionSpec inputAfter)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DerivePublicKeyBytesCall derivePublicKeyBytesSpec derivePublicKeyBytesStackSpec
)

/-! ## 1. Static `x25519CliMultiLib` Opcode-Exclusion, Extern-Freeness, & Process/VM Lifting -/

/-- Instruction-word mask/value pattern matching all `SVC #imm16` encodings (`isSvcWord`). -/
@[expose] def svcPat : WordPat := ⟨0xffe0001f#32, 0xd4000001#32⟩

theorem svcPat_matches (w : BitVec 32) : svcPat.matches w = isSvcWord w := rfl

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 10000000 in
theorem x25519CliMultiLib_blocks_all_svc :
    (x25519CliMultiLib.blocks.all fun b => b.patchSafe svcPat) = true := by
  decide +kernel

/-- Every block of `x25519CliMultiLib` is statically free of all `SVC #imm16` instructions under
    arbitrary call/ADRP/ADD relocation patching. -/
theorem x25519CliMultiLib_patchSafe_svc :
    ∀ k (hk : k < x25519CliMultiLib.blocks.length),
      x25519CliMultiLib.blocks[k].patchSafe svcPat = true := by
  intro k hk
  exact List.all_eq_true.mp x25519CliMultiLib_blocks_all_svc x25519CliMultiLib.blocks[k]
    (List.getElem_mem hk)

private theorem program_noSvc_of_patchSafe {lib : PlacedLib}
    (hps : lib.text.patchSafe svcPat = true) (pl : Placement) :
    (lib.program pl).allInstrs (fun i => !i.isSvc) = true :=
  PlacedLib.program_allInstrs_of_patchSafe (p := svcPat) (q := Instr.isSvc)
    (fun _ _ hd hm => decode_not_isSvc hd (by rwa [← svcPat_matches])) hps pl

theorem x25519CliMultiLib_block_externs_nil (i : Nat)
    (hi : i < x25519CliMultiLib.blocks.length) :
    (x25519CliMultiLib.blockLib i).text.externs = [] := by
  have hempty : x25519CliMultiLib.blocks[i].externs = [] := by
    have h := List.all_eq_true.mp x25519CliMultiLib_blocks_all_externs_empty
      x25519CliMultiLib.blocks[i] (List.getElem_mem hi)
    exact List.isEmpty_iff.mp h
  rw [x25519CliMultiLib.blockLib_text hi]
  exact hempty

/-- Every block of `x25519CliMultiLib` has `.externs = []`, so `blockProgram` has
    `externAt? = none` at all PCs for every extern map `externs`. -/
theorem x25519CliMultiLib_externAt_none (mpl : MultiPlacement) (i : Nat)
    (hi : i < x25519CliMultiLib.blocks.length)
    (externs : String → Option (State → State)) (pc : BitVec 64) :
    (x25519CliMultiLib.blockProgram mpl i externs).externAt? pc = none := by
  have hblk := x25519CliMultiLib_block_externs_nil i hi
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program,
    Program.externAt?, Program.hookAtOff?]
  rw [hblk]
  simp

/-- Every address inside the 19 code blocks of `x25519CliMultiLib` under `mpl` is unhooked in `P`. -/
@[expose] def X25519BlocksHookFree (P : Program) (mpl : MultiPlacement) : Prop :=
  ∀ k (hk : k < x25519CliMultiLib.blocks.length) (off : Nat),
    off < x25519CliMultiLib.blocks[k].code.length →
    P.externAt? (mpl.base k + BitVec.ofNat 64 off) = none

/-- Keep predicate covering all 19 placed blocks of `x25519CliMultiLib` under `mpl`. -/
@[expose] def x25519MultiKeep (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  (List.range x25519CliMultiLib.blocks.length).any fun k =>
    ProofLib.progKeep (x25519CliMultiLib.blockProgram mpl k) a

theorem strip_codeLoaded_x25519 {mpl : MultiPlacement} {m : Memory}
    (hcl : x25519CliMultiLib.CodeLoaded mpl m) :
    x25519CliMultiLib.CodeLoaded mpl (stripExecOutside (x25519MultiKeep mpl) m) := by
  intro j hj
  have hL := hcl j hj
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  let Pj := x25519CliMultiLib.blockProgram mpl j
  have hsub : Pj.base + BitVec.ofNat 64 k - Pj.base = BitVec.ofNat 64 k := by bv_omega
  have hin : (Pj.base + BitVec.ofNat 64 k - Pj.base).toNat < Pj.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hk
  have hkp : progKeep Pj (Pj.base + BitVec.ofNat 64 k) = true := by
    unfold progKeep; exact decide_eq_true hin
  have hmk : x25519MultiKeep mpl (Pj.base + BitVec.ofNat 64 k) = true := by
    unfold x25519MultiKeep
    rw [List.any_eq_true]
    exact ⟨j, List.mem_range.mpr hj, hkp⟩
  have hp_eq : (stripExecOutside (x25519MultiKeep mpl) m).perm (Pj.base + BitVec.ofNat 64 k) =
      m.perm (Pj.base + BitVec.ofNat 64 k) := by
    rw [strip_perm, hmk]
    cases m.perm (Pj.base + BitVec.ofNat 64 k) with
    | none => rfl
    | some p => cases p; rfl
  rw [strip_read8, hp_eq, strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

theorem ProcessFieldsPreserved_toHeapVmPreserved {s0 sf : State}
    (hpf : ProcessFieldsPreserved s0 sf) :
    LibsignalBinary.Heap.VmPreserved s0 sf := by
  rcases hpf with ⟨hfs, _htr, htp, _hsig, hbrk, hbrks, hphys, hperm⟩
  exact ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm, fun fd _ _ => by rw [hfs]⟩

theorem ProcessFieldsPreserved_toRustVmPreserved {s0 sf : State}
    (hpf : ProcessFieldsPreserved s0 sf) :
    Arm64.Rust.VmPreserved s0 sf := by
  rcases hpf with ⟨_hfs, _htr, htp, _hsig, hbrk, hbrks, _hphys, hperm⟩
  exact ⟨hbrks, hbrk, htp, funext hperm⟩

theorem x25519BlocksHookFree_externAt_none_of_keep {P : Program} {mpl : MultiPlacement}
    (hpl : x25519CliMultiLib.Placeable mpl)
    (hfree : X25519BlocksHookFree P mpl)
    {pc : BitVec 64} (hk : x25519MultiKeep mpl pc = true) :
    P.externAt? pc = none := by
  unfold x25519MultiKeep at hk
  rw [List.any_eq_true] at hk
  obtain ⟨j, hj_mem, hkp⟩ := hk
  have hj : j < x25519CliMultiLib.blocks.length := List.mem_range.mp hj_mem
  let Pj := x25519CliMultiLib.blockProgram mpl j
  have hin : (pc - Pj.base).toNat < Pj.code.length := by
    unfold progKeep at hkp; exact of_decide_eq_true hkp
  have hbt := (hpl.blocks_ok j hj).len_aligned
  have hplen : Pj.code.length = x25519CliMultiLib.blocks[j].code.length := by
    change ((x25519CliMultiLib.blockLib j).text.patched
      (x25519CliMultiLib.blockPlacement mpl j)).length = _
    rw [CodeBlock.length_patched_of_aligned _
      (by rw [x25519CliMultiLib.blockLib_text hj]; exact hbt),
      x25519CliMultiLib.blockLib_text hj]
  have hbase : Pj.base = mpl.base j := rfl
  let off := (pc - mpl.base j).toNat
  have hpc_eq : pc = mpl.base j + BitVec.ofNat 64 off := by dsimp [off]; bv_omega
  rw [hpc_eq]
  exact hfree j hj off (by dsimp [off]; rw [← hbase, ← hplen]; exact hin)

private theorem fetch_in_x25519_not_svc_msr {mpl : MultiPlacement}
    (hpl : x25519CliMultiLib.Placeable mpl)
    {m0 m : Memory} (hcl0 : x25519CliMultiLib.CodeLoaded mpl m0) (hkf : m0.KeepsFrozen m)
    {pc : BitVec 64} {inst : Instr}
    (hk : x25519MultiKeep mpl pc = true)
    (hfm : Program.pureMem.fetchMem m pc = some inst) :
    inst.isSvc = false ∧ inst.isMsrTpidrEl0 = false := by
  unfold x25519MultiKeep at hk
  rw [List.any_eq_true] at hk
  obtain ⟨j, hj_mem, hkp⟩ := hk
  have hj : j < x25519CliMultiLib.blocks.length := List.mem_range.mp hj_mem
  have hcl_m : (x25519CliMultiLib.blockProgram mpl j).CodeLoaded m := (hcl0 j hj).of_keepsFrozen hkf
  have hal_pc : pc.toNat % 4 = 0 := by
    unfold Program.fetchMem at hfm
    by_cases h4 : pc.toNat % 4 = 0
    · exact h4
    · simp [h4] at hfm
  let Pj := x25519CliMultiLib.blockProgram mpl j
  have hPj_al : Pj.base.toNat % 4 = 0 := hcl_m.aligned
  have hPj_nw : Pj.base.toNat + Pj.code.length ≤ 2 ^ 64 := hcl_m.no_wrap
  have hin : (pc - Pj.base).toNat < Pj.code.length := by
    unfold progKeep at hkp; exact of_decide_eq_true hkp
  have hPj_len4 : Pj.code.length % 4 = 0 := by
    have hbt := (hpl.blocks_ok j hj).len_aligned
    have hplen : ((x25519CliMultiLib.blockLib j).text.patched
        (x25519CliMultiLib.blockPlacement mpl j)).length =
        (x25519CliMultiLib.blockLib j).text.code.length :=
      CodeBlock.length_patched_of_aligned _
        (by rw [x25519CliMultiLib.blockLib_text hj]; exact hbt)
    change ((x25519CliMultiLib.blockLib j).text.patched
      (x25519CliMultiLib.blockPlacement mpl j)).length % 4 = 0
    rw [hplen, x25519CliMultiLib.blockLib_text hj]
    exact hbt
  let off := (pc - Pj.base).toNat
  have hpc_eq : pc = Pj.base + BitVec.ofNat 64 off := by dsimp [off]; bv_omega
  have hpc_ge : Pj.base.toNat ≤ pc.toNat := by
    change (pc - Pj.base).toNat < Pj.code.length at hin; bv_omega
  have hoff_nat : off = pc.toNat - Pj.base.toNat := by dsimp [off]; bv_omega
  have hoff_lt : off < Pj.code.length := hin
  have hPj_len_eq : (x25519CliMultiLib.blockProgram mpl j).code.length = Pj.code.length := rfl
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
  have hps_svc : (x25519CliMultiLib.blockLib j).text.patchSafe svcPat = true := by
    rw [x25519CliMultiLib.blockLib_text hj]
    exact x25519CliMultiLib_patchSafe_svc j hj
  have hps_msr : (x25519CliMultiLib.blockLib j).text.patchSafe msrTpidrEl0Pat = true := by
    rw [x25519CliMultiLib.blockLib_text hj]
    exact x25519CliMultiLib_patchSafe_msr j hj
  have hall_svc := program_noSvc_of_patchSafe hps_svc
    (x25519CliMultiLib.blockPlacement mpl j)
  have hall_msr := PlacedLib.program_noMsrTpidrEl0_of_patchSafe hps_msr
    (x25519CliMultiLib.blockPlacement mpl j)
  exact ⟨by have hi := Program.fetch_of_allInstrs hall_svc _ _ hfetch_Pj; simpa using hi,
    by have hi := Program.fetch_of_allInstrs hall_msr _ _ hfetch_Pj; simpa using hi⟩

private theorem steps_pureMem_lift_stripS_process (keep : BitVec 64 → Bool) {P : Program}
    {m0 : Memory}
    (hext_P : ∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none)
    (h_pure : ∀ (m : Memory) (pc : BitVec 64) (inst : Instr),
      m0.KeepsFrozen m →
      keep pc = true →
      Program.pureMem.fetchMem m pc = some inst →
      inst.isSvc = false ∧ inst.isMsrTpidrEl0 = false) :
    ∀ {s0 s' sf' : State},
      s' = stripS keep s0 →
      m0.KeepsFrozen s0.mem →
      Steps Program.pureMem s' sf' →
      sf'.status = .Running →
      ∃ sf : State,
        sf' = stripS keep sf ∧
        Steps P s0 sf ∧
        ProcessFieldsPreserved s0 sf ∧
        AllocCallPreserved s0 sf ∧
        m0.KeepsFrozen sf.mem := by
  intro s0 s' sf' hs' hkf hsteps hrun_f
  induction hsteps generalizing s0 with
  | refl _ =>
    subst hs'
    exact ⟨s0, rfl, Steps.refl s0, ProcessFieldsPreserved.refl s0,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hkf⟩
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
        obtain ⟨hsvc, hmsr⟩ := h_pure s0.mem s0.pc inst hkf hk0 hfetch_pm
        have hns : inst.isSvc0 = false := inst.isSvc0_eq_false_of_isSvc_eq_false hsvc
        rw [evalInst_pureMem] at hrest hrun2' ih
        have heval_P : P.evalInst inst s0 = execInst inst s0 :=
          evalInst_eq_execInst_of_not_isSvc0 hns s0
        have hstep_s0 : Step P s0 (execInst inst s0) :=
          heval_P ▸ Step.exec hrun1 hfetch_P
        have hstep_pm : Step Program.pureMem s0 (execInst inst s0) :=
          evalInst_pureMem inst s0 ▸ Step.exec hrun1 hfetch_pm
        have hcomm : execInst inst (stripS keep s0) = stripS keep (execInst inst s0) :=
          execInst_stripS hns keep s0
        have hpf1 : ProcessFieldsPreserved s0 (execInst inst s0) :=
          execInst_preserves_processFields hsvc hmsr s0
        have hora1 : (execInst inst s0).oracle = s0.oracle := by
          let Pstd : Program :=
            { code := [], base := 0, externs := fun _ => none, svc := Syscall.standard }
          rw [← evalInst_eq_execInst_of_not_isSvc0 (prog := Pstd) hns s0]
          exact evalInst_oracle_of_standard (prog := Pstd) rfl inst s0
        have hacp1 : AllocCallPreserved s0 (execInst inst s0) :=
          ⟨hpf1.1, hpf1.2.1, hpf1.2.2.2.1, hpf1.2.2.1, hpf1.2.2.2.2.2.1,
           hora1, hstep_s0.symtab_eq⟩
        have hkf2 : m0.KeepsFrozen (execInst inst s0).mem := hkf.trans hstep_pm.keepsFrozen
        obtain ⟨sf, hsf_eq, hsteps_rest, hpf_rest, hacp_rest, hkf_f⟩ := ih hcomm hkf2 hrun_f
        rcases hacp1 with ⟨a1, a2, a3, a4, a5, a6, a7⟩
        rcases hacp_rest with ⟨b1, b2, b3, b4, b5, b6, b7⟩
        exact ⟨sf, hsf_eq, Steps.step hstep_s0 hsteps_rest, hpf1.trans hpf_rest,
          ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5,
           b6.trans a6, b7.trans a7⟩, hkf_f⟩
      · simp [hce'] at hfetch'

/-- Strengthen `spec.post` with `⌜ProcessFieldsPreserved s0 sf⌝`. -/
@[expose] def withProcessPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ spec.post x s0 sf }

/-- Strengthen `spec.post` with `⌜ProcessFieldsPreserved s0 sf ∧ AllocCallPreserved s0 sf⌝`. -/
@[expose] def withProcessAllocPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    post := fun x s0 sf =>
      ⌜ProcessFieldsPreserved s0 sf ∧ AllocCallPreserved s0 sf⌝ ∗ spec.post x s0 sf }

/-- Lift any `subroutine_ok` proved on `x25519CliMultiLib.blockProgram mpl i` to any program `P`
    whose extern table does not hook inside `x25519CliMultiLib` (`X25519BlocksHookFree P mpl`),
    strengthening the postcondition to `withProcessAllocPreserved spec`. -/
theorem x25519_hookFree_withProcessAllocPreserved {α : Type}
    {P : Program} {mpl : MultiPlacement} {i : Nat} {entry : BitVec 64} {spec : Spec α}
    (hi : i < x25519CliMultiLib.blocks.length)
    (hpl : x25519CliMultiLib.Placeable mpl)
    (hfree : X25519BlocksHookFree P mpl)
    (hsub : subroutine_ok (x25519CliMultiLib.blockProgram mpl i) entry
      (x25519CliMultiLib.withCodeLoaded mpl spec))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok P entry
      (x25519CliMultiLib.withCodeLoaded mpl (withProcessAllocPreserved spec)) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp _hLP
  dsimp only [MultiPlacedLib.withCodeLoaded, withProcessAllocPreserved] at hpre
  rw [sepConj_comm (spec.pre x s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_spec⟩ := hpre
  let keep := x25519MultiKeep mpl
  obtain ⟨R_view, hpre_strip, hunstrip⟩ := ProofLib.strip_frame keep hpre_spec
  let s0' := stripS keep s0
  have hcl_strip : x25519CliMultiLib.CodeLoaded mpl s0'.mem := by
    have hm : s0'.mem = stripExecOutside keep s0.mem := by cases s0; rfl
    rw [hm]; exact strip_codeLoaded_x25519 hcl0
  have hpre' : s0'.mem ⊨ (x25519CliMultiLib.withCodeLoaded mpl spec).pre x s0' ∗ R_view := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl_strip]
    have hs0_eq : s0' = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
    rw [hs0_eq, h_pre_mem]
    simpa [State.setMem] using hpre_strip
  have hLi_strip : (x25519CliMultiLib.blockProgram mpl i).CodeLoaded s0'.mem :=
    hcl_strip i hi
  obtain ⟨sf', hsteps_blk, hout'⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hsub x R_view s0' (by cases s0; exact hpc) (by cases s0; exact hrun)
      hpre' (by cases s0; exact hsp))
    hLi_strip
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have hsteps_pm' : Steps Program.pureMem s0' sf' :=
      Steps.of_sameHooks (P := Program.pureMem) (Q := x25519CliMultiLib.blockProgram mpl i)
        (fun pc => x25519CliMultiLib_externAt_none mpl i hi _ pc) rfl hsteps_blk
    obtain ⟨sf, hsf_eq, hsteps_P, hpf, hacp, _hkf_f⟩ :=
      steps_pureMem_lift_stripS_process keep
        (fun _ hk => x25519BlocksHookFree_externAt_none_of_keep hpl hfree hk)
        (fun m pc inst hkf hk hfm => fetch_in_x25519_not_svc_msr hpl hcl0 hkf hk hfm)
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
        hunstrip hpf.2.2.2.2.2.2.2 (by simpa [State.setMem] using hpost')
      dsimp only [MultiPlacedLib.withCodeLoaded, withProcessAllocPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpf, hacp⟩, hpost_sf⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded] at hp
    rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [MultiPlacedLib.withCodeLoaded] at he
    rw [hex] at he; exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [MultiPlacedLib.withCodeLoaded] at ho
    rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-- Lift any `subroutine_ok` proved on `x25519CliMultiLib.blockProgram mpl i` to
    `withProcessAllocPreserved spec` on `x25519CliMultiLib.blockProgram mpl i externs`
    for arbitrary `externs`. -/
theorem x25519_blockProgram_withProcessAllocPreserved {α : Type}
    {mpl : MultiPlacement} {i : Nat} {entry : BitVec 64} {spec : Spec α}
    {externs : String → Option (State → State)}
    (hi : i < x25519CliMultiLib.blocks.length)
    (hpl : x25519CliMultiLib.Placeable mpl)
    (hsub : subroutine_ok (x25519CliMultiLib.blockProgram mpl i) entry
      (x25519CliMultiLib.withCodeLoaded mpl spec))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok (x25519CliMultiLib.blockProgram mpl i externs) entry
      (x25519CliMultiLib.withCodeLoaded mpl (withProcessAllocPreserved spec)) :=
  x25519_hookFree_withProcessAllocPreserved hi hpl
    (fun _ _ _ _ => x25519CliMultiLib_externAt_none mpl i hi externs _)
    hsub hpan hex hoom h_pre_mem h_post_mem

private theorem specSimulates_drop_alloc_from_processAlloc {α : Type} (spec : Spec α) :
    SpecSimulates (withProcessAllocPreserved spec) (withProcessPreserved spec) := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpost⟩ | ⟨c, he, hpost⟩ | ⟨ho, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withProcessAllocPreserved, withProcessPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.1, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hpost⟩))

private theorem specSimulates_traceEq_keepsFs_vm_of_process {α : Type} (spec : Spec α) :
    SpecSimulates (withProcessPreserved spec)
      (Spec.withTraceEq (keepsFs (withVmPreserved spec))) := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpost⟩ | ⟨c, he, hpost⟩ | ⟨ho, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withProcessPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost_sf⟩ := hpost
    have hvm : VmPreserved s0 sf := ProcessFieldsPreserved_toHeapVmPreserved hpf
    dsimp only [Spec.withTraceEq, keepsFs, withVmPreserved]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨hpf.2.1, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨hpf.1, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hvm, hpost_sf⟩
  · exact Or.inr (Or.inl ⟨hp, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hpost⟩))

/-- Lift any `subroutine_ok` proved on `x25519CliMultiLib.blockProgram mpl i` to
    `withProcessPreserved spec` on `x25519CliMultiLib.blockProgram mpl i externs`
    for arbitrary `externs`. -/
theorem x25519_blockProgram_withProcessPreserved {α : Type}
    {mpl : MultiPlacement} {i : Nat} {entry : BitVec 64} {spec : Spec α}
    {externs : String → Option (State → State)}
    (hi : i < x25519CliMultiLib.blocks.length)
    (hpl : x25519CliMultiLib.Placeable mpl)
    (hsub : subroutine_ok (x25519CliMultiLib.blockProgram mpl i) entry
      (x25519CliMultiLib.withCodeLoaded mpl spec))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok (x25519CliMultiLib.blockProgram mpl i externs) entry
      (x25519CliMultiLib.withCodeLoaded mpl (withProcessPreserved spec)) :=
  ((specSimulates_drop_alloc_from_processAlloc spec).withCodeLoaded
    x25519CliMultiLib mpl).subroutine_ok
    (x25519_blockProgram_withProcessAllocPreserved hi hpl hsub
      hpan hex hoom h_pre_mem h_post_mem)

/-- Lift any `subroutine_ok` proved on `x25519CliMultiLib.blockProgram mpl i` to
    `Spec.withTraceEq (keepsFs (withVmPreserved spec))` on
    `x25519CliMultiLib.blockProgram mpl i externs` for arbitrary `externs`. -/
theorem x25519_blockProgram_withTraceEq_keepsFs_withVmPreserved {α : Type}
    {mpl : MultiPlacement} {i : Nat} {entry : BitVec 64} {spec : Spec α}
    {externs : String → Option (State → State)}
    (hi : i < x25519CliMultiLib.blocks.length)
    (hpl : x25519CliMultiLib.Placeable mpl)
    (hsub : subroutine_ok (x25519CliMultiLib.blockProgram mpl i) entry
      (x25519CliMultiLib.withCodeLoaded mpl spec))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok (x25519CliMultiLib.blockProgram mpl i externs) entry
      (x25519CliMultiLib.withCodeLoaded mpl
        (Spec.withTraceEq (keepsFs (withVmPreserved spec)))) :=
  ((specSimulates_traceEq_keepsFs_vm_of_process spec).withCodeLoaded
    x25519CliMultiLib mpl).subroutine_ok
    (x25519_blockProgram_withProcessPreserved hi hpl hsub
      hpan hex hoom h_pre_mem h_post_mem)

/-- Export any `X25519BlockOk j spec` to `x25519CliMultiLib.subroutineOk sym` with
    `withProcessAllocPreserved` under any extern table `externs`. -/
theorem x25519SubroutineOk_withProcessAllocPreserved {j : Nat} (sym : String)
    {α : Type} {spec : MultiPlacement → Spec α}
    (hok : X25519BlockOk j spec)
    (externs : String → Option (State → State) := fun _ => none)
    (hexp : sym ∈ x25519CliMultiLib.exports := by decide +kernel)
    (hsym : lookupBlockSym sym x25519CliMultiLib.blocks = some (j, 0) := by decide +kernel)
    (hj : j < x25519CliMultiLib.blocks.length := by decide +kernel)
    (hpan : ∀ mpl, (spec mpl).onPanic = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hex : ∀ mpl, (spec mpl).onExit = fun _ _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hoom : ∀ mpl, (spec mpl).onOom = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (h_pre_mem : ∀ mpl x (s : State) (m : Memory),
      (spec mpl).pre x (s.setMem m) = (spec mpl).pre x s := by
      intro _ _ s _; cases s; rfl)
    (h_post_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
      (spec mpl).post x (s0.setMem m0) (sf.setMem mf) = (spec mpl).post x s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl) :
    x25519CliMultiLib.subroutineOk sym
      (fun mpl => withProcessAllocPreserved (spec mpl)) externs := by
  refine ⟨hexp, j, 0, hsym, fun mpl hpl => ?_⟩
  let _ : X25519CliPlacement := ⟨mpl, hpl⟩
  have hfn : x25519CliMultiLib.fnAddr mpl sym = mpl.base j := by
    simp [MultiPlacedLib.fnAddr, hsym]
  rw [hfn]
  exact x25519_blockProgram_withProcessAllocPreserved hj hpl hok
    (hpan mpl) (hex mpl) (hoom mpl) (h_pre_mem mpl) (h_post_mem mpl)

/-- Export any `X25519BlockOk j spec` to `x25519CliMultiLib.subroutineOk sym` with
    `withProcessPreserved` under any extern table `externs`. -/
theorem x25519SubroutineOk_withProcessPreserved {j : Nat} (sym : String)
    {α : Type} {spec : MultiPlacement → Spec α}
    (hok : X25519BlockOk j spec)
    (externs : String → Option (State → State) := fun _ => none)
    (hexp : sym ∈ x25519CliMultiLib.exports := by decide +kernel)
    (hsym : lookupBlockSym sym x25519CliMultiLib.blocks = some (j, 0) := by decide +kernel)
    (hj : j < x25519CliMultiLib.blocks.length := by decide +kernel)
    (hpan : ∀ mpl, (spec mpl).onPanic = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hex : ∀ mpl, (spec mpl).onExit = fun _ _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hoom : ∀ mpl, (spec mpl).onOom = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (h_pre_mem : ∀ mpl x (s : State) (m : Memory),
      (spec mpl).pre x (s.setMem m) = (spec mpl).pre x s := by
      intro _ _ s _; cases s; rfl)
    (h_post_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
      (spec mpl).post x (s0.setMem m0) (sf.setMem mf) = (spec mpl).post x s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl) :
    x25519CliMultiLib.subroutineOk sym
      (fun mpl => withProcessPreserved (spec mpl)) externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_drop_alloc_from_processAlloc (spec mpl))
    (x25519SubroutineOk_withProcessAllocPreserved sym hok externs
      hexp hsym hj hpan hex hoom h_pre_mem h_post_mem)

/-- Export any `X25519BlockOk j spec` to `x25519CliMultiLib.subroutineOk sym` with
    `Spec.withTraceEq`, `keepsFs`, and `withVmPreserved` under any extern table `externs`. -/
theorem x25519SubroutineOk_withTraceEq_keepsFs_vmPreserved {j : Nat} (sym : String)
    {α : Type} {spec : MultiPlacement → Spec α}
    (hok : X25519BlockOk j spec)
    (externs : String → Option (State → State) := fun _ => none)
    (hexp : sym ∈ x25519CliMultiLib.exports := by decide +kernel)
    (hsym : lookupBlockSym sym x25519CliMultiLib.blocks = some (j, 0) := by decide +kernel)
    (hj : j < x25519CliMultiLib.blocks.length := by decide +kernel)
    (hpan : ∀ mpl, (spec mpl).onPanic = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hex : ∀ mpl, (spec mpl).onExit = fun _ _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hoom : ∀ mpl, (spec mpl).onOom = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (h_pre_mem : ∀ mpl x (s : State) (m : Memory),
      (spec mpl).pre x (s.setMem m) = (spec mpl).pre x s := by
      intro _ _ s _; cases s; rfl)
    (h_post_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
      (spec mpl).post x (s0.setMem m0) (sf.setMem mf) = (spec mpl).post x s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl) :
    x25519CliMultiLib.subroutineOk sym
      (fun mpl => Spec.withTraceEq (keepsFs (withVmPreserved (spec mpl)))) externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_traceEq_keepsFs_vm_of_process (spec mpl))
    (x25519SubroutineOk_withProcessPreserved sym hok externs
      hexp hsym hj hpan hex hoom h_pre_mem h_post_mem)

/-- Placement-independent specialization of `x25519SubroutineOk_withTraceEq_keepsFs_vmPreserved`. -/
theorem x25519SubroutineOk_const_withTraceEq_keepsFs_vmPreserved {j : Nat} (sym : String)
    {α : Type} {spec : Spec α}
    (hok : X25519BlockConstOk j spec)
    (externs : String → Option (State → State) := fun _ => none)
    (hexp : sym ∈ x25519CliMultiLib.exports := by decide +kernel)
    (hsym : lookupBlockSym sym x25519CliMultiLib.blocks = some (j, 0) := by decide +kernel)
    (hj : j < x25519CliMultiLib.blocks.length := by decide +kernel)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by
      intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    x25519CliMultiLib.subroutineOk sym
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved spec))) externs :=
  x25519SubroutineOk_withTraceEq_keepsFs_vmPreserved sym (spec := fun _ => spec) hok externs
    hexp hsym hj (fun _ => hpan) (fun _ => hex) (fun _ => hoom)
    (fun _ => h_pre_mem) (fun _ => h_post_mem)

/-! ## 2. Pure `.rodata` Image Facts (`X25519CliRoOk`) & `InElf` Supply -/

/-- Adjoin a pure memory predicate `⌜RoOk s0.mem⌝` to `spec.pre`. -/
@[expose] def withRoOk {α : Type} (RoOk : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜RoOk s0.mem⌝ ∗ spec.pre x s0 }

/-- All 3 `.rodata` entries of `x25519CliMultiLib` hold at their placed addresses in `m` with
    `Perm.ro` (and `lazyFree = false`). -/
structure X25519CliRoOk (mpl : MultiPlacement) (m : Memory) : Prop where
  ro_fe51_one : RoDataAt m (fe51_one mpl) fe51OneBytes
  ro_fe51_mont_a24 : RoDataAt m (fe51_mont_a24 mpl) fe51MontA24Bytes
  ro_ed25519_basepoint_table : RoDataAt m (ed25519_basepoint_table mpl) ed25519BasepointTableBytes

/-- Load-time `HoldsBytes ... Perm.ro` for all `x25519CliMultiLib.data` entries supplies
    `X25519CliRoOk mpl m` on any memory `m` with `m₀.KeepsFrozen m`. -/
theorem x25519CliRoOk_of_holdsBytes_keepsFrozen {mpl : MultiPlacement} {m₀ m : Memory}
    (hhold : ∀ d ∈ x25519CliMultiLib.data,
      HoldsBytes m₀ (mpl.ρ d.sym) (x25519CliMultiLib.patchedData mpl d) (fun _ => Perm.ro))
    (hkf : m₀.KeepsFrozen m) :
    X25519CliRoOk mpl m := by
  have hd_eq : x25519CliMultiLib.data =
      [x25519CliData00, x25519CliData01, x25519CliData02] := rfl
  rw [hd_eq] at hhold
  simp only [List.forall_mem_cons] at hhold
  rcases hhold with ⟨h0, h1, h2, -⟩
  simp only [x25519CliData00, x25519CliData01, x25519CliData02,
    MultiPlacedLib.patchedData, List.foldl_nil, List.replicate_zero,
    List.append_nil] at h0 h1 h2
  exact
    { ro_fe51_one := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h0 hkf)
      ro_fe51_mont_a24 := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h1 hkf)
      ro_ed25519_basepoint_table := ProofLib.ObjectLoad.holdsBytes_ro
        (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h2 hkf) }

/-- `ElfMaps ... (· == Perm.ro)` for all `x25519CliMultiLib.data` entries supplies
    `X25519CliRoOk mpl m` on any memory `m` preserving frozen bytes from
    `img.loadState inputs = .ok s0`. -/
theorem x25519CliRoOk_of_elfMaps_keepsFrozen {img : ElfImage} {mpl : MultiPlacement}
    {inputs : ProcessInputs} {s0 : State} {m : Memory}
    (hmap : ∀ d ∈ x25519CliMultiLib.data,
      ElfMaps img (mpl.ρ d.sym) (x25519CliMultiLib.patchedData mpl d) (fun p => p == Perm.ro))
    (hload : img.loadState inputs = .ok s0)
    (hkf : s0.mem.KeepsFrozen m) :
    X25519CliRoOk mpl m :=
  x25519CliRoOk_of_holdsBytes_keepsFrozen
    (fun d hd => ElfMaps.holdsBytes hload (p := Perm.ro) (fun q hq => by simpa using hq) (hmap d hd))
    hkf

private theorem readBytes_eq_of_read8_eq :
    ∀ (n : Nat) (m₀ m : Memory) (addr : BitVec 64),
      (∀ k < n, m.read8 (addr + BitVec.ofNat 64 k) = m₀.read8 (addr + BitVec.ofNat 64 k)) →
      m.readBytes addr n = m₀.readBytes addr n
  | 0, _, _, _, _ => rfl
  | n + 1, m₀, m, addr, h => by
      simp only [Memory.readBytes]
      have h0 : m.read8 addr = m₀.read8 addr := by
        simpa using h 0 (Nat.zero_lt_succ n)
      have hrest : m.readBytes (addr + 1#64) n = m₀.readBytes (addr + 1#64) n := by
        refine readBytes_eq_of_read8_eq n m₀ m (addr + 1#64) fun k hk => ?_
        have heq : addr + 1#64 + BitVec.ofNat 64 k = addr + BitVec.ofNat 64 (k + 1) := by bv_omega
        rw [heq]
        exact h (k + 1) (Nat.succ_lt_succ hk)
      rw [h0, hrest]

private theorem roDataAt_of_keepsFrozen {m₀ m : Memory} {addr : BitVec 64}
    {bytes : List (BitVec 8)} (hro : RoDataAt m₀ addr bytes) (hkf : m₀.KeepsFrozen m)
    (hlen : bytes.length ≤ 2 ^ 64) :
    RoDataAt m addr bytes := by
  rcases hro with ⟨hro_mem, hrb⟩
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨hp, hlf⟩ := hro_mem a ha
    have hfr : m₀.Frozen a := by unfold Memory.Frozen; rw [hp]; rfl
    obtain ⟨_, hp', hlf', _⟩ := hkf a hfr
    exact ⟨hp'.trans hp, hlf'.trans hlf⟩
  · rw [readBytes_eq_of_read8_eq bytes.length m₀ m addr fun k hk => by
      have hin : InRegion addr bytes.length (addr + BitVec.ofNat 64 k) := by
        unfold InRegion
        have hsub : addr + BitVec.ofNat 64 k - addr = BitVec.ofNat 64 k := by bv_omega
        rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hk hlen)]
        exact hk
      obtain ⟨hp, _⟩ := hro_mem _ hin
      have hfr : m₀.Frozen (addr + BitVec.ofNat 64 k) := by unfold Memory.Frozen; rw [hp]; rfl
      exact (hkf _ hfr).1]
    exact hrb

/-- `X25519CliRoOk` is preserved across `m₀.KeepsFrozen m`. -/
theorem x25519CliRoOk_of_keepsFrozen {mpl : MultiPlacement} {m₀ m : Memory}
    (hro : X25519CliRoOk mpl m₀) (hkf : m₀.KeepsFrozen m) :
    X25519CliRoOk mpl m :=
  { ro_fe51_one := roDataAt_of_keepsFrozen hro.ro_fe51_one hkf
      (by rw [fe51OneBytes_length]; decide)
    ro_fe51_mont_a24 := roDataAt_of_keepsFrozen hro.ro_fe51_mont_a24 hkf
      (by rw [fe51MontA24Bytes_length]; decide)
    ro_ed25519_basepoint_table := roDataAt_of_keepsFrozen hro.ro_ed25519_basepoint_table hkf
      (by rw [ed25519BasepointTableBytes_length]; decide) }

private theorem roDataAt_stripExecOutside (keep : BitVec 64 → Bool) {m : Memory}
    {addr : BitVec 64} {bytes : List (BitVec 8)} (hro : RoDataAt m addr bytes) :
    RoDataAt (stripExecOutside keep m) addr bytes := by
  rcases hro with ⟨hro_mem, hrb⟩
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨hp, hlf⟩ := hro_mem a ha
    rw [strip_perm, hp, strip_isLazyFree, hlf]
    cases keep a <;> exact ⟨rfl, rfl⟩
  · rw [readBytes_eq_of_read8_eq bytes.length m (stripExecOutside keep m) addr
      fun _ _ => by rw [strip_read8]]
    exact hrb

/-- `X25519CliRoOk` is invariant under `stripExecOutside keep`. -/
theorem x25519CliRoOk_stripExecOutside (keep : BitVec 64 → Bool) {mpl : MultiPlacement}
    {m : Memory} (hro : X25519CliRoOk mpl m) :
    X25519CliRoOk mpl (stripExecOutside keep m) :=
  { ro_fe51_one := roDataAt_stripExecOutside keep hro.ro_fe51_one
    ro_fe51_mont_a24 := roDataAt_stripExecOutside keep hro.ro_fe51_mont_a24
    ro_ed25519_basepoint_table :=
      roDataAt_stripExecOutside keep hro.ro_ed25519_basepoint_table }

/-- Absorb a separating `withRoDataSep addr bytes` wrapper into `withRoData addr bytes`. -/
theorem specSimulates_absorb_ro1 {α : Type}
    {addr : BitVec 64} {bytes : List (BitVec 8)} {spec : Spec α}
    (hlen : bytes.length ≤ 2 ^ 64) :
    SpecSimulates (withRoDataSep addr bytes spec) (withRoData addr bytes spec) :=
  SpecSimulates.withRoData_of_sep hlen

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

/-! ## 3. Consumer `SpecSimulates` & `x25519CliMultiLib.subroutineOk` Contracts -/

/-- Unmangled symbol name for `<PublicKey as From<&StaticSecret>>::from` (`Blk18`). -/
abbrev pubFromSecretSym : String :=
  "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from"

/-- Unmangled symbol name for `<StaticSecret>::diffie_hellman` (`Blk17`). -/
abbrev diffieHellmanSym : String :=
  "<x25519_dalek::x25519::StaticSecret>::diffie_hellman"

/-- Separating `.rodata` wrapper for `<PublicKey as From<&StaticSecret>>::from` (`Blk18`):
    frames `ed25519_basepoint_table` (`30,720` B) and `fe51_one` (`40` B). -/
@[expose] def withPubFromSecretRoSep (mpl : MultiPlacement) {α : Type} (spec : Spec α) : Spec α :=
  withRoDataSep (ed25519_basepoint_table mpl) ed25519BasepointTableBytes
    (withRoDataSep (fe51_one mpl) fe51OneBytes spec)

/-- Separating `.rodata` wrapper for `<StaticSecret>::diffie_hellman` (`Blk17`):
    frames `fe51_one` (`40` B) and `fe51_mont_a24` (`40` B). -/
@[expose] def withDiffieHellmanRoSep (mpl : MultiPlacement) {α : Type} (spec : Spec α) : Spec α :=
  withRoDataSep (fe51_one mpl) fe51OneBytes
    (withRoDataSep (fe51_mont_a24 mpl) fe51MontA24Bytes spec)

/-- Absorb two nested `withRoDataSep` wrappers into `withRoOk RoOk`. -/
theorem specSimulates_absorb_roDataSep2 {α : Type} {RoOk : Memory → Prop}
    {a₁ a₂ : BitVec 64} {b₁ b₂ : List (BitVec 8)} {spec : Spec α}
    (hlen₁ : b₁.length ≤ 2 ^ 64) (hlen₂ : b₂.length ≤ 2 ^ 64)
    (hro₁ : ∀ m, RoOk m → RoDataAt m a₁ b₁)
    (hro₂ : ∀ m, RoOk m → RoDataAt m a₂ b₂) :
    SpecSimulates (withRoDataSep a₁ b₁ (withRoDataSep a₂ b₂ spec)) (withRoOk RoOk spec) := by
  have s1 : SpecSimulates (withRoDataSep a₁ b₁ (withRoDataSep a₂ b₂ spec))
      (withRoData a₁ b₁ (withRoDataSep a₂ b₂ spec)) :=
    SpecSimulates.withRoData_of_sep hlen₁
  have s2 : SpecSimulates (withRoData a₁ b₁ (withRoDataSep a₂ b₂ spec))
      (withRoDataSep a₂ b₂ (withRoData a₁ b₁ spec)) := by
    intro x R s0 hpre
    refine ⟨x, R, ?_, fun _ hout => hout⟩
    dsimp only [withRoData, withRoDataSep] at hpre ⊢
    exact Satisfies.mono (by sep_entail) hpre
  have s3 : SpecSimulates (withRoDataSep a₂ b₂ (withRoData a₁ b₁ spec))
      (withRoData a₂ b₂ (withRoData a₁ b₁ spec)) :=
    SpecSimulates.withRoData_of_sep hlen₂
  have s4 : SpecSimulates (withRoData a₂ b₂ (withRoData a₁ b₁ spec))
      (withRoOk RoOk spec) := by
    intro x R s0 hpre
    dsimp only [withRoOk] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨hro, hpre⟩ := hpre
    refine ⟨x, R, ?_, fun _ hout => hout⟩
    dsimp only [withRoData]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨hro₂ s0.mem hro, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hro₁ s0.mem hro, hpre⟩
  exact s1.trans (s2.trans (s3.trans s4))

/-- Absorb `withPubFromSecretRoSep mpl` into `withRoOk (X25519CliRoOk mpl)`. -/
theorem specSimulates_absorb_pubFromSecretRoSep (mpl : MultiPlacement) {α : Type} (spec : Spec α) :
    SpecSimulates (withPubFromSecretRoSep mpl spec) (withRoOk (X25519CliRoOk mpl) spec) :=
  specSimulates_absorb_roDataSep2
    (by rw [ed25519BasepointTableBytes_length]; decide)
    (by rw [fe51OneBytes_length]; decide)
    (fun _ h => h.ro_ed25519_basepoint_table)
    (fun _ h => h.ro_fe51_one)

/-- Absorb `withDiffieHellmanRoSep mpl` into `withRoOk (X25519CliRoOk mpl)`. -/
theorem specSimulates_absorb_diffieHellmanRoSep (mpl : MultiPlacement) {α : Type} (spec : Spec α) :
    SpecSimulates (withDiffieHellmanRoSep mpl spec) (withRoOk (X25519CliRoOk mpl) spec) :=
  specSimulates_absorb_roDataSep2
    (by rw [fe51OneBytes_length]; decide)
    (by rw [fe51MontA24Bytes_length]; decide)
    (fun _ h => h.ro_fe51_one)
    (fun _ h => h.ro_fe51_mont_a24)

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

theorem specSimulates_withProcessPreserved {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (withProcessPreserved spec₁) (withProcessPreserved spec₂) := by
  intro y R s0 hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  refine ⟨x, R₁, hpre₁, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hp, hm_p⟩ | ⟨c, he, hm_e⟩ | ⟨ho, hm_o⟩
  · dsimp only [withProcessPreserved] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    obtain ⟨hpf, hp⟩ := hp
    rcases hm sf (Or.inl ⟨hret, hcc, hp⟩) with ⟨hret₂, hcc₂, hp₂⟩ | hout₂
    · refine Or.inl ⟨hret₂, hcc₂, ?_⟩
      dsimp only [withProcessPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpf, hp₂⟩
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

theorem specSimulates_withProcessAllocPreserved {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (withProcessAllocPreserved spec₁) (withProcessAllocPreserved spec₂) := by
  intro y R s0 hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  refine ⟨x, R₁, hpre₁, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hp, hm_p⟩ | ⟨c, he, hm_e⟩ | ⟨ho, hm_o⟩
  · dsimp only [withProcessAllocPreserved] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    obtain ⟨hpfa, hp⟩ := hp
    rcases hm sf (Or.inl ⟨hret, hcc, hp⟩) with ⟨hret₂, hcc₂, hp₂⟩ | hout₂
    · refine Or.inl ⟨hret₂, hcc₂, ?_⟩
      dsimp only [withProcessAllocPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpfa, hp₂⟩
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

private theorem specSimulates_dup_vm_in_traceEq_keepsFs {α : Type} (spec : Spec α) :
    SpecSimulates
      (Spec.withTraceEq (keepsFs (withVmPreserved spec)))
      (keepsFs (withVmPreserved (Spec.withTraceEq (withVmPreserved spec)))) := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hm_p⟩ | ⟨c, he, hm_e⟩ | ⟨ho, hm_o⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.withTraceEq, keepsFs, withVmPreserved] at hpost ⊢
    simp only [sepConj_assoc] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hpost⟩ := hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hfs, hpost⟩ := hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hvm, hpost⟩ := hpost
    rw [satisfies_pure_sepConj]; refine ⟨hfs, ?_⟩
    rw [satisfies_pure_sepConj]; refine ⟨hvm, ?_⟩
    rw [satisfies_pure_sepConj]; refine ⟨htr, ?_⟩
    rw [satisfies_pure_sepConj]; exact ⟨hvm, hpost⟩
  · exact Or.inr (Or.inl ⟨hp, hm_p⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hm_e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hm_o⟩))

private theorem specSimulates_traceEq_of_processPreserved {α : Type} (spec : Spec α) :
    SpecSimulates (withProcessPreserved spec) (withProcessPreserved (Spec.withTraceEq spec)) := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hm_p⟩ | ⟨c, he, hm_e⟩ | ⟨ho, hm_o⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withProcessPreserved, Spec.withTraceEq] at hpost ⊢
    simp only [sepConj_assoc] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    rw [satisfies_pure_sepConj]; refine ⟨hpf, ?_⟩
    rw [satisfies_pure_sepConj]; exact ⟨hpf.2.1, hpost⟩
  · exact Or.inr (Or.inl ⟨hp, hm_p⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hm_e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hm_o⟩))

private theorem specSimulates_traceEq_vm_of_processPreserved {α : Type} (spec : Spec α) :
    SpecSimulates (withProcessPreserved spec)
      (withProcessPreserved (Spec.withTraceEq (withVmPreserved spec))) := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hm_p⟩ | ⟨c, he, hm_e⟩ | ⟨ho, hm_o⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withProcessPreserved, Spec.withTraceEq, withVmPreserved] at hpost ⊢
    simp only [sepConj_assoc] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    rw [satisfies_pure_sepConj]; refine ⟨hpf, ?_⟩
    rw [satisfies_pure_sepConj]; refine ⟨hpf.2.1, ?_⟩
    rw [satisfies_pure_sepConj]; exact ⟨ProcessFieldsPreserved_toHeapVmPreserved hpf, hpost⟩
  · exact Or.inr (Or.inl ⟨hp, hm_p⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hm_e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hm_o⟩))

private theorem specSimulates_drop_keepsFs_vm {α : Type} (spec : Spec α) :
    SpecSimulates (keepsFs (withVmPreserved spec)) spec := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hm_p⟩ | ⟨c, he, hm_e⟩ | ⟨ho, hm_o⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [keepsFs, withVmPreserved] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨_, hpost⟩ := hpost
    rw [satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr (Or.inl ⟨hp, hm_p⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hm_e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hm_o⟩))

/-! ### 3.1 Raw `Blk18` (`pubFromSecretSym`) & `Blk17` (`diffieHellmanSym`) `subroutineOk` Exports -/

/-- Raw `publicKeyFromSecretSpec` (`Blk18`) exported with `withProcessAllocPreserved`. -/
theorem publicKeyFromSecret_subroutineOk_withProcessAllocPreserved
    (hPub : PublicKeyFromStaticSecretOk)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl => withProcessAllocPreserved (publicKeyFromSecretSpec mpl)) externs :=
  x25519SubroutineOk_withProcessAllocPreserved pubFromSecretSym hPub externs

/-- Raw `publicKeyFromSecretSpec` (`Blk18`) exported with `withProcessPreserved`. -/
theorem publicKeyFromSecret_subroutineOk_withProcessPreserved
    (hPub : PublicKeyFromStaticSecretOk)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl => withProcessPreserved (publicKeyFromSecretSpec mpl)) externs :=
  x25519SubroutineOk_withProcessPreserved pubFromSecretSym hPub externs

/-- Raw `publicKeyFromSecretSpec` (`Blk18`) exported with `Spec.withTraceEq`, `keepsFs`, and
    `withVmPreserved`. -/
theorem publicKeyFromSecret_subroutineOk_withTraceEq_keepsFs_vmPreserved
    (hPub : PublicKeyFromStaticSecretOk)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl => Spec.withTraceEq (keepsFs (withVmPreserved (publicKeyFromSecretSpec mpl))))
      externs :=
  x25519SubroutineOk_withTraceEq_keepsFs_vmPreserved pubFromSecretSym hPub externs

/-- Raw `staticSecretDiffieHellmanSpec` (`Blk17`) exported with `withProcessAllocPreserved`. -/
theorem staticSecretDiffieHellman_subroutineOk_withProcessAllocPreserved
    (hDH : StaticSecretDiffieHellmanOk)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl => withProcessAllocPreserved (staticSecretDiffieHellmanSpec mpl)) externs :=
  x25519SubroutineOk_withProcessAllocPreserved diffieHellmanSym hDH externs

/-- Raw `staticSecretDiffieHellmanSpec` (`Blk17`) exported with `withProcessPreserved`. -/
theorem staticSecretDiffieHellman_subroutineOk_withProcessPreserved
    (hDH : StaticSecretDiffieHellmanOk)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl => withProcessPreserved (staticSecretDiffieHellmanSpec mpl)) externs :=
  x25519SubroutineOk_withProcessPreserved diffieHellmanSym hDH externs

/-- Raw `staticSecretDiffieHellmanSpec` (`Blk17`) exported with `Spec.withTraceEq`, `keepsFs`,
    and `withVmPreserved`. -/
theorem staticSecretDiffieHellman_subroutineOk_withTraceEq_keepsFs_vmPreserved
    (hDH : StaticSecretDiffieHellmanOk)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl => Spec.withTraceEq (keepsFs (withVmPreserved (staticSecretDiffieHellmanSpec mpl))))
      externs :=
  x25519SubroutineOk_withTraceEq_keepsFs_vmPreserved diffieHellmanSym hDH externs

/-! ### 3.2 `<PublicKey as From<&StaticSecret>>::from` (`Blk18`, Stack `≥ 1904`) Consumer Bridges -/

/-- `Spec.withTraceEq (publicKeyFromSecretSpec mpl)` simulates stack-parameterized
    `withPubFromSecretRoSep mpl (withStack (LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef) stk)`
    for any stack budget `1904 ≤ stk ≤ 2 ^ 64`. -/
theorem pubFromSecret_simulates_hooks_roSep (mpl : MultiPlacement) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide) :
    SpecSimulates (Spec.withTraceEq (publicKeyFromSecretSpec mpl))
      (withPubFromSecretRoSep mpl
        (withStack
          (CryptoVerification.LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef)
          stk)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨secA, sec, ret⟩ R s0 hpre
  dsimp only [withPubFromSecretRoSep, withRoDataSep, withStack,
    CryptoVerification.LibsignalTripleRatchet.pubFromSecretSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜_ ∧ _⌝,
    sepConj_left_comm (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ⌜_ ∧ _⌝,
    satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8⟩, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes ret 32 (by decide),
    stackAt_shrink s0.sp stk 1904 hlo hhi,
    stackAt_eq_stackFrameAt s0.sp 1904 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨out_bs, hpre⟩ := hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (secA ↦ₛ sec.toList) ⌜out_bs.length = 32⌝,
    sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜out_bs.length = 32⌝,
    sepConj_left_comm (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes)
      ⌜out_bs.length = 32⌝,
    satisfies_pure_sepConj] at hpre
  obtain ⟨hout_len, hpre⟩ := hpre
  refine ⟨(ret, secA, out_bs, sec.toList),
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 1904) ∗ R, ?_, ?_⟩
  · dsimp only [Spec.withTraceEq, publicKeyFromSecretSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hout_len, sec.2⟩, Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret hcc hpost
    dsimp only [Spec.withTraceEq, publicKeyFromSecretSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hpost⟩ := hpost
    have hsf_frame : stackFrame sf 1904 = stackFrameAt s0.sp 1904 := by
      unfold stackFrame
      rw [hcc.1]
      exact stackAt_eq_stackFrameAt s0.sp 1904 (by decide)
    rw [hsf_frame] at hpost
    dsimp only [withPubFromSecretRoSep, withRoDataSep, withStack,
      CryptoVerification.LibsignalTripleRatchet.pubFromSecretSpec,
      x25519PubFromSecretRef_toList]
    rw [stackAt_shrink s0.sp stk 1904 hlo hhi,
      stackAt_eq_stackFrameAt s0.sp 1904 (by decide)]
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜sf.trace = s0.trace⌝,
      sepConj_left_comm (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes)
        ⌜sf.trace = s0.trace⌝,
      satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.mono (by sep_entail) hpost⟩

/-- Pure `X25519CliRoOk` simulation for stack-parameterized
    `LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef`. -/
theorem pubFromSecret_simulates_hooks_roOk (mpl : MultiPlacement) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide) :
    SpecSimulates (Spec.withTraceEq (publicKeyFromSecretSpec mpl))
      (withRoOk (X25519CliRoOk mpl)
        (withStack
          (CryptoVerification.LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef)
          stk)) :=
  (pubFromSecret_simulates_hooks_roSep mpl hlo hhi).trans
    (specSimulates_absorb_pubFromSecretRoSep mpl _)

/-- `CliExt.pubFromSecretSpec C` simulation in separating `withPubFromSecretRoSep` form
    (under `C.pubKey = x25519PubFromSecretRef`). -/
theorem pubFromSecret_simulates_cliExt_roSep (mpl : MultiPlacement) {C : Crypto}
    (hC : C.pubKey = x25519PubFromSecretRef) :
    SpecSimulates (Spec.withTraceEq (publicKeyFromSecretSpec mpl))
      (withPubFromSecretRoSep mpl (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)) := by
  have heq : CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C =
      withStack
        (CryptoVerification.LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef)
        extHookStack := by
    rw [← hC]; rfl
  rw [heq]
  exact pubFromSecret_simulates_hooks_roSep mpl (by decide) (by decide)

/-- `CliExt.pubFromSecretSpec C` simulation in pure `withRoOk (X25519CliRoOk mpl)` form
    (under `C.pubKey = x25519PubFromSecretRef`). -/
theorem pubFromSecret_simulates_cliExt_roOk (mpl : MultiPlacement) {C : Crypto}
    (hC : C.pubKey = x25519PubFromSecretRef) :
    SpecSimulates (Spec.withTraceEq (publicKeyFromSecretSpec mpl))
      (withRoOk (X25519CliRoOk mpl)
        (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)) :=
  (pubFromSecret_simulates_cliExt_roSep mpl hC).trans
    (specSimulates_absorb_pubFromSecretRoSep mpl _)

/-- `CliExt.pureByteFunctionSpec x25519PubFromSecretRef byVal` simulation in separating
    `withPubFromSecretRoSep` form. -/
theorem pubFromSecret_simulates_pureByteFunction_roSep (mpl : MultiPlacement) (byVal : Bool) :
    SpecSimulates (Spec.withTraceEq (publicKeyFromSecretSpec mpl))
      (withPubFromSecretRoSep mpl (pureByteFunctionSpec x25519PubFromSecretRef byVal)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨inA, v, ret⟩ R s0 hpre
  dsimp only [withPubFromSecretRoSep, withRoDataSep, pureByteFunctionSpec,
    CryptoVerification.SignalSession.CliExt.withStack] at hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜_ ∧ _⌝,
    sepConj_left_comm (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ⌜_ ∧ _⌝,
    satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8⟩, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes ret 32 (by decide),
    stackAt_shrink s0.sp extHookStack 1904 (by decide) (by decide),
    stackAt_eq_stackFrameAt s0.sp 1904 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨out_bs, hpre⟩ := hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (inA ↦ₛ v.toList) ⌜out_bs.length = 32⌝,
    sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜out_bs.length = 32⌝,
    sepConj_left_comm (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes)
      ⌜out_bs.length = 32⌝,
    satisfies_pure_sepConj] at hpre
  obtain ⟨hout_len, hpre⟩ := hpre
  refine ⟨(ret, inA, out_bs, v.toList),
    memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 1904) ∗ R, ?_, ?_⟩
  · dsimp only [Spec.withTraceEq, publicKeyFromSecretSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hout_len, v.2⟩, Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret hcc hpost
    dsimp only [Spec.withTraceEq, publicKeyFromSecretSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hpost⟩ := hpost
    have hsf_frame : stackFrame sf 1904 = stackFrameAt s0.sp 1904 := by
      unfold stackFrame
      rw [hcc.1]
      exact stackAt_eq_stackFrameAt s0.sp 1904 (by decide)
    rw [hsf_frame] at hpost
    dsimp only [withPubFromSecretRoSep, withRoDataSep, pureByteFunctionSpec,
      CryptoVerification.SignalSession.CliExt.withStack, x25519PubFromSecretRef_toList]
    rw [stackAt_shrink s0.sp extHookStack 1904 (by decide) (by decide),
      stackAt_eq_stackFrameAt s0.sp 1904 (by decide)]
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜sf.trace = s0.trace⌝,
      sepConj_left_comm (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes)
        ⌜sf.trace = s0.trace⌝,
      satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    cases byVal
    · simp only [inputAfter, Bool.false_eq_true, ↓reduceIte]
      exact Satisfies.mono (by sep_entail) hpost
    · simp only [inputAfter, ↓reduceIte]
      have hin_reg : (inA ↦ₛ v.toList) ⊢ memRegion inA 32 :=
        pointsToBytes_entails_memRegion_of_length v.2
      have hreord : sf.mem ⊨ (inA ↦ₛ v.toList) ∗
          (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗
          (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
          (ret ↦ₛ x25519Pubkey v.toList) ∗
          memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 1904) ∗
          stackFrameAt s0.sp 1904 ∗ R :=
        Satisfies.mono (by sep_entail) hpost
      have hfolded := Satisfies.mono (sepConj_mono hin_reg (Entails.refl _)) hreord
      exact Satisfies.mono (by sep_entail) hfolded

/-- `CliExt.pureByteFunctionSpec x25519PubFromSecretRef byVal` simulation in pure
    `withRoOk (X25519CliRoOk mpl)` form. -/
theorem pubFromSecret_simulates_pureByteFunction_roOk (mpl : MultiPlacement) (byVal : Bool) :
    SpecSimulates (Spec.withTraceEq (publicKeyFromSecretSpec mpl))
      (withRoOk (X25519CliRoOk mpl) (pureByteFunctionSpec x25519PubFromSecretRef byVal)) :=
  (pubFromSecret_simulates_pureByteFunction_roSep mpl byVal).trans
    (specSimulates_absorb_pubFromSecretRoSep mpl _)

/-- `Alloc.derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk` simulation in separating
    `withPubFromSecretRoSep` form (`1904 ≤ stk ≤ 2 ^ 64`). -/
theorem pubFromSecret_simulates_derivePublicKeyBytesStack_roSep (mpl : MultiPlacement) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide) :
    SpecSimulates (Spec.withTraceEq (withVmPreserved (publicKeyFromSecretSpec mpl)))
      (withPubFromSecretRoSep mpl
        (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨secret, sec, out⟩ R s0 hpre
  dsimp only [withPubFromSecretRoSep, withRoDataSep, derivePublicKeyBytesStackSpec,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.derivePublicKeyBytesStackBudgetSpec]
    at hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜_ ∧ _⌝,
    sepConj_left_comm (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ⌜_ ∧ _⌝,
    satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8⟩, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes out 32 (by decide),
    stackAt_shrink s0.sp stk 1904 hlo hhi,
    stackAt_eq_stackFrameAt s0.sp 1904 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨out_bs, hpre⟩ := hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (secret ↦ₛ sec.toList) ⌜out_bs.length = 32⌝,
    sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜out_bs.length = 32⌝,
    sepConj_left_comm (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes)
      ⌜out_bs.length = 32⌝,
    satisfies_pure_sepConj] at hpre
  obtain ⟨hout_len, hpre⟩ := hpre
  refine ⟨(out, secret, out_bs, sec.toList),
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 1904) ∗ R, ?_, ?_⟩
  · dsimp only [Spec.withTraceEq, withVmPreserved, publicKeyFromSecretSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hout_len, sec.2⟩, Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret hcc hpost
    dsimp only [Spec.withTraceEq, withVmPreserved, publicKeyFromSecretSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hpost⟩ := hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hvm, hpost⟩ := hpost
    have hsf_frame : stackFrame sf 1904 = stackFrameAt s0.sp 1904 := by
      unfold stackFrame
      rw [hcc.1]
      exact stackAt_eq_stackFrameAt s0.sp 1904 (by decide)
    rw [hsf_frame] at hpost
    dsimp only [withPubFromSecretRoSep, withRoDataSep, derivePublicKeyBytesStackSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.derivePublicKeyBytesStackBudgetSpec,
      x25519PubFromSecretRef_toList]
    rw [stackAt_shrink s0.sp stk 1904 hlo hhi,
      stackAt_eq_stackFrameAt s0.sp 1904 (by decide)]
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜_ ∧ _⌝,
      sepConj_left_comm (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ⌜_ ∧ _⌝,
      satisfies_pure_sepConj]
    exact ⟨⟨htr, hvm⟩, Satisfies.mono (by sep_entail) hpost⟩

/-- `Alloc.derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk` simulation in pure
    `withRoOk (X25519CliRoOk mpl)` form (`1904 ≤ stk ≤ 2 ^ 64`). -/
theorem pubFromSecret_simulates_derivePublicKeyBytesStack_roOk (mpl : MultiPlacement) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide) :
    SpecSimulates (Spec.withTraceEq (withVmPreserved (publicKeyFromSecretSpec mpl)))
      (withRoOk (X25519CliRoOk mpl)
        (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)) :=
  (pubFromSecret_simulates_derivePublicKeyBytesStack_roSep mpl hlo hhi).trans
    (specSimulates_absorb_pubFromSecretRoSep mpl _)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against stack-parameterized
    `LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef` with `keepsFs`,
    `withVmPreserved`, and separating `withPubFromSecretRoSep`. -/
theorem pubFromSecret_hooks_roSep_subroutineOk_keepsFs_vmPreserved
    (hPub : PublicKeyFromStaticSecretOk) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        keepsFs (withVmPreserved
          (withPubFromSecretRoSep mpl
            (withStack
              (CryptoVerification.LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef)
              stk))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_comm_traceEq_keepsFs_vm (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved (pubFromSecret_simulates_hooks_roSep mpl hlo hhi))))
    (publicKeyFromSecret_subroutineOk_withTraceEq_keepsFs_vmPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against stack-parameterized
    `LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef` with `withRoOk (X25519CliRoOk mpl)`,
    `keepsFs`, and `withVmPreserved`. -/
theorem pubFromSecret_hooks_roOk_subroutineOk_keepsFs_vmPreserved
    (hPub : PublicKeyFromStaticSecretOk) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl)
          (keepsFs (withVmPreserved
            (withStack
              (CryptoVerification.LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef)
              stk))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_comm_traceEq_keepsFs_vm (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved (pubFromSecret_simulates_hooks_roOk mpl hlo hhi))))
    (publicKeyFromSecret_subroutineOk_withTraceEq_keepsFs_vmPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against stack-parameterized
    `LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef` with `withProcessPreserved`
    and separating `withPubFromSecretRoSep`. -/
theorem pubFromSecret_hooks_roSep_subroutineOk_withProcessPreserved
    (hPub : PublicKeyFromStaticSecretOk) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withProcessPreserved
          (withPubFromSecretRoSep mpl
            (withStack
              (CryptoVerification.LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef)
              stk)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_of_processPreserved (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_withProcessPreserved (pubFromSecret_simulates_hooks_roSep mpl hlo hhi)))
    (publicKeyFromSecret_subroutineOk_withProcessPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against stack-parameterized
    `LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef` with `withRoOk (X25519CliRoOk mpl)`
    and `withProcessPreserved`. -/
theorem pubFromSecret_hooks_roOk_subroutineOk_withProcessPreserved
    (hPub : PublicKeyFromStaticSecretOk) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl)
          (withProcessPreserved
            (withStack
              (CryptoVerification.LibsignalTripleRatchet.pubFromSecretSpec x25519PubFromSecretRef)
              stk)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_of_processPreserved (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_withProcessPreserved (pubFromSecret_simulates_hooks_roOk mpl hlo hhi)))
    (publicKeyFromSecret_subroutineOk_withProcessPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against `CliExt.pubFromSecretSpec C` with
    `keepsFs`, `withVmPreserved`, and separating `withPubFromSecretRoSep`. -/
theorem pubFromSecret_cliExt_roSep_subroutineOk_keepsFs_vmPreserved
    (hPub : PublicKeyFromStaticSecretOk) {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        keepsFs (withVmPreserved
          (withPubFromSecretRoSep mpl
            (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_comm_traceEq_keepsFs_vm (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved (pubFromSecret_simulates_cliExt_roSep mpl hC))))
    (publicKeyFromSecret_subroutineOk_withTraceEq_keepsFs_vmPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against `CliExt.pubFromSecretSpec C` with
    `withRoOk (X25519CliRoOk mpl)`, `keepsFs`, and `withVmPreserved`. -/
theorem pubFromSecret_cliExt_roOk_subroutineOk_keepsFs_vmPreserved
    (hPub : PublicKeyFromStaticSecretOk) {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl)
          (keepsFs (withVmPreserved
            (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_comm_traceEq_keepsFs_vm (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved (pubFromSecret_simulates_cliExt_roOk mpl hC))))
    (publicKeyFromSecret_subroutineOk_withTraceEq_keepsFs_vmPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against `CliExt.pubFromSecretSpec C` with
    `withProcessPreserved` and separating `withPubFromSecretRoSep`. -/
theorem pubFromSecret_cliExt_roSep_subroutineOk_withProcessPreserved
    (hPub : PublicKeyFromStaticSecretOk) {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withProcessPreserved
          (withPubFromSecretRoSep mpl
            (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_of_processPreserved (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_withProcessPreserved (pubFromSecret_simulates_cliExt_roSep mpl hC)))
    (publicKeyFromSecret_subroutineOk_withProcessPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against `CliExt.pubFromSecretSpec C` with
    `withRoOk (X25519CliRoOk mpl)` and `withProcessPreserved`. -/
theorem pubFromSecret_cliExt_roOk_subroutineOk_withProcessPreserved
    (hPub : PublicKeyFromStaticSecretOk) {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl)
          (withProcessPreserved
            (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_of_processPreserved (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_withProcessPreserved (pubFromSecret_simulates_cliExt_roOk mpl hC)))
    (publicKeyFromSecret_subroutineOk_withProcessPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against
    `CliExt.pureByteFunctionSpec x25519PubFromSecretRef byVal` with `keepsFs`, `withVmPreserved`,
    and separating `withPubFromSecretRoSep`. -/
theorem pubFromSecret_pureByteFunction_roSep_subroutineOk_keepsFs_vmPreserved
    (hPub : PublicKeyFromStaticSecretOk) (byVal : Bool)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        keepsFs (withVmPreserved
          (withPubFromSecretRoSep mpl (pureByteFunctionSpec x25519PubFromSecretRef byVal))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_comm_traceEq_keepsFs_vm (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved
            (pubFromSecret_simulates_pureByteFunction_roSep mpl byVal))))
    (publicKeyFromSecret_subroutineOk_withTraceEq_keepsFs_vmPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against
    `CliExt.pureByteFunctionSpec x25519PubFromSecretRef byVal` with `withRoOk (X25519CliRoOk mpl)`,
    `keepsFs`, and `withVmPreserved`. -/
theorem pubFromSecret_pureByteFunction_roOk_subroutineOk_keepsFs_vmPreserved
    (hPub : PublicKeyFromStaticSecretOk) (byVal : Bool)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl)
          (keepsFs (withVmPreserved (pureByteFunctionSpec x25519PubFromSecretRef byVal))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_comm_traceEq_keepsFs_vm (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved
            (pubFromSecret_simulates_pureByteFunction_roOk mpl byVal))))
    (publicKeyFromSecret_subroutineOk_withTraceEq_keepsFs_vmPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against
    `CliExt.pureByteFunctionSpec x25519PubFromSecretRef byVal` with `withProcessPreserved`
    and separating `withPubFromSecretRoSep`. -/
theorem pubFromSecret_pureByteFunction_roSep_subroutineOk_withProcessPreserved
    (hPub : PublicKeyFromStaticSecretOk) (byVal : Bool)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withProcessPreserved
          (withPubFromSecretRoSep mpl (pureByteFunctionSpec x25519PubFromSecretRef byVal)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_of_processPreserved (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_withProcessPreserved
          (pubFromSecret_simulates_pureByteFunction_roSep mpl byVal)))
    (publicKeyFromSecret_subroutineOk_withProcessPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against
    `CliExt.pureByteFunctionSpec x25519PubFromSecretRef byVal` with `withRoOk (X25519CliRoOk mpl)`
    and `withProcessPreserved`. -/
theorem pubFromSecret_pureByteFunction_roOk_subroutineOk_withProcessPreserved
    (hPub : PublicKeyFromStaticSecretOk) (byVal : Bool)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl)
          (withProcessPreserved (pureByteFunctionSpec x25519PubFromSecretRef byVal)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_of_processPreserved (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_withProcessPreserved
          (pubFromSecret_simulates_pureByteFunction_roOk mpl byVal)))
    (publicKeyFromSecret_subroutineOk_withProcessPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against
    `Alloc.derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk` (`1904 ≤ stk ≤ 2 ^ 64`)
    with `keepsFs`, `withVmPreserved`, and separating `withPubFromSecretRoSep`. -/
theorem pubFromSecret_derivePublicKeyBytesStack_roSep_subroutineOk_keepsFs_vmPreserved
    (hPub : PublicKeyFromStaticSecretOk) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        keepsFs (withVmPreserved
          (withPubFromSecretRoSep mpl
            (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_dup_vm_in_traceEq_keepsFs (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved
            (pubFromSecret_simulates_derivePublicKeyBytesStack_roSep mpl hlo hhi))))
    (publicKeyFromSecret_subroutineOk_withTraceEq_keepsFs_vmPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against
    `Alloc.derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk` (`1904 ≤ stk ≤ 2 ^ 64`)
    with `withRoOk (X25519CliRoOk mpl)`, `keepsFs`, and `withVmPreserved`. -/
theorem pubFromSecret_derivePublicKeyBytesStack_roOk_subroutineOk_keepsFs_vmPreserved
    (hPub : PublicKeyFromStaticSecretOk) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl)
          (keepsFs (withVmPreserved
            (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_dup_vm_in_traceEq_keepsFs (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved
            (pubFromSecret_simulates_derivePublicKeyBytesStack_roOk mpl hlo hhi))))
    (publicKeyFromSecret_subroutineOk_withTraceEq_keepsFs_vmPreserved hPub externs)

/-- Direct `subroutineOk` for `pubFromSecretSym` (`Blk18`) against
    `withPubFromSecretRoSep mpl (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)`. -/
theorem pubFromSecret_derivePublicKeyBytesStack_roSep_subroutineOk
    (hPub : PublicKeyFromStaticSecretOk) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withPubFromSecretRoSep mpl (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun _ => specSimulates_drop_keepsFs_vm _)
    (pubFromSecret_derivePublicKeyBytesStack_roSep_subroutineOk_keepsFs_vmPreserved
      hPub hlo hhi externs)

/-- Direct `subroutineOk` for `pubFromSecretSym` (`Blk18`) against
    `withRoOk (X25519CliRoOk mpl) (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)`. -/
theorem pubFromSecret_derivePublicKeyBytesStack_roOk_subroutineOk
    (hPub : PublicKeyFromStaticSecretOk) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl) (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => (specSimulates_drop_keepsFs_vm (withRoOk (X25519CliRoOk mpl) _)))
    (pubFromSecret_derivePublicKeyBytesStack_roOk_subroutineOk_keepsFs_vmPreserved
      hPub hlo hhi externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against
    `Alloc.derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk` (`1904 ≤ stk ≤ 2 ^ 64`)
    with `withProcessPreserved` and separating `withPubFromSecretRoSep`. -/
theorem pubFromSecret_derivePublicKeyBytesStack_roSep_subroutineOk_withProcessPreserved
    (hPub : PublicKeyFromStaticSecretOk) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withProcessPreserved
          (withPubFromSecretRoSep mpl
            (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_vm_of_processPreserved (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_withProcessPreserved
          (pubFromSecret_simulates_derivePublicKeyBytesStack_roSep mpl hlo hhi)))
    (publicKeyFromSecret_subroutineOk_withProcessPreserved hPub externs)

/-- `subroutineOk` for `pubFromSecretSym` (`Blk18`) against
    `Alloc.derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk` (`1904 ≤ stk ≤ 2 ^ 64`)
    with `withRoOk (X25519CliRoOk mpl)` and `withProcessPreserved`. -/
theorem pubFromSecret_derivePublicKeyBytesStack_roOk_subroutineOk_withProcessPreserved
    (hPub : PublicKeyFromStaticSecretOk) {stk : Nat}
    (hlo : 1904 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk pubFromSecretSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl)
          (withProcessPreserved
            (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_vm_of_processPreserved (publicKeyFromSecretSpec mpl)).trans
        (specSimulates_withProcessPreserved
          (pubFromSecret_simulates_derivePublicKeyBytesStack_roOk mpl hlo hhi)))
    (publicKeyFromSecret_subroutineOk_withProcessPreserved hPub externs)

/-! ### 3.3 `<StaticSecret>::diffie_hellman` (`Blk17`, Stack `≥ 1808`) Consumer Bridges -/

/-- `Spec.withTraceEq (staticSecretDiffieHellmanSpec mpl)` simulates stack-parameterized
    `withDiffieHellmanRoSep mpl (withStack (LibsignalTripleRatchet.diffieHellmanSpec x25519Ref) stk)`
    for any stack budget `1808 ≤ stk ≤ 2 ^ 64`. -/
theorem diffieHellman_simulates_hooks_roSep (mpl : MultiPlacement) {stk : Nat}
    (hlo : 1808 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide) :
    SpecSimulates (Spec.withTraceEq (staticSecretDiffieHellmanSpec mpl))
      (withDiffieHellmanRoSep mpl
        (withStack
          (CryptoVerification.LibsignalTripleRatchet.diffieHellmanSpec x25519Ref)
          stk)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨secA, sec, pubA, pub, ret⟩ R s0 hpre
  dsimp only [withDiffieHellmanRoSep, withRoDataSep, withStack,
    CryptoVerification.LibsignalTripleRatchet.diffieHellmanSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ⌜_ ∧ _ ∧ _⌝,
    sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜_ ∧ _ ∧ _⌝,
    satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx8⟩, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes ret 32 (by decide),
    stackAt_shrink s0.sp stk 1808 hlo hhi,
    stackAt_eq_stackFrameAt s0.sp 1808 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨out_bs, hpre⟩ := hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (pubA ↦ₛ pub.toList) ⌜out_bs.length = 32⌝,
    sepConj_left_comm (secA ↦ₛ sec.toList) ⌜out_bs.length = 32⌝,
    sepConj_left_comm (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ⌜out_bs.length = 32⌝,
    sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜out_bs.length = 32⌝,
    satisfies_pure_sepConj] at hpre
  obtain ⟨hout_len, hpre⟩ := hpre
  refine ⟨(ret, secA, pubA, out_bs, sec.toList, pub.toList),
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 1808) ∗ R, ?_, ?_⟩
  · dsimp only [Spec.withTraceEq, staticSecretDiffieHellmanSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hout_len, sec.2, pub.2⟩, Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret hcc hpost
    dsimp only [Spec.withTraceEq, staticSecretDiffieHellmanSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hpost⟩ := hpost
    have hsf_frame : stackFrame sf 1808 = stackFrameAt s0.sp 1808 := by
      unfold stackFrame
      rw [hcc.1]
      exact stackAt_eq_stackFrameAt s0.sp 1808 (by decide)
    rw [hsf_frame] at hpost
    dsimp only [withDiffieHellmanRoSep, withRoDataSep, withStack,
      CryptoVerification.LibsignalTripleRatchet.diffieHellmanSpec,
      x25519Ref_toList]
    rw [stackAt_shrink s0.sp stk 1808 hlo hhi,
      stackAt_eq_stackFrameAt s0.sp 1808 (by decide)]
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ⌜sf.trace = s0.trace⌝,
      sepConj_left_comm (fe51_one mpl ↦ᵣ fe51OneBytes) ⌜sf.trace = s0.trace⌝,
      satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.mono (by sep_entail) hpost⟩

/-- Pure `X25519CliRoOk` simulation for stack-parameterized
    `LibsignalTripleRatchet.diffieHellmanSpec x25519Ref`. -/
theorem diffieHellman_simulates_hooks_roOk (mpl : MultiPlacement) {stk : Nat}
    (hlo : 1808 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide) :
    SpecSimulates (Spec.withTraceEq (staticSecretDiffieHellmanSpec mpl))
      (withRoOk (X25519CliRoOk mpl)
        (withStack
          (CryptoVerification.LibsignalTripleRatchet.diffieHellmanSpec x25519Ref)
          stk)) :=
  (diffieHellman_simulates_hooks_roSep mpl hlo hhi).trans
    (specSimulates_absorb_diffieHellmanRoSep mpl _)

/-- `CliExt.dhSpec C` simulation in separating `withDiffieHellmanRoSep` form
    (under `C.X = x25519Ref`). -/
theorem diffieHellman_simulates_cliExt_roSep (mpl : MultiPlacement) {C : Crypto}
    (hC : C.X = x25519Ref) :
    SpecSimulates (Spec.withTraceEq (staticSecretDiffieHellmanSpec mpl))
      (withDiffieHellmanRoSep mpl (dhSpec C)) := by
  have heq : dhSpec C =
      withStack
        (CryptoVerification.LibsignalTripleRatchet.diffieHellmanSpec x25519Ref)
        extHookStack := by
    rw [← hC]; rfl
  rw [heq]
  exact diffieHellman_simulates_hooks_roSep mpl (by decide) (by decide)

/-- `CliExt.dhSpec C` simulation in pure `withRoOk (X25519CliRoOk mpl)` form
    (under `C.X = x25519Ref`). -/
theorem diffieHellman_simulates_cliExt_roOk (mpl : MultiPlacement) {C : Crypto}
    (hC : C.X = x25519Ref) :
    SpecSimulates (Spec.withTraceEq (staticSecretDiffieHellmanSpec mpl))
      (withRoOk (X25519CliRoOk mpl) (dhSpec C)) :=
  (diffieHellman_simulates_cliExt_roSep mpl hC).trans
    (specSimulates_absorb_diffieHellmanRoSep mpl _)

/-- `subroutineOk` for `diffieHellmanSym` (`Blk17`) against stack-parameterized
    `LibsignalTripleRatchet.diffieHellmanSpec x25519Ref` with `keepsFs`, `withVmPreserved`,
    and separating `withDiffieHellmanRoSep`. -/
theorem diffieHellman_hooks_roSep_subroutineOk_keepsFs_vmPreserved
    (hDH : StaticSecretDiffieHellmanOk) {stk : Nat}
    (hlo : 1808 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl =>
        keepsFs (withVmPreserved
          (withDiffieHellmanRoSep mpl
            (withStack
              (CryptoVerification.LibsignalTripleRatchet.diffieHellmanSpec x25519Ref)
              stk))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_comm_traceEq_keepsFs_vm (staticSecretDiffieHellmanSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved (diffieHellman_simulates_hooks_roSep mpl hlo hhi))))
    (staticSecretDiffieHellman_subroutineOk_withTraceEq_keepsFs_vmPreserved hDH externs)

/-- `subroutineOk` for `diffieHellmanSym` (`Blk17`) against stack-parameterized
    `LibsignalTripleRatchet.diffieHellmanSpec x25519Ref` with `withRoOk (X25519CliRoOk mpl)`,
    `keepsFs`, and `withVmPreserved`. -/
theorem diffieHellman_hooks_roOk_subroutineOk_keepsFs_vmPreserved
    (hDH : StaticSecretDiffieHellmanOk) {stk : Nat}
    (hlo : 1808 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl)
          (keepsFs (withVmPreserved
            (withStack
              (CryptoVerification.LibsignalTripleRatchet.diffieHellmanSpec x25519Ref)
              stk))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_comm_traceEq_keepsFs_vm (staticSecretDiffieHellmanSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved (diffieHellman_simulates_hooks_roOk mpl hlo hhi))))
    (staticSecretDiffieHellman_subroutineOk_withTraceEq_keepsFs_vmPreserved hDH externs)

/-- `subroutineOk` for `diffieHellmanSym` (`Blk17`) against stack-parameterized
    `LibsignalTripleRatchet.diffieHellmanSpec x25519Ref` with `withProcessPreserved`
    and separating `withDiffieHellmanRoSep`. -/
theorem diffieHellman_hooks_roSep_subroutineOk_withProcessPreserved
    (hDH : StaticSecretDiffieHellmanOk) {stk : Nat}
    (hlo : 1808 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl =>
        withProcessPreserved
          (withDiffieHellmanRoSep mpl
            (withStack
              (CryptoVerification.LibsignalTripleRatchet.diffieHellmanSpec x25519Ref)
              stk)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_of_processPreserved (staticSecretDiffieHellmanSpec mpl)).trans
        (specSimulates_withProcessPreserved (diffieHellman_simulates_hooks_roSep mpl hlo hhi)))
    (staticSecretDiffieHellman_subroutineOk_withProcessPreserved hDH externs)

/-- `subroutineOk` for `diffieHellmanSym` (`Blk17`) against stack-parameterized
    `LibsignalTripleRatchet.diffieHellmanSpec x25519Ref` with `withRoOk (X25519CliRoOk mpl)`
    and `withProcessPreserved`. -/
theorem diffieHellman_hooks_roOk_subroutineOk_withProcessPreserved
    (hDH : StaticSecretDiffieHellmanOk) {stk : Nat}
    (hlo : 1808 ≤ stk) (hhi : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl =>
        withRoOk (X25519CliRoOk mpl)
          (withProcessPreserved
            (withStack
              (CryptoVerification.LibsignalTripleRatchet.diffieHellmanSpec x25519Ref)
              stk)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_of_processPreserved (staticSecretDiffieHellmanSpec mpl)).trans
        (specSimulates_withProcessPreserved (diffieHellman_simulates_hooks_roOk mpl hlo hhi)))
    (staticSecretDiffieHellman_subroutineOk_withProcessPreserved hDH externs)

/-- `subroutineOk` for `diffieHellmanSym` (`Blk17`) against `CliExt.dhSpec C` with `keepsFs`,
    `withVmPreserved`, and separating `withDiffieHellmanRoSep`. -/
theorem diffieHellman_cliExt_roSep_subroutineOk_keepsFs_vmPreserved
    (hDH : StaticSecretDiffieHellmanOk) {C : Crypto} (hC : C.X = x25519Ref)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl => keepsFs (withVmPreserved (withDiffieHellmanRoSep mpl (dhSpec C))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_comm_traceEq_keepsFs_vm (staticSecretDiffieHellmanSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved (diffieHellman_simulates_cliExt_roSep mpl hC))))
    (staticSecretDiffieHellman_subroutineOk_withTraceEq_keepsFs_vmPreserved hDH externs)

/-- `subroutineOk` for `diffieHellmanSym` (`Blk17`) against `CliExt.dhSpec C` with
    `withRoOk (X25519CliRoOk mpl)`, `keepsFs`, and `withVmPreserved`. -/
theorem diffieHellman_cliExt_roOk_subroutineOk_keepsFs_vmPreserved
    (hDH : StaticSecretDiffieHellmanOk) {C : Crypto} (hC : C.X = x25519Ref)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl => withRoOk (X25519CliRoOk mpl) (keepsFs (withVmPreserved (dhSpec C))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_comm_traceEq_keepsFs_vm (staticSecretDiffieHellmanSpec mpl)).trans
        (specSimulates_keepsFs
          (specSimulates_withVmPreserved (diffieHellman_simulates_cliExt_roOk mpl hC))))
    (staticSecretDiffieHellman_subroutineOk_withTraceEq_keepsFs_vmPreserved hDH externs)

/-- `subroutineOk` for `diffieHellmanSym` (`Blk17`) against `CliExt.dhSpec C` with
    `withProcessPreserved` and separating `withDiffieHellmanRoSep`. -/
theorem diffieHellman_cliExt_roSep_subroutineOk_withProcessPreserved
    (hDH : StaticSecretDiffieHellmanOk) {C : Crypto} (hC : C.X = x25519Ref)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl => withProcessPreserved (withDiffieHellmanRoSep mpl (dhSpec C)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_of_processPreserved (staticSecretDiffieHellmanSpec mpl)).trans
        (specSimulates_withProcessPreserved (diffieHellman_simulates_cliExt_roSep mpl hC)))
    (staticSecretDiffieHellman_subroutineOk_withProcessPreserved hDH externs)

/-- `subroutineOk` for `diffieHellmanSym` (`Blk17`) against `CliExt.dhSpec C` with
    `withRoOk (X25519CliRoOk mpl)` and `withProcessPreserved`. -/
theorem diffieHellman_cliExt_roOk_subroutineOk_withProcessPreserved
    (hDH : StaticSecretDiffieHellmanOk) {C : Crypto} (hC : C.X = x25519Ref)
    (externs : String → Option (State → State) := fun _ => none) :
    x25519CliMultiLib.subroutineOk diffieHellmanSym
      (fun mpl => withRoOk (X25519CliRoOk mpl) (withProcessPreserved (dhSpec C)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (specSimulates_traceEq_of_processPreserved (staticSecretDiffieHellmanSpec mpl)).trans
        (specSimulates_withProcessPreserved (diffieHellman_simulates_cliExt_roOk mpl hC)))
    (staticSecretDiffieHellman_subroutineOk_withProcessPreserved hDH externs)

/-! ## 4. Pure Algebraic Satisfaction Lemmas for `(x25519Ref, x25519PubFromSecretRef)` -/

/-! ### 4.1 Little-Endian Codec Bridges (`leBytesToNat` & `decodeU255`) -/

/-- `leBytesToNat bs` agrees with structural little-endian recursion `x + 256 * acc` over
    `bs.map BitVec.toNat` (matching `DY.X25519.leValue (bs.map BitVec.toNat)`). -/
theorem leBytesToNat_eq_nat_rec (bs : List (BitVec 8)) :
    leBytesToNat bs = List.rec 0 (fun x _ acc => x + 256 * acc) (bs.map BitVec.toNat) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [leBytesToNat_cons, List.map_cons]
    change leBytesToNat bs * 256 + b.toNat =
      b.toNat + 256 * List.rec 0 (fun x _ acc => x + 256 * acc) (bs.map BitVec.toNat)
    omega

/-- `List.foldr` variant of `leBytesToNat_eq_nat_rec`. -/
theorem leBytesToNat_eq_foldr_toNat (bs : List (BitVec 8)) :
    leBytesToNat bs = (bs.map BitVec.toNat).foldr (fun x acc => x + 256 * acc) 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [leBytesToNat_cons, List.map_cons, List.foldr_cons]
    omega

/-- On any 32-byte list `bs`, `decodeU255 bs % p25519` equals the `List.rec` little-endian
    integer modulo `2 ^ 255` and modulo `p25519` (matching `DY.X25519.uCoord (bs.map BitVec.toNat)`). -/
theorem decodeU255_mod_p_eq_nat_rec_of_length_32 {bs : List (BitVec 8)} (hbs : bs.length = 32) :
    decodeU255 bs % p25519 =
      (List.rec 0 (fun x _ acc => x + 256 * acc) (bs.map BitVec.toNat)) % (2 ^ 255) % p25519 := by
  unfold decodeU255
  rw [List.take_of_length_le (Nat.le_of_eq hbs), leBytesToNat_eq_nat_rec]

/-! ### 4.2 Scalar Clamping Idempotence & `SignalPqxdh.clampScalar25519` Byte-List Bridges -/

private theorem clamp_b0_idem_bv (b : BitVec 8) :
    (b &&& 0xf8#8) &&& 0xf8#8 = b &&& 0xf8#8 := by
  revert b; decide

private theorem clamp_b31_idem_bv (b : BitVec 8) :
    (((b &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8 = (b &&& 0x7f#8) ||| 0x40#8 := by
  revert b; decide

private theorem uint8_clamp_b0_toBitVec (b : UInt8) :
    (b &&& 0xF8).toBitVec = b.toBitVec &&& 0xf8#8 := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_clamp_b31_toBitVec (b : UInt8) :
    ((b &&& 0x7F) ||| 0x40).toBitVec = (b.toBitVec &&& 0x7f#8) ||| 0x40#8 := by
  rcases b with ⟨bv⟩
  revert bv; decide

/-- `clampScalarBytes` is idempotent on every 32-byte scalar `s`. -/
theorem clampScalarBytes_idem {s : List (BitVec 8)} (hs : s.length = 32) :
    clampScalarBytes (clampScalarBytes s) = clampScalarBytes s := by
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (exfalso; simp at hs; done)
  change [(b0 &&& 0xf8#8) &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13,
      b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      (((b31 &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8] =
    [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
      b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      (b31 &&& 0x7f#8) ||| 0x40#8]
  rw [clamp_b0_idem_bv, clamp_b31_idem_bv]

/-- `clampScalar` is invariant under pre-clamping by `clampScalarBytes` on 32-byte lists. -/
theorem clampScalar_clampScalarBytes {s : List (BitVec 8)} (hs : s.length = 32) :
    clampScalar (clampScalarBytes s) = clampScalar s := by
  have hcs : (clampScalarBytes s).length = 32 := clampScalarBytes_length_of_eq32 hs
  simp only [clampScalar, List.take_of_length_le (Nat.le_of_eq hcs),
    List.take_of_length_le (Nat.le_of_eq hs), clampScalarBytes_idem hs]

/-- `x25519` is invariant under pre-clamping `s` with `clampScalarBytes` (`s.length = 32`). -/
theorem x25519_clampScalarBytes {s : List (BitVec 8)} (hs : s.length = 32)
    (pk : List (BitVec 8)) :
    x25519 (clampScalarBytes s) pk = x25519 s pk := by
  simp only [x25519, clampScalar_clampScalarBytes hs]

/-- `x25519Pubkey` is invariant under pre-clamping `s` with `clampScalarBytes` (`s.length = 32`). -/
theorem x25519Pubkey_clampScalarBytes {s : List (BitVec 8)} (hs : s.length = 32) :
    x25519Pubkey (clampScalarBytes s) = x25519Pubkey s :=
  x25519_clampScalarBytes hs x25519Basepoint

/-- Re-export of `x25519Ref` clamping idempotence under `CryptoGames.Ratchet.clampScalar`. -/
theorem x25519Ref_clampScalar (sec pub : List.Vector (BitVec 8) 32) :
    x25519Ref (CryptoGames.Ratchet.clampScalar sec) pub = x25519Ref sec pub :=
  x25519Ref_clampScalar_eq sec pub

/-- Re-export of `x25519PubFromSecretRef` clamping idempotence under
    `CryptoGames.Ratchet.clampScalar`. -/
theorem x25519PubFromSecretRef_clampScalar (sec : List.Vector (BitVec 8) 32) :
    x25519PubFromSecretRef (CryptoGames.Ratchet.clampScalar sec) = x25519PubFromSecretRef sec :=
  x25519PubFromSecretRef_clampScalar_eq sec

/-- Exact byte-list equivalence between `SignalPqxdh.clampScalar25519 sk` and `clampScalarBytes`
    for arbitrary `sk : SignalPqxdh.Bytes` (via `SignalPqxdh.fitBytesRef 32 sk`). -/
theorem signalPqxdh_clampScalar25519_map_toBitVec (sk : SignalPqxdh.Bytes) :
    (SignalPqxdh.clampScalar25519 sk).map UInt8.toBitVec =
      clampScalarBytes ((SignalPqxdh.fitBytesRef 32 sk).map UInt8.toBitVec) := by
  have hs : (SignalPqxdh.fitBytesRef 32 sk).length = 32 := SignalPqxdh.fitBytesRef_length 32 sk
  unfold SignalPqxdh.clampScalar25519
  generalize SignalPqxdh.fitBytesRef 32 sk = s at hs ⊢
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (exfalso; simp at hs; done)
  change [(b0 &&& 0xF8).toBitVec, b1.toBitVec, b2.toBitVec, b3.toBitVec, b4.toBitVec,
      b5.toBitVec, b6.toBitVec, b7.toBitVec, b8.toBitVec, b9.toBitVec, b10.toBitVec,
      b11.toBitVec, b12.toBitVec, b13.toBitVec, b14.toBitVec, b15.toBitVec, b16.toBitVec,
      b17.toBitVec, b18.toBitVec, b19.toBitVec, b20.toBitVec, b21.toBitVec, b22.toBitVec,
      b23.toBitVec, b24.toBitVec, b25.toBitVec, b26.toBitVec, b27.toBitVec, b28.toBitVec,
      b29.toBitVec, b30.toBitVec, ((b31 &&& 0x7F) ||| 0x40).toBitVec] =
    [b0.toBitVec &&& 0xf8#8, b1.toBitVec, b2.toBitVec, b3.toBitVec, b4.toBitVec,
      b5.toBitVec, b6.toBitVec, b7.toBitVec, b8.toBitVec, b9.toBitVec, b10.toBitVec,
      b11.toBitVec, b12.toBitVec, b13.toBitVec, b14.toBitVec, b15.toBitVec, b16.toBitVec,
      b17.toBitVec, b18.toBitVec, b19.toBitVec, b20.toBitVec, b21.toBitVec, b22.toBitVec,
      b23.toBitVec, b24.toBitVec, b25.toBitVec, b26.toBitVec, b27.toBitVec, b28.toBitVec,
      b29.toBitVec, b30.toBitVec, (b31.toBitVec &&& 0x7f#8) ||| 0x40#8]
  rw [uint8_clamp_b0_toBitVec, uint8_clamp_b31_toBitVec]

/-- `SignalPqxdh.clampScalar25519 sk` always has length `32`. -/
theorem signalPqxdh_clampScalar25519_length (sk : SignalPqxdh.Bytes) :
    (SignalPqxdh.clampScalar25519 sk).length = 32 := by
  have h := congrArg List.length (signalPqxdh_clampScalar25519_map_toBitVec sk)
  have hs : ((SignalPqxdh.fitBytesRef 32 sk).map UInt8.toBitVec).length = 32 := by
    simp [SignalPqxdh.fitBytesRef_length]
  simpa [clampScalarBytes_length_of_eq32 hs] using h

/-- On 32-byte `SignalPqxdh.Bytes` lists, `SignalPqxdh.clampScalar25519 sk` maps directly to
    `clampScalarBytes (sk.map UInt8.toBitVec)`. -/
theorem signalPqxdh_clampScalar25519_map_toBitVec_of_length_32 {sk : SignalPqxdh.Bytes}
    (hsk : sk.length = 32) :
    (SignalPqxdh.clampScalar25519 sk).map UInt8.toBitVec =
      clampScalarBytes (sk.map UInt8.toBitVec) := by
  have hfit : SignalPqxdh.fitBytesRef 32 sk = sk := by
    simp [SignalPqxdh.fitBytesRef, hsk]
  rw [signalPqxdh_clampScalar25519_map_toBitVec, hfit]

/-- On 32-byte `BitVec 8` lists, `(clampScalarBytes bs).map UInt8.ofBitVec` equals
    `SignalPqxdh.clampScalar25519 (bs.map UInt8.ofBitVec)`. -/
theorem clampScalarBytes_map_ofBitVec_eq_signalPqxdh {bs : List (BitVec 8)}
    (hbs : bs.length = 32) :
    (clampScalarBytes bs).map UInt8.ofBitVec =
      SignalPqxdh.clampScalar25519 (bs.map UInt8.ofBitVec) := by
  have hlen : (bs.map UInt8.ofBitVec).length = 32 := by simp [hbs]
  have hmap := signalPqxdh_clampScalar25519_map_toBitVec_of_length_32 hlen
  have hrt : (bs.map UInt8.ofBitVec).map UInt8.toBitVec = bs := by
    simp [List.map_map, Function.comp_def]
  rw [hrt] at hmap
  have hinj := congrArg (List.map UInt8.ofBitVec) hmap.symm
  simpa [List.map_map, Function.comp_def] using hinj

/-- Unconditional `WellFormedDh.x25519_clamp` bridge: `x25519` on `(fitBytesRef 32 sk)` is
    invariant under `SignalPqxdh.clampScalar25519` for every `sk : SignalPqxdh.Bytes` (of any length). -/
theorem x25519_signalPqxdh_clampScalar25519_fitBytesRef (sk : SignalPqxdh.Bytes)
    (pk : List (BitVec 8)) :
    x25519 ((SignalPqxdh.fitBytesRef 32 (SignalPqxdh.clampScalar25519 sk)).map UInt8.toBitVec) pk =
      x25519 ((SignalPqxdh.fitBytesRef 32 sk).map UInt8.toBitVec) pk := by
  have hcl_len : (SignalPqxdh.clampScalar25519 sk).length = 32 :=
    signalPqxdh_clampScalar25519_length sk
  have hfit_cl : SignalPqxdh.fitBytesRef 32 (SignalPqxdh.clampScalar25519 sk) =
      SignalPqxdh.clampScalar25519 sk := by
    simp [SignalPqxdh.fitBytesRef, hcl_len]
  have hs_len : ((SignalPqxdh.fitBytesRef 32 sk).map UInt8.toBitVec).length = 32 := by
    simp [SignalPqxdh.fitBytesRef_length]
  rw [hfit_cl, signalPqxdh_clampScalar25519_map_toBitVec, x25519_clampScalarBytes hs_len]

/-- Unconditional `WellFormedDh.x25519Base_clamp` bridge: `x25519Pubkey` on `(fitBytesRef 32 sk)`
    is invariant under `SignalPqxdh.clampScalar25519` for every `sk : SignalPqxdh.Bytes`. -/
theorem x25519Pubkey_signalPqxdh_clampScalar25519_fitBytesRef (sk : SignalPqxdh.Bytes) :
    x25519Pubkey
        ((SignalPqxdh.fitBytesRef 32 (SignalPqxdh.clampScalar25519 sk)).map UInt8.toBitVec) =
      x25519Pubkey ((SignalPqxdh.fitBytesRef 32 sk).map UInt8.toBitVec) :=
  x25519_signalPqxdh_clampScalar25519_fitBytesRef sk x25519Basepoint

/-! ### 4.3 Output Lengths, DH Commutativity, & $u$-Coordinate Congruence -/

/-- Re-export: `x25519 s p` always has length `32`. -/
theorem x25519_out_length (s p : List (BitVec 8)) : (x25519 s p).length = 32 :=
  x25519_length s p

/-- Re-export: `x25519Pubkey s` always has length `32`. -/
theorem x25519Pubkey_out_length (s : List (BitVec 8)) : (x25519Pubkey s).length = 32 :=
  x25519Pubkey_length s

/-- Re-export: Diffie–Hellman commutativity on byte lists (`x25519`). -/
theorem x25519_dh_comm (a b : List (BitVec 8)) :
    x25519 a (x25519Pubkey b) = x25519 b (x25519Pubkey a) :=
  x25519_comm a b

/-- Re-export: Diffie–Hellman commutativity on `List.Vector (BitVec 8) 32` (`x25519Ref`). -/
theorem x25519Ref_dh_comm (a b : List.Vector (BitVec 8) 32) :
    x25519Ref a (x25519PubFromSecretRef b) = x25519Ref b (x25519PubFromSecretRef a) :=
  x25519Ref_comm a b

/-- Re-export: `x25519 s p` depends on `p` only through `decodeU255 p % p25519`. -/
theorem x25519_congr_of_decodeU255_mod_eq (s : List (BitVec 8)) {p1 p2 : List (BitVec 8)}
    (hu : decodeU255 p1 % p25519 = decodeU255 p2 % p25519) :
    x25519 s p1 = x25519 s p2 :=
  x25519_uCoord_congr s p1 p2 hu

/-! ### 4.4 Low-Order / All-Zero Shared-Secret Characterization & Non-Degeneracy -/

/-- Boolean predicate identifying 32-byte X25519 inputs whose decoded $u$-coordinate mod $p_{25519}$
    lies in `lowOrderUs` (matching `DY.X25519.isLowOrderKey (bs.map BitVec.toNat)`). -/
@[expose] def isLowOrderX25519 (bs : List (BitVec 8)) : Bool :=
  bs.length == 32 && lowOrderUs.contains (decodeU255 bs % p25519)

/-- Codec bridge for `isLowOrderX25519` into structural `List.rec` over `bs.map BitVec.toNat`. -/
theorem isLowOrderX25519_eq_nat_rec (bs : List (BitVec 8)) :
    isLowOrderX25519 bs =
      ((bs.map BitVec.toNat).length == 32 &&
        lowOrderUs.contains
          ((List.rec 0 (fun x _ acc => x + 256 * acc) (bs.map BitVec.toNat)) %
            (2 ^ 255) % p25519)) := by
  unfold isLowOrderX25519
  rw [List.length_map]
  by_cases hbs : bs.length = 32
  · simp [hbs, decodeU255_mod_p_eq_nat_rec_of_length_32 hbs]
  · have hbeq : (bs.length == 32) = false := beq_eq_false_iff_ne.mpr hbs
    simp [hbeq]

/-- For any 32-byte public key `pk`, `x25519 s pk = List.replicate 32 0#8` iff
    `isLowOrderX25519 pk = true`. -/
theorem x25519_eq_zero_iff_isLowOrderX25519 (s : List (BitVec 8)) {pk : List (BitVec 8)}
    (hpk : pk.length = 32) :
    x25519 s pk = List.replicate 32 0#8 ↔ isLowOrderX25519 pk = true := by
  rw [x25519_eq_zero_iff_lowOrder]
  unfold isLowOrderX25519
  simp [hpk]

/-- Scalar-independent zero-output equivalence (`WellFormedDh.x25519_zero_iff`): whether
    `x25519 a pk` produces `[0#8; 32]` depends only on `pk`, never on the secret scalar `a`. -/
theorem x25519_zero_iff {a1 a2 pk : List (BitVec 8)}
    (_ha1 : a1.length = 32) (_ha2 : a2.length = 32) (_hpk : pk.length = 32) :
    x25519 a1 pk = List.replicate 32 0#8 ↔ x25519 a2 pk = List.replicate 32 0#8 := by
  rw [x25519_eq_zero_iff_lowOrder, x25519_eq_zero_iff_lowOrder]

/-- Unconditional variant of `x25519_zero_iff` (valid for arbitrary byte lengths). -/
theorem x25519_zero_iff_any (a1 a2 pk : List (BitVec 8)) :
    x25519 a1 pk = List.replicate 32 0#8 ↔ x25519 a2 pk = List.replicate 32 0#8 := by
  rw [x25519_eq_zero_iff_lowOrder, x25519_eq_zero_iff_lowOrder]

/-- Derived public keys never satisfy `isLowOrderX25519` (`isLowOrderX25519 (x25519Pubkey s) = false`). -/
theorem isLowOrderX25519_x25519Pubkey (s : List (BitVec 8)) :
    isLowOrderX25519 (x25519Pubkey s) = false := by
  unfold isLowOrderX25519
  rw [Bool.and_eq_false_iff]
  right
  rw [List.contains_eq_mem, decide_eq_false_iff_not]
  exact x25519Pubkey_not_lowOrder s

/-- `List.Vector` variant: `isLowOrderX25519 (x25519PubFromSecretRef sk).toList = false`. -/
theorem isLowOrderX25519_x25519PubFromSecretRef (sk : List.Vector (BitVec 8) 32) :
    isLowOrderX25519 (x25519PubFromSecretRef sk).toList = false :=
  isLowOrderX25519_x25519Pubkey sk.toList

/-- Re-export (`WellFormedDh.x25519_base_ne_zero`): DH agreement with any derived public key is
    never all-zero. -/
theorem x25519_base_ne_zero (a b : List (BitVec 8)) :
    x25519 a (x25519Pubkey b) ≠ List.replicate 32 0#8 :=
  x25519_pub_ne_zero a b

/-- `List.Vector` variant of `x25519_base_ne_zero`. -/
theorem x25519Ref_base_ne_zero (a b : List.Vector (BitVec 8) 32) :
    (x25519Ref a (x25519PubFromSecretRef b)).toList ≠ List.replicate 32 0#8 :=
  x25519_pub_ne_zero a.toList b.toList

/-- Every derived public key `x25519Pubkey s` decodes to a canonical integer `< p25519`
    (`X25519PubCanonical`). -/
theorem leBytesToNat_x25519Pubkey_lt_p25519 (s : List (BitVec 8)) :
    leBytesToNat (x25519Pubkey s) < p25519 := by
  rw [x25519Pubkey_eq_edNatSmul s]
  have hlt_p : edToMontU (edNatSmul (clampScalar s) edBasepoint) < p25519 := edToMontU_lt _
  have hlt_256 : edToMontU (edNatSmul (clampScalar s) edBasepoint) < 256 ^ 32 :=
    Nat.lt_trans hlt_p (by unfold p25519; decide +kernel)
  rwa [leBytesToNat_natToLeBytes_of_lt hlt_256]

/-! ### 4.5 Canonicality (`canon_base` & `canon_x25519`) -/

/-- Derived public keys are always canonical (`WellFormedDh.canon_base`), including for `s.length = 32`. -/
theorem x25519Pubkey_isCanonical (s : List (BitVec 8)) :
    isCanonicalX25519 (x25519Pubkey s) = true :=
  isCanonicalX25519_x25519Pubkey s

/-- Scalar multiplication preserves `isCanonicalX25519` (`WellFormedDh.canon_x25519`). -/
theorem x25519_preserves_isCanonical {a pk : List (BitVec 8)}
    (_ha : a.length = 32) (hpk : isCanonicalX25519 pk = true) :
    isCanonicalX25519 (x25519 a pk) = true :=
  isCanonicalX25519_x25519 hpk

/-! ### 4.6 Equal-Basepoint Congruence on Canonical & Curve Keys (`x25519_congr_of_base_eq`) -/

private def foldHalf (r : Nat) : Nat :=
  if r ≤ (edOrderL - 1) / 2 then r else edOrderL - r

private theorem foldHalf_le {r : Nat} (hr : r < edOrderL) :
    foldHalf r ≤ (edOrderL - 1) / 2 := by
  have hhalf : 2 * ((edOrderL - 1) / 2) = edOrderL - 1 := by
    unfold edOrderL; decide +kernel
  unfold foldHalf
  split <;> omega

private theorem edNatSmul_mod_ord_of_ord_zero {Q : EdPoint}
    (hQ : edOnCurve Q = true) (hord : edNatSmul edOrderL Q = edZero) (n : Nat) :
    edNatSmul n Q = edNatSmul (n % edOrderL) Q := by
  have hmul : edNatSmul (edOrderL * (n / edOrderL)) Q = edZero := by
    rw [Nat.mul_comm, edNatSmul_mul (n / edOrderL) edOrderL hQ, hord, edNatSmul_edZero]
  have hdiv : n = n % edOrderL + edOrderL * (n / edOrderL) := by
    have := Nat.div_add_mod n edOrderL
    omega
  conv => lhs; rw [hdiv]
  rw [edNatSmul_add (n % edOrderL) (edOrderL * (n / edOrderL)) hQ,
      hmul, edAdd_edZero (edOnCurve_edNatSmul _ hQ)]

private theorem edToMontU_edNatSmul_foldHalf {Q : EdPoint}
    (hQ : edOnCurve Q = true) (hord : edNatSmul edOrderL Q = edZero)
    {r : Nat} (hr : r < edOrderL) :
    edToMontU (edNatSmul r Q) = edToMontU (edNatSmul (foldHalf r) Q) := by
  unfold foldHalf
  split
  · rfl
  · have hsum : edAdd (edNatSmul r Q) (edNatSmul (edOrderL - r) Q) = edZero := by
      rw [← edNatSmul_add r (edOrderL - r) hQ, show r + (edOrderL - r) = edOrderL by omega, hord]
    have hr_on : edOnCurve (edNatSmul r Q) = true := edOnCurve_edNatSmul r hQ
    have hsub_on : edOnCurve (edNatSmul (edOrderL - r) Q) = true :=
      edOnCurve_edNatSmul (edOrderL - r) hQ
    have hneg_on : edOnCurve (edNeg (edNatSmul (edOrderL - r) Q)) = true :=
      edOnCurve_edNeg hsub_on
    have heq_neg : edNatSmul r Q = edNeg (edNatSmul (edOrderL - r) Q) := by
      have h1 := congrArg (fun X => edAdd X (edNeg (edNatSmul (edOrderL - r) Q))) hsum
      rw [edAdd_assoc hr_on hsub_on hneg_on,
          edAdd_edNeg_self hsub_on, edAdd_edZero hr_on,
          edZero_edAdd hneg_on] at h1
      exact h1
    rw [heq_neg, edToMontU_edNeg_of_onCurve hsub_on]

private theorem foldHalf_clampScalar_mod_eq_of_pubkey_eq {a1 a2 : List (BitVec 8)}
    (hpk : x25519Pubkey a1 = x25519Pubkey a2) :
    foldHalf (clampScalar a1 % edOrderL) = foldHalf (clampScalar a2 % edOrderL) := by
  have hordB : edNatSmul edOrderL edBasepoint = edZero := by
    rw [← edNatSmul_mod_edOrderL_edBasepoint edOrderL, Nat.mod_self, edNatSmul_zero]
  have hu_eq : edToMontU (edNatSmul (clampScalar a1) edBasepoint) =
      edToMontU (edNatSmul (clampScalar a2) edBasepoint) := by
    rw [x25519Pubkey_eq_edNatSmul a1, x25519Pubkey_eq_edNatSmul a2] at hpk
    have h1_lt : edToMontU (edNatSmul (clampScalar a1) edBasepoint) < 256 ^ 32 :=
      Nat.lt_trans (edToMontU_lt _) (by unfold p25519; decide +kernel)
    have h2_lt : edToMontU (edNatSmul (clampScalar a2) edBasepoint) < 256 ^ 32 :=
      Nat.lt_trans (edToMontU_lt _) (by unfold p25519; decide +kernel)
    have hinj := congrArg leBytesToNat hpk
    rwa [leBytesToNat_natToLeBytes_of_lt h1_lt, leBytesToNat_natToLeBytes_of_lt h2_lt] at hinj
  have hr1_lt : clampScalar a1 % edOrderL < edOrderL := Nat.mod_lt _ edOrderL_pos
  have hr2_lt : clampScalar a2 % edOrderL < edOrderL := Nat.mod_lt _ edOrderL_pos
  have hf1_le := foldHalf_le hr1_lt
  have hf2_le := foldHalf_le hr2_lt
  have hf1_lt256 : foldHalf (clampScalar a1 % edOrderL) < 2 ^ 256 :=
    Nat.lt_trans (Nat.lt_of_le_of_lt hf1_le (by have := edOrderL_pos; omega)) edOrderL_lt_two_pow_256
  have hf2_lt256 : foldHalf (clampScalar a2 % edOrderL) < 2 ^ 256 :=
    Nat.lt_trans (Nat.lt_of_le_of_lt hf2_le (by have := edOrderL_pos; omega)) edOrderL_lt_two_pow_256
  rw [edNatSmul_mod_ord_of_ord_zero edOnCurve_edBasepoint hordB (clampScalar a1),
      edNatSmul_mod_ord_of_ord_zero edOnCurve_edBasepoint hordB (clampScalar a2),
      edToMontU_edNatSmul_foldHalf edOnCurve_edBasepoint hordB hr1_lt,
      edToMontU_edNatSmul_foldHalf edOnCurve_edBasepoint hordB hr2_lt,
      ← edSmul_eq_edNatSmul hf1_lt256 edOnCurve_edBasepoint,
      ← edSmul_eq_edNatSmul hf2_lt256 edOnCurve_edBasepoint] at hu_eq
  exact (edToMontU_edSmul_edBasepoint_eq_iff hf1_le hf2_le).mp hu_eq

private theorem match_edPoint_eq_true (m : Option VerifiedLibraries.Common.EdPoint)
    (f : VerifiedLibraries.Common.EdPoint → Bool)
    (h : (match m with | none => false | some P => f P) = true) :
    ∃ P, m = some P ∧ f P = true := by
  cases m with
  | none => cases h
  | some P => exact ⟨P, rfl, h⟩

/-- Equal derived public keys imply equal Diffie–Hellman outputs on every canonical public key `pk`
    (`WellFormedDh.x25519_congr_of_base_eq`, canonical branch). -/
theorem x25519_congr_of_pubkey_eq_of_canonical {a1 a2 pk : List (BitVec 8)}
    (_ha1 : a1.length = 32 := by rfl) (_ha2 : a2.length = 32 := by rfl)
    (hcan : isCanonicalX25519 pk = true)
    (hpk : x25519Pubkey a1 = x25519Pubkey a2) :
    x25519 a1 pk = x25519 a2 pk := by
  have hfold := foldHalf_clampScalar_mod_eq_of_pubkey_eq hpk
  unfold isCanonicalX25519 at hcan
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcan
  rcases hcan with ⟨⟨_, _⟩, hmont_cond⟩
  obtain ⟨P, hmont, hmont_cond⟩ := match_edPoint_eq_true _ _ hmont_cond
  rw [beq_iff_eq] at hmont_cond
  have hP_on : edOnCurve P = true := montToEdwards_some_onCurve hmont
  have huP : edToMontU P = decodeU255 pk % p25519 := montToEdwards_some_edToMontU hmont
  have hP_ord : edNatSmul edOrderL P = edZero :=
    (edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 hP_on).symm.trans hmont_cond
  have hladder_mod : ∀ k u, x25519Ladder k (u % p25519) = x25519Ladder k u := by
    intro k u; simp [x25519Ladder]
  have hx_eq : ∀ s : List (BitVec 8),
      x25519 s pk =
        natToLeBytes 32 (edToMontU (edNatSmul (foldHalf (clampScalar s % edOrderL)) P)) := by
    intro s
    unfold x25519
    rw [← hladder_mod (clampScalar s) (decodeU255 pk), ← huP,
        x25519Ladder_edToMontU (clampScalar_lt_two_pow_255 s) hP_on,
        edNatSmul_mod_ord_of_ord_zero hP_on hP_ord (clampScalar s),
        edToMontU_edNatSmul_foldHalf hP_on hP_ord (Nat.mod_lt _ edOrderL_pos)]
  rw [hx_eq a1, hx_eq a2, hfold]

/-- Equal derived public keys imply equal Diffie–Hellman outputs on any derived public key
    `x25519Pubkey b`. -/
theorem x25519_congr_of_pubkey_eq_pubkey (a1 a2 b : List (BitVec 8))
    (hpk : x25519Pubkey a1 = x25519Pubkey a2) :
    x25519 a1 (x25519Pubkey b) = x25519 a2 (x25519Pubkey b) := by
  rw [x25519_comm a1 b, hpk, ← x25519_comm a2 b]

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.ConsumerBridges
