/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacStep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclPure
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacFetch
import LibsignalBinary.Proofs.Common.SharedHelpers
import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers

/-!
# Machine-code proof for `libcrux_hmac::hmac` (SHA-256)

Verifies block `6` (`libcrux_hmac::hmac`, `w0 = 0` SHA-256 arm), parameterized over
`HaclSubroutines P mpl`:

1. Pure segments from `+1004` to `ret`: `opad` 64-byte XOR loop, empty and non-empty inner
   SHA-256 setups, outer SHA-256 setups, three `__rust_dealloc` setups, 32-byte tag allocation
   and OOM handling, 32-byte SIMD tag copy, `Vec<u8>` header, and epilogue.
2. Allocator-independent HACL SHA-256 core (`+1060 → +2140`) computing
   `CryptoGames.HMAC.hmacWith sha256CompressState x.key x.data`.
3. Top-level `subroutine_ok` theorems for
   `LibsignalBinary.Heap.SpecBudget.libcruxHmacBudgetSpec sha256CompressState M A lim` and
   `CryptoVerification.LibsignalSpqrV1.libcruxHmacSpec sha256CompressState A`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmac

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState sha256IV toBEBytes chunks64 sha256With hmacWith)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.RustHeap
  (RustAlloc LayoutOk allocFailedEvent allocFailedIn rustAllocSpec rustDeallocSpec
   vecU8 vecU8At vecHeader allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (extHookStack rustAllocZeroedSpec)
open CryptoVerification.LibsignalSpqrV1 (LibcruxHmacCall libcruxHmacSpec libcruxHmacName)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEvent FitsEvents FitsEnv
   NullAllowed RustLayoutOk VmPreserved OomPreserved AllocCallPreserved
   rustAllocEvents rustDeallocEvents fitsEvents_append not_nullAllowed_of_fitsAllocEvents
   rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliAllocNoOomSpecBase
   subroutine_ok_allocNoOom_of_budgetBase)
open LibsignalBinary.Heap.SpecBudget
  (libcruxHmacSha256Events LibcruxHmacEnv libcruxHmacBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (rustAllocShimVmSpec allocMemcpyVmSpec rustHandleErrorPanicSpec RustStdAllocAuxEntries)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math
  (sha256CompressState pointsToBytes_shaStateBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclPure
  (chunks64_exact_one sha256With_length haclUpdateLastState haclHash256Pure_eq_sha256With
   hmacInnerEmpty_eq_sha256With hmacInnerNonEmpty_eq_sha256With hmacOuter_eq_sha256With)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (libcruxHmacLib HaclPlacement haclMpl
   sha256InitBlock sha256UpdateBlock sha256UpdateNblocksBlock sha256UpdateLastBlock
   sha256FinishBlock hash256Block libcruxHmacBlock
   sha256InitSym sha256UpdateSym sha256UpdateNblocksSym sha256UpdateLastSym
   sha256FinishSym hash256Sym libcruxHmacSym
   rustAllocShimSym rustAllocZeroedSym rustAllocSym rustDeallocSym
   memcpySym rustHandleErrorSym rustUnwrapFailedSym fnAddr_libcruxHmac)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts
  (HaclInProg HaclSubroutines withHaclPreserved execInst_bl_eq codeLoaded_of_steps
   sepWP_block_seg sepWP_block_bl sepWPp_block_seg sepWPp_block_bl sepWPp_block_bl_panic
   sha256InitRawSpec sha256UpdateNblocksSpec sha256UpdateLastSpec sha256FinishRawSpec hash256Spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift
  (ProcessFieldsPreserved_toHeapVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacFetch
  (haclLib6 haclTree6 hacl6_code_eq hacl6_tree_size
   haclPl6 haclPC6 haclPC6_eq_blockProgram haclPl6_base haclPl6_rho)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacStep
  (libcruxHmacKeyBlock libcruxHmacInnerPure libcruxHmacPure
   libcruxHmacKeyBlock_eq libcruxHmacKeyBlock_length
   libcruxHmacInnerPure_eq_sha256With libcruxHmacPure_eq_hmacWith
   stackAt_split_hmac stackAt_4096_split_480 stackAt_4096_split_352
   stackAt_4096_split_224 stackAt_4096_split_16
   hmacSavedCalleeRegs pointsTo64_8_replicate64 pointsTo64_4_sha256IV
   tryFromKeyNiche tryFromKeyNiche_bit0_iff tryFromKeyNiche_lsr32
   tryFromDataNiche tryFromDataNiche_bit0_iff tryFromDataNiche_lsr32
   hmac_nonempty_nblk_arith
   hmacMemcpyVmSpec HmacAuxSubroutines memRegion32_elim pts64_4_entails_memRegion32
   vecU8_pack_32 hmacStack224_recombine hmacPrologueSpatial hmacProloguePure
   hmac_seg_oom_key hmac_seg_oom_ipad hmac_seg_oom_opad hmac_seg_unwrap_pre
   hmac_seg_prologue hmac_seg_alloc64_args_key hmac_seg_alloc64_args_ipad
   hmac_seg_alloc64_args_opad hmac_seg_key_short hmac_seg_after_memcpy
   hmac_seg_ipad_xor xor_w32_to8_a xor_w32_to8_b xor_w32_to8_c)

arm64_proof_prelude

@[wp_norm]
private theorem zeroExtend_32_64_eq_setWidth (x : BitVec 32) :
    BitVec.zeroExtend 64 x = BitVec.setWidth 64 x := rfl

/-! ## 1. Block 6 Symbol Resolution & Placed `BL` Fetch Lemmas -/

private theorem add_off_rel_target (base target off : BitVec 64) :
    (base + off) + ((target - base) - off) = target := by bv_omega

private theorem resolve_sha256Init (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl sha256InitSym = mpl.base 0 := by
  simp [Obj.MultiPlacedLib.resolve, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256InitSym]

private theorem resolve_sha256UpdateNblocks (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl sha256UpdateNblocksSym = mpl.base 2 := by
  simp [Obj.MultiPlacedLib.resolve, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256InitSym, sha256UpdateSym, sha256UpdateNblocksSym]

private theorem resolve_sha256UpdateLast (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl sha256UpdateLastSym = mpl.base 3 := by
  simp [Obj.MultiPlacedLib.resolve, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256InitSym, sha256UpdateSym, sha256UpdateNblocksSym,
    sha256UpdateLastSym]

private theorem resolve_sha256Finish (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl sha256FinishSym = mpl.base 4 := by
  simp [Obj.MultiPlacedLib.resolve, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256FinishBlock, sha256InitSym, sha256UpdateSym,
    sha256UpdateNblocksSym, sha256UpdateLastSym, sha256FinishSym]

private theorem resolve_hash256 (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl hash256Sym = mpl.base 5 := by
  simp [Obj.MultiPlacedLib.resolve, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256FinishBlock, hash256Block, sha256InitSym, sha256UpdateSym,
    sha256UpdateNblocksSym, sha256UpdateLastSym, sha256FinishSym, hash256Sym]

private theorem resolve_ext_sym (mpl : Obj.MultiPlacement) (sym : String)
    (h0 : sym ≠ sha256InitSym) (h1 : sym ≠ sha256UpdateSym)
    (h2 : sym ≠ sha256UpdateNblocksSym) (h3 : sym ≠ sha256UpdateLastSym)
    (h4 : sym ≠ sha256FinishSym) (h5 : sym ≠ hash256Sym) (h6 : sym ≠ libcruxHmacSym) :
    libcruxHmacLib.resolve mpl sym = mpl.ρ sym := by
  simp [Obj.MultiPlacedLib.resolve, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256FinishBlock, hash256Block, libcruxHmacBlock,
    h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm]

private theorem resolve_shim (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl rustAllocShimSym = mpl.ρ rustAllocShimSym :=
  resolve_ext_sym mpl rustAllocShimSym
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem resolve_allocZeroed (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl rustAllocZeroedSym = mpl.ρ rustAllocZeroedSym :=
  resolve_ext_sym mpl rustAllocZeroedSym
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem resolve_alloc (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl rustAllocSym = mpl.ρ rustAllocSym :=
  resolve_ext_sym mpl rustAllocSym
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem resolve_dealloc (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl rustDeallocSym = mpl.ρ rustDeallocSym :=
  resolve_ext_sym mpl rustDeallocSym
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem resolve_memcpy (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl memcpySym = mpl.ρ memcpySym :=
  resolve_ext_sym mpl memcpySym
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem resolve_handleError (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl rustHandleErrorSym = mpl.ρ rustHandleErrorSym :=
  resolve_ext_sym mpl rustHandleErrorSym
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem resolve_unwrapFailed (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl rustUnwrapFailedSym = mpl.ρ rustUnwrapFailedSym :=
  resolve_ext_sym mpl rustUnwrapFailedSym
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem fetch_bl6_of [HaclPlacement] {off tgt : BitVec 64} {sym : String}
    (hf : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch (haclPl6.base + off) =
      some (.bl ((haclPl6.ρ sym - haclPl6.base) - off)))
    (hres : libcruxHmacLib.resolve haclMpl sym = tgt) :
    (libcruxHmacLib.blockProgram haclMpl 6).fetch (haclMpl.base 6 + off) =
      some (.bl ((tgt - haclMpl.base 6) - off)) := by
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base, hf, ← haclPl6_rho, haclPl6_base, hres]

/-! ## 2. Remaining Block 6 Pure Segments (`+1004 → ret`) -/

private theorem hmac_seg_key_long_x4 [HaclPlacement] {s : State} {keyLenBV : BitVec 64} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 268#64) (hrun : s.status = .Running)
    (hpKey : s.readReg64 .x0 ≠ 0#64) (hx23 : s.readReg64 .x23 = keyLenBV)
    (hx25 : s.readReg64 .x25 = tryFromKeyNiche keyLenBV)
    (hk64 : 64 < keyLenBV.toNat) (hk32 : keyLenBV.toNat < 2 ^ 32) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 908#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧ CalleeSavedPreserved (s.writeReg64 .x22 (s.readReg64 .x0)) sf ∧
         sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = 32#64 ∧
         sf.readReg64 .x2 = s.readReg64 .x24 ∧ sf.readReg64 .x3 = keyLenBV ∧
         sf.readReg64 .x4 = keyLenBV) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 268#64 := hpc; clear hpc
  have hne0 : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hpKey
  have hlsr : tryFromKeyNiche keyLenBV >>> 32 = keyLenBV := tryFromKeyNiche_lsr32 keyLenBV hk32
  have hx25_gpr : s.readReg64 (Reg.gpr 25#5) = tryFromKeyNiche keyLenBV := hx25
  have hx23_gpr : s.readReg64 (Reg.gpr 23#5) = keyLenBV := hx23
  have hcmp65_ule : BitVec.ule 65#64 keyLenBV = true := by simp [BitVec.ule]; omega
  have hcmp65_ult : BitVec.ult keyLenBV 65#64 = false := by simp [BitVec.ult]; omega
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 9
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm],
      by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
      by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_opad_xor_loop [HaclPlacement]
    (suff' : List (BitVec 8)) (b : BitVec 8) {pref : List (BitVec 8)}
    {pKey pDst : BitVec 64} {pad : BitVec 8} {s : State} {R : SepProp}
    (hlen : pref.length + (b :: suff').length = 64)
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 1028#64) (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 pref.length)
    (hx22 : s.readReg64 .x22 = pKey) (hx24 : s.readReg64 .x24 = pDst) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 1060#64) s
      ((pKey ↦ₛ (pref ++ b :: suff')) ∗
       (pDst ↦ₛ (pref.map (· ^^^ pad) ++ List.replicate (b :: suff').length pad)) ∗ R)
      (fun sf P' =>
        (sf.sp = s.sp ∧ CalleeSavedPreserved s sf) ∧
        (P' ⊢ (pKey ↦ₛ (pref ++ b :: suff')) ∗
              (pDst ↦ₛ (pref ++ b :: suff').map (· ^^^ pad)) ∗ R)) := by
  induction suff' generalizing b pref s with
  | nil =>
    have hplen : pref.length = 63 := by simp at hlen; omega
    have hpc' : s.pc = haclPl6.base + 1028#64 := hpc; clear hpc
    have hx8_gpr : s.readReg64 (Reg.gpr 8#5) = 63#64 := by
      change s.readReg64 .x8 = 63#64; rw [hx8, hplen]
    have hx22_gpr : s.readReg64 (Reg.gpr 22#5) = pKey := hx22
    have hx24_gpr : s.readReg64 (Reg.gpr 24#5) = pDst := hx24
    have hpre_eq : ((pKey ↦ₛ (pref ++ [b])) ∗
         (pDst ↦ₛ (pref.map (· ^^^ pad) ++ List.replicate 1 pad)) ∗ R) =
        (((pKey + 63#64) ↦₈ b) ∗ ((pDst + 63#64) ↦₈ pad) ∗
         ((pKey ↦ₛ pref) ∗ (pDst ↦ₛ pref.map (· ^^^ pad)) ∗ R)) := by
      rw [show List.replicate 1 pad = [pad] from rfl, pointsToBytes_snoc pKey,
          pointsToBytes_snoc pDst, List.length_map, hplen]
      change ((pKey ↦ₛ pref) ∗ ((pKey + 63#64) ↦₈ b)) ∗
        (((pDst ↦ₛ pref.map (· ^^^ pad)) ∗ ((pDst + 63#64) ↦₈ pad)) ∗ R) = _; sep_ac_rfl
    dsimp only [List.length]
    rw [← haclPC6_eq_blockProgram, ← haclPl6_base, hpre_eq]
    wp_sym_steps 8
    refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
      ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm]⟩, ?_⟩
    try simp only [xor_w32_to8_a, xor_w32_to8_b, xor_w32_to8_c]
    refine Entails.of_eq ?_
    rw [List.map_append, List.map_singleton, pointsToBytes_snoc pKey, pointsToBytes_snoc pDst,
        List.length_map, hplen]
    change (((pKey + 63#64) ↦₈ b) ∗ ((pDst + 63#64) ↦₈ (b ^^^ pad)) ∗
      ((pKey ↦ₛ pref) ∗ (pDst ↦ₛ pref.map (· ^^^ pad)) ∗ R)) =
      ((pKey ↦ₛ pref) ∗ ((pKey + 63#64) ↦₈ b)) ∗
      (((pDst ↦ₛ pref.map (· ^^^ pad)) ∗ ((pDst + 63#64) ↦₈ (b ^^^ pad))) ∗ R); sep_ac_rfl
  | cons b2 suff'' ih =>
    have hlt63 : pref.length < 63 := by simp at hlen; omega
    have hpc' : s.pc = haclPl6.base + 1028#64 := hpc; clear hpc
    have hx8_gpr : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 pref.length := hx8
    have hx22_gpr : s.readReg64 (Reg.gpr 22#5) = pKey := hx22
    have hx24_gpr : s.readReg64 (Reg.gpr 24#5) = pDst := hx24
    have hne64_eq : BitVec.ofNat 64 pref.length + 1#64 ≠ 64#64 := by bv_omega
    have hne64 : (BitVec.ofNat 64 pref.length + 1#64 != 64#64) = true := bne_iff_ne.mpr hne64_eq
    have hbeq64 : (BitVec.ofNat 64 pref.length + 1#64 == 64#64) = false := beq_false_of_ne hne64_eq
    have hpre_eq : ((pKey ↦ₛ (pref ++ b :: b2 :: suff'')) ∗
         (pDst ↦ₛ (pref.map (· ^^^ pad) ++ List.replicate (b :: b2 :: suff'').length pad)) ∗ R) =
        (((pKey + BitVec.ofNat 64 pref.length) ↦₈ b) ∗
         ((pDst + BitVec.ofNat 64 pref.length) ↦₈ pad) ∗
         ((pKey ↦ₛ pref) ∗ ((pKey + BitVec.ofNat 64 (pref.length + 1)) ↦ₛ (b2 :: suff'')) ∗
          (pDst ↦ₛ pref.map (· ^^^ pad)) ∗
          ((pDst + BitVec.ofNat 64 (pref.length + 1)) ↦ₛ List.replicate (b2 :: suff'').length pad) ∗ R)) := by
      rw [show List.replicate (b :: b2 :: suff'').length pad =
          pad :: List.replicate (b2 :: suff'').length pad from rfl,
          pointsToBytes_append pKey, pointsToBytes_cons_off pKey,
          pointsToBytes_append pDst, List.length_map, pointsToBytes_cons_off pDst]; sep_ac_rfl
    rw [← haclPC6_eq_blockProgram, ← haclPl6_base, hpre_eq]
    wp_sym_steps 8
    try simp only [xor_w32_to8_a, xor_w32_to8_b, xor_w32_to8_c]
    have hmid_eq :
        (((pKey + BitVec.ofNat 64 pref.length) ↦₈ b) ∗
         ((pDst + BitVec.ofNat 64 pref.length) ↦₈ (b ^^^ pad)) ∗
         ((pKey ↦ₛ pref) ∗ ((pKey + BitVec.ofNat 64 (pref.length + 1)) ↦ₛ (b2 :: suff'')) ∗
          (pDst ↦ₛ pref.map (· ^^^ pad)) ∗
          ((pDst + BitVec.ofNat 64 (pref.length + 1)) ↦ₛ List.replicate (b2 :: suff'').length pad) ∗ R)) =
        ((pKey ↦ₛ ((pref ++ [b]) ++ b2 :: suff'')) ∗
         (pDst ↦ₛ ((pref ++ [b]).map (· ^^^ pad) ++ List.replicate (b2 :: suff'').length pad)) ∗ R) := by
      rw [List.map_append, List.map_singleton,
          pointsToBytes_append pKey (pref ++ [b]), pointsToBytes_snoc pKey,
          pointsToBytes_append pDst (pref.map (· ^^^ pad) ++ [b ^^^ pad]),
          pointsToBytes_snoc pDst, List.length_append, List.length_singleton,
          List.length_append, List.length_map, List.length_singleton]; sep_ac_rfl
    rw [hmid_eq, haclPC6_eq_blockProgram, haclPl6_base]
    have hlen' : (pref ++ [b]).length + (b2 :: suff'').length = 64 := by simp at hlen ⊢; omega
    refine (ih b2 hlen' ?_ ?_ ?_ ?_ ?_).mono fun sf P' _ _ ⟨⟨hsp_sf, hcs_sf⟩, hent⟩ => ⟨⟨?_, ?_⟩, ?_⟩
    · simp [wp_norm]
    · simp [wp_norm, hrun]
    · simp only [wp_norm, List.length_append, List.length_singleton]; bv_omega
    · simp [wp_norm, hx22]
    · simp [wp_norm, hx24]
    · rw [hsp_sf]; simp [wp_norm]
    · refine CalleeSavedPreserved.trans ?_ hcs_sf
      simp [CalleeSavedPreserved.iff_regs, wp_norm]
    · simpa only [List.append_assoc, List.singleton_append] using hent

private theorem hmac_seg_opad_xor [HaclPlacement] {pKey pOpad : BitVec 64} {k0 : List (BitVec 8)}
    {s : State} {R : SepProp} (hk0 : k0.length = 64)
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 1004#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = pOpad) (hne0 : pOpad ≠ 0#64) (hx22 : s.readReg64 .x22 = pKey) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 1060#64) s
      ((pKey ↦ₛ k0) ∗ memRegion pOpad 64 ∗ R)
      (fun sf P' =>
        (sf.sp = s.sp ∧ CalleeSavedPreserved (s.writeReg64 .x24 pOpad) sf) ∧
        (P' ⊢ (pKey ↦ₛ k0) ∗ (pOpad ↦ₛ k0.map (· ^^^ 0x5c#8)) ∗ R)) := by
  have hpc' : s.pc = haclPl6.base + 1004#64 := hpc; clear hpc
  have hx0_gpr : s.readReg64 (Reg.gpr 0#5) = pOpad := hx0
  have hx22_gpr : s.readReg64 (Reg.gpr 22#5) = pKey := hx22
  have hne0_beq : (pOpad == 0#64) = false := beq_false_of_ne hne0
  have hm64 : (pKey ↦ₛ k0) ∗ memRegion pOpad 64 ∗ R =
      memRegion pOpad 32 ∗ (memRegion (pOpad + 32#64) 32 ∗ ((pKey ↦ₛ k0) ∗ R)) := by
    rw [memRegion_split pOpad 32 32 (by decide)]; sep_ac_rfl
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base, hm64]
  apply memRegion32_elim; intro w0 w1 w2 w3
  rw [show ((pOpad ↦₆₄ w0) ∗ ((pOpad + 8#64) ↦₆₄ w1) ∗ ((pOpad + 16#64) ↦₆₄ w2) ∗
      ((pOpad + 24#64) ↦₆₄ w3) ∗ (memRegion (pOpad + 32#64) 32 ∗ ((pKey ↦ₛ k0) ∗ R))) =
      memRegion (pOpad + 32#64) 32 ∗ ((pOpad ↦₆₄ w0) ∗ ((pOpad + 8#64) ↦₆₄ w1) ∗
      ((pOpad + 16#64) ↦₆₄ w2) ∗ ((pOpad + 24#64) ↦₆₄ w3) ∗ (pKey ↦ₛ k0) ∗ R) by sep_ac_rfl]
  apply memRegion32_elim; intro w4 w5 w6 w7
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_sym_steps 6
  have hfold64 :
      (((pOpad + 32#64) ↦₆₄ 0x5c5c5c5c5c5c5c5c#64) ∗ ((pOpad + 40#64) ↦₆₄ 0x5c5c5c5c5c5c5c5c#64) ∗
       ((pOpad + 48#64) ↦₆₄ 0x5c5c5c5c5c5c5c5c#64) ∗ ((pOpad + 56#64) ↦₆₄ 0x5c5c5c5c5c5c5c5c#64) ∗
       ((pOpad ↦₆₄ 0x5c5c5c5c5c5c5c5c#64) ∗ ((pOpad + 8#64) ↦₆₄ 0x5c5c5c5c5c5c5c5c#64) ∗
        ((pOpad + 16#64) ↦₆₄ 0x5c5c5c5c5c5c5c5c#64) ∗ ((pOpad + 24#64) ↦₆₄ 0x5c5c5c5c5c5c5c5c#64) ∗
        (pKey ↦ₛ k0) ∗ R)) =
      ((pKey ↦ₛ k0) ∗ (pOpad ↦ₛ List.replicate 64 0x5c#8) ∗ R) := by
    rw [← pointsTo64_8_replicate64 pOpad 0x5c#8 0x5c5c5c5c5c5c5c5c#64 (by decide)]; sep_ac_rfl
  rw [hfold64, haclPC6_eq_blockProgram, haclPl6_base]
  match k0, hk0 with
  | b0 :: suff', hk0' =>
    rw [show List.replicate 64 0x5c#8 = List.replicate (b0 :: suff').length 0x5c#8 by rw [hk0']]
    refine (hmac_seg_opad_xor_loop suff' b0 (pref := []) (pKey := pKey) (pDst := pOpad)
      (pad := 0x5c#8) (R := R) (by simpa using hk0') ?_ ?_ ?_ ?_ ?_).mono
      fun sf P' _ _ ⟨⟨hsp_sf, hcs_sf⟩, hent⟩ => ⟨⟨?_, ?_⟩, hent⟩
    · simp [wp_norm]
    · simp [wp_norm, hrun]
    · simp [wp_norm]
    · simp [wp_norm, hx22]
    · simp [wp_norm]
    · rw [hsp_sf]; simp [wp_norm]
    · refine CalleeSavedPreserved.trans ?_ hcs_sf
      simp [CalleeSavedPreserved.iff_regs, wp_norm, isCalleeSavedVReg]

private theorem hmac_seg_inner_empty [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 1060#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hx26 : s.readReg64 .x26 = 0#64) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 2008#64) s
      (memRegion (s.sp + 64#64) 32 ∗ R)
      (fun sf P' =>
        (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
         sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 64#64 ∧
         sf.readReg64 .x2 = s.readReg64 .x23 ∧ sf.readReg64 .x3 = 64#64 ∧
         sf.readReg64 .x4 = s.sp + 64#64 ∧ sf.readReg64 .x5 = 8#64) ∧
        (P' ⊢ ((s.sp + 64#64) ↦ₛ shaStateBytes sha256IV) ∗ R)) := by
  have hpc' : s.pc = haclPl6.base + 1060#64 := hpc; clear hpc
  have hsp_al : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  have hx26_gpr : s.readReg64 (Reg.gpr 26#5) = 0#64 := hx26
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  apply memRegion32_elim; intro w0 w1 w2 w3
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_sym_steps 25
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm],
      by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
      by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, ?_⟩
  rw [show (s.sp + 72#64) = (s.sp + 64#64) + 8#64 by bv_omega,
      show (s.sp + 80#64) = (s.sp + 64#64) + 16#64 by bv_omega,
      show (s.sp + 88#64) = (s.sp + 64#64) + 24#64 by bv_omega]
  refine Entails.of_eq ?_
  rw [← pointsTo64_4_sha256IV (s.sp + 64#64)]; sep_ac_rfl

private theorem and_mask63_32 (w : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 w &&& 270582939711#64) = w &&& 63#32 := by
  have hw : BitVec.setWidth 32 (BitVec.setWidth 64 w) = w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans w.isLt (by decide)),
        Nat.mod_eq_of_lt w.isLt]
  rw [BitVec.setWidth_and, hw]
  rfl

private theorem and_63_toNat_32 {L : Nat} (hlt : L < 2 ^ 32) :
    (BitVec.ofNat 32 L &&& 63#32).toNat = L % 64 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  change (L &&& 63) = L % 64
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

private theorem hmac_seg_inner_nonempty_1 [HaclPlacement] {L : Nat} {s : State} {R : SepProp}
    (h0 : 0 < L) (hlt : L < 2 ^ 32)
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 1060#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 L)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 L) :
    let nblk := 64 * ((L - 1) / 64)
    let remLen := L - nblk
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 1208#64) s
      (memRegion (s.sp + 64#64) 32 ∗ R)
      (fun sf P' =>
        (sf.sp = s.sp ∧
         CalleeSavedPreserved
           (((s.writeReg64 .x25 (BitVec.ofNat 64 nblk)).writeReg64 .x21
             (BitVec.ofNat 64 remLen)).writeReg64 .x26 (BitVec.ofNat 64 remLen)) sf ∧
         sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = s.readReg64 .x23 ∧
         sf.readReg64 .x2 = 64#64 ∧ sf.readReg64 .x3 = s.sp + 64#64 ∧
         sf.readReg64 .x4 = 8#64) ∧
        (P' ⊢ ((s.sp + 64#64) ↦ₛ shaStateBytes sha256IV) ∗ R)) := by
  intro nblk remLen
  have hpc' : s.pc = haclPl6.base + 1060#64 := hpc; clear hpc
  have hsp_al : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  have hx21_gpr : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 L := hx21
  have hx26_gpr : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 L := hx26
  have hne0_beq : (BitVec.ofNat 64 L == 0#64) = false := beq_false_of_ne (by bv_omega)
  have hw26_32 : (BitVec.ofNat 64 L).setWidth 32 = BitVec.ofNat 32 L := by bv_omega
  have hands63 := and_mask63_32 (BitVec.ofNat 32 L)
  have hnblk_lt : nblk < L := by dsimp only [nblk]; omega
  have hL64 : L < 2 ^ 64 := by omega
  have hsub_rem : BitVec.ofNat 64 L - BitVec.ofNat 64 nblk = BitVec.ofNat 64 remLen := by
    dsimp only [nblk, remLen]; bv_omega
  have hult_nblk : (BitVec.ofNat 64 L).ult (BitVec.ofNat 64 nblk) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hL64, Nat.mod_eq_of_lt (by omega : nblk < 2 ^ 64)] at hh
    omega
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  apply memRegion32_elim; intro w0 w1 w2 w3
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  by_cases h64 : L < 64
  · have hdiv0 : BitVec.ofNat 32 L >>> 6 = 0#32 := by bv_omega
    have hult_c1 : (BitVec.ofNat 64 L).ult 0#64 = false := by simp [BitVec.ult]
    have hnblk0 : nblk = 0 := by dsimp only [nblk]; omega
    have hremL : remLen = L := by dsimp only [remLen, nblk]; omega
    wp_sym_steps 29
    conv in (State.setPC _ _) => arg 2; simp [wp_norm, hult_c1]
    wp_sym_steps 8
    refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
      ⟨⟨by simp [wp_norm], ?_,
        by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
        by simp [wp_norm], by simp [wp_norm]⟩, ?_⟩
    · simp only [CalleeSavedPreserved.iff_regs, wp_norm]
      refine ⟨trivial, trivial, ?_, trivial, trivial, trivial, ?_, ?_, trivial, trivial, trivial, trivial⟩
      · simp [hremL]
      · simp [hnblk0]
      · simp only [BitVec.zero_and, BitVec.setWidth_zero, beq_self_eq_true, not_true_eq_false,
          ↓reduceIte, hremL]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, and_63_toNat_32 hlt, Nat.mod_eq_of_lt h64,
            Nat.mod_eq_of_lt hL64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL64]
    · rw [show (s.sp + 72#64) = (s.sp + 64#64) + 8#64 by bv_omega,
          show (s.sp + 80#64) = (s.sp + 64#64) + 16#64 by bv_omega,
          show (s.sp + 88#64) = (s.sp + 64#64) + 24#64 by bv_omega]
      refine Entails.of_eq ?_; rw [← pointsTo64_4_sha256IV (s.sp + 64#64)]; sep_ac_rfl
  · have hult1 : (BitVec.ofNat 32 L >>> 6).ult 1#32 = false := by
      apply Bool.eq_false_iff.mpr; intro hh
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow] at hh
      change L / 64 < 1 at hh; omega
    by_cases hmod0 : L % 64 = 0
    · have hands0 : BitVec.ofNat 32 L &&& 63#32 = 0#32 := by
        apply BitVec.eq_of_toNat_eq; rw [and_63_toNat_32 hlt]; simpa using hmod0
      have hx25_eq :
          BitVec.setWidth 64 ((BitVec.ofNat 32 L >>> 6 - 1#32) <<< 6) =
          BitVec.ofNat 64 nblk := by
        dsimp only [nblk]; bv_omega
      have hx26_eq :
          BitVec.setWidth 64
            (BitVec.ofNat 32 L - (BitVec.ofNat 32 L >>> 6 - 1#32) <<< 6) =
          BitVec.ofNat 64 remLen := by
        dsimp only [remLen, nblk]; bv_omega
      wp_sym_steps 37
      refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
        ⟨⟨by simp [wp_norm], ?_,
          by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
          by simp [wp_norm], by simp [wp_norm]⟩, ?_⟩
      · simp only [CalleeSavedPreserved.iff_regs, wp_norm]
        exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
          by rw [hw26_32, hx26_eq], trivial, trivial, trivial, trivial⟩
      · rw [show (s.sp + 72#64) = (s.sp + 64#64) + 8#64 by bv_omega,
            show (s.sp + 80#64) = (s.sp + 64#64) + 16#64 by bv_omega,
            show (s.sp + 88#64) = (s.sp + 64#64) + 24#64 by bv_omega]
        refine Entails.of_eq ?_; rw [← pointsTo64_4_sha256IV (s.sp + 64#64)]; sep_ac_rfl
    · have hands_ne : (BitVec.ofNat 32 L &&& 63#32 == 0#32) = false := by
        apply beq_false_of_ne; intro heq
        have := congrArg BitVec.toNat heq; rw [and_63_toNat_32 hlt] at this; exact hmod0 this
      have hx25_eq :
          BitVec.setWidth 64 (BitVec.ofNat 32 L >>> 6 <<< 6) = BitVec.ofNat 64 nblk := by
        dsimp only [nblk]; bv_omega
      have hx26_eq :
          BitVec.setWidth 64 (BitVec.ofNat 32 L &&& 63#32) = BitVec.ofNat 64 remLen := by
        have hrem_eq : remLen = L % 64 := by dsimp only [remLen, nblk]; omega
        have hrem64 : remLen < 2 ^ 64 := by rw [hrem_eq]; omega
        have hto := and_63_toNat_32 hlt
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by rw [hto]; omega), hto,
            ← hrem_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem64]
      wp_sym_steps 37
      refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
        ⟨⟨by simp [wp_norm], ?_,
          by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
          by simp [wp_norm], by simp [wp_norm]⟩, ?_⟩
      · simp only [CalleeSavedPreserved.iff_regs, wp_norm]
        refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, trivial, trivial, trivial, trivial⟩
        have hrem32 : remLen < 2 ^ 32 := by dsimp only [remLen, nblk]; omega
        have hrem64 : remLen < 2 ^ 64 := by omega
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hrem64, Nat.mod_eq_of_lt hrem32, Nat.mod_eq_of_lt hrem64]
      · rw [show (s.sp + 72#64) = (s.sp + 64#64) + 8#64 by bv_omega,
            show (s.sp + 80#64) = (s.sp + 64#64) + 16#64 by bv_omega,
            show (s.sp + 88#64) = (s.sp + 64#64) + 24#64 by bv_omega]
        refine Entails.of_eq ?_; rw [← pointsTo64_4_sha256IV (s.sp + 64#64)]; sep_ac_rfl

private theorem hmac_seg_inner_nonempty_2 [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 1212#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 1232#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
         sf.readReg64 .x0 = ((s.readReg64 .x25).setWidth 32).setWidth 64 ∧
         sf.readReg64 .x1 = s.readReg64 .x20 ∧
         sf.readReg64 .x2 = s.readReg64 .x25 ∧
         sf.readReg64 .x3 = s.sp + 64#64 ∧
         sf.readReg64 .x4 = 8#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 1212#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 5
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm],
      by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
      by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_inner_nonempty_3 [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 1236#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 2008#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
         sf.readReg64 .x0 = s.readReg64 .x25 + s.readReg64 .x26 + 64#64 ∧
         sf.readReg64 .x1 = ((s.readReg64 .x26).setWidth 32).setWidth 64 ∧
         sf.readReg64 .x2 = s.readReg64 .x20 + s.readReg64 .x25 ∧
         sf.readReg64 .x3 = s.readReg64 .x21 ∧
         sf.readReg64 .x4 = s.sp + 64#64 ∧
         sf.readReg64 .x5 = 8#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 1236#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 8
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm],
      by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
      by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_inner_finish_args [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2012#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6) (HaclPlacement.mpl.base 6 + 2028#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧ sf.readReg64 .x0 = s.sp + 64#64 ∧
        sf.readReg64 .x1 = 8#64 ∧ sf.readReg64 .x2 = s.readReg64 .x23 ∧ sf.readReg64 .x3 = 64#64) ∧
        (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2012#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]; wp_sym_steps 4
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨by simp [wp_norm],
    by simp [CalleeSavedPreserved.iff_regs, wp_norm], by simp [wp_norm], by simp [wp_norm],
    by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_outer_init_args [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2032#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6) (HaclPlacement.mpl.base 6 + 2040#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧ sf.readReg64 .x0 = s.sp + 64#64 ∧
        sf.readReg64 .x1 = 8#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2032#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]; wp_sym_steps 2
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨by simp [wp_norm],
    by simp [CalleeSavedPreserved.iff_regs, wp_norm], by simp [wp_norm], by simp [wp_norm]⟩,
    Entails.refl _⟩

private theorem hmac_seg_outer_opad_args [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2044#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6) (HaclPlacement.mpl.base 6 + 2064#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧ sf.readReg64 .x0 = 64#64 ∧
        sf.readReg64 .x1 = s.readReg64 .x24 ∧ sf.readReg64 .x2 = 64#64 ∧
        sf.readReg64 .x3 = s.sp + 64#64 ∧ sf.readReg64 .x4 = 8#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2044#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]; wp_sym_steps 5
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨by simp [wp_norm],
    by simp [CalleeSavedPreserved.iff_regs, wp_norm], by simp [wp_norm], by simp [wp_norm],
    by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_outer_zero_args [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2068#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6) (HaclPlacement.mpl.base 6 + 2088#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧ sf.readReg64 .x0 = 0#64 ∧
        sf.readReg64 .x1 = s.readReg64 .x23 ∧ sf.readReg64 .x2 = 0#64 ∧
        sf.readReg64 .x3 = s.sp + 64#64 ∧ sf.readReg64 .x4 = 8#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2068#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]; wp_sym_steps 5
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨by simp [wp_norm],
    by simp [CalleeSavedPreserved.iff_regs, wp_norm], by simp [wp_norm], by simp [wp_norm],
    by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_outer_last_args [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2092#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6) (HaclPlacement.mpl.base 6 + 2116#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧ sf.readReg64 .x0 = 96#64 ∧
        sf.readReg64 .x1 = 32#64 ∧ sf.readReg64 .x2 = s.readReg64 .x23 ∧ sf.readReg64 .x3 = 64#64 ∧
        sf.readReg64 .x4 = s.sp + 64#64 ∧ sf.readReg64 .x5 = 8#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2092#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]; wp_sym_steps 6
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨by simp [wp_norm],
    by simp [CalleeSavedPreserved.iff_regs, wp_norm], by simp [wp_norm], by simp [wp_norm],
    by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_outer_finish_args [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2120#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6) (HaclPlacement.mpl.base 6 + 2136#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧ sf.readReg64 .x0 = s.sp + 64#64 ∧
        sf.readReg64 .x1 = 8#64 ∧ sf.readReg64 .x2 = s.sp ∧ sf.readReg64 .x3 = 32#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2120#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]; wp_sym_steps 4
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨by simp [wp_norm],
    by simp [CalleeSavedPreserved.iff_regs, wp_norm], by simp [wp_norm], by simp [wp_norm],
    by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_dealloc_x24 [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2140#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6) (HaclPlacement.mpl.base 6 + 2152#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
        sf.readReg64 .x0 = s.readReg64 .x24 ∧ sf.readReg64 .x1 = 64#64 ∧ sf.readReg64 .x2 = 1#64) ∧
        (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2140#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]; wp_sym_steps 3
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨by simp [wp_norm],
    by simp [CalleeSavedPreserved.iff_regs, wp_norm], by simp [wp_norm], by simp [wp_norm],
    by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_dealloc_x23 [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2156#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6) (HaclPlacement.mpl.base 6 + 2168#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
        sf.readReg64 .x0 = s.readReg64 .x23 ∧ sf.readReg64 .x1 = 64#64 ∧ sf.readReg64 .x2 = 1#64) ∧
        (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2156#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]; wp_sym_steps 3
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨by simp [wp_norm],
    by simp [CalleeSavedPreserved.iff_regs, wp_norm], by simp [wp_norm], by simp [wp_norm],
    by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_dealloc_x22 [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2172#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6) (HaclPlacement.mpl.base 6 + 2184#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
        sf.readReg64 .x0 = s.readReg64 .x22 ∧ sf.readReg64 .x1 = 64#64 ∧ sf.readReg64 .x2 = 1#64) ∧
        (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2172#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]; wp_sym_steps 3
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨by simp [wp_norm],
    by simp [CalleeSavedPreserved.iff_regs, wp_norm], by simp [wp_norm], by simp [wp_norm],
    by simp [wp_norm]⟩, Entails.refl _⟩

private theorem hmac_seg_alloc32_args [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2192#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6) (HaclPlacement.mpl.base 6 + 2200#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧ sf.readReg64 .x0 = 32#64 ∧
        sf.readReg64 .x1 = 1#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2192#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]; wp_sym_steps 2
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨by simp [wp_norm],
    by simp [CalleeSavedPreserved.iff_regs, wp_norm], by simp [wp_norm], by simp [wp_norm]⟩,
    Entails.refl _⟩

private theorem hmac_seg_oom_tag [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2204#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 2700#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = 32#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 2204#64 := hpc; clear hpc
  have hx0_gpr : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 3
  exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

private theorem pointsToBytes8_exists_pts64 {bs : List (BitVec 8)} (h : bs.length = 8) :
    ∃ v : BitVec 64, ∀ p : BitVec 64, (p ↦ₛ bs) = (p ↦₆₄ v) := by
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    exact ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0,
      fun p => pointsToBytes8_eq_pointsTo64 p b0 b1 b2 b3 b4 b5 b6 b7⟩

private theorem pointsToBytes32_exists_pts64 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ t0 t1 t2 t3 : BitVec 64, ∀ p : BitVec 64,
      (p ↦ₛ bs) =
        ((p ↦₆₄ t0) ∗ ((p + 8#64) ↦₆₄ t1) ∗ ((p + 16#64) ↦₆₄ t2) ∗ ((p + 24#64) ↦₆₄ t3)) := by
  obtain ⟨t0, ht0⟩ := pointsToBytes8_exists_pts64 (bs := bs.take 8) (by simp [h])
  obtain ⟨t1, ht1⟩ := pointsToBytes8_exists_pts64 (bs := (bs.drop 8).take 8) (by simp [h])
  obtain ⟨t2, ht2⟩ := pointsToBytes8_exists_pts64 (bs := (bs.drop 16).take 8) (by simp [h])
  obtain ⟨t3, ht3⟩ := pointsToBytes8_exists_pts64 (bs := bs.drop 24) (by simp [h])
  refine ⟨t0, t1, t2, t3, fun p => ?_⟩
  conv_lhs => rw [← List.take_append_drop 8 bs]
  rw [pointsToBytes_append p, show (bs.take 8).length = 8 by simp [h], ht0 p]
  conv_lhs => rw [← List.take_append_drop 8 (bs.drop 8)]
  rw [pointsToBytes_append (p + 8#64), show ((bs.drop 8).take 8).length = 8 by simp [h],
      ht1 (p + 8#64), List.drop_drop, show 8 + 8 = 16 from rfl]
  conv_lhs => rw [← List.take_append_drop 8 (bs.drop 16)]
  rw [pointsToBytes_append (p + 8#64 + 8#64), show ((bs.drop 16).take 8).length = 8 by simp [h],
      ht2 (p + 8#64 + 8#64), List.drop_drop, show 16 + 8 = 24 from rfl,
      ht3 (p + 8#64 + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion24_elim {prog : Program} {target_pc : BitVec 64}
    {s : State} {a : BitVec 64} {R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ w0 w1 w2 : BitVec 64,
      SepWP prog target_pc s
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ R) post oom) :
    SepWP prog target_pc s (memRegion a 24 ∗ R) post oom := by
  rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split a 8 16 (by decide),
      memRegion_eight a, sepConj_assoc, sepExists_sepConj_left]
  refine SepWP.exists_elim fun w0 => ?_
  rw [show (a ↦₆₄ w0) ∗ (memRegion (a + 8#64) 16 ∗ R) =
      memRegion (a + 8#64) 16 ∗ ((a ↦₆₄ w0) ∗ R) by sep_ac_rfl,
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (a + 8#64) 8 8 (by decide),
      memRegion_eight (a + 8#64), sepConj_assoc, sepExists_sepConj_left]
  refine SepWP.exists_elim fun w1 => ?_
  rw [show ((a + 8#64) ↦₆₄ w1) ∗ (memRegion ((a + 8#64) + 8#64) 8 ∗ ((a ↦₆₄ w0) ∗ R)) =
      memRegion (a + 16#64) 8 ∗ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ R) by
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl,
      memRegion_eight (a + 16#64), sepExists_sepConj_left]
  refine SepWP.exists_elim fun w2 => ?_
  rw [show ((a + 16#64) ↦₆₄ w2) ∗ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ R) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ R by sep_ac_rfl]
  exact h w0 w1 w2

private theorem hmac_seg_tag_epilogue [HaclPlacement] {A : RustAlloc}
    {s0 s : State} {ret pOut pad152 : BitVec 64} {tag stBs : List (BitVec 8)} {R : SepProp}
    (htag : tag.length = 32) (hst : stBs.length = 32)
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2204#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64) (hsp0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = pOut) (hne0 : pOut ≠ 0#64)
    (hx19 : s.readReg64 .x19 = ret) (hx27 : s.readReg64 .x27 = 32#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    let sp1 := s0.sp - 224#64
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (s0.readReg64 .x30) s
      ((sp1 ↦ₛ tag) ∗ memRegion (sp1 + 32#64) 32 ∗ ((sp1 + 64#64) ↦ₛ stBs) ∗
       memRegion (sp1 + 96#64) 32 ∗ hmacSavedCalleeRegs sp1 s0 pad152 ∗
       A.live pOut 32 1 ∗ memRegion pOut 32 ∗ memRegion ret 24 ∗ R)
      (fun sf P' =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) ∧
        (P' ⊢ stackAt s0.sp 224 ∗ vecU8 A ret tag ∗ R)) := by
  intro sp1
  have hpc' : s.pc = haclPl6.base + 2204#64 := hpc; clear hpc
  have hsp_al : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := State.spAligned_sub s0 224#64 hsp0
  have hx0_gpr : s.readReg64 (Reg.gpr 0#5) = pOut := hx0
  have hx19_gpr : s.readReg64 (Reg.gpr 19#5) = ret := hx19
  have hx27_gpr : s.readReg64 (Reg.gpr 27#5) = 32#64 := hx27
  have hne0_beq : (pOut == 0#64) = false := beq_false_of_ne hne0
  obtain ⟨t0, t1, t2, t3, htag_pts⟩ := pointsToBytes32_exists_pts64 htag
  rw [← haclPC6_eq_blockProgram]
  have hpre1 :
      ((sp1 ↦ₛ tag) ∗ memRegion (sp1 + 32#64) 32 ∗ ((sp1 + 64#64) ↦ₛ stBs) ∗
       memRegion (sp1 + 96#64) 32 ∗ hmacSavedCalleeRegs sp1 s0 pad152 ∗
       A.live pOut 32 1 ∗ memRegion pOut 32 ∗ memRegion ret 24 ∗ R) =
      (memRegion pOut 32 ∗ (memRegion ret 24 ∗
       ((sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
        hmacSavedCalleeRegs sp1 s0 pad152 ∗
        (memRegion (sp1 + 32#64) 32 ∗ ((sp1 + 64#64) ↦ₛ stBs) ∗ memRegion (sp1 + 96#64) 32 ∗
         A.live pOut 32 1 ∗ R)))) := by
    rw [htag_pts sp1]; sep_ac_rfl
  rw [hpre1]
  apply memRegion32_elim; intro o0 o1 o2 o3
  rw [show ((pOut ↦₆₄ o0) ∗ ((pOut + 8#64) ↦₆₄ o1) ∗ ((pOut + 16#64) ↦₆₄ o2) ∗ ((pOut + 24#64) ↦₆₄ o3) ∗
      (memRegion ret 24 ∗
       ((sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
        hmacSavedCalleeRegs sp1 s0 pad152 ∗
        (memRegion (sp1 + 32#64) 32 ∗ ((sp1 + 64#64) ↦ₛ stBs) ∗ memRegion (sp1 + 96#64) 32 ∗
         A.live pOut 32 1 ∗ R)))) =
      (memRegion ret 24 ∗
       ((pOut ↦₆₄ o0) ∗ ((pOut + 8#64) ↦₆₄ o1) ∗ ((pOut + 16#64) ↦₆₄ o2) ∗ ((pOut + 24#64) ↦₆₄ o3) ∗
        (sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
        hmacSavedCalleeRegs sp1 s0 pad152 ∗
        (memRegion (sp1 + 32#64) 32 ∗ ((sp1 + 64#64) ↦ₛ stBs) ∗ memRegion (sp1 + 96#64) 32 ∗
         A.live pOut 32 1 ∗ R))) by sep_ac_rfl]
  apply memRegion24_elim; intro r0 r1 r2
  dsimp only [hmacSavedCalleeRegs, sp1]
  wp_sym_steps 17
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], ?_⟩, ?_⟩
  · simp only [CalleeSavedPreserved.iff_regs, wp_norm]
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, hx28, trivial, ?_⟩
    simp [calleeSavedVRegs, wp_norm] at hvregs ⊢; exact hvregs
  · refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono (hmacStack224_recombine s0.sp s0 pad152 tag stBs htag hst)
        (sepConj_mono (vecU8_pack_32 A ret pOut tag htag hne0) (Entails.refl _)))
    rw [htag_pts (s0.sp - 224#64), htag_pts pOut]
    unfold hmacSavedCalleeRegs
    sep_ac_rfl

/-! ## 3. Public Block 6 Interfaces, Combinators, & Allocator-Independent SHA-256 Core -/

/-- Adjoin `⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝` to `spec.post` (matching `HaclSha256.withTraceEq`). -/
abbrev withTraceEq {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun g s0 sf => spec.post g s0 sf ∗ ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ }

/-- Trace-preserving `libcrux_sha2::hacl` subroutine bundle consumed by `libcrux_hmac::hmac`
(Block 6). Note `init_ok`, `updateNblocks_ok`, and `finish_ok` already carry
`ProcessFieldsPreserved s0 sf` (which implies `sf.trace = s0.trace`). -/
structure HaclSubroutinesTrace (P : Program) (mpl : Obj.MultiPlacement) : Prop where
  init_ok          : subroutine_ok P (mpl.base 0) (withHaclPreserved mpl sha256InitRawSpec)
  updateNblocks_ok : subroutine_ok P (mpl.base 2) (sha256UpdateNblocksSpec mpl)
  updateLast_ok    : subroutine_ok P (mpl.base 3) (withTraceEq (sha256UpdateLastSpec mpl))
  finish_ok        : subroutine_ok P (mpl.base 4) (withHaclPreserved mpl sha256FinishRawSpec)
  hash256_ok       : subroutine_ok P (mpl.base 5) (withTraceEq (hash256Spec mpl))

/-- Explicit Block 6 contract wrapper adjoining `⌜libcruxHmacLib.CodeLoaded mpl s0.mem⌝` to `pre`. -/
@[expose] def withHaclCodeLoaded {α : Type} (mpl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜libcruxHmacLib.CodeLoaded mpl s0.mem⌝ ∗ spec.pre x s0 }

/-- Discharge `withHaclCodeLoaded mpl spec` whenever `P.CodeLoaded` implies
`libcruxHmacLib.CodeLoaded mpl`. -/
theorem subroutine_ok_of_withHaclCodeLoaded {α : Type} {P : Program} {entry : BitVec 64}
    {mpl : Obj.MultiPlacement} {spec : Spec α}
    (hCL : ∀ m : Memory, P.CodeLoaded m → libcruxHmacLib.CodeLoaded mpl m)
    (h : subroutine_ok P entry (withHaclCodeLoaded mpl spec)) :
    subroutine_ok P entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hpre' : s0.mem ⊨ (withHaclCodeLoaded mpl spec).pre x s0 ∗ R := by
    dsimp only [withHaclCodeLoaded]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hCL s0.mem hLP, hpre⟩
  exact h.mono_outcome x R s0 hpc hrun hpre' hsp (fun _ hout => hout)

/-- Budget-threaded allocator subroutines (`__rust_alloc_zeroed`, `__rust_alloc`, `__rust_dealloc`)
at placement `mpl`. -/
structure HmacBudgetAllocSubroutines (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (P : Program) (mpl : Obj.MultiPlacement) : Prop where
  allocZeroed_ok : subroutine_ok P (mpl.ρ rustAllocZeroedSym)
                     (rustCliAllocBudgetSpecBase M A lim true)
  alloc_ok       : subroutine_ok P (mpl.ρ rustAllocSym)
                     (rustCliAllocBudgetSpecBase M A lim false)
  dealloc_ok     : subroutine_ok P (mpl.ρ rustDeallocSym)
                     (rustCliDeallocBudgetSpecBase M A lim)

/-- Unbudgeted allocator subroutines (`__rust_alloc_zeroed`, `__rust_alloc`, `__rust_dealloc`)
at placement `mpl`. -/
structure HmacAllocSubroutines (A : RustAlloc) (P : Program) (mpl : Obj.MultiPlacement) : Prop where
  allocZeroed_ok : subroutine_ok P (mpl.ρ rustAllocZeroedSym) (rustAllocZeroedSpec A)
  alloc_ok       : subroutine_ok P (mpl.ρ rustAllocSym) (rustAllocSpec A)
  dealloc_ok     : subroutine_ok P (mpl.ρ rustDeallocSym) (rustDeallocSpec A)

private theorem bl_vmPreserved (imm : BitVec 64) (s : State) :
    VmPreserved s (execInst (.bl imm) s) := by
  rw [execInst_bl_eq]
  exact ⟨⟨by cases s; rfl, by cases s; rfl, by cases s; rfl⟩,
    by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

private theorem bl_sp (imm : BitVec 64) (s : State) :
    (execInst (.bl imm) s).sp = s.sp := by cases s; rfl

private theorem bl_mem (imm : BitVec 64) (s : State) :
    (execInst (.bl imm) s).mem = s.mem := by cases s; rfl

private theorem bl_trace (imm : BitVec 64) (s : State) :
    (execInst (.bl imm) s).trace = s.trace := by cases s; rfl

private theorem bl_fs (imm : BitVec 64) (s : State) :
    (execInst (.bl imm) s).fs = s.fs := by cases s; rfl

private theorem block6_code_length :
    (libcruxHmacLib.blocks[6]'(by decide)).code.length = 2848 := by
  have h : (libcruxHmacLib.blocks[6]'(by decide)).code = haclTree6.toBytes := by
    rw [← libcruxHmacLib.blockLib_text (i := 6) (by decide)]; exact hacl6_code_eq
  rw [h, ProofLib.ProgramReflection.WordTree.length_toBytes_of_checkSize? hacl6_tree_size]

private theorem bl_csp {imm : BitVec 64} {s sf : State}
    (h : CalleeSavedPreserved (execInst (.bl imm) s) sf) : CalleeSavedPreserved s sf := by
  rw [CalleeSavedPreserved.iff_regs] at h ⊢
  simpa [execInst_bl_eq, wp_norm, calleeSavedVRegs] using h

private theorem sepWP_pure_left {P : Program} {target : BitVec 64} {s : State}
    {φ : Prop} {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWP P target s Rest post oom) :
    SepWP P target s (⌜φ⌝ ∗ Rest) post oom := by
  unfold SepWP reaches_pc; intro R hm hLP
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact (h hm.1).elim hm.2 hLP

private theorem sepWP_congr_pre {P : Program} {target : BitVec 64} {s : State}
    {P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hent : P1 ⊢ P2) (h : SepWP P target s P2 post oom) :
    SepWP P target s P1 post oom := by
  unfold SepWP reaches_pc; intro R hm hLP
  exact h.elim (Satisfies.mono (sepConj_mono_left hent) hm) hLP

private theorem sepWP_seg6 [HaclPlacement] {P : Program}
    (hP : HaclInProg P haclMpl) {mid target : BitVec 64} {s : State}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    {FullPre Pre Post Frame : SepProp} {PurePost : State → Prop}
    {post : State → SepProp → Prop}
    (hsplit : FullPre ⊢ Pre ∗ Frame)
    (hseg : ∀ m : Memory,
      SepWP (libcruxHmacLib.blockProgram haclMpl 6) mid (s.setMem m) Pre
        (fun sm' Pm' => PurePost sm' ∧ (Pm' ⊢ Post)))
    (hcont : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      VmPreserved s sm → sm.trace = s.trace → sm.fs = s.fs →
      libcruxHmacLib.CodeLoaded haclMpl sm.mem → PurePost sm →
      SepWP P target sm (Post ∗ Frame) post)
    (hPure_mem : ∀ (sm : State) (m : Memory), PurePost (sm.setMem m) ↔ PurePost sm := by
      intro sm _; cases sm; exact Iff.rfl) :
    SepWP P target s FullPre post :=
  sepWP_congr_pre hsplit <|
    sepWP_block_seg (i := 6) (by decide) hP hcl (Post := fun _ => Post) (fun _ _ => rfl) hPure_mem
      hseg fun sm hpc hrun hpf hcl' hpure =>
        hcont sm hpc hrun (ProcessFieldsPreserved_toHeapVmPreserved hpf) hpf.2.1 hpf.1 hcl' hpure

private theorem sepWP_bl6 [HaclPlacement] {α : Type} {P : Program}
    (hP : HaclInProg P haclMpl) (off : Nat) {sym : String} {calleeAddr target_pc : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok P calleeAddr spec)
    (hres : libcruxHmacLib.resolve haclMpl sym = calleeAddr)
    (x : α) (F : SepProp) {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off)
    (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hpre : Pre ⊢
      spec.pre x (execInst (.bl ((calleeAddr - haclMpl.base 6) - BitVec.ofNat 64 off)) s) ∗ F)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf
        (spec.post x (execInst (.bl ((calleeAddr - haclMpl.base 6) - BitVec.ofNat 64 off)) s) sf ∗ F)
        post)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ sym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, sha256InitSym, sha256UpdateNblocksSym, sha256UpdateLastSym,
          sha256FinishSym, hash256Sym, rustAllocShimSym, rustAllocZeroedSym, rustAllocSym,
          rustDeallocSym, memcpySym, rustHandleErrorSym, rustUnwrapFailedSym])
    (hpan_eq : ∀ s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hexit_eq : ∀ code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    SepWP P target_pc s Pre post := by
  have hoff' : off < (libcruxHmacLib.blocks[6]'(by decide)).code.length := by
    rw [block6_code_length]; exact hoff
  have hf : (libcruxHmacLib.blockProgram haclMpl 6).fetch s.pc =
      some (.bl ((calleeAddr - haclMpl.base 6) - BitVec.ofNat 64 off)) := by
    rw [hpc]; exact fetch_bl6_of hf_pc6 hres
  have htgt : s.pc + ((calleeAddr - haclMpl.base 6) - BitVec.ofNat 64 off) = calleeAddr := by
    rw [hpc]; exact add_off_rel_target (haclMpl.base 6) calleeAddr (BitVec.ofNat 64 off)
  refine sepWP_block_bl (i := 6) (by decide) hP hoff' hcall (x := x) (F := F) hcl hpc hrun hsp_align
    hf htgt
    (fun R hm => by rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hpre) hm)
    (fun R' sf _ hp => by rw [hpan_eq] at hp; exact not_satisfies_false_sepConj (R := R') hp)
    (fun R' code sf _ he => by rw [hexit_eq] at he; exact not_satisfies_false_sepConj (R := R') he)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
    (fun R' sf _ ho => by
      rw [hoom_eq] at ho; exact False.elim (not_satisfies_false_sepConj (R := F ∗ R') ho))
  have hpc_sf' : sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) := by
    rw [hpc_sf, hpc, BitVec.add_assoc]; congr 1; bv_omega
  have hsp_al' : sf.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp_sf]
  exact hnext sf hpc_sf' hrun_sf hsp_sf hsp_al' (bl_csp hcs_sf) hcl_sf

private theorem call_init_6 [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hsubs : HaclSubroutinesTrace P haclMpl) (off : Nat)
    (stA : BitVec 64) (old : List (BitVec 8)) (F : SepProp)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hargs : s.readReg64 .x0 = stA ∧ s.readReg64 .x1 = 8#64 ∧ old.length = 32)
    (hpre : Pre ⊢ (stA ↦ₛ old) ∗ stackAt s.sp 4096 ∗ F)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → VmPreserved s sf → sf.trace = s.trace → sf.fs = s.fs →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf ((stA ↦ₛ shaStateBytes sha256IV) ∗ stackAt s.sp 4096 ∗ F) post)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ sha256InitSym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, sha256InitSym]) :
    SepWP P target_pc s Pre post := by
  let imm := (haclMpl.base 0 - haclMpl.base 6) - BitVec.ofNat 64 off
  have hstk : stackAt s.sp 4096 = stackFrame (execInst (.bl imm) s) 16 ∗ stackAt (s.sp - 16#64) 4080 := by
    unfold stackFrame; rw [bl_sp, stackAt_4096_split_16 s.sp, ← stackAt_eq_stackFrameAt s.sp 16]
  refine sepWP_bl6 hP off hsubs.init_ok (resolve_sha256Init haclMpl) (stA, old)
    (stackAt (s.sp - 16#64) 4080 ∗ F) hcl hpc hrun hsp_align ?_
    (fun sf hpcf hrunf hspf hsp_alf hcs hclf => ?_) hoff hf_pc6
  · dsimp only [withHaclPreserved, sha256InitRawSpec]
    have hp1 : libcruxHmacLib.CodeLoaded haclMpl (execInst (.bl imm) s).mem := by rwa [bl_mem]
    have hp2 : (execInst (.bl imm) s).readReg64 .x0 = stA ∧
        8 ≤ ((execInst (.bl imm) s).readReg64 .x1).toNat ∧ old.length = 32 := by
      rcases hargs with ⟨hx0, hx1, hold⟩
      simp only [wp_norm, hx0, hx1, hold]; exact ⟨trivial, by decide, trivial⟩
    refine Entails.trans hpre ?_; rw [hstk]
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (Entails.pure_right hp1 (Entails.pure_right hp2 (Entails.refl _))))
  · dsimp only [withHaclPreserved, sha256InitRawSpec]; rw [sepConj_assoc]
    refine sepWP_pure_left fun ⟨hpf, _⟩ => sepWP_congr_pre ?_
      (hnext sf hpcf hrunf hspf hsp_alf hcs
        ((bl_vmPreserved _ s).trans (ProcessFieldsPreserved_toHeapVmPreserved hpf))
        (by rw [hpf.2.1, bl_trace]) (by rw [hpf.1, bl_fs]) hclf)
    rw [hstk]; exact Entails.of_eq (by sep_ac_rfl)

private theorem call_nblocks_6 [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hsubs : HaclSubroutinesTrace P haclMpl) (off len : Nat)
    (blkA : BitVec 64) (bs : List (BitVec 8)) (stA : BitVec 64) (st : ShaState) (F : SepProp)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hargs : len < 2 ^ 32 ∧ (s.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 len ∧
      s.readReg64 .x1 = blkA ∧ (s.readReg64 .x2).toNat = bs.length ∧
      len ≤ bs.length ∧ bs.length + 64 < 2 ^ 64 ∧
      s.readReg64 .x3 = stA ∧ s.readReg64 .x4 = 8#64)
    (hpre : Pre ⊢ (blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st) ∗ stackAt s.sp 4096 ∗ F)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → VmPreserved s sf → sf.trace = s.trace → sf.fs = s.fs →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf
        ((blkA ↦ₛ bs) ∗
         (stA ↦ₛ shaStateBytes ((chunks64 (bs.take (64 * (len / 64)))).foldl sha256CompressState st)) ∗
         stackAt s.sp 4096 ∗ F) post)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ sha256UpdateNblocksSym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, sha256UpdateNblocksSym]) :
    SepWP P target_pc s Pre post := by
  let imm := (haclMpl.base 2 - haclMpl.base 6) - BitVec.ofNat 64 off
  have hstk : stackAt s.sp 4096 = stackFrame (execInst (.bl imm) s) 224 ∗ stackAt (s.sp - 224#64) 3872 := by
    unfold stackFrame; rw [bl_sp, stackAt_4096_split_224 s.sp, ← stackAt_eq_stackFrameAt s.sp 224]
  refine sepWP_bl6 hP off hsubs.updateNblocks_ok (resolve_sha256UpdateNblocks haclMpl)
    (len, blkA, bs, stA, st) (stackAt (s.sp - 224#64) 3872 ∗ F) hcl hpc hrun hsp_align ?_
    (fun sf hpcf hrunf hspf hsp_alf hcs hclf => ?_) hoff hf_pc6
  · dsimp only [sha256UpdateNblocksSpec]
    rcases hargs with ⟨hl32, hx0, hx1, hx2, hle, hlt64, hx3, hx4⟩
    have hp : libcruxHmacLib.CodeLoaded haclMpl (execInst (.bl imm) s).mem ∧
        len < 2 ^ 32 ∧ ((execInst (.bl imm) s).readReg64 .x0).setWidth 32 = BitVec.ofNat 32 len ∧
        (execInst (.bl imm) s).readReg64 .x1 = blkA ∧
        ((execInst (.bl imm) s).readReg64 .x2).toNat = bs.length ∧
        len ≤ bs.length ∧ bs.length + 64 < 2 ^ 64 ∧
        (execInst (.bl imm) s).readReg64 .x3 = stA ∧
        8 ≤ ((execInst (.bl imm) s).readReg64 .x4).toNat := by
      rw [bl_mem]; simp only [wp_norm, hx0, hx1, hx2, hx3, hx4]
      exact ⟨hcl, hl32, trivial, trivial, trivial, hle, hlt64, trivial, by decide⟩
    refine Entails.trans hpre ?_; rw [hstk]
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (Entails.pure_right hp (Entails.refl _)))
  · dsimp only [sha256UpdateNblocksSpec]; rw [sepConj_assoc]
    refine sepWP_pure_left fun ⟨hpf, _⟩ => sepWP_congr_pre ?_
      (hnext sf hpcf hrunf hspf hsp_alf hcs
        ((bl_vmPreserved _ s).trans (ProcessFieldsPreserved_toHeapVmPreserved hpf))
        (by rw [hpf.2.1, bl_trace]) (by rw [hpf.1, bl_fs]) hclf)
    rw [hstk]; exact Entails.of_eq (by sep_ac_rfl)

private theorem call_last_6 [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hsubs : HaclSubroutinesTrace P haclMpl) (off totlen remLen : Nat)
    (remA : BitVec 64) (slice : List (BitVec 8)) (stA : BitVec 64) (st : ShaState) (F : SepProp)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hargs : (s.readReg64 .x0).toNat = totlen ∧ remLen ≤ 64 ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 remLen ∧
      s.readReg64 .x2 = remA ∧ (s.readReg64 .x3).toNat = slice.length ∧
      remLen ≤ slice.length ∧ s.readReg64 .x4 = stA ∧ s.readReg64 .x5 = 8#64)
    (hpre : Pre ⊢ (remA ↦ₛ slice) ∗ (stA ↦ₛ shaStateBytes st) ∗ stackAt s.sp 4096 ∗ F)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → VmPreserved s sf → sf.trace = s.trace → sf.fs = s.fs →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf
        ((remA ↦ₛ slice) ∗
         (stA ↦ₛ shaStateBytes (haclUpdateLastState sha256CompressState totlen (slice.take remLen) st)) ∗
         stackAt s.sp 4096 ∗ F) post)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ sha256UpdateLastSym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, sha256UpdateLastSym]) :
    SepWP P target_pc s Pre post := by
  let imm := (haclMpl.base 3 - haclMpl.base 6) - BitVec.ofNat 64 off
  have hstk : stackAt s.sp 4096 = stackFrame (execInst (.bl imm) s) 352 ∗ stackAt (s.sp - 352#64) 3744 := by
    unfold stackFrame; rw [bl_sp, stackAt_4096_split_352 s.sp, ← stackAt_eq_stackFrameAt s.sp 352]
  refine sepWP_bl6 hP off hsubs.updateLast_ok (resolve_sha256UpdateLast haclMpl)
    (totlen, remLen, remA, slice, stA, st) (stackAt (s.sp - 352#64) 3744 ∗ F) hcl hpc hrun hsp_align ?_
    (fun sf hpcf hrunf hspf hsp_alf hcs hclf => ?_) hoff hf_pc6
  · dsimp only [withTraceEq, sha256UpdateLastSpec]
    rcases hargs with ⟨hx0, hrem64, hx1, hx2, hx3, hle, hx4, hx5⟩
    have hp : libcruxHmacLib.CodeLoaded haclMpl (execInst (.bl imm) s).mem ∧
        ((execInst (.bl imm) s).readReg64 .x0).toNat = totlen ∧ remLen ≤ 64 ∧
        ((execInst (.bl imm) s).readReg64 .x1).setWidth 32 = BitVec.ofNat 32 remLen ∧
        (execInst (.bl imm) s).readReg64 .x2 = remA ∧
        ((execInst (.bl imm) s).readReg64 .x3).toNat = slice.length ∧ remLen ≤ slice.length ∧
        (execInst (.bl imm) s).readReg64 .x4 = stA ∧
        8 ≤ ((execInst (.bl imm) s).readReg64 .x5).toNat := by
      rw [bl_mem]; simp only [wp_norm, hx0, hx1, hx2, hx3, hx4, hx5]
      exact ⟨hcl, trivial, hrem64, trivial, trivial, trivial, hle, trivial, by decide⟩
    refine Entails.trans hpre ?_; rw [hstk]
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (Entails.pure_right hp (Entails.refl _)))
  · dsimp only [withTraceEq, sha256UpdateLastSpec]
    have hreord :
        ((⌜VmPreserved (execInst (.bl imm) s) sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem⌝ ∗
          (remA ↦ₛ slice) ∗
          (stA ↦ₛ shaStateBytes (haclUpdateLastState sha256CompressState totlen (slice.take remLen) st)) ∗
          stackFrame (execInst (.bl imm) s) 352) ∗
         ⌜sf.trace = (execInst (.bl imm) s).trace ∧ sf.fs = (execInst (.bl imm) s).fs⌝) ∗
         (stackAt (s.sp - 352#64) 3744 ∗ F) ⊢
        ⌜VmPreserved (execInst (.bl imm) s) sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem⌝ ∗
        (⌜sf.trace = (execInst (.bl imm) s).trace ∧ sf.fs = (execInst (.bl imm) s).fs⌝ ∗
         ((remA ↦ₛ slice) ∗
          (stA ↦ₛ shaStateBytes (haclUpdateLastState sha256CompressState totlen (slice.take remLen) st)) ∗
          stackAt s.sp 4096 ∗ F)) := by
      rw [hstk]; exact Entails.of_eq (by sep_ac_rfl)
    refine sepWP_congr_pre hreord <| sepWP_pure_left fun ⟨hvm, _⟩ => sepWP_pure_left fun ⟨htr, hfs⟩ =>
      hnext sf hpcf hrunf hspf hsp_alf hcs ((bl_vmPreserved _ s).trans hvm)
        (by rw [htr, bl_trace]) (by rw [hfs, bl_fs]) hclf

private theorem call_finish_6 [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hsubs : HaclSubroutinesTrace P haclMpl) (off : Nat)
    (stA : BitVec 64) (st : ShaState) (dstA : BitVec 64) (dst : List (BitVec 8)) (F : SepProp)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hargs : s.readReg64 .x0 = stA ∧ s.readReg64 .x1 = 8#64 ∧
      s.readReg64 .x2 = dstA ∧ (s.readReg64 .x3).toNat = dst.length ∧ 32 ≤ dst.length)
    (hpre : Pre ⊢ (stA ↦ₛ shaStateBytes st) ∗ (dstA ↦ₛ dst) ∗ stackAt s.sp 4096 ∗ F)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → VmPreserved s sf → sf.trace = s.trace → sf.fs = s.fs →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf
        ((stA ↦ₛ shaStateBytes st) ∗ (dstA ↦ₛ (st.toList.flatMap (toBEBytes 4) ++ dst.drop 32)) ∗
         stackAt s.sp 4096 ∗ F) post)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ sha256FinishSym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, sha256FinishSym]) :
    SepWP P target_pc s Pre post := by
  let imm := (haclMpl.base 4 - haclMpl.base 6) - BitVec.ofNat 64 off
  have hstk : stackAt s.sp 4096 = stackFrame (execInst (.bl imm) s) 16 ∗ stackAt (s.sp - 16#64) 4080 := by
    unfold stackFrame; rw [bl_sp, stackAt_4096_split_16 s.sp, ← stackAt_eq_stackFrameAt s.sp 16]
  refine sepWP_bl6 hP off hsubs.finish_ok (resolve_sha256Finish haclMpl)
    (stA, st, dstA, dst) (stackAt (s.sp - 16#64) 4080 ∗ F) hcl hpc hrun hsp_align ?_
    (fun sf hpcf hrunf hspf hsp_alf hcs hclf => ?_) hoff hf_pc6
  · dsimp only [withHaclPreserved, sha256FinishRawSpec]
    rcases hargs with ⟨hx0, hx1, hx2, hx3, h32⟩
    have hp1 : libcruxHmacLib.CodeLoaded haclMpl (execInst (.bl imm) s).mem := by rwa [bl_mem]
    have hp2 : (execInst (.bl imm) s).readReg64 .x0 = stA ∧
        8 ≤ ((execInst (.bl imm) s).readReg64 .x1).toNat ∧
        (execInst (.bl imm) s).readReg64 .x2 = dstA ∧
        ((execInst (.bl imm) s).readReg64 .x3).toNat = dst.length ∧ 32 ≤ dst.length := by
      simp only [wp_norm, hx0, hx1, hx2, hx3]; exact ⟨trivial, by decide, trivial, trivial, h32⟩
    refine Entails.trans hpre ?_; rw [hstk]
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (Entails.pure_right hp1 (Entails.pure_right hp2 (Entails.refl _))))
  · dsimp only [withHaclPreserved, sha256FinishRawSpec]; rw [sepConj_assoc]
    refine sepWP_pure_left fun ⟨hpf, _⟩ => sepWP_congr_pre ?_
      (hnext sf hpcf hrunf hspf hsp_alf hcs
        ((bl_vmPreserved _ s).trans (ProcessFieldsPreserved_toHeapVmPreserved hpf))
        (by rw [hpf.2.1, bl_trace]) (by rw [hpf.1, bl_fs]) hclf)
    rw [hstk]; exact Entails.of_eq (by sep_ac_rfl)

/-- Valid-path auxiliary subroutines for Block 6 (`libcrux_hmac::hmac`): only `shim_ok` and
    `memcpy_ok` (no panic stubs needed when `key.length < 2^32`, `data.length < 2^32`, and
    `FitsEnv` holds). -/
structure HmacValidAuxSubroutines (P : Program) (mpl : Obj.MultiPlacement) : Prop where
  shim_ok   : subroutine_ok P (mpl.ρ rustAllocShimSym) rustAllocShimVmSpec
  memcpy_ok : subroutine_ok P (mpl.ρ memcpySym) hmacMemcpyVmSpec

theorem hmacAux_toValid {P : Program} {mpl : Obj.MultiPlacement}
    (h : HmacAuxSubroutines P mpl) : HmacValidAuxSubroutines P mpl :=
  ⟨h.shim_ok, h.memcpy_ok⟩

private theorem hmac_key_prep_wp [HaclPlacement] {P : Program}
    (hP : HaclInProg P haclMpl) (hsubs : HaclSubroutinesTrace P haclMpl)
    (haux : HmacValidAuxSubroutines P haclMpl)
    {x : LibcruxHmacCall} {pKey keyLenBV : BitVec 64} {s : State} {Frame : SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + 268#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = pKey) (hpKey : pKey ≠ 0#64)
    (hx23 : s.readReg64 .x23 = keyLenBV) (hx24 : s.readReg64 .x24 = x.keyA)
    (hx25 : s.readReg64 .x25 = tryFromKeyNiche keyLenBV)
    (hk_nat : keyLenBV.toNat = x.key.length) (hk32 : x.key.length < 2 ^ 32) :
    SepWP P (haclMpl.base 6 + 912#64) s
      ((pKey ↦ₛ List.replicate 64 0#8) ∗ (x.keyA ↦ₛ x.key) ∗ stackAt s.sp 4096 ∗ Frame)
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧ CalleeSavedPreserved (s.writeReg64 .x22 pKey) sf ∧
         VmPreserved s sf ∧ sf.trace = s.trace ∧ sf.fs = s.fs ∧
         libcruxHmacLib.CodeLoaded haclMpl sf.mem) ∧
        (P' ⊢ (pKey ↦ₛ libcruxHmacKeyBlock sha256CompressState x.key) ∗
              (x.keyA ↦ₛ x.key) ∗ stackAt s.sp 4096 ∗ Frame)) := by
  have hk_bv : keyLenBV = BitVec.ofNat 64 x.key.length := by
    apply BitVec.eq_of_toNat_eq; rw [hk_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hk64 : x.key.length ≤ 64
  · refine sepWP_seg6 hP hcl (Pre := emp) (Post := emp)
      (Frame := (pKey ↦ₛ List.replicate 64 0#8) ∗ (x.keyA ↦ₛ x.key) ∗ stackAt s.sp 4096 ∗ Frame)
      (PurePost := fun sf => sf.sp = s.sp ∧
        CalleeSavedPreserved (s.writeReg64 .x22 (s.readReg64 .x0)) sf ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x24 ∧
        sf.readReg64 .x2 = keyLenBV)
      (Entails.of_eq (by rw [emp_sepConj]))
      (fun m => by
        have h := hmac_seg_key_short (s := s.setMem m) (keyLenBV := keyLenBV) (R := emp)
          (by cases s; exact hpc) (by cases s; exact hrun) (by cases s; exact hx0 ▸ hpKey)
          (by cases s; exact hx23) (by cases s; exact hx25) (by rw [hk_nat]; exact hk64)
        cases s; exact h)
      fun s1 hpc1 hrun1 hvm1 htr1 hfs1 hcl1 ⟨hsp1, hcs1, hx0_1, hx1_1, hx2_1⟩ => ?_
    have hsp_al1 : s1.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp1]
    have hsplit64 : (pKey ↦ₛ List.replicate 64 0#8) ⊢
        memRegion pKey x.key.length ∗
          ((pKey + BitVec.ofNat 64 x.key.length) ↦ₛ List.replicate (64 - x.key.length) 0#8) := by
      conv_lhs => rw [show (64 : Nat) = x.key.length + (64 - x.key.length) by omega, List.replicate_add]
      rw [pointsToBytes_append, List.length_replicate]
      exact sepConj_mono_left (by
        simpa [List.length_replicate] using
          pointsToBytes_entails_memRegion pKey (List.replicate x.key.length 0#8))
    refine sepWP_bl6 hP 308 haux.memcpy_ok (resolve_memcpy haclMpl) (pKey, x.keyA, x.key)
      (((pKey + BitVec.ofNat 64 x.key.length) ↦ₛ List.replicate (64 - x.key.length) 0#8) ∗ Frame)
      hcl1 hpc1 hrun1 hsp_al1 ?_ fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2 => ?_
    · dsimp only [hmacMemcpyVmSpec]
      let imm := (haclMpl.ρ memcpySym - haclMpl.base 6) - 308#64
      have hpure_mc : (execInst (.bl imm) s1).readReg64 .x0 = pKey ∧
          (execInst (.bl imm) s1).readReg64 .x1 = x.keyA ∧
          (execInst (.bl imm) s1).readReg64 .x2 = BitVec.ofNat 64 x.key.length ∧
          x.key.length < 2 ^ 64 := by
        simp only [imm, wp_norm, hx0_1, hx0, hx1_1, hx24, hx2_1, hk_bv]
        exact ⟨trivial, trivial, trivial, by omega⟩
      rw [emp_sepConj, show (execInst (.bl imm) s1).sp = s.sp by rw [bl_sp, hsp1]]
      exact Entails.trans (sepConj_mono_left hsplit64)
        (Entails.trans (Entails.of_eq (by sep_ac_rfl))
          (sepConj_mono_left (Entails.pure_right hpure_mc (Entails.refl _))))
    · dsimp only [hmacMemcpyVmSpec]; rw [sepConj_assoc]
      refine sepWP_pure_left fun ⟨_, hvm_mc, htr_mc, hfs_mc⟩ => ?_
      have hcs02 : CalleeSavedPreserved (s.writeReg64 .x22 pKey) s2 := by
        rw [hx0] at hcs1; exact hcs1.trans hcs2
      have hmerge64 :
          ((pKey ↦ₛ x.key) ∗ (x.keyA ↦ₛ x.key) ∗
            stackAt (execInst (.bl ((haclMpl.ρ memcpySym - haclMpl.base 6) - 308#64)) s1).sp 4096) ∗
            (((pKey + BitVec.ofNat 64 x.key.length) ↦ₛ List.replicate (64 - x.key.length) 0#8) ∗ Frame) ⊢
          emp ∗ ((pKey ↦ₛ libcruxHmacKeyBlock sha256CompressState x.key) ∗
            (x.keyA ↦ₛ x.key) ∗ stackAt s.sp 4096 ∗ Frame) := by
        have hk_eq : libcruxHmacKeyBlock sha256CompressState x.key =
            x.key ++ List.replicate (64 - x.key.length) 0#8 := by
          unfold libcruxHmacKeyBlock; simp [Nat.not_lt.mpr hk64]
        rw [bl_sp, hsp1, emp_sepConj, hk_eq, pointsToBytes_append]; exact Entails.of_eq (by sep_ac_rfl)
      refine sepWP_seg6 hP hcl2 (Pre := emp) (Post := emp)
        (Frame := (pKey ↦ₛ libcruxHmacKeyBlock sha256CompressState x.key) ∗
          (x.keyA ↦ₛ x.key) ∗ stackAt s.sp 4096 ∗ Frame)
        (PurePost := fun sf => sf.sp = s2.sp ∧ CalleeSavedPreserved s2 sf) hmerge64
        (fun m => by
          have h := hmac_seg_after_memcpy (s := s2.setMem m) (R := emp)
            (by cases s2; exact hpc2) (by cases s2; exact hrun2)
          cases s2; exact h)
        fun sf hpcf hrunf hvm3 htr3 hfs3 hclf ⟨hspf, hcs3⟩ => ?_
      refine SepWP.done hpcf hrunf ⟨⟨by rw [hspf, hsp2, hsp1], ?_, hcs02.trans hcs3,
        (hvm1.trans ((bl_vmPreserved _ s1).trans hvm_mc)).trans hvm3,
        by rw [htr3, htr_mc, bl_trace, htr1], by rw [hfs3, hfs_mc, bl_fs, hfs1], hclf⟩,
        by rw [emp_sepConj]; exact Entails.refl _⟩
      unfold State.spAligned at hsp_al2 ⊢; rwa [hspf]
  · have hk64' : 64 < x.key.length := Nat.lt_of_not_ge hk64
    refine sepWP_seg6 hP hcl (Pre := emp) (Post := emp)
      (Frame := (pKey ↦ₛ List.replicate 64 0#8) ∗ (x.keyA ↦ₛ x.key) ∗ stackAt s.sp 4096 ∗ Frame)
      (PurePost := fun sf => sf.sp = s.sp ∧
        CalleeSavedPreserved (s.writeReg64 .x22 (s.readReg64 .x0)) sf ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = 32#64 ∧
        sf.readReg64 .x2 = s.readReg64 .x24 ∧ sf.readReg64 .x3 = keyLenBV ∧
        sf.readReg64 .x4 = keyLenBV)
      (Entails.of_eq (by rw [emp_sepConj]))
      (fun m => by
        have h := hmac_seg_key_long_x4 (s := s.setMem m) (keyLenBV := keyLenBV) (R := emp)
          (by cases s; exact hpc) (by cases s; exact hrun) (by cases s; exact hx0 ▸ hpKey)
          (by cases s; exact hx23) (by cases s; exact hx25)
          (by rw [hk_nat]; exact hk64') (by rw [hk_nat]; exact hk32)
        cases s; exact h)
      fun s1 hpc1 hrun1 hvm1 htr1 hfs1 hcl1 ⟨hsp1, hcs1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1⟩ => ?_
    have hsp_al1 : s1.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp1]
    let imm := (haclMpl.base 5 - haclMpl.base 6) - 908#64
    have hstk : stackAt s.sp 4096 = stackFrame (execInst (.bl imm) s1) 480 ∗ stackAt (s.sp - 480#64) 3616 := by
      unfold stackFrame; rw [bl_sp, hsp1, stackAt_4096_split_480 s.sp, ← stackAt_eq_stackFrameAt s.sp 480]
    refine sepWP_bl6 hP 908 hsubs.hash256_ok (resolve_hash256 haclMpl)
      (pKey, List.replicate 32 0#8, x.keyA, x.key)
      (((pKey + 32#64) ↦ₛ List.replicate 32 0#8) ∗ stackAt (s.sp - 480#64) 3616 ∗ Frame)
      hcl1 hpc1 hrun1 hsp_al1 ?_ fun sf hpcf hrunf hspf hsp_alf hcs2 hclf => ?_
    · dsimp only [withTraceEq, hash256Spec]
      have hpure_h : libcruxHmacLib.CodeLoaded haclMpl (execInst (.bl imm) s1).mem ∧
          (execInst (.bl imm) s1).readReg64 .x0 = pKey ∧
          ((execInst (.bl imm) s1).readReg64 .x1).toNat = (List.replicate 32 0#8).length ∧
          32 ≤ (List.replicate 32 0#8).length ∧
          (execInst (.bl imm) s1).readReg64 .x2 = x.keyA ∧
          ((execInst (.bl imm) s1).readReg64 .x3).toNat = x.key.length ∧
          x.key.length < 2 ^ 32 ∧
          ((execInst (.bl imm) s1).readReg64 .x4).setWidth 32 = BitVec.ofNat 32 x.key.length := by
        rw [bl_mem]; simp only [imm, wp_norm, hx0_1, hx0, hx1_1, hx2_1, hx24, hx3_1, hx4_1,
          hk_nat, List.length_replicate]
        refine ⟨hcl1, trivial, trivial, trivial, trivial, trivial, hk32, ?_⟩
        rw [hk_bv]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hk32, Nat.mod_eq_of_lt (by omega)]
      have hrep64 : (pKey ↦ₛ List.replicate 64 0#8) =
          (pKey ↦ₛ List.replicate 32 0#8) ∗ ((pKey + 32#64) ↦ₛ List.replicate 32 0#8) := by
        conv_lhs => rw [show (64 : Nat) = 32 + 32 from rfl, List.replicate_add]
        rw [pointsToBytes_append, List.length_replicate]
      rw [emp_sepConj, hrep64, hstk]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono_left (Entails.pure_right hpure_h (Entails.refl _)))
    · dsimp only [withTraceEq, hash256Spec]
      have hreord :
          ((⌜VmPreserved (execInst (.bl imm) s1) sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem⌝ ∗
            (pKey ↦ₛ (sha256With sha256CompressState x.key ++ (List.replicate 32 0#8).drop 32)) ∗
            (x.keyA ↦ₛ x.key) ∗ stackFrame (execInst (.bl imm) s1) 480) ∗
           ⌜sf.trace = (execInst (.bl imm) s1).trace ∧ sf.fs = (execInst (.bl imm) s1).fs⌝) ∗
            (((pKey + 32#64) ↦ₛ List.replicate 32 0#8) ∗ stackAt (s.sp - 480#64) 3616 ∗ Frame) ⊢
          ⌜VmPreserved (execInst (.bl imm) s1) sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem⌝ ∗
          (⌜sf.trace = (execInst (.bl imm) s1).trace ∧ sf.fs = (execInst (.bl imm) s1).fs⌝ ∗
           ((pKey ↦ₛ libcruxHmacKeyBlock sha256CompressState x.key) ∗
            (x.keyA ↦ₛ x.key) ∗ stackAt s.sp 4096 ∗ Frame)) := by
        have hk_eq : libcruxHmacKeyBlock sha256CompressState x.key =
            sha256With sha256CompressState x.key ++ List.replicate 32 0#8 := by
          rw [libcruxHmacKeyBlock_eq]; simp [hk64', sha256With_length]
        have hpts : (pKey ↦ₛ sha256With sha256CompressState x.key) ∗
            ((pKey + 32#64) ↦ₛ List.replicate 32 0#8) =
            (pKey ↦ₛ libcruxHmacKeyBlock sha256CompressState x.key) := by
          rw [hk_eq, pointsToBytes_append, sha256With_length]
        rw [show (List.replicate 32 0#8).drop 32 = [] by simp, List.append_nil, hstk]
        refine Entails.of_eq ?_; rw [← hpts]; sep_ac_rfl
      refine sepWP_congr_pre hreord <| sepWP_pure_left fun ⟨hvm_h, _⟩ => sepWP_pure_left fun ⟨htr_h, hfs_h⟩ => ?_
      have hcs0f : CalleeSavedPreserved (s.writeReg64 .x22 pKey) sf := by
        rw [hx0] at hcs1; exact hcs1.trans hcs2
      exact SepWP.done hpcf hrunf ⟨⟨by rw [hspf, hsp1], hsp_alf, hcs0f,
        hvm1.trans ((bl_vmPreserved _ s1).trans hvm_h),
        by rw [htr_h, bl_trace, htr1], by rw [hfs_h, bl_fs, hfs1], hclf⟩,
        Entails.refl _⟩

private theorem shaState_be_length (st : ShaState) :
    (st.toList.flatMap (toBEBytes 4)).length = 32 := by
  have hlen : st.toList.length = 8 := st.2
  rcases h : st.toList with
    _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    (rw [h] at hlen; try (simp at hlen))
  simp [toBEBytes]

private theorem shaStateBytes_length (st : ShaState) : (shaStateBytes st).length = 32 := by
  unfold shaStateBytes
  have hlen : st.toList.length = 8 := st.2
  rcases h : st.toList with
    _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    (rw [h] at hlen; try (simp at hlen))
  rfl

private def HmacCoreRegsPreserved (s sf : State) : Prop :=
  sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
  sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
  sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
  calleeSavedVRegs sf = calleeSavedVRegs s

private theorem HmacCoreRegsPreserved.trans {s1 s2 s3 : State}
    (h1 : HmacCoreRegsPreserved s1 s2) (h2 : HmacCoreRegsPreserved s2 s3) :
    HmacCoreRegsPreserved s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩

private theorem HmacCoreRegsPreserved.of_csp {s sf : State}
    (h : CalleeSavedPreserved s sf) : HmacCoreRegsPreserved s sf := by
  rcases (CalleeSavedPreserved.iff_regs s sf).mp h with
    ⟨h19, _, _, h22, h23, h24, _, _, h27, h28, _, hv⟩
  exact ⟨h19, h22, h23, h24, h27, h28, hv⟩

private def hmacInnerState (ipad data : List (BitVec 8)) : ShaState :=
  if data.isEmpty then
    haclUpdateLastState sha256CompressState 64 ipad sha256IV
  else
    let nblk := 64 * ((data.length - 1) / 64)
    haclUpdateLastState sha256CompressState (64 + data.length) (data.drop nblk)
      ((chunks64 (data.take nblk)).foldl sha256CompressState (sha256CompressState sha256IV ipad))

private theorem hmacInnerState_be (ipad data : List (BitVec 8)) :
    (hmacInnerState ipad data).toList.flatMap (toBEBytes 4) =
      libcruxHmacInnerPure sha256CompressState ipad data := by
  unfold hmacInnerState libcruxHmacInnerPure; split <;> rfl

private def hmacOuterState (key data : List (BitVec 8)) : ShaState :=
  let k0 := libcruxHmacKeyBlock sha256CompressState key
  let ipad := k0.map (· ^^^ 0x36#8)
  let opad := k0.map (· ^^^ 0x5c#8)
  haclUpdateLastState sha256CompressState 96
    (libcruxHmacInnerPure sha256CompressState ipad data)
    (sha256CompressState sha256IV opad)

private theorem hmacOuterState_be (key data : List (BitVec 8)) :
    (hmacOuterState key data).toList.flatMap (toBEBytes 4) =
      hmacWith sha256CompressState key data := by
  rw [← libcruxHmacPure_eq_hmacWith]; rfl

private theorem hmac_inner_sha256_wp [HaclPlacement] {P : Program}
    (hP : HaclInProg P haclMpl) (hsubs : HaclSubroutinesTrace P haclMpl)
    {x : LibcruxHmacCall} {pIpad : BitVec 64} {ipad : List (BitVec 8)}
    {s : State} {Frame : SepProp}
    (hipad : ipad.length = 64) (hd32 : x.data.length < 2 ^ 32)
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + 1060#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = x.dataA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.data.length)
    (hx23 : s.readReg64 .x23 = pIpad)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.data.length) :
    SepWP P (haclMpl.base 6 + 2012#64) s
      (memRegion (s.sp + 64#64) 32 ∗ (pIpad ↦ₛ ipad) ∗ (x.dataA ↦ₛ x.data) ∗
       stackAt s.sp 4096 ∗ Frame)
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧ HmacCoreRegsPreserved s sf ∧
         VmPreserved s sf ∧ sf.trace = s.trace ∧ sf.fs = s.fs ∧
         libcruxHmacLib.CodeLoaded haclMpl sf.mem) ∧
        (P' ⊢ ((s.sp + 64#64) ↦ₛ shaStateBytes (hmacInnerState ipad x.data)) ∗
              (pIpad ↦ₛ ipad) ∗ (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)) := by
  by_cases hdata : x.data = []
  · refine sepWP_seg6 hP hcl (Pre := memRegion (s.sp + 64#64) 32)
      (Post := (s.sp + 64#64) ↦ₛ shaStateBytes sha256IV)
      (Frame := (pIpad ↦ₛ ipad) ∗ (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)
      (PurePost := fun sf => sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
        sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 64#64 ∧ sf.readReg64 .x2 = s.readReg64 .x23 ∧
        sf.readReg64 .x3 = 64#64 ∧ sf.readReg64 .x4 = s.sp + 64#64 ∧ sf.readReg64 .x5 = 8#64)
      (Entails.of_eq (by sep_ac_rfl))
      (fun m => by
        have h := hmac_seg_inner_empty (s := s.setMem m) (R := emp)
          (by cases s; exact hpc) (by cases s; exact hrun) (by cases s; exact hsp_align)
          (by cases s; simpa [hdata] using hx26)
        cases s; simpa [sepConj_emp] using h)
      fun s1 hpc1 hrun1 hvm1 htr1 hfs1 hcl1 ⟨hsp1, hcs1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1⟩ => ?_
    have hsp_al1 : s1.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp1]
    refine call_last_6 hP hsubs 2008 64 64 pIpad ipad (s.sp + 64#64) sha256IV
      ((x.dataA ↦ₛ x.data) ∗ Frame) hcl1 hpc1 hrun1 hsp_al1
      ⟨by rw [hx0_1]; rfl, Nat.le_refl 64, by rw [hx1_1]; rfl, hx2_1.trans hx23,
       by rw [hx3_1, hipad]; rfl, by omega, hx4_1, hx5_1⟩
      (by rw [hsp1]; exact Entails.of_eq (by sep_ac_rfl))
      fun sf hpcf hrunf hspf hsp_alf hcs2 hvm2 htr2 hfs2 hclf => ?_
    refine SepWP.done hpcf hrunf ⟨⟨by rw [hspf, hsp1], hsp_alf,
      (HmacCoreRegsPreserved.of_csp hcs1).trans (HmacCoreRegsPreserved.of_csp hcs2),
      hvm1.trans hvm2, by rw [htr2, htr1], by rw [hfs2, hfs1], hclf⟩, ?_⟩
    have hst_eq : haclUpdateLastState sha256CompressState 64 (ipad.take 64) sha256IV =
        hmacInnerState ipad x.data := by
      unfold hmacInnerState; simp [hdata, List.take_of_length_le (Nat.le_of_eq hipad)]
    rw [hsp1, hst_eq]; exact Entails.of_eq (by sep_ac_rfl)
  · have hpos : 0 < x.data.length := List.length_pos_iff.mpr hdata
    let L := x.data.length
    let nblk := 64 * ((L - 1) / 64)
    let remLen := L - nblk
    have hnblk_lt : nblk < L := by dsimp only [nblk]; omega
    have hrem_hi : remLen ≤ 64 := by dsimp only [remLen, nblk]; omega
    refine sepWP_seg6 hP hcl (Pre := memRegion (s.sp + 64#64) 32)
      (Post := (s.sp + 64#64) ↦ₛ shaStateBytes sha256IV)
      (Frame := (pIpad ↦ₛ ipad) ∗ (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)
      (PurePost := fun sf => sf.sp = s.sp ∧
        CalleeSavedPreserved
          (((s.writeReg64 .x25 (BitVec.ofNat 64 nblk)).writeReg64 .x21
            (BitVec.ofNat 64 remLen)).writeReg64 .x26 (BitVec.ofNat 64 remLen)) sf ∧
        sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = s.readReg64 .x23 ∧
        sf.readReg64 .x2 = 64#64 ∧ sf.readReg64 .x3 = s.sp + 64#64 ∧ sf.readReg64 .x4 = 8#64)
      (Entails.of_eq (by sep_ac_rfl))
      (fun m => by
        have h := hmac_seg_inner_nonempty_1 (L := L) (s := s.setMem m) (R := emp)
          hpos hd32 (by cases s; exact hpc) (by cases s; exact hrun)
          (by cases s; exact hsp_align) (by cases s; exact hx21) (by cases s; exact hx26)
        cases s; simpa [sepConj_emp] using h)
      fun s1 hpc1 hrun1 hvm1 htr1 hfs1 hcl1 ⟨hsp1, hcs1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1⟩ => ?_
    have hsp_al1 : s1.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp1]
    have hcr1 : HmacCoreRegsPreserved s s1 ∧
        s1.readReg64 .x20 = x.dataA ∧ s1.readReg64 .x21 = BitVec.ofNat 64 remLen ∧
        s1.readReg64 .x25 = BitVec.ofNat 64 nblk ∧ s1.readReg64 .x26 = BitVec.ofNat 64 remLen := by
      rcases (CalleeSavedPreserved.iff_regs _ s1).mp hcs1 with
        ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, _, hv⟩
      simp only [wp_norm, calleeSavedVRegs] at h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 hv
      exact ⟨⟨h19, h22, h23, h24, h27, h28, hv⟩, h20.trans hx20, h21, h25, h26⟩
    rcases hcr1 with ⟨hcore1, hx20_1, hx21_1, hx25_1, hx26_1⟩
    refine call_nblocks_6 hP hsubs 1208 64 pIpad ipad (s.sp + 64#64) sha256IV
      ((x.dataA ↦ₛ x.data) ∗ Frame) hcl1 hpc1 hrun1 hsp_al1
      ⟨by decide, by rw [hx0_1]; rfl, hx1_1.trans hx23, by rw [hx2_1, hipad]; rfl,
       by omega, by omega, hx3_1, hx4_1⟩
      (by rw [hsp1]; exact Entails.of_eq (by sep_ac_rfl))
      fun s2 hpc2 hrun2 hsp2 _ hcs2 hvm2 htr2 hfs2 hcl2 => ?_
    have hfold_ipad :
        (chunks64 (ipad.take (64 * (64 / 64)))).foldl sha256CompressState sha256IV =
        sha256CompressState sha256IV ipad := by
      rw [show 64 * (64 / 64) = 64 from rfl, List.take_of_length_le (Nat.le_of_eq hipad),
          chunks64_exact_one ipad hipad]; rfl
    refine sepWP_seg6 hP hcl2 (Pre := emp) (Post := emp)
      (Frame := ((s.sp + 64#64) ↦ₛ shaStateBytes (sha256CompressState sha256IV ipad)) ∗
        (pIpad ↦ₛ ipad) ∗ (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)
      (PurePost := fun sf => sf.sp = s2.sp ∧ CalleeSavedPreserved s2 sf ∧
        sf.readReg64 .x0 = ((s2.readReg64 .x25).setWidth 32).setWidth 64 ∧
        sf.readReg64 .x1 = s2.readReg64 .x20 ∧ sf.readReg64 .x2 = s2.readReg64 .x25 ∧
        sf.readReg64 .x3 = s2.sp + 64#64 ∧ sf.readReg64 .x4 = 8#64)
      (by rw [hsp1, hfold_ipad, emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl))
      (fun m => by
        have h := hmac_seg_inner_nonempty_2 (s := s2.setMem m) (R := emp)
          (by cases s2; exact hpc2) (by cases s2; exact hrun2)
        cases s2; exact h)
      fun s3 hpc3 hrun3 hvm3 htr3 hfs3 hcl3 ⟨hsp3, hcs3, hx0_3, hx1_3, hx2_3, hx3_3, hx4_3⟩ => ?_
    have hsp3_eq : s3.sp = s.sp := by rw [hsp3, hsp2, hsp1]
    have hsp_al3 : s3.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp3_eq]
    have hcs13 := hcs2.trans hcs3
    have hx20_3 : s3.readReg64 .x20 = x.dataA := (CalleeSavedPreserved.readReg64_x20 hcs13).trans hx20_1
    have hx25_3 : s3.readReg64 .x25 = BitVec.ofNat 64 nblk :=
      (CalleeSavedPreserved.readReg64_x25 hcs13).trans hx25_1
    have hlen_tk : (x.data.take nblk).length = nblk := List.length_take_of_le (by omega)
    have hd_split : (x.dataA ↦ₛ x.data) =
        (x.dataA ↦ₛ x.data.take nblk) ∗ ((x.dataA + BitVec.ofNat 64 nblk) ↦ₛ x.data.drop nblk) := by
      conv_lhs => rw [← List.take_append_drop nblk x.data]
      rw [pointsToBytes_append, hlen_tk]
    refine call_nblocks_6 hP hsubs 1232 nblk x.dataA (x.data.take nblk) (s.sp + 64#64)
      (sha256CompressState sha256IV ipad)
      ((pIpad ↦ₛ ipad) ∗ ((x.dataA + BitVec.ofNat 64 nblk) ↦ₛ x.data.drop nblk) ∗ Frame)
      hcl3 hpc3 hrun3 hsp_al3
      ⟨by omega, ?_, by rw [hx1_3, (CalleeSavedPreserved.readReg64_x20 hcs2).trans hx20_1],
       ?_, Nat.le_of_eq hlen_tk.symm, by omega, by rw [hx3_3, hsp2, hsp1], hx4_3⟩
      (by rw [emp_sepConj, hd_split, hsp3_eq]; exact Entails.of_eq (by sep_ac_rfl))
      fun s4 hpc4 hrun4 hsp4 _ hcs4 hvm4 htr4 hfs4 hcl4 => ?_
    · rw [hx0_3, (CalleeSavedPreserved.readReg64_x25 hcs2).trans hx25_1]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    · rw [hx2_3, (CalleeSavedPreserved.readReg64_x25 hcs2).trans hx25_1, hlen_tk,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · let st_mid := (chunks64 (x.data.take nblk)).foldl sha256CompressState
        (sha256CompressState sha256IV ipad)
      have htk_eq : (x.data.take nblk).take (64 * (nblk / 64)) = x.data.take nblk := by
        rw [show 64 * (nblk / 64) = nblk by dsimp only [nblk]; omega, List.take_take, Nat.min_self]
      have hcs14 := hcs13.trans hcs4
      refine sepWP_seg6 hP hcl4 (Pre := emp) (Post := emp)
        (Frame := ((s.sp + 64#64) ↦ₛ shaStateBytes st_mid) ∗
          ((x.dataA + BitVec.ofNat 64 nblk) ↦ₛ x.data.drop nblk) ∗
          (x.dataA ↦ₛ x.data.take nblk) ∗ (pIpad ↦ₛ ipad) ∗ stackAt s.sp 4096 ∗ Frame)
        (PurePost := fun sf => sf.sp = s4.sp ∧ CalleeSavedPreserved s4 sf ∧
          sf.readReg64 .x0 = s4.readReg64 .x25 + s4.readReg64 .x26 + 64#64 ∧
          sf.readReg64 .x1 = ((s4.readReg64 .x26).setWidth 32).setWidth 64 ∧
          sf.readReg64 .x2 = s4.readReg64 .x20 + s4.readReg64 .x25 ∧
          sf.readReg64 .x3 = s4.readReg64 .x21 ∧ sf.readReg64 .x4 = s4.sp + 64#64 ∧
          sf.readReg64 .x5 = 8#64)
        (by rw [hsp3_eq, htk_eq, emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl))
        (fun m => by
          have h := hmac_seg_inner_nonempty_3 (s := s4.setMem m) (R := emp)
            (by cases s4; exact hpc4) (by cases s4; exact hrun4)
          cases s4; exact h)
        fun s5 hpc5 hrun5 hvm5 htr5 hfs5 hcl5 ⟨hsp5, hcs5, hx0_5, hx1_5, hx2_5, hx3_5, hx4_5, hx5_5⟩ => ?_
      have hsp5_eq : s5.sp = s.sp := by rw [hsp5, hsp4, hsp3_eq]
      have hsp_al5 : s5.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp5_eq]
      have hx20_4 : s4.readReg64 .x20 = x.dataA :=
        (CalleeSavedPreserved.readReg64_x20 hcs14).trans hx20_1
      have hx21_4 : s4.readReg64 .x21 = BitVec.ofNat 64 remLen :=
        (CalleeSavedPreserved.readReg64_x21 hcs14).trans hx21_1
      have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 nblk :=
        (CalleeSavedPreserved.readReg64_x25 hcs14).trans hx25_1
      have hx26_4 : s4.readReg64 .x26 = BitVec.ofNat 64 remLen :=
        (CalleeSavedPreserved.readReg64_x26 hcs14).trans hx26_1
      have hlen_dr : (x.data.drop nblk).length = remLen := List.length_drop
      refine call_last_6 hP hsubs 2008 (64 + L) remLen (x.dataA + BitVec.ofNat 64 nblk)
        (x.data.drop nblk) (s.sp + 64#64) st_mid
        ((x.dataA ↦ₛ x.data.take nblk) ∗ (pIpad ↦ₛ ipad) ∗ Frame)
        hcl5 hpc5 hrun5 hsp_al5
        ⟨?_, hrem_hi, ?_, by rw [hx2_5, hx20_4, hx25_4], ?_, Nat.le_of_eq hlen_dr.symm,
         by rw [hx4_5, hsp4, hsp3_eq], hx5_5⟩
        (by rw [emp_sepConj, hsp5_eq]; exact Entails.of_eq (by sep_ac_rfl))
        fun sf hpcf hrunf hspf hsp_alf hcs6 hvm6 htr6 hfs6 hclf => ?_
      · rw [hx0_5, hx25_4, hx26_4, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
            BitVec.toNat_ofNat, show (64#64 : BitVec 64).toNat = 64 from rfl]
        have : nblk < 2 ^ 64 := by omega
        have : remLen < 2 ^ 64 := by omega
        omega
      · rw [hx1_5, hx26_4]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
            BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
      · rw [hx3_5, hx21_4, hlen_dr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · refine SepWP.done hpcf hrunf ⟨⟨by rw [hspf, hsp5_eq], hsp_alf,
          hcore1.trans (HmacCoreRegsPreserved.of_csp ((hcs14.trans hcs5).trans hcs6)),
          ((((hvm1.trans hvm2).trans hvm3).trans hvm4).trans hvm5).trans hvm6,
          by rw [htr6, htr5, htr4, htr3, htr2, htr1],
          by rw [hfs6, hfs5, hfs4, hfs3, hfs2, hfs1], hclf⟩, ?_⟩
        have hst_eq : haclUpdateLastState sha256CompressState (64 + L)
            ((x.data.drop nblk).take remLen) st_mid = hmacInnerState ipad x.data := by
          unfold hmacInnerState
          rw [List.isEmpty_eq_false_iff.mpr hdata,
              List.take_of_length_le (Nat.le_of_eq hlen_dr)]; rfl
        rw [hsp5_eq, hst_eq]; refine Entails.of_eq ?_; rw [hd_split]; sep_ac_rfl

private theorem hmac_core_1004_to_2140_wp [HaclPlacement] {P : Program}
    (hP : HaclInProg P haclMpl) (hsubs : HaclSubroutinesTrace P haclMpl)
    {x : LibcruxHmacCall} {pKey pIpad pOpad : BitVec 64} {s : State} {Frame : SepProp}
    (hd32 : x.data.length < 2 ^ 32)
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + 1004#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = pOpad) (hpOpad : pOpad ≠ 0#64)
    (hx20 : s.readReg64 .x20 = x.dataA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.data.length)
    (hx22 : s.readReg64 .x22 = pKey) (hx23 : s.readReg64 .x23 = pIpad)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.data.length) :
    let k0 := libcruxHmacKeyBlock sha256CompressState x.key
    SepWP P (haclMpl.base 6 + 2140#64) s
      ((s.sp ↦ₛ List.replicate 32 0#8) ∗ memRegion (s.sp + 64#64) 32 ∗
       (pKey ↦ₛ k0) ∗ (pIpad ↦ₛ k0.map (· ^^^ 0x36#8)) ∗ memRegion pOpad 64 ∗
       (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧
         HmacCoreRegsPreserved (s.writeReg64 .x24 pOpad) sf ∧
         VmPreserved s sf ∧ sf.trace = s.trace ∧ sf.fs = s.fs ∧
         libcruxHmacLib.CodeLoaded haclMpl sf.mem) ∧
        (P' ⊢ (s.sp ↦ₛ hmacWith sha256CompressState x.key x.data) ∗
              ((s.sp + 64#64) ↦ₛ shaStateBytes (hmacOuterState x.key x.data)) ∗
              memRegion pKey 64 ∗ memRegion pIpad 64 ∗ memRegion pOpad 64 ∗
              (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)) := by
  intro k0
  let ipad := k0.map (· ^^^ 0x36#8)
  let opad := k0.map (· ^^^ 0x5c#8)
  have hk0 : k0.length = 64 := libcruxHmacKeyBlock_length sha256CompressState x.key
  have hipad : ipad.length = 64 := by simp [ipad, hk0]
  have hopad : opad.length = 64 := by simp [opad, hk0]
  -- 1. `+1004 → +1060`: `hmac_seg_opad_xor`
  refine sepWP_seg6 hP hcl
    (Pre := (pKey ↦ₛ k0) ∗ memRegion pOpad 64)
    (Post := (pKey ↦ₛ k0) ∗ (pOpad ↦ₛ opad))
    (Frame := (s.sp ↦ₛ List.replicate 32 0#8) ∗ memRegion (s.sp + 64#64) 32 ∗
      (pIpad ↦ₛ ipad) ∗ (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)
    (PurePost := fun sf => sf.sp = s.sp ∧ CalleeSavedPreserved (s.writeReg64 .x24 pOpad) sf)
    (Entails.of_eq (by sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_opad_xor (pKey := pKey) (pOpad := pOpad) (k0 := k0) (s := s.setMem m)
        (R := emp) hk0 (by cases s; exact hpc) (by cases s; exact hrun)
        (by cases s; exact hx0) hpOpad (by cases s; exact hx22)
      cases s; simpa [sepConj_emp] using h)
    fun s1 hpc1 hrun1 hvm1 htr1 hfs1 hcl1 ⟨hsp1, hcs1⟩ => ?_
  have hsp_al1 : s1.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp1]
  have hcr01 : HmacCoreRegsPreserved (s.writeReg64 .x24 pOpad) s1 := HmacCoreRegsPreserved.of_csp hcs1
  have hx20_1 : s1.readReg64 .x20 = x.dataA := (CalleeSavedPreserved.readReg64_x20 hcs1).trans hx20
  have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 x.data.length :=
    (CalleeSavedPreserved.readReg64_x21 hcs1).trans hx21
  have hx23_1 : s1.readReg64 .x23 = pIpad := (CalleeSavedPreserved.readReg64_x23 hcs1).trans hx23
  have hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 x.data.length :=
    (CalleeSavedPreserved.readReg64_x26 hcs1).trans hx26
  -- 2. `+1060 → +2012`: `hmac_inner_sha256_wp`
  have hinner := hmac_inner_sha256_wp hP hsubs (x := x) (pIpad := pIpad) (ipad := ipad) (s := s1)
    (Frame := (s.sp ↦ₛ List.replicate 32 0#8) ∗ (pKey ↦ₛ k0) ∗ (pOpad ↦ₛ opad) ∗ Frame)
    hipad hd32 hcl1 hpc1 hrun1 hsp_al1 hx20_1 hx21_1 hx23_1 hx26_1
  refine SepWP.bind_sepPost hinner
    (by rw [hsp1]; exact Entails.of_eq (by sep_ac_rfl))
    fun s2 hpc2 hrun2 ⟨hsp2, hsp_al2, hcr12, hvm2, htr2, hfs2, hcl2⟩ => ?_
  have hsp2_eq : s2.sp = s.sp := hsp2.trans hsp1
  have hcr02 := hcr01.trans hcr12
  -- 3. `+2012 → +2032`: `hmac_seg_inner_finish_args` + `call_finish_6`
  refine sepWP_seg6 hP hcl2 (Pre := emp) (Post := emp)
    (Frame := (((s.sp + 64#64) ↦ₛ shaStateBytes (hmacInnerState ipad x.data)) ∗
      (pIpad ↦ₛ ipad) ∗ (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗
      ((s.sp ↦ₛ List.replicate 32 0#8) ∗ (pKey ↦ₛ k0) ∗ (pOpad ↦ₛ opad) ∗ Frame)))
    (PurePost := fun sf => sf.sp = s2.sp ∧ CalleeSavedPreserved s2 sf ∧
      sf.readReg64 .x0 = s2.sp + 64#64 ∧ sf.readReg64 .x1 = 8#64 ∧
      sf.readReg64 .x2 = s2.readReg64 .x23 ∧ sf.readReg64 .x3 = 64#64)
    (by rw [hsp1, emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_inner_finish_args (s := s2.setMem m) (R := emp)
        (by cases s2; exact hpc2) (by cases s2; exact hrun2)
      cases s2; exact h)
    fun s3 hpc3 hrun3 hvm3 htr3 hfs3 hcl3 ⟨hsp3, hcs3, hx0_3, hx1_3, hx2_3, hx3_3⟩ => ?_
  have hsp3_eq : s3.sp = s.sp := hsp3.trans hsp2_eq
  have hsp_al3 : s3.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp3_eq]
  have hx23_2 : s2.readReg64 .x23 = pIpad := by
    have := hcr02.2.2.1; simpa [wp_norm, hx23] using this
  refine call_finish_6 hP hsubs 2028 (s.sp + 64#64) (hmacInnerState ipad x.data) pIpad ipad
    ((s.sp ↦ₛ List.replicate 32 0#8) ∗ (pKey ↦ₛ k0) ∗ (pOpad ↦ₛ opad) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl3 hpc3 hrun3 hsp_al3
    ⟨by rw [hx0_3, hsp2_eq], hx1_3, hx2_3.trans hx23_2, by rw [hx3_3, hipad]; rfl, by omega⟩
    (by rw [emp_sepConj, hsp3_eq]; exact Entails.of_eq (by sep_ac_rfl))
    fun s4 hpc4 hrun4 hsp4 _ hcs4 hvm4 htr4 hfs4 hcl4 => ?_
  let inner := libcruxHmacInnerPure sha256CompressState ipad x.data
  let innerBuf := inner ++ ipad.drop 32
  have hinner_len : inner.length = 32 := by
    dsimp only [inner]; rw [← hmacInnerState_be]; exact shaState_be_length _
  have hbuf_len : innerBuf.length = 64 := by simp [innerBuf, hinner_len, hipad]
  have hsp4_eq : s4.sp = s.sp := hsp4.trans hsp3_eq
  have hcr04 := hcr02.trans (HmacCoreRegsPreserved.of_csp (hcs3.trans hcs4))
  -- 4. `+2032 → +2044`: `hmac_seg_outer_init_args` + `call_init_6`
  refine sepWP_seg6 hP hcl4 (Pre := emp) (Post := emp)
    (Frame := ((s.sp + 64#64) ↦ₛ shaStateBytes (hmacInnerState ipad x.data)) ∗
      (pIpad ↦ₛ innerBuf) ∗ (s.sp ↦ₛ List.replicate 32 0#8) ∗ (pKey ↦ₛ k0) ∗
      (pOpad ↦ₛ opad) ∗ (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)
    (PurePost := fun sf => sf.sp = s4.sp ∧ CalleeSavedPreserved s4 sf ∧
      sf.readReg64 .x0 = s4.sp + 64#64 ∧ sf.readReg64 .x1 = 8#64)
    (by rw [hsp3_eq, hmacInnerState_be, emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_outer_init_args (s := s4.setMem m) (R := emp)
        (by cases s4; exact hpc4) (by cases s4; exact hrun4)
      cases s4; exact h)
    fun s5 hpc5 hrun5 hvm5 htr5 hfs5 hcl5 ⟨hsp5, hcs5, hx0_5, hx1_5⟩ => ?_
  have hsp5_eq : s5.sp = s.sp := hsp5.trans hsp4_eq
  have hsp_al5 : s5.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp5_eq]
  refine call_init_6 hP hsubs 2040 (s.sp + 64#64) (shaStateBytes (hmacInnerState ipad x.data))
    ((pIpad ↦ₛ innerBuf) ∗ (s.sp ↦ₛ List.replicate 32 0#8) ∗ (pKey ↦ₛ k0) ∗
      (pOpad ↦ₛ opad) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl5 hpc5 hrun5 hsp_al5
    ⟨by rw [hx0_5, hsp4_eq], hx1_5, shaStateBytes_length _⟩
    (by rw [emp_sepConj, hsp5_eq]; exact Entails.of_eq (by sep_ac_rfl))
    fun s6 hpc6 hrun6 hsp6 _ hcs6 hvm6 htr6 hfs6 hcl6 => ?_
  have hsp6_eq : s6.sp = s.sp := hsp6.trans hsp5_eq
  have hcr06 := hcr04.trans (HmacCoreRegsPreserved.of_csp (hcs5.trans hcs6))
  -- 5. `+2044 → +2068`: `hmac_seg_outer_opad_args` + `call_nblocks_6(64, opad)`
  refine sepWP_seg6 hP hcl6 (Pre := emp) (Post := emp)
    (Frame := ((s.sp + 64#64) ↦ₛ shaStateBytes sha256IV) ∗ (pOpad ↦ₛ opad) ∗
      (pIpad ↦ₛ innerBuf) ∗ (s.sp ↦ₛ List.replicate 32 0#8) ∗ (pKey ↦ₛ k0) ∗
      (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)
    (PurePost := fun sf => sf.sp = s6.sp ∧ CalleeSavedPreserved s6 sf ∧
      sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = s6.readReg64 .x24 ∧ sf.readReg64 .x2 = 64#64 ∧
      sf.readReg64 .x3 = s6.sp + 64#64 ∧ sf.readReg64 .x4 = 8#64)
    (by rw [hsp5_eq, emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_outer_opad_args (s := s6.setMem m) (R := emp)
        (by cases s6; exact hpc6) (by cases s6; exact hrun6)
      cases s6; exact h)
    fun s7 hpc7 hrun7 hvm7 htr7 hfs7 hcl7 ⟨hsp7, hcs7, hx0_7, hx1_7, hx2_7, hx3_7, hx4_7⟩ => ?_
  have hsp7_eq : s7.sp = s.sp := hsp7.trans hsp6_eq
  have hsp_al7 : s7.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp7_eq]
  have hx24_6 : s6.readReg64 .x24 = pOpad := by
    have := hcr06.2.2.2.1; simpa [wp_norm] using this
  refine call_nblocks_6 hP hsubs 2064 64 pOpad opad (s.sp + 64#64) sha256IV
    ((pIpad ↦ₛ innerBuf) ∗ (s.sp ↦ₛ List.replicate 32 0#8) ∗ (pKey ↦ₛ k0) ∗
      (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl7 hpc7 hrun7 hsp_al7
    ⟨by decide, by rw [hx0_7]; rfl, hx1_7.trans hx24_6, by rw [hx2_7, hopad]; rfl,
     by omega, by omega, by rw [hx3_7, hsp6_eq], hx4_7⟩
    (by rw [emp_sepConj, hsp7_eq]; exact Entails.of_eq (by sep_ac_rfl))
    fun s8 hpc8 hrun8 hsp8 _ hcs8 hvm8 htr8 hfs8 hcl8 => ?_
  have hfold_opad :
      (chunks64 (opad.take (64 * (64 / 64)))).foldl sha256CompressState sha256IV =
      sha256CompressState sha256IV opad := by
    rw [show 64 * (64 / 64) = 64 from rfl, List.take_of_length_le (Nat.le_of_eq hopad),
        chunks64_exact_one opad hopad]; rfl
  have hsp8_eq : s8.sp = s.sp := hsp8.trans hsp7_eq
  have hcr08 := hcr06.trans (HmacCoreRegsPreserved.of_csp (hcs7.trans hcs8))
  -- 6. `+2068 → +2092`: `hmac_seg_outer_zero_args` + `call_nblocks_6(0, [])`
  refine sepWP_seg6 hP hcl8 (Pre := emp) (Post := emp)
    (Frame := ((s.sp + 64#64) ↦ₛ shaStateBytes (sha256CompressState sha256IV opad)) ∗
      (pIpad ↦ₛ innerBuf) ∗ (pOpad ↦ₛ opad) ∗ (s.sp ↦ₛ List.replicate 32 0#8) ∗
      (pKey ↦ₛ k0) ∗ (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)
    (PurePost := fun sf => sf.sp = s8.sp ∧ CalleeSavedPreserved s8 sf ∧
      sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = s8.readReg64 .x23 ∧ sf.readReg64 .x2 = 0#64 ∧
      sf.readReg64 .x3 = s8.sp + 64#64 ∧ sf.readReg64 .x4 = 8#64)
    (by rw [hsp7_eq, hfold_opad, emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_outer_zero_args (s := s8.setMem m) (R := emp)
        (by cases s8; exact hpc8) (by cases s8; exact hrun8)
      cases s8; exact h)
    fun s9 hpc9 hrun9 hvm9 htr9 hfs9 hcl9 ⟨hsp9, hcs9, hx0_9, hx1_9, hx2_9, hx3_9, hx4_9⟩ => ?_
  have hsp9_eq : s9.sp = s.sp := hsp9.trans hsp8_eq
  have hsp_al9 : s9.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp9_eq]
  have hx23_8 : s8.readReg64 .x23 = pIpad := by
    have := hcr08.2.2.1; simpa [wp_norm, hx23] using this
  refine call_nblocks_6 hP hsubs 2088 0 pIpad [] (s.sp + 64#64) (sha256CompressState sha256IV opad)
    ((pIpad ↦ₛ innerBuf) ∗ (pOpad ↦ₛ opad) ∗ (s.sp ↦ₛ List.replicate 32 0#8) ∗
      (pKey ↦ₛ k0) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl9 hpc9 hrun9 hsp_al9
    ⟨by decide, by rw [hx0_9]; rfl, hx1_9.trans hx23_8, by rw [hx2_9]; rfl,
     Nat.le_refl 0, by decide, by rw [hx3_9, hsp8_eq], hx4_9⟩
    (by rw [pointsToBytes_nil, emp_sepConj, emp_sepConj, hsp9_eq]; exact Entails.of_eq (by sep_ac_rfl))
    fun s10 hpc10 hrun10 hsp10 _ hcs10 hvm10 htr10 hfs10 hcl10 => ?_
  have hsp10_eq : s10.sp = s.sp := hsp10.trans hsp9_eq
  have hcr10 := hcr08.trans (HmacCoreRegsPreserved.of_csp (hcs9.trans hcs10))
  -- 7. `+2092 → +2120`: `hmac_seg_outer_last_args` + `call_last_6(96, 32, innerBuf)`
  refine sepWP_seg6 hP hcl10 (Pre := emp) (Post := emp)
    (Frame := ((s.sp + 64#64) ↦ₛ shaStateBytes (sha256CompressState sha256IV opad)) ∗
      (pIpad ↦ₛ innerBuf) ∗ (pOpad ↦ₛ opad) ∗ (s.sp ↦ₛ List.replicate 32 0#8) ∗
      (pKey ↦ₛ k0) ∗ (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)
    (PurePost := fun sf => sf.sp = s10.sp ∧ CalleeSavedPreserved s10 sf ∧
      sf.readReg64 .x0 = 96#64 ∧ sf.readReg64 .x1 = 32#64 ∧ sf.readReg64 .x2 = s10.readReg64 .x23 ∧
      sf.readReg64 .x3 = 64#64 ∧ sf.readReg64 .x4 = s10.sp + 64#64 ∧ sf.readReg64 .x5 = 8#64)
    (by rw [pointsToBytes_nil, emp_sepConj, emp_sepConj, hsp9_eq]; exact Entails.of_eq (by sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_outer_last_args (s := s10.setMem m) (R := emp)
        (by cases s10; exact hpc10) (by cases s10; exact hrun10)
      cases s10; exact h)
    fun s11 hpc11 hrun11 hvm11 htr11 hfs11 hcl11 ⟨hsp11, hcs11, hx0_11, hx1_11, hx2_11, hx3_11, hx4_11, hx5_11⟩ => ?_
  have hsp11_eq : s11.sp = s.sp := hsp11.trans hsp10_eq
  have hsp_al11 : s11.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp11_eq]
  have hx23_10 : s10.readReg64 .x23 = pIpad := by
    have := hcr10.2.2.1; simpa [wp_norm, hx23] using this
  refine call_last_6 hP hsubs 2116 96 32 pIpad innerBuf (s.sp + 64#64)
    (sha256CompressState sha256IV opad)
    ((pOpad ↦ₛ opad) ∗ (s.sp ↦ₛ List.replicate 32 0#8) ∗ (pKey ↦ₛ k0) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl11 hpc11 hrun11 hsp_al11
    ⟨by rw [hx0_11]; rfl, by decide, by rw [hx1_11]; rfl, hx2_11.trans hx23_10,
     by rw [hx3_11, hbuf_len]; rfl, by omega, by rw [hx4_11, hsp10_eq], hx5_11⟩
    (by rw [emp_sepConj, hsp11_eq]; exact Entails.of_eq (by sep_ac_rfl))
    fun s12 hpc12 hrun12 hsp12 _ hcs12 hvm12 htr12 hfs12 hcl12 => ?_
  have htk32 : innerBuf.take 32 = inner := by
    dsimp only [innerBuf]
    rw [List.take_append_of_le_length (Nat.le_of_eq hinner_len.symm),
        List.take_of_length_le (Nat.le_of_eq hinner_len)]
  have hsp12_eq : s12.sp = s.sp := hsp12.trans hsp11_eq
  have hcr12' := hcr10.trans (HmacCoreRegsPreserved.of_csp (hcs11.trans hcs12))
  -- 8. `+2120 → +2140`: `hmac_seg_outer_finish_args` + `call_finish_6(sp)`
  refine sepWP_seg6 hP hcl12 (Pre := emp) (Post := emp)
    (Frame := ((s.sp + 64#64) ↦ₛ shaStateBytes (hmacOuterState x.key x.data)) ∗
      (s.sp ↦ₛ List.replicate 32 0#8) ∗ (pIpad ↦ₛ innerBuf) ∗ (pOpad ↦ₛ opad) ∗
      (pKey ↦ₛ k0) ∗ (x.dataA ↦ₛ x.data) ∗ stackAt s.sp 4096 ∗ Frame)
    (PurePost := fun sf => sf.sp = s12.sp ∧ CalleeSavedPreserved s12 sf ∧
      sf.readReg64 .x0 = s12.sp + 64#64 ∧ sf.readReg64 .x1 = 8#64 ∧
      sf.readReg64 .x2 = s12.sp ∧ sf.readReg64 .x3 = 32#64)
    (by
      have hst_out : haclUpdateLastState sha256CompressState 96 (innerBuf.take 32)
          (sha256CompressState sha256IV opad) = hmacOuterState x.key x.data := by
        rw [htk32]; rfl
      rw [hsp11_eq, hst_out, emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_outer_finish_args (s := s12.setMem m) (R := emp)
        (by cases s12; exact hpc12) (by cases s12; exact hrun12)
      cases s12; exact h)
    fun s13 hpc13 hrun13 hvm13 htr13 hfs13 hcl13 ⟨hsp13, hcs13, hx0_13, hx1_13, hx2_13, hx3_13⟩ => ?_
  have hsp13_eq : s13.sp = s.sp := hsp13.trans hsp12_eq
  have hsp_al13 : s13.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp13_eq]
  refine call_finish_6 hP hsubs 2136 (s.sp + 64#64) (hmacOuterState x.key x.data) s.sp
    (List.replicate 32 0#8)
    ((pIpad ↦ₛ innerBuf) ∗ (pOpad ↦ₛ opad) ∗ (pKey ↦ₛ k0) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl13 hpc13 hrun13 hsp_al13
    ⟨by rw [hx0_13, hsp12_eq], hx1_13, hx2_13.trans hsp12_eq,
     by rw [hx3_13, List.length_replicate]; rfl, by simp⟩
    (by rw [emp_sepConj, hsp13_eq]; exact Entails.of_eq (by sep_ac_rfl))
    fun sf hpcf hrunf hspf hsp_alf hcs14 hvm14 htr14 hfs14 hclf => ?_
  refine SepWP.done hpcf hrunf ⟨⟨hspf.trans hsp13_eq, hsp_alf,
    hcr12'.trans (HmacCoreRegsPreserved.of_csp (hcs13.trans hcs14)),
    ((((((((((((hvm1.trans hvm2).trans hvm3).trans hvm4).trans hvm5).trans hvm6).trans
      hvm7).trans hvm8).trans hvm9).trans hvm10).trans hvm11).trans hvm12).trans hvm13).trans hvm14,
    by rw [htr14, htr13, htr12, htr11, htr10, htr9, htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1],
    by rw [hfs14, hfs13, hfs12, hfs11, hfs10, hfs9, hfs8, hfs7, hfs6, hfs5, hfs4, hfs3, hfs2, hfs1],
    hclf⟩, ?_⟩
  rw [hsp13_eq, hmacOuterState_be, show (List.replicate 32 0#8).drop 32 = [] by simp, List.append_nil]
  have hmK : (pKey ↦ₛ k0) ⊢ memRegion pKey 64 :=
    hk0 ▸ pointsToBytes_entails_memRegion pKey k0
  have hmI : (pIpad ↦ₛ innerBuf) ⊢ memRegion pIpad 64 :=
    hbuf_len ▸ pointsToBytes_entails_memRegion pIpad innerBuf
  have hmO : (pOpad ↦ₛ opad) ⊢ memRegion pOpad 64 :=
    hopad ▸ pointsToBytes_entails_memRegion pOpad opad
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hmK (sepConj_mono hmI (sepConj_mono_left hmO)))))
  sep_ac_rfl

/-! ## 4. Block 6 Tail (`+2140 → ret`) and Top-Level `subroutine_ok` Contracts -/

private theorem hmacWith_sha256_length (key data : List (BitVec 8)) :
    (hmacWith sha256CompressState key data).length = 32 := by
  unfold CryptoGames.HMAC.hmacWith
  exact sha256With_length _ _

private theorem rustLayoutOk_64_1 : RustLayoutOk 64 1 :=
  ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩

private theorem rustLayoutOk_32_1 : RustLayoutOk 32 1 :=
  ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩

private theorem layoutOk_64_1 : LayoutOk 64 1 := rustLayoutOk_64_1.1

private theorem layoutOk_32_1 : LayoutOk 32 1 := rustLayoutOk_32_1.1

private theorem allocFailedIn_of_append {s0 sf : State}
    (htr : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], htr.symm⟩⟩
  unfold allocFailedIn
  simp [htr]

private theorem fitsEvents_hmacSha256_split {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : LibcruxHmacCall}
    (hEnv : FitsEnv M lim st (LibcruxHmacEnv x))
    (hk32 : x.key.length < 2 ^ 32) (hd32 : x.data.length < 2 ^ 32) :
    let st1 := M.stepEvents (rustAllocEvents 64 1) st
    let st2 := M.stepEvents (rustAllocEvents 64 1) st1
    let st3 := M.stepEvents (rustAllocEvents 64 1) st2
    let st4 := M.stepEvents (rustDeallocEvents 64 1) st3
    let st5 := M.stepEvents (rustDeallocEvents 64 1) st4
    let st6 := M.stepEvents (rustDeallocEvents 64 1) st5
    let st7 := M.stepEvents (rustAllocEvents 32 1) st6
    FitsEvents M lim st (rustAllocEvents 64 1) ∧
    FitsEvents M lim st1 (rustAllocEvents 64 1) ∧
    FitsEvents M lim st2 (rustAllocEvents 64 1) ∧
    FitsEvents M lim st6 (rustAllocEvents 32 1) ∧
    M.stepEvents libcruxHmacSha256Events st = st7 := by
  have htot : FitsEvents M lim st libcruxHmacSha256Events :=
    hEnv libcruxHmacSha256Events (by unfold LibcruxHmacEnv; split <;> [rfl; omega])
  unfold libcruxHmacSha256Events at htot ⊢
  simp only [List.append_assoc, fitsEvents_append, M.stepEvents_append] at htot ⊢
  exact ⟨htot.1, htot.2.1, htot.2.2.1, htot.2.2.2.2.2.2, trivial⟩

private theorem sepWPp_congr_pre {P : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hent : P1 ⊢ P2) (h : SepWPp P ret s P2 Q Qp oom) :
    SepWPp P ret s P1 Q Qp oom := fun R hm hLP =>
  h R (Satisfies.mono (sepConj_mono_left hent) hm) hLP

private theorem sepWPp_exists_elim {α : Type} {P : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a : α, SepWPp P ret s (Φ a ∗ Rest) Q Qp oom) :
    SepWPp P ret s ((∃∗ a : α, Φ a) ∗ Rest) Q Qp oom := by
  intro R hm hLP
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hma⟩
  rw [← sepConj_assoc] at hma
  exact h a R hma hLP

private theorem sepWPp_pure_left {P : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp P ret s Pre Q Qp oom) :
    SepWPp P ret s (⌜φ⌝ ∗ Pre) Q Qp oom := by
  intro R hm hLP
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hLP

private theorem sepWPp_done {P : Program} {ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hQ : Q s Pre) :
    SepWPp P ret s Pre Q Qp oom := fun _ hm _ =>
  ⟨s, Steps.refl s, Or.inl ⟨hpc, hrun, Pre, hm, hQ⟩⟩

private theorem sepWPp_of_sepWP {P : Program} {mid ret : BitVec 64} {s : State}
    {FullPre Pre Post Frame : SepProp} {PurePost : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hsplit : FullPre ⊢ Pre ∗ Frame)
    (hwp : SepWP P mid s Pre (fun sm Pm => PurePost sm ∧ (Pm ⊢ Post)))
    (hcont : ∀ sm : State, sm.pc = mid → sm.status = .Running → PurePost sm →
      SepWPp P ret sm (Post ∗ Frame) Q Qp oom) :
    SepWPp P ret s FullPre Q Qp oom := by
  intro R hm hLP
  have hm' : s.mem ⊨ Pre ∗ (Frame ∗ R) := by
    rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hsplit) hm
  obtain ⟨sm, hsteps1, ⟨hpc, hrun, Pm, hmm, hpure, hent⟩ | ⟨_, hoom1⟩⟩ := hwp.elim hm' hLP
  · have hmm' : sm.mem ⊨ (Post ∗ Frame) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps2, hout2⟩ :=
      hcont sm hpc hrun hpure R hmm' (hsteps1.codeLoaded hLP)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom1)

private theorem sepWPp_of_sepWP_dep {P : Program} {mid ret : BitVec 64} {s : State}
    {FullPre Pre Frame : SepProp} {Post : State → SepProp} {PurePost : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hsplit : FullPre ⊢ Pre ∗ Frame)
    (hwp : SepWP P mid s Pre (fun sm Pm => PurePost sm ∧ (Pm ⊢ Post sm)))
    (hcont : ∀ sm : State, sm.pc = mid → sm.status = .Running → PurePost sm →
      SepWPp P ret sm (Post sm ∗ Frame) Q Qp oom) :
    SepWPp P ret s FullPre Q Qp oom := by
  intro R hm hLP
  have hm' : s.mem ⊨ Pre ∗ (Frame ∗ R) := by
    rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hsplit) hm
  obtain ⟨sm, hsteps1, ⟨hpc, hrun, Pm, hmm, hpure, hent⟩ | ⟨_, hoom1⟩⟩ := hwp.elim hm' hLP
  · have hmm' : sm.mem ⊨ (Post sm ∗ Frame) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps2, hout2⟩ :=
      hcont sm hpc hrun hpure R hmm' (hsteps1.codeLoaded hLP)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom1)

private theorem sepWPp_seg6 [HaclPlacement] {P : Program}
    (hP : HaclInProg P haclMpl) {mid ret : BitVec 64} {s : State}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    {FullPre Pre Post Frame : SepProp} {PurePost : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hsplit : FullPre ⊢ Pre ∗ Frame)
    (hseg : ∀ m : Memory,
      SepWP (libcruxHmacLib.blockProgram haclMpl 6) mid (s.setMem m) Pre
        (fun sm' Pm' => PurePost sm' ∧ (Pm' ⊢ Post)))
    (hcont : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      VmPreserved s sm → sm.trace = s.trace → sm.fs = s.fs →
      libcruxHmacLib.CodeLoaded haclMpl sm.mem → PurePost sm →
      SepWPp P ret sm (Post ∗ Frame) Q Qp oom)
    (hPure_mem : ∀ (sm : State) (m : Memory), PurePost (sm.setMem m) ↔ PurePost sm := by
      intro sm _; cases sm; exact Iff.rfl) :
    SepWPp P ret s FullPre Q Qp oom :=
  sepWPp_congr_pre hsplit <|
    sepWPp_block_seg (i := 6) (by decide) hP hcl (Post := fun _ => Post) (fun _ _ => rfl) hPure_mem
      hseg fun sm hpc hrun hpf hcl' hpure =>
        hcont sm hpc hrun (ProcessFieldsPreserved_toHeapVmPreserved hpf) hpf.2.1 hpf.1 hcl' hpure

private theorem hmac_panic_bl6 [HaclPlacement] {P : Program}
    (hP : HaclInProg P haclMpl) (off : Nat) {sym : String} {calleeAddr ret_pc : BitVec 64}
    (hcall : subroutine_ok P calleeAddr rustHandleErrorPanicSpec)
    (hres : libcruxHmacLib.resolve haclMpl sym = calleeAddr)
    (F : SepProp) {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off)
    (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hpre : Pre ⊢ stackFrameAt s.sp 16 ∗ F)
    (hQp : ∀ sf : State, sf.trace = s.trace → Qp sf anyHeap)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ sym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, rustHandleErrorSym, rustUnwrapFailedSym]) :
    SepWPp P ret_pc s Pre Q Qp oom := by
  have hoff' : off < (libcruxHmacLib.blocks[6]'(by decide)).code.length := by
    rw [block6_code_length]; exact hoff
  have hf : (libcruxHmacLib.blockProgram haclMpl 6).fetch s.pc =
      some (.bl ((calleeAddr - haclMpl.base 6) - BitVec.ofNat 64 off)) := by
    rw [hpc]; exact fetch_bl6_of hf_pc6 hres
  have htgt : s.pc + ((calleeAddr - haclMpl.base 6) - BitVec.ofNat 64 off) = calleeAddr := by
    rw [hpc]; exact add_off_rel_target (haclMpl.base 6) calleeAddr (BitVec.ofNat 64 off)
  refine sepWPp_block_bl (i := 6) (by decide) hP hoff' hcall (x := ()) (F := F)
    hcl hpc hrun hsp_align hf htgt
    (fun R hm => by
      dsimp only [rustHandleErrorPanicSpec]
      rw [bl_sp, ← sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hpre) hm)
    (fun R' _ _ _ hex => not_satisfies_false_sepConj (R := R') hex)
    (fun _ _ _ _ _ _ R hm _ => by
      dsimp only [rustHandleErrorPanicSpec] at hm
      rw [sepConj_assoc] at hm
      exact False.elim (not_satisfies_false_sepConj hm))
    (fun R' sf _ hpan => ?_)
    (fun R' _ _ ho => False.elim (not_satisfies_false_sepConj (R := F ∗ R') ho))
  dsimp only [rustHandleErrorPanicSpec] at hpan
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
  rcases hpan with ⟨⟨_, htr⟩, hmem⟩
  rw [bl_trace] at htr
  rw [← sepConj_assoc] at hmem
  exact ⟨anyHeap, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem, hQp sf htr⟩

private theorem hmac_unwrap_panic_wpp [HaclPlacement] {P : Program}
    (hP : HaclInProg P haclMpl) (haux : HmacAuxSubroutines P haclMpl)
    {ret_pc : BitVec 64} {s : State} {Pre Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + 2592#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hpre : Pre ⊢ memRegion (s.sp + 64#64) 32 ∗ (stackAt s.sp 4096 ∗ Rest))
    (hQp : ∀ sf : State, sf.trace = s.trace → Qp sf anyHeap) :
    SepWPp P ret_pc s Pre Q Qp oom := by
  refine sepWPp_seg6 hP hcl (Pre := memRegion (s.sp + 64#64) 32)
    (Post := memRegion (s.sp + 64#64) 32) (Frame := stackAt s.sp 4096 ∗ Rest)
    (PurePost := fun sf => sf.sp = s.sp) hpre
    (fun m => by
      have h := hmac_seg_unwrap_pre (s := s.setMem m) (R := emp)
        (by cases s; exact hpc) (by cases s; exact hrun) (by cases s; exact hsp_align)
      cases s; simpa only [sepConj_emp, State.sp_setMem] using h)
    fun s1 hpc1 hrun1 _ htr1 _ hcl1 hsp1 => ?_
  have hsp_al1 : s1.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp1]
  refine hmac_panic_bl6 hP 2632 haux.unwrapFailed_ok (resolve_unwrapFailed haclMpl)
    (stackAt (s1.sp - 16#64) 4080 ∗ memRegion (s.sp + 64#64) 32 ∗ Rest)
    hcl1 hpc1 hrun1 hsp_al1 ?_ (fun sf htrf => hQp sf (htrf.trans htr1))
  rw [← hsp1, stackAt_4096_split_16 s1.sp]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem call_shim_6 [HaclPlacement] {P : Program}
    (hP : HaclInProg P haclMpl) (haux : HmacAuxSubroutines P haclMpl) (off : Nat)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off)
    (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → VmPreserved s sf → sf.trace = s.trace →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf Pre post)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ rustAllocShimSym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, rustAllocShimSym]) :
    SepWP P target_pc s Pre post := by
  refine sepWP_bl6 hP off haux.shim_ok (resolve_shim haclMpl) () Pre
    hcl hpc hrun hsp_align (Entails.of_eq (emp_sepConj Pre).symm)
    (fun sf hpcsf hrunsf hspsf hsp_alsf hcssf hclsf => ?_) hoff hf_pc6
  dsimp only [rustAllocShimVmSpec]
  refine sepWP_pure_left fun ⟨hacp, hvm⟩ => ?_
  exact hnext sf hpcsf hrunsf hspsf hsp_alsf hcssf
    ((bl_vmPreserved _ s).trans hvm) (hacp.2.1.trans (bl_trace _ s)) hclsf

private theorem call_shim_fs_6 [HaclPlacement] {P : Program}
    (hP : HaclInProg P haclMpl) (haux : HmacValidAuxSubroutines P haclMpl) (off : Nat)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off)
    (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → VmPreserved s sf → sf.trace = s.trace → sf.fs = s.fs →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf Pre post)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ rustAllocShimSym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, rustAllocShimSym]) :
    SepWP P target_pc s Pre post := by
  refine sepWP_bl6 hP off haux.shim_ok (resolve_shim haclMpl) () Pre
    hcl hpc hrun hsp_align (Entails.of_eq (emp_sepConj Pre).symm)
    (fun sf hpcsf hrunsf hspsf hsp_alsf hcssf hclsf => ?_) hoff hf_pc6
  dsimp only [rustAllocShimVmSpec]
  refine sepWP_pure_left fun ⟨hacp, hvm⟩ => ?_
  exact hnext sf hpcsf hrunsf hspsf hsp_alsf hcssf
    ((bl_vmPreserved _ s).trans hvm) (hacp.2.1.trans (bl_trace _ s))
    (hacp.1.trans (bl_fs _ s)) hclsf

private theorem call_allocZeroed64_budget_6 [HaclPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program}
    (hP : HaclInProg P haclMpl) (halloc : HmacBudgetAllocSubroutines M A lim P haclMpl)
    (st : M.σ) (F : SepProp) {target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + 264#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 64#64) (hx1 : s.readReg64 .x1 = 1#64)
    (hFit : FitsEvents M lim st (rustAllocEvents 64 1))
    (hpre : Pre ⊢ A.pool lim st s ∗ stackAt s.sp 4096 ∗ F)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + 268#64 →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.trace = s.trace → sf.fs = s.fs → sf.readReg64 .x0 ≠ 0#64 →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf
        (A.pool lim (M.stepEvents (rustAllocEvents 64 1) st) sf ∗ stackAt s.sp 4096 ∗
         A.live (sf.readReg64 .x0) 64 1 ∗ (sf.readReg64 .x0 ↦ₛ List.replicate 64 0#8) ∗ F) post) :
    SepWP P target_pc s Pre post := by
  let imm := (haclMpl.ρ rustAllocZeroedSym - haclMpl.base 6) - 264#64
  refine sepWP_bl6 hP 264 (subroutine_ok_allocNoOom_of_budgetBase halloc.allocZeroed_ok)
    (resolve_allocZeroed haclMpl) (64, 1, st) F hcl hpc hrun hsp_align ?_
    (fun sf hpcsf hrunsf hspsf hsp_alsf hcssf hclsf => ?_)
  · dsimp only [rustCliAllocNoOomSpecBase]
    have hpure : ((execInst (.bl imm) s).readReg64 .x0).toNat = 64 ∧
        ((execInst (.bl imm) s).readReg64 .x1).toNat = 1 ∧
        RustLayoutOk 64 1 ∧ FitsEvents M lim st (rustAllocEvents 64 1) := by
      simp only [wp_norm, hx0, hx1]
      exact ⟨by decide, by decide, rustLayoutOk_64_1, hFit⟩
    have hpool : A.pool lim st (execInst (.bl imm) s) = A.pool lim st s :=
      A.pool_of_vmPreserved (bl_vmPreserved imm s)
    refine Entails.trans hpre ?_
    rw [← hpool, show stackAt s.sp 4096 = stackAt (execInst (.bl imm) s).sp allocHookStack by
      rw [bl_sp]]
    simp only [sepConj_assoc]
    exact Entails.pure_right hpure (Entails.refl _)
  · dsimp only [rustCliAllocNoOomSpecBase]
    simp only [↓reduceIte, sepConj_assoc]
    refine sepWP_pure_left fun ⟨hacp, hne0, _⟩ => sepWP_congr_pre ?_
      (hnext sf hpcsf hrunsf hspsf hsp_alsf hcssf
        (hacp.2.1.trans (bl_trace imm s)) (hacp.1.trans (bl_fs imm s)) hne0 hclsf)
    rw [bl_sp]; unfold allocHookStack; exact Entails.of_eq (by sep_ac_rfl)

private theorem call_alloc_budget_6 [HaclPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program}
    (hP : HaclInProg P haclMpl) (halloc : HmacBudgetAllocSubroutines M A lim P haclMpl)
    (off size : Nat) (st : M.σ) (F : SepProp) {target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hargs : (s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = 1 ∧ RustLayoutOk size 1)
    (hFit : FitsEvents M lim st (rustAllocEvents size 1))
    (hpre : Pre ⊢ A.pool lim st s ∗ stackAt s.sp 4096 ∗ F)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.trace = s.trace → sf.fs = s.fs → sf.readReg64 .x0 ≠ 0#64 →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf
        (A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sf ∗ stackAt s.sp 4096 ∗
         A.live (sf.readReg64 .x0) size 1 ∗ memRegion (sf.readReg64 .x0) size ∗ F) post)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ rustAllocSym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, rustAllocSym]) :
    SepWP P target_pc s Pre post := by
  let imm := (haclMpl.ρ rustAllocSym - haclMpl.base 6) - BitVec.ofNat 64 off
  refine sepWP_bl6 hP off (subroutine_ok_allocNoOom_of_budgetBase halloc.alloc_ok)
    (resolve_alloc haclMpl) (size, 1, st) F hcl hpc hrun hsp_align ?_
    (fun sf hpcsf hrunsf hspsf hsp_alsf hcssf hclsf => ?_) hoff hf_pc6
  · dsimp only [rustCliAllocNoOomSpecBase]
    have hpure : ((execInst (.bl imm) s).readReg64 .x0).toNat = size ∧
        ((execInst (.bl imm) s).readReg64 .x1).toNat = 1 ∧
        RustLayoutOk size 1 ∧ FitsEvents M lim st (rustAllocEvents size 1) := by
      simp only [wp_norm]; exact ⟨hargs.1, hargs.2.1, hargs.2.2, hFit⟩
    have hpool : A.pool lim st (execInst (.bl imm) s) = A.pool lim st s :=
      A.pool_of_vmPreserved (bl_vmPreserved imm s)
    refine Entails.trans hpre ?_
    rw [← hpool, show stackAt s.sp 4096 = stackAt (execInst (.bl imm) s).sp allocHookStack by
      rw [bl_sp]]
    simp only [sepConj_assoc]
    exact Entails.pure_right hpure (Entails.refl _)
  · dsimp only [rustCliAllocNoOomSpecBase]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine sepWP_pure_left fun ⟨hacp, hne0, _⟩ => sepWP_congr_pre ?_
      (hnext sf hpcsf hrunsf hspsf hsp_alsf hcssf
        (hacp.2.1.trans (bl_trace imm s)) (hacp.1.trans (bl_fs imm s)) hne0 hclsf)
    rw [bl_sp]; unfold allocHookStack; exact Entails.of_eq (by sep_ac_rfl)

private theorem call_dealloc_budget_6 [HaclPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program}
    (hP : HaclInProg P haclMpl) (halloc : HmacBudgetAllocSubroutines M A lim P haclMpl)
    (off : Nat) (p : BitVec 64) (st : M.σ) (F : SepProp)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hargs : s.readReg64 .x0 = p ∧ s.readReg64 .x1 = 64#64 ∧ s.readReg64 .x2 = 1#64)
    (hpre : Pre ⊢ A.pool lim st s ∗ A.live p 64 1 ∗ memRegion p 64 ∗ stackAt s.sp 4096 ∗ F)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.trace = s.trace → sf.fs = s.fs →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf
        (A.pool lim (M.stepEvents (rustDeallocEvents 64 1) st) sf ∗ stackAt s.sp 4096 ∗ F) post)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ rustDeallocSym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, rustDeallocSym]) :
    SepWP P target_pc s Pre post := by
  let imm := (haclMpl.ρ rustDeallocSym - haclMpl.base 6) - BitVec.ofNat 64 off
  refine sepWP_bl6 hP off halloc.dealloc_ok (resolve_dealloc haclMpl) (p, 64, 1, st) F
    hcl hpc hrun hsp_align ?_
    (fun sf hpcsf hrunsf hspsf hsp_alsf hcssf hclsf => ?_) hoff hf_pc6
  · dsimp only [rustCliDeallocBudgetSpecBase]
    have hpure : (execInst (.bl imm) s).readReg64 .x0 = p ∧
        ((execInst (.bl imm) s).readReg64 .x1).toNat = 64 ∧
        ((execInst (.bl imm) s).readReg64 .x2).toNat = 1 := by
      rcases hargs with ⟨hx0, hx1, hx2⟩
      simp only [wp_norm, hx0, hx1, hx2]; exact ⟨trivial, by decide, by decide⟩
    have hpool : A.pool lim st (execInst (.bl imm) s) = A.pool lim st s :=
      A.pool_of_vmPreserved (bl_vmPreserved imm s)
    refine Entails.trans hpre ?_
    rw [← hpool, show stackAt s.sp 4096 = stackAt (execInst (.bl imm) s).sp allocHookStack by
      rw [bl_sp]]
    simp only [sepConj_assoc]
    exact Entails.pure_right hpure (Entails.refl _)
  · dsimp only [rustCliDeallocBudgetSpecBase]
    simp only [sepConj_assoc]
    refine sepWP_pure_left fun ⟨hacp, _⟩ => sepWP_congr_pre ?_
      (hnext sf hpcsf hrunsf hspsf hsp_alsf hcssf
        (hacp.2.1.trans (bl_trace imm s)) (hacp.1.trans (bl_fs imm s)) hclsf)
    rw [bl_sp]; unfold allocHookStack; exact Entails.of_eq (by sep_ac_rfl)

private theorem hmac_budget_tail_wp [HaclPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program}
    (hP : HaclInProg P haclMpl) (haux : HmacValidAuxSubroutines P haclMpl)
    (halloc : HmacBudgetAllocSubroutines M A lim P haclMpl)
    {x : LibcruxHmacCall} {st3 : M.σ} {pKey pIpad pOpad pad152 : BitVec 64}
    {s0 s : State} {Frame : SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + 2140#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64) (hsp_align : s.spAligned = true) (hsp0 : s0.spAligned = true)
    (hregs : s.readReg64 .x19 = x.ret ∧ s.readReg64 .x22 = pKey ∧ s.readReg64 .x23 = pIpad ∧
      s.readReg64 .x24 = pOpad ∧ s.readReg64 .x27 = 32#64 ∧
      s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hf7 : FitsEvents M lim
      (M.stepEvents (rustDeallocEvents 64 1)
        (M.stepEvents (rustDeallocEvents 64 1)
          (M.stepEvents (rustDeallocEvents 64 1) st3)))
      (rustAllocEvents 32 1)) :
    let sp1 := s0.sp - 224#64
    let st6 := M.stepEvents (rustDeallocEvents 64 1)
      (M.stepEvents (rustDeallocEvents 64 1)
        (M.stepEvents (rustDeallocEvents 64 1) st3))
    let st7 := M.stepEvents (rustAllocEvents 32 1) st6
    SepWP P (s0.readReg64 .x30) s
      ((sp1 ↦ₛ hmacWith sha256CompressState x.key x.data) ∗ memRegion (sp1 + 32#64) 32 ∗
       ((sp1 + 64#64) ↦ₛ shaStateBytes (hmacOuterState x.key x.data)) ∗ memRegion (sp1 + 96#64) 32 ∗
       hmacSavedCalleeRegs sp1 s0 pad152 ∗ A.pool lim st3 s ∗
       A.live pKey 64 1 ∗ memRegion pKey 64 ∗ A.live pIpad 64 1 ∗ memRegion pIpad 64 ∗
       A.live pOpad 64 1 ∗ memRegion pOpad 64 ∗ memRegion x.ret 24 ∗ stackAt sp1 4096 ∗ Frame)
      (fun sf P' =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s.trace ∧ sf.fs = s.fs) ∧
        (P' ⊢ stackAt s0.sp 224 ∗ vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
              A.pool lim st7 sf ∗ stackAt sp1 4096 ∗ Frame)) := by
  intro sp1 st6 st7
  rcases hregs with ⟨hx19, hx22, hx23, hx24, hx27, hx28, hvregs⟩
  let st4 := M.stepEvents (rustDeallocEvents 64 1) st3
  let st5 := M.stepEvents (rustDeallocEvents 64 1) st4
  let CoreKeep := (sp1 ↦ₛ hmacWith sha256CompressState x.key x.data) ∗
    memRegion (sp1 + 32#64) 32 ∗ ((sp1 + 64#64) ↦ₛ shaStateBytes (hmacOuterState x.key x.data)) ∗
    memRegion (sp1 + 96#64) 32 ∗ hmacSavedCalleeRegs sp1 s0 pad152 ∗ memRegion x.ret 24
  -- 1. dealloc(pOpad, 64, 1)
  refine sepWP_seg6 hP hcl (Pre := emp) (Post := emp)
    (Frame := CoreKeep ∗ A.pool lim st3 s ∗ A.live pKey 64 1 ∗ memRegion pKey 64 ∗
      A.live pIpad 64 1 ∗ memRegion pIpad 64 ∗ A.live pOpad 64 1 ∗ memRegion pOpad 64 ∗
      stackAt sp1 4096 ∗ Frame)
    (PurePost := fun sf => sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
      sf.readReg64 .x0 = s.readReg64 .x24 ∧ sf.readReg64 .x1 = 64#64 ∧ sf.readReg64 .x2 = 1#64)
    (by rw [emp_sepConj]; exact Entails.of_eq (by dsimp only [CoreKeep]; sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_dealloc_x24 (s := s.setMem m) (R := emp)
        (by cases s; exact hpc) (by cases s; exact hrun)
      cases s; exact h)
    fun s1 hpc1 hrun1 hvm1 htr1 hfs1 hcl1 ⟨hsp1, hcs1, hx0_1, hx1_1, hx2_1⟩ => ?_
  have hsp_al1 : s1.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp1]
  refine call_dealloc_budget_6 hP halloc 2152 pOpad st3
    (CoreKeep ∗ A.live pKey 64 1 ∗ memRegion pKey 64 ∗ A.live pIpad 64 1 ∗ memRegion pIpad 64 ∗ Frame)
    hcl1 hpc1 hrun1 hsp_al1 ⟨hx0_1.trans hx24, hx1_1, hx2_1⟩
    (by rw [emp_sepConj, A.pool_of_vmPreserved hvm1, hsp1, hsp]; exact Entails.of_eq (by sep_ac_rfl))
    fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 htr2 hfs2 hcl2 => ?_
  -- 2. dealloc(pIpad, 64, 1)
  have hcs02 := hcs1.trans hcs2
  refine sepWP_seg6 hP hcl2 (Pre := emp) (Post := emp)
    (Frame := A.pool lim st4 s2 ∗ stackAt s1.sp 4096 ∗ CoreKeep ∗
      A.live pKey 64 1 ∗ memRegion pKey 64 ∗ A.live pIpad 64 1 ∗ memRegion pIpad 64 ∗ Frame)
    (PurePost := fun sf => sf.sp = s2.sp ∧ CalleeSavedPreserved s2 sf ∧
      sf.readReg64 .x0 = s2.readReg64 .x23 ∧ sf.readReg64 .x1 = 64#64 ∧ sf.readReg64 .x2 = 1#64)
    (Entails.of_eq (emp_sepConj _).symm)
    (fun m => by
      have h := hmac_seg_dealloc_x23 (s := s2.setMem m) (R := emp)
        (by cases s2; exact hpc2) (by cases s2; exact hrun2)
      cases s2; exact h)
    fun s3 hpc3 hrun3 hvm3 htr3 hfs3 hcl3 ⟨hsp3, hcs3, hx0_3, hx1_3, hx2_3⟩ => ?_
  have hsp_al3 : s3.spAligned = true := by unfold State.spAligned at hsp_al2 ⊢; rwa [hsp3]
  have hx23_2 : s2.readReg64 .x23 = pIpad := (HmacCoreRegsPreserved.of_csp hcs02).2.2.1.trans hx23
  refine call_dealloc_budget_6 hP halloc 2168 pIpad st4
    (CoreKeep ∗ A.live pKey 64 1 ∗ memRegion pKey 64 ∗ Frame)
    hcl3 hpc3 hrun3 hsp_al3 ⟨hx0_3.trans hx23_2, hx1_3, hx2_3⟩
    (by rw [emp_sepConj, A.pool_of_vmPreserved hvm3, hsp3, hsp2]; exact Entails.of_eq (by sep_ac_rfl))
    fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 htr4 hfs4 hcl4 => ?_
  -- 3. dealloc(pKey, 64, 1)
  have hcs04 := (hcs02.trans hcs3).trans hcs4
  refine sepWP_seg6 hP hcl4 (Pre := emp) (Post := emp)
    (Frame := A.pool lim st5 s4 ∗ stackAt s3.sp 4096 ∗ CoreKeep ∗
      A.live pKey 64 1 ∗ memRegion pKey 64 ∗ Frame)
    (PurePost := fun sf => sf.sp = s4.sp ∧ CalleeSavedPreserved s4 sf ∧
      sf.readReg64 .x0 = s4.readReg64 .x22 ∧ sf.readReg64 .x1 = 64#64 ∧ sf.readReg64 .x2 = 1#64)
    (Entails.of_eq (emp_sepConj _).symm)
    (fun m => by
      have h := hmac_seg_dealloc_x22 (s := s4.setMem m) (R := emp)
        (by cases s4; exact hpc4) (by cases s4; exact hrun4)
      cases s4; exact h)
    fun s5 hpc5 hrun5 hvm5 htr5 hfs5 hcl5 ⟨hsp5, hcs5, hx0_5, hx1_5, hx2_5⟩ => ?_
  have hsp_al5 : s5.spAligned = true := by unfold State.spAligned at hsp_al4 ⊢; rwa [hsp5]
  have hx22_4 : s4.readReg64 .x22 = pKey := (HmacCoreRegsPreserved.of_csp hcs04).2.1.trans hx22
  refine call_dealloc_budget_6 hP halloc 2184 pKey st5 (CoreKeep ∗ Frame)
    hcl5 hpc5 hrun5 hsp_al5 ⟨hx0_5.trans hx22_4, hx1_5, hx2_5⟩
    (by rw [emp_sepConj, A.pool_of_vmPreserved hvm5, hsp5, hsp4]; exact Entails.of_eq (by sep_ac_rfl))
    fun s6 hpc6 hrun6 hsp6 hsp_al6 hcs6 htr6 hfs6 hcl6 => ?_
  -- 4. shim + alloc(32, 1)
  have hcs06 := (hcs04.trans hcs5).trans hcs6
  have hsp6_eq : s6.sp = sp1 := by rw [hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp]
  refine call_shim_fs_6 hP haux 2188 hcl6 hpc6 hrun6 hsp_al6
    fun s7 hpc7 hrun7 hsp7 hsp_al7 hcs7 hvm7 htr7 hfs7 hcl7 => ?_
  refine sepWP_seg6 hP hcl7 (Pre := emp) (Post := emp)
    (Frame := A.pool lim st6 s6 ∗ stackAt s5.sp 4096 ∗ CoreKeep ∗ Frame)
    (PurePost := fun sf => sf.sp = s7.sp ∧ CalleeSavedPreserved s7 sf ∧
      sf.readReg64 .x0 = 32#64 ∧ sf.readReg64 .x1 = 1#64)
    (Entails.of_eq (by rw [emp_sepConj]))
    (fun m => by
      have h := hmac_seg_alloc32_args (s := s7.setMem m) (R := emp)
        (by cases s7; exact hpc7) (by cases s7; exact hrun7)
      cases s7; exact h)
    fun s8 hpc8 hrun8 hvm8 htr8 hfs8 hcl8 ⟨hsp8, hcs8, hx0_8, hx1_8⟩ => ?_
  have hsp_al8 : s8.spAligned = true := by unfold State.spAligned at hsp_al7 ⊢; rwa [hsp8]
  refine call_alloc_budget_6 hP halloc 2200 32 st6 (CoreKeep ∗ Frame)
    hcl8 hpc8 hrun8 hsp_al8
    ⟨by rw [hx0_8]; decide, by rw [hx1_8]; decide, rustLayoutOk_32_1⟩ hf7
    (by
      rw [emp_sepConj, A.pool_of_vmPreserved (hvm7.trans hvm8), hsp8, hsp7, hsp6]
      exact Entails.of_eq (by sep_ac_rfl))
    fun s9 hpc9 hrun9 hsp9 hsp_al9 hcs9 htr9 hfs9 hpOut hcl9 => ?_
  -- 5. tag epilogue (+2204 → ret)
  have hcs09 := ((hcs06.trans hcs7).trans hcs8).trans hcs9
  have hcr09 := HmacCoreRegsPreserved.of_csp hcs09
  have hsp9_eq : s9.sp = sp1 := by rw [hsp9, hsp8, hsp7, hsp6_eq]
  have hsp8_eq : s8.sp = sp1 := by rw [hsp8, hsp7, hsp6_eq]
  let pOut := s9.readReg64 .x0
  refine sepWP_seg6 hP hcl9
    (Pre := (sp1 ↦ₛ hmacWith sha256CompressState x.key x.data) ∗ memRegion (sp1 + 32#64) 32 ∗
      ((sp1 + 64#64) ↦ₛ shaStateBytes (hmacOuterState x.key x.data)) ∗ memRegion (sp1 + 96#64) 32 ∗
      hmacSavedCalleeRegs sp1 s0 pad152 ∗ A.repAlloc.live pOut 32 1 ∗ memRegion pOut 32 ∗
      memRegion x.ret 24)
    (Post := stackAt s0.sp 224 ∗ vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data))
    (Frame := A.pool lim st7 s9 ∗ stackAt sp1 4096 ∗ Frame)
    (PurePost := fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (by
      rw [A.repAlloc_live, hsp8_eq]
      exact Entails.of_eq (by dsimp only [CoreKeep, pOut, st7]; sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_tag_epilogue (A := A.repAlloc) (s0 := s0) (s := s9.setMem m)
        (ret := x.ret) (pOut := pOut) (pad152 := pad152) (R := emp)
        (hmacWith_sha256_length x.key x.data)
        (shaStateBytes_length (hmacOuterState x.key x.data))
        (by cases s9; exact hpc9) (by cases s9; exact hrun9)
        (by cases s9; exact hsp9_eq) hsp0
        (by cases s9; rfl) hpOut
        (by cases s9; exact hcr09.1.trans hx19)
        (by cases s9; exact hcr09.2.2.2.2.1.trans hx27)
        (by cases s9; exact hcr09.2.2.2.2.2.1.trans hx28)
        (by cases s9; exact hcr09.2.2.2.2.2.2.trans hvregs)
      cases s9; simpa only [sepConj_emp] using h)
    fun sf hpcf hrunf hvmf htrf hfsf _ ⟨hspf, hcsf⟩ => ?_
  refine SepWP.done hpcf hrunf ⟨⟨hspf, hcsf, ?_, ?_⟩, ?_⟩
  · rw [htrf, htr9, htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1]
  · rw [hfsf, hfs9, hfs8, hfs7, hfs6, hfs5, hfs4, hfs3, hfs2, hfs1]
  · rw [A.pool_of_vmPreserved hvmf]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem sepWP_seq {P : Program} {mid target : BitVec 64} {s : State}
    {FullPre Pre Post Frame : SepProp} {PurePost : State → Prop}
    {post : State → SepProp → Prop}
    (hsplit : FullPre ⊢ Pre ∗ Frame)
    (hwp : SepWP P mid s Pre (fun sm Pm => PurePost sm ∧ (Pm ⊢ Post)))
    (hcont : ∀ sm : State, sm.pc = mid → sm.status = .Running → PurePost sm →
      SepWP P target sm (Post ∗ Frame) post) :
    SepWP P target s FullPre post := by
  unfold SepWP reaches_pc; intro R hm hLP
  have hm' : s.mem ⊨ Pre ∗ (Frame ∗ R) := by
    rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hsplit) hm
  obtain ⟨sm, hsteps1, ⟨hpc, hrun, Pm, hmm, hpure, hent⟩ | ⟨_, hoom1⟩⟩ := hwp.elim hm' hLP
  · have hmm' : sm.mem ⊨ (Post ∗ Frame) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps2, hout2⟩ :=
      (hcont sm hpc hrun hpure).elim hmm' (hsteps1.codeLoaded hLP)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom1)

private theorem sepWP_seq_dep {P : Program} {mid target : BitVec 64} {s : State}
    {FullPre Pre Frame : SepProp} {Post : State → SepProp} {PurePost : State → Prop}
    {post : State → SepProp → Prop}
    (hsplit : FullPre ⊢ Pre ∗ Frame)
    (hwp : SepWP P mid s Pre (fun sm Pm => PurePost sm ∧ (Pm ⊢ Post sm)))
    (hcont : ∀ sm : State, sm.pc = mid → sm.status = .Running → PurePost sm →
      SepWP P target sm (Post sm ∗ Frame) post) :
    SepWP P target s FullPre post := by
  unfold SepWP reaches_pc; intro R hm hLP
  have hm' : s.mem ⊨ Pre ∗ (Frame ∗ R) := by
    rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hsplit) hm
  obtain ⟨sm, hsteps1, ⟨hpc, hrun, Pm, hmm, hpure, hent⟩ | ⟨_, hoom1⟩⟩ := hwp.elim hm' hLP
  · have hmm' : sm.mem ⊨ (Post sm ∗ Frame) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps2, hout2⟩ :=
      (hcont sm hpc hrun hpure).elim hmm' (hsteps1.codeLoaded hLP)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom1)

private theorem calleeSavedPreserved_write_setMem (s : State) (m : Memory)
    (pIpad : BitVec 64) (sf : State) :
    CalleeSavedPreserved
      (((s.setMem m).writeReg64 .x23 pIpad).writeReg64 .x26 ((s.setMem m).readReg64 .x26 >>> 32))
      sf ↔
    CalleeSavedPreserved
      ((s.writeReg64 .x23 pIpad).writeReg64 .x26 (s.readReg64 .x26 >>> 32)) sf := by
  simp only [CalleeSavedPreserved.iff_regs, wp_norm, calleeSavedVRegs]

private theorem calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := by
  simp only [calleeSavedVRegs, wp_norm]

private theorem hmac_budget_valid_wp [HaclPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program}
    (hP : HaclInProg P haclMpl) (hsubs : HaclSubroutinesTrace P haclMpl)
    (haux : HmacValidAuxSubroutines P haclMpl)
    (halloc : HmacBudgetAllocSubroutines M A lim P haclMpl)
    {x : LibcruxHmacCall} {st : M.σ} {keyLenBV dataLenBV pad152 : BitVec 64}
    {s0 s1 : State} {Frame : SepProp}
    (hk32 : x.key.length < 2 ^ 32) (hd32 : x.data.length < 2 ^ 32)
    (hk_nat : keyLenBV.toNat = x.key.length) (hd_nat : dataLenBV.toNat = x.data.length)
    (hEnv : FitsEnv M lim st (LibcruxHmacEnv x))
    (hcl1 : libcruxHmacLib.CodeLoaded haclMpl s1.mem)
    (hpc1 : s1.pc = haclMpl.base 6 + 252#64) (hrun1 : s1.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp1 : s1.sp = s0.sp - 224#64)
    (hregs1 : s1.readReg64 .x19 = x.ret ∧ s1.readReg64 .x20 = x.dataA ∧
      s1.readReg64 .x21 = dataLenBV ∧ s1.readReg64 .x23 = keyLenBV ∧
      s1.readReg64 .x24 = x.keyA ∧ s1.readReg64 .x25 = tryFromKeyNiche keyLenBV ∧
      s1.readReg64 .x26 = tryFromDataNiche dataLenBV ∧ s1.readReg64 .x27 = 32#64 ∧
      s1.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    let sp1 := s0.sp - 224#64
    SepWP P (s0.readReg64 .x30) s1
      ((sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
       memRegion (sp1 + 64#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
       hmacSavedCalleeRegs sp1 s0 pad152 ∗
       (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
       A.pool lim st s1 ∗ stackAt sp1 4096 ∗ Frame)
      (fun sf P' =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s1.trace ∧ sf.fs = s1.fs) ∧
        (P' ⊢ (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
              vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
              A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗
              stackAt s0.sp 224 ∗ stackAt sp1 4096 ∗ Frame)) := by
  intro sp1
  rcases hregs1 with ⟨hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hv_1⟩
  have hd_bv : dataLenBV = BitVec.ofNat 64 x.data.length := by
    apply BitVec.eq_of_toNat_eq; rw [hd_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsp_al1 : s1.spAligned = true := by
    unfold State.spAligned; rw [hsp1]; exact State.spAligned_sub s0 224#64 hsp0
  rcases fitsEvents_hmacSha256_split hEnv hk32 hd32 with ⟨hf1, hf2, hf3, hf7, hst_eq⟩
  let st1 := M.stepEvents (rustAllocEvents 64 1) st
  let st2 := M.stepEvents (rustAllocEvents 64 1) st1
  let st3 := M.stepEvents (rustAllocEvents 64 1) st2
  let k0 := libcruxHmacKeyBlock sha256CompressState x.key
  have hk0 : k0.length = 64 := libcruxHmacKeyBlock_length sha256CompressState x.key
  let Locals := memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
    hmacSavedCalleeRegs sp1 s0 pad152 ∗ memRegion x.ret 24
  -- 1. shim + allocZeroed(64, 1) -> pKey
  refine call_shim_fs_6 hP haux 252 hcl1 hpc1 hrun1 hsp_al1
    fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hvm2 htr2 hfs2 hcl2 => ?_
  refine sepWP_seg6 hP hcl2 (Pre := emp) (Post := emp)
    (Frame := (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 64#64) 32 ∗ Locals ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ A.pool lim st s1 ∗ stackAt sp1 4096 ∗ Frame)
    (PurePost := fun sf => sf.sp = s2.sp ∧ CalleeSavedPreserved s2 sf ∧
      sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 1#64)
    (by rw [emp_sepConj]; exact Entails.of_eq (by dsimp only [Locals]; sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_alloc64_args_key (s := s2.setMem m) (R := emp)
        (by cases s2; exact hpc2) (by cases s2; exact hrun2)
      cases s2; exact h)
    fun s3 hpc3 hrun3 hvm3 htr3 hfs3 hcl3 ⟨hsp3, hcs3, hx0_3, hx1_3⟩ => ?_
  have hsp_al3 : s3.spAligned = true := by unfold State.spAligned at hsp_al2 ⊢; rwa [hsp3]
  have hsp3_eq : s3.sp = sp1 := by rw [hsp3, hsp2, hsp1]
  refine call_allocZeroed64_budget_6 hP halloc st
    ((sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 64#64) 32 ∗ Locals ∗
     (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl3 hpc3 hrun3 hsp_al3 hx0_3 hx1_3 hf1
    (by
      rw [emp_sepConj, A.pool_of_vmPreserved (hvm2.trans hvm3), hsp3_eq]
      exact Entails.of_eq (by sep_ac_rfl))
    fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 htr4 hfs4 hpKey hcl4 => ?_
  -- 2. hmac_key_prep_wp (+268 -> +912)
  let pKey := s4.readReg64 .x0
  have hcs14 := (hcs2.trans hcs3).trans hcs4
  rcases (CalleeSavedPreserved.iff_regs s1 s4).mp hcs14 with
    ⟨hx19_4, hx20_4, hx21_4, _, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _, hv_4⟩
  have hsp4_eq : s4.sp = sp1 := hsp4.trans hsp3_eq
  refine sepWP_seq
    (Frame := A.pool lim st1 s4 ∗ A.live pKey 64 1 ∗ (sp1 ↦ₛ List.replicate 32 0#8) ∗
      memRegion (sp1 + 64#64) 32 ∗ Locals ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    (by rw [hsp4_eq, hsp3_eq]; exact Entails.of_eq (by dsimp only [pKey, st1]; sep_ac_rfl))
    (hmac_key_prep_wp hP hsubs haux (Frame := emp) hcl4 hpc4 hrun4 hsp_al4 rfl hpKey
      (hx23_4.trans hx23_1) (hx24_4.trans hx24_1) (hx25_4.trans hx25_1) hk_nat hk32)
    fun s5 hpc5 hrun5 ⟨hsp5, hsp_al5, hcs5, hvm5, htr5, hfs5, hcl5⟩ => ?_
  rcases (CalleeSavedPreserved.iff_regs (s4.writeReg64 .x22 pKey) s5).mp hcs5 with
    ⟨hx19_5, hx20_5, hx21_5, hx22_5, _, _, _, hx26_5, hx27_5, hx28_5, _, hv_5⟩
  simp only [wp_norm] at hx19_5 hx20_5 hx21_5 hx22_5 hx26_5 hx27_5 hx28_5
  rw [calleeSavedVRegs_writeReg64] at hv_5
  have hsp5_eq : s5.sp = sp1 := hsp5.trans hsp4_eq
  -- 3. shim + alloc(64, 1) -> pIpad
  refine call_shim_fs_6 hP haux 912 hcl5 hpc5 hrun5 hsp_al5
    fun s6 hpc6 hrun6 hsp6 hsp_al6 hcs6 hvm6 htr6 hfs6 hcl6 => ?_
  refine sepWP_seg6 hP hcl6 (Pre := emp) (Post := emp)
    (Frame := ((pKey ↦ₛ k0) ∗ (x.keyA ↦ₛ x.key) ∗ stackAt s4.sp 4096 ∗ emp) ∗
      A.pool lim st1 s4 ∗ A.live pKey 64 1 ∗ (sp1 ↦ₛ List.replicate 32 0#8) ∗
      memRegion (sp1 + 64#64) 32 ∗ Locals ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    (PurePost := fun sf => sf.sp = s6.sp ∧ CalleeSavedPreserved s6 sf ∧
      sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 1#64)
    (Entails.of_eq (by rw [emp_sepConj]))
    (fun m => by
      have h := hmac_seg_alloc64_args_ipad (s := s6.setMem m) (R := emp)
        (by cases s6; exact hpc6) (by cases s6; exact hrun6)
      cases s6; exact h)
    fun s7 hpc7 hrun7 hvm7 htr7 hfs7 hcl7 ⟨hsp7, hcs7, hx0_7, hx1_7⟩ => ?_
  have hsp_al7 : s7.spAligned = true := by unfold State.spAligned at hsp_al6 ⊢; rwa [hsp7]
  have hsp7_eq : s7.sp = sp1 := by rw [hsp7, hsp6, hsp5_eq]
  refine call_alloc_budget_6 hP halloc 924 64 st1
    ((pKey ↦ₛ k0) ∗ A.live pKey 64 1 ∗ (sp1 ↦ₛ List.replicate 32 0#8) ∗
     memRegion (sp1 + 64#64) 32 ∗ Locals ∗ (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl7 hpc7 hrun7 hsp_al7
    ⟨by rw [hx0_7]; decide, by rw [hx1_7]; decide, rustLayoutOk_64_1⟩ hf2
    (by
      rw [emp_sepConj, sepConj_emp, A.pool_of_vmPreserved ((hvm5.trans hvm6).trans hvm7),
          hsp4_eq, hsp7_eq]
      exact Entails.of_eq (by sep_ac_rfl))
    fun s8 hpc8 hrun8 hsp8 hsp_al8 hcs8 htr8 hfs8 hpIpad hcl8 => ?_
  -- 4. hmac_seg_ipad_xor (+928 -> +988)
  let pIpad := s8.readReg64 .x0
  have hcs58 := (hcs6.trans hcs7).trans hcs8
  rcases (CalleeSavedPreserved.iff_regs s5 s8).mp hcs58 with
    ⟨hx19_8, hx20_8, hx21_8, hx22_8, _, _, _, hx26_8, hx27_8, hx28_8, _, hv_8⟩
  have hsp8_eq : s8.sp = sp1 := hsp8.trans hsp7_eq
  refine sepWP_seg6 hP hcl8
    (Pre := (pKey ↦ₛ k0) ∗ memRegion pIpad 64)
    (Post := (pKey ↦ₛ k0) ∗ (pIpad ↦ₛ k0.map (· ^^^ 0x36#8)))
    (Frame := A.pool lim st2 s8 ∗ stackAt sp1 4096 ∗ A.live pKey 64 1 ∗ A.live pIpad 64 1 ∗
      (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 64#64) 32 ∗ Locals ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    (PurePost := fun sf => sf.sp = s8.sp ∧
      CalleeSavedPreserved ((s8.writeReg64 .x23 pIpad).writeReg64 .x26 (s8.readReg64 .x26 >>> 32)) sf)
    (by rw [hsp7_eq]; exact Entails.of_eq (by dsimp only [pIpad, st2]; sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_ipad_xor (pKey := pKey) (pIpad := pIpad) (k0 := k0)
        (s := s8.setMem m) (R := emp) hk0
        (by cases s8; exact hpc8) (by cases s8; exact hrun8)
        (by cases s8; rfl) hpIpad (by cases s8; exact hx22_8.trans hx22_5)
      simpa only [sepConj_emp, State.sp_setMem, calleeSavedPreserved_write_setMem] using h)
    fun s9 hpc9 hrun9 hvm9 htr9 hfs9 hcl9 ⟨hsp9, hcs9⟩ => ?_
  have hsp_al9 : s9.spAligned = true := by unfold State.spAligned at hsp_al8 ⊢; rwa [hsp9]
  have hsp9_eq : s9.sp = sp1 := hsp9.trans hsp8_eq
  rcases (CalleeSavedPreserved.iff_regs
      ((s8.writeReg64 .x23 pIpad).writeReg64 .x26 (s8.readReg64 .x26 >>> 32)) s9).mp hcs9 with
    ⟨hx19_9, hx20_9, hx21_9, hx22_9, hx23_9, _, _, hx26_9, hx27_9, hx28_9, _, hv_9⟩
  simp only [wp_norm] at hx19_9 hx20_9 hx21_9 hx22_9 hx23_9 hx26_9 hx27_9 hx28_9
  rw [calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg64] at hv_9
  have hx26_9_eq : s9.readReg64 .x26 = BitVec.ofNat 64 x.data.length := by
    rw [hx26_9, hx26_8, hx26_5, hx26_4, hx26_1,
        tryFromDataNiche_lsr32 dataLenBV (by omega), hd_bv]
  -- 5. shim + alloc(64, 1) -> pOpad
  refine call_shim_fs_6 hP haux 988 hcl9 hpc9 hrun9 hsp_al9
    fun s10 hpc10 hrun10 hsp10 hsp_al10 hcs10 hvm10 htr10 hfs10 hcl10 => ?_
  refine sepWP_seg6 hP hcl10 (Pre := emp) (Post := emp)
    (Frame := ((pKey ↦ₛ k0) ∗ (pIpad ↦ₛ k0.map (· ^^^ 0x36#8))) ∗
      A.pool lim st2 s8 ∗ stackAt sp1 4096 ∗ A.live pKey 64 1 ∗ A.live pIpad 64 1 ∗
      (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 64#64) 32 ∗ Locals ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    (PurePost := fun sf => sf.sp = s10.sp ∧ CalleeSavedPreserved s10 sf ∧
      sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 1#64)
    (Entails.of_eq (by rw [emp_sepConj]))
    (fun m => by
      have h := hmac_seg_alloc64_args_opad (s := s10.setMem m) (R := emp)
        (by cases s10; exact hpc10) (by cases s10; exact hrun10)
      cases s10; exact h)
    fun s11 hpc11 hrun11 hvm11 htr11 hfs11 hcl11 ⟨hsp11, hcs11, hx0_11, hx1_11⟩ => ?_
  have hsp_al11 : s11.spAligned = true := by unfold State.spAligned at hsp_al10 ⊢; rwa [hsp11]
  have hsp11_eq : s11.sp = sp1 := by rw [hsp11, hsp10, hsp9_eq]
  refine call_alloc_budget_6 hP halloc 1000 64 st2
    ((pKey ↦ₛ k0) ∗ (pIpad ↦ₛ k0.map (· ^^^ 0x36#8)) ∗ A.live pKey 64 1 ∗ A.live pIpad 64 1 ∗
     (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 64#64) 32 ∗ Locals ∗
     (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl11 hpc11 hrun11 hsp_al11
    ⟨by rw [hx0_11]; decide, by rw [hx1_11]; decide, rustLayoutOk_64_1⟩ hf3
    (by
      rw [emp_sepConj, A.pool_of_vmPreserved ((hvm9.trans hvm10).trans hvm11), hsp11_eq]
      exact Entails.of_eq (by sep_ac_rfl))
    fun s12 hpc12 hrun12 hsp12 hsp_al12 hcs12 htr12 hfs12 hpOpad hcl12 => ?_
  -- 6. hmac_core_1004_to_2140_wp (+1004 -> +2140)
  let pOpad := s12.readReg64 .x0
  have hcs912 := (hcs10.trans hcs11).trans hcs12
  rcases (CalleeSavedPreserved.iff_regs s9 s12).mp hcs912 with
    ⟨hx19_12, hx20_12, hx21_12, hx22_12, hx23_12, _, _, hx26_12, hx27_12, hx28_12, _, hv_12⟩
  have hsp12_eq : s12.sp = sp1 := hsp12.trans hsp11_eq
  refine sepWP_seq
    (Frame := A.pool lim st3 s12 ∗ A.live pKey 64 1 ∗ A.live pIpad 64 1 ∗ A.live pOpad 64 1 ∗
      Locals ∗ (x.keyA ↦ₛ x.key) ∗ Frame)
    (by rw [hsp12_eq, hsp11_eq]; exact Entails.of_eq (by dsimp only [pOpad, st3, k0]; sep_ac_rfl))
    (hmac_core_1004_to_2140_wp hP hsubs (Frame := emp) hd32 hcl12 hpc12 hrun12 hsp_al12 rfl hpOpad
      (by rw [hx20_12, hx20_9, hx20_8, hx20_5, hx20_4, hx20_1])
      (by rw [hx21_12, hx21_9, hx21_8, hx21_5, hx21_4, hx21_1, hd_bv])
      (by rw [hx22_12, hx22_9, hx22_8, hx22_5])
      (by rw [hx23_12, hx23_9])
      (hx26_12.trans hx26_9_eq))
    fun s13 hpc13 hrun13 ⟨hsp13, hsp_al13, hcr13, hvm13, htr13, hfs13, hcl13⟩ => ?_
  -- 7. hmac_budget_tail_wp (+2140 -> ret)
  have hsp13_eq : s13.sp = sp1 := hsp13.trans hsp12_eq
  rcases hcr13 with ⟨hcr19, hcr22, hcr23, hcr24, hcr27, hcr28, hcrv⟩
  simp only [wp_norm] at hcr19 hcr22 hcr23 hcr24 hcr27 hcr28
  rw [calleeSavedVRegs_writeReg64] at hcrv
  let st7 := M.stepEvents (rustAllocEvents 32 1)
    (M.stepEvents (rustDeallocEvents 64 1)
      (M.stepEvents (rustDeallocEvents 64 1)
        (M.stepEvents (rustDeallocEvents 64 1) st3)))
  refine sepWP_seq_dep (mid := s0.readReg64 .x30)
    (Frame := (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    (Pre := (sp1 ↦ₛ hmacWith sha256CompressState x.key x.data) ∗ memRegion (sp1 + 32#64) 32 ∗
      ((sp1 + 64#64) ↦ₛ shaStateBytes (hmacOuterState x.key x.data)) ∗ memRegion (sp1 + 96#64) 32 ∗
      hmacSavedCalleeRegs sp1 s0 pad152 ∗ A.pool lim st3 s13 ∗
      A.live pKey 64 1 ∗ memRegion pKey 64 ∗ A.live pIpad 64 1 ∗ memRegion pIpad 64 ∗
      A.live pOpad 64 1 ∗ memRegion pOpad 64 ∗ memRegion x.ret 24 ∗ stackAt sp1 4096 ∗ emp)
    (Post := fun sf => stackAt s0.sp 224 ∗
      vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
      A.pool lim st7 sf ∗ stackAt sp1 4096 ∗ emp)
    (PurePost := fun sf =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s13.trace ∧ sf.fs = s13.fs)
    (by
      rw [sepConj_emp, A.pool_of_vmPreserved hvm13, hsp12_eq]
      exact Entails.of_eq (by dsimp only [Locals]; sep_ac_rfl))
    (hmac_budget_tail_wp hP haux halloc (x := x) (st3 := st3)
      (pKey := pKey) (pIpad := pIpad) (pOpad := pOpad) (pad152 := pad152)
      (s0 := s0) (Frame := emp)
      hcl13 hpc13 hrun13 hsp13_eq hsp_al13 hsp0
      ⟨by rw [hcr19, hx19_12, hx19_9, hx19_8, hx19_5, hx19_4, hx19_1],
       by rw [hcr22, hx22_12, hx22_9, hx22_8, hx22_5],
       by rw [hcr23, hx23_12, hx23_9],
       hcr24,
       by rw [hcr27, hx27_12, hx27_9, hx27_8, hx27_5, hx27_4, hx27_1],
       by rw [hcr28, hx28_12, hx28_9, hx28_8, hx28_5, hx28_4, hx28_1],
       by rw [hcrv, hv_12, hv_9, hv_8, hv_5, hv_4, hv_1]⟩
      hf7)
    fun sf hpcf hrunf ⟨hspf, hcsf, htr14, hfs14⟩ => ?_
  refine SepWP.done hpcf hrunf ⟨⟨hspf, hcsf, ?_, ?_⟩, ?_⟩
  · rw [htr14, htr13, htr12, htr11, htr10, htr9, htr8, htr7, htr6, htr5, htr4, htr3, htr2]
  · rw [hfs14, hfs13, hfs12, hfs11, hfs10, hfs9, hfs8, hfs7, hfs6, hfs5, hfs4, hfs3, hfs2]
  · dsimp only [st7, st3, st2, st1]
    rw [sepConj_emp, hst_eq]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Ambient-program `subroutine_ok` for Block `6` (`libcrux_hmac::hmac`, `w0 = 0` SHA-256)
discharging `withHaclCodeLoaded mpl (libcruxHmacBudgetSpec sha256CompressState M A lim)`. -/
theorem libcruxHmac_budget_withHaclCodeLoaded_subroutineOk
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hsubs : HaclSubroutinesTrace P mpl)
    (haux : HmacAuxSubroutines P mpl)
    (halloc : HmacBudgetAllocSubroutines M A lim P mpl) :
    subroutine_ok P (mpl.base 6)
      (withHaclCodeLoaded mpl (libcruxHmacBudgetSpec sha256CompressState M A lim)) := by
  let _ : HaclPlacement := ⟨mpl, hP.placeable⟩
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st⟩ R s0 hpc0 hrun0 hpre0 hsp0
  dsimp only [withHaclCodeLoaded, libcruxHmacBudgetSpec] at hpre0
  simp only [sepConj_assoc] at hpre0
  rw [satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨hcl0, hpre0⟩
  rw [satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8, hw0, hx1, hx2, hx3, hx4, hw5, hx6, hEnv⟩, hm0⟩
  refine ⟨(x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
    A.pool lim st s0 ∗ stackAt s0.sp extHookStack, R,
    by simpa only [sepConj_assoc] using hm0, ?_⟩
  let sp1 := s0.sp - 224#64
  refine sepWPp_seg6 hP hcl0
    (mid := if 2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat then
      mpl.base 6 + 2592#64 else mpl.base 6 + 252#64)
    (Pre := stackAt s0.sp 224)
    (Post := hmacPrologueSpatial s0)
    (Frame := (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
      A.pool lim st s0 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
    (PurePost := hmacProloguePure s0)
    (by
      unfold extHookStack; dsimp only [Nat.reducePow]
      rw [stackAt_split_hmac s0.sp]
      exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_prologue (s0 := s0.setMem m)
        (by cases s0; exact hpc0) (by cases s0; exact hrun0) (by cases s0; exact hsp0)
        (by cases s0; exact hw0) (by cases s0; exact hw5) (by cases s0; exact hx6)
      cases s0; exact h)
    fun s1 hpc1 hrun1 hvm1 htr1 _ hcl1 hpure1 => ?_
  by_cases hovf : 2 ^ 32 ≤ x.key.length ∨ 2 ^ 32 ≤ x.data.length
  · have hcond : 2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat := by
      rwa [hx2, hx4]
    simp only [hcond, ↓reduceIte] at hpc1
    have hsp1 : s1.sp = sp1 := hpure1.1
    have hsp_al1 : s1.spAligned = true := by
      unfold State.spAligned; rw [hsp1]; exact State.spAligned_sub s0 224#64 hsp0
    refine hmac_unwrap_panic_wpp hP haux hcl1 hpc1 hrun1 hsp_al1
      (Rest := (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
        memRegion (sp1 + 96#64) 32 ∗ (∃∗ p, hmacSavedCalleeRegs sp1 s0 p) ∗
        (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 4320#64) 12064)
      (by
        dsimp only [hmacPrologueSpatial]
        rw [hsp1]
        exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
      fun sf htrf hmR => ?_
    dsimp only [withHaclCodeLoaded, libcruxHmacBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hovf, by rw [htrf, htr1]⟩, hmR⟩
  · have hk32 : x.key.length < 2 ^ 32 := by omega
    have hd32 : x.data.length < 2 ^ 32 := by omega
    have hcond : ¬(2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat) := by
      rw [hx2, hx4]; exact hovf
    simp only [hcond, ↓reduceIte] at hpc1
    rcases hpure1 with ⟨hsp1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1,
      hx27_1, hx28_1, hv_1, hx26_fn⟩
    have hx26_1 : s1.readReg64 .x26 = tryFromDataNiche (s0.readReg64 .x4) :=
      hx26_fn (hx2.symm ▸ hk32) (hx4.symm ▸ hd32)
    refine sepWPp_congr_pre
      (P2 := (∃∗ pad152 : BitVec 64, hmacSavedCalleeRegs sp1 s0 pad152) ∗
        ((sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
         memRegion (sp1 + 64#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
         (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
         A.pool lim st s1 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064))
      (by
        dsimp only [hmacPrologueSpatial]
        rw [A.pool_of_vmPreserved hvm1]
        exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl)) ?_
    refine sepWPp_exists_elim fun pad152 => ?_
    refine sepWPp_of_sepWP_dep (mid := s0.readReg64 .x30) (Frame := emp)
      (Pre := (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
        memRegion (sp1 + 64#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
        hmacSavedCalleeRegs sp1 s0 pad152 ∗
        (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
        A.pool lim st s1 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
      (PurePost := fun sf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s1.trace ∧ sf.fs = s1.fs)
      (Post := fun sf => (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
        vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
        A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗
        stackAt s0.sp 224 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
      (by rw [sepConj_emp]; exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
      (hmac_budget_valid_wp hP hsubs (hmacAux_toValid haux) halloc (s0 := s0) (pad152 := pad152)
        (Frame := stackAt (s0.sp - 4320#64) 12064)
        hk32 hd32 hx2 hx4 hEnv hcl1 hpc1 hrun1 hsp0 hsp1
        ⟨hx19_1.trans hx8, hx20_1.trans hx3, hx21_1, hx23_1, hx24_1.trans hx1,
         hx25_1, hx26_1, hx27_1, hx28_1, hv_1⟩)
      fun sf hpcf hrunf ⟨hspf, hcsf, htr_val, _⟩ => ?_
    refine sepWPp_done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
    dsimp only [withHaclCodeLoaded, libcruxHmacBudgetSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨libcruxHmacSha256Events, ?_⟩
    have hpost_ent :
        (((x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
          vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
          A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗
          stackAt s0.sp 224 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064) ∗ emp) ⊢
        (⌜x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
          sf.trace = s0.trace ∧ LibcruxHmacEnv x libcruxHmacSha256Events⌝ ∗
         (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
         vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
         A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗
         stackAt s0.sp extHookStack) := by
      have hpure_f : x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
          sf.trace = s0.trace ∧ LibcruxHmacEnv x libcruxHmacSha256Events :=
        ⟨hk32, hd32, htr_val.trans htr1, by unfold LibcruxHmacEnv; split <;> [rfl; omega]⟩
      rw [sepConj_emp]
      refine Entails.trans (Entails.of_eq ?_) (Entails.pure_right hpure_f (Entails.refl _))
      unfold extHookStack; dsimp only [Nat.reducePow]
      rw [stackAt_split_hmac s0.sp]
    exact Satisfies.mono (sepConj_mono_left hpost_ent) hmf

/-- Ambient-program `subroutine_ok` for Block `6` (`libcrux_hmac::hmac`, `w0 = 0` SHA-256)
discharging `libcruxHmacBudgetSpec sha256CompressState M A lim` when `P.CodeLoaded` implies
`libcruxHmacLib.CodeLoaded mpl`. -/
theorem libcruxHmac_budget_subroutineOk
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hCL : ∀ m : Memory, P.CodeLoaded m → libcruxHmacLib.CodeLoaded mpl m)
    (hsubs : HaclSubroutinesTrace P mpl)
    (haux : HmacAuxSubroutines P mpl)
    (halloc : HmacBudgetAllocSubroutines M A lim P mpl) :
    subroutine_ok P (mpl.base 6) (libcruxHmacBudgetSpec sha256CompressState M A lim) :=
  subroutine_ok_of_withHaclCodeLoaded hCL
    (libcruxHmac_budget_withHaclCodeLoaded_subroutineOk hP hsubs haux halloc)

/-- Strengthen `spec.post` and `spec.onPanic` with `⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝`
(with `onExit = False` and `onOom = False`), keeping `spec.pre` definitionally (`rfl`) unchanged. -/
@[expose] def withFsTraceBudget {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    post := fun x s0 sf => ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ spec.post x s0 sf
    onPanic := fun x s0 sf => ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ spec.onPanic x s0 sf
    onExit := fun _ _ _ _ => ⌜False⌝
    onOom := fun _ _ _ => ⌜False⌝ }

private theorem hmac_unwrap_panic_ext_wpp [HaclPlacement] {P : Program}
    (hP : HaclInProg P haclMpl)
    (hext_uf : P.externAt? (haclMpl.ρ rustUnwrapFailedSym) = some Rust.panicked)
    {ret_pc : BitVec 64} {s : State} {Pre Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + 2592#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hpre : Pre ⊢ memRegion (s.sp + 64#64) 32 ∗ (stackAt s.sp 4096 ∗ Rest))
    (hQp : ∀ sf : State, ∀ P' : SepProp, sf.trace = s.trace → sf.fs = s.fs → Qp sf P') :
    SepWPp P ret_pc s Pre Q Qp oom := by
  refine sepWPp_seg6 hP hcl (Pre := memRegion (s.sp + 64#64) 32)
    (Post := memRegion (s.sp + 64#64) 32) (Frame := stackAt s.sp 4096 ∗ Rest)
    (PurePost := fun sf => sf.sp = s.sp) hpre
    (fun m => by
      have h := hmac_seg_unwrap_pre (s := s.setMem m) (R := emp)
        (by cases s; exact hpc) (by cases s; exact hrun) (by cases s; exact hsp_align)
      cases s; simpa only [sepConj_emp, State.sp_setMem] using h)
    fun s1 hpc1 hrun1 _ htr1 hfs1 hcl1 _ => ?_
  have hoff' : 2632 < (libcruxHmacLib.blocks[6]'(by decide)).code.length := by
    rw [block6_code_length]; decide
  have hf : (libcruxHmacLib.blockProgram haclMpl 6).fetch s1.pc =
      some (.bl ((haclMpl.ρ rustUnwrapFailedSym - haclMpl.base 6) - 2632#64)) := by
    rw [hpc1]
    exact fetch_bl6_of (by simp [wp_norm, rustUnwrapFailedSym]) (resolve_unwrapFailed haclMpl)
  have htgt : s1.pc + ((haclMpl.ρ rustUnwrapFailedSym - haclMpl.base 6) - 2632#64) =
      haclMpl.ρ rustUnwrapFailedSym := by
    rw [hpc1]; exact add_off_rel_target (haclMpl.base 6) _ 2632#64
  refine sepWPp_block_bl_panic (i := 6) (by decide) hP hoff' hcl1 hpc1 hrun1 hf htgt hext_uf ?_
  refine hQp _ _ ?_ ?_
  · exact (by cases s1; rfl : (Rust.panicked _).trace = s1.trace).trans htr1
  · exact (by cases s1; rfl : (Rust.panicked _).fs = s1.fs).trans hfs1

/-- Ambient-program `subroutine_ok` for Block `6` (`libcrux_hmac::hmac`, `w0 = 0` SHA-256)
discharging `withHaclCodeLoaded mpl (withFsTraceBudget (libcruxHmacBudgetSpec ...))` when
`unwrap_failed` resolves directly to `some Rust.panicked`. -/
theorem libcruxHmac_budget_fs_withHaclCodeLoaded_subroutineOk
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hsubs : HaclSubroutinesTrace P mpl)
    (haux : HmacAuxSubroutines P mpl)
    (hext_uf : P.externAt? (mpl.ρ rustUnwrapFailedSym) = some Rust.panicked)
    (halloc : HmacBudgetAllocSubroutines M A lim P mpl) :
    subroutine_ok P (mpl.base 6)
      (withHaclCodeLoaded mpl
        (withFsTraceBudget (libcruxHmacBudgetSpec sha256CompressState M A lim))) := by
  let _ : HaclPlacement := ⟨mpl, hP.placeable⟩
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st⟩ R s0 hpc0 hrun0 hpre0 hsp0
  dsimp only [withHaclCodeLoaded, withFsTraceBudget, libcruxHmacBudgetSpec] at hpre0
  simp only [sepConj_assoc] at hpre0
  rw [satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨hcl0, hpre0⟩
  rw [satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8, hw0, hx1, hx2, hx3, hx4, hw5, hx6, hEnv⟩, hm0⟩
  refine ⟨(x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
    A.pool lim st s0 ∗ stackAt s0.sp extHookStack, R,
    by simpa only [sepConj_assoc] using hm0, ?_⟩
  let sp1 := s0.sp - 224#64
  refine sepWPp_seg6 hP hcl0
    (mid := if 2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat then
      mpl.base 6 + 2592#64 else mpl.base 6 + 252#64)
    (Pre := stackAt s0.sp 224)
    (Post := hmacPrologueSpatial s0)
    (Frame := (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
      A.pool lim st s0 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
    (PurePost := hmacProloguePure s0)
    (by
      unfold extHookStack; dsimp only [Nat.reducePow]
      rw [stackAt_split_hmac s0.sp]
      exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_prologue (s0 := s0.setMem m)
        (by cases s0; exact hpc0) (by cases s0; exact hrun0) (by cases s0; exact hsp0)
        (by cases s0; exact hw0) (by cases s0; exact hw5) (by cases s0; exact hx6)
      cases s0; exact h)
    fun s1 hpc1 hrun1 hvm1 htr1 hfs1 hcl1 hpure1 => ?_
  by_cases hovf : 2 ^ 32 ≤ x.key.length ∨ 2 ^ 32 ≤ x.data.length
  · have hcond : 2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat := by
      rwa [hx2, hx4]
    simp only [hcond, ↓reduceIte] at hpc1
    have hsp1 : s1.sp = sp1 := hpure1.1
    have hsp_al1 : s1.spAligned = true := by
      unfold State.spAligned; rw [hsp1]; exact State.spAligned_sub s0 224#64 hsp0
    refine hmac_unwrap_panic_ext_wpp hP hext_uf hcl1 hpc1 hrun1 hsp_al1
      (Rest := (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
        memRegion (sp1 + 96#64) 32 ∗ (∃∗ p, hmacSavedCalleeRegs sp1 s0 p) ∗
        (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 4320#64) 12064)
      (by
        dsimp only [hmacPrologueSpatial]
        rw [hsp1]
        exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
      fun sf P' htrf hfsf hmR => ?_
    dsimp only [withHaclCodeLoaded, withFsTraceBudget, libcruxHmacBudgetSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hfsf.trans hfs1, htrf.trans htr1⟩, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hovf, (htrf.trans htr1) ▸ List.prefix_refl s0.trace⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap P')) hmR⟩
  · have hk32 : x.key.length < 2 ^ 32 := by omega
    have hd32 : x.data.length < 2 ^ 32 := by omega
    have hcond : ¬(2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat) := by
      rw [hx2, hx4]; exact hovf
    simp only [hcond, ↓reduceIte] at hpc1
    rcases hpure1 with ⟨hsp1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1,
      hx27_1, hx28_1, hv_1, hx26_fn⟩
    have hx26_1 : s1.readReg64 .x26 = tryFromDataNiche (s0.readReg64 .x4) :=
      hx26_fn (hx2.symm ▸ hk32) (hx4.symm ▸ hd32)
    refine sepWPp_congr_pre
      (P2 := (∃∗ pad152 : BitVec 64, hmacSavedCalleeRegs sp1 s0 pad152) ∗
        ((sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
         memRegion (sp1 + 64#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
         (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
         A.pool lim st s1 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064))
      (by
        dsimp only [hmacPrologueSpatial]
        rw [A.pool_of_vmPreserved hvm1]
        exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl)) ?_
    refine sepWPp_exists_elim fun pad152 => ?_
    refine sepWPp_of_sepWP_dep (mid := s0.readReg64 .x30) (Frame := emp)
      (Pre := (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
        memRegion (sp1 + 64#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
        hmacSavedCalleeRegs sp1 s0 pad152 ∗
        (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
        A.pool lim st s1 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
      (PurePost := fun sf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s1.trace ∧ sf.fs = s1.fs)
      (Post := fun sf => (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
        vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
        A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗
        stackAt s0.sp 224 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
      (by rw [sepConj_emp]; exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
      (hmac_budget_valid_wp hP hsubs (hmacAux_toValid haux) halloc (s0 := s0) (pad152 := pad152)
        (Frame := stackAt (s0.sp - 4320#64) 12064)
        hk32 hd32 hx2 hx4 hEnv hcl1 hpc1 hrun1 hsp0 hsp1
        ⟨hx19_1.trans hx8, hx20_1.trans hx3, hx21_1, hx23_1, hx24_1.trans hx1,
         hx25_1, hx26_1, hx27_1, hx28_1, hv_1⟩)
      fun sf hpcf hrunf ⟨hspf, hcsf, htr_val, hfs_val⟩ => ?_
    refine sepWPp_done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
    dsimp only [withHaclCodeLoaded, withFsTraceBudget, libcruxHmacBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfs_val.trans hfs1, htr_val.trans htr1⟩, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨libcruxHmacSha256Events, ?_⟩
    have hpost_ent :
        (((x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
          vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
          A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗
          stackAt s0.sp 224 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064) ∗ emp) ⊢
        (⌜x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
          sf.trace = s0.trace ∧ LibcruxHmacEnv x libcruxHmacSha256Events⌝ ∗
         (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
         vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
         A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗
         stackAt s0.sp extHookStack) := by
      have hpure_f : x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
          sf.trace = s0.trace ∧ LibcruxHmacEnv x libcruxHmacSha256Events :=
        ⟨hk32, hd32, htr_val.trans htr1, by unfold LibcruxHmacEnv; split <;> [rfl; omega]⟩
      rw [sepConj_emp]
      refine Entails.trans (Entails.of_eq ?_) (Entails.pure_right hpure_f (Entails.refl _))
      unfold extHookStack; dsimp only [Nat.reducePow]
      rw [stackAt_split_hmac s0.sp]
    exact Satisfies.mono (sepConj_mono_left hpost_ent) hmf

/-- Ambient-program `subroutine_ok` for Block `6` (`libcrux_hmac::hmac`, `w0 = 0` SHA-256)
discharging `withFsTraceBudget (libcruxHmacBudgetSpec sha256CompressState M A lim)` when
`P.CodeLoaded` implies `libcruxHmacLib.CodeLoaded mpl` and `unwrap_failed` resolves directly to
`some Rust.panicked`. -/
theorem libcruxHmac_budget_fs_subroutineOk
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hCL : ∀ m : Memory, P.CodeLoaded m → libcruxHmacLib.CodeLoaded mpl m)
    (hsubs : HaclSubroutinesTrace P mpl)
    (haux : HmacAuxSubroutines P mpl)
    (hext_uf : P.externAt? (mpl.ρ rustUnwrapFailedSym) = some Rust.panicked)
    (halloc : HmacBudgetAllocSubroutines M A lim P mpl) :
    subroutine_ok P (mpl.base 6)
      (withFsTraceBudget (libcruxHmacBudgetSpec sha256CompressState M A lim)) :=
  subroutine_ok_of_withHaclCodeLoaded hCL
    (libcruxHmac_budget_fs_withHaclCodeLoaded_subroutineOk hP hsubs haux hext_uf halloc)

/-- Prepend pure unfetched-extern guard (`HooksUnfetched P s0.mem`) to `spec.pre`. -/
@[expose] def withHooksUnfetched (P : Program) {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 =>
      ⌜∀ (m' : Memory) (pc : BitVec 64),
        s0.mem.KeepsFrozen m' → P.externAt? pc ≠ none → Program.pureMem.fetchMem m' pc = none⌝ ∗
      spec.pre x s0 }

private theorem step_pureMem_of_noExterns {P : Program} {s s' : State}
    (hsvc : P.svc = Syscall.standard) (hno : ∀ pc : BitVec 64, P.externAt? pc = none)
    (hs : Step P s s') : Step Program.pureMem s s' := by
  have hpure_no : ∀ pc : BitVec 64, Program.pureMem.externAt? pc = none := by
    intro pc
    unfold Program.externAt? Program.pureMem Program.pureWithSvc
    rfl
  have hfetch : ∀ (m : Memory) (pc : BitVec 64),
      P.fetchMem m pc = Program.pureMem.fetchMem m pc := by
    intro m pc
    unfold Program.fetchMem
    rw [hno pc, hpure_no pc]
  cases hs with
  | @exec inst h_run h_fetch =>
    have heval : P.evalInst inst s = Program.pureMem.evalInst inst s := by
      unfold Program.evalInst Program.pureMem Program.pureWithSvc Program.ofSvc
      rw [hsvc]
    rw [heval]
    exact Step.exec h_run (hfetch s.mem s.pc ▸ h_fetch)
  | halt_unmapped h_run h_fetch _ =>
    exact Step.halt_unmapped h_run (hfetch s.mem s.pc ▸ h_fetch) (hpure_no s.pc)
  | extern _ h_ext _ _ =>
    rw [hno] at h_ext; cases h_ext
  | extern_fault _ h_ext _ =>
    rw [hno] at h_ext; cases h_ext

private theorem steps_pureMem_of_noExterns {P : Program} {s sf : State}
    (hsvc : P.svc = Syscall.standard) (hno : ∀ pc : BitVec 64, P.externAt? pc = none)
    (hs : Steps P s sf) : Steps Program.pureMem s sf := by
  induction hs with
  | refl _ => exact Steps.refl _
  | step h1 _ ih => exact Steps.step (step_pureMem_of_noExterns hsvc hno h1) ih

/-- Split-program `subroutine_ok` for Block `6` (`libcrux_hmac::hmac`, `w0 = 0` SHA-256):
discharges `withHooksUnfetched P (withFsTraceBudget (libcruxHmacBudgetSpec ...))` by running
the valid path on extern-free `P_valid` (`P_valid.svc = Syscall.standard`,
`∀ pc, P_valid.externAt? pc = none`) and lifting via `steps_prog_of_pureMem_outcome`, while
running the `unwrap_failed` overflow-panic path directly on `P`. -/
theorem libcruxHmac_budget_fs_split_subroutineOk
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P_valid P : Program} {mpl : Obj.MultiPlacement}
    (hPv_svc : P_valid.svc = Syscall.standard)
    (hPv_noext : ∀ pc : BitVec 64, P_valid.externAt? pc = none)
    (hPv : HaclInProg P_valid mpl)
    (hP : HaclInProg P mpl)
    (hCL_Pv : ∀ m : Memory, P.CodeLoaded m → P_valid.CodeLoaded m)
    (hCL_lib : ∀ m : Memory, P.CodeLoaded m → libcruxHmacLib.CodeLoaded mpl m)
    (hsubs : HaclSubroutinesTrace P_valid mpl)
    (haux : HmacValidAuxSubroutines P_valid mpl)
    (hext_uf : P.externAt? (mpl.ρ rustUnwrapFailedSym) = some Rust.panicked)
    (halloc : HmacBudgetAllocSubroutines M A lim P_valid mpl) :
    subroutine_ok P (mpl.base 6)
      (withHooksUnfetched P
        (withFsTraceBudget (libcruxHmacBudgetSpec sha256CompressState M A lim))) := by
  let _ : HaclPlacement := ⟨mpl, hP.placeable⟩
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st⟩ R s0 hpc0 hrun0 hpre0 hsp0
  dsimp only [withHooksUnfetched, withFsTraceBudget, libcruxHmacBudgetSpec] at hpre0
  simp only [sepConj_assoc] at hpre0
  rw [satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨hhooks0, hpre0⟩
  rw [satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8, hw0, hx1, hx2, hx3, hx4, hw5, hx6, hEnv⟩, hm0⟩
  refine ⟨(x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
    A.pool lim st s0 ∗ stackAt s0.sp extHookStack, R,
    by simpa only [sepConj_assoc] using hm0, ?_⟩
  let sp1 := s0.sp - 224#64
  by_cases hovf : 2 ^ 32 ≤ x.key.length ∨ 2 ^ 32 ≤ x.data.length
  · intro R' hm' hLP
    have hcl0 : libcruxHmacLib.CodeLoaded mpl s0.mem := hCL_lib s0.mem hLP
    have hwp_pan :
        SepWPp P (s0.readReg64 .x30) s0
          ((x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
            A.pool lim st s0 ∗ stackAt s0.sp extHookStack)
          (fun sf P_f =>
            ((sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (withHooksUnfetched P
                (withFsTraceBudget (libcruxHmacBudgetSpec sha256CompressState M A lim))).post
                (x, st) s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f =>
            (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (withHooksUnfetched P
                (withFsTraceBudget (libcruxHmacBudgetSpec sha256CompressState M A lim))).onPanic
                (x, st) s0 sf ∗ R)) := by
      refine sepWPp_seg6 hP hcl0
        (mid := if 2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat then
          mpl.base 6 + 2592#64 else mpl.base 6 + 252#64)
        (Pre := stackAt s0.sp 224)
        (Post := hmacPrologueSpatial s0)
        (Frame := (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
          A.pool lim st s0 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
        (PurePost := hmacProloguePure s0)
        (by
          unfold extHookStack; dsimp only [Nat.reducePow]
          rw [stackAt_split_hmac s0.sp]
          exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
        (fun m => by
          have h := hmac_seg_prologue (s0 := s0.setMem m)
            (by cases s0; exact hpc0) (by cases s0; exact hrun0) (by cases s0; exact hsp0)
            (by cases s0; exact hw0) (by cases s0; exact hw5) (by cases s0; exact hx6)
          cases s0; exact h)
        fun s1 hpc1 hrun1 _ htr1 hfs1 hcl1 hpure1 => ?_
      have hcond : 2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat := by
        rwa [hx2, hx4]
      simp only [hcond, ↓reduceIte] at hpc1
      have hsp1 : s1.sp = sp1 := hpure1.1
      have hsp_al1 : s1.spAligned = true := by
        unfold State.spAligned; rw [hsp1]; exact State.spAligned_sub s0 224#64 hsp0
      refine hmac_unwrap_panic_ext_wpp hP hext_uf hcl1 hpc1 hrun1 hsp_al1
        (Rest := (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
          memRegion (sp1 + 96#64) 32 ∗ (∃∗ p, hmacSavedCalleeRegs sp1 s0 p) ∗
          (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
          A.pool lim st s0 ∗ stackAt (s0.sp - 4320#64) 12064)
        (by
          dsimp only [hmacPrologueSpatial]
          rw [hsp1]
          exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
        fun sf P' htrf hfsf hmR => ?_
      dsimp only [withHooksUnfetched, withFsTraceBudget, libcruxHmacBudgetSpec]
      simp only [sepConj_assoc]
      rw [satisfies_pure_sepConj]
      refine ⟨⟨hfsf.trans hfs1, htrf.trans htr1⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hovf, (htrf.trans htr1) ▸ List.prefix_refl s0.trace⟩,
        Satisfies.mono (sepConj_mono_left (entails_anyHeap P')) hmR⟩
    exact hwp_pan R' hm' hLP
  · intro R' hm' hLP
    have hcl0 : libcruxHmacLib.CodeLoaded mpl s0.mem := hCL_lib s0.mem hLP
    have hLP_v : P_valid.CodeLoaded s0.mem := hCL_Pv s0.mem hLP
    have hk32 : x.key.length < 2 ^ 32 := by omega
    have hd32 : x.data.length < 2 ^ 32 := by omega
    have hwp_valid :
        SepWPp P_valid (s0.readReg64 .x30) s0
          ((x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
            A.pool lim st s0 ∗ stackAt s0.sp extHookStack)
          (fun sf P_f =>
            ((sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (withHooksUnfetched P
                (withFsTraceBudget (libcruxHmacBudgetSpec sha256CompressState M A lim))).post
                (x, st) s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun _ _ => False) := by
      refine sepWPp_seg6 hPv hcl0
        (mid := if 2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat then
          mpl.base 6 + 2592#64 else mpl.base 6 + 252#64)
        (Pre := stackAt s0.sp 224)
        (Post := hmacPrologueSpatial s0)
        (Frame := (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
          A.pool lim st s0 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
        (PurePost := hmacProloguePure s0)
        (by
          unfold extHookStack; dsimp only [Nat.reducePow]
          rw [stackAt_split_hmac s0.sp]
          exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
        (fun m => by
          have h := hmac_seg_prologue (s0 := s0.setMem m)
            (by cases s0; exact hpc0) (by cases s0; exact hrun0) (by cases s0; exact hsp0)
            (by cases s0; exact hw0) (by cases s0; exact hw5) (by cases s0; exact hx6)
          cases s0; exact h)
        fun s1 hpc1 hrun1 hvm1 htr1 hfs1 hcl1 hpure1 => ?_
      have hcond : ¬(2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat) := by
        rw [hx2, hx4]; exact hovf
      simp only [hcond, ↓reduceIte] at hpc1
      rcases hpure1 with ⟨hsp1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1,
        hx27_1, hx28_1, hv_1, hx26_fn⟩
      have hx26_1 : s1.readReg64 .x26 = tryFromDataNiche (s0.readReg64 .x4) :=
        hx26_fn (hx2.symm ▸ hk32) (hx4.symm ▸ hd32)
      refine sepWPp_congr_pre
        (P2 := (∃∗ pad152 : BitVec 64, hmacSavedCalleeRegs sp1 s0 pad152) ∗
          ((sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
           memRegion (sp1 + 64#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
           (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
           A.pool lim st s1 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064))
        (by
          dsimp only [hmacPrologueSpatial]
          rw [A.pool_of_vmPreserved hvm1]
          exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl)) ?_
      refine sepWPp_exists_elim fun pad152 => ?_
      refine sepWPp_of_sepWP_dep (mid := s0.readReg64 .x30) (Frame := emp)
        (Pre := (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
          memRegion (sp1 + 64#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
          hmacSavedCalleeRegs sp1 s0 pad152 ∗
          (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
          A.pool lim st s1 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
        (PurePost := fun sf =>
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s1.trace ∧ sf.fs = s1.fs)
        (Post := fun sf => (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
          vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
          A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗
          stackAt s0.sp 224 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
        (by rw [sepConj_emp]; exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
        (hmac_budget_valid_wp hPv hsubs haux halloc (s0 := s0) (pad152 := pad152)
          (Frame := stackAt (s0.sp - 4320#64) 12064)
          hk32 hd32 hx2 hx4 hEnv hcl1 hpc1 hrun1 hsp0 hsp1
          ⟨hx19_1.trans hx8, hx20_1.trans hx3, hx21_1, hx23_1, hx24_1.trans hx1,
           hx25_1, hx26_1, hx27_1, hx28_1, hv_1⟩)
        fun sf hpcf hrunf ⟨hspf, hcsf, htr_val, hfs_val⟩ => ?_
      refine sepWPp_done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
      dsimp only [withHooksUnfetched, withFsTraceBudget, libcruxHmacBudgetSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hfs_val.trans hfs1, htr_val.trans htr1⟩, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨libcruxHmacSha256Events, ?_⟩
      have hpost_ent :
          (((x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
            vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
            A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗
            stackAt s0.sp 224 ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064) ∗ emp) ⊢
          (⌜x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
            sf.trace = s0.trace ∧ LibcruxHmacEnv x libcruxHmacSha256Events⌝ ∗
           (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
           vecU8 A.repAlloc x.ret (hmacWith sha256CompressState x.key x.data) ∗
           A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗
           stackAt s0.sp extHookStack) := by
        have hpure_f : x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
            sf.trace = s0.trace ∧ LibcruxHmacEnv x libcruxHmacSha256Events :=
          ⟨hk32, hd32, htr_val.trans htr1, by unfold LibcruxHmacEnv; split <;> [rfl; omega]⟩
        rw [sepConj_emp]
        refine Entails.trans (Entails.of_eq ?_) (Entails.pure_right hpure_f (Entails.refl _))
        unfold extHookStack; dsimp only [Nat.reducePow]
        rw [stackAt_split_hmac s0.sp]
      exact Satisfies.mono (sepConj_mono_left hpost_ent) hmf
    obtain ⟨sf, hsteps_pv, ⟨hpcf, hrunf, P_f, hmf, hQ⟩ | ⟨_, _, _, hQp⟩ | ⟨_, hoom⟩⟩ :=
      hwp_valid R' hm' hLP_v
    · have hpure := steps_pureMem_of_noExterns hPv_svc hPv_noext hsteps_pv
      have hsteps_P := VerifiedLibraries.Mallocng.Proofs.steps_prog_of_pureMem_outcome
        hP.svc_eq hhooks0 (Memory.KeepsFrozen.refl s0.mem) hpure (Or.inl hrunf)
      exact ⟨sf, hsteps_P, Or.inl ⟨hpcf, hrunf, P_f, hmf, hQ⟩⟩
    · exact False.elim hQp
    · exact False.elim (not_satisfies_false_sepConj hoom)

/-! ### SPQR Unbudgeted `libcruxHmacSpec` Counterparts -/

private theorem call_allocZeroed64_spqr_p6 [HaclPlacement] {A : RustAlloc} {P : Program}
    (hP : HaclInProg P haclMpl) (haux : HmacAuxSubroutines P haclMpl)
    (halloc : HmacAllocSubroutines A P haclMpl)
    (F : SepProp) {ret_pc : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + 264#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 64#64) (hx1 : s.readReg64 .x1 = 1#64)
    (hpre : Pre ⊢ A.pool ∗ stackAt s.sp 4096 ∗ F)
    (hQp : ∀ sf : State, sf.trace = s.trace ++ [allocFailedEvent] → Qp sf anyHeap)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + 268#64 →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.trace = s.trace → sf.readReg64 .x0 ≠ 0#64 →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWPp P ret_pc sf
        (A.pool ∗ stackAt s.sp 4096 ∗ A.live (sf.readReg64 .x0) 64 1 ∗
         (sf.readReg64 .x0 ↦ₛ List.replicate 64 0#8) ∗ F) Q Qp oom) :
    SepWPp P ret_pc s Pre Q Qp oom := by
  let imm := (haclMpl.ρ rustAllocZeroedSym - haclMpl.base 6) - 264#64
  refine sepWPp_of_sepWP_dep (mid := haclMpl.base 6 + 268#64) (Frame := emp)
    (Post := fun sf => (rustAllocZeroedSpec A).post (64, 1) (execInst (.bl imm) s) sf ∗ F)
    (PurePost := fun sf => sf.sp = s.sp ∧ sf.spAligned = true ∧
      CalleeSavedPreserved s sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem)
    (Entails.of_eq (sepConj_emp Pre).symm)
    (sepWP_bl6 hP 264 halloc.allocZeroed_ok (resolve_allocZeroed haclMpl) (64, 1) F
      hcl hpc hrun hsp_align
      (by
        dsimp only [rustAllocZeroedSpec]
        have hpure : ((execInst (.bl imm) s).readReg64 .x0).toNat = 64 ∧
            ((execInst (.bl imm) s).readReg64 .x1).toNat = 1 ∧ LayoutOk 64 1 := by
          simp only [wp_norm, hx0, hx1]; exact ⟨by decide, by decide, layoutOk_64_1⟩
        refine Entails.trans hpre ?_
        rw [show stackAt s.sp 4096 = stackAt (execInst (.bl imm) s).sp allocHookStack by
          rw [bl_sp]]
        simp only [sepConj_assoc]
        exact Entails.pure_right hpure (Entails.refl _))
      fun sf hpcsf hrunsf hspsf hsp_alsf hcssf hclsf =>
        SepWP.done hpcsf hrunsf
          ⟨⟨hspsf, hsp_alsf, hcssf, hclsf⟩, Entails.refl _⟩)
    fun s1 hpc1 hrun1 ⟨hsp1, hsp_al1, hcs1, hcl1⟩ => ?_
  dsimp only [rustAllocZeroedSpec]
  by_cases hp0 : s1.readReg64 .x0 = 0#64
  · refine sepWPp_congr_pre
      (P2 := ⌜s1.trace = (execInst (.bl imm) s).trace ++ [allocFailedEvent]⌝ ∗
        (stackAt s1.sp 4096 ∗ A.pool ∗ F))
      (by
        have hp0' : s1.readReg64 .x0 = 0 := hp0
        simp only [hp0', ↓reduceIte]
        rw [bl_sp, sepConj_emp, ← hsp1]
        unfold allocHookStack; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine sepWPp_pure_left fun htr1 => ?_
    rw [bl_trace] at htr1
    refine sepWPp_seg6 hP hcl1 (Pre := emp) (Post := emp)
      (Frame := stackAt s1.sp 4096 ∗ A.pool ∗ F)
      (PurePost := fun sf => sf.sp = s1.sp ∧ sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = 64#64)
      (Entails.of_eq (emp_sepConj _).symm)
      (fun m => by
        have h := hmac_seg_oom_key (s := s1.setMem m) (R := emp)
          (by cases s1; exact hpc1) (by cases s1; exact hrun1) (by cases s1; exact hp0)
        cases s1; exact h)
      fun s2 hpc2 hrun2 _ htr2 _ hcl2 ⟨hsp2, _, _⟩ => ?_
    have hsp_al2 : s2.spAligned = true := by unfold State.spAligned at hsp_al1 ⊢; rwa [hsp2]
    refine hmac_panic_bl6 hP 2544 haux.handleError_ok (resolve_handleError haclMpl)
      (stackAt (s2.sp - 16#64) 4080 ∗ A.pool ∗ F)
      hcl2 hpc2 hrun2 hsp_al2
      (by rw [emp_sepConj, ← hsp2, stackAt_4096_split_16 s2.sp]; exact Entails.of_eq (by sep_ac_rfl))
      fun sf htrf => hQp sf (by rw [htrf, htr2, htr1])
  · refine sepWPp_congr_pre
      (P2 := ⌜(s1.readReg64 .x0).toNat % 1 = 0 ∧ s1.trace = (execInst (.bl imm) s).trace⌝ ∗
        (A.pool ∗ stackAt s.sp 4096 ∗ A.live (s1.readReg64 .x0) 64 1 ∗
         (s1.readReg64 .x0 ↦ₛ List.replicate 64 0#8) ∗ F))
      (by
        have hp0' : s1.readReg64 .x0 ≠ 0 := hp0
        simp only [hp0', ↓reduceIte]
        rw [bl_sp, sepConj_emp]
        unfold allocHookStack; exact Entails.of_eq (by sep_ac_rfl)) ?_
    intro R hm hLP
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm
    rcases hm with ⟨⟨_, htr1⟩, hm1⟩
    rw [bl_trace] at htr1
    exact hnext s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 htr1 hp0 hcl1 R hm1 hLP

private theorem call_alloc_spqr_p6 [HaclPlacement] {A : RustAlloc} {P : Program}
    (hP : HaclInProg P haclMpl) (haux : HmacAuxSubroutines P haclMpl)
    (halloc : HmacAllocSubroutines A P haclMpl)
    (off size oom_off : Nat) (F : SepProp)
    {ret_pc : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hargs : (s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = 1 ∧ LayoutOk size 1)
    (hpre : Pre ⊢ A.pool ∗ stackAt s.sp 4096 ∗ F)
    (hoom_seg : ∀ (s1 : State) (m : Memory),
      s1.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) → s1.status = .Running →
      s1.readReg64 .x0 = 0#64 →
      SepWP (libcruxHmacLib.blockProgram haclMpl 6)
        (haclMpl.base 6 + BitVec.ofNat 64 oom_off) (s1.setMem m) emp
        (fun sf P' => (sf.sp = s1.sp) ∧ (P' ⊢ emp)))
    (hQp : ∀ sf : State, sf.trace = s.trace ++ [allocFailedEvent] → Qp sf anyHeap)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.trace = s.trace → sf.readReg64 .x0 ≠ 0#64 →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWPp P ret_pc sf
        (A.pool ∗ stackAt s.sp 4096 ∗ A.live (sf.readReg64 .x0) size 1 ∗
         memRegion (sf.readReg64 .x0) size ∗ F) Q Qp oom)
    (hoff : off < 2848 := by decide)
    (hoom_lt : oom_off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ rustAllocSym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, rustAllocSym])
    (hf_oom : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 oom_off) =
      some (.bl ((haclPl6.ρ rustHandleErrorSym - haclPl6.base) - BitVec.ofNat 64 oom_off)) := by
        simp [wp_norm, rustHandleErrorSym]) :
    SepWPp P ret_pc s Pre Q Qp oom := by
  let imm := (haclMpl.ρ rustAllocSym - haclMpl.base 6) - BitVec.ofNat 64 off
  refine sepWPp_of_sepWP_dep (mid := haclMpl.base 6 + BitVec.ofNat 64 (off + 4)) (Frame := emp)
    (Post := fun sf => (rustAllocSpec A).post (size, 1) (execInst (.bl imm) s) sf ∗ F)
    (PurePost := fun sf => sf.sp = s.sp ∧ sf.spAligned = true ∧
      CalleeSavedPreserved s sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem)
    (Entails.of_eq (sepConj_emp Pre).symm)
    (sepWP_bl6 hP off halloc.alloc_ok (resolve_alloc haclMpl) (size, 1) F
      hcl hpc hrun hsp_align
      (by
        dsimp only [rustAllocSpec]
        have hpure : ((execInst (.bl imm) s).readReg64 .x0).toNat = size ∧
            ((execInst (.bl imm) s).readReg64 .x1).toNat = 1 ∧ LayoutOk size 1 := by
          simp only [wp_norm]; exact hargs
        refine Entails.trans hpre ?_
        rw [show stackAt s.sp 4096 = stackAt (execInst (.bl imm) s).sp allocHookStack by
          rw [bl_sp]]
        simp only [sepConj_assoc]
        exact Entails.pure_right hpure (Entails.refl _))
      (fun sf hpcsf hrunsf hspsf hsp_alsf hcssf hclsf =>
        SepWP.done hpcsf hrunsf ⟨⟨hspsf, hsp_alsf, hcssf, hclsf⟩, Entails.refl _⟩)
      hoff hf_pc6)
    fun s1 hpc1 hrun1 ⟨hsp1, hsp_al1, hcs1, hcl1⟩ => ?_
  dsimp only [rustAllocSpec]
  by_cases hp0 : s1.readReg64 .x0 = 0#64
  · refine sepWPp_congr_pre
      (P2 := ⌜s1.trace = (execInst (.bl imm) s).trace ++ [allocFailedEvent]⌝ ∗
        (stackAt s1.sp 4096 ∗ A.pool ∗ F))
      (by
        have hp0' : s1.readReg64 .x0 = 0 := hp0
        simp only [hp0', ↓reduceIte]
        rw [bl_sp, sepConj_emp, ← hsp1]
        unfold allocHookStack; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine sepWPp_pure_left fun htr1 => ?_
    rw [bl_trace] at htr1
    refine sepWPp_seg6 hP hcl1 (Pre := emp) (Post := emp)
      (Frame := stackAt s1.sp 4096 ∗ A.pool ∗ F)
      (PurePost := fun sf => sf.sp = s1.sp)
      (Entails.of_eq (emp_sepConj _).symm)
      (fun m => hoom_seg s1 m hpc1 hrun1 hp0)
      fun s2 hpc2 hrun2 _ htr2 _ hcl2 hsp2 => ?_
    have hsp_al2 : s2.spAligned = true := by unfold State.spAligned at hsp_al1 ⊢; rwa [hsp2]
    refine hmac_panic_bl6 hP oom_off haux.handleError_ok (resolve_handleError haclMpl)
      (stackAt (s2.sp - 16#64) 4080 ∗ A.pool ∗ F)
      hcl2 hpc2 hrun2 hsp_al2
      (by rw [emp_sepConj, ← hsp2, stackAt_4096_split_16 s2.sp]; exact Entails.of_eq (by sep_ac_rfl))
      (fun sf htrf => hQp sf (by rw [htrf, htr2, htr1])) hoom_lt hf_oom
  · refine sepWPp_congr_pre
      (P2 := ⌜(s1.readReg64 .x0).toNat % 1 = 0 ∧ s1.trace = (execInst (.bl imm) s).trace⌝ ∗
        (A.pool ∗ stackAt s.sp 4096 ∗ A.live (s1.readReg64 .x0) size 1 ∗
         memRegion (s1.readReg64 .x0) size ∗ F))
      (by
        have hp0' : s1.readReg64 .x0 ≠ 0 := hp0
        simp only [hp0', ↓reduceIte]
        rw [bl_sp, sepConj_emp]
        unfold allocHookStack; exact Entails.of_eq (by sep_ac_rfl)) ?_
    intro R hm hLP
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm
    rcases hm with ⟨⟨_, htr1⟩, hm1⟩
    rw [bl_trace] at htr1
    exact hnext s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 htr1 hp0 hcl1 R hm1 hLP

private theorem call_dealloc_spqr_6 [HaclPlacement] {A : RustAlloc} {P : Program}
    (hP : HaclInProg P haclMpl) (halloc : HmacAllocSubroutines A P haclMpl)
    (off : Nat) (p : BitVec 64) (F : SepProp)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hargs : s.readReg64 .x0 = p ∧ s.readReg64 .x1 = 64#64 ∧ s.readReg64 .x2 = 1#64)
    (hpre : Pre ⊢ A.pool ∗ A.live p 64 1 ∗ memRegion p 64 ∗ stackAt s.sp 4096 ∗ F)
    (hnext : ∀ sf : State, sf.pc = haclMpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.trace = s.trace →
      libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf (A.pool ∗ stackAt s.sp 4096 ∗ F) post)
    (hoff : off < 2848 := by decide)
    (hf_pc6 : (haclPC6.rebase haclPl6.base (fun _ => none)).fetch
        (haclPl6.base + BitVec.ofNat 64 off) =
      some (.bl ((haclPl6.ρ rustDeallocSym - haclPl6.base) - BitVec.ofNat 64 off)) := by
        simp [wp_norm, rustDeallocSym]) :
    SepWP P target_pc s Pre post := by
  let imm := (haclMpl.ρ rustDeallocSym - haclMpl.base 6) - BitVec.ofNat 64 off
  refine sepWP_bl6 hP off halloc.dealloc_ok (resolve_dealloc haclMpl) (p, 64, 1) F
    hcl hpc hrun hsp_align ?_
    (fun sf hpcsf hrunsf hspsf hsp_alsf hcssf hclsf => ?_) hoff hf_pc6
  · dsimp only [rustDeallocSpec]
    have hpure : (execInst (.bl imm) s).readReg64 .x0 = p ∧
        ((execInst (.bl imm) s).readReg64 .x1).toNat = 64 ∧
        ((execInst (.bl imm) s).readReg64 .x2).toNat = 1 := by
      rcases hargs with ⟨hx0, hx1, hx2⟩
      simp only [wp_norm, hx0, hx1, hx2]; exact ⟨trivial, by decide, by decide⟩
    refine Entails.trans hpre ?_
    rw [show stackAt s.sp 4096 = stackAt (execInst (.bl imm) s).sp allocHookStack by
      rw [bl_sp]]
    simp only [sepConj_assoc]
    exact Entails.pure_right hpure (Entails.refl _)
  · dsimp only [rustDeallocSpec]
    simp only [sepConj_assoc]
    refine sepWP_pure_left fun htr => sepWP_congr_pre ?_
      (hnext sf hpcsf hrunsf hspsf hsp_alsf hcssf (htr.trans (bl_trace imm s)) hclsf)
    rw [bl_sp]; unfold allocHookStack; exact Entails.of_eq (by sep_ac_rfl)

private theorem oom_seg_drop_regs {P : Program} {target : BitVec 64} {s : State}
    {Q1 : State → Prop}
    (h : SepWP P target s emp (fun sf P' => (sf.sp = s.sp ∧ Q1 sf) ∧ (P' ⊢ emp))) :
    SepWP P target s emp (fun sf P' => (sf.sp = s.sp) ∧ (P' ⊢ emp)) := by
  unfold SepWP reaches_pc
  intro R hm hLP
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, ⟨hsp, _⟩, hent⟩ | hoom⟩ := h.elim hm hLP
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hsp, hent⟩⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩

private theorem hmac_spqr_tail_wpp [HaclPlacement] {A : RustAlloc} {P : Program}
    (hP : HaclInProg P haclMpl) (haux : HmacAuxSubroutines P haclMpl)
    (halloc : HmacAllocSubroutines A P haclMpl)
    {x : LibcruxHmacCall} {pKey pIpad pOpad pad152 : BitVec 64}
    {s0 s : State} {Frame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem)
    (hpc : s.pc = haclMpl.base 6 + 2140#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64) (hsp_align : s.spAligned = true) (hsp0 : s0.spAligned = true)
    (hregs : s.readReg64 .x19 = x.ret ∧ s.readReg64 .x22 = pKey ∧ s.readReg64 .x23 = pIpad ∧
      s.readReg64 .x24 = pOpad ∧ s.readReg64 .x27 = 32#64 ∧
      s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hQp : ∀ sf : State, sf.trace = s.trace ++ [allocFailedEvent] → Qp sf anyHeap)
    (hQ : ∀ sf : State, ∀ P' : SepProp,
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s.trace →
      (P' ⊢ stackAt s0.sp 224 ∗ vecU8 A x.ret (hmacWith sha256CompressState x.key x.data) ∗
            A.pool ∗ stackAt (s0.sp - 224#64) 4096 ∗ Frame) →
      Q sf P') :
    let sp1 := s0.sp - 224#64
    SepWPp P (s0.readReg64 .x30) s
      ((sp1 ↦ₛ hmacWith sha256CompressState x.key x.data) ∗ memRegion (sp1 + 32#64) 32 ∗
       ((sp1 + 64#64) ↦ₛ shaStateBytes (hmacOuterState x.key x.data)) ∗ memRegion (sp1 + 96#64) 32 ∗
       hmacSavedCalleeRegs sp1 s0 pad152 ∗ A.pool ∗
       A.live pKey 64 1 ∗ memRegion pKey 64 ∗ A.live pIpad 64 1 ∗ memRegion pIpad 64 ∗
       A.live pOpad 64 1 ∗ memRegion pOpad 64 ∗ memRegion x.ret 24 ∗ stackAt sp1 4096 ∗ Frame)
      Q Qp oom := by
  intro sp1
  rcases hregs with ⟨hx19, hx22, hx23, hx24, hx27, hx28, hvregs⟩
  let CoreKeep := (sp1 ↦ₛ hmacWith sha256CompressState x.key x.data) ∗
    memRegion (sp1 + 32#64) 32 ∗ ((sp1 + 64#64) ↦ₛ shaStateBytes (hmacOuterState x.key x.data)) ∗
    memRegion (sp1 + 96#64) 32 ∗ hmacSavedCalleeRegs sp1 s0 pad152 ∗ memRegion x.ret 24
  -- 3 x dealloc + shim + alloc32_args (+2140 -> +2200) via sepWPp_of_sepWP
  refine sepWPp_of_sepWP (mid := haclMpl.base 6 + 2200#64) (Frame := CoreKeep ∗ Frame)
    (Pre := A.pool ∗ A.live pKey 64 1 ∗ memRegion pKey 64 ∗
      A.live pIpad 64 1 ∗ memRegion pIpad 64 ∗ A.live pOpad 64 1 ∗ memRegion pOpad 64 ∗
      stackAt sp1 4096)
    (Post := A.pool ∗ stackAt sp1 4096)
    (PurePost := fun s8 => s8.sp = sp1 ∧ s8.spAligned = true ∧ CalleeSavedPreserved s s8 ∧
      s8.trace = s.trace ∧ libcruxHmacLib.CodeLoaded haclMpl s8.mem ∧
      s8.readReg64 .x0 = 32#64 ∧ s8.readReg64 .x1 = 1#64)
    (Entails.of_eq (by dsimp only [CoreKeep]; sep_ac_rfl))
    (?_)
    fun s8 hpc8 hrun8 ⟨hsp8, hsp_al8, hcs08, htr08, hcl8, hx0_8, hx1_8⟩ => ?_
  · refine sepWP_seg6 hP hcl (Pre := emp) (Post := emp)
      (Frame := A.pool ∗ A.live pKey 64 1 ∗ memRegion pKey 64 ∗
        A.live pIpad 64 1 ∗ memRegion pIpad 64 ∗ A.live pOpad 64 1 ∗ memRegion pOpad 64 ∗
        stackAt sp1 4096)
      (PurePost := fun sf => sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
        sf.readReg64 .x0 = s.readReg64 .x24 ∧ sf.readReg64 .x1 = 64#64 ∧ sf.readReg64 .x2 = 1#64)
      (Entails.of_eq (emp_sepConj _).symm)
      (fun m => by
        have h := hmac_seg_dealloc_x24 (s := s.setMem m) (R := emp)
          (by cases s; exact hpc) (by cases s; exact hrun)
        cases s; exact h)
      fun s1 hpc1 hrun1 _ htr1 _ hcl1 ⟨hsp1, hcs1, hx0_1, hx1_1, hx2_1⟩ => ?_
    have hsp_al1 : s1.spAligned = true := by unfold State.spAligned at hsp_align ⊢; rwa [hsp1]
    refine call_dealloc_spqr_6 hP halloc 2152 pOpad
      (A.live pKey 64 1 ∗ memRegion pKey 64 ∗ A.live pIpad 64 1 ∗ memRegion pIpad 64)
      hcl1 hpc1 hrun1 hsp_al1 ⟨hx0_1.trans hx24, hx1_1, hx2_1⟩
      (by rw [emp_sepConj, hsp1, hsp]; exact Entails.of_eq (by sep_ac_rfl))
      fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 htr2 hcl2 => ?_
    have hcs02 := hcs1.trans hcs2
    refine sepWP_seg6 hP hcl2 (Pre := emp) (Post := emp)
      (Frame := A.pool ∗ stackAt s1.sp 4096 ∗ A.live pKey 64 1 ∗ memRegion pKey 64 ∗
        A.live pIpad 64 1 ∗ memRegion pIpad 64)
      (PurePost := fun sf => sf.sp = s2.sp ∧ CalleeSavedPreserved s2 sf ∧
        sf.readReg64 .x0 = s2.readReg64 .x23 ∧ sf.readReg64 .x1 = 64#64 ∧ sf.readReg64 .x2 = 1#64)
      (Entails.of_eq (emp_sepConj _).symm)
      (fun m => by
        have h := hmac_seg_dealloc_x23 (s := s2.setMem m) (R := emp)
          (by cases s2; exact hpc2) (by cases s2; exact hrun2)
        cases s2; exact h)
      fun s3 hpc3 hrun3 _ htr3 _ hcl3 ⟨hsp3, hcs3, hx0_3, hx1_3, hx2_3⟩ => ?_
    have hsp_al3 : s3.spAligned = true := by unfold State.spAligned at hsp_al2 ⊢; rwa [hsp3]
    have hx23_2 : s2.readReg64 .x23 = pIpad := (HmacCoreRegsPreserved.of_csp hcs02).2.2.1.trans hx23
    refine call_dealloc_spqr_6 hP halloc 2168 pIpad (A.live pKey 64 1 ∗ memRegion pKey 64)
      hcl3 hpc3 hrun3 hsp_al3 ⟨hx0_3.trans hx23_2, hx1_3, hx2_3⟩
      (by rw [emp_sepConj, hsp3, hsp2]; exact Entails.of_eq (by sep_ac_rfl))
      fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 htr4 hcl4 => ?_
    have hcs04 := (hcs02.trans hcs3).trans hcs4
    refine sepWP_seg6 hP hcl4 (Pre := emp) (Post := emp)
      (Frame := A.pool ∗ stackAt s3.sp 4096 ∗ A.live pKey 64 1 ∗ memRegion pKey 64)
      (PurePost := fun sf => sf.sp = s4.sp ∧ CalleeSavedPreserved s4 sf ∧
        sf.readReg64 .x0 = s4.readReg64 .x22 ∧ sf.readReg64 .x1 = 64#64 ∧ sf.readReg64 .x2 = 1#64)
      (Entails.of_eq (emp_sepConj _).symm)
      (fun m => by
        have h := hmac_seg_dealloc_x22 (s := s4.setMem m) (R := emp)
          (by cases s4; exact hpc4) (by cases s4; exact hrun4)
        cases s4; exact h)
      fun s5 hpc5 hrun5 _ htr5 _ hcl5 ⟨hsp5, hcs5, hx0_5, hx1_5, hx2_5⟩ => ?_
    have hsp_al5 : s5.spAligned = true := by unfold State.spAligned at hsp_al4 ⊢; rwa [hsp5]
    have hx22_4 : s4.readReg64 .x22 = pKey := (HmacCoreRegsPreserved.of_csp hcs04).2.1.trans hx22
    refine call_dealloc_spqr_6 hP halloc 2184 pKey emp
      hcl5 hpc5 hrun5 hsp_al5 ⟨hx0_5.trans hx22_4, hx1_5, hx2_5⟩
      (by rw [emp_sepConj, sepConj_emp, hsp5, hsp4]; exact Entails.of_eq (by sep_ac_rfl))
      fun s6 hpc6 hrun6 hsp6 hsp_al6 hcs6 htr6 hcl6 => ?_
    have hcs06 := (hcs04.trans hcs5).trans hcs6
    refine call_shim_6 hP haux 2188 hcl6 hpc6 hrun6 hsp_al6
      fun s7 hpc7 hrun7 hsp7 hsp_al7 hcs7 _ htr7 hcl7 => ?_
    refine sepWP_seg6 hP hcl7 (Pre := emp) (Post := emp)
      (Frame := A.pool ∗ stackAt s5.sp 4096 ∗ emp)
      (PurePost := fun sf => sf.sp = s7.sp ∧ CalleeSavedPreserved s7 sf ∧
        sf.readReg64 .x0 = 32#64 ∧ sf.readReg64 .x1 = 1#64)
      (Entails.of_eq (emp_sepConj _).symm)
      (fun m => by
        have h := hmac_seg_alloc32_args (s := s7.setMem m) (R := emp)
          (by cases s7; exact hpc7) (by cases s7; exact hrun7)
        cases s7; exact h)
      fun s8 hpc8 hrun8 _ htr8 _ hcl8 ⟨hsp8, hcs8, hx0_8, hx1_8⟩ => ?_
    have hsp_al8 : s8.spAligned = true := by unfold State.spAligned at hsp_al7 ⊢; rwa [hsp8]
    refine SepWP.done hpc8 hrun8 ⟨⟨by rw [hsp8, hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp],
      hsp_al8, (hcs06.trans hcs7).trans hcs8,
      by rw [htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1], hcl8, hx0_8, hx1_8⟩, ?_⟩
    rw [emp_sepConj, sepConj_emp, hsp5, hsp4, hsp3, hsp2, hsp1, hsp]
    exact Entails.refl _
  · -- alloc(32, 1) at +2200 -> OOM at +2700 or tag epilogue at +2204
    refine call_alloc_spqr_p6 hP haux halloc 2200 32 2700 (CoreKeep ∗ Frame)
      hcl8 hpc8 hrun8 hsp_al8
      ⟨by rw [hx0_8]; decide, by rw [hx1_8]; decide, layoutOk_32_1⟩
      (by rw [hsp8]; exact Entails.of_eq (by sep_ac_rfl))
      (fun s9 m hpc9 hrun9 hp0 =>
        oom_seg_drop_regs (Q1 := fun sf => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = 32#64) <| by
        have h := hmac_seg_oom_tag (s := s9.setMem m) (R := emp)
          (by cases s9; exact hpc9) (by cases s9; exact hrun9) (by cases s9; exact hp0)
        cases s9; exact h)
      (fun sf htrf => hQp sf (by rwa [htr08] at htrf))
      fun s9 hpc9 hrun9 hsp9 _ hcs9 htr9 hpOut hcl9 => ?_
    have hcs09 := hcs08.trans hcs9
    have hcr09 := HmacCoreRegsPreserved.of_csp hcs09
    have hsp9_eq : s9.sp = sp1 := hsp9.trans hsp8
    let pOut := s9.readReg64 .x0
    refine sepWPp_seg6 hP hcl9
      (Pre := (sp1 ↦ₛ hmacWith sha256CompressState x.key x.data) ∗ memRegion (sp1 + 32#64) 32 ∗
        ((sp1 + 64#64) ↦ₛ shaStateBytes (hmacOuterState x.key x.data)) ∗ memRegion (sp1 + 96#64) 32 ∗
        hmacSavedCalleeRegs sp1 s0 pad152 ∗ A.live pOut 32 1 ∗ memRegion pOut 32 ∗
        memRegion x.ret 24)
      (Post := stackAt s0.sp 224 ∗ vecU8 A x.ret (hmacWith sha256CompressState x.key x.data))
      (Frame := A.pool ∗ stackAt sp1 4096 ∗ Frame)
      (PurePost := fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (by rw [hsp8]; exact Entails.of_eq (by dsimp only [CoreKeep, pOut]; sep_ac_rfl))
      (fun m => by
        have h := hmac_seg_tag_epilogue (A := A) (s0 := s0) (s := s9.setMem m)
          (ret := x.ret) (pOut := pOut) (pad152 := pad152) (R := emp)
          (hmacWith_sha256_length x.key x.data)
          (shaStateBytes_length (hmacOuterState x.key x.data))
          (by cases s9; exact hpc9) (by cases s9; exact hrun9)
          (by cases s9; exact hsp9_eq) hsp0
          (by cases s9; rfl) hpOut
          (by cases s9; exact hcr09.1.trans hx19)
          (by cases s9; exact hcr09.2.2.2.2.1.trans hx27)
          (by cases s9; exact hcr09.2.2.2.2.2.1.trans hx28)
          (by cases s9; exact hcr09.2.2.2.2.2.2.trans hvregs)
        cases s9; simpa only [sepConj_emp] using h)
      fun sf hpcf hrunf _ htrf _ _ ⟨hspf, hcsf⟩ =>
        sepWPp_done hpcf hrunf
          (hQ sf _ hspf hcsf (by rw [htrf, htr9, htr08]) (Entails.of_eq (by sep_ac_rfl)))

private theorem hmac_spqr_valid_wpp [HaclPlacement] {A : RustAlloc} {P : Program}
    (hP : HaclInProg P haclMpl) (hsubs : HaclSubroutinesTrace P haclMpl)
    (haux : HmacAuxSubroutines P haclMpl) (halloc : HmacAllocSubroutines A P haclMpl)
    {x : LibcruxHmacCall} {keyLenBV dataLenBV pad152 : BitVec 64}
    {s0 s1 : State} {Frame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hk32 : x.key.length < 2 ^ 32) (hd32 : x.data.length < 2 ^ 32)
    (hk_nat : keyLenBV.toNat = x.key.length) (hd_nat : dataLenBV.toNat = x.data.length)
    (hcl1 : libcruxHmacLib.CodeLoaded haclMpl s1.mem)
    (hpc1 : s1.pc = haclMpl.base 6 + 252#64) (hrun1 : s1.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp1 : s1.sp = s0.sp - 224#64)
    (hregs1 : s1.readReg64 .x19 = x.ret ∧ s1.readReg64 .x20 = x.dataA ∧
      s1.readReg64 .x21 = dataLenBV ∧ s1.readReg64 .x23 = keyLenBV ∧
      s1.readReg64 .x24 = x.keyA ∧ s1.readReg64 .x25 = tryFromKeyNiche keyLenBV ∧
      s1.readReg64 .x26 = tryFromDataNiche dataLenBV ∧ s1.readReg64 .x27 = 32#64 ∧
      s1.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hQp : ∀ sf : State, sf.trace = s1.trace ++ [allocFailedEvent] → Qp sf anyHeap)
    (hQ : ∀ sf : State, ∀ P' : SepProp,
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s1.trace →
      (P' ⊢ (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
            vecU8 A x.ret (hmacWith sha256CompressState x.key x.data) ∗
            A.pool ∗ stackAt s0.sp 224 ∗ stackAt (s0.sp - 224#64) 4096 ∗ Frame) →
      Q sf P') :
    let sp1 := s0.sp - 224#64
    SepWPp P (s0.readReg64 .x30) s1
      ((sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
       memRegion (sp1 + 64#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
       hmacSavedCalleeRegs sp1 s0 pad152 ∗
       (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
       A.pool ∗ stackAt sp1 4096 ∗ Frame)
      Q Qp oom := by
  intro sp1
  rcases hregs1 with ⟨hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hv_1⟩
  have hd_bv : dataLenBV = BitVec.ofNat 64 x.data.length := by
    apply BitVec.eq_of_toNat_eq; rw [hd_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsp_al1 : s1.spAligned = true := by
    unfold State.spAligned; rw [hsp1]; exact State.spAligned_sub s0 224#64 hsp0
  let k0 := libcruxHmacKeyBlock sha256CompressState x.key
  have hk0 : k0.length = 64 := libcruxHmacKeyBlock_length sha256CompressState x.key
  let Locals := memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
    hmacSavedCalleeRegs sp1 s0 pad152 ∗ memRegion x.ret 24
  -- 1. shim + alloc64_args_key (+252 -> +264)
  refine sepWPp_of_sepWP
    (Frame := (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 64#64) 32 ∗ Locals ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ A.pool ∗ stackAt sp1 4096 ∗ Frame)
    (Pre := emp) (Post := emp)
    (PurePost := fun s3 => s3.sp = sp1 ∧ s3.spAligned = true ∧ CalleeSavedPreserved s1 s3 ∧
      s3.trace = s1.trace ∧ libcruxHmacLib.CodeLoaded haclMpl s3.mem ∧
      s3.readReg64 .x0 = 64#64 ∧ s3.readReg64 .x1 = 1#64)
    (by rw [emp_sepConj]; exact Entails.of_eq (by dsimp only [Locals]; sep_ac_rfl))
    (call_shim_6 hP haux 252 hcl1 hpc1 hrun1 hsp_al1
      fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 _ htr2 hcl2 =>
        sepWP_seg6 hP hcl2 (Pre := emp) (Post := emp) (Frame := emp)
          (PurePost := fun sf => sf.sp = s2.sp ∧ CalleeSavedPreserved s2 sf ∧
            sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 1#64)
          (Entails.of_eq (emp_sepConj emp).symm)
          (fun m => by
            have h := hmac_seg_alloc64_args_key (s := s2.setMem m) (R := emp)
              (by cases s2; exact hpc2) (by cases s2; exact hrun2)
            cases s2; exact h)
          fun s3 hpc3 hrun3 _ htr3 _ hcl3 ⟨hsp3, hcs3, hx0_3, hx1_3⟩ =>
            SepWP.done hpc3 hrun3 ⟨⟨by rw [hsp3, hsp2, hsp1],
              by unfold State.spAligned at hsp_al2 ⊢; rwa [hsp3],
              hcs2.trans hcs3, htr3.trans htr2, hcl3, hx0_3, hx1_3⟩,
              Entails.of_eq (emp_sepConj emp)⟩)
    fun s3 hpc3 hrun3 ⟨hsp3, hsp_al3, hcs13, htr13, hcl3, hx0_3, hx1_3⟩ => ?_
  -- 2. allocZeroed(64, 1) -> pKey
  refine call_allocZeroed64_spqr_p6 hP haux halloc
    ((sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 64#64) 32 ∗ Locals ∗
     (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl3 hpc3 hrun3 hsp_al3 hx0_3 hx1_3
    (by rw [emp_sepConj, hsp3]; exact Entails.of_eq (by sep_ac_rfl))
    (fun sf htrf => hQp sf (by rwa [htr13] at htrf))
    fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 htr4 hpKey hcl4 => ?_
  -- 3. hmac_key_prep_wp + shim + alloc64_args_ipad (+268 -> +924)
  let pKey := s4.readReg64 .x0
  have hcs14 := hcs13.trans hcs4
  rcases (CalleeSavedPreserved.iff_regs s1 s4).mp hcs14 with
    ⟨hx19_4, hx20_4, hx21_4, _, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _, hv_4⟩
  have hsp4_eq : s4.sp = sp1 := hsp4.trans hsp3
  refine sepWPp_of_sepWP
    (Frame := A.pool ∗ A.live pKey 64 1 ∗ (sp1 ↦ₛ List.replicate 32 0#8) ∗
      memRegion (sp1 + 64#64) 32 ∗ Locals ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    (Pre := (pKey ↦ₛ List.replicate 64 0#8) ∗ (x.keyA ↦ₛ x.key) ∗ stackAt s4.sp 4096 ∗ emp)
    (Post := (pKey ↦ₛ k0) ∗ (x.keyA ↦ₛ x.key) ∗ stackAt sp1 4096)
    (PurePost := fun s7 => s7.sp = sp1 ∧ s7.spAligned = true ∧
      CalleeSavedPreserved (s4.writeReg64 .x22 pKey) s7 ∧
      s7.trace = s4.trace ∧ libcruxHmacLib.CodeLoaded haclMpl s7.mem ∧
      s7.readReg64 .x0 = 64#64 ∧ s7.readReg64 .x1 = 1#64)
    (by rw [hsp4_eq, hsp3]; exact Entails.of_eq (by dsimp only [pKey]; sep_ac_rfl))
    (sepWP_seq (Frame := emp) (Entails.of_eq (sepConj_emp _).symm)
      (hmac_key_prep_wp hP hsubs (hmacAux_toValid haux) (Frame := emp) hcl4 hpc4 hrun4 hsp_al4 rfl hpKey
        (hx23_4.trans hx23_1) (hx24_4.trans hx24_1) (hx25_4.trans hx25_1) hk_nat hk32)
      fun s5 hpc5 hrun5 ⟨hsp5, hsp_al5, hcs5, _, htr5, _, hcl5⟩ =>
        call_shim_6 hP haux 912 hcl5 hpc5 hrun5 hsp_al5
          fun s6 hpc6 hrun6 hsp6 hsp_al6 hcs6 _ htr6 hcl6 =>
            sepWP_seg6 hP hcl6 (Pre := emp) (Post := emp)
              (Frame := ((pKey ↦ₛ k0) ∗ (x.keyA ↦ₛ x.key) ∗ stackAt s4.sp 4096 ∗ emp) ∗ emp)
              (PurePost := fun sf => sf.sp = s6.sp ∧ CalleeSavedPreserved s6 sf ∧
                sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 1#64)
              (Entails.of_eq (emp_sepConj _).symm)
              (fun m => by
                have h := hmac_seg_alloc64_args_ipad (s := s6.setMem m) (R := emp)
                  (by cases s6; exact hpc6) (by cases s6; exact hrun6)
                cases s6; exact h)
              fun s7 hpc7 hrun7 _ htr7 _ hcl7 ⟨hsp7, hcs7, hx0_7, hx1_7⟩ =>
                SepWP.done hpc7 hrun7 ⟨⟨by rw [hsp7, hsp6, hsp5, hsp4_eq],
                  by unfold State.spAligned at hsp_al6 ⊢; rwa [hsp7],
                  (hcs5.trans hcs6).trans hcs7, by rw [htr7, htr6, htr5], hcl7, hx0_7, hx1_7⟩,
                  by rw [emp_sepConj, sepConj_emp, sepConj_emp, hsp4_eq]; exact Entails.refl _⟩)
    fun s7 hpc7 hrun7 ⟨hsp7, hsp_al7, hcs47, htr47, hcl7, hx0_7, hx1_7⟩ => ?_
  -- 4. alloc(64, 1) -> pIpad
  refine call_alloc_spqr_p6 hP haux halloc 924 64 2544
    ((pKey ↦ₛ k0) ∗ A.live pKey 64 1 ∗ (sp1 ↦ₛ List.replicate 32 0#8) ∗
     memRegion (sp1 + 64#64) 32 ∗ Locals ∗ (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl7 hpc7 hrun7 hsp_al7
    ⟨by rw [hx0_7]; decide, by rw [hx1_7]; decide, layoutOk_64_1⟩
    (by rw [hsp7]; exact Entails.of_eq (by sep_ac_rfl))
    (fun s8 m hpc8 hrun8 hp0 =>
      oom_seg_drop_regs (Q1 := fun sf => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = 64#64) <| by
      have h := hmac_seg_oom_ipad (s := s8.setMem m) (R := emp)
        (by cases s8; exact hpc8) (by cases s8; exact hrun8) (by cases s8; exact hp0)
      cases s8; exact h)
    (fun sf htrf => hQp sf (by rw [htr47, htr4, htr13] at htrf; exact htrf))
    fun s8 hpc8 hrun8 hsp8 hsp_al8 hcs8 htr8 hpIpad hcl8 => ?_
  -- 5. hmac_seg_ipad_xor + shim + alloc64_args_opad (+928 -> +1000)
  let pIpad := s8.readReg64 .x0
  have hcs48 := hcs47.trans hcs8
  rcases (CalleeSavedPreserved.iff_regs (s4.writeReg64 .x22 pKey) s8).mp hcs48 with
    ⟨hx19_8, hx20_8, hx21_8, hx22_8, _, _, _, hx26_8, hx27_8, hx28_8, _, hv_8⟩
  simp only [wp_norm] at hx19_8 hx20_8 hx21_8 hx22_8 hx26_8 hx27_8 hx28_8
  rw [calleeSavedVRegs_writeReg64] at hv_8
  have hsp8_eq : s8.sp = sp1 := hsp8.trans hsp7
  refine sepWPp_of_sepWP
    (Frame := A.pool ∗ stackAt sp1 4096 ∗ A.live pKey 64 1 ∗ A.live pIpad 64 1 ∗
      (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 64#64) 32 ∗ Locals ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    (Pre := (pKey ↦ₛ k0) ∗ memRegion pIpad 64)
    (Post := (pKey ↦ₛ k0) ∗ (pIpad ↦ₛ k0.map (· ^^^ 0x36#8)))
    (PurePost := fun s11 => s11.sp = sp1 ∧ s11.spAligned = true ∧
      CalleeSavedPreserved
        ((s8.writeReg64 .x23 pIpad).writeReg64 .x26 (s8.readReg64 .x26 >>> 32)) s11 ∧
      s11.trace = s8.trace ∧ libcruxHmacLib.CodeLoaded haclMpl s11.mem ∧
      s11.readReg64 .x0 = 64#64 ∧ s11.readReg64 .x1 = 1#64)
    (by rw [hsp7]; exact Entails.of_eq (by dsimp only [pIpad]; sep_ac_rfl))
    (sepWP_seg6 hP hcl8 (Pre := (pKey ↦ₛ k0) ∗ memRegion pIpad 64)
      (Post := (pKey ↦ₛ k0) ∗ (pIpad ↦ₛ k0.map (· ^^^ 0x36#8))) (Frame := emp)
      (PurePost := fun sf => sf.sp = s8.sp ∧
        CalleeSavedPreserved
          ((s8.writeReg64 .x23 pIpad).writeReg64 .x26 (s8.readReg64 .x26 >>> 32)) sf)
      (Entails.of_eq (sepConj_emp _).symm)
      (fun m => by
        have h := hmac_seg_ipad_xor (pKey := pKey) (pIpad := pIpad) (k0 := k0)
          (s := s8.setMem m) (R := emp) hk0
          (by cases s8; exact hpc8) (by cases s8; exact hrun8)
          (by cases s8; rfl) hpIpad (by cases s8; exact hx22_8)
        simpa only [sepConj_emp, State.sp_setMem, calleeSavedPreserved_write_setMem] using h)
      fun s9 hpc9 hrun9 _ htr9 _ hcl9 ⟨hsp9, hcs9⟩ =>
        call_shim_6 hP haux 988 hcl9 hpc9 hrun9
          (by unfold State.spAligned at hsp_al8 ⊢; rwa [hsp9])
          fun s10 hpc10 hrun10 hsp10 hsp_al10 hcs10 _ htr10 hcl10 =>
            sepWP_seg6 hP hcl10 (Pre := emp) (Post := emp)
              (Frame := ((pKey ↦ₛ k0) ∗ (pIpad ↦ₛ k0.map (· ^^^ 0x36#8))) ∗ emp)
              (PurePost := fun sf => sf.sp = s10.sp ∧ CalleeSavedPreserved s10 sf ∧
                sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 1#64)
              (Entails.of_eq (emp_sepConj _).symm)
              (fun m => by
                have h := hmac_seg_alloc64_args_opad (s := s10.setMem m) (R := emp)
                  (by cases s10; exact hpc10) (by cases s10; exact hrun10)
                cases s10; exact h)
              fun s11 hpc11 hrun11 _ htr11 _ hcl11 ⟨hsp11, hcs11, hx0_11, hx1_11⟩ =>
                SepWP.done hpc11 hrun11 ⟨⟨by rw [hsp11, hsp10, hsp9, hsp8_eq],
                  by unfold State.spAligned at hsp_al10 ⊢; rwa [hsp11],
                  (hcs9.trans hcs10).trans hcs11, by rw [htr11, htr10, htr9], hcl11,
                  hx0_11, hx1_11⟩,
                  by rw [emp_sepConj, sepConj_emp]; exact Entails.refl _⟩)
    fun s11 hpc11 hrun11 ⟨hsp11, hsp_al11, hcs811, htr811, hcl11, hx0_11, hx1_11⟩ => ?_
  -- 6. alloc(64, 1) -> pOpad
  refine call_alloc_spqr_p6 hP haux halloc 1000 64 2544
    ((pKey ↦ₛ k0) ∗ (pIpad ↦ₛ k0.map (· ^^^ 0x36#8)) ∗ A.live pKey 64 1 ∗ A.live pIpad 64 1 ∗
     (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 64#64) 32 ∗ Locals ∗
     (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
    hcl11 hpc11 hrun11 hsp_al11
    ⟨by rw [hx0_11]; decide, by rw [hx1_11]; decide, layoutOk_64_1⟩
    (by rw [hsp11]; exact Entails.of_eq (by sep_ac_rfl))
    (fun s12 m hpc12 hrun12 hp0 =>
      oom_seg_drop_regs (Q1 := fun sf => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = 64#64) <| by
      have h := hmac_seg_oom_opad (s := s12.setMem m) (R := emp)
        (by cases s12; exact hpc12) (by cases s12; exact hrun12) (by cases s12; exact hp0)
      cases s12; exact h)
    (fun sf htrf => hQp sf (by rw [htr811, htr8, htr47, htr4, htr13] at htrf; exact htrf))
    fun s12 hpc12 hrun12 hsp12 hsp_al12 hcs12 htr12 hpOpad hcl12 => ?_
  -- 7. hmac_core_1004_to_2140_wp (+1004 -> +2140)
  let pOpad := s12.readReg64 .x0
  have hcs812 := hcs811.trans hcs12
  rcases (CalleeSavedPreserved.iff_regs
      ((s8.writeReg64 .x23 pIpad).writeReg64 .x26 (s8.readReg64 .x26 >>> 32)) s12).mp hcs812 with
    ⟨hx19_12, hx20_12, hx21_12, hx22_12, hx23_12, _, _, hx26_12, hx27_12, hx28_12, _, hv_12⟩
  simp only [wp_norm] at hx19_12 hx20_12 hx21_12 hx22_12 hx23_12 hx26_12 hx27_12 hx28_12
  rw [calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg64] at hv_12
  have hx26_12_eq : s12.readReg64 .x26 = BitVec.ofNat 64 x.data.length := by
    rw [hx26_12, hx26_8, hx26_4, hx26_1,
        tryFromDataNiche_lsr32 dataLenBV (by omega), hd_bv]
  have hsp12_eq : s12.sp = sp1 := hsp12.trans hsp11
  refine sepWPp_of_sepWP
    (Frame := A.pool ∗ A.live pKey 64 1 ∗ A.live pIpad 64 1 ∗ A.live pOpad 64 1 ∗
      Locals ∗ (x.keyA ↦ₛ x.key) ∗ Frame)
    (by rw [hsp12_eq, hsp11]; exact Entails.of_eq (by dsimp only [pOpad, k0]; sep_ac_rfl))
    (hmac_core_1004_to_2140_wp hP hsubs (Frame := emp) hd32 hcl12 hpc12 hrun12 hsp_al12 rfl hpOpad
      (by rw [hx20_12, hx20_8, hx20_4, hx20_1])
      (by rw [hx21_12, hx21_8, hx21_4, hx21_1, hd_bv])
      (hx22_12.trans hx22_8) hx23_12 hx26_12_eq)
    fun s13 hpc13 hrun13 ⟨hsp13, hsp_al13, hcr13, _, htr12_13, _, hcl13⟩ => ?_
  -- 8. hmac_spqr_tail_wpp (+2140 -> ret / OOM panic)
  have hsp13_eq : s13.sp = sp1 := hsp13.trans hsp12_eq
  rcases hcr13 with ⟨hcr19, hcr22, hcr23, hcr24, hcr27, hcr28, hcrv⟩
  simp only [wp_norm] at hcr19 hcr22 hcr23 hcr24 hcr27 hcr28
  rw [calleeSavedVRegs_writeReg64] at hcrv
  have htr_s13 : s13.trace = s1.trace := by
    rw [htr12_13, htr12, htr811, htr8, htr47, htr4, htr13]
  refine sepWPp_congr_pre
    (by rw [sepConj_emp, hsp12_eq]; exact Entails.of_eq (by dsimp only [Locals]; sep_ac_rfl)) <|
    hmac_spqr_tail_wpp hP haux halloc (x := x)
      (pKey := pKey) (pIpad := pIpad) (pOpad := pOpad) (pad152 := pad152) (s0 := s0)
      (Frame := (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ Frame)
      hcl13 hpc13 hrun13 hsp13_eq hsp_al13 hsp0
      ⟨by rw [hcr19, hx19_12, hx19_8, hx19_4, hx19_1],
       by rw [hcr22, hx22_12, hx22_8],
       hcr23.trans hx23_12,
       hcr24,
       by rw [hcr27, hx27_12, hx27_8, hx27_4, hx27_1],
       by rw [hcr28, hx28_12, hx28_8, hx28_4, hx28_1],
       by rw [hcrv, hv_12, hv_8, hv_4, hv_1]⟩
      (fun sf htrf => hQp sf (by rwa [htr_s13] at htrf))
      fun sf P' hspf hcsf htrf hent =>
        hQ sf P' hspf hcsf (htrf.trans htr_s13)
          (Entails.trans hent (Entails.of_eq (by sep_ac_rfl)))

/-- Ambient-program `subroutine_ok` for Block `6` (`libcrux_hmac::hmac`, `w0 = 0` SHA-256)
discharging `withHaclCodeLoaded mpl (libcruxHmacSpec sha256CompressState A)`. -/
theorem libcruxHmac_spqr_withHaclCodeLoaded_subroutineOk
    {A : RustAlloc} {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hsubs : HaclSubroutinesTrace P mpl)
    (haux : HmacAuxSubroutines P mpl)
    (halloc : HmacAllocSubroutines A P mpl) :
    subroutine_ok P (mpl.base 6)
      (withHaclCodeLoaded mpl (libcruxHmacSpec sha256CompressState A)) := by
  let _ : HaclPlacement := ⟨mpl, hP.placeable⟩
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre0 hsp0
  dsimp only [withHaclCodeLoaded, libcruxHmacSpec] at hpre0
  simp only [sepConj_assoc] at hpre0
  rw [satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨hcl0, hpre0⟩
  rw [satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8, hw0, hx1, hx2, hx3, hx4, hw5, hx6⟩, hm0⟩
  refine ⟨(x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
    A.pool ∗ stackAt s0.sp extHookStack, R,
    by simpa only [sepConj_assoc] using hm0, ?_⟩
  let sp1 := s0.sp - 224#64
  refine sepWPp_seg6 hP hcl0
    (mid := if 2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat then
      mpl.base 6 + 2592#64 else mpl.base 6 + 252#64)
    (Pre := stackAt s0.sp 224)
    (Post := hmacPrologueSpatial s0)
    (Frame := (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
      A.pool ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
    (PurePost := hmacProloguePure s0)
    (by
      unfold extHookStack; dsimp only [Nat.reducePow]
      rw [stackAt_split_hmac s0.sp]
      exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
    (fun m => by
      have h := hmac_seg_prologue (s0 := s0.setMem m)
        (by cases s0; exact hpc0) (by cases s0; exact hrun0) (by cases s0; exact hsp0)
        (by cases s0; exact hw0) (by cases s0; exact hw5) (by cases s0; exact hx6)
      cases s0; exact h)
    fun s1 hpc1 hrun1 _ htr1 _ hcl1 hpure1 => ?_
  by_cases hovf : 2 ^ 32 ≤ x.key.length ∨ 2 ^ 32 ≤ x.data.length
  · have hcond : 2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat := by
      rwa [hx2, hx4]
    simp only [hcond, ↓reduceIte] at hpc1
    have hsp1 : s1.sp = sp1 := hpure1.1
    have hsp_al1 : s1.spAligned = true := by
      unfold State.spAligned; rw [hsp1]; exact State.spAligned_sub s0 224#64 hsp0
    refine hmac_unwrap_panic_wpp hP haux hcl1 hpc1 hrun1 hsp_al1
      (Rest := (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
        memRegion (sp1 + 96#64) 32 ∗ (∃∗ p, hmacSavedCalleeRegs sp1 s0 p) ∗
        (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
        A.pool ∗ stackAt (s0.sp - 4320#64) 12064)
      (by
        dsimp only [hmacPrologueSpatial]
        rw [hsp1]
        exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl))
      fun sf htrf hmR => ?_
    dsimp only [withHaclCodeLoaded, libcruxHmacSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨Or.inr hovf, by rw [htrf, htr1]⟩, hmR⟩
  · have hk32 : x.key.length < 2 ^ 32 := by omega
    have hd32 : x.data.length < 2 ^ 32 := by omega
    have hcond : ¬(2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat) := by
      rw [hx2, hx4]; exact hovf
    simp only [hcond, ↓reduceIte] at hpc1
    rcases hpure1 with ⟨hsp1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1,
      hx27_1, hx28_1, hv_1, hx26_fn⟩
    have hx26_1 : s1.readReg64 .x26 = tryFromDataNiche (s0.readReg64 .x4) :=
      hx26_fn (hx2.symm ▸ hk32) (hx4.symm ▸ hd32)
    refine sepWPp_congr_pre
      (P2 := (∃∗ pad152 : BitVec 64, hmacSavedCalleeRegs sp1 s0 pad152) ∗
        ((sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
         memRegion (sp1 + 64#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
         (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
         A.pool ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064))
      (by
        dsimp only [hmacPrologueSpatial]
        exact Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl)) ?_
    refine sepWPp_exists_elim fun pad152 => ?_
    refine sepWPp_congr_pre
      (P2 := (sp1 ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp1 + 32#64) 32 ∗
        memRegion (sp1 + 64#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗
        hmacSavedCalleeRegs sp1 s0 pad152 ∗
        (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
        A.pool ∗ stackAt sp1 4096 ∗ stackAt (s0.sp - 4320#64) 12064)
      (Entails.of_eq (by dsimp only [sp1]; sep_ac_rfl)) ?_
    refine hmac_spqr_valid_wpp hP hsubs haux halloc (s0 := s0) (pad152 := pad152)
      (Frame := stackAt (s0.sp - 4320#64) 12064)
      hk32 hd32 hx2 hx4 hcl1 hpc1 hrun1 hsp0 hsp1
      ⟨hx19_1.trans hx8, hx20_1.trans hx3, hx21_1, hx23_1, hx24_1.trans hx1,
       hx25_1, hx26_1, hx27_1, hx28_1, hv_1⟩
      (fun sf htrf => ?_)
      fun sf P' hspf hcsf htr_val hent => ?_
    · intro hmR
      rw [htr1] at htrf
      rcases allocFailedIn_of_append htrf with ⟨hfail, hpref⟩
      dsimp only [withHaclCodeLoaded, libcruxHmacSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨Or.inl hfail, hpref⟩, hmR⟩
    · refine ⟨fun hmf => ?_, hspf, hcsf⟩
      dsimp only [withHaclCodeLoaded, libcruxHmacSpec]
      have hpost_ent :
          P' ⊢
          (⌜x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧ sf.trace = s0.trace⌝ ∗
           (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
           vecU8 A x.ret (hmacWith sha256CompressState x.key x.data) ∗
           A.pool ∗ stackAt s0.sp extHookStack) := by
        have hpure_f : x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧ sf.trace = s0.trace :=
          ⟨hk32, hd32, htr_val.trans htr1⟩
        refine Entails.trans hent (Entails.trans (Entails.of_eq ?_)
          (Entails.pure_right hpure_f (Entails.refl _)))
        unfold extHookStack; dsimp only [Nat.reducePow]
        rw [stackAt_split_hmac s0.sp]
      exact Satisfies.mono (sepConj_mono_left hpost_ent) hmf

/-- Ambient-program `subroutine_ok` for Block `6` (`libcrux_hmac::hmac`, `w0 = 0` SHA-256)
discharging `libcruxHmacSpec sha256CompressState A` when `P.CodeLoaded` implies
`libcruxHmacLib.CodeLoaded mpl`. -/
theorem libcruxHmac_spqr_subroutineOk
    {A : RustAlloc} {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hCL : ∀ m : Memory, P.CodeLoaded m → libcruxHmacLib.CodeLoaded mpl m)
    (hsubs : HaclSubroutinesTrace P mpl)
    (haux : HmacAuxSubroutines P mpl)
    (halloc : HmacAllocSubroutines A P mpl) :
    subroutine_ok P (mpl.base 6) (libcruxHmacSpec sha256CompressState A) :=
  subroutine_ok_of_withHaclCodeLoaded hCL
    (libcruxHmac_spqr_withHaclCodeLoaded_subroutineOk hP hsubs haux halloc)

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmac
