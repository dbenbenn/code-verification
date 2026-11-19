/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegsExact -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Proofs.CodeLayout

/-!
# `HookSat` Relocatable Verification of `extract`

Establishes `ExtractPlacedOkSat` for `GenericHkdf<Hmac<Sha256>>::extract` under
`[HkdfPlacedHooksExactSat C.F H]` with `1152`-B `extractStackSat` (`976 + 176` B `compress256` slack).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (ExtractGhost RW RunsTo blkPC_54 blkPl_54 effectiveSalt extPlacedFakeB finPlacedFakeB)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HkdfPlacedHooksExactSat extractSpecSat newFromSliceSpecSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegsExact
  (EC88Sat EFinPlacedSat EMemcpyPlacedSat ERetFinSat extract_placed_ok_exact
   extract_placed_ok_of_inv_exact extract_placed_ok_of_plain_exact fin_placed_runsTo_s2
   seg1b_placed_runsTo_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat
  (FinPostSat FinPreSat finalize_fixed_placed_runsTo_of_other_block_sat)

section SegmentsPlacedSat

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}

theorem seg1b_placed_runsTo_sat [hH : HkdfPlacedHooksExactSat C.F H]
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 720#64) 1152)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hikm_len : x.ikm.length = 32)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 720#64) 1152)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyPlacedSat C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EC88Sat extPlacedFakeB C.F x s0 sp0) :=
  seg1b_placed_runsTo_exact hH.memcpy
    hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs

end SegmentsPlacedSat

/-- `1152`-B stack `HookSat` separation-logic contract for `GenericHkdf<Hmac<Sha256>>::extract` (Block `54`). -/
public abbrev ExtractPlacedOkSat [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
    (withLsCodeLoaded lsmpl (extractSpecSat C.F))

public theorem extract_placed_ok_of_inv_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [hH : HkdfPlacedHooksExactSat C.F H]
    {Inv : Memory → Prop}
    (hInv_kf : ∀ {m1 m2 : Memory}, Inv m1 → m1.KeepsFrozen m2 → Inv m2)
    (hInv_cl : ∀ {m : Memory}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpecSat C.F with pre := fun x s0 => (newFromSliceSpecSat C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ }) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
      { extractSpecSat C.F with pre := fun x s0 => (extractSpecSat C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ } :=
  extract_placed_ok_of_inv_exact C H hH.memcpy
    (fun hcl hpre => finalize_fixed_placed_runsTo_of_other_block_sat (C := C) (H := H) hcl hpre)
    hInv_kf hInv_cl hNfs

public theorem extract_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [hH : HkdfPlacedHooksExactSat C.F H]
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpecSat C.F))) :
    ExtractPlacedOkSat C H :=
  extract_placed_ok_exact C H hH.memcpy
    (fun hcl hpre => finalize_fixed_placed_runsTo_of_other_block_sat (C := C) (H := H) hcl hpre)
    hNfs

public theorem extract_placed_ok_withLsCodeLoaded_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactSat C.F H]
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpecSat C.F))) :
    ExtractPlacedOkSat C H :=
  extract_placed_ok_sat C H hNfs

public theorem extract_placed_ok_of_plain_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [hH : HkdfPlacedHooksExactSat C.F H]
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (newFromSliceSpecSat C.F)) :
    ExtractPlacedOkSat C H :=
  extract_placed_ok_of_plain_exact C H hH.memcpy
    (fun hcl hpre => finalize_fixed_placed_runsTo_of_other_block_sat (C := C) (H := H) hcl hpre)
    hNfs

end LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSat
