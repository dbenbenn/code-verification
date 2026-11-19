/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hmac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Mac.MacCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
import LibsignalBinary.Proofs.TripleRatchet.Mac.Compute
import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddresses
import ProofLib.SepLogic.WPFrozen

/-!
# Top-Level Composition for `<SignalMessage>::verify_mac_with_addresses`

Composes `serialize_addresses`, `compute_mac`, and `VerifyMacWithAddresses` into top-level
`subroutine_ok` contracts on `tripleRatchetProgAt`, `tripleRatchetProgAtExt`, and
`[LibsignalPlacement]`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

private theorem ls_subroutine_ok_lscl_of_block [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

theorem verifyMacWithAddresses_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (parse : UuidParser)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpec)
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked)
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A parse)) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_placed_ok_of_compute C A parse H
    hdealloc hbb_raw
    (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok hparse hshim halloc hpanic))
    (ls_subroutine_ok_lscl_of_block (computeMac_placed_ok C A H hnew hpk hmemcpy hcompress hdealloc hmemset))

theorem verifyMacWithAddresses_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec extHookStack)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecX A)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym)
      (withStack blackBoxU8Spec extHookStack))
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked)
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpecX C.F A uuidTryParse)) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_placed_ok_of_compute_x C A uuidTryParse H
    hdealloc hbb_raw
    (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok_x hparse hshim halloc hpanic))
    (ls_subroutine_ok_lscl_of_block (computeMac_placed_ok_x C A H hnew hpk hmemcpy hcompress hdealloc hmemset))

theorem verifyMacWithAddresses_placed_cro_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (parse : UuidParser)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpec A)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpec)
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked)
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A parse)) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_placed_cro_ok_of_compute C A parse H
    hdealloc hbb_raw
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok hparse hshim halloc hpanic)))
    (keys_ls_subroutine_ok_of_block_cro (computeMac_placed_cro_ok C A H hnew hpk hmemcpy hcompress hdealloc hmemset))

end CryptoVerification.LibsignalTripleRatchet

