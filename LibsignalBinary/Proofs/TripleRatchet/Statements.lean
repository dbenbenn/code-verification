/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Root -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Compute -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Verify -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddresses -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchet
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKey
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeys
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepMain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecv
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMac
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Root
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main
import LibsignalBinary.Proofs.TripleRatchet.Record.SegClone
import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Core
import LibsignalBinary.Proofs.TripleRatchet.Wire.New

/-!
# Top-Level Binary Refinement Theorems for Triple-Ratchet Session Entry Points

Composes the assembled subroutine and region proofs to establish the top-level specifications of
`Specifications/LibsignalTripleRatchet.lean` for session encryption (`otrFrom_run`, `otrEncrypt_run`,
`otrApply_run`), message parsing (`tryFrom_run`), state and record decryption (`tryDecrypt_run`,
`recordDecrypt_run`), and their empty-state and SPQR v1 specializations.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Statements

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

instance instHkdfHooks_trap (C : Crypto) (abs : String → Option (State → State)) :
    HkdfHooks C.F (trTrapExterns C abs) where
  memset := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact HkdfHooks.memset (F := C.F) (ext := tripleRatchetExterns C 0#64 abs)
  memcpy := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact HkdfHooks.memcpy (F := C.F) (ext := tripleRatchetExterns C 0#64 abs)
  compress256 := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact HkdfHooks.compress256 (F := C.F) (ext := tripleRatchetExterns C 0#64 abs)

section Ext32Statements

open CryptoVerification.InImageLift
open ProofLib.ProgramReflection

/-- Lift `uuidTryParseCodeSpec uuidTryParse` (`uuidTryParseStack` = 192 B) to
`withStack (uuidTryParseSpec uuidTryParse) hookStack` for `192 ≤ hookStack ≤ 2^64`. -/
theorem uuidTryParseWithStack_of_code {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h : subroutine_ok P addr (uuidTryParseCodeSpec uuidTryParse))
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (withStack (uuidTryParseSpec uuidTryParse) hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗
        stackAt s0.sp uuidTryParseStack := by
    have h1 := stackAt_split_bottom s0.sp uuidTryParseStack (hookStack - uuidTryParseStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R
  have hpre' : s0.mem ⊨ (uuidTryParseCodeSpec uuidTryParse).pre (p, bs, out) s0 ∗ R' := by
    dsimp only [withStack, uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (p, bs, out) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · rcases hpan with ⟨_, hpan_sat⟩
    have h0 : (uuidTryParseCodeSpec uuidTryParse).onPanic (p, bs, out) s0 sf = ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hpan_sat
    exact False.elim hpan_sat.1
  · rcases hex with ⟨code, _, hex_sat⟩ | ⟨_, hoom_sat⟩
    · have h0 : (uuidTryParseCodeSpec uuidTryParse).onExit (p, bs, out) code s0 sf = ⌜False⌝ := rfl
      rw [h0, satisfies_pure_sepConj] at hex_sat
      exact False.elim hex_sat.1
    · have h0 : (uuidTryParseCodeSpec uuidTryParse).onOom (p, bs, out) s0 sf = ⌜False⌝ := rfl
      rw [h0, satisfies_pure_sepConj] at hoom_sat
      exact False.elim hoom_sat.1

/-- Callee stack budget inside `compute_mac` when `Hmac<Sha256>::new_from_slice` also uses
`extHookStack` (`544 + 16384 = 16928` B). -/
abbrev computeMacPkStackExt32 : Nat := newFromSliceStack + extHookStack

/-- Total `compute_mac` stack budget (`16928 + 496 = 17424` B) under stacked `new_from_slice`. -/
abbrev computeMacStackExt32 : Nat := computeMacPkStackExt32 + 496

private theorem stackAt_16928_eq_16416 (sp : BitVec 64) :
    stackAt sp computeMacPkStackExt32 =
      stackAt sp publicKeySerializeStackX ∗ memRegion (sp - 16928#64) 512 := by
  simp only [stackAt, computeMacPkStackExt32, newFromSliceStack, publicKeySerializeStackX, extHookStack]
  rw [show (544 + 2 ^ 14 : Nat) = 512 + (2 ^ 14 + 32) by decide,
    memRegion_split _ 512 (2 ^ 14 + 32) (by decide)]
  have e1 : sp - BitVec.ofNat 64 (512 + (2 ^ 14 + 32)) = sp - 16928#64 := by bv_arith
  have e2 : sp - 16928#64 + BitVec.ofNat 64 512 = sp - BitVec.ofNat 64 (2 ^ 14 + 32) := by bv_arith
  rw [e1, e2, sepConj_comm]

private theorem stackAt_16928_eq_16384 (sp : BitVec 64) :
    stackAt sp computeMacPkStackExt32 =
      stackAt sp extHookStack ∗ memRegion (sp - 16928#64) 544 := by
  simp only [stackAt, computeMacPkStackExt32, newFromSliceStack, extHookStack]
  rw [memRegion_split _ 544 (2 ^ 14) (by decide)]
  have e1 : sp - BitVec.ofNat 64 (544 + 2 ^ 14) = sp - 16928#64 := by bv_arith
  have e2 : sp - 16928#64 + BitVec.ofNat 64 544 = sp - BitVec.ofNat 64 (2 ^ 14) := by bv_arith
  rw [e1, e2, sepConj_comm]

end Ext32Statements

end CryptoVerification.LibsignalTripleRatchet.Statements
