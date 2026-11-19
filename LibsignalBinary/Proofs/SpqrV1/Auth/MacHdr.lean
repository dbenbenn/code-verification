/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.Repr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Auth.SpqrAuthCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import

/-!
# `<spqr::authenticator::Authenticator>::mac_hdr`

Verifies `<spqr::authenticator::Authenticator>::mac_hdr` (`0x5e068`, block 342):
concatenates `[Authenticator.hdrLabel, toBEBytes 8 ep, hdr]` via `slice::Concat::concat`,
computes HMAC-SHA256 truncated to 32 bytes (`self.macHdrUnchecked F ep hdr`) via
`libcrux_hmac::hmac`, and deallocates the temporary buffer.
-/

public section

namespace CryptoVerification.SpqrV1.Layout.L25

open Lean Meta Elab Term Command Tactic ProofLib ProofLib.CodeLookup
open CryptoVerification.CodeLayout

scoped elab (name := codeFetchesLenMacHdr) "code_fetches_len " codeId:ident decPrefix:ident b:term:max H:term:max sym:str len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← lookup codeName .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offStx := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches $codeId $decPrefix $b $H $hfn $offStx $len))

end CryptoVerification.SpqrV1.Layout.L25

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L25
open DoReserveNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Specifications and Fixed-Image Proof -/

/-- Stack budget of `Authenticator::mac_hdr` (`112 + extHookStack`). -/
abbrev authMacHdrStackX : Nat := 112 + extHookStack

/-- Pinned ghost arguments for `Authenticator::mac_hdr`. -/
structure AuthMacHdrPinnedGhost where
  /-- Sret pointer (`x8`, 24-byte `Vec<u8>` output `Mac`). -/
  outVec : BitVec 64
  /-- `&Authenticator` pointer (`x0`, 48 bytes). -/
  selfA : BitVec 64
  /-- Ghost `(cap, ptr)` pins of `self`. -/
  g : AuthenticatorGhost
  auth : Authenticator
  /-- Epoch (`x1`, `u64`). -/
  ep : Epoch
  /-- Whether `hdr` is read-only (`true`) or read-write (`false`). -/
  hdrRO : Bool
  /-- `hdr: &[u8]` pointer (`x2`). -/
  hdrA : BitVec 64
  /-- `hdr: &[u8]` contents (`x3 = hdr.length`). -/
  hdr : Bytes

/-- Unpinned ghost arguments for `Authenticator::mac_hdr`. -/
structure AuthMacHdrGhost where
  /-- Sret pointer (`x8`, 24-byte `Vec<u8>` output `Mac`). -/
  outVec : BitVec 64
  /-- `&Authenticator` pointer (`x0`, 48 bytes). -/
  selfA : BitVec 64
  auth : Authenticator
  /-- Epoch (`x1`, `u64`). -/
  ep : Epoch
  /-- Whether `hdr` is read-only (`true`) or read-write (`false`). -/
  hdrRO : Bool
  /-- `hdr: &[u8]` pointer (`x2`). -/
  hdrA : BitVec 64
  /-- `hdr: &[u8]` contents (`x3 = hdr.length`). -/
  hdr : Bytes

/-- Pinned specification of `<spqr::authenticator::Authenticator>::mac_hdr` (`0x5e068`):
writes `vecU8 A outVec (auth.macHdrUnchecked F ep hdr)` on normal return, or panics on
OOM / `u32` HMAC input length overflow. -/
@[expose] def authMacHdrPinnedSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthMacHdrPinnedGhost where
  pre x s :=
    ⌜s.readReg64 .x8 = x.outVec ∧ s.readReg64 .x0 = x.selfA ∧
      s.readReg64 .x1 = x.ep ∧ s.readReg64 .x2 = x.hdrA ∧
      s.readReg64 .x3 = BitVec.ofNat 64 x.hdr.length ∧
      41 + x.hdr.length < 2 ^ 63⌝ ∗
      memRegion x.outVec 24 ∗
      authenticatorPinAt A x.g x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool ∗ stackAt s.sp authMacHdrStackX
  post x s0 sf :=
    ⌜x.auth.macHdr F x.ep x.hdr = .ok (x.auth.macHdrUnchecked F x.ep x.hdr) ∧
      sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (x.auth.macHdrUnchecked F x.ep x.hdr) ∗
      authenticatorPinAt A x.g x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool ∗ stackAt s0.sp authMacHdrStackX
  onPanic x s0 sf :=
    ⌜(allocFailedIn s0 sf ∨
      2 ^ 32 ≤ x.auth.macKey.length ∨
      2 ^ 32 ≤ (Authenticator.hdrLabel ++ toBEBytes 8 x.ep ++ x.hdr).length) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned specification of `Authenticator::mac_hdr`. -/
@[expose] def authMacHdrSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthMacHdrGhost where
  pre x s :=
    ⌜s.readReg64 .x8 = x.outVec ∧ s.readReg64 .x0 = x.selfA ∧
      s.readReg64 .x1 = x.ep ∧ s.readReg64 .x2 = x.hdrA ∧
      s.readReg64 .x3 = BitVec.ofNat 64 x.hdr.length ∧
      41 + x.hdr.length < 2 ^ 63⌝ ∗
      memRegion x.outVec 24 ∗
      authenticatorAt A x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool ∗ stackAt s.sp authMacHdrStackX
  post x s0 sf :=
    ⌜x.auth.macHdr F x.ep x.hdr = .ok (x.auth.macHdrUnchecked F x.ep x.hdr) ∧
      sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (x.auth.macHdrUnchecked F x.ep x.hdr) ∗
      authenticatorAt A x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool ∗ stackAt s0.sp authMacHdrStackX
  onPanic x s0 sf :=
    ⌜(allocFailedIn s0 sf ∨
      2 ^ 32 ≤ x.auth.macKey.length ∨
      2 ^ 32 ≤ (Authenticator.hdrLabel ++ toBEBytes 8 x.ep ++ x.hdr).length) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

namespace MacHdrFacts

@[simp] theorem hdrLabel_length :
    Authenticator.hdrLabel.length = 33 := by decide

theorem macHdrUnchecked_eq_hmacWith (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) :
    self.macHdrUnchecked F ep hdr =
      hmacWith F self.macKey (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr) := by
  unfold Authenticator.macHdrUnchecked Authenticator.macSize
  exact List.take_of_length_le (by rw [length_hmacWith])

/-- Splits `stackAt sp authMacHdrStackX` into the `ct_mac_data` `Vec<u8>` sret (`[sp - 112, sp - 88)`),
the `[&[u8]; 3]` slice array (`[sp - 88, sp - 40)`), `ep.to_be_bytes()` (`[sp - 40, sp - 32)`),
and four callee-saved registers (`[sp - 32, sp)`). -/
theorem stackAt_authMacHdrX_split (sp : BitVec 64) :
    stackAt sp authMacHdrStackX =
      stackAt (sp - 112#64) extHookStack ∗
        memRegion (sp - 112#64) 24 ∗
        (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
         ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
          ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
          ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
          ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5)) ∗
        (∃∗ e0 : BitVec 64, (sp - 40#64) ↦₆₄ e0) ∗
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
          ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3)) := by
  change memRegion (sp - BitVec.ofNat 64 16496) 16496 =
    memRegion (sp - 112#64 - BitVec.ofNat 64 16384) 16384 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16496) (n := 16384) (k := 112)
      (b' := sp - 112#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 112#64) (n := 24) (k := 88)
      (b' := sp - 88#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 88#64) (n := 48) (k := 40)
      (b' := sp - 40#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32)
      (b' := sp - 32#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16496) 16384 ∗
    (memRegion (sp - 112#64) 24 ∗
      (memRegion (sp - 88#64) (8 * 6) ∗
        (memRegion (sp - 40#64) 8 ∗ memRegion (sp - 32#64) (8 * 4)))) = _
  rw [ProofLib.memRegion_cells (sp - 88#64) 6 (by decide),
    ProofLib.memRegion_eight (sp - 40#64),
    ProofLib.memRegion_cells (sp - 32#64) 4 (by decide)]
  have hsub : sp - 112#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16496 := by bv_kernel
  have hc6 : cells (sp - 88#64) 6 =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
        ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
        ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5)) := by
    cells_unfold
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
        ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3)) := by
    cells_unfold
  rw [hsub, hc6, hc4]

/-- Reassembles the `mac_hdr` frame back into `stackAt sp authMacHdrStackX`. -/
theorem rejoin_stack_authMacHdrX (sp : BitVec 64)
    (v0 v1 v2 : BitVec 64)
    (s0 s1 s2 s3 s4 s5 : BitVec 64)
    {beBytes : List (BitVec 8)} (hbe : beBytes.length = 8)
    (c0 c1 c2 c3 : BitVec 64) :
    stackAt (sp - 112#64) extHookStack ∗
      ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
      ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
      ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
      ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5) ∗
      ((sp - 40#64) ↦ₛ beBytes) ∗
      ((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
      ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3) ⊢
      stackAt sp authMacHdrStackX := by
  have heq : stackAt sp authMacHdrStackX =
      stackAt (sp - 112#64) extHookStack ∗
        cells (sp - 112#64) 9 ∗
        memRegion (sp - 40#64) 8 ∗
        cells (sp - 32#64) 4 := by
    change memRegion (sp - BitVec.ofNat 64 16496) 16496 =
      memRegion (sp - 112#64 - BitVec.ofNat 64 16384) 16384 ∗ _
    rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16496) (n := 16384) (k := 112)
        (b' := sp - 112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 112#64) (n := 72) (k := 40)
        (b' := sp - 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide)]
    change memRegion (sp - BitVec.ofNat 64 16496) 16384 ∗
      (memRegion (sp - 112#64) (8 * 9) ∗
        (memRegion (sp - 40#64) 8 ∗ memRegion (sp - 32#64) (8 * 4))) = _
    rw [ProofLib.memRegion_cells (sp - 112#64) 9 (by decide),
      ProofLib.memRegion_cells (sp - 32#64) 4 (by decide)]
    have hsub : sp - 112#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16496 := by bv_kernel
    rw [hsub]
  rw [heq]
  have hc9 :
      (((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
       ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
       ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
       ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5)) ⊢ cells (sp - 112#64) 9 := by
    cells_unfold
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right s0 (Entails.sepExists_right s1 (Entails.sepExists_right s2
        (Entails.sepExists_right s3 (Entails.sepExists_right s4
          (Entails.sepExists_right s5 (Entails.refl _)))))))))
  have hmbe : ((sp - 40#64) ↦ₛ beBytes) ⊢ memRegion (sp - 40#64) 8 :=
    hbe ▸ pointsToBytes_entails_memRegion (sp - 40#64) beBytes
  have hc4 :
      (((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
       ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3)) ⊢ cells (sp - 32#64) 4 := by
    cells_unfold
    exact Entails.sepExists_right c0 (Entails.sepExists_right c1
      (Entails.sepExists_right c2 (Entails.sepExists_right c3 (Entails.refl _))))
  have hgroup :
      stackAt (sp - 112#64) extHookStack ∗
        ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
        ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
        ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
        ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5) ∗
        ((sp - 40#64) ↦ₛ beBytes) ∗
        ((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
        ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3) =
      stackAt (sp - 112#64) extHookStack ∗
        (((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
         ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
         ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
         ((sp - 56#64) ↦₆₄ s4) ∗ ((sp - 48#64) ↦₆₄ s5)) ∗
        ((sp - 40#64) ↦ₛ beBytes) ∗
        (((sp - 32#64) ↦₆₄ c0) ∗ ((sp - 24#64) ↦₆₄ c1) ∗
         ((sp - 16#64) ↦₆₄ c2) ∗ ((sp - 8#64) ↦₆₄ c3)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right (sepConj_mono hc9 (sepConj_mono hmbe hc4))

theorem onPanic_concat_entails_macHdr {s0 s sf : State} {P1 P2 : Prop} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(allocFailedIn s0 sf ∨ P1 ∨ P2) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  refine Entails.pure_left fun ⟨haf, hpref⟩ => ?_
  exact Entails.pure_right ⟨Or.inl haf, hpref⟩ (entails_anyHeap _)

theorem onPanic_hmac_entails_macHdr {s0 s sf : State} {P1 P2 : Prop} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜(allocFailedIn s sf ∨ P1 ∨ P2) ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(allocFailedIn s0 sf ∨ P1 ∨ P2) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

open Lean Elab Tactic in
elab "wpp_call_inImage_concat_macHdr " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_inImage_mid $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_inImage_concat_macHdr: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_concat_entails_macHdr (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
elab "wpp_call_inImage_hmac_macHdr " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (NextKeyInternalFacts.SepWPp.call_allowPanic_inImage_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_inImage_hmac_macHdr: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR'
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm, *]
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_hmac_entails_macHdr (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

end MacHdrFacts

open MacHdrFacts
open NextKeyInternalFacts
open AgreeStateSimp

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length hdrLabel_length
theorem SepWPp.pure_left_focus {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post post_err : State → SepProp → Prop} (φ : Prop)
    (hf : P = ⌜φ⌝ ∗ P')
    (h : φ → SepWPp prog pc s P' post post_err) :
    SepWPp prog pc s P post post_err := by
  intro R hm hL
  rw [hf, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact (h hm.1) R hm.2 hL

theorem rodata_hdrLabel_placed [LibsignalPlacement] {m : Memory}
    (hF : LsCallInv lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ "spqr:.rodata..Lanon.140") ↦ᵣ Authenticator.hdrLabel) ∗ P :=
  lsro_intro_chk hF.1 (by decide +kernel) hP

open Lean Elab Tactic in
elab "wpp_call_lsCallInv_concat_macHdr " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_lsCallInv_mid $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_lsCallInv_concat_macHdr: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_concat_entails_macHdr (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
elab "wpp_call_lsCallInv_hmac_macHdr " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_lsCallInv_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_lsCallInv_hmac_macHdr: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR'
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm, *]
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_hmac_entails_macHdr (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

set_option maxHeartbeats 1600000 in
/-- Block 342 (`Authenticator::mac_hdr`) meets `withLsCallInv lsmpl (authMacHdrPinnedSpec F A)`. -/
theorem authMacHdrPinned_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat3Spec A)))
    (h_hmac : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac")
      (withLsCallInv lsmpl (libcruxHmacSpec F A)))
    (h_dealloc : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack)) :
    subroutine_ok ((blkPC_342).rebase (blkPl_342).base H) (blkPl_342).base
      (withLsCallInv lsmpl (authMacHdrPinnedSpec F A)) := by
  refine subroutine_ok_withLsCallInv_rodata1_keep rodata_hdrLabel_placed ?_
  wpp_init x s0
  rcases x with ⟨outVec, selfA, g, auth, ep, hdrRO, hdrA, hdr⟩
  dsimp only [authMacHdrPinnedSpec] at hpre h_1 h_2 h_3 h_4 h_5 h_6 h ⊢
  have hinv0 : LsCallInv lsmpl s0.mem := h_1
  subst h_2 h_3 h_4 h_5
  have hadd24_8 : (s0.readReg64 (.gpr 0#5) + 0x18#64) + 8#64 = s0.readReg64 (.gpr 0#5) + 32#64 := by bv_omega
  have hadd24_16 : (s0.readReg64 (.gpr 0#5) + 0x18#64) + 16#64 = s0.readReg64 (.gpr 0#5) + 40#64 := by bv_omega
  dsimp only [authenticatorPinAt]
  refine SepWPp.rw_pre (by rw [stackAt_authMacHdrX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.fold
    (vecU8At_expose_entails A (s0.readReg64 (.gpr 0#5) + 0x18#64) g.macKey.cap g.macKey.ptr auth.macKey)
    (by sep_focus) ?_
  refine SepWPp.rw_pre (by rw [hadd24_8, hadd24_16]) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmac_le, hmac_lt63, hmac_ptr_ne⟩
  have hmac_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 386) hinv0 ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 40#64) (s0.readReg64 (.gpr 1#5)))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  change subroutine_ok _ _ (withLsCallInv lsmpl (sliceConcat3Spec A)) at h_concat
  wpp_call_lsCallInv_concat_macHdr h_concat
    (⟨s0.sp - 112#64, s0.sp - 88#64,
      true, lsρ "spqr:.rodata..Lanon.140", Authenticator.hdrLabel,
      false, s0.sp - 40#64, toBEBytes 8 (s0.readReg64 (.gpr 1#5)),
      hdrRO, s0.readReg64 (.gpr 2#5), hdr⟩ : SliceConcat3Ghost)
    hinv1
  have hdata_pos :
      0 < (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length := by
    simp [List.length_append]
  have hdata_lt64 :
      (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length < 2 ^ 64 := by
    simp only [List.length_append, hdrLabel_length, toBEBytes_8_length]
    omega
  have hdata_toNat :
      (BitVec.ofNat 64 (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length).toNat =
        (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdata_lt64]
  rw [← List.append_assoc Authenticator.hdrLabel]
  refine SepWPp.fold (vecU8_nonempty_entails A (s0.sp - 112#64) hdata_pos) (by sep_focus) ?_
  sep_elim_exists
  rename_i cap ptr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_ne, hlayout, hptr_ne, hle⟩
  have ⟨hpos1, hpow1, hisize⟩ := hlayout
  have hcap_beq : (cap == 0#64) = false := beq_false_of_ne hcap_ne
  refine SepWPp.of_sepWP_lsCallInv (mid := lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac") hF_sf ?_
  wp_steps
  have hstack_sf : stackAt (s0.sp - 112#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 112#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  change subroutine_ok _ _ (withLsCallInv lsmpl (libcruxHmacSpec F A)) at h_hmac
  wpp_call_lsCallInv_hmac_macHdr h_hmac
    (⟨s0.readReg64 (.gpr 8#5), g.macKey.ptr, auth.macKey,
      ptr, Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr⟩ : LibcruxHmacCall)
    hinv2
  have hk_lt32 : auth.macKey.length < 4294967296 := ‹_›
  have hd_lt32 : (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length < 4294967296 := by
    rwa [List.append_assoc]
  rw [← List.append_assoc Authenticator.hdrLabel]
  wp_steps
  refine SepWP.fold (pointsToBytes_memRegion_entails _ hle hlayout) (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  wp_call h_dealloc (_, _, 1)
  wp_steps
  refine SepWP.fold (Entails.of_eq (hstack_sf.trans hstack_sf1).symm) (by sep_focus) ?_
  have hbe_len : (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length = 8 := by simp
  refine SepWP.fold (rejoin_stack_authMacHdrX s0.sp _ _ _ _ _ _ _ _ _ hbe_len _ _ _ _) (by sep_focus) ?_
  have hmac_rejoin :
      ((s0.readReg64 (.gpr 0#5) + 0x18#64) ↦₆₄ g.macKey.cap) ∗
        ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
        ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
        (g.macKey.ptr ↦ₛ auth.macKey) ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) ⊢
        vecU8At A (s0.readReg64 (.gpr 0#5) + 0x18#64) g.macKey.cap g.macKey.ptr auth.macKey := by
    rw [← hadd24_8, ← hadd24_16]
    exact vecU8At_unexpose_entails A (s0.readReg64 (.gpr 0#5) + 0x18#64)
      g.macKey.cap g.macKey.ptr auth.macKey hmac_le hmac_lt63 hmac_ptr_ne
  refine SepWP.fold hmac_rejoin (by sep_focus) ?_
  have hmacHdr_ok :
      auth.macHdr F (s0.readReg64 (.gpr 1#5)) hdr =
        .ok (auth.macHdrUnchecked F (s0.readReg64 (.gpr 1#5)) hdr) :=
    Authenticator.macHdr_of_lt F auth (s0.readReg64 (.gpr 1#5)) hdr hk_lt32 hd_lt32
  rw [← List.append_assoc Authenticator.hdrLabel,
    ← macHdrUnchecked_eq_hmacWith F auth (s0.readReg64 (.gpr 1#5)) hdr]
  wp_done

/-- Block 342 (`Authenticator::mac_hdr`) meets `withLsCallInv lsmpl (authMacHdrSpec F A)`. -/
theorem authMacHdr_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat3Spec A)))
    (h_hmac : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac")
      (withLsCallInv lsmpl (libcruxHmacSpec F A)))
    (h_dealloc : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack)) :
    subroutine_ok ((blkPC_342).rebase (blkPl_342).base H) (blkPl_342).base
      (withLsCallInv lsmpl (authMacHdrSpec F A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpin := authMacHdrPinned_placed_ok h_concat h_hmac h_dealloc
  simp only [authMacHdrSpec, withLsCallInv, authenticatorAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨
      (withLsCallInv lsmpl (authMacHdrPinnedSpec F A)).pre
        ⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩ s0 ∗ R := by
    simpa only [authMacHdrPinnedSpec, withLsCallInv] using hpre
  refine hpin.mono_outcome ⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩ R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hent :
        (withLsCallInv lsmpl (authMacHdrPinnedSpec F A)).post
          ⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩ s0 sf ∗ R ⊢
        (withLsCallInv lsmpl (authMacHdrSpec F A)).post x s0 sf ∗ R := by
      apply sepConj_mono_left
      dsimp only [authMacHdrPinnedSpec, authMacHdrSpec, withLsCallInv]
      exact sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (authenticatorPinAt_entails_authenticatorAt A g x.selfA x.auth)))
    exact Satisfies.mono hent hpost
  · exact Or.inr (Or.inl ⟨hpan, hpost⟩)
  · exact Or.inr (Or.inr hex)

end CryptoVerification.SpqrV1.Auth
