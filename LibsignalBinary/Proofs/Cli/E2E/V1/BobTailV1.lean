/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCut -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhDefs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHChain
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Mac.Compute
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# CLI `initialize_bob_session` at SPQR V1

Verifies `initialize_bob_session` (`0x21c80`, 608 B; frame `fsp = sp0 - 768`) on the SPQR V1
accepting path (`Model.acceptKeys P inp = some drKey`):
- `initBob_to_spqr_full_v1`: entry to `bl spqr::initial_state` (`+248`), preserving the full stack
  frame (`bobFrameAtSpqr`) and saved registers (`initBobSavedRegs`) alongside `bobSpqrCutCells`;
- `initBob_session_build_v1`: `spqr::initial_state` return (`+252`) to `+564`, checking the `Ok`
  tag (`0`), serializing keys, invoking `with_sender_chain`, and packing the 344-byte V1
  `SessionState` (`bobSession344Bv8V1`) with dynamic SPQR `Vec<u8>` header `(cap, ptr, len)` at `+0x78`;
- `initBob_epilogue_v1` and `initializeBobSession_ok_v1`: epilogue (`+564 → RET`) and end-to-end
  composition at caller stack budget `stageP2bStack + 0x700`.
-/

public section

namespace CryptoVerification.E2E.V1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure (stageP2bStack)
open CryptoVerification.SpqrV1.Top.InitialState (initialStateStack initialStateStackExt initialStateValue paramsAt)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
@[local arm64_norm ↓, local wp_norm ↓]
private theorem _root_.CryptoVerification.Cli.E2E.V1.calleeSavedVRegs_setPC_pre_bob (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem _root_.CryptoVerification.Cli.E2E.V1.calleeSavedVRegs_setMem_setPC_pre_bob (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem _root_.CryptoVerification.Cli.E2E.V1.calleeSavedVRegs_writeVReg128_0_bob (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl

/-- The `Params` Bob passes to `spqr::initial_state`: `B2A`, `V1`, `V1`, `auth_key = pqr_key`,
`ChainParams::default` (25000, 2000). -/
@[expose] def _root_.CryptoVerification.Cli.E2E.V1.bobSpqrParams (pqrKey : SignalPqxdh.Bytes) : CryptoVerification.LibsignalSpqrV1.Params :=
  { direction := .b2a, version := .v1, minVersion := .v1, authKey := bytesToBv8 pqrKey }

/-- Heap buffer part of a `Vec<u8>` with capacity `cap` at `ptr` holding `bs` (`vecU8At` without
its 24-byte header). -/
@[expose] def _root_.CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem _root_.CryptoVerification.Cli.E2E.V1.vecU8At_eq_header_bobBuf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A cap ptr bs := rfl

/-- First 144 bytes of Bob's `SessionState` with dynamic SPQR `Vec<u8>` length `spqrLen` at `+0x88`. -/
@[expose] def _root_.CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen : BitVec 64) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64 ++ unpack64 rootKeyBoxPtr ++ unpack64 32#64 ++
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 spqrLen

@[local simp]
theorem _root_.CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1_length (p1 p2 p3 p4 c5 p5 l5 : BitVec 64) :
    (CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 p1 p2 p3 p4 c5 p5 l5).length = 144 := by
  simp [CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1]

theorem _root_.CryptoVerification.Cli.E2E.V1.bobHead144Bv8_eq_V1 (p1 p2 p3 p4 c5 p5 : BitVec 64) :
    bobHead144Bv8 p1 p2 p3 p4 c5 p5 = CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 p1 p2 p3 p4 c5 p5 0#64 := rfl

theorem _root_.CryptoVerification.Cli.E2E.V1.bobHead144V1_eq_pointsToBytes (ptr : BitVec 64)
    (p1 p2 p3 p4 c5 p5 l5 : BitVec 64) :
    (ptr ↦₆₄ 33#64) ∗
    ((ptr + 0x08#64) ↦₆₄ p1) ∗
    ((ptr + 0x10#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x18#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x20#64) ↦₆₄ p2) ∗
    ((ptr + 0x28#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x30#64) ↦₆₄ 32#64) ∗
    ((ptr + 0x38#64) ↦₆₄ p3) ∗
    ((ptr + 0x40#64) ↦₆₄ 32#64) ∗
    ((ptr + 0x48#64) ↦₆₄ 0#64) ∗
    ((ptr + 0x50#64) ↦₆₄ 8#64) ∗
    ((ptr + 0x58#64) ↦₆₄ 0#64) ∗
    ((ptr + 0x60#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x68#64) ↦₆₄ p4) ∗
    ((ptr + 0x70#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x78#64) ↦₆₄ c5) ∗
    ((ptr + 0x80#64) ↦₆₄ p5) ∗
    ((ptr + 0x88#64) ↦₆₄ l5) =
      (ptr ↦ₛ CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 p1 p2 p3 p4 c5 p5 l5) := by
  unfold CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes]

/-- The 344-byte `SessionState` Bob builds, with the V1 pq vec header `(spqrCap, spqrBufPtr,
spqrLen)` at `+0x78`. -/
@[expose] def _root_.CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    spqrLen ++
  senderChainBytes100 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ++ unpack32 pad_f4 ++
  bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2

@[local simp]
theorem _root_.CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1_length (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2).length =
      344 := by
  simp [CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1]

theorem _root_.CryptoVerification.Cli.E2E.V1.bobSession344Bv8_eq_V1 (p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    bobSession344Bv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 =
      CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 p1 p2 p3 p4 c5 p5 0#64 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 := rfl

theorem _root_.CryptoVerification.Cli.E2E.V1.bobSession344V1_pack (ptr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (ptr ↦ₛ CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap
      spqrBufPtr spqrLen) ∗
    senderChainFieldsAt ptr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ∗
    ((ptr + 0xf4#64) ↦ₛ (unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2)) =
      (ptr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap
        spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) := by
  unfold CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1
  rw [senderChainFieldsAt_eq_pointsToBytes]
  simp only [List.append_assoc, pointsToBytes_append, CryptoVerification.Cli.E2E.V1.bobHead144Bv8V1_length,
    senderChainBytes100_length, BitVec.add_assoc, BitVec.reduceAdd]

/-- The twelve callee-saved words `initialize_bob_session`'s prologue stores at `sp0 - 96`
(`stp x29, x30, [sp, #-0x60]!` … `stp x20, x19, [sp, #0x50]`). -/
@[expose] def _root_.CryptoVerification.Cli.E2E.V1.initBobSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

theorem _root_.CryptoVerification.Cli.E2E.V1.initBobSavedRegs_entails_memRegion96 (sp0 : BitVec 64) (s0 : State) :
    CryptoVerification.Cli.E2E.V1.initBobSavedRegs sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  rw [(ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide) :
    memRegion (sp0 - 96#64) 96 = cells (sp0 - 96#64) 12)]
  exact cells12_sub96_merge sp0 _ _ _ _ _ _ _ _ _ _ _ _

/-- The cells of `initialize_bob_session`'s frame at `spqr::initial_state`'s entry other than
`bobSpqrCutCells`, the saved registers and the stack below `sp0 - 768`. `sp0 - 768 .. sp0 - 672`
is the cut's leftover copy of the handshake keys (`sp + 0` is the callee's sret);
`sp0 - 452 .. sp0 - 384` is the rest of `pqxdhAccept`'s result after the `Params`. -/
@[expose] def _root_.CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr (sp0 : BitVec 64) (rk pq ck : SignalPqxdh.Bytes) : SepProp :=
  ((sp0 - 768#64) ↦ₛ bytesToBv8 rk) ∗ ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗
  ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗ ((sp0 - 672#64) ↦₃₂ 0#32) ∗
  memRegion (sp0 - 668#64) 12 ∗ ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
  memRegion (sp0 - 544#64) 56 ∗
  ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
  ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288

/-! ## Stack and parameter bridges -/

private theorem _root_.CryptoVerification.Cli.E2E.V1.bv_add_sub_lit_bob (x a b : BitVec 64) : (x + a) - b = x + (a - b) := by bv_omega

private theorem _root_.CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega, memRegion_split' (n := d) (k := n) (by omega) rfl (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

private theorem _root_.CryptoVerification.Cli.E2E.V1.split64_hi_lo (p : BitVec 64) (lo hi : BitVec 32) (w : BitVec 64)
    (hw : unpack64 w = unpack32 lo ++ unpack32 hi) :
    (p ↦₆₄ w) = (p ↦₃₂ lo) ∗ ((p + 4#64) ↦₃₂ hi) := by
  rw [pointsTo64_eq_pointsToBytes, hw, pointsToBytes_append, unpack32_length,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]

/-- Rewrites `bobSpqrCutCells` into `paramsAt (sp0 - 488) (sp0 - 576) (bobSpqrParams pq)` plus the
32-byte `auth_key` slice at `sp0 - 576`. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.bobSpqrCutCells_eq_paramsAt (sp0 rkp : BitVec 64) (rk pq ck spkPk spkSk : SignalPqxdh.Bytes)
    (hpq : pq.length = 32) :
    bobSpqrCutCells sp0 rkp rk pq ck spkPk spkSk =
      paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
      ((sp0 - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq).authKey) ∗
      ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ∗
      (rkp ↦ₛ bytesToBv8 spkPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkSk) := by
  have hlen : (bytesToBv8 pq).length = 32 := by simp [bytesToBv8, hpq]
  have h468 := CryptoVerification.Cli.E2E.V1.split64_hi_lo (sp0 - 468#64) 2000#32 1#32 0x1000007d0#64 (by decide)
  have h460 := CryptoVerification.Cli.E2E.V1.split64_hi_lo (sp0 - 460#64) 1#32 1#32 0x100000001#64 (by decide)
  simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h468 h460
  unfold bobSpqrCutCells paramsAt CryptoVerification.Cli.E2E.V1.bobSpqrParams
  rw [h468, h460]
  simp only [hlen, Initiator.bv_sub_add_lit', BitVec.reduceSub]
  have hdir : (CryptoVerification.LibsignalSpqrV1.Direction.b2a).toI32 = 1#32 := rfl
  have hver : (CryptoVerification.LibsignalSpqrV1.Version.v1).toI32 = 1#32 := rfl
  have hmj : (CryptoVerification.LibsignalSpqrV1.ChainParams.default).maxJump = 25000#32 := rfl
  have hmo : (CryptoVerification.LibsignalSpqrV1.ChainParams.default).maxOooKeys = 2000#32 := rfl
  simp only [hdir, hver, hmj, hmo]
  ac_rfl

/-- Splits `stackAt sp0 (stageP2bStack + 0x700)` into `768 + pqxdhEntryStack` and the `0x700`
extra bytes immediately below `initialStateStack` at `sp0 - 768`. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_stack_extra (sp0 : BitVec 64) :
    stackAt sp0 (stageP2bStack + 0x700) =
      memRegion (sp0 - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
        stackAt sp0 (768 + Initiator.pqxdhEntryStack) := by
  have ha : sp0 - BitVec.ofNat 64 (stageP2bStack + 0x700) =
      sp0 - 768#64 - BitVec.ofNat 64 initialStateStack := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add,
      show stageP2bStack + 0x700 = 768 + initialStateStack by decide]
  rw [CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom sp0 stageP2bStack 0x700 (by decide), ha]

/-- Joins the `0x700` extra bytes with `stackAt (sp0 - 768) pqxdhEntryStack` to form
`stackAt (sp0 - 768) initialStateStack` at the `spqr::initial_state` call site. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_stack_join (sp0 : BitVec 64) :
    memRegion (sp0 - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
      stackAt (sp0 - 768#64) Initiator.pqxdhEntryStack =
    stackAt (sp0 - 768#64) initialStateStack := by
  have h := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom (sp0 - 768#64) Initiator.pqxdhEntryStack 0x700 (by decide)
  rw [show Initiator.pqxdhEntryStack + 0x700 = initialStateStack by decide] at h
  exact h.symm

theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_stack_ext_split (sp0 : BitVec 64) :
    stackAt sp0 (768 + Initiator.pqxdhEntryStackExt) =
      memRegion (sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗
        stackAt sp0 (768 + Initiator.pqxdhEntryStack) := by
  have ha : sp0 - BitVec.ofNat 64 (768 + Initiator.pqxdhEntryStackExt) =
      sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have h := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom sp0
    (768 + Initiator.pqxdhEntryStack) 16384 (by decide)
  rw [show (768 + Initiator.pqxdhEntryStack) + 16384 = 768 + Initiator.pqxdhEntryStackExt by decide,
    ha] at h
  exact h

theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_split (sp0 : BitVec 64) :
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStackExt =
      memRegion (sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗
        stackAt (sp0 - 768#64) Initiator.pqxdhEntryStack := by
  have h := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom (sp0 - 768#64)
    Initiator.pqxdhEntryStack 16384 (by decide)
  rwa [show Initiator.pqxdhEntryStack + 16384 = Initiator.pqxdhEntryStackExt by decide] at h

theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_to_initialState (sp0 : BitVec 64) :
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStackExt =
      memRegion (sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 14592 ∗
        stackAt (sp0 - 768#64) initialStateStack := by
  have h := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom (sp0 - 768#64)
    initialStateStack 14592 (by decide)
  rwa [show initialStateStack + 14592 = Initiator.pqxdhEntryStackExt by decide] at h

theorem _root_.CryptoVerification.Cli.E2E.V1.bobV1_entry_ext_to_initialStateExt (sp0 : BitVec 64) :
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStackExt =
      memRegion (sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 13360 ∗
        stackAt (sp0 - 768#64) initialStateStackExt := by
  have h := CryptoVerification.Cli.E2E.V1.bob_stackAt_split_bottom (sp0 - 768#64)
    initialStateStackExt 13360 (by decide)
  rwa [show initialStateStackExt + 13360 = Initiator.pqxdhEntryStackExt by decide] at h

/-! ## Subroutine segments and end-to-end composition -/

@[local arm64_norm, local wp_norm]
private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb1b_bv_sub_add_lit' (x a b : BitVec 64) :
    (x - a) + b = x - (a - b) := Initiator.bv_sub_add_lit' x a b

@[local simp, local arm64_norm, local wp_norm]
private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb1b_cond_ne_subs64_0_1 :
    ConditionHolds CondCode.NE (subsPState64 0#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb1b_sub488_split (sp : BitVec 64) :
    memRegion (sp - 488#64) 344 =
      cells (sp - 488#64) 19 ∗
      memRegion (sp - 336#64) 92 ∗
      (∃∗ pad_f4 : BitVec 32, (sp - 244#64) ↦₃₂ pad_f4) ∗
      memRegion (sp - 240#64) 96 := by
  rw [ProofLib.memRegion_split' (b := sp - 488#64) (n := 152) (k := 192)
      (b' := sp - 336#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 336#64) (n := 92) (k := 100)
      (b' := sp - 244#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 244#64) (n := 4) (k := 96)
      (b' := sp - 240#64) rfl (by bv_omega) (by decide),
    (ProofLib.memRegion_cells (sp - 488#64) 19 (by decide) :
      memRegion (sp - 488#64) 152 = cells (sp - 488#64) 19),
    ProofLib.memRegion_four (sp - 244#64)]

private def _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameRest (sp0 : BitVec 64) (pq ck : SignalPqxdh.Bytes) : SepProp :=
  ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗
  ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗ ((sp0 - 672#64) ↦₃₂ 0#32) ∗
  memRegion (sp0 - 668#64) 12 ∗ ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
  memRegion (sp0 - 544#64) 56 ∗
  ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
  ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameAtSpqr_entails (sp0 : BitVec 64) (rk pq ck : SignalPqxdh.Bytes)
    (hrk : rk.length = 32) :
    CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr sp0 rk pq ck ⊢
      memRegion (sp0 - 768#64) 32 ∗ CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameRest sp0 pq ck := by
  unfold CryptoVerification.Cli.E2E.V1.bobFrameAtSpqr CryptoVerification.Cli.E2E.V1.wp6pb4b_bobFrameRest
  have hlen : (bytesToBv8 rk).length = 32 := by simp [bytesToBv8, hrk]
  have hm : ((sp0 - 768#64) ↦ₛ bytesToBv8 rk) ⊢ memRegion (sp0 - 768#64) 32 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (sp0 - 768#64) (bytesToBv8 rk)
  exact sepConj_mono_left hm

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_sub488_merge (sp0 : BitVec 64) (pq ck : SignalPqxdh.Bytes)
    (hpq : pq.length = 32) (hck : ck.length = 32) :
    paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
    ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288 ⊢
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 := by
  have hpq_len : (bytesToBv8 pq).length = 32 := by simp [bytesToBv8, hpq]
  have hck_len : (bytesToBv8 ck).length = 32 := by simp [bytesToBv8, hck]
  have h104 :
      paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
      ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
      ((sp0 - 388#64) ↦₃₂ 0#32) ⊢ memRegion (sp0 - 488#64) 104 := by
    unfold paramsAt CryptoVerification.Cli.E2E.V1.bobSpqrParams
    simp only [hpq_len, Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    rw [ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 8) (k := 96)
        (b' := sp0 - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 480#64) (n := 8) (k := 88)
        (b' := sp0 - 472#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 472#64) (n := 4) (k := 84)
        (b' := sp0 - 468#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 468#64) (n := 4) (k := 80)
        (b' := sp0 - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 464#64) (n := 4) (k := 76)
        (b' := sp0 - 460#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 460#64) (n := 4) (k := 72)
        (b' := sp0 - 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 456#64) (n := 4) (k := 68)
        (b' := sp0 - 452#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 452#64) (n := 32) (k := 36)
        (b' := sp0 - 420#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 420#64) (n := 32) (k := 4)
        (b' := sp0 - 388#64) rfl (by bv_omega) (by decide)]
    have hm_pq : ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 452#64) 32 := by
      rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 452#64) (bytesToBv8 pq)
    have hm_ck : ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 420#64) 32 := by
      rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 420#64) (bytesToBv8 ck)
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono (pointsTo32_entails_memRegion _ _)
              (sepConj_mono (pointsTo32_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono hm_pq
                    (sepConj_mono hm_ck
                      (pointsTo32_entails_memRegion _ _)))))))))
  have hsplit :
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 488#64) 104 ∗ memRegion (sp0 - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 344) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 104) (k := 288)
        (b' := sp0 - 384#64) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  have hrearr :
      paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
      ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
      ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288 =
      (paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
       ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
       ((sp0 - 388#64) ↦₃₂ 0#32)) ∗ memRegion (sp0 - 384#64) 288 := by ac_rfl
  rw [hrearr]
  exact sepConj_mono_left h104

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_sub768_merge_280 (sp0 : BitVec 64) (rk pq ck : SignalPqxdh.Bytes)
    (hrk : rk.length = 32) (hpq : pq.length = 32) (hck : ck.length = 32) :
    memRegion (sp0 - 768#64) 32 ∗
    ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 672#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 668#64) 12 ∗
    ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
    ((sp0 - 576#64) ↦ₛ bytesToBv8 pq) ∗ memRegion (sp0 - 544#64) 56 ⊢
      memRegion (sp0 - 768#64) 280 := by
  have hrk_len : (bytesToBv8 rk).length = 32 := by simp [bytesToBv8, hrk]
  have hpq_len : (bytesToBv8 pq).length = 32 := by simp [bytesToBv8, hpq]
  have hck_len : (bytesToBv8 ck).length = 32 := by simp [bytesToBv8, hck]
  rw [ProofLib.memRegion_split' (b := sp0 - 768#64) (n := 32) (k := 248)
      (b' := sp0 - 736#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 736#64) (n := 32) (k := 216)
      (b' := sp0 - 704#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 704#64) (n := 32) (k := 184)
      (b' := sp0 - 672#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 672#64) (n := 4) (k := 180)
      (b' := sp0 - 668#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 668#64) (n := 12) (k := 168)
      (b' := sp0 - 656#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 656#64) (n := 32) (k := 136)
      (b' := sp0 - 624#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 624#64) (n := 32) (k := 104)
      (b' := sp0 - 592#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 592#64) (n := 4) (k := 100)
      (b' := sp0 - 588#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 588#64) (n := 12) (k := 88)
      (b' := sp0 - 576#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 576#64) (n := 32) (k := 56)
      (b' := sp0 - 544#64) rfl (by bv_omega) (by decide)]
  have hm_pq736 : ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 736#64) 32 := by
    rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 736#64) (bytesToBv8 pq)
  have hm_ck704 : ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 704#64) 32 := by
    rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 704#64) (bytesToBv8 ck)
  have hm_rk656 : ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ⊢ memRegion (sp0 - 656#64) 32 := by
    rw [← hrk_len]; exact pointsToBytes_entails_memRegion (sp0 - 656#64) (bytesToBv8 rk)
  have hm_ck624 : ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 624#64) 32 := by
    rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 624#64) (bytesToBv8 ck)
  have hm_pq576 : ((sp0 - 576#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 576#64) 32 := by
    rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 576#64) (bytesToBv8 pq)
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono hm_pq736
      (sepConj_mono hm_ck704
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono hm_rk656
              (sepConj_mono hm_ck624
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono (Entails.refl _)
                    (sepConj_mono hm_pq576
                      (Entails.refl _))))))))))

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_stack_final_eq (sp0 : BitVec 64) :
    memRegion (sp0 - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStack ∗
    memRegion (sp0 - 768#64) 280 ∗
    memRegion (sp0 - 488#64) 344 ∗
    memRegion (sp0 - 144#64) 48 ∗
    memRegion (sp0 - 96#64) 96 =
      stackAt sp0 (stageP2bStack + 0x700) := by
  have hsplit :
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 488#64) 104 ∗ memRegion (sp0 - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 344) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 104) (k := 288)
        (b' := sp0 - 384#64) rfl (by bv_omega) (by decide)]
  rw [CryptoVerification.Cli.E2E.V1.bobV1_stack_extra sp0, stackAt_initBob_entry sp0,
    ← (ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide) :
      memRegion (sp0 - 96#64) 96 = cells (sp0 - 96#64) 12),
    ← sepConj_assoc (memRegion (sp0 - 488#64) 344), hsplit]
  ac_rfl

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_seq {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm → SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  unfold SepWPp at h1 ⊢
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | hpan⟩
  · rcases h2 sm Pm hpcm hrunm hQ R hmm (hsteps.codeLoaded hL) with ⟨sf, hsteps', hout⟩
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

private theorem _root_.CryptoVerification.Cli.E2E.V1.wp6pb4b_stack_final_ext_eq (sp0 : BitVec 64) :
    memRegion (sp0 - 768#64 - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt) 16384 ∗
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStack ∗
    memRegion (sp0 - 768#64) 280 ∗
    memRegion (sp0 - 488#64) 344 ∗
    memRegion (sp0 - 144#64) 48 ∗
    memRegion (sp0 - 96#64) 96 =
      stackAt sp0 (768 + Initiator.pqxdhEntryStackExt) := by
  have hsplit :
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 488#64) 104 ∗ memRegion (sp0 - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 344) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 104) (k := 288)
        (b' := sp0 - 384#64) rfl (by bv_omega) (by decide)]
  rw [CryptoVerification.Cli.E2E.V1.bobV1_stack_ext_split sp0, stackAt_initBob_entry sp0,
    ← (ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide) :
      memRegion (sp0 - 96#64) 96 = cells (sp0 - 96#64) 12),
    ← sepConj_assoc (memRegion (sp0 - 488#64) 344), hsplit]
  ac_rfl

end CryptoVerification.E2E.V1
