/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Decodes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerialize -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Auth.Update -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Defs
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpoch -- proof-setup: allow-public-import

/-!
# Shared Definitions, Stack Layout, and Callee Contract Bundle for `spqr::send` (`0x3085c`)

**Checked by Lean.**

Defines stack frame constants (`spqrSendFrame = 8064`, `spqrSendCalleeStack = 123008`),
`spqrSendSavedRegs`, `optEpochSecretRegSlotAt`, `statesSendArmOffset` for jump table 1,
and the callee contract bundles `SpqrSendContracts` and `SpqrSendContractsExt`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

/-! ## Stack Frame Constants and Saved Callee-Saved Registers (`sp + 0x1f20 .. sp + 0x1f80`) -/

/-- Own stack frame of `spqr::send::<HookRng>` (`0x3085c`):
    `0x60` (`96`B saved registers) + `0x1f20` (`7,968`B local slots) = `0x1f80` (`8,064`B). -/
abbrev spqrSendFrame : Nat := 8064

/-- Remaining callee stack budget of `spqr::send::<HookRng>` (`2^17 - 8,064 = 123,008`B). -/
abbrev spqrSendCalleeStack : Nat := 123008

theorem spqrSendStack_eq : spqrSendStack = spqrSendCalleeStack + spqrSendFrame := by decide

/-- Saved callee-saved registers (`x29, x30, x28..x19`) at `[sp + 0x1f20 .. sp + 0x1f80)`
    (`sp = s0.sp - 0x1f80`, `sp + 0x1f20 = s0.sp - 0x60`). -/
@[expose] def spqrSendSavedRegs (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp + 0x1f20#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp + 0x1f28#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp + 0x1f30#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp + 0x1f38#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp + 0x1f40#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp + 0x1f48#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp + 0x1f50#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp + 0x1f58#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp + 0x1f60#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp + 0x1f68#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp + 0x1f70#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp + 0x1f78#64) ↦₆₄ s0.readReg64 .x19)

theorem spqrSendSavedRegs_entails_memRegion (sp : BitVec 64) (s0 : State) :
    spqrSendSavedRegs sp s0 ⊢ memRegion (sp + 0x1f20#64) 96 := by
  unfold spqrSendSavedRegs
  have hcell (off : BitVec 64) (v : BitVec 64) :
      ((sp + off) ↦₆₄ v) ⊢ memRegion (sp + off) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp + off) v
  rw [ProofLib.memRegion_split (sp + 0x1f20#64) 8 88 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64) 8 80 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64) 8 72 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _)
    (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _)
    (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _)
    (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (hcell _ _)))))))))))

theorem stackAt_spqrSend_split_96 (sp0 : BitVec 64) :
    stackAt sp0 spqrSendStack =
      stackAt (sp0 - 96#64) (spqrSendCalleeStack + 7968) ∗ cells (sp0 - 96#64) 12 := by
  have h := ProofLib.stackAt_split_cells sp0 (spqrSendCalleeStack + 7968) 12 (by decide)
  have h1 : spqrSendCalleeStack + 7968 + 8 * 12 = spqrSendStack := by decide
  rw [h1] at h
  exact h

theorem stackAt_spqrSend_split_frame (sp0 : BitVec 64) :
    stackAt (sp0 - 96#64) (spqrSendCalleeStack + 7968) =
      stackAt (sp0 - 8064#64) spqrSendCalleeStack ∗ memRegion (sp0 - 8064#64) 7968 := by
  simp only [stackAt]
  rw [ProofLib.memRegion_split ((sp0 - 96#64) - BitVec.ofNat 64 (spqrSendCalleeStack + 7968))
    spqrSendCalleeStack 7968 (by decide)]
  have h1 : (sp0 - 96#64) - BitVec.ofNat 64 (spqrSendCalleeStack + 7968) =
      (sp0 - 8064#64) - BitVec.ofNat 64 spqrSendCalleeStack := by
    change (sp0 - 96#64) - 130976#64 = (sp0 - 8064#64) - 123008#64
    bv_omega
  have h2 : (sp0 - 96#64) - BitVec.ofNat 64 (spqrSendCalleeStack + 7968) +
      BitVec.ofNat 64 spqrSendCalleeStack = sp0 - 8064#64 := by
    change (sp0 - 96#64) - 130976#64 + 123008#64 = sp0 - 8064#64
    bv_omega
  rw [h2, h1]

theorem stackAt_spqrSend_eq_callee_and_frame (sp0 : BitVec 64) :
    stackAt sp0 spqrSendStack =
      stackAt (sp0 - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (sp0 - 0x1f80#64) 0x1f20 ∗
      memRegion (sp0 - 0x1f80#64 + 0x1f20#64) 96 := by
  simp only [stackAt]
  have h1 := ProofLib.memRegion_split (sp0 - BitVec.ofNat 64 spqrSendStack)
    spqrSendCalleeStack 8064 (by decide)
  have h1' : spqrSendCalleeStack + 8064 = spqrSendStack := rfl
  rw [h1'] at h1
  have h2 := ProofLib.memRegion_split (sp0 - 0x1f80#64) 0x1f20 96 (by decide)
  have h2' : 0x1f20 + 96 = (8064 : Nat) := rfl
  rw [h2'] at h2
  have ha : (sp0 - 0x1f80#64) - BitVec.ofNat 64 spqrSendCalleeStack =
      sp0 - BitVec.ofNat 64 spqrSendStack := by
    change (sp0 - 8064#64) - 123008#64 = sp0 - 131072#64
    bv_omega
  have hb : (sp0 - BitVec.ofNat 64 spqrSendStack) + BitVec.ofNat 64 spqrSendCalleeStack =
      sp0 - 0x1f80#64 := by
    change (sp0 - 131072#64) + 123008#64 = sp0 - 8064#64
    bv_omega
  rw [h1, hb, ← ha, h2]

theorem stack_restore_spqrSend (sp0 : BitVec 64) (s0 : State) :
    stackAt (sp0 - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (sp0 - 0x1f80#64) 0x1f20 ∗
      spqrSendSavedRegs (sp0 - 0x1f80#64) s0 ⊢
      stackAt sp0 spqrSendStack := by
  rw [stackAt_spqrSend_eq_callee_and_frame sp0]
  exact sepConj_mono_right (sepConj_mono_right (spqrSendSavedRegs_entails_memRegion (sp0 - 0x1f80#64) s0))

/-! ## Optional `epoch_secret` Register/Stack Layout (`sp + 0x1bc0`, `x21`, `x27`) -/

/-- Register+stack representation of `epoch_secret : Option<EpochSecret>` at the Phase 2 -> Phase 3
    join point (`0x314dc` / `0x31580`):
    - `x21 = cap` (`noneCap = -1` when `None`, `32 <= cap < 2^63` when `Some es`),
    - `x27 = ptr` (allocated buffer pointer when `Some es`),
    - `[sp + 0x1bc0] = es.secret.length` and `[sp + 0x1bc8] = es.epoch` when `Some es`
      (or `memRegion (sp + 0x1bc0) 16` when `None`). -/
@[expose] def optEpochSecretRegSlotAt (A : RustAlloc) (sp x21 x27 : BitVec 64) :
    Option EpochSecret → SepProp
  | none =>
      ⌜x21 = LibsignalTripleRatchetRepr.noneCap⌝ ∗ memRegion (sp + 0x1bc0#64) 16
  | some es =>
      ⌜x21 ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗
        ((sp + 0x1bc0#64) ↦₆₄ BitVec.ofNat 64 es.secret.length) ∗
        ((sp + 0x1bc8#64) ↦₆₄ es.epoch) ∗
        vecU8Heap A x21 x27 es.secret

/-! ## Jump Table 1 Target Offsets (`0x309cc`) -/

/-- PC offset (in bytes from `spqrSendEntry b = b + 0x3085c`) jumped to by `br x10` at `0x309cc`
    for each of the 11 `States` variants. -/
@[expose] def statesSendArmOffset {F : ShaCompress} :
    States spqrPolyApi (spqrAuthApi F) → BitVec 64
  | .keysUnsampled _ => 372#64          -- 0x309d0 (tag 2, idx 0, entry 0x0000)
  | .keysSampled _ => 1208#64           -- 0x30d14 (tag 3, idx 1, entry 0x00d1)
  | .headerSent _ => 960#64             -- 0x30c1c (tag 4, idx 2, entry 0x0093)
  | .ct1Received _ => 1040#64           -- 0x30c6c (tag 5, idx 3, entry 0x00a7)
  | .ekSentCt1Received _ => 924#64      -- 0x30bf8 (tag 6, idx 4, entry 0x008a)
  | .noHeaderReceived _ => 1284#64      -- 0x30d60 (tag 7, idx 5, entry 0x00e4)
  | .headerReceived _ => 1312#64        -- 0x30d7c (tag 8, idx 6, entry 0x00eb)
  | .ct1Sampled _ => 1128#64            -- 0x30cc4 (tag 1, idx 7, entry 0x00bd)
  | .ekReceivedCt1Sampled _ => 2460#64  -- 0x311f8 (tag 10, idx 8, entry 0x020a)
  | .ct1Acknowledged _ => 952#64        -- 0x30c14 (tag 11, idx 9, entry 0x0091)
  | .ct2Sampled _ => 2372#64            -- 0x311a0 (tag 12, idx 10, entry 0x01f4)

/-! ## `<PolyEncoder>::next_chunk` and Leaf `send_*_chunk` Contracts -/

private theorem stackAt_split_grow (sp : BitVec 64) (nX nExt : Nat)
    (hle : nX ≤ nExt := by decide) (hbd : nExt ≤ 131072 := by decide) :
    stackAt sp nExt = memRegion (sp - BitVec.ofNat 64 nExt) (nExt - nX) ∗ stackAt sp nX := by
  have hbd' : nX + (nExt - nX) ≤ 2 ^ 64 := by omega
  have h := ProofLib.stackAt_split_bottom sp nX (nExt - nX) hbd'
  rwa [Nat.add_sub_of_le hle] at h

end CryptoVerification.SpqrV1.Top.Send
