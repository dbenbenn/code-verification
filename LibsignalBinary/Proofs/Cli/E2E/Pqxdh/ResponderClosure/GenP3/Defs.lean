/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneFetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase

public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Junction Predicates

Shared `SepProp` junction state predicates for cloning an arbitrary `SessionState` inside
`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}` (frame `0xcd0`):
- `genP3Pre` at `+0x1778` (entry of `SessionState` field-by-field clone);
- `genP3J1` at `+0x19b0` (after `local_identity_public`, `remote_identity_public`, `root_key`, `sender_chain`);
- `genP3J2` at `+0x1a5c` (after `receiver_chains` clone loop);
- `genP3J3` at `+0x1b20` (after `pending_pre_key` and `pending_kyber_pre_key`);
- `genP3J4` at `+0x1bac` (after `alice_base_key` and `pq_ratchet_state`);
- `genP3PostEq` / `genP3PostNe` / `genP3Post` at `+0x1cd4` (`st.version = msgVer`) and `+0x1e04` (`st.version ≠ msgVer`).
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.ChainClone3

/-- Ghost relation between original and cloned optional `SenderChainGhost`:
preserves `none`/`some` alignment and, when present, preserves serialized ratchet key bytes. -/
@[expose] def OptSenderChainCloneRel :
    Option SenderChainGhost → Option SenderChain → Option SenderChainGhost → Prop
  | none, none, none => True
  | some sg, some _, some sg' => sg'.srk.bytes = sg.srk.bytes ∧ sg'.priv.bytes = sg.priv.bytes
  | _, _, _ => False

/-- Named scratch values for pending/kyber spill slots `[sp + 0x08 .. sp + 0x2c]`. -/
structure GenP3PendSpill where
  v08 : BitVec 64
  v10 : BitVec 64
  v18 : BitVec 64
  v24 : BitVec 32
  v28 : BitVec 32
  v2c : BitVec 32

/-- Pending/kyber scratch spill slots `[sp + 0x08 .. sp + 0x2c]` prior to `ClonePendingStmt` (`J3`). -/
@[expose] def genP3PendSpillScratch (sp : BitVec 64) : SepProp :=
  ∃∗ w : GenP3PendSpill,
    ((sp + 0x8#64) ↦₆₄ w.v08) ∗
      ((sp + 0x10#64) ↦₆₄ w.v10) ∗
      ((sp + 0x18#64) ↦₆₄ w.v18) ∗
      ((sp + 0x24#64) ↦₃₂ w.v24) ∗
      ((sp + 0x28#64) ↦₃₂ w.v28) ∗
      ((sp + 0x2c#64) ↦₃₂ w.v2c)

/-- Named scratch values for tail spill slots `[sp + 0x30 .. sp + 0x40]`. -/
structure GenP3TailSpill where
  u_30 : BitVec 32
  u_34 : BitVec 32
  u_38 : BitVec 64
  u_40 : BitVec 64

/-- Tail-segment spill slots `[sp + 0x30 .. sp + 0x40]` prior to `CloneKeysTailStmt` (`J4`). -/
@[expose] def genP3TailSpillScratch (sp : BitVec 64) : SepProp :=
  ∃∗ w : GenP3TailSpill,
    ((sp + 0x30#64) ↦₃₂ w.u_30) ∗
      ((sp + 0x34#64) ↦₃₂ w.u_34) ∗
      ((sp + 0x38#64) ↦₆₄ w.u_38) ∗
      ((sp + 0x40#64) ↦₆₄ w.u_40)

/-- Named scratch values for chains spill slots `[sp + 0x60 .. sp + 0x70]`. -/
structure GenP3ChainsSpill where
  u_60 : BitVec 64
  u_68 : BitVec 64
  u_70 : BitVec 64

/-- Chains-segment spill slots `[sp + 0x60 .. sp + 0x70]` prior to `CloneChainsStmt` (`J2`). -/
@[expose] def genP3ChainsSpillScratch (sp : BitVec 64) : SepProp :=
  ∃∗ w : GenP3ChainsSpill,
    ((sp + 0x60#64) ↦₆₄ w.u_60) ∗
      ((sp + 0x68#64) ↦₆₄ w.u_68) ∗
      ((sp + 0x70#64) ↦₆₄ w.u_70)

/-- Named scratch values for front-segment spill slots `[sp + 0x48..0xd0, sp + 0x930..0x988]`. -/
structure GenP3FrontSpill where
  u_48 : BitVec 64
  u_50 : BitVec 64
  u_5c : BitVec 32
  u_7c : BitVec 32
  u_98 : BitVec 64
  u_d0 : BitVec 64
  u930 : BitVec 64
  u938 : BitVec 64
  u940 : BitVec 64
  u948 : BitVec 64
  u950 : BitVec 64
  u958 : BitVec 64
  u960 : BitVec 64
  u968 : BitVec 64
  u970 : BitVec 64
  u978 : BitVec 64
  u980 : BitVec 64
  u988 : BitVec 64

/-- Sender-chain inline 96-byte scratch `[sp + 0x930 .. sp + 0x990)` expressed as 6 × 128-bit quads
matching `bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5`. -/
@[expose] def genP3SenderInlineWords (sp : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) : SepProp :=
  ((sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗
    ((sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
    ((sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
    ((sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
    ((sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗
    ((sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
    ((sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
    ((sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
    ((sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗
    ((sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
    ((sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗
    ((sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)

/-- Full spill scratch bundle `[sp + 0x08 .. sp + 0x98, sp + 0xd0, sp + 0x930 .. sp + 0x988]` at
`+0x1778` (`genP3Pre`) and after packing (`genP3Post`). -/
@[expose] def genP3SpillAll (sp : BitVec 64) : SepProp :=
  genP3PendSpillScratch sp ∗
    genP3TailSpillScratch sp ∗
    genP3ChainsSpillScratch sp ∗
    ∃∗ w : GenP3FrontSpill,
      ((sp + 0x48#64) ↦₆₄ w.u_48) ∗
        ((sp + 0x50#64) ↦₆₄ w.u_50) ∗
        ((sp + 0x5c#64) ↦₃₂ w.u_5c) ∗
        ((sp + 0x7c#64) ↦₃₂ w.u_7c) ∗
        ((sp + 0x98#64) ↦₆₄ w.u_98) ∗
        ((sp + 0xd0#64) ↦₆₄ w.u_d0) ∗
        ((sp + 0x930#64) ↦₆₄ w.u930) ∗
        ((sp + 0x938#64) ↦₆₄ w.u938) ∗
        ((sp + 0x940#64) ↦₆₄ w.u940) ∗
        ((sp + 0x948#64) ↦₆₄ w.u948) ∗
        ((sp + 0x950#64) ↦₆₄ w.u950) ∗
        ((sp + 0x958#64) ↦₆₄ w.u958) ∗
        ((sp + 0x960#64) ↦₆₄ w.u960) ∗
        ((sp + 0x968#64) ↦₆₄ w.u968) ∗
        ((sp + 0x970#64) ↦₆₄ w.u970) ∗
        ((sp + 0x978#64) ↦₆₄ w.u978) ∗
        ((sp + 0x980#64) ↦₆₄ w.u980) ∗
        ((sp + 0x988#64) ↦₆₄ w.u988)

/-- Named witness at junction `J1` (`+0x19b0`). -/
structure GenP3J1Witness where
  newLocIdPtr : BitVec 64
  newRemIdPtr : BitVec 64
  newRootKeyPtr : BitVec 64
  c0 : BitVec 64
  sender' : Option SenderChainGhost
  sq0 : BitVec 128
  sq1 : BitVec 128
  sq2 : BitVec 128
  sq3 : BitVec 128
  sq4 : BitVec 128
  sq5 : BitVec 128

/-- Named witness at junction `J2` (`+0x1a5c`). -/
structure GenP3J2Witness extends GenP3J1Witness where
  newRcPtr : BitVec 64
  chains' : List ChainGhost

/-- Named witness at junction `J3` (`+0x1b20`). -/
structure GenP3J3Witness extends GenP3J2Witness where
  pendCap' : BitVec 64
  pendPtr' : BitVec 64
  kybCap' : BitVec 64
  kybPtr' : BitVec 64
  d10 : BitVec 64
  w24 : BitVec 32
  w28 : BitVec 32
  w2c : BitVec 32

/-- Named witness at junction `J4` (`+0x1bac`). -/
structure GenP3J4Witness extends GenP3J3Witness where
  newAlicePtr : BitVec 64
  newPqPtr : BitVec 64
  regW0 : BitVec 32
  regW1 : BitVec 32

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
