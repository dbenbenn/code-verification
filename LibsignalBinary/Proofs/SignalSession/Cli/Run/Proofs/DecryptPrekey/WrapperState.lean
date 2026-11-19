/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SpecState -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Prologue
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.Entry
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome

/-!
# State-Coupled Wrapper Reduction for `decrypt_prekey`

Proves that `signal_session_handshake::decrypt_prekey` satisfies `cliDecryptPrekeySpecState K`
whenever the `message_decrypt_prekey` poll closure satisfies `dpPollSpecState K`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre

private def dps_fixedK (K : DpPollKState) (s0 : State) : DpPollK where
  Ghost := K.Ghost
  args := K.args
  inv := fun g => K.inv g s0.fs s0.trace
  res := fun _ _ => emp
  io := fun _ _ _ _ _ => True
  panics := K.panics
  need := K.need

private theorem dps_sepWPp_seq_keepsFrozen {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P
      (fun sm Pm => s.mem.KeepsFrozen sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (Φ := fun m => s.mem.KeepsFrozen m)
    (fun _ _ h1 h2 => h1.trans h2) (Memory.KeepsFrozen.refl s.mem) h

private structure dps_EpilogueMid (entry : BitVec 64) (s0 sm se : State) : Prop where
  pc : se.pc = entry + bv% (176)
  run : se.status = .Running
  sp : se.sp = s0.sp - 2144#64
  sp_align : se.spAligned = true
  x22 : se.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)
  x23 : se.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5)
  x24 : se.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)
  x25 : se.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : se.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : se.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  vregs : calleeSavedVRegs se = calleeSavedVRegs s0
  fs : se.fs = sm.fs
  trace : se.trace = sm.trace

private abbrev dps_epilogueMidProp (stk : Nat) (s0 sm : State) (ret : BitVec 64)
    {K : DpPollKState} (g : K.Ghost) (w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (∃∗ ws : List (BitVec 64),
      ⌜ws.length = 6 ∧ ws.head? ≠ some (BitVec.ofNat 64 (2 ^ 64 - 3))⌝ ∗
        dpWordsAt ret ws ∗ K.res g s0.fs s0.trace sm.fs sm.trace ws) ∗
    dpWordsAt s0.sp ((K.args g).drop 8) ∗
    stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗
    memRegion (s0.sp - 2144#64) 704 ∗
    ((s0.sp - 1440#64) ↦₈ 1#8) ∗
    memRegion (s0.sp - 1439#64) 1303 ∗
    memRegion (s0.sp - 136#64) 32 ∗
    ((s0.sp - 104#64) ↦₆₄ w0) ∗ ((s0.sp - 96#64) ↦₆₄ w1) ∗
    ((s0.sp - 88#64) ↦₆₄ w2) ∗ ((s0.sp - 80#64) ↦₆₄ w3) ∗
    ((s0.sp - 72#64) ↦₆₄ w4) ∗ ((s0.sp - 64#64) ↦₆₄ w5) ∗
    memRegion (s0.sp - 56#64) 8 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.fp) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

end CryptoVerification.SignalSession.Cli.RunProofs
