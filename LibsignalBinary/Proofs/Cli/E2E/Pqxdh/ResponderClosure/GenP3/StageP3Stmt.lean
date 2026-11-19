/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3c -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3c -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2

/-!
# General Stage P3 Statement

Defines `StageP3GenStmt` for general-state Stage P3 (`+0x1778 → +0x34dc` on `Ok pt`;
`+0x1778 → s0.readReg64 .x30` on `Err e` or `st.version ≠ msgVer`) of
`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`, together with its
model, panic, and spatial frame predicates (`genP3S5*`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SignalSession

/-! Guard against `HkdfToSliceProof` global `@[arm64_norm]` simp pollution
(`sp_sub_688_eq_hsp` rewrites every `sp - k#64` to `(sp - 688#64) + (688 - k)#64`, breaking
`stackAt_sub`). Imported transitively via `DecryptPq.DefsP`; downstream proof modules importing
`StageP3Stmt` must repeat this `attribute [-arm64_norm]` block after their `open` lines. -/
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Model, Panic, and Spatial Frame Predicates (`genP3S5*`) -/

/-- Pure `SessionState.tryDecryptWithState` model evaluation at SPQR v1 (`spqrV1 C.F K`) and
`.preKey` message type. Definitionally equal (`rfl`) to `(x.model C (spqrV1 C.F K) uuidTryParse)`
when `x.msgType = .preKey`, and to `pqxdhTryDecryptModel C (spqrV1 C.F K) uuidTryParse`. -/
abbrev genP3S5Model (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (rem loc : AddrGhost) (msg : SignalMessage) (rest : List (BitVec 8))
    (st : SessionState (List (BitVec 8))) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState (List (BitVec 8)) :=
  Mut.exec (SessionState.tryDecryptWithState C (LibsignalSpqrV1.spqrV1 C.F K).spqr
    (serializeAddresses (serviceIdParse uuidTryParse) rem loc) msg .preKey (coinsOf rest)) st

/-- Frame-polymorphic model-panic postcondition delivered at the `+0x1cd4` junction by the left
disjunct `(x.model C (spqrV1 C.F K) uuidTryParse).1 = .error .panic` of
`Decrypt.tryDecryptOnPanicTight` (under the live branch guard `st.version = msgVer`). -/
@[expose] def genP3S5ModelPanicProp (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (rem loc : AddrGhost) (st : SessionState (List (BitVec 8)))
    (msg : SignalMessage) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (s0 sf : State) (Pf : SepProp) : Prop :=
  ∀ R : SepProp, (sf.mem ⊨ Pf ∗ R) →
    sf.mem ⊨
      (⌜st.version = msgVer ∧
          (genP3S5Model C K rem loc msg rest st).1 = .error .panic ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R

/-- Full Stage P3 panic postcondition: either allocator OOM (`P3P4.PanicOomProp s0`) or the tight
model-panic disjunct of `tryDecryptPqOnPanicTight` at `(st, msg, rest)` with `st.version = msgVer`. -/
@[expose] def genP3S5PanicProp (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (rem loc : AddrGhost) (st : SessionState (List (BitVec 8)))
    (msg : SignalMessage) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (s0 sf : State) (Pf : SepProp) : Prop :=
  P3P4.PanicOomProp s0 sf Pf ∨
    genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0 sf Pf

/-- Existential witness for the six low front-spill stack slots `[+0x48, +0x50, +0x5c, +0x7c, +0x98, +0xd0]`
preserved untouched across Stage P3 Sub5 after splitting `memRegion (sp + 0x930#64) 48` out of
`genP3SpillAll sp`. -/
structure GenP3S5FrontRem where
  u48 : BitVec 64
  u50 : BitVec 64
  u98 : BitVec 64
  ud0 : BitVec 64
  u5c : BitVec 32
  u7c : BitVec 32

/-- Stack spill slots from `genP3SpillAll sp` untouched after splitting off
`memRegion (sp + 0x930#64) 48` for `stageP3DispatchPre`. -/
@[expose] def genP3S5SpillRem (sp : BitVec 64) : SepProp :=
  genP3PendSpillScratch sp ∗
    genP3TailSpillScratch sp ∗
    genP3ChainsSpillScratch sp ∗
    (∃∗ w : GenP3S5FrontRem,
      ((sp + 0x48#64) ↦₆₄ w.u48) ∗
      ((sp + 0x50#64) ↦₆₄ w.u50) ∗
      ((sp + 0x5c#64) ↦₃₂ w.u5c) ∗
      ((sp + 0x7c#64) ↦₃₂ w.u7c) ∗
      ((sp + 0x98#64) ↦₆₄ w.u98) ∗
      ((sp + 0xd0#64) ↦₆₄ w.ud0)) ∗
    memRegion (sp + 0x960#64) 48

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
