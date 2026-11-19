/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.New -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Decodes -- proof-setup: allow-public-import
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `spqr::init_inner` (`0x532dc..0x5349c`, 112 instructions): Definitions and Specifications

**Checked by Lean.**

Defines instruction-fetch helpers, pure evaluation models `initV1State` / `initInnerValue`
agreeing with `initInner (spqrDeps F K)`, and separation-logic specifications `initInnerSpec`,
`initInnerSpecX`, and `initInnerSpecExt` for `spqr::init_inner`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.InitInner

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## 1. Symbol Name, Instruction Decodes, and Stack Budgets -/

/-- Symbol name of `spqr::init_inner` (`0x532dc..0x5349c`, 112 instructions, 448 bytes). -/
abbrev initInnerName : String := "spqr::init_inner"

/-- Own stack frame of `spqr::init_inner` (`48 + 992 = 1040` bytes = `0x410`). -/
abbrev initInnerFrame : Nat := 1040

/-- Stack budget of `spqr::init_inner` (`1040 + authNewStackX = 1296 + extHookStack`).
    Note `statesIntoPbStack = 5872 ≤ 16640 = authNewStackX`, so `authNewStackX` dominates
    all callees of `spqr::init_inner`. -/
abbrev initInnerStack : Nat := initInnerFrame + authNewStackX

/-- Extended-stack budget of `spqr::init_inner` (`= initInnerStack = 1296 + extHookStack`). -/
abbrev initInnerStackX : Nat := initInnerStack

/-! ## 2. Total Pure Model of `initInner` and Agreement with `spqrDeps` -/

/-- Initial 96-byte header+MAC `PolyDecoder` constructed by `States.init_b`:
    `ptsNeeded = 48`, `isComplete = false`, and 16 empty `SortedSetPt`s. -/
@[expose] def initHdrDecoder : PolyDecoder :=
  { ptsNeeded := 48
    isComplete := false
    pts := List.replicate 16 (SortedSetPt.withCapacity 0) }

@[simp]
theorem polyDecoderNew_96_eq :
    PolyDecoder.new (HEADER_SIZE + 32) = .ok (.ok initHdrDecoder) := rfl

/-- Total initial `States` constructed for `.v1` by `States.init_a` (`.a2b`) or
    `States.init_b` (`.b2a`). -/
@[expose] def initV1State (F : ShaCompress) (d : Direction) (authKey : Bytes) :
    States spqrPolyApi (spqrAuthApi F) :=
  match d with
  | .a2b =>
    .keysUnsampled { uc := { epoch := 1#64, auth := Authenticator.new F authKey 1#64 } }
  | .b2a =>
    .noHeaderReceived
      { uc := { epoch := 1#64, auth := Authenticator.new F authKey 1#64 }
        receiving_hdr := initHdrDecoder }

@[simp]
theorem states_init_a_eq_ok (F : ShaCompress) (authKey : Bytes) :
    States.init_a spqrPolyApi (spqrAuthApi F) authKey =
      .ok (initV1State F .a2b authKey) := rfl

@[simp]
theorem states_init_b_eq_ok (F : ShaCompress) (authKey : Bytes) :
    States.init_b spqrPolyApi (spqrAuthApi F) authKey =
      .ok (initV1State F .b2a authKey) := rfl

@[simp]
theorem spqrDeps_initV1Inner_eq_ok (F : ShaCompress) (K : MlKem)
    (d : Direction) (authKey : Bytes) :
    (spqrDeps F K).initV1Inner d authKey =
      .ok (initV1State F d authKey).into_pb := by
  cases d <;> rfl

/-- Total result of `initInner (spqrDeps F K) v d authKey`. -/
@[expose] def initInnerValue (F : ShaCompress) (v : Version) (d : Direction) (authKey : Bytes) :
    Option V1State :=
  match v with
  | .v0 => none
  | .v1 => some (initV1State F d authKey).into_pb

@[simp]
theorem initInner_spqrDeps_eq_ok (F : ShaCompress) (K : MlKem)
    (v : Version) (d : Direction) (authKey : Bytes) :
    initInner (spqrDeps F K) v d authKey =
      .ok (initInnerValue F v d authKey) := by
  cases v with
  | v0 => rfl
  | v1 => cases d <;> rfl

/-! ## 3. Specifications of `spqr::init_inner` (`0x532dc`) -/

/-- Binary layout of the 224-byte `Option<spqr::proto::pq_ratchet::pq_ratchet_state::Inner>`
    written at `out` (`x0`) by `spqr::init_inner`:
    * `v = .v0`: `optProtoPqRatchetInnerAt A out none` (`(out ↦₆₄ none3Cap') ∗ memRegion (out + 8) 216`)
    * `v = .v1`: `optProtoInnerStateAt A out (initV1State F d authKey).into_pb.innerState` -/
@[expose] def initInnerResultAt (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (v : Version) (d : Direction) (authKey : Bytes) : SepProp :=
  optProtoPqRatchetInnerAt A out ((initInnerValue F v d authKey).map PqRatchetState.Inner.v1)

@[simp]
theorem initInnerResultAt_v0 (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (d : Direction) (authKey : Bytes) :
    initInnerResultAt A (F := F) out .v0 d authKey =
      optProtoPqRatchetInnerAt A out none := rfl

@[simp]
theorem initInnerResultAt_v1 (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (d : Direction) (authKey : Bytes) :
    initInnerResultAt A (F := F) out .v1 d authKey =
      optProtoInnerStateAt A out (initV1State F d authKey).into_pb.innerState := rfl

/-- Ghost arguments of `spqr::init_inner` (`0x532dc`). -/
structure InitInnerGhost where
  /-- Indirect return pointer (`x0`, 224-byte `Option<pq_ratchet_state::Inner>` output). -/
  out : BitVec 64
  /-- Negotiated protocol version (`w1 = v.toI32`). -/
  v : Version
  /-- Ratchet direction (`w2 = d.toI32`). -/
  d : Direction
  /-- Slice pointer for `auth_key: &[u8]` (`x3`, non-null). -/
  akPtr : BitVec 64
  /-- Byte contents of `auth_key: &[u8]` (`x4 = BitVec.ofNat 64 authKey.length`). -/
  authKey : Bytes

/-- Panic postcondition of `spqr::init_inner`: heap allocation failure (`allocFailedIn`). -/
@[expose] def initInnerOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract-backed (`AuthNewOkExt` / `extHookStack`) stack budget for `spqr::init_inner`:
    `1040`B own frame + `authNewStackExt` (`17872`B) = `18912`B (`= initInnerStack + 1232`). -/
abbrev initInnerStackExt : Nat := 1040 + authNewStackExt

theorem initInnerStackExt_eq : initInnerStackExt = 18912 := rfl

theorem initInnerStackExt_eq_add : initInnerStackExt = initInnerStack + 1232 := rfl

end CryptoVerification.SpqrV1.Top.InitInner
