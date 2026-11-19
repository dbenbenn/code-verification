/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Decodes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Drop.StatesRepr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Definitions, Specifications, and Dispatch

**Checked by Lean.**

Defines the `Result<States, spqr::Error>` (`928` B) representation predicate, the total
`<PolyDecoder>::from_pb` pure model and callee contract, top-level and per-variant Hoare
specifications for `<States>::from_pb` (`0x5a0a4`, 2,911 instructions), and prologue, epilogue,
and `None`-variant stepping lemmas.
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. `Result<States, spqr::Error>` Representation (`928`B = `0x3a0`) -/

/-- `spqr::Error` `u8` discriminant in `Result<States, spqr::Error>` at `out + 8`:
    * `0#8`: `Error::StateDecode`
    * `1#8`: `Error::EpochOutOfRange` (carries `u64` at `out + 16`, unused in `from_pb`)
    * `2#8`: `Error::MsgDecode`
    * `3#8`: `Error::MacVerifyFailed`
    * `4#8`: `Error::ErroneousDataReceived` -/
@[expose] def spqrErrorByte : LibsignalSpqrV1.Error → BitVec 8
  | .stateDecode => 0#8
  | .epochOutOfRange _ => 1#8
  | .msgDecode => 2#8
  | .macVerifyFailed => 3#8
  | .erroneousDataReceived => 4#8
  | _ => 0#8

/-- Binary layout of `Result<spqr::v1::chunked::states::States, spqr::Error>` (`928`B = `0x3a0`):
    * `.ok st`: `chunkedStatesAt A out st` (`928`B)
    * `.error (.err err)`: `(out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ spqrErrorByte err) ∗ memRegion (out + 9#64) 919`
    * `.error (.panic _)`: `⌜False⌝` (`States.from_pb` never returns `.error (.panic _)`). -/
@[expose] def resultChunkedStatesAt (A : RustAlloc) {F : ShaCompress} (out : BitVec 64) :
    StatesResult (States spqrPolyApi (spqrAuthApi F)) → SepProp
  | .ok st => chunkedStatesAt A out st
  | .error (.err err) =>
    (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ spqrErrorByte err) ∗ memRegion (out + 9#64) 919
  | .error (.panic _) => ⌜False⌝

theorem memRegion_out_928_split_err (out : BitVec 64) :
    memRegion out chunkedStatesSize =
      (∃∗ v0 : BitVec 64, (out ↦₆₄ v0)) ∗
      (∃∗ b8 : BitVec 8, ((out + 8#64) ↦₈ b8)) ∗
      memRegion (out + 9#64) 919 := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split out 8 920 (by decide),
      ProofLib.memRegion_eight out,
      ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 919)
        (b' := out + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one (out + 8#64)]

/-! ## 2. Total Pure Model and Contract for `<PolyDecoder>::from_pb` (`0x62b1c`) -/

/-- Symbol name of `<spqr::encoding::polynomial::PolyDecoder>::from_pb` (`0x62b1c`, 325 insns). -/
abbrev decoderFromPbName : String :=
  "<spqr::encoding::polynomial::PolyDecoder>::from_pb"

/-- Stack budget of `<PolyDecoder>::from_pb` (`1056 + allocHookStack`, matching `encoderFromPbStack`). -/
abbrev decoderFromPbStack : Nat := encoderFromPbStack

/-- Total version of `PolyDecoder.pushChunksExact4` on 4-byte-aligned byte lists. -/
@[expose] def pushChunksExact4Total : List (BitVec 8) → SortedSetPt → SortedSetPt
  | b0 :: b1 :: b2 :: b3 :: rest, v =>
    let pt : Pt := { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
    let (v', _, _) := v.push pt
    pushChunksExact4Total rest v'
  | _, v => v

theorem pushChunksExact4_eq_ok :
    ∀ (pts : List (BitVec 8)) (v : SortedSetPt),
      pts.length % 4 = 0 →
      PolyDecoder.pushChunksExact4 pts v = .ok (pushChunksExact4Total pts v)
  | [], v, _ => rfl
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | [_, _, _], _, h => by simp at h
  | b0 :: b1 :: b2 :: b3 :: rest, v, h => by
    have hrest : rest.length % 4 = 0 := by
      simp only [List.length_cons] at h
      omega
    unfold PolyDecoder.pushChunksExact4 pushChunksExact4Total
    change (do
      let pt ← Pt.deserialize [b0, b1, b2, b3]
      let (v', _, _) := v.push pt
      PolyDecoder.pushChunksExact4 rest v') = _
    have hpt : Pt.deserialize [b0, b1, b2, b3] =
        .ok { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) } := rfl
    rw [hpt]
    exact pushChunksExact4_eq_ok rest (v.push { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }).1 hrest

/-- Total version of `PolyDecoder.decodeDecoderPbPts`. -/
@[expose] def decodeDecoderPbPtsTotal : List (List (BitVec 8)) → Except PolynomialError (List SortedSetPt)
  | [] => .ok []
  | pts :: rest =>
    if pts.length % 4 != 0 then
      .error .serializationInvalid
    else
      let v := pushChunksExact4Total pts (SortedSetPt.withCapacity (pts.length / 4))
      match decodeDecoderPbPtsTotal rest with
      | .error e => .error e
      | .ok tail => .ok (v :: tail)

theorem decodeDecoderPbPts_eq_ok (bss : List (List (BitVec 8))) :
    PolyDecoder.decodeDecoderPbPts bss = .ok (decodeDecoderPbPtsTotal bss) := by
  induction bss with
  | nil => rfl
  | cons pts rest ih =>
    unfold PolyDecoder.decodeDecoderPbPts decodeDecoderPbPtsTotal
    by_cases hmod : (pts.length % 4 != 0) = true
    · simp [hmod, pure, Except.pure]
    · have hdiv4 : pts.length % 4 = 0 := by
        simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hmod
        exact hmod
      simp only [hmod, Bool.false_eq_true, ↓reduceIte,
        pushChunksExact4_eq_ok pts (SortedSetPt.withCapacity (pts.length / 4)) hdiv4,
        ih, bind, Except.bind, pure, Except.pure]
      cases decodeDecoderPbPtsTotal rest <;> rfl

/-- Total result of `PolyDecoder.fromPb pb`. -/
@[expose] def decoderFromPbResult (pb : ProtoPolynomialDecoder) : Except PolynomialError PolyDecoder :=
  if pb.pts.length != 16 then
    .error .serializationInvalid
  else
    match decodeDecoderPbPtsTotal pb.pts with
    | .error e => .error e
    | .ok outPts =>
      .ok
        { ptsNeeded := pb.ptsNeeded.toNat
          isComplete := pb.isComplete
          pts := outPts }

theorem decoderFromPb_eq_ok (pb : ProtoPolynomialDecoder) :
    PolyDecoder.fromPb pb = .ok (decoderFromPbResult pb) := by
  unfold PolyDecoder.fromPb decoderFromPbResult
  by_cases hlen : (pb.pts.length != 16) = true
  · simp [hlen, pure, Except.pure]
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte,
      decodeDecoderPbPts_eq_ok pb.pts, bind, Except.bind, pure, Except.pure]
    cases decodeDecoderPbPtsTotal pb.pts <;> rfl

@[simp]
theorem encoderFromPbStateDecode_none :
    encoderFromPbStateDecode spqrPolyApi none = .error (.err .stateDecode) := rfl

@[simp]
theorem encoderFromPbStateDecode_some (pb : PolynomialEncoder) :
    encoderFromPbStateDecode spqrPolyApi (some pb) =
      match fromPbResult (pbToProtoPolyEncoder pb) with
      | .ok enc => .ok enc
      | .error _ => .error (.err .stateDecode) := by
  unfold encoderFromPbStateDecode spqrPolyApi
  dsimp only
  rw [fromPb_eq_ok (pbToProtoPolyEncoder pb)]
  cases fromPbResult (pbToProtoPolyEncoder pb) <;> rfl

@[simp]
theorem decoderFromPbStateDecode_none :
    decoderFromPbStateDecode spqrPolyApi none = .error (.err .stateDecode) := rfl

@[simp]
theorem decoderFromPbStateDecode_some (pb : PolynomialDecoder) :
    decoderFromPbStateDecode spqrPolyApi (some pb) =
      match decoderFromPbResult (pbToProtoPolyDecoder pb) with
      | .ok dec => .ok dec
      | .error _ => .error (.err .stateDecode) := by
  unfold decoderFromPbStateDecode spqrPolyApi
  dsimp only
  rw [decoderFromPb_eq_ok (pbToProtoPolyDecoder pb)]
  cases decoderFromPbResult (pbToProtoPolyDecoder pb) <;> rfl

/-- Ghost arguments of `<PolyDecoder>::from_pb` (`0x62b1c`). -/
structure DecoderFromPbGhost where
  /-- Sret pointer (`x0`, 400-byte `Result<PolyDecoder, PolynomialError>` output). -/
  out : BitVec 64
  /-- Pointer to the 40-byte `ProtoPolynomialDecoder` moved by value (`x1`). -/
  pbA : BitVec 64
  /-- Logical `ProtoPolynomialDecoder` value at `pbA`. -/
  pb : ProtoPolynomialDecoder

/-- Specification of `<spqr::encoding::polynomial::PolyDecoder>::from_pb` (`0x62b1c`, 325 insns). -/
@[expose] def decoderFromPbSpec (A : RustAlloc) : Spec DecoderFromPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp decoderFromPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyDecoderFromPbAt A x.out (decoderFromPbResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool ∗ stackAt s0.sp decoderFromPbStack
  onPanic := fun _ s0 sf => encoderFromPbOnPanic s0 sf

/-- Point-slice length bound required by `<PolyEncoder>::from_pb` (`encoderFromPbSpec`). -/
@[expose] def optEncoderPtsBound : Option PolynomialEncoder → Prop
  | none => True
  | some enc => ∀ bs ∈ enc.pts, bs.length ≤ 2 * 0x0555555555555555

/-- Point-slice length bound on any `PolynomialEncoder` inside a `V1State`. -/
@[expose] def v1StatePtsBound (pb : V1State) : Prop :=
  match pb.innerState with
  | some (.keysSampled s) => optEncoderPtsBound s.sendingHdr
  | some (.headerSent s) => optEncoderPtsBound s.sendingEk
  | some (.ct1Received s) => optEncoderPtsBound s.sendingEk
  | some (.ct1Sampled s) => optEncoderPtsBound s.sendingCt1
  | some (.ekReceivedCt1Sampled s) => optEncoderPtsBound s.sendingCt1
  | some (.ct2Sampled s) => optEncoderPtsBound s.sendingCt2
  | _ => True

/-- Own stack frame of `<States>::from_pb` (`96 + 2304 = 2400` bytes = `0x960`). -/
abbrev statesFromPbFrame : Nat := 2400

/-- Stack budget of `<States>::from_pb` (`2400 + encoderFromPbStack = 3456 + allocHookStack`). -/
abbrev statesFromPbStack : Nat := statesFromPbFrame + encoderFromPbStack

/-- Extended-stack budget of `<States>::from_pb` (`2400 + extHookStack`). -/
abbrev statesFromPbStackX : Nat := statesFromPbFrame + extHookStack

/-- Ghost arguments of `<spqr::v1::chunked::states::States>::from_pb` (`0x5a0a4`). -/
structure StatesFromPbGhost where
  /-- Indirect return pointer (`x8`, 928-byte `Result<States, spqr::Error>` output). -/
  out : BitVec 64
  /-- Pointer to consumed 224-byte `V1State` (`x0`). -/
  pbA : BitVec 64
  /-- Logical `V1State` value at `pbA`. -/
  pb : V1State

/-- Panic postcondition of `<States>::from_pb`: heap allocation failure (`allocFailedIn`). -/
@[expose] def statesFromPbOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Saved callee-saved registers at `[s0.sp - 96 .. s0.sp)` (`12` words = `96` bytes):
    `fp, lr, x28, x27, x26, x25, x24, x23, x22, x21, x20, x19`. -/
@[expose] def statesFromPbSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_statesFromPb_split_96 (sp : BitVec 64) :
    stackAt sp statesFromPbStack =
      stackAt (sp - 96#64) (encoderFromPbStack + 2304) ∗ cells (sp - 96#64) 12 :=
  ProofLib.stackAt_split_cells sp (encoderFromPbStack + 2304) 12 (by decide)

theorem stackAt_statesFromPb_split_fsp (sp : BitVec 64) :
    stackAt (sp - 96#64) (encoderFromPbStack + 2304) =
      stackAt (sp - 2400#64) encoderFromPbStack ∗ memRegion (sp - 2400#64) 2304 := by
  simp only [stackAt]
  rw [ProofLib.memRegion_split ((sp - 96#64) - BitVec.ofNat 64 (encoderFromPbStack + 2304))
    encoderFromPbStack 2304 (by decide)]
  have h1 : (sp - 96#64) - BitVec.ofNat 64 (encoderFromPbStack + 2304) =
      (sp - 2400#64) - BitVec.ofNat 64 encoderFromPbStack := by
    change (sp - 96#64) - 7456#64 = (sp - 2400#64) - 5152#64
    bv_omega
  have h2 : (sp - 96#64) - BitVec.ofNat 64 (encoderFromPbStack + 2304) +
      BitVec.ofNat 64 encoderFromPbStack = sp - 2400#64 := by
    change (sp - 96#64) - 7456#64 + 5152#64 = sp - 2400#64
    bv_omega
  rw [h2, h1]

theorem memRegion_2304_split_cell0 (fsp : BitVec 64) :
    memRegion fsp 2304 =
      (∃∗ v0 : BitVec 64, (fsp ↦₆₄ v0)) ∗ memRegion (fsp + 8#64) 2296 := by
  rw [ProofLib.memRegion_split fsp 8 2296 (by decide),
      ProofLib.memRegion_eight fsp]

theorem cell0_2296_entails_memRegion_2304 (fsp v0 : BitVec 64) :
    (fsp ↦₆₄ v0) ∗ memRegion (fsp + 8#64) 2296 ⊢ memRegion fsp 2304 := by
  rw [ProofLib.memRegion_split fsp 8 2296 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion fsp v0)

theorem statesFromPbSavedCells_entails_cells12 (s0 : State) :
    statesFromPbSavedCells s0 ⊢ cells (s0.sp - 96#64) 12 := by
  unfold statesFromPbSavedCells
  cells_unfold
  exact Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x27)
          (Entails.sepExists_right (s0.readReg64 .x26)
            (Entails.sepExists_right (s0.readReg64 .x25)
              (Entails.sepExists_right (s0.readReg64 .x24)
                (Entails.sepExists_right (s0.readReg64 .x23)
                  (Entails.sepExists_right (s0.readReg64 .x22)
                    (Entails.sepExists_right (s0.readReg64 .x21)
                      (Entails.sepExists_right (s0.readReg64 .x20)
                        (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))))))

theorem stack_restore_statesFromPb (s0 : State) :
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ⊢
      stackAt s0.sp statesFromPbStack := by
  rw [stackAt_statesFromPb_split_96 s0.sp, stackAt_statesFromPb_split_fsp s0.sp, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (statesFromPbSavedCells_entails_cells12 s0))

@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_16 (sp : BitVec 64) : (sp - 96#64) + 16#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_32 (sp : BitVec 64) : (sp - 96#64) + 32#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_48 (sp : BitVec 64) : (sp - 96#64) + 48#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_64 (sp : BitVec 64) : (sp - 96#64) + 64#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_80 (sp : BitVec 64) : (sp - 96#64) + 80#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_2304 (sp : BitVec 64) : (sp - 96#64) - 2304#64 = sp - 2400#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_2400_add_2304 (sp : BitVec 64) : (sp - 2400#64) + 2304#64 = sp - 96#64 := by bv_omega

/-- Combined trace and callee-saved SIMD register preservation from `s0` to `s`. -/
abbrev TraceCalleeSaved (s s0 : State) : Prop :=
  s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem _root_.And.trans {α β : Type _} {a1 a2 a3 : α} {b1 b2 b3 : β}
    (h1 : a1 = a2 ∧ b1 = b2) (h2 : a2 = a3 ∧ b2 = b3) :
    a1 = a3 ∧ b1 = b3 :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-! ## 5. Prologue (`+0 -> +36`), Epilogue (`+64 -> +92`), and `None` Path (`0x5a0a4`) -/

end CryptoVerification.SpqrV1.States.FromPb
