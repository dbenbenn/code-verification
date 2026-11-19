/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeVarintSlowX
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefs -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2 -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Key Decode and Jump-Table Dispatch (`+0x216c → overDecArmOff fl`)

Verifies key decoding and `.rodata` jump-table dispatch (`overDecKey_of`, `overDecKey_cli_ok`) at
`+0x216c..+0x21b8` in `message_decrypt_prekey::<Coins>::{closure#0}`, calling `decode_varint [local#5]`
and branching via `br x9` to `entry + overDecArmOff fl`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.CodeLayout SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint (decodeVarint2SpecX decodeVarint2StackX)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (decodeVarint5Name)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem allowPanic_oom_of_trace_eq {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    rintro ⟨ha, hp⟩
    unfold allocFailedIn at ha ⊢
    rw [← htr]
    exact ⟨ha, hp⟩
  exact allowPanic_frame himp hm

private theorem stackAt_sub_eq (sp : BitVec 64) (M N : Nat) (hMN : N ≤ M := by decide)
    (hbound : M < 2 ^ 64 := by decide) :
    stackAt sp M = stackAt sp N ∗ memRegion (sp - BitVec.ofNat 64 M) (M - N) := by
  have h1 : M = N + (M - N) := (Nat.add_sub_of_le hMN).symm
  have h2 := ProofLib.stackAt_split_bottom sp N (M - N) (by omega)
  rw [← h1] at h2
  rw [h2, sepConj_comm]

/-! ## Pure Helpers on `GenFieldQ` Keys and `.rodata` Jump Table -/

private theorem overDecWt_toNat_eq (fl : GenFieldQ) :
    (overDecWt fl).toNat = fl.wt.toNat := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl

/-- The 64-bit key value `fl.tag * 8 + (overDecWt fl).toNat` of `fl`. -/
abbrev overDecKeyVal (fl : GenFieldQ) : BitVec 64 :=
  BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat)

private theorem decodeVarint_fl_enc (fl : GenFieldQ) (rest : List (BitVec 8)) :
    decodeVarint (fl.enc ++ rest) = some (overDecKeyVal fl, fl.payload ++ rest) := by
  rw [GenFieldQ.enc, List.append_assoc, encodeKey, overDecKeyVal, overDecWt_toNat_eq fl]
  exact decodeVarint_encodeVarint _ _

/-- The 15-byte jump table in `.rodata` referenced by `adrp/add x11` at `+0x21a4/+0x21a8`. -/
abbrev overDecJtabBytes : List (BitVec 8) :=
  [0#8, 68#8, 63#8, 53#8, 11#8, 22#8, 73#8, 58#8, 101#8, 123#8, 117#8, 58#8, 6#8, 39#8, 17#8]

/-- The jump-table byte for `fl` (`overDecJtabBytes[fl.tag - 1]`). -/
@[expose] def overDecJtabByte (fl : GenFieldQ) : BitVec 8 :=
  match fl with
  | .base (.version _) => 0#8
  | .base (.lik _) => 68#8
  | .base (.rik _) => 63#8
  | .base (.root _) => 53#8
  | .base (.prevCounter _) => 11#8
  | .base (.sender _) => 22#8
  | .base (.recv _) => 73#8
  | .base (.pending _) | .pendingId _ _ | .pendingSpk _ _ _ => 101#8
  | .remReg _ => 123#8
  | .locReg _ => 117#8
  | .abk _ => 6#8
  | .kyber _ _ => 39#8
  | .pq _ => 17#8

private theorem holdsBytes_singleton_of_getElem {m : Memory} {addr : BitVec 64}
    {bs : List (BitVec 8)}
    (h : Arm64.Obj.HoldsBytes m addr bs (fun _ => .ro)) (i : Nat) (hi : i < bs.length) :
    Arm64.Obj.HoldsBytes m (addr + BitVec.ofNat 64 i) [bs[i]] (fun _ => .ro) := by
  intro j hj
  have hj0 : j = 0 := by simp at hj; omega
  subst hj0
  simpa using h i hi

private theorem overDecJtab_tag_sub_one_lt (fl : GenFieldQ) :
    fl.tag - 1 < overDecJtabBytes.length := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp [GenFieldQ.tag, GenField.tag, overDecJtabBytes]

private theorem overDecJtab_getElem_eq (fl : GenFieldQ) :
    overDecJtabBytes[fl.tag - 1]'(overDecJtab_tag_sub_one_lt fl) = overDecJtabByte fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl

private theorem fl_payload_rest_len_le (fl : GenFieldQ) (rest : List (BitVec 8)) :
    (fl.payload ++ rest).length ≤ (fl.enc ++ rest).length := by
  simp only [GenFieldQ.enc, List.length_append]
  omega

private theorem sliceCursorAfter_split_of_append (slot ptr : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) :
    Prost.sliceCursorAfter slot ptr (bs1 ++ bs2) bs2 =
      Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 bs1.length) bs2 ∗ (ptr ↦ₛ bs1) := by
  unfold Prost.sliceCursorAfter Prost.sliceCursorAt
  have hsub : (bs1 ++ bs2).length - bs2.length = bs1.length := by
    rw [List.length_append]; omega
  rw [hsub, pointsToBytes_append ptr bs1 bs2]
  ac_rfl

private theorem sliceCursorAfter_unsplit_of_append (slot ptr : BitVec 64)
    (bs1 bs2 bs3 : List (BitVec 8)) (hle : bs3.length ≤ bs2.length) :
    Prost.sliceCursorAfter slot (ptr + BitVec.ofNat 64 bs1.length) bs2 bs3 ∗ (ptr ↦ₛ bs1) =
      Prost.sliceCursorAfter slot ptr (bs1 ++ bs2) bs3 := by
  unfold Prost.sliceCursorAfter
  have hadd : (ptr + BitVec.ofNat 64 bs1.length) + BitVec.ofNat 64 (bs2.length - bs3.length) =
      ptr + BitVec.ofNat 64 ((bs1 ++ bs2).length - bs3.length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    rw [List.length_append]
    omega
  rw [hadd, pointsToBytes_append ptr bs1 bs2]
  ac_rfl

/-! ## Stage 1 (`+0x216c → +0x2174`): `decode_varint [local#5]` Call -/

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr32 (fl : GenFieldQ) :
    overDecKeyVal fl >>> 32#64 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr32_nat (fl : GenFieldQ) :
    overDecKeyVal fl >>> 32 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_and7 (fl : GenFieldQ) :
    overDecKeyVal fl &&& 7#64 = overDecWt fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecWt_ule6 (fl : GenFieldQ) :
    (6#64).ule (overDecWt fl) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecWt, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_trunc32_zext64 (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (overDecKeyVal fl)) = overDecKeyVal fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr3 (fl : GenFieldQ) :
    overDecKeyVal fl >>> 3 = BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_wlsr3 (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (overDecKeyVal fl) >>> 3#32) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_wlsr3_nat (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (overDecKeyVal fl) >>> 3) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecTag_trunc32_zext64 (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 fl.tag)) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_beq_zero (fl : GenFieldQ) :
    (BitVec.ofNat 64 fl.tag == 0#64) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_beq_zero (fl : GenFieldQ) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) == 0#32) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_64 (fl : GenFieldQ) :
    BitVec.ofNat 64 fl.tag - 1#64 = BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_add_neg1_64 (fl : GenFieldQ) :
    BitVec.ofNat 64 fl.tag + 0xffffffffffffffff#64 = BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_sub1 (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) - 1#32) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_add_neg1 (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) + 4294967295#32) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_trunc32_zext64 (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 (fl.tag - 1))) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_ult14 (fl : GenFieldQ) :
    (14#32).ult (BitVec.setWidth 32 (BitVec.ofNat 64 (fl.tag - 1))) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_ult14_64 (fl : GenFieldQ) :
    (14#64).ult (BitVec.ofNat 64 (fl.tag - 1)) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_add_armOff (fl : GenFieldQ) :
    8636#64 + (BitVec.setWidth 64 (overDecJtabByte fl) <<< 2#64) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_add_armOff_nat (fl : GenFieldQ) :
    8636#64 + (BitVec.setWidth 64 (overDecJtabByte fl) <<< 2) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_zext_add_armOff (fl : GenFieldQ) :
    8636#64 + (BitVec.zeroExtend 64 (overDecJtabByte fl) <<< 2) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

private theorem drop_left_sepWPp {prog : Program} {ret : BitVec 64}
    {s : State} {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
