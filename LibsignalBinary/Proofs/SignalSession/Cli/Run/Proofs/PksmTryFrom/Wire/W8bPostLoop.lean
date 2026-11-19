/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresence -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: Post-Loop `Ok` Dispatch (`+0x460 → +0x5b4` / Presence Error)

Proves `preKeyPostLoopOkW_of_5b4`, discharging `PreKeyPostLoopOkW` (`+0x460 → ret` on
`some m`) into `post_seg1_xok_to_5b4_wpW` + `PreKey5b4OkW` when all four required fields
are `some`, and `PreKeyPresenceErrW` when any required field is `none`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

/-! ## 1. Raw `Option<u32>` cells -/

/-- The raw `(tag, val)` cells of a stack `Option<u32>` holding `o` (`none`: `tag = 0`, `val`
arbitrary; `some v`: `tag = 1`, `val = v`). -/
@[expose] def w8bOptU32Cells : Option (BitVec 32) → BitVec 32 × BitVec 32 → Prop
  | none, p => p.1 = 0#32
  | some v, p => p.1 = 1#32 ∧ p.2 = v

/-- `Option<u32>` at `a` as raw `(tag, val)` cells (witness bundled with its cell facts). -/
theorem w8b_optU32At_entails (a : BitVec 64) (o : Option (BitVec 32)) :
    CryptoVerification.LibsignalTripleRatchet.Prost.optU32At a o ⊢
      ∃∗ p : {p : BitVec 32 × BitVec 32 // w8bOptU32Cells o p},
        (a ↦₃₂ p.1.1) ∗ ((a + 4#64) ↦₃₂ p.1.2) := by
  cases o with
  | none =>
    have h4 : memRegion (a + 4#64) 4 = ∃∗ v : BitVec 32, (a + 4#64) ↦₃₂ v :=
      IsBlock.eq (IsBlock.memRegion (a + 4#64) 4)
        (IsBlock.sepExists fun v => IsBlock.pointsTo32 (a + 4#64) v)
        fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩
    simp only [CryptoVerification.LibsignalTripleRatchet.Prost.optU32At, h4,
      sepExists_sepConj_right]
    exact Entails.sepExists_elim fun v =>
      Entails.sepExists_intro
        (P := fun p : {p : BitVec 32 × BitVec 32 // w8bOptU32Cells none p} =>
          (a ↦₃₂ p.1.1) ∗ ((a + 4#64) ↦₃₂ p.1.2))
        ⟨(0#32, v), rfl⟩
  | some v =>
    simp only [CryptoVerification.LibsignalTripleRatchet.Prost.optU32At]
    exact Entails.sepExists_intro
      (P := fun p : {p : BitVec 32 × BitVec 32 // w8bOptU32Cells (some v) p} =>
        (a ↦₃₂ p.1.1) ∗ ((a + 4#64) ↦₃₂ p.1.2))
      ⟨(1#32, v), ⟨rfl, rfl⟩⟩

/-! ## 2. Stack-scratch split and wire-struct unfolding -/

theorem w8b_memRegion296_split (sp' : BitVec 64) :
    memRegion sp' 296 =
      memRegion sp' 16 ∗ memRegion (sp' + 16#64) 96 ∗ memRegion (sp' + 112#64) 184 := by
  rw [show (296 : Nat) = 16 + 280 by decide, Prost.memRegion_split sp' 16 280 (by decide),
    show (280 : Nat) = 96 + 184 by decide,
    Prost.memRegion_split (sp' + BitVec.ofNat 64 16) 96 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- `wirePreKeyAt` with the three required `Option<Vec<u8>>` fields and `signedPreKeyId` `some`. -/
theorem w8b_wirePreKeyAt_some_eq (A : RustAlloc) (g : WirePreKeyGhost) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) {bk ik msg : List (BitVec 8)} (hbk : m.baseKey = some bk)
    (hik : m.identityKey = some ik) (hmsg : m.message = some msg) {spkId : BitVec 32}
    (hspk : m.signedPreKeyId = some spkId) :
    wirePreKeyAt A g a m =
      (CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.kyberCt a
          m.kyberCiphertext ∗
        (vecHeader (a + 0x18#64) g.baseKey.cap g.baseKey.ptr (BitVec.ofNat 64 bk.length) ∗
          Wire.vecU8Buf A g.baseKey.cap g.baseKey.ptr bk) ∗
        (vecHeader (a + 0x30#64) g.identityKey.cap g.identityKey.ptr
            (BitVec.ofNat 64 ik.length) ∗
          Wire.vecU8Buf A g.identityKey.cap g.identityKey.ptr ik) ∗
        (vecHeader (a + 0x48#64) g.message.cap g.message.ptr (BitVec.ofNat 64 msg.length) ∗
          Wire.vecU8Buf A g.message.cap g.message.ptr msg) ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x60#64) m.registrationId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x68#64) m.preKeyId ∗
        (((a + 0x70#64) ↦₃₂ 1#32) ∗ ((a + 0x70#64 + 4#64) ↦₃₂ spkId)) ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x78#64) m.kyberPreKeyId) := by
  unfold wirePreKeyAt
  rw [hbk, hik, hmsg, hspk]
  rfl

/-! ## 3. Frames and the `+0x5b4` continuation -/

/-- Presence check post-frame at `+0x5b4` (the `Pf` of `post_seg1_xok_to_5b4_wpW`). -/
@[expose] def w8bXokPost (A : RustAlloc) (sp' bkCap bkPtr kyberCap kyberPtr kyberLen ikCap ikPtr msgCap msgPtr :
    BitVec 64) (regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) (bk ik msg : List (BitVec 8)) : SepProp :=
  seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
      ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
      regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
    memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
    Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
    A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
