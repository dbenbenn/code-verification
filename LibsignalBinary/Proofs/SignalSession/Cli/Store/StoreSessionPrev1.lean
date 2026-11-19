/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollX.Sym
import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# CLI `<SessionFiles as SessionStore>::store_session` on a `Prev1` Record

Contracts and proofs for `SessionFiles::store_session` when the input `SessionRecord` holds a
current session `sess` and one archived previous session `enc` (`sessionRecordPrevAt`):
- `sessStorePollPrev1Mem_ok_of_deps` and `sessStorePollPrev1_of_mem` prove the poll against
  `encodeRecordPrev1Mem` and canonical `encodeRecordPrev1`, buffering the serialized record via
  `Dir::put` with `sf.trace = s0.trace`;
- instantiations at `cliExterns W` and `CliExternsOk P A ext`, plus `FsInv` and `DirGhost.changed`
  preservation lemmas.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.Store.StoreSessionPrev1

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.Store.StorePollX.Helpers
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
open CliStorePollNorm
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre
  readVReg128_setMem_pre readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi

/-! ## 1. Ghost state and specifications for `store_session::{closure#0}` on `Prev1` -/

/-- Ghost inputs for `<SessionFiles as SessionStore>::store_session::{closure#0}` when the record
at `recA` has current session `sess` (ghost `G`) and one archived previous session `enc`. -/
structure SessStorePollPrev1Ghost where
  fut : BitVec 64
  self : BitVec 64
  out : BitVec 64
  addrA : BitVec 64
  addr : AddrGhost
  recA : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  enc : List (BitVec 8)
  dir : DirGhost

structure SerPrev1CellsGhost where
  recA : BitVec 64
  out : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  enc : List (BitVec 8)
  o0 : BitVec 64
  o1 : BitVec 64
  o2 : BitVec 64
  o3 : BitVec 64
  fsp : BitVec 64

@[expose] def serializePrev1CellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec SerPrev1CellsGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.recA ∧ s.readReg64 .x8 = g.out ∧ s.sp = g.fsp ∧
      (encodeRecordPrev1Mem g.G g.sess g.enc).length < 2 ^ 32⌝ ∗
    prevVecAt A g.recA g.prevCap g.prevPtr [g.enc] ∗
    sessionStateReprAt A (g.recA + 24#64) g.G g.sess ∗
    (g.out ↦₆₄ g.o0) ∗ ((g.out + 8#64) ↦₆₄ g.o1) ∗
    ((g.out + 16#64) ↦₆₄ g.o2) ∗ ((g.out + 24#64) ↦₆₄ g.o3) ∗
    A.pool ∗ stackAt g.fsp calleeStk
  post := fun g s0 sf =>
    ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      prevVecAt A g.recA g.prevCap g.prevPtr [g.enc] ∗
      sessionStateReprAt A (g.recA + 24#64) g.G g.sess ∗
      (g.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((g.out + 8#64) ↦₆₄ bCap) ∗ ((g.out + 16#64) ↦₆₄ bPtr) ∗
      ((g.out + 24#64) ↦₆₄ BitVec.ofNat 64 (encodeRecordPrev1Mem g.G g.sess g.enc).length) ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr (encodeRecordPrev1Mem g.G g.sess g.enc) ∗
      A.pool ∗ stackAt g.fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem close_panic_prev1 {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame (F := F) ?_ (by simpa only [sepConj_assoc] using hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private theorem cells_26_split_prev1 (sp : BitVec 64) :
    cells (sp - 208#64) 26 =
      storePollSlack sp ∗
        cells (sp - 200#64) 6 ∗ cells (sp - 144#64) 4 ∗
        cells (sp - 96#64) 5 ∗ cells (sp - 48#64) 6 := by
  rw [show (26 : Nat) = 1 + 25 from rfl, cells_split_sub sp 208 200 1 25,
    show (25 : Nat) = 6 + 19 from rfl, cells_split_sub sp 200 152 6 19,
    show (19 : Nat) = 1 + 18 from rfl, cells_split_sub sp 152 144 1 18,
    show (18 : Nat) = 4 + 14 from rfl, cells_split_sub sp 144 112 4 14,
    show (14 : Nat) = 2 + 12 from rfl, cells_split_sub sp 112 96 2 12,
    show (12 : Nat) = 5 + 7 from rfl, cells_split_sub sp 96 56 5 7,
    show (7 : Nat) = 1 + 6 from rfl, cells_split_sub sp 56 48 1 6]
  dsimp only [storePollSlack]
  ac_rfl

private theorem cells_sub_4_eq_prev1 (sp : BitVec 64) :
    cells (sp - 144#64) 4 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗
        ((sp - 128#64) ↦₆₄ v2) ∗ ((sp - 120#64) ↦₆₄ v3) := by
  cells_unfold

private theorem cells_sub_5_eq_prev1 (sp : BitVec 64) :
    cells (sp - 96#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) := by
  cells_unfold

private theorem cells_sub_6_200_eq_prev1 (sp : BitVec 64) :
    cells (sp - 200#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 200#64) ↦₆₄ v0) ∗ ((sp - 192#64) ↦₆₄ v1) ∗ ((sp - 184#64) ↦₆₄ v2) ∗
        ((sp - 176#64) ↦₆₄ v3) ∗ ((sp - 168#64) ↦₆₄ v4) ∗ ((sp - 160#64) ↦₆₄ v5) := by
  cells_unfold

private theorem cells_sub_6_48_eq_prev1 (sp : BitVec 64) :
    cells (sp - 48#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5) := by
  cells_unfold

@[expose] def cliStorePollPrev1InnerSpec (A : RustAlloc) (calleeStk : Nat) : Spec SessStorePollPrev1Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.addr.name.bytes.length < 2 ^ 32 ∧
      (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32 ∧
      x.dir.changed.length < 2 ^ 32⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₆₄ x.addrA) ∗
      ((x.fut + 16#64) ↦₆₄ x.recA) ∗ ((x.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.addr x.addrA ∗
      prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗
      A.pool ∗ stackAt (s.sp - 208#64) calleeStk ∗ cells (s.sp - 208#64) 26
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₆₄ x.addrA) ∗
      ((x.fut + 16#64) ↦₆₄ x.recA) ∗ ((x.fut + 24#64) ↦₈ 1#8) ∗
      dirAt A x.self
        (x.dir.put (addressText x.addr.val) (encodeRecordPrev1Mem x.G x.sess x.enc)) ∗
      (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.out + 8#64) 40 ∗
      protocolAddressAt A x.addr x.addrA ∗
      prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗
      A.pool ∗ stackAt (s0.sp - 208#64) calleeStk ∗ cells (s0.sp - 208#64) 26
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `DirGhost.changed` bound preservation under `d.put (addressText peer.val) bytes`: holds
for arbitrary serialized `bytes` (including `encodeRecordPrev1` / `encodeRecordPrev1Mem`),
and guarantees `addressText peer.val ∈ (d.put ...).changed.map Prod.fst` afterwards. -/
theorem changedLt_put_self {peer : AddrGhost} {d : DirGhost} (bytes : List (BitVec 8))
    (h : d.changed.length < 2 ^ 32 ∧
      (d.changed.length + 1 < 2 ^ 32 ∨ addressText peer.val ∈ d.changed.map Prod.fst)) :
    (d.put (addressText peer.val) bytes).changed.length < 2 ^ 32 ∧
      ((d.put (addressText peer.val) bytes).changed.length + 1 < 2 ^ 32 ∨
        addressText peer.val ∈ (d.put (addressText peer.val) bytes).changed.map Prod.fst) := by
  obtain ⟨hlt, hroom⟩ := h
  refine ⟨?_, Or.inr (KitInst.mem_setOrPush_self _ _ _)⟩
  show (DirGhost.setOrPush _ _ d.changed).length < 2 ^ 32
  rcases hroom with hroom | hmem
  · exact Nat.lt_of_le_of_lt (KitInst.setOrPush_length_le _ _ _) hroom
  · rw [KitInst.setOrPush_length_of_mem hmem]; exact hlt

/-! ## 5. Contract-backed instantiations (`CliExternsOk P A ext` & `AllocContractsX`) -/

attribute [local irreducible] Program.fnOff

private theorem serializeName_eq_recordSerializeName :
    E2E.Record.Serialization.serializeName = recordSerializeName := rfl

end CryptoVerification.SignalSession.Cli.Store.StoreSessionPrev1
