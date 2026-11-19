/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.ReprBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoGames.LibsignalSessionApi
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

theorem canonRecord_of_satisfies_sessionRecordAt (A : RustAlloc) (a : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (R : SepProp) (m : Memory)
    (hm : m ⊨ sessionRecordAt A a g r ∗ R) :
    E2E.Record.Serialization.CanonRecord (E2E.InMem.SessionStoreImpl.toRecordGhost g) r := by
  unfold sessionRecordAt at hm
  rw [sepConj_assoc] at hm
  have hcur := Satisfies.drop_left hm
  cases hg : g.cur <;> cases hr : r.currentSession
  · unfold E2E.Record.Serialization.CanonRecord E2E.Record.Serialization.CanonCur
      E2E.InMem.SessionStoreImpl.toRecordGhost
    simp [hg, hr]
  · rw [hg, hr] at hcur
    exact (not_satisfies_false_sepConj hcur).elim
  · rw [hg, hr] at hcur
    exact (not_satisfies_false_sepConj hcur).elim
  · rename_i G s
    rw [hg, hr] at hcur
    dsimp only at hcur
    have hss : m ⊨ sessionStateReprAt A (a + 0x18#64) G s :=
      Satisfies.drop_left (sepConj_comm (sessionStateReprAt A (a + 0x18#64) G s) R ▸ hcur)
    unfold E2E.Record.Serialization.CanonRecord E2E.Record.Serialization.CanonCur
      E2E.InMem.SessionStoreImpl.toRecordGhost
    dsimp only
    rw [hg, hr]
    exact E2E.InMem.SessionStoreImpl.canonSession_of_satisfies_sessionAt A (a + 0x18#64) G s m hss

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_sub_split (sp : BitVec 64) {subStk topStk : Nat}
    (hle : subStk ≤ topStk) (hhi : topStk ≤ 2 ^ 64) :
    stackAt sp topStk =
      memRegion (sp - BitVec.ofNat 64 topStk) (topStk - subStk) ∗ stackAt sp subStk := by
  have heq : topStk = subStk + (topStk - subStk) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp subStk (topStk - subStk) (by omega), ← heq]

theorem stackAt_storePoll_frame (sp : BitVec 64) {calleeStk : Nat}
    (hhi : calleeStk + 208 ≤ 2 ^ 64) :
    stackAt sp (calleeStk + 208) =
      stackAt (sp - 208#64) calleeStk ∗ cells (sp - 208#64) 26 :=
  ProofLib.stackAt_split_cells sp calleeStk 26 hhi

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (a ↦₆₄ v3) ∗ ((a + 8#64) ↦₆₄ v2) ∗ ((a + 16#64) ↦₆₄ v1) ∗ ((a + 24#64) ↦₆₄ v0)) := by
  rw [show (32 : Nat) = 8 + 24 by rfl, memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_eight, memRegion_24_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64,
        (a ↦₆₄ v4) ∗ ((a + 8#64) ↦₆₄ v3) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v1) ∗ ((a + 32#64) ↦₆₄ v0)) := by
  rw [show (40 : Nat) = 8 + 32 by rfl, memRegion_split a 8 32 (by decide),
    ProofLib.memRegion_eight, memRegion_32_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        (a ↦₆₄ v5) ∗ ((a + 8#64) ↦₆₄ v4) ∗ ((a + 16#64) ↦₆₄ v3) ∗
        ((a + 24#64) ↦₆₄ v2) ∗ ((a + 32#64) ↦₆₄ v1) ∗ ((a + 40#64) ↦₆₄ v0)) := by
  rw [show (48 : Nat) = 8 + 40 by rfl, memRegion_split a 8 40 (by decide),
    ProofLib.memRegion_eight, memRegion_40_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem vecU8_intro (A : RustAlloc) (v bCap bPtr : BitVec 64) (bs : List (BitVec 8)) :
    ((v ↦₆₄ bCap) ∗ ((v + 8#64) ↦₆₄ bPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr bs ⊢ vecU8 A v bs := by
  have heq :
      ((v ↦₆₄ bCap) ∗ ((v + 8#64) ↦₆₄ bPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        SpqrV1.Alloc.vecU8Buf A bCap bPtr bs =
      vecU8At A v bCap bPtr bs := by
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
    rfl
  rw [heq]
  exact Entails.sepExists_right bCap (Entails.sepExists_right bPtr (Entails.refl _))

abbrev AddrCellsGhost :=
  BitVec 64 × AddrGhost × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def addrTextCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec AddrCellsGhost where
  pre := fun (addrA, g, ret, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = addrA ∧ s.sp = fsp ∧
      g.name.bytes.length < 2 ^ 32⌝ ∗
    protocolAddressAt A g addrA ∗
    (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (addrA, g, ret, _o0, _o1, _o2, fsp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecU8 A ret (addressText g.val) ∗
    protocolAddressAt A g addrA ∗ stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev SerCellsGhost :=
  BitVec 64 × BitVec 64 × E2E.Record.RecordGhost × SessionRecord (List (BitVec 8)) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def serializeCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec SerCellsGhost where
  pre := fun (recA, out, g, r, o0, o1, o2, o3, fsp) s =>
    ⌜s.readReg64 .x0 = recA ∧ s.readReg64 .x8 = out ∧ s.sp = fsp ∧
      E2E.Record.Serialization.CanonRecord g r ∧
      (E2E.Record.encodeRecord r).length < 2 ^ 32⌝ ∗
    E2E.Record.sessionRecordAt A recA g r ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗ ((out + 24#64) ↦₆₄ o3) ∗
    A.pool ∗ stackAt fsp calleeStk
  post := fun (recA, out, g, r, _o0, _o1, _o2, _o3, fsp) s0 sf =>
    ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗ E2E.Record.sessionRecordAt A recA g r ∗
      (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₆₄ bCap) ∗ ((out + 16#64) ↦₆₄ bPtr) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 (E2E.Record.encodeRecord r).length) ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr (E2E.Record.encodeRecord r) ∗
      A.pool ∗ stackAt fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev PutCellsGhost :=
  BitVec 64 × DirGhost × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64

@[expose] def dirPutCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec PutCellsGhost where
  pre := fun (self, dir, nameV, name, bytesV, bCap, bPtr, bytes, fsp) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x1 = nameV ∧ s.readReg64 .x2 = bytesV ∧
      s.sp = fsp ∧ dir.changed.length < 2 ^ 32⌝ ∗
    dirAt A self dir ∗ vecU8 A nameV name ∗
    (bytesV ↦₆₄ bCap) ∗ ((bytesV + 8#64) ↦₆₄ bPtr) ∗
    ((bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 bytes.length) ∗
    SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (self, dir, nameV, name, bytesV, _bCap, _bPtr, bytes, fsp) s0 sf =>
    ∃∗ n0 : BitVec 64, ∃∗ n1 : BitVec 64, ∃∗ n2 : BitVec 64,
    ∃∗ m0 : BitVec 64, ∃∗ m1 : BitVec 64, ∃∗ m2 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗ dirAt A self (dir.put name bytes) ∗
      (nameV ↦₆₄ n0) ∗ ((nameV + 8#64) ↦₆₄ n1) ∗ ((nameV + 16#64) ↦₆₄ n2) ∗
      (bytesV ↦₆₄ m0) ∗ ((bytesV + 8#64) ↦₆₄ m1) ∗ ((bytesV + 16#64) ↦₆₄ m2) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[expose] def cliStorePollInnerSpec (A : RustAlloc) (calleeStk : Nat) : Spec SessStorePollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
      x.call.call.addr.name.bytes.length < 2 ^ 32 ∧
      (E2E.Record.encodeRecord x.call.call.record).length < 2 ^ 32 ∧
      x.dir.changed.length < 2 ^ 32 ∧
      E2E.Record.Serialization.CanonRecord (E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g)
        x.call.call.record⌝ ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
      protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
      E2E.Record.sessionRecordAt A x.call.call.recA
        (E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g) x.call.call.record ∗
      A.pool ∗ stackAt (s.sp - 208#64) calleeStk ∗ cells (s.sp - 208#64) 26
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 1#8) ∗
      dirAt A x.self (x.dir.put (addressText x.call.call.addr.val)
        (E2E.Record.encodeRecord x.call.call.record)) ∗
      (x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.call.out + 8#64) 40 ∗
      protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
      E2E.Record.sessionRecordAt A x.call.call.recA
        (E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g) x.call.call.record ∗
      A.pool ∗ stackAt (s0.sp - 208#64) calleeStk ∗ cells (s0.sp - 208#64) 26
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
