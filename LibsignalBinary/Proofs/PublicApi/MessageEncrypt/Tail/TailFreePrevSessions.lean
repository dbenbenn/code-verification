/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem stackAt_encSubStack_alloc (sp : BitVec 64) :
    stackAt sp encSubStack =
      stackAt sp allocHookStack ∗
        memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - allocHookStack) := by
  unfold stackAt
  rw [memRegion_split' (b := sp - BitVec.ofNat 64 encSubStack)
        (b' := sp - BitVec.ofNat 64 allocHookStack)
        (n := encSubStack - allocHookStack) (k := allocHookStack)
        (by decide)
        (by dsimp [encSubStack, withStoresEncStack, entryStack, encFrameSize, allocHookStack]; bv_omega)
        (by decide),
      sepConj_comm]

theorem mul24_shift_toNat {c : BitVec 64} (hc : c.toNat * 24 < 2 ^ 63) :
    ((c + (c <<< 1)) <<< 3).toNat = c.toNat * 24 := by
  bv_omega

theorem sepWP_call_dealloc {prog : Program} {entry target_pc : BitVec 64} (ret_pc : BitVec 64)
    {A : RustAlloc} (hdealloc : subroutine_ok prog entry (rustDeallocSpec A))
    {p sp : BitVec 64} {size align : Nat} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hsp : s.sp = sp)
    (hP : P = (A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt sp allocHookStack) ∗ F)
    (hx0 : s.readReg64 .x0 = p) (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp → CalleeSavedPreserved s sf → sf.trace = s.trace →
      SepWP prog target_pc sf ((A.pool ∗ stackAt sp allocHookStack) ∗ F) post) :
    SepWP prog target_pc s P post := by
  subst hsp
  exact SepWP.call_framed_mut hdealloc (p, size, align) rfl (fun _ => rfl) hP ⟨hx0, hx1, hx2⟩
    hpc hrun hsp_al hlr hnext

theorem vecHeader_prev_weaken (sp prevCap prevPtr : BitVec 64) :
    ((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
      ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ⊢
    memRegion (sp + 0x110#64) 0x35a := by
  have hhdr :
      (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
        ((sp + 0x120#64) ↦₆₄ 0#64)) =
      words64At (sp + 0x110#64) [prevCap, prevPtr, 0#64] := by
    simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  have hhdr_mem :
      words64At (sp + 0x110#64) [prevCap, prevPtr, 0#64] ⊢
        memRegion (sp + 0x110#64) 0x18 :=
    words64At_entails_memRegion (sp + 0x110#64) [prevCap, prevPtr, 0#64] (by simp)
  have hjoin :
      memRegion (sp + 0x110#64) 0x35a =
        memRegion (sp + 0x110#64) 0x18 ∗
          (memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea) := by
    rw [memRegion_split' (b := sp + 0x110#64) (b' := sp + 0x128#64) (n := 0x18) (k := 0x342)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x128#64) (b' := sp + 0x280#64) (n := 0x158) (k := 0x1ea)
          (by decide) (by bv_omega) (by decide)]
  have hlhs :
      ((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
        ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea =
      words64At (sp + 0x110#64) [prevCap, prevPtr, 0#64] ∗
        (memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea) := by
    rw [← hhdr]; ac_rfl
  rw [hlhs, hjoin]
  exact sepConj_mono_left hhdr_mem

theorem vecAt_prev_zero_eq (A : RustAlloc) (sp prevPtr : BitVec 64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) 0#64 prevPtr [] =
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
      (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) := by
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem vecAt_prev_nz_eq (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (hcap : prevCap ≠ 0#64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] =
      ⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
      (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64) ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) := by
  unfold vecAt vecHeader vecBuf arrayAt
  simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero,
    BitVec.ofNat_eq_ofNat, hcap, ite_false, BitVec.add_zero, emp_sepConj,
    BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions

