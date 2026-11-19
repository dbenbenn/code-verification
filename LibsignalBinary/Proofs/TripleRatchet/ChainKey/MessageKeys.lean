/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.Defs
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.ChainKeyCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import ProofLib
import ProofLib.Sep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public meta import ProofLib.GenDecodes
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout

public section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.InImageLift

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Close a `CalleeSavedPreserved s0 sf` goal after straight-line execution. -/
macro "mk_cc_close" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
    State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
    State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
    State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
    State.writeVReg128_setPC, State.writeVReg128_setPState, State.writeVReg128_setMem,
    arm64_norm, *]
  done))

/-! ## 1. Pure & Cryptographic Helpers -/

private theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  simp only [leBytes, unpack32, List.range, List.range.loop, List.map]
  have h0 : BitVec.ofNat 8 (w.toNat / 256 ^ 0) = w.setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  have h1 : BitVec.ofNat 8 (w.toNat / 256 ^ 1) = (w >>> 8).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : BitVec.ofNat 8 (w.toNat / 256 ^ 2) = (w >>> 16).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h3 : BitVec.ofNat 8 (w.toNat / 256 ^ 3) = (w >>> 24).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [h0, h1, h2, h3]
  unfold BitVec.extractLsb'
  rfl

private theorem pointsToBytes_chainKeyBytes_eq (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) = (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

@[local simp] private theorem toBEBytes_length (n : ℕ) (w : BitVec (8 * n)) :
    (toBEBytes n w).length = n := by
  simp [toBEBytes]

@[local simp] private theorem shaState_flatMap_length (h : ShaState) :
    (h.toList.flatMap (toBEBytes 4)).length = 32 := by
  rcases h with ⟨l, hl⟩
  simp [List.length_flatMap, hl]

@[local simp]
private theorem length_hmacWith (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) : (hmacWith F key msg).length = 32 := by
  unfold hmacWith sha256With
  exact shaState_flatMap_length _

theorem hmacWith_one_eq_messageKeys_seed (F : ShaState → List (BitVec 8) → ShaState)
    (ck : ChainKey) :
    hmacWith F (keyToBytes32 ck.key) [0x01#8] = (ck.messageKeys F).seed := rfl

@[local simp]
private theorem length_messageKeys_seed (F : ShaState → List (BitVec 8) → ShaState)
    (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 := by
  rw [← hmacWith_one_eq_messageKeys_seed]
  exact length_hmacWith F _ _

@[local simp]
private theorem length_keyToBytes32 (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

private theorem pointsTo8_eq_pointsToBytes1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

@[local wp_norm] theorem symtab_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by
  cases s; cases r <;> rfl

@[local wp_norm] theorem symtab_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by
  cases s; rfl

@[local wp_norm] theorem symtab_setPState (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by
  cases s; rfl

/-! ## 2. Stack, `MkgRawLayout`, and Memory Region Lemmas -/

private structure MkgRawSnap where
  tag : BitVec 32
  cap : BitVec 64
  ptr : BitVec 64
  len : BitVec 64
  counter : BitVec 32

private def MkgRawLayout : ProofLib.Sep.StructLayout MkgRawSnap where
  totalSz := 40
  fields := [
    .u32 0  (·.tag),
    .u64 8  (·.cap),
    .u64 16 (·.ptr),
    .u64 24 (·.len),
    .u32 32 (·.counter)
  ]

private theorem memRegion40_entails_mkgRaw (r : BitVec 64) :
    memRegion r 40 ⊢ ∃∗ m : MkgRawSnap, MkgRawLayout.own r m := by
  have h : memRegion r 40 ⊢
      ∃∗ t0 : BitVec 32, ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
      ∃∗ l0 : BitVec 64, ∃∗ i0 : BitVec 32,
        (r ↦₃₂ t0) ∗ memRegion (r + 4#64) 4 ∗
        ((r + 8#64) ↦₆₄ c0) ∗ ((r + 16#64) ↦₆₄ p0) ∗
        ((r + 24#64) ↦₆₄ l0) ∗ ((r + 32#64) ↦₃₂ i0) ∗
        memRegion (r + 36#64) 4 := by
    sep_interval
  refine Entails.trans h ?_
  refine Entails.sepExists_elim fun t0 => Entails.sepExists_elim fun c0 =>
    Entails.sepExists_elim fun p0 => Entails.sepExists_elim fun l0 =>
    Entails.sepExists_elim fun i0 => Entails.sepExists_right ⟨t0, c0, p0, l0, i0⟩ ?_
  simp (config := { decide := true }) only [MkgRawLayout, ProofLib.Sep.StructLayout.own,
    ProofLib.Sep.fieldsRenderAt, ProofLib.Sep.renderWithGap, ProofLib.Sep.renderTailGap,
    ProofLib.Sep.StructField.u32, ProofLib.Sep.StructField.u64,
    ProofLib.Sep.StructField.field32, ProofLib.Sep.StructField.field64,
    ProofLib.Sep.fieldAddr, ↓reduceIte]
  bi_entail

private theorem memRegion40_eq_mkgRaw (r : BitVec 64) :
    memRegion r 40 = ∃∗ m : MkgRawSnap, MkgRawLayout.own r m :=
  Entails.antisymm (memRegion40_entails_mkgRaw r)
    (Entails.sepExists_elim fun m => MkgRawLayout.struct_to_memRegion r m)

private theorem mkgRaw_capPtr_lens (r : BitVec 64) :
    ProofLib.Sep.LawfulSepLens
      (MkgRawLayout.own r)
      (fun (kv : BitVec 64 × BitVec 64) => ((r + 8#64) ↦₆₄ kv.1) ∗ ((r + 16#64) ↦₆₄ kv.2))
      (fun m => (r ↦₃₂ m.tag) ∗ memRegion (r + 4#64) 4 ∗
        ((r + 24#64) ↦₆₄ m.len) ∗ ((r + 32#64) ↦₃₂ m.counter) ∗ memRegion (r + 36#64) 4)
      (fun m => (m.cap, m.ptr))
      (fun m kv => { m with cap := kv.1, ptr := kv.2 }) where
  open_entails m := by
    simp (config := { decide := true }) only [MkgRawLayout, ProofLib.Sep.StructLayout.own,
      ProofLib.Sep.fieldsRenderAt, ProofLib.Sep.renderWithGap, ProofLib.Sep.renderTailGap,
      ProofLib.Sep.StructField.u32, ProofLib.Sep.StructField.u64,
      ProofLib.Sep.StructField.field32, ProofLib.Sep.StructField.field64,
      ProofLib.Sep.fieldAddr, ↓reduceIte]
    bi_entail
  close_entails m kv := by
    simp (config := { decide := true }) only [MkgRawLayout, ProofLib.Sep.StructLayout.own,
      ProofLib.Sep.fieldsRenderAt, ProofLib.Sep.renderWithGap, ProofLib.Sep.renderTailGap,
      ProofLib.Sep.StructField.u32, ProofLib.Sep.StructField.u64,
      ProofLib.Sep.StructField.field32, ProofLib.Sep.StructField.field64,
      ProofLib.Sep.fieldAddr, ↓reduceIte]
    bi_entail
  put_get m := by cases m; rfl
  get_put _ _ := rfl
  put_put m _ _ := by cases m; rfl

private instance : ProofLib.Sep.SepLensRule ``mkgRaw_capPtr_lens := {}

private theorem stackAt_80_messageKeys (sp : BitVec 64) :
    stackAt sp 80 =
      memRegion (sp - 80#64) 32 ∗
      (∃∗ v : BitVec 64, (sp - 48#64) ↦₆₄ v) ∗
      (∃∗ v : BitVec 64, (sp - 40#64) ↦₆₄ v) ∗
      (∃∗ v : BitVec 64, (sp - 32#64) ↦₆₄ v) ∗
      memRegion (sp - 24#64) 4 ∗
      (∃∗ b : BitVec 8, (sp - 20#64) ↦₈ b) ∗
      memRegion (sp - 19#64) 3 ∗
      (∃∗ v : BitVec 64, (sp - 16#64) ↦₆₄ v) ∗
      (∃∗ v : BitVec 64, (sp - 8#64) ↦₆₄ v) := by
  dsimp only [stackAt]; sep_interval_eq

private theorem stackAt_gen_split (sp : BitVec 64) (totalStack midStack padTop : Nat)
    (htot : (80 + midStack) + padTop = totalStack) (hbound : totalStack ≤ 2 ^ 64) :
    stackAt sp totalStack =
      memRegion (sp - BitVec.ofNat 64 totalStack) padTop ∗
      stackAt (sp - 80#64) midStack ∗
      stackAt sp 80 := by
  subst htot
  rw [stackAt_split_bottom sp (80 + midStack) padTop hbound,
      stackAt_split_bottom sp 80 midStack (by omega)]
  have hsub : sp - BitVec.ofNat 64 (80 + midStack) = sp - 80#64 - BitVec.ofNat 64 midStack := by
    rw [BitVec.ofNat_add]; bv_arith
  unfold stackAt; rw [hsub]

private theorem stackAt_sub_split (sp : BitVec 64) (subStack subPad midStack : Nat)
    (h : subStack + subPad = midStack) (hb : midStack ≤ 2 ^ 64) :
    stackAt sp midStack =
      memRegion (sp - BitVec.ofNat 64 midStack) subPad ∗ stackAt sp subStack := by
  subst h; exact stackAt_split_bottom sp subStack subPad hb

private theorem stackAt_gen_repack (sp : BitVec 64)
    (totalStack midStack padTop allocStack allocPad : Nat)
    (htot : (80 + midStack) + padTop = totalStack)
    (ha : allocStack + allocPad = midStack)
    (hb : totalStack ≤ 2 ^ 64)
    (w0 w1 w2 w3 v29 v30 v21 v20 v19 : BitVec 64) (b0 : BitVec 8) :
    memRegion (sp - BitVec.ofNat 64 totalStack) padTop ∗
    memRegion (sp - 80#64 - BitVec.ofNat 64 midStack) allocPad ∗
    stackAt (sp - 80#64) allocStack ∗
    ((sp - 80#64) ↦₆₄ w0) ∗ ((sp - 72#64) ↦₆₄ w1) ∗
    ((sp - 64#64) ↦₆₄ w2) ∗ ((sp - 56#64) ↦₆₄ w3) ∗
    ((sp - 48#64) ↦₆₄ v29) ∗ ((sp - 40#64) ↦₆₄ v30) ∗
    ((sp - 32#64) ↦₆₄ v21) ∗ memRegion (sp - 24#64) 4 ∗
    ((sp - 20#64) ↦₈ b0) ∗ memRegion (sp - 19#64) 3 ∗
    ((sp - 16#64) ↦₆₄ v20) ∗ ((sp - 8#64) ↦₆₄ v19) ⊢
      stackAt sp totalStack := by
  rw [stackAt_gen_split sp totalStack midStack padTop htot hb,
      stackAt_sub_split (sp - 80#64) allocStack allocPad midStack ha (by omega),
      sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  dsimp only [stackAt]; sep_interval

private theorem remerge_and_split_midStack (sp : BitVec 64)
    (hmacStack hmacPad allocStack allocPad midStack : Nat)
    (hh : hmacStack + hmacPad = midStack) (ha : allocStack + allocPad = midStack)
    (hb : midStack ≤ 2 ^ 64)
    (P1 P2 P3 P4 P5 P6 P7 P8 : SepProp) :
    P1 ∗ P2 ∗ P3 ∗ stackAt sp hmacStack ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗
        memRegion (sp - BitVec.ofNat 64 midStack) hmacPad ∗ P8 =
      memRegion (sp - BitVec.ofNat 64 midStack) allocPad ∗ stackAt sp allocStack ∗
        P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 := by
  have h : memRegion (sp - BitVec.ofNat 64 midStack) hmacPad ∗ stackAt sp hmacStack =
      memRegion (sp - BitVec.ofNat 64 midStack) allocPad ∗ stackAt sp allocStack :=
    (stackAt_sub_split sp hmacStack hmacPad midStack hh hb).symm.trans
      (stackAt_sub_split sp allocStack allocPad midStack ha hb)
  exact Entails.antisymm
    (Entails.trans (Q := (memRegion (sp - BitVec.ofNat 64 midStack) hmacPad ∗ stackAt sp hmacStack) ∗
        (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8))
      (by bi_entail) (by rw [h]; bi_entail))
    (Entails.trans (Q := (memRegion (sp - BitVec.ofNat 64 midStack) allocPad ∗ stackAt sp allocStack) ∗
        (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8))
      (by bi_entail) (by rw [← h]; bi_entail))

private theorem memRegion32_eq_exists_cells4 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) := by
  sep_interval_eq

theorem mkgAt_of_parts (A : RustAlloc) (r ptr : BitVec 64) (k : MessageKeyGenerator)
    (hseed : k.seed.length = 32) (hptr : ptr ≠ 0) :
    (r ↦₃₂ 1#32) ∗ memRegion (r + 4#64) 4 ∗
      ((r + 8#64) ↦₆₄ 32#64) ∗ ((r + 16#64) ↦₆₄ ptr) ∗ ((r + 24#64) ↦₆₄ 32#64) ∗
      ((r + 32#64) ↦₃₂ k.counter) ∗ memRegion (r + 36#64) 4 ∗
      A.live ptr 32 1 ∗ (ptr ↦ₛ k.seed) ⊢
      mkgAt A r k := by
  unfold mkgAt
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (vecU8At_entails_vecU8 A (r + 8#64) 32#64 ptr k.seed))))
  unfold vecU8At vecHeader
  have hcap_ne : (32#64 : BitVec 64) ≠ 0 := by decide
  have h32_eq : BitVec.ofNat 64 k.seed.length = 32#64 := by rw [hseed]
  have hrem_zero : (32#64 : BitVec 64).toNat - k.seed.length = 0 := by
    change 32 - k.seed.length = 0; omega
  simp only [hcap_ne, ↓reduceIte, h32_eq, hrem_zero, memRegion_zero, sepConj_emp]
  have hpure : k.seed.length ≤ (32#64 : BitVec 64).toNat ∧ (32#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0 :=
    ⟨by change k.seed.length ≤ 32; omega, by decide, hptr⟩
  bi_entail

private theorem mkgRaw_to_mkgAt (A : RustAlloc) (r ptr : BitVec 64) (k : MessageKeyGenerator)
    (hseed : k.seed.length = 32) (hptr : ptr ≠ 0) :
    MkgRawLayout.own r ⟨1#32, 32#64, ptr, 32#64, k.counter⟩ ∗ A.live ptr 32 1 ∗ (ptr ↦ₛ k.seed) ⊢
      mkgAt A r k := by
  simp (config := { decide := true }) only [MkgRawLayout, ProofLib.Sep.StructLayout.own,
    ProofLib.Sep.fieldsRenderAt, ProofLib.Sep.renderWithGap, ProofLib.Sep.renderTailGap,
    ProofLib.Sep.StructField.u32, ProofLib.Sep.StructField.u64,
    ProofLib.Sep.StructField.field32, ProofLib.Sep.StructField.field64,
    ProofLib.Sep.fieldAddr, ↓reduceIte]
  refine Entails.trans ?_ (mkgAt_of_parts A r ptr k hseed hptr)
  bi_entail

/-! ## 3. Parameterized Specs & Callee Contract Wrappers -/

/-- Stack-parameterized `hmacSpec` (`= hmacSpec F` at `2048`, `= Stage1X.hmacSpecX F` at `18432`). -/
@[expose] def hmacSpecWithStack (F : ShaState → List (BitVec 8) → ShaState) (hmacStack : Nat) :
    Spec HmacGhost where
  pre := fun (out, ka, key, ia, inp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = ka ∧ (s.readReg64 .x2).toNat = key.length ∧
      s.readReg64 .x3 = ia ∧ (s.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
      inp.length = 1⌝ ∗
    memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s.sp hmacStack
  post := fun (out, ka, key, ia, inp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s0.sp hmacStack

theorem SepWPp_pure_elim_oom_shared_lb {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) Q Qp := by
  rw [show P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ P3) from
    Entails.antisymm (by bi_entail) (by bi_entail)]
  exact SepWPp.pure_elim h

private abbrev SepWPp.pure_elim_oom := @SepWPp_pure_elim_oom_shared_lb

theorem SepWPp_pure_elim_alloc_shared_lb {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 P4 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ P4) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ (⌜φ⌝ ∗ P3) ∗ P4) Q Qp := by
  rw [show P1 ∗ P2 ∗ (⌜φ⌝ ∗ P3) ∗ P4 = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ P4) from
    Entails.antisymm (by bi_entail) (by bi_entail)]
  exact SepWPp.pure_elim h

private abbrev SepWPp.pure_elim_alloc := @SepWPp_pure_elim_alloc_shared_lb

private theorem allocFailedIn_of_trace_eq {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ?_⟩
  · unfold allocFailedIn
    simp [h]
  · rw [h]
    exact List.prefix_append _ _

/-! ## 4. Unified Stack-Parameterized Proof & Specializations -/

abbrev lsRustNoAllocShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

abbrev lsRustAllocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

abbrev lsHandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

@[expose] def messageKeysPlacedSpecWithStack (F : ShaCompress) (A : RustAlloc)
    (totalStack : Nat) : Spec ChainKeyGhost where
  pre := fun (self, ck, ret) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = ret⌝ ∗
    (self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 40 ∗ A.pool ∗ stackAt s.sp totalStack
  post := fun (self, ck, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (self ↦ₛ chainKeyBytes ck) ∗ mkgAt A ret (ck.messageKeys F) ∗
    A.pool ∗ stackAt s0.sp totalStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev messageKeysPlacedSpec (F : ShaCompress) (A : RustAlloc) : Spec ChainKeyGhost :=
  messageKeysPlacedSpecWithStack F A messageKeysStack

abbrev messageKeysPlacedSpecX (F : ShaCompress) (A : RustAlloc) : Spec ChainKeyGhost :=
  messageKeysPlacedSpecWithStack F A messageKeysStackX

private theorem shimWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (shimSpecWithStack hookStack) := by
  have h' := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, shimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  exact h'.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)

private theorem sepWPp_seq_lscl {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h

private theorem hmacWithStack_placed_ok_at_state [LibsignalPlacement] {prog : Program}
    {F : ShaState → List (BitVec 8) → ShaState} {hmacStack : Nat} {addr : BitVec 64} {s : State}
    (hhmac : subroutine_ok prog addr (withLsCodeLoaded lsmpl (hmacSpecWithStack F hmacStack)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp hmacStack
        post := (hmacSpecWithStack F hmacStack).post } := by
  refine subroutine_ok_outcome_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hm hsp => ?_
  refine hhmac.mono_outcome (out, ka, key, ia, inp) R s0 hpc hrun ?_ hsp (fun _ hout => hout)
  dsimp only [withLsCodeLoaded, hmacSpecWithStack] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

private theorem ls_externAt?_of_mem [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalHookedExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem (mem_libsignalSessionExterns_of_hooked hmem)
  exact ls_externAt?_of_blockProg (k := k) (by rw [List.getElem?_eq_getElem hlt, hk]) hi hunmut (hhooked := hmem)

private theorem ls_hook_ok_of_mem [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalHookedExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((ls_externAt?_of_mem hmem hi hunmut).trans hf) hok

set_option maxHeartbeats 2000000 in
theorem message_keys_placed_ok_gen [LibsignalPlacement] {F : ShaCompress} {A : RustAlloc}
    {H : String → Option (State → State)}
    {totalStack midStack padTop hmacStack hmacPad allocStack allocPad : Nat}
    (htot : (80 + midStack) + padTop = totalStack := by decide)
    (htot64 : totalStack ≤ 2 ^ 64 := by decide)
    (hhmac_pad : hmacStack + hmacPad = midStack := by decide)
    (halloc_pad : allocStack + allocPad = midStack := by decide)
    (hhmac_at : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsmpl.base 73)
      (withLsCodeLoaded lsmpl (hmacSpecWithStack F hmacStack)))
    (hshim_in : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsρ lsRustNoAllocShimSym)
      (shimSpecWithStack allocStack))
    (halloc_in : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsρ lsRustAllocSym)
      (rustAllocSpecWithStack A allocStack))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (blkPl_38).base
      (withLsCodeLoaded lsmpl (messageKeysPlacedSpecWithStack F A totalStack)) := by
  have hpan_err : ((blkPC_38).rebase (blkPl_38).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked :=
    (ls_externAt?_of_mem).trans hpanic
  have hshim := hshim_in
  simp only [shimSpecWithStack] at hshim
  have halloc := halloc_in
  simp only [rustAllocSpecWithStack] at halloc
  apply subroutine_ok_of_sepWPp
  intro ⟨self, ck, ret⟩ R s0 hpc hrun hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [messageKeysPlacedSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  refine ⟨(self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 40 ∗ A.pool ∗ stackAt s0.sp totalStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  rw [pointsToBytes_chainKeyBytes_eq self ck,
      stackAt_gen_split s0.sp totalStack midStack padTop htot htot64,
      stackAt_sub_split (s0.sp - 80#64) hmacStack hmacPad midStack hhmac_pad (by omega),
      stackAt_80_messageKeys s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v19 => SepWPp.exists_elim fun v20 =>
    SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun v21 =>
    SepWPp.exists_elim fun v30 => SepWPp.exists_elim fun v29 => ?_
  apply sepWPp_seq_lscl (mid := lsmpl.base 73) hcl0
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl1
  have hhmac1 := hmacWithStack_placed_ok_at_state hhmac_at hcl1
  have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hlen_inp : ([1#8] : List (BitVec 8)).length = 1 := rfl
  apply sepWPp_seq_lscl (mid := (blkPl_38).base + 60#64) hcl1
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 20#64) 1#8]
  wp_call hhmac1 (s0.sp - 80#64, self, keyToBytes32 ck.key, s0.sp - 20#64, [1#8])
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl2
  rw [hmacWith_one_eq_messageKeys_seed F ck]
  obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
    exists_unpack64_of_length_32 (length_messageKeys_seed F ck)
  have hw_sp : ((s0.sp - 80#64) ↦ₛ (ck.messageKeys F).seed) =
      ((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗
      ((s0.sp - 64#64) ↦₆₄ w2) ∗ ((s0.sp - 56#64) ↦₆₄ w3) := by
    rw [hw32 (s0.sp - 80#64)]; sep_interval_eq
  rw [hw_sp, remerge_and_split_midStack (s0.sp - 80#64) hmacStack hmacPad allocStack allocPad
      midStack hhmac_pad halloc_pad (by omega)]
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayout32 : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  apply sepWPp_seq_lscl (mid := (blkPl_38).base + 68#64) hcl2
  wp_steps
  wp_call hshim ()
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl2'
  apply sepWPp_seq_lscl (mid := (blkPl_38).base + 80#64) hcl2'
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl3
  by_cases hoom : sf_2.readReg64 Reg.x0 = 0
  · simp only [hoom, ite_true]
    refine SepWPp.pure_elim_oom fun htr_oom => ?_
    apply sepWPp_seq_lscl (mid := lsρ lsHandleErrorSym) hcl3
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    intro _
    refine SepWPp.panic (by simp_all) (by simpa using hpan_err) fun hm' => ?_
    have hfail : allocFailedIn s0 sf_2 ∧ s0.trace <+: sf_2.trace :=
      allocFailedIn_of_trace_eq (by simp_all)
    simpa only [withLsCodeLoaded, messageKeysPlacedSpecWithStack, sepConj_assoc] using
      allowPanic_panicked (⟨by simpa [allocFailedIn, Rust.panicked] using hfail.1,
        by simpa [Rust.panicked] using hfail.2⟩) hm'
  · simp only [hoom, ite_false]
    refine SepWPp.pure_elim_alloc fun ⟨_halign, htr_alloc⟩ => ?_
    have hoom' : ¬sf_2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    rw [memRegion40_eq_mkgRaw ret, memRegion32_eq_exists_cells4 (sf_2.readReg64 Reg.x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
      SepWPp.exists_elim fun m0 => ?_
    apply sepWPp_seq_lscl (mid := s0.readReg64 Reg.lr) hcl3
    wp_lens_auto
    apply SepWP.done (by simp_all) (by simp_all)
    intro _
    refine SepWPp.done (by simp_all) (by simp_all) ⟨fun hm => ?_, rfl, by mk_cc_close⟩
    have hsp_sf1 : sf_1.sp = s0.sp - 80#64 := by simp_all
    rw [hsp_sf1] at hm
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    refine Entails.pure_right (by simp_all) ?_
    rw [pointsToBytes_chainKeyBytes_eq self ck]
    have hmkg := mkgRaw_to_mkgAt A ret (sf_2.readReg64 Reg.x0) (ck.messageKeys F)
      (length_messageKeys_seed F ck) hoom
    rw [hw32 (sf_2.readReg64 Reg.x0)] at hmkg
    have hstk := stackAt_gen_repack s0.sp totalStack midStack padTop allocStack allocPad
      htot halloc_pad htot64 w0 w1 w2 w3
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
      (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19) 1#8
    dsimp only [ChainKey.messageKeys, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29] at hmkg ⊢
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono hmkg (sepConj_mono_right hstk)))
    bi_entail

theorem message_keys_placed_ok [LibsignalPlacement] {F : ShaCompress} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hhmac : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsmpl.base 73)
      (withLsCodeLoaded lsmpl (hmacSpec F)))
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (blkPl_38).base
      (withLsCodeLoaded lsmpl (messageKeysPlacedSpec F A)) :=
  message_keys_placed_ok_gen
    (totalStack := messageKeysStack) (midStack := 4096) (padTop := 4016)
    (hmacStack := 2048) (hmacPad := 2048) (allocStack := allocHookStack) (allocPad := 0)
    (by decide) (by decide) (by decide) (by decide)
    hhmac
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (ls_hook_ok_of_mem (rustAllocSpecWithStack_eq_rustAllocSpec A ▸ halloc))
    hpanic

theorem message_keys_placed_ok_x [LibsignalPlacement] {F : ShaCompress} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hhmac : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsmpl.base 73)
      (withLsCodeLoaded lsmpl (hmacSpec F)))
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (blkPl_38).base
      (withLsCodeLoaded lsmpl (messageKeysPlacedSpecX F A)) :=
  message_keys_placed_ok_gen
    (totalStack := messageKeysStackX) (midStack := extHookStack) (padTop := 4016)
    (hmacStack := 2048) (hmacPad := 14336) (allocStack := extHookStack) (allocPad := 0)
    (by decide) (by decide) (by decide) (by decide)
    hhmac
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (ls_hook_ok_of_mem halloc) (by decide) (by decide))
    hpanic

private theorem hmacWithStack_placed_cro_ok_at_state [LibsignalPlacement] {prog : Program}
    {F : ShaState → List (BitVec 8) → ShaState} {hmacStack : Nat} {addr : BitVec 64} {s : State}
    (hhmac : subroutine_ok prog addr (withLsCodeRoLoaded lsmpl (hmacSpecWithStack F hmacStack)))
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp hmacStack
        post := (hmacSpecWithStack F hmacStack).post } := by
  refine subroutine_ok_mono hhmac (fun ⟨out, ka, key, ia, inp⟩ R s0 hm => ?_)
    (fun _ _ _ _ hpost => hpost)
  dsimp only [withLsCodeRoLoaded, hmacSpecWithStack] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

set_option maxHeartbeats 2000000 in
theorem message_keys_placed_cro_ok_gen [LibsignalPlacement] {F : ShaCompress} {A : RustAlloc}
    {H : String → Option (State → State)}
    {totalStack midStack padTop hmacStack hmacPad allocStack allocPad : Nat}
    (htot : (80 + midStack) + padTop = totalStack := by decide)
    (htot64 : totalStack ≤ 2 ^ 64 := by decide)
    (hhmac_pad : hmacStack + hmacPad = midStack := by decide)
    (halloc_pad : allocStack + allocPad = midStack := by decide)
    (hhmac_at : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (hmacSpecWithStack F hmacStack)))
    (hshim_in : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsρ lsRustNoAllocShimSym)
      (shimSpecWithStack allocStack))
    (halloc_in : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsρ lsRustAllocSym)
      (rustAllocSpecWithStack A allocStack))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (blkPl_38).base
      (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpecWithStack F A totalStack)) := by
  have hpan_err : ((blkPC_38).rebase (blkPl_38).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked :=
    (ls_externAt?_of_mem).trans hpanic
  have hshim := hshim_in
  simp only [shimSpecWithStack] at hshim
  have halloc := halloc_in
  simp only [rustAllocSpecWithStack] at halloc
  apply subroutine_ok_of_sepWPp
  intro ⟨self, ck, ret⟩ R s0 hpc hrun hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [messageKeysPlacedSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  refine ⟨(self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 40 ∗ A.pool ∗ stackAt s0.sp totalStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  rw [pointsToBytes_chainKeyBytes_eq self ck,
      stackAt_gen_split s0.sp totalStack midStack padTop htot htot64,
      stackAt_sub_split (s0.sp - 80#64) hmacStack hmacPad midStack hhmac_pad (by omega),
      stackAt_80_messageKeys s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v19 => SepWPp.exists_elim fun v20 =>
    SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun v21 =>
    SepWPp.exists_elim fun v30 => SepWPp.exists_elim fun v29 => ?_
  apply sepWPp_seq_lscro (mid := lsmpl.base 73) hcl0
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl1
  have hhmac1 := hmacWithStack_placed_cro_ok_at_state hhmac_at hcl1
  have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hlen_inp : ([1#8] : List (BitVec 8)).length = 1 := rfl
  apply sepWPp_seq_lscro (mid := (blkPl_38).base + 60#64) hcl1
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 20#64) 1#8]
  wp_call hhmac1 (s0.sp - 80#64, self, keyToBytes32 ck.key, s0.sp - 20#64, [1#8])
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl2
  rw [hmacWith_one_eq_messageKeys_seed F ck]
  obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
    exists_unpack64_of_length_32 (length_messageKeys_seed F ck)
  have hw_sp : ((s0.sp - 80#64) ↦ₛ (ck.messageKeys F).seed) =
      ((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗
      ((s0.sp - 64#64) ↦₆₄ w2) ∗ ((s0.sp - 56#64) ↦₆₄ w3) := by
    rw [hw32 (s0.sp - 80#64)]; sep_interval_eq
  rw [hw_sp, remerge_and_split_midStack (s0.sp - 80#64) hmacStack hmacPad allocStack allocPad
      midStack hhmac_pad halloc_pad (by omega)]
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayout32 : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  apply sepWPp_seq_lscro (mid := (blkPl_38).base + 68#64) hcl2
  wp_steps
  wp_call hshim ()
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl2'
  apply sepWPp_seq_lscro (mid := (blkPl_38).base + 80#64) hcl2'
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl3
  by_cases hoom : sf_2.readReg64 Reg.x0 = 0
  · simp only [hoom, ite_true]
    refine SepWPp.pure_elim_oom fun htr_oom => ?_
    apply sepWPp_seq_lscro (mid := lsρ lsHandleErrorSym) hcl3
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    intro _
    refine SepWPp.panic (by simp_all) (by simpa using hpan_err) fun hm' => ?_
    have hfail : allocFailedIn s0 sf_2 ∧ s0.trace <+: sf_2.trace :=
      allocFailedIn_of_trace_eq (by simp_all)
    simpa only [withLsCodeRoLoaded, messageKeysPlacedSpecWithStack, sepConj_assoc] using
      allowPanic_panicked (⟨by simpa [allocFailedIn, Rust.panicked] using hfail.1,
        by simpa [Rust.panicked] using hfail.2⟩) hm'
  · simp only [hoom, ite_false]
    refine SepWPp.pure_elim_alloc fun ⟨_halign, htr_alloc⟩ => ?_
    have hoom' : ¬sf_2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    rw [memRegion40_eq_mkgRaw ret, memRegion32_eq_exists_cells4 (sf_2.readReg64 Reg.x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
      SepWPp.exists_elim fun m0 => ?_
    apply sepWPp_seq_lscro (mid := s0.readReg64 Reg.lr) hcl3
    wp_lens_auto
    apply SepWP.done (by simp_all) (by simp_all)
    intro _
    refine SepWPp.done (by simp_all) (by simp_all) ⟨fun hm => ?_, rfl, by mk_cc_close⟩
    have hsp_sf1 : sf_1.sp = s0.sp - 80#64 := by simp_all
    rw [hsp_sf1] at hm
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    refine Entails.pure_right (by simp_all) ?_
    rw [pointsToBytes_chainKeyBytes_eq self ck]
    have hmkg := mkgRaw_to_mkgAt A ret (sf_2.readReg64 Reg.x0) (ck.messageKeys F)
      (length_messageKeys_seed F ck) hoom
    rw [hw32 (sf_2.readReg64 Reg.x0)] at hmkg
    have hstk := stackAt_gen_repack s0.sp totalStack midStack padTop allocStack allocPad
      htot halloc_pad htot64 w0 w1 w2 w3
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
      (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19) 1#8
    dsimp only [ChainKey.messageKeys, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29] at hmkg ⊢
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono hmkg (sepConj_mono_right hstk)))
    bi_entail

theorem message_keys_placed_cro_ok [LibsignalPlacement] {F : ShaCompress} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hhmac : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (hmacSpec F)))
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (blkPl_38).base
      (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec F A)) :=
  message_keys_placed_cro_ok_gen
    (totalStack := messageKeysStack) (midStack := 4096) (padTop := 4016)
    (hmacStack := 2048) (hmacPad := 2048) (allocStack := allocHookStack) (allocPad := 0)
    (by decide) (by decide) (by decide) (by decide)
    hhmac
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (ls_hook_ok_of_mem (rustAllocSpecWithStack_eq_rustAllocSpec A ▸ halloc))
    hpanic

end CryptoVerification.LibsignalTripleRatchet
