/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Varint
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Preamble & Epilogue for `spqr::recv`

Default allocation-event envelope (`SpqrRecvEnv`), protocol-only panic postcondition
(`spqrRecvBudgetPanicPost`), shared epilogue (`+1040..+1072`), and preamble varint steppers
(`+96..+312`) for `spqr::recv` (Block `329`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalSpqrV1
  (AuthApi Bytes Chain ChainEpoch ChainEpochDirection ChainEpochPB ChainPB ChainParamsPB
   ChainResult Direction Epoch EpochDirectionPB Error HkdfFn KeyHistory Message MlKem MsgPreamble
   PolyApi SpqrRecvModel States StatesResult V1Recv VersionNegotiationPB chainFrom
   chainFromVersionNegotiation decodeVarint decodeVarintLoop decode_chunk decode_varint msgPreamble)
open CryptoVerification.LibsignalTripleRatchet (VecArg spqrRecvStack)
open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
  (csel_rest1_min_10 hb_eq_of_not_sxtb_tb hb_ne_of_sxtb_tb index_bounds_ne msg_expose_byte
   msg_unexpose_byte nat_le_of_bv_ule nat_lt_of_not_bv_ule rest1_cons_of_not_ule rest1_nil_of_ule
   varint_cont_of_lt varint_end_of_ge varint_out_norm)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Top.DecodeState (TraceVRegs decodeStateSavedAt)
open CryptoVerification.SpqrV1.Top.Recv
  (MsgRemValid SepWPpLS decodeVarintLoop_err_of_hi decodeVarintLoop_ok_of_lo
   decodeVarintLoop_step_of_hi rem_len_add_not ret_48_split
   sp_sub_4992_aligned sp_sub_96_aligned spqrRecvCalleeStackX spqrRecvPlacedEntry
   spqrRecvPlacedProg spqrRecvRoPlacedAt spqrRecvSavedRegs spqrRecvSavedRegs_eq_decodeStateSavedAt
   stack_restore_spqrRecv zeroExtend_setWidth32_of_lt)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag
  (SpqrErrorValidTag recvResultExactKeyDispAt recvResultExactKeyDispAt_error_of_byte
   spqrErrorTagCanonical spqrErrorTagCanonical_valid_of_ne_invalidParams spqrErrorValidTag_zero)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

private theorem align_pre_wp {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

/-! ## 0. Displayable Error-Result Fold Helpers & Pure `Error ≠ .invalidParams` Lemmas -/

/-- Fold `recvResultExactKeyDispAt A r (.error sd)` from `r ↦₆₄ -1`, byte `code` at `r + 8`,
    and trailing cells `[r + 9 .. r + 48)` when `SpqrErrorValidTag code` holds. -/
theorem recv_err_byte_disp_foldX (A : RustAlloc) (r r2 r3 : BitVec 64)
    (code : BitVec 8) (sd : Bool) (hsd : code = 0#8 ↔ sd = true) (hd : SpqrErrorValidTag code) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((r + 8#64) ↦₈ code) ∗ memRegion (r + 9#64) 7 ∗
      ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗ memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyDispAt A r (.error sd) := by
  have htail :
      memRegion (r + 9#64) 7 ∗ ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗
        memRegion (r + 32#64) 16 ⊢
      memRegion (r + 9#64) 39 := by
    rw [show (39 : Nat) = 7 + (8 + (8 + 16)) by decide,
        memRegion_split (r + 9#64) 7 32 (by decide),
        show r + 9#64 + 7#64 = r + 16#64 by bv_arith,
        memRegion_split (r + 16#64) 8 24 (by decide),
        show r + 16#64 + 8#64 = r + 24#64 by bv_arith,
        memRegion_split (r + 24#64) 8 16 (by decide),
        show r + 24#64 + 8#64 = r + 32#64 by bv_arith]
    exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right htail)) ?_
  exact recvResultExactKeyDispAt_error_of_byte A r code sd hsd hd

/-- Fold `recvResultExactKeyDispAt A r (.error false)` for `Err(MsgDecode)` (`w8 = 2#64`). -/
theorem recv_err_msgDecode_disp_foldX (A : RustAlloc) (r r2 r3 : BitVec 64) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((r + 8#64) ↦₆₄ 2#64) ∗
      ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗ memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyDispAt A r (.error false) := by
  have h8 : ((r + 8#64) ↦₆₄ 2#64) ⊢ ((r + 8#64) ↦₈ 2#8) ∗ memRegion (r + 9#64) 7 := by
    rw [pointsTo64_eq_pointsToBytes]
    change ((r + 8#64) ↦ₛ (2#8 :: [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8])) ⊢ _
    rw [pointsToBytes_cons, show r + 8#64 + 1#64 = r + 9#64 by bv_arith]
    exact sepConj_mono_right (pointsToBytes_entails_memRegion _ _)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h8)) ?_
  rw [sepConj_assoc]
  exact recv_err_byte_disp_foldX A r r2 r3 2#8 false (by decide) (by decide)

/-- Fold `recvResultExactKeyDispAt A r (.error sd)` from 4 words `(-1, w1, w2, w3)` when `w1`
    carries `tag` in its low byte and `SpqrErrorValidTag tag` holds. -/
theorem recv_err_words_disp_foldX (A : RustAlloc) (r w1 w2 w3 : BitVec 64)
    (tag : BitVec 8) (sd : Bool) (hsd : tag = 0#8 ↔ sd = true) (hd : SpqrErrorValidTag tag)
    (hw1 : ∀ r' : BitVec 64,
      ((r' + 8#64) ↦₆₄ w1) ⊢ ((r' + 8#64) ↦₈ tag) ∗ memRegion (r' + 9#64) 7) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((r + 8#64) ↦₆₄ w1) ∗
      ((r + 16#64) ↦₆₄ w2) ∗ ((r + 24#64) ↦₆₄ w3) ∗ memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyDispAt A r (.error sd) := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (hw1 r))) ?_
  rw [sepConj_assoc]
  exact recv_err_byte_disp_foldX A r w2 w3 tag sd hsd hd

private theorem pointsTo64_entails_pointsTo8_memRegion7_local (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ⊢ ((a ↦₈ BitVec.truncate 8 w) ∗ memRegion (a + 1#64) 7) := by
  have hsplit (k r : Nat) (off off' : BitVec 64)
      (hkr : k = 1 + r) (hoff : (a + off) + 1#64 = a + off') (hr : k ≤ 2 ^ 64) :
      memRegion (a + off) k = memRegion (a + off) 1 ∗ memRegion (a + off') r :=
    ProofLib.memRegion_split' (b := a + off) (n := 1) (k := r) (b' := a + off') hkr hoff.symm hr
  rw [hsplit 7 6 1#64 2#64 rfl (by bv_omega) (by decide),
      hsplit 6 5 2#64 3#64 rfl (by bv_omega) (by decide),
      hsplit 5 4 3#64 4#64 rfl (by bv_omega) (by decide),
      hsplit 4 3 4#64 5#64 rfl (by bv_omega) (by decide),
      hsplit 3 2 5#64 6#64 rfl (by bv_omega) (by decide),
      hsplit 2 1 6#64 7#64 rfl (by bv_omega) (by decide),
      pointsTo64_eq_pointsToBytes]
  dsimp only [unpack64]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  have hb0 : w.extractLsb' 0 8 = BitVec.truncate 8 w := by bv_kernel
  rw [hb0]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (pointsTo8_entails_memRegion _ _)))))))

/-- Fold `recvResultExactKeyDispAt A r (.error sd)` from `q0.extractLsb' 0 64` at `r + 8`
    when `BitVec.truncate 8 q0 = tag` and `SpqrErrorValidTag tag` holds. -/
theorem recv_err_q0_disp_foldX (A : RustAlloc) (r r2 r3 : BitVec 64) (q0 : BitVec 128)
    (tag : BitVec 8) (sd : Bool)
    (hq0 : BitVec.truncate 8 q0 = tag)
    (hsd : tag = 0#8 ↔ sd = true)
    (hd : SpqrErrorValidTag tag) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      ((r + 8#64) ↦₆₄ q0.extractLsb' 0 64) ∗
      ((r + 16#64) ↦₆₄ r2) ∗
      ((r + 24#64) ↦₆₄ r3) ∗
      memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyDispAt A r (.error sd) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left
      (pointsTo64_entails_pointsTo8_memRegion7_local (r + 8#64) (q0.extractLsb' 0 64)))) ?_
  have haddr : (r + 8#64) + 1#64 = r + 9#64 := by bv_omega
  have htrunc : BitVec.truncate 8 (q0.extractLsb' 0 64) = BitVec.truncate 8 q0 := by bv_kernel
  rw [haddr, htrunc, hq0, sepConj_assoc]
  exact recv_err_byte_disp_foldX A r r2 r3 tag sd hsd hd

private theorem except_bind_eq_error {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {e : ε}
    (h : (m >>= f) = .error e) :
    m = .error e ∨ ∃ a, m = .ok a ∧ f a = .error e := by
  cases m with
  | error e' => exact Or.inl (by simpa [Bind.bind, Except.bind] using h)
  | ok a => exact Or.inr ⟨a, rfl, by simpa [Bind.bind, Except.bind] using h⟩

private theorem chainEpochDirectionFromPb_ne_invalidParams {pb : EpochDirectionPB} {e : Error}
    (h : ChainEpochDirection.fromPb pb = .error e) (s : String) :
    e ≠ .invalidParams s := by
  unfold ChainEpochDirection.fromPb at h
  split at h
  · injection h with he; subst he; exact nofun
  · contradiction

private theorem chainLinksFromPb_ne_invalidParams {ls : List ChainEpochPB} {e : Error}
    (h : Chain.linksFromPb ls = .error e) (s : String) :
    e ≠ .invalidParams s := by
  induction ls with
  | nil => simp [Chain.linksFromPb] at h
  | cons link rest ih =>
    unfold Chain.linksFromPb at h
    cases hsend : link.send with
    | none =>
      rw [hsend] at h
      simp [Bind.bind, Except.bind] at h
      subst h; exact nofun
    | some sendPb =>
      rw [hsend] at h
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      rcases except_bind_eq_error h with h2 | ⟨_, _, h3⟩
      · exact chainEpochDirectionFromPb_ne_invalidParams h2 s
      · cases hrecv : link.recv with
        | none =>
          rw [hrecv] at h3
          simp [Bind.bind, Except.bind] at h3
          subst h3; exact nofun
        | some recvPb =>
          rw [hrecv] at h3
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h3
          rcases except_bind_eq_error h3 with h4 | ⟨_, _, h5⟩
          · exact chainEpochDirectionFromPb_ne_invalidParams h4 s
          · rcases except_bind_eq_error h5 with h5 | ⟨_, _, h6⟩
            · exact ih h5
            · nomatch h6

theorem chainFromPb_ne_invalidParams {pb : ChainPB} {e : Error}
    (h : Chain.fromPb pb = .error e) (s : String) :
    e ≠ .invalidParams s := by
  unfold Chain.fromPb at h
  cases hdir : Direction.fromI32? pb.direction with
  | none =>
    rw [hdir] at h
    simp [Bind.bind, Except.bind] at h
    subst h; exact nofun
  | some dir =>
    rw [hdir] at h
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    rcases except_bind_eq_error h with h2 | ⟨_, _, h3⟩
    · exact chainLinksFromPb_ne_invalidParams h2 s
    · cases hpar : pb.params with
      | none =>
        rw [hpar] at h3
        simp [Bind.bind, Except.bind] at h3
        subst h3; exact nofun
      | some params =>
        rw [hpar] at h3
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h3

theorem chainFromVersionNegotiation_ne_invalidParams {hkdf : HkdfFn} {vn : VersionNegotiationPB}
    {e : Error} (h : chainFromVersionNegotiation hkdf vn = .error e) (s : String) :
    e ≠ .invalidParams s := by
  unfold chainFromVersionNegotiation at h
  cases hdir : Direction.fromI32? vn.direction with
  | none =>
    rw [hdir] at h
    simp [Bind.bind, Except.bind] at h
    subst h; exact nofun
  | some dir =>
    rw [hdir] at h
    cases hpar : vn.chainParams with
    | none =>
      rw [hpar] at h
      simp [Bind.bind, Except.bind] at h
      subst h; exact nofun
    | some params =>
      rw [hpar] at h
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Chain.new] at h

theorem chainFrom_ne_invalidParams {hkdf : HkdfFn} {pb : Option ChainPB}
    {vn : Option VersionNegotiationPB} {e : Error}
    (h : chainFrom hkdf pb vn = .error e) (s : String) :
    e ≠ .invalidParams s := by
  unfold chainFrom at h
  cases pb with
  | some pb => exact chainFromPb_ne_invalidParams h s
  | none =>
    cases vn with
    | none => injection h with he; subst he; exact nofun
    | some vn => exact chainFromVersionNegotiation_ne_invalidParams h s

private theorem chainResult_ofPanic_ne_err {α : Type} (r : Except CryptoVerification.LibsignalSpqrV1.ChainPanic α)
    (e : Error) : ChainResult.ofPanic r ≠ .error (.err e) := by
  cases r <;> simp [ChainResult.ofPanic]

private theorem keyHistoryGetLoop_ne_invalidParams (self : KeyHistory) (atIdx : BitVec 32)
    (want : Bytes) (params : ChainParamsPB) (e : Error) (s : String) :
    ∀ (k i : Nat), self.data.length - i ≤ k →
      KeyHistory.getLoop self atIdx want params i = .error (.err e) →
      e ≠ .invalidParams s := by
  intro k
  induction k with
  | zero =>
    intro i hk h
    unfold KeyHistory.getLoop at h
    split at h
    · omega
    · simp at h; subst h; exact nofun
  | succ k ih =>
    intro i hk h
    unfold KeyHistory.getLoop at h
    split at h
    · split at h
      · simp at h
      · exact ih (i + KeyHistory.KEY_SIZE) (by simp only [KeyHistory.KEY_SIZE]; omega) h
    · simp at h; subst h; exact nofun

private theorem keyAdvanceLoop_ne_err (hkdf : HkdfFn) (atIdx : BitVec 32) (params : ChainParamsPB)
    (e : Error) :
    ∀ (k : Nat) (self : ChainEpochDirection), atIdx.toNat - self.ctr.toNat ≤ k →
      ChainEpochDirection.keyAdvanceLoop hkdf self atIdx params ≠ .error (.err e) := by
  intro k
  induction k with
  | zero =>
    intro self hk h
    unfold ChainEpochDirection.keyAdvanceLoop at h
    split at h
    · omega
    · split at h <;> simp at h
  | succ k ih =>
    intro self hk h
    unfold ChainEpochDirection.keyAdvanceLoop at h
    split at h
    · split at h
      · simp at h
      · rename_i _ next' ctr' kv hnk
        have hctr := ChainEpochDirection.nextKeyInternal_ctr hkdf self.next next' self.ctr ctr' kv hnk
        dsimp only at h
        split at h
        · simp at h
        · exact ih _ (by dsimp only; omega) h
    · split at h <;> simp at h

private theorem chainEpochDirectionKey_ne_invalidParams {hkdf : HkdfFn} {self : ChainEpochDirection}
    {atIdx : BitVec 32} {params : ChainParamsPB} {e : Error}
    (h : self.key hkdf atIdx params = .error (.err e)) (s : String) :
    e ≠ .invalidParams s := by
  unfold ChainEpochDirection.key at h
  split at h
  · rcases except_bind_eq_error h with h1 | ⟨_, _, h2⟩
    · unfold KeyHistory.get at h1
      dsimp only at h1
      split at h1
      · simp at h1
      · split at h1
        · simp at h1
        · split at h1
          · simp at h1; subst h1; exact nofun
          · exact keyHistoryGetLoop_ne_invalidParams self.prev atIdx _ params e s
              self.prev.data.length 0 (Nat.sub_zero _ ▸ Nat.le_refl _) h1
    · nomatch h2
  · split at h
    · simp at h; subst h; exact nofun
    · split at h
      · simp at h; subst h; exact nofun
      · dsimp only at h
        split at h
        · simp at h
        · rcases except_bind_eq_error h with h1 | ⟨self1, _, h2⟩
          · exact False.elim (keyAdvanceLoop_ne_err hkdf atIdx params e _ _ (Nat.le_refl _) h1)
          · rcases except_bind_eq_error h2 with h2 | ⟨_, _, h3⟩
            · exact False.elim (chainResult_ofPanic_ne_err _ e h2)
            · rcases except_bind_eq_error h3 with h3 | ⟨_, _, h4⟩
              · exact False.elim (chainResult_ofPanic_ne_err _ e h3)
              · nomatch h4

theorem chainRecvKey_ne_invalidParams {hkdf : HkdfFn} {self : Chain} {epoch : Epoch}
    {index : BitVec 32} {e : Error}
    (h : self.recvKey hkdf epoch index = .error (.err e)) (s : String) :
    e ≠ .invalidParams s := by
  unfold Chain.recvKey at h
  split at h
  · simp at h
  · rcases except_bind_eq_error h with h1 | ⟨epochIndex, _, h2⟩
    · unfold Chain.epochIdx at h1
      split at h1
      · simp [ChainResult.ofError] at h1; subst h1; exact nofun
      · dsimp only at h1
        split at h1
        · simp [ChainResult.ofError] at h1; subst h1; exact nofun
        · simp [ChainResult.ofError] at h1
    · split at h2
      · simp at h2
      · rcases except_bind_eq_error h2 with h2 | ⟨_, _, h3⟩
        · exact chainEpochDirectionKey_ne_invalidParams h2 s
        · nomatch h3

private theorem decodeChunk_ne_invalidParams {P : PolyApi} {bs : Bytes} {e : Error}
    (h : decode_chunk P bs = .error e) (s : String) :
    e ≠ .invalidParams s := by
  unfold decode_chunk at h
  rcases except_bind_eq_error h with h1 | ⟨⟨index, rest⟩, _, h2⟩
  · unfold decode_varint at h1
    split at h1 <;> simp at h1; subst h1; exact nofun
  · dsimp only at h2
    by_cases hcond : (decide (rest.length < 32) || decide (index.toNat > 65535)) = true
    · simp [hcond] at h2; subst h2; exact nofun
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h2
      cases hvec : CryptoVerification.LibsignalSpqrV1.bytesToVector? 32 (rest.take 32) with
      | none => rw [hvec] at h2; injection h2 with he; subst he; exact nofun
      | some v => rw [hvec] at h2; nomatch h2

theorem msgDeserialize_ne_invalidParams {P : PolyApi} {epoch : Epoch} {bs : Bytes} {e : Error}
    (h : Message.deserialize P epoch bs = .error e) (s : String) :
    e ≠ .invalidParams s := by
  unfold Message.deserialize at h
  cases bs with
  | nil => simp at h; subst h; exact nofun
  | cons b0 rest =>
    dsimp only at h
    cases hmt : CryptoVerification.LibsignalSpqrV1.MessageType.tryFromU8 b0 with
    | none =>
      rw [hmt] at h
      simp [Bind.bind, Except.bind] at h
      subst h; exact nofun
    | some msgType =>
      rw [hmt] at h
      cases msgType <;> dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      · cases h
      · rcases except_bind_eq_error h with h1 | ⟨⟨_, _⟩, _, h2⟩
        · exact decodeChunk_ne_invalidParams h1 s
        · cases h2
      · rcases except_bind_eq_error h with h1 | ⟨⟨_, _⟩, _, h2⟩
        · exact decodeChunk_ne_invalidParams h1 s
        · cases h2
      · rcases except_bind_eq_error h with h1 | ⟨⟨_, _⟩, _, h2⟩
        · exact decodeChunk_ne_invalidParams h1 s
        · cases h2
      · cases h
      · rcases except_bind_eq_error h with h1 | ⟨⟨_, _⟩, _, h2⟩
        · exact decodeChunk_ne_invalidParams h1 s
        · cases h2
      · rcases except_bind_eq_error h with h1 | ⟨⟨_, _⟩, _, h2⟩
        · exact decodeChunk_ne_invalidParams h1 s
        · cases h2

private theorem statesResult_ofPanic_ne_err {α ε : Type}
    [CryptoVerification.LibsignalSpqrV1.ToStatesPanic ε] (r : Except ε α) (e : Error) :
    StatesResult.ofPanic r ≠ .error (.err e) := by
  cases r <;> simp [StatesResult.ofPanic]

private theorem recvCt2_ne_invalidParams {K : MlKem} {Au : AuthApi}
    {self : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received Au} {ct2 mac : Bytes} {e : Error}
    (h : self.recv_ct2 K ct2 mac = .error (.err e)) (s : String) :
    e ≠ .invalidParams s := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.recv_ct2 at h
  rcases except_bind_eq_error h with h | ⟨_, _, h⟩
  · exact False.elim (statesResult_ofPanic_ne_err _ e h)
  · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
    · exact False.elim (statesResult_ofPanic_ne_err _ e h)
    · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
      · exact False.elim (statesResult_ofPanic_ne_err _ e h)
      · rcases except_bind_eq_error h with h | ⟨verifyRes, _, h⟩
        · exact False.elim (statesResult_ofPanic_ne_err _ e h)
        · cases verifyRes with
          | error _ => simp at h; subst h; exact nofun
          | ok u => cases u; dsimp only at h; split at h <;> simp at h

private theorem recvCt2Chunk_ne_invalidParams {K : MlKem} {P : PolyApi} {Au : AuthApi}
    {self : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received P Au} {epoch : Epoch} {chunk : P.Chunk} {e : Error}
    (h : self.recv_ct2_chunk K epoch chunk = .error (.err e)) (s : String) :
    e ≠ .invalidParams s := by
  unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk at h
  split at h
  · simp at h
  · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
    · exact False.elim (statesResult_ofPanic_ne_err _ e h)
    · rcases except_bind_eq_error h with h | ⟨decoded?, _, h⟩
      · exact False.elim (statesResult_ofPanic_ne_err _ e h)
      · cases decoded? with
        | none => simp at h
        | some ct2Full =>
          dsimp only at h
          split at h
          · simp at h
          · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
            · exact recvCt2_ne_invalidParams h s
            · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
              · exact False.elim (statesResult_ofPanic_ne_err _ e h)
              · simp at h

private theorem recvHeader_ne_invalidParams {Au : AuthApi}
    {self : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.NoHeaderReceived Au} {epoch : Epoch} {hdr mac : Bytes} {e : Error}
    (h : self.recv_header epoch hdr mac = .error (.err e)) (s : String) :
    e ≠ .invalidParams s := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.NoHeaderReceived.recv_header at h
  split at h
  · simp at h
  · rcases except_bind_eq_error h with h | ⟨verifyRes, _, h⟩
    · exact False.elim (statesResult_ofPanic_ne_err _ e h)
    · cases verifyRes with
      | error _ => simp at h; subst h; exact nofun
      | ok u => cases u; simp at h

private theorem recvHdrChunk_ne_invalidParams {P : PolyApi} {Au : AuthApi}
    {self : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived P Au} {epoch : Epoch} {chunk : P.Chunk} {e : Error}
    (h : self.recv_hdr_chunk epoch chunk = .error (.err e)) (s : String) :
    e ≠ .invalidParams s := by
  unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk at h
  split at h
  · simp at h
  · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
    · exact False.elim (statesResult_ofPanic_ne_err _ e h)
    · rcases except_bind_eq_error h with h | ⟨decoded?, _, h⟩
      · exact False.elim (statesResult_ofPanic_ne_err _ e h)
      · cases decoded? with
        | none => simp at h
        | some hdrFull =>
          dsimp only at h
          split at h
          · simp at h
          · rcases except_bind_eq_error h with h | ⟨receivingEkRes, _, h⟩
            · exact False.elim (statesResult_ofPanic_ne_err _ e h)
            · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
              · exact recvHeader_ne_invalidParams h s
              · cases receivingEkRes <;> simp at h

private theorem recvEk_ne_invalidParams {K : MlKem} {Au : AuthApi}
    {self : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent Au} {epoch : Epoch} {ek : Bytes} {e : Error}
    (h : self.recv_ek K epoch ek = .error (.err e)) (s : String) :
    e ≠ .invalidParams s := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.recv_ek at h
  split at h
  · simp at h
  · split at h <;> simp at h; subst h; exact nofun

private theorem ct1SampledRecvEkChunk_ne_invalidParams {K : MlKem} {P : PolyApi} {Au : AuthApi}
    {self : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled P Au} {epoch : Epoch} {chunk : P.Chunk} {ct1Ack : Bool}
    {e : Error} (h : self.recv_ek_chunk K epoch chunk ct1Ack = .error (.err e)) (s : String) :
    e ≠ .invalidParams s := by
  unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.recv_ek_chunk at h
  rcases except_bind_eq_error h with h | ⟨_, _, h⟩
  · exact False.elim (statesResult_ofPanic_ne_err _ e h)
  · rcases except_bind_eq_error h with h | ⟨decoded?, _, h⟩
    · exact False.elim (statesResult_ofPanic_ne_err _ e h)
    · cases decoded? with
      | none => cases ct1Ack <;> simp at h
      | some decoded =>
        dsimp only at h
        rcases except_bind_eq_error h with h | ⟨_, _, h⟩
        · exact recvEk_ne_invalidParams h s
        · cases ct1Ack with
          | false => simp at h
          | true =>
            rcases except_bind_eq_error h with h | ⟨_, _, h⟩
            · exact False.elim (statesResult_ofPanic_ne_err _ e h)
            · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
              · exact False.elim (statesResult_ofPanic_ne_err _ e h)
              · simp at h

private theorem ct1AckRecvEkChunk_ne_invalidParams {K : MlKem} {P : PolyApi} {Au : AuthApi}
    {self : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged P Au} {epoch : Epoch} {chunk : P.Chunk} {e : Error}
    (h : self.recv_ek_chunk K epoch chunk = .error (.err e)) (s : String) :
    e ≠ .invalidParams s := by
  unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at h
  rcases except_bind_eq_error h with h | ⟨_, _, h⟩
  · exact False.elim (statesResult_ofPanic_ne_err _ e h)
  · rcases except_bind_eq_error h with h | ⟨decoded?, _, h⟩
    · exact False.elim (statesResult_ofPanic_ne_err _ e h)
    · cases decoded? with
      | none => simp at h
      | some decoded =>
        dsimp only at h
        rcases except_bind_eq_error h with h | ⟨_, _, h⟩
        · exact recvEk_ne_invalidParams h s
        · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
          · exact False.elim (statesResult_ofPanic_ne_err _ e h)
          · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
            · exact False.elim (statesResult_ofPanic_ne_err _ e h)
            · simp at h

theorem statesRecv_ne_invalidParams {K : MlKem} {P : PolyApi} {Au : AuthApi}
    {self : States P Au} {msg : Message P} {e : Error}
    (h : self.recv K msg = .error (.err e)) (s : String) :
    e ≠ .invalidParams s := by
  unfold States.recv at h
  cases self with
  | keysUnsampled state =>
    dsimp only at h; split at h <;> simp at h; subst h; exact nofun
  | keysSampled state =>
    dsimp only at h
    split at h
    · simp at h; subst h; exact nofun
    · split at h
      · simp at h
      · cases hp : msg.payload <;> (rw [hp] at h; try dsimp only at h; try cases h)
        rcases except_bind_eq_error h with h | ⟨_, _, h⟩
        · exact False.elim (statesResult_ofPanic_ne_err _ e h)
        · cases h
  | headerSent state =>
    dsimp only at h
    split at h
    · simp at h; subst h; exact nofun
    · split at h
      · simp at h
      · cases hp : msg.payload <;> (rw [hp] at h; try dsimp only at h; try cases h)
        rcases except_bind_eq_error h with h | ⟨res, _, h⟩
        · exact False.elim (statesResult_ofPanic_ne_err _ e h)
        · cases res <;> cases h
  | ct1Received state =>
    dsimp only at h
    split at h
    · simp at h; subst h; exact nofun
    · split at h
      · simp at h
      · cases hp : msg.payload <;> (rw [hp] at h; try dsimp only at h; try cases h)
        rcases except_bind_eq_error h with h | ⟨_, _, h⟩
        · exact False.elim (statesResult_ofPanic_ne_err _ e h)
        · cases h
  | ekSentCt1Received state =>
    dsimp only at h
    split at h
    · simp at h; subst h; exact nofun
    · split at h
      · simp at h
      · cases hp : msg.payload <;> (rw [hp] at h; try dsimp only at h; try cases h)
        rcases except_bind_eq_error h with h | ⟨res, _, h⟩
        · exact recvCt2Chunk_ne_invalidParams h s
        · cases res with
          | stillReceiving _ => cases h
          | done p => rcases p with ⟨_, _⟩; cases h
  | noHeaderReceived state =>
    dsimp only at h
    split at h
    · simp at h; subst h; exact nofun
    · split at h
      · simp at h
      · cases hp : msg.payload <;> (rw [hp] at h; try dsimp only at h; try cases h)
        rcases except_bind_eq_error h with h | ⟨res, _, h⟩
        · exact recvHdrChunk_ne_invalidParams h s
        · cases res <;> cases h
  | headerReceived state =>
    dsimp only at h; split at h <;> simp at h; subst h; exact nofun
  | ct1Sampled state =>
    dsimp only at h
    split at h
    · simp at h; subst h; exact nofun
    · split at h
      · simp at h
      · cases hp : msg.payload <;> (rw [hp] at h; try dsimp only at h; try cases h)
        all_goals
          rcases except_bind_eq_error h with h | ⟨res, _, h⟩
          · exact ct1SampledRecvEkChunk_ne_invalidParams h s
          · cases res <;> cases h
  | ekReceivedCt1Sampled state =>
    dsimp only at h
    split at h
    · simp at h; subst h; exact nofun
    · split at h
      · simp at h
      · split at h
        · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
          · exact False.elim (statesResult_ofPanic_ne_err _ e h)
          · cases h
        · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
          · exact False.elim (statesResult_ofPanic_ne_err _ e h)
          · cases h
        · simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases h
  | ct1Acknowledged state =>
    dsimp only at h
    split at h
    · simp at h; subst h; exact nofun
    · split at h
      · simp at h
      · cases hp : msg.payload <;> (rw [hp] at h; try dsimp only at h; try cases h)
        all_goals
          rcases except_bind_eq_error h with h | ⟨res, _, h⟩
          · exact ct1AckRecvEkChunk_ne_invalidParams h s
          · cases res <;> cases h
  | ct2Sampled state =>
    dsimp only at h
    split at h
    · split at h
      · rcases except_bind_eq_error h with h | ⟨_, _, h⟩
        · exact False.elim (statesResult_ofPanic_ne_err _ e h)
        · cases h
      · simp at h; subst h; exact nofun
    · cases h

/-! ## 1. Budget-Threaded Postconditions, Panic Postcondition, and `SepWPpLS` Lifting Helpers -/

/-- Default bounded allocation-event envelope of `spqr::recv` (`Block 329`), linear in the input
    state and message byte lengths. All core definitions and step lemmas below are also exposed
    in envelope-parametric `*OfEnv` form. -/
@[expose] def SpqrRecvEnv (st msg : VecArg) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 512 (4 * st.bytes.length + 4 * msg.bytes.length + 16384) evs

/-- Budget-form panic postcondition of `spqr::recv`: drops `allocFailedIn s0 sf` while
    preserving the genuine non-allocation panic predicate `M.recvPanics st.bytes msg.bytes`. -/
abbrev spqrRecvBudgetPanicPost (M : SpqrRecvModel)
    (st msg : VecArg) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (⌜M.recvPanics st.bytes msg.bytes ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

/-- Envelope-parametric relocatable core postcondition of `spqr::recv` without `¬ M.recvPanics`. -/
abbrev spqrRecvPlacedCorePost0OfEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (Env : List AllocEvent → Prop)
    (M : SpqrRecvModel) (st msg : VecArg) (ret : BitVec 64) (s0 sf : State) : SepProp :=
  ∃∗ evs,
    ⌜sf.trace = s0.trace ∧ Env evs⌝ ∗
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyDispAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs st_cost) sf ∗
      stackAt s0.sp spqrRecvStack

abbrev spqrRecvPlacedPost0OfEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (Env : List AllocEvent → Prop)
    (M : SpqrRecvModel) (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ spqrRecvPlacedCorePost0OfEnv A lim st_cost Env M st msg ret s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Envelope-parametric relocatable core postcondition of `spqr::recv` with `¬ M.recvPanics`. -/
abbrev spqrRecvPlacedCorePostOfEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (Env : List AllocEvent → Prop)
    (M : SpqrRecvModel) (st msg : VecArg) (ret : BitVec 64) (s0 sf : State) : SepProp :=
  ∃∗ evs,
    ⌜sf.trace = s0.trace ∧ Env evs ∧ ¬ M.recvPanics st.bytes msg.bytes⌝ ∗
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyDispAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs st_cost) sf ∗
      stackAt s0.sp spqrRecvStack

abbrev spqrRecvPlacedPostOfEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (Env : List AllocEvent → Prop)
    (M : SpqrRecvModel) (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ spqrRecvPlacedCorePostOfEnv A lim st_cost Env M st msg ret s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev spqrRecvPlacedCorePost0 {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 sf : State) : SepProp :=
  spqrRecvPlacedCorePost0OfEnv A lim st_cost (SpqrRecvEnv st msg) M st msg ret s0 sf

abbrev spqrRecvPlacedPost0 {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  spqrRecvPlacedPost0OfEnv A lim st_cost (SpqrRecvEnv st msg) M st msg ret s0 R

abbrev spqrRecvPlacedCorePost {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 sf : State) : SepProp :=
  spqrRecvPlacedCorePostOfEnv A lim st_cost (SpqrRecvEnv st msg) M st msg ret s0 sf

abbrev spqrRecvPlacedPost {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  spqrRecvPlacedPostOfEnv A lim st_cost (SpqrRecvEnv st msg) M st msg ret s0 R

theorem spqrRecvPlacedPostOfEnv_of_post0 {MC : AllocCostModel} {A : RustCliAllocBudget MC}
    {lim : BudgetLimits} {st_cost : MC.σ} {Env : List AllocEvent → Prop} {M : SpqrRecvModel}
    {st msg : VecArg} {ret : BitVec 64} {s0 : State} {R : SepProp} {sf : State} {P_f : SepProp}
    (hnp : ¬ M.recvPanics st.bytes msg.bytes)
    (h : spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R sf P_f) :
    spqrRecvPlacedPostOfEnv A lim st_cost Env M st msg ret s0 R sf P_f := by
  refine ⟨fun hm => ?_, h.2⟩
  have hm0 := h.1 hm
  dsimp only [spqrRecvPlacedCorePost0OfEnv, spqrRecvPlacedCorePostOfEnv] at hm0 ⊢
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm0 ⊢
  obtain ⟨evs, hevs⟩ := hm0
  refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hevs ⊢
  exact ⟨⟨hevs.1.1, hevs.1.2, hnp⟩, hevs.2⟩

theorem spqrRecvPlacedPost_of_post0 {MC : AllocCostModel} {A : RustCliAllocBudget MC}
    {lim : BudgetLimits} {st_cost : MC.σ} {M : SpqrRecvModel}
    {st msg : VecArg} {ret : BitVec 64} {s0 : State} {R : SepProp} {sf : State} {P_f : SepProp}
    (hnp : ¬ M.recvPanics st.bytes msg.bytes)
    (h : spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R sf P_f) :
    spqrRecvPlacedPost A lim st_cost M st msg ret s0 R sf P_f :=
  spqrRecvPlacedPostOfEnv_of_post0 hnp h

theorem sepWP_spqrRecvPlacedPostOfEnv_of_post0 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {MC : AllocCostModel} {A : RustCliAllocBudget MC}
    {lim : BudgetLimits} {st_cost : MC.σ} {Env : List AllocEvent → Prop} {M : SpqrRecvModel}
    {st msg : VecArg} {ret : BitVec 64} {s0 : State} {R : SepProp}
    (hnp : ¬ M.recvPanics st.bytes msg.bytes)
    (h : SepWP prog target_pc s P
      (spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)) :
    SepWP prog target_pc s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env M st msg ret s0 R) :=
  SepWP.mono h (fun _ _ _ _ hq => spqrRecvPlacedPostOfEnv_of_post0 hnp hq)

theorem sepWP_spqrRecvPlacedPost_of_post0 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {MC : AllocCostModel} {A : RustCliAllocBudget MC}
    {lim : BudgetLimits} {st_cost : MC.σ} {M : SpqrRecvModel}
    {st msg : VecArg} {ret : BitVec 64} {s0 : State} {R : SepProp}
    (hnp : ¬ M.recvPanics st.bytes msg.bytes)
    (h : SepWP prog target_pc s P (spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)) :
    SepWP prog target_pc s P (spqrRecvPlacedPost A lim st_cost M st msg ret s0 R) :=
  sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp h

/-! ## 2. Common Epilogue (`+1040 .. +1072`) and `Err(MsgDecode)` Exit (`+276 .. +288`) -/

private theorem sepWP_spqrRecv_finish {MC : AllocCostModel}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {Env : List AllocEvent → Prop} {evs : List AllocEvent} (hevs : Env evs)
    {M : SpqrRecvModel} {ext : String → Option (State → State)}
    {st msg : VecArg} {ret : BitVec 64} {s0 s : State} {P R : SepProp}
    {post : State → SepProp → Prop}
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hwp : SepWP ((blkPC_329).rebase (blkPl_329).base (Rust.withPanics ext))
      (s0.readReg64 .x30) s P
      (fun sf P_f =>
        VmPreserved s sf ∧
        (P_f ⊢
          spqrRecvRoPlacedAt ∗
          st.at A.repAlloc ∗
          msg.at A.repAlloc ∗
          recvResultExactKeyDispAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
          A.pool lim (MC.stepEvents evs st_cost) s ∗
          stackAt s0.sp spqrRecvStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  subst hpost
  refine SepWP.mono hwp ?_
  intro sf P_f _ _ ⟨hvm, hent, hspf, hcsf, htrf⟩
  refine ⟨fun hmR => ?_, hspf, hcsf⟩
  have hm1 := Satisfies.mono (sepConj_mono_left hent) hmR
  rw [← A.pool_of_vmPreserved (lim := lim) (st := MC.stepEvents evs st_cost) hvm] at hm1
  dsimp only [spqrRecvPlacedCorePost0OfEnv]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, hevs⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1⟩

/-- Relocatable shared epilogue (`+1040 .. +1072`, 9 instructions) for Block `329`
    (`spqr::recv`), parameterized over any event envelope `Env`. -/
theorem step_epilogue_placed_ofEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (Env : List AllocEvent → Prop)
    (evs : List AllocEvent) (hevs : Env evs)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hpc : s.pc = spqrRecvPlacedEntry + 1040#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyDispAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  refine sepWP_spqrRecv_finish hevs hpost ?_
  rcases htr with ⟨htr, hvregs⟩
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_4992_aligned s0 hs0A
  have hsp96A : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    sp_sub_96_aligned s0 hs0A
  subst hP
  dsimp only [spqrRecvPlacedEntry] at hpc
  generalize hsp0 : s0.sp = sp0 at hsp hsp96A ⊢
  have hrestore := stack_restore_spqrRecv sp0 s0
  rw [spqrRecvSavedRegs_eq_decodeStateSavedAt sp0 s0] at hrestore ⊢
  by_vm_steps (
    unfold decodeStateSavedAt
    wp_steps 9
    refine SepWP.fold hrestore (by
      unfold decodeStateSavedAt
      sep_focus) ?_
    refine align_pre_wp (by sep_ac_rfl) ?_
    wp_done
  )

theorem step_epilogue_placed {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (st msg : VecArg)
    (evs : List AllocEvent) (hevs : SpqrRecvEnv st msg evs)
    (ret : BitVec 64) (s0 s : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hpc : s.pc = spqrRecvPlacedEntry + 1040#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyDispAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_epilogue_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs hevs M ext st msg ret
    s0 s P R post hpost hpc hrun hsp hs0A htr hP

/-- Relocatable `Err(MsgDecode)` exit (`+276 .. +288 -> +1040 .. +1072`) for Block `329`,
    parameterized over any event envelope `Env` satisfied by `evs`. -/
theorem step_err_msgDecode_placed_ofEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (Env : List AllocEvent → Prop)
    (evs : List AllocEvent) (hevs : Env evs)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (hpc : s.pc = spqrRecvPlacedEntry + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  refine sepWP_spqrRecv_finish hevs hpost ?_
  rcases htr with ⟨htr, hvregs⟩
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_4992_aligned s0 hs0A
  have hsp96A : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    sp_sub_96_aligned s0 hs0A
  subst hP
  dsimp only [spqrRecvPlacedEntry] at hpc
  generalize hsp0 : s0.sp = sp0 at hsp hsp96A ⊢
  have hrestore := stack_restore_spqrRecv sp0 s0
  rw [spqrRecvSavedRegs_eq_decodeStateSavedAt sp0 s0] at hrestore ⊢
  by_vm_steps (
    rw [ret_48_split ret]
    wp_pull_exists
    rename_i r3 r2 r1 r0
    wp_steps 4
    have hfold := recv_err_msgDecode_disp_foldX A.repAlloc ret r2 r3
    rw [← herr] at hfold
    refine SepWP.fold hfold (by sep_focus) ?_
    unfold decodeStateSavedAt
    wp_steps 9
    refine SepWP.fold hrestore (by
      unfold decodeStateSavedAt
      sep_focus) ?_
    refine align_pre_wp (by sep_ac_rfl) ?_
    wp_done
  )

theorem step_err_msgDecode_placed {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (hpc : s.pc = spqrRecvPlacedEntry + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cost s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_err_msgDecode_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) []
    (SpqrBoundedEvs.nil _ _) M ext st msg ret s0 s P R post hpost herr hpc hrun hsp hs0A htr hx19 hP

/-- Lift `step_err_msgDecode_placed_ofEnv` into `SepWPpLS` with `spqrRecvBudgetPanicPost`. -/
theorem step_err_msgDecode_wppLS_ofEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (Env : List AllocEvent → Prop)
    (evs : List AllocEvent) (hevs : Env evs)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (hpc : s.pc = spqrRecvPlacedEntry + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
      (spqrRecvBudgetPanicPost M st msg s0 R) :=
  SepWPpLS.of_sepWPp (SepWPp.of_sepWP_ret
    (step_err_msgDecode_placed_ofEnv A lim st_cost Env evs hevs M ext st msg ret
      s0 s P R _ rfl herr hpc hrun hsp hs0A htr hx19 hP))

theorem step_err_msgDecode_wppLS {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (hpc : s.pc = spqrRecvPlacedEntry + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cost s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
      (spqrRecvBudgetPanicPost M st msg s0 R) :=
  step_err_msgDecode_wppLS_ofEnv A lim st_cost (SpqrRecvEnv st msg) []
    (SpqrBoundedEvs.nil _ _) M ext st msg ret s0 s P R herr hpc hrun hsp hs0A htr hx19 hP

/-! ## 3. Preamble Varint Decoding (`+96 .. +276`, `+312`) -/

/-- Relocatable budget-threaded frame invariant throughout `+96 .. +312` (after the prologue). -/
abbrev spqrRecvPlacedPreambleFrame {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (st msg : VecArg)
    (ret : BitVec 64) (s0 s : State) : SepProp :=
  spqrRecvRoPlacedAt ∗
  st.at A.repAlloc ∗
  msg.at A.repAlloc ∗
  memRegion ret 48 ∗
  A.pool lim st_cost s ∗
  stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
  memRegion (s0.sp - 4992#64) 0x1320 ∗
  spqrRecvSavedRegs (s0.sp - 4992#64) s0

/-- Relocatable continuation hypothesis at `+276` (`Err(MsgDecode)`). -/
abbrev PreamblePlacedErrTail {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64) (s0 : State)
    (post : State → SepProp → Prop) : Prop :=
  ∀ (s1 : State) (P1 : SepProp),
    msgPreamble msg.bytes = .error .msgDecode →
    s1.pc = spqrRecvPlacedEntry + 276#64 →
    s1.status = .Running →
    s1.sp = s0.sp - 4992#64 →
    TraceVRegs s1 s0 →
    s1.readReg64 .x19 = ret →
    P1 = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s1 →
    SepWP (spqrRecvPlacedProg ext) target_pc s1 P1 post

/-- Relocatable continuation hypothesis at `+312` (`Ok(pre)`). -/
abbrev PreamblePlacedOkTail {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64) (s0 : State)
    (post : State → SepProp → Prop) : Prop :=
  ∀ (pre : MsgPreamble) (msgPtr : BitVec 64) (s1 : State) (P1 : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg msgPtr pre.remaining →
    s1.pc = spqrRecvPlacedEntry + 312#64 →
    s1.status = .Running →
    s1.sp = s0.sp - 4992#64 →
    TraceVRegs s1 s0 →
    s1.readReg64 .x0 = st.v →
    s1.readReg64 .x19 = ret →
    s1.readReg64 .x21 = pre.index.zeroExtend 64 →
    s1.readReg64 .x22 = pre.epoch →
    s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s1.readReg64 .x24 = msgPtr →
    s1.readReg64 .x25 = pre.version.zeroExtend 64 →
    s1.readReg64 .x29 = s0.sp - 96#64 →
    P1 = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s1 →
    SepWP (spqrRecvPlacedProg ext) target_pc s1 P1 post

set_option maxHeartbeats 800000 in
/-- Relocatable steps from `+252` after decoding `(index, rest')`. -/
theorem step_after_index_placed {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (epoch index : BitVec 64)
    (pre₁ pre₂ rest' : List (BitVec 8)) (byteJ : BitVec 8) (j : Nat)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (herr_tail : PreamblePlacedErrTail A lim st_cost ext st msg ret target_pc s0 post)
    (hok_tail : PreamblePlacedOkTail A lim st_cost ext st msg ret target_pc s0 post)
    (hlen_lt : msg.bytes.length < 2 ^ 63)
    (hsplit : msg.bytes = (version :: pre₁ ++ pre₂) ++ byteJ :: rest')
    (hpre2 : pre₂.length = j)
    (hpre : msgPreamble msg.bytes =
      if index.toNat < 2 ^ 32 then
        .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest' }
      else
        .error .msgDecode)
    (hpc : s.pc = spqrRecvPlacedEntry + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx8 : s.readReg64 .x8 = msg.ptr + 1#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (pre₁.length + j + 1))
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = index)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx25 : s.readReg64 .x25 = version.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s) :
    SepWP (spqrRecvPlacedProg ext) target_pc s P post := by
  have hlen_eq : msg.bytes.length = 1 + pre₁.length + j + 1 + rest'.length := by
    rw [hsplit]; simp [hpre2]; omega
  have hrem := rem_len_add_not hlen_eq hlen_lt
  clear hlen_eq
  have hvalid : MsgRemValid msg
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j + 1))) rest' := by
    right
    refine ⟨(version :: pre₁ ++ pre₂) ++ [byteJ], ?_, ?_⟩
    · rw [hsplit]; simp [List.append_assoc]
    · have hlen_p : ((version :: pre₁ ++ pre₂) ++ [byteJ]).length = 1 + (pre₁.length + j + 1) := by
        simp [List.length_cons, List.length_append, List.length_singleton, hpre2]; omega
      rw [hlen_p]
      simp only [BitVec.ofNat_add]
  clear hsplit
  dsimp only [PreamblePlacedErrTail, PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry,
    BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail ⊢
  wp_steps
  wp_if hhi
  · have hnlt : ¬ index.toNat < 2 ^ 32 := by bv_omega
    have herr : msgPreamble msg.bytes = .error .msgDecode := by
      simp only [hpre, hnlt, ↓reduceIte]
    exact herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm])
      (by rw [hP]; simp only [spqrRecvPlacedPreambleFrame, arm64_norm])
  · have hlt : index.toNat < 2 ^ 32 := by bv_omega
    have hok : msgPreamble msg.bytes =
        .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest' } := by
      simp only [hpre, hlt, ↓reduceIte]
    wp_steps 4
    exact hok_tail
      { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest' }
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j + 1)))
      _ P hok hvalid
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx21, arm64_norm, zeroExtend_setWidth32_of_lt hlt])
      (by simp [hx22, arm64_norm])
      (by simp [hx9, hx10, hrem, arm64_norm])
      (by simp [hx8, hx10, arm64_norm]; bv_arith)
      (by simp [hx25, arm64_norm])
      (by simp [hx29, arm64_norm])
      (by rw [hP]; simp only [spqrRecvPlacedPreambleFrame, arm64_norm])

set_option maxHeartbeats 1600000 in
/-- Relocatable index varint loop (`+192 .. +248`) from iteration `j` (`k = 10 - j` fuel). -/
theorem step_index_loop_placed {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (epoch : BitVec 64)
    (pre₁ rest1 : List (BitVec 8))
    (s0 : State) (post : State → SepProp → Prop)
    (herr_tail : PreamblePlacedErrTail A lim st_cost ext st msg ret target_pc s0 post)
    (hok_tail : PreamblePlacedOkTail A lim st_cost ext st msg ret target_pc s0 post)
    (hpre1 : 1 ≤ pre₁.length)
    (hlen_lt : msg.bytes.length < 2 ^ 63) :
    ∀ (k j : Nat) (out : BitVec 64) (pre₂ rest' : List (BitVec 8)) (byteJ : BitVec 8)
      (s : State) (P : SepProp),
      10 - j ≤ k →
      j < 10 →
      msg.bytes = (version :: pre₁ ++ pre₂) ++ byteJ :: rest' →
      rest1 = pre₂ ++ byteJ :: rest' →
      pre₂.length = j →
      (msgPreamble msg.bytes =
        match decodeVarintLoop j out (byteJ :: rest') with
        | none => .error .msgDecode
        | some (index, rest2) =>
          if index.toNat < 2 ^ 32 then
            .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
          else
            .error .msgDecode) →
      s.pc = spqrRecvPlacedEntry + 192#64 →
      s.status = .Running →
      s.sp = s0.sp - 4992#64 →
      TraceVRegs s s0 →
      s.readReg64 .x0 = st.v →
      s.readReg64 .x19 = ret →
      s.readReg64 .x22 = epoch →
      s.readReg64 .x25 = version.zeroExtend 64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      s.readReg64 .x8 = msg.ptr + 1#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length →
      s.readReg64 .x10 = BitVec.ofNat 64 (pre₁.length + j) →
      s.readReg64 .x11 = BitVec.ofNat 64 (7 * j) →
      s.readReg64 .x12 = BitVec.ofNat 64 (pre₁.length - 1 + j) →
      s.readReg64 .x13 = BitVec.ofNat 64 (min rest1.length 10) →
      s.readReg64 .x14 = BitVec.ofNat 64 (msg.bytes.length - 2) →
      s.readReg64 .x15 = BitVec.ofNat 64 (j + 1) →
      s.readReg64 .x21 = out →
      P = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s →
      SepWP (spqrRecvPlacedProg ext) target_pc s P post := by
  intro k
  induction k with
  | zero =>
    intro j _ _ _ _ _ _ hjk hj
    omega
  | succ k ih =>
    intro j out pre₂ rest' byteJ s P hjk hj hsplit hrest1 hpre2 hpre
      hpc hrun hsp htr hx0 hx19 hx22 hx25 hx29 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx21 hP
    have hafter := step_after_index_placed A lim st_cost ext st msg ret target_pc version epoch
      (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
      pre₁ pre₂ rest' byteJ j s0
    have hmsg_ge : pre₁.length + j + 2 ≤ msg.bytes.length := by
      rw [hsplit]; simp [hpre2]
    have hne_bounds := index_bounds_ne hpre1 hmsg_ge hlen_lt
    have hoff : msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j)) =
        msg.ptr + BitVec.ofNat 64 (version :: pre₁ ++ pre₂).length := by
      simp only [List.length_cons, List.length_append, hpre2]; bv_omega
    have hexp := msg_expose_byte A.repAlloc msg (version :: pre₁ ++ pre₂) rest' byteJ
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j))) hsplit hoff
    have hunexp := msg_unexpose_byte A.repAlloc msg (version :: pre₁ ++ pre₂) rest' byteJ
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j))) hsplit hoff
    clear hoff
    have hsplit_symm := hsplit.symm; clear hsplit
    have hrest1_symm := hrest1.symm; clear hrest1
    subst hP
    dsimp only [PreamblePlacedErrTail, PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry,
      spqrRecvPlacedPreambleFrame, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail hafter ih ⊢
    wp_steps
    wp_if hbounds
    · exact False.elim (hne_bounds hbounds)
    clear hbounds
    refine SepWP.fold hexp (by sep_focus) ?_
    wp_steps
    refine SepWP.fold hunexp (by sep_focus) ?_
    wp_if hhs
    · have hge : min rest1.length 10 ≤ j + 1 :=
        nat_le_of_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      have hend := varint_end_of_ge hj hrest1_symm.symm hpre2 hge
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have herr : msgPreamble msg.bytes = .error .msgDecode := by
          rw [hpre, decodeVarintLoop_err_of_hi hb hend]
        exact herr_tail _ _ herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm])
          (by simp [hx19, arm64_norm]) (by simp only [arm64_norm]; sep_ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).toNat < 2 ^ 32 then
              .ok { version := version, epoch := epoch,
                    index := (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).setWidth 32,
                    remaining := rest' }
            else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        exact hafter _ _ post herr_tail hok_tail hlen_lt hsplit_symm.symm hpre2 hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx8, arm64_norm])
          (by simp [hx9, arm64_norm]) (by simp [hx10, arm64_norm]; try bv_omega)
          (by simp [hx19, arm64_norm])
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp only [arm64_norm]; sep_ac_rfl)
    · have hlt : j + 1 < min rest1.length 10 :=
        nat_lt_of_not_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      obtain ⟨hj1, b', rest'', rfl⟩ := varint_cont_of_lt hrest1_symm.symm hpre2 hlt
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have hpre_step : msgPreamble msg.bytes =
            match decodeVarintLoop (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) (b' :: rest'') with
            | none => .error .msgDecode
            | some (index, rest2) =>
              if index.toNat < 2 ^ 32 then
                .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
              else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_step_of_hi hb hj1]
        have hsplit' : msg.bytes = (version :: pre₁ ++ (pre₂ ++ [byteJ])) ++ b' :: rest'' := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hrest1' : rest1 = (pre₂ ++ [byteJ]) ++ b' :: rest'' := by
          rw [← hrest1_symm]; simp [List.append_assoc]
        have hpre2' : (pre₂ ++ [byteJ]).length = j + 1 := by
          rw [List.length_append, List.length_singleton, hpre2]
        exact ih (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
          (pre₂ ++ [byteJ]) rest'' b' _ _ (by omega) hj1 hsplit' hrest1' hpre2' hpre_step
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; try bv_omega)
          (by simp [hx13, arm64_norm]) (by simp [hx14, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by simp only [arm64_norm]; sep_ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).toNat < 2 ^ 32 then
              .ok { version := version, epoch := epoch,
                    index := (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).setWidth 32,
                    remaining := b' :: rest'' }
            else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        wp_steps 1
        exact hafter _ _ post herr_tail hok_tail hlen_lt hsplit_symm.symm hpre2 hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx8, arm64_norm])
          (by simp [hx9, arm64_norm]) (by simp [hx10, arm64_norm]; try bv_omega)
          (by simp [hx19, arm64_norm])
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp only [arm64_norm]; sep_ac_rfl)

set_option maxHeartbeats 800000 in
/-- Relocatable steps from `+144` after decoding `(epoch, rest1)`. -/
theorem step_after_epoch_placed {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (pre₁ rest1 : List (BitVec 8)) (epoch : BitVec 64)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (herr_tail : PreamblePlacedErrTail A lim st_cost ext st msg ret target_pc s0 post)
    (hok_tail : PreamblePlacedOkTail A lim st_cost ext st msg ret target_pc s0 post)
    (hpre1 : 1 ≤ pre₁.length)
    (hlen_lt : msg.bytes.length < 2 ^ 63)
    (hmsg_eq : msg.bytes = version :: (pre₁ ++ rest1))
    (hpre : msgPreamble msg.bytes =
      if epoch == 0#64 then .error .msgDecode
      else
        match decodeVarint rest1 with
        | .error e => .error e
        | .ok (index, rest2) =>
          if index.toNat < 2 ^ 32 then
            .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
          else .error .msgDecode)
    (hpc : s.pc = spqrRecvPlacedEntry + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx25 : s.readReg64 .x25 = version.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx8 : s.readReg64 .x8 = msg.ptr + 1#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 (1 + pre₁.length))
    (hx22 : s.readReg64 .x22 = epoch)
    (hP : P = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s) :
    SepWP (spqrRecvPlacedProg ext) target_pc s P post := by
  have hidx_loop := step_index_loop_placed A lim st_cost ext st msg ret target_pc
    version epoch pre₁ rest1 s0 post herr_tail hok_tail hpre1 hlen_lt 10 0 0#64 []
  have hmsg_symm := hmsg_eq.symm; clear hmsg_eq
  dsimp only [PreamblePlacedErrTail, PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry,
    BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail hidx_loop ⊢
  wp_steps
  wp_if hepoch
  · have herr : msgPreamble msg.bytes = .error .msgDecode := by
      simp [hpre, hepoch]
    exact herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm])
      (by rw [hP]; simp only [spqrRecvPlacedPreambleFrame, arm64_norm])
  · have hepoch_f : (epoch == 0#64) = false := beq_false_of_ne hepoch
    wp_steps
    wp_if hls
    · have hrest1_nil := rest1_nil_of_ule hmsg_symm.symm hlen_lt hls
      have herr : msgPreamble msg.bytes = .error .msgDecode := by
        rw [hpre, hepoch_f, hrest1_nil]; rfl
      exact herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm])
        (by rw [hP]; simp only [spqrRecvPlacedPreambleFrame, arm64_norm])
    · wp_steps 9
      obtain ⟨b₀, rest1', hrest1_cons⟩ := rest1_cons_of_not_ule hmsg_symm.symm hlen_lt hls
      have hlen_eq : msg.bytes.length = 1 + pre₁.length + rest1.length := by
        rw [← hmsg_symm, List.length_cons, List.length_append]
        omega
      have hpre1_lt : 1 + pre₁.length < 2 ^ 63 := by omega
      have hlen_ge : 2 ≤ msg.bytes.length := by
        rw [← hmsg_symm, hrest1_cons]; simp; omega
      have hsplit0 : msg.bytes = (version :: pre₁ ++ []) ++ b₀ :: rest1' := by
        rw [← hmsg_symm, hrest1_cons]; simp
      have hrest1_0 : rest1 = [] ++ b₀ :: rest1' := hrest1_cons
      have hpre0 : msgPreamble msg.bytes =
          match decodeVarintLoop 0 0#64 (b₀ :: rest1') with
          | none => .error .msgDecode
          | some (index, rest2) =>
            if index.toNat < 2 ^ 32 then
              .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
            else .error .msgDecode := by
        rw [hpre, hepoch_f, hrest1_cons]
        dsimp only [decodeVarint, decode_varint, Bool.false_eq_true, ↓reduceIte]
        cases decodeVarintLoop 0 0#64 (b₀ :: rest1') <;> rfl
      exact hidx_loop rest1' b₀ _ P (by omega) (by omega) hsplit0 hrest1_0 rfl hpre0
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
        (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
        (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
        (by simp [arm64_norm]; try bv_omega)
        (by simp [arm64_norm])
        (by simp [arm64_norm]; try bv_omega)
        (by simp [arm64_norm]; exact csel_rest1_min_10 hlen_eq hlen_lt)
        (by simp [arm64_norm]; try bv_omega)
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by rw [hP]; simp only [spqrRecvPlacedPreambleFrame, arm64_norm])

set_option maxHeartbeats 1600000 in
/-- Relocatable epoch varint loop (`+96 .. +140`) from iteration `j` (`k = 10 - j` fuel). -/
theorem step_epoch_loop_placed {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (rest0 : List (BitVec 8))
    (s0 : State) (post : State → SepProp → Prop)
    (herr_tail : PreamblePlacedErrTail A lim st_cost ext st msg ret target_pc s0 post)
    (hok_tail : PreamblePlacedOkTail A lim st_cost ext st msg ret target_pc s0 post)
    (hlen_lt : msg.bytes.length < 2 ^ 63) :
    ∀ (k j : Nat) (out : BitVec 64) (pre₁ rest0' : List (BitVec 8)) (byteJ : BitVec 8)
      (s : State) (P : SepProp),
      10 - j ≤ k →
      j < 10 →
      msg.bytes = (version :: pre₁) ++ byteJ :: rest0' →
      rest0 = pre₁ ++ byteJ :: rest0' →
      pre₁.length = j →
      (msgPreamble msg.bytes =
        match decodeVarintLoop j out (byteJ :: rest0') with
        | none => .error .msgDecode
        | some (epoch, rest1) =>
          if epoch == 0#64 then .error .msgDecode
          else
            match decodeVarint rest1 with
            | .error e => .error e
            | .ok (index, rest2) =>
              if index.toNat < 2 ^ 32 then
                .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
              else .error .msgDecode) →
      s.pc = spqrRecvPlacedEntry + 96#64 →
      s.status = .Running →
      s.sp = s0.sp - 4992#64 →
      TraceVRegs s s0 →
      s.readReg64 .x0 = st.v →
      s.readReg64 .x19 = ret →
      s.readReg64 .x25 = version.zeroExtend 64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      s.readReg64 .x8 = msg.ptr + 1#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length →
      s.readReg64 .x10 = BitVec.ofNat 64 (7 * j) →
      s.readReg64 .x11 = msg.ptr →
      s.readReg64 .x12 = BitVec.ofNat 64 (min rest0.length 10) →
      s.readReg64 .x14 = BitVec.ofNat 64 (j + 1) →
      s.readReg64 .x22 = out →
      P = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s →
      SepWP (spqrRecvPlacedProg ext) target_pc s P post := by
  intro k
  induction k with
  | zero =>
    intro j _ _ _ _ _ _ hjk hj
    omega
  | succ k ih =>
    intro j out pre₁ rest0' byteJ s P hjk hj hsplit hrest0 hpre1 hpre
      hpc hrun hsp htr hx0 hx19 hx25 hx29 hx8 hx9 hx10 hx11 hx12 hx14 hx22 hP
    have hafter := step_after_epoch_placed A lim st_cost ext st msg ret target_pc version
      (pre₁ ++ [byteJ]) rest0' (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) s0
    have hoff : msg.ptr + BitVec.ofNat 64 (j + 1) =
        msg.ptr + BitVec.ofNat 64 (version :: pre₁).length := by
      simp only [List.length_cons, hpre1]
    have hexp := msg_expose_byte A.repAlloc msg (version :: pre₁) rest0' byteJ
      (msg.ptr + BitVec.ofNat 64 (j + 1)) hsplit hoff
    have hunexp := msg_unexpose_byte A.repAlloc msg (version :: pre₁) rest0' byteJ
      (msg.ptr + BitVec.ofNat 64 (j + 1)) hsplit hoff
    clear hoff
    have hsplit_symm := hsplit.symm; clear hsplit
    have hrest0_symm := hrest0.symm; clear hrest0
    subst hP
    dsimp only [PreamblePlacedErrTail, PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry,
      spqrRecvPlacedPreambleFrame, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail hafter ih ⊢
    refine SepWP.fold hexp (by sep_focus) ?_
    wp_steps
    refine SepWP.fold hunexp (by sep_focus) ?_
    wp_if hhs
    · have hge : min rest0.length 10 ≤ j + 1 :=
        nat_le_of_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      have hend := varint_end_of_ge hj hrest0_symm.symm hpre1 hge
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have herr : msgPreamble msg.bytes = .error .msgDecode := by
          rw [hpre, decodeVarintLoop_err_of_hi hb hend]
        exact herr_tail _ _ herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm])
          (by simp [hx19, arm64_norm]) (by simp only [arm64_norm]; sep_ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) == 0#64 then .error .msgDecode
            else
              match decodeVarint rest0' with
              | .error e => .error e
              | .ok (index, rest2) =>
                if index.toNat < 2 ^ 32 then
                  .ok { version := version,
                        epoch := out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)),
                        index := index.setWidth 32, remaining := rest2 }
                else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        have hmsg_eq' : msg.bytes = version :: ((pre₁ ++ [byteJ]) ++ rest0') := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hpre1' : 1 ≤ (pre₁ ++ [byteJ]).length := by
          rw [List.length_append, List.length_singleton]; omega
        exact hafter _ _ post herr_tail hok_tail hpre1' hlen_lt hmsg_eq' hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [hpre1, arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by simp only [arm64_norm]; sep_ac_rfl)
    · have hlt : j + 1 < min rest0.length 10 :=
        nat_lt_of_not_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      obtain ⟨hj1, b', rest0'', rfl⟩ := varint_cont_of_lt hrest0_symm.symm hpre1 hlt
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have hpre_step : msgPreamble msg.bytes =
            match decodeVarintLoop (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) (b' :: rest0'') with
            | none => .error .msgDecode
            | some (epoch, rest1) =>
              if epoch == 0#64 then .error .msgDecode
              else
                match decodeVarint rest1 with
                | .error e => .error e
                | .ok (index, rest2) =>
                  if index.toNat < 2 ^ 32 then
                    .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
                  else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_step_of_hi hb hj1]
        have hsplit' : msg.bytes = (version :: (pre₁ ++ [byteJ])) ++ b' :: rest0'' := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hrest0' : rest0 = (pre₁ ++ [byteJ]) ++ b' :: rest0'' := by
          rw [← hrest0_symm]; simp [List.append_assoc]
        have hpre1' : (pre₁ ++ [byteJ]).length = j + 1 := by
          rw [List.length_append, List.length_singleton, hpre1]
        exact ih (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
          (pre₁ ++ [byteJ]) rest0'' b' _ _ (by omega) hj1 hsplit' hrest0' hpre1' hpre_step
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [hx11, arm64_norm]) (by simp [hx12, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by simp only [arm64_norm]; sep_ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) == 0#64 then .error .msgDecode
            else
              match decodeVarint (b' :: rest0'') with
              | .error e => .error e
              | .ok (index, rest2) =>
                if index.toNat < 2 ^ 32 then
                  .ok { version := version,
                        epoch := out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)),
                        index := index.setWidth 32, remaining := rest2 }
                else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        have hmsg_eq' : msg.bytes = version :: ((pre₁ ++ [byteJ]) ++ b' :: rest0'') := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hpre1' : 1 ≤ (pre₁ ++ [byteJ]).length := by
          rw [List.length_append, List.length_singleton]; omega
        wp_steps 1
        exact hafter _ _ post herr_tail hok_tail hpre1' hlen_lt hmsg_eq' hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [hpre1, arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by simp only [arm64_norm]; sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
