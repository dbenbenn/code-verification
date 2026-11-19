/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.PoolSliceBound -- proof-setup: allow-public-import
import Arm64.Trusted.ISA.Memory
import ProofLib.MallocngBridge
import ProofLib.SepLogic
import ProofLib.SepLogic.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `PoolSliceBound` Instances for `mallocng`, `fine`, and `AllocWithFds.withFds`

Concrete `PoolSliceBound` instances, separated from `PoolSliceBound.lean` so `Main/Proofs/M5*`
modules do not import `Mallocng` or `cliElfBytes`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.PoolSliceBoundInst

open Arm64 SepProp
open ProofLib hiding MallocngAddrs
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits MallocngCostModelIface MallocngCostModelSound MallocngModelEnv
   RustCliAllocBudget mallocngBudgetPool mallocngBudgetPoolAt
   mallocngBudgetPoolAt_mapped_lt_userVa mallocngRustCliAllocBudget mallocngRustCliAllocBudgetAt)
open LibsignalBinary.Heap.Fine
  (fineCostModel fineCostModelIface fineCostModelSound fineRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (aesStorageCell fineHookRustCliAllocBudget mallocngHookBudgetPool mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.PoolSliceBound (PoolSliceBound)
open VerifiedLibraries.Mallocng (MallocngAddrs mallocngAddrsOfPlacement)

private theorem pointsToBytes_perm_rw {m : Memory} :
    ∀ (bs : List (BitVec 8)) {buf : BitVec 64} {R : SepProp},
      (m ⊨ (buf ↦ₛ bs) ∗ R) →
      ∀ i < bs.length, m.perm (buf + BitVec.ofNat 64 i) = some Perm.rw
  | [], _, _, _, i, hi => nomatch hi
  | b :: bs, buf, R, hm, 0, _ => by
    rw [pointsToBytes_cons, sepConj_assoc] at hm
    simpa using (satisfies_pointsTo8_frame hm).2
  | b :: bs, buf, R, hm, i + 1, hi => by
    rw [pointsToBytes_cons, sepConj_assoc] at hm
    have hm' : m ⊨ ((buf + 1#64) ↦ₛ bs) ∗ ((buf ↦₈ b) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    have hrec := pointsToBytes_perm_rw bs hm' i (Nat.lt_of_succ_lt_succ hi)
    have hadj : buf + 1#64 + BitVec.ofNat 64 i = buf + BitVec.ofNat 64 (i + 1) := by
      bv_omega
    rwa [hadj] at hrec

private theorem countPerm_add (m : Memory) (p : Option Perm → Bool) :
    ∀ (a : Nat) (addr : BitVec 64) (b : Nat),
      m.countPerm p addr (a + b) =
        m.countPerm p addr a + m.countPerm p (addr + BitVec.ofNat 64 a) b
  | 0, addr, b => by simp [Memory.countPerm]
  | a + 1, addr, b => by
    have ih := countPerm_add m p a (addr + 1#64) b
    have hadj : addr + 1#64 + BitVec.ofNat 64 a = addr + BitVec.ofNat 64 (a + 1) := by
      bv_omega
    rw [hadj] at ih
    simp only [Nat.succ_add, Memory.countPerm, ih, Nat.add_assoc]

private theorem countRw_eq_len_of_perm_rw {m : Memory} :
    ∀ (n : Nat) (addr : BitVec 64),
      (∀ i < n, m.perm (addr + BitVec.ofNat 64 i) = some Perm.rw) →
      m.countRw addr n = n
  | 0, _, _ => rfl
  | n + 1, addr, h => by
    have h0 : m.perm addr = some Perm.rw := by simpa using h 0 (Nat.zero_lt_succ n)
    have hrest : m.countRw (addr + 1#64) n = n := by
      apply countRw_eq_len_of_perm_rw n (addr + 1#64)
      intro i hi
      have hi1 := h (i + 1) (Nat.succ_lt_succ hi)
      have hadj : addr + 1#64 + BitVec.ofNat 64 i = addr + BitVec.ofNat 64 (i + 1) := by
        bv_omega
      rwa [hadj]
    unfold Memory.countRw at hrest ⊢
    simp [Memory.countPerm, h0, hrest]
    omega

private theorem countRw_le_rwBytes {m : Memory} (buf : BitVec 64) (n : Nat)
    (hbnd : buf.toNat + n ≤ 2 ^ 64) :
    m.countRw buf n ≤ ProofLib.rwBytes m := by
  unfold ProofLib.rwBytes Memory.countRw
  let pre := buf.toNat
  let suf := 2 ^ 64 - (buf.toNat + n)
  have htot : (2 ^ 64 : Nat) = pre + (n + suf) := by omega
  have hbase : (0#64 : BitVec 64) + BitVec.ofNat 64 pre = buf := by
    change (0#64 : BitVec 64) + BitVec.ofNat 64 buf.toNat = buf
    bv_omega
  rw [htot, countPerm_add m _ pre 0#64 (n + suf), hbase, countPerm_add m _ n buf suf]
  omega

theorem mallocngBudgetPoolAt_slice_len_le {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {γ : GhostName} {addrs : MallocngAddrs} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s : State} {buf : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp}
    (henf : lim.enforced = true)
    (hcap : lim.staticBytes + M.footprint st ≤ lim.physCap)
    (hbs64 : bs.length ≤ 2 ^ 64)
    (hsat : s.mem ⊨ (buf ↦ₛ bs) ∗ mallocngBudgetPoolAt M I γ addrs tp brkStart lim st s ∗ R) :
    bs.length ≤ lim.physCap := by
  by_cases hzero : bs.length = 0
  · omega
  · have hpos : 0 < bs.length := Nat.pos_of_ne_zero hzero
    have hperm : ∀ i < bs.length, s.mem.perm (buf + BitVec.ofNat 64 i) = some Perm.rw :=
      pointsToBytes_perm_rw bs hsat
    have hpoolSat :
        s.mem ⊨ mallocngBudgetPoolAt M I γ addrs tp brkStart lim st s ∗ ((buf ↦ₛ bs) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat
    have hlt_va : ∀ i < bs.length, (buf + BitVec.ofNat 64 i).toNat < Arm64.USER_VA_LIMIT := by
      intro i hi
      apply mallocngBudgetPoolAt_mapped_lt_userVa hS henf hpoolSat
      rw [hperm i hi]
      rfl
    have hLim : Arm64.USER_VA_LIMIT = 2 ^ 48 := rfl
    have hbuf_va : buf.toNat < 2 ^ 48 := by
      have h0 := hlt_va 0 hpos
      rw [hLim] at h0
      simpa using h0
    have hno_wrap : buf.toNat + bs.length ≤ 2 ^ 64 := by
      by_contra hgt
      have hk_lt : 2 ^ 64 - 1 - buf.toNat < bs.length := by omega
      have hlast := hlt_va (2 ^ 64 - 1 - buf.toNat) hk_lt
      rw [hLim] at hlast
      have hto : (buf + BitVec.ofNat 64 (2 ^ 64 - 1 - buf.toNat)).toNat = 2 ^ 64 - 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      omega
    have hcount_eq : s.mem.countRw buf bs.length = bs.length :=
      countRw_eq_len_of_perm_rw bs.length buf hperm
    have hle_rw : bs.length ≤ ProofLib.rwBytes s.mem := by
      rw [← hcount_eq]
      exact countRw_le_rwBytes buf bs.length hno_wrap
    unfold mallocngBudgetPoolAt at hpoolSat
    simp only [sepExists_sepConj_left] at hpoolSat
    obtain ⟨staticIvs, hpoolSat⟩ := (satisfies_sepExists _ _).mp hpoolSat
    obtain ⟨ivs0, hpoolSat⟩ := (satisfies_sepExists _ _).mp hpoolSat
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpoolSat
    obtain ⟨hInv0, hEnvSat⟩ := hpoolSat
    obtain ⟨⟨_, hStSum, _, hCov⟩, _⟩ := hInv0 henf
    let φ := (ivs0.map Prod.snd).sum ≤ M.footprint st
    have hent : MallocngModelEnv M I γ addrs tp brkStart st ivs0 s ∗ ((buf ↦ₛ bs) ∗ R) ⊢
        ⌜φ⌝ ∗ (MallocngModelEnv M I γ addrs tp brkStart st ivs0 s ∗ ((buf ↦ₛ bs) ∗ R)) := by
      unfold MallocngModelEnv
      have hh : I.HeapM γ addrs tp brkStart s.brk st ivs0 ⊢
          ⌜φ⌝ ∗ I.HeapM γ addrs tp brkStart s.brk st ivs0 :=
        Entails.extract_heap_fact fun hp hhp =>
          (hS.heap_footprint_bound γ addrs tp brkStart s.brk st ivs0 hp hhp).2.1
      have hEq :
          (⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
            (⌜φ⌝ ∗ I.HeapM γ addrs tp brkStart s.brk st ivs0)) ∗ ((buf ↦ₛ bs) ∗ R) =
          ⌜φ⌝ ∗ ((⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
            I.HeapM γ addrs tp brkStart s.brk st ivs0) ∗ ((buf ↦ₛ bs) ∗ R)) := by sep_ac_rfl
      exact Entails.trans (sepConj_mono_left (sepConj_mono_right hh)) (Entails.of_eq hEq)
    have hEnvSat' := Satisfies.mono hent hEnvSat
    rw [satisfies_pure_sepConj] at hEnvSat'
    have hDynSum : (ivs0.map Prod.snd).sum ≤ M.footprint st := hEnvSat'.1
    have hTotCov : ∀ a : BitVec 64, (s.mem.perm a).mapped = true →
        ∃ iv ∈ staticIvs ++ ivs0, (a - iv.1).toNat < iv.2 := by
      intro a hmap
      rcases hCov a hmap with ⟨iv, hm, hlt⟩ | ⟨iv, hm, hlt⟩
      · exact ⟨iv, List.mem_append_left _ hm, hlt⟩
      · exact ⟨iv, List.mem_append_right _ hm, hlt⟩
    have hrw_le : ProofLib.rwBytes s.mem ≤ ((staticIvs ++ ivs0).map Prod.snd).sum :=
      ProofLib.rwBytes_le_intervals_sum hTotCov
    rw [List.map_append, List.sum_append] at hrw_le
    omega

instance instPoolSliceBoundMallocngAt (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (addrs : MallocngAddrs) (tp brkStart : BitVec 64) :
    PoolSliceBound (mallocngRustCliAllocBudgetAt M I hS γ addrs tp brkStart) where
  slice_len_le henf hcap hbs64 hsat :=
    mallocngBudgetPoolAt_slice_len_le hS henf hcap hbs64 hsat

instance instPoolSliceBoundMallocng (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    PoolSliceBound (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) :=
  instPoolSliceBoundMallocngAt M I hS γ (mallocngAddrsOfPlacement mpl) tp brkStart

instance instPoolSliceBoundFine (γ : GhostName) (mpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) :
    PoolSliceBound (fineRustCliAllocBudget γ mpl tp brkStart) :=
  instPoolSliceBoundMallocng fineCostModel fineCostModelIface fineCostModelSound γ mpl tp brkStart

instance instPoolSliceBoundMallocngHook (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    PoolSliceBound (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) where
  slice_len_le {lim st s buf bs R} henf hcap hbs64 hsat := by
    change s.mem ⊨ (buf ↦ₛ bs) ∗ mallocngHookBudgetPool M I γ mpl tp brkStart lim st s ∗ R at hsat
    unfold mallocngHookBudgetPool mallocngBudgetPool at hsat
    have hsat' :
        s.mem ⊨ (buf ↦ₛ bs) ∗
          mallocngBudgetPoolAt M I γ (mallocngAddrsOfPlacement mpl) tp brkStart lim st s ∗
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗
            aesStorageCell brkStart ∗
            ⌜lim.enforced = true → _⌝ ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat
    exact mallocngBudgetPoolAt_slice_len_le hS henf hcap hbs64 hsat'

instance instPoolSliceBoundFineHook (γ : GhostName) (mpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) :
    PoolSliceBound (fineHookRustCliAllocBudget γ mpl tp brkStart) :=
  instPoolSliceBoundMallocngHook
    fineCostModel fineCostModelIface fineCostModelSound γ mpl tp brkStart

instance instPoolSliceBoundWithFds {M : AllocCostModel} (A : RustCliAllocBudget M)
    [PoolSliceBound A] :
    PoolSliceBound (withFds A) where
  slice_len_le {lim st s buf bs R} henf hcap hbs64 hsat := by
    rw [withFds_pool_enforced A henf st s] at hsat
    have hsat' : s.mem ⊨ (buf ↦ₛ bs) ∗ A.pool lim st s ∗ (⌜_⌝ ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat
    exact PoolSliceBound.slice_len_le (A := A) henf hcap hbs64 hsat'

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.PoolSliceBoundInst
