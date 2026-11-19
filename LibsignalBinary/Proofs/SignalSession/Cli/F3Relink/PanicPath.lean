/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.ProgramReflection
public import ProofLib.SepLogic.Stack
public import ProofLib.StdStartup.CleanupAndExit
public import ProofLib.Process.Core
public import LibsignalBinary.Specifications.SignalSession.CliProcess
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.CoreLemmas
import ProofLib.Invariant
import ProofLib.BV.Arith
import ProofLib.BV.WidthNorm

/-!
# Layout-Generic Linked Rust Panic & `musl` `abort` Termination Proofs

Proves whole-path termination to `ExecStatus.Signaled 6#7` (`SIGABRT`, exit status `134`),
preserving `fs` and `trace`, under any hook-free `Syscall.standard` `Program` (and directly under
`Program.pureMem` / `ProcessRunsTo ... (OutcomeMatchesProcess .aborted)`) for:

1. The `musl` `abort` chain (`musl_abort_to_sigabrt`, 43 dynamic instructions, `0x100` B stack):
   `abort` → `raise(6)` → `__block_app_sigs` (`rt_sigprocmask(SIG_BLOCK, &app_mask, &old, 8)`) →
   `tkill(tid = 1, 6)` → `__syscall_ret` (`x0 = 0` fast path) → `__restore_sigs`
   (`rt_sigprocmask(SIG_SETMASK, &old, 0, 8)` → synchronous `.Signaled 6#7`).
2. The abort-only `rdl_shim.S` panic handlers (`rdl_panic_shims_to_sigabrt`):
   `rust_begin_unwind` (`b abort`) and `__rust_alloc_error_handler` (`b abort`).
3. Every linked `core`/`alloc` panic entry point (`panicEntry_reaches_sigabrt`, arbitrary
   registers `x0..x30`, `pstate`, `vregs`, `0x200` B combined stack), certified by a fast
   `WordTree`-backed layout-generic validator `checkF3PanicCode` / `f3PanicCode_of_wordTree`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.PanicPath

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CryptoVerification.SignalSession (OutcomeMatchesProcess)

/-! ## 1. Layout-Generic Address Bundle and Preconditions -/

/-- Layout-generic addresses of the `musl` `abort` chain, `rdl_shim.S` abort-only handlers,
    readable `.rodata`/`.got` tables referenced by `core`/`alloc` panic wrappers, and all linked
    Rust panic entry points. -/
structure F3PanicAddrs where
  /-- `musl` `abort` entry point. -/
  abortAddr : BitVec 64
  /-- `musl` `raise` entry point. -/
  raiseAddr : BitVec 64
  /-- `musl` `__block_app_sigs` entry point. -/
  blockAppSigsAddr : BitVec 64
  /-- `musl` `__restore_sigs` entry point. -/
  restoreSigsAddr : BitVec 64
  /-- `musl` `__syscall_ret` entry point. -/
  syscallRetAddr : BitVec 64
  /-- `musl` 64-bit `app_mask` constant in `.rodata` (with bit 5 `SIGABRT_MASK` set). -/
  appMaskAddr : BitVec 64
  /-- Abort-only `rdl_shim.S` `rust_begin_unwind` (`b abort`). -/
  rustBeginUnwindAddr : BitVec 64
  /-- Abort-only `rdl_shim.S` `__rust_alloc_error_handler` (`b abort`). -/
  rustAllocErrorHandlerAddr : BitVec 64
  /-- 1024-byte (256 × 4 B) `.rodata` tables indexed by `x0 &&& 0xff` (`ldrsw [rn, rm, lsl #2]`). -/
  roAssertTable32Addrs : List (BitVec 64)
  /-- 2048-byte (256 × 8 B) `.rodata` tables indexed by `x0 &&& 0xff` (`ldr [rn, rm, lsl #3]`). -/
  roAssertTable64Addrs : List (BitVec 64)
  /-- 8-byte readable `.got`/`.data.rel.ro` formatter pointers loaded (never dereferenced). -/
  gotRead8Addrs : List (BitVec 64)
  /-- Linked Rust panic entry points (e.g. the 19 `cliPanicSymbolsLinked` addresses). -/
  panicEntries : List (BitVec 64)
  deriving DecidableEq, Repr

/-- Every abort, shim, and linked Rust panic entry point covered by `addrs`. -/
@[expose] def F3PanicAddrs.allEntries (a : F3PanicAddrs) : List (BitVec 64) :=
  a.abortAddr :: a.rustBeginUnwindAddr :: a.rustAllocErrorHandlerAddr :: a.panicEntries

/-- `n` bytes of strictly positive, non-wrapping read-write stack `[sp - n, sp)` below `sp`. -/
@[expose] def StackRW (m : Memory) (sp : BitVec 64) (n : Nat) : Prop :=
  n < sp.toNat ∧
  ∀ k : Nat, k < n →
    let a := sp - BitVec.ofNat 64 n + BitVec.ofNat 64 k
    (m.perm a).r = true ∧ (m.perm a).w = true ∧ (m.perm a).x = false

/-- Preconditions for `musl` `abort` and the 1-instruction `rdl_shim.S` abort handlers (`0x100` B
    stack, default `SIGABRT` disposition, clear signal mask/pending, TLS `tid = 1`, frozen
    `app_mask` with `SIGABRT` bit set). -/
structure PanicAbortPre (P : Program) (addrs : F3PanicAddrs) (s : State) : Prop where
  codeLoaded        : P.CodeLoaded s.mem
  running           : s.status = .Running
  spAligned         : s.spAligned = true
  stackRW           : StackRW s.mem s.sp 0x100
  sigMask           : s.sigMask = 0#64
  sigPending        : s.sigPending = 0#64
  sigAbrtDfl        : (s.getSigAction LINUX_SIGABRT).handler = SIG_DFL
  appMaskNeZero     : addrs.appMaskAddr ≠ 0#64
  appMaskNoWrap     : addrs.appMaskAddr.toNat + 8 ≤ 2 ^ 64
  appMaskCanRead    : s.mem.canRead addrs.appMaskAddr 8 = true
  appMaskFrozen     : s.mem.allPerm (·.frozen) addrs.appMaskAddr 8 = true
  appMaskBlocksAbrt : (s.mem.read64 addrs.appMaskAddr &&& SIGABRT_MASK) ≠ 0#64
  tidCanRead        : s.mem.canRead (s.tpidrEl0 - 0xa8#64) 4 = true
  tidVal            : s.mem.read32 (s.tpidrEl0 - 0xa8#64) = 1#32
  tidDisjoint       : DisjointRegions (s.sp - 0x100#64) 0x100 (s.tpidrEl0 - 0xa8#64) 4

/-- Preconditions for any linked Rust panic entry point (`0x200` B combined stack plus readable
    `.rodata` assert tables and `.got` formatter pointers). -/
structure PanicEntryPre (P : Program) (addrs : F3PanicAddrs) (s : State) : Prop where
  codeLoaded        : P.CodeLoaded s.mem
  running           : s.status = .Running
  spAligned         : s.spAligned = true
  stackRW           : StackRW s.mem s.sp 0x200
  sigMask           : s.sigMask = 0#64
  sigPending        : s.sigPending = 0#64
  sigAbrtDfl        : (s.getSigAction LINUX_SIGABRT).handler = SIG_DFL
  appMaskNeZero     : addrs.appMaskAddr ≠ 0#64
  appMaskNoWrap     : addrs.appMaskAddr.toNat + 8 ≤ 2 ^ 64
  appMaskCanRead    : s.mem.canRead addrs.appMaskAddr 8 = true
  appMaskFrozen     : s.mem.allPerm (·.frozen) addrs.appMaskAddr 8 = true
  appMaskBlocksAbrt : (s.mem.read64 addrs.appMaskAddr &&& SIGABRT_MASK) ≠ 0#64
  tidCanRead        : s.mem.canRead (s.tpidrEl0 - 0xa8#64) 4 = true
  tidVal            : s.mem.read32 (s.tpidrEl0 - 0xa8#64) = 1#32
  tidDisjoint       : DisjointRegions (s.sp - 0x200#64) 0x200 (s.tpidrEl0 - 0xa8#64) 4
  roTable32Readable : ∀ a ∈ addrs.roAssertTable32Addrs, s.mem.Readable a 1024
  roTable64Readable : ∀ a ∈ addrs.roAssertTable64Addrs, s.mem.Readable a 2048
  gotRead8CanRead   : ∀ a ∈ addrs.gotRead8Addrs, s.mem.canRead a 8 = true

/-! ## 2. Low-Level Memory, Stack, and Permission Helpers -/

theorem StackRW.shrink {m : Memory} {sp : BitVec 64} {n d m' : Nat}
    (h : StackRW m sp n) (hd : d + m' ≤ n) :
    StackRW m (sp - BitVec.ofNat 64 d) m' := by
  refine ⟨?_, ?_⟩
  · have hlt := h.1
    bv_omega
  · intro k hk
    have hidx : (n - d - m') + k < n := by omega
    have hperm := h.2 ((n - d - m') + k) hidx
    have ha : sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - d - m' + k) =
        sp - BitVec.ofNat 64 d - BitVec.ofNat 64 m' + BitVec.ofNat 64 k := by
      have hlt := h.1
      bv_omega
    rwa [ha] at hperm

theorem StackRW.of_stackAt {m : Memory} {sp : BitVec 64} {n : Nat} {R : SepProp}
    (hsp : n < sp.toNat) (hm : m ⊨ stackAt sp n ∗ R) :
    StackRW m sp n := by
  refine ⟨hsp, fun k hk => ?_⟩
  have hmem := (IsBlock.memRegion (sp - BitVec.ofNat 64 n) n).perm_rw hm
    (a := sp - BitVec.ofNat 64 n + BitVec.ofNat 64 k) (by
      unfold InRegion
      have hsub : sp - BitVec.ofNat 64 n + BitVec.ofNat 64 k - (sp - BitVec.ofNat 64 n) =
          BitVec.ofNat 64 k := by bv_omega
      rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hk)
  simp [hmem, Perm.rw]

private theorem StackRW.of_perm_eq {m m' : Memory} {sp : BitVec 64} {n : Nat}
    (h : StackRW m sp n) (hp : ∀ a, m'.perm a = m.perm a) : StackRW m' sp n :=
  ⟨h.1, fun k hk => by simpa only [hp] using h.2 k hk⟩

private theorem StackRW.sub_ne_zero {m : Memory} {sp : BitVec 64} {n off : Nat}
    (h : StackRW m sp n) (hoff : off ≤ n) :
    sp - BitVec.ofNat 64 off ≠ 0#64 := by
  have hlt := h.1
  bv_omega

private theorem StackRW.sub_no_wrap {m : Memory} {sp : BitVec 64} {n off len : Nat}
    (h : StackRW m sp n) (hoff : off ≤ n) (hlen : len ≤ off) :
    (sp - BitVec.ofNat 64 off).toNat + len ≤ 2 ^ 64 := by
  have hlt := h.1
  have hsp := sp.isLt
  bv_omega

private theorem StackRW.allPerm_r_sub {m : Memory} {sp : BitVec 64} {n off len : Nat}
    (h : StackRW m sp n) (hoff : off ≤ n) (hlen : len ≤ off) :
    m.allPerm (·.r) (sp - BitVec.ofNat 64 off) len = true := by
  rw [Memory.allPerm_iff]
  intro k hk
  have hidx : n - off + k < n := by omega
  have ha : sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - off + k) =
      sp - BitVec.ofNat 64 off + BitVec.ofNat 64 k := by
    have hlt := h.1; bv_omega
  have hp := h.2 (n - off + k) hidx
  rw [ha] at hp
  exact hp.1

private theorem StackRW.canWrite_sub {m : Memory} {sp : BitVec 64} {n off len : Nat}
    (h : StackRW m sp n) (hoff : off ≤ n) (hlen : len ≤ off) :
    m.canWrite (sp - BitVec.ofNat 64 off) len = true := by
  unfold Memory.canWrite
  rw [Memory.allPerm_iff]
  intro k hk
  have hidx : n - off + k < n := by omega
  have ha : sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - off + k) =
      sp - BitVec.ofNat 64 off + BitVec.ofNat 64 k := by
    have hlt := h.1; bv_omega
  have hp := h.2 (n - off + k) hidx
  rw [ha] at hp
  simp [hp.2.1, hp.2.2]

private theorem StackRW.canWrite_sub_add {m : Memory} {sp : BitVec 64} {n spDrop off len : Nat}
    (h : StackRW m sp n) (hdrop : spDrop ≤ n) (hoff : off + len ≤ spDrop) :
    m.canWrite (sp - BitVec.ofNat 64 spDrop + BitVec.ofNat 64 off) len = true := by
  have hcw := h.canWrite_sub (off := spDrop - off) (len := len) (by omega) (by omega)
  have heq : sp - BitVec.ofNat 64 (spDrop - off) =
      sp - BitVec.ofNat 64 spDrop + BitVec.ofNat 64 off := by
    have hlt := h.1; bv_omega
  rwa [heq] at hcw

private theorem StackRW.inRegion_sub {m : Memory} {sp : BitVec 64} {n off len : Nat}
    (h : StackRW m sp n) (hoff : off ≤ n) (hlen : len ≤ off) {k : Nat} (hk : k < len) :
    InRegion (sp - BitVec.ofNat 64 n) n (sp - BitVec.ofNat 64 off + BitVec.ofNat 64 k) := by
  unfold InRegion
  have hlt := h.1
  have hsub : sp - BitVec.ofNat 64 off + BitVec.ofNat 64 k - (sp - BitVec.ofNat 64 n) =
      BitVec.ofNat 64 (n - off + k) := by bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem mem_ne_of_disjointRegions {b1 b2 a1 a2 : BitVec 64} {n1 n2 : Nat}
    (hd : DisjointRegions b1 n1 b2 n2)
    (h1 : InRegion b1 n1 a1) (h2 : InRegion b2 n2 a2) : a1 ≠ a2 := by
  intro heq
  subst heq
  unfold DisjointRegions at hd
  unfold InRegion at h1 h2
  have h1' : (a1 - b1).toNat < n1 := h1
  have h2' : (a1 - b2).toNat < n2 := h2
  bv_omega

private theorem read8_write8_of_ne {m : Memory} {w a : BitVec 64} {v : BitVec 8}
    (hne : w ≠ a) : (m.write8 w v).read8 a = m.read8 a := by
  simp [Memory.read8, Memory.write8, Ne.symm hne]

private theorem isLazyFree_write8_eq (m : Memory) (w a : BitVec 64) (v : BitVec 8) :
    (m.write8 w v).isLazyFree a = if a = w then false else m.isLazyFree a := by
  by_cases ha : a = w
  · subst ha; unfold Memory.isLazyFree Memory.write8; simp; cases m.rawPerm a <;> rfl
  · unfold Memory.isLazyFree Memory.write8; simp [ha]

private theorem isLazyFree_write8_self (m : Memory) (w : BitVec 64) (v : BitVec 8) :
    (m.write8 w v).isLazyFree w = false := by
  rw [isLazyFree_write8_eq]; simp

private theorem isLazyFree_write8_false {m : Memory} (w a : BitVec 64) (v : BitVec 8)
    (h : m.isLazyFree a = false) : (m.write8 w v).isLazyFree a = false := by
  rw [isLazyFree_write8_eq]; split <;> [rfl; exact h]

private theorem isLazyFree_writeSized_false {m : Memory} (sz : MemWidth) (w a : BitVec 64)
    (v : BitVec 64) (h : m.isLazyFree a = false) :
    (m.writeSized sz w v).isLazyFree a = false := by
  cases sz <;> simp [Memory.writeSized, Memory.write16, Memory.write32, Memory.write64, h]

private theorem perm_writeSized_eq (m : Memory) (sz : MemWidth) (w a : BitVec 64) (v : BitVec 64) :
    (m.writeSized sz w v).perm a = m.perm a := by
  cases sz <;> simp [Memory.writeSized, Memory.write16, Memory.write32, Memory.write64]

private theorem readable_writeSized {m : Memory} {base : BitVec 64} {len : Nat}
    (sz : MemWidth) (w : BitVec 64) (v : BitVec 64) (h : m.Readable base len) :
    (m.writeSized sz w v).Readable base len := by
  intro a ha
  exact ⟨by rw [perm_writeSized_eq]; exact (h a ha).1,
    isLazyFree_writeSized_false sz w a v (h a ha).2⟩

private theorem canRead_writeSized_of_canRead {m : Memory} {addr : BitVec 64} {len : Nat}
    (sz : MemWidth) (w : BitVec 64) (v : BitVec 64) (h : m.canRead addr len = true) :
    (m.writeSized sz w v).canRead addr len = true := by
  cases sz
  · exact Memory.canRead_write8_of_canRead w _ h
  · exact Memory.canRead_write16_of_canRead w _ h
  · exact Memory.canRead_write32_of_canRead w _ h
  · exact Memory.canRead_write64_of_canRead w _ h

private theorem canRead_write64_self {m : Memory} {a v : BitVec 64}
    (hr : m.allPerm (·.r) a 8 = true) :
    (m.write64 a v).canRead a 8 = true := by
  unfold Memory.canRead
  have hp : (m.write64 a v).allPerm (·.r) a 8 = true := by
    rw [Memory.allPerm_iff] at hr ⊢
    intro k hk
    have hp8 : (m.write64 a v).perm (a + BitVec.ofNat 64 k) = m.perm (a + BitVec.ofNat 64 k) := by
      simp [Memory.write64]
    rw [hp8]; exact hr k hk
  rw [hp, Bool.true_and]
  have h0 : (m.write64 a v).isLazyFree a = false := by
    unfold Memory.write64; simp only [BitVec.add_zero]
    exact isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _
      (isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _
        (isLazyFree_write8_false _ _ _ (isLazyFree_write8_self _ _ _)))))))
  have h1 : (m.write64 a v).isLazyFree (a + 1#64) = false := by
    unfold Memory.write64
    exact isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _
      (isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _
        (isLazyFree_write8_self _ _ _))))))
  have h2 : (m.write64 a v).isLazyFree (a + 2#64) = false := by
    unfold Memory.write64
    exact isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _
      (isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _ (isLazyFree_write8_self _ _ _)))))
  have h3 : (m.write64 a v).isLazyFree (a + 3#64) = false := by
    unfold Memory.write64
    exact isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _
      (isLazyFree_write8_false _ _ _ (isLazyFree_write8_self _ _ _))))
  have h4 : (m.write64 a v).isLazyFree (a + 4#64) = false := by
    unfold Memory.write64
    exact isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _
      (isLazyFree_write8_self _ _ _)))
  have h5 : (m.write64 a v).isLazyFree (a + 5#64) = false := by
    unfold Memory.write64
    exact isLazyFree_write8_false _ _ _ (isLazyFree_write8_false _ _ _ (isLazyFree_write8_self _ _ _))
  have h6 : (m.write64 a v).isLazyFree (a + 6#64) = false := by
    unfold Memory.write64
    exact isLazyFree_write8_false _ _ _ (isLazyFree_write8_self _ _ _)
  have h7 : (m.write64 a v).isLazyFree (a + 7#64) = false := by
    unfold Memory.write64
    exact isLazyFree_write8_self _ _ _
  simp only [Memory.allNoLazyFree]
  have ha2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have ha3 : a + 2#64 + 1#64 = a + 3#64 := by bv_omega
  have ha4 : a + 3#64 + 1#64 = a + 4#64 := by bv_omega
  have ha5 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
  have ha6 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
  have ha7 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
  rw [h0, h1, ha2, h2, ha3, h3, ha4, h4, ha5, h5, ha6, h6, ha7, h7]
  rfl

private theorem writeBytes_leBytes64_eq_write64 (m : Memory) (a v : BitVec 64) :
    m.writeBytes a (leBytes64 v) = m.write64 a v := by
  simp only [leBytes64, Memory.writeBytes, Memory.write64, BitVec.add_zero]
  have ha2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have ha3 : a + 2#64 + 1#64 = a + 3#64 := by bv_omega
  have ha4 : a + 3#64 + 1#64 = a + 4#64 := by bv_omega
  have ha5 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
  have ha6 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
  have ha7 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
  rw [ha2, ha3, ha4, ha5, ha6, ha7]

private theorem read64_write64_self (m : Memory) (a v : BitVec 64) :
    (m.write64 a v).read64 a = v :=
  Memory.read64_write64_same m a v

private theorem read64_write64_disjoint {m : Memory} {w a v : BitVec 64}
    (hd : DisjointRegions w 8 a 8) :
    (m.write64 w v).read64 a = m.read64 a := by
  have hbyte : ∀ j : Nat, j < 8 → (m.write64 w v).read8 (a + BitVec.ofNat 64 j) =
      m.read8 (a + BitVec.ofNat 64 j) := by
    intro j hj
    have hne : ∀ i : Nat, i < 8 → w + BitVec.ofNat 64 i ≠ a + BitVec.ofNat 64 j := by
      intro i hi
      exact mem_ne_of_disjointRegions hd
        (by unfold InRegion; have : w + BitVec.ofNat 64 i - w = BitVec.ofNat 64 i := by bv_omega
            rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)
        (by unfold InRegion; have : a + BitVec.ofNat 64 j - a = BitVec.ofNat 64 j := by bv_omega
            rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hj)
    unfold Memory.write64
    simp only [BitVec.add_zero]
    rw [read8_write8_of_ne (hne 7 (by omega)), read8_write8_of_ne (hne 6 (by omega)),
        read8_write8_of_ne (hne 5 (by omega)), read8_write8_of_ne (hne 4 (by omega)),
        read8_write8_of_ne (hne 3 (by omega)), read8_write8_of_ne (hne 2 (by omega)),
        read8_write8_of_ne (hne 1 (by omega)),
        read8_write8_of_ne (by simpa using hne 0 (by omega))]
  unfold Memory.read64
  rw [hbyte 7 (by omega), hbyte 6 (by omega), hbyte 5 (by omega), hbyte 4 (by omega),
      hbyte 3 (by omega), hbyte 2 (by omega), hbyte 1 (by omega), hbyte 0 (by omega)]

private theorem read32_writeSized_disjoint {m : Memory} {b1 a w v : BitVec 64} {n1 : Nat}
    {sz : MemWidth}
    (hd : DisjointRegions b1 n1 a 4)
    (hin : ∀ i : Nat, i < sz.bytes → InRegion b1 n1 (w + BitVec.ofNat 64 i)) :
    (m.writeSized sz w v).read32 a = m.read32 a := by
  have hbyte : ∀ j : Nat, j < 4 →
      (m.writeSized sz w v).read8 (a + BitVec.ofNat 64 j) = m.read8 (a + BitVec.ofNat 64 j) := by
    intro j hj
    have ha : InRegion a 4 (a + BitVec.ofNat 64 j) := by
      unfold InRegion
      have : a + BitVec.ofNat 64 j - a = BitVec.ofNat 64 j := by bv_omega
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hj
    have hne : ∀ i : Nat, i < sz.bytes → w + BitVec.ofNat 64 i ≠ a + BitVec.ofNat 64 j :=
      fun i hi => mem_ne_of_disjointRegions hd (hin i hi) ha
    cases sz with
    | B8 =>
      simp only [Memory.writeSized]
      exact read8_write8_of_ne (by simpa using hne 0 (by decide))
    | H16 =>
      simp only [Memory.writeSized, Memory.write16, BitVec.add_zero]
      rw [read8_write8_of_ne (hne 1 (by decide)),
          read8_write8_of_ne (by simpa using hne 0 (by decide))]
    | W32 =>
      simp only [Memory.writeSized, Memory.write32, BitVec.add_zero]
      rw [read8_write8_of_ne (hne 3 (by decide)), read8_write8_of_ne (hne 2 (by decide)),
          read8_write8_of_ne (hne 1 (by decide)),
          read8_write8_of_ne (by simpa using hne 0 (by decide))]
    | X64 =>
      simp only [Memory.writeSized, Memory.write64, BitVec.add_zero]
      rw [read8_write8_of_ne (hne 7 (by decide)), read8_write8_of_ne (hne 6 (by decide)),
          read8_write8_of_ne (hne 5 (by decide)), read8_write8_of_ne (hne 4 (by decide)),
          read8_write8_of_ne (hne 3 (by decide)), read8_write8_of_ne (hne 2 (by decide)),
          read8_write8_of_ne (hne 1 (by decide)),
          read8_write8_of_ne (by simpa using hne 0 (by decide))]
  unfold Memory.read32
  rw [hbyte 3 (by omega), hbyte 2 (by omega), hbyte 1 (by omega), hbyte 0 (by omega)]

private theorem read64_of_keepsFrozen {m m' : Memory} {a : BitVec 64}
    (hkf : m.KeepsFrozen m') (hf : m.allPerm (·.frozen) a 8 = true) :
    m'.read64 a = m.read64 a := by
  rw [Memory.allPerm_iff] at hf
  have hb : ∀ k : Nat, k < 8 → m'.read8 (a + BitVec.ofNat 64 k) = m.read8 (a + BitVec.ofNat 64 k) :=
    fun k hk => (hkf _ (hf k hk)).1
  unfold Memory.read64
  rw [hb 7 (by omega), hb 6 (by omega), hb 5 (by omega), hb 4 (by omega),
      hb 3 (by omega), hb 2 (by omega), hb 1 (by omega), hb 0 (by omega)]

private theorem canRead_of_keepsFrozen {m m' : Memory} {a : BitVec 64} {n : Nat}
    (hkf : m.KeepsFrozen m') (hf : m.allPerm (·.frozen) a n = true)
    (hcr : m.canRead a n = true) : m'.canRead a n = true := by
  rw [Memory.allPerm_iff] at hf
  unfold Memory.canRead at hcr ⊢
  simp only [Bool.and_eq_true] at hcr ⊢
  constructor
  · rw [Memory.allPerm_iff] at hcr ⊢
    intro k hk
    rw [(hkf _ (hf k hk)).2.1]
    exact hcr.1 k hk
  · have hlf : ∀ j : Nat, ∀ addr : BitVec 64,
        (∀ i < j, m.Frozen (addr + BitVec.ofNat 64 i)) →
        m.allNoLazyFree addr j = true → m'.allNoLazyFree addr j = true := by
      intro j
      induction j with
      | zero => intros; rfl
      | succ j ih =>
        intro addr hfj hno
        simp only [Memory.allNoLazyFree, Bool.and_eq_true] at hno ⊢
        refine ⟨?_, ih (addr + 1#64) (fun i hi => by
          have := hfj (i + 1) (by omega)
          rwa [show addr + BitVec.ofNat 64 (i + 1) = addr + 1#64 + BitVec.ofNat 64 i by bv_omega] at this) hno.2⟩
        have hf0 := hfj 0 (by omega)
        simp only [BitVec.add_zero] at hf0
        rw [(hkf _ hf0).2.2.1]
        exact hno.1
    exact hlf n a hf hcr.2

private theorem allPerm_frozen_of_keepsFrozen {m m' : Memory} {a : BitVec 64} {n : Nat}
    (hkf : m.KeepsFrozen m') (hf : m.allPerm (·.frozen) a n = true) :
    m'.allPerm (·.frozen) a n = true := by
  rw [Memory.allPerm_iff] at hf ⊢
  intro k hk
  rw [(hkf _ (hf k hk)).2.1]
  exact hf k hk

private theorem codeLoaded_of_keepsFrozen {P : Program} {m m' : Memory}
    (hCL : P.CodeLoaded m) (hkf : m.KeepsFrozen m') : P.CodeLoaded m' := by
  refine Program.CodeLoaded.intro hCL.aligned hCL.no_wrap fun i hi => ?_
  have hfr : m.Frozen (P.base + BitVec.ofNat 64 i) := by
    unfold Memory.Frozen
    rw [hCL.perm_eq i hi]
    rfl
  obtain ⟨hr, hp, hlf, _⟩ := hkf _ hfr
  exact ⟨hr.trans (hCL.byte_eq i hi), hp.trans (hCL.perm_eq i hi),
    hlf.trans (hCL.isLazyFree_eq i hi)⟩

private theorem steps_exec {P : Program} {s s' sf : State} {inst : Instr}
    (hCL : P.CodeLoaded s.mem)
    (hrun : s.status = .Running)
    (hfetch : P.fetch s.pc = some inst)
    (heval : P.evalInst inst s = s')
    (hrest : Steps P s' sf) :
    Steps P s sf := by
  rw [← heval] at hrest
  exact Steps.step (Step.exec hrun (Program.fetchMem_of_fetch hCL hfetch)) hrest

private theorem advancePC_eq_setPC {s : State} {pc' : BitVec 64} (h : s.pc + 4#64 = pc') :
    s.advancePC = s.setPC pc' := by
  cases s; simp only [State.advancePC, State.setPC] at h ⊢; congr 1

private theorem evalInst_bl_eq {P : Program} {s : State} {off pc' lr' : BitVec 64}
    (hlr : s.pc + 4#64 = lr') (hpc : s.pc + off = pc') :
    P.evalInst (.bl off) s = (s.writeReg64 .lr lr').setPC pc' := by
  simp only [Program.evalInst, execInstWithSvc, hlr, hpc]

private theorem evalInst_movz_eq {P : Program} {s : State} {w : Width} {rd : Reg} {imm16 : BitVec 16}
    {v pc' : BitVec 64} (hv : (match w with | .W32 => ((imm16.zeroExtend 64).truncate 32).zeroExtend 64 | .W64 => imm16.zeroExtend 64) = v)
    (hpc : s.pc + 4#64 = pc') :
    P.evalInst (.moveWide w .MOVZ rd imm16 0) s = (s.writeReg64 rd v).setPC pc' := by
  dsimp only [Program.evalInst, execInstWithSvc, execMoveWide]
  rw [show (imm16.zeroExtend 64) <<< 0 = imm16.zeroExtend 64 by bv_omega]
  cases w
  · dsimp only [] at hv
    simp only [State.writeReg, hv]
    exact advancePC_eq_setPC (by simpa [State.writeReg64] using hpc)
  · dsimp only [] at hv
    simp only [State.writeReg, hv]
    exact advancePC_eq_setPC (by simpa [State.writeReg64] using hpc)

private theorem evalInst_movReg_eq {P : Program} {s : State} {w : Width} {rd rm : Reg}
    {v pc' : BitVec 64} (hv : s.readReg w rm = v)
    (hv32 : w = .W32 → (v.truncate 32).zeroExtend 64 = v := by intro h; cases h)
    (hpc : s.pc + 4#64 = pc') :
    P.evalInst (.logicalShift w .ORR rd .xzr rm .LSL 0) s = (s.writeReg64 rd v).setPC pc' := by
  dsimp only [Program.evalInst, execInstWithSvc, execLogicalShift]
  rw [hv]
  cases w
  · have h32 := hv32 rfl
    have hshift : shiftVal .W32 v .LSL 0 = (v.truncate 32).zeroExtend 64 := by
      simp [shiftVal, shift32]
    have hxzr : s.readReg .W32 .xzr = 0#64 := rfl
    rw [hshift, h32, hxzr]
    simp only [evalLogical, BitVec.zero_or, State.writeReg, h32]
    exact advancePC_eq_setPC (by simpa [State.writeReg64] using hpc)
  · have hshift : shiftVal .W64 v .LSL 0 = v := by simp [shiftVal, shift64]
    have hxzr : s.readReg .W64 .xzr = 0#64 := rfl
    rw [hshift, hxzr]
    simp only [evalLogical, BitVec.zero_or, State.writeReg]
    exact advancePC_eq_setPC (by simpa [State.writeReg64] using hpc)

private theorem evalInst_addImm64_eq {P : Program} {s : State} {rd rn : Reg} {imm12 : BitVec 12}
    {v pc' : BitVec 64} (hv : s.readReg64 rn + imm12.zeroExtend 64 = v) (hpc : s.pc + 4#64 = pc') :
    P.evalInst (.addSubImm .W64 .ADD rd rn imm12 false) s = (s.writeReg64 rd v).setPC pc' := by
  dsimp only [Program.evalInst, execInstWithSvc, execAddSubImm]
  have hr : s.readReg .W64 rn = s.readReg64 rn := rfl
  have hadd : evalAddSub .W64 .ADD (s.readReg64 rn) (imm12.zeroExtend 64) none = (v, none) := by
    simp only [evalAddSub, AddWithCarry64, Bool.false_eq_true, ↓reduceIte]
    refine Prod.ext ?_ rfl
    rw [← hv]
    bv_omega
  rw [hr]
  simp only [Bool.false_eq_true, ↓reduceIte, hadd, State.writeReg]
  exact advancePC_eq_setPC (by simpa [State.writeReg64] using hpc)

private theorem evalInst_svc_standard {P : Program} {s : State}
    (hsvc : P.svc = Syscall.standard) :
    P.evalInst (.system false 0#16) s = Syscall.standard s := by
  simp only [Program.evalInst, execInstWithSvc, hsvc, Bool.false_eq_true, ↓reduceIte,
    beq_self_eq_true]
  exact evalSvc_standard s

private theorem syscalls_standard_rt_sigprocmask (s : State)
    (hx8 : s.readReg64 .x8 = 135#64) :
    Syscall.standard s = execRtSigprocmask s := by
  unfold Syscall.standard Syscall.dispatch
  rw [hx8]
  rfl

private theorem syscalls_standard_tkill (s : State)
    (hx8 : s.readReg64 .x8 = 130#64) :
    Syscall.standard s = execTkill s := by
  unfold Syscall.standard Syscall.dispatch
  rw [hx8]
  rfl

/-! ## 3. `musl` `abort` Code Bundle & Termination Proof (`musl_abort_to_sigabrt`) -/

/-- Position-independent fast path of `musl` `__syscall_ret` (`0x476c3c..0x476c5c`, 9 words). -/
@[expose] def syscallRetFastWords : List (BitVec 32) :=
  [ 0xa9be7bfd#32, 0xb140041f#32, 0x910003fd#32, 0xf9000bf3#32, 0xaa0003f3#32,
    0x54000088#32, 0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32 ]

/-- Position-independent `musl` `__restore_sigs` (`0x479168..0x47917c`, 6 words). -/
@[expose] def restoreSigsWords : List (BitVec 32) :=
  [ 0xaa0003e1#32, 0xd28010e8#32, 0xd2800040#32, 0xd2800002#32, 0xd2800103#32,
    0xd4000001#32 ]

/-- Layout-parametric code chunks for the 5 `musl` functions executed by `abort` (`abort`, `raise`,
    `__block_app_sigs`, `__syscall_ret` fast path, `__restore_sigs`). -/
@[expose] def f3AbortChunks (addrs : F3PanicAddrs) : List CodeChunk :=
  [ .words addrs.abortAddr [0xa9bc7bfd#32, 0x528000c0#32, 0x910003fd#32],
    .instrs addrs.abortAddr 0xc [.bl (addrs.raiseAddr - (addrs.abortAddr + 0xc#64))],
    .words addrs.raiseAddr
      [0xa9b67bfd#32, 0x910003fd#32, 0xa90153f3#32, 0x2a0003f4#32, 0x910083f3#32, 0xaa1303e0#32],
    .instrs addrs.raiseAddr 0x18 [.bl (addrs.blockAppSigsAddr - (addrs.raiseAddr + 0x18#64))],
    .words (addrs.raiseAddr + 0x1c#64)
      [0x93407e81#32, 0xd2801048#32, 0xd53bd040#32, 0xb8958000#32, 0xd4000001#32],
    .instrs addrs.raiseAddr 0x30 [.bl (addrs.syscallRetAddr - (addrs.raiseAddr + 0x30#64))],
    .words (addrs.raiseAddr + 0x34#64) [0xaa0003f4#32, 0xaa1303e0#32],
    .instrs addrs.raiseAddr 0x3c [.bl (addrs.restoreSigsAddr - (addrs.raiseAddr + 0x3c#64))],
    .words addrs.blockAppSigsAddr [0xaa0003e2#32],
    .instrs addrs.blockAppSigsAddr 0x4
      [.adr true .x1 (adrpOff (addrs.blockAppSigsAddr + 4#64) addrs.appMaskAddr)],
    .words (addrs.blockAppSigsAddr + 0x8#64) [0xd28010e8#32],
    .instrs addrs.blockAppSigsAddr 0xc
      [.addSubImm .W64 .ADD .x1 .x1 (addrs.appMaskAddr.truncate 12) false],
    .words (addrs.blockAppSigsAddr + 0x10#64)
      [0xd2800000#32, 0xd2800103#32, 0xd4000001#32, 0xd65f03c0#32],
    .words addrs.syscallRetAddr syscallRetFastWords,
    .words addrs.restoreSigsAddr restoreSigsWords ]

/-- Layout-parametric code chunks for the two abort-only `rdl_shim.S` panic handlers. -/
@[expose] def f3PanicShimChunks (addrs : F3PanicAddrs) : List CodeChunk :=
  [ .instrs0 addrs.rustBeginUnwindAddr [.b (addrs.abortAddr - addrs.rustBeginUnwindAddr)],
    .instrs0 addrs.rustAllocErrorHandlerAddr
      [.b (addrs.abortAddr - addrs.rustAllocErrorHandlerAddr)] ]

private theorem fetch_word_at {P : Program} {base : BitVec 64} {ws : List (BitVec 32)}
    (hw : P.hasWords base ws) (i : Nat) {w : BitVec 32} {inst : Instr}
    (hget : ws[i]? = some w := by rfl) (hdec : decode w = some inst := by rfl) :
    P.fetch (base + BitVec.ofNat 64 (4 * i)) = some inst :=
  Program.fetch_of_hasWords_getElem_decode i w hw rfl hget hdec

private theorem fetch_instr_at0 {P : Program} {base : BitVec 64} {inst : Instr}
    (hi : hasInstrs P base [inst]) : P.fetch base = some inst := by
  simpa using hi 0 (Nat.zero_lt_succ 0)

private theorem adrp_add_lo12 (pc tgt : BitVec 64) :
    (pc &&& 0xfffffffffffff000#64) + adrpOff pc tgt + (tgt.truncate 12).zeroExtend 64 = tgt := by
  unfold adrpOff
  bv_bits

private def syscallRetZeroPState : PState :=
  (AddWithCarry64 0#64 0x1000#64 false).2

private theorem regFile_write_ext {r1 r2 : RegFile} (h : ∀ i, r1.regs i = r2.regs i) : r1 = r2 := by
  cases r1; cases r2; congr 1; funext i; exact h i

private theorem blockAppSigs_steps {P : Program} {addrs : F3PanicAddrs} {s : State}
    (hsvc : P.svc = Syscall.standard)
    (hw0 : P.hasWords addrs.blockAppSigsAddr [0xaa0003e2#32])
    (hi1 : hasInstrs P (addrs.blockAppSigsAddr + 4#64)
      [.adr true .x1 (adrpOff (addrs.blockAppSigsAddr + 4#64) addrs.appMaskAddr)])
    (hw2 : P.hasWords (addrs.blockAppSigsAddr + 8#64) [0xd28010e8#32])
    (hi3 : hasInstrs P (addrs.blockAppSigsAddr + 0xc#64)
      [.addSubImm .W64 .ADD .x1 .x1 (addrs.appMaskAddr.truncate 12) false])
    (hw4 : P.hasWords (addrs.blockAppSigsAddr + 0x10#64)
      [0xd2800000#32, 0xd2800103#32, 0xd4000001#32, 0xd65f03c0#32])
    (hCL : P.CodeLoaded s.mem)
    (hpc : s.pc = addrs.blockAppSigsAddr)
    (hrun : s.status = .Running)
    (hmask : s.sigMask = 0#64)
    (hpend : s.sigPending = 0#64)
    (happNe : addrs.appMaskAddr ≠ 0#64)
    (happNW : addrs.appMaskAddr.toNat + 8 ≤ 2 ^ 64)
    (happCR : s.mem.canRead addrs.appMaskAddr 8 = true)
    (happBl : (s.mem.read64 addrs.appMaskAddr &&& SIGABRT_MASK) ≠ 0#64)
    (holdNe : s.readReg64 .x0 ≠ 0#64)
    (holdNW : (s.readReg64 .x0).toNat + 8 ≤ 2 ^ 64)
    (holdCW : s.mem.canWrite (s.readReg64 .x0) 8 = true) :
    let oldset := s.readReg64 .x0
    let newMask := s.mem.read64 addrs.appMaskAddr &&& ~~~SIG_UNBLOCKABLE_MASK
    let m' := s.mem.write64 oldset 0#64
    let sf := ((((((((s.writeReg64 .x2 oldset).writeReg64 .x1 addrs.appMaskAddr).writeReg64 .x8 135#64).writeReg64 .x0 0#64).writeReg64 .x3 8#64).setSigMask newMask).setMem m').setPC (s.readReg64 .lr))
    Steps P s sf := by
  have hf0 : P.fetch addrs.blockAppSigsAddr = some (.logicalShift .W64 .ORR .x2 .xzr .x0 .LSL 0) := by
    simpa using fetch_word_at hw0 0
  have hf1 : P.fetch (addrs.blockAppSigsAddr + 4#64) =
      some (.adr true .x1 (adrpOff (addrs.blockAppSigsAddr + 4#64) addrs.appMaskAddr)) :=
    fetch_instr_at0 hi1
  have hf2 : P.fetch (addrs.blockAppSigsAddr + 8#64) = some (.moveWide .W64 .MOVZ .x8 0x87#16 0) := by
    simpa using fetch_word_at hw2 0
  have hf3 : P.fetch (addrs.blockAppSigsAddr + 0xc#64) =
      some (.addSubImm .W64 .ADD .x1 .x1 (addrs.appMaskAddr.truncate 12) false) :=
    fetch_instr_at0 hi3
  have hf4 : P.fetch (addrs.blockAppSigsAddr + 0x10#64) = some (.moveWide .W64 .MOVZ .x0 0#16 0) := by
    simpa using fetch_word_at hw4 0
  have hf5 : P.fetch (addrs.blockAppSigsAddr + 0x14#64) = some (.moveWide .W64 .MOVZ .x3 8#16 0) := by
    have := fetch_word_at hw4 1
    rwa [show addrs.blockAppSigsAddr + 0x10#64 + 4#64 = addrs.blockAppSigsAddr + 0x14#64 by bv_omega] at this
  have hf6 : P.fetch (addrs.blockAppSigsAddr + 0x18#64) = some (.system false 0#16) := by
    have := fetch_word_at hw4 2
    rwa [show addrs.blockAppSigsAddr + 0x10#64 + 8#64 = addrs.blockAppSigsAddr + 0x18#64 by bv_omega] at this
  have hf7 : P.fetch (addrs.blockAppSigsAddr + 0x1c#64) = some (.ret .x30) := by
    have := fetch_word_at hw4 3
    rwa [show addrs.blockAppSigsAddr + 0x10#64 + 0xc#64 = addrs.blockAppSigsAddr + 0x1c#64 by bv_omega] at this
  let oldset := s.readReg64 .x0
  let pageVal := ((addrs.blockAppSigsAddr + 4#64) &&& 0xfffffffffffff000#64) +
    adrpOff (addrs.blockAppSigsAddr + 4#64) addrs.appMaskAddr
  let s1 := (s.writeReg64 .x2 oldset).setPC (addrs.blockAppSigsAddr + 4#64)
  let s2 := (s1.writeReg64 .x1 pageVal).setPC (addrs.blockAppSigsAddr + 8#64)
  let s3 := (s2.writeReg64 .x8 135#64).setPC (addrs.blockAppSigsAddr + 0xc#64)
  let s4 := (s3.writeReg64 .x1 addrs.appMaskAddr).setPC (addrs.blockAppSigsAddr + 0x10#64)
  let s5 := (s4.writeReg64 .x0 0#64).setPC (addrs.blockAppSigsAddr + 0x14#64)
  let s6 := (s5.writeReg64 .x3 8#64).setPC (addrs.blockAppSigsAddr + 0x18#64)
  let newMask := s.mem.read64 addrs.appMaskAddr &&& ~~~SIG_UNBLOCKABLE_MASK
  let m' := s.mem.write64 oldset 0#64
  let s7 := ((s6.setSigMask newMask).setMem m').setPC (addrs.blockAppSigsAddr + 0x1c#64)
  have hs0 : P.evalInst (.logicalShift .W64 .ORR .x2 .xzr .x0 .LSL 0) s = s1 :=
    evalInst_movReg_eq rfl (by intro h; cases h) (by rw [hpc])
  have hs1 : P.evalInst (.adr true .x1 (adrpOff (addrs.blockAppSigsAddr + 4#64) addrs.appMaskAddr)) s1 = s2 := by
    have hpc1 : s1.pc = addrs.blockAppSigsAddr + 4#64 := rfl
    dsimp only [s2, Program.evalInst, execInstWithSvc]
    rw [hpc1]
    exact advancePC_eq_setPC (by change addrs.blockAppSigsAddr + 4#64 + 4#64 = _; bv_omega)
  have hs2 : P.evalInst (.moveWide .W64 .MOVZ .x8 0x87#16 0) s2 = s3 :=
    evalInst_movz_eq rfl (by change addrs.blockAppSigsAddr + 8#64 + 4#64 = _; bv_omega)
  have hs3 : P.evalInst (.addSubImm .W64 .ADD .x1 .x1 (addrs.appMaskAddr.truncate 12) false) s3 = s4 :=
    evalInst_addImm64_eq
      (by
        have hr1 : s3.readReg64 .x1 = pageVal := by
          simp [s3, s2, State.readReg64, State.writeReg64, State.setPC]
        rw [hr1]
        exact adrp_add_lo12 (addrs.blockAppSigsAddr + 4#64) addrs.appMaskAddr)
      (by change addrs.blockAppSigsAddr + 0xc#64 + 4#64 = _; bv_omega)
  have hs4 : P.evalInst (.moveWide .W64 .MOVZ .x0 0#16 0) s4 = s5 :=
    evalInst_movz_eq rfl (by change addrs.blockAppSigsAddr + 0x10#64 + 4#64 = _; bv_omega)
  have hs5 : P.evalInst (.moveWide .W64 .MOVZ .x3 8#16 0) s5 = s6 :=
    evalInst_movz_eq rfl (by change addrs.blockAppSigsAddr + 0x14#64 + 4#64 = _; bv_omega)
  have hs6_x8 : s6.readReg64 .x8 = 135#64 := by
    simp [s6, s5, s4, s3, State.readReg64, State.writeReg64, State.setPC]
  have hs6_x0 : s6.readReg32 .x0 = 0#32 := by
    simp [s6, s5, State.readReg32, State.readReg64, State.writeReg64, State.setPC]
  have hs6_x1 : s6.readReg64 .x1 = addrs.appMaskAddr := by
    simp [s6, s5, s4, State.readReg64, State.writeReg64, State.setPC]
  have hs6_x2 : s6.readReg64 .x2 = oldset := by
    simp [s6, s5, s4, s3, s2, s1, State.readReg64, State.writeReg64, State.setPC]
  have hs6_x3 : s6.readReg64 .x3 = 8#64 := by
    simp [s6, State.readReg64, State.writeReg64, State.setPC]
  have hs6_mem : s6.mem = s.mem := rfl
  have hs6_mask : s6.sigMask = 0#64 := hmask
  have hs6_pend : s6.sigPending = 0#64 := hpend
  have happAllR : s.mem.allPerm (·.r) addrs.appMaskAddr 8 = true := by
    unfold Memory.canRead at happCR; simp only [Bool.and_eq_true] at happCR; exact happCR.1
  have hs6_svc : P.evalInst (.system false 0#16) s6 = s7 := by
    rw [evalInst_svc_standard hsvc, syscalls_standard_rt_sigprocmask _ hs6_x8]
    unfold execRtSigprocmask
    dsimp only []
    rw [hs6_x0, hs6_x1, hs6_x2, hs6_x3, hs6_mem, hs6_mask]
    have hne1 : (addrs.appMaskAddr != 0#64) = true := bne_iff_ne.mpr happNe
    have heq1 : (addrs.appMaskAddr == 0#64) = false := beq_false_of_ne happNe
    have heq2 : (oldset == 0#64) = false := beq_false_of_ne holdNe
    have hnw1 : decide (addrs.appMaskAddr.toNat + 8 ≤ 2 ^ 64) = true := decide_eq_true happNW
    have hnw2 : decide (oldset.toNat + 8 ≤ 2 ^ 64) = true := decide_eq_true holdNW
    have hwb : s.mem.writeBytes oldset (leBytes64 0#64) = m' :=
      writeBytes_leBytes64_eq_write64 s.mem oldset 0#64
    have hnotZero : (0#32 != 0#32) = false := rfl
    have hne8 : (8#64 != 8#64) = false := rfl
    have holdCW' : s.mem.canWrite oldset 8 = true := holdCW
    have hs1_mem : (s6.setSigMask (s.mem.read64 addrs.appMaskAddr &&& ~~~SIG_UNBLOCKABLE_MASK)).mem = s.mem := rfl
    have hst_eq : ((s6.setSigMask newMask).setMem m').writeReg64 .x0 0#64 = (s6.setSigMask newMask).setMem m' := by
      have hreg_eq : (((s6.setSigMask newMask).setMem m').writeReg64 .x0 0#64).regs =
          ((s6.setSigMask newMask).setMem m').regs := by
        apply regFile_write_ext
        intro r
        by_cases h0 : r = 0#5
        · subst h0
          simp [s6, s5, State.writeReg64, State.setSigMask, State.setMem, State.setPC, RegFile.write]
        · simp [State.writeReg64, State.setSigMask, State.setMem, RegFile.write, h0]
      generalize ht : (s6.setSigMask newMask).setMem m' = t at hreg_eq ⊢
      cases t
      dsimp only [State.writeReg64] at hreg_eq ⊢
      rw [show (0#5 == 31#5) = false from rfl] at hreg_eq ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hreg_eq ⊢
      congr 1
    simp only [hne8, hnotZero, Bool.false_eq_true, Bool.false_and, ↓reduceIte, hne1, hnw1,
      happAllR, happCR, Bool.not_true, Bool.and_false, heq1, beq_self_eq_true, heq2, hnw2,
      BitVec.zero_or, hs1_mem, holdCW', Bool.or_self, hwb]
    change (let s2 := (((s6.setSigMask newMask).setMem m').writeReg64 Reg.x0 0#64).advancePC
      let deliverable := s2.sigPending &&& ~~~s2.sigMask
      if deliverable == 0#64 then s2
      else if deliverable == SIGABRT_MASK then
        let s3 := s2.setSigPending (s2.sigPending &&& ~~~SIGABRT_MASK)
        let disp := (s3.getSigAction LINUX_SIGABRT).handler
        if disp == SIG_DFL then s3.setStatus (.Signaled 6#7)
        else if disp == SIG_IGN then s3
        else s3.setStatus (.Exception "unmodeled signal handler delivery")
      else s2.setStatus (.Exception "unmodeled pending signal delivery")) = s7
    dsimp only []
    rw [hst_eq]
    have hpend' : ((s6.setSigMask newMask).setMem m').advancePC.sigPending = 0#64 := hs6_pend
    have hdeliv0 : (0#64 &&& ~~~((s6.setSigMask newMask).setMem m').advancePC.sigMask) = 0#64 := by bv_bits
    rw [hpend', hdeliv0]
    simp only [beq_self_eq_true, ↓reduceIte]
    exact advancePC_eq_setPC (by change addrs.blockAppSigsAddr + 0x18#64 + 4#64 = _; bv_omega)
  have hCL7 : P.CodeLoaded s7.mem :=
    codeLoaded_of_keepsFrozen hCL (Memory.keepsFrozen_write64 (m := s.mem) (a := oldset) holdCW 0#64)
  have hs7_lr : s7.readReg64 .x30 = s.readReg64 .lr := by
    simp [s7, s6, s5, s4, s3, s2, s1, State.readReg64, State.writeReg64, State.setSigMask,
      State.setMem, State.setPC]
  have hs7_ret : P.evalInst (.ret .x30) s7 =
      ((((((((s.writeReg64 .x2 oldset).writeReg64 .x1 addrs.appMaskAddr).writeReg64 .x8 135#64).writeReg64 .x0 0#64).writeReg64 .x3 8#64).setSigMask newMask).setMem m').setPC (s.readReg64 .lr)) := by
    simp only [Program.evalInst, execInstWithSvc, hs7_lr]
    cases s with | mk regs =>
    dsimp only [s7, s6, s5, s4, s3, s2, s1, State.setSigMask, State.setMem, State.setPC]
    congr 1
    apply regFile_write_ext
    intro r
    by_cases h3 : r = 3#5
    · subst h3; simp [State.writeReg64, RegFile.write]
    · by_cases h0 : r = 0#5
      · subst h0; simp [State.writeReg64, RegFile.write, h3]
      · by_cases h8 : r = 8#5
        · subst h8; simp [State.writeReg64, RegFile.write, h3, h0]
        · by_cases h1 : r = 1#5
          · subst h1; simp [State.writeReg64, RegFile.write, h3, h0, h8]
          · simp [State.writeReg64, RegFile.write, h3, h0, h8, h1]
  refine steps_exec hCL hrun (hpc.symm ▸ hf0) hs0 ?_
  refine steps_exec hCL hrun hf1 hs1 ?_
  refine steps_exec hCL hrun hf2 hs2 ?_
  refine steps_exec hCL hrun hf3 hs3 ?_
  refine steps_exec hCL hrun hf4 hs4 ?_
  refine steps_exec hCL hrun hf5 hs5 ?_
  refine steps_exec hCL hrun hf6 hs6_svc ?_
  refine steps_exec hCL7 hrun hf7 hs7_ret (Steps.refl _)

private theorem syscallRet_zero_steps {P : Program} {addrs : F3PanicAddrs} {s : State}
    (hw : P.hasWords addrs.syscallRetAddr syscallRetFastWords)
    (hCL : P.CodeLoaded s.mem)
    (hpc : s.pc = addrs.syscallRetAddr)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hstk : StackRW s.mem s.sp 0x20) :
    let m1 := (s.mem.write64 (s.sp - 0x20#64) (s.readReg64 .x29)).write64 (s.sp - 0x18#64) (s.readReg64 .x30)
    let m2 := m1.write64 (s.sp - 0x10#64) (s.readReg64 .x19)
    let sf := (((s.setMem m2).setPState syscallRetZeroPState).setPC (s.readReg64 .x30))
    Steps P s sf := by
  have hf0 : P.fetch addrs.syscallRetAddr = some (.stp .W64 .x29 .x30 (.PreIndex .sp (-0x20#64))) := by
    simpa using fetch_word_at hw 0
  have hf1 : P.fetch (addrs.syscallRetAddr + 4#64) = some (.addSubImm .W64 .ADDS .xzr .x0 1#12 true) :=
    fetch_word_at hw 1
  have hf2 : P.fetch (addrs.syscallRetAddr + 8#64) = some (.addSubImm .W64 .ADD .x29 .sp 0#12 false) :=
    fetch_word_at hw 2
  have hf3 : P.fetch (addrs.syscallRetAddr + 0xc#64) = some (.str .X64 .x19 (.Offset .sp 0x10#64)) :=
    fetch_word_at hw 3
  have hf4 : P.fetch (addrs.syscallRetAddr + 0x10#64) = some (.logicalShift .W64 .ORR .x19 .xzr .x0 .LSL 0) :=
    fetch_word_at hw 4
  have hf5 : P.fetch (addrs.syscallRetAddr + 0x14#64) = some (.bCond .HI 0x10#64) :=
    fetch_word_at hw 5
  have hf6 : P.fetch (addrs.syscallRetAddr + 0x18#64) = some (.ldr .W64 .X64 false .x19 (.Offset .sp 0x10#64)) :=
    fetch_word_at hw 6
  have hf7 : P.fetch (addrs.syscallRetAddr + 0x1c#64) = some (.ldp .W64 false .x29 .x30 (.PostIndex .sp 0x20#64)) :=
    fetch_word_at hw 7
  have hf8 : P.fetch (addrs.syscallRetAddr + 0x20#64) = some (.ret .x30) :=
    fetch_word_at hw 8
  have hcw0 : s.mem.canWrite (s.sp - 0x20#64) 8 = true := hstk.canWrite_sub (by omega) (by omega)
  have hcw1 : s.mem.canWrite (s.sp - 0x18#64) 8 = true := hstk.canWrite_sub (by omega) (by omega)
  have hcw2 : s.mem.canWrite (s.sp - 0x10#64) 8 = true := hstk.canWrite_sub (by omega) (by omega)
  have hsp_eq : s.sp + (-0x20#64) = s.sp - 0x20#64 := by bv_omega
  have hsp8 : s.sp - 0x20#64 + 8#64 = s.sp - 0x18#64 := by bv_omega
  have hsp16 : s.sp - 0x20#64 + 0x10#64 = s.sp - 0x10#64 := by bv_omega
  have hsp32 : s.sp - 0x20#64 + 0x20#64 = s.sp := by bv_omega
  have hsp_al1 : ((s.sp - 0x20#64) &&& 15#64 == 0#64) = true :=
    s.spAligned_sub 0x20#64 hsp
  let m1 := (s.mem.write64 (s.sp - 0x20#64) (s.readReg64 .x29)).write64 (s.sp - 0x18#64) (s.readReg64 .x30)
  let m2 := m1.write64 (s.sp - 0x10#64) (s.readReg64 .x19)
  let ps := syscallRetZeroPState
  let s1 := ((s.setMem m1).writeReg64 .sp (s.sp - 0x20#64)).setPC (addrs.syscallRetAddr + 4#64)
  let s2 := (s1.setPState ps).setPC (addrs.syscallRetAddr + 8#64)
  let s3 := (s2.writeReg64 .x29 (s.sp - 0x20#64)).setPC (addrs.syscallRetAddr + 0xc#64)
  let s4 := (s3.setMem m2).setPC (addrs.syscallRetAddr + 0x10#64)
  let s5 := (s4.writeReg64 .x19 0#64).setPC (addrs.syscallRetAddr + 0x14#64)
  let s6 := s5.setPC (addrs.syscallRetAddr + 0x18#64)
  let s7 := (s6.writeReg64 .x19 (s.readReg64 .x19)).setPC (addrs.syscallRetAddr + 0x1c#64)
  let s8 := (((s7.writeReg64 .sp s.sp).writeReg64 .x29 (s.readReg64 .x29)).writeReg64 .x30 (s.readReg64 .x30)).setPC (addrs.syscallRetAddr + 0x20#64)
  have hs0 : P.evalInst (.stp .W64 .x29 .x30 (.PreIndex .sp (-0x20#64))) s = s1 := by
    dsimp only [s1, m1, Program.evalInst, execInstWithSvc, execStp]
    have hchk : checkAddrSPAligned s (.PreIndex .sp (-0x20#64)) = true := hsp
    simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, State.readReg64,
      hsp_eq, hsp8, hcw0, hcw1, Bool.and_self, Memory.writeSized, MemWidth.bytes]
    exact advancePC_eq_setPC (by simp [State.writeReg64, State.setMem, hpc])
  have hs1 : P.evalInst (.addSubImm .W64 .ADDS .xzr .x0 1#12 true) s1 = s2 := by
    have hr0 : s1.readReg .W64 .x0 = 0#64 := by
      simpa [s1, State.readReg, State.readReg64, State.writeReg64, State.setPC, State.setMem] using hx0
    have hev_add : evalAddSub .W64 .ADDS 0#64 (((1#12 : BitVec 12).zeroExtend 64) <<< 12) none =
        ((AddWithCarry64 0#64 0x1000#64 false).1, some syscallRetZeroPState) := by
      simp [syscallRetZeroPState, addsPState64]
    dsimp only [s2, ps, Program.evalInst, execInstWithSvc, execAddSubImm]
    rw [hr0]
    simp only [↓reduceIte, hev_add, State.writeReg, State.writeReg64]
    exact advancePC_eq_setPC (by change addrs.syscallRetAddr + 4#64 + 4#64 = _; bv_omega)
  have hs2 : P.evalInst (.addSubImm .W64 .ADD .x29 .sp 0#12 false) s2 = s3 :=
    evalInst_addImm64_eq (by change s.sp - 0x20#64 + 0#64 = _; bv_omega)
      (by change addrs.syscallRetAddr + 8#64 + 4#64 = _; bv_omega)
  have hcw2_m1 : m1.canWrite (s.sp - 0x10#64) 8 = true := by
    have hstk1 := hstk.of_perm_eq (m' := m1) (fun a => by simp [m1, Memory.write64])
    exact hstk1.canWrite_sub (off := 0x10) (by omega) (by omega)
  have hs3 : P.evalInst (.str .X64 .x19 (.Offset .sp 0x10#64)) s3 = s4 := by
    have hsp3 : s3.spAligned = true := hsp_al1
    have hsp3_eq : s3.readReg64 .sp = s.sp - 0x20#64 := rfl
    have hx19 : s3.readReg64 .x19 = s.readReg64 .x19 := by
      simp [s3, s2, s1, State.readReg64, State.writeReg64, State.setPC, State.setPState, State.setMem]
    have hmem3 : s3.mem = m1 := rfl
    dsimp only [s4, m2, Program.evalInst, execInstWithSvc, execStr]
    have hchk : checkAddrSPAligned s3 (.Offset .sp 0x10#64) = true := hsp3
    simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, hsp3_eq,
      hsp16, hmem3, hcw2_m1, hx19, Memory.writeSized, MemWidth.bytes]
    exact advancePC_eq_setPC (by change addrs.syscallRetAddr + 0xc#64 + 4#64 = _; bv_omega)
  have hs4 : P.evalInst (.logicalShift .W64 .ORR .x19 .xzr .x0 .LSL 0) s4 = s5 :=
    evalInst_movReg_eq (by simpa [s4, s3, s2, s1, State.readReg, State.readReg64, State.writeReg64,
      State.setPC, State.setPState, State.setMem] using hx0)
      (by intro h; cases h)
      (by change addrs.syscallRetAddr + 0x10#64 + 4#64 = _; bv_omega)
  have hs5 : P.evalInst (.bCond .HI 0x10#64) s5 = s6 := by
    have hp5 : s5.pstate = syscallRetZeroPState := rfl
    have hcond : ConditionHolds .HI s5.pstate = false := by
      rw [hp5]
      dsimp only [syscallRetZeroPState, ConditionHolds, AddWithCarry64]
      bv_bits
    dsimp only [s6, Program.evalInst, execInstWithSvc]
    rw [hcond]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact advancePC_eq_setPC (by change addrs.syscallRetAddr + 0x14#64 + 4#64 = _; bv_omega)
  have hstk1 := hstk.of_perm_eq (m' := m1) (fun a => by simp [m1, Memory.write64])
  have hcr_x19 : m2.canRead (s.sp - 0x10#64) 8 = true :=
    canRead_write64_self (hstk1.allPerm_r_sub (off := 0x10) (by omega) (by omega))
  have hrd_x19 : m2.read64 (s.sp - 0x10#64) = s.readReg64 .x19 :=
    read64_write64_self m1 (s.sp - 0x10#64) (s.readReg64 .x19)
  have hcr_x29 : m2.canRead (s.sp - 0x20#64) 8 = true := by
    have h0 := canRead_write64_self (v := s.readReg64 .x29) (hstk.allPerm_r_sub (off := 0x20) (by omega) (by omega))
    exact Memory.canRead_write64_of_canRead _ _ (Memory.canRead_write64_of_canRead _ _ h0)
  have hcr_x30 : m2.canRead (s.sp - 0x18#64) 8 = true := by
    have hstk0 := hstk.of_perm_eq (m' := s.mem.write64 (s.sp - 0x20#64) (s.readReg64 .x29))
      (fun a => by simp [Memory.write64])
    have h1 := canRead_write64_self (v := s.readReg64 .x30) (hstk0.allPerm_r_sub (off := 0x18) (by omega) (by omega))
    exact Memory.canRead_write64_of_canRead _ _ h1
  have hrd_x29 : m2.read64 (s.sp - 0x20#64) = s.readReg64 .x29 := by
    have hd1 : DisjointRegions (s.sp - 0x10#64) 8 (s.sp - 0x20#64) 8 := by
      unfold DisjointRegions; bv_omega
    have hd2 : DisjointRegions (s.sp - 0x18#64) 8 (s.sp - 0x20#64) 8 := by
      unfold DisjointRegions; bv_omega
    rw [read64_write64_disjoint hd1, read64_write64_disjoint hd2, read64_write64_self]
  have hrd_x30 : m2.read64 (s.sp - 0x18#64) = s.readReg64 .x30 := by
    have hd1 : DisjointRegions (s.sp - 0x10#64) 8 (s.sp - 0x18#64) 8 := by
      unfold DisjointRegions; bv_omega
    rw [read64_write64_disjoint hd1, read64_write64_self]
  have hsp6 : s6.spAligned = true := hsp_al1
  have hs6 : P.evalInst (.ldr .W64 .X64 false .x19 (.Offset .sp 0x10#64)) s6 = s7 := by
    have hsp6_eq : s6.readReg64 .sp = s.sp - 0x20#64 := rfl
    have hmem6 : s6.mem = m2 := rfl
    dsimp only [s7, Program.evalInst, execInstWithSvc, execLdr]
    have hchk : checkAddrSPAligned s6 (.Offset .sp 0x10#64) = true := hsp6
    simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, hsp6_eq,
      hsp16, hmem6, hcr_x19, hrd_x19, Memory.readSized, MemWidth.bytes, State.writeReg]
    exact advancePC_eq_setPC (by change addrs.syscallRetAddr + 0x18#64 + 4#64 = _; bv_omega)
  have hsp7 : s7.spAligned = true := hsp_al1
  have hs7 : P.evalInst (.ldp .W64 false .x29 .x30 (.PostIndex .sp 0x20#64)) s7 = s8 := by
    have hsp7_eq : s7.readReg64 .sp = s.sp - 0x20#64 := rfl
    have hmem7 : s7.mem = m2 := rfl
    dsimp only [s8, Program.evalInst, execInstWithSvc, execLdp]
    have hchk : checkAddrSPAligned s7 (.PostIndex .sp 0x20#64) = true := hsp7
    simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, hsp7_eq,
      hsp8, hsp32, hmem7, hcr_x29, hcr_x30, Bool.and_self, hrd_x29, hrd_x30,
      Memory.readSized, MemWidth.bytes, State.writeReg]
    exact advancePC_eq_setPC (by change addrs.syscallRetAddr + 0x1c#64 + 4#64 = _; bv_omega)
  have hs8 : P.evalInst (.ret .x30) s8 = (((s.setMem m2).setPState ps).setPC (s.readReg64 .x30)) := by
    have hlr : s8.readReg64 .x30 = s.readReg64 .x30 := by
      simp [s8, State.readReg64, State.writeReg64, State.setPC]
    simp only [Program.evalInst, execInstWithSvc, hlr]
    cases s with | mk regs =>
    dsimp only [s8, s7, s6, s5, s4, s3, s2, s1, State.setPC, State.setPState, State.setMem]
    congr 1
    apply regFile_write_ext
    intro r
    by_cases h30 : r = 30#5
    · subst h30; simp [State.writeReg64, State.readReg64, RegFile.write, RegFile.read]
    · by_cases h29 : r = 29#5
      · subst h29; simp [State.writeReg64, State.readReg64, RegFile.write, RegFile.read, h30]
      · by_cases h19 : r = 19#5
        · subst h19; simp [State.writeReg64, State.readReg64, RegFile.write, RegFile.read, h30, h29]
        · simp [State.writeReg64, RegFile.write, h30, h29, h19]
  have hCL1 : P.CodeLoaded m1 :=
    codeLoaded_of_keepsFrozen (codeLoaded_of_keepsFrozen hCL (Memory.keepsFrozen_write64 hcw0 _))
      (Memory.keepsFrozen_write64 (by
        have hstk0 := hstk.of_perm_eq (m' := s.mem.write64 (s.sp - 0x20#64) (s.readReg64 .x29))
          (fun a => by simp [Memory.write64])
        exact hstk0.canWrite_sub (off := 0x18) (by omega) (by omega)) _)
  have hCL2 : P.CodeLoaded m2 := codeLoaded_of_keepsFrozen hCL1 (Memory.keepsFrozen_write64 hcw2_m1 _)
  refine steps_exec hCL hrun (hpc.symm ▸ hf0) hs0 ?_
  refine steps_exec hCL1 hrun hf1 hs1 ?_
  refine steps_exec hCL1 hrun hf2 hs2 ?_
  refine steps_exec hCL1 hrun hf3 hs3 ?_
  refine steps_exec hCL2 hrun hf4 hs4 ?_
  refine steps_exec hCL2 hrun hf5 hs5 ?_
  refine steps_exec hCL2 hrun hf6 hs6 ?_
  refine steps_exec hCL2 hrun hf7 hs7 ?_
  refine steps_exec hCL2 hrun hf8 hs8 (Steps.refl _)

private theorem restoreSigs_sigabrt_steps {P : Program} {addrs : F3PanicAddrs} {s : State}
    (hsvc : P.svc = Syscall.standard)
    (hw : P.hasWords addrs.restoreSigsAddr restoreSigsWords)
    (hCL : P.CodeLoaded s.mem)
    (hpc : s.pc = addrs.restoreSigsAddr)
    (hrun : s.status = .Running)
    (hpend : s.sigPending = SIGABRT_MASK)
    (hdfl : (s.getSigAction LINUX_SIGABRT).handler = SIG_DFL)
    (hsetNe : s.readReg64 .x0 ≠ 0#64)
    (hsetNW : (s.readReg64 .x0).toNat + 8 ≤ 2 ^ 64)
    (hsetCR : s.mem.canRead (s.readReg64 .x0) 8 = true)
    (hsetVal : s.mem.read64 (s.readReg64 .x0) = 0#64) :
    ∃ sf, Steps P s sf ∧ sf.status = .Signaled 6#7 ∧ sf.fs = s.fs ∧ sf.trace = s.trace := by
  have hf0 : P.fetch addrs.restoreSigsAddr = some (.logicalShift .W64 .ORR .x1 .xzr .x0 .LSL 0) := by
    simpa using fetch_word_at hw 0
  have hf1 : P.fetch (addrs.restoreSigsAddr + 4#64) = some (.moveWide .W64 .MOVZ .x8 0x87#16 0) :=
    fetch_word_at hw 1
  have hf2 : P.fetch (addrs.restoreSigsAddr + 8#64) = some (.moveWide .W64 .MOVZ .x0 2#16 0) :=
    fetch_word_at hw 2
  have hf3 : P.fetch (addrs.restoreSigsAddr + 0xc#64) = some (.moveWide .W64 .MOVZ .x2 0#16 0) :=
    fetch_word_at hw 3
  have hf4 : P.fetch (addrs.restoreSigsAddr + 0x10#64) = some (.moveWide .W64 .MOVZ .x3 8#16 0) :=
    fetch_word_at hw 4
  have hf5 : P.fetch (addrs.restoreSigsAddr + 0x14#64) = some (.system false 0#16) :=
    fetch_word_at hw 5
  let setPtr := s.readReg64 .x0
  let s1 := (s.writeReg64 .x1 setPtr).setPC (addrs.restoreSigsAddr + 4#64)
  let s2 := (s1.writeReg64 .x8 135#64).setPC (addrs.restoreSigsAddr + 8#64)
  let s3 := (s2.writeReg64 .x0 2#64).setPC (addrs.restoreSigsAddr + 0xc#64)
  let s4 := (s3.writeReg64 .x2 0#64).setPC (addrs.restoreSigsAddr + 0x10#64)
  let s5 := (s4.writeReg64 .x3 8#64).setPC (addrs.restoreSigsAddr + 0x14#64)
  have hs0 : P.evalInst (.logicalShift .W64 .ORR .x1 .xzr .x0 .LSL 0) s = s1 :=
    evalInst_movReg_eq rfl (by intro h; cases h) (by rw [hpc])
  have hs1 : P.evalInst (.moveWide .W64 .MOVZ .x8 0x87#16 0) s1 = s2 :=
    evalInst_movz_eq rfl (by change addrs.restoreSigsAddr + 4#64 + 4#64 = _; bv_omega)
  have hs2 : P.evalInst (.moveWide .W64 .MOVZ .x0 2#16 0) s2 = s3 :=
    evalInst_movz_eq rfl (by change addrs.restoreSigsAddr + 8#64 + 4#64 = _; bv_omega)
  have hs3 : P.evalInst (.moveWide .W64 .MOVZ .x2 0#16 0) s3 = s4 :=
    evalInst_movz_eq rfl (by change addrs.restoreSigsAddr + 0xc#64 + 4#64 = _; bv_omega)
  have hs4 : P.evalInst (.moveWide .W64 .MOVZ .x3 8#16 0) s4 = s5 :=
    evalInst_movz_eq rfl (by change addrs.restoreSigsAddr + 0x10#64 + 4#64 = _; bv_omega)
  have hs5_x8 : s5.readReg64 .x8 = 135#64 := by
    simp [s5, s4, s3, s2, State.readReg64, State.writeReg64, State.setPC]
  have hs5_x0 : s5.readReg32 .x0 = 2#32 := by
    simp [s5, s4, s3, State.readReg32, State.readReg64, State.writeReg64, State.setPC]
  have hs5_x1 : s5.readReg64 .x1 = setPtr := by
    simp [s5, s4, s3, s2, s1, State.readReg64, State.writeReg64, State.setPC]
  have hs5_x2 : s5.readReg64 .x2 = 0#64 := by
    simp [s5, s4, State.readReg64, State.writeReg64, State.setPC]
  have hs5_x3 : s5.readReg64 .x3 = 8#64 := by
    simp [s5, State.readReg64, State.writeReg64, State.setPC]
  have hsetAllR : s.mem.allPerm (·.r) setPtr 8 = true := by
    unfold Memory.canRead at hsetCR; simp only [Bool.and_eq_true] at hsetCR; exact hsetCR.1
  let sf := ((((s5.setSigMask 0#64).writeReg64 .x0 0#64).advancePC).setSigPending 0#64).setStatus (.Signaled 6#7)
  have hs5_svc : P.evalInst (.system false 0#16) s5 = sf := by
    rw [evalInst_svc_standard hsvc, syscalls_standard_rt_sigprocmask _ hs5_x8]
    unfold execRtSigprocmask
    dsimp only []
    rw [hs5_x0, hs5_x1, hs5_x2, hs5_x3]
    have hmem5 : s5.mem = s.mem := rfl
    have hne : (setPtr != 0#64) = true := bne_iff_ne.mpr hsetNe
    have heq : (setPtr == 0#64) = false := beq_false_of_ne hsetNe
    have hnw : decide (setPtr.toNat + 8 ≤ 2 ^ 64) = true := decide_eq_true hsetNW
    have hzeroMask : (0#64 &&& ~~~SIG_UNBLOCKABLE_MASK) = 0#64 := by decide
    have hdeliv : (SIGABRT_MASK &&& ~~~0#64) = SIGABRT_MASK := by decide
    have hclr : (SIGABRT_MASK &&& ~~~SIGABRT_MASK) = 0#64 := by decide
    have h2chk :
        ((8#64 : BitVec 64) != 8#64) = false ∧
        ((2#32 : BitVec 32) != 2#32) = false ∧
        ((2#32 : BitVec 32) == 0#32) = false ∧
        ((2#32 : BitVec 32) == 1#32) = false := by decide
    rw [hmem5, hsetAllR, hsetCR, hsetVal]
    simp only [h2chk.1, h2chk.2.1, h2chk.2.2.1, h2chk.2.2.2, hne, hnw, heq, hzeroMask,
      beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.and_false]
    have hpend5 : (((s5.setSigMask 0#64).writeReg64 Reg.x0 0#64).advancePC).sigPending = SIGABRT_MASK := hpend
    have hmask5 : (((s5.setSigMask 0#64).writeReg64 Reg.x0 0#64).advancePC).sigMask = 0#64 := rfl
    have hdfl5 : (((((s5.setSigMask 0#64).writeReg64 Reg.x0 0#64).advancePC).setSigPending
        (SIGABRT_MASK &&& ~~~SIGABRT_MASK)).getSigAction LINUX_SIGABRT).handler = SIG_DFL := hdfl
    rw [hpend5, hmask5, hdeliv]
    have hne0 : (SIGABRT_MASK == 0#64) = false := by decide
    simp only [hne0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    rw [hdfl5, hclr]
    simp only [beq_self_eq_true, ↓reduceIte]
    rfl
  refine ⟨sf, ?_, rfl, rfl, rfl⟩
  refine steps_exec hCL hrun (hpc.symm ▸ hf0) hs0 ?_
  refine steps_exec hCL hrun hf1 hs1 ?_
  refine steps_exec hCL hrun hf2 hs2 ?_
  refine steps_exec hCL hrun hf3 hs3 ?_
  refine steps_exec hCL hrun hf4 hs4 ?_
  refine steps_exec hCL hrun hf5 hs5_svc (Steps.refl _)

/-- From `abortAddr` with `0x100` B stack, default `SIGABRT` disposition, clear signal
    mask/pending, TLS `tid = 1`, and frozen `app_mask` blocking `SIGABRT`, `abort` executes
    43 instructions (`abort` → `raise(6)` → `__block_app_sigs` → `tkill(1, 6)` →
    `__syscall_ret` → `__restore_sigs`) and terminates with `ExecStatus.Signaled 6#7`,
    preserving `fs` and `trace`. -/
theorem musl_abort_to_sigabrt {P : Program} {addrs : F3PanicAddrs} {s : State}
    (hsvc : P.svc = Syscall.standard)
    (hcode : CodeChunks P (f3AbortChunks addrs))
    (hpc : s.pc = addrs.abortAddr)
    (hpre : PanicAbortPre P addrs s) :
    ∃ sf, Steps P s sf ∧ sf.status = .Signaled 6#7 ∧ sf.fs = s.fs ∧ sf.trace = s.trace := by
  dsimp only [f3AbortChunks, CodeChunks, CodeChunk.holds] at hcode
  obtain ⟨hw_ab0, hi_ab3, hw_r0, hi_r6, hw_r7, hi_r12, hw_r13, hi_r15,
          hw_b0, hi_b1, hw_b2, hi_b3, hw_b4, hw_sr, hw_rs⟩ := hcode
  have hCL := hpre.codeLoaded
  have hrun := hpre.running
  have hsp := hpre.spAligned
  have hstk := hpre.stackRW
  have hsp_al40 : ((s.sp - 0x40#64) &&& 15#64 == 0#64) = true := s.spAligned_sub 0x40#64 hsp
  have hsp_ale0 : ((s.sp - 0xe0#64) &&& 15#64 == 0#64) = true := s.spAligned_sub 0xe0#64 hsp
  -- Step 1: abort (4 instructions) → raise
  have hfa0 : P.fetch addrs.abortAddr = some (.stp .W64 .x29 .x30 (.PreIndex .sp (-0x40#64))) := by
    simpa using fetch_word_at hw_ab0 0
  have hfa1 : P.fetch (addrs.abortAddr + 4#64) = some (.moveWide .W32 .MOVZ .x0 6#16 0) :=
    fetch_word_at hw_ab0 1
  have hfa2 : P.fetch (addrs.abortAddr + 8#64) = some (.addSubImm .W64 .ADD .x29 .sp 0#12 false) :=
    fetch_word_at hw_ab0 2
  have hfa3 : P.fetch (addrs.abortAddr + 0xc#64) = some (.bl (addrs.raiseAddr - (addrs.abortAddr + 0xc#64))) :=
    fetch_instr_at0 hi_ab3
  have hcw_a0 : s.mem.canWrite (s.sp - 0x40#64) 8 = true := hstk.canWrite_sub (off := 0x40) (by omega) (by omega)
  have hcw_a1 : s.mem.canWrite (s.sp - 0x38#64) 8 = true := hstk.canWrite_sub (off := 0x38) (by omega) (by omega)
  let m_a := (s.mem.write64 (s.sp - 0x40#64) (s.readReg64 .x29)).write64 (s.sp - 0x38#64) (s.readReg64 .x30)
  let sa1 := ((s.setMem m_a).writeReg64 .sp (s.sp - 0x40#64)).setPC (addrs.abortAddr + 4#64)
  let sa2 := (sa1.writeReg64 .x0 6#64).setPC (addrs.abortAddr + 8#64)
  let sa3 := (sa2.writeReg64 .x29 (s.sp - 0x40#64)).setPC (addrs.abortAddr + 0xc#64)
  let sa4 := (sa3.writeReg64 .lr (addrs.abortAddr + 0x10#64)).setPC addrs.raiseAddr
  have hsa0 : P.evalInst (.stp .W64 .x29 .x30 (.PreIndex .sp (-0x40#64))) s = sa1 := by
    dsimp only [sa1, m_a, Program.evalInst, execInstWithSvc, execStp]
    have hchk : checkAddrSPAligned s (.PreIndex .sp (-0x40#64)) = true := hsp
    simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, State.readReg64,
      show s.sp + (-0x40#64) = s.sp - 0x40#64 by bv_omega,
      show s.sp - 0x40#64 + 8#64 = s.sp - 0x38#64 by bv_omega,
      hcw_a0, hcw_a1, Bool.and_self, Memory.writeSized, MemWidth.bytes]
    exact advancePC_eq_setPC (by simp [State.writeReg64, State.setMem, hpc])
  have hsa1 : P.evalInst (.moveWide .W32 .MOVZ .x0 6#16 0) sa1 = sa2 :=
    evalInst_movz_eq rfl (by change addrs.abortAddr + 4#64 + 4#64 = _; bv_omega)
  have hsa2 : P.evalInst (.addSubImm .W64 .ADD .x29 .sp 0#12 false) sa2 = sa3 :=
    evalInst_addImm64_eq (by change s.sp - 0x40#64 + 0#64 = _; bv_omega)
      (by change addrs.abortAddr + 8#64 + 4#64 = _; bv_omega)
  have hsa3 : P.evalInst (.bl (addrs.raiseAddr - (addrs.abortAddr + 0xc#64))) sa3 = sa4 :=
    evalInst_bl_eq (by change addrs.abortAddr + 0xc#64 + 4#64 = _; bv_omega)
      (by change addrs.abortAddr + 0xc#64 + (addrs.raiseAddr - (addrs.abortAddr + 0xc#64)) = _; bv_omega)
  have hkf_a : s.mem.KeepsFrozen m_a :=
    (Memory.keepsFrozen_write64 hcw_a0 _).trans (Memory.keepsFrozen_write64 (by
      have hstk' := hstk.of_perm_eq (m' := s.mem.write64 (s.sp - 0x40#64) (s.readReg64 .x29))
        (fun a => by simp [Memory.write64])
      exact hstk'.canWrite_sub (off := 0x38) (by omega) (by omega)) _)
  have hCL_a : P.CodeLoaded m_a := codeLoaded_of_keepsFrozen hCL hkf_a
  have hstk_a : StackRW m_a s.sp 0x100 := hstk.of_perm_eq (fun a => by simp [m_a, Memory.write64])
  -- Step 2: raise part 1 (7 instructions) → __block_app_sigs
  have hfr0 : P.fetch addrs.raiseAddr = some (.stp .W64 .x29 .x30 (.PreIndex .sp (-0xa0#64))) := by
    simpa using fetch_word_at hw_r0 0
  have hfr1 : P.fetch (addrs.raiseAddr + 4#64) = some (.addSubImm .W64 .ADD .x29 .sp 0#12 false) :=
    fetch_word_at hw_r0 1
  have hfr2 : P.fetch (addrs.raiseAddr + 8#64) = some (.stp .W64 .x19 .x20 (.Offset .sp 0x10#64)) :=
    fetch_word_at hw_r0 2
  have hfr3 : P.fetch (addrs.raiseAddr + 0xc#64) = some (.logicalShift .W32 .ORR .x20 .xzr .x0 .LSL 0) :=
    fetch_word_at hw_r0 3
  have hfr4 : P.fetch (addrs.raiseAddr + 0x10#64) = some (.addSubImm .W64 .ADD .x19 .sp 0x20#12 false) :=
    fetch_word_at hw_r0 4
  have hfr5 : P.fetch (addrs.raiseAddr + 0x14#64) = some (.logicalShift .W64 .ORR .x0 .xzr .x19 .LSL 0) :=
    fetch_word_at hw_r0 5
  have hfr6 : P.fetch (addrs.raiseAddr + 0x18#64) = some (.bl (addrs.blockAppSigsAddr - (addrs.raiseAddr + 0x18#64))) :=
    fetch_instr_at0 hi_r6
  have hcw_r0 : m_a.canWrite (s.sp - 0xe0#64) 8 = true := hstk_a.canWrite_sub (by omega) (by omega)
  have hcw_r1 : m_a.canWrite (s.sp - 0xd8#64) 8 = true := hstk_a.canWrite_sub (by omega) (by omega)
  let m_r1 := (m_a.write64 (s.sp - 0xe0#64) (sa4.readReg64 .x29)).write64 (s.sp - 0xd8#64) (sa4.readReg64 .x30)
  have hstk_r1 : StackRW m_r1 s.sp 0x100 := hstk_a.of_perm_eq (fun a => by simp [m_r1, Memory.write64])
  have hcw_r2 : m_r1.canWrite (s.sp - 0xd0#64) 8 = true := hstk_r1.canWrite_sub (by omega) (by omega)
  have hcw_r3 : m_r1.canWrite (s.sp - 0xc8#64) 8 = true := hstk_r1.canWrite_sub (by omega) (by omega)
  let m_r2 := (m_r1.write64 (s.sp - 0xd0#64) (sa4.readReg64 .x19)).write64 (s.sp - 0xc8#64) (sa4.readReg64 .x20)
  let sr1 := ((sa4.setMem m_r1).writeReg64 .sp (s.sp - 0xe0#64)).setPC (addrs.raiseAddr + 4#64)
  let sr2 := (sr1.writeReg64 .x29 (s.sp - 0xe0#64)).setPC (addrs.raiseAddr + 8#64)
  let sr3 := (sr2.setMem m_r2).setPC (addrs.raiseAddr + 0xc#64)
  let sr4 := (sr3.writeReg64 .x20 6#64).setPC (addrs.raiseAddr + 0x10#64)
  let sr5 := (sr4.writeReg64 .x19 (s.sp - 0xc0#64)).setPC (addrs.raiseAddr + 0x14#64)
  let sr6 := (sr5.writeReg64 .x0 (s.sp - 0xc0#64)).setPC (addrs.raiseAddr + 0x18#64)
  let sr7 := (sr6.writeReg64 .lr (addrs.raiseAddr + 0x1c#64)).setPC addrs.blockAppSigsAddr
  have hsr0 : P.evalInst (.stp .W64 .x29 .x30 (.PreIndex .sp (-0xa0#64))) sa4 = sr1 := by
    have hspa : sa4.spAligned = true := hsp_al40
    have hsp4 : sa4.readReg64 .sp = s.sp - 0x40#64 := rfl
    have hmem4 : sa4.mem = m_a := rfl
    dsimp only [sr1, m_r1, Program.evalInst, execInstWithSvc, execStp]
    have hchk : checkAddrSPAligned sa4 (.PreIndex .sp (-0xa0#64)) = true := hspa
    simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, hsp4, hmem4,
      show s.sp - 0x40#64 + (-0xa0#64) = s.sp - 0xe0#64 by bv_omega,
      show s.sp - 0xe0#64 + 8#64 = s.sp - 0xd8#64 by bv_omega,
      hcw_r0, hcw_r1, Bool.and_self, Memory.writeSized, MemWidth.bytes]
    exact advancePC_eq_setPC rfl
  have hsr1 : P.evalInst (.addSubImm .W64 .ADD .x29 .sp 0#12 false) sr1 = sr2 :=
    evalInst_addImm64_eq (by change s.sp - 0xe0#64 + 0#64 = _; bv_omega)
      (by change addrs.raiseAddr + 4#64 + 4#64 = _; bv_omega)
  have hsr2 : P.evalInst (.stp .W64 .x19 .x20 (.Offset .sp 0x10#64)) sr2 = sr3 := by
    have hspr2 : sr2.spAligned = true := hsp_ale0
    have hsp2 : sr2.readReg64 .sp = s.sp - 0xe0#64 := rfl
    have hmem2 : sr2.mem = m_r1 := rfl
    have hx19 : sr2.readReg64 .x19 = sa4.readReg64 .x19 := by
      simp [sr2, sr1, State.readReg64, State.writeReg64, State.setPC, State.setMem]
    have hx20 : sr2.readReg64 .x20 = sa4.readReg64 .x20 := by
      simp [sr2, sr1, State.readReg64, State.writeReg64, State.setPC, State.setMem]
    dsimp only [sr3, m_r2, Program.evalInst, execInstWithSvc, execStp]
    have hchk : checkAddrSPAligned sr2 (.Offset .sp 0x10#64) = true := hspr2
    simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, hsp2, hmem2,
      show s.sp - 0xe0#64 + 0x10#64 = s.sp - 0xd0#64 by bv_omega,
      show s.sp - 0xd0#64 + 8#64 = s.sp - 0xc8#64 by bv_omega,
      hcw_r2, hcw_r3, Bool.and_self, hx19, hx20, Memory.writeSized, MemWidth.bytes]
    exact advancePC_eq_setPC (by change addrs.raiseAddr + 8#64 + 4#64 = _; bv_omega)
  have hsr3 : P.evalInst (.logicalShift .W32 .ORR .x20 .xzr .x0 .LSL 0) sr3 = sr4 :=
    evalInst_movReg_eq
      (by simp [sr3, sr2, sr1, sa4, sa3, sa2, State.readReg, State.readReg32, State.readReg64,
        State.writeReg64, State.setPC, State.setMem])
      (by intro _; rfl)
      (by change addrs.raiseAddr + 0xc#64 + 4#64 = _; bv_omega)
  have hsr4 : P.evalInst (.addSubImm .W64 .ADD .x19 .sp 0x20#12 false) sr4 = sr5 :=
    evalInst_addImm64_eq (by change s.sp - 0xe0#64 + 0x20#64 = s.sp - 0xc0#64; bv_omega)
      (by change addrs.raiseAddr + 0x10#64 + 4#64 = _; bv_omega)
  have hsr5 : P.evalInst (.logicalShift .W64 .ORR .x0 .xzr .x19 .LSL 0) sr5 = sr6 :=
    evalInst_movReg_eq
      (by simp [sr5, State.readReg, State.readReg64, State.writeReg64, State.setPC])
      (by intro h; cases h)
      (by change addrs.raiseAddr + 0x14#64 + 4#64 = _; bv_omega)
  have hsr6 : P.evalInst (.bl (addrs.blockAppSigsAddr - (addrs.raiseAddr + 0x18#64))) sr6 = sr7 :=
    evalInst_bl_eq (by change addrs.raiseAddr + 0x18#64 + 4#64 = _; bv_omega)
      (by change addrs.raiseAddr + 0x18#64 + (addrs.blockAppSigsAddr - (addrs.raiseAddr + 0x18#64)) = _; bv_omega)
  have hkf_r1 : m_a.KeepsFrozen m_r1 :=
    (Memory.keepsFrozen_write64 hcw_r0 _).trans (Memory.keepsFrozen_write64 (by
      have hstk' := hstk_a.of_perm_eq (m' := m_a.write64 (s.sp - 0xe0#64) (sa4.readReg64 .x29))
        (fun a => by simp [Memory.write64])
      exact hstk'.canWrite_sub (off := 0xd8) (by omega) (by omega)) _)
  have hkf_r2 : m_r1.KeepsFrozen m_r2 :=
    (Memory.keepsFrozen_write64 hcw_r2 _).trans (Memory.keepsFrozen_write64 (by
      have hstk' := hstk_r1.of_perm_eq (m' := m_r1.write64 (s.sp - 0xd0#64) (sa4.readReg64 .x19))
        (fun a => by simp [Memory.write64])
      exact hstk'.canWrite_sub (off := 0xc8) (by omega) (by omega)) _)
  have hkf_s_r2 : s.mem.KeepsFrozen m_r2 := hkf_a.trans (hkf_r1.trans hkf_r2)
  have hCL_r1 : P.CodeLoaded m_r1 := codeLoaded_of_keepsFrozen hCL_a hkf_r1
  have hCL_r2 : P.CodeLoaded m_r2 := codeLoaded_of_keepsFrozen hCL_r1 hkf_r2
  have hstk_r2 : StackRW m_r2 s.sp 0x100 := hstk_r1.of_perm_eq (fun a => by simp [m_r2, Memory.write64])
  -- Step 3: __block_app_sigs (8 instructions) → raise + 0x1c
  have hsr7_x0 : sr7.readReg64 .x0 = s.sp - 0xc0#64 := by
    simp [sr7, sr6, State.readReg64, State.writeReg64, State.setPC]
  have hsr7_lr : sr7.readReg64 .lr = addrs.raiseAddr + 0x1c#64 := by
    simp [sr7, State.readReg64, State.writeReg64, State.setPC]
  have hblk := blockAppSigs_steps (s := sr7) hsvc hw_b0 hi_b1 hw_b2 hi_b3 hw_b4 hCL_r2 rfl hrun
    hpre.sigMask hpre.sigPending hpre.appMaskNeZero hpre.appMaskNoWrap
    (canRead_of_keepsFrozen hkf_s_r2 hpre.appMaskFrozen hpre.appMaskCanRead)
    (by
      change m_r2.read64 addrs.appMaskAddr &&& SIGABRT_MASK ≠ 0#64
      rw [read64_of_keepsFrozen hkf_s_r2 hpre.appMaskFrozen]; exact hpre.appMaskBlocksAbrt)
    (hsr7_x0 ▸ hstk_r2.sub_ne_zero (by omega))
    (hsr7_x0 ▸ hstk_r2.sub_no_wrap (by omega) (by omega))
    (hsr7_x0 ▸ hstk_r2.canWrite_sub (by omega) (by omega))
  dsimp only [] at hblk
  rw [hsr7_x0, hsr7_lr] at hblk
  let newMask := m_r2.read64 addrs.appMaskAddr &&& ~~~SIG_UNBLOCKABLE_MASK
  let m_b := m_r2.write64 (s.sp - 0xc0#64) 0#64
  let sb := (((((((sr7.writeReg64 .x2 (s.sp - 0xc0#64)).writeReg64 .x1 addrs.appMaskAddr).writeReg64 .x8 135#64).writeReg64 .x0 0#64).writeReg64 .x3 8#64).setSigMask newMask).setMem m_b).setPC (addrs.raiseAddr + 0x1c#64)
  have hkf_r2_b : m_r2.KeepsFrozen m_b :=
    Memory.keepsFrozen_write64 (hstk_r2.canWrite_sub (off := 0xc0) (by omega) (by omega)) 0#64
  have hCL_b : P.CodeLoaded m_b := codeLoaded_of_keepsFrozen hCL_r2 hkf_r2_b
  have hstk_b : StackRW m_b s.sp 0x100 := hstk_r2.of_perm_eq (fun a => by simp [m_b, Memory.write64])
  -- Preserve tid at tpidrEl0 - 0xa8 across all stack writes so far
  have htid_cr_b : m_b.canRead (s.tpidrEl0 - 0xa8#64) 4 = true :=
    Memory.canRead_write64_of_canRead _ _ (Memory.canRead_write64_of_canRead _ _ (Memory.canRead_write64_of_canRead _ _
      (Memory.canRead_write64_of_canRead _ _ (Memory.canRead_write64_of_canRead _ _ (Memory.canRead_write64_of_canRead _ _
        (Memory.canRead_write64_of_canRead _ _ hpre.tidCanRead))))))
  have htid_val_b : m_b.read32 (s.tpidrEl0 - 0xa8#64) = 1#32 := by
    have hin : ∀ off : Nat, off ≤ 0x100 → 8 ≤ off →
        ∀ i : Nat, i < (MemWidth.X64).bytes →
          InRegion (s.sp - 0x100#64) 0x100 (s.sp - BitVec.ofNat 64 off + BitVec.ofNat 64 i) :=
      fun off ho h8 i hi => hstk.inRegion_sub ho h8 hi
    have hstep_r : ∀ (m0 : Memory) (off : Nat) (v : BitVec 64), off ≤ 0x100 → 8 ≤ off →
        (m0.write64 (s.sp - BitVec.ofNat 64 off) v).read32 (s.tpidrEl0 - 0xa8#64) =
          m0.read32 (s.tpidrEl0 - 0xa8#64) := fun m0 off v ho h8 =>
      read32_writeSized_disjoint (sz := .X64) hpre.tidDisjoint (hin off ho h8)
    dsimp only [m_b, m_r2, m_r1, m_a]
    rw [hstep_r _ 0xc0 _ (by omega) (by omega), hstep_r _ 0xc8 _ (by omega) (by omega),
        hstep_r _ 0xd0 _ (by omega) (by omega), hstep_r _ 0xd8 _ (by omega) (by omega),
        hstep_r _ 0xe0 _ (by omega) (by omega), hstep_r _ 0x38 _ (by omega) (by omega),
        hstep_r _ 0x40 _ (by omega) (by omega)]
    exact hpre.tidVal
  -- Step 4: raise part 2 (6 instructions: sxtw, mov x8, mrs tp, ldursw tid, svc tkill, bl __syscall_ret)
  have hfr7 : P.fetch (addrs.raiseAddr + 0x1c#64) = some (.bitfield .W64 .SBFM .x1 .x20 0 31) := by
    simpa using fetch_word_at hw_r7 0
  have hfr8 : P.fetch (addrs.raiseAddr + 0x20#64) = some (.moveWide .W64 .MOVZ .x8 0x82#16 0) := by
    have := fetch_word_at hw_r7 1
    rwa [show addrs.raiseAddr + 0x1c#64 + 4#64 = addrs.raiseAddr + 0x20#64 by bv_omega] at this
  have hfr9 : P.fetch (addrs.raiseAddr + 0x24#64) = some (.sysReg true 0x5e82#15 .x0) := by
    have := fetch_word_at hw_r7 2
    rwa [show addrs.raiseAddr + 0x1c#64 + 8#64 = addrs.raiseAddr + 0x24#64 by bv_omega] at this
  have hfr10 : P.fetch (addrs.raiseAddr + 0x28#64) = some (.ldr .W64 .W32 true .x0 (.UnscaledOffset .x0 (-0xa8#64))) := by
    have := fetch_word_at hw_r7 3
    rwa [show addrs.raiseAddr + 0x1c#64 + 0xc#64 = addrs.raiseAddr + 0x28#64 by bv_omega] at this
  have hfr11 : P.fetch (addrs.raiseAddr + 0x2c#64) = some (.system false 0#16) := by
    have := fetch_word_at hw_r7 4
    rwa [show addrs.raiseAddr + 0x1c#64 + 0x10#64 = addrs.raiseAddr + 0x2c#64 by bv_omega] at this
  have hfr12 : P.fetch (addrs.raiseAddr + 0x30#64) = some (.bl (addrs.syscallRetAddr - (addrs.raiseAddr + 0x30#64))) :=
    fetch_instr_at0 hi_r12
  let st1 := (sb.writeReg64 .x1 6#64).setPC (addrs.raiseAddr + 0x20#64)
  let st2 := (st1.writeReg64 .x8 130#64).setPC (addrs.raiseAddr + 0x24#64)
  let st3 := (st2.writeReg64 .x0 s.tpidrEl0).setPC (addrs.raiseAddr + 0x28#64)
  let st4 := (st3.writeReg64 .x0 1#64).setPC (addrs.raiseAddr + 0x2c#64)
  let st5 := ((st4.setSigPending SIGABRT_MASK).writeReg64 .x0 0#64).setPC (addrs.raiseAddr + 0x30#64)
  let st6 := (st5.writeReg64 .lr (addrs.raiseAddr + 0x34#64)).setPC addrs.syscallRetAddr
  have hst0 : P.evalInst (.bitfield .W64 .SBFM .x1 .x20 0 31) sb = st1 := by
    have hr20 : sb.readReg .W64 .x20 = 6#64 := by
      simp [sb, sr7, sr6, sr5, sr4, State.readReg, State.readReg64, State.writeReg64,
        State.setSigMask, State.setMem, State.setPC]
    have hbf : evalBitfield .W64 .SBFM (sb.readReg .W64 .x1) 6#64 0 31 = 6#64 := by
      simp [evalBitfield]
    dsimp only [st1, Program.evalInst, execInstWithSvc, execBitfield]
    rw [hr20, hbf]
    simp only [State.writeReg]
    exact advancePC_eq_setPC (by change addrs.raiseAddr + 0x1c#64 + 4#64 = _; bv_omega)
  have hst1 : P.evalInst (.moveWide .W64 .MOVZ .x8 0x82#16 0) st1 = st2 :=
    evalInst_movz_eq rfl (by change addrs.raiseAddr + 0x20#64 + 4#64 = _; bv_omega)
  have hst2 : P.evalInst (.sysReg true 0x5e82#15 .x0) st2 = st3 := by
    have htp : st2.tpidrEl0 = s.tpidrEl0 := rfl
    dsimp only [st3, Program.evalInst, execInstWithSvc]
    simp only [↓reduceIte, beq_self_eq_true, htp]
    exact advancePC_eq_setPC (by change addrs.raiseAddr + 0x24#64 + 4#64 = _; bv_omega)
  have hst3 : P.evalInst (.ldr .W64 .W32 true .x0 (.UnscaledOffset .x0 (-0xa8#64))) st3 = st4 := by
    have hr0 : st3.readReg64 .x0 = s.tpidrEl0 := by
      simp [st3, State.readReg64, State.writeReg64, State.setPC]
    have hmem3 : st3.mem = m_b := rfl
    dsimp only [st4, Program.evalInst, execInstWithSvc, execLdr]
    have hchk : checkAddrSPAligned st3 (.UnscaledOffset .x0 (-0xa8#64)) = true := rfl
    simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, hr0, hmem3,
      show s.tpidrEl0 + (-0xa8#64) = s.tpidrEl0 - 0xa8#64 by bv_omega,
      htid_cr_b, htid_val_b, Memory.readSized, MemWidth.bytes, State.writeReg]
    rw [show (1#32 : BitVec 32).signExtend 64 = 1#64 from rfl]
    exact advancePC_eq_setPC (by change addrs.raiseAddr + 0x28#64 + 4#64 = _; bv_omega)
  have hnewMask_abrt : (newMask &&& SIGABRT_MASK) ≠ 0#64 := by
    have hbl : (m_r2.read64 addrs.appMaskAddr &&& SIGABRT_MASK) ≠ 0#64 := by
      rw [read64_of_keepsFrozen hkf_s_r2 hpre.appMaskFrozen]; exact hpre.appMaskBlocksAbrt
    dsimp only [newMask]
    intro heq
    apply hbl
    have hbit : (~~~SIG_UNBLOCKABLE_MASK &&& SIGABRT_MASK) = SIGABRT_MASK := by decide
    have : (m_r2.read64 addrs.appMaskAddr &&& ~~~SIG_UNBLOCKABLE_MASK) &&& SIGABRT_MASK =
        m_r2.read64 addrs.appMaskAddr &&& (~~~SIG_UNBLOCKABLE_MASK &&& SIGABRT_MASK) :=
      BitVec.and_assoc _ _ _
    rw [this, hbit] at heq
    exact heq
  have hst4 : P.evalInst (.system false 0#16) st4 = st5 := by
    have hx8 : st4.readReg64 .x8 = 130#64 := by
      simp [st4, st3, st2, State.readReg64, State.writeReg64, State.setPC]
    have hx0 : st4.readReg32 .x0 = 1#32 := by
      simp [st4, State.readReg32, State.readReg64, State.writeReg64, State.setPC]
    have hx1 : st4.readReg32 .x1 = 6#32 := by
      simp [st4, st3, st2, st1, State.readReg32, State.readReg64, State.writeReg64, State.setPC]
    have hmask4 : st4.sigMask = newMask := rfl
    have hpend4 : st4.sigPending = 0#64 := hpre.sigPending
    rw [evalInst_svc_standard hsvc, syscalls_standard_tkill _ hx8]
    unfold execTkill
    dsimp only []
    rw [hx0, hx1, hmask4, hpend4]
    have hne : ((newMask &&& SIGABRT_MASK) != 0#64) = true := bne_iff_ne.mpr hnewMask_abrt
    simp only [LINUX_SIGABRT, hne, BitVec.zero_or, ↓reduceIte]
    have hchecks :
        ((1#32 : BitVec 32).sle 0#32 = false) ∧ ((1#32 : BitVec 32) != 1#32) = false ∧
        ((6#32 : BitVec 32).slt 0#32 = false) ∧ (decide ((6#32 : BitVec 32).toNat > 64) = false) ∧
        ((6#32 : BitVec 32) == 0#32) = false := by decide
    simp only [hchecks.1, hchecks.2.1, hchecks.2.2.1, hchecks.2.2.2.1, hchecks.2.2.2.2,
      Bool.false_eq_true, Bool.or_self, beq_self_eq_true, ↓reduceIte]
    exact advancePC_eq_setPC (by change addrs.raiseAddr + 0x2c#64 + 4#64 = _; bv_omega)
  have hst5 : P.evalInst (.bl (addrs.syscallRetAddr - (addrs.raiseAddr + 0x30#64))) st5 = st6 :=
    evalInst_bl_eq (by change addrs.raiseAddr + 0x30#64 + 4#64 = _; bv_omega)
      (by change addrs.raiseAddr + 0x30#64 + (addrs.syscallRetAddr - (addrs.raiseAddr + 0x30#64)) = _; bv_omega)
  -- Step 5: __syscall_ret (9 instructions, x0 = 0 fast path) → raise + 0x34
  have hst6_sp : st6.sp = s.sp - 0xe0#64 := rfl
  have hst6_spAl : st6.spAligned = true := hsp_ale0
  have hst6_x0 : st6.readReg64 .x0 = 0#64 := by
    simp [st6, st5, State.readReg64, State.writeReg64, State.setPC]
  have hst6_lr : st6.readReg64 .x30 = addrs.raiseAddr + 0x34#64 := by
    simp [st6, State.readReg64, State.writeReg64, State.setPC]
  have hstk_sr : StackRW m_b st6.sp 0x20 := by
    rw [hst6_sp]
    exact hstk_b.shrink (by omega)
  have hsysc := syscallRet_zero_steps (s := st6) hw_sr hCL_b rfl hrun hst6_spAl hst6_x0 hstk_sr
  dsimp only [] at hsysc
  rw [hst6_lr] at hsysc
  let m_s1 := (m_b.write64 (st6.sp - 0x20#64) (st6.readReg64 .x29)).write64 (st6.sp - 0x18#64) (st6.readReg64 .x30)
  let m_s2 := m_s1.write64 (st6.sp - 0x10#64) (st6.readReg64 .x19)
  let ss := ((st6.setMem m_s2).setPState syscallRetZeroPState).setPC (addrs.raiseAddr + 0x34#64)
  have hCL_s2 : P.CodeLoaded m_s2 := by
    have h0 : m_b.canWrite (st6.sp - 0x20#64) 8 = true := hstk_sr.canWrite_sub (by omega) (by omega)
    have h1 : (m_b.write64 (st6.sp - 0x20#64) (st6.readReg64 .x29)).canWrite (st6.sp - 0x18#64) 8 = true :=
      (hstk_sr.of_perm_eq (fun a => by simp [Memory.write64])).canWrite_sub (by omega) (by omega)
    have h2 : m_s1.canWrite (st6.sp - 0x10#64) 8 = true :=
      (hstk_sr.of_perm_eq (fun a => by simp [m_s1, Memory.write64])).canWrite_sub (by omega) (by omega)
    exact codeLoaded_of_keepsFrozen hCL_b
      ((Memory.keepsFrozen_write64 h0 _).trans ((Memory.keepsFrozen_write64 h1 _).trans (Memory.keepsFrozen_write64 h2 _)))
  -- Step 6: raise part 3 (3 instructions) → __restore_sigs
  have hfr13 : P.fetch (addrs.raiseAddr + 0x34#64) = some (.logicalShift .W64 .ORR .x20 .xzr .x0 .LSL 0) := by
    simpa using fetch_word_at hw_r13 0
  have hfr14 : P.fetch (addrs.raiseAddr + 0x38#64) = some (.logicalShift .W64 .ORR .x0 .xzr .x19 .LSL 0) := by
    have := fetch_word_at hw_r13 1
    rwa [show addrs.raiseAddr + 0x34#64 + 4#64 = addrs.raiseAddr + 0x38#64 by bv_omega] at this
  have hfr15 : P.fetch (addrs.raiseAddr + 0x3c#64) = some (.bl (addrs.restoreSigsAddr - (addrs.raiseAddr + 0x3c#64))) :=
    fetch_instr_at0 hi_r15
  let su1 := (ss.writeReg64 .x20 0#64).setPC (addrs.raiseAddr + 0x38#64)
  let su2 := (su1.writeReg64 .x0 (s.sp - 0xc0#64)).setPC (addrs.raiseAddr + 0x3c#64)
  let su3 := (su2.writeReg64 .lr (addrs.raiseAddr + 0x40#64)).setPC addrs.restoreSigsAddr
  have hsu0 : P.evalInst (.logicalShift .W64 .ORR .x20 .xzr .x0 .LSL 0) ss = su1 :=
    evalInst_movReg_eq
      (by simpa [ss, State.readReg, State.readReg64, State.setPC, State.setPState, State.setMem] using hst6_x0)
      (by intro h; cases h)
      (by change addrs.raiseAddr + 0x34#64 + 4#64 = _; bv_omega)
  have hsu1 : P.evalInst (.logicalShift .W64 .ORR .x0 .xzr .x19 .LSL 0) su1 = su2 :=
    evalInst_movReg_eq
      (by simp [su1, ss, st6, st5, st4, st3, st2, st1, sb, sr7, sr6, sr5,
        State.readReg, State.readReg64, State.writeReg64, State.setPC, State.setPState,
        State.setSigMask, State.setSigPending, State.setMem])
      (by intro h; cases h)
      (by change addrs.raiseAddr + 0x38#64 + 4#64 = _; bv_omega)
  have hsu2 : P.evalInst (.bl (addrs.restoreSigsAddr - (addrs.raiseAddr + 0x3c#64))) su2 = su3 :=
    evalInst_bl_eq (by change addrs.raiseAddr + 0x3c#64 + 4#64 = _; bv_omega)
      (by change addrs.raiseAddr + 0x3c#64 + (addrs.restoreSigsAddr - (addrs.raiseAddr + 0x3c#64)) = _; bv_omega)
  -- Step 7: __restore_sigs (6 instructions) → .Signaled 6#7
  have hsu3_x0 : su3.readReg64 .x0 = s.sp - 0xc0#64 := by
    simp [su3, su2, State.readReg64, State.writeReg64, State.setPC]
  have hold_cr_b : m_b.canRead (s.sp - 0xc0#64) 8 = true :=
    canRead_write64_self (hstk_r2.allPerm_r_sub (by omega) (by omega))
  have hold_cr_s2 : m_s2.canRead (s.sp - 0xc0#64) 8 = true :=
    Memory.canRead_write64_of_canRead _ _ (Memory.canRead_write64_of_canRead _ _ (Memory.canRead_write64_of_canRead _ _ hold_cr_b))
  have hold_val_s2 : m_s2.read64 (s.sp - 0xc0#64) = 0#64 := by
    have hd0 : DisjointRegions (st6.sp - 0x10#64) 8 (s.sp - 0xc0#64) 8 := by
      rw [hst6_sp]; unfold DisjointRegions; bv_omega
    have hd1 : DisjointRegions (st6.sp - 0x18#64) 8 (s.sp - 0xc0#64) 8 := by
      rw [hst6_sp]; unfold DisjointRegions; bv_omega
    have hd2 : DisjointRegions (st6.sp - 0x20#64) 8 (s.sp - 0xc0#64) 8 := by
      rw [hst6_sp]; unfold DisjointRegions; bv_omega
    dsimp only [m_s2, m_s1]
    rw [read64_write64_disjoint hd0, read64_write64_disjoint hd1, read64_write64_disjoint hd2,
        read64_write64_self]
  obtain ⟨sf, hrest, hsig, hfs, htr⟩ := restoreSigs_sigabrt_steps (s := su3) hsvc hw_rs hCL_s2 rfl hrun
    rfl hpre.sigAbrtDfl
    (hsu3_x0 ▸ hstk.sub_ne_zero (by omega))
    (hsu3_x0 ▸ hstk.sub_no_wrap (by omega) (by omega))
    (hsu3_x0 ▸ hold_cr_s2)
    (hsu3_x0 ▸ hold_val_s2)
  refine ⟨sf, ?_, hsig, hfs, htr⟩
  -- Chain all 7 steps
  refine steps_exec hCL hrun (hpc.symm ▸ hfa0) hsa0 ?_
  refine steps_exec hCL_a hrun hfa1 hsa1 ?_
  refine steps_exec hCL_a hrun hfa2 hsa2 ?_
  refine steps_exec hCL_a hrun hfa3 hsa3 ?_
  refine steps_exec hCL_a hrun hfr0 hsr0 ?_
  refine steps_exec hCL_r1 hrun hfr1 hsr1 ?_
  refine steps_exec hCL_r1 hrun hfr2 hsr2 ?_
  refine steps_exec hCL_r2 hrun hfr3 hsr3 ?_
  refine steps_exec hCL_r2 hrun hfr4 hsr4 ?_
  refine steps_exec hCL_r2 hrun hfr5 hsr5 ?_
  refine steps_exec hCL_r2 hrun hfr6 hsr6 ?_
  refine hblk.trans ?_
  refine steps_exec hCL_b hrun hfr7 hst0 ?_
  refine steps_exec hCL_b hrun hfr8 hst1 ?_
  refine steps_exec hCL_b hrun hfr9 hst2 ?_
  refine steps_exec hCL_b hrun hfr10 hst3 ?_
  refine steps_exec hCL_b hrun hfr11 hst4 ?_
  refine steps_exec hCL_b hrun hfr12 hst5 ?_
  refine hsysc.trans ?_
  refine steps_exec hCL_s2 hrun hfr13 hsu0 ?_
  refine steps_exec hCL_s2 hrun hfr14 hsu1 ?_
  refine steps_exec hCL_s2 hrun hfr15 hsu2 hrest

/-! ## 4. Abort-Only `rdl_shim.S` Handlers (`rdl_panic_shims_to_sigabrt`) -/

private theorem PanicAbortPre.withPC {P : Program} {addrs : F3PanicAddrs} {s : State}
    (h : PanicAbortPre P addrs s) (pc : BitVec 64) :
    PanicAbortPre P addrs (s.setPC pc) :=
  { codeLoaded := h.codeLoaded
    running := h.running
    spAligned := h.spAligned
    stackRW := h.stackRW
    sigMask := h.sigMask
    sigPending := h.sigPending
    sigAbrtDfl := h.sigAbrtDfl
    appMaskNeZero := h.appMaskNeZero
    appMaskNoWrap := h.appMaskNoWrap
    appMaskCanRead := h.appMaskCanRead
    appMaskFrozen := h.appMaskFrozen
    appMaskBlocksAbrt := h.appMaskBlocksAbrt
    tidCanRead := h.tidCanRead
    tidVal := h.tidVal
    tidDisjoint := h.tidDisjoint }

/-- Both abort-only `rdl_shim.S` handlers (`rust_begin_unwind` and `__rust_alloc_error_handler`)
    branch directly to `abort` in 1 instruction and terminate with `.Signaled 6#7`. -/
theorem rdl_panic_shims_to_sigabrt {P : Program} {addrs : F3PanicAddrs} {s : State}
    (hsvc : P.svc = Syscall.standard)
    (habort : CodeChunks P (f3AbortChunks addrs))
    (hshims : CodeChunks P (f3PanicShimChunks addrs))
    (hpc : s.pc = addrs.rustBeginUnwindAddr ∨ s.pc = addrs.rustAllocErrorHandlerAddr)
    (hpre : PanicAbortPre P addrs s) :
    ∃ sf, Steps P s sf ∧ sf.status = .Signaled 6#7 ∧ sf.fs = s.fs ∧ sf.trace = s.trace := by
  dsimp only [f3PanicShimChunks, CodeChunks, CodeChunk.holds] at hshims
  obtain ⟨hbu, hae⟩ := hshims
  rcases hpc with hpc | hpc
  · have hf : P.fetch s.pc = some (.b (addrs.abortAddr - addrs.rustBeginUnwindAddr)) :=
      hpc.symm ▸ fetch_instr_at0 hbu
    have hev : P.evalInst (.b (addrs.abortAddr - addrs.rustBeginUnwindAddr)) s =
        s.setPC addrs.abortAddr := by
      simp only [Program.evalInst, execInstWithSvc, hpc]; congr 1; bv_omega
    obtain ⟨sf, hsteps, hsig, hfs, htr⟩ :=
      musl_abort_to_sigabrt hsvc habort rfl (s := s.setPC addrs.abortAddr) (hpre.withPC _)
    exact ⟨sf, steps_exec hpre.codeLoaded hpre.running hf hev hsteps, hsig, hfs, htr⟩
  · have hf : P.fetch s.pc = some (.b (addrs.abortAddr - addrs.rustAllocErrorHandlerAddr)) :=
      hpc.symm ▸ fetch_instr_at0 hae
    have hev : P.evalInst (.b (addrs.abortAddr - addrs.rustAllocErrorHandlerAddr)) s =
        s.setPC addrs.abortAddr := by
      simp only [Program.evalInst, execInstWithSvc, hpc]; congr 1; bv_omega
    obtain ⟨sf, hsteps, hsig, hfs, htr⟩ :=
      musl_abort_to_sigabrt hsvc habort rfl (s := s.setPC addrs.abortAddr) (hpre.withPC _)
    exact ⟨sf, steps_exec hpre.codeLoaded hpre.running hf hev hsteps, hsig, hfs, htr⟩

/-! ## 5. Layout-Generic Abstract Verifier for All Linked Rust Panic Entry Points -/

/-- Minimal symbolic register value tracked across non-returning Rust panic wrappers:
    - `.constVal v`: exact 64-bit constant (`adrp` / `adrp + add lo12`),
    - `.masked8`: byte-masked index `< 256` (`and rd, rn, #0xff`). -/
inductive PanicSymVal where
  | constVal (v : BitVec 64)
  | masked8
  deriving DecidableEq, Repr

/-- Semantics of `PanicSymVal` on a 64-bit register value. -/
@[expose] def PanicSymVal.Holds : PanicSymVal → BitVec 64 → Prop
  | .constVal v, x => x = v
  | .masked8, x => x.toNat < 256

/-- Small associative map from tracked registers (`x8`/`x9`/`x10`, etc.) to `PanicSymVal`. -/
abbrev PanicSymEnv := List (Reg × PanicSymVal)

/-- Lookup a tracked register in `PanicSymEnv`. -/
@[expose] def PanicSymEnv.lookup (env : PanicSymEnv) (r : Reg) : Option PanicSymVal :=
  (env.find? fun p => decide (p.1 = r)).map Prod.snd

/-- Erase register `r` from `PanicSymEnv`. -/
@[expose] def PanicSymEnv.erase (env : PanicSymEnv) (r : Reg) : PanicSymEnv :=
  env.filter fun p => decide (p.1 ≠ r)

/-- Bind non-zero, non-SP register `r` to `v` in `PanicSymEnv`. -/
@[expose] def PanicSymEnv.set (env : PanicSymEnv) (r : Reg) (v : PanicSymVal) : PanicSymEnv :=
  match r with
  | .gpr idx => if idx == 31#5 then env else (r, v) :: env.erase r
  | .sp | .xzr => env

/-- Invariant: every tracked binding in `env` holds in `s`. -/
@[expose] def PanicSymEnv.Holds (env : PanicSymEnv) (s : State) : Prop :=
  ∀ p ∈ env, p.2.Holds (s.readReg64 p.1)

private theorem PanicSymEnv.lookup_holds {env : PanicSymEnv} {s : State} {r : Reg} {v : PanicSymVal}
    (henv : env.Holds s) (hl : env.lookup r = some v) : v.Holds (s.readReg64 r) := by
  unfold PanicSymEnv.lookup at hl
  rcases Option.map_eq_some_iff.mp hl with ⟨⟨r', v'⟩, hfind, rfl⟩
  have hmem := List.mem_of_find?_eq_some hfind
  have hdec := List.find?_some hfind
  have heq : r' = r := of_decide_eq_true hdec
  subst heq
  exact henv (r', v') hmem

private theorem PanicSymEnv.holds_writeReg64_erase {env : PanicSymEnv} {s : State}
    (henv : env.Holds s) (rd : Reg) (val : BitVec 64) :
    (env.erase rd).Holds (s.writeReg64 rd val) := by
  intro p hp
  simp only [PanicSymEnv.erase, List.mem_filter, decide_eq_true_eq] at hp
  rcases p with ⟨rp, vp⟩
  have hne : rp ≠ rd := hp.2
  have hrd : (s.writeReg64 rd val).readReg64 rp = s.readReg64 rp := by
    cases rd with
    | sp =>
      cases rp with
      | sp => exact (hne rfl).elim
      | xzr => rfl
      | gpr _ => rfl
    | xzr =>
      cases rp <;> rfl
    | gpr i =>
      cases rp with
      | sp => simp [State.writeReg64, State.readReg64]
      | xzr => rfl
      | gpr j =>
        have hij : j ≠ i := fun h => hne (by rw [h])
        simp only [State.writeReg64, State.readReg64]
        split
        · rfl
        · by_cases hi : i = 31#5 <;> simp [hi, hij, RegFile.read, RegFile.write]
  rw [hrd]
  exact henv (rp, vp) hp.1

private theorem PanicSymEnv.holds_writeReg_erase {env : PanicSymEnv} {s : State}
    (henv : env.Holds s) (w : Width) (rd : Reg) (val : BitVec 64) :
    (env.erase rd).Holds (s.writeReg w rd val) := by
  cases w
  · exact PanicSymEnv.holds_writeReg64_erase henv rd _
  · exact PanicSymEnv.holds_writeReg64_erase henv rd _

private theorem PanicSymEnv.holds_setMem {env : PanicSymEnv} {s : State}
    (henv : env.Holds s) (m : Memory) : env.Holds (s.setMem m) := henv

private theorem PanicSymEnv.holds_setPC {env : PanicSymEnv} {s : State}
    (henv : env.Holds s) (pc : BitVec 64) : env.Holds (s.setPC pc) := henv

private theorem PanicSymEnv.holds_advancePC {env : PanicSymEnv} {s : State}
    (henv : env.Holds s) : env.Holds s.advancePC := henv

private theorem PanicSymEnv.holds_setPState {env : PanicSymEnv} {s : State}
    (henv : env.Holds s) (ps : PState) : env.Holds (s.setPState ps) := henv

/-- Register is a GPR or `xzr` (not `.sp`). -/
@[expose] def regIsNotSp : Reg → Bool
  | .sp => false
  | .gpr _ | .xzr => true

/-- Inductive soundness certificate that executing from `(pc, spDrop, env)` in `P`
    reaches `addrs.abortAddr` with `spDrop' ≤ 0x100`, using only stack writes in
    `[sp0 - 0x100, sp0)` and reads from `addrs`'s `.rodata`/`.got` tables. -/
inductive PanicSafeFrom (P : Program) (addrs : F3PanicAddrs) :
    BitVec 64 → Nat → PanicSymEnv → Prop where
  | atAbort (spDrop : Nat) (env : PanicSymEnv) (hdrop : spDrop ≤ 0x100) :
      PanicSafeFrom P addrs addrs.abortAddr spDrop env
  | b (pc off : BitVec 64) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.b off))
      (hnext : PanicSafeFrom P addrs (pc + off) spDrop env) :
      PanicSafeFrom P addrs pc spDrop env
  | bl (pc off : BitVec 64) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.bl off))
      (hnext : PanicSafeFrom P addrs (pc + off) spDrop (env.erase .lr)) :
      PanicSafeFrom P addrs pc spDrop env
  | bCond (pc off : BitVec 64) (cond : CondCode) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.bCond cond off))
      (htaken : PanicSafeFrom P addrs (pc + off) spDrop env)
      (hfall : PanicSafeFrom P addrs (pc + 4#64) spDrop env) :
      PanicSafeFrom P addrs pc spDrop env
  | cbz (pc off : BitVec 64) (w : Width) (isNZ : Bool) (rt : Reg) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.cbz w isNZ rt off))
      (htaken : PanicSafeFrom P addrs (pc + off) spDrop env)
      (hfall : PanicSafeFrom P addrs (pc + 4#64) spDrop env) :
      PanicSafeFrom P addrs pc spDrop env
  | subSp (pc : BitVec 64) (imm12 : BitVec 12) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.addSubImm .W64 .SUB .sp .sp imm12 false))
      (hal : imm12.toNat % 16 = 0)
      (hdrop : spDrop + imm12.toNat ≤ 0x100)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) (spDrop + imm12.toNat) (env.erase .sp)) :
      PanicSafeFrom P addrs pc spDrop env
  | stpPreSp (pc off : BitVec 64) (rt1 rt2 : Reg) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.stp .W64 rt1 rt2 (.PreIndex .sp off)))
      (hge16 : 16 ≤ (0#64 - off).toNat)
      (hal : (0#64 - off).toNat % 16 = 0)
      (hdrop : spDrop + (0#64 - off).toNat ≤ 0x100)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) (spDrop + (0#64 - off).toNat) (env.erase .sp)) :
      PanicSafeFrom P addrs pc spDrop env
  | stpOffSp (pc off : BitVec 64) (rt1 rt2 : Reg) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.stp .W64 rt1 rt2 (.Offset .sp off)))
      (hbound : off.toNat + 16 ≤ spDrop)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop env) :
      PanicSafeFrom P addrs pc spDrop env
  | strOffSp (pc off : BitVec 64) (sz : MemWidth) (rt : Reg) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.str sz rt (.Offset .sp off)))
      (hbound : off.toNat + sz.bytes ≤ spDrop)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop env) :
      PanicSafeFrom P addrs pc spDrop env
  | adr (pc off : BitVec 64) (page : Bool) (rd : Reg) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.adr page rd off))
      (hnotSp : regIsNotSp rd = true)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop
        (env.set rd (.constVal ((if page then pc &&& 0xfffffffffffff000#64 else pc) + off)))) :
      PanicSafeFrom P addrs pc spDrop env
  | addSubImmConst (pc : BitVec 64) (rd rn : Reg) (imm12 : BitVec 12) (v : BitVec 64)
      (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.addSubImm .W64 .ADD rd rn imm12 false))
      (hnotSp : regIsNotSp rd = true)
      (hlook : env.lookup rn = some (.constVal v))
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop
        (env.set rd (.constVal (v + imm12.zeroExtend 64)))) :
      PanicSafeFrom P addrs pc spDrop env
  | addSubImmPure (pc : BitVec 64) (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12)
      (sh : Bool) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.addSubImm w op rd rn imm12 sh))
      (hnotSp : regIsNotSp rd = true)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop (env.erase rd)) :
      PanicSafeFrom P addrs pc spDrop env
  | andMask8 (pc : BitVec 64) (rd rn : Reg) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.logicalImm .W64 .AND rd rn 0xff#64))
      (hnotSp : regIsNotSp rd = true)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop (env.set rd .masked8)) :
      PanicSafeFrom P addrs pc spDrop env
  | logicalImmPure (pc mask : BitVec 64) (w : Width) (op : LogicalOp) (rd rn : Reg)
      (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.logicalImm w op rd rn mask))
      (hnotSp : regIsNotSp rd = true)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop (env.erase rd)) :
      PanicSafeFrom P addrs pc spDrop env
  | moveWidePure (pc : BitVec 64) (w : Width) (op : MoveWideOp) (rd : Reg) (imm16 : BitVec 16)
      (hw : Nat) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.moveWide w op rd imm16 hw))
      (hnotSp : regIsNotSp rd = true)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop (env.erase rd)) :
      PanicSafeFrom P addrs pc spDrop env
  | logicalShiftPure (pc : BitVec 64) (w : Width) (op : LogicalOp) (rd rn rm : Reg)
      (sh : ShiftType) (amt : Nat) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.logicalShift w op rd rn rm sh amt))
      (hnotSp : regIsNotSp rd = true)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop (env.erase rd)) :
      PanicSafeFrom P addrs pc spDrop env
  | addSubShiftPure (pc : BitVec 64) (w : Width) (op : AddSubOp) (rd rn rm : Reg)
      (sh : ShiftType) (amt : Nat) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.addSubShift w op rd rn rm sh amt))
      (hnotSp : regIsNotSp rd = true)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop (env.erase rd)) :
      PanicSafeFrom P addrs pc spDrop env
  | ldrGot8 (pc off v : BitVec 64) (w : Width) (rt rn : Reg) (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.ldr w .X64 false rt (.Offset rn off)))
      (hnotSpRt : regIsNotSp rt = true)
      (hnotSpRn : regIsNotSp rn = true)
      (hlook : env.lookup rn = some (.constVal v))
      (hmem : (v + off) ∈ addrs.gotRead8Addrs)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop (env.erase rt)) :
      PanicSafeFrom P addrs pc spDrop env
  | ldrRoTable32 (pc v : BitVec 64) (w : Width) (signed : Bool) (rt rn rm : Reg)
      (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.ldr w .W32 signed rt (.RegOffset rn rm .UXTX 2)))
      (hnotSpRt : regIsNotSp rt = true)
      (hnotSpRn : regIsNotSp rn = true)
      (hlookRn : env.lookup rn = some (.constVal v))
      (hlookRm : env.lookup rm = some .masked8)
      (hmem : v ∈ addrs.roAssertTable32Addrs)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop (env.erase rt)) :
      PanicSafeFrom P addrs pc spDrop env
  | ldrRoTable64 (pc v : BitVec 64) (w : Width) (signed : Bool) (rt rn rm : Reg)
      (spDrop : Nat) (env : PanicSymEnv)
      (hfetch : P.fetch pc = some (.ldr w .X64 signed rt (.RegOffset rn rm .UXTX 3)))
      (hnotSpRt : regIsNotSp rt = true)
      (hnotSpRn : regIsNotSp rn = true)
      (hlookRn : env.lookup rn = some (.constVal v))
      (hlookRm : env.lookup rm = some .masked8)
      (hmem : v ∈ addrs.roAssertTable64Addrs)
      (hnext : PanicSafeFrom P addrs (pc + 4#64) spDrop (env.erase rt)) :
      PanicSafeFrom P addrs pc spDrop env

/-- Invariant maintained across every step of `PanicSafeFrom` from initial stack pointer `sp0`. -/
private structure PanicWalkInv (P : Program) (addrs : F3PanicAddrs) (sp0 : BitVec 64)
    (fs0 : FsState) (tr0 : List TraceEvent) (spDrop : Nat) (s : State) : Prop where
  codeLoaded        : P.CodeLoaded s.mem
  running           : s.status = .Running
  spAligned         : s.spAligned = true
  spEq              : s.sp = sp0 - BitVec.ofNat 64 spDrop
  dropLe            : spDrop ≤ 0x100
  stackRW           : StackRW s.mem sp0 0x200
  sigMask           : s.sigMask = 0#64
  sigPending        : s.sigPending = 0#64
  sigAbrtDfl        : (s.getSigAction LINUX_SIGABRT).handler = SIG_DFL
  appMaskNeZero     : addrs.appMaskAddr ≠ 0#64
  appMaskNoWrap     : addrs.appMaskAddr.toNat + 8 ≤ 2 ^ 64
  appMaskCanRead    : s.mem.canRead addrs.appMaskAddr 8 = true
  appMaskFrozen     : s.mem.allPerm (·.frozen) addrs.appMaskAddr 8 = true
  appMaskBlocksAbrt : (s.mem.read64 addrs.appMaskAddr &&& SIGABRT_MASK) ≠ 0#64
  tidCanRead        : s.mem.canRead (s.tpidrEl0 - 0xa8#64) 4 = true
  tidVal            : s.mem.read32 (s.tpidrEl0 - 0xa8#64) = 1#32
  tidDisjoint       : DisjointRegions (sp0 - 0x200#64) 0x200 (s.tpidrEl0 - 0xa8#64) 4
  roTable32Readable : ∀ a ∈ addrs.roAssertTable32Addrs, s.mem.Readable a 1024
  roTable64Readable : ∀ a ∈ addrs.roAssertTable64Addrs, s.mem.Readable a 2048
  gotRead8CanRead   : ∀ a ∈ addrs.gotRead8Addrs, s.mem.canRead a 8 = true
  fsEq              : s.fs = fs0
  traceEq           : s.trace = tr0

private theorem PanicWalkInv.toAbortPre {P : Program} {addrs : F3PanicAddrs} {sp0 : BitVec 64}
    {fs0 : FsState} {tr0 : List TraceEvent} {spDrop : Nat} {s : State}
    (h : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s) :
    PanicAbortPre P addrs s := by
  refine
    { codeLoaded := h.codeLoaded
      running := h.running
      spAligned := h.spAligned
      stackRW := by rw [h.spEq]; exact h.stackRW.shrink (by have := h.dropLe; omega)
      sigMask := h.sigMask
      sigPending := h.sigPending
      sigAbrtDfl := h.sigAbrtDfl
      appMaskNeZero := h.appMaskNeZero
      appMaskNoWrap := h.appMaskNoWrap
      appMaskCanRead := h.appMaskCanRead
      appMaskFrozen := h.appMaskFrozen
      appMaskBlocksAbrt := h.appMaskBlocksAbrt
      tidCanRead := h.tidCanRead
      tidVal := h.tidVal
      tidDisjoint := ?_ }
  rw [h.spEq]
  have hd := h.tidDisjoint
  have hlt := h.stackRW.1
  have hle := h.dropLe
  unfold DisjointRegions at hd ⊢
  constructor
  · have h1 : s.tpidrEl0 - 0xa8#64 - (sp0 - BitVec.ofNat 64 spDrop - 0x100#64) =
        (s.tpidrEl0 - 0xa8#64 - (sp0 - 0x200#64)) - BitVec.ofNat 64 (0x100 - spDrop) := by
      bv_omega
    bv_omega
  · bv_omega

private theorem PanicWalkInv.of_entryPre {P : Program} {addrs : F3PanicAddrs} {s : State}
    (h : PanicEntryPre P addrs s) :
    PanicWalkInv P addrs s.sp s.fs s.trace 0 s :=
  { codeLoaded := h.codeLoaded
    running := h.running
    spAligned := h.spAligned
    spEq := by simp
    dropLe := by omega
    stackRW := h.stackRW
    sigMask := h.sigMask
    sigPending := h.sigPending
    sigAbrtDfl := h.sigAbrtDfl
    appMaskNeZero := h.appMaskNeZero
    appMaskNoWrap := h.appMaskNoWrap
    appMaskCanRead := h.appMaskCanRead
    appMaskFrozen := h.appMaskFrozen
    appMaskBlocksAbrt := h.appMaskBlocksAbrt
    tidCanRead := h.tidCanRead
    tidVal := h.tidVal
    tidDisjoint := h.tidDisjoint
    roTable32Readable := h.roTable32Readable
    roTable64Readable := h.roTable64Readable
    gotRead8CanRead := h.gotRead8CanRead
    fsEq := rfl
    traceEq := rfl }

private theorem PanicWalkInv.withRegNotSp {P : Program} {addrs : F3PanicAddrs} {sp0 : BitVec 64}
    {fs0 : FsState} {tr0 : List TraceEvent} {spDrop : Nat} {s : State}
    (h : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s) (rd : Reg) (hrd : regIsNotSp rd = true)
    (v : BitVec 64) :
    PanicWalkInv P addrs sp0 fs0 tr0 spDrop (s.writeReg64 rd v) := by
  cases rd with
  | sp => simp [regIsNotSp] at hrd
  | xzr => simpa [State.writeReg64] using h
  | gpr idx =>
    exact
      { h with
        codeLoaded := h.codeLoaded
        running := h.running
        spAligned := h.spAligned
        spEq := h.spEq
        stackRW := h.stackRW
        sigMask := h.sigMask
        sigPending := h.sigPending
        sigAbrtDfl := h.sigAbrtDfl
        appMaskCanRead := h.appMaskCanRead
        appMaskFrozen := h.appMaskFrozen
        appMaskBlocksAbrt := h.appMaskBlocksAbrt
        tidCanRead := h.tidCanRead
        tidVal := h.tidVal
        tidDisjoint := h.tidDisjoint
        roTable32Readable := h.roTable32Readable
        roTable64Readable := h.roTable64Readable
        gotRead8CanRead := h.gotRead8CanRead
        fsEq := h.fsEq
        traceEq := h.traceEq }

private theorem PanicWalkInv.withRegWNotSp {P : Program} {addrs : F3PanicAddrs} {sp0 : BitVec 64}
    {fs0 : FsState} {tr0 : List TraceEvent} {spDrop : Nat} {s : State}
    (h : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s) (w : Width) (rd : Reg)
    (hrd : regIsNotSp rd = true) (v : BitVec 64) :
    PanicWalkInv P addrs sp0 fs0 tr0 spDrop (s.writeReg w rd v) := by
  cases w
  · exact h.withRegNotSp rd hrd _
  · exact h.withRegNotSp rd hrd _

private theorem PanicWalkInv.withPState {P : Program} {addrs : F3PanicAddrs} {sp0 : BitVec 64}
    {fs0 : FsState} {tr0 : List TraceEvent} {spDrop : Nat} {s : State}
    (h : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s) (ps : PState) :
    PanicWalkInv P addrs sp0 fs0 tr0 spDrop (s.setPState ps) :=
  { codeLoaded := h.codeLoaded, running := h.running, spAligned := h.spAligned, spEq := h.spEq,
    dropLe := h.dropLe, stackRW := h.stackRW, sigMask := h.sigMask, sigPending := h.sigPending,
    sigAbrtDfl := h.sigAbrtDfl, appMaskNeZero := h.appMaskNeZero, appMaskNoWrap := h.appMaskNoWrap,
    appMaskCanRead := h.appMaskCanRead, appMaskFrozen := h.appMaskFrozen,
    appMaskBlocksAbrt := h.appMaskBlocksAbrt, tidCanRead := h.tidCanRead, tidVal := h.tidVal,
    tidDisjoint := h.tidDisjoint, roTable32Readable := h.roTable32Readable,
    roTable64Readable := h.roTable64Readable, gotRead8CanRead := h.gotRead8CanRead,
    fsEq := h.fsEq, traceEq := h.traceEq }

private theorem PanicWalkInv.withPC {P : Program} {addrs : F3PanicAddrs} {sp0 : BitVec 64}
    {fs0 : FsState} {tr0 : List TraceEvent} {spDrop : Nat} {s : State}
    (h : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s) (pc : BitVec 64) :
    PanicWalkInv P addrs sp0 fs0 tr0 spDrop (s.setPC pc) :=
  { codeLoaded := h.codeLoaded, running := h.running, spAligned := h.spAligned, spEq := h.spEq,
    dropLe := h.dropLe, stackRW := h.stackRW, sigMask := h.sigMask, sigPending := h.sigPending,
    sigAbrtDfl := h.sigAbrtDfl, appMaskNeZero := h.appMaskNeZero, appMaskNoWrap := h.appMaskNoWrap,
    appMaskCanRead := h.appMaskCanRead, appMaskFrozen := h.appMaskFrozen,
    appMaskBlocksAbrt := h.appMaskBlocksAbrt, tidCanRead := h.tidCanRead, tidVal := h.tidVal,
    tidDisjoint := h.tidDisjoint, roTable32Readable := h.roTable32Readable,
    roTable64Readable := h.roTable64Readable, gotRead8CanRead := h.gotRead8CanRead,
    fsEq := h.fsEq, traceEq := h.traceEq }

private theorem PanicWalkInv.withWriteSized {P : Program} {addrs : F3PanicAddrs} {sp0 : BitVec 64}
    {fs0 : FsState} {tr0 : List TraceEvent} {spDrop : Nat} {s : State}
    (h : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s)
    (sz : MemWidth) (w v : BitVec 64)
    (hcw : s.mem.canWrite w sz.bytes = true)
    (hin : ∀ i : Nat, i < sz.bytes → InRegion (sp0 - 0x200#64) 0x200 (w + BitVec.ofNat 64 i)) :
    PanicWalkInv P addrs sp0 fs0 tr0 spDrop (s.setMem (s.mem.writeSized sz w v)) := by
  have hkf : s.mem.KeepsFrozen (s.mem.writeSized sz w v) := Memory.keepsFrozen_writeSized hcw v
  exact
    { codeLoaded := codeLoaded_of_keepsFrozen h.codeLoaded hkf
      running := h.running
      spAligned := h.spAligned
      spEq := h.spEq
      dropLe := h.dropLe
      stackRW := h.stackRW.of_perm_eq (fun a => perm_writeSized_eq s.mem sz w a v)
      sigMask := h.sigMask
      sigPending := h.sigPending
      sigAbrtDfl := h.sigAbrtDfl
      appMaskNeZero := h.appMaskNeZero
      appMaskNoWrap := h.appMaskNoWrap
      appMaskCanRead := canRead_of_keepsFrozen hkf h.appMaskFrozen h.appMaskCanRead
      appMaskFrozen := allPerm_frozen_of_keepsFrozen hkf h.appMaskFrozen
      appMaskBlocksAbrt := by
        dsimp only [State.setMem]
        rw [read64_of_keepsFrozen hkf h.appMaskFrozen]; exact h.appMaskBlocksAbrt
      tidCanRead := canRead_writeSized_of_canRead sz w v h.tidCanRead
      tidVal := by
        dsimp only [State.setMem]
        rw [read32_writeSized_disjoint h.tidDisjoint hin]; exact h.tidVal
      tidDisjoint := h.tidDisjoint
      roTable32Readable := fun a ha => readable_writeSized sz w v (h.roTable32Readable a ha)
      roTable64Readable := fun a ha => readable_writeSized sz w v (h.roTable64Readable a ha)
      gotRead8CanRead := fun a ha => canRead_writeSized_of_canRead sz w v (h.gotRead8CanRead a ha)
      fsEq := h.fsEq
      traceEq := h.traceEq }

private theorem canRead_of_readable {m : Memory} {base a : BitVec 64} {len n : Nat}
    (hr : m.Readable base len)
    (hin : ∀ k : Nat, k < n → InRegion base len (a + BitVec.ofNat 64 k)) :
    m.canRead a n = true := by
  unfold Memory.canRead
  simp only [Bool.and_eq_true]
  constructor
  · rw [Memory.allPerm_iff]
    exact fun k hk => (hr _ (hin k hk)).1
  · have hlf : ∀ j : Nat, ∀ addr : BitVec 64,
        (∀ i < j, InRegion base len (addr + BitVec.ofNat 64 i)) →
        m.allNoLazyFree addr j = true := by
      intro j
      induction j with
      | zero => intros; rfl
      | succ j ih =>
        intro addr hj
        simp only [Memory.allNoLazyFree, Bool.and_eq_true]
        refine ⟨?_, ih (addr + 1#64) fun i hi => by
          have := hj (i + 1) (by omega)
          rwa [show addr + BitVec.ofNat 64 (i + 1) = addr + 1#64 + BitVec.ofNat 64 i by bv_omega] at this⟩
        have h0 := hj 0 (by omega)
        simp only [BitVec.add_zero] at h0
        simp [(hr _ h0).2]
    exact hlf n a hin

private theorem PanicSymEnv.holds_writeReg64_set_notSp {env : PanicSymEnv} {s : State}
    (henv : env.Holds s) (rd : Reg) (hrd : regIsNotSp rd = true) (val : BitVec 64) (sv : PanicSymVal)
    (hsv : sv.Holds val) :
    (env.set rd sv).Holds (s.writeReg64 rd val) := by
  cases rd with
  | sp => simp [regIsNotSp] at hrd
  | xzr =>
    intro p hp
    simp only [PanicSymEnv.set, State.writeReg64] at hp ⊢
    exact henv p hp
  | gpr idx =>
    intro p hp
    by_cases h31 : idx = 31#5
    · subst h31
      simp only [PanicSymEnv.set, beq_self_eq_true, ↓reduceIte] at hp
      have hw : s.writeReg64 (.gpr 31#5) val = s := by
        cases s; simp [State.writeReg64]
      rw [hw]
      exact henv p hp
    · have h31f : (idx == 31#5) = false := beq_false_of_ne h31
      simp only [PanicSymEnv.set, h31f, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp only [State.readReg64, State.writeReg64, h31f, Bool.false_eq_true, ↓reduceIte,
          RegFile.read_write_same]
        exact hsv
      · exact PanicSymEnv.holds_writeReg64_erase henv (.gpr idx) val p hp

private theorem bv64_and15_eq_zero_of_mod16 {x : BitVec 64} (h : x.toNat % 16 = 0) :
    (x &&& 15#64 == 0#64) = true := by
  have heq : (x &&& 15#64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change x.toNat &&& (2 ^ 4 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact h
  simp [heq]

private theorem panicSafeFrom_reaches_abort {P : Program} {addrs : F3PanicAddrs}
    {sp0 : BitVec 64} {fs0 : FsState} {tr0 : List TraceEvent}
    {pc : BitVec 64} {spDrop : Nat} {env : PanicSymEnv}
    (hsafe : PanicSafeFrom P addrs pc spDrop env) :
    ∀ s : State, s.pc = pc → PanicWalkInv P addrs sp0 fs0 tr0 spDrop s → env.Holds s →
      ∃ sf, Steps P s sf ∧ sf.pc = addrs.abortAddr ∧
        PanicAbortPre P addrs sf ∧ sf.fs = fs0 ∧ sf.trace = tr0 := by
  induction hsafe with
  | atAbort spDrop env _ =>
    intro s hpc hinv _
    exact ⟨s, Steps.refl s, hpc, hinv.toAbortPre, hinv.fsEq, hinv.traceEq⟩
  | b pc off spDrop env hfetch _ ih =>
    intro s hpc hinv henv
    let s' := s.setPC (pc + off)
    have hev : P.evalInst (.b off) s = s' := by
      simp [s', Program.evalInst, execInstWithSvc, hpc]
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ := ih s' rfl (hinv.withPC _) (PanicSymEnv.holds_setPC henv _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | bl pc off spDrop env hfetch _ ih =>
    intro s hpc hinv henv
    let s' := (s.writeReg64 .lr (pc + 4#64)).setPC (pc + off)
    have hev : P.evalInst (.bl off) s = s' := by
      simp [s', Program.evalInst, execInstWithSvc, hpc]
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl ((hinv.withRegNotSp .lr rfl _).withPC _)
        (PanicSymEnv.holds_setPC (PanicSymEnv.holds_writeReg64_erase henv .lr _) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | bCond pc off cond spDrop env hfetch _ _ ihT ihF =>
    intro s hpc hinv henv
    by_cases hc : ConditionHolds cond s.pstate = true
    · let s' := s.setPC (pc + off)
      have hev : P.evalInst (.bCond cond off) s = s' := by
        simp [s', Program.evalInst, execInstWithSvc, hc, hpc]
      obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ := ihT s' rfl (hinv.withPC _) (PanicSymEnv.holds_setPC henv _)
      exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
    · let s' := s.setPC (pc + 4#64)
      have hev : P.evalInst (.bCond cond off) s = s' := by
        simp [s', Program.evalInst, execInstWithSvc, hc, State.advancePC, State.setPC, hpc]
      obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ := ihF s' rfl (hinv.withPC _) (PanicSymEnv.holds_setPC henv _)
      exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | cbz pc off w isNZ rt spDrop env hfetch _ _ ihT ihF =>
    intro s hpc hinv henv
    cases hc : (if isNZ then (s.readReg w rt == 0#64) != true else s.readReg w rt == 0#64) with
    | true =>
      let s' := s.setPC (pc + off)
      have hev : P.evalInst (.cbz w isNZ rt off) s = s' := by
        dsimp only [s', Program.evalInst, execInstWithSvc]
        rw [hc]; simp only [↓reduceIte, hpc]
      obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ := ihT s' rfl (hinv.withPC _) (PanicSymEnv.holds_setPC henv _)
      exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
    | false =>
      let s' := s.setPC (pc + 4#64)
      have hev : P.evalInst (.cbz w isNZ rt off) s = s' := by
        dsimp only [s', Program.evalInst, execInstWithSvc]
        rw [hc]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact advancePC_eq_setPC (by rw [hpc])
      obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ := ihF s' rfl (hinv.withPC _) (PanicSymEnv.holds_setPC henv _)
      exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | subSp pc imm12 spDrop env hfetch hal hdrop _ ih =>
    intro s hpc hinv henv
    let s' := (s.writeReg64 .sp (s.sp - imm12.zeroExtend 64)).setPC (pc + 4#64)
    have hsub : evalAddSub .W64 .SUB s.sp (imm12.zeroExtend 64) none = (s.sp - imm12.zeroExtend 64, none) := by
      simp only [evalAddSub, AddWithCarry64, Bool.false_eq_true, ↓reduceIte]
      refine Prod.ext ?_ rfl
      bv_omega
    have hev : P.evalInst (.addSubImm .W64 .SUB .sp .sp imm12 false) s = s' := by
      dsimp only [s', Program.evalInst, execInstWithSvc, execAddSubImm]
      have hr : s.readReg .W64 .sp = s.sp := rfl
      rw [hr]
      simp only [Bool.false_eq_true, ↓reduceIte, hsub, State.writeReg]
      exact advancePC_eq_setPC (by simp [State.writeReg64, hpc])
    have hsp' : s'.sp = sp0 - BitVec.ofNat 64 (spDrop + imm12.toNat) := by
      change s.sp - imm12.zeroExtend 64 = sp0 - BitVec.ofNat 64 (spDrop + imm12.toNat)
      rw [hinv.spEq]
      bv_omega
    have hspAl' : s'.spAligned = true := by
      have himm15 : (imm12.zeroExtend 64 &&& 15#64 == 0#64) = true :=
        bv64_and15_eq_zero_of_mod16 (by simpa using hal)
      exact s.spAligned_sub (imm12.zeroExtend 64) hinv.spAligned himm15
    have hinv' : PanicWalkInv P addrs sp0 fs0 tr0 (spDrop + imm12.toNat) s' :=
      { hinv with spAligned := hspAl', spEq := hsp', dropLe := hdrop }
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl hinv' (PanicSymEnv.holds_setPC (PanicSymEnv.holds_writeReg64_erase henv .sp _) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | stpPreSp pc off rt1 rt2 spDrop env hfetch hge16 hal hdrop _ ih =>
    intro s hpc hinv henv
    let d := (0#64 - off).toNat
    have hd16 : 16 ≤ d := hge16
    have hdrop' : spDrop + d ≤ 0x100 := hdrop
    have hsp_off : s.sp + off = sp0 - BitVec.ofNat 64 (spDrop + d) := by
      rw [hinv.spEq]; dsimp only [d]; bv_omega
    have hsp_off8 : s.sp + off + 8#64 = sp0 - BitVec.ofNat 64 (spDrop + d - 8) := by
      rw [hsp_off]; bv_omega
    have hcw0 : s.mem.canWrite (s.sp + off) 8 = true := by
      rw [hsp_off]; exact hinv.stackRW.canWrite_sub (off := spDrop + d) (by omega) (by omega)
    have hcw1 : s.mem.canWrite (s.sp + off + 8#64) 8 = true := by
      rw [hsp_off8]; exact hinv.stackRW.canWrite_sub (off := spDrop + d - 8) (by omega) (by omega)
    let m1 := s.mem.write64 (s.sp + off) (s.readReg64 rt1)
    let m2 := m1.write64 (s.sp + off + 8#64) (s.readReg64 rt2)
    let s' := ((s.setMem m2).writeReg64 .sp (s.sp + off)).setPC (pc + 4#64)
    have hev : P.evalInst (.stp .W64 rt1 rt2 (.PreIndex .sp off)) s = s' := by
      dsimp only [s', m2, m1, Program.evalInst, execInstWithSvc, execStp]
      have hchk : checkAddrSPAligned s (.PreIndex .sp off) = true := hinv.spAligned
      simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, State.readReg64,
        hcw0, hcw1, Bool.and_self, Memory.writeSized, MemWidth.bytes]
      exact advancePC_eq_setPC (by simp [State.writeReg64, State.setMem, hpc])
    have hinv1 := hinv.withWriteSized .X64 (s.sp + off) (s.readReg64 rt1) hcw0 (fun i hi => by
      rw [hsp_off]; exact hinv.stackRW.inRegion_sub (off := spDrop + d) (by omega) (by change 8 ≤ _; omega) hi)
    have hcw1' : m1.canWrite (s.sp + off + 8#64) 8 = true := by
      rw [hsp_off8]; exact hinv1.stackRW.canWrite_sub (off := spDrop + d - 8) (by omega) (by omega)
    have hinv2 := hinv1.withWriteSized .X64 (s.sp + off + 8#64) (s.readReg64 rt2) hcw1' (fun i hi => by
      rw [hsp_off8]; exact hinv1.stackRW.inRegion_sub (off := spDrop + d - 8) (by omega) (by change 8 ≤ _; omega) hi)
    have hspAl' : s'.spAligned = true := by
      have hoff15 : ((0#64 - off) &&& 15#64 == 0#64) = true := bv64_and15_eq_zero_of_mod16 hal
      have hsub_eq : s.sp + off = s.sp - (0#64 - off) := by bv_omega
      change ((s.sp + off) &&& 15#64 == 0#64) = true
      rw [hsub_eq]
      exact s.spAligned_sub (0#64 - off) hinv.spAligned hoff15
    have hinv' : PanicWalkInv P addrs sp0 fs0 tr0 (spDrop + d) s' :=
      { hinv2 with spAligned := hspAl', spEq := hsp_off, dropLe := hdrop }
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl hinv' (PanicSymEnv.holds_setPC (PanicSymEnv.holds_writeReg64_erase (PanicSymEnv.holds_setMem henv m2) .sp _) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | stpOffSp pc off rt1 rt2 spDrop env hfetch hbound _ ih =>
    intro s hpc hinv henv
    have hea0 : s.sp + off = sp0 - BitVec.ofNat 64 (spDrop - off.toNat) := by
      rw [hinv.spEq]; bv_omega
    have hea1 : s.sp + off + 8#64 = sp0 - BitVec.ofNat 64 (spDrop - off.toNat - 8) := by
      rw [hea0]; bv_omega
    have hcw0 : s.mem.canWrite (s.sp + off) 8 = true := by
      rw [hea0]; exact hinv.stackRW.canWrite_sub (off := spDrop - off.toNat) (by have := hinv.dropLe; omega) (by omega)
    have hcw1 : s.mem.canWrite (s.sp + off + 8#64) 8 = true := by
      rw [hea1]; exact hinv.stackRW.canWrite_sub (off := spDrop - off.toNat - 8) (by have := hinv.dropLe; omega) (by omega)
    let m1 := s.mem.write64 (s.sp + off) (s.readReg64 rt1)
    let m2 := m1.write64 (s.sp + off + 8#64) (s.readReg64 rt2)
    let s' := (s.setMem m2).setPC (pc + 4#64)
    have hev : P.evalInst (.stp .W64 rt1 rt2 (.Offset .sp off)) s = s' := by
      dsimp only [s', m2, m1, Program.evalInst, execInstWithSvc, execStp]
      have hchk : checkAddrSPAligned s (.Offset .sp off) = true := hinv.spAligned
      simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, State.readReg64,
        hcw0, hcw1, Bool.and_self, Memory.writeSized, MemWidth.bytes]
      exact advancePC_eq_setPC (by simp [State.setMem, hpc])
    have hinv1 := hinv.withWriteSized .X64 (s.sp + off) (s.readReg64 rt1) hcw0 (fun i hi => by
      rw [hea0]; exact hinv.stackRW.inRegion_sub (off := spDrop - off.toNat) (by have := hinv.dropLe; omega) (by change 8 ≤ _; omega) hi)
    have hcw1' : m1.canWrite (s.sp + off + 8#64) 8 = true := by
      rw [hea1]; exact hinv1.stackRW.canWrite_sub (off := spDrop - off.toNat - 8) (by have := hinv.dropLe; omega) (by omega)
    have hinv2 := hinv1.withWriteSized .X64 (s.sp + off + 8#64) (s.readReg64 rt2) hcw1' (fun i hi => by
      rw [hea1]; exact hinv1.stackRW.inRegion_sub (off := spDrop - off.toNat - 8) (by have := hinv.dropLe; omega) (by change 8 ≤ _; omega) hi)
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl (hinv2.withPC _) (PanicSymEnv.holds_setPC (PanicSymEnv.holds_setMem henv m2) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | strOffSp pc off sz rt spDrop env hfetch hbound _ ih =>
    intro s hpc hinv henv
    have hea : s.sp + off = sp0 - BitVec.ofNat 64 (spDrop - off.toNat) := by
      rw [hinv.spEq]; bv_omega
    have hcw : s.mem.canWrite (s.sp + off) sz.bytes = true := by
      rw [hea]; exact hinv.stackRW.canWrite_sub (off := spDrop - off.toNat) (by have := hinv.dropLe; omega) (by omega)
    let m1 := s.mem.writeSized sz (s.sp + off) (s.readReg64 rt)
    let s' := (s.setMem m1).setPC (pc + 4#64)
    have hev : P.evalInst (.str sz rt (.Offset .sp off)) s = s' := by
      dsimp only [s', m1, Program.evalInst, execInstWithSvc, execStr]
      have hchk : checkAddrSPAligned s (.Offset .sp off) = true := hinv.spAligned
      simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, State.readReg64, hcw]
      exact advancePC_eq_setPC (by simp [State.setMem, hpc])
    have hinv1 := hinv.withWriteSized sz (s.sp + off) (s.readReg64 rt) hcw (fun i hi => by
      rw [hea]; exact hinv.stackRW.inRegion_sub (off := spDrop - off.toNat) (by have := hinv.dropLe; omega) (by omega) hi)
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl (hinv1.withPC _) (PanicSymEnv.holds_setPC (PanicSymEnv.holds_setMem henv m1) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | adr pc off page rd spDrop env hfetch hnotSp _ ih =>
    intro s hpc hinv henv
    let v := (if page then pc &&& 0xfffffffffffff000#64 else pc) + off
    let s' := (s.writeReg64 rd v).setPC (pc + 4#64)
    have hev : P.evalInst (.adr page rd off) s = s' := by
      dsimp only [s', v, Program.evalInst, execInstWithSvc]
      rw [hpc]
      exact advancePC_eq_setPC (by simp [State.writeReg64, hpc])
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl ((hinv.withRegNotSp rd hnotSp v).withPC _)
        (PanicSymEnv.holds_setPC (PanicSymEnv.holds_writeReg64_set_notSp henv rd hnotSp v (.constVal v) rfl) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | addSubImmConst pc rd rn imm12 v spDrop env hfetch hnotSp hlook _ ih =>
    intro s hpc hinv henv
    have hrn : s.readReg64 rn = v := PanicSymEnv.lookup_holds henv hlook
    let v' := v + imm12.zeroExtend 64
    let s' := (s.writeReg64 rd v').setPC (pc + 4#64)
    have hev : P.evalInst (.addSubImm .W64 .ADD rd rn imm12 false) s = s' :=
      evalInst_addImm64_eq (by rw [hrn]) (by rw [hpc])
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl ((hinv.withRegNotSp rd hnotSp v').withPC _)
        (PanicSymEnv.holds_setPC (PanicSymEnv.holds_writeReg64_set_notSp henv rd hnotSp v' (.constVal v') rfl) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | addSubImmPure pc w op rd rn imm12 sh spDrop env hfetch hnotSp _ ih =>
    intro s hpc hinv henv
    let x := s.readReg w rn
    let imm : BitVec 64 := if sh then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
    let res := evalAddSub w op x imm none
    let s1 := s.writeReg w rd res.1
    let s2 := match res.2 with | some ps => s1.setPState ps | none => s1
    let s' := s2.setPC (pc + 4#64)
    have hev : P.evalInst (.addSubImm w op rd rn imm12 sh) s = s' := by
      dsimp only [s', s2, s1, res, imm, x, Program.evalInst, execInstWithSvc, execAddSubImm]
      cases res.2 <;> exact advancePC_eq_setPC (by simp [State.setPState, State.writeReg, State.writeReg64, hpc])
    have hinv' : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s' := by
      have h1 := hinv.withRegWNotSp w rd hnotSp res.1
      have h2 : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s2 := by
        dsimp only [s2]; cases res.2 with | none => exact h1 | some ps => exact h1.withPState ps
      exact h2.withPC _
    have henv' : (env.erase rd).Holds s' := by
      have h1 := PanicSymEnv.holds_writeReg_erase henv w rd res.1
      have h2 : (env.erase rd).Holds s2 := by
        dsimp only [s2]; cases res.2 with | none => exact h1 | some ps => exact PanicSymEnv.holds_setPState h1 ps
      exact PanicSymEnv.holds_setPC h2 _
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ := ih s' rfl hinv' henv'
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | andMask8 pc rd rn spDrop env hfetch hnotSp _ ih =>
    intro s hpc hinv henv
    let v' := s.readReg64 rn &&& 0xff#64
    let s' := (s.writeReg64 rd v').setPC (pc + 4#64)
    have hev : P.evalInst (.logicalImm .W64 .AND rd rn 0xff#64) s = s' := by
      dsimp only [s', v', Program.evalInst, execInstWithSvc, execLogicalImm, evalLogical,
        State.readReg, State.writeReg]
      exact advancePC_eq_setPC (by simp [State.writeReg64, hpc])
    have hlt : v'.toNat < 256 := by
      dsimp only [v']
      rw [BitVec.toNat_and]
      have hle : (s.readReg64 rn).toNat &&& (0xff#64 : BitVec 64).toNat ≤ (0xff#64 : BitVec 64).toNat :=
        Nat.and_le_right
      have h255 : (0xff#64 : BitVec 64).toNat = 255 := rfl
      omega
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl ((hinv.withRegNotSp rd hnotSp v').withPC _)
        (PanicSymEnv.holds_setPC (PanicSymEnv.holds_writeReg64_set_notSp henv rd hnotSp v' .masked8 hlt) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | logicalImmPure pc mask w op rd rn spDrop env hfetch hnotSp _ ih =>
    intro s hpc hinv henv
    let res := evalLogical w op (s.readReg w rn) mask s.pstate
    let s1 := s.writeReg w rd res.1
    let s2 := match res.2 with | some ps => s1.setPState ps | none => s1
    let s' := s2.setPC (pc + 4#64)
    have hev : P.evalInst (.logicalImm w op rd rn mask) s = s' := by
      dsimp only [s', s2, s1, res, Program.evalInst, execInstWithSvc, execLogicalImm]
      cases res.2 <;> exact advancePC_eq_setPC (by simp [State.setPState, State.writeReg, State.writeReg64, hpc])
    have hinv' : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s' := by
      have h1 := hinv.withRegWNotSp w rd hnotSp res.1
      have h2 : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s2 := by
        dsimp only [s2]; cases res.2 with | none => exact h1 | some ps => exact h1.withPState ps
      exact h2.withPC _
    have henv' : (env.erase rd).Holds s' := by
      have h1 := PanicSymEnv.holds_writeReg_erase henv w rd res.1
      have h2 : (env.erase rd).Holds s2 := by
        dsimp only [s2]; cases res.2 with | none => exact h1 | some ps => exact PanicSymEnv.holds_setPState h1 ps
      exact PanicSymEnv.holds_setPC h2 _
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ := ih s' rfl hinv' henv'
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | moveWidePure pc w op rd imm16 hw spDrop env hfetch hnotSp _ ih =>
    intro s hpc hinv henv
    let shifted : BitVec 64 := (imm16.zeroExtend 64) <<< hw
    let res : BitVec 64 :=
      match op with
      | .MOVZ => shifted
      | .MOVN => ~~~shifted
      | .MOVK => (s.readReg w rd &&& ~~~(0xffff#64 <<< hw)) ||| shifted
    let s' := (s.writeReg w rd res).setPC (pc + 4#64)
    have hev : P.evalInst (.moveWide w op rd imm16 hw) s = s' := by
      dsimp only [s', res, shifted, Program.evalInst, execInstWithSvc, execMoveWide]
      cases op <;> exact advancePC_eq_setPC (by cases w <;> simp [State.writeReg, State.writeReg64, hpc])
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl ((hinv.withRegWNotSp w rd hnotSp res).withPC _)
        (PanicSymEnv.holds_setPC (PanicSymEnv.holds_writeReg_erase henv w rd res) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | logicalShiftPure pc w op rd rn rm sh amt spDrop env hfetch hnotSp _ ih =>
    intro s hpc hinv henv
    let res := evalLogical w op (s.readReg w rn) (shiftVal w (s.readReg w rm) sh amt) s.pstate
    let s1 := s.writeReg w rd res.1
    let s2 := match res.2 with | some ps => s1.setPState ps | none => s1
    let s' := s2.setPC (pc + 4#64)
    have hev : P.evalInst (.logicalShift w op rd rn rm sh amt) s = s' := by
      dsimp only [s', s2, s1, res, Program.evalInst, execInstWithSvc, execLogicalShift]
      cases res.2 <;> exact advancePC_eq_setPC (by simp [State.setPState, State.writeReg, State.writeReg64, hpc])
    have hinv' : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s' := by
      have h1 := hinv.withRegWNotSp w rd hnotSp res.1
      have h2 : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s2 := by
        dsimp only [s2]; cases res.2 with | none => exact h1 | some ps => exact h1.withPState ps
      exact h2.withPC _
    have henv' : (env.erase rd).Holds s' := by
      have h1 := PanicSymEnv.holds_writeReg_erase henv w rd res.1
      have h2 : (env.erase rd).Holds s2 := by
        dsimp only [s2]; cases res.2 with | none => exact h1 | some ps => exact PanicSymEnv.holds_setPState h1 ps
      exact PanicSymEnv.holds_setPC h2 _
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ := ih s' rfl hinv' henv'
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | addSubShiftPure pc w op rd rn rm sh amt spDrop env hfetch hnotSp _ ih =>
    intro s hpc hinv henv
    let res := evalAddSub w op (s.readReg w rn) (shiftVal w (s.readReg w rm) sh amt) none
    let s1 := s.writeReg w rd res.1
    let s2 := match res.2 with | some ps => s1.setPState ps | none => s1
    let s' := s2.setPC (pc + 4#64)
    have hev : P.evalInst (.addSubShift w op rd rn rm sh amt) s = s' := by
      dsimp only [s', s2, s1, res, Program.evalInst, execInstWithSvc, execAddSubShift]
      cases res.2 <;> exact advancePC_eq_setPC (by simp [State.setPState, State.writeReg, State.writeReg64, hpc])
    have hinv' : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s' := by
      have h1 := hinv.withRegWNotSp w rd hnotSp res.1
      have h2 : PanicWalkInv P addrs sp0 fs0 tr0 spDrop s2 := by
        dsimp only [s2]; cases res.2 with | none => exact h1 | some ps => exact h1.withPState ps
      exact h2.withPC _
    have henv' : (env.erase rd).Holds s' := by
      have h1 := PanicSymEnv.holds_writeReg_erase henv w rd res.1
      have h2 : (env.erase rd).Holds s2 := by
        dsimp only [s2]; cases res.2 with | none => exact h1 | some ps => exact PanicSymEnv.holds_setPState h1 ps
      exact PanicSymEnv.holds_setPC h2 _
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ := ih s' rfl hinv' henv'
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | ldrGot8 pc off v w rt rn spDrop env hfetch hnotSpRt hnotSpRn hlook hmem _ ih =>
    intro s hpc hinv henv
    have hrn : s.readReg64 rn = v := PanicSymEnv.lookup_holds henv hlook
    have hcr : s.mem.canRead (v + off) 8 = true := hinv.gotRead8CanRead (v + off) hmem
    have hspRn : checkRegSPAligned s rn = true := by
      cases rn <;> simp [regIsNotSp, checkRegSPAligned] at hnotSpRn ⊢
    let val := s.mem.readSized .X64 false (v + off)
    let s' := (s.writeReg w rt val).setPC (pc + 4#64)
    have hev : P.evalInst (.ldr w .X64 false rt (.Offset rn off)) s = s' := by
      dsimp only [s', val, Program.evalInst, execInstWithSvc, execLdr]
      have hchk : checkAddrSPAligned s (.Offset rn off) = true := hspRn
      simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, hrn, hcr,
        MemWidth.bytes]
      exact advancePC_eq_setPC (by cases w <;> simp [State.writeReg, State.writeReg64, hpc])
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl ((hinv.withRegWNotSp w rt hnotSpRt val).withPC _)
        (PanicSymEnv.holds_setPC (PanicSymEnv.holds_writeReg_erase henv w rt val) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | ldrRoTable32 pc v w signed rt rn rm spDrop env hfetch hnotSpRt hnotSpRn hlookRn hlookRm hmem _ ih =>
    intro s hpc hinv henv
    have hrn : s.readReg64 rn = v := PanicSymEnv.lookup_holds henv hlookRn
    have hrm : (s.readReg64 rm).toNat < 256 := PanicSymEnv.lookup_holds henv hlookRm
    have hspRn : checkRegSPAligned s rn = true := by
      cases rn <;> simp [regIsNotSp, checkRegSPAligned] at hnotSpRn ⊢
    let ea := v + (s.readReg64 rm <<< 2)
    have hcr : s.mem.canRead ea 4 = true :=
      canRead_of_readable (hinv.roTable32Readable v hmem) fun k hk => by
        unfold InRegion
        dsimp only [ea]
        have hsub : v + (s.readReg64 rm <<< 2) + BitVec.ofNat 64 k - v =
            (s.readReg64 rm <<< 2) + BitVec.ofNat 64 k := by bv_omega
        rw [hsub]
        bv_omega
    let val := s.mem.readSized .W32 signed ea
    let s' := (s.writeReg w rt val).setPC (pc + 4#64)
    have hev : P.evalInst (.ldr w .W32 signed rt (.RegOffset rn rm .UXTX 2)) s = s' := by
      dsimp only [ea] at hcr
      dsimp only [s', val, ea, Program.evalInst, execInstWithSvc, execLdr]
      have hchk : checkAddrSPAligned s (.RegOffset rn rm .UXTX 2) = true := hspRn
      simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, extendVal,
        hrn, hcr, MemWidth.bytes]
      exact advancePC_eq_setPC (by cases w <;> simp [State.writeReg, State.writeReg64, hpc])
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl ((hinv.withRegWNotSp w rt hnotSpRt val).withPC _)
        (PanicSymEnv.holds_setPC (PanicSymEnv.holds_writeReg_erase henv w rt val) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩
  | ldrRoTable64 pc v w signed rt rn rm spDrop env hfetch hnotSpRt hnotSpRn hlookRn hlookRm hmem _ ih =>
    intro s hpc hinv henv
    have hrn : s.readReg64 rn = v := PanicSymEnv.lookup_holds henv hlookRn
    have hrm : (s.readReg64 rm).toNat < 256 := PanicSymEnv.lookup_holds henv hlookRm
    have hspRn : checkRegSPAligned s rn = true := by
      cases rn <;> simp [regIsNotSp, checkRegSPAligned] at hnotSpRn ⊢
    let ea := v + (s.readReg64 rm <<< 3)
    have hcr : s.mem.canRead ea 8 = true :=
      canRead_of_readable (hinv.roTable64Readable v hmem) fun k hk => by
        unfold InRegion
        dsimp only [ea]
        have hsub : v + (s.readReg64 rm <<< 3) + BitVec.ofNat 64 k - v =
            (s.readReg64 rm <<< 3) + BitVec.ofNat 64 k := by bv_omega
        rw [hsub]
        bv_omega
    let val := s.mem.readSized .X64 signed ea
    let s' := (s.writeReg w rt val).setPC (pc + 4#64)
    have hev : P.evalInst (.ldr w .X64 signed rt (.RegOffset rn rm .UXTX 3)) s = s' := by
      dsimp only [ea] at hcr
      dsimp only [s', val, ea, Program.evalInst, execInstWithSvc, execLdr]
      have hchk : checkAddrSPAligned s (.RegOffset rn rm .UXTX 3) = true := hspRn
      simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, evalAddrMode, extendVal,
        hrn, hcr, MemWidth.bytes]
      exact advancePC_eq_setPC (by cases w <;> simp [State.writeReg, State.writeReg64, hpc])
    obtain ⟨sf, hsteps, hpc', hab, hfs, htr⟩ :=
      ih s' rfl ((hinv.withRegWNotSp w rt hnotSpRt val).withPC _)
        (PanicSymEnv.holds_setPC (PanicSymEnv.holds_writeReg_erase henv w rt val) _)
    exact ⟨sf, steps_exec hinv.codeLoaded hinv.running (hpc.symm ▸ hfetch) hev hsteps, hpc', hab, hfs, htr⟩

/-! ## 6. `F3PanicCode` Bundle and `WordTree` Validator (`checkF3PanicCode`) -/

/-- Complete layout-generic panic code certificate for a hook-free `Syscall.standard` `Program`:
    covers the 5 `musl` `abort` functions, the 2 abort-only `rdl_shim.S` handlers, and every
    linked Rust panic entry point in `addrs.panicEntries`. -/
structure F3PanicCode (P : Program) (addrs : F3PanicAddrs) : Prop where
  no_hooks  : P.NoHooks
  svc_eq    : P.svc = Syscall.standard
  abortCode : CodeChunks P (f3AbortChunks addrs)
  shimCode  : CodeChunks P (f3PanicShimChunks addrs)
  entriesOk : ∀ pc ∈ addrs.panicEntries, PanicSafeFrom P addrs pc 0 []

/-- Fuel-bounded `WordTree` abstract checker certifying `PanicSafeFrom P addrs pc spDrop env`. -/
@[expose] def checkPanicWordTree (base : BitVec 64) (t : WordTree) (addrs : F3PanicAddrs) :
    Nat → BitVec 64 → Nat → PanicSymEnv → Bool
  | 0, pc, spDrop, _ => (pc == addrs.abortAddr) && Nat.ble spDrop 0x100
  | fuel + 1, pc, spDrop, env =>
    if pc == addrs.abortAddr then
      Nat.ble spDrop 0x100
    else
      match t.fetchDecodeAt (pc - base).toNat with
      | none => false
      | some inst =>
        match inst with
        | .b off =>
          checkPanicWordTree base t addrs fuel (pc + off) spDrop env
        | .bl off =>
          checkPanicWordTree base t addrs fuel (pc + off) spDrop (env.erase .lr)
        | .bCond _ off =>
          checkPanicWordTree base t addrs fuel (pc + off) spDrop env &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop env
        | .cbz _ _ _ off =>
          checkPanicWordTree base t addrs fuel (pc + off) spDrop env &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop env
        | .addSubImm .W64 .SUB .sp .sp imm12 false =>
          (imm12.toNat % 16 == 0) &&
          Nat.ble (spDrop + imm12.toNat) 0x100 &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) (spDrop + imm12.toNat) (env.erase .sp)
        | .stp .W64 _ _ (.PreIndex .sp off) =>
          let d := (0#64 - off).toNat
          Nat.ble 16 d &&
          (d % 16 == 0) &&
          Nat.ble (spDrop + d) 0x100 &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) (spDrop + d) (env.erase .sp)
        | .stp .W64 _ _ (.Offset .sp off) =>
          Nat.ble (off.toNat + 16) spDrop &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop env
        | .str sz _ (.Offset .sp off) =>
          Nat.ble (off.toNat + sz.bytes) spDrop &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop env
        | .adr page rd off =>
          regIsNotSp rd &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop
            (env.set rd (.constVal ((if page then pc &&& 0xfffffffffffff000#64 else pc) + off)))
        | .addSubImm .W64 .ADD rd rn imm12 false =>
          if regIsNotSp rd then
            match env.lookup rn with
            | some (.constVal v) =>
              checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop
                (env.set rd (.constVal (v + imm12.zeroExtend 64)))
            | _ =>
              checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.erase rd)
          else false
        | .addSubImm _ _ rd _ _ _ =>
          regIsNotSp rd &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.erase rd)
        | .logicalImm .W64 .AND rd _ mask =>
          if regIsNotSp rd then
            if mask == 0xff#64 then
              checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.set rd .masked8)
            else
              checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.erase rd)
          else false
        | .logicalImm _ _ rd _ _ =>
          regIsNotSp rd &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.erase rd)
        | .moveWide _ _ rd _ _ =>
          regIsNotSp rd &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.erase rd)
        | .logicalShift _ _ rd _ _ _ _ =>
          regIsNotSp rd &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.erase rd)
        | .addSubShift _ _ rd _ _ _ _ =>
          regIsNotSp rd &&
          checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.erase rd)
        | .ldr _ .X64 false rt (.Offset rn off) =>
          regIsNotSp rt && regIsNotSp rn &&
          match env.lookup rn with
          | some (.constVal v) =>
            addrs.gotRead8Addrs.contains (v + off) &&
            checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.erase rt)
          | _ => false
        | .ldr _ .W32 _ rt (.RegOffset rn rm .UXTX 2) =>
          regIsNotSp rt && regIsNotSp rn &&
          match env.lookup rn, env.lookup rm with
          | some (.constVal v), some .masked8 =>
            addrs.roAssertTable32Addrs.contains v &&
            checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.erase rt)
          | _, _ => false
        | .ldr _ .X64 _ rt (.RegOffset rn rm .UXTX 3) =>
          regIsNotSp rt && regIsNotSp rn &&
          match env.lookup rn, env.lookup rm with
          | some (.constVal v), some .masked8 =>
            addrs.roAssertTable64Addrs.contains v &&
            checkPanicWordTree base t addrs fuel (pc + 4#64) spDrop (env.erase rt)
          | _, _ => false
        | _ => false

/-- Boolean `WordTree` validator ($O(k \log N)$) discharging `F3PanicCode P addrs`. -/
@[expose] def checkF3PanicCode (addrs : F3PanicAddrs) (base : BitVec 64) (t : WordTree)
    (fuel : Nat := 80) : Bool :=
  (f3AbortChunks addrs).all (checkCodeChunk base t) &&
  (f3PanicShimChunks addrs).all (checkCodeChunk base t) &&
  addrs.panicEntries.all (fun pc => checkPanicWordTree base t addrs fuel pc 0 [])

private theorem panicSafeFrom_of_checkWordTree {P : Program} {t : WordTree} {addrs : F3PanicAddrs}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hext : ∀ sym, (P.externs sym).isNone = true)
    (hovr : ∀ sym, (P.overrides sym).isNone = true) :
    ∀ (fuel : Nat) (pc : BitVec 64) (spDrop : Nat) (env : PanicSymEnv),
      checkPanicWordTree P.base t addrs fuel pc spDrop env = true →
      PanicSafeFrom P addrs pc spDrop env
  | 0, pc, spDrop, env, h => by
    simp only [checkPanicWordTree, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, hle⟩
    exact .atAbort spDrop env (Nat.le_of_ble_eq_true hle)
  | fuel + 1, pc, spDrop, env, h => by
    unfold checkPanicWordTree at h
    by_cases hab : pc = addrs.abortAddr
    · subst hab
      simp only [beq_self_eq_true, ↓reduceIte] at h
      exact .atAbort spDrop env (Nat.le_of_ble_eq_true h)
    · have habF : (pc == addrs.abortAddr) = false := beq_false_of_ne hab
      simp only [habF, Bool.false_eq_true, ↓reduceIte] at h
      cases hdec : t.fetchDecodeAt (pc - P.base).toNat with
      | none => rw [hdec] at h; cases h
      | some inst =>
        rw [hdec] at h
        have hfetch : P.fetch pc = some inst := by
          have h1 := fetch_of_wordTree n hcode hwf hdec (pc - P.base).isLt
            (hookAtOff?_eq_none_of_isNone hext hovr _)
          have hpcEq : P.base + BitVec.ofNat 64 (pc - P.base).toNat = pc := by bv_omega
          rwa [hpcEq] at h1
        have ih : ∀ pc' d' e', checkPanicWordTree P.base t addrs fuel pc' d' e' = true →
            PanicSafeFrom P addrs pc' d' e' :=
          fun pc' d' e' h' =>
            panicSafeFrom_of_checkWordTree (addrs := addrs) n hcode hwf hext hovr fuel pc' d' e' h'
        cases inst with
        | b off => exact .b pc off spDrop env hfetch (ih _ _ _ h)
        | bl off => exact .bl pc off spDrop env hfetch (ih _ _ _ h)
        | bCond cond off =>
          simp only [Bool.and_eq_true] at h
          exact .bCond pc off cond spDrop env hfetch (ih _ _ _ h.1) (ih _ _ _ h.2)
        | cbz w isNZ rt off =>
          simp only [Bool.and_eq_true] at h
          exact .cbz pc off w isNZ rt spDrop env hfetch (ih _ _ _ h.1) (ih _ _ _ h.2)
        | adr page rd off =>
          simp only [Bool.and_eq_true] at h
          exact .adr pc off page rd spDrop env hfetch h.1 (ih _ _ _ h.2)
        | moveWide w op rd imm16 hw =>
          simp only [Bool.and_eq_true] at h
          exact .moveWidePure pc w op rd imm16 hw spDrop env hfetch h.1 (ih _ _ _ h.2)
        | logicalShift w op rd rn rm sh amt =>
          simp only [Bool.and_eq_true] at h
          exact .logicalShiftPure pc w op rd rn rm sh amt spDrop env hfetch h.1 (ih _ _ _ h.2)
        | addSubShift w op rd rn rm sh amt =>
          simp only [Bool.and_eq_true] at h
          exact .addSubShiftPure pc w op rd rn rm sh amt spDrop env hfetch h.1 (ih _ _ _ h.2)
        | addSubImm w op rd rn imm12 sh =>
          cases w <;> cases op <;> cases rd <;> cases rn <;> cases sh <;>
            dsimp only [] at h
          all_goals
            first
            | (simp only [Bool.and_eq_true, beq_iff_eq] at h
               exact .subSp pc imm12 spDrop env hfetch h.1.1 (Nat.le_of_ble_eq_true h.1.2)
                 (ih _ _ _ h.2))
            | (split at h
               · rename_i hns
                 cases hlook : env.lookup _ with
                 | none =>
                   rw [hlook] at h
                   exact .addSubImmPure pc _ _ _ _ _ _ spDrop env hfetch hns (ih _ _ _ h)
                 | some sv =>
                   rw [hlook] at h
                   cases sv with
                   | constVal v =>
                     exact .addSubImmConst pc _ _ imm12 v spDrop env hfetch hns hlook (ih _ _ _ h)
                   | masked8 =>
                     exact .addSubImmPure pc _ _ _ _ _ _ spDrop env hfetch hns (ih _ _ _ h)
               · cases h)
            | (simp only [Bool.and_eq_true] at h
               exact .addSubImmPure pc _ _ _ _ _ _ spDrop env hfetch h.1 (ih _ _ _ h.2))
        | logicalImm w op rd rn mask =>
          cases w <;> cases op <;> dsimp only [] at h
          all_goals
            first
            | (split at h
               · rename_i hns
                 split at h
                 · rename_i hm
                   have hmeq : mask = 0xff#64 := beq_iff_eq.mp hm
                   subst hmeq
                   exact .andMask8 pc rd rn spDrop env hfetch hns (ih _ _ _ h)
                 · exact .logicalImmPure pc mask _ _ rd rn spDrop env hfetch hns (ih _ _ _ h)
               · cases h)
            | (simp only [Bool.and_eq_true] at h
               exact .logicalImmPure pc mask _ _ rd rn spDrop env hfetch h.1 (ih _ _ _ h.2))
        | stp w rt1 rt2 addr =>
          cases w <;> cases addr <;> dsimp only [] at h
          all_goals
            first
            | (rename_i baseReg off
               cases baseReg <;> dsimp only [] at h
               · cases h
               · simp only [Bool.and_eq_true, beq_iff_eq] at h
                 first
                 | exact .stpPreSp pc off rt1 rt2 spDrop env hfetch
                     (Nat.le_of_ble_eq_true h.1.1.1) h.1.1.2 (Nat.le_of_ble_eq_true h.1.2)
                     (ih _ _ _ h.2)
                 | exact .stpOffSp pc off rt1 rt2 spDrop env hfetch
                     (Nat.le_of_ble_eq_true h.1) (ih _ _ _ h.2)
               · cases h)
            | cases h
        | str sz rt addr =>
          cases addr <;> dsimp only [] at h
          all_goals
            first
            | (rename_i baseReg off
               cases baseReg <;> dsimp only [] at h
               · cases h
               · simp only [Bool.and_eq_true] at h
                 exact .strOffSp pc off sz rt spDrop env hfetch
                   (Nat.le_of_ble_eq_true h.1) (ih _ _ _ h.2)
               · cases h)
            | cases h
        | ldr w sz signed rt addr =>
          cases sz with
          | B8 => cases h
          | H16 => cases h
          | W32 =>
            cases addr with
            | RegOffset rn rm ext amt =>
              cases ext with
              | UXTX =>
                cases amt with
                | succ a1 =>
                  cases a1 with
                  | succ a2 =>
                    cases a2 with
                    | zero =>
                      dsimp only [] at h
                      simp only [Bool.and_eq_true] at h
                      cases hln : env.lookup rn with
                      | none => rw [hln] at h; cases h.2
                      | some svn =>
                        rw [hln] at h
                        cases svn with
                        | masked8 => cases h.2
                        | constVal v =>
                          cases hlm : env.lookup rm with
                          | none => rw [hlm] at h; cases h.2
                          | some svm =>
                            rw [hlm] at h
                            cases svm with
                            | constVal _ => cases h.2
                            | masked8 =>
                              simp only [Bool.and_eq_true] at h
                              exact .ldrRoTable32 pc v w signed rt rn rm spDrop env hfetch
                                h.1.1 h.1.2 hln hlm (by simpa using h.2.1) (ih _ _ _ h.2.2)
                    | succ _ => cases h
                  | zero => cases h
                | zero => cases h
              | _ => cases h
            | _ => cases h
          | X64 =>
            cases signed with
            | false =>
              cases addr with
              | Offset rn off =>
                dsimp only [] at h
                simp only [Bool.and_eq_true] at h
                cases hlook : env.lookup rn with
                | none => rw [hlook] at h; cases h.2
                | some sv =>
                  rw [hlook] at h
                  cases sv with
                  | masked8 => cases h.2
                  | constVal v =>
                    simp only [Bool.and_eq_true] at h
                    exact .ldrGot8 pc off v w rt rn spDrop env hfetch h.1.1 h.1.2 hlook
                      (by simpa using h.2.1) (ih _ _ _ h.2.2)
              | RegOffset rn rm ext amt =>
                cases ext with
                | UXTX =>
                  cases amt with
                  | succ a1 =>
                    cases a1 with
                    | succ a2 =>
                      cases a2 with
                      | succ a3 =>
                        cases a3 with
                        | zero =>
                          dsimp only [] at h
                          simp only [Bool.and_eq_true] at h
                          cases hln : env.lookup rn with
                          | none => rw [hln] at h; cases h.2
                          | some svn =>
                            rw [hln] at h
                            cases svn with
                            | masked8 => cases h.2
                            | constVal v =>
                              cases hlm : env.lookup rm with
                              | none => rw [hlm] at h; cases h.2
                              | some svm =>
                                rw [hlm] at h
                                cases svm with
                                | constVal _ => cases h.2
                                | masked8 =>
                                  simp only [Bool.and_eq_true] at h
                                  exact .ldrRoTable64 pc v w false rt rn rm spDrop env hfetch
                                    h.1.1 h.1.2 hln hlm (by simpa using h.2.1) (ih _ _ _ h.2.2)
                        | succ _ => cases h
                      | zero => cases h
                    | zero => cases h
                  | zero => cases h
                | _ => cases h
              | _ => cases h
            | true =>
              cases addr with
              | RegOffset rn rm ext amt =>
                cases ext with
                | UXTX =>
                  cases amt with
                  | succ a1 =>
                    cases a1 with
                    | succ a2 =>
                      cases a2 with
                      | succ a3 =>
                        cases a3 with
                        | zero =>
                          dsimp only [] at h
                          simp only [Bool.and_eq_true] at h
                          cases hln : env.lookup rn with
                          | none => rw [hln] at h; cases h.2
                          | some svn =>
                            rw [hln] at h
                            cases svn with
                            | masked8 => cases h.2
                            | constVal v =>
                              cases hlm : env.lookup rm with
                              | none => rw [hlm] at h; cases h.2
                              | some svm =>
                                rw [hlm] at h
                                cases svm with
                                | constVal _ => cases h.2
                                | masked8 =>
                                  simp only [Bool.and_eq_true] at h
                                  exact .ldrRoTable64 pc v w true rt rn rm spDrop env hfetch
                                    h.1.1 h.1.2 hln hlm (by simpa using h.2.1) (ih _ _ _ h.2.2)
                        | succ _ => cases h
                      | zero => cases h
                    | zero => cases h
                  | zero => cases h
                | _ => cases h
              | _ => cases h
        | _ => cases h

private theorem codeChunks_of_all_panic {P : Program} {b : BitVec 64} {t : WordTree}
    (hc : ∀ {c : CodeChunk}, checkCodeChunk b t c = true → c.holds P) :
    ∀ {cs : List CodeChunk}, cs.all (checkCodeChunk b t) = true → CodeChunks P cs
  | [], _ => trivial
  | [_], h => hc (by simpa using h)
  | _ :: _ :: _, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    exact ⟨hc h.1, codeChunks_of_all_panic hc h.2⟩

/-- Discharge `F3PanicCode P addrs` from a single `rfl_kernel` / `decide` check of
    `checkF3PanicCode addrs P.base t = true`. -/
theorem f3PanicCode_of_wordTree {P : Program} {addrs : F3PanicAddrs} {t : WordTree}
    (n : Nat) (fuel : Nat := 80)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkF3PanicCode addrs P.base t fuel = true) :
    F3PanicCode P addrs := by
  have hno_hooks : P.NoHooks := Program.NoHooks.of_eq_none
    (funext fun s => Option.isNone_iff_eq_none.mp (hext s))
    (funext fun s => Option.isNone_iff_eq_none.mp (hovr s))
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  unfold checkF3PanicCode at hok
  simp only [Bool.and_eq_true] at hok
  rcases hok with ⟨⟨hab, hsh⟩, hent⟩
  exact
    { no_hooks := hno_hooks
      svc_eq := hsvc
      abortCode := codeChunks_of_all_panic hc hab
      shimCode := codeChunks_of_all_panic hc hsh
      entriesOk := fun pc hmem =>
        panicSafeFrom_of_checkWordTree n hcode hwf hext hovr fuel pc 0 []
          (List.all_eq_true.mp hent pc hmem) }

/-! ## 7. Top-Level Whole-Path Termination and `Program.pureMem` / `ProcessRunsTo` Theorems -/

/-- From any entry point in `addrs.allEntries` (`abort`, `rust_begin_unwind`,
    `__rust_alloc_error_handler`, or any linked `core`/`alloc` panic symbol in
    `addrs.panicEntries`), with arbitrary registers `x0..x30`, `pstate`, and `vregs`, execution
    under `P` terminates with `ExecStatus.Signaled 6#7`, preserving `fs` and `trace`. -/
theorem panicEntry_reaches_sigabrt {P : Program} {addrs : F3PanicAddrs} {s : State}
    (hcode : F3PanicCode P addrs)
    (hpc : s.pc ∈ addrs.allEntries)
    (hpre : PanicEntryPre P addrs s) :
    ∃ sf, Steps P s sf ∧ sf.status = .Signaled 6#7 ∧ sf.fs = s.fs ∧ sf.trace = s.trace := by
  have hwalk := PanicWalkInv.of_entryPre hpre
  simp only [F3PanicAddrs.allEntries, List.mem_cons] at hpc
  rcases hpc with hpc | hpc | hpc | hpc
  · exact musl_abort_to_sigabrt hcode.svc_eq hcode.abortCode hpc hwalk.toAbortPre
  · exact rdl_panic_shims_to_sigabrt hcode.svc_eq hcode.abortCode hcode.shimCode
      (Or.inl hpc) hwalk.toAbortPre
  · exact rdl_panic_shims_to_sigabrt hcode.svc_eq hcode.abortCode hcode.shimCode
      (Or.inr hpc) hwalk.toAbortPre
  · obtain ⟨sa, hsteps1, hpc_a, hab, hfs_a, htr_a⟩ :=
      panicSafeFrom_reaches_abort (hcode.entriesOk s.pc hpc) s rfl hwalk (fun _ hp => nomatch hp)
    obtain ⟨sf, hsteps2, hsig, hfs_f, htr_f⟩ :=
      musl_abort_to_sigabrt hcode.svc_eq hcode.abortCode hpc_a hab
    exact ⟨sf, hsteps1.trans hsteps2, hsig, hfs_f.trans hfs_a, htr_f.trans htr_a⟩

/-- Lift any `Steps P s sf` trace ending in `.Signaled sig` for a hook-free `Syscall.standard`
    program `P` directly to `Steps Program.pureMem s sf`. -/
theorem steps_toPureMem_of_signaled {P : Program} {s sf : State} {sig : BitVec 7}
    (hno : P.NoHooks)
    (hsvc : P.svc = Syscall.standard)
    (hsteps : Steps P s sf)
    (hsig : sf.status = .Signaled sig) :
    Steps Program.pureMem s sf := by
  induction hsteps with
  | refl s => exact Steps.refl s
  | @step s1 s2 s3 h1 h2 ih =>
    cases h1 with
    | @exec inst hr hf =>
      have hf' : Program.pureMem.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem at hf ⊢
        split at hf
        · contradiction
        · exact hf
      have hev : P.evalInst inst s1 = Program.pureMem.evalInst inst s1 := by
        simp only [Program.evalInst, Program.pureMem, Program.pureWithSvc, Program.ofSvc, hsvc]
      have ih2 := ih hsig
      rw [hev] at ih2
      exact Steps.step (Step.exec hr hf') ih2
    | halt_unmapped _ _ _ =>
      have heq := Steps.from_not_running h2 (by simp)
      subst heq
      simp at hsig
    | extern _ he _ _ =>
      rw [hno s1.pc] at he; cases he
    | extern_fault _ he _ =>
      rw [hno s1.pc] at he; cases he

/-- Direct `Program.pureMem` corollary of `panicEntry_reaches_sigabrt`. -/
theorem panicEntry_pureMem_reaches_sigabrt {P : Program} {addrs : F3PanicAddrs} {s : State}
    (hcode : F3PanicCode P addrs)
    (hpc : s.pc ∈ addrs.allEntries)
    (hpre : PanicEntryPre P addrs s) :
    ∃ sf, Steps Program.pureMem s sf ∧ sf.status = .Signaled 6#7 ∧
      sf.fs = s.fs ∧ sf.trace = s.trace := by
  obtain ⟨sf, hsteps, hsig, hfs, htr⟩ := panicEntry_reaches_sigabrt hcode hpc hpre
  exact ⟨sf, steps_toPureMem_of_signaled hcode.no_hooks hcode.svc_eq hsteps hsig, hsig, hfs, htr⟩

/-- Convert any `Steps prog s sf` reaching `.Signaled 6#7` into
    `ProcessRunsTo prog s (OutcomeMatchesProcess .aborted) oom`. -/
theorem processRunsTo_aborted_of_signaled6 {prog : Program} {s sf : State}
    {oom : State → Prop}
    (hsteps : Steps prog s sf)
    (hsig : sf.status = .Signaled 6#7) :
    ProcessRunsTo prog s (OutcomeMatchesProcess .aborted) oom := by
  have hexit : ProcessExitsWith prog s (ProcessOutcome.ofSignal 6#7 sf) :=
    ⟨sf, hsteps, Or.inr ⟨6#7, hsig, rfl⟩⟩
  refine ProcessRunsTo.of_exitsWith hexit ?_
  simp [OutcomeMatchesProcess, ProcessOutcome.ofSignal]

/-- Direct `ProcessRunsTo Program.pureMem s (OutcomeMatchesProcess .aborted)` theorem from any
    linked panic entry point in `addrs.allEntries`. -/
theorem panicEntry_processRunsTo_aborted {P : Program} {addrs : F3PanicAddrs} {s : State}
    {oom : State → Prop}
    (hcode : F3PanicCode P addrs)
    (hpc : s.pc ∈ addrs.allEntries)
    (hpre : PanicEntryPre P addrs s) :
    ProcessRunsTo Program.pureMem s (OutcomeMatchesProcess .aborted) oom := by
  obtain ⟨sf, hsteps, hsig, _, _⟩ := panicEntry_pureMem_reaches_sigabrt hcode hpc hpre
  exact processRunsTo_aborted_of_signaled6 hsteps hsig

end LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.PanicPath
