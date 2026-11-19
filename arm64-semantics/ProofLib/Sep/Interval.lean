/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Sep.Addr
public meta import Lean

/-!
# Sweep-Line Byte-Interval and Read-Only Subsumption Solver

Provides the `sep_interval` (`P ⊢ Q` and bi-equivalent `P = Q`) and `sep_interval_eq` (`P = Q`)
separation-logic tactics over `Arm64.SepProp`:
- **Address & bundle normalization** (via `ProofLib.Sep.Addr`): canonicalizes multi-base 64-bit
  linear addresses (`root ± k#64`) across `let` bindings, acyclic local `BitVec 64` equalities, and
  `BitVec.ofNat 64 b.toNat` / `b.zeroExtend 64` offsets; unfolds `@[expose]` spatial bundles; and
  pushes/eliminates/synthesizes prenex `∃∗` quantifiers.
- **Root-bucketed $O(K \log K)$ sweep-line**: partitions spatial conjuncts by canonical root,
  verifies disjointness, coalesces/carves `memRegion` / `cells` / `stackAt` / `stackFrame*` /
  `∃∗ v, a ↦_w v` footprints, binary-packs and splits little-endian `↦₈`/`↦₁₆`/`↦₃₂`/`↦₆₄`/`↦₁₂₈`
  cells, and absorbs/duplicates `.ro` (`↦ᵣ`, `↦₈ᵣ`..`↦₁₂₈ᵣ`, `↦₆₄ᵣ*`) resources and subslices,
  stitching the result with a single reflective `SepSolver.eqAC` pass.
-/

namespace ProofLib.Sep

open Arm64 ProofLib

public section

/-! ## Kernel Bridge Lemmas -/

/-- A 64-bit word list of known length `k` (`n = 8 * k ≤ 2 ^ 64`) weakens to `memRegion a n`. -/
theorem pointsToWords64_entails_memRegion_len {a : BitVec 64} {ws : List (BitVec 64)}
    {k n : Nat} (hlen : ws.length = k) (hn : Nat.mul 8 k = n)
    (hb : Nat.ble n 0x10000000000000000 = true) :
    (a ↦₆₄* ws) ⊢ memRegion a n := by
  have hle : 8 * ws.length ≤ 2 ^ 64 := by
    have h1 := le_two_pow_64_of_ble hb
    have h2 : 8 * k = n := hn
    omega
  have heq : 8 * ws.length = n := by
    have h2 : 8 * k = n := hn
    omega
  exact heq ▸ pointsToWords64_entails_memRegion ws a hle

/-- Join two adjacent `memRegion`s at canonical addresses `a` and `b`. -/
theorem memRegion_join_at {a b : BitVec 64} {n k nk : Nat}
    (hab : a + BitVec.ofNat 64 n = b)
    (hnk : Nat.add n k = nk)
    (hle : Nat.ble nk 0x10000000000000000 = true) :
    (memRegion a n ∗ memRegion b k) = memRegion a nk := by
  have h1 : nk ≤ 2 ^ 64 := le_two_pow_64_of_ble hle
  have h2 : nk = n + k := hnk.symm
  exact (memRegion_split' h2 hab.symm h1).symm

/-- Fuse an entailment `P ⊢ memRegion a n` with `R ⊢ memRegion b k` into `(P ∗ R) ⊢ memRegion a nk`. -/
theorem entails_memRegion_cons {P R : SepProp} {a b : BitVec 64} {n k nk : Nat}
    (hP : P ⊢ memRegion a n) (hR : R ⊢ memRegion b k)
    (hab : a + BitVec.ofNat 64 n = b)
    (hnk : Nat.add n k = nk)
    (hle : Nat.ble nk 0x10000000000000000 = true) :
    (P ∗ R) ⊢ memRegion a nk :=
  Entails.trans (sepConj_mono hP hR) (Entails.of_eq (memRegion_join_at hab hnk hle))

/-- Specialized 8-byte `↦₆₄` fusion step avoiding intermediate `pointsTo64_entails_memRegion` nodes. -/
theorem entails_memRegion_pts64_cons {R : SepProp} {a b : BitVec 64} (v : BitVec 64) {k nk : Nat}
    (hR : R ⊢ memRegion b k)
    (hab : a + 8#64 = b)
    (hnk : Nat.add 8 k = nk)
    (hle : Nat.ble nk 0x10000000000000000 = true) :
    ((a ↦₆₄ v) ∗ R) ⊢ memRegion a nk :=
  entails_memRegion_cons (pointsTo64_entails_memRegion a v) hR hab hnk hle

/-- Canonicalize `cells a k` to `memRegion a n` (`n = 8 * k ≤ 2 ^ 64`). -/
theorem cells_eq_memRegion_len (a : BitVec 64) {k n : Nat}
    (hn : Nat.mul 8 k = n) (hle : Nat.ble n 0x10000000000000000 = true) :
    cells a k = memRegion a n := by
  have h1 : 8 * k ≤ 2 ^ 64 := by
    have hb := le_two_pow_64_of_ble hle
    have hm : 8 * k = n := hn
    omega
  have hm : 8 * k = n := hn
  exact hm ▸ (memRegion_cells a k h1).symm

/-- Canonicalize `stackFrameAt sp n` to `memRegion a n` given `sp - n = a`. -/
theorem stackFrameAt_eq_memRegion_at {sp a : BitVec 64} {n : Nat}
    (ha : sp - BitVec.ofNat 64 n = a)
    (hle : Nat.ble n 0x10000000000000000 = true) :
    stackFrameAt sp n = memRegion a n := by
  rw [stackFrameAt_eq_memRegion sp n (le_two_pow_64_of_ble hle), ha]

/-- Canonicalize `stackFrame16At sp` to `memRegion a 16` given `sp - 16#64 = a`. -/
theorem stackFrame16At_eq_memRegion_at {sp a : BitVec 64} (ha : sp - 16#64 = a) :
    stackFrame16At sp = memRegion a 16 := by
  have h16 : stackFrame16At sp = stackFrameAt sp 16 := by
    simp only [stackFrame16At, reduceStackFrameAt]
  rw [h16, stackFrameAt_eq_memRegion sp 16 (le_two_pow_64_of_ble rfl), ha]

/-- Canonicalize `stackFrame32At sp` to `memRegion a 32` given `sp - 32#64 = a`. -/
theorem stackFrame32At_eq_memRegion_at {sp a : BitVec 64} (ha : sp - 32#64 = a) :
    stackFrame32At sp = memRegion a 32 := by
  have h32 : stackFrame32At sp = stackFrameAt sp 32 := by
    simp only [stackFrame32At, reduceStackFrameAt]
  rw [h32, stackFrameAt_eq_memRegion sp 32 (le_two_pow_64_of_ble rfl), ha]

/-- Canonicalize a zero-length read-write byte slice to `emp`. -/
theorem pointsToBytes_eq_emp_of_len_zero (a : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 0) : (a ↦ₛ bs) = emp := by
  rw [List.eq_nil_of_length_eq_zero h, pointsToBytes_nil]

/-- Canonicalize a zero-length read-write 64-bit word list to `emp`. -/
theorem pointsToWords64_eq_emp_of_len_zero (a : BitVec 64) {ws : List (BitVec 64)}
    (h : ws.length = 0) : (a ↦₆₄* ws) = emp := by
  rw [List.eq_nil_of_length_eq_zero h, pointsToWords64_nil]

/-- Canonicalize a zero-length read-only byte slice to `emp`. -/
theorem pointsToBytesRO_eq_emp_of_len_zero (a : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 0) : (a ↦ᵣ bs) = emp := by
  rw [List.eq_nil_of_length_eq_zero h, pointsToBytesRO_nil]

/-- Canonicalize a zero-length read-only 64-bit word list to `emp`. -/
theorem pointsToWords64RO_eq_emp_of_len_zero (a : BitVec 64) {ws : List (BitVec 64)}
    (h : ws.length = 0) : (a ↦₆₄ᵣ* ws) = emp := by
  rw [List.eq_nil_of_length_eq_zero h, pointsToWords64RO_nil]

/-- Pack two adjacent 64-bit cells at canonical addresses `a` and `b` (`a + 8#64 = b`) into `a ↦₁₂₈ v`. -/
theorem pointsTo64_pair_at {a b : BitVec 64} {lo hi : BitVec 64} {v : BitVec 128}
    (hab : a + 8#64 = b) (hv : hi ++ lo = v) :
    ((a ↦₆₄ lo) ∗ (b ↦₆₄ hi)) = (a ↦₁₂₈ v) := by
  rw [← hab, pointsTo64_pair, hv]

/-- Fast-path pack of `(a ↦₆₄ v.extractLsb' 0 64) ∗ (b ↦₆₄ v.extractLsb' 64 64) = (a ↦₁₂₈ v)`. -/
theorem pointsTo64_pair_extract128_at {a b : BitVec 64} (v : BitVec 128) (hab : a + 8#64 = b) :
    ((a ↦₆₄ v.extractLsb' 0 64) ∗ (b ↦₆₄ v.extractLsb' 64 64)) = (a ↦₁₂₈ v) := by
  rw [← hab, ← pointsTo128_split64]

/-- Pack two adjacent 32-bit cells at canonical addresses `a` and `b` (`a + 4#64 = b`) into `a ↦₆₄ v`. -/
theorem pointsTo32_pair_at {a b : BitVec 64} {lo hi : BitVec 32} {v : BitVec 64}
    (hab : a + 4#64 = b) (hv : hi ++ lo = v) :
    ((a ↦₃₂ lo) ∗ (b ↦₃₂ hi)) = (a ↦₆₄ v) := by
  rw [← hab, pointsTo32_pair, hv]

/-- Fast-path pack of `(a ↦₃₂ v.extractLsb' 0 32) ∗ (b ↦₃₂ v.extractLsb' 32 32) = (a ↦₆₄ v)`. -/
theorem pointsTo32_pair_extract64_at {a b : BitVec 64} (v : BitVec 64) (hab : a + 4#64 = b) :
    ((a ↦₃₂ v.extractLsb' 0 32) ∗ (b ↦₃₂ v.extractLsb' 32 32)) = (a ↦₆₄ v) := by
  rw [← hab, ← pointsTo64_split32]

/-- Pack two adjacent 16-bit cells at canonical addresses `a` and `b` (`a + 2#64 = b`) into `a ↦₃₂ v`. -/
theorem pointsTo16_pair_at {a b : BitVec 64} {lo hi : BitVec 16} {v : BitVec 32}
    (hab : a + 2#64 = b) (hv : hi ++ lo = v) :
    ((a ↦₁₆ lo) ∗ (b ↦₁₆ hi)) = (a ↦₃₂ v) := by
  rw [← hab, pointsTo16_pair, hv]

/-- Fast-path pack of `(a ↦₁₆ v.extractLsb' 0 16) ∗ (b ↦₁₆ v.extractLsb' 16 16) = (a ↦₃₂ v)`. -/
theorem pointsTo16_pair_extract32_at {a b : BitVec 64} (v : BitVec 32) (hab : a + 2#64 = b) :
    ((a ↦₁₆ v.extractLsb' 0 16) ∗ (b ↦₁₆ v.extractLsb' 16 16)) = (a ↦₃₂ v) := by
  rw [← hab, ← pointsTo32_split16]

/-- Pack two adjacent 8-bit cells at canonical addresses `a` and `b` (`a + 1#64 = b`) into `a ↦₁₆ v`. -/
theorem pointsTo8_pair_at {a b : BitVec 64} {lo hi : BitVec 8} {v : BitVec 16}
    (hab : a + 1#64 = b) (hv : hi ++ lo = v) :
    ((a ↦₈ lo) ∗ (b ↦₈ hi)) = (a ↦₁₆ v) := by
  rw [← hab, pointsTo8_pair, hv]

/-- Fast-path pack of `(a ↦₈ v.extractLsb' 0 8) ∗ (b ↦₈ v.extractLsb' 8 8) = (a ↦₁₆ v)`. -/
theorem pointsTo8_pair_extract16_at {a b : BitVec 64} (v : BitVec 16) (hab : a + 1#64 = b) :
    ((a ↦₈ v.extractLsb' 0 8) ∗ (b ↦₈ v.extractLsb' 8 8)) = (a ↦₁₆ v) := by
  rw [← hab, ← pointsTo16_split8]

/-- Split `a ↦₁₂₈ v` at canonical addresses `a` and `b` (`a + 8#64 = b`). -/
theorem pointsTo128_split64_at {a b : BitVec 64} (v : BitVec 128) (hab : a + 8#64 = b) :
    (a ↦₁₂₈ v) = ((a ↦₆₄ v.extractLsb' 0 64) ∗ (b ↦₆₄ v.extractLsb' 64 64)) := by
  rw [← hab, pointsTo128_split64]

/-- Split `a ↦₆₄ v` at canonical addresses `a` and `b` (`a + 4#64 = b`). -/
theorem pointsTo64_split32_at_canon {a b : BitVec 64} (v : BitVec 64) (hab : a + 4#64 = b) :
    (a ↦₆₄ v) = ((a ↦₃₂ v.extractLsb' 0 32) ∗ (b ↦₃₂ v.extractLsb' 32 32)) := by
  rw [← hab, pointsTo64_split32]

/-- Split `a ↦₃₂ v` at canonical addresses `a` and `b` (`a + 2#64 = b`). -/
theorem pointsTo32_split16_at_canon {a b : BitVec 64} (v : BitVec 32) (hab : a + 2#64 = b) :
    (a ↦₃₂ v) = ((a ↦₁₆ v.extractLsb' 0 16) ∗ (b ↦₁₆ v.extractLsb' 16 16)) := by
  rw [← hab, pointsTo32_split16]

/-- Split `a ↦₁₆ v` at canonical addresses `a` and `b` (`a + 1#64 = b`). -/
theorem pointsTo16_split8_at_canon {a b : BitVec 64} (v : BitVec 16) (hab : a + 1#64 = b) :
    (a ↦₁₆ v) = ((a ↦₈ v.extractLsb' 0 8) ∗ (b ↦₈ v.extractLsb' 8 8)) := by
  rw [← hab, pointsTo16_split8]

/-- Split a 128-bit read-only points-to cell into two adjacent 64-bit read-only cells. -/
theorem pointsTo128RO_split64 (a : BitVec 64) (v : BitVec 128) :
    (a ↦₁₂₈ᵣ v) = ((a ↦₆₄ᵣ v.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ᵣ v.extractLsb' 64 64)) := by
  have h1 := IsBlockRO.pointsTo128RO a v
  have h2 : IsBlockRO ((a ↦₆₄ᵣ v.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ᵣ v.extractLsb' 64 64))
      a 16 (fun m => m.read128 a = v) :=
    ((IsBlockRO.pointsTo64RO a (v.extractLsb' 0 64)).sepConj
      (IsBlockRO.pointsTo64RO (a + 8#64) (v.extractLsb' 64 64)) (by bv_arith)
      (by decide)).cast rfl fun m => by
        simp only [Memory.read128]
        generalize m.read64 a = lo
        generalize m.read64 (a + 8#64) = hi
        bv_bits
  ext h
  exact (h1.iff h).trans (h2.iff h).symm

/-- Re-express a 128-bit read-only points-to cell as a 16-byte `pointsToBytesRO` list. -/
theorem pointsTo128RO_eq_pointsToBytesRO (a : BitVec 64) (v : BitVec 128) :
    (a ↦₁₂₈ᵣ v) = (a ↦ᵣ (unpack64 (v.extractLsb' 0 64) ++ unpack64 (v.extractLsb' 64 64))) := by
  rw [pointsTo128RO_split64, pointsTo64RO_eq_pointsToBytesRO, pointsTo64RO_eq_pointsToBytesRO,
      pointsToBytesRO_append, unpack64_length]

/-- Re-express an 8-bit read-only points-to cell as a 1-byte `pointsToBytesRO` list. -/
theorem pointsTo8RO_eq_pointsToBytesRO (a : BitVec 64) (v : BitVec 8) :
    (a ↦₈ᵣ v) = (a ↦ᵣ [v]) :=
  (pointsToBytesRO_singleton a v).symm

/-- Absorb a read-only byte subslice `(subA ↦ᵣ sub)` into a containing `(a ↦ᵣ buf)`. -/
theorem pointsToBytesRO_absorb_subslice {a subA : BitVec 64} {buf sub : List (BitVec 8)}
    {totalLen off len : Nat}
    (hAddr : a + BitVec.ofNat 64 off = subA)
    (hLen : buf.length = totalLen)
    (hBound : Nat.ble (Nat.add off len) totalLen = true)
    (hSlice : (buf.drop off).take len = sub) :
    ((subA ↦ᵣ sub) ∗ (a ↦ᵣ buf)) = (a ↦ᵣ buf) := by
  have hle : off + len ≤ buf.length := hLen ▸ Nat.le_of_ble_eq_true hBound
  have hsp := pointsToBytesRO_split3 a buf off len hle
  rw [hAddr, hSlice] at hsp
  rw [hsp, ← sepConj_assoc, pointsToBytesRO_dup]

/-- Absorb any `.ro` subslice resource `dupAtom` into a containing `.ro` resource `survAtom`
    via their `pointsToBytesRO` byte representations. -/
theorem ro_absorb_via_bytes {dupAtom survAtom : SepProp} {a subA : BitVec 64}
    {buf sub : List (BitVec 8)} {totalLen off len : Nat}
    (hDupEq : dupAtom = (subA ↦ᵣ sub))
    (hSurvEq : survAtom = (a ↦ᵣ buf))
    (hAddr : a + BitVec.ofNat 64 off = subA)
    (hLen : buf.length = totalLen)
    (hBound : Nat.ble (Nat.add off len) totalLen = true)
    (hSlice : (buf.drop off).take len = sub) :
    (dupAtom ∗ survAtom) = survAtom := by
  rw [hDupEq, hSurvEq, pointsToBytesRO_absorb_subslice hAddr hLen hBound hSlice]

/-- Absorb a read-only survivor congruence step `d ∗ rest = target` when `rest = target` and `d ∗ target = target`. -/
theorem ro_absorb_step {d rest target : SepProp}
    (hRest : rest = target) (hDup : (d ∗ target) = target) :
    (d ∗ rest) = target := by
  rw [hRest, hDup]

end

/-! ## Sweep-Line Byte-Interval & Read-Only Subsumption Engine -/

public meta section

open Lean Meta Elab Tactic

/-- Typed read-write cell widths (`↦₈`..`↦₁₂₈`). -/
inductive CellWidth where
  | w8 | w16 | w32 | w64 | w128
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Byte width of a `CellWidth`. -/
def CellWidth.bytes : CellWidth → Nat
  | .w8 => 1 | .w16 => 2 | .w32 => 4 | .w64 => 8 | .w128 => 16

/-- Read-write points-to constant name for `CellWidth`. -/
def CellWidth.rwConst : CellWidth → Name
  | .w8 => ``Arm64.pointsTo8
  | .w16 => ``Arm64.pointsTo16
  | .w32 => ``Arm64.pointsTo32
  | .w64 => ``Arm64.pointsTo64
  | .w128 => ``Arm64.pointsTo128

/-- `memRegion a w.bytes = ∃∗ v, a ↦_w v` bridge theorem name for `CellWidth`. -/
def CellWidth.memRegionEqThm : CellWidth → Name
  | .w8 => ``ProofLib.memRegion_one
  | .w16 => ``ProofLib.memRegion_two
  | .w32 => ``ProofLib.memRegion_four
  | .w64 => ``ProofLib.memRegion_eight
  | .w128 => ``ProofLib.memRegion_sixteen

/-- Classify a read-write typed points-to constant name into `CellWidth`. -/
def rwWidthOf? (fn : Name) : Option CellWidth :=
  if fn == ``Arm64.pointsTo8 then some .w8
  else if fn == ``Arm64.pointsTo16 then some .w16
  else if fn == ``Arm64.pointsTo32 then some .w32
  else if fn == ``Arm64.pointsTo64 then some .w64
  else if fn == ``Arm64.pointsTo128 then some .w128
  else none

/-- Duplication theorem `(P ∗ P) = P` for read-only `.ro` spatial heads. -/
def roDupThmOf? (fn : Name) : Option Name :=
  if fn == ``Arm64.pointsTo8RO then some ``pointsTo8RO_dup
  else if fn == ``Arm64.pointsTo16RO then some ``pointsTo16RO_dup
  else if fn == ``Arm64.pointsTo32RO then some ``pointsTo32RO_dup
  else if fn == ``Arm64.pointsTo64RO then some ``pointsTo64RO_dup
  else if fn == ``Arm64.pointsTo128RO then some ``pointsTo128RO_dup
  else if fn == ``Arm64.pointsToBytesRO then some ``pointsToBytesRO_dup
  else if fn == ``Arm64.pointsToWords64RO then some ``pointsToWords64RO_dup
  else none

/-- Byte-list view `(bytesExpr, byteLen, hLen, hEqBytesRO)` of a `.ro` atom `atom = (canonAddr ↦ᵣ bytesExpr)`. -/
structure ROBytesView where
  bytesExpr : Expr
  byteLen : Nat
  hLen : Expr
  eqBytesRO : Expr
  deriving Inhabited

/-- Classification of a flattened `SepProp` conjunct. -/
inductive AtomKind where
  | rwTyped (w : CellWidth) (val : Expr)
  | rwUninit
  | rwBytes (bs : Expr) (hLen : Expr)
  | rwWords64 (ws : Expr) (wordCount : Nat) (hLen : Expr)
  | roChunk (roHead : Name) (payload : Expr) (byteLen? : Option Nat) (bytesView? : Option ROBytesView)
  | zeroEmp
  | opaqueAtom
  deriving Inhabited

/-- Parsed and address-canonicalized `SepProp` atom. -/
structure ParsedAtom where
  origExpr : Expr
  canonAtom : Expr
  /-- Proof of `origExpr = canonAtom` (`none` when `origExpr == canonAtom`). -/
  eqCanon? : Option Expr
  addr? : Option LinAddr64
  byteLen : Nat
  kind : AtomKind
  deriving Inhabited

/-- Check whether `a` is an unconstrained single-cell existential `∃∗ v, addr ↦_w v`. -/
def isSingleCellSepExists (a : Expr) : Bool :=
  let a := (ProofLib.SepSolver.stripMData a).headBeta
  if a.isAppOfArity ``SepProp.sepExists 2 then
    match (a.getArg! 1).consumeMData with
    | .lam _ _ body _ =>
      let bodyClean := (ProofLib.SepSolver.stripMData body).headBeta
      match bodyClean.getAppFn.constName? with
      | some fn =>
        (rwWidthOf? fn).isSome && bodyClean.getAppNumArgs == 2 &&
          !(bodyClean.getArg! 0).hasLooseBVars && bodyClean.getArg! 1 == .bvar 0
      | none => false
    | _ => false
  else false

/-- Auto-unfold reducible / `@[expose]` spatial bundles across both `∗` and `∃∗` binders (kernel-defeq). -/
partial def unfoldBundlesDeep (e : Expr) (depth : Nat := 0) : MetaM Expr := do
  let e ← autoUnfoldBundles e depth
  if e.isAppOfArity ``SepProp.sepConj 2 then
    let l ← unfoldBundlesDeep (e.getArg! 0) depth
    let r ← unfoldBundlesDeep (e.getArg! 1) depth
    if l == e.getArg! 0 && r == e.getArg! 1 then return e
    return ProofLib.SepSolver.mkSep l r
  if e.isAppOfArity ``SepProp.sepExists 2 then
    let α := e.getArg! 0
    if let .lam n ty body bi := (e.getArg! 1).consumeMData then
      let u ← getLevel α
      return ← withLocalDecl n bi ty fun fv => do
        let inst := body.instantiate1 fv
        let inst' ← unfoldBundlesDeep inst depth
        if inst' == inst then return e
        let lam' ← mkLambdaFVars #[fv] inst'
        return mkApp2 (mkConst ``SepProp.sepExists [u]) α lam'
  return e

/-- Count the length of a literal `List.cons` / `List.nil` spine even when elements contain FVars. -/
partial def literalListSpineLen? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  if e.isAppOfArity ``List.nil 1 then
    some 0
  else if e.isAppOfArity ``List.cons 3 then
    (· + 1) <$> literalListSpineLen? (e.getArg! 2)
  else
    none

/-- Resolve `(k, hPrf : xs.length = k)` for a `List` expression `xs` from `ctx.lenEqs`, literal
    spine counting, or closed/reducible reduction. -/
def resolveListLength? (ctx : CtxFacts) (elemTy xs : Expr) : MetaM (Option (Nat × Expr)) := do
  let xs ← instantiateMVars xs
  for (e, k, hPrf) in ctx.lenEqs do
    if e == xs || (← withReducibleAndInstances (isDefEq e xs)) then
      let lenExpr := mkApp2 (mkConst ``List.length [Level.zero]) elemTy xs
      let expectedTy ← mkEq lenExpr (toExpr k)
      return some (k, ← mkExpectedTypeHint hPrf expectedTy)
  if !xs.hasMVar then
    let lenExpr := mkApp2 (mkConst ``List.length [Level.zero]) elemTy xs
    if let some k := literalListSpineLen? xs then
      let kExpr := toExpr k
      let prf ← mkExpectedTypeHint (← mkEqRefl kExpr) (← mkEq lenExpr kExpr)
      return some (k, prf)
    if let some k ← evalClosedNat? lenExpr then
      let kExpr := toExpr k
      let prf ← mkExpectedTypeHint (← mkEqRefl kExpr) (← mkEq lenExpr kExpr)
      return some (k, prf)
    let lenWhnf ← withTransparency .default (whnf lenExpr)
    if let some k ← getNatValue? lenWhnf then
      let kExpr := toExpr k
      let prf ← mkExpectedTypeHint (← mkEqRefl kExpr) (← mkEq lenExpr kExpr)
      return some (k, prf)
  return none

/-- Canonicalize the first (`BitVec 64`) address argument of an otherwise-opaque 2-arg spatial atom. -/
private def canonOpaqueTwoArgAtom (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (a0 : Expr) (fn : Name) (rawAddr arg2 : Expr) : MetaM ParsedAtom := do
  let la? ← try some <$> canonAddr64 ctx cacheRef rawAddr catch _ => pure none
  let some la := la? | return { origExpr := a0, canonAtom := a0, eqCanon? := none,
                                addr? := none, byteLen := 0, kind := .opaqueAtom }
  let canonAtom := if la.eqProof?.isNone then a0 else mkApp2 (mkConst fn) la.canonExpr arg2
  let eqCanon? ← match la.eqProof? with
    | none => pure none
    | some pAddr =>
      let p ← mkCongrFun (← mkCongrArg (mkConst fn) pAddr) arg2
      pure (some (← mkExpectedTypeHint p (← mkEq a0 canonAtom)))
  return { origExpr := a0, canonAtom, eqCanon?, addr? := none, byteLen := 0, kind := .opaqueAtom }

/-- Build an `ROBytesView` for `(canonAddr ↦_ro payload)` when its byte length is statically resolved. -/
private def buildROBytesView? (ctx : CtxFacts) (fn : Name) (canonAddr payload : Expr) :
    MetaM (Option Nat × Option ROBytesView) := do
  let bv8Ty := mkApp (mkConst ``BitVec) (toExpr (8 : Nat))
  if fn == ``Arm64.pointsTo8RO then
    let bsExpr ← mkListLit bv8Ty [payload]
    let hLen := mkEqReflNat (toExpr (1 : Nat))
    let eqRO := mkApp2 (mkConst ``pointsTo8RO_eq_pointsToBytesRO) canonAddr payload
    return (some 1, some { bytesExpr := bsExpr, byteLen := 1, hLen, eqBytesRO := eqRO })
  if fn == ``Arm64.pointsTo16RO then
    let bsExpr := mkApp (mkConst ``ProofLib.unpack16) payload
    let hLen ← mkExpectedTypeHint (mkEqReflNat (toExpr (2 : Nat)))
      (← mkEq (mkApp2 (mkConst ``List.length [Level.zero]) bv8Ty bsExpr) (toExpr (2 : Nat)))
    let eqRO := mkApp2 (mkConst ``ProofLib.pointsTo16RO_eq_pointsToBytesRO) canonAddr payload
    return (some 2, some { bytesExpr := bsExpr, byteLen := 2, hLen, eqBytesRO := eqRO })
  if fn == ``Arm64.pointsTo32RO then
    let bsExpr := mkApp (mkConst ``ProofLib.unpack32) payload
    let hLen ← mkExpectedTypeHint (mkEqReflNat (toExpr (4 : Nat)))
      (← mkEq (mkApp2 (mkConst ``List.length [Level.zero]) bv8Ty bsExpr) (toExpr (4 : Nat)))
    let eqRO := mkApp2 (mkConst ``ProofLib.pointsTo32RO_eq_pointsToBytesRO) canonAddr payload
    return (some 4, some { bytesExpr := bsExpr, byteLen := 4, hLen, eqBytesRO := eqRO })
  if fn == ``Arm64.pointsTo64RO then
    let bsExpr := mkApp (mkConst ``ProofLib.unpack64) payload
    let hLen ← mkExpectedTypeHint (mkEqReflNat (toExpr (8 : Nat)))
      (← mkEq (mkApp2 (mkConst ``List.length [Level.zero]) bv8Ty bsExpr) (toExpr (8 : Nat)))
    let eqRO := mkApp2 (mkConst ``ProofLib.pointsTo64RO_eq_pointsToBytesRO) canonAddr payload
    return (some 8, some { bytesExpr := bsExpr, byteLen := 8, hLen, eqBytesRO := eqRO })
  if fn == ``Arm64.pointsTo128RO then
    let lo64 := mkApp4 (mkConst ``BitVec.extractLsb') (toExpr (128 : Nat)) (toExpr (0 : Nat)) (toExpr (64 : Nat)) payload
    let hi64 := mkApp4 (mkConst ``BitVec.extractLsb') (toExpr (128 : Nat)) (toExpr (64 : Nat)) (toExpr (64 : Nat)) payload
    let bsExpr ← mkAppM ``HAppend.hAppend
      #[mkApp (mkConst ``ProofLib.unpack64) lo64, mkApp (mkConst ``ProofLib.unpack64) hi64]
    let hLen ← mkExpectedTypeHint (mkEqReflNat (toExpr (16 : Nat)))
      (← mkEq (mkApp2 (mkConst ``List.length [Level.zero]) bv8Ty bsExpr) (toExpr (16 : Nat)))
    let eqRO := mkApp2 (mkConst ``pointsTo128RO_eq_pointsToBytesRO) canonAddr payload
    return (some 16, some { bytesExpr := bsExpr, byteLen := 16, hLen, eqBytesRO := eqRO })
  if fn == ``Arm64.pointsToBytesRO then
    if let some (len, hLen) ← resolveListLength? ctx bv8Ty payload then
      let eqRO ← mkEqRefl (mkApp2 (mkConst ``Arm64.pointsToBytesRO) canonAddr payload)
      return (some len, some { bytesExpr := payload, byteLen := len, hLen, eqBytesRO := eqRO })
    return (none, none)
  if fn == ``Arm64.pointsToWords64RO then
    let bv64Ty := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
    let len? := (← resolveListLength? ctx bv64Ty payload).map (fun (k, _) => 8 * k)
    return (len?, none)
  return (none, none)

/-- Parse and canonicalize one flattened `SepProp` atom. -/
def parseAtom (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64)) (a0 : Expr) :
    MetaM ParsedAtom := do
  let a0 ← instantiateMVars a0
  let a := (ProofLib.SepSolver.stripMData a0).headBeta
  -- 1. Existential single cell `∃∗ v, addr ↦_w v` -> canonicalizes directly to `memRegion addrCanon w.bytes`
  if a.isAppOfArity ``SepProp.sepExists 2 then
    let α := a.getArg! 0
    if let .lam n ty body bi := (a.getArg! 1).consumeMData then
      let bodyClean := (ProofLib.SepSolver.stripMData body).headBeta
      if let some fn := bodyClean.getAppFn.constName? then
        if let some cw := rwWidthOf? fn then
          if bodyClean.getAppNumArgs == 2 && !(bodyClean.getArg! 0).hasLooseBVars &&
             bodyClean.getArg! 1 == .bvar 0 then
            let rawAddr := bodyClean.getArg! 0
            let la ← canonAddr64 ctx cacheRef rawAddr
            let canonReg := mkApp2 (mkConst ``Arm64.memRegion) la.canonExpr (toExpr cw.bytes)
            let pRegSymm ← mkEqSymm (mkApp (mkConst cw.memRegionEqThm) la.canonExpr)
            let eqPrf ← match la.eqProof? with
              | none => pure pRegSymm
              | some pAddr =>
                let u ← getLevel α
                let lamOrig := Expr.lam n ty (mkApp2 (mkConst fn) rawAddr (.bvar 0)) bi
                let lamCanon := Expr.lam n ty (mkApp2 (mkConst fn) la.canonExpr (.bvar 0)) bi
                let hFun ← withLocalDecl n bi ty fun fv => do
                  let step ← mkCongrFun (← mkCongrArg (mkConst fn) pAddr) fv
                  mkLambdaFVars #[fv] step
                let pEx := mkApp4 (mkConst ``ProofLib.sepExists_congr [u]) α lamOrig lamCanon hFun
                mkEqTrans pEx pRegSymm
            let eqPrf ← mkExpectedTypeHint eqPrf (← mkEq a0 canonReg)
            return { origExpr := a0, canonAtom := canonReg, eqCanon? := some eqPrf,
                     addr? := some la, byteLen := cw.bytes, kind := .rwUninit }
  let some fn := a.getAppFn.constName? |
    return { origExpr := a0, canonAtom := a0, eqCanon? := none, addr? := none, byteLen := 0, kind := .opaqueAtom }
  -- 2. Concrete RW typed cells `↦₈..↦₁₂₈`
  if let some cw := rwWidthOf? fn then
    if a.getAppNumArgs == 2 then
      let rawAddr := a.getArg! 0
      let val := a.getArg! 1
      let la ← canonAddr64 ctx cacheRef rawAddr
      let canonAtom := if la.eqProof?.isNone then a0 else mkApp2 (mkConst fn) la.canonExpr val
      let eqCanon? ← match la.eqProof? with
        | none => pure none
        | some pAddr =>
          let p ← mkCongrFun (← mkCongrArg (mkConst fn) pAddr) val
          pure (some (← mkExpectedTypeHint p (← mkEq a0 canonAtom)))
      return { origExpr := a0, canonAtom, eqCanon?, addr? := some la, byteLen := cw.bytes,
               kind := .rwTyped cw val }
  -- 3. `memRegion addr len`
  if fn == ``Arm64.memRegion && a.getAppNumArgs == 2 then
    let rawAddr := a.getArg! 0
    let lenExpr := a.getArg! 1
    if let some n ← evalClosedNat? lenExpr then
      let la ← canonAddr64 ctx cacheRef rawAddr
      if n == 0 then
        let empE := mkConst ``SepProp.emp
        let pZero := mkApp (mkConst ``ProofLib.memRegion_zero) rawAddr
        let pTot ← if lenExpr == toExpr (0 : Nat) then pure pZero else do
          let pLen ← mkExpectedTypeHint (← mkEqRefl (toExpr (0 : Nat))) (← mkEq lenExpr (toExpr (0 : Nat)))
          mkEqTrans (← mkCongrArg (mkApp (mkConst ``Arm64.memRegion) rawAddr) pLen) pZero
        return { origExpr := a0, canonAtom := empE,
                 eqCanon? := some (← mkExpectedTypeHint pTot (← mkEq a0 empE)),
                 addr? := some la, byteLen := 0, kind := .zeroEmp }
      let nCanon := toExpr n
      let canonAtom := mkApp2 (mkConst ``Arm64.memRegion) la.canonExpr nCanon
      let eqCanon? ←
        if a0 == canonAtom then pure none
        else do
          let pAddr ← match la.eqProof? with | some p => pure p | none => mkEqRefl la.canonExpr
          let pLen ← if lenExpr == nCanon then mkEqRefl nCanon
            else mkExpectedTypeHint (← mkEqRefl nCanon) (← mkEq lenExpr nCanon)
          let p ← mkCongr (← mkCongrArg (mkConst ``Arm64.memRegion) pAddr) pLen
          pure (some (← mkExpectedTypeHint p (← mkEq a0 canonAtom)))
      return { origExpr := a0, canonAtom, eqCanon?, addr? := some la, byteLen := n, kind := .rwUninit }
    return ← canonOpaqueTwoArgAtom ctx cacheRef a0 fn rawAddr lenExpr
  -- 4. `ProofLib.stackAt sp len` / `Arm64.stackFrame s len` (definitionally `memRegion (sp - len) len`)
  if (fn == ``ProofLib.stackAt || fn == ``Arm64.stackFrame) && a.getAppNumArgs == 2 then
    let spExpr := if fn == ``Arm64.stackFrame then mkApp (mkConst ``Arm64.State.sp) (a.getArg! 0) else a.getArg! 0
    let lenExpr := a.getArg! 1
    if let some n ← evalClosedNat? lenExpr then
      let rawAddr ← mkAppM ``HSub.hSub #[spExpr, mkBV64Lit n]
      let la ← canonAddr64 ctx cacheRef rawAddr
      if n == 0 then
        let empE := mkConst ``SepProp.emp
        let pZero ← mkExpectedTypeHint (mkApp (mkConst ``ProofLib.memRegion_zero) rawAddr) (← mkEq a0 empE)
        return { origExpr := a0, canonAtom := empE, eqCanon? := some pZero,
                 addr? := some la, byteLen := 0, kind := .zeroEmp }
      let nCanon := toExpr n
      let canonAtom := mkApp2 (mkConst ``Arm64.memRegion) la.canonExpr nCanon
      let pAddr ← match la.eqProof? with | some p => pure p | none => mkEqRefl la.canonExpr
      let pLen ← if lenExpr == nCanon then mkEqRefl nCanon
        else mkExpectedTypeHint (← mkEqRefl nCanon) (← mkEq lenExpr nCanon)
      let p ← mkCongr (← mkCongrArg (mkConst ``Arm64.memRegion) pAddr) pLen
      let eqPrf ← mkExpectedTypeHint p (← mkEq a0 canonAtom)
      return { origExpr := a0, canonAtom, eqCanon? := some eqPrf,
               addr? := some la, byteLen := n, kind := .rwUninit }
  -- 5. `Arm64.stackFrameAt` / `stackFrame16At` / `stackFrame32At` / `stackFrame16` / `stackFrame32`
  if fn == ``Arm64.stackFrameAt && a.getAppNumArgs == 2 then
    let spExpr := a.getArg! 0
    let lenExpr := a.getArg! 1
    if let some n ← evalClosedNat? lenExpr then
      let rawAddr ← mkAppM ``HSub.hSub #[spExpr, mkBV64Lit n]
      let la ← canonAddr64 ctx cacheRef rawAddr
      if n == 0 then
        let empE := mkConst ``SepProp.emp
        let p0 := mkApp (mkConst ``stackFrameAt_zero) spExpr
        return { origExpr := a0, canonAtom := empE,
                 eqCanon? := some (← mkExpectedTypeHint p0 (← mkEq a0 empE)),
                 addr? := some la, byteLen := 0, kind := .zeroEmp }
      let nCanon := toExpr n
      let canonAtom := mkApp2 (mkConst ``Arm64.memRegion) la.canonExpr nCanon
      let ha ← match la.eqProof? with | some p => pure p | none => mkEqRefl la.canonExpr
      let ha ← mkExpectedTypeHint ha (← mkEq rawAddr la.canonExpr)
      let pBase := mkAppN (mkConst ``stackFrameAt_eq_memRegion_at) #[spExpr, la.canonExpr, nCanon, ha, rflTrueExpr]
      let eqPrf ← mkExpectedTypeHint pBase (← mkEq a0 canonAtom)
      return { origExpr := a0, canonAtom, eqCanon? := some eqPrf,
               addr? := some la, byteLen := n, kind := .rwUninit }
  if (fn == ``Arm64.stackFrame16At || fn == ``Arm64.stackFrame16) && a.getAppNumArgs == 1 then
    let spExpr := if fn == ``Arm64.stackFrame16 then mkApp (mkConst ``Arm64.State.sp) (a.getArg! 0) else a.getArg! 0
    let rawAddr ← mkAppM ``HSub.hSub #[spExpr, mkBV64Lit 16]
    let la ← canonAddr64 ctx cacheRef rawAddr
    let canonAtom := mkApp2 (mkConst ``Arm64.memRegion) la.canonExpr (toExpr (16 : Nat))
    let ha ← match la.eqProof? with | some p => pure p | none => mkEqRefl la.canonExpr
    let pBase := mkApp3 (mkConst ``stackFrame16At_eq_memRegion_at) spExpr la.canonExpr
      (← mkExpectedTypeHint ha (← mkEq rawAddr la.canonExpr))
    return { origExpr := a0, canonAtom, eqCanon? := some (← mkExpectedTypeHint pBase (← mkEq a0 canonAtom)),
             addr? := some la, byteLen := 16, kind := .rwUninit }
  if (fn == ``Arm64.stackFrame32At || fn == ``Arm64.stackFrame32) && a.getAppNumArgs == 1 then
    let spExpr := if fn == ``Arm64.stackFrame32 then mkApp (mkConst ``Arm64.State.sp) (a.getArg! 0) else a.getArg! 0
    let rawAddr ← mkAppM ``HSub.hSub #[spExpr, mkBV64Lit 32]
    let la ← canonAddr64 ctx cacheRef rawAddr
    let canonAtom := mkApp2 (mkConst ``Arm64.memRegion) la.canonExpr (toExpr (32 : Nat))
    let ha ← match la.eqProof? with | some p => pure p | none => mkEqRefl la.canonExpr
    let pBase := mkApp3 (mkConst ``stackFrame32At_eq_memRegion_at) spExpr la.canonExpr
      (← mkExpectedTypeHint ha (← mkEq rawAddr la.canonExpr))
    return { origExpr := a0, canonAtom, eqCanon? := some (← mkExpectedTypeHint pBase (← mkEq a0 canonAtom)),
             addr? := some la, byteLen := 32, kind := .rwUninit }
  -- 6. `ProofLib.cells addr k` -> `memRegion addrCanon (8 * k)`
  if fn == ``ProofLib.cells && a.getAppNumArgs == 2 then
    let rawAddr := a.getArg! 0
    let kExpr := a.getArg! 1
    if let some k ← evalClosedNat? kExpr then
      let la ← canonAddr64 ctx cacheRef rawAddr
      if k == 0 then
        let empE := mkConst ``SepProp.emp
        let pZero := mkApp (mkConst ``ProofLib.cells_zero) rawAddr
        let pTot ← if kExpr == toExpr (0 : Nat) then pure pZero else do
          let pk ← mkExpectedTypeHint (← mkEqRefl (toExpr (0 : Nat))) (← mkEq kExpr (toExpr (0 : Nat)))
          mkEqTrans (← mkCongrArg (mkApp (mkConst ``ProofLib.cells) rawAddr) pk) pZero
        return { origExpr := a0, canonAtom := empE,
                 eqCanon? := some (← mkExpectedTypeHint pTot (← mkEq a0 empE)),
                 addr? := some la, byteLen := 0, kind := .zeroEmp }
      let byteLen := 8 * k
      let kCanon := toExpr k
      let nCanon := toExpr byteLen
      let canonAtom := mkApp2 (mkConst ``Arm64.memRegion) la.canonExpr nCanon
      let pCells := mkAppN (mkConst ``cells_eq_memRegion_len)
        #[la.canonExpr, kCanon, nCanon, mkEqReflNat nCanon, rflTrueExpr]
      let pTot ←
        if rawAddr == la.canonExpr && kExpr == kCanon then pure pCells
        else do
          let pAddr ← match la.eqProof? with | some p => pure p | none => mkEqRefl la.canonExpr
          let pk ← if kExpr == kCanon then mkEqRefl kCanon
            else mkExpectedTypeHint (← mkEqRefl kCanon) (← mkEq kExpr kCanon)
          let pCongr ← mkCongr (← mkCongrArg (mkConst ``ProofLib.cells) pAddr) pk
          mkEqTrans pCongr pCells
      return { origExpr := a0, canonAtom, eqCanon? := some (← mkExpectedTypeHint pTot (← mkEq a0 canonAtom)),
               addr? := some la, byteLen, kind := .rwUninit }
    return ← canonOpaqueTwoArgAtom ctx cacheRef a0 fn rawAddr kExpr
  -- 7. `pointsToBytes addr bs` (`a ↦ₛ bs`)
  if fn == ``Arm64.pointsToBytes && a.getAppNumArgs == 2 then
    let rawAddr := a.getArg! 0
    let bs := a.getArg! 1
    let bv8Ty := mkApp (mkConst ``BitVec) (toExpr (8 : Nat))
    if let some (byteLen, hLen) ← resolveListLength? ctx bv8Ty bs then
      let la ← canonAddr64 ctx cacheRef rawAddr
      if byteLen == 0 then
        let empE := mkConst ``SepProp.emp
        let p0 := mkApp3 (mkConst ``pointsToBytes_eq_emp_of_len_zero) rawAddr bs hLen
        return { origExpr := a0, canonAtom := empE,
                 eqCanon? := some (← mkExpectedTypeHint p0 (← mkEq a0 empE)),
                 addr? := some la, byteLen := 0, kind := .zeroEmp }
      let canonAtom := if la.eqProof?.isNone then a0 else mkApp2 (mkConst fn) la.canonExpr bs
      let eqCanon? ← match la.eqProof? with
        | none => pure none
        | some pAddr =>
          let p ← mkCongrFun (← mkCongrArg (mkConst fn) pAddr) bs
          pure (some (← mkExpectedTypeHint p (← mkEq a0 canonAtom)))
      return { origExpr := a0, canonAtom, eqCanon?, addr? := some la, byteLen,
               kind := .rwBytes bs hLen }
    return ← canonOpaqueTwoArgAtom ctx cacheRef a0 fn rawAddr bs
  -- 8. `pointsToWords64 addr ws` (`a ↦₆₄* ws`)
  if fn == ``Arm64.pointsToWords64 && a.getAppNumArgs == 2 then
    let rawAddr := a.getArg! 0
    let ws := a.getArg! 1
    let bv64Ty := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
    if let some (wordCount, hLen) ← resolveListLength? ctx bv64Ty ws then
      let la ← canonAddr64 ctx cacheRef rawAddr
      if wordCount == 0 then
        let empE := mkConst ``SepProp.emp
        let p0 := mkApp3 (mkConst ``pointsToWords64_eq_emp_of_len_zero) rawAddr ws hLen
        return { origExpr := a0, canonAtom := empE,
                 eqCanon? := some (← mkExpectedTypeHint p0 (← mkEq a0 empE)),
                 addr? := some la, byteLen := 0, kind := .zeroEmp }
      let canonAtom := if la.eqProof?.isNone then a0 else mkApp2 (mkConst fn) la.canonExpr ws
      let eqCanon? ← match la.eqProof? with
        | none => pure none
        | some pAddr =>
          let p ← mkCongrFun (← mkCongrArg (mkConst fn) pAddr) ws
          pure (some (← mkExpectedTypeHint p (← mkEq a0 canonAtom)))
      return { origExpr := a0, canonAtom, eqCanon?, addr? := some la, byteLen := 8 * wordCount,
               kind := .rwWords64 ws wordCount hLen }
    return ← canonOpaqueTwoArgAtom ctx cacheRef a0 fn rawAddr ws
  -- 9. Read-only `.ro` assertions (`↦₈ᵣ..↦₁₂₈ᵣ`, `↦ᵣ`, `↦₆₄ᵣ*`)
  if (roDupThmOf? fn).isSome && a.getAppNumArgs == 2 then
    let rawAddr := a.getArg! 0
    let payload := a.getArg! 1
    let la ← canonAddr64 ctx cacheRef rawAddr
    if fn == ``Arm64.pointsToBytesRO then
      let bv8Ty := mkApp (mkConst ``BitVec) (toExpr (8 : Nat))
      if let some (0, hLen0) ← resolveListLength? ctx bv8Ty payload then
        let empE := mkConst ``SepProp.emp
        let p0 := mkApp3 (mkConst ``pointsToBytesRO_eq_emp_of_len_zero) rawAddr payload hLen0
        return { origExpr := a0, canonAtom := empE,
                 eqCanon? := some (← mkExpectedTypeHint p0 (← mkEq a0 empE)),
                 addr? := some la, byteLen := 0, kind := .zeroEmp }
    if fn == ``Arm64.pointsToWords64RO then
      let bv64Ty := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
      if let some (0, hLen0) ← resolveListLength? ctx bv64Ty payload then
        let empE := mkConst ``SepProp.emp
        let p0 := mkApp3 (mkConst ``pointsToWords64RO_eq_emp_of_len_zero) rawAddr payload hLen0
        return { origExpr := a0, canonAtom := empE,
                 eqCanon? := some (← mkExpectedTypeHint p0 (← mkEq a0 empE)),
                 addr? := some la, byteLen := 0, kind := .zeroEmp }
    let canonAtom := if la.eqProof?.isNone then a0 else mkApp2 (mkConst fn) la.canonExpr payload
    let eqCanon? ← match la.eqProof? with
      | none => pure none
      | some pAddr =>
        let p ← mkCongrFun (← mkCongrArg (mkConst fn) pAddr) payload
        pure (some (← mkExpectedTypeHint p (← mkEq a0 canonAtom)))
    let (byteLen?, bytesView?) ← buildROBytesView? ctx fn la.canonExpr payload
    return { origExpr := a0, canonAtom, eqCanon?, addr? := some la, byteLen := byteLen?.getD 0,
             kind := .roChunk fn payload byteLen? bytesView? }
  -- 10. Other 2-argument spatial atoms (`memRegionProtNone`, `memRegionLazy`, etc.)
  if (fn == ``Arm64.memRegionProtNone || fn == ``Arm64.memRegionLazy) && a.getAppNumArgs == 2 then
    return ← canonOpaqueTwoArgAtom ctx cacheRef a0 fn (a.getArg! 0) (a.getArg! 1)
  return { origExpr := a0, canonAtom := a0, eqCanon? := none, addr? := none, byteLen := 0, kind := .opaqueAtom }

/-- Rewrite a right-nested `mkSepList` spine pointwise using per-atom optional equality proofs,
    dropping `.zeroEmp` (`emp`) atoms via `emp_sepConj` / `sepConj_emp`. -/
def buildSpineCanonEq (items : Array ParsedAtom) : MetaM (Expr × Array ParsedAtom × Option Expr) := do
  if items.isEmpty then
    return (mkConst ``SepProp.emp, #[], none)
  let mut curExpr : Option Expr := none
  let mut curPrf? : Option Expr := none
  let mut keptRev : Array ParsedAtom := #[]
  let mut idx := items.size
  while idx > 0 do
    idx := idx - 1
    let it := items[idx]!
    match curExpr with
    | none =>
      if it.kind matches .zeroEmp then
        curExpr := some (mkConst ``SepProp.emp)
        curPrf? := it.eqCanon?
      else
        curExpr := some it.canonAtom
        curPrf? := it.eqCanon?
        keptRev := keptRev.push it
    | some restCanon =>
      let origTail :=
        let tailOrigs := (items.extract (idx + 1) items.size).map (·.origExpr)
        ProofLib.SepSolver.mkSepList tailOrigs
      if it.kind matches .zeroEmp then
        let pHead := it.eqCanon?.getD (← mkEqRefl (mkConst ``SepProp.emp))
        let pTail ← match curPrf? with
          | some p => pure p
          | none => mkExpectedTypeHint (← mkEqRefl restCanon) (← mkEq origTail restCanon)
        let pCongr ← mkCongr (← mkCongrArg (mkConst ``SepProp.sepConj) pHead) pTail
        let pEmp := mkApp (mkConst ``emp_sepConj) restCanon
        curPrf? := some (← mkEqTrans pCongr pEmp)
      else if restCanon.isConstOf ``SepProp.emp && keptRev.isEmpty then
        let pHead := it.eqCanon?.getD (← mkEqRefl it.canonAtom)
        let pTail ← match curPrf? with
          | some p => pure p
          | none => mkExpectedTypeHint (← mkEqRefl restCanon) (← mkEq origTail restCanon)
        let pCongr ← mkCongr (← mkCongrArg (mkConst ``SepProp.sepConj) pHead) pTail
        let pEmp := mkApp (mkConst ``sepConj_emp) it.canonAtom
        curExpr := some it.canonAtom
        curPrf? := some (← mkEqTrans pCongr pEmp)
        keptRev := keptRev.push it
      else
        let nextCanon := ProofLib.SepSolver.mkSep it.canonAtom restCanon
        if it.eqCanon?.isNone && curPrf?.isNone then
          curExpr := some nextCanon
        else
          let pHead := it.eqCanon?.getD (← mkEqRefl it.canonAtom)
          let pTail ← match curPrf? with
            | some p => pure p
            | none => mkExpectedTypeHint (← mkEqRefl restCanon) (← mkEq origTail restCanon)
          let pCongr ← mkCongr (← mkCongrArg (mkConst ``SepProp.sepConj) pHead) pTail
          curExpr := some nextCanon
          curPrf? := some pCongr
        keptRev := keptRev.push it
  return (curExpr.getD (mkConst ``SepProp.emp), keptRev.reverse, curPrf?)

/-- Segment plan produced by the bucketed sweep-line. -/
structure SegmentPlan where
  lhsAtoms : Array Expr
  rhsAtoms : Array Expr
  /-- In `eqMode = true`, proves `mkSepList lhsAtoms = mkSepList rhsAtoms`.
      In `eqMode = false`, proves `mkSepList lhsAtoms ⊢ mkSepList rhsAtoms`. -/
  proof : Expr
  deriving Inhabited

/-- Prove `v1 = v2` for typed cell values (`rfl`, `isDefEq`, `bv_slice`, `bv_arith`, or `bv_bits`). -/
def proveValueEq (v1 v2 : Expr) : TacticM Expr := do
  let v1 ← instantiateMVars v1
  let v2 ← instantiateMVars v2
  if v1 == v2 then return ← mkEqRefl v1
  if ← withReducibleAndInstances (isDefEq v1 v2) then
    let v2 ← instantiateMVars v2
    return ← mkExpectedTypeHint (← mkEqRefl v2) (← mkEq v1 v2)
  let eqTy ← mkEq v1 v2
  let mvar ← mkFreshExprMVar eqTy
  let (gs, _) ← runTactic mvar.mvarId! (← `(tactic| first | rfl | assumption | bv_slice | bv_arith | bv_bits))
  if gs.isEmpty then
    return ← instantiateMVars mvar
  throwError "sep_interval: cannot prove cell value equality {v1} = {v2}"

/-- Recursively binary-pack adjacent `.rwTyped` cells in `slice` covering `[startOff, startOff + targetW.bytes)`
    into `(canonTargetAddr ↦_targetW packedVal)`, returning `(packedVal, eqPrf)`. -/
partial def packTypedSlice (root : Expr) (slice : Array ParsedAtom) (startOff : Int)
    (targetW : CellWidth) : TacticM (Expr × Expr) := do
  if slice.size == 1 then
    let it := slice[0]!
    let .rwTyped cw val := it.kind | throwError "sep_interval: expected typed cell"
    if cw != targetW then
      throwError "sep_interval: width mismatch {repr cw} vs {repr targetW}"
    let val ← instantiateMVars val
    let atomExpr ← instantiateMVars it.canonAtom
    return (val, ← mkEqRefl atomExpr)
  let halfBytes : Int := (targetW.bytes / 2 : Nat)
  let midOff := startOff + halfBytes
  let mut splitIdx? : Option Nat := none
  for h : k in [:slice.size] do
    if slice[k].addr?.get!.byteOff == midOff then
      splitIdx? := some k
      break
  let some midIdx := splitIdx?
    | throwError "sep_interval: cannot binary-pack typed cells across midpoint {midOff}"
  let subW : CellWidth ← match targetW with
    | .w16 => pure .w8
    | .w32 => pure .w16
    | .w64 => pure .w32
    | .w128 => pure .w64
    | .w8 => throwError "sep_interval: cannot pack into 8-bit cell"
  let loSlice := slice.extract 0 midIdx
  let hiSlice := slice.extract midIdx slice.size
  let (loVal, loEq) ← packTypedSlice root loSlice startOff subW
  let (hiVal, hiEq) ← packTypedSlice root hiSlice midOff subW
  let loAddr := slice[0]!.addr?.get!.canonExpr
  let hiAddr := slice[midIdx]!.addr?.get!.canonExpr
  let hab ← proveCanonAddrStep root startOff subW.bytes loAddr hiAddr
  -- Check `extractLsb'` fast path (`v.extractLsb' 0 half` + `v.extractLsb' half half` = `v`)
  let extractFast? : Option (Expr × Name) :=
    if loVal.isAppOfArity ``BitVec.extractLsb' 4 && hiVal.isAppOfArity ``BitVec.extractLsb' 4 then
      let qLo := loVal.getArg! 3
      let qHi := hiVal.getArg! 3
      let halfNat := subW.bytes * 8
      if qLo == qHi && loVal.getArg! 1 == toExpr (0 : Nat) &&
         loVal.getArg! 2 == toExpr halfNat &&
         hiVal.getArg! 1 == toExpr halfNat &&
         hiVal.getArg! 2 == toExpr halfNat then
        match targetW with
        | .w128 => some (qLo, ``pointsTo64_pair_extract128_at)
        | .w64 => some (qLo, ``pointsTo32_pair_extract64_at)
        | .w32 => some (qLo, ``pointsTo16_pair_extract32_at)
        | .w16 => some (qLo, ``pointsTo8_pair_extract16_at)
        | .w8 => none
      else none
    else none
  let (packedVal, pairEq) ← match extractFast? with
    | some (origVec, fastThm) =>
      let p := mkAppN (mkConst fastThm) #[loAddr, hiAddr, origVec, hab]
      pure (origVec, p)
    | none =>
      let catVal ← mkAppM ``HAppend.hAppend #[hiVal, loVal]
      let pairThm := match targetW with
        | .w16 => ``pointsTo8_pair_at
        | .w32 => ``pointsTo16_pair_at
        | .w64 => ``pointsTo32_pair_at
        | .w128 => ``pointsTo64_pair_at
        | .w8 => ``pointsTo8_pair_at
      let p := mkAppN (mkConst pairThm) #[loAddr, hiAddr, loVal, hiVal, catVal, hab, ← mkEqRefl catVal]
      pure (catVal, p)
  let sliceAtoms ← slice.mapM (fun x => instantiateMVars x.canonAtom)
  let loAtoms ← loSlice.mapM (fun x => instantiateMVars x.canonAtom)
  let hiAtoms ← hiSlice.mapM (fun x => instantiateMVars x.canonAtom)
  let fullSep := ProofLib.SepSolver.mkSepList sliceAtoms
  let splitSep := ProofLib.SepSolver.mkSep
    (ProofLib.SepSolver.mkSepList loAtoms)
    (ProofLib.SepSolver.mkSepList hiAtoms)
  let assocEq ←
    if fullSep == splitSep then mkEqRefl fullSep
    else ProofLib.SepSolver.eqAC fullSep splitSep
  let pCongr ← mkCongr (← mkCongrArg (mkConst ``SepProp.sepConj) loEq) hiEq
  let pTot ← mkEqTrans assocEq (← mkEqTrans pCongr pairEq)
  let targetAtom := mkApp2 (mkConst targetW.rwConst) loAddr packedVal
  return (packedVal, ← mkExpectedTypeHint pTot (← mkEq fullSep targetAtom))

/-- Join a contiguous slice of `.rwUninit` (`memRegion`) atoms into one `memRegion c₀ totalLen`. -/
def joinMemRegionSlice (root : Expr) (slice : Array ParsedAtom) : MetaM (Expr × Nat × Option Expr) := do
  let n := slice.size
  let last := slice[n - 1]!
  let mut curAddr := last.addr?.get!.canonExpr
  let mut curOff := last.addr?.get!.byteOff
  let mut curLen := last.byteLen
  let mut curEq? : Option Expr := none
  let mut idx := n - 1
  while idx > 0 do
    idx := idx - 1
    let it := slice[idx]!
    let aAddr := it.addr?.get!.canonExpr
    let aOff := it.addr?.get!.byteOff
    let aLen := it.byteLen
    let newLen := aLen + curLen
    let hab ← proveCanonAddrStep root aOff aLen aAddr curAddr
    let newLenExpr := toExpr newLen
    let joinStep := mkAppN (mkConst ``memRegion_join_at)
      #[aAddr, curAddr, toExpr aLen, toExpr curLen, newLenExpr,
        hab, mkEqReflNat newLenExpr, rflTrueExpr]
    curEq? ← match curEq? with
      | none => pure (some joinStep)
      | some prevEq =>
        let tailSep := ProofLib.SepSolver.mkSepList ((slice.extract (idx + 1) n).map (·.canonAtom))
        let curReg := mkApp2 (mkConst ``Arm64.memRegion) curAddr (toExpr curLen)
        let pRight ← mkCongrArg (mkApp (mkConst ``SepProp.sepConj) it.canonAtom)
          (← mkExpectedTypeHint prevEq (← mkEq tailSep curReg))
        pure (some (← mkEqTrans pRight joinStep))
    curAddr := aAddr
    curOff := aOff
    curLen := newLen
  return (curAddr, curLen, curEq?)

/-- Single-atom weakening `it.canonAtom ⊢ memRegion it.addr it.byteLen`. -/
def atomEntailsMemRegion (it : ParsedAtom) : MetaM Expr := do
  let c := it.addr?.get!.canonExpr
  let canonAtom ← instantiateMVars it.canonAtom
  match it.kind with
  | .rwUninit => return mkApp (mkConst ``Entails.refl) canonAtom
  | .rwTyped .w8 v => return mkApp2 (mkConst ``ProofLib.pointsTo8_entails_memRegion) c (← instantiateMVars v)
  | .rwTyped .w16 v => return mkApp2 (mkConst ``ProofLib.pointsTo16_entails_memRegion) c (← instantiateMVars v)
  | .rwTyped .w32 v => return mkApp2 (mkConst ``ProofLib.pointsTo32_entails_memRegion) c (← instantiateMVars v)
  | .rwTyped .w64 v => return mkApp2 (mkConst ``ProofLib.pointsTo64_entails_memRegion) c (← instantiateMVars v)
  | .rwTyped .w128 v => return mkApp2 (mkConst ``pointsTo128_entails_memRegion) c (← instantiateMVars v)
  | .rwBytes bs hLen =>
    return mkApp4 (mkConst ``ProofLib.pointsToBytes_entails_memRegion_of_length)
      c (← instantiateMVars bs) (toExpr it.byteLen) hLen
  | .rwWords64 ws k hLen =>
    let nExpr := toExpr it.byteLen
    return mkAppN (mkConst ``pointsToWords64_entails_memRegion_len)
      #[c, ← instantiateMVars ws, toExpr k, nExpr, hLen, mkEqReflNat nExpr, rflTrueExpr]
  | _ => throwError "sep_interval: atom {canonAtom} cannot weaken to memRegion"

/-- Weaken a contiguous slice of RW atoms into `memRegion c₀ totalLen`. -/
def sliceEntailsMemRegion (root : Expr) (slice : Array ParsedAtom) : MetaM Expr := do
  let n := slice.size
  let last := slice[n - 1]!
  let mut curAddr := last.addr?.get!.canonExpr
  let mut curOff := last.addr?.get!.byteOff
  let mut curLen := last.byteLen
  let mut curEnt ← atomEntailsMemRegion last
  let mut curTailExpr ← instantiateMVars last.canonAtom
  let mut idx := n - 1
  while idx > 0 do
    idx := idx - 1
    let it := slice[idx]!
    let aAddr := it.addr?.get!.canonExpr
    let aOff := it.addr?.get!.byteOff
    let aLen := it.byteLen
    let newLen := aLen + curLen
    let newLenExpr := toExpr newLen
    let hab ← proveCanonAddrStep root aOff aLen aAddr curAddr
    let itCanon ← instantiateMVars it.canonAtom
    curEnt ← match it.kind with
      | .rwTyped .w64 v =>
        pure <| mkAppN (mkConst ``entails_memRegion_pts64_cons)
          #[curTailExpr, aAddr, curAddr, ← instantiateMVars v, toExpr curLen, newLenExpr,
            curEnt, hab, mkEqReflNat newLenExpr, rflTrueExpr]
      | _ =>
        let hHead ← atomEntailsMemRegion it
        pure <| mkAppN (mkConst ``entails_memRegion_cons)
          #[itCanon, curTailExpr, aAddr, curAddr, toExpr aLen, toExpr curLen, newLenExpr,
            hHead, curEnt, hab, mkEqReflNat newLenExpr, rflTrueExpr]
    curTailExpr := ProofLib.SepSolver.mkSep itCanon curTailExpr
    curAddr := aAddr
    curOff := aOff
    curLen := newLen
  return curEnt

/-- Wrap an equality `A = B` as either `A = B` (`eqMode = true`) or `Entails.of_eq` (`eqMode = false`). -/
def liftEqToMode (eqMode : Bool) (a b eqPrf : Expr) : Expr :=
  if eqMode then eqPrf
  else mkApp3 (mkConst ``Entails.of_eq) a b eqPrf

/-- Solve a single RW root bucket by $O(K \log K)$ interval sorting + sweep-line subsumption/carving/packing. -/
def solveRWBucket (eqMode : Bool) (root : Expr) (lhsRaw rhsRaw : Array ParsedAtom) :
    TacticM (Array SegmentPlan) := do
  let cmp (a b : ParsedAtom) : Bool :=
    let oa := a.addr?.get!.byteOff
    let ob := b.addr?.get!.byteOff
    if oa != ob then oa < ob else a.byteLen < b.byteLen
  let lhs := lhsRaw.qsort cmp
  let rhs := rhsRaw.qsort cmp
  for h : k in [:lhs.size] do
    if k + 1 < lhs.size then
      let endK := lhs[k].addr?.get!.byteOff + (lhs[k].byteLen : Int)
      let nextOff := lhs[k + 1]!.addr?.get!.byteOff
      if endK > nextOff then
        throwError "sep_interval: overlapping LHS intervals at root {root}: [{lhs[k].addr?.get!.byteOff}, {endK}) vs {nextOff}"
  for h : k in [:rhs.size] do
    if k + 1 < rhs.size then
      let endK := rhs[k].addr?.get!.byteOff + (rhs[k].byteLen : Int)
      let nextOff := rhs[k + 1]!.addr?.get!.byteOff
      if endK > nextOff then
        throwError "sep_interval: overlapping RHS intervals at root {root}: [{rhs[k].addr?.get!.byteOff}, {endK}) vs {nextOff}"
  let mut plans : Array SegmentPlan := #[]
  let mut i := 0
  let mut j := 0
  while i < lhs.size || j < rhs.size do
    if i >= lhs.size then
      throwError "sep_interval: unmatched RHS interval {rhs[j]!.canonAtom} at {root}"
    if j >= rhs.size then
      throwError "sep_interval: unmatched LHS interval {lhs[i]!.canonAtom} at {root}"
    let h0 := lhs[i]!
    let g0 := rhs[j]!
    let startOff := h0.addr?.get!.byteOff
    if startOff != g0.addr?.get!.byteOff then
      throwError "sep_interval: interval start mismatch at root {root}: LHS {startOff} ({h0.canonAtom}) vs RHS {g0.addr?.get!.byteOff} ({g0.canonAtom})"
    let mut i' := i + 1
    let mut j' := j + 1
    let mut lhsEnd := startOff + (h0.byteLen : Int)
    let mut rhsEnd := startOff + (g0.byteLen : Int)
    while lhsEnd != rhsEnd do
      if lhsEnd < rhsEnd then
        if i' >= lhs.size || lhs[i']!.addr?.get!.byteOff != lhsEnd then
          throwError "sep_interval: gap in LHS covering [{startOff}, {rhsEnd}) at offset {lhsEnd} (root {root})"
        lhsEnd := lhsEnd + (lhs[i']!.byteLen : Int)
        i' := i' + 1
      else
        if j' >= rhs.size || rhs[j']!.addr?.get!.byteOff != rhsEnd then
          throwError "sep_interval: gap in RHS covering [{startOff}, {lhsEnd}) at offset {rhsEnd} (root {root})"
        rhsEnd := rhsEnd + (rhs[j']!.byteLen : Int)
        j' := j' + 1
    let lSlice := lhs.extract i i'
    let rSlice := rhs.extract j j'
    let lExprs ← lSlice.mapM (fun x => instantiateMVars x.canonAtom)
    let rExprs ← rSlice.mapM (fun x => instantiateMVars x.canonAtom)
    let lSep := ProofLib.SepSolver.mkSepList lExprs
    let rSep := ProofLib.SepSolver.mkSepList rExprs
    -- Case 1: Identical single atom
    if lSlice.size == 1 && rSlice.size == 1 && lSep == rSep then
      let reflEq ← mkEqRefl lSep
      plans := plans.push { lhsAtoms := lExprs, rhsAtoms := rExprs,
                            proof := liftEqToMode eqMode lSep rSep reflEq }
    -- Case 2: All RHS atoms in `[startOff, rhsEnd)` are `.rwUninit` (`memRegion` / `cells` / `stackAt` / `∃∗`)
    else if rSlice.all (fun x => x.kind matches .rwUninit) then
      let (_, _, rhsJoinEq?) ← joinMemRegionSlice root rSlice
      if lSlice.all (fun x => x.kind matches .rwUninit) then
        let (_, _, lhsJoinEq?) ← joinMemRegionSlice root lSlice
        let eqPrf ← match lhsJoinEq?, rhsJoinEq? with
          | none, none => mkEqRefl lSep
          | some le, none => pure le
          | none, some re => mkEqSymm re
          | some le, some re => mkEqTrans le (← mkEqSymm re)
        let eqPrf ← mkExpectedTypeHint eqPrf (← mkEq lSep rSep)
        plans := plans.push { lhsAtoms := lExprs, rhsAtoms := rExprs,
                              proof := liftEqToMode eqMode lSep rSep eqPrf }
      else if eqMode then
        throwError "sep_interval_eq: cannot weaken concrete typed cells {lSep} to uninitialized {rSep} in `=` mode (use `sep_interval` for `⊢`)"
      else
        let lhsEnt ← sliceEntailsMemRegion root lSlice
        let segPrf ← match rhsJoinEq? with
          | none => pure lhsEnt
          | some re =>
            let regExpr := mkApp2 (mkConst ``Arm64.memRegion) h0.addr?.get!.canonExpr (toExpr ((rhsEnd - startOff).toNat))
            pure <| mkAppN (mkConst ``entails_of_eq_both)
              #[lSep, lSep, regExpr, rSep, ← mkEqRefl lSep, lhsEnt, ← mkEqSymm re]
        plans := plans.push { lhsAtoms := lExprs, rhsAtoms := rExprs, proof := segPrf }
    -- Case 3: Single RHS `.rwTyped wG valG` packed from 1..16 LHS `.rwTyped` cells
    else if rSlice.size == 1 && (rSlice[0]!.kind matches .rwTyped ..) &&
            lSlice.all (fun x => x.kind matches .rwTyped ..) then
      let .rwTyped wG valG := rSlice[0]!.kind | unreachable!
      let (packedVal, packEq) ← packTypedSlice root lSlice startOff wG
      let valG ← instantiateMVars valG
      let finalEq ←
        if packedVal == valG then pure packEq
        else do
          let hv ← proveValueEq packedVal valG
          let valG' ← instantiateMVars valG
          if packedVal == valG' then pure packEq
          else
            let pVal ← mkCongrArg (mkApp (mkConst wG.rwConst) rSlice[0]!.addr?.get!.canonExpr) hv
            mkEqTrans packEq pVal
      let rExprs' ← rSlice.mapM (fun x => instantiateMVars x.canonAtom)
      let rSep' := ProofLib.SepSolver.mkSepList rExprs'
      let finalEq ← mkExpectedTypeHint finalEq (← mkEq lSep rSep')
      plans := plans.push { lhsAtoms := lExprs, rhsAtoms := rExprs',
                            proof := liftEqToMode eqMode lSep rSep' finalEq }
    -- Case 4: Single LHS `.rwTyped wH valH` unpacked into 1..16 RHS `.rwTyped` cells
    else if lSlice.size == 1 && (lSlice[0]!.kind matches .rwTyped ..) &&
            rSlice.all (fun x => x.kind matches .rwTyped ..) then
      let .rwTyped wH valH := lSlice[0]!.kind | unreachable!
      let valH ← instantiateMVars valH
      let (packedVal, packEq) ← packTypedSlice root rSlice startOff wH
      let rToPacked ←
        if packedVal == valH then pure packEq
        else do
          let hv ← proveValueEq packedVal valH
          let packedVal' ← instantiateMVars packedVal
          if packedVal' == valH then pure (← instantiateMVars packEq)
          else
            let pVal ← mkCongrArg (mkApp (mkConst wH.rwConst) lSlice[0]!.addr?.get!.canonExpr) hv
            mkEqTrans (← instantiateMVars packEq) pVal
      let rExprs' ← rSlice.mapM (fun x => instantiateMVars x.canonAtom)
      let rSep' := ProofLib.SepSolver.mkSepList rExprs'
      let finalEq ← mkExpectedTypeHint (← mkEqSymm rToPacked) (← mkEq lSep rSep')
      plans := plans.push { lhsAtoms := lExprs, rhsAtoms := rExprs',
                            proof := liftEqToMode eqMode lSep rSep' finalEq }
    -- Case 5: Single `.rwBytes` or `.rwWords64` congruence
    else if lSlice.size == 1 && rSlice.size == 1 && lSep.getAppFn == rSep.getAppFn &&
            ((lSlice[0]!.kind matches .rwBytes ..) || (lSlice[0]!.kind matches .rwWords64 ..)) then
      let hv ← proveValueEq (lSep.getArg! 1) (rSep.getArg! 1)
      let rExprs' ← rSlice.mapM (fun x => instantiateMVars x.canonAtom)
      let rSep' := ProofLib.SepSolver.mkSepList rExprs'
      let pCongr ← mkCongrArg (mkApp lSep.getAppFn (lSep.getArg! 0)) hv
      let pCongr ← mkExpectedTypeHint pCongr (← mkEq lSep rSep')
      plans := plans.push { lhsAtoms := lExprs, rhsAtoms := rExprs',
                            proof := liftEqToMode eqMode lSep rSep' pCongr }
    else if lSlice.any (fun x => x.kind matches .rwUninit) then
      throwError "sep_interval: cannot strengthen uninitialized memory {lSep} to typed assertion {rSep}"
    else
      throwError "sep_interval: unsupported mixed representation transition {lSep} -> {rSep}"
    i := i'
    j := j'
  return plans

/-- Prove `(sliceExpr : List (BitVec 8)) = expectedBytes` by `isDefEq` fast path or bytewise `bv_slice`. -/
private def proveROSliceBytesEq? (sliceExpr expectedBytes : Expr) : TacticM (Option Expr) := do
  let sliceExpr ← instantiateMVars sliceExpr
  let expectedBytes ← instantiateMVars expectedBytes
  if ← withTransparency .default (isDefEq sliceExpr expectedBytes) then
    let expectedBytes ← instantiateMVars expectedBytes
    return some (← mkExpectedTypeHint (← mkEqRefl expectedBytes) (← mkEq sliceExpr expectedBytes))
  let eqTy ← mkEq sliceExpr expectedBytes
  let mvar ← mkFreshExprMVar eqTy
  let (gs, _) ← try
    runTactic mvar.mvarId! (← `(tactic| (
      simp only [List.drop, List.take, ProofLib.unpack64, ProofLib.unpack32, ProofLib.unpack16,
        List.cons_append, List.nil_append, List.cons.injEq, and_true]
      first | rfl | (repeat' constructor <;> bv_slice))))
  catch _ =>
    pure ([mvar.mvarId!], {})
  if gs.isEmpty then
    return some (← instantiateMVars mvar)
  return none

/-- Try proving `(dupAtom ∗ survAtom) = survAtom` for `.ro` atoms (exact duplicate or subslice). -/
def proveROAbsorb? (root : Expr) (dup surv : ParsedAtom) : TacticM (Option Expr) := do
  let .roChunk _ _ _ viewD? := dup.kind | return none
  let .roChunk fnS payS _ viewS? := surv.kind | return none
  let dupCanon ← instantiateMVars dup.canonAtom
  let survCanon ← instantiateMVars surv.canonAtom
  if dupCanon == survCanon || (← withReducibleAndInstances (isDefEq dupCanon survCanon)) then
    let some dupThm := roDupThmOf? fnS | return none
    let dupCanon ← instantiateMVars dupCanon
    let survCanon ← instantiateMVars survCanon
    let prf := mkApp2 (mkConst dupThm) surv.addr?.get!.canonExpr (← instantiateMVars payS)
    let goalTy ← mkEq (ProofLib.SepSolver.mkSep dupCanon survCanon) survCanon
    return some (← mkExpectedTypeHint prf goalTy)
  if let (some viewD, some viewS) := (viewD?, viewS?) then
    let offS := surv.addr?.get!.byteOff
    let offD := dup.addr?.get!.byteOff
    if offS ≤ offD && offD + (viewD.byteLen : Int) ≤ offS + (viewS.byteLen : Int) then
      let relOff := (offD - offS).toNat
      let dropExpr ← mkAppM ``List.drop #[toExpr relOff, viewS.bytesExpr]
      let sliceExpr ← mkAppM ``List.take #[toExpr viewD.byteLen, dropExpr]
      if let some hSlice ← proveROSliceBytesEq? sliceExpr viewD.bytesExpr then
        let hAddr ← proveCanonAddrStep root offS relOff surv.addr?.get!.canonExpr dup.addr?.get!.canonExpr
        let dupCanon ← instantiateMVars dup.canonAtom
        let survCanon ← instantiateMVars surv.canonAtom
        let prf := mkAppN (mkConst ``ro_absorb_via_bytes)
          #[dupCanon, survCanon, surv.addr?.get!.canonExpr, dup.addr?.get!.canonExpr,
            ← instantiateMVars viewS.bytesExpr, ← instantiateMVars viewD.bytesExpr,
            toExpr viewS.byteLen, toExpr relOff, toExpr viewD.byteLen,
            ← instantiateMVars viewD.eqBytesRO, ← instantiateMVars viewS.eqBytesRO,
            hAddr, viewS.hLen, rflTrueExpr, hSlice]
        return some prf
  return none

/-- Reduce a side's `.ro` bucket into duplicate-free survivors `S_k`, returning `(survivors, perSurvivorAtomsAndEq)`. -/
def reduceROSide (root : Expr) (items : Array ParsedAtom) :
    TacticM (Array (ParsedAtom × Array Expr × Option Expr)) := do
  let isBytesRO (x : ParsedAtom) : Bool :=
    match x.kind with
    | .roChunk fn _ _ _ => fn == ``Arm64.pointsToBytesRO
    | _ => false
  let sorted := items.qsort fun a b =>
    let oa := a.addr?.get!.byteOff
    let ob := b.addr?.get!.byteOff
    if oa != ob then oa < ob
    else if a.byteLen != b.byteLen then a.byteLen > b.byteLen
    else if isBytesRO a != isBytesRO b then isBytesRO a
    else a.canonAtom.lt b.canonAtom
  let mut groups : Array (ParsedAtom × Array (Expr × Expr)) := #[]
  for it in sorted do
    let mut absorbed := false
    for gIdx in [:groups.size] do
      let (surv, dups) := groups[gIdx]!
      if let some hAbs ← proveROAbsorb? root it surv then
        let itCanon ← instantiateMVars it.canonAtom
        groups := groups.set! gIdx (surv, dups.push (itCanon, hAbs))
        absorbed := true
        break
    if !absorbed then
      groups := groups.push (it, #[])
  let mut out : Array (ParsedAtom × Array Expr × Option Expr) := #[]
  for (surv, dups) in groups do
    let survCanon ← instantiateMVars surv.canonAtom
    if dups.isEmpty then
      out := out.push (surv, #[survCanon], none)
    else
      let mut atomsSeq : Array Expr := #[]
      for (dExpr, _) in dups do
        atomsSeq := atomsSeq.push (← instantiateMVars dExpr)
      atomsSeq := atomsSeq.push survCanon
      let mut curRest := survCanon
      let mut curEq ← mkEqRefl survCanon
      let mut k := dups.size
      while k > 0 do
        k := k - 1
        let (dExprRaw, hDupRaw) := dups[k]!
        let dExpr ← instantiateMVars dExprRaw
        let hDup ← instantiateMVars hDupRaw
        if curRest == survCanon then
          curEq := hDup
        else
          curEq := mkAppN (mkConst ``ro_absorb_step) #[dExpr, curRest, survCanon, curEq, hDup]
        curRest := ProofLib.SepSolver.mkSep dExpr curRest
      out := out.push (surv, atomsSeq, some curEq)
  return out

/-- Solve `.ro` bucket across LHS and RHS (`eqMode = true` or `false`). -/
def solveROBucket (eqMode : Bool) (root : Expr) (lhsRO rhsRO : Array ParsedAtom) :
    TacticM (Array SegmentPlan) := do
  let lGroups ← reduceROSide root lhsRO
  let rGroups ← reduceROSide root rhsRO
  if lGroups.size != rGroups.size then
    throwError "sep_interval: `.ro` bucket count mismatch at root {root}: LHS has {lGroups.size} distinct `.ro` resources vs RHS {rGroups.size}"
  let mut plans : Array SegmentPlan := #[]
  for h : idx in [:lGroups.size] do
    let (lSurv, lSeq, lEq?) := lGroups[idx]
    let (rSurv, rSeq, rEq?) := rGroups[idx]!
    let lSurvAtom ← instantiateMVars lSurv.canonAtom
    let rSurvAtom ← instantiateMVars rSurv.canonAtom
    unless lSurvAtom == rSurvAtom ||
           (← withReducibleAndInstances (isDefEq lSurvAtom rSurvAtom)) do
      throwError "sep_interval: `.ro` resource mismatch {lSurvAtom} vs {rSurvAtom}"
    let lSeq ← lSeq.mapM instantiateMVars
    let rSeq ← rSeq.mapM instantiateMVars
    let lSurvAtom ← instantiateMVars lSurvAtom
    let rSurvAtom ← instantiateMVars rSurvAtom
    let lSep := ProofLib.SepSolver.mkSepList lSeq
    let rSep := ProofLib.SepSolver.mkSepList rSeq
    let pMid ←
      if lSurvAtom == rSurvAtom then mkEqRefl lSurvAtom
      else mkExpectedTypeHint (← mkEqRefl rSurvAtom) (← mkEq lSurvAtom rSurvAtom)
    let p1 ← match lEq? with | some le => mkEqTrans (← instantiateMVars le) pMid | none => pure pMid
    let eqTot ← match rEq? with | some re => mkEqTrans p1 (← mkEqSymm (← instantiateMVars re)) | none => pure p1
    let eqTot ← mkExpectedTypeHint eqTot (← mkEq lSep rSep)
    plans := plans.push { lhsAtoms := lSeq, rhsAtoms := rSeq,
                          proof := liftEqToMode eqMode lSep rSep eqTot }
  return plans

/-- Pre-unify unassigned list metavariables `?bs` / `?ws` in RHS `pointsToBytes` / `pointsToWords64`
    against matching LHS slices at the same canonical `(root, byteOff)`. -/
private def preUnifySliceMVars (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (rawLhs rawRhs : Array Expr) : MetaM Unit := do
  let sliceHeads := #[``Arm64.pointsToBytes, ``Arm64.pointsToWords64,
                      ``Arm64.pointsToBytesRO, ``Arm64.pointsToWords64RO]
  for rAtom0 in rawRhs do
    let rAtom := (ProofLib.SepSolver.stripMData (← instantiateMVars rAtom0)).headBeta
    let some rFn := rAtom.getAppFn.constName? | continue
    unless sliceHeads.contains rFn && rAtom.getAppNumArgs == 2 do continue
    let rPay ← instantiateMVars (rAtom.getArg! 1)
    unless rPay.isMVar do continue
    let some rLa ← (try some <$> canonAddr64 ctx cacheRef (rAtom.getArg! 0) catch _ => pure none) | continue
    let mut candidates : Array Expr := #[]
    for lAtom0 in rawLhs do
      let lAtom := (ProofLib.SepSolver.stripMData (← instantiateMVars lAtom0)).headBeta
      if lAtom.getAppFn.constName? == some rFn && lAtom.getAppNumArgs == 2 then
        if let some lLa ← (try some <$> canonAddr64 ctx cacheRef (lAtom.getArg! 0) catch _ => pure none) then
          if lLa.byteOff == rLa.byteOff &&
             (lLa.root == rLa.root || (← withReducibleAndInstances (isDefEq lLa.root rLa.root))) then
            candidates := candidates.push (lAtom.getArg! 1)
    if candidates.size == 1 then
      let _ ← isDefEq rPay candidates[0]!

/-- Main core solver producing either `P₀ = Q₀` (`eqMode = true`) or `P₀ ⊢ Q₀` (`eqMode = false`). -/
partial def solveIntervalCore (eqMode : Bool) (P₀ Q₀ : Expr) : TacticM Expr := do
  let P₀ ← instantiateMVars P₀
  let Q₀ ← instantiateMVars Q₀
  let P_unf ← unfoldBundlesDeep P₀
  let Q_unf ← unfoldBundlesDeep Q₀
  let (P_ex, hP_ex?) ← pushPrenexSepExists P_unf
  let (Q_ex, hQ_ex?) ← pushPrenexSepExists Q_unf
  if !eqMode then
    let pAtoms := ProofLib.SepSolver.atoms P_ex
    -- 1. Peel non-single-cell LHS `∃∗ x, ...` conjuncts via `Entails.sepExists_elim`
    if let some exIdx := pAtoms.findIdx? (fun a =>
        a.isAppOfArity ``SepProp.sepExists 2 && !isSingleCellSepExists a) then
      let exAtom := pAtoms[exIdx]!
      let α := exAtom.getArg! 0
      if let .lam n ty body bi := (exAtom.getArg! 1).consumeMData then
        let u ← getLevel α
        let lam := exAtom.getArg! 1
        let restAtoms := pAtoms.eraseIdx! exIdx
        if restAtoms.isEmpty then
          let hPerm ← if P_ex == exAtom then mkEqRefl P_ex else ProofLib.SepSolver.eqAC P_ex exAtom
          let hPre ← match hP_ex? with | some hx => mkEqTrans hx hPerm | none => pure hPerm
          let hPre ← mkExpectedTypeHint hPre (← mkEq P₀ exAtom)
          let hFun ← withLocalDecl n bi ty fun fv => do
            let subPrf ← solveIntervalCore false (body.instantiate1 fv) Q₀
            mkLambdaFVars #[fv] subPrf
          let entEx := mkApp4 (mkConst ``Entails.sepExists_elim [u]) α lam Q₀ hFun
          return mkAppN (mkConst ``entails_of_eq_both)
            #[P₀, exAtom, Q₀, Q₀, hPre, entEx, ← mkEqRefl Q₀]
        else
          let restExpr := ProofLib.SepSolver.mkSepList restAtoms
          let frontConj := ProofLib.SepSolver.mkSep exAtom restExpr
          let hPerm ← if P_ex == frontConj then mkEqRefl P_ex else ProofLib.SepSolver.eqAC P_ex frontConj
          let hLift := mkApp3 (mkConst ``sepExists_sepConj_left [u]) α lam restExpr
          let lamCombined := Expr.lam n ty (ProofLib.SepSolver.mkSep body restExpr) bi
          let liftedEx := mkApp2 (mkConst ``SepProp.sepExists [u]) α lamCombined
          let hPre0 ← match hP_ex? with | some hx => mkEqTrans hx hPerm | none => pure hPerm
          let hPre ← mkExpectedTypeHint (← mkEqTrans hPre0 hLift) (← mkEq P₀ liftedEx)
          let hFun ← withLocalDecl n bi ty fun fv => do
            let subPrf ← solveIntervalCore false (ProofLib.SepSolver.mkSep (body.instantiate1 fv) restExpr) Q₀
            mkLambdaFVars #[fv] subPrf
          let entEx := mkApp4 (mkConst ``Entails.sepExists_elim [u]) α lamCombined Q₀ hFun
          return mkAppN (mkConst ``entails_of_eq_both)
            #[P₀, liftedEx, Q₀, Q₀, hPre, entEx, ← mkEqRefl Q₀]
    -- 2. Peel LHS pure `⌜φ⌝` conjuncts via `Entails.pure_left` before collecting context facts
    if let some pIdx := pAtoms.findIdx? (fun a => a.isAppOfArity ``SepProp.pure 1) then
      let pureAtom := pAtoms[pIdx]!
      let φ := pureAtom.getArg! 0
      let restAtoms := pAtoms.eraseIdx! pIdx
      let restExpr := ProofLib.SepSolver.mkSepList restAtoms
      let frontExpr := if restAtoms.isEmpty then pureAtom else ProofLib.SepSolver.mkSep pureAtom restExpr
      let hPerm ← if P_ex == frontExpr then mkEqRefl P_ex else ProofLib.SepSolver.eqAC P_ex frontExpr
      let hPre ← match hP_ex? with | some hx => mkEqTrans hx hPerm | none => pure hPerm
      let hPre ← mkExpectedTypeHint hPre (← mkEq P₀ frontExpr)
      let bodyPrf ← withLocalDeclD `hPure φ fun fv => do
        let subGoal ←
          if restAtoms.isEmpty then solveIntervalCore false (mkConst ``SepProp.emp) Q₀
          else solveIntervalCore false restExpr Q₀
        mkLambdaFVars #[fv] subGoal
      let entFront :=
        if restAtoms.isEmpty then
          mkApp3 (mkConst ``Entails.pure_left_only) φ Q₀ bodyPrf
        else
          mkApp4 (mkConst ``Entails.pure_left) φ restExpr Q₀ bodyPrf
      return mkAppN (mkConst ``entails_of_eq_both)
        #[P₀, frontExpr, Q₀, Q₀, hPre, entFront, ← mkEqRefl Q₀]
    -- 3. Synthesize witnesses for non-single-cell RHS `∃∗ x, ...` conjuncts via `Entails.sepExists_right`
    let qAtoms := ProofLib.SepSolver.atoms Q_ex
    if let some exIdx := qAtoms.findIdx? (fun a =>
        a.isAppOfArity ``SepProp.sepExists 2 && !isSingleCellSepExists a) then
      let exAtom := qAtoms[exIdx]!
      let α := exAtom.getArg! 0
      if let .lam n ty body bi := (exAtom.getArg! 1).consumeMData then
        let u ← getLevel α
        let lam := exAtom.getArg! 1
        let restAtoms := qAtoms.eraseIdx! exIdx
        let wMVar ← mkFreshExprMVar (some α)
        if restAtoms.isEmpty then
          let hPerm ← if Q_ex == exAtom then mkEqRefl Q_ex else ProofLib.SepSolver.eqAC Q_ex exAtom
          let hQ_pre ← match hQ_ex? with | some hx => mkEqTrans hx hPerm | none => pure hPerm
          let subPrf ← solveIntervalCore false P_ex (body.instantiate1 wMVar)
          if !(← wMVar.mvarId!.isAssigned) then
            let some defInst ← synthInstance? (mkApp (mkConst ``Inhabited [u]) α)
              | throwError "sep_interval: could not synthesize witness for existential {exAtom}"
            wMVar.mvarId!.assign (mkApp2 (mkConst ``default [u]) α defInst)
          let wVal ← instantiateMVars wMVar
          let subPrf ← instantiateMVars subPrf
          let exPrf := mkApp5 (mkConst ``Entails.sepExists_right [u]) α P_ex lam wVal subPrf
          let hP ← match hP_ex? with
            | some hp => mkExpectedTypeHint hp (← mkEq P₀ P_ex)
            | none => mkExpectedTypeHint (← mkEqRefl P_ex) (← mkEq P₀ P_ex)
          let hQ ← mkExpectedTypeHint (← mkEqSymm (← instantiateMVars hQ_pre)) (← mkEq exAtom Q₀)
          return mkAppN (mkConst ``entails_of_eq_both) #[P₀, P_ex, exAtom, Q₀, hP, exPrf, hQ]
        else
          let restExpr := ProofLib.SepSolver.mkSepList restAtoms
          let frontConj := ProofLib.SepSolver.mkSep exAtom restExpr
          let hPerm ← if Q_ex == frontConj then mkEqRefl Q_ex else ProofLib.SepSolver.eqAC Q_ex frontConj
          let hLift := mkApp3 (mkConst ``sepExists_sepConj_left [u]) α lam restExpr
          let lamCombined := Expr.lam n ty (ProofLib.SepSolver.mkSep body restExpr) bi
          let liftedEx := mkApp2 (mkConst ``SepProp.sepExists [u]) α lamCombined
          let hQ_pre0 ← match hQ_ex? with | some hx => mkEqTrans hx hPerm | none => pure hPerm
          let hQ_pre ← mkEqTrans hQ_pre0 hLift
          let instRhs := ProofLib.SepSolver.mkSep (body.instantiate1 wMVar) restExpr
          let subPrf ← solveIntervalCore false P_ex instRhs
          if !(← wMVar.mvarId!.isAssigned) then
            let some defInst ← synthInstance? (mkApp (mkConst ``Inhabited [u]) α)
              | throwError "sep_interval: could not synthesize witness for existential {exAtom}"
            wMVar.mvarId!.assign (mkApp2 (mkConst ``default [u]) α defInst)
          let wVal ← instantiateMVars wMVar
          let subPrf ← instantiateMVars subPrf
          let lamCombined ← instantiateMVars lamCombined
          let liftedEx ← instantiateMVars liftedEx
          let exPrf := mkApp5 (mkConst ``Entails.sepExists_right [u]) α P_ex lamCombined wVal subPrf
          let hP ← match hP_ex? with
            | some hp => mkExpectedTypeHint hp (← mkEq P₀ P_ex)
            | none => mkExpectedTypeHint (← mkEqRefl P_ex) (← mkEq P₀ P_ex)
          let hQ ← mkExpectedTypeHint (← mkEqSymm (← instantiateMVars hQ_pre)) (← mkEq liftedEx (← instantiateMVars Q₀))
          return mkAppN (mkConst ``entails_of_eq_both) #[P₀, P_ex, liftedEx, ← instantiateMVars Q₀, hP, exPrf, hQ]
  let ctx ← collectCtxFacts
  let cacheRef ← IO.mkRef ({} : Std.HashMap Expr LinAddr64)
  let rawLhs := ProofLib.SepSolver.atoms P_ex
  let rawRhs := ProofLib.SepSolver.atoms Q_ex
  if !eqMode then
    preUnifySliceMVars ctx cacheRef rawLhs rawRhs
  let parsedLhs ← (rawLhs.mapM (parseAtom ctx cacheRef) : MetaM _)
  let parsedRhs ← (rawRhs.mapM (parseAtom ctx cacheRef) : MetaM _)
  -- Partition `lhsKept` and `rhsKept` after spine canonicalization
  let (_, lhsKept, hP_can?) ← buildSpineCanonEq parsedLhs
  let (_, rhsKept, hQ_can?) ← buildSpineCanonEq parsedRhs
  let mut roots : Array Expr := #[]
  let findOrAddRoot (rs : Array Expr) (r : Expr) : MetaM (Nat × Array Expr) := do
    for h : k in [:rs.size] do
      if rs[k] == r then return (k, rs)
    for h : k in [:rs.size] do
      if ← withReducibleAndInstances (isDefEq rs[k] r) then return (k, rs)
    return (rs.size, rs.push r)
  let mut lhsRW : Array (Array ParsedAtom) := #[]
  let mut rhsRW : Array (Array ParsedAtom) := #[]
  let mut lhsRO : Array (Array ParsedAtom) := #[]
  let mut rhsRO : Array (Array ParsedAtom) := #[]
  let mut lhsOpaque : Array ParsedAtom := #[]
  let mut rhsOpaque : Array ParsedAtom := #[]
  for it in lhsKept do
    match it.addr?, it.kind with
    | _, .opaqueAtom => lhsOpaque := lhsOpaque.push it
    | some la, .roChunk .. =>
      let (rIdx, rs') ← findOrAddRoot roots la.root
      if rs'.size > roots.size then
        roots := rs'
        lhsRW := lhsRW.push #[]; rhsRW := rhsRW.push #[]
        lhsRO := lhsRO.push #[]; rhsRO := rhsRO.push #[]
      lhsRO := lhsRO.set! rIdx (lhsRO[rIdx]!.push it)
    | some la, _ =>
      let (rIdx, rs') ← findOrAddRoot roots la.root
      if rs'.size > roots.size then
        roots := rs'
        lhsRW := lhsRW.push #[]; rhsRW := rhsRW.push #[]
        lhsRO := lhsRO.push #[]; rhsRO := rhsRO.push #[]
      lhsRW := lhsRW.set! rIdx (lhsRW[rIdx]!.push it)
    | none, _ => lhsOpaque := lhsOpaque.push it
  for it in rhsKept do
    match it.addr?, it.kind with
    | _, .opaqueAtom => rhsOpaque := rhsOpaque.push it
    | some la, .roChunk .. =>
      let (rIdx, rs') ← findOrAddRoot roots la.root
      if rs'.size > roots.size then
        roots := rs'
        lhsRW := lhsRW.push #[]; rhsRW := rhsRW.push #[]
        lhsRO := lhsRO.push #[]; rhsRO := rhsRO.push #[]
      rhsRO := rhsRO.set! rIdx (rhsRO[rIdx]!.push it)
    | some la, _ =>
      let (rIdx, rs') ← findOrAddRoot roots la.root
      if rs'.size > roots.size then
        roots := rs'
        lhsRW := lhsRW.push #[]; rhsRW := rhsRW.push #[]
        lhsRO := lhsRO.push #[]; rhsRO := rhsRO.push #[]
      rhsRW := rhsRW.set! rIdx (rhsRW[rIdx]!.push it)
    | none, _ => rhsOpaque := rhsOpaque.push it
  -- Solve `.ro` and `.rw` buckets first so spatial matching instantiates any witness mvars
  let mut allPlans : Array SegmentPlan := #[]
  for h : rIdx in [:roots.size] do
    let root := roots[rIdx]
    if !lhsRO[rIdx]!.isEmpty || !rhsRO[rIdx]!.isEmpty then
      let roPlans ← solveROBucket eqMode root lhsRO[rIdx]! rhsRO[rIdx]!
      allPlans := allPlans ++ roPlans
    if !lhsRW[rIdx]!.isEmpty || !rhsRW[rIdx]!.isEmpty then
      let rwPlans ← solveRWBucket eqMode root lhsRW[rIdx]! rhsRW[rIdx]!
      allPlans := allPlans ++ rwPlans
  -- Match opaque atoms 1-to-1, then discharge pure RHS obligations
  let mut usedRhsOp : Array Bool := Array.replicate rhsOpaque.size false
  for lop in lhsOpaque do
    let lopAtom ← instantiateMVars lop.canonAtom
    let mut matched? : Option Nat := none
    for h : rIdx in [:rhsOpaque.size] do
      if !usedRhsOp[rIdx]! then
        let ropAtom ← instantiateMVars rhsOpaque[rIdx].canonAtom
        if lopAtom == ropAtom || (← withReducibleAndInstances (isDefEq lopAtom ropAtom)) then
          matched? := some rIdx
          break
    let some mIdx := matched?
      | throwError "sep_interval: unmatched opaque LHS atom {lopAtom}"
    usedRhsOp := usedRhsOp.set! mIdx true
    let lopAtom ← instantiateMVars lop.canonAtom
    let ropAtom ← instantiateMVars rhsOpaque[mIdx]!.canonAtom
    let pEq ←
      if lopAtom == ropAtom then mkEqRefl lopAtom
      else mkExpectedTypeHint (← mkEqRefl ropAtom) (← mkEq lopAtom ropAtom)
    allPlans := allPlans.push { lhsAtoms := #[lopAtom], rhsAtoms := #[ropAtom],
                                proof := liftEqToMode eqMode lopAtom ropAtom pEq }
  for h : rIdx in [:rhsOpaque.size] do
    if !usedRhsOp[rIdx]! then
      let ropAtom ← instantiateMVars rhsOpaque[rIdx].canonAtom
      if !eqMode && ropAtom.isAppOfArity ``SepProp.pure 1 then
        let ψ ← instantiateMVars (ropAtom.getArg! 0)
        let mvar ← mkFreshExprMVar ψ
        let (gs, _) ← runTactic mvar.mvarId! (← `(tactic| first | trivial | rfl | assumption | bv_arith | omega))
        if gs.isEmpty then
          let hψ ← instantiateMVars mvar
          let ψ ← instantiateMVars ψ
          let ropAtom := mkApp (mkConst ``SepProp.pure) ψ
          let pPure := mkApp2 (mkConst ``Entails.pure_right_only) ψ hψ
          allPlans := allPlans.push { lhsAtoms := #[], rhsAtoms := #[ropAtom], proof := pPure }
          continue
      throwError "sep_interval: unmatched opaque RHS atom {ropAtom}"
  -- Instantiate mvars before computing flat/canon spines and AC permutations
  let P₀ ← instantiateMVars P₀
  let Q₀ ← instantiateMVars Q₀
  let P_ex ← instantiateMVars P_ex
  let Q_ex ← instantiateMVars Q_ex
  let rawLhsInst ← rawLhs.mapM instantiateMVars
  let rawRhsInst ← rawRhs.mapM instantiateMVars
  let P_flat := ProofLib.SepSolver.mkSepList rawLhsInst
  let Q_flat := ProofLib.SepSolver.mkSepList rawRhsInst
  let hP_flat? ←
    if P_ex == P_flat then pure none
    else pure (some (← ProofLib.SepSolver.eqAC P_ex P_flat))
  let hQ_flat? ←
    if Q_ex == Q_flat then pure none
    else pure (some (← ProofLib.SepSolver.eqAC Q_ex Q_flat))
  let P_canon ← instantiateMVars (ProofLib.SepSolver.mkSepList (lhsKept.map (·.canonAtom)))
  let Q_canon ← instantiateMVars (ProofLib.SepSolver.mkSepList (rhsKept.map (·.canonAtom)))
  let hP_ex? ← hP_ex?.mapM instantiateMVars
  let hQ_ex? ← hQ_ex?.mapM instantiateMVars
  let hP_can? ← hP_can?.mapM instantiateMVars
  let hQ_can? ← hQ_can?.mapM instantiateMVars
  let hP_pre? ← chainEq? hP_ex? (← chainEq? hP_flat? hP_can?)
  let hQ_pre? ← chainEq? hQ_ex? (← chainEq? hQ_flat? hQ_can?)
  if allPlans.isEmpty then
    let empE := mkConst ``SepProp.emp
    let hP ← match hP_pre? with
      | some p => mkExpectedTypeHint p (← mkEq P₀ empE)
      | none => mkExpectedTypeHint (← mkEqRefl empE) (← mkEq P₀ empE)
    let hQ ← match hQ_pre? with
      | some p => mkExpectedTypeHint p (← mkEq Q₀ empE)
      | none => mkExpectedTypeHint (← mkEqRefl empE) (← mkEq Q₀ empE)
    let eqTot ← mkEqTrans hP (← mkEqSymm hQ)
    return liftEqToMode eqMode P₀ Q₀ eqTot
  let lastPl := allPlans.back!
  let mut curGrpP ← instantiateMVars (ProofLib.SepSolver.mkSepList lastPl.lhsAtoms)
  let mut curGrpQ ← instantiateMVars (ProofLib.SepSolver.mkSepList lastPl.rhsAtoms)
  let mut curStitched ← instantiateMVars lastPl.proof
  let mut pIdx := allPlans.size - 1
  while pIdx > 0 do
    pIdx := pIdx - 1
    let pl := allPlans[pIdx]!
    let segP ← instantiateMVars (ProofLib.SepSolver.mkSepList pl.lhsAtoms)
    let segQ ← instantiateMVars (ProofLib.SepSolver.mkSepList pl.rhsAtoms)
    let plPrf ← instantiateMVars pl.proof
    if eqMode then
      curStitched ← mkCongr (← mkCongrArg (mkConst ``SepProp.sepConj) plPrf) curStitched
    else
      curStitched := mkAppN (mkConst ``sepConj_mono) #[segP, segQ, curGrpP, curGrpQ, plPrf, curStitched]
    curGrpP := ProofLib.SepSolver.mkSep segP curGrpP
    curGrpQ := ProofLib.SepSolver.mkSep segQ curGrpQ
  let hPermP? ←
    if P_canon == curGrpP then pure none
    else pure (some (← ProofLib.SepSolver.eqAC P_canon curGrpP))
  let hPermQ? ←
    if curGrpQ == Q_canon then pure none
    else pure (some (← ProofLib.SepSolver.eqAC curGrpQ Q_canon))
  let hTotP? ← chainEq? hP_pre? hPermP?
  let hTotQ? ← chainEq? hPermQ? (← match hQ_pre? with | some p => pure (some (← mkEqSymm p)) | none => pure none)
  if eqMode then
    let s1 ← match hTotP? with
      | some hp => mkEqTrans (← mkExpectedTypeHint hp (← mkEq P₀ curGrpP)) curStitched
      | none => mkExpectedTypeHint curStitched (← mkEq P₀ curGrpQ)
    let s2 ← match hTotQ? with
      | some hq => mkEqTrans s1 (← mkExpectedTypeHint hq (← mkEq curGrpQ Q₀))
      | none => mkExpectedTypeHint s1 (← mkEq P₀ Q₀)
    return s2
  else
    if hTotP?.isNone && hTotQ?.isNone then
      return ← mkExpectedTypeHint curStitched (mkApp2 (mkConst ``SepProp.Entails) P₀ Q₀)
    let hp ← match hTotP? with
      | some p => mkExpectedTypeHint p (← mkEq P₀ curGrpP)
      | none => mkExpectedTypeHint (← mkEqRefl curGrpP) (← mkEq P₀ curGrpP)
    let hq ← match hTotQ? with
      | some p => mkExpectedTypeHint p (← mkEq curGrpQ Q₀)
      | none => mkExpectedTypeHint (← mkEqRefl curGrpQ) (← mkEq curGrpQ Q₀)
    return mkAppN (mkConst ``entails_of_eq_both) #[P₀, curGrpP, curGrpQ, Q₀, hp, curStitched, hq]

/-- Introduce any leading `let` bindings in the main goal so local `let`-bound `BitVec 64` `FVar`s
    enter `LocalContext`. -/
def introLeadingLets : TacticM Unit := do
  while (← instantiateMVars (← getMainTarget)).isLet do
    liftMetaTactic1 fun g => do
      let (_, g') ← g.intro1P
      return g'

/-- `sep_interval`: Root-bucketed sweep-line interval and representation-subsumption solver for
    `P ⊢ Q` (also closes bi-equivalent `P = Q` goals over `SepProp`). -/
syntax (name := sepIntervalTac) "sep_interval" : tactic

@[tactic sepIntervalTac] def elabSepInterval : Tactic
  | `(tactic| sep_interval) => withMainContext do
    introLeadingLets
    withMainContext do
      let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
      if tgt.isAppOfArity ``SepProp.Entails 2 then
        let prf ← solveIntervalCore false (tgt.getArg! 0) (tgt.getArg! 1)
        closeMainGoal `sep_interval prf
      else if tgt.isAppOfArity ``Eq 3 && (tgt.getArg! 0).isConstOf ``SepProp then
        let prf ← solveIntervalCore true (tgt.getArg! 1) (tgt.getArg! 2)
        closeMainGoal `sep_interval prf
      else
        throwError "sep_interval: expected goal `P ⊢ Q` or `P = Q` over `SepProp`, got {tgt}"
  | _ => throwUnsupportedSyntax

/-- `sep_interval_eq`: Root-bucketed sweep-line interval equivalence solver for `P = Q` over `SepProp`. -/
syntax (name := sepIntervalEqTac) "sep_interval_eq" : tactic

@[tactic sepIntervalEqTac] def elabSepIntervalEq : Tactic
  | `(tactic| sep_interval_eq) => withMainContext do
    introLeadingLets
    withMainContext do
      let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
      if tgt.isAppOfArity ``Eq 3 && (tgt.getArg! 0).isConstOf ``SepProp then
        let prf ← solveIntervalCore true (tgt.getArg! 1) (tgt.getArg! 2)
        closeMainGoal `sep_interval_eq prf
      else
        throwError "sep_interval_eq: expected goal `P = Q` over `SepProp`, got {tgt}"
  | _ => throwUnsupportedSyntax

end

end ProofLib.Sep
