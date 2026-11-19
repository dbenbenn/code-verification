/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.PrologueFrame
public import ProofLib.ProgramReflection
public import ProofLib.CoreLemmas
public import ProofLib.BV.Bits

/-!
# Placement-Generic ADRP, Read-Only Memory, Symbol-Table, and Program-Rebasing Helpers

Provides page-aligned `ADRP` normalization (`reduceAdrpPage`), `Obj.HoldsBytes` read-only bridges
(`holdsBytes_ro`, `holdsBytes_ro_of_keepsFrozen`, `memSlice_of_holdsBytes_ro`), integer-encoded
symbol-table reflection (`EncSymTable`, `prepareCharAssocVal`, `lookupEnc`, `lookupUniqueEnc`), and
`Arm64.Program.rebase` / `fnOff` / `fnAddr` normalization simprocs and lemmas.
-/

@[expose] public section

/-! ## `ADRP` Page-Mask Normalization -/

namespace ProofLib.ObjectLoad

open Arm64.Obj

theorem adrp_page_base {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    b &&& 0xfffffffffffff000#64 = b := by
  bv_bits

theorem adrp_page_of_aligned {b off : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    (b + off) &&& 0xfffffffffffff000#64 = b + (off &&& 0xfffffffffffff000#64) := by
  bv_bits

theorem adrp_page_add_zero {b off : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hp : (off &&& 0xfffffffffffff000#64 == 0#64) = true) :
    (b + off) &&& 0xfffffffffffff000#64 = b := by
  rw [adrp_page_of_aligned hb, eq_of_beq hp, BitVec.add_zero]

theorem adrp_page_add_eq {b off pageOff : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hp : (off &&& 0xfffffffffffff000#64 == pageOff) = true) :
    (b + off) &&& 0xfffffffffffff000#64 = b + pageOff := by
  rw [adrp_page_of_aligned hb, eq_of_beq hp]

end ProofLib.ObjectLoad

end

public meta section

namespace ProofLib.ObjectLoad

open Arm64.Obj

open Lean Meta in
private partial def evalNatLitObj? (e : Expr) : MetaM (Option Nat) := do
  if let some n := e.rawNatLit? then return some n
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (e.getArg! 1).rawNatLit? then return some n
  if let some n ← getNatValue? e then return some n
  if e.hasFVar || e.hasMVar then return none
  let e' ← withTransparency .default (whnf e)
  if let some n := e'.rawNatLit? then return some n
  getNatValue? e'

open Lean Meta in
private partial def evalBitVecLitObj? (e : Expr) : MetaM (Option (Nat × Nat)) := do
  if e.isAppOfArity ``BitVec.ofNat 2 then
    if let some w := (e.getArg! 0).rawNatLit? <|>
        (if (e.getArg! 0).isAppOfArity ``OfNat.ofNat 3 then ((e.getArg! 0).getArg! 1).rawNatLit? else none) then
      if let some v := (e.getArg! 1).rawNatLit? <|>
          (if (e.getArg! 1).isAppOfArity ``OfNat.ofNat 3 then ((e.getArg! 1).getArg! 1).rawNatLit? else none) then
        return some (w, v % (1 <<< w))
  if e.hasFVar || e.hasMVar then return none
  let e' ← if e.isConst then withTransparency .default (whnf e) else pure e
  if e'.isAppOfArity ``BitVec.ofNat 2 then
    if let some w ← evalNatLitObj? (e'.getArg! 0) then
      if let some v ← evalNatLitObj? (e'.getArg! 1) then
        return some (w, v % (1 <<< w))
  if e'.isAppOfArity ``BitVec.ofFin 2 then
    if let some w ← evalNatLitObj? (e'.getArg! 0) then
      let finExpr ← whnf (e'.getArg! 1)
      if finExpr.isAppOfArity ``Fin.mk 3 then
        if let some v ← evalNatLitObj? (finExpr.getArg! 1) then
          return some (w, v % (1 <<< w))
  if e'.isAppOfArity ``HAdd.hAdd 6 then
    if let some (w1, v1) ← evalBitVecLitObj? (e'.getArg! 4) then
      if let some (w2, v2) ← evalBitVecLitObj? (e'.getArg! 5) then
        if w1 == w2 then
          return some (w1, (v1 + v2) % (1 <<< w1))
  if e'.isAppOfArity ``Neg.neg 3 then
    let inner := e'.getArg! 2
    if let some (w, v) ← evalBitVecLitObj? inner then
      let m := 1 <<< w
      return some (w, (m - (v % m)) % m)
  return none

open Lean Meta in
/-- Find a hypothesis `hb : b &&& 0xfff#64 = 0#64` in the local context for base address `b`. -/
def findBaseAlignedProof? (b : Expr) : MetaM (Option Expr) := do
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      let ty ← instantiateMVars decl.type
      if let some (_, lhs, rhs) := ty.eq? then
        if (← evalBitVecLitObj? rhs) == some (64, 0) &&
            lhs.isAppOfArity ``HAnd.hAnd 6 then
          if lhs.getArg! 4 == b &&
              (← evalBitVecLitObj? (lhs.getArg! 5)) == some (64, 0xfff) then
            return some decl.toExpr
  return none

open Lean Meta in
/-- Normalize `pc &&& 0xfffffffffffff000#64` (produced by `ADRP`) and ground `BitVec` bitwise-AND
    expressions `lit1 &&& lit2` (after `adrp_page_of_aligned` rewrites `(b + off) &&& mask` to
    `b + (off &&& mask)`). -/
simproc [arm64_norm] reduceAdrpPage (_ &&& _) := fun e => do
  if e.getAppNumArgs != 6 then return .continue
  let lhs := e.getArg! 4
  let rhs := e.getArg! 5
  if let some (w1, v1) ← evalBitVecLitObj? lhs then
    if let some (w2, v2) ← evalBitVecLitObj? rhs then
      if w1 == w2 then
        return .done { expr := toExpr (BitVec.ofNat w1 (v1 &&& v2)) }
  let some (64, 0xfffffffffffff000) ← evalBitVecLitObj? rhs | return .continue
  if lhs.isAppOfArity ``HAdd.hAdd 6 then
    let b := lhs.getArg! 4
    let offExpr := lhs.getArg! 5
    if let some (64, offVal) ← evalBitVecLitObj? offExpr then
      if let some hbPrf ← findBaseAlignedProof? b then
        let pageVal := offVal &&& 0xfffffffffffff000
        let rflTrue ← mkEqRefl (mkConst ``true)
        if pageVal == 0 then
          let prf := mkApp4 (mkConst ``adrp_page_add_zero) b offExpr hbPrf rflTrue
          return .done { expr := b, proof? := some prf }
        else
          let pageExpr := toExpr (BitVec.ofNat 64 pageVal)
          let newExpr ← mkAppM ``HAdd.hAdd #[b, pageExpr]
          let prf := mkApp5 (mkConst ``adrp_page_add_eq) b offExpr pageExpr hbPrf rflTrue
          return .done { expr := newExpr, proof? := some prf }
  else
    if let some hbPrf ← findBaseAlignedProof? lhs then
      let prf := mkApp2 (mkConst ``adrp_page_base) lhs hbPrf
      return .done { expr := lhs, proof? := some prf }
  return .continue

end ProofLib.ObjectLoad

end

@[expose] public section

namespace ProofLib.ObjectLoad

open Arm64.Obj

namespace RoDataFactsAux

theorem bytesLE_length (n : Nat) (v : BitVec 64) : (bytesLE n v).length = n := by
  simp [bytesLE]

end RoDataFactsAux

theorem readBytes_getElem? (m : Arm64.Memory) (p : BitVec 64) (n : Nat) (k : Nat) (hk : k < n) :
    (m.readBytes p n)[k]? = some (m.read8 (p + BitVec.ofNat 64 k)) := by
  induction n generalizing p k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [Arm64.Memory.readBytes_succ]
    | succ k =>
      simp only [Arm64.Memory.readBytes_succ, List.getElem?_cons_succ]
      rw [ih (p + 1#64) k (by omega)]
      have hadd : p + 1#64 + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (k + 1) := by bv_arith
      rw [hadd]

/-- Region-level bridge from `Obj.HoldsBytes m addr bytes (fun _ => Perm.ro)` to `m.RO` and `m.readBytes`. -/
theorem holdsBytes_ro {m : Arm64.Memory} {addr : BitVec 64} {bytes : List (BitVec 8)}
    (h : Arm64.Obj.HoldsBytes m addr bytes (fun _ => .ro)) :
    m.RO addr bytes.length ∧ m.readBytes addr bytes.length = bytes := by
  refine ⟨fun a ha => ?_, ?_⟩
  · unfold Arm64.InRegion at ha
    have hk : (a - addr).toNat < bytes.length := ha
    have hp := (h (a - addr).toNat hk).2
    have heq : addr + BitVec.ofNat 64 (a - addr).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_lin
    rwa [heq] at hp
  · apply List.ext_getElem?
    intro k
    by_cases hk : k < bytes.length
    · rw [readBytes_getElem? _ _ _ _ hk, List.getElem?_eq_getElem hk]
      exact congrArg some (h k hk).1
    · have h1 : ¬ k < (m.readBytes addr bytes.length).length := by
        rw [Arm64.Memory.readBytes_length]; exact hk
      rw [List.getElem?_eq_none (Nat.le_of_not_lt h1), List.getElem?_eq_none (Nat.le_of_not_lt hk)]

theorem splice_length {d bs : List (BitVec 8)} {off : Nat} (h : off + bs.length ≤ d.length) :
    (d.take off ++ bs ++ d.drop (off + bs.length)).length = d.length := by
  simp [List.length_take, List.length_drop]
  omega

theorem splice_drop_take_eq {d bs : List (BitVec 8)} {off k n : Nat}
    (hb : off + bs.length ≤ d.length) (hdisj : off + bs.length ≤ k ∨ k + n ≤ off) :
    ((d.take off ++ bs ++ d.drop (off + bs.length)).drop k).take n = (d.drop k).take n := by
  rcases hdisj with hle | hge
  · have hlen1 : (d.take off ++ bs).length = off + bs.length := by
      simp [List.length_take]; omega
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hlen1,
      List.drop_drop, show off + bs.length + (k - (off + bs.length)) = k by omega]
  · rw [List.append_assoc, List.drop_append, List.take_append]
    have hlen_take : (d.take off).length = off := by simp [List.length_take]; omega
    have hlen_drop : ((d.take off).drop k).length = off - k := by
      simp [List.length_drop, hlen_take]
    have hsub : n - (off - k) = 0 := by omega
    rw [hlen_drop, hsub, List.take_zero, List.append_nil, List.drop_take, List.take_take,
      Nat.min_eq_left (by omega)]

theorem bv_add_sub_add_of_le (b : BitVec 64) {x y : Nat} (hle : y ≤ x) (hx : x < 2 ^ 64) :
    (b + BitVec.ofNat 64 x) - (b + BitVec.ofNat 64 y) = BitVec.ofNat 64 (x - y) := by
  have h1 : (b + BitVec.ofNat 64 x) - (b + BitVec.ofNat 64 y) =
      BitVec.ofNat 64 x - BitVec.ofNat 64 y := by bv_lin
  rw [h1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem holdsBytes_ro_of_keepsFrozen {m m' : Arm64.Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    (h : Arm64.Obj.HoldsBytes m addr bs (fun _ => .ro)) (hk : m.KeepsFrozen m') :
    Arm64.Obj.HoldsBytes m' addr bs (fun _ => .ro) := by
  intro i hi
  obtain ⟨hb, hp, hlf⟩ := h i hi
  have hf : m.Frozen (addr + BitVec.ofNat 64 i) := by
    unfold Arm64.Memory.Frozen; rw [hp]; rfl
  obtain ⟨hb', hp', hlf', _⟩ := hk _ hf
  exact ⟨hb'.trans hb, hp'.trans hp, hlf'.trans hlf⟩

theorem holdsBytes_cons_iff {m : Arm64.Memory} {addr : BitVec 64} {b : BitVec 8} {bs : List (BitVec 8)}
    {p : BitVec 64 → Arm64.Perm} :
    Arm64.Obj.HoldsBytes m addr (b :: bs) p ↔
      (m.read8 addr = b ∧ m.perm addr = some (p addr) ∧ m.isLazyFree addr = false) ∧
        Arm64.Obj.HoldsBytes m (addr + 1#64) bs p := by
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · obtain ⟨hb, hp, hlf⟩ := h 0 (by simp)
      exact ⟨by simpa using hb, by simpa using hp, by simpa using hlf⟩
    · have h1 := h (i + 1) (by simp; omega)
      have ha : addr + BitVec.ofNat 64 (i + 1) = addr + 1#64 + BitVec.ofNat 64 i := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      simpa [ha] using h1
  · rintro ⟨h0, hs⟩ i hi
    rcases i with _ | i
    · simpa using h0
    · have h1 := hs i (by simp at hi; omega)
      have ha : addr + BitVec.ofNat 64 (i + 1) = addr + 1#64 + BitVec.ofNat 64 i := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      simpa [ha] using h1

theorem holdsBytes_append {m : Arm64.Memory} {addr : BitVec 64} {bs1 bs2 : List (BitVec 8)}
    {p : BitVec 64 → Arm64.Perm} (h : Arm64.Obj.HoldsBytes m addr (bs1 ++ bs2) p) :
    Arm64.Obj.HoldsBytes m addr bs1 p ∧
      Arm64.Obj.HoldsBytes m (addr + BitVec.ofNat 64 bs1.length) bs2 p := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h1 := h i (by simp; omega)
    rwa [List.getElem_append_left hi] at h1
  · have h1 := h (bs1.length + i) (by simp; omega)
    rw [List.getElem_append_right (Nat.le_add_right _ _)] at h1
    have ha : addr + BitVec.ofNat 64 (bs1.length + i) =
        addr + BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 i := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    simpa [ha] using h1

theorem memSlice_of_holdsBytes_ro {m : Arm64.Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    (h : Arm64.Obj.HoldsBytes m addr bs (fun _ => .ro)) :
    m.canRead addr bs.length = true ∧ m.readBytes addr bs.length = bs := by
  induction bs generalizing addr with
  | nil => simp [Arm64.Memory.canRead, Arm64.Memory.allPerm, Arm64.Memory.allNoLazyFree]
  | cons b bs ih =>
    obtain ⟨⟨hb, hp, hlf⟩, hs⟩ := holdsBytes_cons_iff.1 h
    obtain ⟨hc, hr⟩ := ih hs
    refine ⟨?_, by simp [hb, hr]⟩
    simp only [List.length_cons, Arm64.Memory.canRead, Arm64.Memory.allPerm,
      Arm64.Memory.allNoLazyFree, Bool.and_eq_true] at hc ⊢
    rw [hp, hlf]
    exact ⟨⟨rfl, hc.1⟩, ⟨rfl, hc.2⟩⟩

open ProofLib.ProgramReflection

/-- Pre-encoded `(length, codepoints)` association list for fast kernel lookups via `natEntryBeq`. -/
abbrev EncSymTable (α : Type) := List ((Nat × List Nat) × α)

def prepareCharAssocVal {α : Type} : List (List Char × α) → EncSymTable α
  | [] => []
  | (cs, v) :: rest => (encodeCharKey cs, v) :: prepareCharAssocVal rest

def lookupEnc {α : Type} (k : Nat × List Nat) : EncSymTable α → Option α
  | [] => none
  | (e, v) :: rest => if natEntryBeq e k then some v else lookupEnc k rest

def filterEnc {α : Type} (k : Nat × List Nat) : EncSymTable α → List ((Nat × List Nat) × α)
  | [] => []
  | (e, v) :: rest => if natEntryBeq e k then (e, v) :: filterEnc k rest else filterEnc k rest

def lookupUniqueEnc {α : Type} (k : Nat × List Nat) (xs : EncSymTable α) : Option α :=
  match filterEnc k xs with
  | [(_, v)] => some v
  | _ => none

def anyEnc {α : Type} (k : Nat × List Nat) : EncSymTable α → Bool
  | [] => false
  | (e, _) :: rest => if natEntryBeq e k then true else anyEnc k rest

def resolveSymEnc (symbols stubs : EncSymTable Nat) (k : Nat × List Nat) : Option Nat :=
  (lookupEnc k symbols).orElse fun _ => lookupEnc k stubs

theorem toStringSymbols_eq_toStringAssoc :
    ∀ (xs : List (List Char × Nat)), toStringSymbols xs = toStringAssoc xs
  | [] => rfl
  | (_, _) :: rest => congrArg _ (toStringSymbols_eq_toStringAssoc rest)

theorem lookupEnc_prepareCharAssocVal {α : Type} (cs : List Char) :
    ∀ (xs : List (List Char × α)),
      lookupEnc (encodeCharKey cs) (prepareCharAssocVal xs) =
        Arm64.Obj.lookup (String.ofList cs) (toStringAssoc xs)
  | [] => rfl
  | (cs₀, _) :: rest => by
    simp only [prepareCharAssocVal, lookupEnc, toStringAssoc, Arm64.Obj.lookup, List.find?,
      string_beq_eq_natEntryBeq cs₀ cs]
    cases natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs)
    · exact lookupEnc_prepareCharAssocVal cs rest
    · rfl

private theorem filterEnc_map_snd {α : Type} (cs : List Char) :
    ∀ (xs : List (List Char × α)),
      (filterEnc (encodeCharKey cs) (prepareCharAssocVal xs)).map Prod.snd =
        ((toStringAssoc xs).filter (·.1 == String.ofList cs)).map Prod.snd
  | [] => rfl
  | (cs₀, _) :: rest => by
    simp only [prepareCharAssocVal, filterEnc, toStringAssoc, List.filter,
      string_beq_eq_natEntryBeq cs₀ cs]
    cases natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs)
    · exact filterEnc_map_snd cs rest
    · simp only [↓reduceIte, List.map_cons, filterEnc_map_snd cs rest]

private theorem lookupUniqueEnc_of_map_snd_eq {α : Type}
    (ys : List ((Nat × List Nat) × α)) (zs : List (String × α))
    (h : ys.map Prod.snd = zs.map Prod.snd) :
    lookupUniqueEnc.match_1 (fun _ => Option α) ys (fun _ v => some v) (fun _ => none) =
    Arm64.Obj.lookupUnique.match_1 (fun _ => Option α) zs (fun _ v => some v) (fun _ => none) := by
  rcases ys with _ | ⟨⟨_, v₁⟩, _ | _⟩ <;>
    rcases zs with _ | ⟨⟨_, v₂⟩, _ | _⟩ <;>
    simp_all <;> rfl

theorem lookupUniqueEnc_prepareCharAssocVal {α : Type} (cs : List Char)
    (xs : List (List Char × α)) :
    lookupUniqueEnc (encodeCharKey cs) (prepareCharAssocVal xs) =
      Arm64.Obj.lookupUnique (String.ofList cs) (toStringAssoc xs) :=
  lookupUniqueEnc_of_map_snd_eq _ _ (filterEnc_map_snd cs xs)

theorem filterEnc_length {α : Type} (cs : List Char) :
    ∀ (xs : List (List Char × α)),
      ((toStringAssoc xs).filter (·.1 == String.ofList cs)).length =
        (filterEnc (encodeCharKey cs) (prepareCharAssocVal xs)).length
  | [] => rfl
  | (cs₀, _) :: rest => by
    simp only [prepareCharAssocVal, filterEnc, toStringAssoc, List.filter,
      string_beq_eq_natEntryBeq cs₀ cs]
    cases natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs)
    · exact filterEnc_length cs rest
    · simp only [↓reduceIte, List.length_cons, filterEnc_length cs rest]

theorem anyEnc_prepareCharAssocVal {α : Type} (cs : List Char) :
    ∀ (xs : List (List Char × α)),
      anyEnc (encodeCharKey cs) (prepareCharAssocVal xs) =
        (toStringAssoc xs).any (·.1 == String.ofList cs)
  | [] => rfl
  | (cs₀, _) :: rest => by
    simp only [prepareCharAssocVal, anyEnc, toStringAssoc, List.any_cons,
      string_beq_eq_natEntryBeq cs₀ cs]
    cases natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs)
    · exact anyEnc_prepareCharAssocVal cs rest
    · rfl

theorem lookup_eq_lookupEnc {α : Type} {tbl : List (String × α)}
    {xs : List (List Char × α)} {enc : EncSymTable α}
    (htbl : tbl = toStringAssoc xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookup name tbl = lookupEnc (encodeCharKey cs) enc := by
  rw [htbl, hname, ← lookupEnc_prepareCharAssocVal, heq]

theorem lookupSymbols_eq_lookupEnc {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)} {enc : EncSymTable Nat}
    (htbl : tbl = toStringSymbols xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookup name tbl = lookupEnc (encodeCharKey cs) enc := by
  rw [toStringSymbols_eq_toStringAssoc] at htbl
  exact lookup_eq_lookupEnc htbl heq hname

theorem lookupUnique_eq_lookupUniqueEnc {α : Type} {tbl : List (String × α)}
    {xs : List (List Char × α)} {enc : EncSymTable α}
    (htbl : tbl = toStringAssoc xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookupUnique name tbl = lookupUniqueEnc (encodeCharKey cs) enc := by
  rw [htbl, hname, ← lookupUniqueEnc_prepareCharAssocVal, heq]

theorem lookupUniqueSymbols_eq_lookupUniqueEnc {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)} {enc : EncSymTable Nat}
    (htbl : tbl = toStringSymbols xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookupUnique name tbl = lookupUniqueEnc (encodeCharKey cs) enc := by
  rw [toStringSymbols_eq_toStringAssoc] at htbl
  exact lookupUnique_eq_lookupUniqueEnc htbl heq hname

theorem filter_length_eq_filterEnc {α : Type} {tbl : List (String × α)}
    {xs : List (List Char × α)} {enc : EncSymTable α}
    (htbl : tbl = toStringAssoc xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    (tbl.filter (·.1 == name)).length = (filterEnc (encodeCharKey cs) enc).length := by
  rw [htbl, hname, filterEnc_length, heq]

theorem filterSymbols_length_eq_filterEnc {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)} {enc : EncSymTable Nat}
    (htbl : tbl = toStringSymbols xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    (tbl.filter (·.1 == name)).length = (filterEnc (encodeCharKey cs) enc).length := by
  rw [toStringSymbols_eq_toStringAssoc] at htbl
  exact filter_length_eq_filterEnc htbl heq hname

theorem any_eq_anyEnc {α : Type} {tbl : List (String × α)}
    {xs : List (List Char × α)} {enc : EncSymTable α}
    (htbl : tbl = toStringAssoc xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    tbl.any (·.1 == name) = anyEnc (encodeCharKey cs) enc := by
  rw [htbl, hname, ← anyEnc_prepareCharAssocVal, heq]

theorem anySymbols_eq_anyEnc {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)} {enc : EncSymTable Nat}
    (htbl : tbl = toStringSymbols xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    tbl.any (·.1 == name) = anyEnc (encodeCharKey cs) enc := by
  rw [toStringSymbols_eq_toStringAssoc] at htbl
  exact any_eq_anyEnc htbl heq hname

theorem lookup_prepareCharSymbols {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)}
    (htbl : tbl = toStringSymbols xs)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookup name tbl = lookupEnc (encodeCharKey cs) (prepareCharAssocVal xs) := by
  rw [htbl, toStringSymbols_eq_toStringAssoc, hname, lookupEnc_prepareCharAssocVal]

theorem lookupUnique_prepareCharSymbols {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)}
    (htbl : tbl = toStringSymbols xs)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookupUnique name tbl = lookupUniqueEnc (encodeCharKey cs) (prepareCharAssocVal xs) := by
  rw [htbl, toStringSymbols_eq_toStringAssoc, hname, lookupUniqueEnc_prepareCharAssocVal]

theorem filter_length_prepareCharSymbols {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)}
    (htbl : tbl = toStringSymbols xs)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    (tbl.filter (·.1 == name)).length = (filterEnc (encodeCharKey cs) (prepareCharAssocVal xs)).length := by
  rw [htbl, toStringSymbols_eq_toStringAssoc, hname, filterEnc_length]

theorem any_prepareCharSymbols {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)}
    (htbl : tbl = toStringSymbols xs)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    tbl.any (·.1 == name) = anyEnc (encodeCharKey cs) (prepareCharAssocVal xs) := by
  rw [htbl, toStringSymbols_eq_toStringAssoc, hname, anyEnc_prepareCharAssocVal]

theorem toStringSymbols_getElem?_of_some :
    ∀ (xs : List (List Char × Nat)) (k : Nat) {cs : List Char} {off : Nat},
      xs[k]? = some (cs, off) →
      (toStringSymbols xs)[k]? = some (String.ofList cs, off)
  | [], _, _, _, h => nomatch h
  | (_, _) :: _, 0, _, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | _ :: rest, k + 1, _, _, h => by
    simp only [List.getElem?_cons_succ] at h
    simpa only [toStringSymbols, List.getElem?_cons_succ] using
      toStringSymbols_getElem?_of_some rest k h

theorem fnOff_of_allFresh_chars (prog : Arm64.Program) (charSyms : List (List Char × Nat))
    (hsyms : prog.symbols = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    prog.fnOff name = off :=
  fnOff_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem fnOff_of_stub_chars (prog : Arm64.Program) (charSyms stubSyms : List (List Char × Nat))
    (hsyms : prog.symbols = toStringSymbols charSyms)
    (hstubs : prog.stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    prog.fnOff name = off :=
  fnOff_of_stub charSyms stubSyms hsyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem lookup_of_allFresh_chars {syms : List (String × Nat)}
    (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    Arm64.Obj.lookup name syms = some off :=
  lookup_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem lookupUnique_of_allFresh_chars {syms : List (String × Nat)}
    (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    Arm64.Obj.lookupUnique name syms = some off :=
  lookupUnique_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem filter_of_allFresh_chars {syms : List (String × Nat)}
    (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    syms.filter (·.1 == name) = [(name, off)] :=
  filter_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem filter_length_of_allFresh_chars {syms : List (String × Nat)}
    (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    (syms.filter (·.1 == name)).length = 1 :=
  filter_length_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem any_of_allFresh_chars {syms : List (String × Nat)}
    (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    syms.any (·.1 == name) = true :=
  any_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem lookup_stub_of_wf_chars {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    Arm64.Obj.lookup name stubs = some off :=
  lookup_stub_of_wf charSyms stubSyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem lookupUnique_stub_of_wf_chars {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    Arm64.Obj.lookupUnique name stubs = some off :=
  lookupUnique_stub_of_wf charSyms stubSyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem filter_length_stub_of_wf_chars {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    (stubs.filter (·.1 == name)).length = 1 :=
  filter_length_stub_of_wf charSyms stubSyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem any_stub_of_wf_chars {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    stubs.any (·.1 == name) = true :=
  any_stub_of_wf charSyms stubSyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem lookup_symbols_none_of_stub_chars {syms stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    Arm64.Obj.lookup name syms = none :=
  lookup_symbols_none_of_stub charSyms stubSyms hsyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem any_symbols_false_of_stub_chars {syms stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    syms.any (·.1 == name) = false :=
  any_symbols_false_of_stub charSyms stubSyms hsyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem any_stubs_false_of_symbol_chars {syms stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    stubs.any (·.1 == name) = false :=
  any_stubs_false_of_symbol charSyms stubSyms hsyms hstubs hwf k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem all_toStringSymbols_snd (P : Nat → Bool) :
    ∀ (xs : List (List Char × Nat)),
      (toStringSymbols xs).all (fun (_, s) => P s) = xs.all (fun (_, s) => P s)
  | [] => rfl
  | (_, _) :: rest => by
    simp only [toStringSymbols, List.all_cons, all_toStringSymbols_snd P rest]

theorem lookup_map_externData (b : BitVec 64) (sym : String) :
    ∀ (xs : List (String × Nat × Nat)),
      Arm64.Obj.lookup sym (xs.map fun (x, o, n) => (x, b + BitVec.ofNat 64 o, n)) =
        (Arm64.Obj.lookup sym xs).map (fun (o, n) => (b + BitVec.ofNat 64 o, n))
  | [] => rfl
  | (x, o, n) :: rest => by
    simp only [List.map_cons, Arm64.Obj.lookup, List.find?]
    cases (x == sym)
    · exact lookup_map_externData b sym rest
    · rfl

theorem Program.fnAddr_eq_of_fnOff {P : Arm64.Program} {name : String} {off : Nat} {addr : BitVec 64}
    (hfn : P.fnOff name = off)
    (haddr : P.base + BitVec.ofNat 64 off = addr) :
    P.fnAddr name = addr := by
  unfold Arm64.Program.fnAddr
  rw [hfn, haddr]

theorem add_off_add_eq {b off1 off2 off3 : BitVec 64}
    (h : off1 = off2 + off3) :
    b + off1 = b + off2 + off3 := by
  rw [h, BitVec.add_assoc]

theorem add_add_eq_add_off {b off1 off2 off3 : BitVec 64}
    (h : off1 + off2 = off3) :
    b + off1 + off2 = b + off3 := by
  rw [← h, BitVec.add_assoc]

theorem all_nil_eq_true {α : Type} (f : α → Bool) : ([] : List α).all f = true := rfl

theorem all_cons_eq_true {α : Type} {x : α} {xs : List α} {f : α → Bool}
    (hx : f x = true) (hxs : xs.all f = true) : (x :: xs).all f = true := by
  simp [hx, hxs]

theorem and_eq_true_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  simp [ha, hb]

theorem not_eq_true_intro {a : Bool} (ha : a = false) : (!a) = true := by
  simp [ha]

theorem not_eq_false_intro {a : Bool} (ha : a = true) : (!a) = false := by
  simp [ha]

theorem beq_eq_true_of_eq {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a = b) :
    (a == b) = true :=
  beq_iff_eq.mpr h

end ProofLib.ObjectLoad

namespace ProofLib
export ProofLib.ObjectLoad (
  adrp_page_base adrp_page_of_aligned adrp_page_add_zero adrp_page_add_eq
  findBaseAlignedProof? reduceAdrpPage
  readBytes_getElem? holdsBytes_ro
  splice_length splice_drop_take_eq
  bv_add_sub_add_of_le
  holdsBytes_ro_of_keepsFrozen holdsBytes_cons_iff holdsBytes_append
  memSlice_of_holdsBytes_ro
  EncSymTable prepareCharAssocVal lookupEnc filterEnc lookupUniqueEnc anyEnc
  toStringSymbols_eq_toStringAssoc
  lookupEnc_prepareCharAssocVal lookupUniqueEnc_prepareCharAssocVal
  filterEnc_length anyEnc_prepareCharAssocVal
  lookup_eq_lookupEnc lookupSymbols_eq_lookupEnc
  lookupUnique_eq_lookupUniqueEnc lookupUniqueSymbols_eq_lookupUniqueEnc
  filter_length_eq_filterEnc filterSymbols_length_eq_filterEnc
  any_eq_anyEnc anySymbols_eq_anyEnc
  lookup_prepareCharSymbols lookupUnique_prepareCharSymbols
  filter_length_prepareCharSymbols any_prepareCharSymbols
  toStringSymbols_getElem?_of_some
  fnOff_of_allFresh_chars fnOff_of_stub_chars
  lookup_of_allFresh_chars lookupUnique_of_allFresh_chars
  filter_of_allFresh_chars filter_length_of_allFresh_chars any_of_allFresh_chars
  lookup_stub_of_wf_chars lookupUnique_stub_of_wf_chars
  filter_length_stub_of_wf_chars any_stub_of_wf_chars
  lookup_symbols_none_of_stub_chars any_symbols_false_of_stub_chars
  any_stubs_false_of_symbol_chars
  lookup_map_externData
  add_off_add_eq add_add_eq_add_off
)
end ProofLib

namespace ProofLib.ProgramReflection
export ProofLib.ObjectLoad (
  EncSymTable prepareCharAssocVal lookupEnc filterEnc lookupUniqueEnc anyEnc
  toStringSymbols_eq_toStringAssoc
  lookupEnc_prepareCharAssocVal lookupUniqueEnc_prepareCharAssocVal
  filterEnc_length anyEnc_prepareCharAssocVal
  lookup_eq_lookupEnc lookupSymbols_eq_lookupEnc
  lookupUnique_eq_lookupUniqueEnc lookupUniqueSymbols_eq_lookupUniqueEnc
  filter_length_eq_filterEnc filterSymbols_length_eq_filterEnc
  any_eq_anyEnc anySymbols_eq_anyEnc
  toStringSymbols_getElem?_of_some
  fnOff_of_allFresh_chars fnOff_of_stub_chars
  lookup_of_allFresh_chars lookupUnique_of_allFresh_chars
  filter_of_allFresh_chars filter_length_of_allFresh_chars any_of_allFresh_chars
  lookup_stub_of_wf_chars lookupUnique_stub_of_wf_chars
  filter_length_stub_of_wf_chars any_stub_of_wf_chars
  lookup_symbols_none_of_stub_chars any_symbols_false_of_stub_chars
  any_stubs_false_of_symbol_chars
)
end ProofLib.ProgramReflection

/-! ## Program Rebasing -/

namespace Arm64.Program

variable {P : Program} {b : BitVec 64} {X O : String → Option (State → State)}

@[simp, arm64_norm] theorem rebase_base : (P.rebase b X O).base = b := by cases P; rfl
@[simp, arm64_norm] theorem rebase_code : (P.rebase b X O).code = P.code := by cases P; rfl
@[simp, arm64_norm] theorem rebase_symbols : (P.rebase b X O).symbols = P.symbols := by cases P; rfl
@[simp, arm64_norm] theorem rebase_stubs : (P.rebase b X O).stubs = P.stubs := by cases P; rfl
@[simp, arm64_norm] theorem rebase_externs : (P.rebase b X O).externs = X := by cases P; rfl
@[simp, arm64_norm] theorem rebase_overrides : (P.rebase b X O).overrides = O := by cases P; rfl
@[simp, arm64_norm] theorem rebase_svc : (P.rebase b X O).svc = P.svc := by cases P; rfl

@[simp, arm64_norm] theorem fnOff_rebase (n : String) : (P.rebase b X O).fnOff n = P.fnOff n := by cases P; rfl

/-- Rewrite a rebased program's `fnAddr` to `b + BitVec.ofNat 64 (P.fnOff n)`.
    Note: not marked `@[simp]` or `@[arm64_norm]` directly; `reduceFnAddrRebase` is the
    guarded `@[simp, arm64_norm]` simproc that normalizes `n` to a string literal and
    only rewrites when `P.fnOff n` simplifies cleanly (preventing unreduced `P.fnOff`
    terms in the goal when `n` is an unknown symbol or `*Code.lean` is not imported). -/
theorem fnAddr_rebase (n : String) :
    (P.rebase b X O).fnAddr n = b + BitVec.ofNat 64 (P.fnOff n) := by cases P; rfl

@[simp, arm64_norm] theorem readWordOff_rebase (off : Nat) :
    (P.rebase b X O).readWordOff off = P.readWordOff off := by cases P; rfl

@[simp, arm64_norm] theorem hookAtOff?_rebase (off : Nat) :
    (P.rebase b X O).hookAtOff? off = (P.rebase 0 X O).hookAtOff? off := by cases P; rfl

/-- Address of an internal callee relative to the caller's `fnAddr` in a rebased program. -/
theorem fnAddr_rel {name callee : String} {off off' k : Nat}
    (hfn : P.fnOff name = off) (hfn' : P.fnOff callee = off') (hk : off + k = off') :
    (P.rebase b X O).fnAddr callee = (P.rebase b X O).fnAddr name + BitVec.ofNat 64 k := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hfn', BitVec.add_assoc,
    ← BitVec.ofNat_add, hk]

/-- Address of an internal callee placed `d` bytes before the caller (`off' + d = off`) in a rebased program. -/
theorem fnAddr_back {name callee : String} {off off' d : Nat}
    (hfn : P.fnOff name = off) (hfn' : P.fnOff callee = off') (hk : off' + d = off) :
    (P.rebase b X O).fnAddr callee = (P.rebase b X O).fnAddr name - BitVec.ofNat 64 d := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hfn', ← hk, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- Express a forward callee's `fnAddr` as `caller + k#64` on the same rebased program. -/
theorem fnAddr_callee_add_of_fnOff {caller callee : String} {callerOff calleeOff k : Nat}
    (hcaller : P.fnOff caller = callerOff) (hcallee : P.fnOff callee = calleeOff)
    (hk : (BitVec.ofNat 64 callerOff + BitVec.ofNat 64 k : BitVec 64) = BitVec.ofNat 64 calleeOff) :
    (P.rebase b X O).fnAddr callee =
      (P.rebase b X O).fnAddr caller + BitVec.ofNat 64 k := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hcaller, hcallee, ← hk]
  bv_lin

/-- Express a backward callee's `fnAddr` as `caller - k#64` on the same rebased program. -/
theorem fnAddr_callee_sub_of_fnOff {caller callee : String} {callerOff calleeOff k : Nat}
    (hcaller : P.fnOff caller = callerOff) (hcallee : P.fnOff callee = calleeOff)
    (hk : (BitVec.ofNat 64 callerOff - BitVec.ofNat 64 k : BitVec 64) = BitVec.ofNat 64 calleeOff) :
    (P.rebase b X O).fnAddr callee =
      (P.rebase b X O).fnAddr caller - BitVec.ofNat 64 k := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hcaller, hcallee, ← hk]
  bv_lin

/-- Rewrite a rebased program's `fnAddr` to `b + BitVec.ofNat 64 off` given `P.fnOff name = off`. -/
theorem fnAddr_rebase_add_of_fnOff {name : String} {off : Nat} (hfn : P.fnOff name = off) :
    (P.rebase b X O).fnAddr name = b + BitVec.ofNat 64 off := by
  rw [Program.fnAddr_rebase, hfn]

end Arm64.Program

end

public meta section

namespace Arm64.Program

open Lean Meta Simp

/-- If `e` is not already a syntactic `String` literal (`.lit (.strVal _)`), unfold reducible
    definitions, local `let`-bindings, or constant definitions step-by-step (without `whnfCore`'s
    `toCtorIfLit`, which expands string literals into `String.ofList`) to check whether `e`
    reduces to a `.lit (.strVal _)`. -/
def reduceToStringLit? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if let .lit (.strVal _) := e then
    return none
  let mut cur := e
  for _ in [:32] do
    cur := cur.consumeMData
    if let .lit (.strVal _) := cur then
      return some cur
    if let .fvar fvarId := cur then
      if let some decl ← fvarId.findDecl? then
        if let some val := decl.value? then
          cur := val
          continue
      return none
    if cur.hasFVar || cur.hasMVar then
      return none
    if let some next ← withReducible (unfoldDefinition? cur) then
      cur := next
      continue
    if cur.isConst then
      if let some next ← unfoldDefinition? cur then
        cur := next
        continue
    return none
  return none

/-- Normalize a non-literal `String` symbol-name argument of `Program.fnOff` (e.g.
    `abbrev fooName : String := "..."`) to a `.lit (.strVal _)` literal via an explicit
    `congrArg` step so generated `@[simp, arm64_norm]` `*_fnOff_0x*` lemmas (keyed in the
    `simp` discrimination tree on `Key.lit (.strVal _)`) match without `DiscrTree.whnfDT`
    expanding the `abbrev` to `String.ofList` and without kernel-reducing `Program.fnOff`. -/
simproc [simp, arm64_norm, wp_norm] reduceFnOffSym (Arm64.Program.fnOff _ _) := fun e => do
  if !e.isAppOfArity ``Arm64.Program.fnOff 2 then return .continue
  let prog := e.getArg! 0
  let name := e.getArg! 1
  let some lit ← reduceToStringLit? name | return .continue
  let hName ← mkExpectedTypeHint (← mkEqRefl lit) (← mkEq name lit)
  let prf ← mkCongrArg (mkApp e.getAppFn prog) hName
  return .visit { expr := mkApp2 e.getAppFn prog lit, proof? := some prf }

/-- Normalize a non-literal `String` symbol-name argument of `Program.fnAddr` (e.g.
    `abbrev fooName : String := "..."`) to a `.lit (.strVal _)` literal via an explicit
    `congrArg` step. -/
simproc [simp, arm64_norm, wp_norm] reduceFnAddrSym (Arm64.Program.fnAddr _ _) := fun e => do
  if !e.isAppOfArity ``Arm64.Program.fnAddr 2 then return .continue
  let prog := e.getArg! 0
  let name := e.getArg! 1
  let some lit ← reduceToStringLit? name | return .continue
  let hName ← mkExpectedTypeHint (← mkEqRefl lit) (← mkEq name lit)
  let prf ← mkCongrArg (mkApp e.getAppFn prog) hName
  return .visit { expr := mkApp2 e.getAppFn prog lit, proof? := some prf }

/-- Guarded `simproc` for `(P.rebase b X O).fnAddr n`: rewrites `(P.rebase b X O).fnAddr n`
    to `b + BitVec.ofNat 64 off` (via `Program.fnAddr_rebase_add_of_fnOff`) only when
    `P.fnOff n` simplifies to an offset expression `off` that no longer mentions `Program.fnOff`.
    If `P.fnOff n` does not simplify (e.g. for an unknown symbol or when `*Code.lean` is not
    imported), leaves `(P.rebase b X O).fnAddr n` intact so an unreduced `P.fnOff n` term is
    never introduced into the goal or local context. -/
simproc [simp, arm64_norm] reduceFnAddrRebase
    (Arm64.Program.fnAddr (Arm64.Program.rebase _ _ _ _) _) := fun e => do
  let e' ← if e.isAppOfArity ``Arm64.Program.fnAddr 2 then pure e else withReducible (whnf e)
  if !e'.isAppOfArity ``Arm64.Program.fnAddr 2 then return .continue
  let prog0 := e'.getArg! 0
  let prog ← if prog0.isAppOfArity ``Arm64.Program.rebase 4 then pure prog0 else withReducible (whnf prog0)
  if !prog.isAppOfArity ``Arm64.Program.rebase 4 then return .continue
  let name := e'.getArg! 1
  if let some lit ← reduceToStringLit? name then
    let hName ← mkExpectedTypeHint (← mkEqRefl lit) (← mkEq name lit)
    let prf0 ← mkCongrArg (mkApp e'.getAppFn prog0) hName
    let rhs0 := mkApp2 e'.getAppFn prog0 lit
    let prf ← if e == e' then pure prf0 else mkExpectedTypeHint prf0 (← mkEq e rhs0)
    return .visit { expr := rhs0, proof? := some prf }
  let P := prog.getArg! 0
  let b := prog.getArg! 1
  let X := prog.getArg! 2
  let O := prog.getArg! 3
  let fnOffExpr := mkApp2 (mkConst ``Arm64.Program.fnOff) P name
  let r ← Simp.simp fnOffExpr
  if (r.expr.find? (·.isAppOf ``Arm64.Program.fnOff)).isSome then
    return .continue
  let offExpr := r.expr
  let hfn ← r.getProof
  let prf0 := mkAppN (mkConst ``Arm64.Program.fnAddr_rebase_add_of_fnOff)
    #[P, b, X, O, name, offExpr, hfn]
  let bv64Off := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) offExpr
  let rhs ← mkAppM ``HAdd.hAdd #[b, bv64Off]
  let prf ← if e == e' && prog0 == prog then pure prf0 else mkExpectedTypeHint prf0 (← mkEq e rhs)
  return .visit { expr := rhs, proof? := some prf }

end Arm64.Program

end

@[expose] public section

namespace Arm64.Program

variable {P : Program} {b : BitVec 64} {X O : String → Option (State → State)}

/-- The hook at `b + off` of a rebased program is the hook at offset `off`. -/
theorem externAt?_rebase_add (off : Nat) (hoff : off < 2 ^ 64 := by decide) :
    (P.rebase b X O).externAt? (b + BitVec.ofNat 64 off) = (P.rebase 0 X O).hookAtOff? off := by
  rw [Program.externAt?, rebase_base, BitVec.add_comm, BitVec.add_sub_cancel,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
  rfl

/-- The extern reached at `fnAddr name + k` of `P.rebase b X O` for stub offset `off + k = stub`. -/
theorem externAt?_fnAddr_add {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64 := by decide) :
    (P.rebase b X O).externAt? ((P.rebase b X O).fnAddr name + BitVec.ofNat 64 k) =
      (P.rebase 0 X O).hookAtOff? stub := by
  rw [Program.fnAddr_rebase, hfn, BitVec.add_assoc, ← BitVec.ofNat_add, hk,
    Program.externAt?_rebase_add _ hs]

/-- Rewrite a rebased instruction fetch at `b + (off + k)` into a fetch at `fnAddr name + k`. -/
theorem fetch_fnAddr_add {name : String} {off k : Nat} {inst : Instr}
    (hfn : P.fnOff name = off)
    (h : (P.rebase b X O).fetch (b + BitVec.ofNat 64 (off + k)) = some inst) :
    (P.rebase b X O).fetch ((P.rebase b X O).fnAddr name + BitVec.ofNat 64 k) = some inst := by
  rwa [Program.fnAddr_rebase, hfn, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Rewrite a rebased instruction fetch at `b + (off + 0)` into a fetch at `fnAddr name`. -/
theorem fetch_fnAddr_entry {name : String} {off : Nat} {inst : Instr}
    (hfn : P.fnOff name = off)
    (h : (P.rebase b X O).fetch (b + BitVec.ofNat 64 (off + 0)) = some inst) :
    (P.rebase b X O).fetch ((P.rebase b X O).fnAddr name) = some inst := by
  simpa using fetch_fnAddr_add hfn h

/-- Fetch at `b + off` of a hook-free base-0 program rebased to `b` equals the base-0 fetch at
    `off`, provided no new hook sits at `off`. -/
theorem fetch_rebase_eq_of_hookAtOff? {P : Program} (hbase : P.base = 0)
    (hX : ∀ n, (P.externs n).isNone = true) (hO : ∀ n, (P.overrides n).isNone = true)
    {b : BitVec 64} {X O : String → Option (State → State)} {off : Nat} (hoff : off < 2 ^ 64)
    (hhook : (P.rebase b X O).hookAtOff? off = none) :
    (P.rebase b X O).fetch (b + BitVec.ofNat 64 off) = P.fetch (BitVec.ofNat 64 off) := by
  have h1 : (P.rebase b X O).fetch (b + BitVec.ofNat 64 off) = _ :=
    Program.fetch_base_add (prog := P.rebase b X O) hoff
  have h2 := Program.fetch_base_add (prog := P) hoff
  rw [hbase, show (0 : BitVec 64) + BitVec.ofNat 64 off = BitVec.ofNat 64 off from
    BitVec.zero_add _] at h2
  rw [h1, h2, hhook, ProofLib.ProgramReflection.hookAtOff?_eq_none_of_isNone hX hO]
  rfl

/-- For a base-0 hook-free program `P` whose stubs all sit at offsets `≥ textEnd`,
    fetching at `b + off` (for `off < textEnd`) in `P.rebase b X` (with any externs `X` and
    no overrides) equals the base-0 fetch `P.fetch (BitVec.ofNat 64 off)`. -/
theorem fetch_rebase_of_noStubBefore {P : Program} (hbase : P.base = 0)
    (hX : ∀ n, (P.externs n).isNone = true) (hO : ∀ n, (P.overrides n).isNone = true)
    {textEnd : Nat} (hstubs : ProofLib.ProgramReflection.noStubBefore textEnd P.stubs = true)
    (b : BitVec 64) (X : String → Option (State → State))
    {off : Nat} (htext : off < textEnd) (hoff : off < 2 ^ 64) :
    (P.rebase b X).fetch (b + BitVec.ofNat 64 off) = P.fetch (BitVec.ofNat 64 off) :=
  fetch_rebase_eq_of_hookAtOff? hbase hX hO hoff
    (ProofLib.ProgramReflection.hookAtOff?_eq_none_of_noStubBefore hstubs (fun _ => rfl) htext)

/-- Every stub or symbol of `P` whose hook is set lies at an offset in `hooked`. -/
def hooksWithin (P : Program) (hooked : List Nat) : Bool :=
  (P.stubs.all fun (n, o) => hooked.contains o || (P.externs n).isNone) &&
  (P.symbols.all fun (n, o) => hooked.contains o || (P.overrides n).isNone)

/-- `hasWordsOff` transfers to a rebased program if its hooks avoid the range. The hook
    condition is stated at base 0 so that `decide` closes it for concrete hooks. -/
theorem hasWordsOff_rebase {off : Nat} {words : List (BitVec 32)} (h : P.hasWordsOff off words)
    (hfree : (P.rebase 0 X O).hookFree off (4 * words.length)) :
    (P.rebase b X O).hasWordsOff off words :=
  ⟨h.1, h.2.1, hfree⟩

/-- `codeAt` transfers to a rebased program if its hooks avoid the function's code. -/
theorem codeAt_rebase {n : String} {hex : List (BitVec 32)} (h : P.codeAt n hex)
    (hfree : (P.rebase 0 X O).hookFree (P.fnOff n) (4 * hex.length)) :
    (P.rebase b X O).codeAt n hex :=
  hasWordsOff_rebase h hfree

/-- `codeAtOff` transfers to a rebased program if its hooks avoid the function's code. -/
theorem codeAtOff_rebase {n : String} {hex : List (BitVec 32)} {off : Nat} (h : P.codeAtOff n off hex)
    (hfree : (P.rebase 0 X O).hookFree (P.fnOff n) (4 * hex.length)) :
    (P.rebase b X O).codeAtOff n off hex :=
  ⟨h.1, codeAt_rebase h.2 hfree⟩

end Arm64.Program

namespace Arm64.FnCode

/-- `c` is not pinned at an absolute address. -/
def unpinned (c : FnCode) : Bool :=
  match c.pin with
  | .addr _ => false
  | _ => true

/-- An unpinned code spec that holds for `P` rebased to 0 with hooks `X`, `O` (decidable for
    concrete programs, and it includes hook freedom) holds at every base. -/
theorem holds_rebase_of_zero {c : FnCode} {P : Program} {b : BitVec 64}
    {X O : String → Option (State → State)} (h : c.holds (P.rebase 0 X O))
    (hpin : c.unpinned = true) : c.holds (P.rebase b X O) := by
  rcases c with ⟨n, hex, _ | off | a⟩
  · exact h
  · exact h
  · simp [unpinned] at hpin

end Arm64.FnCode

namespace Arm64.Program

/-- Bundle version of `FnCode.holds_rebase_of_zero`: decide the bundle once at base 0. -/
theorem hasCodeBundle_rebase_of_zero {P : Program} {b : BitVec 64}
    {X O : String → Option (State → State)} :
    {cs : List FnCode} → (P.rebase 0 X O).hasCodeBundle cs →
      cs.all FnCode.unpinned = true → (P.rebase b X O).hasCodeBundle cs
  | [], _, _ => trivial
  | [c], h, hp => FnCode.holds_rebase_of_zero h (by simpa using hp)
  | c :: c2 :: cs, h, hp => by
    simp only [List.all_cons, Bool.and_eq_true] at hp
    exact ⟨FnCode.holds_rebase_of_zero h.1 hp.1,
      hasCodeBundle_rebase_of_zero (cs := c2 :: cs) h.2 (by simpa using hp.2)⟩

end Arm64.Program

namespace ProofLib
export Arm64.Program (
  fnAddr_back fnAddr_callee_add_of_fnOff fnAddr_callee_sub_of_fnOff fnAddr_rebase_add_of_fnOff
  reduceToStringLit? reduceFnOffSym reduceFnAddrSym reduceFnAddrRebase
)

private meta def elabDeclareFixedRebasedProgram (rebasedName : Lean.Ident)
    (baseTerm progTerm : Lean.Syntax.Term) : Lean.Elab.Command.CommandElabM Unit := do
  let thmId := Lean.mkIdentFrom rebasedName (rebasedName.getId.appendAfter "_subroutineOk")
  Lean.Elab.Command.elabCommand (← `(command|
    @[irreducible, wp_unfold] def $rebasedName : Arm64.Program :=
      Arm64.Program.rebase $progTerm $baseTerm))
  Lean.Elab.Command.elabCommand (← `(command|
    theorem $thmId {α : Type} {S : Type} [Arm64.ToBaseSpec S α]
        {sym : String} {spec : S}
        (hok : Arm64.Program.subroutineOk (Arm64.Program.rebase $progTerm $baseTerm) sym spec) :
        Arm64.Program.subroutineOk $rebasedName sym spec := by
      delta $rebasedName
      exact hok))

/-- Declare an `@[irreducible]` rebased `Program` together with its `<rebasedName>_subroutineOk`
    transport theorem in a single line:
    `declare_rebased_program <rebasedName> <baseConst> <rawProgram>` for `(baseConst : BitVec 64)`
    and `(rawProgram : Arm64.Program)`. -/
elab "declare_rebased_program " rebasedName:ident arg2:term:arg arg3:term:arg : command => do
  Lean.Elab.Command.liftTermElabM do
    let e2 ← Lean.Elab.Term.elabTerm arg2 none
    let e3 ← Lean.Elab.Term.elabTerm arg3 none
    let ty2 ← Lean.instantiateMVars (← Lean.Meta.inferType e2)
    let ty3 ← Lean.instantiateMVars (← Lean.Meta.inferType e3)
    let bv64Ty := Lean.mkApp (Lean.mkConst ``BitVec) (Lean.toExpr (64 : Nat))
    let progTy := Lean.mkConst ``Arm64.Program
    unless (← Lean.Meta.isDefEq ty2 bv64Ty) && (← Lean.Meta.isDefEq ty3 progTy) do
      throwError "declare_rebased_program: expected `(baseConst : BitVec 64) (rawProgram : Program)`, got arguments of types `{ty2}` and `{ty3}`"
  elabDeclareFixedRebasedProgram rebasedName arg2 arg3

end ProofLib

end
