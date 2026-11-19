/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliPlainPanPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl4
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMallocngPlaced
import ProofLib.Process.Overrides
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# ELF-Direct Bridge for `libsignal-cli`

**Checked by Lean. Untrusted (`Role::Proof`).** Bridges the ELF-only run definitions
(`CliBinaryPq.lean`, starting directly from plain `ElfImage.loadState` under `cliProgElf addrs`) to
the plain-memory placed definitions (`CliPlainPanPlaced.lean`) at the unique placement
`cliElfMultiPlacement` of `cliElfBytes`:

1. Resolves all 23 `.symtab` function addresses (`cliElf_resolveAddrs`: 18 Rust panic entry points
   and 5 `SampleNTT` entry points) via a kernel-checked single-pass byte scanner over `cliElfBytes`
   (`std3` axioms only).
2. Proves exact `externAt?` agreement (`cliProgElf_externAt_eq`), `SampleNTT` entry agreement
   (`mlKemSampleNttStuckAtElf_iff`), and therefore full equivalence of `CliRunsToElf`, `cliRunElf`,
   `CliReachesOOMElf`, and `CliReachesSampleNttStuckElf` with their plain-memory placed counterparts
   (`CliPlainPanPlaced`) at `cliElfMultiPlacement`.
3. Exports the non-headline cross-check `cliElf_symtab_agrees_with_placement` certifying that all
   23 `.symtab` entries in `cliElfBytes` agree with `cliElfMultiPlacement.ρ`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge

open Arm64 Arm64.Obj Arm64.Process
open ProofLib.ProgramReflection
open CryptoVerification.SignalSession (
  CliElfAddrs CliPqxdhBinaryCorrect CliReachesOOMElf CliReachesSampleNttStuckElf CliRunsToElf
  Inputs MlKemSampleNttStuckAt MlKemSampleNttStuckAtElf Outcome OutcomeMatchesProcess abortOnPanic
  cliElfBytes cliElfImage cliElf_parse cliExcusedElf cliExternsPlacedSig cliPanicOverrides
  cliPanicSymbolsPlaced cliProcessInputs cliProgElf cliRunElf isCliPanicSymbolPlaced
  kyberDecapsElfSym kyberEncapsElfSym libsignalSessionLib mlkemDecapsElfSym mlkemEncaps1ElfSym
  mlkemFromSeedElfSym resolveCliElfAddrs
)
open CryptoVerification.SignalSession.Placed (cliProgPlacedSig)
open LibsignalBinary.Proofs.Placed.CliPlainPanPlaced (
  CliPqxdhBinaryCorrectPlainPanPlaced CliReachesOOMPlainPanPlaced1
  CliReachesSampleNttStuckPlainPanPlaced1 CliRunsToPlainPanPlaced1
  cliPqxdhElfCorrectPlainPanPlaced_to_1 cliRunPlainPanPlaced1
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced (
  cliElfMultiPlacement cliElfSymAddrs cliElf_linkedAt cliElf_mallocng_linkedAt
  cliElf_trustedCodeMatchesPlaced_of_linkedAt lsInternedMultiLib ls_names_nodup
  ls_toMultiPlacedLib_eq
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (
  f3LsSymAddrs lsPlacedStubPairs lsPlacedStubPairs_eq lsSharedExterns ls_block617_externs_eq
  ls_blockSymsMatch_ok ls_idsOk ls_sharedExterns_lt
)

/-! ## 1. Fast Single-Pass `.symtab` Scanner and Soundness -/

private def strOfBytes (bs : List (BitVec 8)) : String :=
  String.ofList (bs.map fun b => Char.ofNat b.toNat)

private def bytesOfString (s : String) : List (BitVec 8) :=
  s.toList.map fun c => BitVec.ofNat 8 c.toNat

private theorem char_ofNat_bv8_toNat (a : BitVec 8) :
    (Char.ofNat a.toNat).toNat = a.toNat := by
  revert a
  decide

private theorem char_ofNat_bv8_inj {a b : BitVec 8}
    (h : Char.ofNat a.toNat = Char.ofNat b.toNat) : a = b :=
  BitVec.eq_of_toNat_eq
    ((char_ofNat_bv8_toNat a).symm.trans ((congrArg Char.toNat h).trans (char_ofNat_bv8_toNat b)))

private theorem strOfBytes_inj {xs ys : List (BitVec 8)}
    (h : strOfBytes xs = strOfBytes ys) : xs = ys := by
  have h1 := congrArg String.toList h
  simp only [strOfBytes, String.toList_ofList] at h1
  exact List.map_injective_iff.mpr (fun _ _ h' => char_ofNat_bv8_inj h') h1

private def readCStringBytes : Nat → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | rem + 1, b :: bs, acc =>
    if b == 0#8 then some acc.reverse
    else readCStringBytes rem bs (b :: acc)

private theorem readStrtabCString_eq_map :
    ∀ (rem : Nat) (bs acc : List (BitVec 8)),
      readStrtabCString rem bs (acc.map fun b => Char.ofNat b.toNat) =
        (readCStringBytes rem bs acc).map strOfBytes
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | rem + 1, b :: bs, acc => by
    simp only [readStrtabCString, readCStringBytes]
    split
    · simp only [Option.map_some, strOfBytes, List.map_reverse]
    · exact readStrtabCString_eq_map rem bs (b :: acc)

private def cstrHasZero : Nat → List (BitVec 8) → Bool
  | 0, _ => false
  | _ + 1, [] => false
  | rem + 1, b :: bs => if b == 0#8 then true else cstrHasZero rem bs

private theorem readCStringBytes_isSome_of_hasZero :
    ∀ (rem : Nat) (bs acc : List (BitVec 8)),
      cstrHasZero rem bs = true → ∃ cs, readCStringBytes rem bs acc = some cs
  | 0, _, _, h => by cases h
  | _ + 1, [], _, h => by cases h
  | rem + 1, b :: bs, acc, h => by
    simp only [cstrHasZero] at h
    simp only [readCStringBytes]
    split at h
    · rename_i hb
      simp only [hb, ↓reduceIte]
      exact ⟨acc.reverse, rfl⟩
    · rename_i hb
      simp only [hb]
      exact readCStringBytes_isSome_of_hasZero rem bs (b :: acc) h

private theorem readCStringBytes_prefix :
    ∀ (rem : Nat) (bs acc cs : List (BitVec 8)),
      readCStringBytes rem bs acc = some cs → ∃ tail, cs = acc.reverse ++ tail
  | 0, _, _, _, h => by cases h
  | _ + 1, [], _, _, h => by cases h
  | rem + 1, b :: bs, acc, cs, h => by
    simp only [readCStringBytes] at h
    split at h
    · exact ⟨[], by simpa using (Option.some.inj h).symm⟩
    · obtain ⟨tail, htail⟩ := readCStringBytes_prefix rem bs (b :: acc) cs h
      exact ⟨b :: tail, by simpa [List.append_assoc] using htail⟩

private def bytesMatchCstr : List (BitVec 8) → List (BitVec 8) → Bool
  | [], b :: _ => b == 0#8
  | [], [] => false
  | p :: ps, b :: bs => b == p && bytesMatchCstr ps bs
  | _ :: _, [] => false

private theorem readCStringBytes_eq_iff_bytesMatchCstr :
    ∀ (rem : Nat) (bs acc pat : List (BitVec 8)),
      cstrHasZero rem bs = true →
      (∀ b ∈ pat, b ≠ 0#8) →
      (readCStringBytes rem bs acc = some (acc.reverse ++ pat) ↔ bytesMatchCstr pat bs = true)
  | 0, _, _, _, hz, _ => by cases hz
  | _ + 1, [], _, _, hz, _ => by cases hz
  | rem + 1, b :: bs, acc, pat, hz, hpat => by
    simp only [cstrHasZero] at hz
    simp only [readCStringBytes]
    by_cases hb0 : b == 0#8
    · simp only [hb0, ↓reduceIte, Option.some.injEq]
      cases pat with
      | nil =>
        simp [bytesMatchCstr, hb0]
      | cons p ps =>
        have hp0 : p ≠ 0#8 := hpat p List.mem_cons_self
        have hb0eq : b = 0#8 := beq_iff_eq.mp hb0
        have hbp : (b == p) = false := by
          rw [beq_eq_false_iff_ne]; exact fun h => hp0 (h.symm.trans hb0eq)
        simp only [bytesMatchCstr, hbp, Bool.false_and, Bool.false_eq_true, iff_false]
        intro heq
        have hlen := congrArg List.length heq
        simp at hlen
    · simp only [hb0, Bool.false_eq_true, ↓reduceIte] at hz ⊢
      cases pat with
      | nil =>
        simp only [bytesMatchCstr, hb0, Bool.false_eq_true, iff_false]
        intro h
        obtain ⟨tail, htail⟩ := readCStringBytes_prefix rem bs (b :: acc) (acc.reverse ++ []) h
        have hlen := congrArg List.length htail
        simp at hlen
      | cons p ps =>
        simp only [bytesMatchCstr, Bool.and_eq_true, beq_iff_eq]
        by_cases hbp : b = p
        · subst hbp
          have happ : acc.reverse ++ b :: ps = (b :: acc).reverse ++ ps := by simp
          rw [happ, readCStringBytes_eq_iff_bytesMatchCstr rem bs (b :: acc) ps hz
            (fun x hx => hpat x (List.mem_cons_of_mem _ hx))]
          simp
        · constructor
          · intro h
            obtain ⟨tail, htail⟩ :=
              readCStringBytes_prefix rem bs (b :: acc) (acc.reverse ++ p :: ps) h
            have hcons : acc.reverse ++ p :: ps = acc.reverse ++ b :: tail := by
              simpa [List.append_assoc] using htail
            have h1 := List.append_cancel_left hcons
            exact absurd (List.cons.inj h1).1.symm hbp
          · intro h
            exact absurd h.1 hbp

private def findFirstMatch : List (List (BitVec 8)) → Nat → List (BitVec 8) →
    Option (Nat × List (BitVec 8))
  | [], _, _ => none
  | p :: ps, i, bs =>
    if bytesMatchCstr p bs then some (i, p) else findFirstMatch ps (i + 1) bs

private theorem findFirstMatch_some :
    ∀ (pats : List (List (BitVec 8))) (idx : Nat) (bs : List (BitVec 8))
      (k : Nat) (pat : List (BitVec 8)),
      findFirstMatch pats idx bs = some (k, pat) →
      idx ≤ k ∧ ∃ hk : k - idx < pats.length, pats[k - idx] = pat ∧ bytesMatchCstr pat bs = true
  | [], _, _, _, _, h => by cases h
  | p :: ps, idx, bs, k, pat, h => by
    unfold findFirstMatch at h
    split at h
    · rename_i hm
      cases h
      exact ⟨Nat.le_refl _, ⟨by simp, by simp, hm⟩⟩
    · obtain ⟨hle, hk, heq, hm⟩ := findFirstMatch_some ps (idx + 1) bs k pat h
      have hsub : k - idx = (k - (idx + 1)) + 1 := by omega
      exact ⟨by omega, ⟨by simp; omega, by simp [hsub, heq], hm⟩⟩

private theorem findFirstMatch_none :
    ∀ (pats : List (List (BitVec 8))) (idx : Nat) (bs : List (BitVec 8)),
      findFirstMatch pats idx bs = none →
      ∀ p ∈ pats, bytesMatchCstr p bs = false
  | [], _, _, _, _, hp => nomatch hp
  | p :: ps, idx, bs, h, q, hq => by
    unfold findFirstMatch at h
    split at h
    · cases h
    · rename_i hm
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact Bool.eq_false_iff.mpr hm
      · exact findFirstMatch_none ps (idx + 1) bs h q hq'

private def scanSymEntries (strtab : List (BitVec 8)) (strSize : Nat) (tree : StrtabTree)
    (pats : List (List (BitVec 8))) :
    Nat → List (BitVec 8) → List (Nat × ElfSym) → Option (List (Nat × ElfSym))
  | 0, _, acc => some acc.reverse
  | n + 1, sym, acc =>
    withForcedList (drop24 sym) fun nextSym =>
      let stName := listReadU32LE sym 0
      if stName ≥ strSize then none
      else
        let sBytes := lookupStrtabTree strtab stName tree
        if cstrHasZero (strSize - stName) sBytes then
          let acc' := match findFirstMatch pats 0 sBytes with
            | none => acc
            | some (k, pat) =>
              let info := listGetByte sym 4
              let e : ElfSym :=
                { name := strOfBytes pat
                  value := listReadU64LE sym 8
                  size := listReadU64LE sym 16
                  type := info % 16
                  bind := info / 16
                  shndx := listReadU16LE sym 6 }
              (k, e) :: acc
          scanSymEntries strtab strSize tree pats n nextSym acc'
        else none

private theorem scanSymEntries_sound (strtab : List (BitVec 8)) (strSize : Nat)
    (tree : StrtabTree) (htree : tree.Valid strtab)
    (pats : List (List (BitVec 8))) (hnd : pats.Nodup)
    (hno0 : ∀ p ∈ pats, ∀ b ∈ p, b ≠ 0#8) :
    ∀ (n : Nat) (sym : List (BitVec 8)) (acc hits : List (Nat × ElfSym)),
      scanSymEntries strtab strSize tree pats n sym acc = some hits →
      ∃ syms, parseSymEntries strtab strSize n sym = .ok syms ∧
        ∀ (k : Nat) (hk : k < pats.length),
          (acc.reverse.filter (·.1 == k)).map (·.2) ++
            syms.filter (·.name == strOfBytes pats[k]) =
          (hits.filter (·.1 == k)).map (·.2)
  | 0, _, acc, hits, h => by
    simp only [scanSymEntries, Option.some.injEq] at h
    subst h
    refine ⟨[], rfl, fun k _ => by simp⟩
  | n + 1, sym, acc, hits, h => by
    simp only [scanSymEntries, withForcedList_eq, drop24_eq_drop,
      lookupStrtabTree_eq_drop strtab _ tree htree] at h
    split at h
    · cases h
    · rename_i hlt
      split at h
      · rename_i hz
        set stName := listReadU32LE sym 0
        set sBytes := strtab.drop stName
        obtain ⟨cs, hcs⟩ := readCStringBytes_isSome_of_hasZero (strSize - stName) sBytes [] hz
        have hread : readStrtabCString (strSize - stName) sBytes [] = some (strOfBytes cs) := by
          have := readStrtabCString_eq_map (strSize - stName) sBytes []
          simp only [List.map_nil, hcs, Option.map_some] at this
          exact this
        set info := listGetByte sym 4
        set e : ElfSym :=
          { name := strOfBytes cs
            value := listReadU64LE sym 8
            size := listReadU64LE sym 16
            type := info % 16
            bind := info / 16
            shndx := listReadU16LE sym 6 }
        cases hfm : findFirstMatch pats 0 sBytes with
        | none =>
          rw [hfm] at h
          dsimp only at h
          obtain ⟨rest, hrest, hfilt⟩ :=
            scanSymEntries_sound strtab strSize tree htree pats hnd hno0 n (sym.drop 24) acc hits h
          refine ⟨e :: rest, ?_, ?_⟩
          · unfold parseSymEntries
            rw [ite_eq_right (fun hc => absurd hc hlt)]
            show (do
              let some name := readStrtabCString (strSize - stName) sBytes []
                | Except.error "symtab: unterminated name"
              let info := listGetByte sym 4
              let e' : ElfSym :=
                { name, value := listReadU64LE sym 8, size := listReadU64LE sym 16,
                  type := info % 16, bind := info / 16, shndx := listReadU16LE sym 6 }
              return e' :: (← parseSymEntries strtab strSize n (sym.drop 24))) = .ok (e :: rest)
            rw [hread, hrest]; rfl
          · intro k hk
            have hne : (e.name == strOfBytes pats[k]) = false := by
              rw [beq_eq_false_iff_ne]
              intro heq
              have hcseq : cs = pats[k] := strOfBytes_inj heq
              have hmb := (readCStringBytes_eq_iff_bytesMatchCstr (strSize - stName) sBytes []
                pats[k] hz (hno0 _ (List.getElem_mem hk))).mp (by simpa [hcseq] using hcs)
              have hmbF := findFirstMatch_none pats 0 sBytes hfm pats[k] (List.getElem_mem hk)
              rw [hmbF] at hmb
              cases hmb
            simp only [List.filter_cons, hne, Bool.false_eq_true, ↓reduceIte]
            exact hfilt k hk
        | some p =>
          obtain ⟨k0, pat0⟩ := p
          rw [hfm] at h
          dsimp only at h
          obtain ⟨_, hk0, hpat0, hmb0⟩ := findFirstMatch_some pats 0 sBytes k0 pat0 hfm
          simp only [Nat.sub_zero] at hk0 hpat0
          have hcseq : cs = pat0 := by
            have h1 := (readCStringBytes_eq_iff_bytesMatchCstr (strSize - stName) sBytes []
              pat0 hz (hpat0 ▸ hno0 _ (List.getElem_mem hk0))).mpr hmb0
            simp only [List.reverse_nil, List.nil_append] at h1
            exact Option.some.inj (hcs.symm.trans h1)
          have heEq :
              ({ name := strOfBytes pat0
                 value := listReadU64LE sym 8
                 size := listReadU64LE sym 16
                 type := info % 16
                 bind := info / 16
                 shndx := listReadU16LE sym 6 } : ElfSym) = e := by
            simp [e, hcseq]
          rw [heEq] at h
          obtain ⟨rest, hrest, hfilt⟩ :=
            scanSymEntries_sound strtab strSize tree htree pats hnd hno0 n (sym.drop 24)
              ((k0, e) :: acc) hits h
          refine ⟨e :: rest, ?_, ?_⟩
          · unfold parseSymEntries
            rw [ite_eq_right (fun hc => absurd hc hlt)]
            show (do
              let some name := readStrtabCString (strSize - stName) sBytes []
                | Except.error "symtab: unterminated name"
              let info := listGetByte sym 4
              let e' : ElfSym :=
                { name, value := listReadU64LE sym 8, size := listReadU64LE sym 16,
                  type := info % 16, bind := info / 16, shndx := listReadU16LE sym 6 }
              return e' :: (← parseSymEntries strtab strSize n (sym.drop 24))) = .ok (e :: rest)
            rw [hread, hrest]; rfl
          · intro k hk
            have hstep := hfilt k hk
            simp only [List.reverse_cons, List.filter_append, List.map_append,
              List.append_assoc] at hstep
            have heMatch : (e.name == strOfBytes pats[k]) = (k0 == k) := by
              by_cases hkk : k0 = k
              · subst hkk
                have : e.name = strOfBytes pats[k0] := by simp [e, hcseq, hpat0]
                simp [this]
              · have hne1 : (k0 == k) = false := by rw [beq_eq_false_iff_ne]; exact hkk
                have hne2 : (e.name == strOfBytes pats[k]) = false := by
                  rw [beq_eq_false_iff_ne]
                  intro heq
                  have hpeq : pats[k0] = pats[k] := by
                    rw [hpat0, ← hcseq]
                    exact strOfBytes_inj heq
                  have hfin : (⟨k0, hk0⟩ : Fin pats.length) = ⟨k, hk⟩ :=
                    List.nodup_iff_injective_getElem.mp hnd (by simpa using hpeq)
                  exact hkk (Fin.mk.inj hfin)
                rw [hne1, hne2]
            rw [← hstep]
            simp only [List.filter_cons, List.filter_nil, heMatch]
            cases k0 == k <;> simp
      · cases h

private def checkFuncHit (regs : List (Snapshot.Region × Nat)) (shdrs : List ElfShdr)
    (hits : List (Nat × ElfSym)) (k : Nat) : Option Nat :=
  match (hits.filter (·.1 == k)).map (·.2) with
  | [e] =>
    match shdrs[e.shndx]? with
    | some sh =>
      if e.type == 2 && e.size != 0 && e.value % 4 == 0 && e.shndx != 0 && e.shndx < 0xff00 &&
          sh.type == 1 && sh.flags &&& 6 == 6 &&
          sh.addr ≤ e.value && e.value + e.size ≤ sh.addr + sh.size &&
          regs.any (fun p => p.1.perm.x && p.1.start.toNat ≤ e.value &&
            e.value + e.size ≤ p.1.start.toNat + p.2) then some e.value
      else none
    | none => none
  | _ => none

private theorem resolveSym_of_checkFuncHit {img : ElfImage} {syms : List ElfSym}
    {shdrs : List ElfShdr} {hits : List (Nat × ElfSym)} {name : String} {k v : Nat}
    (hfilt : syms.filter (·.name == name) = (hits.filter (·.1 == k)).map (·.2))
    (hchk : checkFuncHit (mapRegionsWithLen img.segments) shdrs hits k = some v) :
    resolveSym img syms shdrs name = .ok v := by
  unfold resolveSym
  rw [hfilt]
  unfold checkFuncHit at hchk
  simp only [mapRegionsWithLen_eq, List.any_map, Function.comp_def] at hchk
  split at hchk
  · rename_i e he
    rw [he]
    dsimp only
    split at hchk
    · rename_i sh hsh
      rw [hsh]
      dsimp only
      split at hchk
      · rename_i hc
        simp only [hc, ↓reduceIte]
        cases hchk
        rfl
      · cases hchk
    · cases hchk
  · cases hchk

private def cliElfTargetNames : List String :=
  cliPanicSymbolsPlaced ++
    [kyberEncapsElfSym, kyberDecapsElfSym, mlkemFromSeedElfSym,
     mlkemEncaps1ElfSym, mlkemDecapsElfSym]

private def cliElfTargetPats : List (List (BitVec 8)) :=
  cliElfTargetNames.map bytesOfString

private def listNodupPatsB : List (List (BitVec 8)) → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && listNodupPatsB xs

private theorem listNodupPatsB_sound : ∀ {xs : List (List (BitVec 8))},
    listNodupPatsB xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [listNodupPatsB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨?_, listNodupPatsB_sound h.2⟩
    intro hmem
    have := List.contains_iff_mem.mpr hmem
    rw [h.1] at this
    cases this

private def listNodupStrB : List String → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && listNodupStrB xs

private theorem listNodupStrB_sound : ∀ {xs : List String},
    listNodupStrB xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [listNodupStrB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨?_, listNodupStrB_sound h.2⟩
    intro hmem
    have := List.contains_iff_mem.mpr hmem
    rw [h.1] at this
    cases this

private theorem cliElfTargetPats_props :
    cliElfTargetPats.length = 23 ∧
    cliElfTargetPats.Nodup ∧
    (∀ p ∈ cliElfTargetPats, ∀ b ∈ p, b ≠ 0#8) ∧
    cliElfTargetPats.map strOfBytes = cliElfTargetNames ∧
    cliPanicSymbolsPlaced.Nodup := by
  have hlen : cliElfTargetPats.length = 23 := by rfl_kernel
  have hndP : listNodupPatsB cliElfTargetPats = true := by rfl_kernel
  have hno0B : (cliElfTargetPats.all fun p => p.all fun b => b != 0#8) = true := by rfl_kernel
  have hmap : cliElfTargetPats.map strOfBytes = cliElfTargetNames := by rfl_kernel
  have hndS : listNodupStrB cliPanicSymbolsPlaced = true := by rfl_kernel
  refine ⟨hlen, listNodupPatsB_sound hndP, ?_, hmap, listNodupStrB_sound hndS⟩
  intro p hp b hb
  have hpB := List.all_eq_true.mp hno0B p hp
  have hbB := List.all_eq_true.mp hpB b hb
  simpa using hbB

private def listNodupNatB : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && listNodupNatB xs

private theorem listNodupNatB_sound : ∀ {xs : List Nat}, listNodupNatB xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [listNodupNatB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨?_, listNodupNatB_sound h.2⟩
    intro hmem
    have := List.contains_iff_mem.mpr hmem
    rw [h.1] at this
    cases this

private def forceStrtabTree {α : Type} : StrtabTree → (StrtabTree → α) → α
  | .leaf off tail, k => k (.leaf off tail)
  | .node m l r, k =>
    forceStrtabTree l fun l' =>
      forceStrtabTree r fun r' =>
        k (.node m l' r')

private theorem forceStrtabTree_eq {α : Type} :
    ∀ (t : StrtabTree) (k : StrtabTree → α), forceStrtabTree t k = k t
  | .leaf _ _, _ => rfl
  | .node _ l r, k => by
    simp only [forceStrtabTree, forceStrtabTree_eq l, forceStrtabTree_eq r]

private def forceListSpine {α β : Type} : List α → (List α → β) → β
  | [], k => k []
  | x :: xs, k => forceListSpine xs fun rest => k (x :: rest)

private theorem forceListSpine_eq {α β : Type} :
    ∀ (xs : List α) (k : List α → β), forceListSpine xs k = k xs
  | [], _ => rfl
  | x :: xs, k => forceListSpine_eq xs (fun rest => k (x :: rest))

private def scanAndResolveCliElfAddrs (bytes : List (BitVec 8)) (elf : ElfImage) :
    Option CliElfAddrs :=
  withForcedNat (fastFileSize bytes (listReadU64LE bytes 40)) fun fileSize =>
    let eShoff := listReadU64LE bytes 40
    let eShnum := listReadU16LE bytes 60
    if fileSize < 64 || listReadU16LE bytes 58 != 64 || eShnum == 0 then none
    else if eShoff + eShnum * 64 > fileSize then none
    else withForcedList (fastDrop eShoff bytes) fun shTable =>
      match fastFindSymtabShdr eShnum shTable with
      | none => none
      | some (shOff, shSize, shLink, _, shEnt) =>
        if shEnt != 24 || shSize % 24 != 0 || shOff + shSize > fileSize || shLink ≥ eShnum then
          none
        else
          let strSh := drop64Blocks shLink shTable
          let strOff := listReadU64LE strSh 24
          let strSize := listReadU64LE strSh 32
          if listReadU32LE strSh 4 != 3 || strOff + strSize > fileSize then none
          else
            withForcedList (fastDrop shOff bytes) fun symtab =>
              withForcedList (fastDrop strOff bytes) fun strtab =>
                forceStrtabTree (buildStrtabTree 10 0 strSize strtab) fun tree =>
                  match scanSymEntries strtab strSize tree
                      cliElfTargetPats (shSize / 24) symtab [] with
                | none => none
                | some hits =>
                  forceListSpine (fastParseShdrs eShnum shTable) fun shdrs =>
                    forceListSpine (mapRegionsWithLen elf.segments) fun regs =>
                      do
                        let panicAddrs ← (List.range 18).mapM (checkFuncHit regs shdrs hits)
                        let kyberEncaps ← checkFuncHit regs shdrs hits 18
                        let kyberDecaps ← checkFuncHit regs shdrs hits 19
                        let mlkemFromSeed ← checkFuncHit regs shdrs hits 20
                        let mlkemEncaps1 ← checkFuncHit regs shdrs hits 21
                        let mlkemDecaps ← checkFuncHit regs shdrs hits 22
                        if !listNodupNatB (panicAddrs ++
                            [kyberEncaps, kyberDecaps, mlkemFromSeed, mlkemEncaps1, mlkemDecaps]) then
                          none
                        some {
                          panicAddrs
                          kyberEncapsVa := BitVec.ofNat 64 kyberEncaps
                          kyberDecapsVa := BitVec.ofNat 64 kyberDecaps
                          mlkemFromSeedVa := BitVec.ofNat 64 mlkemFromSeed
                          mlkemEncaps1Va := BitVec.ofNat 64 mlkemEncaps1
                          mlkemDecapsVa := BitVec.ofNat 64 mlkemDecaps
                        }

private theorem mapM_range_resolveSym {img : ElfImage} {syms : List ElfSym}
    {shdrs : List ElfShdr} {hits : List (Nat × ElfSym)} {addrs : List Nat}
    (hfilt : ∀ (k : Nat) (hk : k < 23),
      syms.filter (·.name == cliElfTargetNames[k]'(by
        have := cliElfTargetPats_props.1
        rw [← cliElfTargetPats_props.2.2.2.1, List.length_map]; omega)) =
        (hits.filter (·.1 == k)).map (·.2))
    (hmap : (List.range 18).mapM (checkFuncHit (mapRegionsWithLen img.segments) shdrs hits) =
      some addrs) :
    cliPanicSymbolsPlaced.mapM (resolveSym img syms shdrs) = .ok addrs := by
  have h18 : cliPanicSymbolsPlaced =
      (List.range 18).map (fun k => cliElfTargetNames.getD k "") := by decide
  rw [h18]
  have aux : ∀ (ks : List Nat) (as : List Nat),
      (∀ k ∈ ks, k < 18) →
      ks.mapM (checkFuncHit (mapRegionsWithLen img.segments) shdrs hits) = some as →
      (ks.map (fun k => cliElfTargetNames.getD k "")).mapM (resolveSym img syms shdrs) = .ok as := by
    intro ks
    induction ks with
    | nil =>
      intro as _ hm
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
      subst hm; rfl
    | cons k ks ih =>
      intro as hlt hm
      rw [List.mapM_cons] at hm
      cases h1 : checkFuncHit (mapRegionsWithLen img.segments) shdrs hits k with
      | none => rw [h1] at hm; cases hm
      | some v =>
        rw [h1] at hm
        change (do let vs ← ks.mapM _; some (v :: vs)) = some as at hm
        cases h2 : ks.mapM (checkFuncHit (mapRegionsWithLen img.segments) shdrs hits) with
        | none => rw [h2] at hm; cases hm
        | some vs =>
          rw [h2] at hm
          cases (Option.some.inj hm)
          have hk18 : k < 18 := hlt k List.mem_cons_self
          have hk23 : k < 23 := by omega
          have hkLen : k < cliElfTargetNames.length := by
            have := cliElfTargetPats_props.1
            rw [← cliElfTargetPats_props.2.2.2.1, List.length_map]; omega
          have hget : cliElfTargetNames.getD k "" = cliElfTargetNames[k]'hkLen := by
            simp [List.getD_eq_getElem?_getD, hkLen]
          have hres1 : resolveSym img syms shdrs (cliElfTargetNames.getD k "") = .ok v := by
            rw [hget]
            exact resolveSym_of_checkFuncHit (hfilt k hk23) h1
          have hres2 := ih vs (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) h2
          simp only [List.map_cons, List.mapM_cons, hres1, hres2]
          rfl
  exact aux (List.range 18) addrs (fun k hk => List.mem_range.mp hk) hmap

private theorem resolveCliElfAddrs_of_scan {bytes : List (BitVec 8)} {elf : ElfImage}
    {addrs : CliElfAddrs}
    (h : scanAndResolveCliElfAddrs bytes elf = some addrs) :
    resolveCliElfAddrs bytes elf = .ok addrs := by
  unfold scanAndResolveCliElfAddrs at h
  simp only [withForcedNat_eq, fastFileSize_eq_length, withForcedList_eq, fastDrop_eq_drop,
    fastFindSymtabShdr_eq, drop64Blocks_eq_drop, forceStrtabTree_eq, forceListSpine_eq,
    fastParseShdrs_eq] at h
  unfold resolveCliElfAddrs
  split at h
  · cases h
  · rename_i hc1
    split at h
    · cases h
    · rename_i hc2
      cases hsh : findSymtabShdr (listReadU16LE bytes 60) (bytes.drop (listReadU64LE bytes 40)) with
      | none => rw [hsh] at h; cases h
      | some t =>
        obtain ⟨shOff, shSize, shLink, shInfo, shEnt⟩ := t
        rw [hsh] at h
        dsimp only at h
        split at h
        · cases h
        · rename_i hc3
          split at h
          · cases h
          · rename_i hc4
            cases hsc : scanSymEntries (bytes.drop (listReadU64LE
                  ((bytes.drop (listReadU64LE bytes 40)).drop (shLink * 64)) 24))
                (listReadU64LE ((bytes.drop (listReadU64LE bytes 40)).drop (shLink * 64)) 32)
                (buildStrtabTree 10 0
                  (listReadU64LE ((bytes.drop (listReadU64LE bytes 40)).drop (shLink * 64)) 32)
                  (bytes.drop (listReadU64LE
                    ((bytes.drop (listReadU64LE bytes 40)).drop (shLink * 64)) 24)))
                cliElfTargetPats (shSize / 24) (bytes.drop shOff) [] with
            | none => rw [hsc] at h; cases h
            | some hits =>
              rw [hsc] at h
              dsimp only at h
              obtain ⟨hlen, hndP, hno0, hmapStr, hndPanics⟩ := cliElfTargetPats_props
              obtain ⟨syms, hparse, hfilt0⟩ := scanSymEntries_sound _ _ _
                (buildStrtabTree_valid _ 10 0 _ _ rfl) cliElfTargetPats hndP hno0
                (shSize / 24) (bytes.drop shOff) [] hits hsc
              have hfilt : ∀ (k : Nat) (hk : k < 23),
                  syms.filter (·.name == cliElfTargetNames[k]'(by
                    rw [← hmapStr, List.length_map, hlen]; exact hk)) =
                  (hits.filter (·.1 == k)).map (·.2) := by
                intro k hk
                have hk' : k < cliElfTargetPats.length := by omega
                have hnm : cliElfTargetNames[k]'(by rw [← hmapStr, List.length_map, hlen]; exact hk) =
                    strOfBytes cliElfTargetPats[k] := by
                  have := congrArg (fun l => l.getD k "") hmapStr
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
                    List.getElem?_eq_getElem hk', Option.map_some] at this
                  have hkL : k < cliElfTargetNames.length := by
                    rw [← hmapStr, List.length_map, hlen]; exact hk
                  rw [List.getElem?_eq_getElem hkL] at this
                  exact this.symm
                rw [hnm]
                have hf := hfilt0 k hk'
                simpa using hf
              set shdrs := parseShdrs (listReadU16LE bytes 60) (bytes.drop (listReadU64LE bytes 40))
              set regs := mapRegionsWithLen elf.segments
              -- Destructure the `Option` do-block in `h`
              cases hpan : (List.range 18).mapM (checkFuncHit regs shdrs hits) with
              | none => simp [hpan] at h
              | some panicAddrs =>
                simp only [hpan, bind, Option.bind] at h
                cases h18 : checkFuncHit regs shdrs hits 18 with
                | none => simp [h18] at h
                | some v18 =>
                  cases h19 : checkFuncHit regs shdrs hits 19 with
                  | none => simp [h18, h19] at h
                  | some v19 =>
                    cases h20 : checkFuncHit regs shdrs hits 20 with
                    | none => simp [h18, h19, h20] at h
                    | some v20 =>
                      cases h21 : checkFuncHit regs shdrs hits 21 with
                      | none => simp [h18, h19, h20, h21] at h
                      | some v21 =>
                        cases h22 : checkFuncHit regs shdrs hits 22 with
                        | none => simp [h18, h19, h20, h21, h22] at h
                        | some v22 =>
                          simp only [h18, h19, h20, h21, h22] at h
                          cases hndA : listNodupNatB (panicAddrs ++ [v18, v19, v20, v21, v22]) with
                          | false => simp [hndA] at h
                          | true =>
                            simp only [hndA, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                              Option.some.injEq] at h
                            subst h
                            have hrPan := mapM_range_resolveSym hfilt hpan
                            have hr18 : resolveSym elf syms shdrs kyberEncapsElfSym = .ok v18 :=
                              resolveSym_of_checkFuncHit (hfilt 18 (by omega)) h18
                            have hr19 : resolveSym elf syms shdrs kyberDecapsElfSym = .ok v19 :=
                              resolveSym_of_checkFuncHit (hfilt 19 (by omega)) h19
                            have hr20 : resolveSym elf syms shdrs mlkemFromSeedElfSym = .ok v20 :=
                              resolveSym_of_checkFuncHit (hfilt 20 (by omega)) h20
                            have hr21 : resolveSym elf syms shdrs mlkemEncaps1ElfSym = .ok v21 :=
                              resolveSym_of_checkFuncHit (hfilt 21 (by omega)) h21
                            have hr22 : resolveSym elf syms shdrs mlkemDecapsElfSym = .ok v22 :=
                              resolveSym_of_checkFuncHit (hfilt 22 (by omega)) h22
                            have hndBoth : cliPanicSymbolsPlaced.Nodup ∧
                                (panicAddrs ++ [v18, v19, v20, v21, v22]).Nodup :=
                              ⟨hndPanics, listNodupNatB_sound hndA⟩
                            have hndDec : (!decide (cliPanicSymbolsPlaced.Nodup ∧
                                (panicAddrs ++ [v18, v19, v20, v21, v22]).Nodup)) = false := by
                              rw [decide_eq_true hndBoth]; rfl
                            have hpf : parseSymtabFull bytes = .ok (syms, shdrs) := by
                              unfold parseSymtabFull
                              simp only [bind, Except.bind, pure, Except.pure]
                              rw [ite_eq_right (fun hc => absurd hc hc1),
                                ite_eq_right (fun hc => absurd hc hc2)]
                              simp only [hsh]
                              rw [ite_eq_right (fun hc => absurd hc hc3),
                                ite_eq_right (fun hc => absurd hc hc4)]
                              simp only [hparse]
                              rfl
                            simp only [hpf, hrPan, hr18, hr19, hr20, hr21, hr22,
                              hndDec, Bool.false_eq_true, ↓reduceIte,
                              bind, Except.bind, pure, Except.pure]

/-! ## 2. Concrete Resolution Witness for `cliElfBytes` (Layout-Generic) -/

/-- Lookup address of an extern symbol in `lsPlacedStubPairs` (no hardcoded address literals). -/
private noncomputable def stubPairAddr (sym : String) : BitVec 64 :=
  (lsPlacedStubPairs.lookup sym).getD 0#64

/-- Resolved `.symtab` addresses for `cliElfBytes`, derived directly from `lsPlacedStubPairs`
(zero hardcoded address literals). -/
noncomputable def cliElfAddrsVal : CliElfAddrs :=
  { panicAddrs := cliPanicSymbolsPlaced.map (fun s => (stubPairAddr s).toNat)
    kyberEncapsVa := stubPairAddr kyberEncapsElfSym
    kyberDecapsVa := stubPairAddr kyberDecapsElfSym
    mlkemFromSeedVa := stubPairAddr mlkemFromSeedElfSym
    mlkemEncaps1Va := stubPairAddr mlkemEncaps1ElfSym
    mlkemDecapsVa := stubPairAddr mlkemDecapsElfSym }

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1600000 in
private theorem cliElf_scanAddrs_ok :
    scanAndResolveCliElfAddrs cliElfBytes cliElfImage = some cliElfAddrsVal := by
  rfl_kernel

/-- All 23 `.symtab` function symbols of `cliElfBytes` resolve fail-closed to `cliElfAddrsVal`. -/
theorem cliElf_resolveAddrs :
    resolveCliElfAddrs cliElfBytes cliElfImage = .ok cliElfAddrsVal :=
  resolveCliElfAddrs_of_scan cliElf_scanAddrs_ok

/-! ## 3. Placement Agreement & Program / Patch / SampleNTT Bridge -/

private theorem cliElf_rho_getD_eq {idx : Nat}
    (hlt : idx < lsInternedMultiLib.names.length) :
    cliElfMultiPlacement.ρ (lsInternedMultiLib.names.getD idx "") =
      cliElfSymAddrs.getD idx 0#64 := by
  show (ElfCodeMatchesData.f3LsLayout.toMultiPlacement lsInternedMultiLib.names).ρ
      (lsInternedMultiLib.names.getD idx "") = cliElfSymAddrs.getD idx 0#64
  change ElfCodeMatchesData.f3LsLayout.addrs.getD
      (lsInternedMultiLib.names.idxOf (lsInternedMultiLib.names.getD idx "")) 0#64 = _
  rw [Obj.Interned.idxOf_getD ls_names_nodup hlt]
  rfl

private theorem cliElfMultiPlacement_rho_of_mem_stubPairs {nm : String} {va : BitVec 64}
    (hmem : (nm, va) ∈ lsPlacedStubPairs) :
    cliElfMultiPlacement.ρ nm = va := by
  rw [lsPlacedStubPairs_eq, List.mem_map] at hmem
  obtain ⟨idx, hidx, heq⟩ := hmem
  have hlt : idx < lsInternedMultiLib.names.length :=
    Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx)
  cases heq
  exact cliElf_rho_getD_eq hlt

private theorem lookup_eq_some_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {v : β}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by cases h
  | (k', v') :: rest, k, v, h => by
    simp only [List.lookup] at h
    cases hk : (k == k') with
    | true =>
      simp only [hk] at h
      have hkeq := beq_iff_eq.mp hk
      cases hkeq; cases Option.some.inj h
      exact List.mem_cons_self
    | false =>
      simp only [hk] at h
      exact List.mem_cons_of_mem _ (lookup_eq_some_mem h)

private theorem cliElfMultiPlacement_rho_eq_stubPairAddr {sym : String}
    (h : (lsPlacedStubPairs.lookup sym).isSome = true) :
    cliElfMultiPlacement.ρ sym = stubPairAddr sym := by
  unfold stubPairAddr
  cases hl : lsPlacedStubPairs.lookup sym with
  | none => rw [hl] at h; cases h
  | some va =>
    exact cliElfMultiPlacement_rho_of_mem_stubPairs (lookup_eq_some_mem hl)

set_option maxRecDepth 4000000 in
private theorem cliElf_targets_in_stubPairs :
    (cliPanicSymbolsPlaced.all fun s => (lsPlacedStubPairs.lookup s).isSome) = true ∧
    (lsPlacedStubPairs.lookup kyberEncapsElfSym).isSome = true ∧
    (lsPlacedStubPairs.lookup kyberDecapsElfSym).isSome = true ∧
    (lsPlacedStubPairs.lookup mlkemFromSeedElfSym).isSome = true ∧
    (lsPlacedStubPairs.lookup mlkemEncaps1ElfSym).isSome = true ∧
    (lsPlacedStubPairs.lookup mlkemDecapsElfSym).isSome = true := by
  exact ⟨by rfl_kernel, by rfl_kernel, by rfl_kernel, by rfl_kernel, by rfl_kernel, by rfl_kernel⟩

/-- The 5 `SampleNTT` entry predicates coincide between `.symtab` addresses and placement. -/
theorem mlKemSampleNttStuckAtElf_iff (u : State) :
    MlKemSampleNttStuckAtElf cliElfAddrsVal u ↔
      MlKemSampleNttStuckAt cliElfMultiPlacement u := by
  have h1 := cliElfMultiPlacement_rho_eq_stubPairAddr cliElf_targets_in_stubPairs.2.1
  have h2 := cliElfMultiPlacement_rho_eq_stubPairAddr cliElf_targets_in_stubPairs.2.2.1
  have h3 := cliElfMultiPlacement_rho_eq_stubPairAddr cliElf_targets_in_stubPairs.2.2.2.1
  have h4 := cliElfMultiPlacement_rho_eq_stubPairAddr cliElf_targets_in_stubPairs.2.2.2.2.1
  have h5 := cliElfMultiPlacement_rho_eq_stubPairAddr cliElf_targets_in_stubPairs.2.2.2.2.2
  unfold MlKemSampleNttStuckAtElf MlKemSampleNttStuckAt
  dsimp only [cliElfAddrsVal]
  rw [← h1, ← h2, ← h3, ← h4, ← h5]

private theorem externAt?_cliProgPlacedSig_direct (mpl : Obj.MultiPlacement) (pc : BitVec 64) :
    (cliProgPlacedSig mpl).externAt? pc =
      (libsignalSessionLib.blockLib 617).text.externs.findSome? fun e =>
        if libsignalSessionLib.resolve mpl e == pc then cliExternsPlacedSig e else none := by
  have key : ∀ (b : BitVec 64) (e : String),
      ((libsignalSessionLib.resolve mpl e - b).toNat == (pc - b).toNat) =
        (libsignalSessionLib.resolve mpl e == pc) := by
    intro b e
    cases h : libsignalSessionLib.resolve mpl e == pc with
    | true =>
      have heq := beq_iff_eq.mp h
      subst heq
      simp
    | false =>
      rw [beq_eq_false_iff_ne] at h ⊢
      intro hnat
      apply h
      have hbv := BitVec.eq_of_toNat_eq hnat
      have : (libsignalSessionLib.resolve mpl e - b) + b = (pc - b) + b := congrArg (· + b) hbv
      simpa [BitVec.sub_add_cancel] using this
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  dsimp only [cliProgPlacedSig, MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
    MultiPlacedLib.blockPlacement, Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0, Option.or_none, List.findSome?_map, Function.comp_def, key]

private theorem list_findSome?_congr {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.findSome?_cons, h a List.mem_cons_self]
    cases g a with
    | none => exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    | some _ => rfl

private theorem cliExternsPlacedSig_eq_panic (e : String) :
    cliExternsPlacedSig e =
      if isCliPanicSymbolPlaced e then some (abortOnPanic Rust.panicked) else none := by
  unfold cliExternsPlacedSig
  cases isCliPanicSymbolPlaced e <;> rfl

private def panicPrefixChars : List Char :=
  ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':']

private theorem string_startsWith_eq_isPrefixOf (s pat : String) :
    s.startsWith pat = pat.toList.isPrefixOf s.toList := by
  rw [Bool.eq_iff_iff, String.startsWith_string_iff, List.isPrefixOf_iff_prefix]

private theorem core_panicking_toList_eq : "core::panicking::".toList = panicPrefixChars := by
  decide

private def isPanicSymbolFast (name : String) : Bool :=
  panicPrefixChars.isPrefixOf name.toList ||
    (name == "core::result::unwrap_failed" ||
      (name == "core::option::unwrap_failed" ||
        (name == "core::option::expect_failed" ||
          (name == "core::slice::index::slice_start_index_len_fail" ||
            (name == "core::slice::index::slice_end_index_len_fail" ||
              (name == "core::slice::index::slice_index_order_fail" ||
                (name == "core::slice::index::slice_index_fail" ||
                  (name == "alloc::raw_vec::handle_error" ||
                    (name == "alloc::raw_vec::capacity_overflow" ||
                      name == "alloc::alloc::handle_alloc_error")))))))))

private theorem isPanicSymbol_eq_fast (name : String) :
    Rust.isPanicSymbol name = isPanicSymbolFast name := by
  apply Bool.eq_iff_iff.mpr
  simp [Rust.isPanicSymbol, isPanicSymbolFast, string_startsWith_eq_isPrefixOf,
    core_panicking_toList_eq]

private def isCliPanicFast (name : String) : Bool :=
  cliPanicSymbolsPlaced.contains name || isPanicSymbolFast name

private theorem isCliPanicSymbolPlaced_eq_fast (name : String) :
    isCliPanicSymbolPlaced name = isCliPanicFast name := by
  simp [isCliPanicSymbolPlaced, isCliPanicFast, isPanicSymbol_eq_fast]

private theorem findSome_panic_eq_contains (pairs : List (String × BitVec 64)) (pc : BitVec 64) :
    (pairs.findSome? fun (n, a) =>
      if a == pc then (if isCliPanicFast n then some (abortOnPanic Rust.panicked) else none)
      else none) =
      if ((pairs.filter (fun p => isCliPanicFast p.1)).map (fun p => p.2.toNat)).contains pc.toNat
      then some (abortOnPanic Rust.panicked) else none := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨n, a⟩ := p
    simp only [List.findSome?_cons, List.filter_cons]
    have haEq : (a == pc) = (a.toNat == pc.toNat) := by
      cases h : a == pc
      · have hne : a ≠ pc := beq_eq_false_iff_ne.mp h
        symm; rw [beq_eq_false_iff_ne]
        exact fun hn => hne (BitVec.eq_of_toNat_eq hn)
      · have heq := beq_iff_eq.mp h
        subst heq; simp
    cases hp : isCliPanicFast n
    · simp only [Bool.false_eq_true, ↓reduceIte, ite_self, ih]
    · simp only [↓reduceIte, List.map_cons, List.contains_cons, haEq]
      have hcomm : (pc.toNat == a.toNat) = (a.toNat == pc.toNat) := BEq.comm
      rw [hcomm]
      cases hpc : a.toNat == pc.toNat
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or, ih]
      · simp only [↓reduceIte, Bool.true_or]

private theorem lsPlacedStubPairs_panic_eq_list :
    (lsPlacedStubPairs.all fun p =>
      isCliPanicFast p.1 == cliPanicSymbolsPlaced.contains p.1) = true := by
  rfl_kernel

private theorem lsPlacedStubPairs_panic_lookup_agrees :
    (lsPlacedStubPairs.all fun p =>
      !cliPanicSymbolsPlaced.contains p.1 ||
        lsPlacedStubPairs.lookup p.1 == some p.2) = true := by
  rfl_kernel

private theorem cliElf_panicAddrs_contains_eq (x : Nat) :
    cliElfAddrsVal.panicAddrs.contains x =
      ((lsPlacedStubPairs.filter (fun p => isCliPanicFast p.1)).map
        (fun p => p.2.toNat)).contains x := by
  have h1 := List.all_eq_true.mp lsPlacedStubPairs_panic_eq_list
  have h2 := List.all_eq_true.mp lsPlacedStubPairs_panic_lookup_agrees
  have h3 := List.all_eq_true.mp cliElf_targets_in_stubPairs.1
  apply Bool.eq_iff_iff.mpr
  simp only [cliElfAddrsVal, List.contains_iff_mem, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hisSome := h3 s hs
    cases hl : lsPlacedStubPairs.lookup s with
    | none => rw [hl] at hisSome; cases hisSome
    | some va =>
      refine ⟨(s, va), ⟨lookup_eq_some_mem hl, ?_⟩, ?_⟩
      · have heq := beq_iff_eq.mp (h1 (s, va) (lookup_eq_some_mem hl))
        rw [heq, List.contains_iff_mem]
        exact hs
      · simp [stubPairAddr, hl]
  · rintro ⟨⟨n, a⟩, ⟨hmem, hpan⟩, rfl⟩
    have hmemPan : n ∈ cliPanicSymbolsPlaced := by
      have heq := beq_iff_eq.mp (h1 (n, a) hmem)
      rw [← List.contains_iff_mem, ← heq]
      exact hpan
    have hlk := h2 (n, a) hmem
    have hcnt : cliPanicSymbolsPlaced.contains n = true := List.contains_iff_mem.mpr hmemPan
    simp only [hcnt, Bool.not_true, Bool.false_or, beq_iff_eq] at hlk
    exact ⟨n, hmemPan, by simp [stubPairAddr, hlk]⟩

/-- The ELF-direct panic program `cliProgElf cliElfAddrsVal` has the exact same `externAt?` table
as `cliProgPlacedSig cliElfMultiPlacement` at every `pc : BitVec 64`. -/
theorem cliProgElf_externAt_eq (pc : BitVec 64) :
    (cliProgElf cliElfAddrsVal).externAt? pc =
      (cliProgPlacedSig cliElfMultiPlacement).externAt? pc := by
  -- LHS: `overrideProgram` via `Program.ofSites_externAt`
  have hndNames : (zipSites cliPanicOverrides cliElfAddrsVal.panicAddrs |>.map (·.1)).Nodup := by
    have hmap : (zipSites cliPanicOverrides cliElfAddrsVal.panicAddrs).map (·.1) =
        cliPanicSymbolsPlaced := by
      have aux : ∀ (ns : List String) (as : List Nat), ns.length = as.length →
          (zipSites (ns.map (fun s => (s, abortOnPanic Rust.panicked))) as).map (·.1) = ns := by
        intro ns
        induction ns with
        | nil => intro as h; cases as <;> simp [zipSites] at h ⊢
        | cons n ns ih =>
          intro as h
          cases as with
          | nil => simp at h
          | cons a as =>
            change n :: (zipSites (ns.map (fun s => (s, abortOnPanic Rust.panicked))) as).map (·.1) =
              n :: ns
            exact congrArg (n :: ·) (ih as (by simpa using h))
      exact aux cliPanicSymbolsPlaced cliElfAddrsVal.panicAddrs (by simp [cliElfAddrsVal])
    rw [hmap]
    exact cliElfTargetPats_props.2.2.2.2
  have hlhs : (cliProgElf cliElfAddrsVal).externAt? pc =
      if cliElfAddrsVal.panicAddrs.contains pc.toNat
      then some (abortOnPanic Rust.panicked) else none := by
    change (Program.ofSites execSyscall
        (zipSites cliPanicOverrides cliElfAddrsVal.panicAddrs)).externAt? pc = _
    rw [Program.ofSites_externAt _ _ hndNames]
    have aux : ∀ (ns : List String) (as : List Nat), ns.length = as.length →
        ((zipSites (ns.map (fun s => (s, abortOnPanic Rust.panicked))) as).find?
          (·.2.1 == pc.toNat)).map (·.2.2) =
        if as.contains pc.toNat then some (abortOnPanic Rust.panicked) else none := by
      intro ns
      induction ns with
      | nil => intro as h; cases as <;> simp [zipSites] at h ⊢
      | cons n ns ih =>
        intro as h
        cases as with
        | nil => simp at h
        | cons a as =>
          simp only [zipSites, List.map_cons, List.zipWith_cons_cons, List.find?_cons,
            List.contains_cons]
          have hcomm : (pc.toNat == a) = (a == pc.toNat) := BEq.comm
          rw [hcomm]
          cases ha : a == pc.toNat
          · simp only [Bool.false_or]
            exact ih as (by simpa using h)
          · simp
    exact aux cliPanicSymbolsPlaced cliElfAddrsVal.panicAddrs (by simp [cliElfAddrsVal])
  -- RHS: `cliProgPlacedSig` via `ls_block617_externs_eq` and `lsPlacedStubPairs_eq`
  have hrhs : (cliProgPlacedSig cliElfMultiPlacement).externAt? pc =
      if ((lsPlacedStubPairs.filter (fun p => isCliPanicFast p.1)).map
            (fun p => p.2.toNat)).contains pc.toNat
      then some (abortOnPanic Rust.panicked) else none := by
    rw [externAt?_cliProgPlacedSig_direct, ls_block617_externs_eq, List.findSome?_map]
    rw [← findSome_panic_eq_contains, lsPlacedStubPairs_eq, List.findSome?_map]
    refine list_findSome?_congr fun idx hidx => ?_
    dsimp only [Function.comp_def]
    have hlt : idx < lsInternedMultiLib.names.length :=
      Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx)
    have hres : libsignalSessionLib.resolve cliElfMultiPlacement
        (lsInternedMultiLib.names.getD idx "") = f3LsSymAddrs.getD idx 0#64 := by
      rw [ls_toMultiPlacedLib_eq]
      change lsInternedMultiLib.toMultiPlacedLib.resolve
        (ElfCodeMatchesData.f3LsLayout.toMultiPlacement lsInternedMultiLib.names) _ = _
      rw [Obj.Interned.toMultiPlacement_resolve_eq ls_names_nodup ls_idsOk ls_blockSymsMatch_ok,
        Obj.Interned.idxOf_getD ls_names_nodup hlt]
      rfl
    rw [hres, cliExternsPlacedSig_eq_panic, isCliPanicSymbolPlaced_eq_fast]
  rw [hlhs, hrhs, cliElf_panicAddrs_contains_eq]

private theorem step_of_externAt_eq {p₁ p₂ : Program}
    (hext : ∀ pc, p₁.externAt? pc = p₂.externAt? pc) (hsvc : p₁.svc = p₂.svc)
    {s s' : State} (h : Step p₁ s s') : Step p₂ s s' := by
  have hf : p₁.fetchMem s.mem s.pc = p₂.fetchMem s.mem s.pc := by
    unfold Program.fetchMem; rw [hext]
  have hev : ∀ inst, p₁.evalInst inst s = p₂.evalInst inst s := fun inst => by
    unfold Program.evalInst; rw [hsvc]
  cases h with
  | @exec inst hr hfe => rw [hev inst]; exact .exec hr (hf ▸ hfe)
  | halt_unmapped hr hfe he => exact .halt_unmapped hr (hf ▸ hfe) (hext _ ▸ he)
  | extern hr he hk hsy => exact .extern hr (hext _ ▸ he) hk hsy
  | extern_fault hr he hn => exact .extern_fault hr (hext _ ▸ he) hn

private theorem step_iff_of_externAt_eq {p₁ p₂ : Program}
    (hext : ∀ pc, p₁.externAt? pc = p₂.externAt? pc) (hsvc : p₁.svc = p₂.svc)
    (s s' : State) : Step p₁ s s' ↔ Step p₂ s s' :=
  ⟨step_of_externAt_eq hext hsvc,
   step_of_externAt_eq (fun pc => (hext pc).symm) hsvc.symm⟩

private theorem steps_of_externAt_eq {p₁ p₂ : Program}
    (hext : ∀ pc, p₁.externAt? pc = p₂.externAt? pc) (hsvc : p₁.svc = p₂.svc)
    {s s' : State} (h : Steps p₁ s s') : Steps p₂ s s' := by
  induction h with
  | refl => exact .refl _
  | step h1 _ ih => exact .step (step_of_externAt_eq hext hsvc h1) ih

private theorem steps_iff_of_externAt_eq {p₁ p₂ : Program}
    (hext : ∀ pc, p₁.externAt? pc = p₂.externAt? pc) (hsvc : p₁.svc = p₂.svc)
    (s s' : State) : Steps p₁ s s' ↔ Steps p₂ s s' :=
  ⟨steps_of_externAt_eq hext hsvc,
   steps_of_externAt_eq (fun pc => (hext pc).symm) hsvc.symm⟩

private theorem processRunsTo_iff_of_externAt_eq {p₁ p₂ : Program}
    (hext : ∀ pc, p₁.externAt? pc = p₂.externAt? pc) (hsvc : p₁.svc = p₂.svc)
    (s0 : State) (post : ProcessOutcome → Prop) :
    ProcessRunsTo p₁ s0 post ↔ ProcessRunsTo p₂ s0 post := by
  unfold ProcessRunsTo ProcessTerminates ProcessExitsWith ProcessPartialRunsTo
  simp only [steps_iff_of_externAt_eq hext hsvc, step_iff_of_externAt_eq hext hsvc]

/-- `CliRunsToElf` at `cliElfAddrsVal` is equivalent to `CliRunsToPlainPanPlaced1` at
`cliElfMultiPlacement`. -/
theorem cliRunsToElf_iff (i : Inputs) (o : Outcome) :
    CliRunsToElf cliElfImage cliElfAddrsVal i o ↔
      CliRunsToPlainPanPlaced1 cliElfMultiPlacement cliElfImage i o := by
  unfold CliRunsToElf CliRunsToPlainPanPlaced1
  constructor
  · rintro ⟨s0, hl, hr⟩
    exact ⟨s0, hl, (processRunsTo_iff_of_externAt_eq cliProgElf_externAt_eq rfl _ _).mp hr⟩
  · rintro ⟨s0, hl, hr⟩
    exact ⟨s0, hl, (processRunsTo_iff_of_externAt_eq cliProgElf_externAt_eq rfl _ _).mpr hr⟩

open Classical in
/-- `cliRunElf` at `cliElfAddrsVal` equals `cliRunPlainPanPlaced1` at `cliElfMultiPlacement`. -/
theorem cliRunElf_eq :
    cliRunElf cliElfImage cliElfAddrsVal =
      cliRunPlainPanPlaced1 cliElfMultiPlacement cliElfImage := by
  funext i
  unfold cliRunElf cliRunPlainPanPlaced1
  have h : (fun o => CliRunsToElf cliElfImage cliElfAddrsVal i o) =
      (fun o => CliRunsToPlainPanPlaced1 cliElfMultiPlacement cliElfImage i o) :=
    funext fun o => propext (cliRunsToElf_iff i o)
  have aux : ∀ (p q : Outcome → Prop), p = q →
      (if h : ∃ o, p o then some (Classical.choose h) else none) =
      (if h : ∃ o, q o then some (Classical.choose h) else none) := by
    rintro p _ rfl; rfl
  exact aux _ _ h

/-- `CliReachesOOMElf` at `cliElfAddrsVal` is equivalent to `CliReachesOOMPlainPanPlaced1`. -/
theorem cliReachesOOMElf_iff (i : Inputs) :
    CliReachesOOMElf cliElfImage cliElfAddrsVal i ↔
      CliReachesOOMPlainPanPlaced1 cliElfMultiPlacement cliElfImage i := by
  unfold CliReachesOOMElf CliReachesOOMPlainPanPlaced1
  constructor
  · rintro ⟨s0, s, hl, hst, hoom⟩
    exact ⟨s0, s, hl, (steps_iff_of_externAt_eq cliProgElf_externAt_eq rfl _ _).mp hst, hoom⟩
  · rintro ⟨s0, s, hl, hst, hoom⟩
    exact ⟨s0, s, hl, (steps_iff_of_externAt_eq cliProgElf_externAt_eq rfl _ _).mpr hst, hoom⟩

/-- `CliReachesSampleNttStuckElf` at `cliElfAddrsVal` is equivalent to
`CliReachesSampleNttStuckPlainPanPlaced1`. -/
theorem cliReachesSampleNttStuckElf_iff (i : Inputs) :
    CliReachesSampleNttStuckElf cliElfImage cliElfAddrsVal i ↔
      CliReachesSampleNttStuckPlainPanPlaced1 cliElfMultiPlacement cliElfImage i := by
  unfold CliReachesSampleNttStuckElf CliReachesSampleNttStuckPlainPanPlaced1
  constructor
  · rintro ⟨s0, u, hl, hst, hrun, hstck⟩
    exact ⟨s0, u, hl, (steps_iff_of_externAt_eq cliProgElf_externAt_eq rfl _ _).mp hst,
      hrun, (mlKemSampleNttStuckAtElf_iff u).mp hstck⟩
  · rintro ⟨s0, u, hl, hst, hrun, hstck⟩
    exact ⟨s0, u, hl, (steps_iff_of_externAt_eq cliProgElf_externAt_eq rfl _ _).mpr hst,
      hrun, (mlKemSampleNttStuckAtElf_iff u).mpr hstck⟩

/-- Excuse-predicate equivalence between ELF-direct and plain-memory placed runs. -/
theorem cliExcusedElf_iff (i : Inputs) :
    cliExcusedElf cliElfImage cliElfAddrsVal i ↔
      (CliReachesOOMPlainPanPlaced1 cliElfMultiPlacement cliElfImage i ∨
        CliReachesSampleNttStuckPlainPanPlaced1 cliElfMultiPlacement cliElfImage i) := by
  unfold cliExcusedElf
  rw [cliReachesOOMElf_iff, cliReachesSampleNttStuckElf_iff]

/-- Uniqueness of `(elf, addrs)` parsed and resolved from `cliElfBytes`. -/
theorem cliElf_parse_resolve_unique {elf : ElfImage} {addrs : CliElfAddrs}
    (hp : ElfImage.parse cliElfBytes = .ok elf)
    (hr : resolveCliElfAddrs cliElfBytes elf = .ok addrs) :
    elf = cliElfImage ∧ addrs = cliElfAddrsVal := by
  have h1 : elf = cliElfImage := Except.ok.inj (hp.symm.trans cliElf_parse)
  subst h1
  exact ⟨rfl, Except.ok.inj (hr.symm.trans cliElf_resolveAddrs)⟩

/-- Bridge: any `CliPqxdhBinaryCorrectPlainPanPlaced cliElfBytes` proof yields the ELF-direct
`CliPqxdhBinaryCorrect cliElfBytes`. -/
theorem cliPqxdhBinaryCorrect_of_plainPanPlaced
    (h : CliPqxdhBinaryCorrectPlainPanPlaced cliElfBytes) :
    CliPqxdhBinaryCorrect cliElfBytes := by
  obtain ⟨elf, hp, hcorr2⟩ :=
    h cliElfMultiPlacement ElfMallocngPlaced.cliElfMallocngPlacement
      cliElf_linkedAt cliElf_mallocng_linkedAt
  cases cliElf_parse.symm.trans hp
  have hcorr1 := cliPqxdhElfCorrectPlainPanPlaced_to_1
    (cliElf_trustedCodeMatchesPlaced_of_linkedAt cliElf_linkedAt) hcorr2
  refine ⟨cliElfImage, cliElfAddrsVal, cliElf_parse, cliElf_resolveAddrs, fun X => ?_⟩
  have hX := hcorr1.2 X
  have hexc : cliExcusedElf cliElfImage cliElfAddrsVal =
      (fun i => CliReachesOOMPlainPanPlaced1 cliElfMultiPlacement cliElfImage i ∨
        CliReachesSampleNttStuckPlainPanPlaced1 cliElfMultiPlacement cliElfImage i) :=
    funext (fun i => propext (cliExcusedElf_iff i))
  rw [hexc, cliRunElf_eq]
  exact hX

/-! ## 4. Non-Headline Cross-Check: `.symtab` Labels Agree with Placement -/

/-- Non-headline kernel-checked cross-check: every one of the 23 `.symtab` function addresses
resolved from `cliElfBytes` (18 Rust panic entry points and 5 `SampleNTT` entry points) agrees with
`cliElfMultiPlacement.ρ` (whose names are tied to the pre-link extracted objects by
`CliLabelsFromObjects`). -/
theorem cliElf_symtab_agrees_with_placement :
    (∀ p ∈ cliPanicSymbolsPlaced.zip cliElfAddrsVal.panicAddrs,
      cliElfMultiPlacement.ρ p.1 = BitVec.ofNat 64 p.2) ∧
    cliElfMultiPlacement.ρ kyberEncapsElfSym = cliElfAddrsVal.kyberEncapsVa ∧
    cliElfMultiPlacement.ρ kyberDecapsElfSym = cliElfAddrsVal.kyberDecapsVa ∧
    cliElfMultiPlacement.ρ mlkemFromSeedElfSym = cliElfAddrsVal.mlkemFromSeedVa ∧
    cliElfMultiPlacement.ρ mlkemEncaps1ElfSym = cliElfAddrsVal.mlkemEncaps1Va ∧
    cliElfMultiPlacement.ρ mlkemDecapsElfSym = cliElfAddrsVal.mlkemDecapsVa := by
  dsimp only [cliElfAddrsVal]
  refine ⟨?_,
    cliElfMultiPlacement_rho_eq_stubPairAddr cliElf_targets_in_stubPairs.2.1,
    cliElfMultiPlacement_rho_eq_stubPairAddr cliElf_targets_in_stubPairs.2.2.1,
    cliElfMultiPlacement_rho_eq_stubPairAddr cliElf_targets_in_stubPairs.2.2.2.1,
    cliElfMultiPlacement_rho_eq_stubPairAddr cliElf_targets_in_stubPairs.2.2.2.2.1,
    cliElfMultiPlacement_rho_eq_stubPairAddr cliElf_targets_in_stubPairs.2.2.2.2.2⟩
  intro p hp
  have hzip : ∀ (ns : List String) (q : String × Nat),
      q ∈ ns.zip (ns.map (fun s => (stubPairAddr s).toNat)) →
      q.1 ∈ ns ∧ q.2 = (stubPairAddr q.1).toNat := by
    intro ns
    induction ns with
    | nil => intro q hq; cases hq
    | cons n ns ih =>
      intro q hq
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨List.mem_cons_self, rfl⟩
      · obtain ⟨hm, he⟩ := ih q hq
        exact ⟨List.mem_cons_of_mem _ hm, he⟩
  obtain ⟨hmem, hval⟩ := hzip cliPanicSymbolsPlaced p hp
  rw [hval, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact cliElfMultiPlacement_rho_eq_stubPairAddr
    (List.all_eq_true.mp cliElf_targets_in_stubPairs.1 p.1 hmem)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge
