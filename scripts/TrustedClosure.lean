/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean

/-!
# Trusted Closure of the Headline Theorems

Computes the transitive definition closure of each headline theorem statement: starting from each
theorem's type, traverses types and bodies of definitions, abbreviations, instances, and inductive
declarations without unfolding proofs (`thmInfo` or `Prop`-valued `defnInfo`), while recording
opaque constants by type only. Source ranges of unfolded declarations are unioned per file and
grouped into five tiers (`T`, `repo`, `arm64-semantics`, `generated`, `foundations`), alongside
module import closures, trust banners (`trusted_banners.csv`), and Rule 5 checks.

Invoke after `lake build` via `scripts/trusted-closure.sh` (which merges the split `Arm64`
`LEAN_PATH` roots):

    scripts/trusted-closure.sh [--symbolic] [--out-dir DIR] [--commit SHA]
        [--headline LABEL:NAME:MODULE ... | --headlines-file PATH] [--statement-file PATH ...]
        [--stop NAME ...] [--self-test-pinned-stop]
-/

open Lean Meta System

namespace TrustedClosure

structure Headline where
  label : String
  name : Name
  module : Name
  deriving Inhabited

/-- Default computational headline theorems in `Computational/Theorems/` (excluding `CliElfLib`,
which lives in `Computational.Theorems.Main`). The first entry is the main headline used for
per-file report tables. -/
def defaultHeadlines : Array Headline := #[
  -- Lemma 1: model-level PQXDH correctness, one-key key indistinguishability, and one-key
  -- first-message `Auth` under a δ-correct KEM
  ⟨"L1", `SignalPqxdh.Security.headlineδ, `Computational.Theorems.Lemmas⟩,
  -- Lemma 2: Double Ratchet + SPQR V1 single-session security (`SessionSecure`)
  ⟨"L2", `CryptoVerification.E2E.session_secure, `Computational.Theorems.Lemmas⟩,
  -- Lemma 3: multi-session model composition with costed reductions (`ModelSecure`)
  ⟨"L3", `CryptoVerification.E2E.model_secure_costed, `Computational.Theorems.Lemmas⟩,
  -- Round-3 CRYSTALS-Kyber-1024 `δ_kem = ε + 1 / 2^112` under `KyberNoiseGap ε`
  ⟨"KyberDelta", `CryptoVerification.E2E.kyber1024_kem_delta_correct, `Computational.Theorems.Lemmas⟩
]

/-- Statement files forming tier `T` (`Computational/docs/TRUSTED_BASE.md` §1). Files from which
headlines use only isolated definitions are omitted here and counted in tier `repo`. -/
def defaultStatementFiles : Array String := #[
  "LibsignalBinary/Specifications/LibsignalE2E/State.lean",
  "LibsignalBinary/Specifications/LibsignalE2E/PqxdhInputs.lean",
  "LibsignalBinary/Specifications/LibsignalE2E/PqxdhModelLink.lean",
  "LibsignalBinary/Specifications/LibsignalE2E/PqxdhCorrectModel.lean",
  "Computational/Specifications/Pqxdh/Security/HeadlineDelta.lean",
  "Computational/Specifications/Pqxdh/Security/Headline.lean",
  "Computational/Specifications/Pqxdh/Security/Auth/Headline.lean",
  "Computational/Specifications/Pqxdh/Security/Auth/Game.lean",
  "Computational/Specifications/Pqxdh/Bound.lean",
  "Computational/Specifications/Pqxdh/Game.lean",
  "Computational/Specifications/Assumptions/Assumptions.lean",
  "LibsignalBinary/Specifications/SignalPqxdh/Model.lean",
  "Computational/Specifications/Session/StatementSpkModel.lean",
  "Computational/Specifications/Session/StatementSession.lean",
  "Computational/Specifications/Composition/StatementModel.lean",
  "Computational/Specifications/Game/ModelIface.lean",
  "LibsignalBinary/Specifications/SignalSession/Run.lean",
  "LibsignalBinary/Specifications/SignalSession/PqDir.lean",
  "LibsignalBinary/Specifications/SignalSession/PqDirNoMatch.lean",
  "Computational/Specifications/Game/StatementPq.lean",
  "Computational/Specifications/Game/GenericGame.lean",
  "Computational/Specifications/Game/StatementPqOomFlag.lean",
  "Computational/Specifications/Game/StatementPqOomGame.lean",
  "Computational/Specifications/LibsignalCli/Kyber1024Delta.lean",
  "Computational/Specifications/LibsignalCli/StatementPqElf.lean",
  "LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean",
  "LibsignalBinary/Specifications/SignalSession/CliElf.lean"
]

/-- Symbolic headline theorems across `Symbolic/Theorems/` and `Symbolic/Tests/ExternWitness.lean`,
including the two `CliElfLib` binary headlines (requires `lake build CliElfLib`). -/
def symbolicHeadlines : Array Headline := #[
  ⟨"compFs", `Proven.ForwardSecrecy.forward_secrecy,
    `Symbolic.Theorems.ModelSecurity⟩,
  ⟨"compPcs", `Proven.PostCompromiseSecurity.post_compromise_security,
    `Symbolic.Theorems.ModelSecurity⟩,
  ⟨"compAliceInitiatorSecrecy", `Proven.Handshake.alice_initiator_secrecy,
    `Symbolic.Theorems.ModelSecurity⟩,
  ⟨"compBobResponderSecrecy", `Proven.Handshake.bob_responder_secrecy,
    `Symbolic.Theorems.ModelSecurity⟩,
  ⟨"compAuthentication", `Proven.Handshake.authentication,
    `Symbolic.Theorems.ModelSecurity⟩,
  ⟨"compPeerAuthentication", `Proven.Handshake.peer_authentication,
    `Symbolic.Theorems.ModelSecurity⟩,
  ⟨"compHandshakeFs", `Proven.Handshake.handshake_forward_secrecy,
    `Symbolic.Theorems.ModelSecurity⟩,
  ⟨"compKci", `Proven.Handshake.kci_resistance,
    `Symbolic.Theorems.ModelSecurity⟩,
  ⟨"compSessionIndependence", `Proven.Handshake.session_independence,
    `Symbolic.Theorems.ModelSecurity⟩,
  ⟨"compHndl", `Proven.Handshake.hndl_resistance,
    `Symbolic.Theorems.ModelSecurity⟩,
  ⟨"compRefinementPreservationCli",
    `Proven.RefinementPreservation.comp_refinement_preservation_cli,
    `Symbolic.Theorems.RefinementPreservation⟩,
  ⟨"compExternsSatisfiableCli", `Proven.ExternWitness.comp_externsSatisfiable_cli,
    `Symbolic.Tests.ExternWitness⟩,
  ⟨"SymRefines", `Proven.Refinement.comp_refines_cli,
    `Symbolic.Theorems.Refinement⟩,
  ⟨"SymSecure", `Proven.Security.signal_session_secure,
    `Symbolic.Theorems.Security⟩
]

structure Config where
  outDir : FilePath := ".lake/trusted_closure"
  headlines : Array Headline := defaultHeadlines
  statementFiles : Array String := defaultStatementFiles
  commit : String := ""
  /-- Check that every theorem of `Computational/Theorems/` is a headline (rule 5); only for the
  default computational headlines. -/
  checkTheorems : Bool := true
  /-- Compute trust banners with respect to `Symbolic/Theorems/` only. -/
  symbolic : Bool := false
  /-- Constants listed in the closure without unfolding their bodies. -/
  stops : NameSet := {}
  /-- Run self-tests for `pinnedPremiseStops`, Rule 5 proof-tree rejection, and
  `checkPinnedPremiseStop`. -/
  selfTestPinnedStop : Bool := false

def fileToModule (path : String) : Name :=
  let s := if path.endsWith ".lean" then (path.dropEnd 5).toString else path
  (s.splitOn "/").foldl Name.mkStr Name.anonymous

def parseName (s : String) : Name :=
  (s.splitOn ".").foldl Name.mkStr Name.anonymous

/-- Parse the contents of a headlines file (lines `LABEL NAME MODULE`; `#` starts a comment). -/
def parseHeadlines (text : String) : Except String (Array Headline) := do
  let mut hs := #[]
  for line in text.splitOn "\n" do
    let line := ((line.splitOn "#").head!).trimAscii.toString
    if line.isEmpty then continue
    match (line.splitOn " ").filter (!·.isEmpty) with
    | [label, name, module] => hs := hs.push ⟨label, parseName name, parseName module⟩
    | _ => throw s!"bad headline line: {line}"
  return hs

partial def parseArgs (cfg : Config) (customHeadlines customFiles : Bool) :
    List String → Except String Config
  | [] => .ok cfg
  | "--symbolic" :: rest =>
    let hs := if customHeadlines then cfg.headlines else symbolicHeadlines
    let fs := if customFiles then cfg.statementFiles else #[]
    parseArgs { cfg with headlines := hs, statementFiles := fs, checkTheorems := false,
                         symbolic := true }
      customHeadlines customFiles rest
  | "--out-dir" :: d :: rest => parseArgs { cfg with outDir := d } customHeadlines customFiles rest
  | "--commit" :: c :: rest => parseArgs { cfg with commit := c } customHeadlines customFiles rest
  | "--headline" :: h :: rest =>
    match h.splitOn ":" with
    | [label, name, module] =>
      let hs := if customHeadlines then cfg.headlines else #[]
      parseArgs { cfg with headlines := hs.push ⟨label, parseName name, parseName module⟩,
                           checkTheorems := false } true customFiles rest
    | _ => .error s!"--headline expects LABEL:NAME:MODULE, got {h}"
  | "--headlines-file" :: contents :: rest =>
    -- `main` has replaced the path by the file's contents.
    match parseHeadlines contents with
    | .ok hs => parseArgs { cfg with headlines := hs, checkTheorems := false } true customFiles rest
    | .error e => .error e
  | "--stop" :: n :: rest =>
    parseArgs { cfg with stops := cfg.stops.insert (parseName n) } customHeadlines customFiles rest
  | "--statement-file" :: f :: rest =>
    let fs := if customFiles then cfg.statementFiles else #[]
    parseArgs { cfg with statementFiles := fs.push f } customHeadlines true rest
  | "--self-test-pinned-stop" :: rest =>
    parseArgs { cfg with selfTestPinnedStop := true } customHeadlines customFiles rest
  | a :: _ => .error s!"unknown argument {a}"

inductive Tier where
  | statement | repo | engine | generated | foundations
  deriving BEq, Inhabited, Repr

def Tier.key : Tier → String
  | .statement => "T"
  | .repo => "repo"
  | .engine => "arm64-semantics"
  | .generated => "generated"
  | .foundations => "foundations"

def Tier.describe : Tier → String
  | .statement => "statement files (T), read in full"
  | .repo => "other definitions from this repository"
  | .engine => "arm64-semantics: AArch64 semantics and machine model"
  | .generated => "generated image code (rust-obj2lean output)"
  | .foundations => "VCVio, Mathlib, other Lake packages, Lean core"

def allTiers : Array Tier := #[.statement, .repo, .engine, .generated, .foundations]

structure ModInfo where
  pkg : String := "?"
  tier : Tier := .foundations
  /-- Path for reports: repository-relative for this repository and the engine,
  `<package>/<path>` for the other packages, `lean4/<path>` for Lean core. -/
  display : String := "?"
  src? : Option FilePath := none
  fileLines : Nat := 0
  fileCodeLines : Nat := 0
  /-- `codeMask[i]` is `true` iff 1-indexed line `i + 1` has code outside comments/whitespace. -/
  codeMask : Array Bool := #[]
  deriving Inhabited

/-- For each line of `lines`, whether it contains a non-whitespace character outside nested block
comments and `--` line comments. -/
partial def codeLineMask (lines : Array String) : Array Bool := Id.run do
  let rec scanLine (depth : Nat) (hasCode : Bool) : List Char → Nat × Bool
    | [] => (depth, hasCode)
    | '/' :: '-' :: rest => scanLine (depth + 1) hasCode rest
    | '-' :: '/' :: rest =>
      if depth > 0 then scanLine (depth - 1) hasCode rest
      else scanLine 0 true rest
    | '-' :: '-' :: rest =>
      if depth == 0 then (0, hasCode)
      else scanLine depth hasCode ('-' :: rest)
    | c :: rest =>
      let hasCode := if depth == 0 && !c.isWhitespace then true else hasCode
      scanLine depth hasCode rest
  let mut depth := 0
  let mut out := Array.mkEmpty lines.size
  for line in lines do
    let (d, hc) := scanLine depth false line.toList
    depth := d
    out := out.push hc
  return out

def countLines (p : FilePath) : IO Nat := do
  return (← IO.FS.lines p).size

def stripPrefix? (s pre : String) : Option String :=
  if s.startsWith pre then some (s.drop pre.length).toString else none

/-- Repository-relative directories holding proofs, tests, and proof-support definitions rather
than specifications. Unfolding a definition from these directories violates Rule 5. -/
def proofTreePrefixes : Array String :=
  #["Computational/Proofs/", "Computational/Tests/", "LibsignalBinary/Heap/",
    "LibsignalBinary/Proofs/", "Symbolic/Proofs/"]

/-- Subdirectories of `proofTreePrefixes` exempted from `isProofTreeFile`. -/
def proofTreeExceptions : Array String :=
  #[]

def isProofTreeFile (p : String) : Bool :=
  proofTreePrefixes.any (p.startsWith ·) && !proofTreeExceptions.any (p.startsWith ·)

/-- Directory of computational headline theorem modules (`Computational/Theorems/`): tier `T`, but
excluded from `defaultStatementFiles` because they import proofs. -/
def theoremsDir : String := "Computational/Theorems/"

/-- Directory of symbolic headline theorem modules (`Symbolic/Theorems/`): tier `T`, but excluded
from `defaultStatementFiles` because they import proofs. -/
def symbolicTheoremsDir : String := "Symbolic/Theorems/"

/-- Directory of shared binary headline theorem modules (`LibsignalBinary/Theorems/`): tier `T`,
but excluded from `defaultStatementFiles` because they import proofs. -/
def sharedTheoremsDir : String := "LibsignalBinary/Theorems/"

/-- Modules in `Computational/Theorems/` built by the optional `CliElfLib` library rather than
the default target. Rule 5 skips them when unloaded and checks their theorems when loaded. -/
def cliElfTheoremsModules : Array Name :=
  #[`Computational.Theorems.Main]

partial def dirModules (root dir : String) : IO (Array Name) := do
  let rec go (rel : String) (acc : Array Name) : IO (Array Name) := do
    let mut acc := acc
    for e in (← (FilePath.mk (root ++ "/" ++ rel)).readDir).qsort (·.fileName < ·.fileName) do
      if ← e.path.isDir then acc ← go (rel ++ e.fileName ++ "/") acc
      else if e.fileName.endsWith ".lean" then
        acc := acc.push (fileToModule (rel ++ e.fileName))
    return acc
  if ← (FilePath.mk (root ++ "/" ++ dir)).isDir then go dir #[] else return #[]

def theoremsModules (root : String) : IO (Array Name) :=
  dirModules root theoremsDir

/-- Classify `mod` into package, tier, and source file from its `.olean` location (`pkgRoot` is
the resolved `.lake/packages` path). -/
def classifyModule (root pkgRoot sysroot : String) (statementMods : NameSet) (mod : Name) :
    IO ModInfo := do
  let rel := (modToFilePath "" mod "lean").toString
  let rel := (stripPrefix? rel "/").getD rel
  let olean ← try
      some <$> (IO.FS.realPath (← findOLean mod))
    catch _ => pure none
  let some olean := olean | return { display := s!"?/{rel}" }
  let olean := olean.toString
  let pick (cands : List (FilePath × String)) : IO (Option FilePath × String) := do
    for (p, d) in cands do
      if ← p.pathExists then return (some p, d)
    return (none, cands.head?.map (·.2) |>.getD rel)
  let (pkg, cands) : String × List (FilePath × String) :=
    if (stripPrefix? olean (root ++ "/.lake/build/")).isSome then
      ("crypto-verification",
        [(root ++ "/" ++ rel, rel), (root ++ "/.GeneratedLean/" ++ rel, ".GeneratedLean/" ++ rel)])
    else if (stripPrefix? olean (root ++ "/arm64-semantics/")).isSome then
      ("arm64-semantics",
        [(root ++ "/arm64-semantics/" ++ rel, "arm64-semantics/" ++ rel)])
    else if let some r := stripPrefix? olean (pkgRoot ++ "/") then
      let p := (r.splitOn "/").head!
      (p, [(pkgRoot ++ "/" ++ p ++ "/" ++ rel, p ++ "/" ++ rel)])
    else if (stripPrefix? olean (sysroot ++ "/")).isSome then
      ("lean4", [(sysroot ++ "/src/lean/" ++ rel, "lean4/" ++ rel)])
    else ("?", [])
  let (src?, display) ← pick cands
  let tier :=
    if pkg == "crypto-verification" then
      if statementMods.contains mod || display.startsWith theoremsDir ||
          display.startsWith symbolicTheoremsDir ||
          display.startsWith sharedTheoremsDir then .statement
      else if mod.getRoot == `GeneratedLean then .generated
      else .repo
    else if pkg == "arm64-semantics" then
      if (mod.components.map toString).contains "Generated" then .generated else .engine
    else .foundations
  let fileLines ← match src? with
    | some p => countLines p
    | none => pure 0
  return { pkg, tier, display, src?, fileLines }

/-- Classification and outgoing constant references of a single environment constant. -/
structure Node where
  /-- `def`, `abbrev`, `instance`, `projection`, `matcher`, `aux-recursor`, `noConfusion`,
  `structure`, `class`, `inductive`, `ctor`, `recursor`, `opaque`, `axiom`, `quot`,
  `theorem`, `proof-def` (a `Prop`-typed definition), or `missing`. -/
  kind : String
  /-- Whether the closure unfolds this constant (`false` for theorems and proofs). -/
  descend : Bool
  /-- Constants referenced in the type and (when `descend`) body. -/
  refs : Array Name
  /-- Structural hash of the type, mixed with the body hash when `descend` holds. -/
  hash : UInt64 := 0
  deriving Inhabited

def isPropSafe (t : Expr) : MetaM Bool := do
  try isProp t catch _ => pure false

def sortNames (s : NameSet) : Array Name :=
  s.toArray.qsort Name.lt

def nodeOf (c : Name) : MetaM Node := do
  let env ← getEnv
  let some info := env.find? c | return { kind := "missing", descend := false, refs := #[] }
  let refsOf (es : List Expr) (extra : List Name := []) : Array Name :=
    sortNames <| extra.foldl (·.insert ·) <| es.foldl (fun s e => s ++ e.getUsedConstantsAsSet) {}
  let th := info.type.hash
  let proof : Node := { kind := "proof-def", descend := false, refs := #[], hash := th }
  match info with
  | .thmInfo _ => return { kind := "theorem", descend := false, refs := #[], hash := th }
  | .axiomInfo v => return { kind := "axiom", descend := true, refs := refsOf [v.type], hash := th }
  | .quotInfo v => return { kind := "quot", descend := true, refs := refsOf [v.type], hash := th }
  | .opaqueInfo v =>
    if ← isPropSafe v.type then return proof
    return { kind := "opaque", descend := true, refs := refsOf [v.type], hash := th }
  | .defnInfo v =>
    if ← isPropSafe v.type then return proof
    let kind :=
      if isInstanceCore env c then "instance"
      else if (env.getProjectionFnInfo? c).isSome then "projection"
      else if Meta.isMatcherCore env c then "matcher"
      else if isAuxRecursor env c then "aux-recursor"
      else if isNoConfusion env c then "noConfusion"
      else if v.hints.isAbbrev then "abbrev"
      else "def"
    return { kind, descend := true, refs := refsOf [v.type, v.value],
             hash := mixHash th v.value.hash }
  | .inductInfo v =>
    let kind := if isClass env c then "class" else if isStructure env c then "structure"
      else "inductive"
    return { kind, descend := true, refs := refsOf [v.type] (v.ctors ++ v.all), hash := th }
  | .ctorInfo v =>
    return { kind := "ctor", descend := true, refs := refsOf [v.type] [v.induct], hash := th }
  | .recInfo v =>
    return { kind := "recursor", descend := true, refs := refsOf [v.type] v.all, hash := th }

/-- BFS traversal order and discovery-parent map for a headline's closure. -/
structure Closure where
  order : Array Name := #[]
  parent : Std.HashMap Name Name := {}
  deriving Inhabited

def closureOf (cache : IO.Ref (Std.HashMap Name Node)) (h : Name) (stops : NameSet := {}) :
    MetaM Closure := do
  let env ← getEnv
  let some info := env.find? h |
    throwError "unknown headline {h} (if in CliElfLib, run `lake build CliElfLib` first)"
  let node (c : Name) : MetaM Node := do
    if let some n := (← cache.get)[c]? then return n
    let n ← nodeOf c
    cache.modify (·.insert c n)
    return n
  let mut cl : Closure := {}
  let mut queue : Array Name := #[]
  for c in sortNames info.type.getUsedConstantsAsSet do
    unless cl.parent.contains c do
      cl := { cl with parent := cl.parent.insert c h }
      queue := queue.push c
  let mut i := 0
  while i < queue.size do
    let c := queue[i]!
    i := i + 1
    cl := { cl with order := cl.order.push c }
    let n ← node c
    if stops.contains c then continue
    for d in n.refs do
      unless cl.parent.contains d || d == h do
        cl := { cl with parent := cl.parent.insert d c }
        queue := queue.push d
  return cl

/-- Hash-pinned premise stop specification verified by `checkPinnedPremiseStop`. Unused in
production (`pinnedPremiseStops = #[]`), so Rule 5 admits no proof-tree exemptions; retained for
`--self-test-pinned-stop` regression checks. -/
structure PinnedPremiseStop where
  name           : Name
  expectedMod    : Name
  typeHash       : UInt64
  valueHash      : UInt64
  subClosureSize : Nat
  transitiveHash : UInt64
  requiredSeen   : Array Name
  probeConst     : Name
  devId          : String
  deriving Inhabited

/-- Active hash-pinned premise stops (empty: Rule 5 admits zero proof-tree exemptions). -/
def pinnedPremiseStops : Array PinnedPremiseStop := #[]

def modOfConstEnv (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx => env.header.moduleNames.getD idx.toNat Name.anonymous
  | none     => env.mainModule

/-- Normalizes `TrustedClosure.nodeOf` kinds to `CheckPromotedHeadlinesClosure.nodeOf` kinds so
that `computePinnedPremiseDigest` produces the identical sorted Merkle `transitiveHash`. -/
def cphcKindOf (k : String) : String :=
  match k with
  | "instance" | "projection" | "matcher" | "aux-recursor" | "noConfusion" | "abbrev" | "def" => "def"
  | "class" | "structure" | "inductive" => "inductive"
  | other => other

/-- Full transitive definition closure rooted at `rootDef` with no stops. -/
def rawDefClosureOf (cache : IO.Ref (Std.HashMap Name Node)) (rootDef : Name) : MetaM Closure := do
  let env ← getEnv
  let some _ := env.find? rootDef | throwError "unknown definition {rootDef}"
  let node (c : Name) : MetaM Node := do
    if let some n := (← cache.get)[c]? then return n
    let n ← nodeOf c
    cache.modify (·.insert c n)
    return n
  let mut cl : Closure := { parent := ({} : Std.HashMap Name Name).insert rootDef rootDef }
  let mut queue : Array Name := #[rootDef]
  let mut i := 0
  while i < queue.size do
    let c := queue[i]!
    i := i + 1
    cl := { cl with order := cl.order.push c }
    let n ← node c
    for d in n.refs do
      unless cl.parent.contains d do
        cl := { cl with parent := cl.parent.insert d c }
        queue := queue.push d
  return cl

/-- Computes `(subClosureSize, transitiveHash, opaqueHits, seenSet)` with the exact algorithm of
`CheckPromotedHeadlinesClosure.computeCarveOutDigest`. -/
def computePinnedPremiseDigest (cache : IO.Ref (Std.HashMap Name Node)) (targetDef : Name)
    (hashOverrides : Std.HashMap Name UInt64 := {}) :
    MetaM (Nat × UInt64 × Array String × Std.HashSet Name) := do
  let env ← getEnv
  let rawCl ← rawDefClosureOf cache targetDef
  let sortedConsts := rawCl.order.qsort Name.lt
  let mut acc : UInt64 := 14695981039346656037
  let mut opaqueHits : Array String := #[]
  let mut seenSet : Std.HashSet Name := {}
  for c in sortedConsts do
    seenSet := seenSet.insert c
    let n ← do
      if let some cached := (← cache.get)[c]? then pure cached
      else
        let fresh ← nodeOf c
        cache.modify (·.insert c fresh)
        pure fresh
    let modName := modOfConstEnv env c
    let ms := modName.toString
    let isRepoMod :=
      ms.startsWith "LibsignalBinary." || ms.startsWith "Computational." ||
      ms.startsWith "Symbolic." || ms.startsWith "VerifiedLibraries." ||
      ms.startsWith "GeneratedLean."
    if isRepoMod then
      match env.find? c with
      | some (.opaqueInfo _) =>
        opaqueHits := opaqueHits.push s!"forbidden `opaqueInfo` `{c}` in repo/generated module `{ms}`"
      | some (.axiomInfo _) =>
        opaqueHits := opaqueHits.push s!"forbidden `axiomInfo` `{c}` in repo/generated module `{ms}`"
      | _ => pure ()
    let effKind := cphcKindOf n.kind
    let baseHash : UInt64 :=
      if c == `CryptoVerification.libsignalSessionExtractedObjs then
        match env.find? c with
        | some ci => ci.type.hash
        | none => n.hash
      else
        n.hash
    let effHash := hashOverrides.getD c baseHash
    let entryHash :=
      mixHash c.toString.hash
        (mixHash effKind.hash
          (mixHash ms.hash effHash))
    acc := mixHash acc entryHash
  return (sortedConsts.size, acc, opaqueHits, seenSet)

def checkPinnedPremiseStop (env : Environment) (p : PinnedPremiseStop)
    (ci? : Option ConstantInfo) (subSz : Nat) (transHash : UInt64)
    (opaqueHits : Array String) (seenSet : Std.HashSet Name)
    (expectedModOverride : Option Name := none) : Except String Unit := do
  let expMod := expectedModOverride.getD p.expectedMod
  let some ci := ci?
    | throw s!"pinned premise `{p.name}` missing from environment"
  match ci with
  | .defnInfo dv =>
    if (Lean.privateToUserName? p.name).isSome then
      throw s!"pinned premise `{p.name}` must be public"
    if !dv.levelParams.isEmpty then
      throw s!"pinned premise `{p.name}` must have empty levelParams"
    if dv.safety != .safe then
      throw s!"pinned premise `{p.name}` must be safe"
    let actMod := modOfConstEnv env p.name
    if actMod != expMod then
      throw s!"PIN-DEF-MOD mismatch on `{p.name}`: declared in `{actMod}`, expected `{expMod}`"
    if p.typeHash == 0 && p.valueHash == 0 then
      throw s!"unpopulated 0 direct hash pin for `{p.name}`"
    if dv.type.hash != p.typeHash || dv.value.hash != p.valueHash then
      throw s!"direct (type.hash, value.hash) mismatch on `{p.name}`: expected ({p.typeHash}, {p.valueHash}), got ({dv.type.hash}, {dv.value.hash})"
  | .opaqueInfo _ =>
    throw s!"pinned premise `{p.name}` is `opaqueInfo` (opaque wrapping forbidden)"
  | .axiomInfo _ =>
    throw s!"pinned premise `{p.name}` is `axiomInfo` (axiom wrapping forbidden)"
  | _ =>
    throw s!"pinned premise `{p.name}` expected `defnInfo`, got non-def"
  if !opaqueHits.isEmpty then
    throw s!"pinned premise `{p.name}` transitive closure violation: {opaqueHits[0]!}"
  for reqC in p.requiredSeen do
    if !seenSet.contains reqC then
      throw s!"pinned premise `{p.name}` closure missing required SR-(v) constant `{reqC}`"
  if p.subClosureSize == 0 && p.transitiveHash == 0 then
    throw s!"unpopulated 0 transitive hash pin for `{p.name}`"
  if subSz != p.subClosureSize || transHash != p.transitiveHash then
    throw s!"transitive (subClosureSize, transitiveHash) mismatch on `{p.name}`: expected ({p.subClosureSize}, {p.transitiveHash}), got ({subSz}, {transHash})"
  return ()

/-- Coin-only `ReductionDsl.Samplers` declarations permitted in computational headline statement
closures. -/
def allowedHeadlineSamplers : Array Name := #[
  `ReductionDsl.unifSamplers,
  `ReductionDsl.atomicBaseSamplers,
  `ReductionDsl.atomicSamplers,
  `ReductionDsl.pqAtomicSamplers
]

/-- Protocol and game state constants that no sampler in a headline statement closure may reference
in its body or type. -/
def forbiddenSamplerStateRefs : Array Name := #[
  `SignalPqxdh.KeyIndState,
  `CryptoGames.LibsignalSession.GhostState,
  `CryptoVerification.E2E.BHE2EDrvState,
  `CryptoVerification.E2E.ModelDriverBase,
  `CryptoVerification.E2E.ModelDriverState,
  `CryptoVerification.E2E.BHModelInst,
  `CryptoGames.SM.GameState,
  `CryptoVerification.E2E.Costed.E2ESort.ghostSt,
  `CryptoVerification.E2E.Costed.E2ESort.binSt,
  `ReductionDsl.AtomicSort.ghostSt,
  `ReductionDsl.AtomicSort.binSt
]

/-- Pre-costed E2E reduction and sampler declarations banned from headline statement closures. -/
def forbiddenLegacyE2EDecls : Array Name := #[
  `CryptoVerification.E2E.BHE2ESamp,
  `CryptoVerification.E2E.BHE2EOp,
  `CryptoVerification.E2E.bhE2EOps,
  `CryptoVerification.E2E.compositionSamplers,
  `CryptoVerification.E2E.bhE2ESamplers,
  `CryptoVerification.E2E.bhE2ELocalStart,
  `CryptoVerification.E2E.BHE2ESort,
  `CryptoVerification.E2E.bhE2ESig,
  `CryptoVerification.E2E.bhE2ECodec,
  `CryptoVerification.E2E.BHAdapterSort,
  `CryptoVerification.E2E.BHAdapterOp,
  `CryptoVerification.E2E.bhAdapterOps,
  `CryptoVerification.E2E.bhAdapterIface,
  `CryptoVerification.E2E.bhAdapterCodec,
  `CryptoVerification.E2E.keyIndTargetIface,
  `CryptoVerification.E2E.sessionTargetIface,
  `CryptoVerification.E2E.bhKiIface,
  `CryptoVerification.E2E.bhSmTargetIface,
  `CryptoVerification.E2E.E2ECostedReds,
  `CryptoVerification.E2E.E2ECostedBounds
]

/-- Head constant of the return type of `e`, stripping universal binders, `let` bindings, and
metadata. -/
partial def retHeadConst? : Expr → Option Name
  | .forallE _ _ b _ => retHeadConst? b
  | .letE _ _ _ b _ => retHeadConst? b
  | .mdata _ b => retHeadConst? b
  | e => e.getAppFn.constName?

partial def stripLambdas : Expr → Expr
  | .lam _ _ b _ => stripLambdas b
  | .mdata _ b => stripLambdas b
  | e => e

def isStructProjDef (env : Environment) (c : Name) (d : DefinitionVal) : Bool :=
  match stripLambdas d.value with
  | .proj indName _ (.bvar 0) =>
      c.getPrefix == indName &&
      match env.find? indName with
      | some (.inductInfo iv) => iv.ctors.length == 1
      | _ => false
  | _ => false

/-- Structural or compiler-generated `Samplers` constants (constructors, recursors, projections,
and internal auxiliaries) excluded from the user-level sampler allowlist check. -/
def isInternalSamplerAux (env : Environment) (c : Name) (info : ConstantInfo) : Bool :=
  let user := (privateToUserName? c).getD c
  let genAux :=
    env.isProjectionFn c ||
    isAuxRecursor env c ||
    isNoConfusion env c ||
    Meta.isMatcherCore env c ||
    user.components.any fun p =>
      p.isInternalDetail || match p with | .str _ s => s.startsWith "_" | _ => false
  match info with
  | .ctorInfo _ | .recInfo _ | .inductInfo _ | .quotInfo _ => true
  | .defnInfo d => isStructProjDef env c d || genAux
  | _ => genAux

def callsSamplersMk (env : Environment) (c : Name) : ConstantInfo → Bool
  | .defnInfo d =>
      d.value.getUsedConstantsAsSet.contains `ReductionDsl.Samplers.mk ||
      (!isAuxRecursor env c && !isNoConfusion env c &&
        d.type.getUsedConstantsAsSet.contains `ReductionDsl.Samplers.mk)
  | .opaqueInfo o => o.type.getUsedConstantsAsSet.contains `ReductionDsl.Samplers.mk
  | .axiomInfo a => a.type.getUsedConstantsAsSet.contains `ReductionDsl.Samplers.mk
  | _ => false

/-- Forbidden protocol/game state constants reachable from sampler declaration `s` (stopping at
theorem proofs and ambient `ReductionDsl.Sig` carrier/block tables). -/
def samplerStateViolations (env : Environment) (s : Name) : Array Name := Id.run do
  let samplerStops : Array Name := #[
    `CryptoVerification.E2E.Costed.E2ESort,
    `CryptoVerification.E2E.Costed.E2ESort.den,
    `CryptoVerification.E2E.Costed.E2ESort.blocks,
    `ReductionDsl.AtomicSort,
    `ReductionDsl.AtomicSort.den,
    `ReductionDsl.AtomicSort.blocks
  ]
  let mut visited : NameSet := {}
  let mut queue : Array Name := #[s]
  let mut hits : NameSet := {}
  let mut idx := 0
  while idx < queue.size do
    let c := queue[idx]!
    idx := idx + 1
    if visited.contains c then continue
    visited := visited.insert c
    let user := (privateToUserName? c).getD c
    if c != s && (forbiddenSamplerStateRefs.contains c || forbiddenSamplerStateRefs.contains user) then
      hits := hits.insert user
    if c != s && (samplerStops.contains c || samplerStops.contains user) then continue
    let some info := env.find? c | continue
    if c != s && retHeadConst? info.type == some `ReductionDsl.Sig then continue
    let deps : NameSet := match info with
      | .thmInfo _ => {}
      | .defnInfo d => d.type.getUsedConstantsAsSet ++ d.value.getUsedConstantsAsSet
      | .opaqueInfo o => o.type.getUsedConstantsAsSet
      | .axiomInfo a => a.type.getUsedConstantsAsSet
      | .ctorInfo k => k.type.getUsedConstantsAsSet
      | .inductInfo i => i.ctors.foldl (·.insert ·) i.type.getUsedConstantsAsSet
      | .recInfo r => r.type.getUsedConstantsAsSet
      | .quotInfo q => q.type.getUsedConstantsAsSet
    for d in sortNames deps do
      unless visited.contains d do
        queue := queue.push d
  return sortNames hits

/-- Check one headline's statement closure `order` against `forbiddenLegacyE2EDecls`,
`allowedHeadlineSamplers`, and `forbiddenSamplerStateRefs`. -/
def headlineSamplerViolations (env : Environment) (hName : Name) (order : Array Name) :
    Array String := Id.run do
  let mut out : Array String := #[]
  for c in order do
    let user := (privateToUserName? c).getD c
    if forbiddenLegacyE2EDecls.contains c || forbiddenLegacyE2EDecls.contains user then
      out := out.push s!"FORBIDDEN-LEGACY-E2E: {hName} reaches legacy declaration {user}"
    let some info := env.find? c | continue
    let isSamplerDecl :=
      retHeadConst? info.type == some `ReductionDsl.Samplers &&
      !isInternalSamplerAux env c info
    let isSamplersMkCaller := callsSamplersMk env c info
    if isSamplerDecl || isSamplersMkCaller then
      let isAllowed :=
        if isSamplerDecl then
          allowedHeadlineSamplers.contains c || allowedHeadlineSamplers.contains user
        else
          allowedHeadlineSamplers.contains c || allowedHeadlineSamplers.contains user ||
          (isInternalSamplerAux env c info &&
            allowedHeadlineSamplers.any fun a => a.isPrefixOf c || a.isPrefixOf user)
      unless isAllowed do
        out := out.push
          s!"UNLISTED-SAMPLER: {hName} reaches {user}, which is not in allowedHeadlineSamplers"
      let stateHits := samplerStateViolations env c
      unless stateHits.isEmpty do
        let joined := ", ".intercalate (stateHits.toList.map toString)
        out := out.push
          s!"STATEFUL-SAMPLER: {hName} reaches {user}, which references protocol/game state [{joined}]"
  return out

/-- The source lines `[first, last]` of a constant. Auxiliary constants without their own range
(matchers, `proof_n`, ...) get the range of the nearest enclosing declaration of the same
module. -/
partial def lineRange? (c : Name) : MetaM (Option (Nat × Nat)) := do
  let env ← getEnv
  let mod? := env.getModuleIdxFor? c
  let rec go (n : Name) (fuel : Nat) : MetaM (Option (Nat × Nat)) := do
    if fuel == 0 || n.isAnonymous then return none
    if env.contains n && env.getModuleIdxFor? n == mod? then
      if let some r ← findDeclarationRanges? n then
        return some (r.range.pos.line, r.range.endPos.line)
    go n.getPrefix (fuel - 1)
  go c 64

def countCodeInRange (mask : Array Bool) (cs ce : Nat) : Nat := Id.run do
  if mask.isEmpty || ce < cs then return 0
  let mut k := 0
  for l in [cs : ce + 1] do
    if mask.getD (l - 1) false then k := k + 1
  return k

/-- Merge overlapping 1-indexed line intervals into `(blocks, lines, codeLines)`. -/
def unionLines (rs : Array (Nat × Nat)) (mask : Array Bool := #[]) : Nat × Nat × Nat := Id.run do
  let rs := rs.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 > b.2))
  let mut blocks := 0
  let mut lines := 0
  let mut codeLines := 0
  let mut cur : Option (Nat × Nat) := none
  for (s, e) in rs do
    match cur with
    | none => cur := some (s, e)
    | some (cs, ce) =>
      if s ≤ ce then cur := some (cs, max ce e)
      else
        blocks := blocks + 1
        lines := lines + (ce - cs + 1)
        codeLines := codeLines + countCodeInRange mask cs ce
        cur := some (s, e)
  if let some (cs, ce) := cur then
    blocks := blocks + 1
    lines := lines + (ce - cs + 1)
    codeLines := codeLines + countCodeInRange mask cs ce
  return (blocks, lines, codeLines)

def csvField (s : String) : String :=
  if s.any (fun c => c == ',' || c == '"' || c == '\n') then
    "\"" ++ s.replace "\"" "\"\"" ++ "\""
  else s

def csvRow (fs : List String) : String :=
  ",".intercalate (fs.map csvField) ++ "\n"

def pct (a b : Nat) : String :=
  if b == 0 then "-" else
    let x := (a * 1000 + b / 2) / b
    s!"{x / 10}.{x % 10}%"

/-- `1234567` ↦ `"1,234,567"`. -/
partial def fmt (n : Nat) : String :=
  if n < 1000 then toString n
  else
    let r := toString (n % 1000)
    fmt (n / 1000) ++ "," ++ "".pushn '0' (3 - r.length) ++ r

def mdRow (fs : List String) : String :=
  "| " ++ " | ".intercalate fs ++ " |\n"

structure ConstRow where
  name : Name
  kind : String
  descend : Bool
  mod : Name
  range? : Option (Nat × Nat)
  /-- Labels of the headlines whose closure contains it. -/
  headlines : Array String
  /-- The constant that reached it (in the closure of the first headline containing it). -/
  parent : Name
  hash : UInt64 := 0
  deriving Inhabited

/-- Aggregates for one set of constants, per tier or per file. -/
structure Agg where
  files : Nat := 0
  consts : Nat := 0
  /-- Constants the closure looked inside (definitions, types, constructors, ...). -/
  defs : Nat := 0
  /-- Theorems and proofs reached inside definitions (not unfolded). -/
  proofs : Nat := 0
  blocks : Nat := 0
  codeLines : Nat := 0
  lines : Nat := 0
  fileCodeLines : Nat := 0
  fileLines : Nat := 0
  deriving Inhabited

def Agg.add (a b : Agg) : Agg :=
  { files := a.files + b.files, consts := a.consts + b.consts, defs := a.defs + b.defs,
    proofs := a.proofs + b.proofs, blocks := a.blocks + b.blocks,
    codeLines := a.codeLines + b.codeLines, lines := a.lines + b.lines,
    fileCodeLines := a.fileCodeLines + b.fileCodeLines, fileLines := a.fileLines + b.fileLines }

def perFile (rows : Array ConstRow) (mods : Std.HashMap Name ModInfo) :
    Array (Name × Agg) := Id.run do
  let mut byMod : Std.HashMap Name (Array ConstRow) := {}
  for r in rows do
    byMod := byMod.insert r.mod ((byMod.getD r.mod #[]).push r)
  let mut out := #[]
  for (m, rs) in byMod.toArray do
    let mi := mods.getD m default
    -- Count lines only for unfolded definitions (`r.descend`), excluding listed proofs.
    let (blocks, lines, codeLines) :=
      unionLines (rs.filterMap fun r => if r.descend then r.range? else none) mi.codeMask
    let defs := (rs.filter (·.descend)).size
    out := out.push (m, { files := 1, consts := rs.size, defs, proofs := rs.size - defs,
                          blocks, codeLines, lines, fileCodeLines := mi.fileCodeLines,
                          fileLines := mi.fileLines })
  return out.qsort (fun a b => (mods.getD a.1 default).display < (mods.getD b.1 default).display)

def perTier (files : Array (Name × Agg)) (mods : Std.HashMap Name ModInfo) (t : Tier) : Agg :=
  files.foldl (init := {}) fun acc (m, a) =>
    if (mods.getD m default).tier == t then acc.add a else acc

def importClosure (env : Environment) (root : Name) : Array Name := Id.run do
  let names := env.header.moduleNames
  let mut idx : Std.HashMap Name Nat := {}
  for h : i in [:names.size] do
    idx := idx.insert names[i] i
  let mut seen : NameSet := {}
  let mut out := #[]
  let mut stack := #[root]
  while !stack.isEmpty do
    let m := stack.back!
    stack := stack.pop
    if seen.contains m then continue
    seen := seen.insert m
    out := out.push m
    if let some i := idx[m]? then
      for imp in env.header.moduleData[i]!.imports do
        unless seen.contains imp.module do stack := stack.push imp.module
  return out.qsort Name.lt

def isRepoTreeRoot (t : Name) : Bool :=
  t == `Computational || t == `LibsignalBinary || t == `Symbolic

def isRepoSpecMod (m : Name) : Bool :=
  match m.components with
  | t :: `Specifications :: _ :: _ => isRepoTreeRoot t
  | _ => false

def isArm64LegacyMod (m : Name) : Bool :=
  match m.components with
  | `Arm64 :: `Legacy :: _ => true
  | _ => false

def specImportEdgeViolation? (src imp : Name) : Option String :=
  if isRepoTreeRoot imp.getRoot then
    if isRepoSpecMod imp then none
    else some s!"non-Specifications repo module {imp}"
  else if imp.components.contains `Proofs || imp.components.contains `Tests then
    some s!"untrusted external Proofs/Tests module {imp}"
  else if isRepoTreeRoot src.getRoot && isArm64LegacyMod imp then
    some s!"deprecated Arm64.Legacy module {imp}"
  else
    none

/-- Rule 5 `.olean` import-closure check over `edges` (`(module, directImports)`): every
`<Tree>.Specifications.<Sub>...` module (`<Tree>` in `Computational`, `LibsignalBinary`, `Symbolic`)
must keep 100% of its transitive repository imports inside
`{Computational,LibsignalBinary,Symbolic}.Specifications.*`, import no `Arm64.Legacy*` module from
any repository specification module, and transitively reach no external `.Proofs.` or `.Tests.`
module. -/
def checkSpecImportGraph (edges : Array (Name × Array Name)) : Array String := Id.run do
  let mut adj : Std.HashMap Name (Array Name) := {}
  for (m, imps) in edges do
    adj := adj.insert m imps
  let specMods := (edges.filter (fun (m, _) => isRepoSpecMod m)).map (·.1) |>.qsort Name.lt
  let mut clean : NameSet := {}
  let mut errs : Array String := #[]
  for rootMod in specMods do
    if clean.contains rootMod then continue
    let mut seen : NameSet := ({} : NameSet).insert rootMod
    let mut badForRoot : NameSet := {}
    let mut stack : Array (Bool × Name) := #[(false, rootMod)]
    while !stack.isEmpty do
      let (post, u) := stack.back!
      stack := stack.pop
      if post then
        let imps := adj.getD u #[]
        let allClean := imps.all fun imp =>
          (specImportEdgeViolation? u imp).isNone && clean.contains imp
        if allClean then
          clean := clean.insert u
      else
        stack := stack.push (true, u)
        for imp in (adj.getD u #[]).reverse do
          if clean.contains imp then continue
          if let some why := specImportEdgeViolation? u imp then
            unless badForRoot.contains imp do
              badForRoot := badForRoot.insert imp
              let via := if u == rootMod then "" else s!" (via {u})"
              errs := errs.push s!"SPEC-IMPORTS-UNTRUSTED: {rootMod} imports {why}{via}"
            continue
          unless seen.contains imp do
            seen := seen.insert imp
            stack := stack.push (false, imp)
  return errs

def specImportClosureViolations (env : Environment) : Array String := Id.run do
  let names := env.header.moduleNames
  let mut edges : Array (Name × Array Name) := Array.mkEmpty names.size
  for h : i in [:names.size] do
    edges := edges.push (names[i], env.header.moduleData[i]!.imports.map (·.module))
  return checkSpecImportGraph edges

/-- Per-tier file and theorem line counts along a headline's repository import closure. -/
structure PathStats where
  files : Nat := 0
  fileLines : Nat := 0
  theorems : Nat := 0
  theoremLines : Nat := 0
  deriving Inhabited

/-- Writes the report and returns the number of rule 5 violations. -/
def run (cfg : Config) (root pkgRoot sysroot : String) : MetaM Nat := do
  let env ← getEnv
  let statementMods : NameSet := cfg.statementFiles.foldl (·.insert <| fileToModule ·) {}
  let modsRef ← IO.mkRef ({} : Std.HashMap Name ModInfo)
  let modInfo (m : Name) : MetaM ModInfo := do
    if let some mi := (← modsRef.get)[m]? then return mi
    let mi ← classifyModule root pkgRoot sysroot statementMods m
    modsRef.modify (·.insert m mi)
    return mi
  let ensureCodeMask (m : Name) : MetaM Unit := do
    let mi ← modInfo m
    if mi.codeMask.isEmpty then
      if let some p := mi.src? then
        let mask := codeLineMask (← IO.FS.lines p)
        let k := mask.foldl (fun n b => if b then n + 1 else n) 0
        modsRef.modify (·.insert m { mi with codeMask := mask, fileCodeLines := k })
  let modOf (c : Name) : Name :=
    match env.getModuleIdxFor? c with
    | some i => env.header.moduleNames[i.toNat]!
    | none => `«(current)»
  let cache ← IO.mkRef ({} : Std.HashMap Name Node)
  let mut verifiedPinnedStops : Std.HashMap Name PinnedPremiseStop := {}
  let mut effectiveStops : NameSet := cfg.stops
  let mut pinnedStopErrors : Array String := #[]
  for p in pinnedPremiseStops do
    if env.contains p.name then
      let (subSz, transHash, opaqueHits, seenSet) ← computePinnedPremiseDigest cache p.name
      match checkPinnedPremiseStop env p (env.find? p.name) subSz transHash opaqueHits seenSet with
      | .ok () =>
        IO.eprintln s!"[trusted-closure] verified pinned-premise stop `{p.name}` ({p.devId}): direct=({p.typeHash}, {p.valueHash}), transitive=({subSz} consts, hash {transHash}), opaqueHits=0"
        verifiedPinnedStops := verifiedPinnedStops.insert p.name p
        effectiveStops := effectiveStops.insert p.name
        if cfg.selfTestPinnedStop then
          let pValMut := { p with valueHash := p.valueHash ^^^ 1 }
          match checkPinnedPremiseStop env pValMut (env.find? p.name) subSz transHash opaqueHits seenSet with
          | .ok () => pinnedStopErrors := pinnedStopErrors.push s!"SELF-TEST FAIL: mutated valueHash on `{p.name}` passed!"
          | .error msg => IO.eprintln s!"[trusted-closure] self-test Neg 1 (valueHash) rejected: {msg}"
          let probeNode ← do
            if let some cn := (← cache.get)[p.probeConst]? then pure cn else nodeOf p.probeConst
          let (subSzMut, transHashMut, _, _) ← computePinnedPremiseDigest cache p.name
            (hashOverrides := ({} : Std.HashMap Name UInt64).insert p.probeConst (probeNode.hash ^^^ 1))
          match checkPinnedPremiseStop env p (env.find? p.name) subSzMut transHashMut opaqueHits seenSet with
          | .ok () => pinnedStopErrors := pinnedStopErrors.push s!"SELF-TEST FAIL: mutated transitive `{p.probeConst}` on `{p.name}` passed!"
          | .error msg => IO.eprintln s!"[trusted-closure] self-test Neg 2 (transitive `{p.probeConst}`) rejected: {msg}"
          for reqC in p.requiredSeen do
            match checkPinnedPremiseStop env p (env.find? p.name) subSz transHash opaqueHits (seenSet.erase reqC) with
            | .ok () => pinnedStopErrors := pinnedStopErrors.push s!"SELF-TEST FAIL: absent `{reqC}` on `{p.name}` passed!"
            | .error msg => IO.eprintln s!"[trusted-closure] self-test Neg 3 (absent `{reqC}`) rejected: {msg}"
          match checkPinnedPremiseStop env p (env.find? p.name) subSz transHash opaqueHits seenSet
              (expectedModOverride := some `LibsignalBinary.Specifications.SignalSession.CliBinaryPq) with
          | .ok () => pinnedStopErrors := pinnedStopErrors.push s!"SELF-TEST FAIL: wrong module on `{p.name}` passed!"
          | .error msg => IO.eprintln s!"[trusted-closure] self-test Neg 4 (wrong module) rejected: {msg}"
          if pinnedStopErrors.isEmpty then
            IO.eprintln s!"[trusted-closure] self-test-pinned-stop PASS for `{p.name}`"
      | .error msg =>
        IO.eprintln s!"[trusted-closure] pinned-premise verification FAILED for `{p.name}`: {msg}"
        pinnedStopErrors := pinnedStopErrors.push s!"pinned-premise `{p.name}` ({p.devId}) verification failed: {msg}"
    else if cfg.selfTestPinnedStop then
      pinnedStopErrors := pinnedStopErrors.push s!"SELF-TEST FAIL: `{p.name}` not loaded in environment"
  let mut closures : Array (Headline × Closure) := #[]
  for h in cfg.headlines do
    IO.eprintln s!"[trusted-closure] closure of {h.name}"
    closures := closures.push (h, ← closureOf cache h.name effectiveStops)
  -- One row per constant of the union, in the BFS order of the first closure containing it.
  let mut rowIdx : Std.HashMap Name Nat := {}
  let mut rows : Array ConstRow := #[]
  for (h, cl) in closures do
    for c in cl.order do
      match rowIdx[c]? with
      | some i => rows := rows.modify i fun r => { r with headlines := r.headlines.push h.label }
      | none =>
        let n := (← cache.get).getD c default
        let (rowKind, rowDescend, rowHash) :=
          match verifiedPinnedStops[c]? with
          | some p => ("pinned-premise", false, p.transitiveHash)
          | none   => (n.kind, n.descend, n.hash)
        rowIdx := rowIdx.insert c rows.size
        rows := rows.push {
          name := c, kind := rowKind, descend := rowDescend, mod := modOf c, range? := none,
          headlines := #[h.label], parent := cl.parent.getD c .anonymous, hash := rowHash }
  IO.eprintln s!"[trusted-closure] {rows.size} constants; source ranges"
  rows ← rows.mapM fun r => do
    ensureCodeMask r.mod
    return { r with range? := ← lineRange? r.name }
  let rowsOf (label : String) : Array ConstRow := rows.filter (·.headlines.contains label)
  IO.eprintln s!"[trusted-closure] import closures"
  let mut importClosures : Array (Headline × Array Name) := #[]
  for h in cfg.headlines do
    let ms := importClosure env h.module
    for m in ms do discard <| modInfo m
    importClosures := importClosures.push (h, ms)
  -- Make sure every statement file is classified (some may be outside every closure).
  for m in statementMods.toArray do
    if env.header.moduleNames.contains m then ensureCodeMask m
  let allThmDirs := (← theoremsModules root) ++ (← dirModules root symbolicTheoremsDir) ++
    (← dirModules root sharedTheoremsDir)
  let thmMods := allThmDirs.filter env.header.moduleNames.contains
  for m in thmMods do ensureCodeMask m
  -- Transitive module import closure of the statement files.
  let mut stmtImports : NameSet := {}
  for m in statementMods.toArray do
    if env.header.moduleNames.contains m then
      for x in importClosure env m do
        unless stmtImports.contains x do
          stmtImports := stmtImports.insert x
          discard <| modInfo x
  let mods ← modsRef.get
  let mut thmStats : Std.HashMap Name (Nat × Nat) := {}
  for (_, ms) in importClosures do
    for m in ms do
      if thmStats.contains m then continue
      let mi := mods.getD m default
      unless mi.pkg == "crypto-verification" do continue
      let some i := env.header.moduleNames.idxOf? m | continue
      let mut rs : Array (Nat × Nat) := #[]
      let mut n := 0
      for c in env.header.moduleData[i]!.constNames do
        if let some (.thmInfo _) := env.find? c then
          unless c.isInternalDetail do n := n + 1
          if let some r ← lineRange? c then rs := rs.push r
      thmStats := thmStats.insert m (n, (unionLines rs).2.1)
  let mut axioms : Array (Headline × Array Name) := #[]
  for h in cfg.headlines do
    axioms := axioms.push (h, ← collectAxioms h.name)
  IO.FS.createDirAll cfg.outDir
  let mut csv := csvRow ["name", "kind", "unfolded", "tier", "package", "module", "file",
    "line_start", "line_end", "headlines", "reached_from", "hash"]
  for r in rows do
    let mi := mods.getD r.mod default
    let (s, e) := match r.range? with
      | some (s, e) => (toString s, toString e)
      | none => ("", "")
    csv := csv ++ csvRow [toString r.name, r.kind, toString r.descend, mi.tier.key, mi.pkg,
      toString r.mod, mi.display, s, e, " ".intercalate r.headlines.toList, toString r.parent,
      toString r.hash]
  IO.FS.writeFile (cfg.outDir / "trusted_closure.csv") csv
  let mut hcsv := csvRow ["label", "name", "module", "statement_hash", "constants", "axioms"]
  for ((h, cl), (_, axs)) in closures.zip axioms do
    let th := (env.find? h.name).map (·.type.hash) |>.getD 0
    hcsv := hcsv ++ csvRow [h.label, toString h.name, toString h.module, toString th,
      toString cl.order.size, toString axs.size]
  IO.FS.writeFile (cfg.outDir / "headlines.csv") hcsv
  let main := cfg.headlines[0]!
  let mainRows := rowsOf main.label
  let mainFiles := perFile mainRows mods
  let mut fcsv := csvRow ["tier", "package", "file", "module", "constants", "unfolded",
    "proofs_listed", "blocks", "code_lines", "trusted_lines", "file_code_lines", "file_lines",
    "headline"]
  for (h, _) in closures do
    for (m, a) in perFile (rowsOf h.label) mods do
      let mi := mods.getD m default
      fcsv := fcsv ++ csvRow [mi.tier.key, mi.pkg, mi.display, toString m, toString a.consts,
        toString a.defs, toString a.proofs, toString a.blocks, toString a.codeLines,
        toString a.lines, toString a.fileCodeLines, toString a.fileLines, h.label]
  IO.FS.writeFile (cfg.outDir / "trusted_closure_files.csv") fcsv
  let mut icsv := csvRow ["headline", "module", "tier", "package", "file", "file_lines"]
  for (h, ms) in importClosures do
    for m in ms do
      let mi := mods.getD m default
      icsv := icsv ++ csvRow [h.label, toString m, mi.tier.key, mi.pkg, mi.display,
        toString mi.fileLines]
  IO.FS.writeFile (cfg.outDir / "import_closure.csv") icsv
  -- Compute B1–B4 trust banners (`Computational/docs/TRUSTED_BASE.md` §3) relative to headlines
  -- in `theoremsDir` / `symbolicTheoremsDir` (falling back to `main`). Instances count as trusted
  -- when unfolded, but an untrusted instance alone does not downgrade a module from B4/B2 to B3.
  let isBannerThmDisplay (d : String) : Bool :=
    if cfg.symbolic then d.startsWith symbolicTheoremsDir || d.startsWith sharedTheoremsDir
    else d.startsWith theoremsDir || d.startsWith symbolicTheoremsDir ||
      d.startsWith sharedTheoremsDir
  let declModule (h : Headline) : Option Name :=
    env.getModuleIdxFor? h.name |>.map (env.header.moduleNames[·.toNat]!)
  let declared := cfg.headlines.filter fun h =>
    match declModule h with
    | some m => isBannerThmDisplay (mods.getD m default).display
    | none => false
  let bannerHeadlines := if declared.isEmpty then #[main] else declared
  let bannerLabels : Std.HashSet String := bannerHeadlines.foldl (·.insert ·.label) {}
  let bannerRows := rows.filter (·.headlines.any bannerLabels.contains)
  let bannerUnfolded : NameSet := bannerRows.foldl (init := {}) fun s r =>
    if r.descend then s.insert r.name else s
  let bannerImports : NameSet := importClosures.foldl (init := {}) fun s (h, ms) =>
    if bannerLabels.contains h.label then ms.foldl (·.insert ·) s else s
  let auxSuffixes := ["below", "ibelow", "brecOn", "binductionOn", "ctorIdx", "toCtorIdx",
    "ctorElim", "ctorElimType", "noConfusionType", "casesOn", "recOn", "rec"]
  let mut bcsv := csvRow ["file", "module", "banner", "in_import_closure", "definitions",
    "trusted_definitions", "trusted_instances", "theorems", "trusted_names", "untrusted_definitions"]
  let mut bannerCount : Std.HashMap String Nat := {}
  for (m, mi) in mods.toArray.qsort (fun a b => a.2.display < b.2.display) do
    unless mi.pkg == "crypto-verification" && (mi.tier == .statement || mi.tier == .repo) do
      continue
    let some i := env.header.moduleNames.idxOf? m | continue
    let mut defs : Array Name := #[]
    let mut insts : Array Name := #[]
    let mut thms := 0
    let mut anyUnfolded := false
    for c in env.header.moduleData[i]!.constNames do
      if bannerUnfolded.contains c then anyUnfolded := true
      let user := (privateToUserName? c).getD c
      -- Skip compiler-, deriving-, and notation-generated auxiliary constants.
      if user.components.any (·.isInternalDetail) then continue
      if let .str pre last := user then
        if auxSuffixes.contains last then continue
        if isInstanceCore env pre || (privateToUserName? pre).any (isInstanceCore env) then
          continue
        if last == "ofNat" && (env.find? pre matches some (.inductInfo _)) then continue
      if let some info := env.find? c then
        if let some h := info.type.getAppFn.constName? then
          if h == ``Lean.ParserDescr || h == ``Lean.TrailingParserDescr then continue
      let n ← nodeOf c
      match n.kind with
      | "theorem" => thms := thms + 1
      | "def" | "abbrev" | "opaque" | "structure" | "class" | "inductive" | "axiom" =>
        defs := defs.push c
      | "instance" => insts := insts.push c
      | _ => pure ()
    let tDefs := defs.filter bannerUnfolded.contains
    let tInsts := insts.filter bannerUnfolded.contains
    let uDefs := defs.filter (!bannerUnfolded.contains ·)
    let banner :=
      if mi.tier == .statement then "B1"
      else if !anyUnfolded then "B4"
      else if uDefs.isEmpty then "B2"
      else "B3"
    bannerCount := bannerCount.insert banner (bannerCount.getD banner 0 + 1)
    let names := (tDefs ++ tInsts).map toString |>.qsort (· < ·)
    let unames := uDefs.map toString |>.qsort (· < ·)
    bcsv := bcsv ++ csvRow [mi.display, toString m, banner,
      toString (bannerImports.contains m), toString defs.size, toString tDefs.size,
      toString tInsts.size, toString thms, " ".intercalate names.toList,
      " ".intercalate unames.toList]
  IO.FS.writeFile (cfg.outDir / "trusted_banners.csv") bcsv
  -- Rule 5: theorem-dir headlines may not unfold proof-tree definitions, and all default theorems must be headlines.
  let isThmMod (m : Name) : Bool :=
    let d := (mods.getD m default).display
    d.startsWith theoremsDir || d.startsWith symbolicTheoremsDir || d.startsWith sharedTheoremsDir
  let isRule5BadRowWith (mMap : Std.HashMap Name ModInfo) (r : ConstRow) : Bool :=
    let mi := mMap.getD r.mod default
    !verifiedPinnedStops.contains r.name &&
    r.descend && mi.pkg == "crypto-verification" && proofTreePrefixes.any (mi.display.startsWith ·)
  let isRule5BadRow (r : ConstRow) : Bool :=
    isRule5BadRowWith mods r
  if cfg.selfTestPinnedStop then
    if !pinnedPremiseStops.isEmpty || !verifiedPinnedStops.isEmpty then
      pinnedStopErrors := pinnedStopErrors.push
        s!"SELF-TEST FAIL (Empty-Stops): expected 0 pinned premise stops post-S4, got pinned={pinnedPremiseStops.size}, verified={verifiedPinnedStops.size}!"
    let hole2Name : Name :=
      `LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.CliElfHole2Assumption
    let hole2Mod : Name :=
      `LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
    let ghostName : Name :=
      `LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms.H2KGhostArms
    let ghostMod : Name :=
      `LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
    let specProbeName : Name :=
      `CryptoVerification.LibsignalCli.CliPqxdhBinaryCorrectAndSecure
    let specProbeMod : Name :=
      `Computational.Specifications.LibsignalCli.StatementPqElf
    let testMods : Std.HashMap Name ModInfo :=
      (((mods.insert hole2Mod
          { pkg := "crypto-verification", tier := .repo,
            display := "LibsignalBinary/Proofs/SpecLemmas/SignalSession/ElfSlicesPqOomPlacedInst.lean" })
        ).insert ghostMod
          { pkg := "crypto-verification", tier := .repo,
            display := "LibsignalBinary/Proofs/SpecLemmas/SignalSession/ElfSlicesPqOomH2KGhostArms.lean" }
      ).insert specProbeMod
          { pkg := "crypto-verification", tier := .statement,
            display := "Computational/Specifications/LibsignalCli/StatementPqElf.lean" }
    for (pName, pMod) in #[(hole2Name, hole2Mod), (ghostName, ghostMod)] do
      if effectiveStops.contains pName || verifiedPinnedStops.contains pName then
        pinnedStopErrors := pinnedStopErrors.push
          s!"SELF-TEST FAIL (Rule5-Probe): retired proof premise `{pName}` unexpectedly stopped/exempted!"
      let probeRow : ConstRow := {
        name := pName, kind := "def", descend := true, mod := pMod, range? := none,
        headlines := #["Main"], parent := .anonymous, hash := 1 }
      if !isRule5BadRowWith testMods probeRow then
        pinnedStopErrors := pinnedStopErrors.push
          s!"SELF-TEST FAIL (Rule5-Probe): proof-tree premise `{pName}` did NOT fail Rule 5!"
      else
        IO.eprintln s!"[trusted-closure] self-test Rule-5 rejection confirmed for `{pName}`"
    let specRow : ConstRow := {
      name := specProbeName, kind := "def", descend := true, mod := specProbeMod, range? := none,
      headlines := #["Main"], parent := .anonymous, hash := 1 }
    if isRule5BadRowWith testMods specRow then
      pinnedStopErrors := pinnedStopErrors.push
        s!"SELF-TEST FAIL (Rule5-Pos): `Specifications/` row `{specProbeName}` unexpectedly failed Rule 5!"
    let synthName : Name := `_selfTest.synthPremiseStop
    let propSort : Expr := .sort .zero
    let trueConst : Expr := .const ``True []
    let synthDefCi : ConstantInfo := .defnInfo {
      name := synthName, levelParams := [], type := propSort, value := trueConst,
      hints := .abbrev, safety := .safe }
    let synthOpaqueCi : ConstantInfo := .opaqueInfo {
      name := synthName, levelParams := [], type := propSort, value := trueConst, isUnsafe := false }
    let seenOk : Std.HashSet Name := ({} : Std.HashSet Name).insert ``True
    let basePin : PinnedPremiseStop := {
      name := synthName, expectedMod := env.mainModule,
      typeHash := propSort.hash, valueHash := trueConst.hash,
      subClosureSize := 12, transitiveHash := 987654321,
      requiredSeen := #[``True], probeConst := ``True, devId := "SELF-TEST" }
    match checkPinnedPremiseStop env basePin (some synthDefCi) 12 987654321 #[] seenOk with
    | .ok () => pure ()
    | .error msg =>
      pinnedStopErrors := pinnedStopErrors.push
        s!"SELF-TEST FAIL (Verifier-Pos): exact synthetic pin rejected: {msg}"
    let negCases : Array (String × Except String Unit) := #[
      ("zero-direct-hash",
        checkPinnedPremiseStop env { basePin with typeHash := 0, valueHash := 0 }
          (some synthDefCi) 12 987654321 #[] seenOk),
      ("opaque-wrapping",
        checkPinnedPremiseStop env basePin (some synthOpaqueCi) 12 987654321 #[] seenOk),
      ("valueHash-tamper",
        checkPinnedPremiseStop env { basePin with valueHash := trueConst.hash ^^^ 1 }
          (some synthDefCi) 12 987654321 #[] seenOk),
      ("missing-requiredSeen",
        checkPinnedPremiseStop env basePin (some synthDefCi) 12 987654321 #[] {}),
      ("wrong-module",
        checkPinnedPremiseStop env basePin (some synthDefCi) 12 987654321 #[] seenOk
          (expectedModOverride := some `LibsignalBinary.Specifications.SignalSession.CliBinaryPq)),
      ("transitiveHash-tamper",
        checkPinnedPremiseStop env basePin (some synthDefCi) 12 (987654321 ^^^ 1) #[] seenOk)
    ]
    for (lbl, res) in negCases do
      match res with
      | .ok () =>
        pinnedStopErrors := pinnedStopErrors.push
          s!"SELF-TEST FAIL (Verifier-Neg `{lbl}`): tamper case passed!"
      | .error msg =>
        IO.eprintln s!"[trusted-closure] self-test verifier `{lbl}` rejected: {msg}"
    let synthGraph : Array (Name × Array Name) := #[
      (`Computational.Specifications.CleanLeaf, #[`Arm64.Trusted.ISA]),
      (`ProofLib.ObjectLoad, #[`Arm64.Legacy]),
      (`Computational.Specifications.CleanViaEngine,
        #[`Computational.Specifications.CleanLeaf, `ProofLib.ObjectLoad]),
      (`LibsignalBinary.Proofs.Cli.Specifications.UntrustedHelper, #[`LibsignalBinary.Proofs.Leaf]),
      (`Computational.Specifications.MidSpec, #[`LibsignalBinary.Proofs.Leaf]),
      (`Computational.Specifications.ASpecHop, #[`Computational.Specifications.MidSpec]),
      (`LibsignalBinary.Specifications.BadHeap, #[`LibsignalBinary.Heap.SpecBudget]),
      (`Symbolic.Specifications.BadExt, #[`ProofLib.BadBridge]),
      (`ProofLib.BadBridge, #[`VerifiedLibraries.Musl.Proofs.Leak]),
      (`LibsignalBinary.Specifications.BadLegacy, #[`Arm64.Legacy.Object.Loader])
    ]
    let synthErrs := checkSpecImportGraph synthGraph
    if synthErrs.size != 5 ||
        synthErrs.any (·.startsWith "SPEC-IMPORTS-UNTRUSTED: Computational.Specifications.Clean") ||
        synthErrs.any (·.startsWith "SPEC-IMPORTS-UNTRUSTED: LibsignalBinary.Proofs.") then
      pinnedStopErrors := pinnedStopErrors.push
        s!"SELF-TEST FAIL (SpecImportGraph): expected 5 errors (0 on Clean*/Proofs.Cli.Specifications), got {synthErrs.size}: {synthErrs}"
    else
      IO.eprintln s!"[trusted-closure] self-test SpecImportGraph confirmed ({synthErrs.size}/5 violations caught, CleanViaEngine clean)"
    if pinnedStopErrors.isEmpty then
      IO.eprintln "[trusted-closure] self-test-pinned-stop PASS (0 active stops, Rule-5 probes, SpecImportGraph & 6 verifier tamper controls green)"
  let mut r5 : Array String := pinnedStopErrors ++ specImportClosureViolations env
  let mut r5rows : Array (Headline × Nat) := #[]
  for (h, _) in closures do
    let some hm := env.getModuleIdxFor? h.name |>.map (env.header.moduleNames[·.toNat]!) | continue
    unless isThmMod hm do continue
    let bad := (rowsOf h.label).filter isRule5BadRow
    r5rows := r5rows.push (h, bad.size)
    for r in bad do
      r5 := r5.push s!"{h.name} unfolds {r.name}, declared in the proof file \
        {(mods.getD r.mod default).display}"
  unless cfg.symbolic do
    for (h, cl) in closures do
      for v in headlineSamplerViolations env h.name cl.order do
        r5 := r5.push v
  if cfg.checkTheorems then
    let hnames : NameSet := cfg.headlines.foldl (·.insert ·.name) {}
    for m in ← theoremsModules root do
      match env.header.moduleNames.idxOf? m with
      | none =>
        unless cliElfTheoremsModules.contains m do
          r5 := r5.push s!"{m} is not imported by any headline module"
      | some i =>
        for c in env.header.moduleData[i]!.constNames do
          if let some (.thmInfo _) := env.find? c then
            unless c.isInternalDetail || hnames.contains c do
              r5 := r5.push s!"{c} (in {m}) is not a headline"
  -- Reject non-canonical declarations that inline signature constants of a headline predicate.
  let canonicalHeadlineSigs : Array (Array (Name × Name) × Name × Name × Array Name) := #[
    (#[(`Computational.Specifications.LibsignalCli.StatementPqElf,
        `CryptoVerification.E2E.CliPqxdhSecurityFor),
       (`Computational.Specifications.LibsignalCli.StatementPqElfAnyKem,
        `CryptoVerification.E2E.CliPqxdhSecurityForAnyKem)],
     `CryptoVerification.E2E.CliPqxdhSecurityFor,
     `CryptoVerification.E2E.CliAdapterCostBounded,
     #[`CryptoVerification.E2E.bhPrefixFullBoundMixV1With]),
    (#[(`Symbolic.Specifications.Security.Binary,
        `DY.Libsignal.Composed.Security.SignalSessionSecureFor)],
     `DY.Libsignal.Composed.Security.SignalSessionSecureFor,
     `DY.Libsignal.Composed.Refinement.AllSecurityQueriesHoldOnHwTrace,
     #[`DY.Libsignal.Composed.Refinement.Cli.CollisionAfterExplainedPrefix,
       `DY.Libsignal.Composed.Refinement.Cli.NextEventCollides])
  ]
  for (m, mi) in mods.toArray.qsort (fun a b => a.2.display < b.2.display) do
    unless mi.pkg == "crypto-verification" do continue
    let some i := env.header.moduleNames.idxOf? m | continue
    for c in env.header.moduleData[i]!.constNames do
      let user := (privateToUserName? c).getD c
      if user.components.any (·.isInternalDetail) then continue
      if let .str pre last := user then
        if auxSuffixes.contains last then continue
        if isInstanceCore env pre || (privateToUserName? pre).any (isInstanceCore env) then
          continue
        let isEqNum := last.startsWith "eq_" &&
          let rest := (last.drop 3).toString
          !rest.isEmpty && rest.all Char.isDigit
        if env.contains pre &&
            (last == "eq_def" || last == "eq_unfold" || isEqNum || last == "congr_simp") then
          continue
      let some info := env.find? c | continue
      let used : NameSet := match info with
        | .defnInfo d => d.type.getUsedConstantsAsSet ++ d.value.getUsedConstantsAsSet
        | .thmInfo t => t.type.getUsedConstantsAsSet
        | .opaqueInfo o => o.type.getUsedConstantsAsSet
        | .axiomInfo a => a.type.getUsedConstantsAsSet
        | .ctorInfo k => k.type.getUsedConstantsAsSet
        | _ => {}
      for (allowedPairs, canon, sigA, sigBs) in canonicalHeadlineSigs do
        if !allowedPairs.contains (m, user) && used.contains sigA then
          if let some sigB := sigBs.find? used.contains then
            r5 := r5.push s!"RESTATED-HEADLINE: {user} (in {mi.display}) mentions both {sigA} and \
              {sigB}; specialize {canon} instead"
  for v in r5 do IO.eprintln s!"[trusted-closure] rule 5 violation: {v}"
  let mut md := "# Trusted closure of the headline theorems\n\n"
  md := md ++ s!"Generated by `scripts/TrustedClosure.lean`"
  unless cfg.commit.isEmpty do md := md ++ s!" at commit `{cfg.commit}`"
  md := md ++ ". Rerun from the repository root after `lake build`:\n\n"
  let symFlag := if cfg.symbolic then " --symbolic" else ""
  md := md ++ s!"```\nscripts/trusted-closure.sh{symFlag} --out-dir DIR\n```\n\n"
  md := md ++ "**Method.** Start from the statement (the type) of each headline theorem. Collect, "
  md := md ++ "transitively, every constant reachable through the types and bodies of definitions, "
  md := md ++ "abbreviations, instances, inductive types and structures (constructor types "
  md := md ++ "included). Do not look inside proofs: a theorem, or a definition whose type is a "
  md := md ++ "proposition, reached inside a definition is listed (`proofs listed`) but not "
  md := md ++ "unfolded, because its proof does not change what the statement means; opaque "
  md := md ++ "constants contribute their type only. *Lines* are the union of the source ranges "
  md := md ++ "of the unfolded constants (doc comments included); a *block* is a maximal run of "
  md := md ++ "overlapping ranges, roughly one declaration a reader reads. The tiers are:\n\n"
  for t in allTiers do
    md := md ++ s!"- `{t.key}`: {t.describe}\n"
  -- Tier 1 counts every statement file in full, even if no headline imports it.
  let tFileCodeLines := cfg.statementFiles.foldl (init := 0) fun acc f =>
    acc + (mods.getD (fileToModule f) default).fileCodeLines
  let tFileLines := cfg.statementFiles.foldl (init := 0) fun acc f =>
    acc + (mods.getD (fileToModule f) default).fileLines
  let hasCompDeclared := declared.any fun h =>
    match declModule h with
    | some m => (mods.getD m default).display.startsWith theoremsDir
    | none => false
  let hasSymDeclared := declared.any fun h =>
    match declModule h with
    | some m => (mods.getD m default).display.startsWith symbolicTheoremsDir
    | none => false
  let hasSharedDeclared := declared.any fun h =>
    match declModule h with
    | some m => (mods.getD m default).display.startsWith sharedTheoremsDir
    | none => false
  let fmtDirs (hc hs hsh : Bool) (sep : String) : String :=
    let ds := (if hc then [s!"`{theoremsDir}`"] else []) ++
              (if hsh then [s!"`{sharedTheoremsDir}`"] else []) ++
              (if hs then [s!"`{symbolicTheoremsDir}`"] else [])
    if ds.isEmpty then s!"`{theoremsDir}`" else sep.intercalate ds
  let bannerDirTicks :=
    if hasCompDeclared || hasSymDeclared || hasSharedDeclared then
      fmtDirs hasCompDeclared hasSymDeclared hasSharedDeclared ", "
    else if cfg.symbolic then s!"`{symbolicTheoremsDir}`"
    else s!"`{theoremsDir}`"
  let thmDirsTicks (ms : Array Name) : String :=
    let hc := ms.any fun m => (mods.getD m default).display.startsWith theoremsDir
    let hs := ms.any fun m => (mods.getD m default).display.startsWith symbolicTheoremsDir
    let hsh := ms.any fun m => (mods.getD m default).display.startsWith sharedTheoremsDir
    fmtDirs hc hs hsh ", "
  let thmCodeOf (ms : Array Name) : Nat :=
    ms.foldl (init := 0) fun acc m => acc + (mods.getD m default).fileCodeLines
  let thmLinesOf (ms : Array Name) : Nat :=
    ms.foldl (init := 0) fun acc m => acc + (mods.getD m default).fileLines
  let tiersTable (fs : Array (Name × Agg)) (thms : Array Name) : String := Id.run do
    let row (tier what : String) (ts : List Tier) : String :=
      let a := ts.foldl (init := ({} : Agg)) fun acc t => acc.add (perTier fs mods t)
      mdRow [tier, what, fmt a.files, fmt a.defs, fmt a.codeLines, fmt a.lines, fmt a.fileLines]
    let mut s := mdRow ["tier", "what", "files", "definitions", "code lines", "lines (with docs)",
      "lines of those files"]
    s := s ++ mdRow ["---", "---", "---:", "---:", "---:", "---:", "---:"]
    s := s ++ mdRow ["1", "statement files (T), read in full", fmt cfg.statementFiles.size,
      fmt (perTier fs mods .statement).defs, fmt tFileCodeLines, fmt tFileLines, fmt tFileLines]
    unless thms.isEmpty do
      s := s ++ mdRow ["1", s!"theorem files ({thmDirsTicks thms}), read in full", fmt thms.size,
        "", fmt (thmCodeOf thms), fmt (thmLinesOf thms), fmt (thmLinesOf thms)]
    s := s ++ row "2" "definitions from this repository that T uses (games, schemes, bound terms, reductions)" [.repo]
    s := s ++ row "3a" "AArch64 semantics and machine model (`arm64-semantics`)" [.engine]
    s := s ++ row "3b" "compiled image as Lean data (`rust-obj2lean` output)" [.generated]
    s := s ++ row "3c" "Lean core, Mathlib, VCVio, other packages" [.foundations]
    return s
  md := md ++ s!"\n## The three tiers for `{main.name}`\n\n"
  md := md ++ "To trust the result you read tiers 1 and 2 and trust tier 3; you never read a "
  md := md ++ "proof. *Code lines* exclude blank lines and `/- ... -/` / `--` comments; "
  md := md ++ "*lines (with docs)* include the docstrings of the declarations the statement uses.\n\n"
  md := md ++ tiersTable mainFiles (thmMods.filter (· == main.module))
  md := md ++ "\nTier 3 also contains what no line count captures: the Lean kernel and the "
  md := md ++ "`rust-obj2lean` exporter itself. Tier 1 lists all the statement files, also "
  md := md ++ "those with no constant in the closure, and counts their whole length; "
  md := md ++ "*definitions* counts the constants of the closure.\n"
  unless declared.isEmpty do
    md := md ++ s!"\n## The three tiers for the {declared.size} theorems of {bannerDirTicks}\n\n"
    md := md ++ "The same table over the union of the closures of the headlines declared in "
    md := md ++ s!"{bannerDirTicks} ({", ".intercalate (declared.toList.map (s!"`{·.label}`"))}): "
    md := md ++ "what a reader reads to trust all of them. The trust banners "
    md := md ++ "(`trusted_banners.csv`) are computed with respect to this union.\n\n"
    md := md ++ tiersTable (perFile bannerRows mods) thmMods
  md := md ++ "\n## Headlines\n\n"
  md := md ++ mdRow ["headline", "theorem", "constants", "T lines", "repo lines",
    "arm64-semantics lines", "generated lines", "foundations lines", "axioms"]
  md := md ++ mdRow ["---", "---", "---:", "---:", "---:", "---:", "---:", "---:", "---"]
  for ((h, _), (_, axs)) in closures.zip axioms do
    let fs := perFile (rowsOf h.label) mods
    let l (t : Tier) := fmt (perTier fs mods t).lines
    let std := #[``propext, ``Classical.choice, ``Quot.sound]
    let others := axs.filter (!std.contains ·)
    let axDesc := (if std.all axs.contains then "std3" else "not std3") ++
      (if others.isEmpty then "" else s!" + {others.size} other")
    md := md ++ mdRow [h.label, s!"`{h.name}`", fmt (rowsOf h.label).size, l .statement,
      l .repo, l .engine, l .generated, l .foundations, axDesc]
  md := md ++ s!"\n## Main headline `{main.name}`: the three tiers of the trusted base\n\n"
  md := md ++ mdRow ["tier", "files", "blocks", "constants unfolded", "proofs listed",
    "code lines", "trusted lines", "lines of those files"]
  md := md ++ mdRow ["---", "---:", "---:", "---:", "---:", "---:", "---:", "---:"]
  let mut total : Agg := {}
  for t in allTiers do
    let a := perTier mainFiles mods t
    total := total.add a
    md := md ++ mdRow [s!"`{t.key}`", fmt a.files, fmt a.blocks, fmt a.defs, fmt a.proofs,
      fmt a.codeLines, fmt a.lines, fmt a.fileLines]
  md := md ++ mdRow ["total", fmt total.files, fmt total.blocks, fmt total.defs,
    fmt total.proofs, fmt total.codeLines, fmt total.lines, fmt total.fileLines]
  md := md ++ "\n`arm64-semantics` by directory:\n\n"
  md := md ++ mdRow ["directory", "files", "constants unfolded", "trusted lines"]
  md := md ++ mdRow ["---", "---:", "---:", "---:"]
  let engDirs := (mainFiles.filterMap fun (m, _) =>
    let mi := mods.getD m default
    if mi.tier == .engine then some ((mi.display.splitOn "/")[1]?.getD "?") else none
    ).toList.eraseDups
  for d in engDirs do
    let a := mainFiles.foldl (init := ({} : Agg)) fun acc (m, a) =>
      let mi := mods.getD m default
      if mi.tier == .engine && (mi.display.splitOn "/")[1]?.getD "?" == d then acc.add a
      else acc
    md := md ++ mdRow [s!"`{d}/`", fmt a.files, fmt a.defs, fmt a.lines]
  md := md ++ "\nFoundations by package:\n\n"
  md := md ++ mdRow ["package", "files", "constants unfolded", "trusted lines"]
  md := md ++ mdRow ["---", "---:", "---:", "---:"]
  let pkgs := (mainFiles.filterMap fun (m, _) =>
    let mi := mods.getD m default
    if mi.tier == .foundations then some mi.pkg else none).toList.eraseDups
  for p in pkgs do
    let a := mainFiles.foldl (init := ({} : Agg)) fun acc (m, a) =>
      if (mods.getD m default).pkg == p && (mods.getD m default).tier == .foundations then
        acc.add a else acc
    md := md ++ mdRow [p, fmt a.files, fmt a.defs, fmt a.lines]
  md := md ++ "\n## Statement files (T)\n\n"
  md := md ++ mdRow ["file", "file code lines", "file lines", s!"code lines ({main.label})",
    s!"trusted lines ({main.label})", s!"blocks ({main.label})", "in the closure of"]
  md := md ++ mdRow ["---", "---:", "---:", "---:", "---:", "---:", "---"]
  for f in cfg.statementFiles do
    let m := fileToModule f
    let mi := mods.getD m default
    let a := (mainFiles.find? (·.1 == m)).map (·.2) |>.getD {}
    let inCl := closures.filterMap fun (h, _) =>
      if (rowsOf h.label).any (·.mod == m) then some h.label else none
    let inClS := if inCl.isEmpty then
        "none (no constant in any headline's closure; checked by the default build)"
      else ", ".intercalate inCl.toList
    md := md ++ mdRow [s!"`{f}`", fmt mi.fileCodeLines, fmt mi.fileLines, fmt a.codeLines,
      fmt a.lines, fmt a.blocks, inClS]
  md := md ++ s!"\n## Repository definitions on the trusted path of `{main.label}`\n\n"
  md := md ++ "Files of this repository (outside T and the generated code) with constants in the "
  md := md ++ "closure. Definitions in proof, test or untrusted proof-support files "
  md := md ++ "(`Computational/Proofs/`, `Computational/Tests/`, `LibsignalBinary/Heap/`, "
  md := md ++ "`LibsignalBinary/Proofs/`, `Symbolic/Proofs/`) are trusted definitions declared "
  md := md ++ "outside `Specifications/`.\n\n"
  md := md ++ mdRow ["file", "blocks", "constants unfolded", "proofs listed", "code lines",
    "trusted lines", "file lines", "share"]
  md := md ++ mdRow ["---", "---:", "---:", "---:", "---:", "---:", "---:", "---:"]
  for (m, a) in mainFiles do
    let mi := mods.getD m default
    if mi.tier == .repo then
      md := md ++ mdRow [s!"`{mi.display}`", fmt a.blocks, fmt a.defs, fmt a.proofs,
        fmt a.codeLines, fmt a.lines, fmt a.fileLines, pct a.lines a.fileLines]
  let inProofs := mainRows.filter fun r =>
    let mi := mods.getD r.mod default
    mi.tier == .repo && isProofTreeFile mi.display && r.descend
  md := md ++ s!"\n### Trusted definitions declared in proof-tree files ({inProofs.size})\n\n"
  if inProofs.isEmpty then md := md ++ "None.\n"
  for r in inProofs do
    let mi := mods.getD r.mod default
    let loc := match r.range? with
      | some (s, e) => s!"{mi.display}:{s}-{e}"
      | none => mi.display
    md := md ++ s!"- `{r.name}` ({r.kind}), `{loc}`, reached from `{r.parent}`\n"
  for t in [Tier.generated, Tier.engine] do
    md := md ++ s!"\n## `{t.key}` files on the trusted path of `{main.label}`\n\n"
    md := md ++ mdRow ["file", "blocks", "constants unfolded", "trusted lines", "file lines"]
    md := md ++ mdRow ["---", "---:", "---:", "---:", "---:"]
    for (m, a) in mainFiles do
      let mi := mods.getD m default
      if mi.tier == t then
        md := md ++ mdRow [s!"`{mi.display}`", fmt a.blocks, fmt a.defs, fmt a.lines,
          fmt a.fileLines]
  let pinnedRows := rows.filter (·.kind == "pinned-premise")
  unless pinnedRows.isEmpty do
    md := md ++ "\n## Disclosed hash-pinned premises: listed, not unfolded\n\n"
    md := md ++ "Temporary premise definitions listed in `trusted_closure.csv` "
    md := md ++ "(`kind = pinned-premise`, `unfolded = false`), excluded from unfolding and "
    md := md ++ "trust-banner escalation only after verifying their defining module, direct "
    md := md ++ "`(type.hash, value.hash)`, zero repository/generated `opaqueInfo`/`axiomInfo`, "
    md := md ++ "required `SR-(v)` closure constants, and full un-carved transitive Merkle "
    md := md ++ "`(subClosureSize, transitiveHash)` digest:\n\n"
    for r in pinnedRows do
      let mi := mods.getD r.mod default
      let loc := match r.range? with
        | some (s, e) => s!"{mi.display}:{s}-{e}"
        | none => mi.display
      let pInfo := match verifiedPinnedStops[r.name]? with
        | some p => s!" ({p.devId}; direct=({p.typeHash}, {p.valueHash}), un-carved closure={fmt p.subClosureSize} constants, transitiveHash={p.transitiveHash})"
        | none => ""
      md := md ++ s!"- `{r.name}` (`{loc}`), headlines: `{", ".intercalate r.headlines.toList}`{pInfo}\n"
  let listed := mainRows.filter (fun r => !r.descend && r.kind != "pinned-premise")
  md := md ++ s!"\n## Proofs reached inside definitions (`{main.label}`): listed, not unfolded\n\n"
  md := md ++ mdRow ["tier", "theorems", "proof-defs", "missing"]
  md := md ++ mdRow ["---", "---:", "---:", "---:"]
  for t in allTiers do
    let ls := listed.filter fun r => (mods.getD r.mod default).tier == t
    md := md ++ mdRow [s!"`{t.key}`", fmt (ls.filter (·.kind == "theorem")).size,
      fmt (ls.filter (·.kind == "proof-def")).size, fmt (ls.filter (·.kind == "missing")).size]
  let repoListed := listed.filter fun r =>
    let t := (mods.getD r.mod default).tier
    t == .statement || t == .repo
  unless repoListed.isEmpty do
    md := md ++ "\nThose from this repository:\n\n"
    for r in repoListed do
      md := md ++ s!"- `{r.name}` ({r.kind}, `{(mods.getD r.mod default).display}`), "
      md := md ++ s!"used by `{r.parent}`\n"
  md := md ++ "\n## Trusted lines versus all lines on the import path\n\n"
  md := md ++ "All files of this repository that the headline's module imports, transitively "
  md := md ++ "(the headline's own file included). *Theorem lines* are the union of the source "
  md := md ++ "ranges of the theorems declared in those files.\n\n"
  md := md ++ mdRow ["headline", "tier", "files", "file lines", "theorems", "theorem lines",
    "trusted lines", "checked by Lean (lines)"]
  md := md ++ mdRow ["---", "---", "---:", "---:", "---:", "---:", "---:", "---:"]
  for (h, ms) in importClosures do
    let fs := perFile (rowsOf h.label) mods
    for t in [Tier.statement, Tier.repo, Tier.generated] do
      let mut st : PathStats := {}
      for m in ms do
        let mi := mods.getD m default
        unless mi.pkg == "crypto-verification" && mi.tier == t do continue
        let (n, tl) := thmStats.getD m (0, 0)
        st := { files := st.files + 1, fileLines := st.fileLines + mi.fileLines,
                theorems := st.theorems + n, theoremLines := st.theoremLines + tl }
      let trusted := (perTier fs mods t).lines
      md := md ++ mdRow [h.label, s!"`{t.key}`", fmt st.files, fmt st.fileLines,
        fmt st.theorems, fmt st.theoremLines, fmt trusted, fmt (st.fileLines - trusted)]
  let bannerWrt :=
    if declared.isEmpty then s!"`{main.label}`" else s!"the theorems of {bannerDirTicks}"
  md := md ++ s!"\n## Trust banners (`trusted_banners.csv`, with respect to {bannerWrt})\n\n"
  md := md ++ "Repository modules loaded by this run (outside the generated code): `B1` statement "
  md := md ++ "file; `B2` every definition is trusted; `B3` some are; `B4` none.\n\n"
  md := md ++ mdRow ["banner", "modules"] ++ mdRow ["---", "---:"]
  for k in ["B1", "B2", "B3", "B4"] do
    md := md ++ mdRow [k, fmt (bannerCount.getD k 0)]
  md := md ++ "\n## Import closure of the statement files (module level)\n\n"
  md := md ++ "The modules the statement files import, transitively (the statement files "
  md := md ++ "included). This over-approximates the trusted part: it counts whole files, "
  md := md ++ "including proofs that happen to sit in imported files.\n\n"
  md := md ++ mdRow ["tier", "modules", "file lines"]
  md := md ++ mdRow ["---", "---:", "---:"]
  for t in allTiers do
    let ms := stmtImports.toArray.filter fun m => (mods.getD m default).tier == t
    let ls := ms.foldl (init := 0) fun acc m => acc + (mods.getD m default).fileLines
    md := md ++ mdRow [s!"`{t.key}`", fmt ms.size, fmt ls]
  let r5DirTicks :=
    if r5rows.any (fun (h, _) =>
        (declModule h).any fun m => (mods.getD m default).display.startsWith theoremsDir) &&
       r5rows.any (fun (h, _) =>
        (declModule h).any fun m => (mods.getD m default).display.startsWith symbolicTheoremsDir)
    then s!"`{theoremsDir}` and `{symbolicTheoremsDir}`"
    else if cfg.symbolic then s!"`{symbolicTheoremsDir}`"
    else s!"`{theoremsDir}`"
  md := md ++ s!"\n## Theorems of {r5DirTicks} (rule 5)\n\n"
  md := md ++ "The trusted closure of each theorem there may not unfold a definition declared in "
  md := md ++ "a proof, test or untrusted proof-support file (`Computational/Proofs/`, "
  md := md ++ "`Computational/Tests/`, `LibsignalBinary/Heap/`, `LibsignalBinary/Proofs/`, "
  md := md ++ "`Symbolic/Proofs/`, with no exception)"
  if cfg.checkTheorems then md := md ++ s!", and each theorem of `{theoremsDir}` must be a headline"
  md := md ++ ".\n\n"
  md := md ++ mdRow ["headline", "theorem", "proof-file definitions unfolded"]
  md := md ++ mdRow ["---", "---", "---:"]
  for (h, n) in r5rows do
    md := md ++ mdRow [h.label, s!"`{h.name}`", fmt n]
  md := md ++ s!"\nViolations: {r5.size}.\n"
  for v in r5 do md := md ++ s!"- {v}\n"
  md := md ++ "\n## Axioms (`collectAxioms`, the data behind `#print axioms`)\n\n"
  for (h, axs) in axioms do
    let std := #[``propext, ``Classical.choice, ``Quot.sound]
    let others := axs.filter (!std.contains ·)
    let present := std.filter axs.contains
    md := md ++ s!"- `{h.name}`: {", ".intercalate (present.toList.map (s!"`{·}`"))}"
    unless others.isEmpty do
      let shown := (others.toList.take 3).map (s!"`{·}`")
      md := md ++ s!" and {others.size} other axioms (first: {", ".intercalate shown})"
    md := md ++ "\n"
  IO.FS.writeFile (cfg.outDir / "trusted_closure.md") md
  IO.eprintln s!"[trusted-closure] wrote {cfg.outDir}"
  return r5.size

end TrustedClosure

open TrustedClosure in
unsafe def main (args : List String) : IO UInt32 := do
  -- `--headlines-file PATH`: read the file here, so that `parseArgs` stays pure.
  let rec expand : List String → IO (List String)
    | "--headlines-file" :: f :: rest => do
      return "--headlines-file" :: (← IO.FS.readFile f) :: (← expand rest)
    | a :: rest => return a :: (← expand rest)
    | [] => return []
  let args ← expand args
  let cfg ← match parseArgs {} false false args with
    | .ok c => pure c
    | .error e => IO.eprintln e; return 2
  let sysroot ← findSysroot
  initSearchPath sysroot
  enableInitializersExecution
  -- Require every statement file to exist so a stale path cannot silently shrink T.
  for f in cfg.statementFiles do
    unless (← System.FilePath.pathExists f) do
      IO.eprintln s!"[trusted-closure] error: statement file {f} does not exist"
      return 2
  let imports := (cfg.headlines.map (·.module) ++ cfg.statementFiles.map fileToModule).toList
    |>.eraseDups.toArray
  -- `findOLean` returns a candidate path even when the `.olean` was not built (e.g. optional `CliElfLib`), so check `pathExists`.
  let mut present := #[]
  for m in imports do
    if ← (try (do (← findOLean m).pathExists) catch _ => pure false) then
      present := present.push m
    else IO.eprintln s!"[trusted-closure] warning: no .olean for {m}, skipped"
  IO.eprintln s!"[trusted-closure] importing {present.size} modules"
  let env ← importModules (present.map ({ module := · })) {} (trustLevel := 1024)
    (loadExts := true)
  let root := (← IO.FS.realPath ".").toString
  let pkgRoot := (← IO.FS.realPath (root ++ "/.lake/packages")).toString
  let sysroot := (← IO.FS.realPath sysroot).toString
  let ctx : Core.Context := {
    fileName := "<trusted-closure>", fileMap := default, maxHeartbeats := 0, options := {} }
  let (r5, _, _) ← (run cfg root pkgRoot sysroot).toIO ctx { env }
  return if r5 == 0 then 0 else 1
