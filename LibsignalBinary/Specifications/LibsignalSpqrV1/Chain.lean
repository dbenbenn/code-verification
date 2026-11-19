/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
import all Init.Data.Range.Basic

/-!
# SPQR V1: symmetric key chain (`Chain`, `src/chain.rs` and `src/lib.rs`)

**Trusted in part.** The theorems of `Computational/Theorems/` use only part of this file (see
`Computational/docs/TRUSTED_BASE.md`): the rest (the private self-test drivers `run*`, `sendMany`,
`recvAndCheckAll`, `testHkdf` and `testShaCompress`, and the `isPanic` helpers of `ChainError`
and `ChainResult`) is checked by Lean.

Panic-explicit specification of SPQR's symmetric per-epoch, per-direction hash chain (`src/chain.rs`
and `src/lib.rs`): `HkdfFn`, `spqrHkdfWith`, `ChainPanic`, `ChainError`, `ChainResult`, bounded
skipped-key store `KeyHistory` (`get`, `add`, `gc`), directional chain state `ChainEpochDirection`
(`nextKey`, `key`), and multi-epoch `ChainEpoch` / `Chain` (`new`, `addEpoch`, `sendKey`, `recvKey`,
`intoPb`, `fromPb`, `chainFromVersionNegotiation`, `chainFrom`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.HKDF (hkdfExpand)

/-! ## Helper functions and HKDF parameter signature -/

/-- Signature of `kdf::hkdf_to_vec` / `kdf::hkdf_to_slice`: `salt → ikm → info → okm_len → Bytes`. -/
abbrev HkdfFn := Bytes → Bytes → Bytes → Nat → Bytes

/-- HKDF-SHA256 instantiation of `HkdfFn` over compression function `F` (`src/kdf.rs:14–18`). -/
def spqrHkdfWith (F : ShaState → Bytes → ShaState) : HkdfFn :=
  fun salt ikm info okmLen => hkdfExpand F (hmacWith F salt ikm) info okmLen

def asciiBytes (s : String) : Bytes :=
  s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- Lexicographical `<` on byte slices. -/
def bytesLt : Bytes → Bytes → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else bytesLt xs ys

/-- Rust panic sites in `src/chain.rs`. -/
inductive ChainPanic where
  /-- `src/chain.rs:149`: `current_key < params.max_ooo_keys_or_default()` in `KeyHistory::gc`. -/
  | gcKeyUnderflow
  /-- `src/chain.rs:157`: `&self.data[i..i + 4]` out of bounds in `KeyHistory::gc`. -/
  | gcSliceBounds
  /-- `src/chain.rs:191`: `self.data.len() % KEY_SIZE != 0` in `KeyHistory::get`. -/
  | keyHistoryUnaligned
  /-- `src/chain.rs:192`: `at + max_ooo_keys_or_default()` `u32` overflow in `KeyHistory::get`. -/
  | keyHistoryAddOverflow
  /-- `src/chain.rs:230`: `next.len() != 32` in `ChainEpochDirection::next_key_internal`. -/
  | nextKeyBadLen
  /-- `src/chain.rs:231, 266, 271, 280`: `u32` addition overflow on `ctr`. -/
  | ctrOverflow
  /-- `src/chain.rs:361`: `self.current_epoch + 1` `u64` overflow in `Chain::add_epoch`. -/
  | addEpochOverflow
  /-- `src/chain.rs:361`: `epoch_secret.epoch != self.current_epoch + 1` in `Chain::add_epoch`. -/
  | addEpochMismatch
  /-- `src/chain.rs:405, 413, 421`: `self.links[epoch_index]` out of bounds. -/
  | linksOutOfBounds
  deriving DecidableEq, Repr, Inhabited

/-- Error or panic outcome of a fallible chain operation. -/
inductive ChainError where
  | err (e : Error)
  | panic (p : ChainPanic)
  deriving DecidableEq, Repr, Inhabited

namespace ChainError

def isPanic : ChainError → Bool
  | .panic _ => true
  | .err _ => false

end ChainError

abbrev ChainResult (α : Type) := Except ChainError α

namespace ChainResult

def ofPanic (r : Except ChainPanic α) : ChainResult α :=
  match r with
  | .ok v => .ok v
  | .error p => .error (.panic p)

def ofError (r : Except Error α) : ChainResult α :=
  match r with
  | .ok v => .ok v
  | .error e => .error (.err e)

def isPanic (r : ChainResult α) : Bool :=
  match r with
  | .ok _ => false
  | .error e => e.isPanic

end ChainResult

/-! ## `KeyHistory` (`src/chain.rs:91–208`) -/

/-- Skipped-key table storing 36-byte entries `[u8; 4][u8; 32]` (4-byte BE index + 32-byte key). -/
structure KeyHistory where
  data : Bytes := []
  deriving DecidableEq, Repr, Inhabited

namespace KeyHistory

def KEY_SIZE : Nat := 4 + 32

def new : KeyHistory :=
  { data := [] }

def add (self : KeyHistory) (k : BitVec 32 × Bytes) (_params : ChainParamsPB) : KeyHistory :=
  { data := self.data ++ toBEBytes 4 k.1 ++ k.2 }

def clear (_self : KeyHistory) : KeyHistory :=
  { data := [] }

/-- Swap-remove the 36-byte entry at byte offset `myArrayIndex` (`src/chain.rs:175–182`). -/
def remove (self : KeyHistory) (myArrayIndex : Nat) (_params : ChainParamsPB) : KeyHistory :=
  { data :=
      if myArrayIndex + KEY_SIZE < self.data.length then
        let newEnd := self.data.length - KEY_SIZE
        let moved := self.data.drop newEnd
        let prefixBytes := self.data.take myArrayIndex
        let restBytes := (self.data.take newEnd).drop (myArrayIndex + KEY_SIZE)
        (prefixBytes ++ moved ++ restBytes).take newEnd
      else
        self.data.take myArrayIndex }

theorem remove_length_lt (self : KeyHistory) (i : Nat) (params : ChainParamsPB)
    (hi : i < self.data.length) :
    (self.remove i params).data.length < self.data.length := by
  simp only [remove, KEY_SIZE]
  by_cases h : i + (4 + 32) < self.data.length <;> simp [h] <;> omega

/-- Inner `while i < self.data.len()` loop of `KeyHistory::gc` (`src/chain.rs:155–166`). -/
def gcLoop (self : KeyHistory) (trimHorizon : Bytes) (params : ChainParamsPB) (i : Nat) :
    Except ChainPanic KeyHistory :=
  if h : i < self.data.length then
    if self.data.length < i + 4 then
      .error .gcSliceBounds
    else
      let entryKey := (self.data.drop i).take 4
      if bytesLt entryKey trimHorizon then
        have _hlt : (self.remove i params).data.length < self.data.length :=
          remove_length_lt self i params h
        gcLoop (self.remove i params) trimHorizon params i
      else
        gcLoop self trimHorizon params (i + KEY_SIZE)
  else
    .ok self
termination_by self.data.length - i
decreasing_by
  · omega
  · simp only [KEY_SIZE]; omega

/-- `KeyHistory::gc(&mut self, current_key: u32, params: &pqrpb::ChainParams)`
(`src/chain.rs:145–168`).
Panics with `.gcKeyUnderflow` at `src/chain.rs:149` if `self.data.len() >= trim_size * 36` and
`current_key < max_ooo_keys_or_default()`. -/
def gc (self : KeyHistory) (currentKey : BitVec 32) (params : ChainParamsPB) :
    Except ChainPanic KeyHistory :=
  if self.data.length ≥ params.trimSize * KEY_SIZE then
    let maxOoo := params.maxOooKeysOrDefault
    if currentKey < maxOoo then
      .error .gcKeyUnderflow
    else
      let trimHorizon := toBEBytes 4 (currentKey - maxOoo)
      gcLoop self trimHorizon params 0
  else
    .ok self

/-- Inner `for i in (0..self.data.len()).step_by(Self::KEY_SIZE)` loop of `KeyHistory::get`
(`src/chain.rs:197–203`). -/
def getLoop (self : KeyHistory) (atIdx : BitVec 32) (want : Bytes) (params : ChainParamsPB)
    (i : Nat) : ChainResult (KeyHistory × Bytes) :=
  if _h : i < self.data.length then
    if (self.data.drop i).take 4 == want then
      let out := (self.data.drop (i + 4)).take 32
      let self' := self.remove i params
      .ok (self', out)
    else
      getLoop self atIdx want params (i + KEY_SIZE)
  else
    .error (.err (.keyAlreadyRequested atIdx))
termination_by self.data.length - i
decreasing_by
  simp only [KEY_SIZE]; omega

/-- `KeyHistory::get` (`src/chain.rs:185–207`): retrieves and swap-removes the key for `atIdx`,
checking 36-byte alignment, `u32` overflow on `atIdx + maxOoo`, and the trim horizon `currentCtr`. -/
def get (self : KeyHistory) (atIdx currentCtr : BitVec 32) (params : ChainParamsPB) :
    ChainResult (KeyHistory × Bytes) :=
  if self.data.length % KEY_SIZE != 0 then
    .error (.panic .keyHistoryUnaligned)
  else
    let maxOoo := params.maxOooKeysOrDefault
    if atIdx.toNat + maxOoo.toNat ≥ 2 ^ 32 then
      .error (.panic .keyHistoryAddOverflow)
    else if atIdx + maxOoo < currentCtr then
      .error (.err (.keyTrimmed atIdx))
    else
      let want := toBEBytes 4 atIdx
      getLoop self atIdx want params 0

end KeyHistory

/-! ## `ChainEpochDirection` (`src/chain.rs:99–104, 210–321`) -/

/-- Directional chain state within one epoch (`src/chain.rs:99–104`). -/
structure ChainEpochDirection where
  ctr : BitVec 32
  next : Bytes
  prev : KeyHistory
  deriving DecidableEq, Repr, Inhabited

def chainNextInfo : Bytes :=
  asciiBytes "Signal PQ Ratchet V1 Chain Next"

namespace ChainEpochDirection

def new (k : Bytes) : ChainEpochDirection :=
  { ctr := 0#32
    prev := KeyHistory.new
    next := k }

/-- `ChainEpochDirection::next_key_internal` (`src/chain.rs:229–246`): advances `(next, ctr)` via
64-byte HKDF (`next' = out[..32]`, `key = out[32..64]`), panicking if `next.length != 32` or
`ctr == u32::MAX`. -/
def nextKeyInternal (hkdf : HkdfFn) (next : Bytes) (ctr : BitVec 32) :
    Except ChainPanic (Bytes × BitVec 32 × (BitVec 32 × Bytes)) :=
  if next.length != 32 then
    .error .nextKeyBadLen
  else if ctr == 0xffffffff#32 then
    .error .ctrOverflow
  else
    let ctr' := ctr + 1#32
    let salt := List.replicate 32 0#8
    let info := toBEBytes 4 ctr' ++ chainNextInfo
    let genr8r := hkdf salt next info 64
    let next' := genr8r.take 32
    let key := (genr8r.drop 32).take 32
    .ok (next', ctr', (ctr', key))

theorem nextKeyInternal_ctr (hkdf : HkdfFn) (next next' : Bytes) (ctr ctr' : BitVec 32)
    (k : BitVec 32 × Bytes)
    (h : nextKeyInternal hkdf next ctr = .ok (next', ctr', k)) :
    ctr'.toNat = ctr.toNat + 1 := by
  unfold nextKeyInternal at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  rename_i hctr
  have hne : ctr ≠ 0xffffffff#32 := by simpa using hctr
  have hlt : ctr.toNat < 4294967295 := by
    have := ctr.isLt
    have : ctr.toNat ≠ 4294967295 := fun heq => hne (BitVec.eq_of_toNat_eq heq)
    omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `ChainEpochDirection::next_key(&mut self) -> (u32, Vec<u8>)` (`src/chain.rs:222–225`). -/
def nextKey (hkdf : HkdfFn) (self : ChainEpochDirection) :
    Except ChainPanic (ChainEpochDirection × (BitVec 32 × Bytes)) := do
  let (next', ctr', out) ← nextKeyInternal hkdf self.next self.ctr
  return ({ self with next := next', ctr := ctr' }, out)

/-- Inner `while at > self.ctr + 1` loop of `ChainEpochDirection::key` (`src/chain.rs:271–287`). -/
def keyAdvanceLoop (hkdf : HkdfFn) (self : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) : ChainResult ChainEpochDirection :=
  if _h : self.ctr.toNat + 1 < atIdx.toNat then
    match hnk : nextKeyInternal hkdf self.next self.ctr with
    | .error p => .error (.panic p)
    | .ok (next', ctr', k) =>
      have _hctr' : ctr'.toNat = self.ctr.toNat + 1 :=
        nextKeyInternal_ctr hkdf self.next next' self.ctr ctr' k hnk
      let maxOoo := params.maxOooKeysOrDefault
      if ctr'.toNat + maxOoo.toNat ≥ 2 ^ 32 then
        .error (.panic .ctrOverflow)
      else
        let prev' :=
          if ctr' + maxOoo ≥ atIdx then
            self.prev.add k params
          else
            self.prev
        keyAdvanceLoop hkdf { ctr := ctr', next := next', prev := prev' } atIdx params
  else if self.ctr == 0xffffffff#32 then
    -- Unreachable when `self.ctr < atIdx`, included for completeness of `self.ctr + 1` check.
    .error (.panic .ctrOverflow)
  else
    .ok self
termination_by atIdx.toNat - self.ctr.toNat
decreasing_by
  omega

/-- `ChainEpochDirection::key(&mut self, at: u32, params: &pqrpb::ChainParams) -> Result<Vec<u8>, Error>`
(`src/chain.rs:248–297`). -/
def key (hkdf : HkdfFn) (self : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) : ChainResult (ChainEpochDirection × Bytes) :=
  if atIdx < self.ctr then do
    let (prev', out) ← self.prev.get atIdx self.ctr params
    return ({ self with prev := prev' }, out)
  else if atIdx == self.ctr then
    .error (.err (.keyAlreadyRequested atIdx))
  else
    if atIdx - self.ctr > params.maxJumpOrDefault then
      .error (.err (.keyJump self.ctr atIdx))
    else
      let maxOoo := params.maxOooKeysOrDefault
      if self.ctr.toNat + maxOoo.toNat ≥ 2 ^ 32 then
        .error (.panic .ctrOverflow)
      else do
        let self0 :=
          if atIdx > self.ctr + maxOoo then
            { self with prev := self.prev.clear }
          else
            self
        let self1 ← keyAdvanceLoop hkdf self0 atIdx params
        let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr params)
        let self2 := { self1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ←
          ChainResult.ofPanic (nextKeyInternal hkdf self2.next self2.ctr)
        return ({ self2 with next := next', ctr := ctr' }, outKey)

def intoPb (self : ChainEpochDirection) : EpochDirectionPB :=
  { ctr := self.ctr
    next := self.next
    prev := self.prev.data }

/-- `ChainEpochDirection::from_pb` (`src/chain.rs:307–316`), rejecting non-empty `next` of length
`≠ 32`. -/
def fromPb (pb : EpochDirectionPB) : Except Error ChainEpochDirection :=
  if !pb.next.isEmpty && pb.next.length != 32 then
    .error .stateDecode
  else
    .ok { ctr := pb.ctr, next := pb.next, prev := { data := pb.prev } }

def clearNext (self : ChainEpochDirection) : ChainEpochDirection :=
  { self with next := [] }

end ChainEpochDirection

/-! ## `ChainEpoch` and `Chain` (`src/chain.rs:106–125, 323–463`) -/

/-- Send and receive chains of a single epoch (`src/chain.rs:107–110`). -/
structure ChainEpoch where
  send : ChainEpochDirection
  recv : ChainEpochDirection
  deriving DecidableEq, Repr, Inhabited

/-- Full symmetric chain state (`src/chain.rs:113–121`). -/
structure Chain where
  dir : Direction
  currentEpoch : Epoch
  sendEpoch : Epoch
  links : List ChainEpoch
  nextRoot : Bytes
  params : ChainParamsPB
  deriving DecidableEq, Repr, Inhabited

def EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH : Nat := 1

/-- `"Signal PQ Ratchet V1 Chain  Start"` (`src/chain.rs:338`; two spaces before `Start`). -/
def chainStartInfo : Bytes :=
  asciiBytes "Signal PQ Ratchet V1 Chain  Start"

def chainAddEpochInfo : Bytes :=
  asciiBytes "Signal PQ Ratchet V1 Chain Add Epoch"

namespace Chain

def cedForDirection (genr8r : Bytes) (dir : Direction) : ChainEpochDirection :=
  ChainEpochDirection.new <|
    match dir with
    | .a2b => (genr8r.drop 32).take 32
    | .b2a => (genr8r.drop 64).take 32

/-- `Chain::new` (`src/chain.rs:333–354`). -/
def new (hkdf : HkdfFn) (initialKey : Bytes) (dir : Direction) (params : ChainParamsPB) :
    Except Error Chain :=
  let salt := List.replicate 32 0#8
  let genr8r := hkdf salt initialKey chainStartInfo 96
  let epoch0 : ChainEpoch :=
    { send := cedForDirection genr8r dir
      recv := cedForDirection genr8r dir.switch }
  .ok
    { dir := dir
      currentEpoch := 0#64
      sendEpoch := 0#64
      links := [epoch0]
      nextRoot := genr8r.take 32
      params := params }

/-- `Chain::add_epoch(&mut self, epoch_secret: EpochSecret)` (`src/chain.rs:356–375`).
* Panics with `.addEpochOverflow` if `self.current_epoch == u64::MAX` (`src/chain.rs:361`).
* Panics with `.addEpochMismatch` if `epoch_secret.epoch != self.current_epoch + 1`
  (`src/chain.rs:361`). -/
def addEpoch (hkdf : HkdfFn) (self : Chain) (epochSecret : EpochSecret) :
    Except ChainPanic Chain :=
  if self.currentEpoch == 0xffffffffffffffff#64 then
    .error .addEpochOverflow
  else if epochSecret.epoch != self.currentEpoch + 1#64 then
    .error .addEpochMismatch
  else
    let genr8r := hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96
    let newLink : ChainEpoch :=
      { send := cedForDirection genr8r self.dir
        recv := cedForDirection genr8r self.dir.switch }
    .ok
      { self with
        currentEpoch := epochSecret.epoch
        nextRoot := genr8r.take 32
        links := self.links ++ [newLink] }

/-- `Chain::epoch_idx(&mut self, epoch: Epoch) -> Result<usize, Error>` (`src/chain.rs:378–388`). -/
def epochIdx (self : Chain) (epoch : Epoch) : Except Error Nat :=
  if epoch > self.currentEpoch then
    .error (.epochOutOfRange epoch)
  else
    let back := (self.currentEpoch - epoch).toNat
    let linksLen := self.links.length
    if back ≥ linksLen then
      .error (.epochOutOfRange epoch)
    else
      .ok (linksLen - 1 - back)

/-- Clear `send.next` on the first `n` elements of `links` (`for i in 0..epoch_index` in
`Chain::send_key`, `src/chain.rs:403–406`). -/
def clearSendNextPrefix : Nat → List ChainEpoch → List ChainEpoch
  | 0, xs => xs
  | _ + 1, [] => []
  | n + 1, x :: xs => { x with send := x.send.clearNext } :: clearSendNextPrefix n xs

/-- Derive the next sending key `(index, key)` in `epoch`, dropping older epochs when the send epoch
advances. `Chain::send_key(&mut self, epoch: Epoch) -> Result<(u32, Vec<u8>), Error>`
(`src/chain.rs:390–414`). -/
def sendKey (hkdf : HkdfFn) (self : Chain) (epoch : Epoch) :
    ChainResult (Chain × (BitVec 32 × Bytes)) :=
  if epoch < self.sendEpoch then
    .error (.err (.sendKeyEpochDecreased self.sendEpoch epoch))
  else do
    let epochIndex0 ← ChainResult.ofError (self.epochIdx epoch)
    let (self1, epochIndex) :=
      if self.sendEpoch != epoch then
        let dropCount := epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
        let epochIndex' := epochIndex0 - dropCount
        let links1 := self.links.drop dropCount
        let links2 := clearSendNextPrefix epochIndex' links1
        ({ self with sendEpoch := epoch, links := links2 }, epochIndex')
      else
        (self, epochIndex0)
    match self1.links[epochIndex]? with
    | none => .error (.panic .linksOutOfBounds)
    | some link => do
      let (send', out) ← ChainResult.ofPanic (link.send.nextKey hkdf)
      let links' := self1.links.set epochIndex { link with send := send' }
      return ({ self1 with links := links' }, out)

/-- Derive the receiving key for message `index` of `epoch`; epoch 0, index 0 yields the empty key.
`Chain::recv_key(&mut self, epoch: Epoch, index: u32) -> Result<Vec<u8>, Error>`
(`src/chain.rs:416–422`). -/
def recvKey (hkdf : HkdfFn) (self : Chain) (epoch : Epoch) (index : BitVec 32) :
    ChainResult (Chain × Bytes) :=
  if epoch == 0#64 && index == 0#32 then
    .ok (self, [])
  else do
    let epochIndex ← ChainResult.ofError (self.epochIdx epoch)
    match self.links[epochIndex]? with
    | none => .error (.panic .linksOutOfBounds)
    | some link => do
      let (recv', out) ← link.recv.key hkdf index self.params
      let links' := self.links.set epochIndex { link with recv := recv' }
      return ({ self with links := links' }, out)

def intoPb (self : Chain) : ChainPB :=
  { direction := self.dir.toI32
    currentEpoch := self.currentEpoch
    sendEpoch := self.sendEpoch
    links := self.links.map fun link =>
      { send := some link.send.intoPb
        recv := some link.recv.intoPb }
    nextRoot := self.nextRoot
    params := some self.params }

def linksFromPb : List ChainEpochPB → Except Error (List ChainEpoch)
  | [] => .ok []
  | link :: rest => do
    let sendPb ←
      match link.send with
      | some s => .ok s
      | none => .error .stateDecode
    let send ← ChainEpochDirection.fromPb sendPb
    let recvPb ←
      match link.recv with
      | some r => .ok r
      | none => .error .stateDecode
    let recv ← ChainEpochDirection.fromPb recvPb
    let tail ← linksFromPb rest
    return { send := send, recv := recv } :: tail

/-- `Chain::from_pb` (`src/chain.rs:444–462`). -/
def fromPb (pb : ChainPB) : Except Error Chain := do
  let dir ←
    match Direction.fromI32? pb.direction with
    | some d => .ok d
    | none => .error .stateDecode
  let links ← linksFromPb pb.links
  let params ←
    match pb.params with
    | some p => .ok p
    | none => .error .stateDecode
  return {
    dir := dir
    currentEpoch := pb.currentEpoch
    sendEpoch := pb.sendEpoch
    nextRoot := pb.nextRoot
    links := links
    params := params
  }

end Chain

/-! ## `chain_from_version_negotiation` and `chain_from` (`src/lib.rs:332–353`) -/

/-- `chain_from_version_negotiation` (`src/lib.rs:332–340`). -/
def chainFromVersionNegotiation (hkdf : HkdfFn) (vn : VersionNegotiationPB) :
    Except Error Chain := do
  let dir ←
    match Direction.fromI32? vn.direction with
    | some d => .ok d
    | none => .error .stateDecode
  let params ←
    match vn.chainParams with
    | some p => .ok p
    | none => .error .chainNotAvailable
  Chain.new hkdf vn.authKey dir params

/-- `chain_from` (`src/lib.rs:342–353`). -/
def chainFrom (hkdf : HkdfFn) (pb : Option ChainPB) (vn : Option VersionNegotiationPB) :
    Except Error Chain :=
  match pb with
  | some pb => Chain.fromPb pb
  | none =>
    match vn with
    | none => .error .chainNotAvailable
    | some vn => chainFromVersionNegotiation hkdf vn

/-! ## Executable guards (`src/chain.rs:465–728`) -/

section Guards

end Guards

end CryptoVerification.LibsignalSpqrV1
