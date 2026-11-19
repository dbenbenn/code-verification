/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Concrete.SessionRecord

/-!
# Decidability of `EligibleForSessionPromotion`

Provides `instDecidableEligibleForSessionPromotion : Decidable (EligibleForSessionPromotion rec b)`
via a canonical protobuf wire-type-0 / wire-type-2 parser (`DecodeRecord.*`, `decodeRecordBytes?`).

This module only provides a `Decidable` instance, which is correct by its type
(`Subsingleton (Decidable p)`), so its body need not be read when auditing the trusted
specification.
-/

@[expose] public section

namespace DY.Libsignal.Rust

open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (PbValue encodeField paddedVarint readVarint)
open DY.Libsignal.PQXDH.Refinement (parsePreKeyWire)

namespace DecodeRecord

/-- Normalizes each pending pre-key pair `p` of `rec.current` to `(p.1 ++ p.2, [])`. -/
def normPending (rec : RecordRec) : RecordRec :=
  { rec with current :=
      { rec.current with
        pendingPreKey := rec.current.pendingPreKey.map fun p => (p.1 ++ p.2, [])
        pendingKyberPreKey := rec.current.pendingKyberPreKey.map fun p => (p.1 ++ p.2, []) } }

/-- Parses canonical varint (`wt = 0`) and length-delimited (`wt = 2`) protobuf fields with fuel. -/
def parsePbFields : Nat → HwBytes → Option (List (Nat × PbValue))
  | 0, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bs =>
    if bs = [] then some []
    else
      match readVarint bs with
      | none => none
      | some (key, rest) =>
        match key % 8 with
        | 0 =>
          match readVarint rest with
          | none => none
          | some (n, rest') => (parsePbFields fuel rest').map ((key / 8, .varint n) :: ·)
        | 2 =>
          match readVarint rest with
          | none => none
          | some (len, rest') =>
            if len ≤ rest'.length then
              (parsePbFields fuel (rest'.drop len)).map ((key / 8, .bytes (rest'.take len)) :: ·)
            else none
        | _ => none

/-- Decodes `bs` into `(tag, value)` pairs, returning `[]` on malformed input. -/
def decodePbFields (bs : HwBytes) : List (Nat × PbValue) :=
  (parsePbFields bs.length bs).getD []

/-- Extracts a single proto3 `uint32` varint field at `tag` (defaulting to `0`). -/
def decodeU32Field (tag : Nat) (fs : List (Nat × PbValue)) : BitVec 32 :=
  match fs.filter (fun p => p.1 == tag) with
  | [(_, .varint n)] => BitVec.ofNat 32 n
  | _ => 0

/-- Extracts a single proto3 `bytes` field at `tag` (defaulting to `[]`). -/
def decodeBytesField (tag : Nat) (fs : List (Nat × PbValue)) : HwBytes :=
  match fs.filter (fun p => p.1 == tag) with
  | [(_, .bytes b)] => b
  | _ => []

/-- Extracts an optional length-delimited submessage payload at `tag`. -/
def decodeMsgOptField (tag : Nat) (fs : List (Nat × PbValue)) : Option HwBytes :=
  match fs.filter (fun p => p.1 == tag) with
  | [(_, .bytes b)] => some b
  | _ => none

/-- Extracts all repeated length-delimited payloads at `tag` in wire order. -/
def decodeMsgListField (tag : Nat) (fs : List (Nat × PbValue)) : List HwBytes :=
  (fs.filter (fun p => p.1 == tag)).filterMap fun
    | (_, .bytes b) => some b
    | _ => none

/-- Reconstructs a `ChainRec` from its raw `chainBytes` payload. -/
def decodeChainBytes (bs : HwBytes) : ChainRec :=
  let fs := decodePbFields bs
  { senderRatchetKey := decodeBytesField 1 fs
    senderRatchetKeyPrivate := decodeBytesField 2 fs
    chainKey := (decodeMsgOptField 3 fs).map fun b =>
      let kf := decodePbFields b
      (decodeU32Field 1 kf, decodeBytesField 2 kf)
    messageKeys := (decodeMsgListField 4 fs).map fun b =>
      let mf := decodePbFields b
      (decodeU32Field 1 mf, decodeBytesField 5 mf) }

/-- Reconstructs a `SessionRec` (with normalized pending pre-key pairs) from its payload bytes. -/
def decodeSessionBytes (bs : HwBytes) : SessionRec :=
  let fs := decodePbFields bs
  { sessionVersion := decodeU32Field 1 fs
    localIdentityPublic := decodeBytesField 2 fs
    remoteIdentityPublic := decodeBytesField 3 fs
    rootKey := decodeBytesField 4 fs
    previousCounter := decodeU32Field 5 fs
    senderChain := (decodeMsgOptField 6 fs).map decodeChainBytes
    receiverChains := (decodeMsgListField 7 fs).map decodeChainBytes
    pendingPreKey := (decodeMsgOptField 9 fs).map (·, [])
    pendingKyberPreKey := (decodeMsgOptField 14 fs).map (·, [])
    remoteRegistrationId := decodeU32Field 10 fs
    localRegistrationId := decodeU32Field 11 fs
    aliceBaseKey := decodeBytesField 13 fs
    pqRatchetState := decodeBytesField 15 fs }

/-- Unchecked candidate `RecordRec` decoded from raw record bytes `b`. -/
def decodeRecordRaw (b : HwBytes) : RecordRec :=
  let fs := decodePbFields b
  { current := decodeSessionBytes ((decodeMsgOptField 1 fs).getD [])
    previous := decodeMsgListField 2 fs }

end DecodeRecord

/-- Constructive canonical protobuf decoder for `recordBytes` (normalized on pending pre-key pairs
via `DecodeRecord.normPending`), guarded by re-encoding so `decodeRecordBytes? b = some rr` implies
`b = recordBytes rr`. -/
def decodeRecordBytes? (b : HwBytes) : Option RecordRec :=
  if b = recordBytes (DecodeRecord.decodeRecordRaw b) then
    some (DecodeRecord.decodeRecordRaw b)
  else none

namespace DecodeRecord

private def pbFields (l : List (Nat × PbValue)) : HwBytes :=
  l.flatMap fun p => encodeField p.1 0 0 p.2

private def PbOk (p : Nat × PbValue) : Prop :=
  match p.2 with
  | .varint _ | .bytes _ => True
  | .unknown _ _ => False

private theorem paddedVarint0_length_pos (n : Nat) : 0 < (paddedVarint n 0).length := by
  rw [paddedVarint]; split <;> simp

private theorem readVarint_paddedVarint0 (n : Nat) (rest : HwBytes) :
    readVarint (paddedVarint n 0 ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [paddedVarint]
    by_cases hn : n < 128
    · have h8 : (BitVec.ofNat 8 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
      simp [hn, readVarint, h8]
    · have h8 : (BitVec.ofNat 8 (n % 128 + 128)).toNat = n % 128 + 128 := by
        rw [BitVec.toNat_ofNat]; omega
      simp only [hn, and_true, ↓reduceIte, List.cons_append, readVarint, h8,
        show ¬ n % 128 + 128 < 128 by omega, ih (n / 128) (by omega), Option.map_some,
        Option.some.injEq, Prod.mk.injEq]
      omega

private theorem parsePbFields_pbFields :
    ∀ (l : List (Nat × PbValue)) (fuel : Nat),
      (∀ x ∈ l, PbOk x) → (pbFields l).length ≤ fuel →
      parsePbFields fuel (pbFields l) = some l
  | [], 0, _, _ => rfl
  | [], _ + 1, _, _ => rfl
  | (t, v) :: rest, fuel, hok, hlen => by
    have hv := hok (t, v) (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, PbOk x := fun x hx => hok x (List.mem_cons_of_mem _ hx)
    change (encodeField t 0 0 v ++ pbFields rest).length ≤ fuel at hlen
    cases v with
    | unknown _ _ => exact False.elim hv
    | varint n =>
      have hpos : 0 < (encodeField t 0 0 (.varint n)).length := by
        simp only [encodeField, List.length_append]
        have := paddedVarint0_length_pos (t * 8); omega
      cases fuel with
      | zero => simp only [List.length_append] at hlen; omega
      | succ fuel' =>
        have hne : encodeField t 0 0 (.varint n) ++ pbFields rest ≠ [] := by
          intro he; have := congrArg List.length he
          simp only [List.length_append, List.length_nil] at this; omega
        have hfuel' : (pbFields rest).length ≤ fuel' := by
          simp only [List.length_append] at hlen; omega
        have hr1 : readVarint (encodeField t 0 0 (.varint n) ++ pbFields rest) =
            some (t * 8, paddedVarint n 0 ++ pbFields rest) := by
          rw [encodeField, List.append_assoc, readVarint_paddedVarint0]
        have hr2 : readVarint (paddedVarint n 0 ++ pbFields rest) = some (n, pbFields rest) :=
          readVarint_paddedVarint0 n (pbFields rest)
        change parsePbFields (fuel' + 1) (encodeField t 0 0 (.varint n) ++ pbFields rest) =
          some ((t, .varint n) :: rest)
        simp only [parsePbFields, hne, ↓reduceIte, hr1,
          Nat.mul_mod_left, Nat.mul_div_cancel _ (by decide : 0 < 8), hr2,
          parsePbFields_pbFields rest fuel' hrest hfuel', Option.map_some]
    | bytes b =>
      have hpos : 0 < (encodeField t 0 0 (.bytes b)).length := by
        simp only [encodeField, List.length_append]
        have := paddedVarint0_length_pos (t * 8 + 2); omega
      cases fuel with
      | zero => simp only [List.length_append] at hlen; omega
      | succ fuel' =>
        have hne : encodeField t 0 0 (.bytes b) ++ pbFields rest ≠ [] := by
          intro he; have := congrArg List.length he
          simp only [List.length_append, List.length_nil] at this; omega
        have hfuel' : (pbFields rest).length ≤ fuel' := by
          simp only [List.length_append] at hlen; omega
        have hr1 : readVarint (encodeField t 0 0 (.bytes b) ++ pbFields rest) =
            some (t * 8 + 2, paddedVarint b.length 0 ++ (b ++ pbFields rest)) := by
          rw [encodeField, List.append_assoc, List.append_assoc, readVarint_paddedVarint0]
        have hr2 : readVarint (paddedVarint b.length 0 ++ (b ++ pbFields rest)) =
            some (b.length, b ++ pbFields rest) :=
          readVarint_paddedVarint0 b.length (b ++ pbFields rest)
        have hmod : (t * 8 + 2) % 8 = 2 := by omega
        have hdiv : (t * 8 + 2) / 8 = t := by omega
        have hle : b.length ≤ (b ++ pbFields rest).length := by simp
        change parsePbFields (fuel' + 1) (encodeField t 0 0 (.bytes b) ++ pbFields rest) =
          some ((t, .bytes b) :: rest)
        simp only [parsePbFields, hne, ↓reduceIte, hr1,
          hmod, hdiv, hr2, hle, List.drop_left, List.take_left,
          parsePbFields_pbFields rest fuel' hrest hfuel', Option.map_some]

private theorem decodePbFields_pbFields {l : List (Nat × PbValue)} (hok : ∀ x ∈ l, PbOk x) :
    decodePbFields (pbFields l) = l := by
  simp [decodePbFields, parsePbFields_pbFields l (pbFields l).length hok (Nat.le_refl _)]

private theorem pbFields_append (l₁ l₂ : List (Nat × PbValue)) :
    pbFields (l₁ ++ l₂) = pbFields l₁ ++ pbFields l₂ := by
  simp [pbFields, List.flatMap_append]

private def bytesFieldList (tag : Nat) (b : HwBytes) : List (Nat × PbValue) :=
  if b = [] then [] else [(tag, .bytes b)]

private def u32FieldList (tag : Nat) (v : BitVec 32) : List (Nat × PbValue) :=
  if v = 0 then [] else [(tag, .varint v.toNat)]

private theorem pbFields_bytesFieldList (tag : Nat) (b : HwBytes) :
    pbFields (bytesFieldList tag b) = bytesField tag b := by
  unfold bytesFieldList bytesField; split <;> simp [pbFields]

private theorem pbFields_u32FieldList (tag : Nat) (v : BitVec 32) :
    pbFields (u32FieldList tag v) = u32Field tag v := by
  unfold u32FieldList u32Field; split <;> simp [pbFields]

private theorem pbOk_bytesFieldList (tag : Nat) (b : HwBytes) :
    ∀ x ∈ bytesFieldList tag b, PbOk x := by
  intro x hx; unfold bytesFieldList at hx; split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx; subst hx; trivial

private theorem pbOk_u32FieldList (tag : Nat) (v : BitVec 32) :
    ∀ x ∈ u32FieldList tag v, PbOk x := by
  intro x hx; unfold u32FieldList at hx; split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx; subst hx; trivial

private theorem pbOk_append {l₁ l₂ : List (Nat × PbValue)}
    (h₁ : ∀ x ∈ l₁, PbOk x) (h₂ : ∀ x ∈ l₂, PbOk x) : ∀ x ∈ l₁ ++ l₂, PbOk x := by
  intro x hx; rcases List.mem_append.mp hx with h | h
  · exact h₁ x h
  · exact h₂ x h

private theorem filter_bytesFieldList_ne {tag t : Nat} (h : (tag == t) = false) (b : HwBytes) :
    (bytesFieldList tag b).filter (fun p => p.1 == t) = [] := by
  unfold bytesFieldList; split <;> simp [h]

private theorem filter_bytesFieldList_self (tag : Nat) (b : HwBytes) :
    (bytesFieldList tag b).filter (fun p => p.1 == tag) = bytesFieldList tag b := by
  unfold bytesFieldList; split <;> simp

private theorem filter_u32FieldList_ne {tag t : Nat} (h : (tag == t) = false) (v : BitVec 32) :
    (u32FieldList tag v).filter (fun p => p.1 == t) = [] := by
  unfold u32FieldList; split <;> simp [h]

private theorem filter_u32FieldList_self (tag : Nat) (v : BitVec 32) :
    (u32FieldList tag v).filter (fun p => p.1 == tag) = u32FieldList tag v := by
  unfold u32FieldList; split <;> simp

private theorem filter_option_bytes_ne {α : Type} {tag t : Nat} (h : (tag == t) = false)
    (f : α → HwBytes) (o : Option α) :
    ((o.map fun x => [(tag, PbValue.bytes (f x))]).getD []).filter (fun p => p.1 == t) = [] := by
  cases o <;> simp [h]

private theorem filter_option_bytes_self {α : Type} (tag : Nat) (f : α → HwBytes) (o : Option α) :
    ((o.map fun x => [(tag, PbValue.bytes (f x))]).getD []).filter (fun p => p.1 == tag) =
    (o.map fun x => [(tag, PbValue.bytes (f x))]).getD [] := by
  cases o <;> simp

private theorem filter_map_bytes_ne {α : Type} {tag t : Nat} (h : (tag == t) = false)
    (f : α → HwBytes) (l : List α) :
    (l.map fun x => (tag, PbValue.bytes (f x))).filter (fun p => p.1 == t) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [h, ih]

private theorem filter_map_bytes_self {α : Type} (tag : Nat) (f : α → HwBytes) (l : List α) :
    (l.map fun x => (tag, PbValue.bytes (f x))).filter (fun p => p.1 == tag) =
    l.map fun x => (tag, PbValue.bytes (f x)) := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem pbFields_map_msgField {α : Type} (tag : Nat) (f : α → HwBytes) (l : List α) :
    pbFields (l.map fun x => (tag, PbValue.bytes (f x))) = l.flatMap fun x => msgField tag (f x) := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, pbFields, List.flatMap_cons, msgField]; congr 1

private theorem decodeU32Field_of_filter {tag : Nat} {fs : List (Nat × PbValue)} {v : BitVec 32}
    (hf : fs.filter (fun p => p.1 == tag) = u32FieldList tag v) :
    decodeU32Field tag fs = v := by
  unfold decodeU32Field; rw [hf]; unfold u32FieldList; by_cases h : v = 0#32 <;> simp [h]

private theorem decodeBytesField_of_filter {tag : Nat} {fs : List (Nat × PbValue)} {b : HwBytes}
    (hf : fs.filter (fun p => p.1 == tag) = bytesFieldList tag b) :
    decodeBytesField tag fs = b := by
  unfold decodeBytesField; rw [hf]; unfold bytesFieldList; by_cases h : b = [] <;> simp [h]

private theorem decodeMsgListField_of_filter {α : Type} {tag : Nat} {fs : List (Nat × PbValue)}
    {f : α → HwBytes} {l : List α}
    (hf : fs.filter (fun p => p.1 == tag) = l.map (fun x => (tag, PbValue.bytes (f x)))) :
    decodeMsgListField tag fs = l.map f := by
  unfold decodeMsgListField; rw [hf]; clear hf
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem decodeChainKey_eq (k : BitVec 32 × HwBytes) :
    let kf := decodePbFields (u32Field 1 k.1 ++ bytesField 2 k.2)
    (decodeU32Field 1 kf, decodeBytesField 2 kf) = k := by
  have hpb : u32Field 1 k.1 ++ bytesField 2 k.2 =
      pbFields (u32FieldList 1 k.1 ++ bytesFieldList 2 k.2) := by
    simp [pbFields_append, pbFields_u32FieldList, pbFields_bytesFieldList]
  have hok := pbOk_append (pbOk_u32FieldList 1 k.1) (pbOk_bytesFieldList 2 k.2)
  dsimp only; rw [hpb, decodePbFields_pbFields hok]
  ext1
  · exact decodeU32Field_of_filter (by
      simp [List.filter_append, filter_u32FieldList_self, filter_bytesFieldList_ne])
  · exact decodeBytesField_of_filter (by
      simp [List.filter_append, filter_u32FieldList_ne, filter_bytesFieldList_self])

private theorem decodeMsgKey_eq (k : BitVec 32 × HwBytes) :
    let mf := decodePbFields (u32Field 1 k.1 ++ bytesField 5 k.2)
    (decodeU32Field 1 mf, decodeBytesField 5 mf) = k := by
  have hpb : u32Field 1 k.1 ++ bytesField 5 k.2 =
      pbFields (u32FieldList 1 k.1 ++ bytesFieldList 5 k.2) := by
    simp [pbFields_append, pbFields_u32FieldList, pbFields_bytesFieldList]
  have hok := pbOk_append (pbOk_u32FieldList 1 k.1) (pbOk_bytesFieldList 5 k.2)
  dsimp only; rw [hpb, decodePbFields_pbFields hok]
  ext1
  · exact decodeU32Field_of_filter (by
      simp [List.filter_append, filter_u32FieldList_self, filter_bytesFieldList_ne])
  · exact decodeBytesField_of_filter (by
      simp [List.filter_append, filter_u32FieldList_ne, filter_bytesFieldList_self])

private def chainFields (c : ChainRec) : List (Nat × PbValue) :=
  bytesFieldList 1 c.senderRatchetKey ++
  bytesFieldList 2 c.senderRatchetKeyPrivate ++
  ((c.chainKey.map fun k => [(3, PbValue.bytes (u32Field 1 k.1 ++ bytesField 2 k.2))]).getD []) ++
  c.messageKeys.map fun k => (4, PbValue.bytes (u32Field 1 k.1 ++ bytesField 5 k.2))

private theorem decodeChainBytes_chainBytes (c : ChainRec) : decodeChainBytes (chainBytes c) = c := by
  have hpb : chainBytes c = pbFields (chainFields c) := by
    unfold chainFields chainBytes
    repeat rw [pbFields_append]
    rw [pbFields_bytesFieldList, pbFields_bytesFieldList, pbFields_map_msgField]
    congr 1; congr 1
    cases c.chainKey <;> simp [pbFields, msgField]
  have hok : ∀ x ∈ chainFields c, PbOk x := by
    unfold chainFields; repeat apply pbOk_append
    · exact pbOk_bytesFieldList 1 c.senderRatchetKey
    · exact pbOk_bytesFieldList 2 c.senderRatchetKeyPrivate
    · cases c.chainKey with
      | none => simp
      | some _ => intro x hx; simp only [Option.map_some, Option.getD_some, List.mem_singleton] at hx; subst hx; trivial
    · intro x hx; rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; trivial
  unfold decodeChainBytes; rw [hpb, decodePbFields_pbFields hok]
  let fs := chainFields c
  change ChainRec.mk (decodeBytesField 1 fs) (decodeBytesField 2 fs)
    ((decodeMsgOptField 3 fs).map fun b =>
      let kf := decodePbFields b; (decodeU32Field 1 kf, decodeBytesField 2 kf))
    ((decodeMsgListField 4 fs).map fun b =>
      let mf := decodePbFields b; (decodeU32Field 1 mf, decodeBytesField 5 mf)) = c
  have h1 : decodeBytesField 1 fs = c.senderRatchetKey := decodeBytesField_of_filter (by
    simp [fs, chainFields, List.filter_append, filter_bytesFieldList_self,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne])
  have h2 : decodeBytesField 2 fs = c.senderRatchetKeyPrivate := decodeBytesField_of_filter (by
    simp [fs, chainFields, List.filter_append, filter_bytesFieldList_self,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne])
  have hf3 : fs.filter (fun p => p.1 == 3) =
      (c.chainKey.map fun k => [(3, PbValue.bytes (u32Field 1 k.1 ++ bytesField 2 k.2))]).getD [] := by
    simp [fs, chainFields, List.filter_append, filter_option_bytes_self,
      filter_bytesFieldList_ne, filter_map_bytes_ne]
  have h3 : ((decodeMsgOptField 3 fs).map fun b =>
      let kf := decodePbFields b; (decodeU32Field 1 kf, decodeBytesField 2 kf)) = c.chainKey := by
    unfold decodeMsgOptField; rw [hf3]
    cases c.chainKey with
    | none => rfl
    | some k => simp [decodeChainKey_eq k]
  have hf4 : fs.filter (fun p => p.1 == 4) =
      c.messageKeys.map (fun k => (4, PbValue.bytes (u32Field 1 k.1 ++ bytesField 5 k.2))) := by
    simp [fs, chainFields, List.filter_append, filter_map_bytes_self,
      filter_bytesFieldList_ne, filter_option_bytes_ne]
  have h4 : ((decodeMsgListField 4 fs).map fun b =>
      let mf := decodePbFields b; (decodeU32Field 1 mf, decodeBytesField 5 mf)) = c.messageKeys := by
    rw [decodeMsgListField_of_filter hf4, List.map_map]
    have hfn : ((fun b => let mf := decodePbFields b; (decodeU32Field 1 mf, decodeBytesField 5 mf)) ∘
        fun k : BitVec 32 × HwBytes => u32Field 1 k.1 ++ bytesField 5 k.2) = id := by
      funext k; exact decodeMsgKey_eq k
    rw [hfn, List.map_id]
  rw [h1, h2, h3, h4]

private def sessionBytes (s : SessionRec) : HwBytes :=
  u32Field 1 s.sessionVersion ++ bytesField 2 s.localIdentityPublic ++
  bytesField 3 s.remoteIdentityPublic ++ bytesField 4 s.rootKey ++
  u32Field 5 s.previousCounter ++ ((s.senderChain.map (msgField 6 ∘ chainBytes)).getD []) ++
  s.receiverChains.flatMap (msgField 7 ∘ chainBytes) ++
  ((s.pendingPreKey.map fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
  u32Field 10 s.remoteRegistrationId ++ u32Field 11 s.localRegistrationId ++
  bytesField 13 s.aliceBaseKey ++
  ((s.pendingKyberPreKey.map fun p => msgField 14 (p.1 ++ p.2)).getD []) ++
  bytesField 15 s.pqRatchetState

private def sessionFields (s : SessionRec) : List (Nat × PbValue) :=
  u32FieldList 1 s.sessionVersion ++
  bytesFieldList 2 s.localIdentityPublic ++
  bytesFieldList 3 s.remoteIdentityPublic ++
  bytesFieldList 4 s.rootKey ++
  u32FieldList 5 s.previousCounter ++
  ((s.senderChain.map fun c => [(6, PbValue.bytes (chainBytes c))]).getD []) ++
  s.receiverChains.map (fun c => (7, PbValue.bytes (chainBytes c))) ++
  ((s.pendingPreKey.map fun p => [(9, PbValue.bytes (p.1 ++ p.2))]).getD []) ++
  u32FieldList 10 s.remoteRegistrationId ++
  u32FieldList 11 s.localRegistrationId ++
  bytesFieldList 13 s.aliceBaseKey ++
  ((s.pendingKyberPreKey.map fun p => [(14, PbValue.bytes (p.1 ++ p.2))]).getD []) ++
  bytesFieldList 15 s.pqRatchetState

private theorem decodeSessionBytes_sessionBytes (s : SessionRec) :
    decodeSessionBytes (sessionBytes s) = (normPending ⟨s, []⟩).current := by
  have hpb : sessionBytes s = pbFields (sessionFields s) := by
    unfold sessionFields sessionBytes
    repeat rw [pbFields_append]
    rw [pbFields_u32FieldList, pbFields_bytesFieldList, pbFields_bytesFieldList,
        pbFields_bytesFieldList, pbFields_u32FieldList,
        pbFields_map_msgField 7 chainBytes s.receiverChains,
        pbFields_u32FieldList, pbFields_u32FieldList, pbFields_bytesFieldList, pbFields_bytesFieldList]
    cases s.senderChain <;> cases s.pendingPreKey <;> cases s.pendingKyberPreKey <;>
      simp [pbFields, msgField, Function.comp_def]
  have hok : ∀ x ∈ sessionFields s, PbOk x := by
    unfold sessionFields; repeat apply pbOk_append
    · exact pbOk_u32FieldList 1 s.sessionVersion
    · exact pbOk_bytesFieldList 2 s.localIdentityPublic
    · exact pbOk_bytesFieldList 3 s.remoteIdentityPublic
    · exact pbOk_bytesFieldList 4 s.rootKey
    · exact pbOk_u32FieldList 5 s.previousCounter
    · cases s.senderChain with
      | none => simp
      | some _ => intro x hx; simp only [Option.map_some, Option.getD_some, List.mem_singleton] at hx; subst hx; trivial
    · intro x hx; rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; trivial
    · cases s.pendingPreKey with
      | none => simp
      | some _ => intro x hx; simp only [Option.map_some, Option.getD_some, List.mem_singleton] at hx; subst hx; trivial
    · exact pbOk_u32FieldList 10 s.remoteRegistrationId
    · exact pbOk_u32FieldList 11 s.localRegistrationId
    · exact pbOk_bytesFieldList 13 s.aliceBaseKey
    · cases s.pendingKyberPreKey with
      | none => simp
      | some _ => intro x hx; simp only [Option.map_some, Option.getD_some, List.mem_singleton] at hx; subst hx; trivial
    · exact pbOk_bytesFieldList 15 s.pqRatchetState
  unfold decodeSessionBytes; rw [hpb, decodePbFields_pbFields hok]
  let fs := sessionFields s
  have hf1 : fs.filter (fun p => p.1 == 1) = u32FieldList 1 s.sessionVersion := by
    simp [fs, sessionFields, List.filter_append, filter_u32FieldList_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf2 : fs.filter (fun p => p.1 == 2) = bytesFieldList 2 s.localIdentityPublic := by
    simp [fs, sessionFields, List.filter_append, filter_bytesFieldList_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf3 : fs.filter (fun p => p.1 == 3) = bytesFieldList 3 s.remoteIdentityPublic := by
    simp [fs, sessionFields, List.filter_append, filter_bytesFieldList_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf4 : fs.filter (fun p => p.1 == 4) = bytesFieldList 4 s.rootKey := by
    simp [fs, sessionFields, List.filter_append, filter_bytesFieldList_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf5 : fs.filter (fun p => p.1 == 5) = u32FieldList 5 s.previousCounter := by
    simp [fs, sessionFields, List.filter_append, filter_u32FieldList_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf6 : fs.filter (fun p => p.1 == 6) =
      (s.senderChain.map fun c => [(6, PbValue.bytes (chainBytes c))]).getD [] := by
    simp [fs, sessionFields, List.filter_append, filter_option_bytes_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf7 : fs.filter (fun p => p.1 == 7) =
      s.receiverChains.map (fun c => (7, PbValue.bytes (chainBytes c))) := by
    simp [fs, sessionFields, List.filter_append, filter_map_bytes_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne]
  have hf9 : fs.filter (fun p => p.1 == 9) =
      (s.pendingPreKey.map fun p => [(9, PbValue.bytes (p.1 ++ p.2))]).getD [] := by
    simp [fs, sessionFields, List.filter_append, filter_option_bytes_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf10 : fs.filter (fun p => p.1 == 10) = u32FieldList 10 s.remoteRegistrationId := by
    simp [fs, sessionFields, List.filter_append, filter_u32FieldList_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf11 : fs.filter (fun p => p.1 == 11) = u32FieldList 11 s.localRegistrationId := by
    simp [fs, sessionFields, List.filter_append, filter_u32FieldList_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf13 : fs.filter (fun p => p.1 == 13) = bytesFieldList 13 s.aliceBaseKey := by
    simp [fs, sessionFields, List.filter_append, filter_bytesFieldList_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf14 : fs.filter (fun p => p.1 == 14) =
      (s.pendingKyberPreKey.map fun p => [(14, PbValue.bytes (p.1 ++ p.2))]).getD [] := by
    simp [fs, sessionFields, List.filter_append, filter_option_bytes_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  have hf15 : fs.filter (fun p => p.1 == 15) = bytesFieldList 15 s.pqRatchetState := by
    simp [fs, sessionFields, List.filter_append, filter_bytesFieldList_self, filter_u32FieldList_ne,
      filter_bytesFieldList_ne, filter_option_bytes_ne, filter_map_bytes_ne]
  change SessionRec.mk (decodeU32Field 1 fs) (decodeBytesField 2 fs) (decodeBytesField 3 fs)
      (decodeBytesField 4 fs) (decodeU32Field 5 fs) ((decodeMsgOptField 6 fs).map decodeChainBytes)
      ((decodeMsgListField 7 fs).map decodeChainBytes) ((decodeMsgOptField 9 fs).map (·, []))
      ((decodeMsgOptField 14 fs).map (·, [])) (decodeU32Field 10 fs) (decodeU32Field 11 fs)
      (decodeBytesField 13 fs) (decodeBytesField 15 fs) = (normPending ⟨s, []⟩).current
  have h1 := decodeU32Field_of_filter hf1
  have h2 := decodeBytesField_of_filter hf2
  have h3 := decodeBytesField_of_filter hf3
  have h4 := decodeBytesField_of_filter hf4
  have h5 := decodeU32Field_of_filter hf5
  have h6 : (decodeMsgOptField 6 fs).map decodeChainBytes = s.senderChain := by
    unfold decodeMsgOptField; rw [hf6]
    cases s.senderChain with
    | none => rfl
    | some c => simp [decodeChainBytes_chainBytes c]
  have h7 : (decodeMsgListField 7 fs).map decodeChainBytes = s.receiverChains := by
    rw [decodeMsgListField_of_filter hf7, List.map_map]
    have hfn : (decodeChainBytes ∘ chainBytes) = id := funext decodeChainBytes_chainBytes
    rw [hfn, List.map_id]
  have h9 : (decodeMsgOptField 9 fs).map (·, ([] : HwBytes)) =
      s.pendingPreKey.map fun p => (p.1 ++ p.2, ([] : HwBytes)) := by
    unfold decodeMsgOptField; rw [hf9]; cases s.pendingPreKey <;> rfl
  have h10 := decodeU32Field_of_filter hf10
  have h11 := decodeU32Field_of_filter hf11
  have h13 := decodeBytesField_of_filter hf13
  have h14 : (decodeMsgOptField 14 fs).map (·, ([] : HwBytes)) =
      s.pendingKyberPreKey.map fun p => (p.1 ++ p.2, ([] : HwBytes)) := by
    unfold decodeMsgOptField; rw [hf14]; cases s.pendingKyberPreKey <;> rfl
  have h15 := decodeBytesField_of_filter hf15
  rw [h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h13, h14, h15]
  rfl

private theorem recordBytes_normPending (rec : RecordRec) :
    recordBytes (normPending rec) = recordBytes rec := by
  cases rec with | mk cur prev =>
  cases cur with | mk sv lip rip rk pc sc rcs ppk pkpk rrid lrid abk pq =>
  cases ppk <;> cases pkpk <;> simp [normPending, recordBytes]

private theorem decodeRecordRaw_recordBytes (rec : RecordRec) :
    decodeRecordRaw (recordBytes rec) = normPending rec := by
  let rf : List (Nat × PbValue) :=
    (1, PbValue.bytes (sessionBytes rec.current)) ::
      rec.previous.map (fun p => (2, PbValue.bytes (id p)))
  have hpb : recordBytes rec = pbFields rf := by
    unfold rf recordBytes sessionBytes pbFields
    simp only [List.flatMap_cons, msgField]
    congr 1
    exact (pbFields_map_msgField 2 id rec.previous).symm
  have hok : ∀ x ∈ rf, PbOk x := by
    intro x hx; simp only [rf, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨_, _, rfl⟩ <;> trivial
  unfold decodeRecordRaw
  have hfs : decodePbFields (recordBytes rec) = rf := by
    rw [hpb, decodePbFields_pbFields hok]
  rw [hfs]; dsimp only
  have hf1 : decodeMsgOptField 1 rf = some (sessionBytes rec.current) := by
    unfold decodeMsgOptField rf
    simp [filter_map_bytes_ne (by decide : (2 == 1) = false)]
  have hf2 : decodeMsgListField 2 rf = rec.previous := by
    have hflt : rf.filter (fun p => p.1 == 2) = rec.previous.map (fun p => (2, PbValue.bytes (id p))) := by
      simp [rf]
    rw [decodeMsgListField_of_filter hflt, List.map_id]
  rw [hf1, Option.getD_some, decodeSessionBytes_sessionBytes, hf2]
  rfl

private theorem ite_some_eq_some {α : Type} {p : Prop} [Decidable p] {a b : α}
    (h : (if p then some a else none) = some b) : p ∧ a = b := by
  by_cases hp : p
  · simp only [hp, ↓reduceIte, Option.some.injEq] at h
    exact ⟨hp, h⟩
  · simp only [hp, ↓reduceIte] at h
    nomatch h

end DecodeRecord

/-- Soundness of `decodeRecordBytes?`: any returned record re-encodes to `b`. -/
theorem decodeRecordBytes?_sound {b : HwBytes} {rr : RecordRec}
    (h : decodeRecordBytes? b = some rr) : b = recordBytes rr :=
  let ⟨hb, heq⟩ := DecodeRecord.ite_some_eq_some h
  heq ▸ hb

/-- Completeness of `decodeRecordBytes?`: `recordBytes rec` decodes to `some (DecodeRecord.normPending rec)`. -/
theorem decodeRecordBytes?_recordBytes (rec : RecordRec) :
    decodeRecordBytes? (recordBytes rec) = some (DecodeRecord.normPending rec) := by
  unfold decodeRecordBytes?
  rw [DecodeRecord.decodeRecordRaw_recordBytes, DecodeRecord.recordBytes_normPending]
  simp

/-- Decides `EligibleForSessionPromotion`. Correct by construction (a `Decidable` instance);
its body need not be read. -/
instance instDecidableEligibleForSessionPromotion (rec b : HwBytes) :
    Decidable (EligibleForSessionPromotion rec b) :=
  match hdec : decodeRecordBytes? rec, hpw : parsePreKeyWire b with
  | some rr₀, some p₀ =>
    if h : rr₀.previous = [] ∧ rr₀.current.aliceBaseKey = p₀.baseKey.take 33 then
      isTrue ⟨rr₀, p₀, decodeRecordBytes?_sound hdec, h.1, hpw, h.2⟩
    else
      isFalse fun ⟨rr, p, hrec, hprev, hpwire, halice⟩ => by
        rw [hrec, decodeRecordBytes?_recordBytes] at hdec
        have hrr := Option.some.inj hdec
        rw [hpwire] at hpw
        have hp := Option.some.inj hpw
        subst hrr; subst hp
        exact h ⟨hprev, halice⟩
  | none, _ =>
    isFalse fun ⟨rr, _, hrec, _⟩ => by
      rw [hrec, decodeRecordBytes?_recordBytes] at hdec
      nomatch hdec
  | some _, none =>
    isFalse fun ⟨_, _, _, _, hpwire, _⟩ => by
      rw [hpwire] at hpw
      nomatch hpw

end DY.Libsignal.Rust
