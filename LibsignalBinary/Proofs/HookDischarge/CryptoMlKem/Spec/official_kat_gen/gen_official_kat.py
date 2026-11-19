#!/usr/bin/env python3
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

"""Generate `Spec/MlKemOfficialVectors.lean` from the official NIST test vectors.

Sources (downloaded and checked against the pinned SHA-256 digests below):

* ML-KEM-768 (FIPS 203): NIST ACVP-Server `v1.1.0.43`,
  `ML-KEM-keyGen-FIPS203/internalProjection.json` and
  `ML-KEM-encapDecap-FIPS203/internalProjection.json`.
* Kyber-1024 (Round 3): `KAT/kyber1024/PQCkemKAT_3168.rsp` from the NIST Round 3 submission
  package `Kyber-Round3.zip` (`NIST-PQ-Submission-Kyber-20201001`).

The `.rsp` file gives only the 48-byte DRBG seed of each case. The script re-derives the
`randombytes` outputs of `PQCgenKAT_kem.c` (NIST `rng.c` AES-256 CTR DRBG): `d` and `z` for
`crypto_kem_keypair`, then the 32-byte `buf` for `crypto_kem_enc`. It checks that `z` equals the
last 32 bytes of the official `sk`.

Large outputs (`ek`, `dk`, ciphertexts) are stored as SHA3-256 digests computed here from the
official values; inputs and shared secrets are stored in full.

Usage: `python3 gen_official_kat.py [--cache DIR] > ../MlKemOfficialVectors.lean`
Needs the `cryptography` package (AES for the DRBG).
"""

import argparse
import hashlib
import io
import json
import os
import sys
import urllib.request
import zipfile

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

ACVP_TAG = "v1.1.0.43"
ACVP_COMMIT = "975de31eb83d87039ec88934fdc47d8c312b892d"
ACVP_BASE = (
    f"https://raw.githubusercontent.com/usnistgov/ACVP-Server/{ACVP_COMMIT}/gen-val/json-files"
)
ACVP_KEYGEN = (
    f"{ACVP_BASE}/ML-KEM-keyGen-FIPS203/internalProjection.json",
    "d7a62a2c3476957f56dd8d24f9004ea6776ccfe995ffe71a65bb9506dc9c7b1b",
)
ACVP_ENCDEC = (
    f"{ACVP_BASE}/ML-KEM-encapDecap-FIPS203/internalProjection.json",
    "a556952ce869bb89c3a3196a701dad89647c193a34c86eafb61a9d710d5b810f",
)
KYBER_ZIP = (
    "https://csrc.nist.gov/CSRC/media/Projects/post-quantum-cryptography/documents/round-3/"
    "submissions/Kyber-Round3.zip",
    "a68b152c7cf70a32bab1abaf2ab5a21423f33b0ac11ca8db9b9dd4864007319b",
)
KYBER_RSP_MEMBER = "NIST-PQ-Submission-Kyber-20201001/KAT/kyber1024/PQCkemKAT_3168.rsp"
KYBER_RSP_SHA256 = "89248f2f33f7f4f7051729111f3049c409a933ec904aedadf035f30fa5646cd5"

# Number of Kyber-1024 `.rsp` cases (counts 0..N-1) to emit.
KYBER_COUNT = 10


def fetch(url_sha, cache):
    url, sha = url_sha
    path = os.path.join(cache, os.path.basename(url.split("?")[0])) if cache else None
    if cache and "json-files" in url:
        path = os.path.join(cache, url.split("/")[-2] + "_" + os.path.basename(url))
    if path and os.path.exists(path):
        data = open(path, "rb").read()
    else:
        with urllib.request.urlopen(url, timeout=120) as r:
            data = r.read()
        if path:
            open(path, "wb").write(data)
    got = hashlib.sha256(data).hexdigest()
    if got != sha:
        sys.exit(f"SHA-256 mismatch for {url}: got {got}, want {sha}")
    return data


class NistDrbg:
    """AES-256 CTR DRBG of the NIST PQC `rng.c` (no derivation function, no reseed)."""

    def __init__(self, entropy48):
        assert len(entropy48) == 48
        self.key = bytes(32)
        self.v = bytes(16)
        self._update(entropy48)

    def _aes(self, block):
        enc = Cipher(algorithms.AES(self.key), modes.ECB()).encryptor()
        return enc.update(block) + enc.finalize()

    def _inc_v(self):
        self.v = ((int.from_bytes(self.v, "big") + 1) % (1 << 128)).to_bytes(16, "big")

    def _update(self, provided):
        temp = b""
        for _ in range(3):
            self._inc_v()
            temp += self._aes(self.v)
        if provided is not None:
            temp = bytes(a ^ b for a, b in zip(temp, provided))
        self.key, self.v = temp[:32], temp[32:]

    def randombytes(self, n):
        out = b""
        while len(out) < n:
            self._inc_v()
            out += self._aes(self.v)
        self._update(None)
        return out[:n]


def sha3(b):
    return hashlib.sha3_256(b).hexdigest()


def parse_rsp(text):
    cases, cur = [], {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        k, v = (s.strip() for s in line.split("=", 1))
        if k == "count" and cur:
            cases.append(cur)
            cur = {}
        cur[k] = v
    if cur:
        cases.append(cur)
    return cases


def lean_str(h):
    return '"' + h.lower() + '"'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cache", help="directory to cache downloads in")
    args = ap.parse_args()
    if args.cache:
        os.makedirs(args.cache, exist_ok=True)

    keygen = json.loads(fetch(ACVP_KEYGEN, args.cache))
    encdec = json.loads(fetch(ACVP_ENCDEC, args.cache))
    zdata = fetch(KYBER_ZIP, args.cache)
    rsp = zipfile.ZipFile(io.BytesIO(zdata)).read(KYBER_RSP_MEMBER)
    if hashlib.sha256(rsp).hexdigest() != KYBER_RSP_SHA256:
        sys.exit("PQCkemKAT_3168.rsp SHA-256 mismatch")

    def group(doc, pset, func=None):
        gs = [g for g in doc["testGroups"]
              if g["parameterSet"] == pset and (func is None or g.get("function") == func)]
        assert len(gs) == 1, (pset, func, len(gs))
        return gs[0]

    out = []
    w = out.append
    w("""/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# Official NIST ML-KEM-768 and Kyber-1024 Test Vectors (generated, data only)

Generated by `Spec/official_kat_gen/gen_official_kat.py`; do not edit by hand. Checked by
`Spec/MlKemOfficialKat.lean`.

* ML-KEM-768 (FIPS 203): NIST ACVP-Server `""" + ACVP_TAG + """` (`""" + ACVP_COMMIT[:12] + """`),
  `ML-KEM-keyGen-FIPS203` and `ML-KEM-encapDecap-FIPS203` `internalProjection.json`, every
  ML-KEM-768 case of the `keyGen`, `encapsulation`, `decapsulation` and `encapsulationKeyCheck`
  groups.
* Kyber-1024 (Round 3): `KAT/kyber1024/PQCkemKAT_3168.rsp` of the NIST Round 3 submission
  `Kyber-Round3.zip`, counts `0`..`""" + str(KYBER_COUNT - 1) + """`. `d`, `z` and `rand` are the
  `randombytes` outputs that `PQCgenKAT_kem.c` draws from the NIST AES-256 CTR DRBG seeded with the
  case's `seed`.

All values are lowercase hex. Fields ending in `Sha3` hold the SHA3-256 digest of the official
value instead of the value.
-/

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKemOfficialVectors

/-- ACVP `ML-KEM-keyGen-FIPS203` case: `KeyGen_internal(d, z) = (ek, dk)`. -/
structure KeyGenVec where
  tcId : Nat
  d : String
  z : String
  ekSha3 : String
  dkSha3 : String

/-- ACVP `ML-KEM-encapDecap-FIPS203` encapsulation case: `Encaps_internal(ek, m) = (k, c)`. -/
structure EncapsVec where
  tcId : Nat
  ek : String
  m : String
  cSha3 : String
  k : String

/-- ACVP `ML-KEM-encapDecap-FIPS203` decapsulation case: `Decaps_internal(dk, c) = k`
(valid ciphertexts and modified ones that take the implicit-rejection branch). -/
structure DecapsVec where
  tcId : Nat
  reason : String
  dk : String
  c : String
  k : String

/-- ACVP `ML-KEM-encapDecap-FIPS203` encapsulation key check (FIPS 203 §7.2 modulus check). -/
structure EkCheckVec where
  tcId : Nat
  reason : String
  ek : String
  passed : Bool

/-- `PQCkemKAT_3168.rsp` case, with the DRBG outputs `d`, `z` (keypair) and `rand` (encaps). -/
structure Kyber1024Vec where
  count : Nat
  d : String
  z : String
  rand : String
  pk : String
  sk : String
  ct : String
  ss : String
""")

    # --- ML-KEM-768 keyGen ---
    g = group(keygen, "ML-KEM-768")
    assert g["testType"] == "AFT"
    w("/-- Every ML-KEM-768 `keyGen` case (ACVP `tgId " + str(g["tgId"]) + "`). -/")
    w("@[expose] def mlkem768KeyGen : List KeyGenVec := [")
    rows = []
    for t in g["tests"]:
        ek, dk = bytes.fromhex(t["ek"]), bytes.fromhex(t["dk"])
        assert len(ek) == 1184 and len(dk) == 2400 and dk[1152:2336] == ek
        rows.append(f"  {{ tcId := {t['tcId']}, d := {lean_str(t['d'])}, z := {lean_str(t['z'])},\n"
                    f"    ekSha3 := {lean_str(sha3(ek))},\n"
                    f"    dkSha3 := {lean_str(sha3(dk))} }}")
    w(",\n".join(rows) + "]\n")

    # --- ML-KEM-768 encapsulation ---
    g = group(encdec, "ML-KEM-768", "encapsulation")
    w("/-- Every ML-KEM-768 `encapsulation` case (ACVP `tgId " + str(g["tgId"]) + "`). -/")
    w("@[expose] def mlkem768Encaps : List EncapsVec := [")
    rows = []
    for t in g["tests"]:
        ek, c = bytes.fromhex(t["ek"]), bytes.fromhex(t["c"])
        assert len(ek) == 1184 and len(c) == 1088
        rows.append(f"  {{ tcId := {t['tcId']},\n"
                    f"    ek := {lean_str(t['ek'])},\n"
                    f"    m := {lean_str(t['m'])},\n"
                    f"    cSha3 := {lean_str(sha3(c))},\n"
                    f"    k := {lean_str(t['k'])} }}")
    w(",\n".join(rows) + "]\n")

    # --- ML-KEM-768 decapsulation ---
    g = group(encdec, "ML-KEM-768", "decapsulation")
    w("/-- Every ML-KEM-768 `decapsulation` case (ACVP `tgId " + str(g["tgId"]) + "`). -/")
    w("@[expose] def mlkem768Decaps : List DecapsVec := [")
    rows = []
    for t in g["tests"]:
        dk, c = bytes.fromhex(t["dk"]), bytes.fromhex(t["c"])
        assert len(dk) == 2400 and len(c) == 1088
        rows.append(f"  {{ tcId := {t['tcId']}, reason := {json.dumps(t['reason'])},\n"
                    f"    dk := {lean_str(t['dk'])},\n"
                    f"    c := {lean_str(t['c'])},\n"
                    f"    k := {lean_str(t['k'])} }}")
    w(",\n".join(rows) + "]\n")

    # --- ML-KEM-768 encapsulationKeyCheck ---
    g = group(encdec, "ML-KEM-768", "encapsulationKeyCheck")
    w("/-- Every ML-KEM-768 `encapsulationKeyCheck` case (ACVP `tgId " + str(g["tgId"]) + "`). -/")
    w("@[expose] def mlkem768EkCheck : List EkCheckVec := [")
    rows = []
    for t in g["tests"]:
        ek = bytes.fromhex(t["ek"])
        assert len(ek) == 1184, (t["tcId"], len(ek))
        rows.append(f"  {{ tcId := {t['tcId']}, reason := {json.dumps(t['reason'])},\n"
                    f"    ek := {lean_str(t['ek'])},\n"
                    f"    passed := {'true' if t['testPassed'] else 'false'} }}")
    w(",\n".join(rows) + "]\n")

    # --- Kyber-1024 Round 3 ---
    cases = parse_rsp(rsp.decode())
    w(f"/-- `PQCkemKAT_3168.rsp` counts `0`..`{KYBER_COUNT - 1}` (Round 3 Kyber-1024). -/")
    w("@[expose] def kyber1024Round3 : List Kyber1024Vec := [")
    rows = []
    for c in cases[:KYBER_COUNT]:
        drbg = NistDrbg(bytes.fromhex(c["seed"]))
        d, z, rand = drbg.randombytes(32), drbg.randombytes(32), drbg.randombytes(32)
        pk, sk = bytes.fromhex(c["pk"]), bytes.fromhex(c["sk"])
        ct, ss = bytes.fromhex(c["ct"]), bytes.fromhex(c["ss"])
        assert len(pk) == 1568 and len(sk) == 3168 and len(ct) == 1568 and len(ss) == 32
        assert sk[3136:] == z, "DRBG re-derivation of z does not match sk"
        assert sk[1536:3104] == pk
        rows.append(f"  {{ count := {c['count']},\n"
                    f"    d := {lean_str(d.hex())},\n"
                    f"    z := {lean_str(z.hex())},\n"
                    f"    rand := {lean_str(rand.hex())},\n"
                    f"    pk := {lean_str(c['pk'])},\n"
                    f"    sk := {lean_str(c['sk'])},\n"
                    f"    ct := {lean_str(c['ct'])},\n"
                    f"    ss := {lean_str(c['ss'])} }}")
    w(",\n".join(rows) + "]\n")

    w("end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKemOfficialVectors")
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
