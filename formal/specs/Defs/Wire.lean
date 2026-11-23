/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas

/-!
# Definitions for the `request_state_wire` statements

Definitions that the statements of the wire functions W01–W15 and `frame_roundtrip` (plan
Section 2.1) are written in: the `.`-components of a token, the version tags and MAC domain
separators as byte lists, big-endian encoding and decoding of 64-bit values, the two MAC
transcripts, the frame layout and the expiry predicate.

Rust source: `crates/rmcp/src/model/request_state_wire.rs` in the patched copy (patch 01 on
origin/main 7caec76, `formal/trusted/patches/01-request-state-wire.patch`, D2 fallback
2026-11-23; the file exists only there); line numbers below refer to it. The translation the
drafts are checked against was generated from it plus the Charon settings of
`crates/rmcp/Cargo.toml` (the seven derived `Debug` impls excluded). Every definition is stated on
mathematical objects (`List U8`, `Nat`, `Int`) and does not refer to the translated code.
Everything lives in the namespace `Defs.Wire`.
-/

namespace Defs.Wire

open Aeneas.Std

/-! ## Constants -/

/-- The byte `.` (ASCII `0x2E`), the component separator of a token (`b'.'`, lines 83 and 96;
plan Section 3, "W06–W09 — splitting"). -/
def dot : U8 := 46#u8

/-- The version tag `"rs1"` as ASCII bytes `r`, `s`, `1` (`VERSION_V1`, line 9). -/
def versionV1 : List U8 := [114#u8, 115#u8, 49#u8]

/-- The version tag `"rs2"` as ASCII bytes `r`, `s`, `2` (`VERSION_V2`, line 11). -/
def versionV2 : List U8 := [114#u8, 115#u8, 50#u8]

/-- The MAC domain separator `"rmcp/mrtr/request-state/v1"` as its 26 ASCII bytes
(`DOMAIN_V1`, line 13). -/
def domainV1 : List U8 :=
  [114#u8, 109#u8, 99#u8, 112#u8, 47#u8,                      -- "rmcp/"
   109#u8, 114#u8, 116#u8, 114#u8, 47#u8,                     -- "mrtr/"
   114#u8, 101#u8, 113#u8, 117#u8, 101#u8, 115#u8, 116#u8,    -- "request"
   45#u8,                                                     -- "-"
   115#u8, 116#u8, 97#u8, 116#u8, 101#u8, 47#u8,              -- "state/"
   118#u8, 49#u8]                                             -- "v1"

/-- The MAC domain separator `"rmcp/mrtr/request-state/v2"` as its 26 ASCII bytes
(`DOMAIN_V2`, line 15). -/
def domainV2 : List U8 :=
  [114#u8, 109#u8, 99#u8, 112#u8, 47#u8,                      -- "rmcp/"
   109#u8, 114#u8, 116#u8, 114#u8, 47#u8,                     -- "mrtr/"
   114#u8, 101#u8, 113#u8, 117#u8, 101#u8, 115#u8, 116#u8,    -- "request"
   45#u8,                                                     -- "-"
   115#u8, 116#u8, 97#u8, 116#u8, 101#u8, 47#u8,              -- "state/"
   118#u8, 50#u8]                                             -- "v2"

/-- Minimum key length in bytes (`MIN_KEY_LENGTH = 32`, line 19; plan Section 2.1, W02). -/
def minKeyLength : Nat := 32

/-- Maximum key-id length in bytes (`MAX_KID_LEN = 255`, line 21; plan Section 2.1, W03). -/
def maxKidLen : Nat := 255

/-- Length of the big-endian expiry prefix of a body (`EXPIRY_LEN = 8`, line 17). -/
def expiryLen : Nat := 8

/-! ## Base64 length -/

/-- `4 * ceil(n / 3)`: the length of the unpadded Base64url encoding rounded up to whole
quads, as plan Section 2.1 (W01) specifies for `b64_len` (lines 27–36). `(n + 2) / 3` is
`ceil(n / 3)` on `Nat`, the value of Rust's `n.div_ceil(3)` (line 28). -/
def b64Len (n : Nat) : Nat := 4 * ((n + 2) / 3)

/-! ## Splitting on `.` -/

/-- The `.`-separated components of a byte string: Lean's `List.splitOn` on the byte `.`.
The result is never empty, an empty input has the single empty component, and the separators
are dropped. This is the independent model of `str::split('.')` on which plan Section 3
("W06–W09 — splitting") and Section 2.1 (W06–W09) state the parsing functions. -/
def components (s : List U8) : List (List U8) := s.splitOn dot

/-! ## Big-endian encoding -/

/-- The byte `n mod 256`. Helper of `be64`: byte `i` of `u64::to_be_bytes` is
`(n >> 8 * (7 - i)) as u8` (lines 186, 196, 198, 241; plan Section 2.1, W10, W11, W15). -/
def byteOf (n : Nat) : U8 := ⟨BitVec.ofNat _ n⟩

/-- `be64 n`: the 8 bytes of `n mod 2 ^ 64` in big-endian order, most significant byte first.
Models `u64::to_be_bytes` (lines 186, 196, 198, 241; plan Section 2.1, W10, W11, W15). -/
def be64 (n : Nat) : List U8 :=
  (List.range 8).map fun i => byteOf (n / 256 ^ (7 - i))

/-- `be64OfInt x`: the 8 big-endian bytes of the two's-complement 64-bit representation of
`x`, i.e. of `x mod 2 ^ 64` (Euclidean remainder). Models `(expiry as u64).to_be_bytes()`
(line 241; plan Section 2.1, W15). -/
def be64OfInt (x : Int) : List U8 := be64 (x % 2 ^ 64).toNat

/-- Unsigned big-endian value of a byte list: the first byte is the most significant.
Models `u64::from_be_bytes` on its 8 input bytes (line 206; plan Section 2.1, W12); on a list
of 8 bytes the value is below `2 ^ 64`. -/
def beNat (b : List U8) : Nat :=
  b.foldl (fun acc x => 256 * acc + x.val) 0

/-- Two's-complement reading of a 64-bit unsigned value `u < 2 ^ 64`: `u` if `u < 2 ^ 63`,
otherwise `u - 2 ^ 64`. Models the cast `as i64` of a `u64` (line 206; plan Section 2.1,
W12). -/
def toInt64 (u : Nat) : Int :=
  if u < 2 ^ 63 then (u : Int) else (u : Int) - 2 ^ 64

/-! ## Transcripts -/

/-- The bytes `rs1` authenticates: `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body` (plan Section 2.1,
W10; doc comment and body of `transcript_v1`, lines 182–190). The length is the length in
bytes of `ad` as a natural number. -/
def transcriptV1 (ad body : List U8) : List U8 :=
  domainV1 ++ be64 ad.length ++ ad ++ body

/-- The bytes `rs2` authenticates:
`DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body` (plan Section 2.1, W11; doc
comment and body of `transcript_v2`, lines 192–202). -/
def transcriptV2 (kid ad body : List U8) : List U8 :=
  domainV2 ++ be64 kid.length ++ kid ++ be64 ad.length ++ ad ++ body

/-! ## Frame and expiry -/

/-- An authenticated body: the expiry as 8 big-endian two's-complement bytes followed by the
payload, `be64(expiry as u64) ++ payload` (plan Section 2.1, W15; lines 238–244). -/
def frameBytes (expiry : Int) (payload : List U8) : List U8 :=
  be64OfInt expiry ++ payload

/-- Expiry of an authenticated body: the two's-complement value of its first 8 bytes read
big-endian (plan Section 2.1, W12 applied in W14). Meaningful for bodies of at least 8 bytes.
Models `decode_expiry([body[0], …, body[7]])` in `open_frame` (lines 205–207 and 229–232). -/
def bodyExpiry (body : List U8) : Int :=
  toInt64 (beNat (body.take expiryLen))

/-- A token with expiry `expiry` is expired at time `now` (milliseconds) iff the expiry is
nonzero and `now` is strictly after it (plan Section 2.1, W13; lines 209–212). An expiry of `0`
never expires, `now = expiry` is accepted, and a negative nonzero expiry is compared as a
signed value like any other (plan Section 3, "W14/E01 — expiry"). -/
def Expired (expiry now : Int) : Prop :=
  expiry ≠ 0 ∧ now > expiry

instance (expiry now : Int) : Decidable (Expired expiry now) :=
  inferInstanceAs (Decidable (expiry ≠ 0 ∧ now > expiry))

end Defs.Wire
