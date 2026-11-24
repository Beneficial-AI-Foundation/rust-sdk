/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas

@[expose] public section

/-!
# Rust's decimal grammar for `i64` (M06)

`Defs.parseI64`, the value that Rust's `i64::from_str` (radix 10) gives a byte string, or `none`
when it reports an error. Written from the documented grammar, not from the `core` source and
not from the model of `i64::from_str` in `trusted/Rmcp/FunsExternal.lean` (plan Section 17,
"M06 (integer parsing)"): an optional single `+` or `-`, then at least one ASCII digit, and
nothing else; leading zeros are allowed; values outside `[-2^63, 2^63 - 1]` are rejected.

Sources, at the toolchain `nightly-2026-06-01` pinned until the Aeneas upgrade of 2026-11-24
(`rust-src`, `library/core/src/num/`; re-checking the citations against `nightly-2026-09-17` is
part of the model review of that upgrade):
- `mod.rs` lines 1592–1606, the doc comment of `FromStr for i64` (generator
  `from_str_int_impl`, signed case): "The characters are expected to be an optional `+` or
  `-` sign followed by only digits. Leading and trailing non-digit characters (including
  whitespace) represent an error. Underscores (which are accepted in Rust literals) also
  represent an error." `from_str` is `from_str_radix(src, 10)` (line 1627). The doc comment of
  `from_str_radix` says "Digits are a subset of these characters, depending on `radix`" and
  lists `0-9`, `a-z`, `A-Z` (lines 1648–1651); that radix 10 admits only `0-9` is an inference
  from that list (the ten characters of the first range), not a sentence of the doc.
- `error.rs` lines 93–129, `IntErrorKind`: `Empty` for an empty string; `InvalidDigit` for a
  non-ASCII character or a misplaced or lone `+`/`-`; `PosOverflow`/`NegOverflow` for a value
  too large or too small for the target type, here `i64` with range `[i64::MIN, i64::MAX] =
  [-2^63, 2^63 - 1]` (`int_macros.rs` lines 36 and 47).

The error kind is not part of this definition: M06 discards it (`.ok()`, `model.rs` line 324).
Everything is stated on `List U8` and `Int`.
-/

namespace Defs

open Aeneas.Std

namespace IntParse

/-- The byte `+` (ASCII `0x2B`), the optional plus sign (`mod.rs` lines 1594–1598, doc of
`FromStr`). -/
def plus : U8 := 43#u8

/-- The byte `-` (ASCII `0x2D`), the optional minus sign (`mod.rs` lines 1594–1598, doc of
`FromStr`). -/
def minus : U8 := 45#u8

/-- `c` is an ASCII decimal digit `'0'`–`'9'` (bytes 48–57): the digits of radix 10, inferred
from the digit list `0-9`, `a-z`, `A-Z` of the doc of `from_str_radix` (`mod.rs` lines
1648–1651). Every other byte, including every byte of a non-ASCII character such as the
Arabic-Indic digit `U+0661`, is not a digit (`error.rs` lines 99–106, `InvalidDigit`). -/
def isAsciiDigit (c : U8) : Bool := decide (48 ≤ c.val ∧ c.val ≤ 57)

/-- The value of a string of ASCII digits read in base 10, most significant digit first; leading
zeros do not change the value. Used only on lists whose bytes satisfy `isAsciiDigit`. -/
def digitsValue (ds : List U8) : Nat :=
  ds.foldl (fun acc c => 10 * acc + (c.val - 48)) 0

/-- Splits off an optional single leading sign: `(true, rest)` after a leading `-`,
`(false, rest)` after a leading `+`, and `(false, s)` when `s` does not start with a sign. Only
the first byte is examined, so a second sign stays in `rest` (and is then not a digit). -/
def splitSign : List U8 → Bool × List U8
  | [] => (false, [])
  | c :: rest =>
    if c = plus then (false, rest)
    else if c = minus then (true, rest)
    else (false, c :: rest)

/-- `i64::MIN = -2^63` (`int_macros.rs` line 36: `!Self::MAX`). -/
def i64Min : Int := -2 ^ 63

/-- `i64::MAX = 2^63 - 1` (`int_macros.rs` line 47: `(u64::MAX >> 1) as i64`). -/
def i64Max : Int := 2 ^ 63 - 1

end IntParse

open IntParse

/-- **The value of `s` under Rust's `i64::from_str` grammar**, or `none` for every input that
`i64::from_str` rejects.

`s` is an optional single sign (`splitSign`) followed by a nonempty list of ASCII digits
(`isAsciiDigit`) and nothing else; the value is that of the digits (`digitsValue`), negated
after `-`, and must lie in `[i64Min, i64Max] = [-2^63, 2^63 - 1]` (module docstring: `mod.rs`
lines 1592–1606, `error.rs` lines 93–129). So `"0"`, `"+0"`, `"-0"`, `"007"`,
`"9223372036854775807"` and `"-9223372036854775808"` are accepted, while `""`, `"+"`, `"-"`,
`" 1"`, `"1 "`, `"9223372036854775808"`, `"-9223372036854775809"`, `"+-1"`, `"1_000"` and the
Arabic-Indic digit `"١"` are rejected. -/
def parseI64 (s : List U8) : Option Int :=
  let (negative, digits) := splitSign s
  if digits ≠ [] ∧ digits.all isAsciiDigit = true then
    let v : Int := if negative then -(digitsValue digits : Int) else (digitsValue digits : Int)
    if i64Min ≤ v ∧ v ≤ i64Max then some v else none
  else none

end Defs
