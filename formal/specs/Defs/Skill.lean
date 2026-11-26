/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Rmcp.Types
public import Rmcp.FunsExternal
public import Defs.Bytes
public import Defs.IntParse
public import Defs.Wire

@[expose] public section

/-!
# Definitions for the public `skill.rs` statements (K01–K20)

Signed off by the spec owner (Hoang Le Truong) on 2026-11-25 together with the statements; drafted
by AI (Claude Code, `claude-opus-5-5`), reviewed in three spec-cycle rounds.

The vocabulary of the statements K01–K20 about `crates/rmcp/src/model/skill.rs` (restated
in `formal/specs/Specs/Model/Skill.lean`): what a skill URI, a skill name, a `sha256:`
digest, a percent-normalised URI and a manifest key are, and the expected results of
`Skill::validate` (`validateResult`) and `validate_skills` (`validateSkillsResult`).

**Strings.** A Rust `&str` or `String` is described by its UTF-8 bytes (`Defs.utf8Bytes`, a
`List U8`); a Rust `char` sequence by a `List Char`.

**Evaluation.** The data-valued definitions (`Bool`, `Option`, `List`, `String` or `Result`
valued) are computable by structural recursion (the kernel evaluates them on small inputs),
except where they name one of the three `opaque` constants of the trusted base, which they do
only unopened, as the value the Rust code computes (review rule of `formal/README.md`,
"Trusted base"): `ExtModel.sha256` (SHA-256, FIPS 180-4) in `sha256Digest`, `ExtModel.nfkc`
(Unicode NFKC, UAX #15) in `isSkillName`, `nameMatchesSegment` and `NfkcFits`, and
`ExtModel.generalCategory` (the Unicode General_Category property) in `isNameAlnum`. No
definition states a law about them. The `Prop`-valued definitions (`ValidManifest`,
`ValidSkill`, `ValidSkills`, `UsizeFits`, `UriFits`, `SkillFits`, `NfkcFits`, `KeysSorted`) are
properties with quantifiers over the inputs, and are not evaluated.

**Shared definitions.** Strings are read with `Defs.utf8Bytes` (`Defs.Bytes`), ASCII digits with
`Defs.IntParse.isAsciiDigit` and byte literals with `Defs.Wire.byteOf`.

**Independence.** The percent-encoding definitions (`decodePercent`, `encodeControls`,
`normalizePercent`) are written from the behaviour the Rust code and RFC 3986 §2.1 and §6.2.2
describe, not from the trusted models `ExtModel.percentDecode` and
`ExtModel.percentEncodeControls` (a proof relates them; they agree on the samples checked by
kernel evaluation in the spec cycle). `ExtModel.strOfBytes?` (UTF-8 decoding, Lean's
`String.fromUTF8?`) is used as the meaning of "these bytes are the UTF-8 encoding of a string".

**Line citations.** "upstream" is `crates/rmcp/src/model/skill.rs` at origin/main `7caec76` (the
working tree, unmodified); "patched" is the copy with translation patches 01–04 applied
(`.llbc/work/crates/rmcp/src/model/skill.rs`), from which the translation is made. The two agree
up to line 103; translation patch 04 (hunks H1–H9) changes `verify`, `sha256_digest`,
`validate`, `skill_name_from_uri`, `is_valid_skill_name`, `manifest_resource_key`,
`normalize_percent_encoding`, `is_sha256_digest` and `validate_skills` without changing the
values they compute (patch header, "Behaviour"), except the patch-induced capacity panics that
`NfkcFits` and `UriFits` exclude.
-/

namespace Defs.Skill

open Aeneas.Std
open Defs (utf8Bytes)
open Defs.IntParse (isAsciiDigit)
open Defs.Wire (byteOf)
open rmcp.model.skill (Skill SkillResource SkillResources SkillValidationError)

/-! ## Bytes and characters -/

/-- The byte of an ASCII character `c` (its code point, for `c.toNat < 128`). Used to write
the bytes `/`, `%`, `?`, `#`, `-`, … of the Rust source readably. -/
def asciiByte (c : Char) : U8 := byteOf c.toNat

/-- `some rest` if `l = pre ++ rest`, otherwise `none`: `str::strip_prefix` on UTF-8 bytes
(upstream lines 362, 418; patched lines 385, 482 through `prim::strip_prefix`, line 600). -/
def stripPrefix (l pre : List U8) : Option (List U8) :=
  if pre.isPrefixOf l then some (l.drop pre.length) else none

/-- `some front` if `l = front ++ suf`, otherwise `none`: `str::strip_suffix` on UTF-8 bytes
(upstream lines 330, 361; patched lines 349, 384 through `prim::strip_suffix`, line 596). -/
def stripSuffix (l suf : List U8) : Option (List U8) :=
  if suf.isSuffixOf l then some (l.take (l.length - suf.length)) else none

/-- Whether a byte is `?` or `#`, which start the query or the fragment of a URI
(`['?', '#']`, upstream lines 327 and 363; patched `prim::find_query_or_fragment`, line 592). -/
def isQueryOrFragmentStart (b : U8) : Bool :=
  b == asciiByte '?' || b == asciiByte '#'

/-! ## Skill URIs (K14) -/

/-- The file name of a skill's entry point, `SKILL.md` (`SKILL_MD`, upstream line 323, patched
line 342), as bytes. -/
def skillMd : List U8 := utf8Bytes "SKILL.md"

/-- The last `/`-separated segment of `path` (all of `path` if it has no `/`): the item that
`path.rsplit('/').next()` yields (upstream line 331; patched `prim::last_slash_segment`, line
604). -/
def lastSegment (path : List U8) : List U8 :=
  (path.splitOn (asciiByte '/')).getLastD []

/-- **The skill name encoded in a `SKILL.md` URI** (`skill_name_from_uri`, upstream lines
326–333, patched lines 345–352), on UTF-8 bytes: `none` if the URI has a `?` or `#` (a query or
fragment); otherwise, if it ends in `/SKILL.md`, the path segment just before that, when it is
not empty; `none` in every other case. For example `skill://acme/billing/SKILL.md` gives
`billing`, and `billing/SKILL.md` gives `billing`; `skill://acme//SKILL.md`, `SKILL.md` and
`skill://acme/billing/SKILL.md?x` give `none`. The segment is returned as written, still
percent-encoded. -/
def skillNameOfUri (uri : List U8) : Option (List U8) :=
  if uri.any isQueryOrFragmentStart then none
  else
    match stripSuffix uri (asciiByte '/' :: skillMd) with
    | none => none
    | some path => if lastSegment path = [] then none else some (lastSegment path)

/-! ## `sha256:` digests (K06, K07, K15) -/

/-- Whether a byte is a lowercase hexadecimal digit, `0`–`9` or `a`–`f` (`b'0'..=b'9' |
b'a'..=b'f'`, upstream line 419, patched line 483). -/
def isLowerHexDigit (b : U8) : Bool :=
  isAsciiDigit b || (97 ≤ b.val && b.val ≤ 102)

/-- **A well-formed digest**: `sha256:` followed by exactly 64 lowercase hexadecimal digits and
nothing else (`is_sha256_digest`, upstream lines 417–421, patched lines 481–485: strip the prefix
`sha256:`, then `hex.len() == 64` and every byte a lowercase hexadecimal digit). -/
def isSha256Digest (digest : List U8) : Bool :=
  match stripPrefix digest (utf8Bytes "sha256:") with
  | some hex => hex.length == 64 && hex.all isLowerHexDigit
  | none => false

/-- The lowercase hexadecimal digit of `n < 16`, `0`–`9` then `a`–`f`. -/
def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The lowercase hexadecimal text of `bytes`: two digits per byte, high nibble first,
zero-padded (`write!(digest, "{byte:02x}")`, upstream line 125; patched lines 120–123 with
`lower_hex_digit`, lines 128–130). -/
def lowerHex (bytes : List U8) : String :=
  String.ofList (bytes.flatMap fun b => [lowerHexDigit (b.val / 16), lowerHexDigit (b.val % 16)])

/-- **The `sha256:` digest of `bytes`** (`sha256_digest`, upstream lines 116–128, patched lines
116–125): `sha256:` followed by the lowercase hexadecimal text of the 32-byte SHA-256 digest of
`bytes`. The digest is the opaque value `ExtModel.sha256 bytes` (FIPS 180-4), named unopened. -/
def sha256Digest (bytes : List U8) : String :=
  "sha256:" ++ lowerHex (ExtModel.sha256 bytes).val

/-! ## Skill names (K13) -/

/-- Whether a character counts as a letter or digit of a skill name: its Unicode
General_Category is `Ll`, `Lm`, `Lo`, `Nd`, `Nl` or `No` (`LowercaseLetter`, `ModifierLetter`,
`OtherLetter`, `DecimalNumber`, `LetterNumber`, `OtherNumber`; upstream lines 343–349, patched
lines 365–371). Uppercase (`Lu`) and titlecase (`Lt`) letters do not count. The category is the
opaque value `ExtModel.generalCategory c`, named unopened. -/
def isNameAlnum (c : Char) : Bool :=
  match ExtModel.generalCategory c with
  | .LowercaseLetter | .ModifierLetter | .OtherLetter | .DecimalNumber | .LetterNumber
  | .OtherNumber => true
  | _ => false

/-- **The skill-name rule on a character sequence**, for a classification `alnum` of the letters
and digits: `cs` has 1 to 64 characters, and each character is a letter or digit (`alnum`), or
a `-` with a letter or digit on both sides. So: no leading, trailing or doubled hyphen, nothing
else. This is the loop of `is_valid_skill_name` (upstream lines 337–355, patched lines
356–378): `needs_alphanumeric` starts `true`, a letter or digit clears it, a `-` is accepted
only when it is clear and sets it again, any other character, or an index of 64 or more,
rejects, and the end accepts only when it is clear. The letter-or-digit test comes first, so a
`-` that `alnum` classifies as a letter or digit counts as one. -/
def nameCharsValid (alnum : Char → Bool) (cs : List Char) : Bool :=
  decide (cs ≠ [] ∧ cs.length ≤ 64) &&
    (List.range cs.length).all fun i =>
      alnum (cs.getD i ' ') ||
        (cs.getD i ' ' == '-' && decide (0 < i) && decide (i + 1 < cs.length) &&
          alnum (cs.getD (i - 1) ' ') && alnum (cs.getD (i + 1) ' '))

/-- **A valid skill name** (`is_valid_skill_name`, upstream lines 335–355, patched lines
354–378): the NFKC form of the name (`ExtModel.nfkc`, unopened; UAX #15) satisfies the
skill-name rule `nameCharsValid` with the letters and digits of `isNameAlnum`. -/
def isSkillName (skillName : String) : Bool :=
  nameCharsValid isNameAlnum (ExtModel.nfkc skillName.toList)

/-! ## Percent-encoding (K13, K16) -/

/-- Whether a byte is a hexadecimal digit of either case, `0`–`9`, `A`–`F`, `a`–`f`
(`u8::is_ascii_hexdigit`, used at patched line 468; `percent-encoding 2.3.2`,
`after_percent_sign` through `char::to_digit(16)`). -/
def isHexDigit (b : U8) : Bool :=
  isAsciiDigit b || (65 ≤ b.val && b.val ≤ 70) || (97 ≤ b.val && b.val ≤ 102)

/-- The value of a hexadecimal digit of either case. Applied only to bytes that pass
`isHexDigit`; its value on any other byte has no meaning. -/
def hexValue (b : U8) : Nat :=
  if b.val ≤ 57 then b.val - 48 else if b.val ≤ 70 then b.val - 55 else b.val - 87

/-- The byte that the two hexadecimal digits `h l` denote, `16 * h + l`. -/
def hexByte (h l : U8) : U8 := byteOf (16 * hexValue h + hexValue l)

/-- The decoding of one part of a string split at `%`, the `%` before it included: if the part
starts with two hexadecimal digits, the byte they denote followed by the rest of the part;
otherwise `%` and the part unchanged. -/
def decodePart (part : List U8) : List U8 :=
  match part with
  | h :: l :: rest =>
    if isHexDigit h && isHexDigit l then hexByte h l :: rest else asciiByte '%' :: part
  | _ => asciiByte '%' :: part

/-- **Percent-decoding** (RFC 3986 §2.1): every `%` followed by two hexadecimal digits (either
case) becomes the byte they denote; every other byte, including a `%` not followed by two
hexadecimal digits, is kept. Written on the parts between the `%` bytes: the first part is
kept, each later part is decoded by `decodePart`. This is `percent_decode_str` of
`percent-encoding 2.3.2` (`src/lib.rs` lines 252–277, called at upstream line 285; patched
`prim::percent_decode_utf8`, line 628). -/
def decodePercent (bytes : List U8) : List U8 :=
  match bytes.splitOn (asciiByte '%') with
  | [] => []
  | first :: parts => first ++ parts.flatMap decodePart

/-- **The segment matches the name**: the percent-decoded segment `encoded` is the UTF-8 encoding
of a string whose NFKC form equals the NFKC form of `skillName` (upstream lines 285–288:
`percent_decode_str(encoded_name).decode_utf8()`
`.is_ok_and(|segment| segment.nfkc().eq(name.nfkc()))`; patched lines 287–290). `false` if the
decoded bytes are not UTF-8. `ExtModel.nfkc` is named unopened; the equality of the two NFKC
forms is the condition the Rust code tests. -/
def nameMatchesSegment (encoded : List U8) (skillName : String) : Bool :=
  match ExtModel.strOfBytes? (decodePercent encoded) with
  | some segment => ExtModel.nfkc segment.toList == ExtModel.nfkc skillName.toList
  | none => false

/-- The uppercase hexadecimal digit of `n < 16`, `0`–`9` then `A`–`F`. -/
def upperHexDigit (n : Nat) : U8 :=
  if n < 10 then byteOf (48 + n) else byteOf (55 + n)

/-- Whether a byte is encoded by `utf8_percent_encode(_, CONTROLS)`: a non-ASCII byte (`≥ 128`)
or an ASCII control (`0x00`–`0x1F`, `0x7F`) (`percent-encoding 2.3.2`, `src/ascii_set.rs` lines
52–54 and 103–114; upstream line 391, patched `prim::percent_encode_controls`, line 624). -/
def needsEncoding (b : U8) : Bool :=
  decide (128 ≤ b.val ∨ b.val < 32 ∨ b.val = 127)

/-- **Percent-encoding of controls and non-ASCII bytes**: each byte that `needsEncoding` becomes
`%` and its two uppercase hexadecimal digits, every other byte is kept (`utf8_percent_encode(value,
CONTROLS)`, upstream line 391; `percent-encoding 2.3.2`, `src/lib.rs` lines 73–100 and
147–176). -/
def encodeControls (bytes : List U8) : List U8 :=
  bytes.flatMap fun b =>
    if needsEncoding b then [asciiByte '%', upperHexDigit (b.val / 16), upperHexDigit (b.val % 16)]
    else [b]

/-- Whether a byte is unreserved in RFC 3986 (§2.3): an ASCII letter or digit, `-`, `.`, `_` or
`~` (upstream line 401; patched `is_unreserved`, lines 476–478). -/
def isUnreserved (b : U8) : Bool :=
  isAsciiDigit b || (65 ≤ b.val && b.val ≤ 90) || (97 ≤ b.val && b.val ≤ 122) ||
    b == asciiByte '-' || b == asciiByte '.' || b == asciiByte '_' || b == asciiByte '~'

/-- The normalisation of one part of a string split at `%`, the `%` before it included: if the
part starts with two hexadecimal digits denoting an unreserved byte, that byte; if they denote
another byte, `%` and the two digits in uppercase; then the rest of the part. A part that does
not start with two hexadecimal digits is kept, after its `%` (upstream lines 396–411; patched
`push_normalized_part`, lines 445–462). -/
def normalizePart (part : List U8) : List U8 :=
  match part with
  | h :: l :: rest =>
    if isHexDigit h && isHexDigit l then
      (if isUnreserved (hexByte h l) then [hexByte h l]
       else [asciiByte '%', upperHexDigit (hexValue h), upperHexDigit (hexValue l)]) ++ rest
    else asciiByte '%' :: part
  | _ => asciiByte '%' :: part

/-- **Percent-normalisation of a URI** (`normalize_percent_encoding`, upstream lines 387–414,
patched lines 425–441): first percent-encode the controls and non-ASCII bytes
(`encodeControls`), then apply RFC 3986 §6.2.2: decode each escape `%XX` of an unreserved byte
and uppercase the hexadecimal digits of every other escape, keeping reserved delimiters
(e.g. `%2F`) encoded. A `%` not followed by two hexadecimal digits is kept. Written on the parts
between the `%` bytes, as the Rust code is: the first part is kept, each later part is
normalised by `normalizePart`. For example `a%7e%2fb` gives `a~%2Fb`. -/
def normalizePercent (bytes : List U8) : List U8 :=
  match (encodeControls bytes).splitOn (asciiByte '%') with
  | [] => []
  | first :: parts => first ++ parts.flatMap normalizePart

/-! ## Manifest keys (K13) -/

/-- **Dot-segment removal** over directory segments, in order: `.` is skipped, `..` removes the
last kept segment, any other segment is kept; `none` once `..` climbs above the root (upstream
lines 371–380; patched `resolve_segments` and `resolve_segment`, lines 401–423). -/
def removeDotSegments (segments : List (List U8)) : Option (List (List U8)) :=
  segments.foldl
    (fun acc segment => acc.bind fun dirs =>
      if segment = utf8Bytes "." then some dirs
      else if segment = utf8Bytes ".." then (if dirs = [] then none else some dirs.dropLast)
      else some (dirs ++ [segment]))
    (some [])

/-- **The comparison key of a manifest file** (`manifest_resource_key`, upstream lines 357–385,
patched lines 380–399), on UTF-8 bytes: the skill's root is its URI without the final
`SKILL.md` (keeping the `/`); the file URI must start with the root; the rest is split before its
first `?` or `#` into a path and a suffix (query or fragment, kept as written); the path is
percent-normalised (`normalizePercent`) and split at `/`; the last segment is the file name,
which must not be empty, `.` or `..` (that would name a directory); the other segments have
their dot-segments removed (`removeDotSegments`, `none` if `..` climbs above the root); the key
is the resolved segments and the file name joined with `/`, followed by the suffix. `none` (the
file is not within the skill's directory) when any step fails. Reads use the advertised URI;
the key only detects two spellings of the same file. -/
def manifestKey (skillUri resourceUri : List U8) : Option (List U8) := do
  let root ← stripSuffix skillUri skillMd
  let relative ← stripPrefix resourceUri root
  let path := relative.takeWhile fun b => !isQueryOrFragmentStart b
  let suffix := relative.dropWhile fun b => !isQueryOrFragmentStart b
  let segments := (normalizePercent path).splitOn (asciiByte '/')
  let file := segments.getLastD []
  if file = [] ∨ file = utf8Bytes "." ∨ file = utf8Bytes ".." then none
  else do
    let dirs ← removeDotSegments segments.dropLast
    some (List.intercalate [asciiByte '/'] (dirs ++ [file]) ++ suffix)

/-! ## Expected result of `Skill::validate` (K13) -/

/-- The key of the manifest file `file` of the skill at `skillUri` (`manifestKey` on the UTF-8
bytes of both URIs). -/
def fileKey (skillUri : String) (file : SkillResource) : Option (List U8) :=
  manifestKey (utf8Bytes skillUri) (utf8Bytes file.uri)

/-- **The fault of one manifest file**, given the files listed before it (`earlier`), in the
order the Rust loop checks them (upstream lines 301–316, patched lines 315–335): no key →
`ResourceOutsideSkill { uri: file.uri, skill_uri }`; a key that an earlier file has →
`DuplicateResource(file.uri)` (the `HashSet` of earlier keys; only membership matters); a
malformed digest → `MalformedDigest { uri: file.uri, digest: file.digest }`; otherwise none. -/
def fileFault (skillUri : String) (earlier : List SkillResource) (file : SkillResource) :
    Option SkillValidationError :=
  match fileKey skillUri file with
  | none => some (.ResourceOutsideSkill file.uri skillUri)
  | some key =>
    if earlier.any (fun g => fileKey skillUri g == some key) then some (.DuplicateResource file.uri)
    else if !isSha256Digest (utf8Bytes file.digest) then
      some (.MalformedDigest file.uri file.digest)
    else none

/-- **The first faulty manifest file**: the fault (`fileFault`) of the first file of `files`, in
manifest order, that has one, each checked against all files before it (`earlier ++` those of
`files` already passed); `none` if no file has one. -/
def firstFileFault (skillUri : String) : List SkillResource → List SkillResource →
    Option SkillValidationError
  | _, [] => none
  | earlier, file :: rest =>
    (fileFault skillUri earlier file).or (firstFileFault skillUri (earlier ++ [file]) rest)

/-- **The expected result of `Skill::validate`** (upstream lines 277–319, patched lines 279–338),
with its checks in the Rust order, the first failing one giving the error:
1. the URI names no skill (`skillNameOfUri`) → `UriNotSkillMd(uri)` (upstream 278–280);
2. the frontmatter name is not a valid skill name (`isSkillName`) → `InvalidName(name)`
   (upstream 281–284);
3. the URI segment does not match the name (`nameMatchesSegment`) →
   `NameMismatch { uri, name }` (upstream 285–293);
4. `resources` is `"dynamic"` → `Ok(())` (upstream 294–296);
5. no manifest file has exactly the skill's URI → `MissingSkillMd(uri)` (upstream 297–299);
6. the first faulty manifest file (`firstFileFault`): `ResourceOutsideSkill`,
   `DuplicateResource` or `MalformedDigest` (upstream 300–317);
7. otherwise `Ok(())` (upstream 318). -/
def validateResult (s : Skill) : core.result.Result Unit SkillValidationError :=
  match skillNameOfUri (utf8Bytes s.uri) with
  | none => .Err (.UriNotSkillMd s.uri)
  | some encoded =>
    if !isSkillName s.frontmatter.name then .Err (.InvalidName s.frontmatter.name)
    else if !nameMatchesSegment encoded s.frontmatter.name then
      .Err (.NameMismatch s.uri s.frontmatter.name)
    else
      match s.resources with
      | .Dynamic => .Ok ()
      | .Files files =>
        if !files.val.any (fun f => f.uri == s.uri) then .Err (.MissingSkillMd s.uri)
        else
          match firstFileFault s.uri [] files.val with
          | some e => .Err e
          | none => .Ok ()

/-- **A manifest that passes the file checks**, for the skill at `skillUri`: some file has
exactly the skill's URI (its own `SKILL.md`), every file has a key (lies within the skill's
directory) and a well-formed digest, and the keys of the files are pairwise distinct (no file is
listed twice, under any spelling that normalises to the same key). -/
def ValidManifest (skillUri : String) (files : List SkillResource) : Prop :=
  (∃ f ∈ files, f.uri = skillUri) ∧
    (∀ f ∈ files, (fileKey skillUri f).isSome ∧ isSha256Digest (utf8Bytes f.digest)) ∧
    (files.map (fileKey skillUri)).Nodup

/-- **A skill that `validate` accepts**, as one property: its URI names a skill
(`skillNameOfUri`: no `?` or `#`, and it ends in `<segment>/SKILL.md` with the segment
non-empty, without `/`, and at the start of the URI or after a `/`; so `billing/SKILL.md` is
accepted as well as `skill://acme/billing/SKILL.md`) whose percent-decoded segment matches the
frontmatter name in NFKC form, the name is a valid skill name, and, unless `resources` is
`"dynamic"`, its manifest passes the file checks (`ValidManifest`). -/
def ValidSkill (s : Skill) : Prop :=
  (∃ encoded, skillNameOfUri (utf8Bytes s.uri) = some encoded ∧
      nameMatchesSegment encoded s.frontmatter.name = true) ∧
    isSkillName s.frontmatter.name = true ∧
    ∀ files, s.resources = .Files files → ValidManifest s.uri files.val

/-! ## Expected result of `validate_skills` (K16) -/

/-- The duplicate-detection key of a skill: its URI, percent-normalised (`normalizePercent`;
upstream line 428, patched line 492). -/
def skillKey (s : Skill) : List U8 := normalizePercent (utf8Bytes s.uri)

/-- **The first faulty skill of a listing** (upstream lines 424–433, patched lines 488–497):
walking the skills in order, each checked against all skills before it (`earlier`), the first
that does not validate gives its `validate` error; the first whose key (`skillKey`) an earlier
skill has gives `DuplicateSkill(uri)` (the `HashSet` of earlier keys; only membership matters);
`none` if there is neither. -/
def firstSkillFault : List Skill → List Skill → Option SkillValidationError
  | _, [] => none
  | earlier, s :: rest =>
    match validateResult s with
    | .Err e => some e
    | .Ok () =>
      if earlier.any (fun t => skillKey t == skillKey s) then some (.DuplicateSkill s.uri)
      else firstSkillFault (earlier ++ [s]) rest

/-- **The expected result of `validate_skills`**: `Err` of the first faulty skill
(`firstSkillFault`), `Ok(())` if there is none. -/
def validateSkillsResult (skills : List Skill) : core.result.Result Unit SkillValidationError :=
  match firstSkillFault [] skills with
  | some e => .Err e
  | none => .Ok ()

/-- **A listing that `validate_skills` accepts**: every skill is valid (`ValidSkill`) and the
percent-normalised URIs (`skillKey`) are pairwise distinct. -/
def ValidSkills (skills : List Skill) : Prop :=
  (∀ s ∈ skills, ValidSkill s) ∧ (skills.map skillKey).Nodup

/-! ## Size premises -/

/-- **A string fits in a slice**: it has at most `usize::MAX` UTF-8 bytes (`String.utf8ByteSize`,
the length of `utf8Bytes s`), the bound of the Lean model of `String::deref`/`as_str`
(`trusted/Rmcp/FunsExternal.lean`, `String::as_bytes`). Every Rust `String` meets it (at most
`isize::MAX` bytes). -/
def UsizeFits (s : String) : Prop := s.utf8ByteSize ≤ Usize.max

/-- **A URI fits the size bounds of the patched helpers**: `24 * (n + 1) ≤ isize::MAX` for a URI
of `n` UTF-8 bytes (`ExtModel.maxStringBytes`). It bounds the `Vec<String>` of 24-byte `String`s
that the patched copy collects in `prim::split_slash` and `prim::split_percent` (patched lines
608–622; a URI has at most `n + 1` parts) and the strings of `normalize_percent_encoding` and
`manifest_resource_key` (at most `3 * n` bytes). Sufficient, and necessary up to the constant for
a URI made only of `/` bytes. The `Vec` bound is patch-induced: the original iterates the parts
without collecting them. Every URI held in memory meets it: the address space of the translated
target has at most `2^57` bytes, and `24 * (2^57 + 1) < 2^63 - 1` (size convention of
`trusted/Rmcp/FunsExternal.lean`). -/
def UriFits (uri : String) : Prop := 24 * (uri.utf8ByteSize + 1) ≤ ExtModel.maxStringBytes

/-- **The sizes of a skill fit** (premise of K13): the URI and the name fit in a slice
(`UsizeFits`), and every manifest file's URI meets `UriFits` and its digest `UsizeFits`. Every Rust
skill held in memory meets it (see `UriFits`). The per-file part is sufficient, not exact:
`validate` reaches the files only up to the first faulty one. -/
def SkillFits (s : Skill) : Prop :=
  UsizeFits s.uri ∧ UsizeFits s.frontmatter.name ∧
    ∀ files, s.resources = .Files files → ∀ f ∈ files.val, UriFits f.uri ∧ UsizeFits f.digest

/-- **The NFKC forms fit** (patch-induced premise of K13): when the URI names a skill (segment
`encoded`), the NFKC form of the frontmatter name, and, when the name is valid and the decoded
segment is a string, the NFKC form of that string, each have at most `isize::MAX / 4`
characters. The patched copy collects each NFKC form into a `Vec<char>` (`prim::nfkc`, patched
lines 635–637; hunks H2, H4 of translation patch 04), which panics with "capacity overflow"
above `isize::MAX` bytes, where the original streams it. It is the exact condition under which
the Lean model of `validate` reaches no such panic (`prim::nfkc` is called on the name in
`is_valid_skill_name`, then on the segment and the name in the name comparison). The real NFKC
expands a character to at most 18 characters (`U+FDFA`), so a name and a URI of at most
`isize::MAX / 72` bytes each meet it; no definition here states that fact about the real
function: the bridge lemma `NfkcFits.of_utf8ByteSize_le` (restated in `Specs/Model/Skill.lean`, "Consequences of
the model") derives `NfkcFits` from it, taken as a premise in implication form. -/
def NfkcFits (s : Skill) : Prop :=
  ∀ encoded, skillNameOfUri (utf8Bytes s.uri) = some encoded →
    4 * (ExtModel.nfkc s.frontmatter.name.toList).length ≤ ExtModel.maxStringBytes ∧
      (isSkillName s.frontmatter.name = true → ∀ segment,
        ExtModel.strOfBytes? (decodePercent encoded) = some segment →
          4 * (ExtModel.nfkc segment.toList).length ≤ ExtModel.maxStringBytes)

/-! ## Frontmatter maps (K08, K09) -/

/-- The value of key `k` in a `serde_json::Map` (the value of the entry with key `k`, `none` if
there is none). -/
def mapLookup (m : serde_json.map.Map String serde_json.value.Value) (k : String) :
    Option serde_json.value.Value :=
  (m.entries.find? fun e => e.1 == k).map Prod.snd

/-- **The map invariant**: the entries are strictly ascending by key in Rust's `String` order
(the lexicographic order of the UTF-8 bytes), so the keys are pairwise distinct. The model of
`serde_json::Map` (`trusted/Rmcp/TypesExternal.lean`, a `BTreeMap` in the translated
configuration) represents each Rust map by its entries in this order; every map built by
`Map::new` and `Map::insert` meets it. With the `serde_json` feature `preserve_order` (off in
the translated configuration; it can be switched on by Cargo feature unification in a crate
that depends on `rmcp`) a `serde_json::Map` is an `IndexMap` in insertion order and does not
meet it. -/
def KeysSorted (m : serde_json.map.Map String serde_json.value.Value) : Prop :=
  m.entries.Pairwise fun a b => utf8Bytes a.1 < utf8Bytes b.1

end Defs.Skill
