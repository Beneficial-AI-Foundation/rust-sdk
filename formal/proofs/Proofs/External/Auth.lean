/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.External.String
public import Proofs.External.WP

@[expose] public section

/-!
# Specs of the externals of the `auth.rs` OAuth metadata checks (A04–A10, patch 06)

Spec theorems for the models of `formal/trusted/Rmcp/FunsExternal.lean`, section "`auth.rs` OAuth
metadata URL and issuer checks": the ten `auth::prim` functions that translation patch 06 adds
(`crates/rmcp/src/transport/auth.rs` in the patched copy), `Option::zip`,
`str::eq_ignore_ascii_case` and the seven `url::Url` functions that the targets A04–A10 reach.
Each external has a theorem named after it with `_spec`. The opaque values (`ExtModel.urlScheme`,
`urlPath`, `urlFragment`, `urlPort`, `urlSerialization`, `urlJoin`, `issuerUrl`; human decision
AD4 2026-11-26) appear in the postconditions unopened; their laws are hypotheses of the statements
that need them.
Stated exceptions (the same three in the header of patch 06, the section docstring of
FunsExternal.lean and the module docstring of Proofs.External.Auth): (1) AD7: the `issuer_url`
setters can panic for a discovery URL longer than `u32::MAX` bytes; the model returns `ok`. (2) AD8:
the `debug_assert!` of `Url::join` (url-2.5.9 `src/parser.rs` line 1304) can panic for a `file:`
base whose last path segment is a normalized Windows drive letter; the model returns `ok`. (3)
The `tracing` side effect of the four log functions is not modelled; they return `()`.

Section "Whitespace" proves that the byte strings of `ExtModel.whitespaceUtf8` are the UTF-8
encodings of the code points `ExtModel.whitespaceCodePoints` (`whitespaceUtf8_eq`), so the
`prim::trim` model strips exactly the encodings of the Unicode `White_Space` chars. Section
"Evaluation of the models" checks the exact models on small inputs by kernel evaluation
(`decide`).
-/

open Aeneas Aeneas.Std Result
open rmcp

namespace Proofs.External.Auth

open ExtModel Proofs.External.Utf8

/-! ### Whitespace -/

/-- The byte strings that the `prim::trim` model strips are the UTF-8 encodings of the Unicode
`White_Space` code points, in the same order. -/
theorem whitespaceUtf8_eq :
    whitespaceUtf8 = whitespaceCodePoints.map (fun n => utf8 (String.ofList [Char.ofNat n])) := by
  simp only [utf8_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  decide

end Proofs.External.Auth

/-! ## The `auth::prim` functions -/

namespace transport.auth.prim

open ExtModel

/-- **Spec theorem for `rmcp::transport::auth::prim::trim`**

Always succeeds with the bytes of `s` without its leading and trailing UTF-8-encoded
`White_Space` chars. -/
@[step]
theorem trim_spec (s : Str) :
    transport.auth.prim.trim s ⦃ (result : Str) => result.val = trimWhitespace s.val ⦄ := by
  exact (WP.spec_ok (p := fun result : Str => result.val = trimWhitespace s.val) _).2
    (Slice.from_val _ _)

/-- **Spec theorem for `rmcp::transport::auth::prim::starts_with`**

Always succeeds: `true` exactly when the bytes of `pre` are a prefix of the bytes of `s`. -/
@[step]
theorem starts_with_spec (s : Str) (pre : Str) :
    transport.auth.prim.starts_with s pre ⦃ (result : Bool) =>
      (result = true ↔ pre.val <+: s.val) ⦄ := by
  simp only [transport.auth.prim.starts_with, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `rmcp::transport::auth::prim::strip_suffix`**

Always succeeds: the bytes of `s` before `suffix` if `suffix` is a suffix of `s`, otherwise
`None`. -/
@[step]
theorem strip_suffix_spec (s : Str) (suffix : Str) :
    transport.auth.prim.strip_suffix s suffix ⦃ (result : Option Str) =>
      result.map (·.val) = if suffix.val <:+ s.val then
        some (s.val.take (s.val.length - suffix.val.length)) else none ⦄ := by
  unfold transport.auth.prim.strip_suffix
  by_cases h : suffix.val <:+ s.val
  · rw [ite_eq_left h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_left h]
    exact congrArg some (Slice.from_val _ _)
  · rw [ite_eq_right h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right h, Option.map_none]

/-- **Spec theorem for `rmcp::transport::auth::prim::strip_dir_prefix`**

Always succeeds: the bytes of `path` after `pre` and a `/` if `path` starts with them, otherwise
`None`. -/
@[step]
theorem strip_dir_prefix_spec (path : Str) (pre : Str) :
    transport.auth.prim.strip_dir_prefix path pre ⦃ (result : Option Str) =>
      result.map (·.val) = if pre.val ++ [47#u8] <+: path.val then
        some (path.val.drop (pre.val.length + 1)) else none ⦄ := by
  unfold transport.auth.prim.strip_dir_prefix
  by_cases h : pre.val ++ [47#u8] <+: path.val
  · rw [ite_eq_left h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_left h]
    exact congrArg some (Slice.from_val _ _)
  · rw [ite_eq_right h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right h, Option.map_none]

/-- **Spec theorem for `rmcp::transport::auth::prim::trim_start_slashes`**

Always succeeds with the bytes of `s` without its leading `/` bytes. -/
@[step]
theorem trim_start_slashes_spec (s : Str) :
    transport.auth.prim.trim_start_slashes s ⦃ (result : Str) =>
      result.val = s.val.dropWhile (fun b => decide (b.val = 47)) ⦄ := by
  exact (WP.spec_ok (p := fun result : Str =>
    result.val = s.val.dropWhile (fun b => decide (b.val = 47))) _).2 (Slice.from_val _ _)

/-- **Spec theorem for `rmcp::transport::auth::prim::issuer_url`**

Always succeeds with the issuer `issuerUrl discovery_url issuer_path.val` (an opaque value).
This is the model; Rust panics for a discovery URL with neither query nor fragment that is longer
than `u32::MAX` bytes (stated exception, human decision AD7, docstring of
`transport.auth.prim.issuer_url`). -/
@[step]
theorem issuer_url_spec (discovery_url : url.Url) (issuer_path : Str) :
    transport.auth.prim.issuer_url discovery_url issuer_path ⦃ (result : String) =>
      result = issuerUrl discovery_url issuer_path.val ⦄ := by
  simp only [transport.auth.prim.issuer_url, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::prim::debug_empty_resource_metadata`**

Always succeeds (the `tracing` event is not modelled). -/
@[step]
theorem debug_empty_resource_metadata_spec :
    transport.auth.prim.debug_empty_resource_metadata ⦃ (_ : Unit) => True ⦄ := by
  simp only [transport.auth.prim.debug_empty_resource_metadata, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::prim::debug_unparsable_resource_metadata`**

Always succeeds (the `tracing` event is not modelled). -/
@[step]
theorem debug_unparsable_resource_metadata_spec (value : Str) (error : url.parser.ParseError) :
    transport.auth.prim.debug_unparsable_resource_metadata value error
      ⦃ (_ : Unit) => True ⦄ := by
  simp only [transport.auth.prim.debug_unparsable_resource_metadata, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::prim::warn_downgraded_resource_metadata`**

Always succeeds (the `tracing` event is not modelled). -/
@[step]
theorem warn_downgraded_resource_metadata_spec (target base_url : url.Url) :
    transport.auth.prim.warn_downgraded_resource_metadata target base_url
      ⦃ (_ : Unit) => True ⦄ := by
  simp only [transport.auth.prim.warn_downgraded_resource_metadata, WP.spec_ok]

/-- **Spec theorem for `rmcp::transport::auth::prim::warn_disallowed_resource_metadata`**

Always succeeds (the `tracing` event is not modelled). -/
@[step]
theorem warn_disallowed_resource_metadata_spec (target base_url : url.Url) :
    transport.auth.prim.warn_disallowed_resource_metadata target base_url
      ⦃ (_ : Unit) => True ⦄ := by
  simp only [transport.auth.prim.warn_disallowed_resource_metadata, WP.spec_ok]

end transport.auth.prim

/-! ## Standard library and `url` -/

open ExtModel

/-- **Spec theorem for `Option::zip`**

Always succeeds: `Some((a, b))` for `Some(a)` and `Some(b)`, otherwise `None`. -/
@[step]
theorem core.option.Option.zip_spec {T U : Type} (self : Option T) (other : Option U) :
    core.option.Option.zip self other ⦃ (result : Option (T × U)) =>
      result = self.bind (fun a => other.map (fun b => (a, b))) ⦄ := by
  cases self <;> cases other <;>
    simp only [core.option.Option.zip, WP.spec_ok, Option.bind_none, Option.bind_some,
      Option.map_none, Option.map_some]

/-- **Spec theorem for `str::eq_ignore_ascii_case`**

Always succeeds: `true` exactly when the bytes agree after mapping `A`–`Z` to `a`–`z`. -/
@[step]
theorem core.str.Str.eq_ignore_ascii_case_spec (self : Str) (other : Str) :
    core.str.Str.eq_ignore_ascii_case self other ⦃ (result : Bool) =>
      (result = true ↔ self.val.map asciiLowercase = other.val.map asciiLowercase) ⦄ := by
  simp only [core.str.Str.eq_ignore_ascii_case, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `<url::Url as Clone>::clone`**

Always succeeds with the same URL. -/
@[step]
theorem url.Url.Insts.CoreCloneClone.clone_spec (self : url.Url) :
    url.Url.Insts.CoreCloneClone.clone self ⦃ (result : url.Url) => result = self ⦄ := by
  simp only [url.Url.Insts.CoreCloneClone.clone, WP.spec_ok]

/-- **Spec theorem for `url::Url::join`**

Always succeeds with the resolution outcome `urlJoin self input.val` (an opaque value). This is
the model; with debug assertions on, Rust can panic for a `file:` base whose last path segment is
a normalized Windows drive letter, joined with an input whose first segment is `..` or a
percent-encoded double dot (stated exception, human decision AD8, docstring of `url.Url.join`;
the condition is a superset description: `file:///C:` joined with `..` does not panic). -/
@[step]
theorem url.Url.join_spec (self : url.Url) (input : Str) :
    url.Url.join self input ⦃ (result : core.result.Result url.Url url.parser.ParseError) =>
      result = urlJoin self input.val ⦄ := by
  simp only [url.Url.join, WP.spec_ok]

/-- **Spec theorem for `url::Url::scheme`**

Always succeeds with the scheme `urlScheme self` (an opaque value). -/
@[step]
theorem url.Url.scheme_spec (self : url.Url) :
    url.Url.scheme self ⦃ (result : Str) => result = urlScheme self ⦄ := by
  simp only [url.Url.scheme, WP.spec_ok]

/-- **Spec theorem for `url::Url::port_or_known_default`**

Always succeeds with the explicit port `urlPort self`, or if there is none the default port of
the scheme `urlScheme self`. -/
@[step]
theorem url.Url.port_or_known_default_spec (self : url.Url) :
    url.Url.port_or_known_default self ⦃ (result : Option Std.U16) =>
      result = (urlPort self).or (defaultPort (urlScheme self).val) ⦄ := by
  unfold url.Url.port_or_known_default
  cases urlPort self <;> simp only [WP.spec_ok, Option.some_or, Option.none_or]

/-- **Spec theorem for `url::Url::path`**

Always succeeds with the path `urlPath self` (an opaque value). -/
@[step]
theorem url.Url.path_spec (self : url.Url) :
    url.Url.path self ⦃ (result : Str) => result = urlPath self ⦄ := by
  simp only [url.Url.path, WP.spec_ok]

/-- **Spec theorem for `url::Url::fragment`**

Always succeeds with the fragment `urlFragment self` (an opaque value). -/
@[step]
theorem url.Url.fragment_spec (self : url.Url) :
    url.Url.fragment self ⦃ (result : Option Str) => result = urlFragment self ⦄ := by
  simp only [url.Url.fragment, WP.spec_ok]

/-- **Spec theorem for `<url::Url as PartialEq>::eq`**

Always succeeds: `true` exactly when the serializations are equal. -/
@[step]
theorem url.Url.Insts.CoreCmpPartialEqUrl.eq_spec (self : url.Url) (other : url.Url) :
    url.Url.Insts.CoreCmpPartialEqUrl.eq self other ⦃ (result : Bool) =>
      (result = true ↔ urlSerialization self = urlSerialization other) ⦄ := by
  simp only [url.Url.Insts.CoreCmpPartialEqUrl.eq, WP.spec_ok, decide_eq_true_eq]

/-! ## Evaluation of the models

Kernel evaluation (`decide`) of the exact models on small inputs; each value is the one Rust
computes (checked against the Rust documentation and the sources cited at each model). -/

namespace Proofs.External.Auth

open Proofs.External.Utf8

/-- `" \t a b\u{a0}\u{3000}\n".trim() == "a b"`: ASCII and multi-byte whitespace at both ends,
the inner space kept. -/
example : trimWhitespace [0x20#u8, 0x09#u8, 0x61#u8, 0x20#u8, 0x62#u8, 0xC2#u8, 0xA0#u8,
    0xE3#u8, 0x80#u8, 0x80#u8, 0x0A#u8] = [0x61#u8, 0x20#u8, 0x62#u8] := by
  decide

/-- `" \u{2028} ".trim() == ""`: only whitespace. -/
example : trimWhitespace [0x20#u8, 0xE2#u8, 0x80#u8, 0xA8#u8, 0x20#u8] = [] := by decide

/-- `"\u{200b}x".trim()` keeps U+200B ZERO WIDTH SPACE (`E2 80 8B`), which is not
`White_Space`; `"\u{1c}x".trim()` keeps U+001C, which `char::is_whitespace` excludes. -/
example : trimWhitespace [0xE2#u8, 0x80#u8, 0x8B#u8, 0x78#u8] = [0xE2#u8, 0x80#u8, 0x8B#u8, 0x78#u8]
    ∧ trimWhitespace [0x1C#u8, 0x78#u8] = [0x1C#u8, 0x78#u8] := by
  decide

/-- `"\u{85}é".trim()` drops U+0085 (`C2 85`) and keeps `é` (`C3 A9`). -/
example : trimWhitespace [0xC2#u8, 0x85#u8, 0xC3#u8, 0xA9#u8] = [0xC3#u8, 0xA9#u8] := by decide

/-- The default ports of `url::parser::default_port`. -/
example : defaultPort (utf8 "http") = some 80#u16 ∧ defaultPort (utf8 "wss") = some 443#u16 ∧
    defaultPort (utf8 "ftp") = some 21#u16 ∧ defaultPort (utf8 "file") = none := by
  have hi : ∀ s t : String, utf8 s = utf8 t ↔ s = t :=
    fun _ _ => ⟨utf8_injective, congrArg utf8⟩
  simp only [defaultPort, hi]
  decide

end Proofs.External.Auth
