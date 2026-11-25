/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Skill
public import Proofs.External.Skill
public import Proofs.External.Std
public import Proofs.External.String
public import Proofs.External.WP
public import Proofs.Model.Skill.Common

@[expose] public section

/-!
# Spec theorems for the builders of `skill.rs` (K01–K05, K07, K08, K10–K12, K17–K20)

The spec theorems of the public functions of `crates/rmcp/src/model/skill.rs` that build or
read values without validating them, the digest function `sha256_digest` (K07), and three
consequences: `from_bytes` as an equation of computations (`SkillResource.from_bytes_eq`), the
well-formedness of a computed digest (`Defs.Skill.isSha256Digest_sha256Digest`) and of the digest
of an entry made from bytes (`SkillResource.isSha256Digest_from_bytes`).

* K01 `Resource::is_directory` (upstream and patched lines 28–30; `DIRECTORY_MIME_TYPE`, line 24);
* K02 `SkillsCapability::new` (lines 46–48), K03 `with_directory_read` (lines 51–54);
* K04 `SkillResource::new` (lines 76–82), K05 `SkillResource::from_bytes` (lines 85–87);
* K07 `sha256_digest` (upstream lines 116–128; patched lines 116–125 and `lower_hex_digit`,
  lines 128–130);
* K08 `SkillFrontmatter::new` (upstream lines 161–167, patched 163–169);
* K10 `Skill::new` (upstream lines 247–258, patched 249–260), K11 `Skill::with_meta` (upstream
  260–263, patched 262–265), K12 `Skill::name` (upstream 266–268, patched 268–270);
* K17–K20 `GetSkillResult::new`, `with_ttl_ms`, `with_cache_scope`, `with_meta` (upstream lines
  488–511, patched 552–575).

The builders are proved by unfolding. `sha256_digest` is proved through the loop over the 32
bytes of the SHA-256 digest (`sha256_digest_loop_spec`): after `k` bytes the string is `sha256:`
followed by the lowercase hexadecimal text of the first `k` bytes (`lowerHex`), and it has at most
`7 + 8 k` bytes, which keeps every `String::push` below `isize::MAX`. Each byte gives two digits
through `lower_hex_digit_spec` (the table lookup of `lower_hex_digit`, checked on its 16 entries
by kernel evaluation). `from_bytes` is proved through `SkillResource.from_bytes_eq`: the `as u64`
cast of a slice length is exact.

Source: "crates/rmcp/src/model/skill.rs", in the patched copy (translation patch 04 on upstream);
line numbers as above.
-/

open Aeneas Aeneas.Std Result
open Defs (utf8Bytes)
open Defs.Skill

/-! ## Helpers -/

namespace Proofs.Model.Skill

open ExtModel Proofs.External.Utf8 Proofs.External.Skill

/-- `isize::MAX` is far above the 71 bytes of a digest (it is at least `2 ^ 31 - 1`). -/
theorem thousand_le_maxStringBytes : 1000 ≤ maxStringBytes := by
  unfold maxStringBytes
  scalar_tac

/-- `x & 0xf` is `x mod 16`. -/
theorem val_and_fifteen (x : U8) : (x &&& 15#u8).val = x.val % 16 := by
  rw [UScalar.val_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 4

/-- The table of `lower_hex_digit` (patched line 129), as characters: `lowerHexDigit`. -/
theorem ofNat_getElem_eq_lowerHexDigit : ∀ (k : Nat) (hk : k < 16),
    Char.ofNat ([48#u8, 49#u8, 50#u8, 51#u8, 52#u8, 53#u8, 54#u8, 55#u8, 56#u8, 57#u8, 97#u8,
      98#u8, 99#u8, 100#u8, 101#u8, 102#u8][k]'hk).val = lowerHexDigit k := by
  decide

/-- The text of the first `k + 1` bytes is that of the first `k` followed by the two digits of
byte `k`. -/
theorem lowerHex_take_add_one (l : List U8) (k : Nat) (hk : k < l.length) :
    lowerHex (l.take (k + 1)) =
      lowerHex (l.take k) ++ String.ofList [lowerHexDigit (l[k].val / 16),
        lowerHexDigit (l[k].val % 16)] := by
  unfold lowerHex
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append,
    String.ofList_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Pushing two characters appends the string of the two. -/
theorem push_push_eq_append (s : String) (a b : Char) :
    (s.push a).push b = s ++ String.ofList [a, b] := by
  rw [String.push_eq_append, String.push_eq_append, String.append_assoc, String.ofList_cons,
    String.ofList_cons, String.ofList_nil, String.append_empty]

/-- Each digit `lowerHexDigit n` (`n < 16`) is one byte. -/
theorem length_map_utf8EncodeChar_lowerHexDigit : ∀ n < 16,
    ((String.utf8EncodeChar (lowerHexDigit n)).map (fun x => byte x.toNat)).length = 1 := by
  decide

/-- The byte of each digit `lowerHexDigit n` (`n < 16`) is a lowercase hexadecimal digit. -/
theorem all_map_utf8EncodeChar_lowerHexDigit : ∀ n < 16,
    ((String.utf8EncodeChar (lowerHexDigit n)).map (fun x => byte x.toNat)).all
      isLowerHexDigit = true := by
  decide

/-- The UTF-8 bytes of `lowerHex l`: the encodings of the two digits of each byte. -/
theorem utf8_lowerHex (l : List U8) :
    utf8 (lowerHex l) = l.flatMap (fun b =>
      (String.utf8EncodeChar (lowerHexDigit (b.val / 16))).map (fun x => byte x.toNat) ++
      (String.utf8EncodeChar (lowerHexDigit (b.val % 16))).map (fun x => byte x.toNat)) := by
  rw [lowerHex, utf8_ofList, List.flatMap_assoc]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The text `lowerHex l` has two bytes per byte of `l`, all lowercase hexadecimal digits. -/
theorem length_utf8_lowerHex_and_all (l : List U8) :
    (utf8 (lowerHex l)).length = 2 * l.length ∧
      (utf8 (lowerHex l)).all isLowerHexDigit = true := by
  rw [utf8_lowerHex]
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih =>
    have hhi : b.val / 16 < 16 := by
      have := Proofs.External.Byte.val_lt b
      omega
    have hlo : b.val % 16 < 16 := Nat.mod_lt _ (by decide)
    rw [List.flatMap_cons, List.length_append, List.length_append, List.all_append,
      List.all_append, length_map_utf8EncodeChar_lowerHexDigit _ hhi,
      length_map_utf8EncodeChar_lowerHexDigit _ hlo, all_map_utf8EncodeChar_lowerHexDigit _ hhi,
      all_map_utf8EncodeChar_lowerHexDigit _ hlo, ih.1, ih.2, List.length_cons]
    exact ⟨by omega, rfl⟩

end Proofs.Model.Skill

/-! ## K07: `sha256_digest` -/

namespace rmcp.model.skill

open Proofs.Model.Skill

/-- `lower_hex_digit` (patched lines 128–130): the lowercase hexadecimal digit of the low nibble
(`HEX[(nibble & 0xf) as usize] as char`). -/
theorem lower_hex_digit_spec (nibble : U8) :
    lower_hex_digit nibble ⦃ (c : Char) => c = lowerHexDigit (nibble.val % 16) ⦄ := by
  have hand : (core.convert.num.FromUsizeU8.from (nibble &&& 15#u8)).val = nibble.val % 16 := by
    rw [core.convert.num.FromUsizeU8.from_val_eq, val_and_fifteen]
  have hlt : nibble.val % 16 < 16 := Nat.mod_lt _ (by decide)
  unfold lower_hex_digit
  simp only [lift, bind_ok]
  step with Array.index_usize_spec as ⟨b, hb⟩
  step as ⟨c, hc⟩
  rw [hc, hb]
  simp only [hand, Array.make]
  exact ofNat_getElem_eq_lowerHexDigit _ hlt

/-- The loop of `sha256_digest` (patched lines 120–123): from the iterator at byte `k` of the
digest, with the string `sha256:` followed by the text of the first `k` bytes, it returns
`sha256:` followed by the text of all 32 bytes. -/
theorem sha256_digest_loop_spec (iter : core.array.iter.IntoIter U8 32#usize) (digest : String)
    (h_end : iter.aliveEnd = 32)
    (h_digest : digest = "sha256:" ++ lowerHex (iter.data.val.take iter.aliveStart))
    (h_size : digest.utf8ByteSize ≤ 7 + 8 * iter.aliveStart) :
    sha256_digest_loop iter digest ⦃ (result : String) =>
      result = "sha256:" ++ lowerHex iter.data.val ⦄ := by
  have hlen : iter.data.val.length = 32 := iter.data.property
  unfold sha256_digest_loop
  apply loop.spec_decr_nat (measure := fun x : core.array.iter.IntoIter U8 32#usize × String =>
      32 - x.1.aliveStart)
    (inv := fun x => x.1.data = iter.data ∧ x.1.aliveEnd = 32 ∧
      x.2 = "sha256:" ++ lowerHex (iter.data.val.take x.1.aliveStart) ∧
      x.2.utf8ByteSize ≤ 7 + 8 * x.1.aliveStart)
  · rintro ⟨it, d⟩ ⟨hdata, hend, hd, hsize⟩
    dsimp only at hdata hend hd hsize
    unfold sha256_digest_loop.body
    step as ⟨o, it1, o_post⟩
    rcases o_post with ⟨hlt, ho, hdata1, hstart1, hend1⟩ | ⟨hge, ho, _⟩
    · subst ho
      have hk : it.aliveStart < iter.data.val.length := by omega
      have hb : it.data.val[it.aliveStart]! = iter.data.val[it.aliveStart] := by
        rw [hdata, getElem!_pos iter.data.val it.aliveStart hk]
      have hbyte := Proofs.External.Byte.val_lt iter.data.val[it.aliveStart]
      have hc4 := Char.utf8Size_le_four
      have hmax := thousand_le_maxStringBytes
      simp only [hb]
      step as ⟨i, i_post, _⟩
      step with lower_hex_digit_spec as ⟨c, c_post⟩
      have h1 : d.utf8ByteSize + c.utf8Size ≤ ExtModel.maxStringBytes := by
        have := hc4 c
        omega
      step with alloc.string.String.push_spec d c h1 as ⟨digest1, digest1_post, _⟩
      step as ⟨i1, i1_post, _⟩
      step with lower_hex_digit_spec as ⟨c1, c1_post⟩
      have h2 : digest1.utf8ByteSize + c1.utf8Size ≤ ExtModel.maxStringBytes := by
        have := hc4 c
        have := hc4 c1
        rw [digest1_post, String.utf8ByteSize_push]
        omega
      step with alloc.string.String.push_spec digest1 c1 h2 as ⟨digest2, digest2_post, _⟩
      have hhi : i.val % 16 = iter.data.val[it.aliveStart].val / 16 := by
        rw [i_post, Nat.shiftRight_eq_div_pow]
        omega
      have hlo : i1.val % 16 = iter.data.val[it.aliveStart].val % 16 := by
        rw [i1_post, val_and_fifteen, Nat.mod_mod]
      refine ⟨by rw [hdata1, hdata], by rw [hend1, hend], ?_, ?_, by omega⟩
      · rw [digest2_post, digest1_post, push_push_eq_append, hd, String.append_assoc, hstart1,
          lowerHex_take_add_one _ _ hk, c_post, c1_post, hhi, hlo]
      · rw [digest2_post, digest1_post, String.utf8ByteSize_push, String.utf8ByteSize_push,
          hstart1]
        have := hc4 c
        have := hc4 c1
        omega
    · subst ho
      simp only [WP.spec_ok]
      rw [hd, List.take_of_length_le (by omega)]
  · exact ⟨rfl, h_end, h_digest, h_size⟩

/-- **Spec theorem for `rmcp::model::skill::sha256_digest`** (K07)

`sha256:` followed by the 64 lowercase hexadecimal digits of the SHA-256 digest of `bytes`
(`sha256Digest`, with `ExtModel.sha256` unopened; upstream lines 116–128, patched lines 116–125
and `lower_hex_digit`, lines 128–130, hunk H1). No premise. Not covered: (S). -/
@[step]
theorem sha256_digest_spec (bytes : Slice U8) :
    sha256_digest bytes ⦃ (result : String) => result = sha256Digest bytes.val ⦄ := by
  have hmax := thousand_le_maxStringBytes
  unfold sha256_digest
  step as ⟨hash, hash_post⟩
  step as ⟨n, n_post⟩
  step with alloc.string.String.with_capacity_spec as ⟨s0, s0_post⟩
  step with alloc.string.String.push_str_spec s0 _ "sha256:" (Proofs.External.Utf8.toStr_val _ _)
    as ⟨s1, s1_post, _⟩
  case h =>
    rw [s0_post, Proofs.External.Utf8.toStr_val, Proofs.External.Utf8.length_utf8]
    have : ("" : String).utf8ByteSize + "sha256:".utf8ByteSize = 7 := by decide
    omega
  step as ⟨it, it_data, it_start, it_end⟩
  have h_digest : s1 = "sha256:" ++ lowerHex (it.data.val.take it.aliveStart) := by
    rw [s1_post, s0_post, it_start, List.take_zero]
    rfl
  have h_size : s1.utf8ByteSize ≤ 7 + 8 * it.aliveStart := by
    rw [s1_post, s0_post, it_start]
    decide
  step with sha256_digest_loop_spec it s1 it_end h_digest h_size as ⟨r, hr⟩
  rw [hr, it_data, hash_post]
  rfl

/-! ## `from_bytes` as an equation (`K05 (K07)`) -/

/-- **`from_bytes` is `new` with the computed digest and length** (`K05 (K07)`): for any `U64`
`size` of value `bytes.len()`, `from_bytes uri bytes` is the computation that converts `uri`
(`uri.into()`) and returns the entry with that URI, the digest `sha256Digest bytes` and size
`size`; this is `SkillResource::new(uri, sha256_digest(bytes), bytes.len() as u64)` (upstream
and patched lines 85–87; the construction of K04) with the digest conversion `String → String`
the identity. An equality of computations: it holds whatever the caller's conversion does (both
sides call it once, on `uri`), so it has no caller-code premise. Not covered: (S). -/
theorem SkillResource.from_bytes_eq {UriLike : Type}
    (uriInto : core.convert.Into UriLike String) (uri : UriLike) (bytes : Slice U8)
    (size : U64) (h_size : size.val = bytes.val.length) :
    SkillResource.from_bytes uriInto uri bytes =
      (do
        let u ← uriInto.into uri
        ok ({ uri := u, digest := sha256Digest bytes.val, size := size } : SkillResource)) := by
  obtain ⟨d, hd, hdv⟩ := Proofs.External.WP.exists_ok_of_spec (sha256_digest_spec bytes)
  have hcast : UScalar.cast .U64 (Slice.len bytes) = size := by
    apply UScalar.eq_of_val_eq
    rw [Proofs.RequestStateWire.val_cast_u64, Slice.len_val, h_size]
  unfold SkillResource.from_bytes SkillResource.new
  simp only [hd, bind_ok, lift, hcast, hdv, core.convert.IntoFrom.into,
    core.convert.FromSame.from]

end rmcp.model.skill

/-! ## K01: `Resource::is_directory` -/

namespace rmcp.model.skill.Resource

/-- **Spec theorem for `rmcp::model::skill::Resource::is_directory`** (K01)

`true` exactly when the MIME type is `Some("inode/directory")` (`DIRECTORY_MIME_TYPE`, upstream
line 24; `self.mime_type.as_deref() == Some(DIRECTORY_MIME_TYPE)`, upstream and patched lines
28–30). Premise (Z) on the MIME type. -/
@[step]
theorem is_directory_spec (self : rmcp.model.resource.Resource)
    (h_mime_fits : ∀ t, self.mime_type = some t → UsizeFits t) :
    is_directory self ⦃ (result : Bool) =>
      (result = true ↔ self.mime_type = some "inode/directory") ⦄ := by
  unfold is_directory
  cases hm : self.mime_type with
  | none =>
    simp only [core.option.Option.as_deref, bind_ok,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq, WP.spec_ok, Bool.false_eq_true,
      reduceCtorEq]
  | some t =>
    obtain ⟨r, hr, hrv⟩ := Proofs.External.WP.exists_ok_of_spec
      (alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec t (h_mime_fits t hm))
    simp only [core.option.Option.as_deref, hr, bind_ok,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.cmp.impls.PartialEqShared.eq,
      Str.Insts.CoreCmpPartialEqStr.eq_eq, WP.spec_ok, decide_eq_true_eq, Option.some.injEq]
    rw [hrv, DIRECTORY_MIME_TYPE, Proofs.External.Utf8.toStr_val]
    exact ⟨Proofs.External.Utf8.utf8_injective, fun h => h ▸ rfl⟩

end rmcp.model.skill.Resource

/-! ## K02, K03: `SkillsCapability` -/

namespace rmcp.model.skill.SkillsCapability

/-- **Spec theorem for `rmcp::model::skill::SkillsCapability::new`** (K02)

The capability without directory reads (`Self::default()`, upstream and patched lines 46–48; the
derived `Default`, line 34, gives `directory_read: false`). -/
@[step]
theorem new_spec :
    new ⦃ (result : SkillsCapability) => result.directory_read = false ⦄ := by
  simp only [new, Insts.CoreDefaultDefault.default, core.default.DefaultBool.default, bind_ok,
    WP.spec_ok]

/-- **Spec theorem for `rmcp::model::skill::SkillsCapability::with_directory_read`** (K03)

Sets `directory_read` to `true` (upstream and patched lines 51–54); it is the only field of
`SkillsCapability` (lines 38–42), so calling it twice gives the same value as once. -/
@[step]
theorem with_directory_read_spec (self : SkillsCapability) :
    with_directory_read self ⦃ (result : SkillsCapability) => result.directory_read = true ⦄ := by
  simp only [with_directory_read, WP.spec_ok]

end rmcp.model.skill.SkillsCapability

/-! ## K04, K05: `SkillResource` -/

namespace rmcp.model.skill.SkillResource

/-- **Spec theorem for `rmcp::model::skill::SkillResource::new`** (K04)

The entry with URI `u = uri.into()`, digest `d = digest.into()` and the given size, unchecked
(upstream and patched lines 76–82; the conversions in this order). Premise: caller code. Not
covered: (I). -/
@[step]
theorem new_spec {UriLike DigestLike : Type} (uriInto : core.convert.Into UriLike String)
    (digestInto : core.convert.Into DigestLike String) (uri : UriLike) (digest : DigestLike)
    (size : U64) (u d : String) (h_uri_into : uriInto.into uri = ok u)
    (h_digest_into : digestInto.into digest = ok d) :
    new uriInto digestInto uri digest size ⦃ (result : SkillResource) =>
      result.uri = u ∧
      result.digest = d ∧
      result.size = size ⦄ := by
  simp only [new, h_uri_into, h_digest_into, bind_ok, WP.spec_ok, and_self]

/-- **Spec theorem for `rmcp::model::skill::SkillResource::from_bytes`** (K05)

The entry for `bytes` at URI `u = uri.into()`: its digest is `sha256Digest bytes` (K07) and its
size the byte length (`Self::new(uri, sha256_digest(bytes), bytes.len() as u64)`, upstream and
patched lines 85–87; `as u64` is exact, `usize` having at most 64 bits). Premise: caller code. Not
covered: (I), (S). -/
@[step]
theorem from_bytes_spec {UriLike : Type} (uriInto : core.convert.Into UriLike String)
    (uri : UriLike) (bytes : Slice U8) (u : String) (h_uri_into : uriInto.into uri = ok u) :
    from_bytes uriInto uri bytes ⦃ (result : SkillResource) =>
      result.uri = u ∧
      result.digest = sha256Digest bytes.val ∧
      result.size.val = bytes.val.length ⦄ := by
  have hlen : (UScalar.cast .U64 (Slice.len bytes)).val = bytes.val.length := by
    rw [Proofs.RequestStateWire.val_cast_u64, Slice.len_val]
  rw [from_bytes_eq uriInto uri bytes _ hlen, h_uri_into, bind_ok, WP.spec_ok]
  exact ⟨rfl, rfl, hlen⟩

end rmcp.model.skill.SkillResource

/-! ## K08: `SkillFrontmatter::new` -/

namespace rmcp.model.skill.SkillFrontmatter

/-- **Spec theorem for `rmcp::model::skill::SkillFrontmatter::new`** (K08)

The frontmatter with name `n = name.into()`, description `d = description.into()` and no other
field (`JsonObject::new()`; upstream lines 161–167, patched lines 163–169). The empty map is
sorted (`KeysSorted`), as K09 then keeps it. Premise: caller code. Not covered: (I). -/
@[step]
theorem new_spec {NameLike DescriptionLike : Type} (nameInto : core.convert.Into NameLike String)
    (descriptionInto : core.convert.Into DescriptionLike String) («name» : NameLike)
    (description : DescriptionLike) (n d : String) (h_name_into : nameInto.into «name» = ok n)
    (h_description_into : descriptionInto.into description = ok d) :
    new nameInto descriptionInto «name» description ⦃ (result : SkillFrontmatter) =>
      result.«name» = n ∧
      result.description = d ∧
      result.extra.entries = [] ⦄ := by
  simp only [new, h_name_into, h_description_into, serde_json.map.MapStringValue.new, bind_ok,
    WP.spec_ok, and_self]

end rmcp.model.skill.SkillFrontmatter

/-! ## K10–K12: `Skill` -/

namespace rmcp.model.skill.Skill

/-- **Spec theorem for `rmcp::model::skill::Skill::new`** (K10)

The skill with URI `u = uri.into()`, the given frontmatter and resources, and no `_meta`,
unchecked (upstream lines 247–258, patched lines 249–260). It fixes all four fields of `Skill`.
Premise: caller code. Not covered: (I). -/
@[step]
theorem new_spec {UriLike : Type} (uriInto : core.convert.Into UriLike String) (uri : UriLike)
    (frontmatter : SkillFrontmatter) (resources : SkillResources) (u : String)
    (h_uri_into : uriInto.into uri = ok u) :
    new uriInto uri frontmatter resources ⦃ (result : Skill) =>
      result.uri = u ∧
      result.frontmatter = frontmatter ∧
      result.resources = resources ∧
      result.«meta» = none ⦄ := by
  simp only [new, h_uri_into, bind_ok, WP.spec_ok, and_self]

/-- **Spec theorem for `rmcp::model::skill::Skill::with_meta`** (K11)

Sets `_meta` to `Some(meta)`; the other fields are unchanged (upstream lines 260–263, patched
lines 262–265). So of two calls the last one wins, and `validate` does not see the change
(`Skill.validate_with_meta`). -/
@[step]
theorem with_meta_spec (self : Skill) (m : rmcp.model.meta.MetaObject) :
    with_meta self m ⦃ (result : Skill) =>
      result.uri = self.uri ∧
      result.frontmatter = self.frontmatter ∧
      result.resources = self.resources ∧
      result.«meta» = some m ⦄ := by
  simp only [with_meta, WP.spec_ok, and_self]

/-- **Spec theorem for `rmcp::model::skill::Skill::name`** (K12)

The frontmatter name, as its UTF-8 bytes (`&self.frontmatter.name`, upstream lines 266–268,
patched lines 268–270). Premise (Z) on the name. -/
@[step]
theorem name_spec (self : Skill) (h_name_fits : UsizeFits self.frontmatter.«name») :
    Skill.name self ⦃ (result : Str) => result.val = utf8Bytes self.frontmatter.«name» ⦄ := by
  unfold Skill.name
  exact alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec _ h_name_fits

end rmcp.model.skill.Skill

/-! ## K17–K20: `GetSkillResult` -/

namespace rmcp.model.skill.GetSkillResult

/-- **Spec theorem for `rmcp::model::skill::GetSkillResult::new`** (K17)

The result for `skill`, marked complete (`result_type: Some(ResultType::COMPLETE)`, the borrowed
string `"complete"`, `model.rs` line 1033 upstream, 1035 patched), with no TTL, no cache scope
and no `_meta` (upstream lines 488–496, patched lines 552–560). It fixes all five fields; K18–K20
each set one of them and keep the others, so they commute with each other, and of two calls of
the same one the last wins. -/
@[step]
theorem new_spec (skill : Skill) :
    new skill ⦃ (result : GetSkillResult) =>
      result.result_type = some rmcp.model.ResultType.COMPLETE ∧
      result.ttl_ms = none ∧
      result.cache_scope = none ∧
      result.skill = skill ∧
      result.«meta» = none ⦄ := by
  simp only [new, WP.spec_ok, and_self]

/-- **Spec theorem for `rmcp::model::skill::GetSkillResult::with_ttl_ms`** (K18)

Sets `ttl_ms` to `Some(ttl_ms)`; the other fields are unchanged (upstream lines 498–501, patched
lines 562–565). It commutes with K19 and K20; of two calls the last wins. -/
@[step]
theorem with_ttl_ms_spec (self : GetSkillResult) (ttl_ms : U64) :
    with_ttl_ms self ttl_ms ⦃ (result : GetSkillResult) =>
      result.result_type = self.result_type ∧
      result.ttl_ms = some ttl_ms ∧
      result.cache_scope = self.cache_scope ∧
      result.skill = self.skill ∧
      result.«meta» = self.«meta» ⦄ := by
  simp only [with_ttl_ms, WP.spec_ok, and_self]

/-- **Spec theorem for `rmcp::model::skill::GetSkillResult::with_cache_scope`** (K19)

Sets `cache_scope` to `Some(cache_scope)`; the other fields are unchanged (upstream lines
503–506, patched lines 567–570). It commutes with K18 and K20; of two calls the last wins. -/
@[step]
theorem with_cache_scope_spec (self : GetSkillResult) (cache_scope : rmcp.model.CacheScope) :
    with_cache_scope self cache_scope ⦃ (result : GetSkillResult) =>
      result.result_type = self.result_type ∧
      result.ttl_ms = self.ttl_ms ∧
      result.cache_scope = some cache_scope ∧
      result.skill = self.skill ∧
      result.«meta» = self.«meta» ⦄ := by
  simp only [with_cache_scope, WP.spec_ok, and_self]

/-- **Spec theorem for `rmcp::model::skill::GetSkillResult::with_meta`** (K20)

Sets `_meta` to `Some(meta)`; the other fields are unchanged (upstream lines 508–511, patched
lines 572–575). It commutes with K18 and K19; of two calls the last wins. -/
@[step]
theorem with_meta_spec (self : GetSkillResult) (m : rmcp.model.meta.MetaObject) :
    with_meta self m ⦃ (result : GetSkillResult) =>
      result.result_type = self.result_type ∧
      result.ttl_ms = self.ttl_ms ∧
      result.cache_scope = self.cache_scope ∧
      result.skill = self.skill ∧
      result.«meta» = some m ⦄ := by
  simp only [with_meta, WP.spec_ok, and_self]

end rmcp.model.skill.GetSkillResult

/-! ## Well-formed digests (model, `K05 (model)`) -/

namespace Defs.Skill

open ExtModel Proofs.External.Utf8 Proofs.Model.Skill

/-- **A computed digest is well-formed**: `sha256Digest` of any bytes passes `isSha256Digest`. In
particular it is 71 ASCII bytes: `sha256:` and 64 lowercase hexadecimal digits. -/
theorem isSha256Digest_sha256Digest (bytes : List U8) :
    isSha256Digest (utf8Bytes (sha256Digest bytes)) = true := by
  have hlen : (ExtModel.sha256 bytes).val.length = 32 := (ExtModel.sha256 bytes).property
  have h := length_utf8_lowerHex_and_all (ExtModel.sha256 bytes).val
  rw [hlen] at h
  have hp : (utf8 "sha256:").isPrefixOf (utf8 "sha256:" ++ utf8 (lowerHex (sha256 bytes).val)) =
      true := List.isPrefixOf_iff_prefix.2 (List.prefix_append _ _)
  rw [isSha256Digest, sha256Digest, utf8Bytes_eq_utf8, utf8_append, stripPrefix,
    utf8Bytes_eq_utf8]
  simp only [hp, ↓reduceIte, List.drop_left, h.1, h.2]
  rfl

end Defs.Skill

namespace rmcp.model.skill

/-- **An entry made from bytes has a well-formed digest** (K05 then the model, `K05 (model)`): the
digest of the entry that `from_bytes` returns passes `isSha256Digest`, so `validate` never reports
`MalformedDigest` for it (`Defs.Skill.firstFileFault_ne_malformedDigest`). Premise: caller code. Not
covered: (I), (S). -/
theorem SkillResource.isSha256Digest_from_bytes {UriLike : Type}
    (uriInto : core.convert.Into UriLike String) (uri : UriLike) (bytes : Slice U8) (u : String)
    (h_uri_into : uriInto.into uri = ok u) :
    SkillResource.from_bytes uriInto uri bytes ⦃ (entry : SkillResource) =>
      isSha256Digest (utf8Bytes entry.digest) = true ⦄ := by
  step with SkillResource.from_bytes_spec uriInto uri bytes u h_uri_into as ⟨entry, _, h_digest, _⟩
  rw [h_digest]
  exact isSha256Digest_sha256Digest bytes.val

end rmcp.model.skill
