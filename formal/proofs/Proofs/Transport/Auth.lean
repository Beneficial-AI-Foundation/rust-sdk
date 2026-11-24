/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Net
import Proofs.External.Net
import Proofs.External.Std

/-!
# Spec theorems for the SSRF address guard of `AuthorizationManager` (A01–A03, C04)

`is_disallowed_metadata_ipv4` (A02) tests an IPv4 address against the blocked ranges with the
`std` predicates and three octet tests; `embedded_ipv4` (A01) decodes an IPv4 address carried in
an IPv4-mapped, NAT64, IPv4-compatible or 6to4 IPv6 address; `is_disallowed_metadata_ipv6` (A03)
returns A02 of the carried address if there is one, and otherwise tests the IPv6 blocked ranges.
The composition theorem C04 and its corollary combine them: a blocked IPv4 address stays blocked
in any of the four embedding forms.

Each spec theorem is proved against the independent definitions of `Defs.Net` through the
`core::net` model laws (`Proofs/External/Net.lean`, `Proofs/External/Std.lean`). The helper
lemmas reduce the prefix tests of `Defs.Net` to conditions on the octets or segments
(`ipv4Disallowed_eq_decide_octets`, `embeddedIpv4_of_segments`,
`ipv6DisallowedPrefixes_any_eq_decide`), which `omega` then compares with the code's tests.

Source: "crates/rmcp/src/transport/auth.rs", lines 1343–1383 at upstream `7caec76` (not touched
by patch 01)
-/

open Aeneas Aeneas.Std Result

namespace Proofs.Transport.Auth

open Defs.Net

/-! ## Values of octets and segments -/

/-- The value of eight segments, most significant first. -/
theorem ipv6Value_eight_segments (s0 s1 s2 s3 s4 s5 s6 s7 : U16) :
    ipv6Value [s0, s1, s2, s3, s4, s5, s6, s7] =
      s0.val * 2^112 + s1.val * 2^96 + s2.val * 2^80 + s3.val * 2^64 + s4.val * 2^48 +
      s5.val * 2^32 + s6.val * 2^16 + s7.val := by
  simp only [ipv6Value, ofBigEndianDigits, List.map, List.foldl]
  ring

/-- A `u8` value is below `256`. -/
theorem u8_val_lt (x : U8) : x.val < 256 := by scalar_tac

/-- A `u16` value is below `65536`. -/
theorem u16_val_lt (x : U16) : x.val < 65536 := by scalar_tac

/-- The value of a `u8` literal pattern. -/
theorem u8_mk_ofNat_val (k : Nat) :
    (@UScalar.mk UScalarTy.U8 (BitVec.ofNat 8 k)).val = k % 256 := by
  simp [UScalar.val]

/-- The value of a `u16` literal pattern (`0#uscalar` in the match arms of A01). -/
theorem u16_mk_ofNat_val (k : Nat) :
    (@UScalar.mk UScalarTy.U16 (BitVec.ofNat 16 k)).val = k % 65536 := by
  simp [UScalar.val]

/-- `(u32::from(x) << 16) | u32::from(y)` is `x · 2^16 + y`. -/
theorem or_from_val_eq (i : U32) (x y : U16) (hi : i.val = x.val <<< 16 % U32.size) :
    (i ||| core.convert.num.FromU32U16.from y).val = x.val * 2^16 + y.val := by
  have bx := u16_val_lt x
  have byy := u16_val_lt y
  rw [UScalar.val_or, core.convert.num.FromU32U16.from_val_eq]
  have : i.val = x.val <<< 16 := by
    rw [hi, Nat.shiftLeft_eq, U32.size_eq]
    omega
  rw [this, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]

/-- An address whose octets are the big-endian bytes of `ip` has value `ip`. -/
theorem ipv4Value_eq_of_octets_map (ip : U32) (r : core.net.ip_addr.Ipv4Addr)
    (h : r.addrOctets.val.map (fun o => o.val) =
      [ip.val / 2 ^ 24, ip.val / 2 ^ 16 % 256, ip.val / 2 ^ 8 % 256, ip.val % 256]) :
    ipv4Value r.addrOctets.val = ip.val := by
  have : ip.val < 2^32 := by scalar_tac
  rw [ipv4Value, h]
  simp only [ofBigEndianDigits, List.foldl]
  omega

/-- `Ipv6Addr::is_loopback` as a value: the address is `::1`. From the law
`core.net.ip_addr.Ipv6Addr.is_loopback_spec`. -/
theorem is_loopback_eq_ok (addr : core.net.ip_addr.Ipv6Addr) (s0 s1 s2 s3 s4 s5 s6 s7 : U16)
    (h : addr.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7]) :
    core.net.ip_addr.Ipv6Addr.is_loopback addr = ok (decide (s0.val = 0 ∧ s1.val = 0 ∧
      s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧ s5.val = 0 ∧ s6.val = 0 ∧ s7.val = 1)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
    (core.net.ip_addr.Ipv6Addr.is_loopback_spec addr s0 s1 s2 s3 s4 s5 s6 s7 h)
  rw [hr, ok.injEq, Bool.eq_iff_iff, hp, decide_eq_true_eq]

/-- `Ipv6Addr::is_unspecified` as a value: the address is `::`. From the law
`core.net.ip_addr.Ipv6Addr.is_unspecified_spec`. -/
theorem is_unspecified_eq_ok (addr : core.net.ip_addr.Ipv6Addr) (s0 s1 s2 s3 s4 s5 s6 s7 : U16)
    (h : addr.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7]) :
    core.net.ip_addr.Ipv6Addr.is_unspecified addr = ok (decide (s0.val = 0 ∧ s1.val = 0 ∧
      s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧ s5.val = 0 ∧ s6.val = 0 ∧ s7.val = 0)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
    (core.net.ip_addr.Ipv6Addr.is_unspecified_spec addr s0 s1 s2 s3 s4 s5 s6 s7 h)
  rw [hr, ok.injEq, Bool.eq_iff_iff, hp, decide_eq_true_eq]

/-! ## Masks -/

/-- Masking with `(2^k - 1) * 2^j` keeps bits `j` to `j + k - 1`. -/
theorem and_mask_eq (n k j : Nat) :
    n &&& ((2 ^ k - 1) * 2 ^ j) = n / 2 ^ j % 2 ^ k * 2 ^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : j ≤ i
  · have : i - j + j = i := by omega
    simp [hi, this, Bool.and_comm]
  · simp [hi]

/-- The link-local test of A03: `s & 0xffc0 == 0xfe80` iff `s / 64 = 1018`. -/
theorem and_65472_eq_65152_iff (s : U16) :
    (s &&& 65472#u16 = 65152#u16) ↔ s.val / 64 = 1018 := by
  have hs : s.val < 65536 := by scalar_tac
  rw [UScalar.eq_equiv, UScalar.val_and]
  rw [show (65472#u16).val = (2 ^ 10 - 1) * 2 ^ 6 from rfl, and_mask_eq,
    show (65152#u16).val = 65152 from rfl]
  omega

/-- The unique-local test of A03: `s & 0xfe00 == 0xfc00` iff `s / 512 = 126`. -/
theorem and_65024_eq_64512_iff (s : U16) :
    (s &&& 65024#u16 = 64512#u16) ↔ s.val / 512 = 126 := by
  have hs : s.val < 65536 := by scalar_tac
  rw [UScalar.eq_equiv, UScalar.val_and]
  rw [show (65024#u16).val = (2 ^ 7 - 1) * 2 ^ 9 from rfl, and_mask_eq,
    show (64512#u16).val = 64512 from rfl]
  omega

/-! ## Normal forms of the `Defs.Net` predicates -/

/-- The IPv4-mapped prefix `::ffff:0:0/96` as an explicit `Prefix` (width, base, length). -/
theorem ipv4Mapped_eq : ipv4Mapped = ⟨128, 281470681743360, 96⟩ := by decide

/-- The NAT64 well-known prefix `64:ff9b::/96` as an explicit `Prefix` (width, base, length). -/
theorem nat64WellKnown_eq : nat64WellKnown = ⟨128, 0x64 * 2^112 + 0xff9b * 2^96, 96⟩ := by
  decide

/-- The IPv4-compatible prefix `::/96` as an explicit `Prefix` (width, base, length). -/
theorem ipv4Compatible_eq : ipv4Compatible = ⟨128, 0, 96⟩ := by decide

/-- The 6to4 prefix `2002::/16` as an explicit `Prefix` (width, base, length). -/
theorem sixToFour_eq : sixToFour = ⟨128, 0x2002 * 2^112, 16⟩ := by decide

/-- `embeddedIpv4` as a condition on eight segments. -/
theorem embeddedIpv4_of_segments (s0 s1 s2 s3 s4 s5 s6 s7 : Nat) (h0 : s0 < 65536)
    (h1 : s1 < 65536) (h2 : s2 < 65536) (h3 : s3 < 65536) (h4 : s4 < 65536) (h5 : s5 < 65536)
    (h6 : s6 < 65536) (h7 : s7 < 65536) (V : Nat) (hV : V = s0 * 2^112 + s1 * 2^96 +
      s2 * 2^80 + s3 * 2^64 + s4 * 2^48 + s5 * 2^32 + s6 * 2^16 + s7) :
    embeddedIpv4 V =
      if (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 65535) ∨
          (s0 = 100 ∧ s1 = 65435 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0) then
        some (s6 * 2^16 + s7)
      else if s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧
          ¬ (s6 = 0 ∧ s7 = 0) ∧ ¬ (s6 = 0 ∧ s7 = 1) then
        some (s6 * 2^16 + s7)
      else if s0 = 8194 then some (s1 * 2^16 + s2)
      else none := by
  have hm : inPrefix ipv4Mapped V =
      decide (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 65535) := by
    rw [ipv4Mapped_eq, Bool.eq_iff_iff]
    simp only [inPrefix, beq_iff_eq, decide_eq_true_eq]
    norm_num
    omega
  have hn : inPrefix nat64WellKnown V =
      decide (s0 = 100 ∧ s1 = 65435 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0) := by
    rw [nat64WellKnown_eq, Bool.eq_iff_iff]
    simp only [inPrefix, beq_iff_eq, decide_eq_true_eq]
    norm_num
    omega
  have hc : inPrefix ipv4Compatible V =
      decide (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0) := by
    rw [ipv4Compatible_eq, Bool.eq_iff_iff]
    simp only [inPrefix, beq_iff_eq, decide_eq_true_eq]
    norm_num
    omega
  have h6 : inPrefix sixToFour V = decide (s0 = 8194) := by
    rw [sixToFour_eq, Bool.eq_iff_iff]
    simp only [inPrefix, beq_iff_eq, decide_eq_true_eq]
    norm_num
    omega
  have hlow : V % 2^32 = s6 * 2^16 + s7 := by omega
  have hmid : V / 2^80 % 2^32 = s1 * 2^16 + s2 := by omega
  have h00 : (V != 0) = decide ¬ (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧
      s6 = 0 ∧ s7 = 0) := by
    rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; omega
  have h01 : (V != 1) = decide ¬ (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧
      s6 = 0 ∧ s7 = 1) := by
    rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; omega
  simp only [embeddedIpv4, hm, hn, hc, h6, hlow, hmid, h00, h01]
  split_ifs <;> simp_all; omega

/-- Membership in an IPv4 prefix, for `V` given by its octets: a prefix test on `V`
rewritten as a condition `P` on the octets. -/
theorem inPrefix_ipv4Prefix_eq_decide (a b c d len : Nat) (V : Nat) (P : Prop) [Decidable P]
    (h : V / 2 ^ (32 - len) = ofBigEndianDigits 256 [a, b, c, d] / 2 ^ (32 - len) ↔ P) :
    inPrefix (ipv4Prefix a b c d len) V = decide P := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, ← h]
  simp [inPrefix, ipv4Prefix]

/-- `ipv4Disallowed` as a condition on four octets, one disjunct per range (each range is
reduced by its own `omega` call; one call over the whole disjunction is too slow). -/
theorem ipv4Disallowed_eq_decide_octets (o0 o1 o2 o3 : Nat) (h0 : o0 < 256) (h1 : o1 < 256)
    (h2 : o2 < 256) (h3 : o3 < 256) (V : Nat)
    (hV : V = o0 * 2^24 + o1 * 2^16 + o2 * 2^8 + o3) :
    ipv4Disallowed V = decide (o0 = 10 ∨ (o0 = 172 ∧ o1 / 16 = 1) ∨
      (o0 = 192 ∧ o1 = 168) ∨ o0 = 127 ∨ (o0 = 169 ∧ o1 = 254) ∨
      (o0 = 255 ∧ o1 = 255 ∧ o2 = 255 ∧ o3 = 255) ∨
      (o0 = 0 ∧ o1 = 0 ∧ o2 = 0 ∧ o3 = 0) ∨ o0 / 16 = 14 ∨ o0 = 0 ∨
      (o0 = 100 ∧ o1 / 64 = 1) ∨ (o0 = 198 ∧ o1 / 2 = 9)) := by
  have e1 := inPrefix_ipv4Prefix_eq_decide 10 0 0 0 8 V (o0 = 10)
    (by simp [ofBigEndianDigits]; omega)
  have e2 := inPrefix_ipv4Prefix_eq_decide 172 16 0 0 12 V (o0 = 172 ∧ o1 / 16 = 1)
    (by simp [ofBigEndianDigits]; omega)
  have e3 := inPrefix_ipv4Prefix_eq_decide 192 168 0 0 16 V (o0 = 192 ∧ o1 = 168)
    (by simp [ofBigEndianDigits]; omega)
  have e4 := inPrefix_ipv4Prefix_eq_decide 127 0 0 0 8 V (o0 = 127)
    (by simp [ofBigEndianDigits]; omega)
  have e5 := inPrefix_ipv4Prefix_eq_decide 169 254 0 0 16 V (o0 = 169 ∧ o1 = 254)
    (by simp [ofBigEndianDigits]; omega)
  have e6 := inPrefix_ipv4Prefix_eq_decide 255 255 255 255 32 V
    (o0 = 255 ∧ o1 = 255 ∧ o2 = 255 ∧ o3 = 255) (by simp [ofBigEndianDigits]; omega)
  have e7 := inPrefix_ipv4Prefix_eq_decide 0 0 0 0 32 V (o0 = 0 ∧ o1 = 0 ∧ o2 = 0 ∧ o3 = 0)
    (by simp [ofBigEndianDigits]; omega)
  have e8 := inPrefix_ipv4Prefix_eq_decide 224 0 0 0 4 V (o0 / 16 = 14)
    (by simp [ofBigEndianDigits]; omega)
  have e9 := inPrefix_ipv4Prefix_eq_decide 0 0 0 0 8 V (o0 = 0)
    (by simp [ofBigEndianDigits]; omega)
  have e10 := inPrefix_ipv4Prefix_eq_decide 100 64 0 0 10 V (o0 = 100 ∧ o1 / 64 = 1)
    (by simp [ofBigEndianDigits]; omega)
  have e11 := inPrefix_ipv4Prefix_eq_decide 198 18 0 0 15 V (o0 = 198 ∧ o1 / 2 = 9)
    (by simp [ofBigEndianDigits]; omega)
  simp only [ipv4Disallowed, ipv4DisallowedPrefixes, List.any_cons, List.any_nil, Bool.or_false,
    e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, Bool.decide_or]

/-- Membership in an IPv6 prefix, for `V` given by its segments: a prefix test on `V`
rewritten as a condition `P` on the segments. -/
theorem inPrefix_ipv6Prefix_eq_decide (segs : List Nat) (len : Nat) (V : Nat) (P : Prop)
    [Decidable P]
    (h : V / 2 ^ (128 - len) =
      ofBigEndianDigits 65536 (segs ++ List.replicate (8 - segs.length) 0) / 2 ^ (128 - len) ↔
        P) :
    inPrefix (ipv6Prefix segs len) V = decide P := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, ← h]
  simp [inPrefix, ipv6Prefix]

/-- The IPv6 range list of `ipv6Disallowed` as a condition on eight segments. -/
theorem ipv6DisallowedPrefixes_any_eq_decide (s0 s1 s2 s3 s4 s5 s6 s7 : Nat) (h0 : s0 < 65536)
    (h1 : s1 < 65536) (h2 : s2 < 65536) (h3 : s3 < 65536) (h4 : s4 < 65536) (h5 : s5 < 65536)
    (h6 : s6 < 65536) (h7 : s7 < 65536) (V : Nat) (hV : V = s0 * 2^112 + s1 * 2^96 +
      s2 * 2^80 + s3 * 2^64 + s4 * 2^48 + s5 * 2^32 + s6 * 2^16 + s7) :
    ipv6DisallowedPrefixes.any (fun p => inPrefix p V) =
      decide (
        (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧ s6 = 0 ∧ s7 = 1) ∨
        (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧ s6 = 0 ∧ s7 = 0) ∨
        s0 / 256 = 255 ∨ s0 / 64 = 1018 ∨ s0 / 512 = 126 ∨ (s0 = 8193 ∧ s1 = 0) ∨
        (s0 = 100 ∧ s1 = 65435 ∧ s2 = 1)) := by
  have e1 := inPrefix_ipv6Prefix_eq_decide [0, 0, 0, 0, 0, 0, 0, 1] 128 V
    (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧ s6 = 0 ∧ s7 = 1)
    (by simp [ofBigEndianDigits]; omega)
  have e2 := inPrefix_ipv6Prefix_eq_decide [] 128 V
    (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧ s6 = 0 ∧ s7 = 0)
    (by simp [ofBigEndianDigits]; omega)
  have e3 := inPrefix_ipv6Prefix_eq_decide [0xff00] 8 V (s0 / 256 = 255)
    (by simp [ofBigEndianDigits]; omega)
  have e4 := inPrefix_ipv6Prefix_eq_decide [0xfe80] 10 V (s0 / 64 = 1018)
    (by simp [ofBigEndianDigits]; omega)
  have e5 := inPrefix_ipv6Prefix_eq_decide [0xfc00] 7 V (s0 / 512 = 126)
    (by simp [ofBigEndianDigits]; omega)
  have e6 := inPrefix_ipv6Prefix_eq_decide [0x2001, 0] 32 V (s0 = 8193 ∧ s1 = 0)
    (by simp [ofBigEndianDigits]; omega)
  have e7 := inPrefix_ipv6Prefix_eq_decide [0x64, 0xff9b, 1] 48 V
    (s0 = 100 ∧ s1 = 65435 ∧ s2 = 1) (by simp [ofBigEndianDigits]; omega)
  simp only [ipv6DisallowedPrefixes, ipv6Loopback, ipv6Unspecified, ipv6Multicast, ipv6LinkLocal,
    ipv6UniqueLocal, teredo, nat64LocalUse, List.any_cons, List.any_nil, Bool.or_false,
    e1, e2, e3, e4, e5, e6, e7, Bool.decide_or]

/-! ## The `Defs.Net` content of C04 -/

/-- A blocked IPv4 address is a 32-bit value. -/
theorem lt_of_ipv4Disallowed (w : Nat) (h : ipv4Disallowed w = true) : w < 2 ^ 32 := by
  simp only [ipv4Disallowed, ipv4DisallowedPrefixes, ipv4Prefix, ofBigEndianDigits, List.foldl,
    List.any_cons, List.any_nil, inPrefix, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
  norm_num at h
  omega

/-- An IPv6 address that writes a blocked IPv4 address in IPv4-mapped, NAT64, IPv4-compatible
or 6to4 form is blocked. -/
theorem ipv6Disallowed_of_ipv4Disallowed (V w : Nat) (h_dis : ipv4Disallowed w = true)
    (h_form : V = ipv4Mapped.base + w ∨ V = nat64WellKnown.base + w ∨ V = w ∨
      ∃ low < 2 ^ 80, V = sixToFour.base + w * 2 ^ 80 + low) :
    ipv6Disallowed V = true := by
  have hw := lt_of_ipv4Disallowed w h_dis
  rw [ipv4Mapped_eq, nat64WellKnown_eq, sixToFour_eq] at h_form
  simp only at h_form
  have key : embeddedIpv4 V = some w ∨ V = 0 ∨ V = 1 := by
    simp only [embeddedIpv4, inPrefix, ipv4Mapped_eq, nat64WellKnown_eq, ipv4Compatible_eq,
      sixToFour_eq]
    norm_num
    rcases h_form with h | h | h | ⟨low, hlow, h⟩
    · left
      rw [if_pos (by omega)]
      simp only [Option.some.injEq]; omega
    · left
      rw [if_pos (by omega)]
      simp only [Option.some.injEq]; omega
    · by_cases h01 : V = 0 ∨ V = 1
      · right; exact h01
      · left
        rw [if_neg (by omega), if_pos (by omega)]
        simp only [Option.some.injEq]; omega
    · left
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      simp only [Option.some.injEq]; omega
  rcases key with h | h | h
  · simp [ipv6Disallowed, h, h_dis]
  · subst h
    decide
  · subst h
    decide

end Proofs.Transport.Auth

open Proofs.Transport.Auth
open Defs.Net

namespace rmcp.transport.auth.AuthorizationManager

/-! ## A02, A01, A03 (`auth.rs` lines 1343–1383), in Rust source order -/

-- 11-range disjunction; 1,400,000 times out
set_option maxHeartbeats 1600000 in
/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_disallowed_metadata_ipv4`**
(A02)

The call never fails. `true` exactly when the address is in one of `10/8`, `172.16/12`,
`192.168/16` (RFC 1918), `127/8`, `169.254/16` (RFC 3927), `255.255.255.255`, `0.0.0.0`,
`224/4`, `0/8`, `100.64/10` (RFC 6598) or `198.18/15` (RFC 2544), as prefixes of the 32-bit
value of its octets (`Defs.Net.ipv4Disallowed`, `Defs.Net.inPrefix`), not as the `std`
predicates (plan Section 16.3, A02; Section 17; `auth.rs` lines 1343–1354: `is_private`,
`is_loopback`, `is_link_local`, `is_broadcast`, `is_unspecified`, `is_multicast`,
`octets[0] == 0`, `100` with `64..=127`, `198` with `18 | 19`). `240.0.0.0/4` other than
`255.255.255.255` gives `false`, the code's behaviour (human decision H8: a recorded bug). No
premise. -/
@[step]
theorem is_disallowed_metadata_ipv4_spec (addr : core.net.ip_addr.Ipv4Addr) :
    is_disallowed_metadata_ipv4 addr ⦃ (result : Bool) =>
      result = Defs.Net.ipv4Disallowed (Defs.Net.ipv4Value addr.addrOctets.val) ⦄ := by
  obtain ⟨o0, o1, o2, o3, ho⟩ := addr.exists_octets
  have b0 := u8_val_lt o0; have b1 := u8_val_lt o1; have b2 := u8_val_lt o2; have b3 := u8_val_lt o3
  rw [ho, ipv4Disallowed_eq_decide_octets o0.val o1.val o2.val o3.val b0 b1 b2 b3 _
    (by simp only [ipv4Value, ofBigEndianDigits, List.map, List.foldl]; ring)]
  unfold is_disallowed_metadata_ipv4
  step with core.net.ip_addr.Ipv4Addr.octets_spec
  step with core.net.ip_addr.Ipv4Addr.is_private_spec addr o0 o1 o2 o3 ho
  split
  · simp only [WP.spec_ok]; simp_all; try omega
  step with core.net.ip_addr.Ipv4Addr.is_loopback_spec addr o0 o1 o2 o3 ho
  split
  · simp only [WP.spec_ok]; simp_all; try omega
  step with core.net.ip_addr.Ipv4Addr.is_link_local_spec addr o0 o1 o2 o3 ho
  split
  · simp only [WP.spec_ok]; simp_all; try omega
  step with core.net.ip_addr.Ipv4Addr.is_broadcast_spec addr o0 o1 o2 o3 ho
  split
  · simp only [WP.spec_ok]; simp_all; try omega
  step with core.net.ip_addr.Ipv4Addr.is_unspecified_spec addr o0 o1 o2 o3 ho
  split
  · simp only [WP.spec_ok]; simp_all; try omega
  step with core.net.ip_addr.Ipv4Addr.is_multicast_spec addr o0 o1 o2 o3 ho
  split
  · simp only [WP.spec_ok]; simp_all; try omega
  have ho' : octets.val = [o0, o1, o2, o3] := by rw [octets_post, ho]
  clear octets_post
  all_goals (repeat' (first | step | split))
  all_goals (try simp only [WP.spec_ok])
  all_goals (try simp [UScalar.eq_equiv, u8_mk_ofNat_val, ho'] at *)
  all_goals (try omega)
  all_goals (simp_all; try omega)

-- 200,000 times out
set_option maxHeartbeats 400000 in
/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::embedded_ipv4`** (A01)

The call never fails. The value of the returned address is `Defs.Net.embeddedIpv4` of the value
of `addr`: over the segments `[a, b, c, d, e, f, g, h]`, IPv4-mapped `::ffff:0:0/96` (RFC 4291
§2.5.5.2) or NAT64 `64:ff9b::/96` (RFC 6052) give `some (g·2^16 + h)`; IPv4-compatible `::/96`
(RFC 4291 §2.5.5.1) except `::` and `::1` gives `some (g·2^16 + h)`; 6to4 `2002::/16` (RFC 3056)
gives `some (b·2^16 + c)`; everything else, including Teredo `2001::/32` and the local-use
NAT64 prefix `64:ff9b:1::/48`, gives `none` (plan Section 16.3, A01; Section 17; Section 22;
`auth.rs` lines 1356–1368). An `Ipv4Addr` is determined by the value of its four octets, so this
fixes the result. No premise. -/
@[step]
theorem embedded_ipv4_spec (addr : core.net.ip_addr.Ipv6Addr) :
    embedded_ipv4 addr ⦃ (result : Option core.net.ip_addr.Ipv4Addr) =>
      result.map (fun v4 => Defs.Net.ipv4Value v4.addrOctets.val) =
        Defs.Net.embeddedIpv4 (Defs.Net.ipv6Value addr.addrSegments.val) ⦄ := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, hs⟩ := addr.exists_segments
  unfold embedded_ipv4
  simp only [core.net.ip_addr.Ipv6Addr.segments, bind_tc_ok, lift]
  step; step; step; step; step; step; step; step
  step
  step with core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_spec
  step
  simp [hs] at a1_post b_post c_post d_post e_post f_post g_post h_post
  subst a1 b c d e f g h
  have b0 := u16_val_lt s0
  have b1 := u16_val_lt s1
  have b2 := u16_val_lt s2
  have b3 := u16_val_lt s3
  have b4 := u16_val_lt s4
  have b5 := u16_val_lt s5
  have b6 := u16_val_lt s6
  have b7 := u16_val_lt s7
  have hlowv : ipv4Value low.addrOctets.val = s6.val * 2^16 + s7.val := by
    rw [ipv4Value_eq_of_octets_map _ _ low_post1, or_from_val_eq _ _ _ i1_post1]
  rw [hs, ipv6Value_eight_segments, embeddedIpv4_of_segments s0.val s1.val s2.val s3.val s4.val
    s5.val s6.val s7.val b0 b1 b2 b3 b4 b5 b6 b7 _ rfl]
  rw [is_loopback_eq_ok addr _ _ _ _ _ _ _ _ hs, is_unspecified_eq_ok addr _ _ _ _ _ _ _ _ hs]
  simp only [i4_post, Array.make, List.getElem_cons_zero, bind_tc_ok]
  all_goals (repeat' (first
    | step
    | step with core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_spec
    | split))
  all_goals (try simp only [WP.spec_ok])
  all_goals (try (simp only [Option.map_some, Option.some.injEq]; rw [ipv4Value_eq_of_octets_map
    _ _ ia_post1, or_from_val_eq _ _ _ i6_post1]))
  all_goals clear low_post1 low_post2 i1_post1 i1_post2 hs i4_post
  all_goals (try simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq,
    hlowv])
  all_goals (try simp [UScalar.eq_equiv, u16_mk_ofNat_val] at *)
  all_goals (try omega)

/-- **Spec theorem for `rmcp::transport::auth::AuthorizationManager::is_disallowed_metadata_ipv6`**
(A03)

The call never fails. If `addr` carries an IPv4 address (A01, `Defs.Net.embeddedIpv4`), the
result is A02 on that address; otherwise `true` exactly when `addr` is `::1`, `::`, or in
`ff00::/8`, `fe80::/10`, `fc00::/7` (RFC 4193), `2001::/32` (Teredo, RFC 4380) or
`64:ff9b:1::/48` (RFC 8215; as a whole, human decision H8) (`Defs.Net.ipv6Disallowed`; plan
Section 16.3, A03; `auth.rs` lines
1370–1383: the early return of lines 1371–1373, then `is_loopback`, `is_unspecified`,
`is_multicast`, the masks `0xffc0`/`0xfe80` and `0xfe00`/`0xfc00`, `segments[..2] == [0x2001,
0]` and `segments[..3] == [0x64, 0xff9b, 1]`). No premise. -/
@[step]
theorem is_disallowed_metadata_ipv6_spec (addr : core.net.ip_addr.Ipv6Addr) :
    is_disallowed_metadata_ipv6 addr ⦃ (result : Bool) =>
      result = Defs.Net.ipv6Disallowed (Defs.Net.ipv6Value addr.addrSegments.val) ⦄ := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, hs⟩ := addr.exists_segments
  have b0 := u16_val_lt s0; have b1 := u16_val_lt s1; have b2 := u16_val_lt s2
  have b3 := u16_val_lt s3; have b4 := u16_val_lt s4; have b5 := u16_val_lt s5
  have b6 := u16_val_lt s6; have b7 := u16_val_lt s7
  unfold is_disallowed_metadata_ipv6
  step with embedded_ipv4_spec addr
  split
  · rw [Defs.Net.ipv6Disallowed, ← o_post, Option.map_none]
    simp only
    rw [hs, ipv6Value_eight_segments, ipv6DisallowedPrefixes_any_eq_decide s0.val s1.val s2.val
      s3.val s4.val s5.val s6.val s7.val b0 b1 b2 b3 b4 b5 b6 b7 _ rfl]
    rw [is_loopback_eq_ok addr _ _ _ _ _ _ _ _ hs, is_unspecified_eq_ok addr _ _ _ _ _ _ _ _ hs]
    step with core.net.ip_addr.Ipv6Addr.segments_spec
    have hseg : segments.val = [s0, s1, s2, s3, s4, s5, s6, s7] := by rw [segments_post, hs]
    clear segments_post
    simp only [lift, bind_tc_ok]
    all_goals (repeat' (first
      | step with core.net.ip_addr.Ipv6Addr.is_multicast_spec addr s0 s1 s2 s3 s4 s5 s6 s7 hs
      | step | split))
    all_goals (try simp only [WP.spec_ok])
    all_goals (try simp only [and_65472_eq_65152_iff, and_65024_eq_64512_iff] at *)
    all_goals (try simp [UScalar.eq_equiv, hseg, Array.make] at *)
    all_goals (try omega)
    all_goals (simp_all [UScalar.eq_equiv]; try omega)
    all_goals (rw [Bool.eq_iff_iff, result_post]; simp only [Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]; omega)
  · rename_i e
    step with is_disallowed_metadata_ipv4_spec e
    rw [Defs.Net.ipv6Disallowed, ← o_post, Option.map_some]
    simp only
    exact result_post

end rmcp.transport.auth.AuthorizationManager

namespace rmcp.transport.auth.AuthorizationManager

/-! ## Composition theorem C04 (plan Section 16.4) -/

/-- **C04** (former plan name `ipv6_embedding_no_bypass`): an IPv6 address that carries an IPv4
address `v` is blocked exactly when `v` is, so a blocked IPv4 address cannot pass the guard in
IPv4-mapped, IPv4-compatible, NAT64 or 6to4 form (plan Section 16.4, C04; uses A01–A03;
`auth.rs` lines 1371–1373, the early return). The plan-prescribed shape, which restates the
code's early return; `is_disallowed_metadata_ipv6_of_ipv4Disallowed` below states the guarantee
in terms of `Defs.Net`. About the translated functions `embedded_ipv4`,
`is_disallowed_metadata_ipv6` and `is_disallowed_metadata_ipv4`. It takes a successful call of
`embedded_ipv4` returning `some v` as its hypothesis and covers only that case (A01 shows that
the call never fails and when it returns `some`). Not tagged `@[step]`. -/
theorem is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some
    (addr : core.net.ip_addr.Ipv6Addr) (v : core.net.ip_addr.Ipv4Addr)
    (h : embedded_ipv4 addr = ok (some v)) :
    is_disallowed_metadata_ipv6 addr = is_disallowed_metadata_ipv4 v := by
  unfold is_disallowed_metadata_ipv6
  rw [h, bind_tc_ok]

/-- **C04, corollary in `Defs.Net` terms**: no SSRF bypass through an embedded address. Let
`w` be a 32-bit address blocked by A02 (`Defs.Net.ipv4Disallowed w = true`, which implies
`w < 2^32`). Every IPv6 address that writes `w` in one of the four embedding forms is blocked:
IPv4-mapped `::ffff:w` (RFC 4291 §2.5.5.2), NAT64 `64:ff9b::w` (RFC 6052 §2.2), IPv4-compatible
`::w` (RFC 4291 §2.5.5.1), and 6to4 `2002:w::/48` with any value of the remaining 80 bits
(RFC 3056 §2, `w` in bits 16–47). The compatible form needs no `1 < w` premise: `::` and `::1`
carry no address (A01) but are blocked as unspecified and loopback (A03), and `0.0.0.0`,
`0.0.0.1` are blocked by `0/8` (A02). Plan Section 16.4, C04 ("No SSRF bypass by writing a
blocked IPv4 address in IPv4-mapped, compatible, NAT64 or 6to4 form"); uses A01–A03; `auth.rs`
lines 1343–1383. About the translated function `is_disallowed_metadata_ipv6`. No call is
assumed to succeed: the conclusion includes that the call terminates without panicking. Not
tagged `@[step]`. -/
theorem is_disallowed_metadata_ipv6_of_ipv4Disallowed (addr : core.net.ip_addr.Ipv6Addr)
    (w : Nat) (h_dis : Defs.Net.ipv4Disallowed w = true)
    (h_form :
      Defs.Net.ipv6Value addr.addrSegments.val = Defs.Net.ipv4Mapped.base + w ∨
      Defs.Net.ipv6Value addr.addrSegments.val = Defs.Net.nat64WellKnown.base + w ∨
      Defs.Net.ipv6Value addr.addrSegments.val = w ∨
      ∃ low < 2 ^ 80,
        Defs.Net.ipv6Value addr.addrSegments.val = Defs.Net.sixToFour.base + w * 2 ^ 80 + low) :
    is_disallowed_metadata_ipv6 addr ⦃ (result : Bool) => result = true ⦄ := by
  apply WP.spec_mono (is_disallowed_metadata_ipv6_spec addr)
  intro r hr
  rw [hr]
  exact ipv6Disallowed_of_ipv4Disallowed _ w h_dis h_form

end rmcp.transport.auth.AuthorizationManager
