/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.Defs.Net
public import Proofs.External.Net
public import Proofs.External.Std

@[expose] public section

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
lemmas reduce the prefix tests of `Defs.Net` to conditions on the octets or segments, one
`omega` call per range (`ipv4Disallowed_eq_octets`, `embeddedIpv4_of_segments`,
`ipv6DisallowedPrefixes_any_eq_decide`), in the order of the code's tests. A02 and A03 are chains
of early `return true`s, matched test by test with `bind_if_ok_true_spec` and
`ite_ok_true_spec`; A01 is followed match arm by match arm, each arm closed by the branch of
`embeddedIpv4` it takes.

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

/-- The value of a `u8` literal pattern (`18#uscalar` in the match arms of A02). -/
theorem u8_mk_ofNat_val (k : Nat) :
    (@UScalar.mk UScalarTy.U8 (BitVec.ofNat 8 k)).val = k % 256 := by
  simp only [UScalar.val, UScalarTy.U8_numBits_eq, ↓UScalar.bv_mk_apply, BitVec.toNat_ofNat,
    Nat.reducePow]

/-- The value of a `u16` literal pattern (`0#uscalar` in the match arms of A01). -/
theorem u16_mk_ofNat_val (k : Nat) :
    (@UScalar.mk UScalarTy.U16 (BitVec.ofNat 16 k)).val = k % 65536 := by
  simp only [UScalar.val, UScalarTy.U16_numBits_eq, ↓UScalar.bv_mk_apply, BitVec.toNat_ofNat,
    Nat.reducePow]

/-- The arm of a `u16` literal pattern taken: the scrutinee `y` has the literal's value. -/
theorem u16_val_eq_of_mk_eq {y : U16} {k : Nat}
    (h : @UScalar.mk UScalarTy.U16 (BitVec.ofNat 16 k) = y) : y.val = k % 65536 := by
  rw [← h, u16_mk_ofNat_val]

/-- The arm of a `u16` literal pattern skipped: the scrutinee `x = y` has another value. -/
theorem u16_val_ne_of_ne_mk {x y : U16} {k : Nat} (hx : x = y)
    (h : x = @UScalar.mk UScalarTy.U16 (BitVec.ofNat 16 k) → False) : y.val ≠ k % 65536 := by
  intro e
  apply h
  rw [hx, UScalar.eq_equiv, e, u16_mk_ofNat_val]

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
    simp only [hi, decide_true, Bool.true_and, Bool.and_comm, this]
  · simp only [hi, decide_false, Bool.false_and, Bool.and_false]

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

/-- Membership in an IPv4 prefix, for `V` given by its octets: a prefix test on `V`
rewritten as a condition `P` on the octets. -/
theorem inPrefix_ipv4Prefix_eq_decide (a b c d len : Nat) (V : Nat) (P : Prop) [Decidable P]
    (h : V / 2 ^ (32 - len) = (a * 2^24 + b * 2^16 + c * 2^8 + d) / 2 ^ (32 - len) ↔ P) :
    inPrefix (ipv4Prefix a b c d len) V = decide P := by
  have hb : ofBigEndianDigits 256 [a, b, c, d] = a * 2^24 + b * 2^16 + c * 2^8 + d := by
    simp only [ofBigEndianDigits, List.foldl]
    ring
  rw [Bool.eq_iff_iff, decide_eq_true_eq, ← h]
  simp only [inPrefix, ipv4Prefix, hb, beq_iff_eq]

/-- Membership in an IPv6 prefix, for `V` given by its segments: a prefix test on `V`
rewritten as a condition `P` on the segments. `t0`, …, `t7` are the segments of the prefix
(`segs` padded with zeros, checked by `rfl`). -/
theorem inPrefix_ipv6Prefix_eq_decide (segs : List Nat) (len : Nat) (t0 t1 t2 t3 t4 t5 t6 t7 : Nat)
    (ht : segs ++ List.replicate (8 - segs.length) 0 = [t0, t1, t2, t3, t4, t5, t6, t7])
    (V : Nat) (P : Prop) [Decidable P]
    (h : V / 2 ^ (128 - len) = (t0 * 2^112 + t1 * 2^96 + t2 * 2^80 + t3 * 2^64 + t4 * 2^48 +
      t5 * 2^32 + t6 * 2^16 + t7) / 2 ^ (128 - len) ↔ P) :
    inPrefix (ipv6Prefix segs len) V = decide P := by
  have hb : ofBigEndianDigits 65536 [t0, t1, t2, t3, t4, t5, t6, t7] = t0 * 2^112 + t1 * 2^96 +
      t2 * 2^80 + t3 * 2^64 + t4 * 2^48 + t5 * 2^32 + t6 * 2^16 + t7 := by
    simp only [ofBigEndianDigits, List.foldl]
    ring
  rw [Bool.eq_iff_iff, decide_eq_true_eq, ← h]
  simp only [inPrefix, ipv6Prefix, ht, hb, beq_iff_eq]

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
      decide (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 65535) :=
    inPrefix_ipv6Prefix_eq_decide _ 96 0 0 0 0 0 65535 0 0 rfl V _ (by omega)
  have hn : inPrefix nat64WellKnown V =
      decide (s0 = 100 ∧ s1 = 65435 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0) :=
    inPrefix_ipv6Prefix_eq_decide _ 96 100 65435 0 0 0 0 0 0 rfl V _ (by omega)
  have hc : (inPrefix ipv4Compatible V && V != 0 && V != 1) =
      decide (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧
        ¬ (s6 = 0 ∧ s7 = 0) ∧ ¬ (s6 = 0 ∧ s7 = 1)) := by
    have e : inPrefix ipv4Compatible V =
        decide (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0) :=
      inPrefix_ipv6Prefix_eq_decide _ 96 0 0 0 0 0 0 0 0 rfl V _ (by omega)
    rw [e, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    omega
  have h6 : inPrefix sixToFour V = decide (s0 = 8194) :=
    inPrefix_ipv6Prefix_eq_decide _ 16 8194 0 0 0 0 0 0 0 rfl V _ (by omega)
  have hlow : V % 2^32 = s6 * 2^16 + s7 := by omega
  have hmid : V / 2^80 % 2^32 = s1 * 2^16 + s2 := by omega
  simp only [embeddedIpv4, hm, hn, hc, h6, hlow, hmid, ← Bool.decide_or, decide_eq_true_eq]

/-- `embeddedIpv4` of an address with segments `s0`, …, `s7`. -/
theorem embeddedIpv4_ipv6Value_eq (addr : core.net.ip_addr.Ipv6Addr) (s0 s1 s2 s3 s4 s5 s6 s7 : U16)
    (hs : addr.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7]) :
    embeddedIpv4 (ipv6Value addr.addrSegments.val) =
      if (s0.val = 0 ∧ s1.val = 0 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧ s5.val = 65535) ∨
          (s0.val = 100 ∧ s1.val = 65435 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧ s5.val = 0) then
        some (s6.val * 2^16 + s7.val)
      else if s0.val = 0 ∧ s1.val = 0 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧ s5.val = 0 ∧
          ¬ (s6.val = 0 ∧ s7.val = 0) ∧ ¬ (s6.val = 0 ∧ s7.val = 1) then
        some (s6.val * 2^16 + s7.val)
      else if s0.val = 8194 then some (s1.val * 2^16 + s2.val)
      else none := by
  rw [hs, ipv6Value_eight_segments]
  exact embeddedIpv4_of_segments _ _ _ _ _ _ _ _ (u16_val_lt s0) (u16_val_lt s1) (u16_val_lt s2)
    (u16_val_lt s3) (u16_val_lt s4) (u16_val_lt s5) (u16_val_lt s6) (u16_val_lt s7) _ rfl

/-- `ipv4Disallowed` as a condition on four octets, one test per branch of A02 in source order
(the three RFC 1918 ranges of `is_private` together, then `127/8`, `169.254/16`,
`255.255.255.255`, `0.0.0.0`, `224/4`, and the three octet tests together). Each range is reduced
by its own `omega` call; one call over the whole disjunction is too slow. -/
theorem ipv4Disallowed_eq_octets (o0 o1 o2 o3 : Nat) (h0 : o0 < 256) (h1 : o1 < 256)
    (h2 : o2 < 256) (h3 : o3 < 256) (V : Nat)
    (hV : V = o0 * 2^24 + o1 * 2^16 + o2 * 2^8 + o3) :
    ipv4Disallowed V =
      (decide (o0 = 10 ∨ (o0 = 172 ∧ o1 / 16 = 1) ∨ (o0 = 192 ∧ o1 = 168)) ||
      (decide (o0 = 127) || (decide (o0 = 169 ∧ o1 = 254) ||
      (decide (o0 = 255 ∧ o1 = 255 ∧ o2 = 255 ∧ o3 = 255) ||
      (decide (o0 = 0 ∧ o1 = 0 ∧ o2 = 0 ∧ o3 = 0) || (decide (o0 / 16 = 14) ||
      decide (o0 = 0 ∨ (o0 = 100 ∧ o1 / 64 = 1) ∨ (o0 = 198 ∧ o1 / 2 = 9)))))))) := by
  have e1 := inPrefix_ipv4Prefix_eq_decide 10 0 0 0 8 V (o0 = 10) (by omega)
  have e2 := inPrefix_ipv4Prefix_eq_decide 172 16 0 0 12 V (o0 = 172 ∧ o1 / 16 = 1) (by omega)
  have e3 := inPrefix_ipv4Prefix_eq_decide 192 168 0 0 16 V (o0 = 192 ∧ o1 = 168) (by omega)
  have e4 := inPrefix_ipv4Prefix_eq_decide 127 0 0 0 8 V (o0 = 127) (by omega)
  have e5 := inPrefix_ipv4Prefix_eq_decide 169 254 0 0 16 V (o0 = 169 ∧ o1 = 254) (by omega)
  have e6 := inPrefix_ipv4Prefix_eq_decide 255 255 255 255 32 V
    (o0 = 255 ∧ o1 = 255 ∧ o2 = 255 ∧ o3 = 255) (by omega)
  have e7 := inPrefix_ipv4Prefix_eq_decide 0 0 0 0 32 V (o0 = 0 ∧ o1 = 0 ∧ o2 = 0 ∧ o3 = 0)
    (by omega)
  have e8 := inPrefix_ipv4Prefix_eq_decide 224 0 0 0 4 V (o0 / 16 = 14) (by omega)
  have e9 := inPrefix_ipv4Prefix_eq_decide 0 0 0 0 8 V (o0 = 0) (by omega)
  have e10 := inPrefix_ipv4Prefix_eq_decide 100 64 0 0 10 V (o0 = 100 ∧ o1 / 64 = 1) (by omega)
  have e11 := inPrefix_ipv4Prefix_eq_decide 198 18 0 0 15 V (o0 = 198 ∧ o1 / 2 = 9) (by omega)
  simp only [ipv4Disallowed, ipv4DisallowedPrefixes, List.any_cons, List.any_nil, Bool.or_false,
    e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, Bool.decide_or, Bool.or_assoc]

/-- The IPv6 range list of `ipv6Disallowed` as a condition on eight segments, one test per
branch of A03 in source order. -/
theorem ipv6DisallowedPrefixes_any_eq_decide (s0 s1 s2 s3 s4 s5 s6 s7 : Nat) (h0 : s0 < 65536)
    (h1 : s1 < 65536) (h2 : s2 < 65536) (h3 : s3 < 65536) (h4 : s4 < 65536) (h5 : s5 < 65536)
    (h6 : s6 < 65536) (h7 : s7 < 65536) (V : Nat) (hV : V = s0 * 2^112 + s1 * 2^96 +
      s2 * 2^80 + s3 * 2^64 + s4 * 2^48 + s5 * 2^32 + s6 * 2^16 + s7) :
    ipv6DisallowedPrefixes.any (fun p => inPrefix p V) =
      (decide (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧ s6 = 0 ∧ s7 = 1) ||
      (decide (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧ s6 = 0 ∧ s7 = 0) ||
      (decide (s0 / 256 = 255) || (decide (s0 / 64 = 1018) || (decide (s0 / 512 = 126) ||
      (decide (s0 = 8193 ∧ s1 = 0) || decide (s0 = 100 ∧ s1 = 65435 ∧ s2 = 1))))))) := by
  have e1 := inPrefix_ipv6Prefix_eq_decide [0, 0, 0, 0, 0, 0, 0, 1] 128 0 0 0 0 0 0 0 1 rfl V
    (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧ s6 = 0 ∧ s7 = 1) (by omega)
  have e2 := inPrefix_ipv6Prefix_eq_decide [] 128 0 0 0 0 0 0 0 0 rfl V
    (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 = 0 ∧ s6 = 0 ∧ s7 = 0) (by omega)
  have e3 := inPrefix_ipv6Prefix_eq_decide [0xff00] 8 0xff00 0 0 0 0 0 0 0 rfl V
    (s0 / 256 = 255) (by omega)
  have e4 := inPrefix_ipv6Prefix_eq_decide [0xfe80] 10 0xfe80 0 0 0 0 0 0 0 rfl V
    (s0 / 64 = 1018) (by omega)
  have e5 := inPrefix_ipv6Prefix_eq_decide [0xfc00] 7 0xfc00 0 0 0 0 0 0 0 rfl V
    (s0 / 512 = 126) (by omega)
  have e6 := inPrefix_ipv6Prefix_eq_decide [0x2001, 0] 32 0x2001 0 0 0 0 0 0 0 rfl V
    (s0 = 8193 ∧ s1 = 0) (by omega)
  have e7 := inPrefix_ipv6Prefix_eq_decide [0x64, 0xff9b, 1] 48 0x64 0xff9b 1 0 0 0 0 0 rfl V
    (s0 = 100 ∧ s1 = 65435 ∧ s2 = 1) (by omega)
  simp only [ipv6DisallowedPrefixes, ipv6Loopback, ipv6Unspecified, ipv6Multicast, ipv6LinkLocal,
    ipv6UniqueLocal, teredo, nat64LocalUse, List.any_cons, List.any_nil, Bool.or_false,
    e1, e2, e3, e4, e5, e6, e7]

/-! ## The `Defs.Net` content of C04 -/

/-- A blocked IPv4 address is a 32-bit value. -/
theorem lt_of_ipv4Disallowed (w : Nat) (h : ipv4Disallowed w = true) : w < 2 ^ 32 := by
  simp only [ipv4Disallowed, ipv4DisallowedPrefixes, ipv4Prefix, ofBigEndianDigits, List.foldl,
    List.any_cons, List.any_nil, inPrefix, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
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
      sixToFour_eq, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    rcases h_form with h | h | h | ⟨low, hlow, h⟩
    · left
      rw [ite_eq_left (by omega)]
      simp only [Option.some.injEq]; omega
    · left
      rw [ite_eq_left (by omega)]
      simp only [Option.some.injEq]; omega
    · by_cases h01 : V = 0 ∨ V = 1
      · right; exact h01
      · left
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        simp only [Option.some.injEq]; omega
    · left
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      simp only [Option.some.injEq]; omega
  rcases key with h | h | h
  · simp only [ipv6Disallowed, h, h_dis]
  · subst h
    decide
  · subst h
    decide

/-! ## Early `return true` -/

/-- A `bool` test followed by an early `return true`: the result is the test or the rest. -/
theorem bind_if_ok_true_spec {f rest : Result Bool} {P : Prop} [Decidable P] {q : Bool}
    (hf : f ⦃ b => (b = true ↔ P) ⦄) (hrest : rest ⦃ r => r = q ⦄) :
    (do let b ← f; if b then ok true else rest) ⦃ r => r = (decide P || q) ⦄ := by
  obtain ⟨b, hb, hp⟩ := Proofs.External.WP.exists_ok_of_spec hf
  rw [hb, bind_ok]
  cases b
  · have hP : ¬ P := fun h => Bool.false_ne_true (hp.mpr h)
    rw [ite_eq_right Bool.false_ne_true, decide_eq_false hP, Bool.false_or]
    exact hrest
  · rw [ite_eq_left rfl, decide_eq_true (hp.mp rfl), Bool.true_or, WP.spec_ok]

/-- A decidable test followed by an early `return true`: the result is the test or the rest. -/
theorem ite_ok_true_spec {c P : Prop} [Decidable c] [Decidable P] {rest : Result Bool} {q : Bool}
    (hc : c ↔ P) (hrest : rest ⦃ r => r = q ⦄) :
    (if c then ok true else rest) ⦃ r => r = (decide P || q) ⦄ := by
  by_cases h : c
  · rw [ite_eq_left h, decide_eq_true (hc.mp h), Bool.true_or, WP.spec_ok]
  · rw [ite_eq_right h, decide_eq_false (mt hc.mpr h), Bool.false_or]
    exact hrest

/-- An arm of A01 returning `none`, when no branch of `embeddedIpv4` applies. -/
theorem ok_none_spec {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R] {x y z : Nat}
    (hP : ¬ P) (hQ : ¬ Q) (hR : ¬ R) :
    (ok none : Result (Option core.net.ip_addr.Ipv4Addr)) ⦃ r =>
      r.map (fun v4 => ipv4Value v4.addrOctets.val) =
        if P then some x else if Q then some y else if R then some z else none ⦄ := by
  rw [ite_eq_right hP, ite_eq_right hQ, ite_eq_right hR, WP.spec_ok, Option.map_none]

/-! ## A02 over the octets -/

/-- A02 over the four octets, as the tests of the code in source order: the six `std`
predicates (model laws of `Proofs/External/Net.lean`), then the three octet tests. -/
theorem is_disallowed_metadata_ipv4_octets_spec (addr : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (ho : addr.addrOctets.val = [o0, o1, o2, o3]) :
    rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv4 addr ⦃ (result : Bool) =>
      result =
        (decide (o0.val = 10 ∨ (o0.val = 172 ∧ o1.val / 16 = 1) ∨ (o0.val = 192 ∧ o1.val = 168)) ||
        (decide (o0.val = 127) || (decide (o0.val = 169 ∧ o1.val = 254) ||
        (decide (o0.val = 255 ∧ o1.val = 255 ∧ o2.val = 255 ∧ o3.val = 255) ||
        (decide (o0.val = 0 ∧ o1.val = 0 ∧ o2.val = 0 ∧ o3.val = 0) ||
        (decide (o0.val / 16 = 14) ||
        decide (o0.val = 0 ∨ (o0.val = 100 ∧ o1.val / 64 = 1) ∨
          (o0.val = 198 ∧ o1.val / 2 = 9)))))))) ⦄ := by
  unfold rmcp.transport.auth.AuthorizationManager.is_disallowed_metadata_ipv4
  step with core.net.ip_addr.Ipv4Addr.octets_spec as ⟨octets, h_octets⟩
  apply bind_if_ok_true_spec (core.net.ip_addr.Ipv4Addr.is_private_spec addr o0 o1 o2 o3 ho)
  apply bind_if_ok_true_spec (core.net.ip_addr.Ipv4Addr.is_loopback_spec addr o0 o1 o2 o3 ho)
  apply bind_if_ok_true_spec (core.net.ip_addr.Ipv4Addr.is_link_local_spec addr o0 o1 o2 o3 ho)
  apply bind_if_ok_true_spec (core.net.ip_addr.Ipv4Addr.is_broadcast_spec addr o0 o1 o2 o3 ho)
  apply bind_if_ok_true_spec (core.net.ip_addr.Ipv4Addr.is_unspecified_spec addr o0 o1 o2 o3 ho)
  apply bind_if_ok_true_spec (core.net.ip_addr.Ipv4Addr.is_multicast_spec addr o0 o1 o2 o3 ho)
  have hv : octets.val = [o0, o1, o2, o3] := by rw [h_octets, ho]
  clear h_octets
  step as ⟨i, hi⟩
  simp only [hv, List.getElem_cons_zero] at hi
  subst hi
  have b1 := u8_val_lt o1
  split
  next h0 =>
    rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq] at h0
    rw [WP.spec_ok, eq_comm, decide_eq_true_iff]
    omega
  next h0 =>
    rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq] at h0
    split
    next h100 =>
      rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq] at h100
      step as ⟨ri, hri1, hri2, hri3⟩
      step as ⟨i1, hi1⟩
      step with core.ops.range.RangeInclusive.contains_u8_spec as ⟨b6, hb6⟩
      simp only [hv, List.getElem_cons_succ, List.getElem_cons_zero] at hi1
      simp only [hri1, hri2, hri3, hi1, UScalar.ofNatCore_val_eq,
        Bool.false_eq_true, ↓reduceIte] at hb6
      split
      next h6 =>
        rw [WP.spec_ok, eq_comm, decide_eq_true_iff]
        have := hb6.mp h6
        omega
      next h6 =>
        rw [ite_eq_right (by rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]; omega), WP.spec_ok,
          eq_comm, decide_eq_false_iff_not]
        have := mt hb6.mpr h6
        omega
    next h100 =>
      rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq] at h100
      split
      next h198 =>
        rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq] at h198
        step as ⟨i1, hi1⟩
        simp only [hv, List.getElem_cons_succ, List.getElem_cons_zero] at hi1
        subst hi1
        split
        · rw [WP.spec_ok, eq_comm, decide_eq_true_iff, u8_mk_ofNat_val]
          omega
        · rw [WP.spec_ok, eq_comm, decide_eq_true_iff, u8_mk_ofNat_val]
          omega
        next h18 h19 =>
          simp only [UScalar.eq_equiv, u8_mk_ofNat_val, imp_false] at h18 h19
          rw [WP.spec_ok, eq_comm, decide_eq_false_iff_not]
          omega
      next h198 =>
        rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq] at h198
        rw [WP.spec_ok, eq_comm, decide_eq_false_iff_not]
        omega

end Proofs.Transport.Auth

open Proofs.Transport.Auth
open Defs.Net

namespace rmcp.transport.auth.AuthorizationManager

/-! ## A02, A01, A03 (`auth.rs` lines 1343–1383), in Rust source order -/

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
  rw [ho, ipv4Disallowed_eq_octets o0.val o1.val o2.val o3.val (u8_val_lt o0) (u8_val_lt o1)
    (u8_val_lt o2) (u8_val_lt o3) _
    (by simp only [ipv4Value, ofBigEndianDigits, List.map, List.foldl]; ring)]
  exact is_disallowed_metadata_ipv4_octets_spec addr o0 o1 o2 o3 ho

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
  step with core.net.ip_addr.Ipv6Addr.segments_spec as ⟨a, h_a⟩
  have ha : a.val = [s0, s1, s2, s3, s4, s5, s6, s7] := by rw [h_a, hs]
  step as ⟨a1, h_a1⟩; step as ⟨b, h_b⟩; step as ⟨c, h_c⟩; step as ⟨d, h_d⟩
  step as ⟨e, h_e⟩; step as ⟨f, h_f⟩; step as ⟨g, h_g⟩; step as ⟨h, h_h⟩
  simp only [ha, List.getElem_cons_zero, List.getElem_cons_succ] at h_a1 h_b h_c h_d
  simp only [ha, List.getElem_cons_succ, List.getElem_cons_zero] at h_e h_f h_g h_h
  subst h_a1 h_b h_c h_d h_e h_f h_g h_h
  simp only [lift]
  step as ⟨i1, h_i1, h_i1'⟩
  step with core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_spec as ⟨low, h_low, h_low'⟩
  have hlow : ipv4Value low.addrOctets.val = g.val * 2^16 + h.val := by
    rw [ipv4Value_eq_of_octets_map _ _ h_low, or_from_val_eq _ _ _ h_i1]
  clear h_low h_low' h_i1 h_i1' h_a ha
  have ba := u16_val_lt a1; have bb := u16_val_lt b; have bc := u16_val_lt c
  have bd := u16_val_lt d; have be := u16_val_lt e; have bf := u16_val_lt f
  have bg := u16_val_lt g; have bh := u16_val_lt h
  rw [embeddedIpv4_ipv6Value_eq addr _ _ _ _ _ _ _ _ hs]
  -- one arm per pattern of the code, each closed by the matching branch of `embeddedIpv4`
  step as ⟨i4, h_i4⟩
  split
  · have n0 : a1.val = 0 % 65536 := u16_val_eq_of_mk_eq h_i4
    step as ⟨i5, h_i5⟩
    split
    · have n1 : b.val = 0 % 65536 := u16_val_eq_of_mk_eq h_i5
      step as ⟨i6, h_i6⟩
      split
      · have n2 : c.val = 0 % 65536 := u16_val_eq_of_mk_eq h_i6
        step as ⟨i7, h_i7⟩
        split
        · have n3 : d.val = 0 % 65536 := u16_val_eq_of_mk_eq h_i7
          step as ⟨i8, h_i8⟩
          split
          · have n4 : e.val = 0 % 65536 := u16_val_eq_of_mk_eq h_i8
            step as ⟨i9, h_i9⟩
            split
            · have n5 : f.val = 65535 % 65536 := u16_val_eq_of_mk_eq h_i9
              rw [ite_eq_left (by omega), WP.spec_ok, Option.map_some, hlow]
            · have n5 : f.val = 0 % 65536 := u16_val_eq_of_mk_eq h_i9
              step with core.net.ip_addr.Ipv6Addr.is_loopback_spec addr a1 b c d e f g h hs
                as ⟨b1, h_b1⟩
              split
              next hl =>
                have := h_b1.mp hl
                exact ok_none_spec (by omega) (by omega) (by omega)
              next hl =>
                have := mt h_b1.mpr hl
                step with core.net.ip_addr.Ipv6Addr.is_unspecified_spec addr a1 b c d e f g h hs
                  as ⟨b2, h_b2⟩
                split
                next hu =>
                  have := h_b2.mp hu
                  exact ok_none_spec (by omega) (by omega) (by omega)
                next hu =>
                  have := mt h_b2.mpr hu
                  rw [ite_eq_right (by omega), ite_eq_left (by omega), WP.spec_ok, Option.map_some, hlow]
            next h65535 h0 =>
              have : f.val ≠ 65535 % 65536 := u16_val_ne_of_ne_mk h_i9 h65535
              have : f.val ≠ 0 % 65536 := u16_val_ne_of_ne_mk h_i9 h0
              exact ok_none_spec (by omega) (by omega) (by omega)
          next hne =>
            have : e.val ≠ 0 % 65536 := u16_val_ne_of_ne_mk h_i8 hne
            exact ok_none_spec (by omega) (by omega) (by omega)
        next hne =>
          have : d.val ≠ 0 % 65536 := u16_val_ne_of_ne_mk h_i7 hne
          exact ok_none_spec (by omega) (by omega) (by omega)
      next hne =>
        have : c.val ≠ 0 % 65536 := u16_val_ne_of_ne_mk h_i6 hne
        exact ok_none_spec (by omega) (by omega) (by omega)
    next hne =>
      have : b.val ≠ 0 % 65536 := u16_val_ne_of_ne_mk h_i5 hne
      exact ok_none_spec (by omega) (by omega) (by omega)
  · have n0 : a1.val = 100 % 65536 := u16_val_eq_of_mk_eq h_i4
    step as ⟨i5, h_i5⟩
    split
    · have n1 : b.val = 65435 % 65536 := u16_val_eq_of_mk_eq h_i5
      step as ⟨i6, h_i6⟩
      split
      · have n2 : c.val = 0 % 65536 := u16_val_eq_of_mk_eq h_i6
        step as ⟨i7, h_i7⟩
        split
        · have n3 : d.val = 0 % 65536 := u16_val_eq_of_mk_eq h_i7
          step as ⟨i8, h_i8⟩
          split
          · have n4 : e.val = 0 % 65536 := u16_val_eq_of_mk_eq h_i8
            step as ⟨i9, h_i9⟩
            split
            · have n5 : f.val = 0 % 65536 := u16_val_eq_of_mk_eq h_i9
              rw [ite_eq_left (by omega), WP.spec_ok, Option.map_some, hlow]
            next hne =>
              have : f.val ≠ 0 % 65536 := u16_val_ne_of_ne_mk h_i9 hne
              exact ok_none_spec (by omega) (by omega) (by omega)
          next hne =>
            have : e.val ≠ 0 % 65536 := u16_val_ne_of_ne_mk h_i8 hne
            exact ok_none_spec (by omega) (by omega) (by omega)
        next hne =>
          have : d.val ≠ 0 % 65536 := u16_val_ne_of_ne_mk h_i7 hne
          exact ok_none_spec (by omega) (by omega) (by omega)
      next hne =>
        have : c.val ≠ 0 % 65536 := u16_val_ne_of_ne_mk h_i6 hne
        exact ok_none_spec (by omega) (by omega) (by omega)
    next hne =>
      have : b.val ≠ 65435 % 65536 := u16_val_ne_of_ne_mk h_i5 hne
      exact ok_none_spec (by omega) (by omega) (by omega)
  · have n0 : a1.val = 8194 % 65536 := u16_val_eq_of_mk_eq h_i4
    step as ⟨i6, h_i6, h_i6'⟩
    step with core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_spec as ⟨ia, h_ia, h_ia'⟩
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Option.map_some,
      ipv4Value_eq_of_octets_map _ _ h_ia, or_from_val_eq _ _ _ h_i6]
  next h0 h100 h8194 =>
    have : a1.val ≠ 0 % 65536 := u16_val_ne_of_ne_mk h_i4 h0
    have : a1.val ≠ 100 % 65536 := u16_val_ne_of_ne_mk h_i4 h100
    have : a1.val ≠ 8194 % 65536 := u16_val_ne_of_ne_mk h_i4 h8194
    exact ok_none_spec (by omega) (by omega) (by omega)

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
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, hs⟩ := addr.exists_segments
  unfold is_disallowed_metadata_ipv6
  step with embedded_ipv4_spec addr as ⟨o, h_o⟩
  split
  · rw [Defs.Net.ipv6Disallowed, ← h_o, Option.map_none]
    simp only
    rw [hs, ipv6Value_eight_segments, ipv6DisallowedPrefixes_any_eq_decide _ _ _ _ _ _ _ _
      (u16_val_lt t0) (u16_val_lt t1) (u16_val_lt t2) (u16_val_lt t3) (u16_val_lt t4)
      (u16_val_lt t5) (u16_val_lt t6) (u16_val_lt t7) _ rfl]
    step with core.net.ip_addr.Ipv6Addr.segments_spec as ⟨segments, h_segments⟩
    have hseg : segments.val = [t0, t1, t2, t3, t4, t5, t6, t7] := by rw [h_segments, hs]
    clear h_segments
    apply bind_if_ok_true_spec
      (core.net.ip_addr.Ipv6Addr.is_loopback_spec addr t0 t1 t2 t3 t4 t5 t6 t7 hs)
    apply bind_if_ok_true_spec
      (core.net.ip_addr.Ipv6Addr.is_unspecified_spec addr t0 t1 t2 t3 t4 t5 t6 t7 hs)
    apply bind_if_ok_true_spec
      (core.net.ip_addr.Ipv6Addr.is_multicast_spec addr t0 t1 t2 t3 t4 t5 t6 t7 hs)
    step as ⟨i, h_i⟩
    simp only [hseg, List.getElem_cons_zero] at h_i
    subst h_i
    simp only [lift, bind_ok]
    apply ite_ok_true_spec (and_65472_eq_65152_iff _)
    apply ite_ok_true_spec (and_65024_eq_64512_iff _)
    step as ⟨s, h_s, h_s'⟩
    have h2 :
        s.val = (Array.make 2#usize [8193#u16, 0#u16]).val ↔ i.val = 8193 ∧ t1.val = 0 := by
      simp only [h_s, Array.val_to_slice, hseg, List.slice_zero_j, List.take_succ_cons,
        List.take_zero, Array.make, Array.from_val, List.cons.injEq, UScalar.eq_equiv,
        UScalar.ofNatCore_val_eq, and_true]
    apply bind_if_ok_true_spec (WP.spec_mono
      (Slice.Insts.CoreCmpPartialEqArray.eq_u16_spec _ _) fun _ hb => hb.trans h2)
    step as ⟨s1, h_s1, h_s1'⟩
    have h3 : s1.val = (Array.make 3#usize [100#u16, 65435#u16, 1#u16]).val ↔
        i.val = 100 ∧ t1.val = 65435 ∧ t2.val = 1 := by
      simp only [h_s1, Array.val_to_slice, hseg, List.slice_zero_j, List.take_succ_cons,
        List.take_zero, Array.make, Array.from_val, List.cons.injEq, UScalar.eq_equiv,
        UScalar.ofNatCore_val_eq, and_true]
    apply WP.spec_mono (Slice.Insts.CoreCmpPartialEqArray.eq_u16_spec _ _)
    intro r hr
    exact Bool.eq_iff_iff.mpr ((hr.trans h3).trans decide_eq_true_iff.symm)
  next e =>
    step with is_disallowed_metadata_ipv4_spec e as ⟨r, h_r⟩
    rw [Defs.Net.ipv6Disallowed, ← h_o, Option.map_some]
    simp only
    exact h_r

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
  rw [h, bind_ok]

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
