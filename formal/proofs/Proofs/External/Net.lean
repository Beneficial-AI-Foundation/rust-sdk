/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.External.Byte

@[expose] public section

/-!
# Laws of the Phase 2 external models: Net (plan steps S26/S27, stage 6)

Proofs of the Phase 2 laws signed off by the spec owner on 2026-11-23 (plan steps S26/S27),
restated in `formal/proofs/Proofs/Internal/External.lean` (Phase 2 part), the project
file that holds them. For this group (spec owner sign-off 2026-11-23). Filled in by the stage-6 prover.
-/

open Aeneas Aeneas.Std Result
open rmcp ExtModel
open Proofs.External.Byte (byte_val)

namespace Proofs.External.Net

/-- Masking with `0xff00` keeps the second byte: `n &&& 0xff00 = (n / 256 % 256) * 256`. -/
theorem and_65280_eq (n : Nat) : n &&& 65280 = n / 256 % 256 * 256 := by
  have h1 : (65280 : Nat) = (2 ^ 8 - 1) * 2 ^ 8 := rfl
  apply Nat.eq_of_testBit_eq
  intro i
  rw [h1, Nat.testBit_and, show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mul_two_pow,
    Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hi : 8 ≤ i
  · simp only [hi, decide_true, Bool.true_and, Nat.sub_add_cancel, Bool.and_comm]
  · simp only [hi, decide_false, Bool.false_and, Bool.and_false]

/-- The octets of an IPv4 address as natural numbers. -/
theorem ipv4Nats_eq (self : core.net.ip_addr.Ipv4Addr) (o0 o1 o2 o3 : U8)
    (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    ExtModel.ipv4Nats self = [o0.val, o1.val, o2.val, o3.val] := by
  simp only [ExtModel.ipv4Nats, h, List.map_cons, List.map_nil]

end Proofs.External.Net

open Proofs.External.Net

/-- Every `Ipv4Addr` has four octets (the model's `Array U8 4#usize`, Rust `octets: [u8; 4]`,
`core/src/net/ip_addr.rs` lines 74–76). -/
theorem core.net.ip_addr.Ipv4Addr.exists_octets (a : core.net.ip_addr.Ipv4Addr) :
    ∃ o0 o1 o2 o3 : U8, a.addrOctets.val = [o0, o1, o2, o3] := by
  have hl : a.addrOctets.val.length = 4 := by simp
  generalize a.addrOctets.val = l at hl ⊢
  match l, hl with
  | [o0, o1, o2, o3], _ => exact ⟨o0, o1, o2, o3, rfl⟩

/-- **Spec theorem for `Ipv4Addr::octets`**: the four octets, most significant first.

Model `core.net.ip_addr.Ipv4Addr.octets`. Rust: `self.octets` (`ip_addr.rs` lines 668–670).

Used by: A02 (`octets[0]`, `octets[1]` for `0/8`, `100.64/10`, `198.18/15`). -/
theorem core.net.ip_addr.Ipv4Addr.octets_spec (self : core.net.ip_addr.Ipv4Addr) :
    core.net.ip_addr.Ipv4Addr.octets self ⦃ (result : Array U8 4#usize) =>
      result = self.addrOctets ⦄ := by
  simp only [core.net.ip_addr.Ipv4Addr.octets, WP.spec_ok]

/-- **Spec theorem for `Ipv4Addr::is_private`**: `10.0.0.0/8`, `172.16.0.0/12` or
`192.168.0.0/16` (RFC 1918).

Model `core.net.ip_addr.Ipv4Addr.is_private`. Rust: `match self.octets() { [10, ..] => true,
[172, b, ..] if b >= 16 && b <= 31 => true, [192, 168, ..] => true, _ => false }`
(`ip_addr.rs` lines 781–788).

Used by: A02. -/
theorem core.net.ip_addr.Ipv4Addr.is_private_spec (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_private self ⦃ (result : Bool) =>
      (result = true ↔ o0.val = 10 ∨ (o0.val = 172 ∧ o1.val / 16 = 1) ∨
        (o0.val = 192 ∧ o1.val = 168)) ⦄ := by
  unfold core.net.ip_addr.Ipv4Addr.is_private
  rw [ipv4Nats_eq self o0 o1 o2 o3 h]
  split
  -- The list is the `simp_all?` output; no shorter list closes all the match cases.
  all_goals simp_all only [List.cons.injEq, Nat.reduceEqDiff, false_and, or_self, or_false,
              iff_true, WP.spec_ok, ge_iff_le, Bool.decide_and, true_and, false_or,
              Bool.and_eq_true, decide_eq_true_eq, Nat.reduceDiv, OfNat.ofNat_ne_one, and_self,
              or_true, imp_false, not_and, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂,
              Bool.false_eq_true, false_iff, not_false_eq_true, implies_true]
  omega

/-- **Spec theorem for `Ipv4Addr::is_loopback`**: `127.0.0.0/8`.

Model `core.net.ip_addr.Ipv4Addr.is_loopback`. Rust: `self.octets()[0] == 127` (`ip_addr.rs`
lines 750–752).

Used by: A02. -/
theorem core.net.ip_addr.Ipv4Addr.is_loopback_spec (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_loopback self ⦃ (result : Bool) =>
      (result = true ↔ o0.val = 127) ⦄ := by
  simp only [core.net.ip_addr.Ipv4Addr.is_loopback, ipv4Nats_eq self o0 o1 o2 o3 h,
    List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some, WP.spec_ok,
    decide_eq_true_eq]

/-- **Spec theorem for `Ipv4Addr::is_link_local`**: `169.254.0.0/16` (RFC 3927).

Model `core.net.ip_addr.Ipv4Addr.is_link_local`. Rust: `matches!(self.octets(), [169, 254,
..])` (`ip_addr.rs` lines 809–811).

Used by: A02. -/
theorem core.net.ip_addr.Ipv4Addr.is_link_local_spec (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_link_local self ⦃ (result : Bool) =>
      (result = true ↔ o0.val = 169 ∧ o1.val = 254) ⦄ := by
  unfold core.net.ip_addr.Ipv4Addr.is_link_local
  rw [ipv4Nats_eq self o0 o1 o2 o3 h]
  split <;> simp_all only [List.cons.injEq, and_self, iff_true, WP.spec_ok, imp_false, not_and,
              forall_apply_eq_imp_iff₂, Bool.false_eq_true, false_iff, not_false_eq_true,
              implies_true]

/-- **Spec theorem for `Ipv4Addr::is_broadcast`**: exactly `255.255.255.255`.

Model `core.net.ip_addr.Ipv4Addr.is_broadcast`. Rust: `u32::from_be_bytes(self.octets()) ==
u32::from_be_bytes(Self::BROADCAST.octets())` (`ip_addr.rs` lines 1032–1034), `BROADCAST =
Ipv4Addr::new(255, 255, 255, 255)` (line 652); the big-endian value determines the octets.

Used by: A02. -/
theorem core.net.ip_addr.Ipv4Addr.is_broadcast_spec (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_broadcast self ⦃ (result : Bool) =>
      (result = true ↔ o0.val = 255 ∧ o1.val = 255 ∧ o2.val = 255 ∧ o3.val = 255) ⦄ := by
  have : o0.val < 256 := by scalar_tac
  have : o1.val < 256 := by scalar_tac
  have : o2.val < 256 := by scalar_tac
  have : o3.val < 256 := by scalar_tac
  simp only [core.net.ip_addr.Ipv4Addr.is_broadcast, ExtModel.beNat, ipv4Nats_eq self o0 o1 o2 o3 h,
    List.foldl_cons, zero_mul, zero_add, List.foldl_nil, Nat.reduceMul, Nat.reduceAdd, WP.spec_ok,
    decide_eq_true_eq]
  omega

/-- **Spec theorem for `Ipv4Addr::is_unspecified`**: exactly `0.0.0.0`.

Model `core.net.ip_addr.Ipv4Addr.is_unspecified`. Rust: `u32::from_be_bytes(self.octets) == 0`
(`ip_addr.rs` lines 728–730); the big-endian value is `0` exactly when every octet is.

Used by: A02. -/
theorem core.net.ip_addr.Ipv4Addr.is_unspecified_spec (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_unspecified self ⦃ (result : Bool) =>
      (result = true ↔ o0.val = 0 ∧ o1.val = 0 ∧ o2.val = 0 ∧ o3.val = 0) ⦄ := by
  simp only [core.net.ip_addr.Ipv4Addr.is_unspecified, ExtModel.beNat,
    ipv4Nats_eq self o0 o1 o2 o3 h, List.foldl_cons, zero_mul, zero_add, List.foldl_nil,
    Nat.add_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, or_false, and_assoc, Bool.decide_and,
    WP.spec_ok, Bool.and_eq_true, decide_eq_true_eq]

/-- **Spec theorem for `Ipv4Addr::is_multicast`**: `224.0.0.0/4` (first four bits `1110`).

Model `core.net.ip_addr.Ipv4Addr.is_multicast`. Rust: `self.octets()[0] >= 224 &&
self.octets()[0] <= 239` (`ip_addr.rs` lines 1010–1012), which is `o0.val / 16 = 14`.

Used by: A02. -/
theorem core.net.ip_addr.Ipv4Addr.is_multicast_spec (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_multicast self ⦃ (result : Bool) =>
      (result = true ↔ o0.val / 16 = 14) ⦄ := by
  simp only [core.net.ip_addr.Ipv4Addr.is_multicast, ipv4Nats_eq self o0 o1 o2 o3 h,
    List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some, ge_iff_le,
    Bool.decide_and, WP.spec_ok, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **Spec theorem for `<Ipv4Addr as From<u32>>::from`**: the big-endian bytes of `ip`, most
significant first; reading them back as a big-endian number gives `ip`.

Model `core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from`. Rust: `Ipv4Addr::from_bits(ip)`
(`ip_addr.rs` lines 1288–1290), `Ipv4Addr { octets: bits.to_be_bytes() }` (lines 608–610).

Used by: A01 `embedded_ipv4` (through `from_u32_segments`). -/
theorem core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_spec (ip : U32) :
    core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from ip
      ⦃ (result : core.net.ip_addr.Ipv4Addr) =>
        result.addrOctets.val.map (fun o => o.val) =
          [ip.val / 2 ^ 24, ip.val / 2 ^ 16 % 256, ip.val / 2 ^ 8 % 256, ip.val % 256] ∧
        ∀ o0 o1 o2 o3 : U8, result.addrOctets.val = [o0, o1, o2, o3] →
          o0.val * 2 ^ 24 + o1.val * 2 ^ 16 + o2.val * 2 ^ 8 + o3.val = ip.val ⦄ := by
  have hip : ip.val < 2 ^ 32 := by scalar_tac
  simp only [core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from, WP.spec_ok,
    Array.from_val]
  refine ⟨?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, byte_val, List.cons.injEq, and_true]
    omega
  · intro o0 o1 o2 o3 heq
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨h0, h1, h2, h3⟩ := heq
    subst h0 h1 h2 h3
    simp only [byte_val]
    omega

/-- **The IPv4 address of two segments**: for `ip = g · 2^16 + h` (the value of
`(u32::from(g) << 16) | u32::from(h)` in A01), the octets are the high and low bytes of `g`,
then of `h`; so an address embedded in the last 32 bits of an IPv6 address has the octets of
those bits. Same model and Rust lines as `from_spec`.

Used by: A01 `embedded_ipv4` (`::ffff:0:0/96`, `64:ff9b::/96`, `::/96` with `g, h`; `2002::/16`
with `b, c`) and C04. -/
theorem core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_u32_segments
    (ip : U32) (g h : U16) (h_ip : ip.val = g.val * 2 ^ 16 + h.val) :
    core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from ip
      ⦃ (result : core.net.ip_addr.Ipv4Addr) =>
        result.addrOctets.val.map (fun o => o.val) =
          [g.val / 256, g.val % 256, h.val / 256, h.val % 256] ⦄ := by
  have hg : g.val < 2 ^ 16 := by scalar_tac
  have hh : h.val < 2 ^ 16 := by scalar_tac
  simp only [core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from, WP.spec_ok,
    Array.from_val, List.map_cons, List.map_nil, byte_val, List.cons.injEq, and_true]
  omega

/-- Every `Ipv6Addr` has eight segments (the model's `Array U16 8#usize`; Rust stores 16
octets, `core/src/net/ip_addr.rs` lines 168–170, and `segments` reads them as eight
big-endian `u16`, lines 1495–1510: the stated change of representation of
`core.net.ip_addr.Ipv6Addr`). -/
theorem core.net.ip_addr.Ipv6Addr.exists_segments (a : core.net.ip_addr.Ipv6Addr) :
    ∃ s0 s1 s2 s3 s4 s5 s6 s7 : U16,
      a.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7] := by
  have hl : a.addrSegments.val.length = 8 := by simp
  generalize a.addrSegments.val = l at hl ⊢
  match l, hl with
  | [s0, s1, s2, s3, s4, s5, s6, s7], _ => exact ⟨s0, s1, s2, s3, s4, s5, s6, s7, rfl⟩

/-- **Spec theorem for `Ipv6Addr::segments`**: the eight segments, most significant first.

Model `core.net.ip_addr.Ipv6Addr.segments`. Rust: lines 1495–1510 of `ip_addr.rs` (segment `i`
is `u16::from_be` of octets `2i`, `2i + 1`), which the model stores.

Used by: A01 (`let [a, b, c, d, e, f, g, h] = addr.segments()`), A03 (`segments[0]`,
`segments[..2]`, `segments[..3]`). -/
theorem core.net.ip_addr.Ipv6Addr.segments_spec (self : core.net.ip_addr.Ipv6Addr) :
    core.net.ip_addr.Ipv6Addr.segments self ⦃ (result : Array U16 8#usize) =>
      result = self.addrSegments ⦄ := by
  simp only [core.net.ip_addr.Ipv6Addr.segments, WP.spec_ok]

/-- **Spec theorem for `Ipv6Addr::is_unspecified`**: exactly `::` (every segment `0`).

Model `core.net.ip_addr.Ipv6Addr.is_unspecified`. Rust: `u128::from_be_bytes(self.octets()) ==
u128::from_be_bytes(Ipv6Addr::UNSPECIFIED.octets())` (`ip_addr.rs` lines 1558–1560),
`UNSPECIFIED = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0)` (line 1479).

Used by: A01 (`::` is not IPv4-compatible), A03 (`::`). -/
theorem core.net.ip_addr.Ipv6Addr.is_unspecified_spec (self : core.net.ip_addr.Ipv6Addr)
    (s0 s1 s2 s3 s4 s5 s6 s7 : U16)
    (h : self.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7]) :
    core.net.ip_addr.Ipv6Addr.is_unspecified self ⦃ (result : Bool) =>
      (result = true ↔ s0.val = 0 ∧ s1.val = 0 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧
        s5.val = 0 ∧ s6.val = 0 ∧ s7.val = 0) ⦄ := by
  simp only [core.net.ip_addr.Ipv6Addr.is_unspecified, ExtModel.beNat, ExtModel.ipv6Nats, h,
    List.map_cons, List.map_nil, List.foldl_cons, zero_mul, zero_add, List.foldl_nil, add_zero,
    Nat.add_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, or_false, and_assoc, Bool.decide_and,
    WP.spec_ok, Bool.and_eq_true, decide_eq_true_eq]

/-- **Spec theorem for `Ipv6Addr::is_loopback`**: exactly `::1`.

Model `core.net.ip_addr.Ipv6Addr.is_loopback`. Rust: `u128::from_be_bytes(self.octets()) ==
u128::from_be_bytes(Ipv6Addr::LOCALHOST.octets())` (`ip_addr.rs` lines 1582–1584),
`LOCALHOST = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)` (line 1462).

Used by: A01 (`::1` is not IPv4-compatible), A03 (`::1`). -/
theorem core.net.ip_addr.Ipv6Addr.is_loopback_spec (self : core.net.ip_addr.Ipv6Addr)
    (s0 s1 s2 s3 s4 s5 s6 s7 : U16)
    (h : self.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7]) :
    core.net.ip_addr.Ipv6Addr.is_loopback self ⦃ (result : Bool) =>
      (result = true ↔ s0.val = 0 ∧ s1.val = 0 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧
        s5.val = 0 ∧ s6.val = 0 ∧ s7.val = 1) ⦄ := by
  have : s0.val < 65536 := by scalar_tac
  have : s1.val < 65536 := by scalar_tac
  have : s2.val < 65536 := by scalar_tac
  have : s3.val < 65536 := by scalar_tac
  have : s4.val < 65536 := by scalar_tac
  have : s5.val < 65536 := by scalar_tac
  have : s6.val < 65536 := by scalar_tac
  have : s7.val < 65536 := by scalar_tac
  simp only [core.net.ip_addr.Ipv6Addr.is_loopback, ExtModel.beNat, ExtModel.ipv6Nats, h,
    List.map_cons, List.map_nil, List.foldl_cons, zero_mul, zero_add, List.foldl_nil, add_zero,
    WP.spec_ok, decide_eq_true_eq]
  omega

/-- **Spec theorem for `Ipv6Addr::is_multicast`**: `ff00::/8` (first eight bits all `1`).

Model `core.net.ip_addr.Ipv6Addr.is_multicast`. Rust: `(self.segments()[0] & 0xff00) ==
0xff00` (`ip_addr.rs` lines 1942–1944), which is `s0.val / 256 = 255`.

Used by: A03 (`ff00::/8`). -/
theorem core.net.ip_addr.Ipv6Addr.is_multicast_spec (self : core.net.ip_addr.Ipv6Addr)
    (s0 s1 s2 s3 s4 s5 s6 s7 : U16)
    (h : self.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7]) :
    core.net.ip_addr.Ipv6Addr.is_multicast self ⦃ (result : Bool) =>
      (result = true ↔ s0.val / 256 = 255) ⦄ := by
  have hs : s0.val < 65536 := by scalar_tac
  have hv : (s0 &&& 65280#u16 = 65280#u16) ↔ (s0 &&& 65280#u16).val = 65280 := by
    constructor
    · intro he; rw [he]; rfl
    · intro he; apply UScalar.eq_of_val_eq; rw [he]; rfl
  simp only [core.net.ip_addr.Ipv6Addr.is_multicast, h, List.getD_cons_zero, WP.spec_ok,
    decide_eq_true_eq]
  rw [hv, UScalar.val_and, show (65280#u16).val = 65280 from rfl, and_65280_eq]
  omega
