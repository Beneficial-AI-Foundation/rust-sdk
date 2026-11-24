/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Mathlib.Data.Nat.Digits.Defs
import Proofs.External.Byte
import Proofs.External.String
import Defs.IntParse

/-!
# Laws of the Phase 2 external models: IntParse (plan steps S26/S27, stage 6)

Proofs of the Phase 2 laws signed off by the spec owner on 2026-11-23 (plan steps S26/S27),
restated in `formal/specs/Specs/External.lean` (Phase 2 part); the draft file was removed at
incorporation. For this group (spec owner sign-off 2026-11-23): `str::parse` and `i64::from_str`.

The digit loop `ExtModel.i64DigitLoop` is described by `i64DigitLoop_eq`: from a magnitude `a`
in range, it reads the longest digit prefix `d` of its input, and its result depends only on
the value `digitFold a d` (the left fold `s ↦ 10 * s + digit`), which is at least every
accumulated value of the loop, so an overflow at some digit is an out-of-range final value.

The S27 deferred law `from_str_eq_parseI64` (signed off 2026-11-24, S24/S25 spec cycle) relates
the model to the documented grammar `Defs.parseI64`, through `parseI64_append` and `from_str_eq`.
-/

open Aeneas Aeneas.Std Result
open rmcp ExtModel

namespace Proofs.External.IntParse

open Proofs.External.Utf8 Proofs.External.Byte

/-- The decimal-digit test of the statements. -/
def isDigit (c : U8) : Bool := decide (48 ≤ c.val ∧ c.val ≤ 57)

/-- The value of the digits `l` read left to right after the value `acc`. -/
def digitFold (acc : Nat) (l : List U8) : Nat :=
  l.foldl (fun s c => 10 * s + (c.val - 48)) acc

/-- The range of the magnitude: `< 2^63` for a positive value, `≤ 2^63` for a negative one. -/
def InRange (positive : Bool) (x : Nat) : Prop :=
  if positive then x < 2 ^ 63 else x ≤ 2 ^ 63

instance (positive : Bool) (x : Nat) : Decidable (InRange positive x) := by
  unfold InRange; split <;> infer_instance

/-- The signed value of a magnitude. -/
def signed (positive : Bool) (x : Nat) : Int := if positive then (x : Int) else -(x : Int)

theorem le_digitFold (acc : Nat) (l : List U8) : acc ≤ digitFold acc l := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons c t ih =>
    have := ih (10 * acc + (c.val - 48))
    simp only [digitFold, List.foldl_cons] at this ⊢
    omega

theorem inRange_mono {positive : Bool} {x y : Nat} (hxy : x ≤ y) (hy : InRange positive y) :
    InRange positive x := by
  unfold InRange at hy ⊢
  split at hy <;> simp only [*, if_true, if_false, Bool.false_eq_true] <;> omega

/-- The digit loop, from a magnitude in range. -/
theorem i64DigitLoop_eq (positive : Bool) (a : Nat) (l : List U8) (ha : InRange positive a) :
    i64DigitLoop positive (signed positive a) l =
      if InRange positive (digitFold a (l.takeWhile isDigit)) then
        (if l.takeWhile isDigit = l then .ok (signed positive (digitFold a (l.takeWhile isDigit)))
          else .error .InvalidDigit)
      else .error (if positive then .PosOverflow else .NegOverflow) := by
  induction l generalizing a with
  | nil =>
    simp only [i64DigitLoop, List.takeWhile_nil, digitFold, List.foldl_nil, if_true, ha]
  | cons c t ih =>
    by_cases hc : 48 ≤ c.val ∧ c.val ≤ 57
    · have hd : isDigit c = true := by simp only [isDigit, decide_eq_true_eq]; exact hc
      have hdec : decDigit? c = some (c.val - 48) := by rw [decDigit?, if_pos hc]
      rw [List.takeWhile_cons_of_pos hd]
      have hfold : digitFold a (c :: t.takeWhile isDigit) =
          digitFold (10 * a + (c.val - 48)) (t.takeWhile isDigit) := by
        simp only [digitFold, List.foldl_cons]
      rw [hfold]
      have hnext : (if positive then signed positive a * 10 + ((c.val - 48 : Nat) : Int)
          else signed positive a * 10 - ((c.val - 48 : Nat) : Int)) =
          signed positive (10 * a + (c.val - 48)) := by
        cases positive <;> simp only [signed, if_true, if_false, Bool.false_eq_true] <;> push_cast
          <;> ring
      simp only [i64DigitLoop, hdec, hnext]
      have hle := le_digitFold (10 * a + (c.val - 48)) (t.takeWhile isDigit)
      by_cases hr : InRange positive (10 * a + (c.val - 48))
      · have hr' : -2 ^ 63 ≤ signed positive (10 * a + (c.val - 48)) ∧
            signed positive (10 * a + (c.val - 48)) < 2 ^ 63 := by
          unfold InRange at hr; unfold signed
          cases positive <;> simp only [if_true, if_false, Bool.false_eq_true] at hr ⊢ <;> omega
        rw [if_pos hr', ih _ hr]
        simp only [List.cons.injEq, true_and]
      · have hr' : ¬ (-2 ^ 63 ≤ signed positive (10 * a + (c.val - 48)) ∧
            signed positive (10 * a + (c.val - 48)) < 2 ^ 63) := by
          unfold InRange at hr; unfold signed
          cases positive <;> simp only [if_true, if_false, Bool.false_eq_true] at hr ⊢ <;> omega
        rw [if_neg hr', if_neg (fun h => hr (inRange_mono hle h))]
    · have hd : isDigit c = false := by simp only [isDigit, decide_eq_false_iff_not]; exact hc
      have hdec : decDigit? c = none := by rw [decDigit?, if_neg hc]
      rw [List.takeWhile_cons_of_neg (by simp only [hd]; decide)]
      simp only [i64DigitLoop, hdec, digitFold, List.foldl_nil, ha, if_true]
      rw [if_neg (fun h => List.cons_ne_nil _ _ h.symm)]

theorem digitFold_eq_ofDigits (acc : Nat) (l : List U8) :
    digitFold acc l =
      acc * 10 ^ l.length + Nat.ofDigits 10 (l.map (fun c => c.val - 48)).reverse := by
  induction l generalizing acc with
  | nil => simp only [digitFold, List.foldl_nil, List.length_nil, pow_zero, mul_one, List.map_nil,
      List.reverse_nil, Nat.ofDigits_nil, add_zero]
  | cons c t ih =>
    have := ih (10 * acc + (c.val - 48))
    simp only [digitFold, List.foldl_cons] at this ⊢
    rw [this, List.map_cons, List.reverse_cons, Nat.ofDigits_append, Nat.ofDigits_singleton,
      List.length_reverse, List.length_map, List.length_cons, pow_succ]
    ring

/-- The model on `sign ++ body`, as the loop on `body`. -/
theorem i64FromAscii_eq (sign body : List U8)
    (h_sign : sign = [] ∨ sign = [43#u8] ∨ sign = [45#u8])
    (h_body : body ≠ [])
    (h_unsigned : sign = [] → ∀ c ∈ body.head?, c.val ≠ 43 ∧ c.val ≠ 45) :
    i64FromAscii (sign ++ body) =
      i64DigitLoop (decide (sign ≠ [45#u8])) (signed (decide (sign ≠ [45#u8])) 0) body := by
  obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil h_body
  rcases h_sign with rfl | rfl | rfl
  · have hc := h_unsigned rfl c rfl
    cases t with
    | nil => simp only [List.nil_append, i64FromAscii, hc, or_self, if_false, signed]; rfl
    | cons c' t' => simp only [List.nil_append, i64FromAscii, hc, if_false, signed]; rfl
  · simp only [List.cons_append, List.nil_append, i64FromAscii]; rfl
  · simp only [List.cons_append, List.nil_append, i64FromAscii]; rfl

/-- The model `from_str` on `sign ++ body`, as one case split. -/
theorem from_str_eq (src : Str) (sign body : List U8)
    (h_src : src.val = sign ++ body)
    (h_sign : sign = [] ∨ sign = [43#u8] ∨ sign = [45#u8])
    (h_body : body ≠ [])
    (h_unsigned : sign = [] → ∀ c ∈ body.head?, c.val ≠ 43 ∧ c.val ≠ 45) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src =
      ok (if InRange (decide (sign ≠ [45#u8])) (digitFold 0 (body.takeWhile isDigit)) then
          (if body.takeWhile isDigit = body then
            core.result.Result.Ok
              ⟨BitVec.ofInt 64 (signed (decide (sign ≠ [45#u8]))
                (digitFold 0 (body.takeWhile isDigit)))⟩
          else core.result.Result.Err { kind := .InvalidDigit })
        else core.result.Result.Err
          { kind := if decide (sign ≠ [45#u8]) then .PosOverflow else .NegOverflow }) := by
  have h0 : InRange (decide (sign ≠ [45#u8])) 0 := by
    unfold InRange; split <;> omega
  rw [I64.Insts.CoreStrTraitsFromStrParseIntError.from_str, h_src,
    i64FromAscii_eq sign body h_sign h_body h_unsigned, i64DigitLoop_eq _ 0 body h0]
  split_ifs <;> rfl

theorem digitFold_append (acc : Nat) (l m : List U8) :
    digitFold acc (l ++ m) = digitFold (digitFold acc l) m := by
  simp only [digitFold, List.foldl_append]

theorem digitFold_replicate_zero (k : Nat) : digitFold 0 (List.replicate k 48#u8) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, digitFold, List.foldl_cons]
    exact ih

theorem takeWhile_isDigit_eq_self (l : List U8) (h : ∀ b ∈ l, isDigit b = true) :
    l.takeWhile isDigit = l := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    rw [List.takeWhile_cons_of_pos (h c (List.mem_cons_self))]
    rw [ih (fun b hb => h b (List.mem_cons_of_mem c hb))]

/-- The bytes of the decimal digits of `m`. -/
def digitBytes (m : Nat) : List U8 := (Nat.toDigits 10 m).map (fun ch => byte ch.toNat)

theorem toNat_of_mem_toDigits {m : Nat} {ch : Char} (h : ch ∈ Nat.toDigits 10 m) :
    48 ≤ ch.toNat ∧ ch.toNat ≤ 57 := by
  have := Nat.isDigit_of_mem_toDigits (by omega) (by omega) h
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
  have h1 := this.1
  have h2 := this.2
  simp only [Char.toNat]
  exact ⟨UInt32.le_iff_toNat_le.1 h1, UInt32.le_iff_toNat_le.1 h2⟩

theorem utf8_toString (m : Nat) : utf8 (toString m) = digitBytes m := by
  have h : Nat.toDigits 10 m = (digitBytes m).map (fun b => Char.ofNat b.val) := by
    rw [digitBytes, List.map_map]
    conv => lhs; rw [← List.map_id (Nat.toDigits 10 m)]
    apply List.map_congr_left
    intro ch hch
    have := toNat_of_mem_toDigits hch
    simp only [Function.comp, byte_val, id]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact (Char.ofNat_toNat ch).symm
  rw [Nat.toString_eq_ofList_toDigits, h, utf8_ofList_ascii]
  intro b hb
  rw [digitBytes, List.mem_map] at hb
  obtain ⟨ch, hch, rfl⟩ := hb
  have := toNat_of_mem_toDigits hch
  rw [byte_val]
  omega

theorem isDigit_of_mem_digitBytes (m : Nat) : ∀ b ∈ digitBytes m, isDigit b = true := by
  intro b hb
  rw [digitBytes, List.mem_map] at hb
  obtain ⟨ch, hch, rfl⟩ := hb
  have := toNat_of_mem_toDigits hch
  simp only [isDigit, byte_val, decide_eq_true_eq]
  omega

theorem digitFold_map (acc : Nat) (L : List Char) (h : ∀ ch ∈ L, ch.toNat < 256) :
    digitFold acc (L.map (fun ch => byte ch.toNat)) = Nat.ofDigitChars 10 L acc := by
  induction L generalizing acc with
  | nil => rfl
  | cons ch t ih =>
    rw [List.map_cons, digitFold, List.foldl_cons, Nat.ofDigitChars_cons, ← digitFold,
      byte_val, Nat.mod_eq_of_lt (h ch List.mem_cons_self)]
    exact ih _ (fun c hc => h c (List.mem_cons_of_mem ch hc))

theorem digitFold_digitBytes (m : Nat) : digitFold 0 (digitBytes m) = m := by
  rw [digitBytes, digitFold_map]
  · exact Nat.ofDigitChars_ten_toDigits
  · intro ch hch
    have := toNat_of_mem_toDigits hch
    omega

theorem digitBytes_ne_nil (m : Nat) : digitBytes m ≠ [] := by
  rw [digitBytes, ne_eq, List.map_eq_nil_iff]
  exact Nat.toDigits_ne_nil

end Proofs.External.IntParse

open Proofs.External.IntParse Proofs.External.Byte Proofs.External.Utf8

/-- **`i64::from_str` on the empty input**: `Err` with kind `Empty`. -/
theorem I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_empty
    (src : Str) (h : src.val = []) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src =
      ok (core.result.Result.Err { kind := ExtModel.IntErrorKind.Empty }) := by
  rw [I64.Insts.CoreStrTraitsFromStrParseIntError.from_str, h]
  rfl

/-- **`i64::from_str` on a lone sign** (`"+"` or `"-"`): `Err` with kind `InvalidDigit`. -/
theorem I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_lone_sign
    (src : Str) (c : U8) (h : src.val = [c]) (hc : c.val = 43 ∨ c.val = 45) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src =
      ok (core.result.Result.Err { kind := ExtModel.IntErrorKind.InvalidDigit }) := by
  rw [I64.Insts.CoreStrTraitsFromStrParseIntError.from_str, h]
  simp only [i64FromAscii, hc, if_true]

/-- **Spec theorem for `i64::from_str`** on every input `sign ++ body` with `body` nonempty:
the exact result, by `from_str_eq`. -/
theorem I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_spec
    (src : Str) (sign body : List U8)
    (h_src : src.val = sign ++ body)
    (h_sign : sign = [] ∨ sign = [43#u8] ∨ sign = [45#u8])
    (h_body : body ≠ [])
    (h_unsigned : sign = [] → ∀ c ∈ body.head?, c.val ≠ 43 ∧ c.val ≠ 45) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src
      ⦃ (result : core.result.Result I64 core.num.error.ParseIntError) =>
        let neg : Prop := sign = [45#u8]
        let d := body.takeWhile (fun c => decide (48 ≤ c.val ∧ c.val ≤ 57))
        let v : Nat := Nat.ofDigits 10 (d.map (fun c => c.val - 48)).reverse
        let overflow : Prop := (neg ∧ 2 ^ 63 < v) ∨ (¬ neg ∧ 2 ^ 63 ≤ v)
        match result with
        | core.result.Result.Ok n =>
          ¬ overflow ∧ d = body ∧ n.val = (if neg then -(v : Int) else (v : Int))
        | core.result.Result.Err e =>
          (overflow ∧ (neg → e.kind = ExtModel.IntErrorKind.NegOverflow) ∧
              (¬ neg → e.kind = ExtModel.IntErrorKind.PosOverflow)) ∨
            (¬ overflow ∧ d ≠ body ∧ e.kind = ExtModel.IntErrorKind.InvalidDigit) ⦄ := by
  rw [from_str_eq src sign body h_src h_sign h_body h_unsigned, WP.spec_ok]
  have hfun : (fun c : U8 => decide (48 ≤ c.val ∧ c.val ≤ 57)) = isDigit := rfl
  have hv : Nat.ofDigits 10 ((body.takeWhile isDigit).map (fun c => c.val - 48)).reverse =
      digitFold 0 (body.takeWhile isDigit) := by
    rw [digitFold_eq_ofDigits, Nat.zero_mul, Nat.zero_add]
  simp only [hfun, hv]
  generalize body.takeWhile isDigit = d
  generalize digitFold 0 d = v
  have hv64 : ∀ x : Int, -2 ^ 63 ≤ x → x < 2 ^ 63 →
      (⟨BitVec.ofInt 64 x⟩ : I64).val = x := by
    intro x h1 h2
    show (BitVec.ofInt 64 x).toInt = x
    rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  by_cases hneg : sign = [45#u8]
  · simp only [hneg, ne_eq, not_true_eq_false, decide_false, InRange, signed, if_false,
      Bool.false_eq_true, true_and, if_true, not_true_eq_false, false_and, or_false]
    split_ifs with h1 h2
    · simp only [hv64 (-(v : Int)) (by omega) (by omega)]
      exact ⟨by omega, h2, trivial⟩
    · exact Or.inr ⟨by omega, h2, rfl⟩
    · exact Or.inl ⟨by omega, fun _ => rfl, False.elim⟩
  · simp only [hneg, ne_eq, not_false_eq_true, decide_true, InRange, signed, if_true,
      false_and, false_or, true_and, if_false]
    split_ifs with h1 h2
    · simp only [hv64 (v : Int) (by omega) (by omega)]
      exact ⟨by omega, h2, trivial⟩
    · exact Or.inr ⟨by omega, h2, rfl⟩
    · exact Or.inl ⟨by omega, fun h => h.elim, fun _ => rfl⟩

/-- **Round trip with an explicit sign and leading zeros**: `sign`, then `k` zeros, then the
decimal digits of `|n|` parse to `n`. -/
theorem I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_signed_toString
    (n : I64) (src : Str) (sign : List U8) (k : Nat)
    (h_sign : (sign = [] ∧ 0 ≤ n.val) ∨ (sign = [43#u8] ∧ 0 ≤ n.val) ∨
      (sign = [45#u8] ∧ n.val ≤ 0))
    (h_src : src.val = sign ++ List.replicate k 48#u8 ++ utf8 (toString n.val.natAbs)) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src =
      ok (core.result.Result.Ok n) := by
  rw [utf8_toString, List.append_assoc] at h_src
  have hdig : ∀ b ∈ List.replicate k 48#u8 ++ digitBytes n.val.natAbs, isDigit b = true := by
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · rw [List.eq_of_mem_replicate hb]; rfl
    · exact isDigit_of_mem_digitBytes _ b hb
  have hne : List.replicate k 48#u8 ++ digitBytes n.val.natAbs ≠ [] := by
    rw [ne_eq, List.append_eq_nil_iff, not_and]
    exact fun _ => digitBytes_ne_nil _
  have htw : (List.replicate k 48#u8 ++ digitBytes n.val.natAbs).takeWhile isDigit =
      List.replicate k 48#u8 ++ digitBytes n.val.natAbs :=
    takeWhile_isDigit_eq_self _ hdig
  have hval : digitFold 0 (List.replicate k 48#u8 ++ digitBytes n.val.natAbs) = n.val.natAbs := by
    rw [digitFold_append, digitFold_replicate_zero, digitFold_digitBytes]
  have hunsigned : sign = [] →
      ∀ c ∈ (List.replicate k 48#u8 ++ digitBytes n.val.natAbs).head?,
        c.val ≠ 43 ∧ c.val ≠ 45 := by
    intro _ c hc
    have := hdig c (List.mem_of_mem_head? hc)
    simp only [isDigit, decide_eq_true_eq] at this
    omega
  have hsign : sign = [] ∨ sign = [43#u8] ∨ sign = [45#u8] := by
    rcases h_sign with h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr h.1)
  rw [from_str_eq src sign _ h_src hsign hne hunsigned, htw, hval, if_pos rfl]
  have hb := n.hBounds
  have hn : ∀ x : Int, x = n.val → (⟨BitVec.ofInt 64 x⟩ : I64) = n := by
    intro x hx
    subst hx
    show (⟨BitVec.ofInt 64 n.bv.toInt⟩ : I64) = n
    rw [BitVec.ofInt_toInt]
  have hb' : -2 ^ 63 ≤ n.val ∧ n.val < 2 ^ 63 := hb
  rcases h_sign with ⟨rfl, h0⟩ | ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · have hr : InRange (decide (([] : List U8) ≠ [45#u8])) n.val.natAbs := by
      show n.val.natAbs < 2 ^ 63
      omega
    rw [if_pos hr, hn _ (by show ((n.val.natAbs : Nat) : Int) = n.val; omega)]
  · have h43 : decide (([43#u8] : List U8) ≠ [45#u8]) = true := by decide
    have hr : InRange true n.val.natAbs := by
      show n.val.natAbs < 2 ^ 63
      omega
    rw [h43, if_pos hr, hn _ (by show ((n.val.natAbs : Nat) : Int) = n.val; omega)]
  · have h45 : decide (([45#u8] : List U8) ≠ [45#u8]) = false := by decide
    have hr : InRange false n.val.natAbs := by
      show n.val.natAbs ≤ 2 ^ 63
      omega
    rw [h45, if_pos hr, hn _ (by show -((n.val.natAbs : Nat) : Int) = n.val; omega)]

/-- **Round trip of `i64::from_str`**: parsing `toString n.val` gives `n` (the case `k = 0` of
`from_str_signed_toString`). -/
theorem I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_toString
    (n : I64) (src : Str) (h_src : src.val = utf8 (toString n.val)) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src =
      ok (core.result.Result.Ok n) := by
  cases h : n.val with
  | ofNat m =>
    rw [h] at h_src
    apply I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_signed_toString n src [] 0
      (Or.inl ⟨rfl, by rw [h]; exact Int.natCast_nonneg m⟩)
    rw [h_src, h]
    rfl
  | negSucc m =>
    rw [h] at h_src
    apply I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_signed_toString n src [45#u8] 0
      (Or.inr (Or.inr ⟨rfl, by omega⟩))
    rw [h_src, h]
    show utf8 ("-" ++ toString (m + 1)) = _
    have hminus : utf8 "-" = [45#u8] := by decide +kernel
    rw [utf8_append, hminus, List.replicate_zero, List.append_nil]
    rfl

/-- `str::parse` calls `from_str` of the `FromStr` instance, including its failure. -/
theorem core.str.Str.parse_eq {F : Type} {Clause0_Err : Type}
    (traitsFromStrInst : core.str.traits.FromStr F Clause0_Err) (self : Str) :
    core.str.Str.parse traitsFromStrInst self = traitsFromStrInst.from_str self := by
  rfl

namespace Proofs.External.IntParse

/-- `Defs.parseI64` on `sign ++ body` with an explicit sign split. -/
theorem parseI64_append (sign body : List U8)
    (h_sign : sign = [] ∨ sign = [43#u8] ∨ sign = [45#u8])
    (h_body : body ≠ [])
    (h_unsigned : sign = [] → ∀ c ∈ body.head?, c.val ≠ 43 ∧ c.val ≠ 45) :
    Defs.parseI64 (sign ++ body) =
      if body.all isDigit = true then
        (if InRange (decide (sign ≠ [45#u8])) (digitFold 0 body) then
          some (signed (decide (sign ≠ [45#u8])) (digitFold 0 body))
        else none)
      else none := by
  have hsplit : Defs.IntParse.splitSign (sign ++ body) = (decide (sign = [45#u8]), body) := by
    obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil h_body
    rcases h_sign with rfl | rfl | rfl
    · have hc := h_unsigned rfl c rfl
      have h1 : c ≠ Defs.IntParse.plus := fun h => hc.1 (by rw [h]; rfl)
      have h2 : c ≠ Defs.IntParse.minus := fun h => hc.2 (by rw [h]; rfl)
      rw [List.nil_append, Defs.IntParse.splitSign, if_neg h1, if_neg h2]
      rfl
    · rfl
    · rfl
  have hfold : Defs.IntParse.digitsValue body = digitFold 0 body := rfl
  have hdig : Defs.IntParse.isAsciiDigit = isDigit := rfl
  unfold Defs.parseI64
  rw [hsplit]
  simp only [hfold, hdig, ne_eq, h_body, not_false_eq_true, true_and]
  by_cases hneg : sign = [45#u8]
  · simp only [List.all_eq_true, Defs.IntParse.i64Min, Int.reducePow, Int.reduceNeg, hneg,
      decide_true, ↓reduceIte, neg_le_neg_iff, Nat.cast_le_ofNat, Defs.IntParse.i64Max,
      Int.reduceSub, Int.neg_natCast_le_ofNat, and_true, InRange, not_true_eq_false, decide_false,
      Bool.false_eq_true, Nat.reducePow, signed]
  · simp only [List.all_eq_true, Defs.IntParse.i64Min, Int.reducePow, Int.reduceNeg, hneg,
      decide_false, Bool.false_eq_true, ↓reduceIte, Int.neg_ofNat_le_natCast,
      Defs.IntParse.i64Max, Int.reduceSub, Nat.cast_le_ofNat, true_and, InRange,
      not_false_eq_true, decide_true, Nat.reducePow, signed]
    split_ifs <;> first | rfl | omega

/-- The digit prefix is the whole list exactly when every byte is a digit. -/
theorem takeWhile_isDigit_eq_self_iff (l : List U8) :
    l.takeWhile isDigit = l ↔ l.all isDigit = true :=
  ⟨fun h => h ▸ List.all_takeWhile,
    fun h => takeWhile_isDigit_eq_self l (List.all_eq_true.1 h)⟩

end Proofs.External.IntParse

open Proofs.External.IntParse

/-- **S27 deferred law.** `i64::from_str` (the model in `trusted/Rmcp/FunsExternal.lean`) never
fails, and it returns `Ok n` exactly when `Defs.parseI64` accepts the bytes of `src`, with
`n.val` the value `Defs.parseI64` gives; otherwise `Err _` (the error kind is not constrained:
M06 discards it). -/
theorem I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64 (src : Str) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src
      ⦃ (result : core.result.Result I64 core.num.error.ParseIntError) =>
        (match result with
         | .Ok n => some n.val
         | .Err _ => none) = Defs.parseI64 src.val ⦄ := by
  have main : ∀ (sign body : List U8), src.val = sign ++ body →
      (sign = [] ∨ sign = [43#u8] ∨ sign = [45#u8]) → body ≠ [] →
      (sign = [] → ∀ c ∈ body.head?, c.val ≠ 43 ∧ c.val ≠ 45) →
      I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src
      ⦃ (result : core.result.Result I64 core.num.error.ParseIntError) =>
        (match result with
         | .Ok n => some n.val
         | .Err _ => none) = Defs.parseI64 src.val ⦄ := by
    intro sign body h_src h_sign h_body h_unsigned
    rw [from_str_eq src sign body h_src h_sign h_body h_unsigned, WP.spec_ok, h_src,
      parseI64_append sign body h_sign h_body h_unsigned]
    have hv64 : ∀ x : Int, -2 ^ 63 ≤ x → x < 2 ^ 63 →
        (⟨BitVec.ofInt 64 x⟩ : I64).val = x := by
      intro x h1 h2
      show (BitVec.ofInt 64 x).toInt = x
      rw [BitVec.toInt_ofInt]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    by_cases hall : body.all isDigit = true
    · have htw := (takeWhile_isDigit_eq_self_iff body).2 hall
      rw [htw, if_pos hall]
      by_cases hr : InRange (decide (sign ≠ [45#u8])) (digitFold 0 body)
      · rw [if_pos hr, if_pos hr, if_pos rfl]
        show some (⟨BitVec.ofInt 64 _⟩ : I64).val = _
        rw [hv64]
        · revert hr; unfold InRange signed; split <;> intro hr <;> omega
        · revert hr; unfold InRange signed; split <;> intro hr <;> omega
      · rw [if_neg hr, if_neg hr]
    · have htw : ¬ body.takeWhile isDigit = body :=
        fun h => hall ((takeWhile_isDigit_eq_self_iff body).1 h)
      rw [if_neg hall]
      split_ifs <;> rfl
  rcases hs : src.val with _ | ⟨c, t⟩
  · rw [I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_empty src hs, WP.spec_ok]
    rfl
  · by_cases hsg : c.val = 43 ∨ c.val = 45
    · have hc : c = 43#u8 ∨ c = 45#u8 := by
        rcases hsg with h | h
        · exact Or.inl (UScalar.eq_of_val_eq (by simp only [h, UScalar.ofNatCore_val_eq]))
        · exact Or.inr (UScalar.eq_of_val_eq (by simp only [h, UScalar.ofNatCore_val_eq]))
      by_cases ht : t = []
      · subst ht
        rw [I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_lone_sign src c hs hsg,
          WP.spec_ok]
        rcases hc with rfl | rfl <;> rfl
      · rw [← hs]
        exact main [c] t (by rw [hs]; rfl) (by rcases hc with rfl | rfl <;> decide) ht
          (fun h => absurd h (List.cons_ne_nil c []))
    · rw [← hs]
      exact main [] (c :: t) (by rw [hs]; rfl) (Or.inl rfl) (List.cons_ne_nil _ _)
        (fun _ x hx => by
          rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
          subst hx; omega)
