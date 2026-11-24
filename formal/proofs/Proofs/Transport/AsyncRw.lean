/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Bytes
import Defs.Methods
import Proofs.External.Std
import Proofs.External.String

/-!
# Spec theorems for the line and method guards of `async_rw.rs` (T04–T06, C05)

`without_carriage_return` drops one trailing `\r` from a line. `is_standard_notification` and
`is_standard_method` compare a method name with the MCP notification (10 names) and request
(18 names, then the notifications) names the code lists. The composition theorem C05 says that
every name the first accepts, the second accepts too.

Source: "crates/rmcp/src/transport/async_rw.rs", lines 385 (T04), 420 (T05) and 396 (T06) at
upstream `7caec76`.
-/

open Aeneas Aeneas.Std Result

namespace rmcp.transport.async_rw

/-! ## T04 -/

/-- **Spec theorem for `rmcp::transport::async_rw::without_carriage_return`** (T04)

If the last byte of `s` is `\r` (`13`), the slice without that one byte; otherwise `s`
unchanged, including for the empty slice (plan Section 16.2, T04; `async_rw.rs` lines 385–387:
`s.strip_suffix(b"\r").unwrap_or(s)`). Only one `\r` is removed: `"a\r\r"` gives `"a\r"`
(plan Section 22). No premise. -/
@[step]
theorem without_carriage_return_spec (s : Slice U8) :
    without_carriage_return s ⦃ (result : Slice U8) =>
      result.val = if s.val.getLast? = some 13#u8 then s.val.dropLast else s.val ⦄ := by
  unfold without_carriage_return
  apply WP.spec_bind (core.slice.Slice.strip_suffix_u8_single_spec s 13#u8)
  intro o ho
  rw [WP.spec_ok]
  cases o with
  | some head => rw [core.option.Option.unwrap_or_some, ho, List.getLast?_concat, if_pos rfl,
      List.dropLast_concat]
  | none => rw [core.option.Option.unwrap_or_none, if_neg ho]

/-! ## T05, T06: MCP method allow-lists (`async_rw.rs` lines 392–433)

The right-hand sides are the independent core-protocol lists of `Defs.Methods` minus the names
the code omits (`Defs.Methods.codeOmits`; code form by H7, the gap recorded as a bug in
`STATUS.md`, "Bugs found"; scope by H6 and its amendment). A name is matched by exact,
case-sensitive byte equality (`matches!` on `&str`, string equality `PartialEq<str> for str`).
The four helpers below are private to this file. -/

/-- One link of the translated `||` chain: if `p` holds the result is `true`, otherwise the rest
of the chain decides, with `Q` as its meaning. -/
private theorem spec_ite_decide_ok_true {p : Prop} [Decidable p] {Q : Prop} {x : Result Bool}
    (hx : x ⦃ (r : Bool) => (r = true ↔ Q) ⦄) :
    (if decide p = true then ok true else x) ⦃ (r : Bool) => (r = true ↔ p ∨ Q) ⦄ := by
  by_cases hp : p
  · rw [if_pos (decide_eq_true hp), WP.spec_ok]
    exact iff_of_true rfl (Or.inl hp)
  · simp only [hp, decide_false, Bool.false_eq_true, if_false, false_or]
    exact hx

/-- The last link of the translated `||` chain. -/
private theorem spec_ite_decide_ok_true_ok_false (p : Prop) [Decidable p] :
    (if decide p = true then ok true else ok false) ⦃ (r : Bool) => (r = true ↔ p) ⦄ := by
  by_cases hp : p
  · rw [if_pos (decide_eq_true hp), WP.spec_ok]
    exact iff_of_true rfl hp
  · rw [if_neg (mt of_decide_eq_true hp), WP.spec_ok]
    exact iff_of_false Bool.false_ne_true hp

/-- Membership in the image of a filtered list, as the statements of T05 and T06 phrase it. -/
private theorem mem_map_utf8Bytes_filter_iff (L : List String) (b : List U8) :
    b ∈ (L.filter (· ∉ Defs.Methods.codeOmits)).map Defs.utf8Bytes ↔
      ∃ n ∈ L, n ∉ Defs.Methods.codeOmits ∧ b = Defs.utf8Bytes n := by
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨n, ⟨hn, ho⟩, he⟩
    exact ⟨n, hn, ho, he.symm⟩
  · rintro ⟨n, hn, ho, he⟩
    exact ⟨n, ⟨hn, ho⟩, he.symm⟩

/-- `is_standard_notification` returns whether `method` is one of the ten names of the Rust list
(`async_rw.rs` lines 423–432), in Rust order. -/
private theorem is_standard_notification_spec_rust (method : Str) :
    is_standard_notification method ⦃ (result : Bool) =>
      (result = true ↔ method.val ∈
        (["notifications/cancelled", "notifications/initialized", "notifications/message",
          "notifications/progress", "notifications/prompts/list_changed",
          "notifications/resources/list_changed", "notifications/resources/updated",
          "notifications/roots/list_changed", "notifications/subscriptions/acknowledged",
          "notifications/tools/list_changed"] : List String).map Defs.utf8Bytes) ⦄ := by
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    Proofs.External.Utf8.utf8Bytes_eq_utf8]
  unfold is_standard_notification
  simp only [Str.Insts.CoreCmpPartialEqStr.eq_eq, Proofs.External.Utf8.toStr_val, bind_tc_ok]
  repeat (first | apply spec_ite_decide_ok_true_ok_false | apply spec_ite_decide_ok_true)

/-- **Spec theorem for `rmcp::transport::async_rw::is_standard_notification`** (T05)

`true` exactly when `method` is, byte for byte, one of the core-protocol MCP notification names
(the union of the five known core schemas, `Defs.Methods.standardNotifications`, H6) other than
those the code omits (`Defs.Methods.codeOmits`: `notifications/tasks/status`,
`notifications/elicitation/complete`; code form by H7, a recorded bug); `false` for every other
string, including a prefix or suffix of a name, a case variant, `notifications/unknown`, the
out-of-scope names `notifications/tasks` and `notifications/elicitation/response` (H6
amendment) and the empty string (plan Section 16.2, T05; Section 21, H6, H7; Section 22;
`async_rw.rs` lines 420–433, ten names). No premise. -/
@[step]
theorem is_standard_notification_spec (method : Str) :
    is_standard_notification method ⦃ (result : Bool) =>
      (result = true ↔
        ∃ n ∈ Defs.Methods.standardNotifications,
          n ∉ Defs.Methods.codeOmits ∧ method.val = Defs.utf8Bytes n) ⦄ := by
  have hp : (Defs.Methods.standardNotifications.filter (· ∉ Defs.Methods.codeOmits)).Perm
      ["notifications/cancelled", "notifications/initialized", "notifications/message",
       "notifications/progress", "notifications/prompts/list_changed",
       "notifications/resources/list_changed", "notifications/resources/updated",
       "notifications/roots/list_changed", "notifications/subscriptions/acknowledged",
       "notifications/tools/list_changed"] := by
    decide
  simp only [← mem_map_utf8Bytes_filter_iff, (hp.map Defs.utf8Bytes).mem_iff]
  exact is_standard_notification_spec_rust method

/-- **Spec theorem for `rmcp::transport::async_rw::is_standard_method`** (T06)

`true` exactly when `method` is, byte for byte, a core-protocol MCP request name (the union of
the five known core schemas, `Defs.Methods.standardRequests`, H6) other than those the code
omits (`tasks/get`, `tasks/result`, `tasks/cancel`, `tasks/list`; code form by H7, a recorded
bug), or a name T05 accepts; the out-of-scope name `tasks/update` (H6) gives `false` (plan
Section 16.2, T06: "`standardRequests` ∨ T05"; Section 21, H6, H7; `async_rw.rs` lines 392–417:
18 request names `|| is_standard_notification(method)`). No premise. -/
@[step]
theorem is_standard_method_spec (method : Str) :
    is_standard_method method ⦃ (result : Bool) =>
      (result = true ↔
        (∃ n ∈ Defs.Methods.standardRequests,
          n ∉ Defs.Methods.codeOmits ∧ method.val = Defs.utf8Bytes n) ∨
        (∃ n ∈ Defs.Methods.standardNotifications,
          n ∉ Defs.Methods.codeOmits ∧ method.val = Defs.utf8Bytes n)) ⦄ := by
  have hp : (Defs.Methods.standardRequests.filter (· ∉ Defs.Methods.codeOmits)).Perm
      [Defs.Methods.handshakeRequest, "ping", "server/discover", "prompts/get", "prompts/list",
       "resources/list", "resources/read", "resources/subscribe", "resources/unsubscribe",
       "resources/templates/list", "subscriptions/listen", "tools/call", "tools/list",
       "completion/complete", "elicitation/create", "logging/setLevel", "roots/list",
       "sampling/createMessage"] := by
    decide
  obtain ⟨r, hr, hn⟩ := WP.spec_imp_exists (is_standard_notification_spec method)
  rw [← mem_map_utf8Bytes_filter_iff, (hp.map Defs.utf8Bytes).mem_iff, ← hn]
  generalize hL : List.map Defs.utf8Bytes [Defs.Methods.handshakeRequest, "ping",
    "server/discover", "prompts/get", "prompts/list", "resources/list", "resources/read",
    "resources/subscribe", "resources/unsubscribe", "resources/templates/list",
    "subscriptions/listen", "tools/call", "tools/list", "completion/complete",
    "elicitation/create", "logging/setLevel", "roots/list", "sampling/createMessage"] = L
  unfold is_standard_method
  rw [hr]
  simp only [Str.Insts.CoreCmpPartialEqStr.eq_eq, Proofs.External.Utf8.toStr_val, bind_tc_ok]
  refine WP.spec_bind (Pₘ := fun b => (b = true ↔ method.val ∈ L)) ?_ ?_
  · rw [← hL]
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      Proofs.External.Utf8.utf8Bytes_eq_utf8, Defs.Methods.handshakeRequest]
    repeat (first | apply spec_ite_decide_ok_true_ok_false | apply spec_ite_decide_ok_true)
  · intro b hb
    cases b
    · rw [if_neg Bool.false_ne_true, WP.spec_ok]
      exact ⟨Or.inr, fun h => h.resolve_left fun hm => absurd (hb.2 hm) Bool.false_ne_true⟩
    · rw [if_pos rfl, WP.spec_ok]
      exact iff_of_true rfl (Or.inl (hb.1 rfl))

/-! ## Composition theorem C05 -/

/-- **C05 `is_standard_method_of_is_standard_notification`**: every method that
`is_standard_notification` accepts, `is_standard_method` accepts too; the allow-lists are
consistent (plan Section 16.4, C05; uses T05, T06; `async_rw.rs` line 417,
`|| is_standard_notification(method)`). About the translated functions
`is_standard_notification` and `is_standard_method`. It takes a successful call returning `true`
as its hypothesis, and covers only that case; T05 shows that the call never fails. Not tagged
`@[step]`. -/
theorem is_standard_method_of_is_standard_notification (method : Str)
    (h : is_standard_notification method = ok true) :
    is_standard_method method = ok true := by
  have hn := is_standard_notification_spec method
  rw [h, WP.spec_ok] at hn
  obtain ⟨r, hr, hm⟩ := WP.spec_imp_exists (is_standard_method_spec method)
  rw [hr, hm.2 (Or.inr (hn.1 rfl))]

end rmcp.transport.async_rw
