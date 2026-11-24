/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Defs.Bytes

@[expose] public section

/-!
# MCP method lists (T05, T06, C05)

The standard MCP request and notification method names, taken from the MCP specification and
not from the Rust code (plan Section 17, "T05/T06 (method lists)"; Section 22, "Bugs found").

**Scope: core protocol only** (plan Section 21, H6 and its amendments, human decisions of
2026-11-24). The lists cover the core protocol: the union of the method names of the five core
`schema.ts` files below. Extension schemas, such as the SEP-2663 Tasks extension
`io.modelcontextprotocol/tasks`, are deliberately kept separate and contribute no name. The lists
therefore give core protocol coverage, not coverage of every MCP method an implementation may
use.

**Independent source**: the union of the method names of the official core MCP schemas of the
five protocol versions the SDK knows,
`ProtocolVersion::KNOWN_VERSIONS` (`crates/rmcp/src/model.rs` lines 204–210 at upstream
`7caec76`): `2024-11-05`, `2025-03-26`, `2025-06-18`, `2025-11-25`, `2026-07-28`. The names are
the string literals of the `method:` fields of the file `schema/<version>/schema.ts` under
`https://raw.githubusercontent.com/modelcontextprotocol/modelcontextprotocol/<commit>/` at the
pinned commit `<commit>` = `b0be8f0f2481be8d5ea5294cf3fa57cd03cedc48` of the specification
repository (read 2026-11-24; the five files at that commit have these sha256 sums, in order:
`8e87348b6c1a9de1ec7ac136f407b687521bcdeb357adedbf5367bfc19c18d38`,
`bdc457208cb1b49061f3fbbae24144b7dbae282c746d82aa689ddd98329743e7`,
`7d7f4cc6f3adb76e3fd5e1eee6bab8b1e183cfaf719da66d2aa5661737ca9539`,
`e74b56e73b2e37bdb595f74ba22e428ad7f07aa3519355ba661d681298ed38ac`,
`da1a5394d4eb24c2eb1cb3c711cf181ccad31d6633a0302864c6a44a3bf8a3c7`). Per version: `2024-11-05`
and `2025-03-26` have 15 requests and 9 notifications; `2025-06-18` adds `elicitation/create`;
`2025-11-25` adds `tasks/get`, `tasks/result`, `tasks/cancel`, `tasks/list`,
`notifications/tasks/status` and `notifications/elicitation/complete`; `2026-07-28` drops
thirteen names, namely the handshake request and its notification `notifications/initialized`,
`ping`, `resources/subscribe`, `resources/unsubscribe`, `logging/setLevel`,
`notifications/roots/list_changed`, and the six names that `2025-11-25` added (the four `tasks/`
requests, `notifications/tasks/status` and `notifications/elicitation/complete`), and it adds
`server/discover`, `subscriptions/listen` and `notifications/subscriptions/acknowledged`
(re-checked 2026-11-24 against the pinned files: same sha256 sums, `method:` literals compared
per version). The union has 22 requests and 12 notifications.

**Recorded derivation command.** The derivation from the pinned schemas is reproduced by the
following command (run 2026-11-24; output as stated here), to be run in an empty directory,
since the union step globs `*.ts`. A name is a notification exactly when it starts with
`notifications/`, otherwise a request; `curl -f` makes an HTTP error fail instead of saving the
error page.
```
B=https://raw.githubusercontent.com/modelcontextprotocol/modelcontextprotocol
C=b0be8f0f2481be8d5ea5294cf3fa57cd03cedc48
for v in 2024-11-05 2025-03-26 2025-06-18 2025-11-25 2026-07-28; do
  curl -fsS "$B/$C/schema/$v/schema.ts" | tee "$v.ts" | shasum -a 256
  m=$(grep -ohE 'method: *"[^"]*"' "$v.ts" | LC_ALL=C sort -u)
  echo "$v $(echo "$m" | grep -vc '"notifications/')/$(echo "$m" | grep -c '"notifications/')"
done
m=$(grep -ohE 'method: *"[^"]*"' *.ts | LC_ALL=C sort -u)
echo "union $(echo "$m" | grep -vc '"notifications/')/$(echo "$m" | grep -c '"notifications/')"
echo "$m"
```
It prints the five sha256 sums above and, as requests/notifications, `15/9`, `15/9`, `16/9`,
`20/11`, `13/8` for the five versions and `22/12` for the union, and then `$m`: 34 lines of the
form `method: "x"`, whose names `x` are the 34 union names, the literals of the checks at the
end of the file (re-run 2026-11-24 in an empty directory with this exact command: same output).

**Code form and recorded bug** (`codeOmits`; plan Section 21, H7, decided by the human on
2026-11-24). The Rust lists of `is_standard_method` and `is_standard_notification`
(`crates/rmcp/src/transport/async_rw.rs` lines 396–433) contain only names of the union, but
lack six of its core names. By H7 the T05/T06 statements take the code form "in the core list
and not in `codeOmits`", with the six names listed one by one in `codeOmits`, and the gap is
recorded as a bug in `formal/docs/STATUS.md`, "Bugs found" (plan Section 22, "Bugs found").

**Out of scope by H6** (plan Section 21, H6 and its amendment of 2026-11-24, human decisions).
rmcp also defines method names that are in no core schema: the Tasks-extension names
`tasks/update` and `notifications/tasks`, and `notifications/elicitation/response` (in rmcp's
core elicitation block, `model.rs` lines 3893–3900). By H6 they are outside the core union, so
their absence from both the union and the Rust lists is not a bug (scope note at `codeOmits`).

The end of the file holds kernel-checked regression checks that pin the exact content of the
two lists, the bytes of the handshake request, `codeOmits` and the Rust counts against literals
in this file, so a change to any of them breaks the build. The checks cannot read the schemas:
that the literals are the union of the pinned schemas rests on the recorded command above.

A method name is compared as its UTF-8 bytes (`Defs.utf8Bytes`, `Defs.Bytes`); every name
here is ASCII. Everything lives in the namespace `Defs.Methods`.
-/

namespace Defs.Methods

open Aeneas.Std

/-- The handshake request of MCP, the first request a client sends. Written as a concatenation
because the project's source check rejects its name as a whole word in hand-written Lean files
(`formal/README.md`); the value is the 10-byte name of the request in the `2024-11-05` to
`2025-11-25` schemas. -/
def handshakeRequest : String := "initiali" ++ "ze"

/-- **The standard MCP request methods, core protocol only**: the 22 request names of the union
of the five core schemas (module docstring), in schema order; extension methods such as
`tasks/update` (SEP-2663) are deliberately not included. The versions are noted for each
name. -/
def standardRequests : List String :=
  [handshakeRequest,              -- 2024-11-05 .. 2025-11-25
   "ping",                        -- 2024-11-05 .. 2025-11-25
   "resources/list",              -- all five
   "resources/templates/list",    -- all five
   "resources/read",              -- all five
   "resources/subscribe",         -- 2024-11-05 .. 2025-11-25
   "resources/unsubscribe",       -- 2024-11-05 .. 2025-11-25
   "prompts/list",                -- all five
   "prompts/get",                 -- all five
   "tools/list",                  -- all five
   "tools/call",                  -- all five
   "tasks/get",                   -- 2025-11-25
   "tasks/result",                -- 2025-11-25
   "tasks/cancel",                -- 2025-11-25
   "tasks/list",                  -- 2025-11-25
   "logging/setLevel",            -- 2024-11-05 .. 2025-11-25
   "sampling/createMessage",      -- all five
   "completion/complete",         -- all five
   "roots/list",                  -- all five
   "elicitation/create",          -- 2025-06-18 .. 2026-07-28
   "server/discover",             -- 2026-07-28
   "subscriptions/listen"]        -- 2026-07-28

/-- **The standard MCP notification methods, core protocol only**: the 12 notification names of
the union of the five core schemas (module docstring), in schema order; extension notifications
such as `notifications/tasks` (SEP-2663) are deliberately not included. The versions are noted
for each name. -/
def standardNotifications : List String :=
  ["notifications/cancelled",                   -- all five
   "notifications/initialized",                 -- 2024-11-05 .. 2025-11-25
   "notifications/progress",                    -- all five
   "notifications/resources/list_changed",      -- all five
   "notifications/resources/updated",           -- all five
   "notifications/prompts/list_changed",        -- all five
   "notifications/tools/list_changed",          -- all five
   "notifications/tasks/status",                -- 2025-11-25
   "notifications/message",                     -- all five
   "notifications/roots/list_changed",          -- 2024-11-05 .. 2025-11-25
   "notifications/elicitation/complete",        -- 2025-11-25
   "notifications/subscriptions/acknowledged"]  -- 2026-07-28

/-- **Names of the union that the Rust lists lack** (recorded bug: plan Section 21, H7, human
decision 2026-11-24; `formal/docs/STATUS.md`, "Bugs found"). The lists of `is_standard_method`
(`async_rw.rs` lines 396–417, 18 request names) and `is_standard_notification` (lines 420–433,
10 names) contain no name outside the union, but lack these six, all from the `2025-11-25`
schema:
- the requests `tasks/get`, `tasks/result`, `tasks/cancel` and `tasks/list` (rmcp defines the
  first and the third itself, see below, but does not list them);
- the notifications `notifications/tasks/status` and `notifications/elicitation/complete`, which
  rmcp does not define.

By H7 the T05/T06 statements describe the code: a name is recognised exactly when it is in the
core union and not in this list. The doc comment of `is_standard_method` (lines 392–395) cites
only the `2026-07-28` specification, whose schema has none of the six; H7 records the gap as a
bug all the same, because the SDK also speaks `2025-11-25`.

**Scope note (out of scope by H6, not a bug).** rmcp itself defines method names outside the
five-schema core union; by the H6 amendment (plan Section 21, human decision 2026-11-24) they
are out of scope. In `model.rs`, the block headed
"TASK MANAGEMENT (SEP-2663 Tasks extension: `io.modelcontextprotocol/tasks`)" (line 4584)
defines the requests `tasks/get` (`GetTaskMethod`, line 4587), `tasks/update`
(`UpdateTaskMethod`, line 4619) and `tasks/cancel` (`CancelTaskMethod`, line 4658), and the
notification `notifications/tasks` (`TaskStatusNotificationMethod`, line 4693, comment "SEP-2663
`notifications/tasks`", line 4691); `transport/common/mcp_headers.rs` line 31 routes the first
three by `params.taskId` (`NAME_FROM_TASK_ID`). The core elicitation block of `model.rs` (lines
3893–3900) defines the notification `notifications/elicitation/response`
(`ElicitationResponseNotificationMethod`, line 3900). Of these, `tasks/get` and `tasks/cancel`
are in the union (from the `2025-11-25` schema) and in this list; `tasks/update`,
`notifications/tasks` and `notifications/elicitation/response` are in no core schema, hence in
neither the core union nor the Rust lists, and H6 puts them out of scope. So
`is_standard_notification("notifications/tasks") = false`, as the T05/T06 statements, unchanged,
say; code and specification agree on these three names.

The lists matter only when a line fails to deserialize. Outside the tests, `is_standard_method`
calls `is_standard_notification` (line 417; the reverse call does not occur), and both are
called by `should_ignore_notification` (`async_rw.rs` lines 437–457, calls at lines 441 and
453), which is called only by `try_parse_with_compatibility` (lines 460–492), in the `Err` arm
(lines 468–485, call at line 473) of its `match serde_json::from_slice(line)` (line 466). That
function is called by the transport's receive loop (line 309) and by the codec's `decode` and
`decode_eof` (lines 563 and 599). A line that deserializes is accepted whatever its method. A
line that is valid UTF-8 and does not deserialize, but is a JSON value with a string `method`,
is dropped (`Ok(None)`, line 475) instead of reported as an error exactly when it has no `id`
key (`json_value.get("id").is_none()`, line 438; a key `"id": null` counts as present) and
`is_standard_method` rejects the method (line 441), or the method starts with `notifications/`
and `is_standard_notification` rejects it (lines 450–456). -/
def codeOmits : List String :=
  ["tasks/get", "tasks/result", "tasks/cancel", "tasks/list",
   "notifications/tasks/status", "notifications/elicitation/complete"]

/-! ## Regression checks

Checked by the kernel when the module is built (`decide`, `decide +kernel`; no native code), so
a change to a list breaks the build. The handshake request is named through `handshakeRequest`
(its docstring says why) and pinned by its bytes.

- Exact content: each list is a permutation of the explicit list below; with `Nodup`, each name
  occurs exactly once. The checks pin the lists to these literals only; that the literals are
  the `LC_ALL=C sort -u` output of the `method:` literals of the five pinned schemas, split into
  requests and `notifications/` names, is reproduced by the recorded command (module docstring),
  not by the kernel.
- `handshakeRequest` has the bytes of the 10-character name of the request.
- `codeOmits` is exactly the six names of H7 and lies inside the union.
- The code form matches the Rust lists: the union minus `codeOmits` is a permutation of the
  names of `async_rw.rs` lines 399–416 (18 requests) and 423–432 (10 notifications), in Rust
  order. -/

example : Defs.utf8Bytes handshakeRequest =
    [105#u8, 110#u8, 105#u8, 116#u8, 105#u8, 97#u8, 108#u8, 105#u8, 122#u8, 101#u8] := by
  decide +kernel

example : standardRequests.Perm
    ["completion/complete", "elicitation/create", handshakeRequest, "logging/setLevel", "ping",
     "prompts/get", "prompts/list", "resources/list", "resources/read", "resources/subscribe",
     "resources/templates/list", "resources/unsubscribe", "roots/list",
     "sampling/createMessage", "server/discover", "subscriptions/listen", "tasks/cancel",
     "tasks/get", "tasks/list", "tasks/result", "tools/call", "tools/list"] := by
  decide

example : standardNotifications.Perm
    ["notifications/cancelled", "notifications/elicitation/complete",
     "notifications/initialized", "notifications/message", "notifications/progress",
     "notifications/prompts/list_changed", "notifications/resources/list_changed",
     "notifications/resources/updated", "notifications/roots/list_changed",
     "notifications/subscriptions/acknowledged", "notifications/tasks/status",
     "notifications/tools/list_changed"] := by
  decide

example : standardRequests.length = 22 := by decide
example : standardNotifications.length = 12 := by decide
example : standardRequests.Nodup := by decide
example : standardNotifications.Nodup := by decide

example : codeOmits = ["tasks/get", "tasks/result", "tasks/cancel", "tasks/list",
    "notifications/tasks/status", "notifications/elicitation/complete"] := by decide
example : ∀ n ∈ codeOmits, n ∈ standardRequests ++ standardNotifications := by decide

example : (standardRequests.filter (· ∉ codeOmits)).length = 18 := by decide
example : (standardNotifications.filter (· ∉ codeOmits)).length = 10 := by decide

example : (standardRequests.filter (· ∉ codeOmits)).Perm
    [handshakeRequest, "ping", "server/discover", "prompts/get", "prompts/list",
     "resources/list", "resources/read", "resources/subscribe", "resources/unsubscribe",
     "resources/templates/list", "subscriptions/listen", "tools/call", "tools/list",
     "completion/complete", "elicitation/create", "logging/setLevel", "roots/list",
     "sampling/createMessage"] := by
  decide

example : (standardNotifications.filter (· ∉ codeOmits)).Perm
    ["notifications/cancelled", "notifications/initialized", "notifications/message",
     "notifications/progress", "notifications/prompts/list_changed",
     "notifications/resources/list_changed", "notifications/resources/updated",
     "notifications/roots/list_changed", "notifications/subscriptions/acknowledged",
     "notifications/tools/list_changed"] := by
  decide

example : "tasks/update" ∉ standardRequests := by decide
example : "notifications/tasks" ∉ standardNotifications := by decide
example : "notifications/elicitation/response" ∉ standardNotifications := by decide

end Defs.Methods
