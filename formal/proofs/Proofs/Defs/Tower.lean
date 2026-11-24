/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas
import Defs.Bytes

/-!
# Definitions for the origin-port statements (T07, T08)

The default port that an origin's scheme implies, as the plan Section 16.2 specification of T07
`default_port` states it: `"http"` gives 80, `"https"` gives 443, every other scheme none, by
exact, case-sensitive byte equality. The two numbers are those of RFC 9110 §4.2.1 (the `http`
URI scheme, default port 80) and §4.2.2 (the `https` URI scheme, default port 443); an origin
serialization omits the port when it is the scheme's default (RFC 6454 §6.2).

The restriction to these two schemes and the case sensitivity are the choice of the code and of
the plan (Section 16.2, T07; Section 17, "T07/T08 (ports)": callers lowercase the scheme first,
and that is their obligation), not RFC rules: RFC 3986 §3.1 makes schemes case-insensitive, and
other schemes such as `ws` and `wss` also have default ports.

Rust source: `crates/rmcp/src/transport/streamable_http_server/tower.rs` at upstream `7caec76`,
unmodified (plan Section 13); line numbers below refer to it. Stated on `List U8` and the port
type `U16` (a port is a 16-bit number, `Option<u16>` in the Rust signatures, lines 1146 and
1164; the width is part of the claim). Everything lives in the namespace `Defs.Tower`.
-/

namespace Defs.Tower

open Aeneas.Std

/-- The scheme `"http"` as its 4 ASCII bytes `h`, `t`, `t`, `p` (`Defs.utf8Bytes`; the pattern
`"http"` of `default_port`, `tower.rs` line 1148). -/
def http : List U8 := Defs.utf8Bytes "http"

/-- The scheme `"https"` as its 5 ASCII bytes `h`, `t`, `t`, `p`, `s` (`Defs.utf8Bytes`; the
pattern `"https"` of `default_port`, `tower.rs` line 1149). -/
def https : List U8 := Defs.utf8Bytes "https"

/-- The default port of the scheme whose bytes are `scheme`: `some 80` for exactly `"http"`,
`some 443` for exactly `"https"`, `none` otherwise (plan Section 16.2, T07; `tower.rs` lines
1145–1152, `"http" => Some(80)` at line 1148 and `"https" => Some(443)` at line 1149). The
numbers are the default ports of RFC 9110 §4.2.1 (`http`, 80) and §4.2.2 (`https`, 443); the
code's doc comment cites RFC 6454 §4, which does not give them. Any other byte string,
including `"HTTP"`, `"ws"` and `"wss"`, has no default port here: the two-scheme restriction and
the case sensitivity follow the code and the plan (Sections 16.2 and 17), not RFC rules (RFC
3986 §3.1 makes schemes case-insensitive). -/
def defaultPort (scheme : List U8) : Option U16 :=
  if scheme = http then some 80#u16
  else if scheme = https then some 443#u16
  else none

end Defs.Tower
