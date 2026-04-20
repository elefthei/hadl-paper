-- Extract: syntactic defunctionalization of E[·] into (oracle-head, continuation).
-- See ../../plan-extract.md (session file) for the design rationale.

import HADL.Syntax

namespace HADL

/-- Reserved fresh-name prefix used by `Extract` for its generated continuation
    binders. Programs in HADL are assumed not to use identifiers with this
    prefix; hygiene is a precondition.  -/
def Extract.freshPrefix : String := "__ex_"

/-- Canonical fresh names chosen per oracle-head kind.  Collision between
    multiple gens is irrelevant because `Extract` always returns the *leftmost*
    oracle head; the corresponding `x` is only ever bound once in the
    continuation produced for that call. -/
def Extract.freshGen   : Name := Extract.freshPrefix ++ "gen"
def Extract.freshAgent : Name := Extract.freshPrefix ++ "ag"
def Extract.freshAsk   : Name := Extract.freshPrefix ++ "ask"

/--
  `Extract e = some (pre, x, suf)` means:
  * `pre` is the *leftmost oracle head* occurring in `e` (a `.gen` or `.agent`
    expression — `.evalE` is intentionally deferred, see the plan);
  * `x` is a binder that does not appear free in `pre`;
  * `suf` is a continuation such that, substituting the result of `pre` for
    `x` inside `suf`, yields the same observation as running the original `e`.

  `Extract e = none` means there is no oracle head in `e`.  In that case
  `GStep.pure` falls back to the existing pure-core small-step relation.

  Loops are handled by a pure syntactic rewrite:
      `while e_c { p }  =  if e_c then (p ; while e_c { p }) else ()`
  Rather than recurse into `while e_c { p }` (which would not decrease
  `sizeOf`), we recurse into `e_c` only; the loop body and the re-emitted
  while live in the *output*, not in a recursive call.
-/
def Extract : Expr → Option (Expr × Name × Expr)
  | .gen τ s π =>
      some (.gen τ s π, Extract.freshGen, .var Extract.freshGen)
  | .agent τ s π =>
      some (.agent τ s π, Extract.freshAgent, .var Extract.freshAgent)
  | .ask s =>
      some (.ask s, Extract.freshAsk, .var Extract.freshAsk)
  | .letE m y τ e₁ e₂ =>
      (Extract e₁).map (fun p => (p.1, p.2.1, .letE m y τ p.2.2 e₂))
  | .assign y e₁ =>
      (Extract e₁).map (fun p => (p.1, p.2.1, .assign y p.2.2))
  | .ifE ec e₁ e₂ =>
      (Extract ec).map (fun p => (p.1, p.2.1, .ifE p.2.2 e₁ e₂))
  | .whileE ec e =>
      -- Desugar `while e_c { p }` ↦ `if e_c then (p ; while e_c { p }) else ()`
      -- and extract the guard.  The recursive call is on `ec`, not on the
      -- produced `whileE`, so structural recursion holds.
      (Extract ec).map
        (fun p => (p.1, p.2.1,
          .ifE p.2.2 (.seq e (.whileE ec e)) .unit))
  | .forE y e₁ e₂ =>
      (Extract e₁).map (fun p => (p.1, p.2.1, .forE y p.2.2 e₂))
  | .seq e₁ e₂ =>
      (Extract e₁).map (fun p => (p.1, p.2.1, .seq p.2.2 e₂))
  -- Everything else: no oracle head visible at the root, no extraction.
  -- (`.evalE`, `.ask`, `.say`, `.js`, `.enforce`, values, literals, var,
  --  `.errTerm`.)
  | _ => none

/-! ### Shape lemmas: see `ExtractShape.lean` (next). -/

end HADL
