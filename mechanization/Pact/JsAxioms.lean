-- Stub JavaScript interop layer: total `jsEval` + well-typedness lemma
-- (two-sort: returns a `Value`).
--
-- The paper (§\ref{sec:design-gradual}, §\ref{app:threat}) positions `js` as an
-- *oracular* escape hatch whose outputs must be runtime-checked. The Lean
-- mechanization here treats `js` as an unreachable stub: `jsEval := fun _ => none`
-- makes `jsEval_wellTyped` vacuously true (no `some v` ever arises), so no
-- soundness obligation is incurred. A faithful axiomatization would replace the
-- stub with `axiom js_oracular : ∀ je τ, ∃ v, jsEval je = some v ∧ RtType v τ`
-- and re-prove `jsEval_wellTyped` from that axiom; this is a future-work item
-- and would add one user axiom to the allowlist checked in `AxiomCheck.lean`.

import Pact.Syntax
import Pact.Typing

namespace Pact

/-- Trivial total evaluator for `js` expressions. -/
def jsEval : JsExpr → Option Value := fun _ => none

theorem jsEval_wellTyped
    (je : JsExpr) (v : Value) (τ : Ty) :
    jsEval je = some v →
    StType (Expr.js je) τ →
    RtType v τ := by
  intro h _
  simp [jsEval] at h

end Pact
