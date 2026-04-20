-- Stub JavaScript interop layer: total `jsEval` + well-typedness lemma
-- (two-sort: returns a `Value`).

import HADL.Syntax
import HADL.Typing

namespace HADL

/-- Trivial total evaluator for `js` expressions. -/
def jsEval : JsExpr → Option Value := fun _ => none

theorem jsEval_wellTyped
    (je : JsExpr) (v : Value) (τ : Ty) :
    jsEval je = some v →
    StType (Expr.js je) τ →
    RtType v τ := by
  intro h _
  simp [jsEval] at h

end HADL
