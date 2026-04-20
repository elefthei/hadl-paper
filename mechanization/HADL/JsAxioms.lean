-- Stub JavaScript interop layer.

import HADL.Syntax
import HADL.Typing

namespace HADL

/-- Trivial total evaluator for `js` expressions. -/
def jsEval : JsExpr → Option Expr := fun _ => none

theorem jsEval_wellTyped
    (je : JsExpr) (v : Expr) (τ : Ty) :
    jsEval je = some v →
    StType (Expr.js je) τ →
    RtType v τ := by
  intro h _
  simp [jsEval] at h

end HADL
