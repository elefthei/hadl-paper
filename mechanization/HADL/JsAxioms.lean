-- Axiomatic opaque JavaScript interop layer.
--
-- The `js` expression evaluates via a host JavaScript runtime we do not
-- mechanize. We axiomatize it with a well-typedness postcondition that is
-- used in the `Js` case of T1.

import HADL.Syntax
import HADL.Env
import HADL.Typing

namespace HADL

/-- Opaque evaluation of a `js` expression against an environment. -/
axiom jsEval : JsExpr → Env → Option Value

/-- If the source `js` expression typechecks against `τ` in the static
    projection of ρ, then any value it produces runtime-typechecks at τ. -/
axiom jsEval_wellTyped
    (je : JsExpr) (ρ : Env) (v : Value) (τ : Ty) :
    jsEval je ρ = some v →
    StType (Env.proj ρ) (Expr.js je) τ →
    RtType ρ v τ

end HADL
