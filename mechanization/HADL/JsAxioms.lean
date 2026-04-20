-- Stub JavaScript interop layer.
--
-- The `js` expression evaluates via a host JavaScript runtime we do not
-- mechanize. In the formal model we provide the trivial interpreter
-- (`fun _ _ => none`) which makes `jsEval_wellTyped` vacuous; consumers
-- who want a live JS fragment can replace these definitions with their
-- own interpreter and re-prove the well-typedness lemma. The paper's
-- (T4c) footnote already delegates JS termination/soundness to the host.

import HADL.Syntax
import HADL.Env
import HADL.Typing

namespace HADL

/-- Trivial total evaluator for the `js` expression. Always returns `none`;
    a richer interpreter can be supplied by overriding this definition. -/
def jsEval : JsExpr → Env → Option Value := fun _ _ => none

/-- Well-typedness of the trivial interpreter: vacuously true since
    `jsEval _ _ = none` for every input. -/
theorem jsEval_wellTyped
    (je : JsExpr) (ρ : Env) (v : Value) (τ : Ty) :
    jsEval je ρ = some v →
    StType (Env.proj ρ) (Expr.js je) τ →
    RtType ρ v τ := by
  intro h _
  simp [jsEval] at h

end HADL
