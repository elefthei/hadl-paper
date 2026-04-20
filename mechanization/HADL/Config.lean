-- Machine configuration + well-formedness predicate.

import HADL.Syntax
import HADL.Env
import HADL.Typing
import HADL.Policy

namespace HADL

/-- Five-tuple configuration ⟨ρ, Σ, Π, π, e⟩. -/
structure Config where
  env       : Env
  err       : ErrCtx
  pol       : Policy
  princ     : Principal
  expr      : Expr

/-- Retry budget. Global parameter of the paper's model. -/
def retryBudget : Nat := 3    -- placeholder; make configurable later

/-- Configuration well-formedness. Three clauses from §4.3 of the paper. -/
def Config.WF (C : Config) : Prop :=
  -- (1) every binding is runtime-typed
  (∀ x b, Env.lookup C.env x = some b → RtType C.env b.value b.ty)
  -- (2) the residual expression typechecks against Γ(ρ) at some type
  ∧ (∃ τ, StType (Env.proj C.env) C.expr τ)
  -- (3) heal context within retry budget (trailing error run bounded)
  ∧ ErrCtx.retries C.err ≤ retryBudget

end HADL
