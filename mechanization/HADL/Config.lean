-- Machine configuration + well-formedness predicate.
--
-- The substitution-based core uses a 3-tuple configuration. The
-- current principal π lives inside `gen`/`agent`/`evalE` syntax.

import HADL.Syntax
import HADL.Policy

namespace HADL

/-- Three-tuple configuration ⟨Σ, Π, e⟩. -/
structure Config where
  err       : ErrCtx
  pol       : Policy
  expr      : Expr

/-- Retry budget. -/
def retryBudget : Nat := 3

/-- Configuration well-formedness: one clause — retry budget bounded. -/
def Config.WF (C : Config) : Prop :=
  ErrCtx.retries C.err ≤ retryBudget

end HADL
