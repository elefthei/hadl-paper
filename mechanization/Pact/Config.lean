-- Machine configuration + well-formedness predicate.
--
-- 4-tuple configuration ⟨Σ, Π, σ, e⟩ with a mutable-state store σ.
-- The current principal π lives inside `gen`/`agent`/`evalE` syntax.

import Pact.Syntax
import Pact.Typing
import Pact.Policy

namespace Pact

/-- Four-tuple configuration. -/
structure Config where
  err   : ErrCtx
  pol   : Policy
  store : Store
  expr  : Expr

/-- Retry budget. -/
def retryBudget : Nat := 3

/-- Configuration well-formedness: retry budget bounded AND store
    well-typed. -/
def Config.WF (C : Config) : Prop :=
  ErrCtx.retries C.err ≤ retryBudget ∧ C.store.WF

end Pact
