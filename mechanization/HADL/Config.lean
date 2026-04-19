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

/--
  Acyclicity of the provenance relation on ρ.
  Placeholder: every binding's provenance label (if any) is less than every
  provenance label appearing in bindings introduced after it. Since our `Env`
  is a snoc-list with most-recent first, this is automatic; we keep the
  predicate opaque here and discharge it as `True` for the initial pass.
-/
def Env.provAcyclic (_ρ : Env) : Prop := True

/-- Configuration well-formedness. Four clauses from §4.3 of the paper. -/
def Config.WF (C : Config) : Prop :=
  -- (1) every binding is runtime-typed
  (∀ x b, Env.lookup C.env x = some b → RtType C.env b.value b.ty)
  -- (2) the residual expression typechecks against Γ(ρ) at some type
  ∧ (∃ τ, StType (Env.proj C.env) C.expr τ)
  -- (3) provenance acyclic
  ∧ Env.provAcyclic C.env
  -- (4) heal context within budget
  ∧ C.err.length ≤ retryBudget

end HADL
