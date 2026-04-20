-- Nondeterministic oracle relation.

import HADL.Syntax
import HADL.Typing

namespace HADL

/-- The oracle: prompt × heal-context × expected-type ↦ returned value. -/
abbrev Oracle := String → ErrCtx → Ty → Expr → Prop

namespace Oracle

/-- Eventual-truthfulness predicate. T4-only. -/
def eventuallyTruthful
    (O : Oracle) (N : Nat) (s : String) (τ : Ty)
    (auth : Expr → Prop) : Prop :=
  ∃ (σ : List Expr), σ.length ≤ N ∧
    ∃ v, v ∈ σ ∧ v.isValueB = true ∧
      (∃ ec, O s ec τ v) ∧ RtType v τ ∧ auth v

end Oracle

end HADL
