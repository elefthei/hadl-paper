-- Oracle signature and eventual-truthfulness predicate.
-- Nondeterministic oracle relation (two-sort: returns a `Value`).

import HADL.Syntax
import HADL.Typing

namespace HADL

/-- The oracle: prompt × heal-context × expected-type ↦ returned value. -/
abbrev Oracle := String → ErrCtx → Ty → Value → Prop

namespace Oracle

/-- Eventual-truthfulness predicate. T4-only. -/
def eventuallyTruthful
    (O : Oracle) (N : Nat) (s : String) (τ : Ty)
    (auth : Value → Prop) : Prop :=
  ∃ (σ : List Value), σ.length ≤ N ∧
    ∃ v, v ∈ σ ∧
      (∃ ec, O s ec τ v) ∧ RtType v τ ∧ auth v

end Oracle

end HADL
