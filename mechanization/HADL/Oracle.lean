-- Oracle signature and eventual-truthfulness predicate.
-- Nondeterministic oracle relation (two-sort: returns a `Value`).

import HADL.Syntax
import HADL.Typing

namespace HADL

/-- The oracle: prompt × heal-context × expected-type ↦ returned value. -/
abbrev Oracle := String → ErrCtx → Ty → Value → Prop

namespace Oracle

/-- Eventual-truthfulness predicate. T4-only.

    **Honest-retreat (review remediation).** Reformulated from the
    earlier list-witness shape (`∃ σ : List Value, σ.length ≤ N ∧ ∃ v ∈ σ, …`)
    to a direct reachability form: there exists *some* err-context with
    no more than `N` retries at which the oracle returns a well-typed,
    authorized value. The list witness in the previous form was an
    abstract bound on retry count whose only constraint was `length ≤ N`,
    which is satisfied vacuously by `σ = []` (modulo the ∃ v ∈ σ which
    rules that out, but does not pin the witness to any particular ec).
    The new form ties the retry budget to the actual `ErrCtx.retries ec`
    of a witnessing context, ruling out adversarial oracles that are
    truthful only at unreachable contexts. -/
def eventuallyTruthful
    (O : Oracle) (N : Nat) (s : String) (τ : Ty)
    (auth : Value → Prop) : Prop :=
  ∃ ec, ErrCtx.retries ec ≤ N ∧
    ∃ v, RtType v τ ∧ O s ec τ v ∧ auth v

end Oracle

end HADL
