-- Nondeterministic oracle relation (schema · err-ctx · type ↦ value).
-- Eventually-truthful predicate is defined here but is not used in the
-- T1–T3 proofs (only T4 needs it).

import HADL.Syntax
import HADL.Env
import HADL.Typing

namespace HADL

/-- The oracle. Any value in the relation is a possible response. -/
abbrev Oracle := String → ErrCtx → Ty → Value → Prop

namespace Oracle

/-- The oracle is "eventually truthful at budget N" for a gen site if,
    within N attempts, it can return a value that both runtime-typechecks
    and is policy-authorized. Placeholder definition; T4-only. -/
def eventuallyTruthful
    (O : Oracle) (N : Nat) (s : String) (ρ : Env) (τ : Ty)
    (auth : Value → Prop) : Prop :=
  ∃ (σ : List Value), σ.length ≤ N ∧
    ∃ v, v ∈ σ ∧
      (∃ ec, O s ec τ v) ∧ RtType ρ v τ ∧ auth v

end Oracle

end HADL
