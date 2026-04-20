-- Oracle-relative safety (T4) for the agent family, plus congruence
-- lifting (two-sort).

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Oracle
import HADL.Config
import HADL.Reduction

namespace HADL

/-- Agent analogue of `T4_truthful_success`.

    Statement change vs. the pre-refactor version: the direct oracle
    witness now carries a `Value` rather than an `Expr` plus
    `isValueB` hypothesis — the two-sort presentation makes the
    value-shape premise redundant. -/
theorem T4_truthful_success_agent
    (O : Oracle) (ec : ErrCtx) (P : Policy) (s : String) (π : Principal)
    (hauth : policyAllows P π .agent)
    (hO : ∃ v, RtType v .tString ∧ O s ec .tString v) :
    ∃ C', Step O ⟨ec, P, .agent s π⟩ C' := by
  obtain ⟨v, hrt, ho⟩ := hO
  exact ⟨_, Step.oracleSuccess (a := OAction.agent s π) hauth ho hrt⟩

/-- Gen analogue. Same signature simplification as the agent case. -/
theorem T4_truthful_success_gen
    (O : Oracle) (ec : ErrCtx) (P : Policy) (τ : Ty) (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, RtType v τ ∧ O s ec τ v) :
    ∃ C', Step O ⟨ec, P, .gen τ s π⟩ C' := by
  obtain ⟨v, hrt, ho⟩ := hO
  exact ⟨_, Step.oracleSuccess (a := OAction.gen τ s π) hauth ho hrt⟩

/-- Progress for `gen`: from the root position, a well-formed config
    whose oracle has a well-typed, policy-allowed successful witness at
    `C.err` can take a step. -/
theorem T4_progress_gen
    (O : Oracle) (C : Config) (τ : Ty) (s : String) (π : Principal)
    (hC : C.expr = .gen τ s π)
    (_hwf : Config.WF C)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, RtType v τ ∧ O s C.err τ v) :
    ∃ C', Step O C C' := by
  rcases C with ⟨ec, P, e⟩
  cases hC
  exact T4_truthful_success_gen O ec P τ s π hauth hO

/-- Progress for `agent` (analogous to `T4_progress_gen`). -/
theorem T4_progress_agent
    (O : Oracle) (C : Config) (s : String) (π : Principal)
    (hC : C.expr = .agent s π)
    (_hwf : Config.WF C)
    (hauth : policyAllows C.pol π .agent)
    (hO : ∃ v, RtType v .tString ∧ O s C.err .tString v) :
    ∃ C', Step O C C' := by
  rcases C with ⟨ec, P, e⟩
  cases hC
  exact T4_truthful_success_agent O ec P s π hauth hO

end HADL
