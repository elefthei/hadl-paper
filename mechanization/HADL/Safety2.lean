-- Oracle-relative safety (T4) for the agent family, plus congruence
-- lifting (two-sort + mutable-state).

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Oracle
import HADL.Config
import HADL.Reduction

namespace HADL

/-- Agent analogue of `T4_truthful_success`. Carries the store through
    unchanged. -/
theorem T4_truthful_success_agent
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (s : String) (π : Principal)
    (hauth : policyAllows P π .agent)
    (hO : ∃ v, RtType v .tString ∧ O s ec .tString v) :
    ∃ C', Step O ⟨ec, P, σ, .agent s π⟩ C' := by
  obtain ⟨v, hrt, ho⟩ := hO
  exact ⟨_, Step.oracleSuccess (a := OAction.agent s π) hauth ho hrt⟩

/-- Gen analogue. -/
theorem T4_truthful_success_gen
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (τ : Ty) (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, RtType v τ ∧ O s ec τ v) :
    ∃ C', Step O ⟨ec, P, σ, .gen τ s π⟩ C' := by
  obtain ⟨v, hrt, ho⟩ := hO
  exact ⟨_, Step.oracleSuccess (a := OAction.gen τ s π) hauth ho hrt⟩

/-- Progress for `gen`. -/
theorem T4_progress_gen
    (O : Oracle) (C : Config) (τ : Ty) (s : String) (π : Principal)
    (hC : C.expr = .gen τ s π)
    (_hwf : Config.WF C)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, RtType v τ ∧ O s C.err τ v) :
    ∃ C', Step O C C' := by
  rcases C with ⟨ec, P, σ, e⟩
  cases hC
  exact T4_truthful_success_gen O ec P σ τ s π hauth hO

/-- Progress for `agent`. -/
theorem T4_progress_agent
    (O : Oracle) (C : Config) (s : String) (π : Principal)
    (hC : C.expr = .agent s π)
    (_hwf : Config.WF C)
    (hauth : policyAllows C.pol π .agent)
    (hO : ∃ v, RtType v .tString ∧ O s C.err .tString v) :
    ∃ C', Step O C C' := by
  rcases C with ⟨ec, P, σ, e⟩
  cases hC
  exact T4_truthful_success_agent O ec P σ s π hauth hO

end HADL
