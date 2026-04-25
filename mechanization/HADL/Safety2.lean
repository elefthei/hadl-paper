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
  exact ⟨_, Step.agentSuccess hauth ho hrt⟩

/-- Gen analogue. With `gen` as a let-only redex, success fires on
    `let _ : τ = gen τ s π ; var 0`. Phase 1 covers Schema and
    non-healable τ; Policy / Arrow extend in Phases 2/3. We show the
    Schema case here. -/
theorem T4_truthful_success_gen
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, RtType v .tSchema ∧ O s ec .tSchema v) :
    ∃ C',
      Step O ⟨ec, P, σ, .letE .tSchema (.gen .tSchema s π) (.var 0)⟩ C' := by
  obtain ⟨v, hrt, ho⟩ := hO
  exact ⟨_, Step.letGenSuccessSchema hauth ho hrt StaticTypeOK.var0⟩

/-- Progress for `gen` at Schema: the let-redex
    `let _ : .tSchema = gen .tSchema s π ; var 0` has a successor when
    the policy allows and the oracle is locally truthful. -/
theorem T4_progress_gen
    (O : Oracle) (C : Config) (s : String) (π : Principal)
    (hC : C.expr = .letE .tSchema (.gen .tSchema s π) (.var 0))
    (_hwf : Config.WF C)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, RtType v .tSchema ∧ O s C.err .tSchema v) :
    ∃ C', Step O C C' := by
  rcases C with ⟨ec, P, σ, e⟩
  cases hC
  exact T4_truthful_success_gen O ec P σ s π hauth hO

/-- Arrow analogue of `T4_truthful_success_gen`. Phase 3. -/
theorem T4_truthful_success_gen_arrow
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store)
    (args : List Ty) (ret : Ty) (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, RtType v (.tArrow args ret) ∧ O s ec (.tArrow args ret) v) :
    ∃ C',
      Step O ⟨ec, P, σ,
              .letE (.tArrow args ret)
                    (.gen (.tArrow args ret) s π) (.var 0)⟩ C' := by
  obtain ⟨v, hrt, ho⟩ := hO
  exact ⟨_, Step.letGenSuccessArrow hauth ho hrt StaticTypeOK.var0⟩

/-- Arrow analogue of `T4_progress_gen`. Phase 3. -/
theorem T4_progress_gen_arrow
    (O : Oracle) (C : Config) (args : List Ty) (ret : Ty)
    (s : String) (π : Principal)
    (hC : C.expr = .letE (.tArrow args ret)
                        (.gen (.tArrow args ret) s π) (.var 0))
    (_hwf : Config.WF C)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, RtType v (.tArrow args ret) ∧ O s C.err (.tArrow args ret) v) :
    ∃ C', Step O C C' := by
  rcases C with ⟨ec, P, σ, e⟩
  cases hC
  exact T4_truthful_success_gen_arrow O ec P σ args ret s π hauth hO

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
