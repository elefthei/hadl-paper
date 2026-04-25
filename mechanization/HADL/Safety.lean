-- Oracle-relative safety (T4): progress for gen/agent when the oracle
-- is eventually truthful and the policy allows the action.
-- Phase B target: discharge the sorries.

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Oracle
import HADL.Config
import HADL.Reduction

namespace HADL

/-- **T4a (Budget → No Heal).** With `gen` no longer a standalone redex,
    the standalone `gen τ s π` has *no* transitions at all. (`gen` only
    reduces inside a let-redex.) So the conclusion holds vacuously. -/
theorem T4_budget_no_heal
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (τ : Ty) (s : String) (π : Principal)
    (_hover : ErrCtx.retries ec > retryBudget) :
    ∀ C', Step O ⟨ec, P, σ, .gen τ s π⟩ C' →
          ∃ v, C' = ⟨[], P, σ, v⟩ := by
  intro C' h
  -- `.gen τ s π` is no longer a standalone redex; no rule fires.
  cases h

/-- **T4b (Truthful Success).** If the oracle is eventually truthful for a
    `gen` site, the policy allows the action, AND τ is Schema (Phase 1
    coverage; Policy & Arrow extend in Phases 2 & 3), there exists an
    error context and store from which a successful let-redex step
    fires from `let _ : .tSchema = gen .tSchema s π ; var 0`.
    The continuation `.var 0` types trivially at `.tSchema` via
    `StaticTypeOK.var0`. -/
theorem T4_truthful_success
    (O : Oracle) (P : Policy) (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (htruth : Oracle.eventuallyTruthful O retryBudget s .tSchema (fun _ => True)) :
    ∃ ec σ C',
      Step O ⟨ec, P, σ, .letE .tSchema (.gen .tSchema s π) (.var 0)⟩ C' := by
  obtain ⟨_σ, _hlen, v, _hv_mem, ⟨ec, hO⟩, hrt, _⟩ := htruth
  exact ⟨ec, Store.empty, _,
         Step.letGenSuccessSchema hauth hO hrt StaticTypeOK.var0⟩

/-- **T4b-Arrow (Truthful Success at arrow type).** Phase 3 analogue of
    `T4_truthful_success`: same existential shape, type generalized to
    `tArrow args ret`. Continuation `.var 0` types via the universally-
    quantified `StaticTypeOK.var0`. -/
theorem T4_truthful_success_arrow
    (O : Oracle) (P : Policy) (args : List Ty) (ret : Ty)
    (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (htruth : Oracle.eventuallyTruthful O retryBudget s
                (.tArrow args ret) (fun _ => True)) :
    ∃ ec σ C',
      Step O ⟨ec, P, σ,
              .letE (.tArrow args ret)
                    (.gen (.tArrow args ret) s π) (.var 0)⟩ C' := by
  obtain ⟨_σ, _hlen, v, _hv_mem, ⟨ec, hO⟩, hrt, _⟩ := htruth
  exact ⟨ec, Store.empty, _,
         Step.letGenSuccessArrow hauth hO hrt StaticTypeOK.var0⟩

end HADL
