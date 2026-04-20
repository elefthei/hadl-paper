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

/-- **T4a (Budget Progress).** If the retry budget is exhausted at a
    stuck `gen` or `agent` redex, no oracle success or heal rule applies.
    The configuration is genuinely stuck — this is the formal notion of
    "fail-fast" without a terminal `errTerm` constructor. -/
theorem T4_budget_progress
    (O : Oracle) (ec : ErrCtx) (P : Policy) (τ : Ty) (s : String) (π : Principal)
    (_hover : ErrCtx.retries ec > retryBudget) :
    ¬ ∃ C', Step O ⟨ec, P, .gen τ s π⟩ C' := by
  sorry

/-- **T4b (Truthful Success).** If the oracle is eventually truthful for a
    `gen` site and the policy allows the action, there exists a successful
    step. -/
theorem T4_truthful_success
    (O : Oracle) (ec : ErrCtx) (P : Policy) (τ : Ty) (s : String) (π : Principal)
    (_hauth : policyAllows P π .gen)
    (_htruth : Oracle.eventuallyTruthful O retryBudget s τ (fun _ => True)) :
    ∃ C', Step O ⟨ec, P, .gen τ s π⟩ C' := by
  sorry

end HADL
