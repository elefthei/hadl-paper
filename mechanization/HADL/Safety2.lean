-- Oracle-relative safety (T4) for the agent family, plus congruence
-- lifting. Phase B target: discharge the sorries.

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Oracle
import HADL.Config
import HADL.Reduction
import HADL.Safety

namespace HADL

/-- Agent analogue of `T4_truthful_success`. -/
theorem T4_truthful_success_agent
    (O : Oracle) (ec : ErrCtx) (P : Policy) (s : String) (π : Principal)
    (_hauth : policyAllows P π .agent)
    (_htruth : Oracle.eventuallyTruthful O retryBudget s .tString (fun _ => True)) :
    ∃ C', Step O ⟨ec, P, .agent s π⟩ C' := by
  sorry

/-- Progress for `gen`: from the root position, a well-formed config
    with an eventually-truthful oracle makes progress. -/
theorem T4_progress_gen
    (O : Oracle) (C : Config) (τ : Ty) (s : String) (π : Principal)
    (_hC : C.expr = .gen τ s π)
    (_hwf : Config.WF C)
    (_htruth : Oracle.eventuallyTruthful O retryBudget s τ (fun _ => True)) :
    ∃ C', Step O C C' := by
  sorry

/-- Progress for `agent` (analogous to `T4_progress_gen`). -/
theorem T4_progress_agent
    (O : Oracle) (C : Config) (s : String) (π : Principal)
    (_hC : C.expr = .agent s π)
    (_hwf : Config.WF C)
    (_htruth : Oracle.eventuallyTruthful O retryBudget s .tString (fun _ => True)) :
    ∃ C', Step O C C' := by
  sorry

end HADL
