-- Soundness theorems for the substitution-based HADL model.
--
-- T1 WF-Preservation, T2 Staged Materialization, T3 Policy Monotonicity.
-- Phase B target: discharge the sorries.

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Config
import HADL.Reduction
import HADL.Lemmas

namespace HADL

/-- **T1 (WF-Preservation).** If `C` is well-formed and `C ⟶ C'`, then
    `C'` is well-formed. Over the new 3-tuple config, `WF C ≝
    ErrCtx.retries C.err ≤ retryBudget`. -/
theorem T1_WF_preservation
    (O : Oracle) (C C' : Config) :
    Config.WF C → Step O C C' → Config.WF C' := by
  sorry

/-- **T2 (Staged Materialization Soundness).** When an oracle response
    step produces a value `v` at an expected type `τ`, that value
    runtime-typechecks. Immediate from the `oracleSuccess` rule,
    which carries `RtType v τ` as a premise. -/
theorem T2_staged_materialization
    (O : Oracle) (ec ec' : ErrCtx) (P P' : Policy) (e e' : Expr) :
    Step O ⟨ec, P, e⟩ ⟨ec', P', e'⟩ →
    e'.isValueB = true →
    ∃ τ, RtType e' τ := by
  sorry

/-- **T3 (Policy Monotonicity).** Step only installs forbid policies, so
    the allow-set shrinks. -/
theorem T3_policy_monotonicity
    (O : Oracle) (C C' : Config) :
    Step O C C' → policyAllowSet C'.pol ⊆ policyAllowSet C.pol := by
  sorry

end HADL
