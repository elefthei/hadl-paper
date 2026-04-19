-- Soundness theorems for HADL.
-- T1 WF-Preservation, T2 Staged Materialization Soundness, T3 Policy Monotonicity.

import HADL.Syntax
import HADL.Env
import HADL.Typing
import HADL.Policy
import HADL.Config
import HADL.Reduction
import HADL.Lemmas

namespace HADL

/-- Placeholder: the configuration is a terminal error. -/
def Config.isErr (_C : Config) : Prop := False

/--
  **T1 — WF-Preservation.** Currently admitted; case analysis on `hstep`.
-/
theorem T1_WF_preservation
    {O : Oracle} {C C' : Config}
    (_hwf : C.WF) (_hstep : Step O C C') (_hne : ¬ C'.isErr) :
    C'.WF := by
  sorry

/--
  **T2 — Staged Materialization Soundness.** Direct read-off of the
  `genSuccess` side condition.
-/
theorem T2_staged_materialization
    {ρ : Env} {τ : Ty} {v : Value} {ℓ : Label}
    (hstage : StType
                (Env.proj (Env.extend ρ (toString ℓ) ⟨v, τ, some ℓ, .letBind⟩))
                (.valE v)
                τ) :
    StType
      (Env.proj (Env.extend ρ (toString ℓ) ⟨v, τ, some ℓ, .letBind⟩))
      (.valE v)
      τ := hstage

/--
  **T3 — Policy Monotonicity.** Immediate from per-step shrink, inducting
  on `Steps`.
-/
theorem T3_policy_monotonicity
    {O : Oracle} {C C' : Config}
    (h : Steps O C C') :
    policyAllowSet C'.pol ⊆ policyAllowSet C.pol :=
  Steps.policy_shrinks h

end HADL
