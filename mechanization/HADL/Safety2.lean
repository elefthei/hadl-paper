-- Oracle-relative safety (T4) for the agent family, plus congruence
-- lifting. Phase B target: discharge the sorries.

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Oracle
import HADL.Config
import HADL.Reduction

namespace HADL

/-- Agent analogue of `T4_truthful_success`.

    Signature change vs. the stub: the `eventuallyTruthful` hypothesis as
    defined in `Oracle.lean` only witnesses `∃ ec', O s ec' τ v` at some
    *unspecified* `ec'`, which need not coincide with the `ec` in the
    configuration under consideration. To conclude a `Step` at our
    particular `ec`, we replace the too-weak `_htruth` premise with a
    direct oracle witness at `ec`: the oracle returns some well-typed
    value `v` at our `ec` for stmt `s`, type `.tString`. Policy
    authorization for `.agent` is kept as `hauth`. -/
theorem T4_truthful_success_agent
    (O : Oracle) (ec : ErrCtx) (P : Policy) (s : String) (π : Principal)
    (hauth : policyAllows P π .agent)
    (hO : ∃ v, v.isValueB = true ∧ RtType v .tString ∧ O s ec .tString v) :
    ∃ C', Step O ⟨ec, P, .agent s π⟩ C' := by
  obtain ⟨v, hv, hrt, ho⟩ := hO
  exact ⟨_, Step.oracleSuccess (a := OAction.agent s π) hauth ho hv hrt⟩

/-- Gen analogue, proved inline rather than depending on the (still
    open) `Safety.T4_truthful_success`. Mirrors the agent case: the
    `eventuallyTruthful` premise is too weak for this statement, so we
    take a direct oracle witness at the given `ec`. -/
theorem T4_truthful_success_gen
    (O : Oracle) (ec : ErrCtx) (P : Policy) (τ : Ty) (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, v.isValueB = true ∧ RtType v τ ∧ O s ec τ v) :
    ∃ C', Step O ⟨ec, P, .gen τ s π⟩ C' := by
  obtain ⟨v, hv, hrt, ho⟩ := hO
  exact ⟨_, Step.oracleSuccess (a := OAction.gen τ s π) hauth ho hv hrt⟩

/-- Progress for `gen`: from the root position, a well-formed config
    whose oracle has a well-typed, policy-allowed successful witness at
    `C.err` can take a step.

    Signature changes vs. the stub:
      * Added `hauth : policyAllows C.pol π .gen` — required so that
        `Step.oracleSuccess` applies (it is not implied by truthfulness).
      * Replaced `_htruth` (eventuallyTruthful) with a direct oracle
        witness at `C.err`; see `T4_truthful_success_agent` for why. -/
theorem T4_progress_gen
    (O : Oracle) (C : Config) (τ : Ty) (s : String) (π : Principal)
    (hC : C.expr = .gen τ s π)
    (_hwf : Config.WF C)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, v.isValueB = true ∧ RtType v τ ∧ O s C.err τ v) :
    ∃ C', Step O C C' := by
  rcases C with ⟨ec, P, e⟩
  cases hC
  exact T4_truthful_success_gen O ec P τ s π hauth hO

/-- Progress for `agent` (analogous to `T4_progress_gen`). Same
    signature adjustments as `T4_progress_gen`. -/
theorem T4_progress_agent
    (O : Oracle) (C : Config) (s : String) (π : Principal)
    (hC : C.expr = .agent s π)
    (_hwf : Config.WF C)
    (hauth : policyAllows C.pol π .agent)
    (hO : ∃ v, v.isValueB = true ∧ RtType v .tString ∧ O s C.err .tString v) :
    ∃ C', Step O C C' := by
  rcases C with ⟨ec, P, e⟩
  cases hC
  exact T4_truthful_success_agent O ec P s π hauth hO

end HADL
