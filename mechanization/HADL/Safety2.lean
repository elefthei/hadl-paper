-- Full-trace safety theorems: T4c gen-case and agent-case progress.
--
-- Under an eventually-truthful oracle, a WF config whose `Extract` finds
-- a `gen` or `agent` head can take a `Step`, regardless of where the
-- oracle head sits in the expression.  The two theorems below close the
-- E[·] gap flagged in `Safety.lean`'s header, directly over the unified
-- `Step` relation (which bakes in the Extract-based evaluation-context
-- routing — see `BigStep.lean`).
--
-- Trace-level termination and the terminal-error blame lemma are still
-- paper-only; see the README.

import HADL.Safety
import HADL.BigStep
import HADL.ExtractShape
import HADL.Hygiene

namespace HADL

/-! ### Agent-side truthful-success (pure-core helper) -/

/--
  Analogue of `T4_truthful_success` for the agent family: under an
  eventually-truthful oracle at a `.agent`-authorized policy, there
  exist `ec` and `v` at which `PureStep.agentSuccess` fires.

  `Oracle.EventuallyTruthful` is policy-indexed by `.gen`; we restate
  the same witness draw here over an agent-authorized policy.  The
  oracle witness predicate itself is action-agnostic.
-/
theorem T4_truthful_success_agent
    {O : Oracle} {ρ : Env} {P : Policy} {π : Principal}
    {τ : Ty} {s : String} {pr : Option String}
    (hET    : Oracle.EventuallyTruthful O retryBudget)
    (hgen   : policyAllows P π .gen)
    (hauthA : policyAllows P π .agent) :
    ∃ (ec : ErrCtx) (v : Value),
      ErrCtx.retries ec ≤ retryBudget ∧
      O s ec τ v ∧
      RtType ρ v τ ∧
      PureStep O ⟨ρ, ec, P, π, .agent τ s pr⟩
               ⟨ρ, ec ++ [Event.success], P, π, .valE v⟩ := by
  obtain ⟨ec, hlen, v, hO, hrt⟩ := hET s ρ τ P π hgen
  refine ⟨ec, v, hlen, hO, hrt, ?_⟩
  exact PureStep.agentSuccess (O := O)
    (ρ := ρ) (ec := ec) (P := P) (π := π)
    (τ := τ) (s := s) (pr := pr) (v := v)
    hauthA hO hrt

/-! ### T4c gen-case progress -/

/--
  **Gen-case trace progress.**  If `Extract` of `e'` returns a `gen τ s
  none` head with fresh binder `x` and continuation `suf`, then under an
  eventually-truthful oracle at an authorized policy there exists a
  successor config such that `Step` reaches it.

  No E[·] congruence rules are needed; `Step.run`'s Extract-based
  constructor does the routing.
-/
theorem T4_progress_gen
    {O : Oracle} {ρ : Env} {P : Policy} {π : Principal}
    {e' pre suf : Expr} {x : Name} {τ : Ty} {s : String}
    (hET   : Oracle.EventuallyTruthful O retryBudget)
    (hauth : policyAllows P π .gen)
    (hext  : Extract e' = some (pre, x, suf))
    (hpre  : pre = .gen τ s none)
    (hx_fresh : Env.fresh ρ x) :
    ∃ (ec : ErrCtx) (C' : Config),
      Step O ⟨ρ, ec, P, π, e'⟩ C' := by
  subst hpre
  obtain ⟨ec', v, _hlen, _hO, hrt, hstep⟩ :=
    T4_truthful_success (O := O) (ρ := ρ) (P := P) (π := π)
      (τ := τ) (s := s) hET hauth
  refine ⟨ec', _, Step.run (O := O) (ρ := ρ) (ec := ec') (P := P) (π := π)
            (e' := e') (x := x) (suf := suf)
            (pre := .gen τ s none)
            (env' := ρ)
            (err' := ec' ++ [Event.success]) (pol' := P) (princ' := π)
            (v := v) (τ := τ) (τ' := .tSchema)
            (hext := hext)
            (hpre := hstep) (hrt := hrt) (hfr := hx_fresh)
            (hrestage := StType.schemaWildcard)⟩

/-! ### T4c agent-case progress -/

/--
  **Agent-case trace progress.**  Symmetric to `T4_progress_gen` for the
  `.agent` oracle head.  Requires that the policy authorize both `.gen`
  (to invoke the truthful-oracle witness) and `.agent` (for the agent
  success rule); under the paper's eventually-truthful model these are
  provided together.
-/
theorem T4_progress_agent
    {O : Oracle} {ρ : Env} {P : Policy} {π : Principal}
    {e' pre suf : Expr} {x : Name} {τ : Ty} {s : String} {pr : Option String}
    (hET    : Oracle.EventuallyTruthful O retryBudget)
    (hgen   : policyAllows P π .gen)
    (hauthA : policyAllows P π .agent)
    (hext   : Extract e' = some (pre, x, suf))
    (hpre   : pre = .agent τ s pr)
    (hx_fresh : Env.fresh ρ x) :
    ∃ (ec : ErrCtx) (C' : Config),
      Step O ⟨ρ, ec, P, π, e'⟩ C' := by
  subst hpre
  obtain ⟨ec', v, _hlen, _hO, hrt, hstep⟩ :=
    T4_truthful_success_agent (O := O) (ρ := ρ) (P := P) (π := π)
      (τ := τ) (s := s) (pr := pr) hET hgen hauthA
  refine ⟨ec', _, Step.run (O := O) (ρ := ρ) (ec := ec') (P := P) (π := π)
            (e' := e') (x := x) (suf := suf)
            (pre := .agent τ s pr)
            (env' := ρ)
            (err' := ec' ++ [Event.success]) (pol' := P) (princ' := π)
            (v := v) (τ := τ) (τ' := .tSchema)
            (hext := hext)
            (hpre := hstep) (hrt := hrt) (hfr := hx_fresh)
            (hrestage := StType.schemaWildcard)⟩

end HADL
