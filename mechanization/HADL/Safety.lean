-- T4 Oracle-Relative Safety — gen-local fragments (stated over `Step`).
--
-- We prove two gen-local claims of T4 over the pure-core relation
-- `Step`:
--   (BudgetProgress) once `retries(Σ) > retryBudget` at a gen, the
--                    `genBudgetExhausted` rule fires (deterministic
--                    fail-fast).
--   (Truthful)       under an eventually-truthful oracle at an
--                    authorized policy, `genSuccess` fires from the
--                    gen-stuck config, flushing Σ and binding the
--                    result.
--
-- Trace-level progress (gen + agent), lifted to the unified `Step`
-- relation defined in `BigStep.lean`, lives in `Safety2.lean`.
-- Pure-core termination is deferred to the paper (see README).

import HADL.Syntax
import HADL.Env
import HADL.Typing
import HADL.Policy
import HADL.Oracle
import HADL.Config
import HADL.Reduction
import HADL.Lemmas
import HADL.Soundness

namespace HADL

/-! ### Value and gen-stuck predicates -/

def Config.isValue (C : Config) : Prop := ∃ v, C.expr = .valE v

def Config.isGenStuck (C : Config) : Prop :=
  ∃ τ s, C.expr = .gen τ s none

/-! ### Eventually-truthful oracle -/

/--
  `O` is *eventually-truthful at budget `N`* when at every authorized
  gen site, there exists an err-context whose *retry metric* is ≤ N at
  which the oracle returns a value well-typed at the requested type.
  This matches Def. 1 of the paper (retries, not total length).
-/
def Oracle.EventuallyTruthful (O : Oracle) (N : Nat) : Prop :=
  ∀ (s : String) (ρ : Env) (τ : Ty) (P : Policy) (π : Principal),
    policyAllows P π .gen →
    ∃ (ec : ErrCtx), ErrCtx.retries ec ≤ N ∧
      ∃ v, O s ec τ v ∧ RtType ρ v τ

/-! ### T4 Budget Progress -/

/--
  **Budget progress.** If the retries-metric of a gen-stuck config has
  exceeded the retry budget, `genBudgetExhausted` fires — deterministic
  fail-fast named in T4.
-/
theorem T4_budget_progress
    {O : Oracle} {ρ : Env} {ε : ErrCtx} {P : Policy} {π : Principal}
    {τ : Ty} {s : String}
    (hover : ErrCtx.retries ε > retryBudget) :
    Step O ⟨ρ, ε, P, π, .gen τ s none⟩
         ⟨ρ, ε, P, π, .errTerm ε (.gen τ s none)⟩ := by
  exact Step.genBudgetExhausted (O := O)
    (ρ := ρ) (ec := ε) (P := P) (π := π)
    (τ := τ) (s := s) hover

/-! ### T4 Truthful Oracle ⇒ Gen-Success -/

/--
  **Truthful oracle yields Gen-Success.** Under an eventually-truthful
  oracle and an authorized policy, there exist `ec` and `v` at which
  `Gen-Success` fires from a gen-stuck config, appending a `.success`
  event to ε and inlining the materialized value.
-/
theorem T4_truthful_success
    {O : Oracle} {ρ : Env} {P : Policy} {π : Principal}
    {τ : Ty} {s : String}
    (hET   : Oracle.EventuallyTruthful O retryBudget)
    (hauth : policyAllows P π .gen) :
    ∃ (ec : ErrCtx) (v : Value),
      ErrCtx.retries ec ≤ retryBudget ∧
      O s ec τ v ∧
      RtType ρ v τ ∧
      Step O ⟨ρ, ec, P, π, .gen τ s none⟩
           ⟨ρ, ec ++ [Event.success], P, π, .valE v⟩ := by
  obtain ⟨ec, hlen, v, hO, hrt⟩ := hET s ρ τ P π hauth
  refine ⟨ec, v, hlen, hO, hrt, ?_⟩
  exact Step.genSuccess (O := O)
    (ρ := ρ) (ec := ec) (P := P) (π := π)
    (τ := τ) (s := s) (v := v)
    hauth hO hrt

end HADL
