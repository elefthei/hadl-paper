-- T4 Oracle-Relative Safety — gen-local fragments.
--
-- Honest mechanization scope: we prove two gen-local claims of T4:
--   (BudgetProgress) once |ε| > retryBudget at a gen, `genBudgetExhausted`
--                    fires (deterministic fail-fast).
--   (Truthful)       under an eventually-truthful oracle at an authorized
--                    policy, `Gen-Success` fires from the gen-stuck
--                    config, flushing ε and binding the result.
--
-- Full trace-level T4 ("every trace terminates in a value or blamed
-- errTerm") additionally requires (i) an E[·] congruence extension to
-- `Step` and (ii) a termination hypothesis on the pure-core fragment;
-- both are treated informally in the paper (§4 T4 and Appendix A) and
-- left to future mechanization.

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
  gen site, there exists an err-context of length ≤ N at which the
  oracle returns a value well-typed at the requested type.
-/
def Oracle.EventuallyTruthful (O : Oracle) (N : Nat) : Prop :=
  ∀ (s : String) (ρ : Env) (τ : Ty) (P : Policy) (π : Principal),
    policyAllows P π .gen →
    ∃ (ec : ErrCtx), ec.length ≤ N ∧
      ∃ v, O s ec τ v ∧ RtType ρ v τ

/--
  The opaque `freshLabel` always produces a name fresh in the current
  environment. Declared as an axiom; used only by T4.
-/
axiom freshLabel_is_fresh (ρ : Env) (e : Expr) :
    Env.fresh ρ (toString (freshLabel ρ e))

/-! ### T4 Budget Progress -/

/--
  **Budget progress.** If the err-context of a gen-stuck config has
  exceeded the retry budget, `genBudgetExhausted` fires — deterministic
  fail-fast named in T4.
-/
theorem T4_budget_progress
    {O : Oracle} {ρ : Env} {ε : ErrCtx} {P : Policy} {π : Principal}
    {τ : Ty} {s : String}
    (hover : ε.length > retryBudget) :
    let ℓ := freshLabel ρ (.gen τ s none)
    Step O ⟨ρ, ε, P, π, .gen τ s none⟩
         ⟨ρ, ε, P, π, .errTerm ε ℓ⟩ := by
  exact Step.genBudgetExhausted (O := O)
    (ρ := ρ) (ec := ε) (P := P) (π := π)
    (τ := τ) (s := s) (ℓ := freshLabel ρ (.gen τ s none)) hover

/-! ### T4 Truthful Oracle ⇒ Gen-Success -/

/--
  **Truthful oracle yields Gen-Success.** Under an eventually-truthful
  oracle and an authorized policy, there exist `ec` and `v` at which
  `Gen-Success` fires from a gen-stuck config, flushing ε to `[]` and
  binding the result value at a fresh label.
-/
theorem T4_truthful_success
    {O : Oracle} {ρ : Env} {P : Policy} {π : Principal}
    {τ : Ty} {s : String}
    (hET   : Oracle.EventuallyTruthful O retryBudget)
    (hauth : policyAllows P π .gen) :
    ∃ (ec : ErrCtx) (v : Value),
      ec.length ≤ retryBudget ∧
      O s ec τ v ∧
      RtType ρ v τ ∧
      let ℓ := freshLabel ρ (.gen τ s none)
      let ρ' := Env.extend ρ (toString ℓ) ⟨v, τ, some ℓ, .letBind⟩
      Step O ⟨ρ, ec, P, π, .gen τ s none⟩
           ⟨ρ', [], P, π, .valE v⟩ := by
  obtain ⟨ec, hlen, v, hO, hrt⟩ := hET s ρ τ P π hauth
  refine ⟨ec, v, hlen, hO, hrt, ?_⟩
  exact Step.genSuccess (O := O)
    (ρ := ρ) (ec := ec) (P := P) (π := π)
    (τ := τ) (s := s) (v := v)
    (ℓ := freshLabel ρ (.gen τ s none))
    hauth hO hrt StType.valueWildcard rfl
    (freshLabel_is_fresh ρ (.gen τ s none))

end HADL
