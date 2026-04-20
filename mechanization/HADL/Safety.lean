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

/-- **T4a (Budget → No Heal).** Under the new substitution-based semantics
    there is no `genBudgetExhausted` constructor: a stuck `gen` redex with
    exhausted budget simply has no heal transition.  The `oracleSuccess`
    rule can still fire independently of the budget (it appends
    `Event.success`, resetting retries), so we cannot claim the redex is
    globally stuck.  The *weakened* claim is: any transition from a
    budget-exhausted `gen` redex must be an `oracleSuccess` step, i.e. the
    resulting error context is `ec ++ [Event.success]`.  This is the
    analogue of the old `T4_budget_progress` — "no heal rule fires when
    the budget is exhausted" — adapted to the unified `OAction` rules.

    Renamed from `T4_budget_progress` because the original claim
    (`¬ ∃ C', Step …`) is false on the new semantics (a truthful oracle can
    always drive `oracleSuccess`). -/
theorem T4_budget_no_heal
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (τ : Ty) (s : String) (π : Principal)
    (hover : ErrCtx.retries ec > retryBudget) :
    ∀ C', Step O ⟨ec, P, σ, .gen τ s π⟩ C' →
          ∃ v, C' = ⟨ec ++ [Event.success], P, σ, v⟩ := by
  intro C' h
  generalize hE : (Expr.gen τ s π : Expr) = eG at h
  cases h
  case letBind => cases hE
  case ifTrue => cases hE
  case ifFalse => cases hE
  case whileUnfold => cases hE
  case forNil => cases hE
  case forCons => cases hE
  case seqStep => cases hE
  case jsStep => cases hE
  case sayStep => cases hE
  case askStep => cases hE
  case evalSuccess => cases hE
  case enforceInstall => cases hE
  case letCong => cases hE
  case ifCong => cases hE
  case seqCong => cases hE
  case forCong => cases hE
  case enforceCong => cases hE
  case evalFunCong => cases hE
  case varDeclEval => cases hE
  case varDeclBind => cases hE
  case assignEval => cases hE
  case assignWrite => cases hE
  case varReadStep => cases hE
  case oracleSuccess a _ _ _ =>
      cases a
      · exact ⟨_, rfl⟩
      · cases hE
  case oracleHealType a _ _ _ hbudget =>
      cases a
      · rename_i hb; rw [ErrCtx.retries_append_error] at hb; omega
      · cases hE
  case oracleHealPol a _ hbudget =>
      cases a
      · rw [ErrCtx.retries_append_error] at hbudget; omega
      · cases hE

/-- **T4b (Truthful Success).** If the oracle is eventually truthful for a
    `gen` site and the policy allows the action, there exists an error
    context and store from which a successful `oracleSuccess` step fires. -/
theorem T4_truthful_success
    (O : Oracle) (P : Policy) (τ : Ty) (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (htruth : Oracle.eventuallyTruthful O retryBudget s τ (fun _ => True)) :
    ∃ ec σ C', Step O ⟨ec, P, σ, .gen τ s π⟩ C' := by
  obtain ⟨_σ, _hlen, v, _hv_mem, ⟨ec, hO⟩, hrt, _⟩ := htruth
  refine ⟨ec, Store.empty, ⟨ec ++ [Event.success], P, Store.empty, .val v⟩, ?_⟩
  exact Step.oracleSuccess (a := OAction.gen τ s π) hauth hO hrt

end HADL
