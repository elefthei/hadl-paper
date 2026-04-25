-- Soundness theorems for the substitution-based HADL model (two-sort).
--
-- T1 WF-Preservation, T2 Staged Materialization, T3 Policy Monotonicity.

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Config
import HADL.Reduction
import HADL.Lemmas

namespace HADL

/-- **T1 (WF-Preservation).** If `C` is well-formed and `C ⟶ C'`, then
    `C'` is well-formed. -/
theorem T1_WF_preservation
    (O : Oracle) (C C' : Config) :
    Config.WF C → Step O C C' → Config.WF C' := by
  intro hwf hs
  induction hs with
  | letBind _ => exact hwf
  | ifTrue => exact hwf
  | ifFalse => exact hwf
  | whileUnfold => exact hwf
  | forNil => exact hwf
  | forCons => exact hwf
  | seqStep => exact hwf
  | jsStep _ => exact hwf
  | sayStep => exact hwf
  | askStep _ _ =>
      refine ⟨?_, hwf.2⟩
      show ErrCtx.retries [] ≤ retryBudget
      simp [retryBudget]
  | agentSuccess _ _ _ =>
      refine ⟨?_, hwf.2⟩
      show ErrCtx.retries [] ≤ retryBudget
      simp [retryBudget]
  | agentHealPol _ hbudget => exact ⟨hbudget, hwf.2⟩
  | letCongNonheal _ _ ih => exact ih hwf
  | letGenSuccessNonheal _ _ _ _ =>
      refine ⟨?_, hwf.2⟩
      show ErrCtx.retries [] ≤ retryBudget
      simp [retryBudget]
  | letGenTypeError _ _ _ _ => exact hwf
  | letGenBudgetError _ => exact hwf
  | letGenHealPol _ hbudget => exact ⟨hbudget, hwf.2⟩
  | letGenSuccessSchema _ _ _ _ =>
      refine ⟨?_, hwf.2⟩
      show ErrCtx.retries [] ≤ retryBudget
      simp [retryBudget]
  | letGenHealSchema _ _ _ _ hbudget => exact ⟨hbudget, hwf.2⟩
  | letGenSuccessArrow _ _ _ _ =>
      refine ⟨?_, hwf.2⟩
      show ErrCtx.retries [] ≤ retryBudget
      simp [retryBudget]
  | letGenHealArrow _ _ _ _ hbudget => exact ⟨hbudget, hwf.2⟩
  | evalSuccess _ => exact hwf
  | enforceInstall _ => exact hwf
  | ifCong _ ih => exact ih hwf
  | seqCong _ ih => exact ih hwf
  | forCong _ ih => exact ih hwf
  | enforceCong _ ih => exact ih hwf
  | evalFunCong _ ih => exact ih hwf
  | varDeclEval _ ih => exact ih hwf
  | varDeclBind hrt => exact ⟨hwf.1, Store.set_WF hwf.2 hrt⟩
  | assignEval _ ih => exact ih hwf
  | assignWrite _ hrt => exact ⟨hwf.1, Store.set_WF hwf.2 hrt⟩
  | varReadStep _ => exact hwf

/-- Every value *other than `errV`* has some runtime type. The
    `errV` sink is intentionally untypeable: it represents a terminal
    failure state produced by the uniform let-redex error rules
    (`letGenTypeError`, `letGenBudgetError`). T2 is therefore weakened
    to `v ≠ errV → ∃ τ, RtType v τ`. -/
private theorem value_typeable : ∀ v : Value, v ≠ .errV → ∃ τ, RtType v τ
  | .unitV,  _   => ⟨_, .vUnit⟩
  | .boolV _, _  => ⟨_, .vBool⟩
  | .numV  _, _  => ⟨_, .vNum⟩
  | .strV  _, _  => ⟨_, .vStr⟩
  | .schemaV _, _ => ⟨_, .vSchema⟩
  | .polV _, _   => ⟨_, .vPol⟩
  | .clos n _body, _ =>
      ⟨.tArrow (List.replicate n .tUnit) .tUnit,
       .vClos (args := List.replicate n .tUnit) (ret := .tUnit)
         (List.length_replicate)⟩
  | .recV _, _   => ⟨_, .vRec⟩
  | .arrV _, _   => ⟨_, .vArr⟩
  | .errV, h     => (h rfl).elim

/--
**T2 (Staged Materialization Soundness, weakened).** If a step reduces
an expression to a value that is not the failure sink `errV`, that
value has a runtime type.

Statement shape change vs. the pre-refactor version: in the two-sort
presentation values are a separate inductive, so the post-state
appears as `.val v` with `v : Value`. Additionally, `Value.errV` is
the new failure sink and has no runtime type by design — the
materialization conclusion is therefore conditional on `v ≠ errV`.
-/
theorem T2_staged_materialization
    (O : Oracle) (ec ec' : ErrCtx) (P P' : Policy) (σ σ' : Store) (e e' : Expr) :
    Step O ⟨ec, P, σ, e⟩ ⟨ec', P', σ', e'⟩ →
    e'.isValueB = true →
    ∃ v, e' = .val v ∧ (v ≠ .errV → ∃ τ, RtType v τ) := by
  intro _hs hv
  cases e' with
  | val v => exact ⟨v, rfl, value_typeable v⟩
  | _ => simp [Expr.isValueB] at hv

/-- **T3 (Policy Monotonicity).** Step only installs forbid policies, so
    the allow-set shrinks. -/
theorem T3_policy_monotonicity
    (O : Oracle) (C C' : Config) :
    Step O C C' → policyAllowSet C'.pol ⊆ policyAllowSet C.pol := by
  intro hs
  induction hs with
  | enforceInstall hinst => exact policyInstall_shrinks _ _ _ hinst
  | letCongNonheal _ _ ih => exact ih
  | ifCong _ ih => exact ih
  | seqCong _ ih => exact ih
  | forCong _ ih => exact ih
  | enforceCong _ ih => exact ih
  | evalFunCong _ ih => exact ih
  | varDeclEval _ ih => exact ih
  | assignEval _ ih => exact ih
  | _ => exact Set.Subset.rfl

end HADL
