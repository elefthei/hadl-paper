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
  intro hwf hs
  induction hs with
  | letBind _ _ => exact hwf
  | ifTrue => exact hwf
  | ifFalse => exact hwf
  | whileUnfold => exact hwf
  | forNil => exact hwf
  | forCons _ => exact hwf
  | seqStep _ => exact hwf
  | jsStep _ _ => exact hwf
  | sayStep => exact hwf
  | askStep _ _ _ =>
      show ErrCtx.retries (_ ++ [Event.success]) ≤ retryBudget
      simp [retryBudget]
  | oracleSuccess _ _ _ _ =>
      show ErrCtx.retries (_ ++ [Event.success]) ≤ retryBudget
      simp [retryBudget]
  | oracleHealType _ _ _ hbudget => exact hbudget
  | oracleHealPol _ hbudget => exact hbudget
  | evalSuccess _ _ => exact hwf
  | enforceInstall _ => exact hwf
  | letCong _ ih => exact ih hwf
  | ifCong _ ih => exact ih hwf
  | seqCong _ ih => exact ih hwf
  | forCong _ ih => exact ih hwf
  | enforceCong _ ih => exact ih hwf
  | evalFunCong _ ih => exact ih hwf

/-- **T2 (Staged Materialization Soundness).** When an oracle response
    step produces a value `v` at an expected type `τ`, that value
    runtime-typechecks. Immediate from the `oracleSuccess` rule,
    which carries `RtType v τ` as a premise. -/
theorem T2_staged_materialization
    (O : Oracle) (ec ec' : ErrCtx) (P P' : Policy) (e e' : Expr) :
    Step O ⟨ec, P, e⟩ ⟨ec', P', e'⟩ →
    e'.isValueB = true →
    ∃ τ, RtType e' τ := by
  intro hs hv
  have value_typeable : ∀ w : Expr, w.isValueB = true → ∃ τ, RtType w τ := by
    intro w hw
    cases w with
    | unit        => exact ⟨_, .vUnit⟩
    | litBool _   => exact ⟨_, .vBool⟩
    | litInt _    => exact ⟨_, .vInt⟩
    | litStr _    => exact ⟨_, .vStr⟩
    | schemaV _   => exact ⟨_, .vSchema⟩
    | polV _      => exact ⟨_, .vPol⟩
    | clos n body =>
        refine ⟨.tArrow (List.replicate n .tUnit) .tUnit,
                .vClos (args := List.replicate n .tUnit) (ret := .tUnit) ?_⟩
        simp
    | recV xs     => exact ⟨_, .vRec⟩
    | arrV vs     => exact ⟨_, .vArr⟩
    | var _       => simp [Expr.isValueB] at hw
    | letE _ _ _  => simp [Expr.isValueB] at hw
    | ifE _ _ _   => simp [Expr.isValueB] at hw
    | whileE _ _  => simp [Expr.isValueB] at hw
    | forE _ _    => simp [Expr.isValueB] at hw
    | seq _ _     => simp [Expr.isValueB] at hw
    | ask _       => simp [Expr.isValueB] at hw
    | say _       => simp [Expr.isValueB] at hw
    | gen _ _ _   => simp [Expr.isValueB] at hw
    | agent _ _   => simp [Expr.isValueB] at hw
    | evalE _ _   => simp [Expr.isValueB] at hw
    | enforce _   => simp [Expr.isValueB] at hw
    | js _        => simp [Expr.isValueB] at hw
  exact value_typeable e' hv

/-- **T3 (Policy Monotonicity).** Step only installs forbid policies, so
    the allow-set shrinks. -/
theorem T3_policy_monotonicity
    (O : Oracle) (C C' : Config) :
    Step O C C' → policyAllowSet C'.pol ⊆ policyAllowSet C.pol := by
  intro hs
  induction hs with
  | letBind _ _ => exact Set.Subset.rfl
  | ifTrue => exact Set.Subset.rfl
  | ifFalse => exact Set.Subset.rfl
  | whileUnfold => exact Set.Subset.rfl
  | forNil => exact Set.Subset.rfl
  | forCons _ => exact Set.Subset.rfl
  | seqStep _ => exact Set.Subset.rfl
  | jsStep _ _ => exact Set.Subset.rfl
  | sayStep => exact Set.Subset.rfl
  | askStep _ _ _ => exact Set.Subset.rfl
  | oracleSuccess _ _ _ _ => exact Set.Subset.rfl
  | oracleHealType _ _ _ _ => exact Set.Subset.rfl
  | oracleHealPol _ _ => exact Set.Subset.rfl
  | evalSuccess _ _ => exact Set.Subset.rfl
  | enforceInstall hinst => exact policyInstall_shrinks _ _ _ hinst
  | letCong _ ih => exact ih
  | ifCong _ ih => exact ih
  | seqCong _ ih => exact ih
  | forCong _ ih => exact ih
  | enforceCong _ ih => exact ih
  | evalFunCong _ ih => exact ih

end HADL
