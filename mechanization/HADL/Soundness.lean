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
      show ErrCtx.retries (_ ++ [Event.success]) ≤ retryBudget
      simp [retryBudget]
  | oracleSuccess _ _ _ =>
      show ErrCtx.retries (_ ++ [Event.success]) ≤ retryBudget
      simp [retryBudget]
  | oracleHealType _ _ _ hbudget => exact hbudget
  | oracleHealPol _ hbudget => exact hbudget
  | evalSuccess _ => exact hwf
  | enforceInstall _ => exact hwf
  | letCong _ ih => exact ih hwf
  | ifCong _ ih => exact ih hwf
  | seqCong _ ih => exact ih hwf
  | forCong _ ih => exact ih hwf
  | enforceCong _ ih => exact ih hwf
  | evalFunCong _ ih => exact ih hwf

/-- Every value has *some* runtime type. Weak typing on records /
    arrays keeps this unconditional. -/
private theorem value_typeable : ∀ v : Value, ∃ τ, RtType v τ
  | .unitV      => ⟨_, .vUnit⟩
  | .boolV _    => ⟨_, .vBool⟩
  | .intV  _    => ⟨_, .vInt⟩
  | .strV  _    => ⟨_, .vStr⟩
  | .schemaV _  => ⟨_, .vSchema⟩
  | .polV _     => ⟨_, .vPol⟩
  | .clos n _body =>
      ⟨.tArrow (List.replicate n .tUnit) .tUnit,
       .vClos (args := List.replicate n .tUnit) (ret := .tUnit)
         (List.length_replicate)⟩
  | .recV _     => ⟨_, .vRec⟩
  | .arrV _     => ⟨_, .vArr⟩

/--
**T2 (Staged Materialization Soundness).** If a step reduces an
expression to a value, that value has a runtime type.

Statement shape change vs. the pre-refactor version: in the two-sort
presentation values are a separate inductive, so the post-state
appears as `.val v` with `v : Value` and the conclusion is
`∃ τ, RtType v τ`. Equivalent up to isomorphism with the old
`e'.isValueB = true → ∃ τ, RtType e' τ`.
-/
theorem T2_staged_materialization
    (O : Oracle) (ec ec' : ErrCtx) (P P' : Policy) (e e' : Expr) :
    Step O ⟨ec, P, e⟩ ⟨ec', P', e'⟩ →
    e'.isValueB = true →
    ∃ v, e' = .val v ∧ ∃ τ, RtType v τ := by
  intro _hs hv
  cases e' with
  | val v       => exact ⟨v, rfl, value_typeable v⟩
  | var _       => simp [Expr.isValueB] at hv
  | letE _ _ _  => simp [Expr.isValueB] at hv
  | ifE _ _ _   => simp [Expr.isValueB] at hv
  | whileE _ _  => simp [Expr.isValueB] at hv
  | forE _ _    => simp [Expr.isValueB] at hv
  | seq _ _     => simp [Expr.isValueB] at hv
  | ask _       => simp [Expr.isValueB] at hv
  | say _       => simp [Expr.isValueB] at hv
  | gen _ _ _   => simp [Expr.isValueB] at hv
  | agent _ _   => simp [Expr.isValueB] at hv
  | evalE _ _   => simp [Expr.isValueB] at hv
  | enforce _   => simp [Expr.isValueB] at hv
  | js _        => simp [Expr.isValueB] at hv

/-- **T3 (Policy Monotonicity).** Step only installs forbid policies, so
    the allow-set shrinks. -/
theorem T3_policy_monotonicity
    (O : Oracle) (C C' : Config) :
    Step O C C' → policyAllowSet C'.pol ⊆ policyAllowSet C.pol := by
  intro hs
  induction hs with
  | letBind _ => exact Set.Subset.rfl
  | ifTrue => exact Set.Subset.rfl
  | ifFalse => exact Set.Subset.rfl
  | whileUnfold => exact Set.Subset.rfl
  | forNil => exact Set.Subset.rfl
  | forCons => exact Set.Subset.rfl
  | seqStep => exact Set.Subset.rfl
  | jsStep _ => exact Set.Subset.rfl
  | sayStep => exact Set.Subset.rfl
  | askStep _ _ => exact Set.Subset.rfl
  | oracleSuccess _ _ _ => exact Set.Subset.rfl
  | oracleHealType _ _ _ _ => exact Set.Subset.rfl
  | oracleHealPol _ _ => exact Set.Subset.rfl
  | evalSuccess _ => exact Set.Subset.rfl
  | enforceInstall hinst => exact policyInstall_shrinks _ _ _ hinst
  | letCong _ ih => exact ih
  | ifCong _ ih => exact ih
  | seqCong _ ih => exact ih
  | forCong _ ih => exact ih
  | enforceCong _ ih => exact ih
  | evalFunCong _ ih => exact ih

end HADL
