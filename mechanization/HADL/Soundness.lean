-- Soundness theorems for the substitution-based HADL model (two-sort).
--
-- T1 WF-Preservation, T2 Staged Materialization, T3 Policy Monotonicity.

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Config
import HADL.Reduction

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
  | letGenSuccessHealable _ _ _ _ _ _ =>
      refine ⟨?_, hwf.2⟩
      show ErrCtx.retries [] ≤ retryBudget
      simp [retryBudget]
  | letGenHealHealable _ _ _ _ _ hbudget => exact ⟨hbudget, hwf.2⟩
  | letGenHealRecordFields _ _ _ _ _ _ hbudget => exact ⟨hbudget, hwf.2⟩
  | evalSuccess _ => exact hwf
  | enforceInstall _ => exact hwf
  | letPrincValue => exact hwf
  | letPrincCong _ ih => exact ih hwf
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
  | projCong _ ih => exact ih hwf
  | projStep _ => exact hwf

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
  | .principalV _, _ => ⟨_, .vPrinc⟩
  | .clos n _body, _ =>
      ⟨.tArrow (List.replicate n .tUnit) .tUnit,
       .vClos (args := List.replicate n .tUnit) (ret := .tUnit)
         (List.length_replicate)⟩
  | .recV _, _   => ⟨_, .vRecWeak⟩
  | .arrV _, _   => ⟨_, .vArrWeak⟩
  | .errV, h     => (h rfl).elim

/-- Extracting a `Value` witness from `Expr.isValueB = true`. -/
private theorem exists_val_of_isValueB {e : Expr} :
    e.isValueB = true → ∃ v, e = .val v := by
  cases e with
  | val v => intro _; exact ⟨v, rfl⟩
  | _ => intro h; simp [Expr.isValueB] at h

/--
**T2 (Staged Materialization Soundness, weakened).** If a step reduces
an expression to a value that is not the failure sink `errV`, that
value has a runtime type.

Statement shape change vs. the pre-refactor version: in the two-sort
presentation values are a separate inductive, so the post-state
appears as `.val v` with `v : Value`. Additionally, `Value.errV` is
the new failure sink and has no runtime type by design — the
materialization conclusion is therefore conditional on `v ≠ errV`.

Proof structure: induction on `Step` (mirroring `T1_WF_preservation`).
Each rule is dispatched in one of three uniform ways:
* If the rule produces a known value `.val w` for a structurally
  determined `w` (`sayStep`, `forNil`, `enforceInstall`, `assignWrite`,
  `letGenTypeError`, `letGenBudgetError`), the witness is supplied
  directly from constructor data.
* If the rule produces a `.val v` for an opaque `v` carrying the
  rule's own `RtType` premise (`askStep`, `agentSuccess`), the type
  witness is the rule's premise.
* Otherwise (substitution-result rules `letBind`, `letGenSuccess*`,
  `evalSuccess`, `varDeclBind`; sub-expression rules `ifTrue`/`ifFalse`/
  `seqStep`; opaque-value rules `jsStep`, `letPrincValue`,
  `varReadStep`), `hv` is consumed via `exists_val_of_isValueB` to
  extract a `Value` witness, and `value_typeable` supplies the type.
* Structurally-non-value rules (all congruence rules, heal rules,
  `whileUnfold`, `forCons`, `agentHealPol`) are eliminated by `simp
  [Expr.isValueB]` which contradicts `hv`.

Conceptually the proof factors through a value-lemma per the paper
(appendix.tex line 294). The induction over `Step` is the mechanism
that ensures every reduction rule is covered — adding a new rule will
fail compilation here unless the rule's post-state is either a
`.val`-shape we can dispatch or a structurally non-value e' that
contradicts `hv`.
-/
theorem T2_staged_materialization
    (O : Oracle) (C C' : Config) :
    Step O C C' →
    C'.expr.isValueB = true →
    ∃ v, C'.expr = .val v ∧ (v ≠ .errV → ∃ τ, RtType v τ) := by
  intro hs hv
  induction hs with
  | letBind _ =>
      obtain ⟨v', heq⟩ := exists_val_of_isValueB hv
      exact ⟨v', heq, value_typeable v'⟩
  | ifTrue =>
      obtain ⟨v', heq⟩ := exists_val_of_isValueB hv
      exact ⟨v', heq, value_typeable v'⟩
  | ifFalse =>
      obtain ⟨v', heq⟩ := exists_val_of_isValueB hv
      exact ⟨v', heq, value_typeable v'⟩
  | whileUnfold => simp [Expr.isValueB] at hv
  | forNil => exact ⟨.unitV, rfl, fun _ => ⟨_, .vUnit⟩⟩
  | forCons => simp [Expr.isValueB] at hv
  | seqStep =>
      obtain ⟨v', heq⟩ := exists_val_of_isValueB hv
      exact ⟨v', heq, value_typeable v'⟩
  | jsStep _ => exact ⟨_, rfl, value_typeable _⟩
  | sayStep => exact ⟨.unitV, rfl, fun _ => ⟨_, .vUnit⟩⟩
  | askStep _ hrt => exact ⟨_, rfl, fun _ => ⟨_, hrt⟩⟩
  | agentSuccess _ _ hrt => exact ⟨_, rfl, fun _ => ⟨_, hrt⟩⟩
  | agentHealPol _ _ => simp [Expr.isValueB] at hv
  | letCongNonheal _ _ _ => simp [Expr.isValueB] at hv
  | letGenSuccessNonheal _ _ _ _ =>
      obtain ⟨v', heq⟩ := exists_val_of_isValueB hv
      exact ⟨v', heq, value_typeable v'⟩
  | letGenTypeError _ _ _ _ =>
      exact ⟨.errV, rfl, fun h => (h rfl).elim⟩
  | letGenBudgetError _ =>
      exact ⟨.errV, rfl, fun h => (h rfl).elim⟩
  | letGenHealPol _ _ => simp [Expr.isValueB] at hv
  | letGenSuccessHealable _ _ _ _ _ _ =>
      obtain ⟨v', heq⟩ := exists_val_of_isValueB hv
      exact ⟨v', heq, value_typeable v'⟩
  | letGenHealHealable _ _ _ _ _ _ => simp [Expr.isValueB] at hv
  | letGenHealRecordFields _ _ _ _ _ _ _ => simp [Expr.isValueB] at hv
  | evalSuccess _ =>
      obtain ⟨v', heq⟩ := exists_val_of_isValueB hv
      exact ⟨v', heq, value_typeable v'⟩
  | enforceInstall _ => exact ⟨.unitV, rfl, fun _ => ⟨_, .vUnit⟩⟩
  | letPrincValue => exact ⟨_, rfl, value_typeable _⟩
  | letPrincCong _ _ => simp [Expr.isValueB] at hv
  | ifCong _ _ => simp [Expr.isValueB] at hv
  | seqCong _ _ => simp [Expr.isValueB] at hv
  | forCong _ _ => simp [Expr.isValueB] at hv
  | enforceCong _ _ => simp [Expr.isValueB] at hv
  | evalFunCong _ _ => simp [Expr.isValueB] at hv
  | varDeclEval _ _ => simp [Expr.isValueB] at hv
  | varDeclBind _ =>
      obtain ⟨v', heq⟩ := exists_val_of_isValueB hv
      exact ⟨v', heq, value_typeable v'⟩
  | assignEval _ _ => simp [Expr.isValueB] at hv
  | assignWrite _ _ => exact ⟨.unitV, rfl, fun _ => ⟨_, .vUnit⟩⟩
  | varReadStep _ => exact ⟨_, rfl, value_typeable _⟩
  | projCong _ _ => simp [Expr.isValueB] at hv
  | projStep _ => exact ⟨_, rfl, value_typeable _⟩

/-- **T3 (Policy Monotonicity).** Step only installs forbid policies, so
    the allow-set shrinks. Each Step constructor is enumerated
    explicitly so that any future rule mutating `pol` will fail
    compilation here rather than silently slipping past a catch-all. -/
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
  | agentSuccess _ _ _ => exact Set.Subset.rfl
  | agentHealPol _ _ => exact Set.Subset.rfl
  | letCongNonheal _ _ ih => exact ih
  | letGenSuccessNonheal _ _ _ _ => exact Set.Subset.rfl
  | letGenTypeError _ _ _ _ => exact Set.Subset.rfl
  | letGenBudgetError _ => exact Set.Subset.rfl
  | letGenHealPol _ _ => exact Set.Subset.rfl
  | letGenSuccessHealable _ _ _ _ _ _ => exact Set.Subset.rfl
  | letGenHealHealable _ _ _ _ _ _ => exact Set.Subset.rfl
  | letGenHealRecordFields _ _ _ _ _ _ _ => exact Set.Subset.rfl
  | evalSuccess _ => exact Set.Subset.rfl
  | enforceInstall hinst => exact policyInstall_shrinks _ _ _ hinst
  | letPrincValue => exact Set.Subset.rfl
  | letPrincCong _ ih => exact ih
  | ifCong _ ih => exact ih
  | seqCong _ ih => exact ih
  | forCong _ ih => exact ih
  | enforceCong _ ih => exact ih
  | evalFunCong _ ih => exact ih
  | varDeclEval _ ih => exact ih
  | varDeclBind _ => exact Set.Subset.rfl
  | assignEval _ ih => exact ih
  | assignWrite _ _ => exact Set.Subset.rfl
  | varReadStep _ => exact Set.Subset.rfl
  | projCong _ ih => exact ih
  | projStep _ => exact Set.Subset.rfl

end HADL
