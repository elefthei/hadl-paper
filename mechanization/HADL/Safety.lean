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

/-- **T4a (Budget → No Heal).** With `gen` no longer a standalone redex,
    the standalone `gen τ s pr` has *no* transitions at all. (`gen` only
    reduces inside a let-redex.) The honest statement is therefore the
    *direct negation*: there is no successor configuration. The earlier
    universal-implication form was vacuously true and read as a
    no-op-on-paper claim. -/
theorem T4_budget_no_heal
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (τ : Ty) (s : String) (n : Nat)
    (_hover : ErrCtx.retries ec > retryBudget) :
    ¬ ∃ C', Step O ⟨ec, P, σ, .gen τ s (.bvar n)⟩ C' := by
  rintro ⟨C', h⟩
  -- `.gen τ s pr` is not a standalone redex; no Step rule applies.
  cases h

/-- **T4b (Truthful Success).** If the oracle is eventually truthful for a
    `gen` site, the policy allows the action, AND τ is Schema (Phase 1
    coverage; Policy & Arrow extend in Phases 2 & 3), there exists an
    error context and store from which a successful let-redex step
    fires from `let _ : .tSchema = gen .tSchema s π ; var 0`.
    The continuation `.var 0` types trivially at `.tSchema` via
    `StaticTypeOK.var0`. -/
theorem T4_truthful_success
    (O : Oracle) (P : Policy) (s : String) (n : Nat) (π : Principal)
    (hauth : policyAllows P π .gen)
    (htruth : Oracle.eventuallyTruthful O retryBudget s .tSchema (fun _ => True)) :
    ∃ ec σ C',
      Step O ⟨ec, P, σ, .letE .tSchema (.gen .tSchema s (.bvar n)) (.var 0)⟩ C' := by
  obtain ⟨ec, _hretries, v, hrt, hO, _⟩ := htruth
  exact ⟨ec, Store.empty, _,
         Step.letGenSuccessHealable (π := π) (by simp)
           hauth hO hrt StaticTypeOK.var0 (Value.recordSatisfies_var0 v)⟩

/-- **T4b-Arrow (Truthful Success at arrow type).** Phase 3 analogue of
    `T4_truthful_success`: same existential shape, type generalized to
    `tArrow args ret`. Continuation `.var 0` types via the universally-
    quantified `StaticTypeOK.var0`. -/
theorem T4_truthful_success_arrow
    (O : Oracle) (P : Policy) (args : List Ty) (ret : Ty)
    (s : String) (n : Nat) (π : Principal)
    (hauth : policyAllows P π .gen)
    (htruth : Oracle.eventuallyTruthful O retryBudget s
                (.tArrow args ret) (fun _ => True)) :
    ∃ ec σ C',
      Step O ⟨ec, P, σ,
              .letE (.tArrow args ret)
                    (.gen (.tArrow args ret) s (.bvar n)) (.var 0)⟩ C' := by
  obtain ⟨ec, _hretries, v, hrt, hO, _⟩ := htruth
  exact ⟨ec, Store.empty, _,
         Step.letGenSuccessHealable (π := π) (by simp)
           hauth hO hrt StaticTypeOK.var0 (Value.recordSatisfies_var0 v)⟩

/-- **T4b-Healable (Truthful Success at any healable τ).** Parametric
    generalization of `T4_truthful_success` and `T4_truthful_success_arrow`.
    Subsumes both via the parametric `letGenSuccessHealable` rule. The
    canonical use is the clinical-trial pattern `Array[crf]` where
    `crf : Schema` (see `nested_array_of_schema_succeeds` below). -/
theorem T4_truthful_success_healable
    (O : Oracle) (P : Policy) (τ : Ty)
    (s : String) (n : Nat) (π : Principal)
    (hheal : Ty.healable τ = true)
    (hauth : policyAllows P π .gen)
    (htruth : Oracle.eventuallyTruthful O retryBudget s τ (fun _ => True)) :
    ∃ ec σ C',
      Step O ⟨ec, P, σ, .letE τ (.gen τ s (.bvar n)) (.var 0)⟩ C' := by
  obtain ⟨ec, _hretries, v, hrt, hO, _⟩ := htruth
  exact ⟨ec, Store.empty, _,
         Step.letGenSuccessHealable (π := π) hheal hauth hO hrt StaticTypeOK.var0
           (Value.recordSatisfies_var0 v)⟩

/-- **Nested healing example (clinical_trial `Array[crf]`).** A let-redex
    at `tArray tSchema` — an array of healable element types, the canonical
    nested-healing case from `figures/clinical_trial.tex` line 13 — fires
    `letGenSuccessHealable` under any eventually-truthful oracle. The
    `Healable(tArray tSchema)` premise is discharged by the recursive
    `Ty.healable` definition. -/
theorem nested_array_of_schema_succeeds
    (O : Oracle) (P : Policy) (s : String) (n : Nat) (π : Principal)
    (hauth : policyAllows P π .gen)
    (htruth : Oracle.eventuallyTruthful O retryBudget s
                (.tArray .tSchema) (fun _ => True)) :
    ∃ ec σ C',
      Step O ⟨ec, P, σ,
              .letE (.tArray .tSchema)
                    (.gen (.tArray .tSchema) s (.bvar n)) (.var 0)⟩ C' :=
  T4_truthful_success_healable O P (.tArray .tSchema) s n π
    (by simp [Ty.healable]) hauth htruth

/-- **Clinical-trial visit.cost projection (paper L17 / L18).** A record
    field projection on an oracle-produced `recV` steps to the field's
    value when the field is present. This is the smallest end-to-end
    fragment of `figures/clinical_trial.tex` that previously had no
    Lean correspondent. The stuck case (field absent) is the paper's
    self-heal trigger; that healing rule is documented future work. -/
theorem clinical_trial_visit_cost_projects
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store)
    (fs : List (String × Value)) (n : Int)
    (h : fs.lookup "cost" = some (.numV n)) :
    Step O ⟨ec, P, σ, .proj (.val (.recV fs)) "cost"⟩
           ⟨ec, P, σ, .val (.numV n)⟩ :=
  Step.projStep h

/-! ## Agent / progress family (formerly Safety2.lean — merged in Phase M).

    These theorems take the raw `∃ v, RtType ∧ O ...` hypothesis form
    used by the agent-family progress lemmas (vs the eventuallyTruthful
    form above). The two hypothesis styles are interconvertible; both
    are kept because each matches a distinct proof obligation in
    downstream Examples.lean. -/

/-- Agent analogue of `T4_truthful_success`. Carries the store through
    unchanged. -/
theorem T4_truthful_success_agent
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (s : String) (n : Nat) (π : Principal)
    (hauth : policyAllows P π .agent)
    (hO : ∃ v, RtType v .tString ∧ O s ec .tString v) :
    ∃ C', Step O ⟨ec, P, σ, .agent s (.bvar n)⟩ C' := by
  obtain ⟨v, hrt, ho⟩ := hO
  exact ⟨_, Step.agentSuccess (π := π) hauth ho hrt⟩

/-- **Gen success at any healable `τ` (parametric).** Subsumes
    `T4_truthful_success_gen` and `T4_truthful_success_gen_arrow`: with
    `gen` as a let-only redex, success fires on `let _ : τ = gen τ s π ; var 0`
    for any `τ` with `Ty.healable τ = true`. The shape-specific Schema and
    Arrow forms below are one-line corollaries. -/
theorem T4_truthful_success_gen_healable
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (τ : Ty)
    (s : String) (n : Nat) (π : Principal)
    (hheal : Ty.healable τ = true)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, RtType v τ ∧ O s ec τ v) :
    ∃ C',
      Step O ⟨ec, P, σ, .letE τ (.gen τ s (.bvar n)) (.var 0)⟩ C' := by
  obtain ⟨v, hrt, ho⟩ := hO
  exact ⟨_, Step.letGenSuccessHealable (π := π) hheal hauth ho hrt StaticTypeOK.var0
              (Value.recordSatisfies_var0 v)⟩

/-- **Progress for `gen` at any healable `τ` (parametric).** Subsumes
    `T4_progress_gen` and `T4_progress_gen_arrow`. The let-redex
    `let _ : τ = gen τ s π ; var 0` has a successor whenever the policy
    allows, the oracle is locally truthful, and `Healable τ`. -/
theorem T4_progress_gen_healable
    (O : Oracle) (C : Config) (τ : Ty) (s : String) (n : Nat) (π : Principal)
    (hC : C.expr = .letE τ (.gen τ s (.bvar n)) (.var 0))
    (_hwf : Config.WF C)
    (hheal : Ty.healable τ = true)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, RtType v τ ∧ O s C.err τ v) :
    ∃ C', Step O C C' := by
  rcases C with ⟨ec, P, σ, e⟩
  cases hC
  exact T4_truthful_success_gen_healable O ec P σ τ s n π hheal hauth hO

/-- Schema corollary of the parametric gen-success theorem. -/
theorem T4_truthful_success_gen
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (s : String) (n : Nat) (π : Principal)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, RtType v .tSchema ∧ O s ec .tSchema v) :
    ∃ C',
      Step O ⟨ec, P, σ, .letE .tSchema (.gen .tSchema s (.bvar n)) (.var 0)⟩ C' :=
  T4_truthful_success_gen_healable O ec P σ .tSchema s n π
    (by simp) hauth hO

/-- Schema corollary of the parametric gen-progress theorem. -/
theorem T4_progress_gen
    (O : Oracle) (C : Config) (s : String) (n : Nat) (π : Principal)
    (hC : C.expr = .letE .tSchema (.gen .tSchema s (.bvar n)) (.var 0))
    (hwf : Config.WF C)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, RtType v .tSchema ∧ O s C.err .tSchema v) :
    ∃ C', Step O C C' :=
  T4_progress_gen_healable O C .tSchema s n π hC hwf
    (by simp) hauth hO

/-- Arrow corollary of the parametric gen-success theorem (success-form
    only — the progress-form `T4_progress_gen_arrow` was dropped during
    the Phase M simplification pass as it was a 1-line specialization
    with no callers). -/
theorem T4_truthful_success_gen_arrow
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store)
    (args : List Ty) (ret : Ty) (s : String) (n : Nat) (π : Principal)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, RtType v (.tArrow args ret) ∧ O s ec (.tArrow args ret) v) :
    ∃ C',
      Step O ⟨ec, P, σ,
              .letE (.tArrow args ret)
                    (.gen (.tArrow args ret) s (.bvar n)) (.var 0)⟩ C' :=
  T4_truthful_success_gen_healable O ec P σ (.tArrow args ret) s n π
    (by simp) hauth hO

/-- **Clinical-trial `gen` at Policy (paper L9-10).** A let-redex at
    `tPolicy` — `let policy: Policy = gen "..." ; var 0` from
    `figures/clinical_trial.tex` line 9-10 — has a successor under any
    locally-truthful oracle producing a `polV` value. Mechanizes the
    "gradual policy typing" claim from the paper caption: oracle-
    generated policies are first-class healable materializations,
    handled by the same parametric `letGenSuccessHealable` rule that
    covers Schema and Array[Schema]. -/
theorem T4_progress_gen_policy
    (O : Oracle) (C : Config) (s : String) (n : Nat) (π : Principal)
    (hC : C.expr = .letE .tPolicy (.gen .tPolicy s (.bvar n)) (.var 0))
    (hwf : Config.WF C)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, RtType v .tPolicy ∧ O s C.err .tPolicy v) :
    ∃ C', Step O C C' :=
  T4_progress_gen_healable O C .tPolicy s n π hC hwf
    (by simp) hauth hO

/-- Progress for `agent`. -/
theorem T4_progress_agent
    (O : Oracle) (C : Config) (s : String) (n : Nat) (π : Principal)
    (hC : C.expr = .agent s (.bvar n))
    (_hwf : Config.WF C)
    (hauth : policyAllows C.pol π .agent)
    (hO : ∃ v, RtType v .tString ∧ O s C.err .tString v) :
    ∃ C', Step O C C' := by
  rcases C with ⟨ec, P, σ, e⟩
  cases hC
  exact T4_truthful_success_agent O ec P σ s n π hauth hO


end HADL
