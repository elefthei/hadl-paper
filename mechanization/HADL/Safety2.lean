-- Oracle-relative safety (T4) for the agent family, plus congruence
-- lifting (two-sort + mutable-state).

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Oracle
import HADL.Config
import HADL.Reduction

namespace HADL

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
    (by simp [Ty.healable]) hauth hO

/-- Schema corollary of the parametric gen-progress theorem. -/
theorem T4_progress_gen
    (O : Oracle) (C : Config) (s : String) (n : Nat) (π : Principal)
    (hC : C.expr = .letE .tSchema (.gen .tSchema s (.bvar n)) (.var 0))
    (hwf : Config.WF C)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, RtType v .tSchema ∧ O s C.err .tSchema v) :
    ∃ C', Step O C C' :=
  T4_progress_gen_healable O C .tSchema s n π hC hwf
    (by simp [Ty.healable]) hauth hO

/-- Arrow corollary of the parametric gen-success theorem. -/
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
    (by simp [Ty.healable]) hauth hO

/-- Arrow corollary of the parametric gen-progress theorem. -/
theorem T4_progress_gen_arrow
    (O : Oracle) (C : Config) (args : List Ty) (ret : Ty)
    (s : String) (n : Nat) (π : Principal)
    (hC : C.expr = .letE (.tArrow args ret)
                        (.gen (.tArrow args ret) s (.bvar n)) (.var 0))
    (hwf : Config.WF C)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, RtType v (.tArrow args ret) ∧ O s C.err (.tArrow args ret) v) :
    ∃ C', Step O C C' :=
  T4_progress_gen_healable O C (.tArrow args ret) s n π hC hwf
    (by simp [Ty.healable]) hauth hO

/-- **Nested healing example (clinical_trial `Array[crf]`) at the progress
    level.** The progress analogue of `nested_array_of_schema_succeeds`
    from `Safety.lean`: a let-redex at `tArray tSchema` — the canonical
    nested-healing pattern — has a successor under any locally-truthful
    oracle. -/
theorem T4_progress_gen_nested_array_of_schema
    (O : Oracle) (C : Config) (s : String) (n : Nat) (π : Principal)
    (hC : C.expr = .letE (.tArray .tSchema)
                        (.gen (.tArray .tSchema) s (.bvar n)) (.var 0))
    (hwf : Config.WF C)
    (hauth : policyAllows C.pol π .gen)
    (hO : ∃ v, RtType v (.tArray .tSchema) ∧ O s C.err (.tArray .tSchema) v) :
    ∃ C', Step O C C' :=
  T4_progress_gen_healable O C (.tArray .tSchema) s n π hC hwf
    (by simp [Ty.healable]) hauth hO

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
    (by simp [Ty.healable]) hauth hO

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
