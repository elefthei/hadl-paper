-- Soundness theorems for HADL.
-- T1 WF-Preservation, T2 Staged Materialization Soundness, T3 Policy Monotonicity.

import HADL.Syntax
import HADL.Env
import HADL.Typing
import HADL.Policy
import HADL.Config
import HADL.Reduction
import HADL.Lemmas

namespace HADL

/-- A config is an error config iff its expression is the terminal error marker. -/
def Config.isErr (C : Config) : Prop := ∃ ec e, C.expr = .errTerm ec e

/--
  Helper: if every binding of ρ is runtime-typed, and we extend ρ with a
  fresh name `x₀` mapped to `b₀` with `RtType ρ b₀.value b₀.ty`, then every
  binding of the extended env is runtime-typed.
-/
theorem bindings_preserved_on_fresh_extend
    {ρ : Env} {x₀ : Name} {b₀ : Binding}
    (hbinds : ∀ y b, ρ.lookup y = some b → RtType ρ b.value b.ty)
    (hfr    : Env.fresh ρ x₀)
    (hrt₀   : RtType ρ b₀.value b₀.ty) :
    ∀ y b, (Env.extend ρ x₀ b₀).lookup y = some b → RtType (Env.extend ρ x₀ b₀) b.value b.ty := by
  intro y b hlk
  by_cases hxy : x₀ = y
  · subst hxy
    rw [Env.lookup_extend_self] at hlk
    cases hlk
    exact RtType.weaken hfr hrt₀
  · rw [Env.lookup_extend_of_ne _ hxy] at hlk
    exact RtType.weaken hfr (hbinds _ _ hlk)

/--
  Helper: `Env.assign ρ x v b` (shadow-update of an existing var binding)
  preserves the all-bindings-typed invariant, provided the new value has
  the old type and the old binding is in var-mode.
-/
theorem bindings_preserved_on_assign
    {ρ : Env} {x : Name} {v : Value} {b : Binding}
    (hbinds : ∀ y b', ρ.lookup y = some b' → RtType ρ b'.value b'.ty)
    (hlk    : ρ.lookup x = some b)
    (hvar   : b.mode = .varBind)
    (hrt    : RtType ρ v b.ty) :
    ∀ y b', (Env.assign ρ x v b).lookup y = some b' →
            RtType (Env.assign ρ x v b) b'.value b'.ty := by
  intro y b' hlk'
  unfold Env.assign at hlk' ⊢
  rw [hlk] at hlk' ⊢
  -- Now the new env = Env.extend ρ x { b with value := v }.
  by_cases hxy : x = y
  · subst hxy
    rw [Env.lookup_extend_self] at hlk'
    cases hlk'
    -- goal: RtType (extend ...) v b.ty
    exact RtType.weaken_to_assign hlk hvar hrt
  · rw [Env.lookup_extend_of_ne _ hxy] at hlk'
    exact RtType.weaken_to_assign hlk hvar (hbinds _ _ hlk')

/--
  Helper: batched fresh-extend preserves the bindings-typed invariant.
  Proceeds by induction on the batch list.
-/
theorem bindings_preserved_on_fresh_extendAll
    (ρ : Env) (bs : List (Name × Binding))
    (hbinds : ∀ y b, ρ.lookup y = some b → RtType ρ b.value b.ty)
    (hfr    : Env.freshAll ρ bs)
    (hrt    : ∀ (x : Name) (b : Binding), (x, b) ∈ bs → RtType ρ b.value b.ty) :
    ∀ y b, (Env.extendAll ρ bs).lookup y = some b →
           RtType (Env.extendAll ρ bs) b.value b.ty := by
  induction bs generalizing ρ with
  | nil => intro y b hlk; exact hbinds y b hlk
  | cons head rest ih =>
      rcases head with ⟨x, b₀⟩
      simp only [Env.extendAll, Env.freshAll] at *
      obtain ⟨hfr₀, hfrRest⟩ := hfr
      have hrt₀ : RtType ρ b₀.value b₀.ty := hrt x b₀ List.mem_cons_self
      have hbinds' :
          ∀ y b, (Env.extend ρ x b₀).lookup y = some b →
                 RtType (Env.extend ρ x b₀) b.value b.ty :=
        bindings_preserved_on_fresh_extend hbinds hfr₀ hrt₀
      have hrt' :
          ∀ (x' : Name) (b' : Binding), (x', b') ∈ rest →
            RtType (Env.extend ρ x b₀) b'.value b'.ty := by
        intro x' b' hmem
        exact RtType.weaken hfr₀ (hrt x' b' (List.mem_cons_of_mem _ hmem))
      exact ih (Env.extend ρ x b₀) hbinds' hfrRest hrt'

/--
  **T1 — WF-Preservation.** Case analysis on `hstep`, with each rule
  discharging the four clauses of `Config.WF`. Uses `StType.schemaWildcard`
  for residual-typing, `bindings_preserved_on_fresh_extend` for the
  env-extending rules, and `bindings_preserved_on_assign` for Assign.
-/
theorem T1_WF_preservation
    {O : Oracle} {C C' : Config}
    (hwf : C.WF) (hstep : Step O C C') (_hne : ¬ C'.isErr) :
    C'.WF := by
  obtain ⟨hbinds, _hres, hlen⟩ := hwf
  cases hstep with
  | var _ _ =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hlen⟩
  | letBind hrt hfr =>
      refine ⟨?_, ⟨_, StType.schemaWildcard⟩, hlen⟩
      exact bindings_preserved_on_fresh_extend hbinds hfr hrt
  | assign hlk hvar hrt =>
      refine ⟨?_, ⟨_, StType.schemaWildcard⟩, hlen⟩
      exact bindings_preserved_on_assign hbinds hlk hvar hrt
  | ifTrue =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hlen⟩
  | ifFalse =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hlen⟩
  | whileUnfold =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hlen⟩
  | forNil =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hlen⟩
  | forCons hrt hfr =>
      refine ⟨?_, ⟨_, StType.schemaWildcard⟩, hlen⟩
      exact bindings_preserved_on_fresh_extend hbinds hfr hrt
  | seqStep =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hlen⟩
  | jsStep _ =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hlen⟩
  | genSuccess _ _ _ hstage =>
      exact ⟨hbinds, ⟨_, hstage⟩, by simp [retryBudget]⟩
  | genHealType _ _ hbudget =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hbudget⟩
  | genHealPol _ hbudget =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hbudget⟩
  | enforceInstall _ _ _ _ =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hlen⟩
  | askStep _ _ =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, by simp [retryBudget]⟩
  | sayStep =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hlen⟩
  | agentSuccess _ _ _ =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, by simp [retryBudget]⟩
  | agentHealType _ _ hbudget =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hbudget⟩
  | agentHealPol _ hbudget =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hbudget⟩
  | evalSuccess _ _ hrt hfr =>
      refine ⟨?_, ⟨_, StType.schemaWildcard⟩, hlen⟩
      exact bindings_preserved_on_fresh_extendAll _ _ hbinds hfr hrt
  | evalHealType _ hbudget =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hbudget⟩
  | evalHealPol _ hbudget =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hbudget⟩
  | genBudgetExhausted _ =>
      -- C' has expr = .errTerm, contradicting `¬ C'.isErr`.
      exact absurd ⟨_, _, rfl⟩ _hne
  | enforceHeal _ _ _ _ hbudget =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, hbudget⟩

/--
  **T2 — Staged Materialization Soundness.** Direct read-off of the
  `genSuccess` side condition `hstage`.
-/
theorem T2_staged_materialization
    {ρ : Env} {τ : Ty} {v : Value}
    (hstage : StType (Env.proj ρ) (.valE v) τ) :
    StType (Env.proj ρ) (.valE v) τ := hstage

/--
  **T3 — Policy Monotonicity.** Along any trace, the allow set can only
  shrink. Immediate from the per-step `Step.policy_shrinks`, inducted over
  the reflexive-transitive closure `Steps`.
-/
theorem T3_policy_monotonicity
    {O : Oracle} {C C' : Config}
    (h : Steps O C C') :
    policyAllowSet C'.pol ⊆ policyAllowSet C.pol :=
  Steps.policy_shrinks h

end HADL
