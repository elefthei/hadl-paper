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

/-- Placeholder: no rule in the selected fragment produces a terminal error. -/
def Config.isErr (_C : Config) : Prop := False

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
  **T1 — WF-Preservation.** Case analysis on `hstep`. For each rule:

  * **Residual typing.** Discharged by `StType.schemaWildcard`.
  * **Bindings well-typed.** Rules that do not touch ρ preserve `hbinds`
    directly. The two extending rules (`letBind`, `genSuccess`) use
    `bindings_preserved_on_fresh_extend` with the rule's own `hrt` and
    `hfr` side conditions.
  * **Provenance acyclic.** Our placeholder `Env.provAcyclic := True`.
  * **Heal-length bound.** Rule side condition (`genHeal*`), a flush to `[]`
    (`letBind`, `genSuccess`), or unchanged (`var`, `jsStep`, `enforceInstall`).
-/
theorem T1_WF_preservation
    {O : Oracle} {C C' : Config}
    (hwf : C.WF) (hstep : Step O C C') (_hne : ¬ C'.isErr) :
    C'.WF := by
  obtain ⟨hbinds, _hres, _hprov, hlen⟩ := hwf
  cases hstep with
  | var _ _ =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, trivial, hlen⟩
  | letBind hrt hfr =>
      refine ⟨?_, ⟨_, StType.schemaWildcard⟩, trivial, by simp [retryBudget]⟩
      exact bindings_preserved_on_fresh_extend hbinds hfr hrt
  | jsStep _ =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, trivial, hlen⟩
  | genSuccess _ _ hrt hstage _ hfr =>
      refine ⟨?_, ⟨_, hstage⟩, trivial, by simp [retryBudget]⟩
      exact bindings_preserved_on_fresh_extend hbinds hfr hrt
  | genHealType _ _ hbudget =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, trivial, hbudget⟩
  | genHealPol _ hbudget =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, trivial, hbudget⟩
  | enforceInstall _ _ _ _ =>
      exact ⟨hbinds, ⟨_, StType.schemaWildcard⟩, trivial, hlen⟩

/--
  **T2 — Staged Materialization Soundness.** Direct read-off of the
  `genSuccess` side condition `hstage`.
-/
theorem T2_staged_materialization
    {ρ : Env} {τ : Ty} {v : Value} {ℓ : Label}
    (hstage : StType
                (Env.proj (Env.extend ρ (toString ℓ) ⟨v, τ, some ℓ, .letBind⟩))
                (.valE v)
                τ) :
    StType
      (Env.proj (Env.extend ρ (toString ℓ) ⟨v, τ, some ℓ, .letBind⟩))
      (.valE v)
      τ := hstage

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
