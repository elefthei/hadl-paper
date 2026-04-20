import HADL.Syntax
import HADL.Env
import HADL.Typing
import HADL.Policy
import HADL.Config
import HADL.Reduction

namespace HADL

theorem Env.proj_extend
    (ρ : Env) (x : Name) (b : Binding) :
    Env.proj (Env.extend ρ x b) = (x, b.ty) :: Env.proj ρ := by
  simp [Env.extend, Env.proj]

/-- Looking up the key just added returns its binding. -/
theorem Env.lookup_extend_self (ρ : Env) (x : Name) (b : Binding) :
    (Env.extend ρ x b).lookup x = some b := by
  simp [Env.extend, Env.lookup]

/-- Looking up a *different* key sees through the new cons cell. -/
theorem Env.lookup_extend_of_ne
    {ρ : Env} {x y : Name} (b : Binding) (h : x ≠ y) :
    (Env.extend ρ x b).lookup y = ρ.lookup y := by
  simp [Env.extend, Env.lookup, h]

/-- Shadow-assign preserves the old binding's ty (value is overwritten). -/
theorem Env.lookup_assign_self_of_exists
    {ρ : Env} {x : Name} {v : Value} {b fallback : Binding}
    (hlk : ρ.lookup x = some b) :
    (ρ.assign x v fallback).lookup x = some { b with value := v } := by
  unfold Env.assign
  rw [hlk]
  exact Env.lookup_extend_self _ _ _

/-- Shadow-assign is the identity on other keys. -/
theorem Env.lookup_assign_of_ne
    {ρ : Env} {x y : Name} {v : Value} {fallback : Binding}
    (h : x ≠ y) :
    (ρ.assign x v fallback).lookup y = ρ.lookup y := by
  unfold Env.assign
  split <;> exact Env.lookup_extend_of_ne _ h

/-- A fresh key is not bound in ρ. -/
theorem Env.lookup_of_fresh
    {ρ : Env} {x : Name} (h : Env.fresh ρ x) :
    ρ.lookup x = none := by
  induction ρ with
  | nil => simp [Env.lookup, List.find?]
  | cons hd tl ih =>
    simp only [Env.fresh, Env.dom, List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, htail⟩ := h
    -- hne : x ≠ hd.1; lookup steps past this cell.
    have hne' : hd.1 ≠ x := fun h' => hne h'.symm
    simp [Env.lookup, List.find?, hne']
    -- Reduce to the tail via ih.
    have := ih htail
    simpa [Env.lookup] using this

/-- If `x` is fresh in ρ and `y` IS bound in ρ, then `x ≠ y`. -/
theorem Env.ne_of_fresh_of_lookup
    {ρ : Env} {x y : Name} {b : Binding}
    (hfr : Env.fresh ρ x) (hlk : ρ.lookup y = some b) : x ≠ y := by
  intro h
  subst h
  rw [Env.lookup_of_fresh hfr] at hlk
  cases hlk

/--
  Weakening for runtime typing under a fresh extension. Freshness is
  needed only in the `tVarResolve` case, whose lookup must see past the
  newly-added cell — which it does when the new name is not already in ρ.
-/
theorem RtType.weaken
    {ρ : Env} {v : Value} {τ : Ty}
    {x : Name} {b : Binding} (hfr : Env.fresh ρ x)
    (h : RtType ρ v τ) :
    RtType (Env.extend ρ x b) v τ := by
  induction h with
  | vUnit => exact .vUnit
  | vBool => exact .vBool
  | vInt  => exact .vInt
  | vStr  => exact .vStr
  | vSchema => exact .vSchema
  | vPol  => exact .vPol
  | tVarResolve hlk _ ih =>
      -- x ≠ y because y is bound in ρ and x is fresh in ρ.
      have hxy : x ≠ _ := Env.ne_of_fresh_of_lookup hfr hlk
      refine RtType.tVarResolve ?_ ih
      rw [Env.lookup_extend_of_ne _ hxy]
      exact hlk

/--
  Weakening for runtime typing across an Assign-style shadow extension.
  The new cell carries `.varBind`, so it cannot shadow a schema binding
  (which must be `.letBind`). This discharges the `tVarResolve` case by
  contradiction on the mode.
-/
theorem RtType.weaken_to_assign
    {ρ : Env} {v₀ : Value} {τ₀ : Ty}
    {x : Name} {b : Binding} {v : Value}
    (hlk_old : ρ.lookup x = some b)
    (hvar : b.mode = .varBind)
    (h : RtType ρ v₀ τ₀) :
    RtType (Env.extend ρ x { b with value := v }) v₀ τ₀ := by
  induction h with
  | vUnit => exact .vUnit
  | vBool => exact .vBool
  | vInt  => exact .vInt
  | vStr  => exact .vStr
  | vSchema => exact .vSchema
  | vPol  => exact .vPol
  | tVarResolve hlk hrec ih =>
      rename_i yname _ _
      have hne : x ≠ yname := by
        intro heq
        subst heq
        rw [hlk_old] at hlk
        cases hlk
        cases hvar
      refine RtType.tVarResolve ?_ ih
      rw [Env.lookup_extend_of_ne _ hne]
      exact hlk

theorem Step.policy_shrinks {O : Oracle} {C C' : Config}
    (h : Step O C C') :
    policyAllowSet C'.pol ⊆ policyAllowSet C.pol := by
  induction h with
  | var _ _             => exact fun _ hp => hp
  | letBind _ _         => exact fun _ hp => hp
  | assign _ _ _        => exact fun _ hp => hp
  | ifTrue              => exact fun _ hp => hp
  | ifFalse             => exact fun _ hp => hp
  | whileUnfold         => exact fun _ hp => hp
  | forNil              => exact fun _ hp => hp
  | forCons _ _         => exact fun _ hp => hp
  | seqStep             => exact fun _ hp => hp
  | jsStep _            => exact fun _ hp => hp
  | genSuccess _ _ _ _ => exact fun _ hp => hp
  | genHealType _ _ _   => exact fun _ hp => hp
  | genHealPol _ _      => exact fun _ hp => hp
  | enforceInstall _ _ _ hinst =>
      exact policyInstall_shrinks _ _ _ hinst
  | askStep _ _         => exact fun _ hp => hp
  | sayStep             => exact fun _ hp => hp
  | agentSuccess _ _ _  => exact fun _ hp => hp
  | agentHealType _ _ _ => exact fun _ hp => hp
  | agentHealPol _ _    => exact fun _ hp => hp
  | evalSuccess _ _ _ _ => exact fun _ hp => hp
  | evalHealType _ _    => exact fun _ hp => hp
  | evalHealPol _ _     => exact fun _ hp => hp
  | genBudgetExhausted _ => exact fun _ hp => hp
  | enforceHeal _ _ _ _ _ => exact fun _ hp => hp
  -- Congruence cases: inner IH already gives the monotonicity.
  | letCong _ _ ih    => exact ih
  | assignCong _ _ ih => exact ih
  | ifCong _ _ ih     => exact ih
  | seqCong _ _ ih    => exact ih
  | forCong _ _ ih    => exact ih

theorem Steps.policy_shrinks {O : Oracle} {C C' : Config}
    (h : Steps O C C') :
    policyAllowSet C'.pol ⊆ policyAllowSet C.pol := by
  induction h with
  | refl => exact fun _ hp => hp
  | step s _ ih => exact fun x hp => Step.policy_shrinks s (ih hp)

end HADL
