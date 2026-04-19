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

theorem Step.policy_shrinks {O : Oracle} {C C' : Config}
    (h : Step O C C') :
    policyAllowSet C'.pol ⊆ policyAllowSet C.pol := by
  cases h with
  | var _ _         => exact fun _ hp => hp
  | letBind _       => exact fun _ hp => hp
  | jsStep _        => exact fun _ hp => hp
  | genSuccess _ _ _ _ _ => exact fun _ hp => hp
  | genHealType _ _ _ => exact fun _ hp => hp
  | genHealPol _ _   => exact fun _ hp => hp
  | enforceInstall _ _ _ hinst =>
      exact policyInstall_shrinks _ _ _ hinst

theorem Steps.policy_shrinks {O : Oracle} {C C' : Config}
    (h : Steps O C C') :
    policyAllowSet C'.pol ⊆ policyAllowSet C.pol := by
  induction h with
  | refl => exact fun _ hp => hp
  | step s _ ih => exact fun x hp => Step.policy_shrinks s (ih hp)

end HADL
