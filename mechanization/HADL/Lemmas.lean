-- Auxiliary lemmas for the substitution-based HADL model.
-- Phase B target: discharge the sorries in this file.

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Config
import HADL.Reduction

namespace HADL

/-- ErrCtx.retries grows by exactly 1 when we append a single error event. -/
theorem retries_append_error
    (ec : ErrCtx) (s : String) :
    ErrCtx.retries (ec ++ [Event.error s]) = ErrCtx.retries ec + 1 := by
  simp

/-- Appending a success event resets the retry counter. -/
theorem retries_append_success (ec : ErrCtx) :
    ErrCtx.retries (ec ++ [Event.success]) = 0 := by
  simp

/-- Single-step reduction can only shrink (or preserve) the allow set. -/
theorem Step.policy_shrinks {O : Oracle} {C C' : Config}
    (h : Step O C C') :
    policyAllowSet C'.pol ⊆ policyAllowSet C.pol := by
  induction h with
  | letBind _               => exact fun _ hp => hp
  | ifTrue                   => exact fun _ hp => hp
  | ifFalse                  => exact fun _ hp => hp
  | whileUnfold              => exact fun _ hp => hp
  | forNil                   => exact fun _ hp => hp
  | forCons                  => exact fun _ hp => hp
  | seqStep                  => exact fun _ hp => hp
  | jsStep _                 => exact fun _ hp => hp
  | sayStep                  => exact fun _ hp => hp
  | askStep _ _              => exact fun _ hp => hp
  | oracleSuccess _ _ _      => exact fun _ hp => hp
  | oracleHealType _ _ _ _   => exact fun _ hp => hp
  | oracleHealPol _ _        => exact fun _ hp => hp
  | evalSuccess _            => exact fun _ hp => hp
  | enforceInstall hinst     => exact policyInstall_shrinks _ _ _ hinst
  | letCong _ ih             => exact ih
  | ifCong _ ih              => exact ih
  | seqCong _ ih             => exact ih
  | forCong _ ih             => exact ih
  | enforceCong _ ih         => exact ih
  | evalFunCong _ ih         => exact ih

/-- Multi-step reduction can only shrink (or preserve) the allow set. -/
theorem Steps.policy_shrinks {O : Oracle} {C C' : Config}
    (h : Steps O C C') :
    policyAllowSet C'.pol ⊆ policyAllowSet C.pol := by
  induction h with
  | refl => exact fun _ hp => hp
  | step s _ ih => exact fun x hp => Step.policy_shrinks s (ih hp)

end HADL
