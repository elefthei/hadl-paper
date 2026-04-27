-- Cedar-backed policy; append-only forbid installation.
-- Thin Cedar-Lean wrapper used by Reduction and Soundness.
-- Policies are drawn from Cedar's Lean mechanization; `policyInstall` is
-- append-only and only admits sequences of forbid-effect policies, which
-- gives us an iterated application of Cedar's `unchanged_deny_when_add_forbid`
-- to discharge `policyInstall_shrinks` without any free axioms.

import HADL.Syntax
import Mathlib.Data.Set.Basic
import Cedar.Spec
import Cedar.Thm.Authorization

namespace HADL

/-- The HADL policy state is a Cedar policy list. -/
abbrev Policy : Type := Cedar.Spec.Policies

inductive Action where
  | gen
  | agent
  deriving DecidableEq, Repr

/-- Opaque parser for the string form stored in `PolicyValue.mk`.
    Returns the parsed Cedar policies, or `none` on parse failure.
    This is a declared function (no body); it is not an axiom, so it
    does not contribute to `#print axioms`. -/
opaque parsePolicies : String → Option Cedar.Spec.Policies

/-- Ambient request for authorization questions: a principal/action pair is
    encoded as a Cedar request over the stub `Principal`/`Action` entity types. -/
def requestOf (π : Principal) (a : Action) : Cedar.Spec.Request :=
  { principal := { ty := { id := "Principal", path := [] }, eid := π.toString }
  , action    := { ty := { id := "Action",    path := [] },
                   eid := match a with
                          | .gen   => "gen"
                          | .agent => "agent" }
  , resource  := { ty := { id := "Resource", path := [] }, eid := "self" }
  , context   := Cedar.Data.Map.empty }

/-- The entity store is empty: we reason about policies that don't depend on
    the entity hierarchy. -/
def ambientEntities : Cedar.Spec.Entities := Cedar.Data.Map.empty

/-- Authorization: Cedar's decision is either `.allow` or `.deny`. -/
def policyAllows (P : Policy) (π : Principal) (a : Action) : Prop :=
  (Cedar.Spec.isAuthorized (requestOf π a) ambientEntities P).decision = .allow

def policyAllowSet (P : Policy) : Set (Principal × Action) :=
  { pa | policyAllows P pa.1 pa.2 }

/-- Install new policies from a `PolicyValue`. We only admit policies whose
    effect is `forbid`; other installs are rejected, so the installed policy
    state only ever tightens. Append-only: new forbids are prepended. -/
def policyInstall (P : Policy) (pv : PolicyValue) : Option Policy :=
  match pv with
  | .mk s =>
    match parsePolicies s with
    | none => none
    | some ps =>
      if ps.all (fun p => decide (p.effect = .forbid)) then
        some (ps ++ P)
      else
        none

/-- Iterated Cedar `unchanged_deny_when_add_forbid`: prepending any list of
    forbid-effect policies keeps a `deny` decision denied. -/
theorem deny_preserved_by_forbid_prefix
    (req : Cedar.Spec.Request) (ent : Cedar.Spec.Entities)
    (ps P : Cedar.Spec.Policies)
    (hall : ∀ p ∈ ps, p.effect = .forbid)
    (hdeny : (Cedar.Spec.isAuthorized req ent P).decision = .deny) :
    (Cedar.Spec.isAuthorized req ent (ps ++ P)).decision = .deny := by
  induction ps with
  | nil => simpa using hdeny
  | cons p rest ih =>
    have hp : p.effect = .forbid := hall p (by simp)
    have hrest : ∀ q ∈ rest, q.effect = .forbid :=
      fun q hq => hall q (by simp [hq])
    have hrestDeny := ih hrest
    -- Goal: decision of (p :: rest ++ P) = deny
    exact Cedar.Thm.unchanged_deny_when_add_forbid req ent (rest ++ P) p hp hrestDeny

/-- Core shrink lemma: installing forbid policies only removes allows. -/
theorem policyInstall_shrinks
    (P P' : Policy) (pv : PolicyValue) :
    policyInstall P pv = some P' →
    policyAllowSet P' ⊆ policyAllowSet P := by
  intro hinst pa hpa
  -- Unfold install; destruct the parse and the all-forbid check.
  rcases pv with ⟨s⟩
  simp [policyInstall] at hinst
  rcases hps : parsePolicies s with _ | ps
  · simp [hps] at hinst
  · simp [hps] at hinst
    rcases hinst with ⟨hall, heq⟩
    subst heq
    -- `pa ∈ allowSet (ps ++ P)` and we want `pa ∈ allowSet P`.
    -- Equivalently, `allow (ps ++ P)` implies `allow P`; contrapositive of
    -- `deny_preserved_by_forbid_prefix`, using binary Decision.
    simp [policyAllowSet, Set.mem_setOf_eq, policyAllows] at hpa ⊢
    by_contra hne
    -- hne : decision P ≠ allow, so decision P = deny (binary).
    have hdeny : (Cedar.Spec.isAuthorized (requestOf pa.1 pa.2) ambientEntities P).decision = .deny := by
      cases hd : (Cedar.Spec.isAuthorized (requestOf pa.1 pa.2) ambientEntities P).decision with
      | allow => exact (hne hd).elim
      | deny  => rfl
    have hall' : ∀ p ∈ ps, p.effect = .forbid := hall
    have :=
      deny_preserved_by_forbid_prefix
        (requestOf pa.1 pa.2) ambientEntities ps P hall' hdeny
    -- But `hpa` says the decision on `ps ++ P` is `allow`; contradiction.
    rw [hpa] at this
    cases this

end HADL
