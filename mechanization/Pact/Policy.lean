-- Cedar-backed policy state with the two-layer Pact discipline.
--
-- Static layer (mechanized here):
--   * `prinDeclared P π` — `π ∈ dom(P)` — the principal named at a
--     gen/agent redex must be declared in the current policy state.
--   * `policyInstall` discipline: a candidate is admitted only when
--     every rule has effect `forbid` AND no rule's principal scope
--     matches the unforbiddable `root`.
--
-- Runtime layer (NOT mechanized; lives in the Rust prototype):
--   * Cedar requests parameterized by Action ∈ {Read, Write, Exec}
--     and Resource ∈ files ∪ dirs, decided just-in-time by the
--     Copilot CLI monitor at every actual filesystem access. The
--     types and helpers below give the abstract shape used in the
--     monotonicity proof; nothing in the reduction rules consults
--     them.
--
-- Monotonicity is preserved: `policyInstall_shrinks` over the
-- `Principal × Action × Resource` allow-set falls out of iterated
-- `unchanged_deny_when_add_forbid` exactly as before.

import Pact.Syntax
import Mathlib.Data.Set.Basic
import Cedar.Spec
import Cedar.Thm.Authorization

namespace Pact

/-- The Pact policy state is a Cedar policy list. -/
abbrev Policy : Type := Cedar.Spec.Policies

/-- Filesystem actions decided by the runtime monitor. -/
inductive Action where
  | read
  | write
  | exec
  deriving DecidableEq, Repr, Inhabited

/-- Resources targeted by the runtime monitor: files or directories,
    with a wildcard escape for `*` patterns. -/
inductive Resource where
  | file (path : String) : Resource
  | dir  (path : String) : Resource
  | wildcard             : Resource
  deriving DecidableEq, Repr, Inhabited

def Action.toString : Action → String
  | .read  => "Read"
  | .write => "Write"
  | .exec  => "Exec"

def Resource.toString : Resource → String
  | .file p  => "File::" ++ p
  | .dir p   => "Dir::"  ++ p
  | .wildcard => "*"

/-- Opaque parser for the string form stored in `PolicyValue.mk`.
    Returns the parsed Cedar policies, or `none` on parse failure. -/
opaque parsePolicies : String → Option Cedar.Spec.Policies

/-- Cedar `EntityUID` for a Pact `Principal`. Uses the same encoding
    as the runtime monitor's request builder. -/
def Principal.toEUID (π : Principal) : Cedar.Spec.EntityUID :=
  { ty := { id := "Principal", path := [] }, eid := π.toString }

/-- Cedar `EntityUID` for an `Action` value. -/
def Action.toEUID (a : Action) : Cedar.Spec.EntityUID :=
  { ty := { id := "Action", path := [] }, eid := a.toString }

/-- Cedar `EntityUID` for a `Resource` value. -/
def Resource.toEUID (r : Resource) : Cedar.Spec.EntityUID :=
  { ty := { id := "Resource", path := [] }, eid := r.toString }

/-- Ambient Cedar request from a Pact triple. -/
def requestOf (π : Principal) (a : Action) (r : Resource) :
    Cedar.Spec.Request :=
  { principal := π.toEUID
  , action    := a.toEUID
  , resource  := r.toEUID
  , context   := Cedar.Data.Map.empty }

/-- The entity store is empty: we reason about policies that do not
    depend on the entity hierarchy. -/
def ambientEntities : Cedar.Spec.Entities := Cedar.Data.Map.empty

/-- Authorization: Cedar's decision is either `.allow` or `.deny`. -/
def policyAllows (P : Policy) (π : Principal) (a : Action) (r : Resource) :
    Prop :=
  (Cedar.Spec.isAuthorized (requestOf π a r) ambientEntities P).decision
    = .allow

/-- Allow-set indexed by the runtime triple. -/
def policyAllowSet (P : Policy) : Set (Principal × Action × Resource) :=
  { t | policyAllows P t.1 t.2.1 t.2.2 }

/-! ## Static admissibility: `π ∈ dom(P)` -/

/-- The explicit principal named by a Cedar scope, if any. `.any` and
    `.is _` do not pin a specific entity. -/
def scopeNamedPrincipal :
    Cedar.Spec.Scope → Option Cedar.Spec.EntityUID
  | .eq euid       => some euid
  | .mem euid      => some euid
  | .isMem _ euid  => some euid
  | _              => none

/-- The explicit principal of a Cedar policy, if any. -/
def policyPrincipalUID? (p : Cedar.Spec.Policy) :
    Option Cedar.Spec.EntityUID :=
  scopeNamedPrincipal p.principalScope.scope

/-- `π ∈ dom(P)`: either `π = root` (always declared, since the policy
    state begins as `allow(root, *, *)`) or some installed rule names
    `π` explicitly in its principal scope. -/
def prinDeclared (P : Policy) (π : Principal) : Prop :=
  π = Principal.root ∨
  ∃ p ∈ P, policyPrincipalUID? p = some π.toEUID

instance (P : Policy) (π : Principal) : Decidable (prinDeclared P π) := by
  unfold prinDeclared
  exact inferInstance

/-! ## Install discipline: `forbidOnly ∧ rootSafe` -/

/-- A scope matches the `root` principal when it could authorize
    against `root`. Conservative: `.any` and `.is Principal` always
    cover root. -/
def scopeMatchesRoot : Cedar.Spec.Scope → Bool
  | .any           => true
  | .is _          => true
  | .eq euid       => decide (euid = Principal.root.toEUID)
  | .mem euid      => decide (euid = Principal.root.toEUID)
  | .isMem _ euid  => decide (euid = Principal.root.toEUID)

/-- `rootSafe p`: the rule does not target `root`. -/
def policyRootSafe (p : Cedar.Spec.Policy) : Bool :=
  ! scopeMatchesRoot p.principalScope.scope

/-- `forbidOnly p`: the rule has effect `forbid`. -/
def policyForbidOnly (p : Cedar.Spec.Policy) : Bool :=
  decide (p.effect = .forbid)

/-- Install new policies from a `PolicyValue`. We only admit policies
    whose every rule (i) has effect `forbid` and (ii) does not target
    `root`. Append-only: new forbids are prepended. -/
def policyInstall (P : Policy) (pv : PolicyValue) : Option Policy :=
  match pv with
  | .mk s =>
    match parsePolicies s with
    | none => none
    | some ps =>
      if ps.all (fun p => policyForbidOnly p && policyRootSafe p) then
        some (ps ++ P)
      else
        none

/-- Iterated Cedar `unchanged_deny_when_add_forbid`: prepending any
    list of forbid-effect policies keeps a `deny` decision denied. -/
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
    exact Cedar.Thm.unchanged_deny_when_add_forbid req ent (rest ++ P) p hp hrestDeny

/-- Core shrink lemma: installing forbid policies only removes allows. -/
theorem policyInstall_shrinks
    (P P' : Policy) (pv : PolicyValue) :
    policyInstall P pv = some P' →
    policyAllowSet P' ⊆ policyAllowSet P := by
  intro hinst t ht
  rcases pv with ⟨s⟩
  simp [policyInstall] at hinst
  rcases hps : parsePolicies s with _ | ps
  · simp [hps] at hinst
  · simp [hps] at hinst
    rcases hinst with ⟨hguard, heq⟩
    subst heq
    simp [policyAllowSet, Set.mem_setOf_eq, policyAllows] at ht ⊢
    by_contra hne
    have hdeny :
        (Cedar.Spec.isAuthorized (requestOf t.1 t.2.1 t.2.2)
          ambientEntities P).decision = .deny := by
      cases hd :
          (Cedar.Spec.isAuthorized (requestOf t.1 t.2.1 t.2.2)
            ambientEntities P).decision with
      | allow => exact (hne hd).elim
      | deny  => rfl
    have hall : ∀ p ∈ ps, p.effect = .forbid := by
      intro p hp
      have := hguard p hp
      simp [policyForbidOnly] at this
      exact this.1
    have :=
      deny_preserved_by_forbid_prefix
        (requestOf t.1 t.2.1 t.2.2) ambientEntities ps P hall hdeny
    rw [ht] at this
    cases this

/-- The static admissibility premise is monotone under install:
    install only prepends rules, so the principal domain only grows. -/
theorem prinDeclared_preserved
    (P P' : Policy) (pv : PolicyValue) (π : Principal) :
    policyInstall P pv = some P' →
    prinDeclared P π → prinDeclared P' π := by
  intro hinst hπ
  rcases pv with ⟨s⟩
  simp [policyInstall] at hinst
  rcases hps : parsePolicies s with _ | ps
  · simp [hps] at hinst
  · simp [hps] at hinst
    rcases hinst with ⟨_, heq⟩
    subst heq
    rcases hπ with hroot | ⟨p, hp, hUID⟩
    · exact Or.inl hroot
    · refine Or.inr ⟨p, ?_, hUID⟩
      simp [hp]

end Pact
