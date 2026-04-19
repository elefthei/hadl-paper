-- Cedar-Lean wrapper: thin interface used by Reduction and Soundness.

import HADL.Syntax
import Mathlib.Data.Set.Basic

namespace HADL

/--
  Abstract policy state Π. Implementation detail:
  wraps Cedar-Lean's `Cedar.Spec.Policies × Cedar.Spec.Entities`.
  For the first pass we model it opaquely plus the lemmas we need.
-/
opaque PolicyNE : NonemptyType
def Policy : Type := PolicyNE.type
instance : Nonempty Policy := PolicyNE.property

inductive Action where
  | gen
  | agent
  | evalA
  deriving DecidableEq, Repr

/-- Authorization decision: does `P` allow principal `π` to perform action `a`? -/
opaque policyAllows : Policy → Principal → Action → Prop

/-- The "allow set" of `P`: pairs `(π, a)` such that `P` allows `π` on `a`. -/
def policyAllowSet (P : Policy) : Set (Principal × Action) :=
  { pa | policyAllows P pa.1 pa.2 }

/-- Installing a policy value produces a new policy, or fails if the
    install-time guards (deny-all, action-type validation, scoped principal,
    append-only) reject it. -/
opaque policyInstall : Policy → PolicyValue → Option Policy

/--
  Key Cedar-level lemma (axiomatized for now; see README).
  Any successful install only shrinks the allow set: no widening is possible.
-/
axiom policyInstall_shrinks
    (P P' : Policy) (pv : PolicyValue) :
    policyInstall P pv = some P' →
    policyAllowSet P' ⊆ policyAllowSet P

end HADL
