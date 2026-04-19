-- Typed environment ρ: x ↦ (v, τ, prov, mut).
-- Represented as a list for simplicity; first match wins on lookup.

import HADL.Syntax

namespace HADL

structure Binding where
  value : Value
  ty    : Ty
  prov  : Option Label
  mode  : Mutability

abbrev Env := List (Name × Binding)

namespace Env

def empty : Env := []

def lookup (ρ : Env) (x : Name) : Option Binding :=
  match ρ.find? (fun p => p.1 = x) with
  | some (_, b) => some b
  | none        => none

def extend (ρ : Env) (x : Name) (b : Binding) : Env := (x, b) :: ρ

/-- Shadow-assign: push a new cell for `x` with an updated value, preserving
    the old binding's static type, provenance, and mutability. If `x` has no
    prior binding we shadow with the ambient defaults from `b`. -/
def assign (ρ : Env) (x : Name) (v : Value) (fallback : Binding) : Env :=
  match ρ.lookup x with
  | some b => Env.extend ρ x { b with value := v }
  | none   => Env.extend ρ x { fallback with value := v }

def dom (ρ : Env) : List Name := ρ.map (·.1)

def fresh (ρ : Env) (x : Name) : Prop := x ∉ ρ.dom

notation ρ " ⊕ " "[" x " ↦ " b "]" => Env.extend ρ x b

/--
  Static projection Γ(ρ): keep only the static type of each binding.
  Matches `\Projenv{\MEnv}` in the paper.
-/
def proj (ρ : Env) : List (Name × Ty) :=
  ρ.map (fun p => (p.1, p.2.ty))

end Env

end HADL
