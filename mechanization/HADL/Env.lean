-- Typed environment ρ: x ↦ (v, τ, mut).
-- Represented as a list for simplicity; first match wins on lookup.

import HADL.Syntax

namespace HADL

structure Binding where
  value : Value
  ty    : Ty
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
    the old binding's static type and mutability. If `x` has no
    prior binding we shadow with the ambient defaults from `b`. -/
def assign (ρ : Env) (x : Name) (v : Value) (fallback : Binding) : Env :=
  match ρ.lookup x with
  | some b => Env.extend ρ x { b with value := v }
  | none   => Env.extend ρ x { fallback with value := v }

def dom (ρ : Env) : List Name := ρ.map (·.1)

def fresh (ρ : Env) (x : Name) : Prop := x ∉ ρ.dom

/-- Batched extend: extends ρ with every pair in `xs` from left to right. -/
def extendAll (ρ : Env) : List (Name × Binding) → Env
  | []            => ρ
  | (x, b) :: xs  => extendAll (Env.extend ρ x b) xs

/-- Pairwise-fresh batch: each name in `xs` is fresh in the env extended
    by the previous entries. -/
def freshAll (ρ : Env) : List (Name × Binding) → Prop
  | []            => True
  | (x, b) :: xs  => Env.fresh ρ x ∧ freshAll (Env.extend ρ x b) xs

notation ρ " ⊕ " "[" x " ↦ " b "]" => Env.extend ρ x b

/--
  Static projection Γ(ρ): keep only the static type of each binding.
  Matches `\Projenv{\MEnv}` in the paper.
-/
def proj (ρ : Env) : List (Name × Ty) :=
  ρ.map (fun p => (p.1, p.2.ty))

end Env

end HADL
