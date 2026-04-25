-- Runtime typing judgment `RtType : Value → Ty → Prop` (two-sort).
--
-- `vRec` and `vArr` are deliberately weak (picking trivial default
-- types): tightening them to carry per-field / per-element types would
-- make arbitrary heterogeneous arrays un-typeable, which breaks the
-- general `value_typeable` lemma used in T2. This matches the
-- single-sort predecessor's typing strength — the refactor is
-- feature-equivalent.

import HADL.Syntax

namespace HADL

/-- Runtime typing judgment `v : τ` on values. -/
inductive RtType : Value → Ty → Prop where
  | vUnit    : RtType .unitV .tUnit
  | vBool {b}: RtType (.boolV b) .tBool
  | vNum  {i}: RtType (.numV  i) .tNumber
  | vStr  {s}: RtType (.strV  s) .tString
  | vSchema {τ} : RtType (.schemaV τ) .tSchema
  | vPol    {p} : RtType (.polV p) .tPolicy
  /-- A closure of arity n has an arrow type. We black-box the body's
      type check here; soundness only needs the outer shape. -/
  | vClos {n body args ret} :
      args.length = n →
      RtType (.clos n body) (.tArrow args ret)
  /-- Record values have *some* record type.  Soundness only needs the
      existence of a runtime type, not a precise field-wise match. -/
  | vRec {xs} : RtType (.recV xs) (.tRecord [])
  /-- Array values have *some* array type, similarly black-boxed. -/
  | vArr {vs} : RtType (.arrV vs) (.tArray .tUnit)

/-! ### Healable types.

    A type is healable iff `gen` can produce it as a first-class value
    that the runtime re-checks (Schema, Policy, Arrow) — or is a
    Record/Array containing a healable component (any nested
    materialization site still requires self-healing).

    Base scalar types (Unit, Bool, Number, String) are NOT healable;
    let-redexes at these types use the uniform success / type-error
    rules instead.

    `Ty.healable` is the only predicate. There is no `simple` shorthand;
    rules and proofs spell out `¬ Ty.healable τ` directly. -/

/-- Healable types: the materialization targets that admit a self-heal
    retry loop in the let-redex reduction rules. Defined by
    well-founded recursion on `sizeOf`; the `tRecord` case scans the
    field list and recurses on each field's type, each of which is
    structurally smaller. -/
def Ty.healable : Ty → Bool
  | .tSchema      => true
  | .tPolicy      => true
  | .tArrow _ _   => true
  | .tRecord fs   =>
      fs.attach.any (fun kv => Ty.healable kv.val.2)
  | .tArray τ'    => Ty.healable τ'
  | .tUnit        => false
  | .tBool        => false
  | .tNumber      => false
  | .tString      => false
decreasing_by
  all_goals first
    | (simp_wf
       have h := List.sizeOf_lt_of_mem kv.property
       have h2 : sizeOf kv.val.snd < sizeOf kv.val := by
         rcases kv with ⟨⟨a, b⟩, _⟩; simp; omega
       omega)
    | simp_wf
    | (simp_wf; omega)

/-- Static typeability of expressions under a single-variable context.
    `StaticTypeOK τbind p τret` witnesses that `p` type-checks at `τret`
    when de-Bruijn `var 0` is bound at `τbind`. Black-boxed like
    `StType` above: only the cases Soundness/Safety need are exposed.
    Used as the continuation-check premise in the healable-τ self-heal
    rules (Schema today; Policy/Arrow in Phases 2/3), per the
    continuation-driven healing rule in `hadl-formal.md`. -/
inductive StaticTypeOK : Ty → Expr → Ty → Prop where
  /-- `var 0` has the type it was bound at — the witness needed for
      `T4_truthful_success` on `let _ : τ = gen τ s π ; var 0`. -/
  | var0 {τ} : StaticTypeOK τ (.var 0) τ
  /-- Any expression is typeable at Schema by the residual static-type
      black-box; parallels `StType.schemaWildcard`. -/
  | schemaWildcard {τbind e} : StaticTypeOK τbind e .tSchema
  /-- Any value expression is typeable at any type; parallels
      `StType.valueWildcard`. -/
  | valueWildcard {τbind v τ} : StaticTypeOK τbind (.val v) τ

/-- Static typing over closed expressions. Black-boxed: the paper
    re-runs the structural checker and Lean treats acceptance as an
    opaque relation. We expose only the cases Soundness needs. -/
inductive StType : Expr → Ty → Prop where
  | schemaWildcard {e} : StType e .tSchema
  | valueWildcard  {v τ} : StType (.val v) τ
  | varDecl {x τ e1 e2 τ2} :
      StType e1 τ → StType e2 τ2 → StType (.varDecl x τ e1 e2) τ2
  | assign {x e τ} : StType e τ → StType (.assign x e) .tUnit
  | varRead {x τ} : StType (.varRead x) τ

/-- Store well-formedness: every cell's value has its declared type. -/
def Store.WF (σ : Store) : Prop :=
  ∀ x τ v, σ x = some (τ, v) → RtType v τ

theorem Store.empty_WF : Store.empty.WF := by
  intro _ _ _ h; simp [Store.empty] at h

theorem Store.set_WF {σ : Store} {x τ v}
    (hσ : σ.WF) (hv : RtType v τ) : (σ.set x τ v).WF := by
  intro y τ' v' h
  unfold Store.set at h
  by_cases hy : y = x
  · simp [hy] at h; rcases h with ⟨rfl, rfl⟩; exact hv
  · simp [hy] at h; exact hσ y τ' v' h

/-! ### Store read/write algebra.

    These lemmas let future mutable-state proofs reason about
    reads-after-writes (`get_set_eq` / `get_set_ne`) and
    independent-cell commutativity (`set_set_eq` / `set_set_ne`).
    `set_set_eq` / `set_set_ne` are NOT `@[simp]` because they could
    loop on repeated writes to the same (or swapped) cells. -/

@[simp]
theorem Store.get_set_eq (σ : Store) (x : String) (τ : Ty) (v : Value) :
    (σ.set x τ v) x = some (τ, v) := by
  simp [Store.set]

@[simp]
theorem Store.get_set_ne {σ : Store} {x y : String} (τ : Ty) (v : Value)
    (h : y ≠ x) : (σ.set x τ v) y = σ y := by
  simp [Store.set, h]

theorem Store.set_set_eq (σ : Store) (x : String) (τ₁ τ₂ : Ty) (v₁ v₂ : Value) :
    (σ.set x τ₁ v₁).set x τ₂ v₂ = σ.set x τ₂ v₂ := by
  funext y
  by_cases hy : y = x
  · simp [Store.set, hy]
  · simp [Store.set, hy]

theorem Store.set_set_ne {σ : Store} {x y : String} (τ₁ τ₂ : Ty) (v₁ v₂ : Value)
    (h : x ≠ y) :
    (σ.set x τ₁ v₁).set y τ₂ v₂ = (σ.set y τ₂ v₂).set x τ₁ v₁ := by
  funext z
  by_cases hzx : z = x
  · subst hzx
    have hzy : z ≠ y := h
    simp [Store.set, hzy]
  · by_cases hzy : z = y
    · subst hzy
      simp [Store.set, hzx]
    · simp [Store.set, hzx, hzy]

end HADL
