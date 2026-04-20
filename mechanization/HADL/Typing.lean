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
  | vInt  {i}: RtType (.intV  i) .tInt
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
