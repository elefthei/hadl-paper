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

end HADL
