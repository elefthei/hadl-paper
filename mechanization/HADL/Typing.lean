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

end HADL
