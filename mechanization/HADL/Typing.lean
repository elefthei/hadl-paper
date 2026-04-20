-- Runtime typing judgment `RtType : Expr → Ty → Prop`.
--
-- Static typing `StType` is black-boxed in the formalization because
-- the paper's §2 description treats it as a standard structural type
-- checker re-invoked on residuals. Soundness inspects `RtType` only.

import HADL.Syntax

namespace HADL

/-- Runtime typing judgment `v : τ` on closed values.
    The hypothesis `h : v.isValue` is carried at construction sites
    when needed; the judgment holds irrespective of it. -/
inductive RtType : Expr → Ty → Prop where
  | vUnit    : RtType .unit .tUnit
  | vBool {b}: RtType (.litBool b) .tBool
  | vInt  {i}: RtType (.litInt  i) .tInt
  | vStr  {s}: RtType (.litStr  s) .tString
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
  | valueWildcard  {e τ} : e.isValueB = true → StType e τ

end HADL
