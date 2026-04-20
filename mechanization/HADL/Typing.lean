-- Static and runtime typing judgments.

import HADL.Syntax
import HADL.Env

namespace HADL

abbrev StCtx := List (Name × Ty)

/-- Static typing judgment `Γ ⊢ e : τ`. Relational; decidability not required. -/
inductive StType : StCtx → Expr → Ty → Prop where
  | var {Γ x τ} :
      (x, τ) ∈ Γ → StType Γ (.var x) τ
  | unit {Γ} : StType Γ .unit .tUnit
  | lbool {Γ b} : StType Γ (.litBool b) .tBool
  | lint  {Γ i} : StType Γ (.litInt  i) .tInt
  | lstr  {Γ s} : StType Γ (.litStr  s) .tString
  -- The residual program-level typing rules are elided here;
  -- we add only the cases the soundness proof inspects.
  | schemaWildcard {Γ e} :
      -- Any expression synthesized against a Schema binding is accepted
      -- at Schema; it will be re-checked at materialization time.
      StType Γ e .tSchema
  | valueWildcard {Γ v τ} :
      -- A lifted `valE` typechecks at any τ at the stage level; its
      -- runtime typing is the binding clause checked separately by
      -- `RtType`.
      StType Γ (.valE v) τ

/-- Runtime typing judgment `ρ ⊨ v : τ`. -/
inductive RtType : Env → Value → Ty → Prop where
  | vUnit {ρ} : RtType ρ .vUnit .tUnit
  | vBool {ρ b} : RtType ρ (.vBool b) .tBool
  | vInt  {ρ i} : RtType ρ (.vInt  i) .tInt
  | vStr  {ρ s} : RtType ρ (.vStr  s) .tString
  | vSchema {ρ τ} : RtType ρ (.vSchema τ) .tSchema
  | vPol {ρ p} : RtType ρ (.vPol p) .tPolicy
  /-- Resolution through ρ: if the type name `y` is bound to a schema value
      `vSchema τ'`, then runtime typing against `tVar y` unfolds to τ'. -/
  | tVarResolve {ρ y τ' v} :
      (Env.lookup ρ y) = some ⟨.vSchema τ', .tSchema, .letBind⟩ →
      RtType ρ v τ' →
      RtType ρ v (.tVar y)

end HADL
