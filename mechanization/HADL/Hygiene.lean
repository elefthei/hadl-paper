-- Hygiene: predicates capturing "no reserved name (Extract.freshPrefix)
-- appears where RtType looks". Just enough to discharge the two sorries in
-- `Safety2.T4_gStep_progress_gen`.
--
-- We do NOT define general Expr/Value hygiene — the RtType weakening proof
-- only inspects types (specifically the `tVar` case) and schema payloads in
-- the environment, so those are the only places the hygiene predicate needs
-- to reach.

import HADL.Syntax
import HADL.Env
import HADL.Typing
import HADL.Extract

namespace HADL

/-! ### Reserved-name predicate -/

/-- A `Name` is *reserved* if it begins with the `Extract.freshPrefix`
    (`"__ex_"`). Source programs must not use such names. -/
def Name.isReserved (n : Name) : Bool := n.startsWith Extract.freshPrefix

/-- Propositional form of `Name.isReserved`. -/
def Name.IsRes (n : Name) : Prop := Eq (Name.isReserved n) true

theorem Extract.freshGen_reserved : Name.IsRes Extract.freshGen := by
  unfold Name.IsRes Name.isReserved Extract.freshGen
  native_decide

theorem Extract.freshAgent_reserved : Name.IsRes Extract.freshAgent := by
  unfold Name.IsRes Name.isReserved Extract.freshAgent
  native_decide

/-! ### Ty hygiene

    Only `tVar` matters for `RtType`. For all other constructors we return
    `True` — they cannot trigger `tVarResolve`. This is intentionally shallow
    and is sound for our proof of runtime-type weakening. -/

def Ty.hygienic : Ty → Prop
  | .tVar y => ¬ Name.IsRes y
  | _       => True

/-! ### Env hygiene -/

/-- `Env.Hygienic ρ`: every schema-typed binding's payload is itself
    `Ty.hygienic`. This is the only property `RtType` recursion needs;
    freshness of reserved names is a separate, per-lookup property. -/
def Env.Hygienic (ρ : Env) : Prop :=
  ∀ {y τ'},
    Env.lookup ρ y
      = some ⟨Value.vSchema τ', Ty.tSchema, Mutability.letBind⟩ →
    τ'.hygienic

namespace Env

/-- Lookup on an extended env: if `x = y` returns the new binding, otherwise
    falls back to the underlying env's lookup. -/
theorem lookup_extend (ρ : Env) (x y : Name) (b : Binding) :
    (Env.extend ρ x b).lookup y =
      (if x = y then some b else ρ.lookup y) := by
  unfold Env.extend Env.lookup
  simp [List.find?]
  by_cases h : x = y <;> simp [h]

/-- Extending with a non-schema binding preserves schema-hygiene. The
    common case: `T4_truthful_success` returns a non-schema value. -/
theorem Hygienic.extend_nonschema
    {ρ : Env} {x : Name} {b : Binding}
    (hρ : ρ.Hygienic)
    (hb : b.ty ≠ .tSchema) :
    (Env.extend ρ x b).Hygienic := by
  intro y τ' hlk
  rw [lookup_extend] at hlk
  by_cases hxy : x = y
  · rw [if_pos hxy] at hlk
    have : b = ⟨Value.vSchema τ', .tSchema, .letBind⟩ :=
      Option.some.inj hlk
    exact absurd (congrArg Binding.ty this) hb
  · rw [if_neg hxy] at hlk
    exact hρ hlk

/-- Extending with a hygienic schema binding preserves schema-hygiene. -/
theorem Hygienic.extend_schema
    {ρ : Env} {x : Name} {τ'' : Ty}
    (hρ  : ρ.Hygienic) (hτ'' : τ''.hygienic) :
    (Env.extend ρ x ⟨Value.vSchema τ'', .tSchema, .letBind⟩).Hygienic := by
  intro y τ' hlk
  rw [lookup_extend] at hlk
  by_cases hxy : x = y
  · rw [if_pos hxy] at hlk
    have heq : (⟨Value.vSchema τ'', .tSchema, .letBind⟩ : Binding) =
               ⟨Value.vSchema τ', .tSchema, .letBind⟩ :=
      Option.some.inj hlk
    have hvv : Value.vSchema τ'' = Value.vSchema τ' :=
      congrArg Binding.value heq
    cases hvv
    exact hτ''
  · rw [if_neg hxy] at hlk
    exact hρ hlk

end Env

/-! ### RtType weakening

    Termwise (not tactic-mode) to avoid issues binding implicit arguments
    of `tVarResolve` from the `induction` tactic. -/

theorem RtType.weaken_extend_reserved
    {ρ : Env} {v : Value} {τ : Ty}
    (h : RtType ρ v τ)
    (hτ : τ.hygienic) (hρ : ρ.Hygienic)
    {x : Name} {b : Binding} (hx : Name.IsRes x) :
    RtType (Env.extend ρ x b) v τ := by
  induction h with
  | vUnit   => exact .vUnit
  | vBool   => exact .vBool
  | vInt    => exact .vInt
  | vStr    => exact .vStr
  | vSchema => exact .vSchema
  | vPol    => exact .vPol
  | @tVarResolve y τ' v hlk _hrt ih =>
      have hy_nr : ¬ Name.IsRes y := hτ
      have hxy : x ≠ y := fun heq => hy_nr (heq ▸ hx)
      have hlk' :
          Env.lookup (Env.extend ρ x b) y =
            some ⟨.vSchema τ', .tSchema, .letBind⟩ := by
        rw [Env.lookup_extend, if_neg hxy]; exact hlk
      have hτ' : τ'.hygienic := hρ hlk
      exact RtType.tVarResolve hlk' (ih hτ')

end HADL
