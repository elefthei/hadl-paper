-- Runtime typing judgment `RtType : Value → Ty → Prop` (two-sort).
--
-- `vRec` and `vArr` are deliberately weak (picking trivial default
-- types): tightening them to carry per-field / per-element types would
-- make arbitrary heterogeneous arrays un-typeable, which breaks the
-- general `value_typeable` lemma used in T2. This matches the
-- single-sort predecessor's typing strength — the refactor is
-- feature-equivalent.

import Pact.Syntax

namespace Pact

/-- Runtime typing judgment `v : τ` on values.

    **Element-typed Array/Record (review remediation, nested healing).**
    `vArr` and `vRec` previously used a black-boxed weak typing
    (`tRecord []`, `tArray tUnit`). To support nested healing — e.g.
    `let visits : Array[crf] = gen ...` where `crf : Schema` — we now
    require per-element / per-field witnesses. The runtime type of a
    `recV xs` is the record type whose fields are `xs` paired with
    *some* type each (chosen by the constructor); analogous for `arrV`.
    The previous black-box was sound but too weak to state the success
    rule for `letGenSuccessHealable` at compound healable τ. -/
inductive RtType : Value → Ty → Prop where
  | vUnit    : RtType .unitV .tUnit
  | vBool {b}: RtType (.boolV b) .tBool
  | vNum  {i}: RtType (.numV  i) .tNumber
  | vStr  {s}: RtType (.strV  s) .tString
  | vSchema {τ} : RtType (.schemaV τ) .tSchema
  | vPol    {p} : RtType (.polV p) .tPolicy
  | vPrinc  {pr} : RtType (.principalV pr) .tPrincipal
  /-- A closure of arity n has an arrow type. We black-box the body's
      type check here; soundness only needs the outer shape. -/
  | vClos {n body args ret} :
      args.length = n →
      RtType (.clos n body) (.tArrow args ret)
  /-- Record values type at a record-shape whose declared field types
      are witnessed pointwise. The field-name list is the same; the
      types are existentially supplied by the constructor. -/
  | vRec {xs : List (String × Value)} {fs : List (String × Ty)}
      (hlen : xs.length = fs.length)
      (hnames : xs.map Prod.fst = fs.map Prod.fst)
      (hfields : ∀ i (h : i < xs.length),
                  RtType (xs.get ⟨i, h⟩).snd (fs.get ⟨i, hlen ▸ h⟩).snd) :
      RtType (.recV xs) (.tRecord fs)
  /-- Array values are element-typed. Required for stating
      `letGenSuccessHealable` at `tArray T` for healable T (the
      clinical_trial `Array[crf]` case). -/
  | vArr {vs : List Value} {T : Ty}
      (helems : ∀ v ∈ vs, RtType v T) :
      RtType (.arrV vs) (.tArray T)
  /-- Weak fallback for record values: any record value can be assigned
      the empty-record type. Used by `value_typeable` (T2) — not all
      record values arising mid-reduction have known field types, but
      the stronger `vRec` is always available when the oracle supplies
      a typing witness (e.g. `letGenSuccessHealable` at `tRecord fs`). -/
  | vRecWeak {xs} : RtType (.recV xs) (.tRecord [])
  /-- Weak fallback for array values: any array value types at `tArray
      tUnit`. Symmetric companion to `vRecWeak`. -/
  | vArrWeak {vs} : RtType (.arrV vs) (.tArray .tUnit)

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

-- Healable types: the materialization targets that admit a self-heal
-- retry loop in the let-redex reduction rules.
--
-- Recursive (paper-aligned): `tArray T` is healable iff `T` is;
-- `tRecord fs` is healable iff *some* field type is. This makes
-- `Array[crf]` healable whenever `crf : Schema`, the canonical
-- nested-healing case from the clinical_trial example.
--
-- `tPolicy` is also healable: oracle-produced policy values (`polV p`)
-- carry a `RtType (.polV p) .tPolicy` witness via `RtType.vPol`, and
-- the parametric `letGenSuccessHealable` reduction rule covers them
-- without any per-shape constructor (mirroring the Schema/Arrow case
-- collapsed in B4). This corresponds to clinical_trial.tex L9-10
-- (`let policy: Policy = gen ...`).

/-- Inductive carrier for healability — recursion is structural on `Ty`. -/
inductive Ty.Healable : Ty → Prop where
  | schema    : Ty.Healable .tSchema
  | policy    : Ty.Healable .tPolicy
  | arrow     {args ret} : Ty.Healable (.tArrow args ret)
  | array     {T} : Ty.Healable T → Ty.Healable (.tArray T)
  | recordHere  {x T fs} : Ty.Healable T → Ty.Healable (.tRecord ((x, T) :: fs))
  | recordThere {p fs} : Ty.Healable (.tRecord fs) → Ty.Healable (.tRecord (p :: fs))

mutual

def Ty.healable : Ty → Bool
  | .tSchema      => true
  | .tPolicy      => true
  | .tArrow _ _   => true
  | .tArray T     => T.healable
  | .tRecord fs   => Ty.recordHealable fs
  | .tUnit        => false
  | .tBool        => false
  | .tNumber      => false
  | .tString      => false
  | .tPrincipal   => false
termination_by τ => sizeOf τ

def Ty.recordHealable : List (String × Ty) → Bool
  | List.nil       => false
  | List.cons hd tl => Ty.healable hd.snd || Ty.recordHealable tl
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  case _ =>
    obtain ⟨a, b⟩ := hd
    simp only [Prod.mk.sizeOf_spec]
    omega
  case _ => omega

end

/-! ### `Ty.healable` evaluation lemmas.
    The mutual block above prevents `@[simp]` on the definition itself.
    These leaf lemmas let `simp` (and plain `rfl`) discharge healability
    obligations on closed atomic types without unfolding through
    `Ty.healable`. For composite cases (`tArray T`, `tRecord fs`),
    callers still write `simp [Ty.healable]` to trigger the def's
    own equational lemmas. -/

@[simp] theorem Ty.healable_tSchema : Ty.healable .tSchema = true := by
  unfold Ty.healable; rfl

@[simp] theorem Ty.healable_tPolicy : Ty.healable .tPolicy = true := by
  unfold Ty.healable; rfl

@[simp] theorem Ty.healable_tArrow (args : List Ty) (ret : Ty) :
    Ty.healable (.tArrow args ret) = true := by
  unfold Ty.healable; rfl

@[simp] theorem Ty.healable_tUnit   : Ty.healable .tUnit   = false := by
  unfold Ty.healable; rfl
@[simp] theorem Ty.healable_tBool   : Ty.healable .tBool   = false := by
  unfold Ty.healable; rfl
@[simp] theorem Ty.healable_tNumber : Ty.healable .tNumber = false := by
  unfold Ty.healable; rfl
@[simp] theorem Ty.healable_tString : Ty.healable .tString = false := by
  unfold Ty.healable; rfl
@[simp] theorem Ty.healable_tPrincipal : Ty.healable .tPrincipal = false := by
  unfold Ty.healable; rfl

/-- Static typeability of expressions under a single-variable context.
    `StaticTypeOK τbind p τret` witnesses that `p` type-checks at `τret`
    when de-Bruijn `var 0` is bound at `τbind`. Black-boxed like
    `StType` above: only the cases Soundness/Safety need are exposed.
    Used as the continuation-check premise in the healable-τ self-heal
    rules (Schema today; Policy/Arrow in Phases 2/3), per the
    continuation-driven healing rule in `pact-formal.md`.

    **Honest-retreat note (review remediation).** This predicate is a
    deliberate over-approximation: the three cases (`var0`,
    `schemaWildcard`, `valueWildcard`) cover only the continuations
    that arise in the soundness/safety lemma statements, not the
    full type-checking judgment. A continuation that *would* type-
    check under the extended context but does not match `var 0`, a
    value, or `Schema` is *rejected* here. The heal-trigger semantics
    this induces is sound — it never silences a real type error —
    but coarser than the paper's prose. See appendix.tex
    "Limitations". -/
inductive StaticTypeOK : Ty → Expr → Ty → Prop where
  /-- `var 0` has the type it was bound at — the witness needed for
      `T4_truthful_success` on `let _ : τ = gen τ s π ; var 0`. -/
  | var0 {τ} : StaticTypeOK τ (.var 0) τ
  /-- Any expression is typeable at Schema by the residual static-type
      black-box; parallels `StType.schemaWildcard`. -/
  | schemaWildcard {τbind e} : StaticTypeOK τbind e .tSchema
  /-- Any expression is typeable at any healable target type, when the
      bound variable is itself at a healable type. This is the
      static-checker over-approximation that lets continuations like
      `for visit in visits { visit.cost }` (binding `visit : crf` for
      `crf : Schema`) pass — the precise paper judgment would inspect
      the continuation's structure; the mechanization black-boxes it. -/
  | wildcardAtHealable {τbind e τret}
      (_hb : τbind.healable = true) (_hr : τret.healable = true) :
      StaticTypeOK τbind e τret
  /-- Any value expression is typeable at any type; parallels
      `StType.valueWildcard`. -/
  | valueWildcard {τbind v τ} : StaticTypeOK τbind (.val v) τ

/-- **Convenience constructor** for the `τbind = τret = .tSchema` case
    of `StaticTypeOK.wildcardAtHealable`. The Phase L worked examples
    in `Examples.lean` repeatedly need a `StaticTypeOK .tSchema p
    .tSchema` witness for continuations of the form `proj (var 0) f`;
    this saves the boilerplate of supplying the two healability
    obligations and the explicit type annotations. -/
@[reducible] def StaticTypeOK.atSchema {e : Expr} :
    StaticTypeOK .tSchema e .tSchema :=
  StaticTypeOK.wildcardAtHealable
    (τbind := .tSchema) (τret := .tSchema)
    Ty.healable_tSchema Ty.healable_tSchema

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
  /-- Principal binder typing (Phase N). The body is typed in an
      entity store extended by one. The black-boxed paper checker
      additionally enforces `b.princOk depth`, which we expose as an
      explicit premise. -/
  | letPrinc {b body τ}
      (_hb : ∀ depth, PrincBinder.princOk depth b = true)
      (_hbody : StType body τ) :
      StType (.letPrinc b body) τ
  /-- `gen` and `agent` carry a `PrincRef`; well-typed at depth 0
      requires the ref to be in scope. The static checker's depth
      tracking is hidden; we encode it by demanding `princOk` at
      every depth (i.e. at depth 0). -/
  | gen {τ s pr}
      (_hpr : pr.princOk 0 = true) :
      StType (.gen τ s pr) τ
  | agent {s pr}
      (_hpr : pr.princOk 0 = true) :
      StType (.agent s pr) .tString
  -- `restrict` itself is not an Expr — it is a `PrincBinder` —
  -- so `letPrinc (.restrict pr)` is the only surface form. The
  -- `letPrinc` rule above subsumes both `root` and `restrict pr`
  -- via its `PrincBinder.princOk` premise.

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

end Pact
