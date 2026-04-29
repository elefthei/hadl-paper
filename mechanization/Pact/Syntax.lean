-- Syntax of Pact: types, values, de-Bruijn expressions.
-- Two-sort presentation: `Value` is its own inductive; `Expr.val`
-- embeds values into expressions.
--
-- Substitution and renaming on `Expr` are provided via the `lean-subst`
-- library. `Value` has its own renaming/substitution helpers defined
-- mutually with `Expr` (needed because `Value.clos` contains an `Expr`
-- body with binders); we do not register a `RenMap Value` instance
-- because closures are the only binder-introducing value constructor
-- and renaming flows naturally through the mutual definition.

import LeanSubst

open LeanSubst

namespace Pact

/-- A principal: a meta-level newtype around a `Nat` tag. This struct
    is **not** an `Expr`-level value (there is no `Value.principalV`);
    it is used only by `Step` rules' existential principals and by
    Cedar's request encoding. The actual principal in scope at a `gen`
    site is determined by the typing derivation's entity store `E`,
    not by any AST node. -/
@[ext] structure Principal where
  id : Nat
deriving DecidableEq, Inhabited, Repr

/-- The unrestricted built-in principal. -/
def Principal.root : Principal := ⟨0⟩

/-- Create a fresh principal from a tag. -/
def Principal.restrict (tag : Nat) : Principal := ⟨tag⟩

/-- String encoding for Cedar entity ids. -/
def Principal.toString (p : Principal) : String := ToString.toString p.id

/-- Syntactic principal slot for `gen`/`agent`. A `PrincRef` is a de
    Bruijn index into the **entity store `E`** (a separate scope from
    regular Expr identifiers). By convention, `bvar 0` in the empty
    program refers to `root`; each `letPrinc b body` introduces a new
    principal at index 0 of the body's entity scope, shifting existing
    principals up by one. -/
inductive PrincRef where
  /-- De Bruijn reference into the entity store `E`. -/
  | bvar : Nat → PrincRef
  deriving Inhabited, Repr

/-- Renaming on `PrincRef`. Principals live in their own de Bruijn
    scope, independent of the regular Expr identifier scope, so
    `Expr` renamings do **not** touch PrincRef indices. -/
def PrincRef.rmap (_ : Ren) : PrincRef → PrincRef
  | .bvar n => .bvar n

/-- Right-hand side of a principal binder `letPrinc`. Introduces either
    the built-in `root` principal (only legal at the top of a program;
    typing rejects nested `letPrinc root` against a non-empty E) or a
    fresh restriction `p <: parent`. -/
inductive PrincBinder where
  | root     : PrincBinder
  | restrict : PrincRef → PrincBinder
  deriving Inhabited, Repr

/-- Renaming on a principal binder: only the parent PrincRef may
    contain a bvar, but PrincRef.rmap is the identity under regular
    Expr renaming, so this is the identity too. -/
def PrincBinder.rmap (_ : Ren) : PrincBinder → PrincBinder
  | .root        => .root
  | .restrict pr => .restrict pr

/-- Types. No `tVar`: Schema materialization is handled at runtime
    via the oracle's truthfulness + `RtType`. -/
inductive Ty where
  | tUnit   : Ty
  | tBool   : Ty
  | tNumber    : Ty
  | tString : Ty
  | tSchema : Ty
  | tPolicy : Ty
  | tPrincipal : Ty
  | tArrow  : List Ty → Ty → Ty
  | tRecord : List (String × Ty) → Ty
  | tArray  : Ty → Ty
  deriving Inhabited

/-- Feedback event. -/
inductive Event
  | error   : String → Event
  | success : Event
  deriving Inhabited, Repr

/-- Opaque JavaScript expression. -/
opaque JsExprNE : NonemptyType
def JsExpr : Type := JsExprNE.type
instance : Nonempty JsExpr := JsExprNE.property

/-- Opaque Cedar policy value. -/
inductive PolicyValue where
  | mk : String → PolicyValue

-- Two-sort syntax: `Value` is the subset traditionally called values,
-- `Expr` is expressions with `.val : Value → Expr` as the embedding.
mutual
inductive Value where
  /-- Unit value (singleton inhabitant of `tUnit`). -/
  | unitV   : Value
  /-- Boolean literal. -/
  | boolV   : Bool → Value
  /-- Integer literal. -/
  | numV    : Int → Value
  /-- String literal. -/
  | strV    : String → Value
  /-- First-class type (reified schema). -/
  | schemaV : Ty → Value
  /-- First-class policy value. -/
  | polV    : PolicyValue → Value
  /-- First-class principal value: a frozen `PrincRef` pointing into
      the entity store at the point of capture. Introduced when a
      principal binder is materialized for use as a `gen`/`agent`
      argument; carries no data beyond the resolved index. -/
  | principalV : PrincRef → Value
  /-- Record value: list of (field-name, value) pairs. -/
  | recV    : List (String × Value) → Value
  /-- Array value: homogeneous(ish) list of values. -/
  | arrV    : List Value → Value
  /-- Closure with `n` de-Bruijn-bound parameters and expression body. -/
  | clos    : Nat → Expr → Value
  /-- Hard-error sink value. Produced only by the uniform let-redex
      error rules (`letGenTypeError`, `letGenBudgetError`). It has NO
      runtime type — `RtType errV τ` is false for every τ — so a
      configuration whose expression is `.val errV` is a terminal
      failure state, not a typeable value. T2 is therefore weakened to
      `v ≠ errV → ∃ τ, RtType v τ`. -/
  | errV    : Value

inductive Expr where
  /-- Embedded value (the `Value ↪ Expr` injection). -/
  | val     : Value → Expr
  /-- De-Bruijn variable reference. -/
  | var     : Nat → Expr
  /-- Let-binding `let _ : τ = e1 in e2` (CBV, substitution-based). -/
  | letE    : Ty → Expr → Expr → Expr
  /-- Conditional. -/
  | ifE     : Expr → Expr → Expr → Expr
  /-- While-loop. -/
  | whileE  : Expr → Expr → Expr
  /-- For-each: iterate `e2` (with one free var) over the array-valued `e1`. -/
  | forE    : Expr → Expr → Expr
  /-- Sequencing. -/
  | seq     : Expr → Expr → Expr
  /-- Oracle `ask`. -/
  | ask     : String → Expr
  /-- Oracle `say`. -/
  | say     : String → Expr
  /-- Principal binder `let p : Principal = b ; body`. The binder `b`
      is either `root` (introducing the built-in principal) or
      `restrict pr` (introducing a sub-principal of `pr`). The body is
      evaluated in an entity store extended with `b` at index 0. This
      is **not** a `letE` form because principals are not Expr-level
      values; they exist only in the entity store `E`, which is
      threaded through typing derivations. -/
  | letPrinc : PrincBinder → Expr → Expr
  /-- Oracle `gen` action. The third argument is a `PrincRef` (a de
      Bruijn index into the entity store `E`): `bvar 0` is the most
      recent binder, `bvar 1` is the next, and so on. -/
  | gen     : Ty → String → PrincRef → Expr
  /-- Oracle `agent` action. The principal slot is a `PrincRef`. -/
  | agent   : String → PrincRef → Expr
  /-- Closure application. -/
  | evalE   : Expr → List Expr → Expr
  /-- Policy installation (`e` evaluates to a `polV`). -/
  | enforce : Expr → Expr
  /-- Embedded JS expression (opaque, see JsAxioms). -/
  | js      : JsExpr → Expr
  /-- Mutable variable declaration: `var x : τ := e1 ; e2`. -/
  | varDecl : String → Ty → Expr → Expr → Expr
  /-- Mutable-variable assignment. -/
  | assign  : String → Expr → Expr
  /-- Mutable-variable read. -/
  | varRead : String → Expr
  /-- Record field projection (`e.f`). The paper's self-heal trigger
      (clinical_trial L17 `visit.cost`, L18 `visit.patient_id`):
      stuck when the field is absent — that stuck state is the
      runtime-error condition the paper retreats from. -/
  | proj    : Expr → String → Expr
end

/-- Value predicate for expressions: `true` iff the expression is a
    `val` wrapper around a `Value`. -/
def Expr.isValueB : Expr → Bool
  | .val _ => true
  | _      => false

abbrev Expr.isValue (e : Expr) : Prop := e.isValueB = true

/-! ## lean-subst setup for `Expr`. -/

@[coe]
def Expr.from_action : Subst.Action Expr → Expr
  | .re y => .var y
  | .su t => t

@[simp, grind =]
theorem Expr.from_action_id {n} : from_action (+0 n) = .var n := by
  simp [from_action, Subst.id]

@[simp, grind =]
theorem Expr.from_action_succ {n} : from_action (+1 n) = .var (n + 1) := by
  simp [from_action, Subst.succ]

@[simp, grind =]
theorem Expr.from_action_re {n} : from_action (.re n) = .var n := by
  simp [from_action]

@[simp, grind =]
theorem Expr.from_action_su {t} : from_action (.su t) = t := by
  simp [from_action]

instance : Coe (Subst.Action Expr) Expr where
  coe := Expr.from_action

/-- Lift a renaming through `n` binders. -/
def Ren.liftN (r : Ren) : Nat → Ren
  | 0     => r
  | n + 1 => (Ren.liftN r n).lift

/-! ### Renaming on `Value` and `Expr`.

    Defined as a single mutual recursion because closures
    `Value.clos n body` contain an `Expr` subterm. We register
    `RenMap Expr` only — users rename on expressions; `Value.rmap` is
    an internal helper that handles the closure-body traversal.
    Registering `RenMap Value` would invite ambiguous elaboration since
    almost every value pushes through identically. -/
mutual

def Value.rmap (r : Ren) : Value → Value
  | .unitV      => .unitV
  | .boolV b    => .boolV b
  | .numV  i    => .numV  i
  | .strV  s    => .strV  s
  | .schemaV τ  => .schemaV τ
  | .polV p     => .polV p
  | .principalV pr => .principalV (PrincRef.rmap r pr)
  | .recV xs    => .recV (Value.rmapRec r xs)
  | .arrV vs    => .arrV (Value.rmapList r vs)
  | .clos n body => .clos n (Expr.rmap (Ren.liftN r n) body)
  | .errV       => .errV

def Value.rmapList (r : Ren) : List Value → List Value
  | List.nil       => List.nil
  | List.cons v vs => List.cons (Value.rmap r v) (Value.rmapList r vs)

def Value.rmapRec (r : Ren) : List (String × Value) → List (String × Value)
  | List.nil             => List.nil
  | List.cons (k, v) xs  => List.cons (k, Value.rmap r v) (Value.rmapRec r xs)

def Expr.rmap (r : Ren) : Expr → Expr
  | .val v             => .val (Value.rmap r v)
  | .var x             => .var (r x)
  | .letE τ e1 e2      => .letE τ (Expr.rmap r e1) (Expr.rmap r.lift e2)
  | .ifE e1 e2 e3      => .ifE (Expr.rmap r e1) (Expr.rmap r e2) (Expr.rmap r e3)
  | .whileE e1 e2      => .whileE (Expr.rmap r e1) (Expr.rmap r e2)
  | .forE e1 e2        => .forE (Expr.rmap r e1) (Expr.rmap r.lift e2)
  | .seq e1 e2         => .seq (Expr.rmap r e1) (Expr.rmap r e2)
  | .ask s             => .ask s
  | .say s             => .say s
  | .letPrinc b body   => .letPrinc (PrincBinder.rmap r b) (Expr.rmap r body)
  | .gen τ s pr        => .gen τ s (PrincRef.rmap r pr)
  | .agent s pr        => .agent s (PrincRef.rmap r pr)
  | .evalE f args      => .evalE (Expr.rmap r f) (Expr.rmapList r args)
  | .enforce e         => .enforce (Expr.rmap r e)
  | .js je             => .js je
  | .varDecl x τ e1 e2 => .varDecl x τ (Expr.rmap r e1) (Expr.rmap r e2)
  | .assign x e        => .assign x (Expr.rmap r e)
  | .varRead x         => .varRead x
  | .proj e f          => .proj (Expr.rmap r e) f

def Expr.rmapList (r : Ren) : List Expr → List Expr
  | List.nil       => List.nil
  | List.cons e es => List.cons (Expr.rmap r e) (Expr.rmapList r es)

end

instance : RenMap Expr where
  rmap := Expr.rmap

/-- Lift a substitution through `n` binders. -/
def Subst.liftN (σ : Subst Expr) : Nat → Subst Expr
  | 0     => σ
  | n + 1 => (Subst.liftN σ n).lift

/-- Substitution on `PrincRef`. Principals live in their own de Bruijn
    scope independent of the regular Expr scope, so an Expr `Subst`
    does **not** affect PrincRef indices. -/
def PrincRef.smap (_ : Subst Expr) : PrincRef → PrincRef
  | .bvar n => .bvar n

/-- Substitution on a `PrincBinder`: identity, since the parent
    `PrincRef` lives in the entity scope (not the Expr scope). -/
def PrincBinder.smap (_ : Subst Expr) : PrincBinder → PrincBinder
  | .root        => .root
  | .restrict pr => .restrict pr

/-! ### Substitution on `Value` and `Expr`.

    Defined as a single mutual recursion because closures
    `Value.clos n body` contain an `Expr` subterm. We register
    `SubstMap Expr Expr` only — users substitute on expressions;
    `Value.smap` is an internal helper that handles the closure-body
    traversal. Registering `SubstMap Value Expr` would invite ambiguous
    elaboration since almost every value pushes through identically. -/
mutual

def Value.smap (σ : Subst Expr) : Value → Value
  | .unitV      => .unitV
  | .boolV b    => .boolV b
  | .numV  i    => .numV  i
  | .strV  s    => .strV  s
  | .schemaV τ  => .schemaV τ
  | .polV p     => .polV p
  | .principalV pr => .principalV (PrincRef.smap σ pr)
  | .recV xs    => .recV (Value.smapRec σ xs)
  | .arrV vs    => .arrV (Value.smapList σ vs)
  | .clos n body => .clos n (Expr.smap (Subst.liftN σ n) body)
  | .errV       => .errV

def Value.smapList (σ : Subst Expr) : List Value → List Value
  | List.nil       => List.nil
  | List.cons v vs => List.cons (Value.smap σ v) (Value.smapList σ vs)

def Value.smapRec (σ : Subst Expr) : List (String × Value) → List (String × Value)
  | List.nil             => List.nil
  | List.cons (k, v) xs  => List.cons (k, Value.smap σ v) (Value.smapRec σ xs)

def Expr.smap (σ : Subst Expr) : Expr → Expr
  | .val v             => .val (Value.smap σ v)
  | .var x             => Expr.from_action (σ x)
  | .letE τ e1 e2      => .letE τ (Expr.smap σ e1) (Expr.smap σ.lift e2)
  | .ifE e1 e2 e3      => .ifE (Expr.smap σ e1) (Expr.smap σ e2) (Expr.smap σ e3)
  | .whileE e1 e2      => .whileE (Expr.smap σ e1) (Expr.smap σ e2)
  | .forE e1 e2        => .forE (Expr.smap σ e1) (Expr.smap σ.lift e2)
  | .seq e1 e2         => .seq (Expr.smap σ e1) (Expr.smap σ e2)
  | .ask s             => .ask s
  | .say s             => .say s
  | .letPrinc b body   => .letPrinc (PrincBinder.smap σ b) (Expr.smap σ body)
  | .gen τ s pr        => .gen τ s (PrincRef.smap σ pr)
  | .agent s pr        => .agent s (PrincRef.smap σ pr)
  | .evalE f args      => .evalE (Expr.smap σ f) (Expr.smapList σ args)
  | .enforce e         => .enforce (Expr.smap σ e)
  | .js je             => .js je
  | .varDecl x τ e1 e2 => .varDecl x τ (Expr.smap σ e1) (Expr.smap σ e2)
  | .assign x e        => .assign x (Expr.smap σ e)
  | .varRead x         => .varRead x
  | .proj e f          => .proj (Expr.smap σ e) f

def Expr.smapList (σ : Subst Expr) : List Expr → List Expr
  | List.nil       => List.nil
  | List.cons e es => List.cons (Expr.smap σ e) (Expr.smapList σ es)

end

instance SubstMap_Expr : SubstMap Expr Expr where
  smap := Expr.smap

/-- Instantiate the outermost binder: replace `var 0` by `v` (a value,
    wrapped into an expression via `.val`) and decrement all other free
    variables by one. -/
def Expr.instantiate (e : Expr) (v : Value) : Expr :=
  Expr.smap (Subst.Action.su (.val v) :: (+0 : Subst Expr)) e

/-! ## Forward field-access analysis (Phase L).

    `fieldSitesAt p k` collects every field name `f` such that the
    expression `p` syntactically contains a projection `(var k).f`.
    This is the static, over-approximate set of field accesses on
    the de-Bruijn-`k`-bound variable. At a `let τ = gen … in p`
    redex, the runtime calls `fieldSitesAt p 0` and, if the materialized
    record value `v` lacks any of those fields, retries the gen with
    the missing-field constraint as feedback (`Step.letGenHealRecordFields`,
    Reduction.lean). The analysis does not look through values, JS,
    `letPrinc`, or principal scope (those don't bind regular Expr
    de Bruijn indices). It does correctly shift under `letE` and
    `forE`, the only Expr-binding constructors. -/
mutual

def Expr.fieldSitesAt : Expr → Nat → List String
  | .proj (.var k') f, k => if k' = k then [f] else []
  | .proj e _, k         => Expr.fieldSitesAt e k
  | .val _, _            => []
  | .var _, _            => []
  | .letE _ e1 e2, k     => Expr.fieldSitesAt e1 k ++ Expr.fieldSitesAt e2 (k + 1)
  | .ifE e1 e2 e3, k     => Expr.fieldSitesAt e1 k ++ Expr.fieldSitesAt e2 k ++ Expr.fieldSitesAt e3 k
  | .whileE e1 e2, k     => Expr.fieldSitesAt e1 k ++ Expr.fieldSitesAt e2 k
  | .forE e1 e2, k       => Expr.fieldSitesAt e1 k ++ Expr.fieldSitesAt e2 (k + 1)
  | .seq e1 e2, k        => Expr.fieldSitesAt e1 k ++ Expr.fieldSitesAt e2 k
  | .ask _, _            => []
  | .say _, _            => []
  | .letPrinc _ body, k  => Expr.fieldSitesAt body k
  | .gen _ _ _, _        => []
  | .agent _ _, _        => []
  | .evalE f args, k     => Expr.fieldSitesAt f k ++ Expr.fieldSitesAtList args k
  | .enforce e, k        => Expr.fieldSitesAt e k
  | .js _, _             => []
  | .varDecl _ _ e1 e2, k => Expr.fieldSitesAt e1 k ++ Expr.fieldSitesAt e2 k
  | .assign _ e, k       => Expr.fieldSitesAt e k
  | .varRead _, _        => []

def Expr.fieldSitesAtList : List Expr → Nat → List String
  | List.nil, _       => []
  | List.cons e es, k => Expr.fieldSitesAt e k ++ Expr.fieldSitesAtList es k

end

/-- Whether the record value `v` (or vacuously, any non-record) supplies
    every field in `sites`. Used by `Step.letGenSuccessHealable` to
    enforce that the materialized record covers every forward
    projection on the bound variable; failure routes through
    `Step.letGenHealRecordFields` instead. Non-records pass vacuously
    because the static `StaticTypeOK` check would already have rejected
    a forward projection on a non-record-typed bound variable. -/
def Value.recordSatisfies : Value → List String → Bool
  | .recV fs, sites => sites.all (fun f => (fs.lookup f).isSome)
  | _, _            => true

@[simp] theorem Value.recordSatisfies_nil (v : Value) :
    Value.recordSatisfies v [] = true := by
  cases v <;> simp [Value.recordSatisfies]

/-- Discharge for the common case: when the let-gen continuation is the
    bare bound variable `var 0`, the forward field-access analysis is
    empty and `recordSatisfies` holds vacuously. -/
@[simp] theorem Value.recordSatisfies_var0 (v : Value) :
    Value.recordSatisfies v ((Expr.var 0).fieldSitesAt 0) = true := by
  simp [Expr.fieldSitesAt]

/-! ## Principal scope well-formedness (Phase N).

    `PrincRef.bvar n` is in-scope iff `n < depth`, where `depth` is the
    number of enclosing `letPrinc` binders. Threaded through every
    Expr / Value constructor; principal binders (`letPrinc`) increment
    depth, every other Expr-binder leaves depth alone (Expr-level vars
    live in a separate de Bruijn scope).

    A closed top-level program is `Expr.princOk 0`; the static checker
    rejects programs whose `WellScoped` predicate does not evaluate to
    `true`. The scope-preservation lemma `Step.preserves_princOk`
    (Soundness) proves that this Boolean is preserved by every
    reduction rule, giving the resolution invariant: every PrincRef
    reachable at runtime points into the dynamic entity store. -/

/-- A `bvar n` is in scope iff `n < depth`. -/
def PrincRef.princOk (depth : Nat) : PrincRef → Bool
  | .bvar n => n < depth

/-- `root` is the unrestricted top-level binder; `restrict pr`
    reuses an existing principal whose `pr` must be in scope. -/
def PrincBinder.princOk (depth : Nat) : PrincBinder → Bool
  | .root        => true
  | .restrict pr => pr.princOk depth

mutual

/-- Principal-scope well-formedness for values. Recursively all
    embedded `principalV`/closure bodies must satisfy `princOk`. -/
def Value.princOk (depth : Nat) : Value → Bool
  | .unitV         => true
  | .boolV _       => true
  | .numV _        => true
  | .strV _        => true
  | .schemaV _     => true
  | .polV _        => true
  | .principalV pr => pr.princOk depth
  | .recV xs       => Value.princOkRec depth xs
  | .arrV vs       => Value.princOkList depth vs
  | .clos _ body   => Expr.princOk depth body
  | .errV          => true
termination_by v => sizeOf v

def Value.princOkList (depth : Nat) : List Value → Bool
  | List.nil       => true
  | List.cons v vs => Value.princOk depth v && Value.princOkList depth vs
termination_by l => sizeOf l

def Value.princOkRec (depth : Nat) : List (String × Value) → Bool
  | List.nil            => true
  | List.cons (_, v) xs => Value.princOk depth v && Value.princOkRec depth xs
termination_by l => sizeOf l

/-- Principal-scope well-formedness for expressions. `letPrinc` grows
    `depth` by 1 for the body; Expr-level binders (`letE`, `forE`,
    `varDecl`) leave it unchanged; `gen`/`agent` check their PrincRef. -/
def Expr.princOk (depth : Nat) : Expr → Bool
  | .val v             => Value.princOk depth v
  | .var _             => true
  | .letE _ e1 e2      => Expr.princOk depth e1 && Expr.princOk depth e2
  | .ifE e1 e2 e3      =>
      Expr.princOk depth e1 && Expr.princOk depth e2 && Expr.princOk depth e3
  | .whileE e1 e2      => Expr.princOk depth e1 && Expr.princOk depth e2
  | .forE e1 e2        => Expr.princOk depth e1 && Expr.princOk depth e2
  | .seq e1 e2         => Expr.princOk depth e1 && Expr.princOk depth e2
  | .ask _             => true
  | .say _             => true
  | .letPrinc b body   =>
      PrincBinder.princOk depth b && Expr.princOk (depth + 1) body
  | .gen _ _ pr        => pr.princOk depth
  | .agent _ pr        => pr.princOk depth
  | .evalE f args      => Expr.princOk depth f && Expr.princOkList depth args
  | .enforce e         => Expr.princOk depth e
  | .js _              => true
  | .varDecl _ _ e1 e2 => Expr.princOk depth e1 && Expr.princOk depth e2
  | .assign _ e        => Expr.princOk depth e
  | .varRead _         => true
  | .proj e _          => Expr.princOk depth e
termination_by e => sizeOf e

def Expr.princOkList (depth : Nat) : List Expr → Bool
  | List.nil       => true
  | List.cons e es => Expr.princOk depth e && Expr.princOkList depth es
termination_by l => sizeOf l

end

/-! ### `Expr.princOk` evaluation lemmas.
    Leaf simp lemmas to discharge well-scoping obligations on closed
    atomic forms without unfolding through the recursive def. -/

@[simp] theorem Expr.princOk_var (depth : Nat) (n : Nat) :
    Expr.princOk depth (.var n) = true := by unfold Expr.princOk; rfl

@[simp] theorem Expr.princOk_ask (depth : Nat) (s : String) :
    Expr.princOk depth (.ask s) = true := by unfold Expr.princOk; rfl

@[simp] theorem Expr.princOk_say (depth : Nat) (s : String) :
    Expr.princOk depth (.say s) = true := by unfold Expr.princOk; rfl

@[simp] theorem Expr.princOk_js (depth : Nat) (j : JsExpr) :
    Expr.princOk depth (.js j) = true := by unfold Expr.princOk; rfl

@[simp] theorem Expr.princOk_varRead (depth : Nat) (x : String) :
    Expr.princOk depth (.varRead x) = true := by unfold Expr.princOk; rfl

abbrev ErrCtx := List Event

/-- Number of trailing `.error` events since the most recent `.success`. -/
def ErrCtx.retries (ec : ErrCtx) : Nat :=
  ec.foldl (fun n e => match e with | .error _ => n + 1 | .success => 0) 0

@[simp] theorem ErrCtx.retries_nil : ErrCtx.retries [] = 0 := rfl

@[simp] theorem ErrCtx.retries_append_error (ec : ErrCtx) (s : String) :
    ErrCtx.retries (ec ++ [Event.error s]) = ErrCtx.retries ec + 1 := by
  unfold ErrCtx.retries
  rw [List.foldl_append]
  rfl

@[simp] theorem ErrCtx.retries_append_success (ec : ErrCtx) :
    ErrCtx.retries (ec ++ [Event.success]) = 0 := by
  unfold ErrCtx.retries
  rw [List.foldl_append]
  rfl

/-! ## Mutable-state store.

    Textbook total-function finite map from variable names to
    `(declared type, current value)` pairs.  Mutable state is a
    *separate surface* from substitution-based `letE`/de-Bruijn
    `var`; the two do not interact. -/

def Store : Type := String → Option (Ty × Value)

def Store.empty : Store := fun _ => none

def Store.get (σ : Store) (x : String) : Option (Ty × Value) := σ x

def Store.set (σ : Store) (x : String) (τ : Ty) (v : Value) : Store :=
  fun y => if y = x then some (τ, v) else σ y

end Pact
