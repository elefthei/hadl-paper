-- Syntax of HADL: types, values, de-Bruijn expressions.
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

namespace HADL

abbrev Principal := String

/-- Types. No `tVar`: Schema materialization is handled at runtime
    via the oracle's truthfulness + `RtType`. -/
inductive Ty where
  | tUnit   : Ty
  | tBool   : Ty
  | tInt    : Ty
  | tString : Ty
  | tSchema : Ty
  | tPolicy : Ty
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
  | unitV   : Value
  | boolV   : Bool → Value
  | intV    : Int → Value
  | strV    : String → Value
  | schemaV : Ty → Value
  | polV    : PolicyValue → Value
  | recV    : List (String × Value) → Value
  | arrV    : List Value → Value
  | clos    : Nat → Expr → Value

inductive Expr where
  | val     : Value → Expr
  | var     : Nat → Expr
  | letE    : Ty → Expr → Expr → Expr
  | ifE     : Expr → Expr → Expr → Expr
  | whileE  : Expr → Expr → Expr
  | forE    : Expr → Expr → Expr
  | seq     : Expr → Expr → Expr
  | ask     : String → Expr
  | say     : String → Expr
  | gen     : Ty → String → Principal → Expr
  | agent   : String → Principal → Expr
  | evalE   : Expr → List Expr → Expr
  | enforce : Expr → Expr
  | js      : JsExpr → Expr
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

mutual

def Value.rmap (r : Ren) : Value → Value
  | .unitV      => .unitV
  | .boolV b    => .boolV b
  | .intV  i    => .intV  i
  | .strV  s    => .strV  s
  | .schemaV τ  => .schemaV τ
  | .polV p     => .polV p
  | .recV xs    => .recV (Value.rmapRec r xs)
  | .arrV vs    => .arrV (Value.rmapList r vs)
  | .clos n body => .clos n (Expr.rmap (Ren.liftN r n) body)

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
  | .gen τ s π         => .gen τ s π
  | .agent s π         => .agent s π
  | .evalE f args      => .evalE (Expr.rmap r f) (Expr.rmapList r args)
  | .enforce e         => .enforce (Expr.rmap r e)
  | .js je             => .js je

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

mutual

def Value.smap (σ : Subst Expr) : Value → Value
  | .unitV      => .unitV
  | .boolV b    => .boolV b
  | .intV  i    => .intV  i
  | .strV  s    => .strV  s
  | .schemaV τ  => .schemaV τ
  | .polV p     => .polV p
  | .recV xs    => .recV (Value.smapRec σ xs)
  | .arrV vs    => .arrV (Value.smapList σ vs)
  | .clos n body => .clos n (Expr.smap (Subst.liftN σ n) body)

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
  | .gen τ s π         => .gen τ s π
  | .agent s π         => .agent s π
  | .evalE f args      => .evalE (Expr.smap σ f) (Expr.smapList σ args)
  | .enforce e         => .enforce (Expr.smap σ e)
  | .js je             => .js je

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

/-! ## Heal context. -/

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

end HADL
