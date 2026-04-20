-- Syntax of HADL: types, de-Bruijn expressions, values.
-- Matches the simplified §4 of the paper (substitution-based CBV).
--
-- Values are the subset of `Expr` satisfying `isValue`.
-- Substitution and renaming are provided via the `lean-subst` library.

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

/-- De-Bruijn expressions. Binders: `letE` (1 in body), `forE`
    (1 in body), `clos n _` (n in body). -/
inductive Expr where
  | var     : Nat → Expr
  | unit    : Expr
  | litBool : Bool → Expr
  | litInt  : Int → Expr
  | litStr  : String → Expr
  | schemaV : Ty → Expr
  | polV    : PolicyValue → Expr
  | recV    : List (String × Expr) → Expr
  | arrV    : List Expr → Expr
  | clos    : Nat → Expr → Expr
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

-- Value predicate, as a `Bool` so it elaborates inside patterns.
mutual
def Expr.isValueB : Expr → Bool
  | .unit | .litBool _ | .litInt _ | .litStr _
  | .schemaV _ | .polV _ | .clos _ _  => true
  | .recV xs => Expr.allValRec xs
  | .arrV vs => Expr.allVal vs
  | _ => false

def Expr.allVal : List Expr → Bool
  | List.nil       => true
  | List.cons v vs => Expr.isValueB v && Expr.allVal vs

def Expr.allValRec : List (String × Expr) → Bool
  | List.nil             => true
  | List.cons (_, e) xs  => Expr.isValueB e && Expr.allValRec xs
end

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

def Expr.rmap (r : Ren) : Expr → Expr
  | .var x             => .var (r x)
  | .unit              => .unit
  | .litBool b         => .litBool b
  | .litInt  i         => .litInt  i
  | .litStr  s         => .litStr  s
  | .schemaV τ         => .schemaV τ
  | .polV p            => .polV p
  | .recV xs           => .recV (Expr.rmapRec r xs)
  | .arrV vs           => .arrV (Expr.rmapList r vs)
  | .clos n body       => .clos n (Expr.rmap (Ren.liftN r n) body)
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

def Expr.rmapRec (r : Ren) : List (String × Expr) → List (String × Expr)
  | List.nil              => List.nil
  | List.cons (k, e) xs   => List.cons (k, Expr.rmap r e) (Expr.rmapRec r xs)

end

instance : RenMap Expr where
  rmap := Expr.rmap

/-- Lift a substitution through `n` binders. -/
def Subst.liftN (σ : Subst Expr) : Nat → Subst Expr
  | 0     => σ
  | n + 1 => (Subst.liftN σ n).lift

mutual

def Expr.smap (σ : Subst Expr) : Expr → Expr
  | .var x             => Expr.from_action (σ x)
  | .unit              => .unit
  | .litBool b         => .litBool b
  | .litInt  i         => .litInt  i
  | .litStr  s         => .litStr  s
  | .schemaV τ         => .schemaV τ
  | .polV p            => .polV p
  | .recV xs           => .recV (Expr.smapRec σ xs)
  | .arrV vs           => .arrV (Expr.smapList σ vs)
  | .clos n body       => .clos n (Expr.smap (Subst.liftN σ n) body)
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

def Expr.smapRec (σ : Subst Expr) : List (String × Expr) → List (String × Expr)
  | List.nil             => List.nil
  | List.cons (k, e) xs  => List.cons (k, Expr.smap σ e) (Expr.smapRec σ xs)

end

instance SubstMap_Expr : SubstMap Expr Expr where
  smap := Expr.smap

/-- Instantiate the outermost binder: replace `var 0` by `v` and
    decrement all other free variables by one. -/
def Expr.instantiate (e : Expr) (v : Expr) : Expr :=
  Expr.smap (Subst.Action.su v :: (+0 : Subst Expr)) e

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
