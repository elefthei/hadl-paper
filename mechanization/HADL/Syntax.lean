-- Syntax of HADL: types, expressions, values, evaluation contexts.
-- Matches §4 of the paper.

namespace HADL

abbrev Name := String
abbrev Principal := String

inductive Mutability
  | letBind
  | varBind
  deriving DecidableEq, Repr

/-- Feedback event in the heal context Σ. A `success` marker ends a retry
    run (contributes 0 to the retry count); an `error` carries the
    explanation string appended by Gen/Agent/Eval/Enforce heal rules. -/
inductive Event
  | error   : String → Event
  | success : Event
  deriving Inhabited, Repr

mutual

inductive Ty where
  | tVar    : Name → Ty          -- reference to a Schema-typed binding
  | tUnit   : Ty
  | tBool   : Ty
  | tInt    : Ty
  | tString : Ty
  | tSchema : Ty                 -- the type of types
  | tPolicy : Ty
  | tArrow  : List Ty → Ty → Ty
  | tRecord : List (Name × Ty) → Ty
  | tArray  : Ty → Ty
  deriving Inhabited

end

-- Placeholder for the opaque JavaScript expression type.
opaque JsExprNE : NonemptyType
def JsExpr : Type := JsExprNE.type
instance : Nonempty JsExpr := JsExprNE.property

mutual

inductive Expr where
  | var     : Name → Expr
  | unit    : Expr
  | litBool : Bool → Expr
  | litInt  : Int → Expr
  | litStr  : String → Expr
  | letE    : Mutability → Name → Ty → Expr → Expr → Expr
  | assign  : Name → Expr → Expr
  | ifE     : Expr → Expr → Expr → Expr
  | whileE  : Expr → Expr → Expr
  | forE    : Name → Expr → Expr → Expr
  | seq     : Expr → Expr → Expr
  | ask     : String → Expr
  | say     : String → Expr
  | gen     : Ty → String → Option Principal → Expr
  | agent   : Ty → String → Option Principal → Expr
  | evalE   : Expr → List Expr → Expr
  | enforce : Name → Expr
  | js      : JsExpr → Expr
  | valE    : Value → Expr          -- lifted value (for reduction)
  | errTerm : List Event → Expr → Expr -- terminal error config marker (full event log + failing redex)

inductive Value where
  | vUnit   : Value
  | vBool   : Bool → Value
  | vInt    : Int → Value
  | vStr    : String → Value
  | vSchema : Ty → Value                     -- schema value reifies a type at runtime
  | vClos   : List Name → Expr → Value       -- arrow-typed binder as AST
  | vPol    : PolicyValue → Value
  | vRec    : List (Name × Value) → Value
  | vArr    : List Value → Value

-- Opaque Cedar policy value in our syntax; Cedar-Lean content lives in HADL.Policy.
inductive PolicyValue where
  | mk : String → PolicyValue        -- raw source; semantics given in Policy.lean

end

-- Error-context / heal context Σ: an append-only log of `Event`s.
-- Gen/Agent heal rules append `Event.error _`; gen-success appends
-- `Event.success`; budget is enforced on `retries`, the length of the
-- trailing run of `error` events.
abbrev ErrCtx := List Event

/-- Number of trailing `.error` events since the most recent `.success`
    (or since the start of the log). This is the retry-budget metric. -/
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

/--
  Evaluation contexts E. Left-to-right order for sequencing, conditionals,
  and argument positions. We use a small syntax-directed form; reduction
  rules unfold it on demand.
-/
inductive EvalCtx where
  | hole    : EvalCtx
  | letRhs  : Mutability → Name → Ty → EvalCtx → Expr → EvalCtx
  | assignR : Name → EvalCtx → EvalCtx
  | ifCond  : EvalCtx → Expr → Expr → EvalCtx
  | seqL    : EvalCtx → Expr → EvalCtx
  | evalFn  : EvalCtx → List Expr → EvalCtx
  | evalArg : Expr → List Value → EvalCtx → List Expr → EvalCtx

end HADL
