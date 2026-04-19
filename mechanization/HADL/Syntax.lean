-- Syntax of HADL: types, expressions, values, evaluation contexts.
-- Matches §4 of the paper.

namespace HADL

abbrev Name := String
abbrev Principal := String
abbrev Label := Nat            -- source-span label used as provenance

inductive Mutability
  | letBind
  | varBind
  deriving DecidableEq, Repr

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

-- Error-context / heal context Σ: a list of feedback strings.
abbrev ErrCtx := List String

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
