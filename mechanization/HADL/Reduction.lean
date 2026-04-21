-- Small-step reduction over 4-tuple configurations, substitution-based CBV.
-- Two-sort values + mutable-state store.

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Oracle
import HADL.JsAxioms
import HADL.Config

open LeanSubst

namespace HADL

/-- Oracle action tag: gen / agent. Shared between success and
    type-heal rules. -/
inductive OAction where
  | gen   : Ty → String → Principal → OAction
  | agent : String → Principal → OAction

def OAction.stmt : OAction → String
  | .gen _ s _   => s
  | .agent s _   => s

def OAction.ty : OAction → Ty
  | .gen τ _ _ => τ
  | .agent _ _ => .tString

def OAction.princ : OAction → Principal
  | .gen _ _ π => π
  | .agent _ π => π

def OAction.eff : OAction → Action
  | .gen _ _ _   => .gen
  | .agent _ _   => .agent

def OAction.toExpr : OAction → Expr
  | .gen τ s π => .gen τ s π
  | .agent s π => .agent s π

opaque explain : OAction → Value → String
opaque explainPolicy : OAction → Policy → String

/--
  Small-step relation `C ⟶ C'`, parameterized by an oracle `O`.

  4-tuple configs carry a mutable-state store `σ`; all existing rules
  thread `σ` unchanged. The three mutable-state constructors
  (`varDecl` / `assign` / `varRead`) add five new rules at the bottom.
-/
inductive Step (O : Oracle) : Config → Config → Prop where

  -- Pure core.

  /-- `let _ : τ = v ; e` reduces to `e[v/0]`. -/
  | letBind {ec P σ τ v e}
      (hrt : RtType v τ) :
      Step O ⟨ec, P, σ, .letE τ (.val v) e⟩ ⟨ec, P, σ, e.instantiate v⟩

  /-- If-then-else on `.boolV true` picks the then-branch. -/
  | ifTrue {ec P σ e₁ e₂} :
      Step O ⟨ec, P, σ, .ifE (.val (.boolV true)) e₁ e₂⟩ ⟨ec, P, σ, e₁⟩

  /-- If-then-else on `.boolV false` picks the else-branch. -/
  | ifFalse {ec P σ e₁ e₂} :
      Step O ⟨ec, P, σ, .ifE (.val (.boolV false)) e₁ e₂⟩ ⟨ec, P, σ, e₂⟩

  /-- `while e e'` unfolds to `if e then (e'; while e e') else unit`. -/
  | whileUnfold {ec P σ e e'} :
      Step O ⟨ec, P, σ, .whileE e e'⟩
             ⟨ec, P, σ, .ifE e (.seq e' (.whileE e e')) (.val .unitV)⟩

  /-- For-each over an empty array reduces to unit. -/
  | forNil {ec P σ e} :
      Step O ⟨ec, P, σ, .forE (.val (.arrV [])) e⟩ ⟨ec, P, σ, .val .unitV⟩

  /-- For-each unfolds one iteration over the head element. -/
  | forCons {ec P σ v vs e} :
      Step O ⟨ec, P, σ, .forE (.val (.arrV (v :: vs))) e⟩
             ⟨ec, P, σ, .seq (e.instantiate v) (.forE (.val (.arrV vs)) e)⟩

  /-- Sequence discards the value to its left. -/
  | seqStep {ec P σ v e} :
      Step O ⟨ec, P, σ, .seq (.val v) e⟩ ⟨ec, P, σ, e⟩

  /-- Opaque JS evaluation: fire if `jsEval` returns `some v`. -/
  | jsStep {ec P σ je v}
      (h : jsEval je = some v) :
      Step O ⟨ec, P, σ, .js je⟩ ⟨ec, P, σ, .val v⟩

  /-- `say s` is a no-op that reduces to unit. -/
  | sayStep {ec P σ s} :
      Step O ⟨ec, P, σ, .say s⟩ ⟨ec, P, σ, .val .unitV⟩

  /-- Oracle ask: consult `O`, append success event. -/
  | askStep {ec P σ s v}
      (horacle : O s ec .tString v)
      (hrt : RtType v .tString) :
      Step O ⟨ec, P, σ, .ask s⟩ ⟨ec ++ [Event.success], P, σ, .val v⟩

  -- Unified oracle rules (gen / agent).

  /-- Unified `gen`/`agent` success rule when oracle returns a well-typed
      value AND policy allows. -/
  | oracleSuccess {ec P σ v} {a : OAction}
      (hauth   : policyAllows P a.princ a.eff)
      (horacle : O a.stmt ec a.ty v)
      (hrt     : RtType v a.ty) :
      Step O ⟨ec, P, σ, a.toExpr⟩ ⟨ec ++ [Event.success], P, σ, .val v⟩

  /-- Type-heal: oracle returned an ill-typed value within budget; record
      error, retry. -/
  | oracleHealType {ec P σ v} {a : OAction}
      (hauth   : policyAllows P a.princ a.eff)
      (horacle : O a.stmt ec a.ty v)
      (hbad    : ¬ RtType v a.ty)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explain a v)]) ≤ retryBudget) :
      Step O ⟨ec, P, σ, a.toExpr⟩
             ⟨ec ++ [Event.error (explain a v)], P, σ, a.toExpr⟩

  /-- Policy-heal: policy denied action within budget; record error, retry. -/
  | oracleHealPol {ec P σ} {a : OAction}
      (hdeny   : ¬ policyAllows P a.princ a.eff)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explainPolicy a P)]) ≤ retryBudget) :
      Step O ⟨ec, P, σ, a.toExpr⟩
             ⟨ec ++ [Event.error (explainPolicy a P)], P, σ, a.toExpr⟩

  -- Eval: closure application.

  /-- Closure application: substitute arguments into body. -/
  | evalSuccess {ec P σ n body} {vs : List Value}
      (_hlen : vs.length = n) :
      Step O ⟨ec, P, σ, .evalE (.val (.clos n body)) (vs.map Expr.val)⟩
             ⟨ec, P, σ, Expr.smap
                (vs.foldr (fun v s => Subst.Action.su (.val v) :: s) (+0 : Subst Expr))
                body⟩

  -- Enforce.

  /-- Install a policy; produces a shrunken allow-set. -/
  | enforceInstall {ec P σ P' p}
      (hinst : policyInstall P p = some P') :
      Step O ⟨ec, P, σ, .enforce (.val (.polV p))⟩ ⟨ec, P', σ, .val .unitV⟩

  -- CBV congruence.

  /-- Let-context congruence: step under `letE _ □ _`. -/
  | letCong {ec ec' P P' σ σ' τ e₁ e₁' e₂}
      (h : Step O ⟨ec, P, σ, e₁⟩ ⟨ec', P', σ', e₁'⟩) :
      Step O ⟨ec, P, σ, .letE τ e₁ e₂⟩ ⟨ec', P', σ', .letE τ e₁' e₂⟩

  /-- If-context congruence: step under `ifE □ _ _`. -/
  | ifCong {ec ec' P P' σ σ' e₁ e₁' e₂ e₃}
      (h : Step O ⟨ec, P, σ, e₁⟩ ⟨ec', P', σ', e₁'⟩) :
      Step O ⟨ec, P, σ, .ifE e₁ e₂ e₃⟩ ⟨ec', P', σ', .ifE e₁' e₂ e₃⟩

  /-- Seq-context congruence: step under `seq □ _`. -/
  | seqCong {ec ec' P P' σ σ' e₁ e₁' e₂}
      (h : Step O ⟨ec, P, σ, e₁⟩ ⟨ec', P', σ', e₁'⟩) :
      Step O ⟨ec, P, σ, .seq e₁ e₂⟩ ⟨ec', P', σ', .seq e₁' e₂⟩

  /-- For-context congruence: step under `forE □ _`. -/
  | forCong {ec ec' P P' σ σ' e₁ e₁' e₂}
      (h : Step O ⟨ec, P, σ, e₁⟩ ⟨ec', P', σ', e₁'⟩) :
      Step O ⟨ec, P, σ, .forE e₁ e₂⟩ ⟨ec', P', σ', .forE e₁' e₂⟩

  /-- Enforce-context congruence: step under `enforce □`. -/
  | enforceCong {ec ec' P P' σ σ' e e'}
      (h : Step O ⟨ec, P, σ, e⟩ ⟨ec', P', σ', e'⟩) :
      Step O ⟨ec, P, σ, .enforce e⟩ ⟨ec', P', σ', .enforce e'⟩

  /-- Eval-function congruence: step under `evalE □ args`. -/
  | evalFunCong {ec ec' P P' σ σ' f f' args}
      (h : Step O ⟨ec, P, σ, f⟩ ⟨ec', P', σ', f'⟩) :
      Step O ⟨ec, P, σ, .evalE f args⟩ ⟨ec', P', σ', .evalE f' args⟩

  -- Mutable state.

  /-- Var-decl initializer congruence: step under `varDecl x τ □ _`. -/
  | varDeclEval {ec ec' P P' σ σ' x τ e1 e1' e2}
      (h : Step O ⟨ec, P, σ, e1⟩ ⟨ec', P', σ', e1'⟩) :
      Step O ⟨ec, P, σ, .varDecl x τ e1 e2⟩
             ⟨ec', P', σ', .varDecl x τ e1' e2⟩

  /-- Declare a new store cell at a well-typed value. -/
  | varDeclBind {ec P σ x τ v e2}
      (hrt : RtType v τ) :
      Step O ⟨ec, P, σ, .varDecl x τ (.val v) e2⟩
             ⟨ec, P, σ.set x τ v, e2⟩

  /-- Assignment RHS congruence: step under `assign x □`. -/
  | assignEval {ec ec' P P' σ σ' x e e'}
      (h : Step O ⟨ec, P, σ, e⟩ ⟨ec', P', σ', e'⟩) :
      Step O ⟨ec, P, σ, .assign x e⟩ ⟨ec', P', σ', .assign x e'⟩

  /-- Assign to an existing store cell (type-checked). -/
  | assignWrite {ec P σ x v τ vOld}
      (hbound : σ x = some (τ, vOld))
      (hrt : RtType v τ) :
      Step O ⟨ec, P, σ, .assign x (.val v)⟩
             ⟨ec, P, σ.set x τ v, .val .unitV⟩

  /-- Read from an existing store cell. -/
  | varReadStep {ec P σ x τ v}
      (hbound : σ x = some (τ, v)) :
      Step O ⟨ec, P, σ, .varRead x⟩ ⟨ec, P, σ, .val v⟩

inductive Steps (O : Oracle) : Config → Config → Prop where
  | refl {C} : Steps O C C
  | step {C C' C''} : Step O C C' → Steps O C' C'' → Steps O C C''

end HADL
