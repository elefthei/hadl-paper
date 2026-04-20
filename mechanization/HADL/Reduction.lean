-- Small-step reduction over 3-tuple configurations, substitution-based CBV.
-- Two-sort variant: values have their own type; value positions use `.val v`.

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

def OAction.effect : OAction → Action
  | .gen _ _ _   => .gen
  | .agent _ _   => .agent

def OAction.toExpr : OAction → Expr
  | .gen τ s π => .gen τ s π
  | .agent s π => .agent s π

opaque explain : OAction → Value → String
opaque explainPolicy : OAction → Policy → String

/--
  Small-step relation `C ⟶ C'`, parameterized by an oracle `O`.

  Substitution-based CBV over the two-sort syntax: `letE` reduces by
  instantiating the body with a `Value`; `forE` reduces by substituting
  the head element and recursing on the tail.

  The three oracle rules (success / type-heal / policy-heal) are unified
  across gen and agent via the `OAction` tag.
-/
inductive Step (O : Oracle) : Config → Config → Prop where

  -- Pure core.

  | letBind {ec P τ v e}
      (hrt : RtType v τ) :
      Step O ⟨ec, P, .letE τ (.val v) e⟩ ⟨ec, P, e.instantiate v⟩

  | ifTrue {ec P e₁ e₂} :
      Step O ⟨ec, P, .ifE (.val (.boolV true)) e₁ e₂⟩ ⟨ec, P, e₁⟩

  | ifFalse {ec P e₁ e₂} :
      Step O ⟨ec, P, .ifE (.val (.boolV false)) e₁ e₂⟩ ⟨ec, P, e₂⟩

  | whileUnfold {ec P e e'} :
      Step O ⟨ec, P, .whileE e e'⟩
             ⟨ec, P, .ifE e (.seq e' (.whileE e e')) (.val .unitV)⟩

  | forNil {ec P e} :
      Step O ⟨ec, P, .forE (.val (.arrV [])) e⟩ ⟨ec, P, .val .unitV⟩

  | forCons {ec P v vs e} :
      Step O ⟨ec, P, .forE (.val (.arrV (v :: vs))) e⟩
             ⟨ec, P, .seq (e.instantiate v) (.forE (.val (.arrV vs)) e)⟩

  | seqStep {ec P v e} :
      Step O ⟨ec, P, .seq (.val v) e⟩ ⟨ec, P, e⟩

  | jsStep {ec P je v}
      (h : jsEval je = some v) :
      Step O ⟨ec, P, .js je⟩ ⟨ec, P, .val v⟩

  | sayStep {ec P s} :
      Step O ⟨ec, P, .say s⟩ ⟨ec, P, .val .unitV⟩

  | askStep {ec P s v}
      (horacle : O s ec .tString v)
      (hrt : RtType v .tString) :
      Step O ⟨ec, P, .ask s⟩ ⟨ec ++ [Event.success], P, .val v⟩

  -- Unified oracle rules (gen / agent).

  | oracleSuccess {ec P v} {a : OAction}
      (hauth   : policyAllows P a.princ a.effect)
      (horacle : O a.stmt ec a.ty v)
      (hrt     : RtType v a.ty) :
      Step O ⟨ec, P, a.toExpr⟩ ⟨ec ++ [Event.success], P, .val v⟩

  | oracleHealType {ec P v} {a : OAction}
      (hauth   : policyAllows P a.princ a.effect)
      (horacle : O a.stmt ec a.ty v)
      (hbad    : ¬ RtType v a.ty)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explain a v)]) ≤ retryBudget) :
      Step O ⟨ec, P, a.toExpr⟩
             ⟨ec ++ [Event.error (explain a v)], P, a.toExpr⟩

  | oracleHealPol {ec P} {a : OAction}
      (hdeny   : ¬ policyAllows P a.princ a.effect)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explainPolicy a P)]) ≤ retryBudget) :
      Step O ⟨ec, P, a.toExpr⟩
             ⟨ec ++ [Event.error (explainPolicy a P)], P, a.toExpr⟩

  -- Eval: closure application. `clos n body` applied to n value args.
  -- Arguments appear in the source Expr position wrapped in `.val`.

  | evalSuccess {ec P n body} {vs : List Value}
      (_hlen : vs.length = n) :
      Step O ⟨ec, P, .evalE (.val (.clos n body)) (vs.map Expr.val)⟩
             ⟨ec, P, Expr.smap
                (vs.foldr (fun v σ => Subst.Action.su (.val v) :: σ) (+0 : Subst Expr))
                body⟩

  -- Enforce.

  | enforceInstall {ec P P' p}
      (hinst : policyInstall P p = some P') :
      Step O ⟨ec, P, .enforce (.val (.polV p))⟩ ⟨ec, P', .val .unitV⟩

  -- CBV congruence. Reduces leftmost redex.

  | letCong {ec ec' P P' τ e₁ e₁' e₂}
      (h : Step O ⟨ec, P, e₁⟩ ⟨ec', P', e₁'⟩) :
      Step O ⟨ec, P, .letE τ e₁ e₂⟩ ⟨ec', P', .letE τ e₁' e₂⟩

  | ifCong {ec ec' P P' e₁ e₁' e₂ e₃}
      (h : Step O ⟨ec, P, e₁⟩ ⟨ec', P', e₁'⟩) :
      Step O ⟨ec, P, .ifE e₁ e₂ e₃⟩ ⟨ec', P', .ifE e₁' e₂ e₃⟩

  | seqCong {ec ec' P P' e₁ e₁' e₂}
      (h : Step O ⟨ec, P, e₁⟩ ⟨ec', P', e₁'⟩) :
      Step O ⟨ec, P, .seq e₁ e₂⟩ ⟨ec', P', .seq e₁' e₂⟩

  | forCong {ec ec' P P' e₁ e₁' e₂}
      (h : Step O ⟨ec, P, e₁⟩ ⟨ec', P', e₁'⟩) :
      Step O ⟨ec, P, .forE e₁ e₂⟩ ⟨ec', P', .forE e₁' e₂⟩

  | enforceCong {ec ec' P P' e e'}
      (h : Step O ⟨ec, P, e⟩ ⟨ec', P', e'⟩) :
      Step O ⟨ec, P, .enforce e⟩ ⟨ec', P', .enforce e'⟩

  | evalFunCong {ec ec' P P' f f' args}
      (h : Step O ⟨ec, P, f⟩ ⟨ec', P', f'⟩) :
      Step O ⟨ec, P, .evalE f args⟩ ⟨ec', P', .evalE f' args⟩

inductive Steps (O : Oracle) : Config → Config → Prop where
  | refl {C} : Steps O C C
  | step {C C' C''} : Step O C C' → Steps O C' C'' → Steps O C C''

end HADL
