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

  Convention: where the paper writes an explicit `isValue(v)` premise
  (e.g. `Seq`, `For-Cons`, `Eval-Success`, `Ask`, `letBind`,
  `oracleSuccess`), the Lean rules enforce it structurally via the
  `.val v` pattern on `Value`, so the premise is omitted rather than
  restated.
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

  /-- Oracle ask: consult `O`, flush heal context to `[]` on success
      (per `hadl-formal.md`: Σ stores only errors and becomes empty on
      a successful oracle step). -/
  | askStep {ec P σ s v}
      (horacle : O s ec .tString v)
      (hrt : RtType v .tString) :
      Step O ⟨ec, P, σ, .ask s⟩ ⟨[], P, σ, .val v⟩

  -- Standalone agent rules.
  --
  -- `agent s π` materializes `tString`, which is `¬ Ty.healable`, so it
  -- has no self-heal-by-type rule. It keeps a success rule and a
  -- policy-denial heal rule, mirroring the let-redex story for
  -- non-healable types but without going through a let-redex.
  -- (Conceptually, `agent s π` is shorthand for
  -- `let _ : String = agent s π ; ()`.)

  /-- `agent` success: oracle returns a well-typed string and policy
      allows; flush heal context to `[]`. -/
  | agentSuccess {ec P σ v s π}
      (hauth   : policyAllows P π .agent)
      (horacle : O s ec .tString v)
      (hrt     : RtType v .tString) :
      Step O ⟨ec, P, σ, .agent s π⟩ ⟨[], P, σ, .val v⟩

  /-- `agent` policy-heal: policy denied within budget; record error and
      retry. -/
  | agentHealPol {ec P σ s π}
      (hdeny   : ¬ policyAllows P π .agent)
      (hbudget : ErrCtx.retries
                   (ec ++ [Event.error (explainPolicy (.agent s π) P)])
                   ≤ retryBudget) :
      Step O ⟨ec, P, σ, .agent s π⟩
             ⟨ec ++ [Event.error (explainPolicy (.agent s π) P)], P, σ,
              .agent s π⟩

  -- Let-redex rules for `gen τ s π`.
  --
  -- `gen` is NOT a standalone redex anymore — it only reduces as the
  -- immediate RHS of a `let`. Per `hadl-formal.md`:
  --   * Success flushes `ec` to `[]` (not `ec ++ [Event.success]`).
  --   * Self-heal at healable τ is driven by *continuation* typing
  --     failure, not by value typing failure.
  --   * Value typing failure at healable τ has NO rule — the
  --     configuration is stuck by omission; progress (T4c) rules it
  --     out under eventually-truthful oracle.
  -- The Schema-specific constructors below implement this; Policy and
  -- Arrow triads follow the same pattern in Phases 2/3.

  /-- Let-context congruence at non-healable types. At a healable τ,
      the RHS of the let must be `gen s π` or already a value, so no
      generic congruence applies. -/
  | letCongNonheal {ec ec' P P' σ σ' τ e₁ e₁' e₂}
      (hheal : Ty.healable τ = false)
      (h : Step O ⟨ec, P, σ, e₁⟩ ⟨ec', P', σ', e₁'⟩) :
      Step O ⟨ec, P, σ, .letE τ e₁ e₂⟩ ⟨ec', P', σ', .letE τ e₁' e₂⟩

  /-- Let-redex success at non-healable τ: oracle returned a well-typed
      value at a non-healable type, policy allows; flush, substitute and
      continue. -/
  | letGenSuccessNonheal {ec P σ τ s π v p}
      (hheal   : Ty.healable τ = false)
      (hauth   : policyAllows P π .gen)
      (horacle : O s ec τ v)
      (hrt     : RtType v τ) :
      Step O ⟨ec, P, σ, .letE τ (.gen τ s π) p⟩
             ⟨[], P, σ, p.instantiate v⟩

  /-- Let-redex hard TypeError at non-healable τ: oracle returned
      ill-typed value. Steps to `errV` — terminal failure. Only fires
      at non-healable τ; at healable τ value-fail has no rule. -/
  | letGenTypeError {ec P σ τ s π v p}
      (hheal   : Ty.healable τ = false)
      (hauth   : policyAllows P π .gen)
      (horacle : O s ec τ v)
      (hbad    : ¬ RtType v τ) :
      Step O ⟨ec, P, σ, .letE τ (.gen τ s π) p⟩
             ⟨ec, P, σ, .val .errV⟩

  /-- Let-redex hard BudgetError (uniform across all τ): retries
      exhausted. Doesn't consult the oracle — fires immediately as soon
      as `retries(ec) > retryBudget`. -/
  | letGenBudgetError {ec P σ τ s π p}
      (hover : ErrCtx.retries ec > retryBudget) :
      Step O ⟨ec, P, σ, .letE τ (.gen τ s π) p⟩
             ⟨ec, P, σ, .val .errV⟩

  /-- Let-redex policy-heal (uniform across all τ): policy denied gen
      action; record error and retry. -/
  | letGenHealPol {ec P σ τ s π p}
      (hdeny   : ¬ policyAllows P π .gen)
      (hbudget : ErrCtx.retries
                   (ec ++ [Event.error (explainPolicy (.gen τ s π) P)])
                   ≤ retryBudget) :
      Step O ⟨ec, P, σ, .letE τ (.gen τ s π) p⟩
             ⟨ec ++ [Event.error (explainPolicy (.gen τ s π) P)], P, σ,
              .letE τ (.gen τ s π) p⟩

  -- Schema triad (Phase 1), continuation-driven per hadl-formal.md.

  /-- Let-redex success at Schema: oracle returned a well-typed Schema
      value AND the continuation `p` statically types at `τ'` under the
      extension `[var 0 : Schema]`. Flush heal context to `[]` and
      commit by substitution. -/
  | letGenSuccessSchema {ec P σ s π v p τ'}
      (hauth   : policyAllows P π .gen)
      (horacle : O s ec .tSchema v)
      (hrt     : RtType v .tSchema)
      (hpok    : StaticTypeOK .tSchema p τ') :
      Step O ⟨ec, P, σ, .letE .tSchema (.gen .tSchema s π) p⟩
             ⟨[], P, σ, p.instantiate v⟩

  /-- Let-redex self-heal at Schema: oracle returned a well-typed Schema
      value, BUT the continuation fails to type-check at some τ' under
      `[var 0 : Schema]`. Record the continuation's feedback string ε
      and retry the same redex within budget. -/
  | letGenHealSchema {ec P σ s π v p τ' ε}
      (hauth   : policyAllows P π .gen)
      (horacle : O s ec .tSchema v)
      (hrt     : RtType v .tSchema)
      (hperr   : ¬ StaticTypeOK .tSchema p τ')
      (hbudget : ErrCtx.retries (ec ++ [Event.error ε]) ≤ retryBudget) :
      Step O ⟨ec, P, σ, .letE .tSchema (.gen .tSchema s π) p⟩
             ⟨ec ++ [Event.error ε], P, σ,
              .letE .tSchema (.gen .tSchema s π) p⟩

  -- Arrow triad (Phase 3), continuation-driven (mirrors Schema).
  -- Only difference from the Schema rules is the materialization type
  -- (`tArrow args ret`). The capture-avoiding substitution `p.instantiate v`
  -- is provided uniformly by `lean-subst` for any value `v`, including the
  -- closure values produced by the oracle at arrow types.

  /-- Let-redex success at arrow type: oracle returned a well-typed
      workflow value AND the continuation `p` statically types at `τ'`
      under `[var 0 : tArrow args ret]`. Flush heal context to `[]`
      and commit by substitution. -/
  | letGenSuccessArrow {ec P σ args ret s π v p τ'}
      (hauth   : policyAllows P π .gen)
      (horacle : O s ec (.tArrow args ret) v)
      (hrt     : RtType v (.tArrow args ret))
      (hpok    : StaticTypeOK (.tArrow args ret) p τ') :
      Step O ⟨ec, P, σ,
              .letE (.tArrow args ret) (.gen (.tArrow args ret) s π) p⟩
             ⟨[], P, σ, p.instantiate v⟩

  /-- Let-redex self-heal at arrow type: well-typed workflow value,
      but the continuation fails to type-check at some τ' under
      `[var 0 : tArrow args ret]`. Record the continuation's feedback
      string ε and retry the same redex within budget. -/
  | letGenHealArrow {ec P σ args ret s π v p τ' ε}
      (hauth   : policyAllows P π .gen)
      (horacle : O s ec (.tArrow args ret) v)
      (hrt     : RtType v (.tArrow args ret))
      (hperr   : ¬ StaticTypeOK (.tArrow args ret) p τ')
      (hbudget : ErrCtx.retries (ec ++ [Event.error ε]) ≤ retryBudget) :
      Step O ⟨ec, P, σ,
              .letE (.tArrow args ret) (.gen (.tArrow args ret) s π) p⟩
             ⟨ec ++ [Event.error ε], P, σ,
              .letE (.tArrow args ret) (.gen (.tArrow args ret) s π) p⟩

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
  --
  -- Note: the generic `letCong` rule is removed in favor of
  -- `letCongNonheal` above, which fires only when `Ty.healable τ`
  -- is `false`. At healable τ, the let-redex must be `letE τ (.gen τ s π) _`
  -- or already a value, so no generic congruence applies.

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
