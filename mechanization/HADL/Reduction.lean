-- Small-step reduction. Three layers: L1 core / L2 gen / L3 policy.

import HADL.Syntax
import HADL.Env
import HADL.Typing
import HADL.Policy
import HADL.Oracle
import HADL.JsAxioms
import HADL.Config

namespace HADL

def EvalCtx.plug : EvalCtx → Expr → Expr
  | .hole, e => e
  | _, e => e

opaque explainType   : Value → Ty → String
opaque explainPolicy : Principal → Policy → String
/-- Implementation-supplied prompt for regenerating the policy value bound
    to `x` on Enforce-Heal. Opaque: in the formal model we do not commit
    to how the implementation recovers the prompt — this abstracts over
    whether it is stored alongside the binding, in a registry, or in the
    IDE. -/
opaque provPrompt : Env → Name → String

/--
  Small-step relation `C ⟶ C'`, parameterized by an oracle `O`.
  We use `ec` for the heal-context component (paper's `Σ`).
-/
inductive Step (O : Oracle) : Config → Config → Prop where
  | var {ρ ec P π x v b}
      (h : Env.lookup ρ x = some b)
      (hv : b.value = v) :
      Step O ⟨ρ, ec, P, π, .var x⟩ ⟨ρ, ec, P, π, .valE v⟩

  | letBind {ρ ec P π m x τ v e}
      (hrt : RtType ρ v τ)
      (hfr : Env.fresh ρ x) :
      Step O
        ⟨ρ, ec, P, π, .letE m x τ (.valE v) e⟩
        ⟨Env.extend ρ x ⟨v, τ, m⟩, ec, P, π, e⟩

  | assign {ρ ec P π x v b}
      (hlk : Env.lookup ρ x = some b)
      (hty : b.mode = .varBind)
      (hrt : RtType ρ v b.ty) :
      Step O
        ⟨ρ, ec, P, π, .assign x (.valE v)⟩
        ⟨Env.assign ρ x v b, ec, P, π, .unit⟩

  | ifTrue {ρ ec P π e₁ e₂} :
      Step O
        ⟨ρ, ec, P, π, .ifE (.litBool true) e₁ e₂⟩
        ⟨ρ, ec, P, π, e₁⟩

  | ifFalse {ρ ec P π e₁ e₂} :
      Step O
        ⟨ρ, ec, P, π, .ifE (.litBool false) e₁ e₂⟩
        ⟨ρ, ec, P, π, e₂⟩

  | whileUnfold {ρ ec P π e e'} :
      Step O
        ⟨ρ, ec, P, π, .whileE e e'⟩
        ⟨ρ, ec, P, π, .ifE e (.seq e' (.whileE e e')) .unit⟩

  | forNil {ρ ec P π x e} :
      Step O
        ⟨ρ, ec, P, π, .forE x (.valE (.vArr [])) e⟩
        ⟨ρ, ec, P, π, .unit⟩

  | forCons {ρ ec P π x τ v vs e}
      (hrt : RtType ρ v τ)
      (hfr : Env.fresh ρ x) :
      Step O
        ⟨ρ, ec, P, π, .forE x (.valE (.vArr (v :: vs))) e⟩
        ⟨Env.extend ρ x ⟨v, τ, .letBind⟩, ec, P, π,
         .seq e (.forE x (.valE (.vArr vs)) e)⟩

  | seqStep {ρ ec P π v e} :
      Step O
        ⟨ρ, ec, P, π, .seq (.valE v) e⟩
        ⟨ρ, ec, P, π, e⟩

  | jsStep {ρ ec P π je v}
      (h : jsEval je ρ = some v) :
      Step O ⟨ρ, ec, P, π, .js je⟩ ⟨ρ, ec, P, π, .valE v⟩

  | genSuccess {ρ ec P π τ s v}
      (hauth  : policyAllows P π .gen)
      (horacle : O s ec τ v)
      (hrt    : RtType ρ v τ)
      (hstage : StType (Env.proj ρ) (.valE v) τ) :
      Step O
        ⟨ρ, ec, P, π, .gen τ s none⟩
        ⟨ρ, ec ++ [Event.success], P, π, .valE v⟩

  | genHealType {ρ ec P π τ s v}
      (horacle : O s ec τ v)
      (hbad    : ¬ RtType ρ v τ)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explainType v τ)]) ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .gen τ s none⟩
        ⟨ρ, ec ++ [Event.error (explainType v τ)], P, π, .gen τ s none⟩

  | genHealPol {ρ ec P π τ s}
      (hdeny   : ¬ policyAllows P π .gen)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explainPolicy π P)]) ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .gen τ s none⟩
        ⟨ρ, ec ++ [Event.error (explainPolicy π P)], P, π, .gen τ s none⟩

  | enforceInstall {ρ ec P P' π x p b}
      (hb   : Env.lookup ρ x = some b)
      (hpol : b.value = .vPol p)
      (hty  : b.ty = .tPolicy)
      (hinst : policyInstall P p = some P') :
      Step O
        ⟨ρ, ec, P, π, .enforce x⟩
        ⟨ρ, ec, P', π, .unit⟩

  -- L1/L2: Ask / Say. Ask queries the oracle for a string answer;
  -- Say is a pure output with no model-level side effect.
  | askStep {ρ ec P π s v}
      (horacle : O s ec .tString v)
      (hrt     : RtType ρ v .tString) :
      Step O
        ⟨ρ, ec, P, π, .ask s⟩
        ⟨ρ, ec ++ [Event.success], P, π, .valE v⟩

  | sayStep {ρ ec P π s} :
      Step O
        ⟨ρ, ec, P, π, .say s⟩
        ⟨ρ, ec, P, π, .unit⟩

  -- L2: Agent family. Agent-Success mirrors Gen-Success but inlines the
  -- returned value rather than binding it, appending a success event.
  | agentSuccess {ρ ec P π τ s pr v}
      (hauth   : policyAllows P π .agent)
      (horacle : O s ec τ v)
      (hrt     : RtType ρ v τ) :
      Step O
        ⟨ρ, ec, P, π, .agent τ s pr⟩
        ⟨ρ, ec ++ [Event.success], P, π, .valE v⟩

  | agentHealType {ρ ec P π τ s pr v}
      (horacle : O s ec τ v)
      (hbad    : ¬ RtType ρ v τ)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explainType v τ)]) ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .agent τ s pr⟩
        ⟨ρ, ec ++ [Event.error (explainType v τ)], P, π, .agent τ s pr⟩

  | agentHealPol {ρ ec P π τ s pr}
      (hdeny   : ¬ policyAllows P π .agent)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explainPolicy π P)]) ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .agent τ s pr⟩
        ⟨ρ, ec ++ [Event.error (explainPolicy π P)], P, π, .agent τ s pr⟩

  -- L2: Eval family. Invokes a workflow value (vClos) extending the env
  -- with the parameter bindings `bs`. The rule takes `bs` as a witness
  -- packaging (xᵢ, vᵢ, Tᵢ) together; the name/value/type correspondence
  -- is checked by the oracle upstream and not re-checked in the rule.
  | evalSuccess {ρ ec P π xs body} {vs : List Value} {bs : List (Name × Binding)}
      (hauth   : policyAllows P π .evalA)
      (_hshape : xs.length = vs.length ∧ vs.length = bs.length)
      (hrt     : ∀ (x : Name) (b : Binding), (x, b) ∈ bs → RtType ρ b.value b.ty)
      (hfr     : Env.freshAll ρ bs) :
      Step O
        ⟨ρ, ec, P, π, .evalE (.valE (.vClos xs body)) (vs.map .valE)⟩
        ⟨Env.extendAll ρ bs, ec, P, π, body⟩

  | evalHealType {ρ ec P π xs body} {vs : List Value}
      (_hbad   : ¬ ∃ bs : List (Name × Binding),
                      ∀ (x : Name) (b : Binding), (x, b) ∈ bs →
                        RtType ρ b.value b.ty)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explainType (.vClos xs body) .tUnit)]) ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .evalE (.valE (.vClos xs body)) (vs.map .valE)⟩
        ⟨ρ, ec ++ [Event.error (explainType (.vClos xs body) .tUnit)], P, π,
         .evalE (.valE (.vClos xs body)) (vs.map .valE)⟩

  | evalHealPol {ρ ec P π e args}
      (_hdeny  : ¬ policyAllows P π .evalA)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explainPolicy π P)]) ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .evalE e args⟩
        ⟨ρ, ec ++ [Event.error (explainPolicy π P)], P, π, .evalE e args⟩

  -- L2: Gen-Budget-Exhausted. When the trailing error-run exceeds the
  -- retry budget, reduction stops at a terminal error marker carrying
  -- the full event log and the failing gen expression for blame.
  | genBudgetExhausted {ρ ec P π τ s}
      (_hover : ErrCtx.retries ec > retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .gen τ s none⟩
        ⟨ρ, ec, P, π, .errTerm ec (.gen τ s none)⟩

  -- L3: Enforce-Heal. When `policyInstall` is undefined for the policy
  -- value bound to `x`, append the explanation to ε and rewrite the redex
  -- back to a gen of Tpolicy using the implementation-supplied prompt.
  | enforceHeal {ρ ec P π x p b}
      (hb     : Env.lookup ρ x = some b)
      (hpol   : b.value = .vPol p)
      (hty    : b.ty = .tPolicy)
      (_hbad  : policyInstall P p = none)
      (hbudget : ErrCtx.retries (ec ++ [Event.error (explainPolicy π P)]) ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .enforce x⟩
        ⟨ρ, ec ++ [Event.error (explainPolicy π P)], P, π, .gen .tPolicy (provPrompt ρ x) none⟩

  -- CBV left-to-right congruence rules.
  -- These replace the evaluation contexts E[·] / Extract defunctionalisation
  -- of earlier drafts: the next redex is always in the leftmost scoring
  -- position, and congruence reduces under that position.  The `hne`
  -- side condition forbids propagation of the `errTerm` terminal marker
  -- through a congruence — a sub-expression that has reached `errTerm`
  -- stalls the whole program, matching the paper's trace-level fail-fast
  -- semantics.

  | letCong {ρ ρ' ec ec' P P' π π' m x τ e₁ e₁' e₂}
      (h   : Step O ⟨ρ, ec, P, π, e₁⟩ ⟨ρ', ec', P', π', e₁'⟩)
      (hne : ¬ (Config.isErr ⟨ρ', ec', P', π', e₁'⟩)) :
      Step O
        ⟨ρ, ec, P, π, .letE m x τ e₁ e₂⟩
        ⟨ρ', ec', P', π', .letE m x τ e₁' e₂⟩

  | assignCong {ρ ρ' ec ec' P P' π π' x e₁ e₁'}
      (h   : Step O ⟨ρ, ec, P, π, e₁⟩ ⟨ρ', ec', P', π', e₁'⟩)
      (hne : ¬ (Config.isErr ⟨ρ', ec', P', π', e₁'⟩)) :
      Step O
        ⟨ρ, ec, P, π, .assign x e₁⟩
        ⟨ρ', ec', P', π', .assign x e₁'⟩

  | ifCong {ρ ρ' ec ec' P P' π π' e₁ e₁' e₂ e₃}
      (h   : Step O ⟨ρ, ec, P, π, e₁⟩ ⟨ρ', ec', P', π', e₁'⟩)
      (hne : ¬ (Config.isErr ⟨ρ', ec', P', π', e₁'⟩)) :
      Step O
        ⟨ρ, ec, P, π, .ifE e₁ e₂ e₃⟩
        ⟨ρ', ec', P', π', .ifE e₁' e₂ e₃⟩

  | seqCong {ρ ρ' ec ec' P P' π π' e₁ e₁' e₂}
      (h   : Step O ⟨ρ, ec, P, π, e₁⟩ ⟨ρ', ec', P', π', e₁'⟩)
      (hne : ¬ (Config.isErr ⟨ρ', ec', P', π', e₁'⟩)) :
      Step O
        ⟨ρ, ec, P, π, .seq e₁ e₂⟩
        ⟨ρ', ec', P', π', .seq e₁' e₂⟩

  | forCong {ρ ρ' ec ec' P P' π π' x e₁ e₁' e₂}
      (h   : Step O ⟨ρ, ec, P, π, e₁⟩ ⟨ρ', ec', P', π', e₁'⟩)
      (hne : ¬ (Config.isErr ⟨ρ', ec', P', π', e₁'⟩)) :
      Step O
        ⟨ρ, ec, P, π, .forE x e₁ e₂⟩
        ⟨ρ', ec', P', π', .forE x e₁' e₂⟩

inductive Steps (O : Oracle) : Config → Config → Prop where
  | refl {C} : Steps O C C
  | step {C C' C''} : Step O C C' → Steps O C' C'' → Steps O C C''

end HADL
