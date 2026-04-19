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

opaque freshLabel (ρ : Env) (e : Expr) : Label
opaque explainType   : Value → Ty → String
opaque explainPolicy : Principal → Policy → String

/--
  Small-step relation `C ⟶ C'`, parameterized by an oracle `O`.
  We use `ec` for the heal-context component (paper's `Σ`).
-/
inductive Step (O : Oracle) : Config → Config → Prop where
  | var {ρ ec P π x v b}
      (h : Env.lookup ρ x = some b)
      (hv : b.value = v) :
      Step O ⟨ρ, ec, P, π, .var x⟩ ⟨ρ, ec, P, π, .valE v⟩

  | letBind {ρ ec P π m x τ v}
      (hrt : RtType ρ v τ)
      (hfr : Env.fresh ρ x) :
      Step O
        ⟨ρ, ec, P, π, .letE m x τ (.valE v) .unit⟩
        ⟨Env.extend ρ x ⟨v, τ, none, m⟩, [], P, π, .unit⟩

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
        ⟨Env.extend ρ x ⟨v, τ, none, .letBind⟩, ec, P, π,
         .seq e (.forE x (.valE (.vArr vs)) e)⟩

  | seqStep {ρ ec P π v e} :
      Step O
        ⟨ρ, ec, P, π, .seq (.valE v) e⟩
        ⟨ρ, ec, P, π, e⟩

  | jsStep {ρ ec P π je v}
      (h : jsEval je ρ = some v) :
      Step O ⟨ρ, ec, P, π, .js je⟩ ⟨ρ, ec, P, π, .valE v⟩

  | genSuccess {ρ ec P π τ s v ℓ}
      (hauth  : policyAllows P π .gen)
      (horacle : O s ec τ v)
      (hrt    : RtType ρ v τ)
      (hstage : StType
                  (Env.proj (Env.extend ρ (toString ℓ) ⟨v, τ, some ℓ, .letBind⟩))
                  (.valE v)
                  τ)
      (hfresh : ℓ = freshLabel ρ (.gen τ s none))
      (hfr    : Env.fresh ρ (toString ℓ)) :
      Step O
        ⟨ρ, ec, P, π, .gen τ s none⟩
        ⟨Env.extend ρ (toString ℓ) ⟨v, τ, some ℓ, .letBind⟩,
         [], P, π, .valE v⟩

  | genHealType {ρ ec P π τ s v}
      (horacle : O s ec τ v)
      (hbad    : ¬ RtType ρ v τ)
      (hbudget : (ec ++ [explainType v τ]).length ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .gen τ s none⟩
        ⟨ρ, ec ++ [explainType v τ], P, π, .gen τ s none⟩

  | genHealPol {ρ ec P π τ s}
      (hdeny   : ¬ policyAllows P π .gen)
      (hbudget : (ec ++ [explainPolicy π P]).length ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .gen τ s none⟩
        ⟨ρ, ec ++ [explainPolicy π P], P, π, .gen τ s none⟩

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
        ⟨ρ, [], P, π, .valE v⟩

  | sayStep {ρ ec P π s} :
      Step O
        ⟨ρ, ec, P, π, .say s⟩
        ⟨ρ, ec, P, π, .unit⟩

  -- L2: Agent family. Agent-Success mirrors Gen-Success but inlines the
  -- returned value rather than binding it, flushing the err-context.
  | agentSuccess {ρ ec P π τ s pr v}
      (hauth   : policyAllows P π .agent)
      (horacle : O s ec τ v)
      (hrt     : RtType ρ v τ) :
      Step O
        ⟨ρ, ec, P, π, .agent τ s pr⟩
        ⟨ρ, [], P, π, .valE v⟩

  | agentHealType {ρ ec P π τ s pr v}
      (horacle : O s ec τ v)
      (hbad    : ¬ RtType ρ v τ)
      (hbudget : (ec ++ [explainType v τ]).length ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .agent τ s pr⟩
        ⟨ρ, ec ++ [explainType v τ], P, π, .agent τ s pr⟩

  | agentHealPol {ρ ec P π τ s pr}
      (hdeny   : ¬ policyAllows P π .agent)
      (hbudget : (ec ++ [explainPolicy π P]).length ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .agent τ s pr⟩
        ⟨ρ, ec ++ [explainPolicy π P], P, π, .agent τ s pr⟩

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
      (hbudget : (ec ++ [explainType (.vClos xs body) .tUnit]).length ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .evalE (.valE (.vClos xs body)) (vs.map .valE)⟩
        ⟨ρ, ec ++ [explainType (.vClos xs body) .tUnit], P, π,
         .evalE (.valE (.vClos xs body)) (vs.map .valE)⟩

  | evalHealPol {ρ ec P π e args}
      (_hdeny  : ¬ policyAllows P π .evalA)
      (hbudget : (ec ++ [explainPolicy π P]).length ≤ retryBudget) :
      Step O
        ⟨ρ, ec, P, π, .evalE e args⟩
        ⟨ρ, ec ++ [explainPolicy π P], P, π, .evalE e args⟩

inductive Steps (O : Oracle) : Config → Config → Prop where
  | refl {C} : Steps O C C
  | step {C C' C''} : Step O C C' → Steps O C' C'' → Steps O C C''

end HADL
