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

inductive Steps (O : Oracle) : Config → Config → Prop where
  | refl {C} : Steps O C C
  | step {C C' C''} : Step O C C' → Steps O C' C'' → Steps O C C''

end HADL
