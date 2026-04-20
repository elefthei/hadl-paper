-- `GStep`: the "gen-step" relation.  One step of `GStep` either:
-- • runs a pure-core step when `Extract` finds no oracle head (delegating
--   to the existing `Step` relation), or
-- • runs exactly one reduction of the leftmost oracle head returned by
--   `Extract`, then binds the result in the environment under the fresh
--   continuation variable and resumes on the extracted suffix.
--
-- This replaces the `E[·]` congruence closure that the existing `Step` was
-- missing.  Because binding is via env-extension (rather than substitution),
-- `GStep` composes cleanly with the rest of the mechanization.

import HADL.Reduction
import HADL.Extract
import HADL.ExtractShape

namespace HADL

/--
  `GStep O C C'` — one extract-based reduction step of the machine under
  oracle `O`.

  * `pure`:  `Extract C.expr = none` ⇒ delegate to the existing pure-core
    `Step`.  The config evolves exactly as in the small-step semantics.
  * `run`:   `Extract C.expr = some (pre, x, suf)` ⇒ reduce the oracle head
    `pre` using a single `Step` transition to `⟨env', err', pol', princ',
    .valE v⟩`.  Extend `env'` with `x ↦ v` at some runtime-witnessed type
    `τ`, then continue with the suffix `suf`.  Binding-by-env-extension
    means the fresh continuation variable `x`'s uses inside `suf` are
    resolved by the existing `Step.var` rule — no substitution is needed.
-/
inductive GStep (O : Oracle) : Config → Config → Prop where
  | pure {C C'}
      (hnone : Extract C.expr = none)
      (hstep : Step O C C')
      : GStep O C C'
  | run {ρ ec P π e' env' err' pol' princ' pre x suf v τ}
      (hext  : Extract e' = some (pre, x, suf))
      (hpre  : Step O ⟨ρ, ec, P, π, pre⟩
                      ⟨env', err', pol', princ', .valE v⟩)
      (hrt   : RtType env' v τ)
      (hfr   : Env.fresh env' x)
      : GStep O ⟨ρ, ec, P, π, e'⟩
          ⟨Env.extend env' x ⟨v, τ, .letBind⟩,
           err', pol', princ', suf⟩

/-- Reflexive-transitive closure of `GStep`. -/
inductive GSteps (O : Oracle) : Config → Config → Prop where
  | refl {C} : GSteps O C C
  | step {C C' C''} : GStep O C C' → GSteps O C' C'' → GSteps O C C''

end HADL
