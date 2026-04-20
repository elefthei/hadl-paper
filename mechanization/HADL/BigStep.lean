-- Extract-based small-step reduction.
--
-- `PureStep`/`PureSteps` (defined in `Reduction.lean`) is the pure-core
-- relation — the set of root-level reduction rules for L1/L2/L3
-- without any congruence closure.  On its own `PureStep` does *not*
-- reduce under `letE`, `seq`, `ifE`-guard, etc.; those contexts are
-- instead handled by `Extract` (see `Extract.lean`), which peels the
-- leftmost oracle head out of an expression into a triple
-- `(pre, x, suf)` where `pre` is the head, `x` a fresh continuation
-- binder, and `suf` the continuation under `x`.
--
-- This module assembles the paper's top-level small-step relation
-- (`Step` under `E[·]`) directly as an inductive with two cases:
--
--   * `pure`:  `Extract e = none`         → delegate to `PureStep`
--   * `run` :  `Extract e = some (pre,x,suf)` → reduce `pre` via a
--              single `PureStep` to `.valE v`, extend the resulting
--              env with `x ↦ v`, and continue with `suf`.
--
-- No separate `GStep` relation; this `Step` is *the* operational
-- semantics used by all safety theorems.

import HADL.Reduction
import HADL.Extract
import HADL.ExtractShape

namespace HADL

/-- Top-level small-step reduction.  Mechanises the paper's
    `Step` under evaluation contexts `E[·]` via the `Extract`
    defunctionalisation. -/
inductive Step (O : Oracle) : Config → Config → Prop where
  | pure {C C'}
      (hnone : Extract C.expr = none)
      (hstep : PureStep O C C')
      : Step O C C'
  | run {ρ ec P π e' env' err' pol' princ' pre x suf v τ τ'}
      (hext  : Extract e' = some (pre, x, suf))
      (hpre  : PureStep O ⟨ρ, ec, P, π, pre⟩
                           ⟨env', err', pol', princ', .valE v⟩)
      (hrt   : RtType env' v τ)
      (hfr   : Env.fresh env' x)
      (hrestage :
        StType
          (Env.proj (Env.extend env' x ⟨v, τ, .letBind⟩))
          suf τ')
      : Step O ⟨ρ, ec, P, π, e'⟩
          ⟨Env.extend env' x ⟨v, τ, .letBind⟩,
           err', pol', princ', suf⟩

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps (O : Oracle) : Config → Config → Prop where
  | refl {C} : Steps O C C
  | step {C C' C''} : Step O C C' → Steps O C' C'' → Steps O C C''

end HADL
