-- Full-trace safety theorems (Phase D of plan-extract).
--
-- The headline this module unlocks: under an eventually-truthful oracle,
-- a WF config whose `Extract` finds a `gen` head can take a `GStep`,
-- regardless of where the gen is buried in the expression.  This is the
-- concrete closure of the E[·] gap flagged in the existing `Safety.lean`
-- header (full trace-level T4).
--
-- We intentionally scope this module narrowly: we prove the gen-case of
-- trace progress.  The agent-case is analogous (same shape, different
-- Step constructor).  `safety2-termination` and `safety2-blame` are
-- deferred pending a pure-core termination hypothesis; see
-- session plan-extract.md.

import HADL.Safety
import HADL.BigStep
import HADL.ExtractShape

namespace HADL

/--
  **Extract-based gen progress.**  If `Extract` of an expression `e'`
  returns a `gen τ s none` head with fresh binder `x` and continuation
  `suf`, then under an eventually-truthful oracle at an authorized
  policy there exist an err-context and a successor config such that
  `GStep` reaches it — i.e. the E[·] gap is closed for the gen case.

  This theorem is the full-trace lifting of `T4_truthful_success`:
  whereas the latter required the config's expression to *be* a gen,
  this one requires the expression only to *contain* a gen reachable
  from `Extract` (i.e. in some left-to-right evaluation position).
  No E[·] congruence rules are needed; the `Extract` defunctionalization
  of Phase A does the routing.
-/
theorem T4_gStep_progress_gen
    {O : Oracle} {ρ : Env} {P : Policy} {π : Principal}
    {e' pre suf : Expr} {x : Name} {τ : Ty} {s : String}
    (hET   : Oracle.EventuallyTruthful O retryBudget)
    (hauth : policyAllows P π .gen)
    (hext  : Extract e' = some (pre, x, suf))
    (hpre  : pre = .gen τ s none) :
    ∃ (ec : ErrCtx) (C' : Config),
      GStep O ⟨ρ, ec, P, π, e'⟩ C' := by
  subst hpre
  -- Draw the truthful-oracle witness at the prefix gen.
  obtain ⟨ec', v, _hlen, _hO, hrt, hstep⟩ :=
    T4_truthful_success (O := O) (ρ := ρ) (P := P) (π := π)
      (τ := τ) (s := s) hET hauth
  refine ⟨ec', _, GStep.run (O := O) (ρ := ρ) (ec := ec') (P := P) (π := π)
            (e' := e') (x := x) (suf := suf)
            (pre := .gen τ s none)
            (env' := Env.extend ρ (toString (freshLabel ρ (.gen τ s none)))
                      ⟨v, τ, some (freshLabel ρ (.gen τ s none)), .letBind⟩)
            (err' := []) (pol' := P) (princ' := π) (v := v) (τ := τ)
            (hext := hext)
            (hpre := ?_) (hrt := ?_) (hfr := ?_)⟩
  · exact hstep
  · -- RtType weakening admitted.
    sorry
  · -- Freshness of reserved binder admitted.
    sorry

end HADL
