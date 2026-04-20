# HADL Mechanization

Lean 4 formalization of the HADL operational semantics from §4 of the paper.

## Status

| Theorem | Clause | Status |
|---|---|---|
| `thm:hadl-sound` | T1 WF-Preservation | ✅ proven (all §4 + appendix A rules) |
| `thm:hadl-sound` | T2 Staged Materialization Soundness | ✅ proven |
| `thm:hadl-sound` | T3 Policy Monotonicity | ✅ proven |
| `thm:hadl-sound` | T4a Budget Progress | ✅ proven (`Safety.lean`) |
| `thm:hadl-sound` | T4b Truthful Gen-Success | ✅ proven (`Safety.lean`) |
| `thm:hadl-sound` | T4c gen-case trace progress | ✅ proven (`Safety2.lean`, via congruence rules) |
| `thm:hadl-sound` | T4c agent-case trace progress | ✅ proven (`Safety2.lean`, symmetric to gen) |
| `thm:hadl-sound` | T4c pure-core termination | ⏳ argued only on paper |

All mechanized theorems are free of `sorry`. `#print axioms` reports only
Lean's standard meta-axioms:

```
T1_WF_preservation              : [propext, Classical.choice, Quot.sound]
T2_staged_materialization       : (none)
T3_policy_monotonicity          : [propext, Classical.choice, Quot.sound]
T4_budget_progress              : [propext, Classical.choice, Quot.sound]
T4_truthful_success             : [propext, Classical.choice, Quot.sound]
T4_truthful_success_agent       : [propext, Classical.choice, Quot.sound]
T4_progress_gen                 : [propext, Classical.choice, Quot.sound]
T4_progress_agent               : [propext, Classical.choice, Quot.sound]
policyInstall_shrinks           : [propext, Classical.choice, Quot.sound]
```

No user-introduced axioms. `policyInstall_shrinks` is proved by iterating
Cedar-Lean's `Cedar.Thm.unchanged_deny_when_add_forbid`.

### T4 scope note

T4 is fully mechanized except for the pure-core termination measure
(clause T4c, last sentence). Specifically:

* **T4a Budget progress** (`Safety.lean`) — once `retries(Σ) > retryBudget`,
  `genBudgetExhausted` fires deterministically. (Stated at the root over
  the unified small-step `Step`.)
* **T4b Truthful gen-success** (`Safety.lean`) — an *eventually-truthful*
  oracle at an authorized policy yields an `ε`, `v`, and a
  `Step.genSuccess` firing, resetting the retry counter.  An
  analogous agent-side lemma (`T4_truthful_success_agent`) is proved in
  `Safety2.lean`.
* **T4c gen & agent trace progress** (`Safety2.lean`) — if an expression
  `e` has a reachable gen/agent head at its leftmost CBV position
  (predicate `HasLeftGen` / `HasLeftAgent`), there is a `Step`
  transition from the config, under the eventually-truthful oracle.
  The lift from root-level to arbitrary evaluation position is carried
  by the congruence rules `letCong` / `assignCong` / `ifCong` /
  `seqCong` / `forCong` baked directly into `Step`; no evaluation-
  context machinery is required.
* **T4c pure-core termination** — the only paper-level gap.  Requires a
  well-founded measure on gen/agent/ask-free configurations plus a
  `While` termination hypothesis on the source program.  The paper's
  footnote at Theorem "hadl-sound" defers this; the mechanization follows.

### Operational relation

A single inductive relation `Step` (`Reduction.lean`) defines the
paper's reduction: root-level pure-core rules (Var, Let-Bind, Assign,
If, While-unfold, For, Seq, Js, Ask, Say, Gen-Success, Gen-Heal-*,
Agent-*, Eval-*, Enforce-*, Gen-Budget-Exhausted) together with five
CBV left-to-right congruence rules (`letCong`, `assignCong`, `ifCong`,
`seqCong`, `forCong`).  Each congruence rule carries a side condition
`¬ Config.isErr ⟨…⟩` on its inner step so that a stalled `errTerm`
successor does not re-enter reduction by being lifted under a
constructor.  This replaces the paper's `E[·]` evaluation-context
notation with an equivalent but more mechanically tractable explicit
congruence closure.

### Mechanized rule coverage

`Step` covers every rule in `semantics.tex` §4 and `appendix.tex` §A:

* **L1 core:** Var, Let-Bind, Assign, If-True/False, While (unfold), For-Nil/Cons, Seq, Js.
* **L1/L2 I/O:** Ask, Say.
* **L2 agent:** Agent-Success, Agent-Heal-Type, Agent-Heal-Pol.
* **L2 eval:** Eval-Success, Eval-Heal-Type, Eval-Heal-Pol.
* **L2 gen:** Gen-Success, Gen-Heal-Type, Gen-Heal-Pol, Gen-Budget-Exhausted.
* **L3 policy:** Enforce-Install, Enforce-Heal.
* **CBV congruence:** letCong, assignCong, ifCong, seqCong, forCong
  (each with a `¬ Config.isErr` side condition on the inner step).


## Build

```bash
cd mechanization
lake update
lake build
```

First build is long: Mathlib + Cedar-Lean transitive compilation (~30-60 min on a cold cache).

## Dependencies

- Lean 4 `v4.29.0` (pinned to match Cedar-Lean)
- `batteries` `v4.29.0`
- `mathlib` `v4.29.0`
- `Cedar` from `cedar-policy/cedar-spec` (subdirectory `cedar-lean`)

## Axioms

Beyond Lean's standard meta-axioms (`propext`, `Classical.choice`,
`Quot.sound`), this development declares **no** free axioms. The
opaque constants below are *declared functions* (no body), not axioms,
and do not appear in `#print axioms`:

- `parsePolicies` (`HADL/Policy.lean`): opaque Cedar policy parser —
  the implementation is delegated to the host; install-time shrinkage
  is proved from Cedar-Lean regardless of what the parser returns.
- `jsEval` (`HADL/JsAxioms.lean`): stubbed to `fun _ _ => none`; the
  associated well-typedness lemma is then vacuously true.
- `explainType`, `explainPolicy`, `provPrompt` (`HADL/Reduction.lean`):
  implementation-supplied diagnostics — their content never enters any
  safety theorem.
- `JsExprNE` (`HADL/Syntax.lean`): nonemptiness carrier for the JS
  expression syntax (the actual AST is host-supplied).

## File layout

```
HADL/
├── Syntax.lean       types, expressions, values, events
├── Env.lean          typed environment + projection Γ(ρ)
├── Typing.lean       static and runtime typing judgments
├── Policy.lean       Cedar-Lean wrapper: Policy = Cedar.Spec.Policies
├── Oracle.lean       nondeterministic oracle relation
├── JsAxioms.lean     stubbed jsEval (host-delegated)
├── Config.lean       five-tuple configuration + WF + isErr predicates
├── Reduction.lean    unified small-step `Step`: root-level L1/L2/L3 rules + CBV congruences
├── Lemmas.lean       env-extension, weakening, policy-shrinkage, …
├── Soundness.lean    T1 / T2 / T3 theorems
├── Safety.lean       T4a, T4b (gen-local at root over `Step`)
└── Safety2.lean      T4c trace progress (gen + agent, via congruence rules)
```
