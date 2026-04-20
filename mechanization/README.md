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
| `thm:hadl-sound` | T4c gen-case trace progress | ✅ proven (`Safety2.lean`, via Extract) |
| `thm:hadl-sound` | T4c agent-case trace progress | ✅ proven (`Safety2.lean`, clone of gen) |
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
  `genBudgetExhausted` fires deterministically. (Stated over the pure-core
  `PureStep` — gen at the root.)
* **T4b Truthful gen-success** (`Safety.lean`) — an *eventually-truthful*
  oracle at an authorized policy yields an `ε`, `v`, and a
  `PureStep.genSuccess` firing, resetting the retry counter.  An
  analogous agent-side lemma (`T4_truthful_success_agent`) is proved in
  `Safety2.lean`.
* **T4c gen & agent trace progress** (`Safety2.lean`) — if an expression
  anywhere *contains* a reachable gen/agent (via `Extract`), there is a
  `Step` transition from the config, under the eventually-truthful
  oracle.  The relation `Step` (defined in `BigStep.lean`) is the
  paper's `Step` under evaluation contexts `E[·]`, implemented via
  `Extract`'s defunctionalisation rather than an explicit congruence
  closure.  See next subsection.
* **T4c pure-core termination** — the only paper-level gap.  Requires a
  well-founded measure on gen/agent/ask-free configurations plus a
  `While` termination hypothesis on the source program.  The paper's
  footnote at Theorem "hadl-sound" defers this; the mechanization follows.

### Operational relation: `Step` vs `PureStep`

Two inductive relations live in the mechanization:

* `PureStep` (`Reduction.lean`) — the pure-core small-step relation.
  Contains exactly the root-level reduction rules for every L1/L2/L3
  constructor (Var, Let-Bind, Assign, If, While-unfold, For, Seq, Js,
  Ask, Say, Gen-Success, Gen-Heal-*, Agent-*, Eval-*, Enforce-*,
  Gen-Budget-Exhausted).  No congruence closure: `PureStep` only fires
  at the root of `C.expr`.
* `Step` (`BigStep.lean`) — the paper's top-level reduction relation.
  Defined inductively with two constructors:
    - `Step.pure`: `Extract e = none → PureStep C C' → Step C C'`
    - `Step.run`:  `Extract e = some (pre, x, suf) → PureStep` at
                    `pre` → env-extend at `x` → continue with `suf`.
  This replaces the explicit `E[·]` congruence of the paper with
  `Extract`'s defunctionalisation (`Extract.lean`), and is the relation
  that appears in the conclusions of the T4c theorems.

### Mechanized rule coverage

`PureStep` covers every rule in `semantics.tex` §4 and `appendix.tex` §A:

* **L1 core:** Var, Let-Bind, Assign, If-True/False, While (unfold), For-Nil/Cons, Seq, Js.
* **L1/L2 I/O:** Ask, Say.
* **L2 agent:** Agent-Success, Agent-Heal-Type, Agent-Heal-Pol.
* **L2 eval:** Eval-Success, Eval-Heal-Type, Eval-Heal-Pol.
* **L2 gen:** Gen-Success, Gen-Heal-Type, Gen-Heal-Pol, Gen-Budget-Exhausted.
* **L3 policy:** Enforce-Install, Enforce-Heal.

The top-level `Step` (see `BigStep.lean`) lifts `PureStep` under the
paper's evaluation contexts `E[·]` via `Extract`, so trace progress
lands directly on the paper's reduction relation.


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
├── Config.lean       five-tuple configuration + WF predicate
├── Reduction.lean    pure-core small-step relation (`PureStep`) — root-level L1/L2/L3 rules
├── Extract.lean      defunctionalized evaluation context (prefix + binder + suffix)
├── ExtractShape.lean shape lemmas on Extract
├── Hygiene.lean      reserved-name framework for Extract binders
├── BigStep.lean      top-level `Step`: `PureStep` lifted under `E[·]` via `Extract`
├── Lemmas.lean       env-extension, weakening, policy-shrinkage, …
├── Soundness.lean    T1 / T2 / T3 theorems
├── Safety.lean       T4a, T4b (gen-local)
└── Safety2.lean      T4c trace progress (gen + agent, over unified `Step`)
```
