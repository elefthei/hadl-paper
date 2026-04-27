# HADL Mechanization

Lean 4 formalization of the HADL operational semantics from §4 of the paper.

## Status

| Theorem | Clause | Status |
|---|---|---|
| `thm:hadl-sound` | T1 WF-Preservation | ✅ proven (all mechanized rules; jsEval-using cases vacuous — see footnote) |
| `thm:hadl-sound` | T2 Staged Materialization Soundness | ✅ proven |
| `thm:hadl-sound` | T3 Policy Monotonicity | ✅ proven (explicit case enumeration) |
| `thm:hadl-sound` | T4a No-Heal-After-Budget | ✅ proven (`Safety.lean`, direct negation) |
| `thm:hadl-sound` | T4b Truthful Gen/Agent Success (root) | ✅ proven (`Safety.lean`) |
| `thm:hadl-sound` | T4c trace progress (root let-redex only) | ⚠️ mechanized at root let-redex shape only — see *T4 scope note* below |
| `thm:hadl-sound` | T4c pure-core termination | ⏳ argued only on paper |

> **jsEval footnote.** `jsEval := fun _ _ => none` is a deliberate stub
> (JavaScript semantics are out of scope). Theorem statements quantified
> over `Expr.js _` are therefore vacuously true on that fragment; this
> is intentional and called out in §"Axioms".

All mechanized theorems are free of `sorry`. `#print axioms` reports only
Lean's standard meta-axioms:

```
T1_WF_preservation              : [propext, Classical.choice, Quot.sound]
T2_staged_materialization       : [propext, Classical.choice, Quot.sound]
T3_policy_monotonicity          : [propext, Classical.choice, Quot.sound]
T4_budget_no_heal               : [propext, Classical.choice, Quot.sound]
T4_truthful_success             : [propext, Classical.choice, Quot.sound]
T4_truthful_success_arrow       : [propext, Classical.choice, Quot.sound]
T4_truthful_success_healable    : [propext, Classical.choice, Quot.sound]
T4_truthful_success_agent       : [propext, Classical.choice, Quot.sound]
T4_truthful_success_gen         : [propext, Classical.choice, Quot.sound]
T4_progress_gen                 : [propext, Classical.choice, Quot.sound]
T4_progress_agent               : [propext, Classical.choice, Quot.sound]
nested_array_of_schema_succeeds : [propext, Classical.choice, Quot.sound]
policyInstall_shrinks           : [propext, Classical.choice, Quot.sound]
```

No user-introduced axioms. `policyInstall_shrinks` is proved by iterating
Cedar-Lean's `Cedar.Thm.unchanged_deny_when_add_forbid`.

### T4 scope note

T4 is mechanized as follows:

* **T4a No-heal-after-budget** (`Safety.lean`) — once
  `retries(ec) > retryBudget`, the standalone `gen τ s pr` form has *no*
  successor configuration. Stated as the *direct negation*
  `¬ ∃ C', Step O ⟨ec, P, σ, .gen τ s pr⟩ C'`.
* **T4b Truthful gen-success** (`Safety.lean`) — an
  *eventually-truthful* oracle (existence of an err-context with bounded
  retries at which the oracle returns a well-typed authorized value)
  yields a successful step on the root let-redex
  `let _ : τ = gen τ s π ; var 0` for `τ ∈ {tSchema, tArrow _ _}`. An
  analogous agent-side lemma is proved.
* **T4c gen / agent trace progress (root only)** —
  *Mechanized at root let-redex shape only.* The statements quantify
  over configurations whose expression is exactly
  `letE τ (gen τ s π) (var 0)` or the agent analogue. Lifting to
  arbitrary CBV evaluation positions is a mechanical congruence-closure
  argument carried out in the paper, not in Lean. The `*Cong` step
  rules (`letCongNonheal`, `ifCong`, `seqCong`, `forCong`, `enforceCong`,
  `evalFunCong`, `varDeclEval`, `assignEval`, `letPrincCong`) exist
  precisely to make that lifting trivial, but no Lean theorem currently
  applies them at the call-site of T4c.
* **T4c pure-core termination** — the only paper-level gap. Requires a
  well-founded measure on gen/agent/ask-free configurations plus a
  `While` termination hypothesis. The paper's footnote at
  Theorem "hadl-sound" defers this; the mechanization follows.

### Operational relation

A single inductive relation `Step` (`Reduction.lean`) defines the
paper's reduction: root-level pure-core rules (Let-Bind, If-True/False,
While-unfold, For-Nil/Cons, Seq, Js, Ask, Say) and L2/L3 rules
(Agent-Success, Agent-Heal-Pol; Eval-Success; Gen-Success-{Schema,Arrow,Nonheal},
Gen-Heal-{Schema,Arrow,Pol}, Gen-Type-Error, Gen-Budget-Error;
Enforce-Install; Var-Decl-Bind, Var-Decl-Eval, Assign-Write,
Assign-Eval, Var-Read; Let-Princ-Value), together with CBV
left-to-right congruence rules (`letCongNonheal`, `letPrincCong`,
`ifCong`, `seqCong`, `forCong`, `enforceCong`, `evalFunCong`,
`varDeclEval`, `assignEval`). Variable resolution is handled by
substitution inside `letBind` (de Bruijn `instantiate`) and by
`varReadStep` for mutable bindings; there is no separate paper-style
`Var` rule. This presentation is equivalent to the paper's `E[·]`
evaluation-context notation.

### Mechanized rule coverage

`Step` covers the rules in `semantics.tex` §4 and `appendix.tex` §A
that fall within the mechanized fragment:

* **L1 core:** Let-Bind, If-True/False, While (unfold), For-Nil/Cons, Seq, Js,
  Var-Decl-Bind, Var-Decl-Eval, Assign-Write, Assign-Eval, Var-Read.
* **L1/L2 I/O:** Ask, Say.
* **L2 agent:** Agent-Success, Agent-Heal-Pol.
* **L2 eval:** Eval-Success.
* **L2 gen (let-redex form):** Gen-Success-Nonheal/Schema/Arrow/**Healable**,
  Gen-Heal-Schema/Arrow/**Healable**/Pol, Gen-Type-Error, Gen-Budget-Error.
* **L3 policy:** Enforce-Install, Let-Princ-Value.
* **CBV congruence:** letCongNonheal, letPrincCong, ifCong, seqCong,
  forCong, enforceCong, evalFunCong, varDeclEval, assignEval.

**Not mechanized** (deferred to future work, called out in `appendix.tex`
"Limitations"):

* `Eval-Heal-Type`, `Eval-Heal-Pol` — eval rules currently model only
  the success path.
* `Agent-Heal-Type` — agent rules currently model only success and
  policy-heal.
* `Enforce-Heal` — only the install path is modeled.
* The `Policy` materialization triad (gen at type `tPolicy`).
* Healing of records / arrays — **partially mechanized.** The parametric
  `letGenSuccessHealable` / `letGenHealHealable` rules cover any healable
  τ (including `tArray T` and `tRecord fs` per the recursive `Ty.healable`
  definition matching `appendix.tex` §"Healable"). See
  `nested_array_of_schema_succeeds` for the canonical `Array[crf]` case
  from the clinical_trial example. The strong typing witnesses for
  record / array values use the per-field/per-element constructors
  `RtType.vRec` / `RtType.vArr`; weak fallbacks `vRecWeak` / `vArrWeak`
  remain available for `value_typeable` (T2) coverage of mid-reduction
  values without known field types.

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
  associated well-typedness lemma is then vacuously true. Theorems
  quantified over `Expr.js _` are vacuously true on that fragment;
  this is intentional (JS semantics are out of scope).
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
├── Oracle.lean       nondeterministic oracle relation + eventually-truthful
├── JsAxioms.lean     stubbed jsEval (host-delegated)
├── Config.lean       four-tuple configuration ⟨err, pol, store, expr⟩ + WF
├── Reduction.lean    unified small-step `Step`: root-level L1/L2/L3 rules + CBV congruences
├── Lemmas.lean       env-extension, weakening, policy-shrinkage, …
├── Soundness.lean    T1 / T2 / T3 theorems
├── Safety.lean       T4a, T4b (gen-local at root over `Step`)
```
