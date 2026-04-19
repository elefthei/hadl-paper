# HADL Mechanization

Lean 4 formalization of the HADL operational semantics from §4 of the paper.

## Status

| Theorem | Clause | Status |
|---|---|---|
| `thm:hadl-sound` | T1 WF-Preservation | 🚧 in progress |
| `thm:hadl-sound` | T2 Staged Materialization Soundness | 🚧 in progress |
| `thm:hadl-sound` | T3 Policy Monotonicity | 🚧 in progress |
| `thm:hadl-sound` | T4 Oracle-Relative Safety | 📄 paper only |

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

Beyond standard `Classical`/choice, this development declares:

- `jsEval`, `jsEval_wellTyped` (axiomatize the opaque JavaScript interop layer)
- possibly `install_allows_shrink` (if Cedar-level monotonicity of policy install cannot be discharged directly against `cedar-lean`'s `isAuthorized`)

See `HADL/JsAxioms.lean` and `HADL/Policy.lean` for the full statements.

## File layout

```
HADL/
├── Syntax.lean       types, expressions, values, evaluation contexts
├── Env.lean          typed environment + projection Γ(ρ)
├── Typing.lean       static and runtime typing judgments
├── Policy.lean       Cedar-Lean wrapper (allows, install, allowSet)
├── Oracle.lean       nondeterministic oracle relation
├── JsAxioms.lean     axiomatic jsEval
├── Config.lean       five-tuple configuration + WF predicate
├── Reduction.lean    small-step relation (L1 core / L2 gen / L3 policy)
├── Lemmas.lean       env-extension, weakening, policy-shrinkage, …
└── Soundness.lean    T1 / T2 / T3 theorems
```
