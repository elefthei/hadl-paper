# HADL Mechanization

Lean 4 formalization of the HADL operational semantics from §4 of the paper.

## Status

| Theorem | Clause | Status |
|---|---|---|
| `thm:hadl-sound` | T1 WF-Preservation | ✅ proven |
| `thm:hadl-sound` | T2 Staged Materialization Soundness | ✅ proven |
| `thm:hadl-sound` | T3 Policy Monotonicity | ✅ proven |
| `thm:hadl-sound` | T4 Oracle-Relative Safety | 📄 paper only |

All three mechanized theorems are free of `sorry`. `#print axioms` reports:

```
T1_WF_preservation        : [propext, jsEval]
T2_staged_materialization : (none)
T3_policy_monotonicity    : [jsEval, policyInstall_shrinks]
```

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

Beyond standard Lean axioms (`propext`), this development declares:

- `jsEval`, `jsEval_wellTyped` (`HADL/JsAxioms.lean`): axiomatize the opaque JavaScript interop layer.
- `policyInstall_shrinks` (`HADL/Policy.lean`): monotonicity of policy install against the Cedar `isAuthorized` allow-set. Could be discharged directly against Cedar-Lean in future work.
- Opaque constants: `PolicyNE`, `JsExprNE`, `policyAllows`, `policyInstall`, `freshLabel`, `explainType`, `explainPolicy`.

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
