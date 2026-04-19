# The Command Language over the Multiset Monad `MS`, written with Kleene `+`

| Document Metadata      | Details                                          |
| ---------------------- | ------------------------------------------------ |
| Author                 | Lef Ioannidis                                    |
| Source                 | Zilberstein, Saxena, Silva, Féret, Majumdar —    |
|                        | *Outcome Logic*, arXiv:2303.03111v2, §3          |
| Status                 | Formal note                                      |
| Created                | 2026‑04‑19                                       |

## 1. Purpose

Section 3 of the paper defines a **Command Language** whose denotational
semantics is parametric over

1. a monad `⟨M, bind, unit⟩` (for `1` and sequencing `⨟`), and
2. a partial commutative monoid (PCM) `⟨MΣ, ⋄, 0⟩` (for choice `+` and
   iteration `C⋆`).

In the paper the PCM operation is printed as `⋄` (the macro
`\monoid = \diamond`). In this note we **rename `⋄` to additive `+`**
— the standard *Kleene‑algebra sum* — and we fix the monad to be the
**multiset monad `MS`**, which is one of the canonical execution models
of §3 (it is the `W_Nat` instance of the semiring model used in the
TOPLAS‑loops follow‑up, and it validates all PCM axioms totally).

Atomic commands are taken to be exactly those of Example 3.6 (GCL):
`assume e` and `x := e`.

## 2. The multiset monad `MS`

Let `ℕ∞ = ℕ ∪ {∞}`. For a set `A` define

```
MS A  =  { μ : A → ℕ∞ | supp(μ) is at most countable }
```

i.e. the set of `ℕ∞`‑valued multisets over `A`. Elements `μ ∈ MS A`
count, for each `a ∈ A`, how many computation traces land on `a`.

**Monad structure** `⟨MS, bind, unit⟩`:

* `unit : A → MS A`,    `unit(a) = [a ↦ 1]`  (the singleton multiset).
* `bind : MS A × (A → MS B) → MS B`,
  `bind(μ, f)(b) = Σ_{a ∈ A} μ(a) · f(a)(b)`.

The three monad laws hold pointwise in `ℕ∞`.

**PCM structure on `MS Σ`**, written additively:

* `+  : MS Σ × MS Σ → MS Σ`,    `(μ₁ + μ₂)(σ) = μ₁(σ) + μ₂(σ)`.
* `0  : MS Σ`,                  `0(σ) = 0` for every `σ`
  (the empty multiset).

This `+` is total (so the semantics will be total — cf. App. A of the
paper), commutative, associative, and has unit `0`. Moreover it
**preserves `bind`**, matching Def. 3.3 (Execution Model):

```
bind(μ₁ + μ₂, k)  =  bind(μ₁, k) + bind(μ₂, k)
bind(0, k)        =  0
```

So `⟨MS, bind, unit, +, 0⟩` is an execution model in the sense of the
paper, and we have renamed `⋄ ↦ +`.

### Notational warning

The symbol `+` already appears in the **syntax** of the language as
non‑deterministic choice `C₁ + C₂`. This overloading is intentional
and standard (Kleene algebra): the denotation of syntactic `+` on
commands is exactly the semantic PCM `+` on multisets. Where
disambiguation matters below, we write `+_MS` for the semantic monoid.

## 3. Syntax

```
C  ::=  0                         -- divergence / empty computation
     |  1                         -- skip
     |  C₁ ⨟ C₂                   -- sequential composition
     |  C₁ + C₂                   -- non-deterministic choice
     |  C⋆                        -- Kleene iteration
     |  c                         -- atomic command

c  ::=  assume e                  -- filter by Boolean expression
     |  x := e                    -- variable assignment
```

with `x ∈ Var`, `e ∈ Exp`. Program states are stacks
`Σ = S = { s : Var → Val }` with `Val = ℤ ⊎ 𝔹`, and expression
evaluation is `⟦ e ⟧_Exp : S → Val`.

We keep the usual sugar of Example 3.6:

```
if e then C₁ else C₂  =  (assume e ⨟ C₁) + (assume ¬e ⨟ C₂)
while e do C          =  (assume e ⨟ C)⋆ ⨟ assume ¬e
skip                  =  1
for N do C            =  C^N
C^0 = 1           C^(k+1) = C ⨟ C^k
```

## 4. Denotational semantics `⟦C⟧ : Σ → MS Σ`

Let `⟦c⟧_atom : Σ → MS Σ` be the semantics of atomic commands
(§4.1 below). The semantics of compound commands follows Fig. 3 of the
paper, with `⋄` replaced by `+`:

```
⟦ 0 ⟧(σ)         =  0                                                   -- the empty multiset
⟦ 1 ⟧(σ)         =  unit(σ)                                             =  [σ ↦ 1]
⟦ C₁ ⨟ C₂ ⟧(σ)   =  bind(⟦C₁⟧(σ), ⟦C₂⟧)
⟦ C₁ + C₂ ⟧(σ)   =  ⟦C₁⟧(σ)  +  ⟦C₂⟧(σ)                                 -- PCM sum on MS Σ
⟦ C⋆ ⟧(σ)        =  lfp (λf. λσ. f†(⟦C⟧(σ)) + unit(σ)) (σ)
⟦ c ⟧(σ)         =  ⟦c⟧_atom(σ)
```

Here `f† : MS Σ → MS Σ` is the monadic extension
`f†(μ) = bind(μ, f)`, and the least fixed point is taken in the
pointwise `≤` order on `Σ → MS Σ` inherited from the pointwise order
on `ℕ∞`. Because `MS` is ω‑cpo‑enriched and `bind` and `+` are
Scott‑continuous in each argument, the `lfp` exists and is obtained by
ω‑iteration from `λσ. 0`.

**Concrete unfolding of `C⋆`.** Writing `⟦C⟧† : MS Σ → MS Σ` for the
Kleisli lift of `⟦C⟧` and iterating the loop functional once shows the
familiar Kleene sum:

```
⟦ C⋆ ⟧(σ)  =  Σ_{n ∈ ℕ}  (⟦C⟧†)^n (unit σ)
          =  unit(σ) + ⟦C⟧(σ) + (⟦C ⨟ C⟧)(σ) + (⟦C ⨟ C ⨟ C⟧)(σ) + …
```

i.e. the multiset of all finite unrollings, exactly matching the
Kleene‑algebra law `C⋆ = 1 + C + C² + C³ + …`. This is where the
choice of `+` (rather than `⋄`) makes the connection to Kleene
algebra visible.

## 4.1 Atomic commands

```
⟦ assume e ⟧(s)  =  unit(s)        if  ⟦e⟧_Exp(s) = true
                 =  0              if  ⟦e⟧_Exp(s) = false

⟦ x := e   ⟧(s)  =  unit( s[ x ↦ ⟦e⟧_Exp(s) ] )
```

These are exactly the equations of Example 3.6, instantiated at the
multiset execution model. Note:

* `assume e` produces either a singleton multiset or the empty
  multiset `0` — so an **`assume` that fails is the PCM unit**, i.e.
  it contributes nothing to any sum. This is the key reason `if` /
  `while` desugaring works: unreachable branches become `0`.
* `x := e` is total and deterministic: the result is a singleton
  multiset.

## 5. Summary of the rename `⋄ ↦ +`

| Paper (§3)        | This note            | Reading                          |
| ----------------- | -------------------- | -------------------------------- |
| `⋄`    (`\monoid`)| `+`                  | Kleene‑algebra sum / PCM join    |
| `1` (PCM unit)    | `0`                  | empty multiset, additive unit    |
| `⋄` preserves `bind` | `+` preserves `bind` | distributivity of `;` over `+` |
| `⟦C⋆⟧ = lfp(λf. f† ∘ ⟦C⟧ ⋄ unit)` | `lfp(λf. f† ∘ ⟦C⟧ + unit)` | `C⋆ = 1 + C ⨟ C⋆` |

All laws, proof rules, and totality arguments of §3 carry over
verbatim under this renaming; the execution model
`⟨MS, bind, unit, +, 0⟩` is a total PCM, so the semantics
`⟦·⟧ : Σ → MS Σ` is a total function for every program `C`.

## 6. References

* Zilberstein, Saxena, Silva, Féret, Majumdar.
  *Outcome Logic: A Unifying Foundation for Correctness and
  Incorrectness Reasoning.* arXiv:2303.03111v2, §3 (A Modular
  Programming Language), Fig. 3, Example 3.6.
* Zilberstein et al., *Outcome Logic with Semiring Weightings*
  (TOPLAS‑loops, arXiv:2401.04594v3), Ex. `multisetsemi` — the `Nat`
  semiring instance giving the multiset monad model used here.

