-- Structural shape lemmas for `Extract`.
-- Proofs use `fun_induction` on `Extract` (functional induction on the
-- recursive structure of the definition), which sidesteps the
-- mutually-inductive `Expr`/`Value` problem that `induction` has.

import HADL.Extract

namespace HADL

/-- Is `e` syntactically an oracle head (gen, agent, or ask)?  `Extract` only
    recognizes these three; `.evalE` is deferred. -/
def Expr.isOracleHead : Expr → Bool
  | .gen   _ _ _ => true
  | .agent _ _ _ => true
  | .ask   _     => true
  | _            => false

namespace Extract

/-- When `Extract e` succeeds, the returned `pre` is syntactically an oracle
    head.  The proof splits on each structural case of `Extract`; the
    non-extracting catch-all (values, literals, js, say, enforce, evalE,
    errTerm, …) returns `none` so the hypothesis is vacuous. -/
theorem head_is_oracle :
    ∀ e pre x suf, Extract e = some (pre, x, suf) → pre.isOracleHead = true := by
  intro e
  fun_induction Extract e with
  | case1 τ s π =>
      intro pre x suf h
      simp at h
      rcases h with ⟨rfl, _, _⟩
      rfl
  | case2 τ s π =>
      intro pre x suf h
      simp at h
      rcases h with ⟨rfl, _, _⟩
      rfl
  | case3 s =>
      intro pre x suf h
      simp at h
      rcases h with ⟨rfl, _, _⟩
      rfl
  | case4 m y τ e₁ e₂ ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, _, _⟩ := h
      exact ih a a1 b hp
  | case5 y e₁ ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, _, _⟩ := h
      exact ih a a1 b hp
  | case6 ec e₁ e₂ ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, _, _⟩ := h
      exact ih a a1 b hp
  | case7 ec e ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, _, _⟩ := h
      exact ih a a1 b hp
  | case8 y e₁ e₂ ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, _, _⟩ := h
      exact ih a a1 b hp
  | case9 e₁ e₂ ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, _, _⟩ := h
      exact ih a a1 b hp
  | case10 t _ _ _ _ _ _ _ _ _ =>
      intro pre x suf h
      -- Catch-all branch: `Extract t = none`, no success case.
      simp at h

/-- The continuation binder chosen by `Extract` is always one of the three
    reserved fresh names.  Under a hygiene precondition on source programs
    (names with prefix `__ex_` are reserved), this implies `x ∉ FV e`. -/
theorem binder_is_reserved :
    ∀ e pre x suf,
      Extract e = some (pre, x, suf) →
      x = Extract.freshGen ∨ x = Extract.freshAgent ∨ x = Extract.freshAsk := by
  intro e
  fun_induction Extract e with
  | case1 τ s π =>
      intro pre x suf h
      simp at h
      rcases h with ⟨_, rfl, _⟩
      exact Or.inl rfl
  | case2 τ s π =>
      intro pre x suf h
      simp at h
      rcases h with ⟨_, rfl, _⟩
      exact Or.inr (Or.inl rfl)
  | case3 s =>
      intro pre x suf h
      simp at h
      rcases h with ⟨_, rfl, _⟩
      exact Or.inr (Or.inr rfl)
  | case4 m y τ e₁ e₂ ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, rfl, _⟩ := h
      exact ih a a1 b hp
  | case5 y e₁ ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, rfl, _⟩ := h
      exact ih a a1 b hp
  | case6 ec e₁ e₂ ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, rfl, _⟩ := h
      exact ih a a1 b hp
  | case7 ec e ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, rfl, _⟩ := h
      exact ih a a1 b hp
  | case8 y e₁ e₂ ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, rfl, _⟩ := h
      exact ih a a1 b hp
  | case9 e₁ e₂ ih =>
      intro pre x suf h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨a, a1, b, hp, rfl, rfl, _⟩ := h
      exact ih a a1 b hp
  | case10 t _ _ _ _ _ _ _ _ _ =>
      intro pre x suf h
      simp at h

end Extract

/-- Does `e` have an oracle head reachable via the positions that `Extract`
    examines?  Mirrors the structural recursion of `Extract`. -/
def Expr.hasOracleHead : Expr → Bool
  | .gen _ _ _        => true
  | .agent _ _ _      => true
  | .ask _            => true
  | .letE _ _ _ e₁ _  => e₁.hasOracleHead
  | .assign _ e₁      => e₁.hasOracleHead
  | .ifE ec _ _       => ec.hasOracleHead
  | .whileE ec _      => ec.hasOracleHead
  | .forE _ e₁ _      => e₁.hasOracleHead
  | .seq e₁ _         => e₁.hasOracleHead
  | _                 => false

/-- `Extract e = none` iff `e` has no reachable oracle head. -/
theorem Extract.none_iff_pure :
    ∀ e, Extract e = none ↔ e.hasOracleHead = false := by
  intro e
  fun_induction Extract e with
  | case1 τ s π => simp [Expr.hasOracleHead]
  | case2 τ s π => simp [Expr.hasOracleHead]
  | case3 s => simp [Expr.hasOracleHead]
  | case4 m y τ e₁ e₂ ih =>
      simp [Expr.hasOracleHead, Option.map_eq_none_iff, ih]
  | case5 y e₁ ih =>
      simp [Expr.hasOracleHead, Option.map_eq_none_iff, ih]
  | case6 ec e₁ e₂ ih =>
      simp [Expr.hasOracleHead, Option.map_eq_none_iff, ih]
  | case7 ec e ih =>
      simp [Expr.hasOracleHead, Option.map_eq_none_iff, ih]
  | case8 y e₁ e₂ ih =>
      simp [Expr.hasOracleHead, Option.map_eq_none_iff, ih]
  | case9 e₁ e₂ ih =>
      simp [Expr.hasOracleHead, Option.map_eq_none_iff, ih]
  | case10 t h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      -- The catch-all: `Extract t = none` by definition.  To show
      -- `t.hasOracleHead = false`, we case on `t` and use each of `h1..h9`
      -- to rule out the interesting constructors.
      constructor
      · intro _
        cases t with
        | gen _ _ _     => exact (h1 _ _ _ rfl).elim
        | agent _ _ _   => exact (h2 _ _ _ rfl).elim
        | ask _         => exact (h3 _ rfl).elim
        | letE _ _ _ _ _ => exact (h4 _ _ _ _ _ rfl).elim
        | assign _ _    => exact (h5 _ _ rfl).elim
        | ifE _ _ _     => exact (h6 _ _ _ rfl).elim
        | whileE _ _    => exact (h7 _ _ rfl).elim
        | forE _ _ _    => exact (h8 _ _ _ rfl).elim
        | seq _ _       => exact (h9 _ _ rfl).elim
        | _ => rfl
      · intro _
        rfl

end HADL
