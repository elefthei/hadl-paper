-- Full-trace safety theorems: T4c gen-case and agent-case trace progress.
--
-- These lift the root-level progress lemmas `T4_truthful_success` and
-- `T4_truthful_success_agent` (in `Safety.lean`) through arbitrary
-- CBV-left-to-right evaluation positions, using the `Step.letCong` /
-- `ifCong` / `seqCong` / `assignCong` / `forCong` congruence rules
-- added to `Reduction.lean`.  No `E[·]` machinery is required: the
-- leftmost-redex discipline is baked into the recursive predicate
-- `HasLeftGen` / `HasLeftAgent`.
--
-- Trace-level termination and the terminal-error blame lemma are still
-- paper-only; see the README.

import HADL.Safety

namespace HADL

/-! ### "Next CBV redex is a gen / agent head" predicate -/

/-- `HasLeftGen τ s e` holds iff the leftmost CBV-evaluation position of
    `e` is a `gen τ s none` head. -/
def HasLeftGen (τ : Ty) (s : String) : Expr → Prop
  | .gen τ0 s0 none   => τ = τ0 ∧ s = s0
  | .letE _ _ _ e₁ _  => HasLeftGen τ s e₁
  | .assign _ e₁      => HasLeftGen τ s e₁
  | .ifE e₁ _ _       => HasLeftGen τ s e₁
  | .seq e₁ _         => HasLeftGen τ s e₁
  | .forE _ e₁ _      => HasLeftGen τ s e₁
  | _                 => False

/-- `HasLeftAgent τ s pr e` holds iff the leftmost CBV-evaluation
    position of `e` is a `agent τ s pr` head. -/
def HasLeftAgent (τ : Ty) (s : String) (pr : Option Principal) : Expr → Prop
  | .agent τ0 s0 pr0  => τ = τ0 ∧ s = s0 ∧ pr = pr0
  | .letE _ _ _ e₁ _  => HasLeftAgent τ s pr e₁
  | .assign _ e₁      => HasLeftAgent τ s pr e₁
  | .ifE e₁ _ _       => HasLeftAgent τ s pr e₁
  | .seq e₁ _         => HasLeftAgent τ s pr e₁
  | .forE _ e₁ _      => HasLeftAgent τ s pr e₁
  | _                 => False

/-! ### Agent-side truthful-success (pure-core helper at root) -/

/-- Analogue of `T4_truthful_success` for the agent family. -/
theorem T4_truthful_success_agent
    {O : Oracle} {ρ : Env} {P : Policy} {π : Principal}
    {τ : Ty} {s : String} {pr : Option Principal}
    (hET    : Oracle.EventuallyTruthful O retryBudget)
    (hgen   : policyAllows P π .gen)
    (hauthA : policyAllows P π .agent) :
    ∃ (ec : ErrCtx) (v : Value),
      ErrCtx.retries ec ≤ retryBudget ∧
      O s ec τ v ∧
      RtType ρ v τ ∧
      Step O ⟨ρ, ec, P, π, .agent τ s pr⟩
             ⟨ρ, ec ++ [Event.success], P, π, .valE v⟩ := by
  obtain ⟨ec, hlen, v, hO, hrt⟩ := hET s ρ τ P π hgen
  refine ⟨ec, v, hlen, hO, hrt, ?_⟩
  exact Step.agentSuccess (O := O)
    (ρ := ρ) (ec := ec) (P := P) (π := π)
    (τ := τ) (s := s) (pr := pr) (v := v)
    hauthA hO hrt

/-! ### T4c gen-case trace progress -/

/-- **Gen-case trace progress, structurally inductive form.**  Whenever the
    leftmost CBV position of `e` is a `gen τ s none` head, under an
    eventually-truthful oracle at a `.gen`-authorized policy, the config
    `⟨ρ, ec, P, π, e⟩` can take a `Step` to a non-err successor for some
    `ec`. -/
theorem T4_progress_gen
    {O : Oracle} {P : Policy} {π : Principal} {τ : Ty} {s : String}
    (hET   : Oracle.EventuallyTruthful O retryBudget)
    (hauth : policyAllows P π .gen) :
    ∀ (e : Expr) (ρ : Env),
      HasLeftGen τ s e →
      ∃ (ec : ErrCtx) (C' : Config),
        Step O ⟨ρ, ec, P, π, e⟩ C' ∧ ¬ C'.isErr
  | .gen τ0 s0 none, ρ, h => by
      simp [HasLeftGen] at h
      obtain ⟨hτ, hs⟩ := h
      subst hτ; subst hs
      obtain ⟨ec', v, _hlen, _hO, hrt, hstep⟩ :=
        T4_truthful_success (O := O) (ρ := ρ) (P := P) (π := π)
          (τ := τ) (s := s) hET hauth
      exact ⟨ec', _, hstep, by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  | .letE m x τl e₁ e₂, ρ, h => by
      have h₁ : HasLeftGen τ s e₁ := h
      obtain ⟨ec, C', hstep, hne⟩ := T4_progress_gen hET hauth e₁ ρ h₁
      rcases C' with ⟨ρ', ec', P', π', e₁'⟩
      exact ⟨ec, ⟨ρ', ec', P', π', .letE m x τl e₁' e₂⟩,
             Step.letCong hstep hne,
             by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  | .assign x e₁, ρ, h => by
      have h₁ : HasLeftGen τ s e₁ := h
      obtain ⟨ec, C', hstep, hne⟩ := T4_progress_gen hET hauth e₁ ρ h₁
      rcases C' with ⟨ρ', ec', P', π', e₁'⟩
      exact ⟨ec, ⟨ρ', ec', P', π', .assign x e₁'⟩,
             Step.assignCong hstep hne,
             by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  | .ifE e₁ e₂ e₃, ρ, h => by
      have h₁ : HasLeftGen τ s e₁ := h
      obtain ⟨ec, C', hstep, hne⟩ := T4_progress_gen hET hauth e₁ ρ h₁
      rcases C' with ⟨ρ', ec', P', π', e₁'⟩
      exact ⟨ec, ⟨ρ', ec', P', π', .ifE e₁' e₂ e₃⟩,
             Step.ifCong hstep hne,
             by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  | .seq e₁ e₂, ρ, h => by
      have h₁ : HasLeftGen τ s e₁ := h
      obtain ⟨ec, C', hstep, hne⟩ := T4_progress_gen hET hauth e₁ ρ h₁
      rcases C' with ⟨ρ', ec', P', π', e₁'⟩
      exact ⟨ec, ⟨ρ', ec', P', π', .seq e₁' e₂⟩,
             Step.seqCong hstep hne,
             by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  | .forE x e₁ e₂, ρ, h => by
      have h₁ : HasLeftGen τ s e₁ := h
      obtain ⟨ec, C', hstep, hne⟩ := T4_progress_gen hET hauth e₁ ρ h₁
      rcases C' with ⟨ρ', ec', P', π', e₁'⟩
      exact ⟨ec, ⟨ρ', ec', P', π', .forE x e₁' e₂⟩,
             Step.forCong hstep hne,
             by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  -- Non-CBV-decomposable heads: HasLeftGen is `False`.
  | .var _, _, h => by cases h
  | .unit, _, h => by cases h
  | .litBool _, _, h => by cases h
  | .litInt _, _, h => by cases h
  | .litStr _, _, h => by cases h
  | .whileE _ _, _, h => by cases h
  | .ask _, _, h => by cases h
  | .say _, _, h => by cases h
  | .gen _ _ (some _), _, h => by cases h
  | .agent _ _ _, _, h => by cases h
  | .evalE _ _, _, h => by cases h
  | .enforce _, _, h => by cases h
  | .js _, _, h => by cases h
  | .valE _, _, h => by cases h
  | .errTerm _ _, _, h => by cases h
termination_by e _ _ => sizeOf e

/-! ### T4c agent-case trace progress -/

/-- **Agent-case trace progress.**  Symmetric to `T4_progress_gen`: when
    the leftmost CBV position of `e` is an `agent τ s pr` head, under an
    eventually-truthful oracle at a policy authorizing both `.gen`
    (to invoke the truthful-oracle witness) and `.agent`, the config can
    `Step`. -/
theorem T4_progress_agent
    {O : Oracle} {P : Policy} {π : Principal}
    {τ : Ty} {s : String} {pr : Option Principal}
    (hET    : Oracle.EventuallyTruthful O retryBudget)
    (hgen   : policyAllows P π .gen)
    (hauthA : policyAllows P π .agent) :
    ∀ (e : Expr) (ρ : Env),
      HasLeftAgent τ s pr e →
      ∃ (ec : ErrCtx) (C' : Config),
        Step O ⟨ρ, ec, P, π, e⟩ C' ∧ ¬ C'.isErr
  | .agent τ0 s0 pr0, ρ, h => by
      simp [HasLeftAgent] at h
      obtain ⟨hτ, hs, hpr⟩ := h
      subst hτ; subst hs; subst hpr
      obtain ⟨ec', v, _hlen, _hO, hrt, hstep⟩ :=
        T4_truthful_success_agent (O := O) (ρ := ρ) (P := P) (π := π)
          (τ := τ) (s := s) (pr := pr) hET hgen hauthA
      exact ⟨ec', _, hstep, by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  | .letE m x τl e₁ e₂, ρ, h => by
      have h₁ : HasLeftAgent τ s pr e₁ := h
      obtain ⟨ec, C', hstep, hne⟩ := T4_progress_agent hET hgen hauthA e₁ ρ h₁
      rcases C' with ⟨ρ', ec', P', π', e₁'⟩
      exact ⟨ec, ⟨ρ', ec', P', π', .letE m x τl e₁' e₂⟩,
             Step.letCong hstep hne,
             by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  | .assign x e₁, ρ, h => by
      have h₁ : HasLeftAgent τ s pr e₁ := h
      obtain ⟨ec, C', hstep, hne⟩ := T4_progress_agent hET hgen hauthA e₁ ρ h₁
      rcases C' with ⟨ρ', ec', P', π', e₁'⟩
      exact ⟨ec, ⟨ρ', ec', P', π', .assign x e₁'⟩,
             Step.assignCong hstep hne,
             by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  | .ifE e₁ e₂ e₃, ρ, h => by
      have h₁ : HasLeftAgent τ s pr e₁ := h
      obtain ⟨ec, C', hstep, hne⟩ := T4_progress_agent hET hgen hauthA e₁ ρ h₁
      rcases C' with ⟨ρ', ec', P', π', e₁'⟩
      exact ⟨ec, ⟨ρ', ec', P', π', .ifE e₁' e₂ e₃⟩,
             Step.ifCong hstep hne,
             by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  | .seq e₁ e₂, ρ, h => by
      have h₁ : HasLeftAgent τ s pr e₁ := h
      obtain ⟨ec, C', hstep, hne⟩ := T4_progress_agent hET hgen hauthA e₁ ρ h₁
      rcases C' with ⟨ρ', ec', P', π', e₁'⟩
      exact ⟨ec, ⟨ρ', ec', P', π', .seq e₁' e₂⟩,
             Step.seqCong hstep hne,
             by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  | .forE x e₁ e₂, ρ, h => by
      have h₁ : HasLeftAgent τ s pr e₁ := h
      obtain ⟨ec, C', hstep, hne⟩ := T4_progress_agent hET hgen hauthA e₁ ρ h₁
      rcases C' with ⟨ρ', ec', P', π', e₁'⟩
      exact ⟨ec, ⟨ρ', ec', P', π', .forE x e₁' e₂⟩,
             Step.forCong hstep hne,
             by intro ⟨_, _, hcontra⟩; cases hcontra⟩
  -- Non-CBV-decomposable heads: HasLeftAgent is `False`.
  | .var _, _, h => by cases h
  | .unit, _, h => by cases h
  | .litBool _, _, h => by cases h
  | .litInt _, _, h => by cases h
  | .litStr _, _, h => by cases h
  | .whileE _ _, _, h => by cases h
  | .ask _, _, h => by cases h
  | .say _, _, h => by cases h
  | .gen _ _ _, _, h => by cases h
  | .evalE _ _, _, h => by cases h
  | .enforce _, _, h => by cases h
  | .js _, _, h => by cases h
  | .valE _, _, h => by cases h
  | .errTerm _ _, _, h => by cases h
termination_by e _ _ => sizeOf e

end HADL
