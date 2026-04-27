import HADL.Reduction

open LeanSubst

/-! # Phase N — Principal scope preservation.

`Expr.princOk depth e = true` says that every `PrincRef.bvar n` in `e`
satisfies `n < depth`. The top-level resolution claim is: if a closed
program is `princOk 0`, then every reachable runtime configuration is
`princOk 0` — i.e. no `gen`/`agent` ever runs with a dangling principal
reference.

The preservation theorem `Step.preserves_princOk` is parametric in the
ambient principal depth and is conditioned on a single semantic premise:
the oracle returns `princOk`-clean values. This is the analogue, on the
principal-scope side, of the truthful-oracle hypothesis on the type
side. Concretely: just as truthfulness asks `RtType v τ`, the scope
hypothesis asks `Value.princOk depth v = true`. For all primitive
`RtType` cases except `vClos` and `vPrinc`, this is trivially true; for
those two it constrains the oracle to produce well-scoped closures /
principals, matching the paper's untrusted-but-checked discipline.

Together with the existing soundness theorem, the corollary
`principal_indices_bounded` states the resolution invariant: every
PrincRef encountered at runtime in a closed program points into the
dynamic entity store.
-/

namespace HADL

/-! ## Monotonicity of `princOk` in `depth`. -/

mutual

theorem Value.princOk_mono {v : Value} {d d' : Nat}
    (h : Value.princOk d v = true) (hd : d ≤ d') :
    Value.princOk d' v = true := by
  cases v with
  | unitV => simp [Value.princOk]
  | boolV _ => simp [Value.princOk]
  | numV _ => simp [Value.princOk]
  | strV _ => simp [Value.princOk]
  | schemaV _ => simp [Value.princOk]
  | polV _ => simp [Value.princOk]
  | principalV pr =>
    cases pr with
    | bvar n =>
      simp [Value.princOk, PrincRef.princOk] at h ⊢
      omega
  | recV xs =>
    simp [Value.princOk] at h ⊢
    exact Value.princOkRec_mono h hd
  | arrV vs =>
    simp [Value.princOk] at h ⊢
    exact Value.princOkList_mono h hd
  | clos _ body =>
    simp [Value.princOk] at h ⊢
    exact Expr.princOk_mono h hd
  | errV => simp [Value.princOk]

theorem Value.princOkList_mono {vs : List Value} {d d' : Nat}
    (h : Value.princOkList d vs = true) (hd : d ≤ d') :
    Value.princOkList d' vs = true := by
  match vs with
  | List.nil => simp [Value.princOkList]
  | List.cons v vs =>
    simp [Value.princOkList] at h ⊢
    exact ⟨Value.princOk_mono h.1 hd, Value.princOkList_mono h.2 hd⟩

theorem Value.princOkRec_mono {xs : List (String × Value)} {d d' : Nat}
    (h : Value.princOkRec d xs = true) (hd : d ≤ d') :
    Value.princOkRec d' xs = true := by
  match xs with
  | List.nil => simp [Value.princOkRec]
  | List.cons (_, v) xs =>
    simp [Value.princOkRec] at h ⊢
    exact ⟨Value.princOk_mono h.1 hd, Value.princOkRec_mono h.2 hd⟩

theorem Expr.princOk_mono {e : Expr} {d d' : Nat}
    (h : Expr.princOk d e = true) (hd : d ≤ d') :
    Expr.princOk d' e = true := by
  cases e with
  | val v =>
    simp [Expr.princOk] at h ⊢
    exact Value.princOk_mono h hd
  | var _ => simp [Expr.princOk]
  | letE _ e1 e2 =>
    simp [Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_mono h.1 hd, Expr.princOk_mono h.2 hd⟩
  | ifE e1 e2 e3 =>
    simp [Expr.princOk] at h ⊢
    exact ⟨⟨Expr.princOk_mono h.1.1 hd, Expr.princOk_mono h.1.2 hd⟩,
           Expr.princOk_mono h.2 hd⟩
  | whileE e1 e2 =>
    simp [Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_mono h.1 hd, Expr.princOk_mono h.2 hd⟩
  | forE e1 e2 =>
    simp [Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_mono h.1 hd, Expr.princOk_mono h.2 hd⟩
  | seq e1 e2 =>
    simp [Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_mono h.1 hd, Expr.princOk_mono h.2 hd⟩
  | ask _ => simp [Expr.princOk]
  | say _ => simp [Expr.princOk]
  | letPrinc b body =>
    simp [Expr.princOk] at h ⊢
    refine ⟨?_, Expr.princOk_mono h.2 (Nat.add_le_add_right hd 1)⟩
    cases b with
    | root => rfl
    | restrict pr =>
      cases pr with
      | bvar n =>
        simp [PrincBinder.princOk, PrincRef.princOk] at h ⊢
        omega
  | gen _ _ pr =>
    cases pr with
    | bvar n =>
      simp [Expr.princOk, PrincRef.princOk] at h ⊢
      omega
  | agent _ pr =>
    cases pr with
    | bvar n =>
      simp [Expr.princOk, PrincRef.princOk] at h ⊢
      omega
  | evalE f args =>
    simp [Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_mono h.1 hd, Expr.princOkList_mono h.2 hd⟩
  | enforce e =>
    simp [Expr.princOk] at h ⊢
    exact Expr.princOk_mono h hd
  | js _ => simp [Expr.princOk]
  | varDecl _ _ e1 e2 =>
    simp [Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_mono h.1 hd, Expr.princOk_mono h.2 hd⟩
  | assign _ e =>
    simp [Expr.princOk] at h ⊢
    exact Expr.princOk_mono h hd
  | varRead _ => simp [Expr.princOk]
  | proj e _ =>
    simp [Expr.princOk] at h ⊢
    exact Expr.princOk_mono h hd

theorem Expr.princOkList_mono {es : List Expr} {d d' : Nat}
    (h : Expr.princOkList d es = true) (hd : d ≤ d') :
    Expr.princOkList d' es = true := by
  match es with
  | List.nil => simp [Expr.princOkList]
  | List.cons e es =>
    simp [Expr.princOkList] at h ⊢
    exact ⟨Expr.princOk_mono h.1 hd, Expr.princOkList_mono h.2 hd⟩

end

/-! ## Substitution preservation.

    `Expr.smap σ e` is the parametric Expr substitution. Since
    `PrincRef.smap σ pr = pr` (Syntax.lean:288), Expr-level
    substitution does **not** affect any `PrincRef` index — principals
    live in a separate de Bruijn scope. So `princOk` is preserved by
    `smap` whenever every action substituted in is itself `princOk`. -/

/-- A substitution is `princOk` at `depth` iff every variable it can
    produce is itself a `princOk` Expr at that depth. We only need
    `.su` actions (substitution targets) — `.re y` (rename) is
    `var y`, which is unconditionally `princOk`. -/
def Subst.princOk (depth : Nat) (σ : Subst Expr) : Prop :=
  ∀ n, Expr.princOk depth (Expr.from_action (σ n)) = true

theorem Subst.princOk.id (depth : Nat) :
    Subst.princOk depth (+0 : Subst Expr) := by
  intro n
  simp [Expr.from_action_id]

theorem Subst.princOk.cons {depth : Nat} {σ : Subst Expr} {v : Value}
    (hv : Value.princOk depth v = true)
    (hσ : Subst.princOk depth σ) :
    Subst.princOk depth (Subst.Action.su (.val v) :: σ) := by
  intro n
  cases n with
  | zero =>
    show Expr.princOk depth (Expr.from_action (Subst.Action.su (.val v))) = true
    simp [Expr.from_action, Expr.princOk]
    exact hv
  | succ k => exact hσ k

/-! ## Renaming preserves `princOk`.

    Since `PrincRef.rmap` and `PrincBinder.rmap` are identity
    (Syntax.lean:51,66), renaming an expression leaves every
    `PrincRef.bvar` index untouched. Therefore `Expr.rmap r e` has
    exactly the same set of principal indices as `e`, and `princOk` is
    invariant under any rename. -/

mutual

theorem Value.princOk_rmap {r : Ren} {v : Value} {d : Nat}
    (h : Value.princOk d v = true) : Value.princOk d (Value.rmap r v) = true := by
  cases v with
  | unitV => simp [Value.rmap, Value.princOk]
  | boolV _ => simp [Value.rmap, Value.princOk]
  | numV _ => simp [Value.rmap, Value.princOk]
  | strV _ => simp [Value.rmap, Value.princOk]
  | schemaV _ => simp [Value.rmap, Value.princOk]
  | polV _ => simp [Value.rmap, Value.princOk]
  | principalV pr =>
    cases pr with
    | bvar n =>
      simp [Value.rmap, PrincRef.rmap, Value.princOk] at h ⊢
      exact h
  | recV xs =>
    simp [Value.rmap, Value.princOk] at h ⊢
    exact Value.princOkRec_rmap h
  | arrV vs =>
    simp [Value.rmap, Value.princOk] at h ⊢
    exact Value.princOkList_rmap h
  | clos n body =>
    simp [Value.rmap, Value.princOk] at h ⊢
    exact Expr.princOk_rmap h
  | errV => simp [Value.rmap, Value.princOk]

theorem Value.princOkList_rmap {r : Ren} {vs : List Value} {d : Nat}
    (h : Value.princOkList d vs = true) :
    Value.princOkList d (Value.rmapList r vs) = true := by
  match vs with
  | List.nil => simp [Value.rmapList, Value.princOkList]
  | List.cons v vs =>
    simp [Value.rmapList, Value.princOkList] at h ⊢
    exact ⟨Value.princOk_rmap h.1, Value.princOkList_rmap h.2⟩

theorem Value.princOkRec_rmap {r : Ren} {xs : List (String × Value)} {d : Nat}
    (h : Value.princOkRec d xs = true) :
    Value.princOkRec d (Value.rmapRec r xs) = true := by
  match xs with
  | List.nil => simp [Value.rmapRec, Value.princOkRec]
  | List.cons (_, v) xs =>
    simp [Value.rmapRec, Value.princOkRec] at h ⊢
    exact ⟨Value.princOk_rmap h.1, Value.princOkRec_rmap h.2⟩

theorem Expr.princOk_rmap {r : Ren} {e : Expr} {d : Nat}
    (h : Expr.princOk d e = true) : Expr.princOk d (Expr.rmap r e) = true := by
  cases e with
  | val v =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact Value.princOk_rmap h
  | var _ => simp [Expr.rmap, Expr.princOk]
  | letE _ e1 e2 =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_rmap h.1, Expr.princOk_rmap h.2⟩
  | ifE e1 e2 e3 =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact ⟨⟨Expr.princOk_rmap h.1.1, Expr.princOk_rmap h.1.2⟩, Expr.princOk_rmap h.2⟩
  | whileE e1 e2 =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_rmap h.1, Expr.princOk_rmap h.2⟩
  | forE e1 e2 =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_rmap h.1, Expr.princOk_rmap h.2⟩
  | seq e1 e2 =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_rmap h.1, Expr.princOk_rmap h.2⟩
  | ask _ => simp [Expr.rmap, Expr.princOk]
  | say _ => simp [Expr.rmap, Expr.princOk]
  | letPrinc b body =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    refine ⟨?_, Expr.princOk_rmap h.2⟩
    cases b with
    | root => rfl
    | restrict pr =>
      cases pr with
      | bvar n =>
        simp [PrincBinder.rmap, PrincBinder.princOk, PrincRef.princOk] at h ⊢
        exact h.1
  | gen _ _ pr =>
    cases pr with
    | bvar n =>
      simp [Expr.rmap, PrincRef.rmap, Expr.princOk, PrincRef.princOk] at h ⊢
      exact h
  | agent _ pr =>
    cases pr with
    | bvar n =>
      simp [Expr.rmap, PrincRef.rmap, Expr.princOk, PrincRef.princOk] at h ⊢
      exact h
  | evalE f args =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_rmap h.1, Expr.princOkList_rmap h.2⟩
  | enforce e =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact Expr.princOk_rmap h
  | js _ => simp [Expr.rmap, Expr.princOk]
  | varDecl _ _ e1 e2 =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact ⟨Expr.princOk_rmap h.1, Expr.princOk_rmap h.2⟩
  | assign _ e =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact Expr.princOk_rmap h
  | varRead _ => simp [Expr.rmap, Expr.princOk]
  | proj e _ =>
    simp [Expr.rmap, Expr.princOk] at h ⊢
    exact Expr.princOk_rmap h

theorem Expr.princOkList_rmap {r : Ren} {es : List Expr} {d : Nat}
    (h : Expr.princOkList d es = true) :
    Expr.princOkList d (Expr.rmapList r es) = true := by
  match es with
  | List.nil => simp [Expr.rmapList, Expr.princOkList]
  | List.cons e es =>
    simp [Expr.rmapList, Expr.princOkList] at h ⊢
    exact ⟨Expr.princOk_rmap h.1, Expr.princOkList_rmap h.2⟩

end

/-- `Subst.princOk` is preserved under `Subst.lift`. The lift maps:
    index 0 → `var 0` (always princOk); index `n+1` → either a renamed
    `Expr` (princOk by `princOk_rmap`) or a shifted variable
    (unconditionally princOk). -/
theorem Subst.princOk.lift {depth : Nat} {σ : Subst Expr}
    (hσ : Subst.princOk depth σ) :
    Subst.princOk depth (Subst.lift σ) := by
  intro n
  show Expr.princOk depth (Expr.from_action ((Subst.lift σ : Subst Expr) n)) = true
  unfold Subst.lift
  by_cases hn : n < 1
  · simp [hn, Expr.from_action_re, Expr.princOk]
  · simp [hn]
    have hσn := hσ (n - 1)
    cases hact : σ (n - 1) with
    | re k =>
      simp [Expr.from_action_re, Expr.princOk]
    | su t =>
      simp [Expr.from_action_su]
      rw [hact] at hσn
      simp [Expr.from_action_su] at hσn
      exact Expr.princOk_rmap hσn

/-- `Subst.princOk` is preserved under `Subst.liftN`. -/
theorem Subst.princOk.liftN {depth : Nat} {σ : Subst Expr}
    (hσ : Subst.princOk depth σ) :
    ∀ n, Subst.princOk depth (Subst.liftN σ n)
  | 0 => hσ
  | n + 1 => by
    show Subst.princOk depth (Subst.lift (Subst.liftN σ n))
    exact Subst.princOk.lift (Subst.princOk.liftN hσ n)

/-! ## Substitution preserves `princOk`. -/

mutual

theorem Value.princOk_smap {σ : Subst Expr} {v : Value} {d : Nat}
    (he : Value.princOk d v = true) (hσ : Subst.princOk d σ) :
    Value.princOk d (Value.smap σ v) = true := by
  cases v with
  | unitV => simp [Value.smap, Value.princOk]
  | boolV _ => simp [Value.smap, Value.princOk]
  | numV _ => simp [Value.smap, Value.princOk]
  | strV _ => simp [Value.smap, Value.princOk]
  | schemaV _ => simp [Value.smap, Value.princOk]
  | polV _ => simp [Value.smap, Value.princOk]
  | principalV pr =>
    cases pr with
    | bvar n =>
      simp [Value.smap, PrincRef.smap, Value.princOk] at he ⊢
      exact he
  | recV xs =>
    simp [Value.smap, Value.princOk] at he ⊢
    exact Value.princOkRec_smap he hσ
  | arrV vs =>
    simp [Value.smap, Value.princOk] at he ⊢
    exact Value.princOkList_smap he hσ
  | clos n body =>
    simp [Value.smap, Value.princOk] at he ⊢
    exact Expr.princOk_smap he (Subst.princOk.liftN hσ n)
  | errV => simp [Value.smap, Value.princOk]

theorem Value.princOkList_smap {σ : Subst Expr} {vs : List Value} {d : Nat}
    (he : Value.princOkList d vs = true) (hσ : Subst.princOk d σ) :
    Value.princOkList d (Value.smapList σ vs) = true := by
  match vs with
  | List.nil => simp [Value.smapList, Value.princOkList]
  | List.cons v vs =>
    simp [Value.smapList, Value.princOkList] at he ⊢
    exact ⟨Value.princOk_smap he.1 hσ, Value.princOkList_smap he.2 hσ⟩

theorem Value.princOkRec_smap {σ : Subst Expr} {xs : List (String × Value)} {d : Nat}
    (he : Value.princOkRec d xs = true) (hσ : Subst.princOk d σ) :
    Value.princOkRec d (Value.smapRec σ xs) = true := by
  match xs with
  | List.nil => simp [Value.smapRec, Value.princOkRec]
  | List.cons (_, v) xs =>
    simp [Value.smapRec, Value.princOkRec] at he ⊢
    exact ⟨Value.princOk_smap he.1 hσ, Value.princOkRec_smap he.2 hσ⟩

theorem Expr.princOk_smap {σ : Subst Expr} {e : Expr} {d : Nat}
    (he : Expr.princOk d e = true) (hσ : Subst.princOk d σ) :
    Expr.princOk d (Expr.smap σ e) = true := by
  cases e with
  | val v =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact Value.princOk_smap he hσ
  | var x =>
    simp [Expr.smap]
    exact hσ x
  | letE _ e1 e2 =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact ⟨Expr.princOk_smap he.1 hσ, Expr.princOk_smap he.2 (Subst.princOk.lift hσ)⟩
  | ifE e1 e2 e3 =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact ⟨⟨Expr.princOk_smap he.1.1 hσ, Expr.princOk_smap he.1.2 hσ⟩,
           Expr.princOk_smap he.2 hσ⟩
  | whileE e1 e2 =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact ⟨Expr.princOk_smap he.1 hσ, Expr.princOk_smap he.2 hσ⟩
  | forE e1 e2 =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact ⟨Expr.princOk_smap he.1 hσ, Expr.princOk_smap he.2 (Subst.princOk.lift hσ)⟩
  | seq e1 e2 =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact ⟨Expr.princOk_smap he.1 hσ, Expr.princOk_smap he.2 hσ⟩
  | ask _ => simp [Expr.smap, Expr.princOk]
  | say _ => simp [Expr.smap, Expr.princOk]
  | letPrinc b body =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    refine ⟨?_, Expr.princOk_smap he.2 ?_⟩
    · cases b with
      | root => rfl
      | restrict pr =>
        cases pr with
        | bvar n =>
          simp [PrincBinder.smap, PrincBinder.princOk, PrincRef.princOk] at he ⊢
          exact he.1
    · intro k
      exact Expr.princOk_mono (hσ k) (Nat.le_succ d)
  | gen _ _ pr =>
    cases pr with
    | bvar n =>
      simp [Expr.smap, PrincRef.smap, Expr.princOk, PrincRef.princOk] at he ⊢
      exact he
  | agent _ pr =>
    cases pr with
    | bvar n =>
      simp [Expr.smap, PrincRef.smap, Expr.princOk, PrincRef.princOk] at he ⊢
      exact he
  | evalE f args =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact ⟨Expr.princOk_smap he.1 hσ, Expr.princOkList_smap he.2 hσ⟩
  | enforce e =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact Expr.princOk_smap he hσ
  | js _ => simp [Expr.smap, Expr.princOk]
  | varDecl _ _ e1 e2 =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact ⟨Expr.princOk_smap he.1 hσ, Expr.princOk_smap he.2 hσ⟩
  | assign _ e =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact Expr.princOk_smap he hσ
  | varRead _ => simp [Expr.smap, Expr.princOk]
  | proj e _ =>
    simp [Expr.smap, Expr.princOk] at he ⊢
    exact Expr.princOk_smap he hσ

theorem Expr.princOkList_smap {σ : Subst Expr} {es : List Expr} {d : Nat}
    (he : Expr.princOkList d es = true) (hσ : Subst.princOk d σ) :
    Expr.princOkList d (Expr.smapList σ es) = true := by
  match es with
  | List.nil => simp [Expr.smapList, Expr.princOkList]
  | List.cons e es =>
    simp [Expr.smapList, Expr.princOkList] at he ⊢
    exact ⟨Expr.princOk_smap he.1 hσ, Expr.princOkList_smap he.2 hσ⟩

end

/-- Single-variable substitution `Expr.instantiate` preserves `princOk`. -/
theorem Expr.princOk_instantiate {e : Expr} {v : Value} {d : Nat}
    (he : Expr.princOk d e = true) (hv : Value.princOk d v = true) :
    Expr.princOk d (e.instantiate v) = true := by
  unfold Expr.instantiate
  apply Expr.princOk_smap he
  exact Subst.princOk.cons hv (Subst.princOk.id d)

/-- N-argument value substitution preserves `princOk` (used by
    `evalSuccess`). -/
theorem Subst.princOk.foldr_vals {d : Nat} {vs : List Value}
    (hvs : Value.princOkList d vs = true) :
    Subst.princOk d
      (vs.foldr (fun v s => Subst.Action.su (.val v) :: s) (+0 : Subst Expr)) := by
  induction vs with
  | nil => exact Subst.princOk.id d
  | cons v vs ih =>
    simp [Value.princOkList] at hvs
    simp [List.foldr]
    exact Subst.princOk.cons hvs.1 (ih hvs.2)

/-- Extract a list of values' princOk from the corresponding list of
    `.val v` expressions' princOk. -/
theorem Value.princOkList_of_map_val {d : Nat} {vs : List Value}
    (h : Expr.princOkList d (vs.map Expr.val) = true) :
    Value.princOkList d vs = true := by
  induction vs with
  | nil => simp [Value.princOkList]
  | cons v vs ih =>
    simp [List.map, Expr.princOkList, Expr.princOk] at h
    simp [Value.princOkList]
    exact ⟨h.1, ih h.2⟩

/-- Extract an individual value's princOk from a record's princOk. -/
theorem Value.princOkRec_lookup {d : Nat} :
    ∀ {fs : List (String × Value)} {f : String} {v : Value},
      Value.princOkRec d fs = true → fs.lookup f = some v → Value.princOk d v = true
  | List.nil, _, _, _, hl => by simp [List.lookup] at hl
  | List.cons (k, vh) tl, f, v, hr, hl => by
    simp [Value.princOkRec] at hr
    simp [List.lookup] at hl
    by_cases hk : f == k
    · simp [hk] at hl; subst hl; exact hr.1
    · simp [hk] at hl; exact Value.princOkRec_lookup hr.2 hl

/-! ## Store and configuration scope. -/

/-- A store is `princOk` iff every cell value is closed (`princOk 0`). -/
def Store.princOk (σ : Store) : Prop :=
  ∀ x τ v, σ x = some (τ, v) → Value.princOk 0 v = true

theorem Store.princOk_set {σ : Store} {x : String} {τ : Ty} {v : Value}
    (hσ : Store.princOk σ) (hv : Value.princOk 0 v = true) :
    Store.princOk (σ.set x τ v) := by
  intro y τ' v' hy
  unfold Store.set at hy
  by_cases hxy : y = x
  · subst hxy; simp at hy; rcases hy with ⟨_, rfl⟩; exact hv
  · simp [hxy] at hy; exact hσ y τ' v' hy

/-! ## Step preservation.

    The preservation theorem is conditioned on three semantic
    hypotheses about the *external* value sources:

    * `hOracle`: every oracle-produced value is closed (no captured
      principal binders). Paper note: oracles synthesize fresh values.
    * `hJs`: `jsEval` produces closed values. Aligns with
      `JsAxioms.lean`: the default `jsEval` returns `none`.
    * the store invariant `Store.princOk` is propagated as a
      conjunctive output, since `varDeclBind`/`assignWrite` add
      values that are themselves princOk by hypothesis on the source
      expression.

    The conclusion is at depth 0 — the top-level closed-program
    invariant. Proofs at non-zero depth fail at `letPrincValue`
    because monotonicity goes the wrong way; depth 0 is the right
    invariant for paper-level resolution claims. -/

/-- Scope is preserved by a single `Step`, conditional on (a) every
    oracle-produced value being closed and (b) `jsEval` producing
    closed values. Generalized to arbitrary depth `d` so that
    `letPrincCong`'s body (under one principal binder) can be handled
    by specializing the inductive hypothesis to depth `d+1`. -/
theorem Step.preserves_princOk {O : Oracle} {C C' : Config}
    (hOracle : ∀ s ec τ v, O s ec τ v → Value.princOk 0 v = true)
    (hJs : ∀ je v, jsEval je = some v → Value.princOk 0 v = true)
    (hstep : Step O C C') :
    ∀ d, Expr.princOk d C.expr = true → Store.princOk C.store →
      Expr.princOk d C'.expr = true ∧ Store.princOk C'.store := by
  induction hstep with
  | letBind hrt =>
    intro d he hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk] at he
    exact Expr.princOk_instantiate he.2 he.1
  | ifTrue =>
    intro d he hσ
    simp [Expr.princOk] at he
    exact ⟨he.1.2, hσ⟩
  | ifFalse =>
    intro d he hσ
    simp [Expr.princOk] at he
    exact ⟨he.2, hσ⟩
  | whileUnfold =>
    intro d he hσ
    simp [Expr.princOk] at he
    refine ⟨?_, hσ⟩
    show Expr.princOk d (.ifE _ (.seq _ (.whileE _ _)) (.val .unitV)) = true
    simp [Expr.princOk, Value.princOk, he.1, he.2]
  | forNil =>
    intro _ _ hσ
    exact ⟨by simp [Expr.princOk, Value.princOk], hσ⟩
  | forCons =>
    intro d he hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk, Value.princOk, Value.princOkList] at he
    simp [Expr.princOk, Value.princOk, Value.princOkList]
    exact ⟨Expr.princOk_instantiate he.2 he.1.1, he.1.2, he.2⟩
  | seqStep =>
    intro d he hσ
    simp [Expr.princOk] at he
    exact ⟨he.2, hσ⟩
  | jsStep h =>
    intro d _ hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk]
    exact Value.princOk_mono (hJs _ _ h) (Nat.zero_le d)
  | sayStep =>
    intro _ _ hσ
    exact ⟨by simp [Expr.princOk, Value.princOk], hσ⟩
  | askStep horacle _ =>
    intro d _ hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk]
    exact Value.princOk_mono (hOracle _ _ _ _ horacle) (Nat.zero_le d)
  | agentSuccess _ horacle _ =>
    intro d _ hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk]
    exact Value.princOk_mono (hOracle _ _ _ _ horacle) (Nat.zero_le d)
  | agentHealPol _ _ =>
    intro _ he hσ; exact ⟨he, hσ⟩
  | letCongNonheal _ _ ih =>
    intro d he hσ
    simp [Expr.princOk] at he
    obtain ⟨he', hσ'⟩ := ih d he.1 hσ
    refine ⟨?_, hσ'⟩
    simp [Expr.princOk]; exact ⟨he', he.2⟩
  | letGenSuccessNonheal _ _ horacle _ =>
    intro d he hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk] at he
    exact Expr.princOk_instantiate he.2
      (Value.princOk_mono (hOracle _ _ _ _ horacle) (Nat.zero_le d))
  | letGenTypeError _ _ _ _ =>
    intro _ _ hσ
    exact ⟨by simp [Expr.princOk, Value.princOk], hσ⟩
  | letGenBudgetError _ =>
    intro _ _ hσ
    exact ⟨by simp [Expr.princOk, Value.princOk], hσ⟩
  | letGenHealPol _ _ =>
    intro _ he hσ; exact ⟨he, hσ⟩
  | letGenSuccessHealable _ _ horacle _ _ _ =>
    intro d he hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk] at he
    exact Expr.princOk_instantiate he.2
      (Value.princOk_mono (hOracle _ _ _ _ horacle) (Nat.zero_le d))
  | letGenHealHealable _ _ _ _ _ _ =>
    intro _ he hσ; exact ⟨he, hσ⟩
  | letGenHealRecordFields _ _ _ _ _ _ _ =>
    intro _ he hσ; exact ⟨he, hσ⟩
  | evalSuccess _ =>
    intro d he hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk, Value.princOk] at he
    apply Expr.princOk_smap he.1
    exact Subst.princOk.foldr_vals (Value.princOkList_of_map_val he.2)
  | enforceInstall _ =>
    intro _ _ hσ
    exact ⟨by simp [Expr.princOk, Value.princOk], hσ⟩
  | letPrincValue hv =>
    intro d he hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk]
    exact Value.princOk_mono hv (Nat.zero_le d)
  | letPrincCong _ ih =>
    intro d he hσ
    simp [Expr.princOk] at he
    obtain ⟨he', hσ'⟩ := ih (d + 1) he.2 hσ
    refine ⟨?_, hσ'⟩
    simp [Expr.princOk]; exact ⟨he.1, he'⟩
  | ifCong _ ih =>
    intro d he hσ
    simp [Expr.princOk] at he
    obtain ⟨he', hσ'⟩ := ih d he.1.1 hσ
    refine ⟨?_, hσ'⟩
    simp [Expr.princOk]; exact ⟨⟨he', he.1.2⟩, he.2⟩
  | seqCong _ ih =>
    intro d he hσ
    simp [Expr.princOk] at he
    obtain ⟨he', hσ'⟩ := ih d he.1 hσ
    refine ⟨?_, hσ'⟩
    simp [Expr.princOk]; exact ⟨he', he.2⟩
  | forCong _ ih =>
    intro d he hσ
    simp [Expr.princOk] at he
    obtain ⟨he', hσ'⟩ := ih d he.1 hσ
    refine ⟨?_, hσ'⟩
    simp [Expr.princOk]; exact ⟨he', he.2⟩
  | enforceCong _ ih =>
    intro d he hσ
    simp [Expr.princOk] at he
    obtain ⟨he', hσ'⟩ := ih d he hσ
    refine ⟨?_, hσ'⟩
    show Expr.princOk d (.enforce _) = true
    simp [Expr.princOk]; exact he'
  | evalFunCong _ ih =>
    intro d he hσ
    simp [Expr.princOk] at he
    obtain ⟨he', hσ'⟩ := ih d he.1 hσ
    refine ⟨?_, hσ'⟩
    simp [Expr.princOk]; exact ⟨he', he.2⟩
  | varDeclEval _ ih =>
    intro d he hσ
    simp [Expr.princOk] at he
    obtain ⟨he', hσ'⟩ := ih d he.1 hσ
    refine ⟨?_, hσ'⟩
    simp [Expr.princOk]; exact ⟨he', he.2⟩
  | varDeclBind _ hv =>
    intro d he hσ
    simp [Expr.princOk] at he
    refine ⟨he.2, ?_⟩
    exact Store.princOk_set hσ hv
  | assignEval _ ih =>
    intro d he hσ
    simp [Expr.princOk] at he
    obtain ⟨he', hσ'⟩ := ih d he hσ
    refine ⟨?_, hσ'⟩
    show Expr.princOk d (.assign _ _) = true
    simp [Expr.princOk]; exact he'
  | assignWrite _ _ hv =>
    intro d _ hσ
    refine ⟨by simp [Expr.princOk, Value.princOk], ?_⟩
    exact Store.princOk_set hσ hv
  | varReadStep hbound =>
    intro d _ hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk]
    exact Value.princOk_mono (hσ _ _ _ hbound) (Nat.zero_le d)
  | projCong _ ih =>
    intro d he hσ
    simp [Expr.princOk] at he
    obtain ⟨he', hσ'⟩ := ih d he hσ
    refine ⟨?_, hσ'⟩
    show Expr.princOk d (.proj _ _) = true
    simp [Expr.princOk]; exact he'
  | projStep hlookup =>
    intro d he hσ
    refine ⟨?_, hσ⟩
    simp [Expr.princOk, Value.princOk] at he
    show Expr.princOk d (.val _) = true
    simp [Expr.princOk]
    exact Value.princOkRec_lookup he hlookup

/-- Multi-step preservation: `princOk` is preserved over any reduction
    sequence under the same external hypotheses. -/
theorem Steps.preserves_princOk {O : Oracle} {C C' : Config}
    (hOracle : ∀ s ec τ v, O s ec τ v → Value.princOk 0 v = true)
    (hJs : ∀ je v, jsEval je = some v → Value.princOk 0 v = true)
    (hsteps : Steps O C C') :
    ∀ d, Expr.princOk d C.expr = true → Store.princOk C.store →
      Expr.princOk d C'.expr = true ∧ Store.princOk C'.store := by
  induction hsteps with
  | refl => intro d he hσ; exact ⟨he, hσ⟩
  | step h _ ih =>
    intro d he hσ
    obtain ⟨he', hσ'⟩ := h.preserves_princOk hOracle hJs d he hσ
    exact ih d he' hσ'

/-- Corollary: starting from a closed program (`princOk 0`) with a
    `princOk` store, every reachable expression has bounded principal
    indices (i.e. `princOk 0`). -/
theorem principal_indices_bounded {O : Oracle} {C C' : Config}
    (hOracle : ∀ s ec τ v, O s ec τ v → Value.princOk 0 v = true)
    (hJs : ∀ je v, jsEval je = some v → Value.princOk 0 v = true)
    (hsteps : Steps O C C')
    (he : Expr.princOk 0 C.expr = true) (hσ : Store.princOk C.store) :
    Expr.princOk 0 C'.expr = true :=
  (hsteps.preserves_princOk hOracle hJs 0 he hσ).1

end HADL
