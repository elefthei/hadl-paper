-- End-to-end clinical-trial workflow example, encoding
-- `figures/clinical_trial.tex` line-by-line in the Lean AST. Proves
-- that each oracle/projection redex named in the figure has a
-- successor under a cooperative oracle and a permissive policy.
--
-- This file is a regression test: future refactors that silently
-- break Schema / Policy / Array[Schema] gen or record projection
-- will fail one of the per-redex progress lemmas below.

import Pact.Syntax
import Pact.Typing
import Pact.Policy
import Pact.Oracle
import Pact.Config
import Pact.Reduction
import Pact.Safety

namespace Pact

namespace ClinicalTrial

/-! ## Workflow AST

    De Bruijn encoding of `figures/clinical_trial.tex`. Variables are
    referenced by their de Bruijn index from the innermost binder.
    Lines below are annotated with their source-line correspondence.

    The continuation after each healable `gen` is `var 0`, the minimal
    `StaticTypeOK.var0` witness — this is what `letGenSuccessHealable`
    requires. (A faithful continuation `(var 0)` extracts the freshly
    bound value; longer continuations would also work given
    `StaticTypeOK.wildcardAtHealable`.) -/

/-- L7 fragment: `let crf: Schema = gen "..."` with continuation `var 0`. -/
def L7_genSchema (s : String) : Expr :=
  .letE .tSchema (.gen .tSchema s (.bvar 0)) (.var 0)

/-- L9-10 fragment: `let policy: Policy = gen "..."`. -/
def L9_genPolicy (s : String) : Expr :=
  .letE .tPolicy (.gen .tPolicy s (.bvar 0)) (.var 0)

/-- L13-14 fragment: `let visits: Array[crf] = gen "..."` with
    `crf : Schema`. -/
def L13_genArrayOfSchema (s : String) : Expr :=
  .letE (.tArray .tSchema)
        (.gen (.tArray .tSchema) s (.bvar 0))
        (.var 0)

/-- L17 fragment: `visit.cost` projection on a record value. -/
def L17_visitCost (fs : List (String × Value)) : Expr :=
  .proj (.val (.recV fs)) "cost"

/-- L20 fragment: `agent "Write final report ..."`. -/
def L20_agent (s : String) : Expr :=
  .agent s (.bvar 0)

/-! ## Per-redex progress lemmas

    Each lemma names the source line and demonstrates that the
    corresponding redex has a successor under a cooperative oracle. -/

/-- L7 progresses: `let crf: Schema = gen ... ; var 0`. -/
theorem L7_progresses
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, RtType v .tSchema ∧ O s ec .tSchema v) :
    ∃ C', Step O ⟨ec, P, σ, L7_genSchema s⟩ C' :=
  T4_truthful_success_gen O ec P σ s 0 π hauth hO

/-- L9-10 progresses: `let policy: Policy = gen ...`. Requires the
    `tPolicy` healability extension from H2. -/
theorem L9_10_progresses
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, RtType v .tPolicy ∧ O s ec .tPolicy v) :
    ∃ C', Step O ⟨ec, P, σ, L9_genPolicy s⟩ C' :=
  T4_truthful_success_gen_healable O ec P σ .tPolicy s 0 π
    (by simp) hauth hO

/-- L13-14 progresses: `let visits: Array[crf] = gen ...` with
    `crf : Schema`. The canonical nested-healing case — requires
    recursive `Ty.healable` on `tArray T`. -/
theorem L13_14_progresses
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (s : String) (π : Principal)
    (hauth : policyAllows P π .gen)
    (hO : ∃ v, RtType v (.tArray .tSchema) ∧ O s ec (.tArray .tSchema) v) :
    ∃ C', Step O ⟨ec, P, σ, L13_genArrayOfSchema s⟩ C' :=
  T4_truthful_success_gen_healable O ec P σ (.tArray .tSchema) s 0 π
    (by simp [Ty.healable]) hauth hO

/-- L17 progresses: `visit.cost` projection on a record carrying the
    field. The stuck case (field absent) is the paper's self-heal
    trigger. -/
theorem L17_progresses
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store)
    (fs : List (String × Value)) (n : Int)
    (hcost : fs.lookup "cost" = some (.numV n)) :
    ∃ C', Step O ⟨ec, P, σ, L17_visitCost fs⟩ C' :=
  ⟨_, Step.projStep hcost⟩

/-! ## Forward-projection self-heal (Phase L)

    These examples exercise `Step.letGenHealRecordFields`: the continuation
    of the let-gen redex projects a field on `var 0`, the oracle returns
    a record value, and the runtime checks `Value.recordSatisfies` against
    `Expr.fieldSitesAt`. When a forward-required field is missing, the
    rule appends a missing-field `Event.error` to `ec` and retries the
    same gen redex. This is the mechanization of the clinical-trial
    caption's "if the generated schema lacks a field accessed later
    (`js visit.cost`, `js visit.patient_id`), the runtime retries the
    causal `gen` with the violated constraint as feedback" trigger. -/

/-- **Generic missing-field self-heal (Phase L).** When the let-gen
    continuation projects a single field `f` on `var 0`, the oracle
    returns a record `fs` that does not contain `f`, and policy
    permits, `letGenHealRecordFields` fires: an `Event.error` is
    appended to `ec` and the redex retries.

    The two clinical-trial examples L17 (`visit.cost` with missing
    `cost`) and L18 (`visit.patient_id` with missing `patient_id`)
    are 1-line corollaries below. -/
theorem letGen_missing_field_heals
    (O : Oracle) (P : Policy) (σ : Store)
    (sV : String) (πGen : Principal) (f : String)
    (fs : List (String × Value))
    (hauth   : policyAllows P πGen .gen)
    (hOmiss  : O sV [] .tSchema (.recV fs))
    (hrt     : RtType (.recV fs) .tSchema)
    (hmiss   : fs.lookup f = none) :
    Step O
      ⟨[], P, σ,
       .letE .tSchema (.gen .tSchema sV (.bvar 0))
             (.proj (.var 0) f)⟩
      ⟨[Event.error s!"missing field {f}"], P, σ,
       .letE .tSchema (.gen .tSchema sV (.bvar 0))
             (.proj (.var 0) f)⟩ :=
  Step.letGenHealRecordFields (π := πGen) (ε := s!"missing field {f}")
    (by simp) hauth hOmiss hrt
    StaticTypeOK.atSchema
    (by simp [Value.recordSatisfies, Expr.fieldSitesAt, List.all, hmiss])
    (by simp [ErrCtx.retries, retryBudget])

/-- L17 (clinical_trial): `let visit : Schema = gen sV ; visit.cost`.
    Oracle returns a record without `"cost"` → forward analysis sees
    `cost` is required → `letGenHealRecordFields` fires. -/
theorem L17_visitCost_with_missing_field_heals
    (O : Oracle) (P : Policy) (σ : Store)
    (sV : String) (πGen : Principal)
    (hauth : policyAllows P πGen .gen)
    (hOmiss : O sV [] .tSchema (.recV [("patient_id", .strV "p1")]))
    (hrt    : RtType (.recV [("patient_id", .strV "p1")]) .tSchema) :
    Step O
      ⟨[], P, σ,
       .letE .tSchema (.gen .tSchema sV (.bvar 0))
             (.proj (.var 0) "cost")⟩
      ⟨[Event.error "missing field cost"], P, σ,
       .letE .tSchema (.gen .tSchema sV (.bvar 0))
             (.proj (.var 0) "cost")⟩ :=
  letGen_missing_field_heals O P σ sV πGen "cost"
    [("patient_id", .strV "p1")] hauth hOmiss hrt (by decide)

/-- L18 (clinical_trial): `let visit : Schema = gen sV ; visit.patient_id`.
    Oracle returns a record without `"patient_id"` → heal fires. -/
theorem L18_patientId_self_heal
    (O : Oracle) (P : Policy) (σ : Store)
    (sV : String) (πGen : Principal)
    (hauth : policyAllows P πGen .gen)
    (hOmiss : O sV [] .tSchema (.recV [("cost", .numV 0)]))
    (hrt    : RtType (.recV [("cost", .numV 0)]) .tSchema) :
    Step O
      ⟨[], P, σ,
       .letE .tSchema (.gen .tSchema sV (.bvar 0))
             (.proj (.var 0) "patient_id")⟩
      ⟨[Event.error "missing field patient_id"], P, σ,
       .letE .tSchema (.gen .tSchema sV (.bvar 0))
             (.proj (.var 0) "patient_id")⟩ :=
  letGen_missing_field_heals O P σ sV πGen "patient_id"
    [("cost", .numV 0)] hauth hOmiss hrt (by decide)

/-- **Heal-then-succeed cycle (Phase L).** A two-step `Steps` chain
    on the L17 redex demonstrating that the forward-projection
    self-heal terminates: the first attempt's oracle returns a record
    missing `"cost"`, `Step.letGenHealRecordFields` appends an error
    and retries; the second attempt's oracle (now indexed at the new
    `ec`) returns a record carrying `"cost"`, and
    `Step.letGenSuccessHealable` instantiates the continuation. -/
theorem L17_heal_then_succeed
    (P : Policy) (σ : Store) (sV : String) (πGen : Principal)
    (hauth  : policyAllows P πGen .gen)
    (pid    : String) (n : Int)
    (O : Oracle)
    (hOmiss : O sV [] .tSchema (.recV [("patient_id", .strV pid)]))
    (hOgood : O sV [Event.error "missing field cost"] .tSchema
                (.recV [("patient_id", .strV pid), ("cost", .numV n)]))
    (hrtBad  : RtType (.recV [("patient_id", .strV pid)]) .tSchema)
    (hrtGood : RtType
                (.recV [("patient_id", .strV pid), ("cost", .numV n)])
                .tSchema) :
    Steps O
      ⟨[], P, σ,
       .letE .tSchema (.gen .tSchema sV (.bvar 0))
             (.proj (.var 0) "cost")⟩
      ⟨[], P, σ,
       (Expr.proj (.var 0) "cost").instantiate
         (.recV [("patient_id", .strV pid), ("cost", .numV n)])⟩ := by
  refine Steps.step
    (Step.letGenHealRecordFields (π := πGen) (ε := "missing field cost")
      (by simp) hauth hOmiss hrtBad
      (StaticTypeOK.atSchema)
      (by simp [Value.recordSatisfies, Expr.fieldSitesAt, List.all, List.lookup])
      (by decide)) ?_
  refine Steps.step
    (Step.letGenSuccessHealable (π := πGen)
      (by simp) hauth hOgood hrtGood
      (StaticTypeOK.atSchema)
      (by simp [Value.recordSatisfies, Expr.fieldSitesAt, List.all, List.lookup]))
    Steps.refl
theorem L20_progresses
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store) (s : String) (π : Principal)
    (hauth : policyAllows P π .agent)
    (hO : ∃ v, RtType v .tString ∧ O s ec .tString v) :
    ∃ C', Step O ⟨ec, P, σ, L20_agent s⟩ C' :=
  T4_truthful_success_agent O ec P σ s 0 π hauth hO

/-! ## Composite end-to-end progress

    Bundles the per-redex progress lemmas into a single statement: the
    five oracle/projection redexes that constitute the paper's
    self-healing story (`Schema gen`, `Policy gen`, `Array[Schema] gen`,
    record projection, `agent`) each have successors when the oracle
    cooperates and the policy permits. -/

/-- **Clinical-trial workflow progress (composite).** Under a
    cooperative oracle and a permissive policy, every oracle and
    projection redex named in `figures/clinical_trial.tex` has a
    successor in the operational semantics. This is a paper-aligned
    regression test: it combines the H1 (`projStep`), H2 (`tPolicy`
    healable), and D1/D2 (parametric `letGenSuccessHealable`) work
    into one statement. -/
theorem clinical_trial_progresses
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store)
    (sSchema sPolicy sArray sAgent : String)
    (πGen πAgent : Principal)
    (fs : List (String × Value)) (n : Int)
    (hauthGen   : policyAllows P πGen   .gen)
    (hauthAgent : policyAllows P πAgent .agent)
    (hOSchema : ∃ v, RtType v .tSchema ∧ O sSchema ec .tSchema v)
    (hOPolicy : ∃ v, RtType v .tPolicy ∧ O sPolicy ec .tPolicy v)
    (hOArray  : ∃ v, RtType v (.tArray .tSchema) ∧
                      O sArray ec (.tArray .tSchema) v)
    (hOAgent  : ∃ v, RtType v .tString ∧ O sAgent ec .tString v)
    (hcost    : fs.lookup "cost" = some (.numV n)) :
    (∃ C', Step O ⟨ec, P, σ, L7_genSchema sSchema⟩ C') ∧
    (∃ C', Step O ⟨ec, P, σ, L9_genPolicy sPolicy⟩ C') ∧
    (∃ C', Step O ⟨ec, P, σ, L13_genArrayOfSchema sArray⟩ C') ∧
    (∃ C', Step O ⟨ec, P, σ, L17_visitCost fs⟩ C') ∧
    (∃ C', Step O ⟨ec, P, σ, L20_agent sAgent⟩ C') :=
  ⟨L7_progresses    O ec P σ sSchema πGen   hauthGen   hOSchema,
   L9_10_progresses O ec P σ sPolicy πGen   hauthGen   hOPolicy,
   L13_14_progresses O ec P σ sArray  πGen   hauthGen   hOArray,
   L17_progresses   O ec P σ fs n hcost,
   L20_progresses   O ec P σ sAgent  πAgent hauthAgent hOAgent⟩

/-! ## Sequential workflow prefix (I1)

The composite `clinical_trial_progresses` proves each redex steps in
some context, but not that they compose into a multi-step reduction.
This section builds the actual chain.

Encoding: `seq` together the four interesting redexes from the
workflow, with `var 0` continuations for each healable gen. After each
`letGenSuccessHealable`, the inner `letE` collapses to the
oracle-supplied value; `seqStep` then discards it and exposes the next
redex. -/

/-- The sequential prefix: Schema gen ; Policy gen ; Array[Schema] gen ;
    `visit.cost` projection. Each gen uses `var 0` as its continuation
    so that `StaticTypeOK.var0` discharges the static-typeability
    premise of the parametric `letGenSuccessHealable` rule. -/
def clinicalTrialPrefix (sS sP sA : String) (fs : List (String × Value)) : Expr :=
  .seq (.letE .tSchema (.gen .tSchema sS (.bvar 0)) (.var 0))
  (.seq (.letE .tPolicy (.gen .tPolicy sP (.bvar 0)) (.var 0))
  (.seq (.letE (.tArray .tSchema)
               (.gen (.tArray .tSchema) sA (.bvar 0))
               (.var 0))
        (.proj (.val (.recV fs)) "cost")))

/-- **Sequential progress through the clinical-trial prefix.**
    Under cooperative oracles for each healable `gen` and a `cost`
    field in the record, the prefix steps in 7 atomic transitions
    to the final numeric value. The heal-context is empty after every
    successful oracle step (per `letGenSuccessHealable`'s post-state),
    so the chain telescopes cleanly through `Steps.step`. -/
theorem clinicalTrialPrefix_steps
    (O : Oracle) (ec : ErrCtx) (P : Policy) (σ : Store)
    (sS sP sA : String) (πGen : Principal)
    (fs : List (String × Value)) (n : Int)
    (hauthGen : policyAllows P πGen .gen)
    (hOSchema : ∃ v, RtType v .tSchema ∧ O sS ec .tSchema v)
    (hOPolicy : ∃ v, RtType v .tPolicy ∧ O sP [] .tPolicy v)
    (hOArray  : ∃ v, RtType v (.tArray .tSchema) ∧
                      O sA [] (.tArray .tSchema) v)
    (hcost    : fs.lookup "cost" = some (.numV n)) :
    Steps O ⟨ec, P, σ, clinicalTrialPrefix sS sP sA fs⟩
           ⟨[], P, σ, .val (.numV n)⟩ := by
  obtain ⟨vS, hrtS, hoS⟩ := hOSchema
  obtain ⟨vP, hrtP, hoP⟩ := hOPolicy
  obtain ⟨vA, hrtA, hoA⟩ := hOArray
  -- Step 1: seqCong on outer + letGenSuccessHealable Schema  (ec → [])
  refine Steps.step
    (Step.seqCong (Step.letGenSuccessHealable (π := πGen)
      (by simp) hauthGen hoS hrtS StaticTypeOK.var0
      (Value.recordSatisfies_var0 vS))) ?_
  -- Step 2: seqStep discards Schema value
  refine Steps.step Step.seqStep ?_
  -- Step 3: seqCong + letGenSuccessHealable Policy
  refine Steps.step
    (Step.seqCong (Step.letGenSuccessHealable (π := πGen)
      (by simp) hauthGen hoP hrtP StaticTypeOK.var0
      (Value.recordSatisfies_var0 vP))) ?_
  -- Step 4: seqStep discards Policy value
  refine Steps.step Step.seqStep ?_
  -- Step 5: seqCong + letGenSuccessHealable Array[Schema]
  refine Steps.step
    (Step.seqCong (Step.letGenSuccessHealable (π := πGen)
      (by simp [Ty.healable]) hauthGen hoA hrtA StaticTypeOK.var0
      (Value.recordSatisfies_var0 vA))) ?_
  -- Step 6: seqStep discards Array value
  refine Steps.step Step.seqStep ?_
  -- Step 7: projStep extracts the cost field
  refine Steps.step (Step.projStep hcost) Steps.refl

end ClinicalTrial

end Pact
