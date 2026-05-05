-- Pact/AxiomCheck.lean
-- Axiom-drift guard: this file fails to compile if any main theorem
-- introduces an axiom beyond [propext, Quot.sound].
-- Any failure here is a RED FLAG — investigate before silencing.

import Pact.Soundness
import Pact.Safety
import Pact.Scope
import Pact.Examples

namespace Pact

/-- info: 'Pact.T1_WF_preservation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T1_WF_preservation

/-- info: 'Pact.T2_staged_materialization' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T2_staged_materialization

/-- info: 'Pact.T3_policy_monotonicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T3_policy_monotonicity

/-- info: 'Pact.T4_budget_no_heal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_budget_no_heal

/-- info: 'Pact.T4_truthful_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success

/-- info: 'Pact.T4_truthful_success_agent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success_agent

/-- info: 'Pact.T4_truthful_success_gen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success_gen

/-- info: 'Pact.T4_progress_gen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_progress_gen

/-- info: 'Pact.T4_progress_agent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_progress_agent

/-- info: 'Pact.T4_truthful_success_arrow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success_arrow

/-- info: 'Pact.T4_truthful_success_healable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success_healable

/-- info: 'Pact.nested_array_of_schema_succeeds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms nested_array_of_schema_succeeds

/-- info: 'Pact.T4_truthful_success_gen_healable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success_gen_healable

/-- info: 'Pact.T4_progress_gen_healable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_progress_gen_healable

/-- info: 'Pact.T4_progress_gen_policy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_progress_gen_policy

/-- info: 'Pact.ClinicalTrial.clinical_trial_progresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms ClinicalTrial.clinical_trial_progresses

/-- info: 'Pact.ClinicalTrial.clinicalTrialPrefix_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms ClinicalTrial.clinicalTrialPrefix_steps

/-- info: 'Pact.ClinicalTrial.L17_visitCost_with_missing_field_heals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms ClinicalTrial.L17_visitCost_with_missing_field_heals

/-- info: 'Pact.ClinicalTrial.L18_patientId_self_heal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms ClinicalTrial.L18_patientId_self_heal

/-- info: 'Pact.ClinicalTrial.L17_heal_then_succeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms ClinicalTrial.L17_heal_then_succeed

/-- info: 'Pact.clinical_trial_visit_cost_projects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms clinical_trial_visit_cost_projects

/-- info: 'Pact.policyInstall_shrinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms policyInstall_shrinks

/-- info: 'Pact.Step.preserves_princOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms Step.preserves_princOk

/-- info: 'Pact.Steps.preserves_princOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms Steps.preserves_princOk

/-- info: 'Pact.principal_indices_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (info) in
#print axioms principal_indices_bounded

end Pact
