-- HADL/AxiomCheck.lean
-- Axiom-drift guard: this file fails to compile if any main theorem
-- introduces an axiom beyond [propext, Classical.choice, Quot.sound].
-- Any failure here is a RED FLAG — investigate before silencing.

import HADL.Soundness
import HADL.Safety
import HADL.Scope
import HADL.Examples

namespace HADL

/-- info: 'HADL.T1_WF_preservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T1_WF_preservation

/-- info: 'HADL.T2_staged_materialization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T2_staged_materialization

/-- info: 'HADL.T3_policy_monotonicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T3_policy_monotonicity

/-- info: 'HADL.T4_budget_no_heal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_budget_no_heal

/-- info: 'HADL.T4_truthful_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success

/-- info: 'HADL.T4_truthful_success_agent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success_agent

/-- info: 'HADL.T4_truthful_success_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success_gen

/-- info: 'HADL.T4_progress_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_progress_gen

/-- info: 'HADL.T4_progress_agent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_progress_agent

/-- info: 'HADL.T4_truthful_success_arrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success_arrow

/-- info: 'HADL.T4_truthful_success_healable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success_healable

/-- info: 'HADL.nested_array_of_schema_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms nested_array_of_schema_succeeds

/-- info: 'HADL.T4_truthful_success_gen_healable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_truthful_success_gen_healable

/-- info: 'HADL.T4_progress_gen_healable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_progress_gen_healable

/-- info: 'HADL.T4_progress_gen_policy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms T4_progress_gen_policy

/-- info: 'HADL.ClinicalTrial.clinical_trial_progresses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms ClinicalTrial.clinical_trial_progresses

/-- info: 'HADL.ClinicalTrial.clinicalTrialPrefix_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms ClinicalTrial.clinicalTrialPrefix_steps

/-- info: 'HADL.ClinicalTrial.L17_visitCost_with_missing_field_heals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms ClinicalTrial.L17_visitCost_with_missing_field_heals

/-- info: 'HADL.ClinicalTrial.L18_patientId_self_heal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms ClinicalTrial.L18_patientId_self_heal

/-- info: 'HADL.ClinicalTrial.L17_heal_then_succeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms ClinicalTrial.L17_heal_then_succeed

/-- info: 'HADL.clinical_trial_visit_cost_projects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms clinical_trial_visit_cost_projects

/-- info: 'HADL.policyInstall_shrinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms policyInstall_shrinks

/-- info: 'HADL.Step.preserves_princOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms Step.preserves_princOk

/-- info: 'HADL.Steps.preserves_princOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms Steps.preserves_princOk

/-- info: 'HADL.principal_indices_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info) in
#print axioms principal_indices_bounded

end HADL
