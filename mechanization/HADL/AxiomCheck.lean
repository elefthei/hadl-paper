-- HADL/AxiomCheck.lean
-- Axiom-drift guard: this file fails to compile if any main theorem
-- introduces an axiom beyond [propext, Classical.choice, Quot.sound].
-- Any failure here is a RED FLAG — investigate before silencing.

import HADL.Soundness
import HADL.Safety
import HADL.Safety2

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

end HADL
