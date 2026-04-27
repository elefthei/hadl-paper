-- Root module: re-exports all public definitions and theorems of the HADL
-- mechanization.
--
-- Soundness scope:
--   T1 WF-Preservation            — proven in HADL.Soundness
--   T2 Staged Materialization     — proven in HADL.Soundness
--   T3 Policy Monotonicity        — proven in HADL.Soundness
--   T4 Oracle-Relative Safety     — T4a/T4b root + T4c congruence-lifted in HADL.Safety

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Oracle
import HADL.JsAxioms
import HADL.Config
import HADL.Reduction
import HADL.Scope
import HADL.Soundness
import HADL.Safety
import HADL.AxiomCheck
import HADL.Examples
