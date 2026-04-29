-- Root module: re-exports all public definitions and theorems of the Pact
-- mechanization.
--
-- Soundness scope:
--   T1 WF-Preservation            — proven in Pact.Soundness
--   T2 Staged Materialization     — proven in Pact.Soundness
--   T3 Policy Monotonicity        — proven in Pact.Soundness
--   T4 Oracle-Relative Safety     — T4a/T4b root + T4c congruence-lifted in Pact.Safety

import Pact.Syntax
import Pact.Typing
import Pact.Policy
import Pact.Oracle
import Pact.JsAxioms
import Pact.Config
import Pact.Reduction
import Pact.Scope
import Pact.Soundness
import Pact.Safety
import Pact.AxiomCheck
import Pact.Examples
