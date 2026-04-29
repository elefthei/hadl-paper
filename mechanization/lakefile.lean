import Lake
open Lake DSL

package Pact

require "leanprover-community" / "batteries" @ git "v4.29.0"

require "leanprover-community" / "mathlib" @ git "v4.29.0"

require "amarmaduke" / "lean-subst" from git
  "https://github.com/amarmaduke/lean-subst" @ "main"

require "Cedar" from git
  "https://github.com/cedar-policy/cedar-spec" @ "main" / "cedar-lean"

@[default_target]
lean_lib Pact where
  defaultFacets := #[LeanLib.staticFacet]
