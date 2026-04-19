import Lake
open Lake DSL

package HADL

require "leanprover-community" / "batteries" @ git "v4.29.0"

require "leanprover-community" / "mathlib" @ git "v4.29.0"

require "Cedar" from git
  "https://github.com/cedar-policy/cedar-spec" @ "main" / "cedar-lean"

@[default_target]
lean_lib HADL where
  defaultFacets := #[LeanLib.staticFacet]
