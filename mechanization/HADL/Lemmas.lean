-- Auxiliary lemmas for the substitution-based HADL model.
-- Phase B target: discharge the sorries in this file.

import HADL.Syntax
import HADL.Typing
import HADL.Policy
import HADL.Config
import HADL.Reduction

namespace HADL

/-- ErrCtx.retries grows by exactly 1 when we append a single error event. -/
theorem retries_append_error
    (ec : ErrCtx) (s : String) :
    ErrCtx.retries (ec ++ [Event.error s]) = ErrCtx.retries ec + 1 := by
  simp

/-- Appending a success event resets the retry counter. -/
theorem retries_append_success (ec : ErrCtx) :
    ErrCtx.retries (ec ++ [Event.success]) = 0 := by
  simp

end HADL
