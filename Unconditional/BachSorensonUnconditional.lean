import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import BachSorenson.Main

/-!
# The Bach–Sorenson bound (constant `7/2`), with GRH supplied by the riemann-hypothesis
# repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.
-/

theorem bachSorenson_unconditional : BachSorenson.BachSorensonBound (7 / 2) :=
  BachSorenson.bachSorenson_of_GRH LFunction_ne_zero_of_half_lt_re

#print axioms bachSorenson_unconditional
