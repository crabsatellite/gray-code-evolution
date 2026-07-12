/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.PetersenGlobalCycle

/-!
# Hamilton cycles for every even order at least four

`PetersenGlobalCycle` gives one uniform Boolean-block construction throughout
this range.  Separate explicit certificates for `n = 4` and `n = 6` are kept
as independent checks, but the theorem below does not depend on enumeration.
-/

namespace Hamilton.Infrastructure

namespace NC

open SimpleGraph

/-- The positive half of the complete classification. -/
theorem NCRefinementGraph_fin_even_geq4_isHamiltonian_proved
    (n : ℕ) (h_even : Even n) (h_ge_four : 4 <= n) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).IsHamiltonian :=
  NCRefinementGraph_fin_even_geq4_isHamiltonian_petersen n h_even h_ge_four

end NC

end Hamilton.Infrastructure
