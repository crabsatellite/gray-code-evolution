/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCType
import Mathlib.Order.Fin.Basic



namespace Hamilton.Infrastructure

namespace NC

/-- `Finset.univ : Finset (Fin (n+1))` is nonempty. -/
theorem fin_univ_succ_nonempty (n : ℕ) :
    (Finset.univ : Finset (Fin (n+1))).Nonempty :=
  ⟨0, Finset.mem_univ _⟩

/-- The max element of `Finset.univ : Finset (Fin (n+1))` is `Fin.last n`. -/
theorem fin_univ_succ_max_eq (n : ℕ) :
    (Finset.univ : Finset (Fin (n+1))).max' (fin_univ_succ_nonempty n) =
      Fin.last n := by
  apply le_antisymm
  · apply Finset.max'_le
    intro a _
    exact Fin.le_last a
  · exact Finset.le_max' _ _ (Finset.mem_univ _)

end NC

end Hamilton.Infrastructure
