/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCRecursion
import Hamilton.Infrastructure.FinHelpers



namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore)

/-- K-S recursion applied to `Finset.univ : Finset (Fin (n+1))`. -/
theorem KS_recursion_fin (n : ℕ) :
    Fintype.card (NC (Finset.univ : Finset (Fin (n+1)))) =
      ∑ S ∈ (Finset.univ : Finset (Fin (n+1))).powerset.filter
        (fun S => S.Nonempty ∧ Fin.last n ∈ S),
        ∏ x ∈ S.attach, Fintype.card (NC (gapBefore
          (Finset.univ : Finset (Fin (n+1))) S x.1)) := by
  have h_max : (Finset.univ : Finset (Fin (n+1))).max'
      (fin_univ_succ_nonempty n) = Fin.last n :=
    fin_univ_succ_max_eq n
  have := card_eq_sum_prod_gap (s := (Finset.univ : Finset (Fin (n+1))))
    (fin_univ_succ_nonempty n)
  rw [h_max] at this
  exact this

end NC

end Hamilton.Infrastructure
