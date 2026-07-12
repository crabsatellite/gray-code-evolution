/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCBoundary
import Mathlib.Combinatorics.Enumerative.Catalan.Basic



namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α]

/-- `|NC ∅| = catalan 0`. -/
theorem card_empty_eq_catalan_zero :
    Fintype.card (NC (∅ : Finset α)) = catalan 0 := by
  rw [card_empty, catalan_zero]

/-- `|NC {x}| = catalan 1`. -/
theorem card_singleton_eq_catalan_one (x : α) :
    Fintype.card (NC ({x} : Finset α)) = catalan 1 := by
  rw [card_singleton, catalan_one]

/-- `|NC (Finset.univ : Finset (Fin 0))| = catalan 0 = 1`. -/
theorem card_NC_univ_fin_zero :
    Fintype.card (NC (Finset.univ : Finset (Fin 0))) = catalan 0 := by
  have huniv_empty : (Finset.univ : Finset (Fin 0)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x _
    exact Fin.elim0 x
  rw [huniv_empty]
  exact card_empty_eq_catalan_zero

/-- `|NC (Finset.univ : Finset (Fin 1))| = catalan 1 = 1`. -/
theorem card_NC_univ_fin_one :
    Fintype.card (NC (Finset.univ : Finset (Fin 1))) = catalan 1 := by
  have huniv_singleton : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro x _
    exact Subsingleton.elim x 0
  rw [huniv_singleton]
  exact card_singleton_eq_catalan_one _

/-- `catalan 2 = 2`. -/
theorem catalan_two : catalan 2 = 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, catalan_succ]
  simp [catalan_succ, catalan_zero, Fin.sum_univ_two]

/-- `catalan 3 = 5`. -/
theorem catalan_three : catalan 3 = 5 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, catalan_succ]
  simp [Fin.sum_univ_three, catalan_zero, catalan_one, catalan_two]

/-- `catalan 4 = 14`. -/
theorem catalan_four : catalan 4 = 14 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, catalan_succ]
  simp [Fin.sum_univ_four, catalan_zero, catalan_one, catalan_two, catalan_three]

/-- `catalan 5 = 42`. -/
theorem catalan_five : catalan 5 = 42 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, catalan_succ]
  simp [Fin.sum_univ_five, catalan_zero, catalan_one, catalan_two,
    catalan_three, catalan_four]

/-- `catalan 6 = 132`. -/
theorem catalan_six : catalan 6 = 132 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, catalan_succ]
  simp [Fin.sum_univ_six, catalan_zero, catalan_one, catalan_two,
    catalan_three, catalan_four, catalan_five]

/-- `catalan 7 = 429`. -/
theorem catalan_seven : catalan 7 = 429 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, catalan_succ]
  simp [Fin.sum_univ_seven, catalan_zero, catalan_one, catalan_two,
    catalan_three, catalan_four, catalan_five, catalan_six]

end NC

end Hamilton.Infrastructure
