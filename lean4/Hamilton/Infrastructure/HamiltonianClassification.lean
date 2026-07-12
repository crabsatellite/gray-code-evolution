/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.SignedDyckInvolution
import Hamilton.Infrastructure.EvenHamiltonian
import Hamilton.Infrastructure.HamiltonFin
import Hamilton.Infrastructure.HamiltonFinParity
import Hamilton.Infrastructure.NCRBipartiteHamilton
import Hamilton.Infrastructure.CatalanPos
import Mathlib.Tactic.IntervalCases

/-!
# Complete Hamiltonicity classification

This module states the complete classification.  The odd obstruction comes
from the bipartition by
block-count parity and a sign-reversing involution proving that the two colour
classes have unequal size.  The even construction is imported from
`EvenHamiltonian`.
-/

namespace Hamilton.Infrastructure

namespace NC

open SimpleGraph

/-- For every odd `n >= 3`, the refinement graph cannot have a Hamilton cycle. -/
theorem NCRefinementGraph_fin_odd_geq3_not_isHamiltonian
    (n : ℕ) (hn : Odd n) (hn3 : 3 <= n) :
    ¬ (NCRefinementGraph (Finset.univ : Finset (Fin n))).IsHamiltonian := by
  apply NCRefinementGraph_not_isHamiltonian_of_bipartite_unbalanced
  · have h_cat : Fintype.card (NC (Finset.univ : Finset (Fin n))) = catalan n := by
      rw [card_NC_eq_catalan_card]
      simp
    rw [h_cat]
    have h_mono : catalan 3 <= catalan n := Nat.catalan_mono hn3
    rw [catalan_three] at h_mono
    omega
  · exact evenBlocks_card_ne_oddBlocks_card_fin_odd_unconditional n hn

/--
The refinement graph of the noncrossing partition lattice on `[n]` has a
Hamilton cycle exactly for `n = 0`, `n = 1`, or even `n >= 4`.
-/
theorem NCRefinementGraph_fin_isHamiltonian_iff (n : ℕ) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).IsHamiltonian ↔
      n = 0 ∨ n = 1 ∨ (Even n ∧ 4 <= n) := by
  constructor
  · intro hG
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · interval_cases n
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd hG NCRefinementGraph_fin_two_not_isHamiltonian
      · exact absurd hG NCRefinementGraph_fin_three_not_isHamiltonian
    · by_cases hev : Even n
      · exact Or.inr (Or.inr ⟨hev, hn4⟩)
      · have hodd : Odd n := Nat.not_even_iff_odd.mp hev
        exact absurd hG (NCRefinementGraph_fin_odd_geq3_not_isHamiltonian n hodd (by omega))
  · rintro (rfl | rfl | ⟨hev, hn4⟩)
    · exact NCRefinementGraph_fin_zero_isHamiltonian
    · exact NCRefinementGraph_fin_one_isHamiltonian
    · exact NCRefinementGraph_fin_even_geq4_isHamiltonian_proved n hev hn4

end NC

end Hamilton.Infrastructure
