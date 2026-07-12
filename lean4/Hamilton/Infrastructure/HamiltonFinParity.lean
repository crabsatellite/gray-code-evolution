/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.HamiltonPath
import Hamilton.Infrastructure.Bipartite
import Hamilton.Infrastructure.CardNCInduction
import Hamilton.Infrastructure.HamiltonFin
import Hamilton.Infrastructure.CatalanPos



namespace Hamilton.Infrastructure

namespace NC

open SimpleGraph

/-- **General negative result**: NCR(Fin n) for `n ≥ 3` with
`Odd (catalan n)` is NOT Hamiltonian. -/
theorem NCRefinementGraph_fin_not_isHamiltonian_of_odd_catalan
    (n : ℕ) (hodd : Odd (catalan n)) (hn3 : 3 ≤ n) :
    ¬ (NCRefinementGraph (Finset.univ : Finset (Fin n))).IsHamiltonian := by
  have hcard : Fintype.card (NC (Finset.univ : Finset (Fin n))) = catalan n := by
    rw [card_NC_eq_catalan_card]
    simp
  have h_card3 : 3 ≤ Fintype.card (NC (Finset.univ : Finset (Fin n))) := by
    rw [hcard]
    have h_mono : catalan 3 ≤ catalan n := Nat.catalan_mono hn3
    rw [catalan_three] at h_mono
    omega
  have h_bipart : (NCRefinementGraph (Finset.univ : Finset (Fin n))).Colorable 2 :=
    NCRefinementGraph_isBipartite
  have h_odd_card : Odd (Fintype.card (NC (Finset.univ : Finset (Fin n)))) := by
    rw [hcard]; exact hodd
  exact SimpleGraph.not_isHamiltonian_of_colorable_two_odd h_bipart h_odd_card h_card3

/-- `NCR(Fin 3)` is **NOT** Hamiltonian: bipartite + |NC(Fin 3)| =
`catalan 3 = 5` is odd. -/
theorem NCRefinementGraph_fin_three_not_isHamiltonian :
    ¬ (NCRefinementGraph (Finset.univ : Finset (Fin 3))).IsHamiltonian := by
  intro hG
  have hcard : Fintype.card (NC (Finset.univ : Finset (Fin 3))) = 5 := by
    rw [card_NC_eq_catalan_card]
    simp [catalan_three]
  have hn1 : Fintype.card (NC (Finset.univ : Finset (Fin 3))) ≠ 1 := by
    rw [hcard]; omega
  have h_bipart : (NCRefinementGraph (Finset.univ : Finset (Fin 3))).Colorable 2 :=
    NCRefinementGraph_isBipartite
  have h_even : Even (Fintype.card (NC (Finset.univ : Finset (Fin 3)))) :=
    hG.even_card_of_colorable_two h_bipart hn1
  rw [hcard] at h_even
  exact (Nat.not_even_iff_odd.mpr ⟨2, rfl⟩) h_even

/-- `NCR(Fin 7)` is **NOT** Hamiltonian: bipartite + `catalan 7 = 429`
is odd. -/
theorem NCRefinementGraph_fin_seven_not_isHamiltonian :
    ¬ (NCRefinementGraph (Finset.univ : Finset (Fin 7))).IsHamiltonian := by
  intro hG
  have hcard : Fintype.card (NC (Finset.univ : Finset (Fin 7))) = 429 := by
    rw [card_NC_eq_catalan_card]
    simp [catalan_seven]
  have hn1 : Fintype.card (NC (Finset.univ : Finset (Fin 7))) ≠ 1 := by
    rw [hcard]; omega
  have h_bipart : (NCRefinementGraph (Finset.univ : Finset (Fin 7))).Colorable 2 :=
    NCRefinementGraph_isBipartite
  have h_even : Even (Fintype.card (NC (Finset.univ : Finset (Fin 7)))) :=
    hG.even_card_of_colorable_two h_bipart hn1
  rw [hcard] at h_even
  exact (Nat.not_even_iff_odd.mpr ⟨214, rfl⟩) h_even

/-- **Generic NCR not Hamilton from odd catalan**: for any `s` with
`3 ≤ s.card` and `Odd (catalan s.card)`, NCR(s) is not Hamiltonian. -/
theorem NCRefinementGraph_not_isHamiltonian_of_odd_catalan
    {α : Type*} [LinearOrder α] (s : Finset α)
    (hcard : 3 ≤ s.card) (hodd : Odd (catalan s.card)) :
    ¬ (NCRefinementGraph s).IsHamiltonian := by
  intro hG
  have hcard_NC : Fintype.card (NC s) = catalan s.card := card_NC_eq_catalan_card s
  have h_card3 : 3 ≤ Fintype.card (NC s) := by
    rw [hcard_NC]
    have h_mono : catalan 3 ≤ catalan s.card := Nat.catalan_mono hcard
    rw [catalan_three] at h_mono
    omega
  have h_bipart : (NCRefinementGraph s).Colorable 2 :=
    NCRefinementGraph_isBipartite
  have h_odd_card : Odd (Fintype.card (NC s)) := by
    rw [hcard_NC]; exact hodd
  exact SimpleGraph.not_isHamiltonian_of_colorable_two_odd
    h_bipart h_odd_card h_card3 hG

end NC

end Hamilton.Infrastructure
