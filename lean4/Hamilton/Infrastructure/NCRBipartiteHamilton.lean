/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.Bipartite
import Hamilton.Infrastructure.NCBipartiteCounts
import Hamilton.Infrastructure.BipartiteHamiltonBalance



namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α]

open SimpleGraph

/-- `Bool`-valued coloring of `NCR(s)` via `numBlocks` parity: `true`
if odd, `false` if even. -/
noncomputable def numBlocksBoolColoring (s : Finset α) :
    (NCRefinementGraph s).Coloring Bool :=
  SimpleGraph.Coloring.mk (fun π => decide (Odd (numBlocks π)))
    (fun {π σ} h => by
      rcases Adj_numBlocks_diff h with h1 | h2
      · -- numBlocks σ = numBlocks π + 1: opposite parities
        intro heq
        simp only [decide_eq_decide] at heq
        rw [h1, Nat.odd_add_one] at heq
        tauto
      · -- numBlocks π = numBlocks σ + 1: opposite parities
        intro heq
        simp only [decide_eq_decide] at heq
        rw [h2, Nat.odd_add_one] at heq
        tauto)

/-- Computational unfolding: `numBlocksBoolColoring s π` equals
`decide (Odd (numBlocks π))`. -/
theorem numBlocksBoolColoring_apply (s : Finset α) (π : NC s) :
    numBlocksBoolColoring s π = decide (Odd (numBlocks π)) := rfl

/-- `filter (color = true)` is precisely `oddBlocks s`. -/
theorem oddBlocks_eq_filter_color_true (s : Finset α) :
    oddBlocks s =
      (Finset.univ : Finset (NC s)).filter
        (fun π => numBlocksBoolColoring s π = true) := by
  ext π
  simp only [oddBlocks, Finset.mem_filter, Finset.mem_univ, true_and,
    numBlocksBoolColoring_apply, decide_eq_true_eq]

/-- `filter (color = false)` is precisely `evenBlocks s`. -/
theorem evenBlocks_eq_filter_color_false (s : Finset α) :
    evenBlocks s =
      (Finset.univ : Finset (NC s)).filter
        (fun π => numBlocksBoolColoring s π = false) := by
  ext π
  simp only [evenBlocks, Finset.mem_filter, Finset.mem_univ, true_and,
    numBlocksBoolColoring_apply, decide_eq_false_iff_not, Nat.not_odd_iff_even]


theorem NCRefinementGraph_evenBlocks_card_eq_oddBlocks_card_of_isHamiltonian
    (s : Finset α) (hcard : Fintype.card (NC s) ≠ 1)
    (hG : (NCRefinementGraph s).IsHamiltonian) :
    (evenBlocks s).card = (oddBlocks s).card := by
  rw [evenBlocks_eq_filter_color_false, oddBlocks_eq_filter_color_true]
  exact (hG.classes_card_eq (numBlocksBoolColoring s) hcard).symm

/-- **NCR bipartite imbalance obstruction**: if `|evenBlocks s|
≠ |oddBlocks s|`, then NCR(s) is **NOT** Hamiltonian. -/
theorem NCRefinementGraph_not_isHamiltonian_of_bipartite_unbalanced
    (s : Finset α) (hcard : Fintype.card (NC s) ≠ 1)
    (h_ne : (evenBlocks s).card ≠ (oddBlocks s).card) :
    ¬ (NCRefinementGraph s).IsHamiltonian := fun hG =>
  h_ne (NCRefinementGraph_evenBlocks_card_eq_oddBlocks_card_of_isHamiltonian
    s hcard hG)

end NC

end Hamilton.Infrastructure
