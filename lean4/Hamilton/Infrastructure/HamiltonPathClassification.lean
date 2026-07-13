/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.HamiltonianClassification
import Hamilton.Infrastructure.Connectivity
import Hamilton.Infrastructure.CardThreeHamiltonPath

/-!
# Complete Hamilton-path classification

The refinement graph on noncrossing partitions of `[n]` has a Hamilton path
exactly when `n <= 3` or `n` is even.

The proof has three independent ingredients.

* Orders zero and one are singleton graphs; order two is the single edge
  between `bot` and `top`; order three has an explicit five-vertex path
  alternating between its two rank-parity classes.
* For even `n >= 4`, delete one edge from the already constructed Hamilton
  cycle.
* For odd `n >= 5`, the signed block-parity count has absolute value
  `catalan ((n - 1) / 2) >= 2`.  A Hamilton path in a bipartite graph can
  leave its two colour classes imbalanced by at most one, so no such path
  exists.
-/

namespace Hamilton.Infrastructure

namespace NC

open SimpleGraph

/-- The order-zero refinement graph has a Hamilton path. -/
theorem NCRefinementGraph_fin_zero_isHamiltonianPath :
    (NCRefinementGraph (Finset.univ : Finset (Fin 0))).IsHamiltonianPath := by
  letI : Subsingleton (NC (Finset.univ : Finset (Fin 0))) :=
    Fintype.card_le_one_iff_subsingleton.mp (by
      rw [card_NC_univ_fin_zero, catalan_zero])
  let v : NC (Finset.univ : Finset (Fin 0)) := bot _
  exact ⟨v, v, HamiltonianPathBetween.of_subsingleton _ v v⟩

/-- The order-one refinement graph has a Hamilton path. -/
theorem NCRefinementGraph_fin_one_isHamiltonianPath :
    (NCRefinementGraph (Finset.univ : Finset (Fin 1))).IsHamiltonianPath := by
  letI : Subsingleton (NC (Finset.univ : Finset (Fin 1))) :=
    Fintype.card_le_one_iff_subsingleton.mp (by
      rw [card_NC_univ_fin_one, catalan_one])
  let v : NC (Finset.univ : Finset (Fin 1)) := bot _
  exact ⟨v, v, HamiltonianPathBetween.of_subsingleton _ v v⟩

/-- The order-two refinement graph is the single edge `bot -- top`, hence has
a Hamilton path. -/
theorem NCRefinementGraph_fin_two_isHamiltonianPath :
    (NCRefinementGraph (Finset.univ : Finset (Fin 2))).IsHamiltonianPath := by
  classical
  let s : Finset (Fin 2) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  have hbt : bot s ≠ top hs := bot_ne_top_fin_two
  obtain ⟨w⟩ := (NCRefinementGraph_connected hs).preconnected (bot s) (top hs)
  let next : NC s := w.snd
  have h_adj_next : (NCRefinementGraph s).Adj (bot s) next :=
    w.adj_snd (SimpleGraph.Walk.not_nil_of_ne hbt)
  have h_next_top : next = top hs := by
    rcases nc_fin_two_eq_bot_or_top next with h | h
    · have h' : next = bot s := by simpa [s] using h
      rw [h'] at h_adj_next
      exact False.elim ((NCRefinementGraph s).irrefl h_adj_next)
    · simpa [s] using h
  have h_adj : (NCRefinementGraph s).Adj (bot s) (top hs) := by
    simpa [h_next_top] using h_adj_next
  let p : (NCRefinementGraph s).Walk (bot s) (top hs) :=
    SimpleGraph.Walk.cons h_adj SimpleGraph.Walk.nil
  refine ⟨bot s, top hs, p, ?_⟩
  intro v
  rcases nc_fin_two_eq_bot_or_top v with rfl | rfl
  · simp [p, s, hbt]
  · simp [p, s, hbt]

/-- The order-three refinement graph has an explicit path through all five
vertices: two distinct two-block partitions occur as endpoints, with the
third two-block partition, `top`, and `bot` in between. -/
theorem NCRefinementGraph_fin_three_isHamiltonianPath :
    (NCRefinementGraph (Finset.univ : Finset (Fin 3))).IsHamiltonianPath := by
  classical
  let s : Finset (Fin 3) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  have hcard : s.card = 3 := by simp [s]
  have h0 : (0 : Fin 3) ∈ s := by simp [s]
  have h1 : (1 : Fin 3) ∈ s := by simp [s]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  let v0 : NC s := cardThreeTwoBlockNCByElem s hcard 0 h0
  let v1 : NC s := cardThreeTwoBlockNCByElem s hcard 1 h1
  refine ⟨v0, v1, ?_⟩
  exact cardThree_hamiltonianPath_between_twoBlock
    hcard hs h0 h1 h01

/-- In an NCR graph with a Hamilton path, the even- and odd-block classes
differ in size by at most one. -/
theorem NCRefinementGraph_evenBlocks_oddBlocks_diff_at_most_one_of_isHamiltonianPath
    {alpha : Type*} [LinearOrder alpha] (s : Finset alpha)
    (hG : (NCRefinementGraph s).IsHamiltonianPath) :
    (evenBlocks s).card ≤ (oddBlocks s).card + 1 ∧
      (oddBlocks s).card ≤ (evenBlocks s).card + 1 := by
  have h := hG.classes_card_diff_at_most_one (numBlocksBoolColoring s)
  rw [← oddBlocks_eq_filter_color_true, ← evenBlocks_eq_filter_color_false] at h
  exact ⟨h.2, h.1⟩

/-- For every odd `n >= 5`, the refinement graph has no Hamilton path. -/
theorem NCRefinementGraph_fin_odd_geq5_not_isHamiltonianPath
    (n : Nat) (hn : Odd n) (hn5 : 5 ≤ n) :
    ¬ (NCRefinementGraph (Finset.univ : Finset (Fin n))).IsHamiltonianPath := by
  intro hG
  obtain ⟨m, rfl⟩ := hn
  have hm2 : 2 ≤ m := by omega
  have hcat : 2 ≤ catalan m := by
    have hmono := Nat.catalan_mono hm2
    rwa [catalan_two] at hmono
  have hbalance :=
    NCRefinementGraph_evenBlocks_oddBlocks_diff_at_most_one_of_isHamiltonianPath
      (Finset.univ : Finset (Fin (2 * m + 1))) hG
  have hdiff :=
    signedNCCount_eq_evenBlocks_sub_oddBlocks
      (Finset.univ : Finset (Fin (2 * m + 1)))
  rw [signedNCCount_univ_eq_signedDyckSumTree,
    signedDyckSumTree_two_mul_succ] at hdiff
  rcases Nat.even_or_odd (m + 1) with heven | hodd
  · rw [heven.neg_one_pow, one_mul] at hdiff
    omega
  · rw [hodd.neg_one_pow, neg_one_mul] at hdiff
    omega

/-- Complete Hamilton-path classification for the noncrossing-partition
refinement graph on `[n]`. -/
theorem NCRefinementGraph_fin_isHamiltonianPath_iff (n : Nat) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).IsHamiltonianPath ↔
      n ≤ 3 ∨ Even n := by
  constructor
  · intro hG
    by_cases hn3 : n ≤ 3
    · exact Or.inl hn3
    · right
      by_contra hneven
      have hodd : Odd n := Nat.not_even_iff_odd.mp hneven
      have hn5 : 5 ≤ n := by
        rcases hodd with ⟨m, hm⟩
        omega
      exact NCRefinementGraph_fin_odd_geq5_not_isHamiltonianPath
        n hodd hn5 hG
  · rintro (hn3 | heven)
    · interval_cases n
      · exact NCRefinementGraph_fin_zero_isHamiltonianPath
      · exact NCRefinementGraph_fin_one_isHamiltonianPath
      · exact NCRefinementGraph_fin_two_isHamiltonianPath
      · exact NCRefinementGraph_fin_three_isHamiltonianPath
    · by_cases hn4 : 4 ≤ n
      · have hcycle :=
          NCRefinementGraph_fin_even_geq4_isHamiltonian_proved n heven hn4
        apply hcycle.isHamiltonianPath
        rw [card_NC_eq_catalan_card]
        simp only [Finset.card_univ, Fintype.card_fin]
        have hmono := Nat.catalan_mono hn4
        rw [catalan_four] at hmono
        omega
      · have hn3 : n ≤ 3 := by omega
        interval_cases n
        · exact NCRefinementGraph_fin_zero_isHamiltonianPath
        · exact NCRefinementGraph_fin_one_isHamiltonianPath
        · exact NCRefinementGraph_fin_two_isHamiltonianPath
        · exact NCRefinementGraph_fin_three_isHamiltonianPath

end NC

end Hamilton.Infrastructure
