/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.Adjacency
import Hamilton.Infrastructure.NumBlocksParity
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The refinement graph is bipartite

The `NCRefinementGraph s` is **bipartite**: its 2-coloring is given
by the parity of `numBlocks`.  Adjacent partitions differ in
`numBlocks` by exactly 1 (`Adj_numBlocks_diff`), hence have different
parities.

## Main results

* `NC.numBlocksParity` — coloring function `NC s → Fin 2`.
* `NCRefinementGraph_isBipartite` — `NCRefinementGraph s` is bipartite.

## Tags

noncrossing partition, refinement graph, bipartite, coloring
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- Adjacent partitions have different `numBlocksParity` values. -/
theorem numBlocksParity_ne_of_adj {π σ : NC s} (h : Adj π σ) :
    numBlocksParity π ≠ numBlocksParity σ := by
  rcases Adj_numBlocks_diff h with h1 | h2
  · intro heq
    have hval : numBlocks π % 2 = numBlocks σ % 2 := by
      have := Fin.mk.inj_iff.mp heq
      exact this
    omega
  · intro heq
    have hval : numBlocks π % 2 = numBlocks σ % 2 := by
      have := Fin.mk.inj_iff.mp heq
      exact this
    omega

theorem numBlocksParityBool_ne_of_adj {π σ : NC s} (h : Adj π σ) :
    numBlocksParityBool π ≠ numBlocksParityBool σ := by
  unfold numBlocksParityBool
  rcases Adj_numBlocks_diff h with h1 | h2 <;>
    (intro heq;
     have : (numBlocks π % 2 = 0) ↔ (numBlocks σ % 2 = 0) := by
       constructor <;> intro h_eq <;> simp_all <;> omega
     have h0 : numBlocks π % 2 = numBlocks σ % 2 := by
       have hπ : numBlocks π % 2 = 0 ∨ numBlocks π % 2 = 1 := by omega
       have hσ : numBlocks σ % 2 = 0 ∨ numBlocks σ % 2 = 1 := by omega
       rcases hπ with hπ | hπ <;> rcases hσ with hσ | hσ <;> simp_all
     omega)

end NC

open SimpleGraph

/-- **NCR `Bool`-coloring** via `numBlocksParityBool`. -/
def NCRefinementGraph.boolColoring {α : Type*} [LinearOrder α]
    {s : Finset α} : (NCRefinementGraph s).Coloring Bool :=
  SimpleGraph.Coloring.mk NC.numBlocksParityBool
    (fun {_ _} h => NC.numBlocksParityBool_ne_of_adj h)

/-- The `NCRefinementGraph s` is bipartite: 2-coloring via
`numBlocksParity` (parity of `numBlocks`).  Adjacent vertices differ
in `numBlocks` by exactly 1 (`Adj_numBlocks_diff`), so have opposite
parities. -/
theorem NCRefinementGraph_isBipartite {α : Type*} [LinearOrder α]
    {s : Finset α} : (NCRefinementGraph s).IsBipartite :=
  ⟨SimpleGraph.Coloring.mk NC.numBlocksParity
    (fun {_ _} h => NC.numBlocksParity_ne_of_adj h)⟩

end Hamilton.Infrastructure
