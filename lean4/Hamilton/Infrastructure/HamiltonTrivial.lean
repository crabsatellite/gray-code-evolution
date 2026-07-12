/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.Adjacency
import Hamilton.Infrastructure.CatalanBase
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Trivial Hamilton cases for `NCRefinementGraph`

By Mathlib's convention (`SimpleGraph.IsHamiltonian`), a graph with
exactly one vertex is trivially Hamiltonian.

For `|s| ≤ 1` we have `|NC s| = 1`, so the refinement graph is
trivially Hamiltonian.

## Main results

* `NC.NCRefinementGraph_isHamiltonian_of_empty` — `NCR ∅` is
  Hamiltonian (singleton).
* `NC.NCRefinementGraph_isHamiltonian_of_singleton` — `NCR {x}` is
  Hamiltonian (singleton).

## Tags

NC, refinement graph, Hamilton, base case
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α]

/-- `NCRefinementGraph ∅` is Hamiltonian (trivially: only one vertex). -/
theorem NCRefinementGraph_isHamiltonian_of_empty :
    (NCRefinementGraph (∅ : Finset α)).IsHamiltonian := by
  intro h
  exact absurd card_empty h

/-- `NCRefinementGraph {x}` is Hamiltonian (trivially: only one vertex). -/
theorem NCRefinementGraph_isHamiltonian_of_singleton (x : α) :
    (NCRefinementGraph ({x} : Finset α)).IsHamiltonian := by
  intro h
  exact absurd (card_singleton x) h

end NC

end Hamilton.Infrastructure
