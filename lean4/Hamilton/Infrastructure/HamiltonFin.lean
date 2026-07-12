/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.HamiltonTrivial
import Hamilton.Infrastructure.FinHelpers
import Hamilton.Infrastructure.CardFin2Final



namespace Hamilton.Infrastructure

namespace NC

/-- `NCRefinementGraph` for `Finset.univ : Finset (Fin 0)` is Hamiltonian. -/
theorem NCRefinementGraph_fin_zero_isHamiltonian :
    (NCRefinementGraph (Finset.univ : Finset (Fin 0))).IsHamiltonian := by
  have huniv_empty : (Finset.univ : Finset (Fin 0)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x _
    exact Fin.elim0 x
  rw [huniv_empty]
  exact NCRefinementGraph_isHamiltonian_of_empty

/-- `NCRefinementGraph` for `Finset.univ : Finset (Fin 1)` is Hamiltonian. -/
theorem NCRefinementGraph_fin_one_isHamiltonian :
    (NCRefinementGraph (Finset.univ : Finset (Fin 1))).IsHamiltonian := by
  have huniv_singleton : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro x _
    exact Subsingleton.elim x 0
  rw [huniv_singleton]
  exact NCRefinementGraph_isHamiltonian_of_singleton _


theorem NCRefinementGraph_fin_two_not_isHamiltonian :
    ¬ (NCRefinementGraph (Finset.univ : Finset (Fin 2))).IsHamiltonian :=
  SimpleGraph.not_isHamiltonian_of_card_eq_two card_NC_univ_fin_two

end NC

end Hamilton.Infrastructure
