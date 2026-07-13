/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.ParentMergeNoncrossing
import Hamilton.Infrastructure.Adjacency



namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The **parent-merge** of `B` in `π`, packaged as an `NC s` element. -/
noncomputable def parentMergeNC (π : NC s) (B : Finset α)
    (hne : B.Nonempty) (hB_mem : B ∈ π.val.parts)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) : NC s :=
  ⟨parentMergeFinpartition π B hne hB_mem h_nonRoot,
   parent_merge_noncrossing π hB_mem hne h_nonRoot⟩

/-- The parent-merge reduces `numBlocks` by exactly 1. -/
theorem parentMergeNC_numBlocks (π : NC s) (B : Finset α)
    (hne : B.Nonempty) (hB_mem : B ∈ π.val.parts)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    numBlocks (parentMergeNC π B hne hB_mem h_nonRoot) + 1 =
      numBlocks π :=
  parentMergeFinpartition_card π B hne hB_mem h_nonRoot

/-- `π` `mergesTo` its parent-merge.  Direct from the `mergesTo`
definition: the witnessing pair is `(B, parentBlock π B)`. -/
theorem mergesTo_parentMergeNC (π : NC s) (B : Finset α)
    (hne : B.Nonempty) (hB_mem : B ∈ π.val.parts)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    mergesTo π (parentMergeNC π B hne hB_mem h_nonRoot) := by
  refine ⟨B, hB_mem,
          parentBlock π B hne,
          parentBlock_mem π B hne h_nonRoot,
          Ne.symm (parentBlock_ne_self π B hne h_nonRoot), ?_⟩
  unfold parentMergeNC
  simp only
  rw [parentMergeFinpartition_parts]

/-- The parent-merge is an `NCRefinementGraph`-neighbour of `π`. -/
theorem NCRefinementGraph_adj_parentMergeNC (π : NC s) (B : Finset α)
    (hne : B.Nonempty) (hB_mem : B ∈ π.val.parts)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    (NCRefinementGraph s).Adj π
      (parentMergeNC π B hne hB_mem h_nonRoot) :=
  Or.inl (mergesTo_parentMergeNC π B hne hB_mem h_nonRoot)

end NC

end Hamilton.Infrastructure
