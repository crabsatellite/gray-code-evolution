/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NestingForest
import Hamilton.Infrastructure.MergeBlocks



namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The **parent-merge** of `B` in `π`: the `Finpartition` obtained
by merging `B` with `parentBlock π B`. -/
noncomputable def parentMergeFinpartition (π : NC s)
    (B : Finset α) (hne : B.Nonempty) (hB_mem : B ∈ π.val.parts)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) : Finpartition s :=
  π.val.mergeBlocks hB_mem
    (parentBlock_mem π B hne h_nonRoot)
    (Ne.symm (parentBlock_ne_self π B hne h_nonRoot))

/-- The parent-merge's parts: `{B ∪ parentBlock π B} ∪
(parts.erase B).erase (parentBlock π B)`. -/
@[simp]
theorem parentMergeFinpartition_parts (π : NC s)
    (B : Finset α) (hne : B.Nonempty) (hB_mem : B ∈ π.val.parts)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    (parentMergeFinpartition π B hne hB_mem h_nonRoot).parts =
      insert (B ∪ parentBlock π B hne)
        ((π.val.parts.erase B).erase (parentBlock π B hne)) := by
  unfold parentMergeFinpartition
  rw [Finpartition.mergeBlocks_parts]

/-- The parent-merge reduces `parts.card` by exactly 1. -/
theorem parentMergeFinpartition_card (π : NC s)
    (B : Finset α) (hne : B.Nonempty) (hB_mem : B ∈ π.val.parts)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    (parentMergeFinpartition π B hne hB_mem h_nonRoot).parts.card + 1
      = π.val.parts.card :=
  Finpartition.mergeBlocks_card π.val hB_mem
    (parentBlock_mem π B hne h_nonRoot)
    (Ne.symm (parentBlock_ne_self π B hne h_nonRoot))

end NC

end Hamilton.Infrastructure
