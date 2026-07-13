/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NestingForest
import Hamilton.Infrastructure.NoncrossingPartition

/-!
# Parent block has no overlap with `B`'s interval

For a noncrossing partition `π : NC s` and a non-root block `B`,
the **parent block** of `B` has *no element* in the interval
`[min B, max B]`.

This is the **structural heart** of the nesting-forest construction
on noncrossing partitions.  It says: the parent block is entirely
"outside" `B`'s convex hull.

## Main result

* `NC.parent_no_overlap` — for non-root `B` of `π`, no element `y`
  of `parentBlock π B` satisfies `min B ≤ y ≤ max B`.

## Proof outline

By contradiction.  Suppose `y ∈ parentBlock π B` with `min B ≤ y
≤ max B`.  By partition disjointness, `y ∉ B`, so the inequalities
are strict: `min B < y < max B`.  Now apply `IsNoncrossing π` to
the alternating quadruple:

  `pred < min B < y < max B`,

where `pred` is the predecessor of `min B` in `s` (in `parentBlock π B`
by `parent_contains_pred`), `min B, max B ∈ B`, and `y ∈ parentBlock
π B`.  This forces `parentBlock π B = B`, contradicting
`parentBlock_ne_self`.

## Tags

noncrossing partition, nesting forest, parent block, no overlap
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- **The structural heart of the nesting forest**: the parent block
of a non-root `B` has no element in the closed interval `[min B,
max B]` (where the endpoints are the min and max of `B`).

Equivalently: every element of `parentBlock π B` is strictly less
than `min B` or strictly greater than `max B`. -/
theorem parent_no_overlap (π : NC s) {B : Finset α}
    (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne)
    {y : α} (hy_par : y ∈ parentBlock π B hne)
    (h_ge : B.min' hne ≤ y) (h_le : y ≤ B.max' hne) : False := by
  -- Step 1: y ∉ B (by partition disjointness, since B and parentBlock differ).
  have hC_mem : parentBlock π B hne ∈ π.val.parts :=
    parentBlock_mem π B hne h_nonRoot
  have hC_ne_B : parentBlock π B hne ≠ B :=
    parentBlock_ne_self π B hne h_nonRoot
  have hdisj : Disjoint (parentBlock π B hne) B :=
    π.val.disjoint hC_mem hB_mem hC_ne_B
  have hy_notin_B : y ∉ B := fun h =>
    (Finset.disjoint_left.mp hdisj hy_par) h
  -- Step 2: Strict inequalities (since y ∉ B and min B, max B ∈ B).
  have hmin_in_B : B.min' hne ∈ B := B.min'_mem hne
  have hmax_in_B : B.max' hne ∈ B := B.max'_mem hne
  have hy_ne_min : y ≠ B.min' hne := fun h => hy_notin_B (h ▸ hmin_in_B)
  have hy_ne_max : y ≠ B.max' hne := fun h => hy_notin_B (h ▸ hmax_in_B)
  have hmin_lt : B.min' hne < y := lt_of_le_of_ne h_ge (Ne.symm hy_ne_min)
  have hlt_max : y < B.max' hne := lt_of_le_of_ne h_le hy_ne_max
  -- Step 3: Build the alternating quadruple (pred, min B, y, max B).
  -- pred ∈ parentBlock π B by parent_contains_pred.
  have h_pred_in_par := parent_contains_pred π B hne h_nonRoot
  set pred := (s.filter (· < B.min' hne)).max'
    (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot)
  -- pred < min B.
  have h_pred_lt : pred < B.min' hne :=
    (Finset.mem_filter.mp
      ((s.filter (· < B.min' hne)).max'_mem _)).2
  -- Apply IsNoncrossing π to (pred, min B, y, max B) ranged over
  -- (parentBlock π B, B).
  have hπ_nc : IsNoncrossing π.val := π.property
  have heq : parentBlock π B hne = B :=
    hπ_nc hC_mem hB_mem
      h_pred_lt hmin_lt hlt_max
      h_pred_in_par hy_par hmin_in_B hmax_in_B
  exact hC_ne_B heq

/-- Positive form of `parent_no_overlap`: every element of
`parentBlock π B` is *strictly* less than `min B` or *strictly*
greater than `max B`. -/
theorem parent_elements_split (π : NC s) {B : Finset α}
    (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne)
    {y : α} (hy_par : y ∈ parentBlock π B hne) :
    y < B.min' hne ∨ B.max' hne < y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact parent_no_overlap π hB_mem hne h_nonRoot hy_par h1 h2

end NC

end Hamilton.Infrastructure
