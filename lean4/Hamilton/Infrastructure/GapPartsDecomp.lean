/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.GapAdditiveBlocks

/-!
# Parts decomposition: `π.parts = {blockOfLast} ∪ ⋃_x gapNC parts`

For `π : NC s` (nonempty `s`), the parts of `π` decompose as:
  parts π = {blockOfLast π hs} ∪ ⋃_{x ∈ blockOfLast π hs} (gapNC π hs hx).parts.

This is the structural form of the Kreweras-Simion fiber
decomposition: parts split into the "root" block and the
gap-partitioned blocks.

## Main results

* `NC.parts_eq_insert_biUnion_gap` — the decomposition.
* `NC.parts_injective_via_gaps` — `π₁ = π₂` iff blockOfLast and all
  gap-NCs agree (injectivity of the fiber-product map).

## Tags

noncrossing partition, parts decomposition, Kreweras-Simion fiber
-/

namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore mem_gapBefore gapBefore_subset_self
  gapBefore_disjoint_S gapBefore_disjoint)

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- **Parts decomposition**: the parts of `π` are exactly the
`blockOfLast` together with the parts of each gap-NC.

Equivalently, parts π = insert (blockOfLast) (parts.erase blockOfLast),
and parts.erase blockOfLast = ⋃ x ∈ S, gap-NC parts at x. -/
theorem parts_eq_insert_biUnion_gap (π : NC s) (hs : s.Nonempty) :
    π.val.parts = insert (blockOfLast π hs)
      ((blockOfLast π hs).biUnion (fun x =>
        π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x))) := by
  rw [biUnion_filter_gap_eq_erase π hs]
  exact (Finset.insert_erase (blockOfLast_mem π hs)).symm

/-- **Parts equal iff blockOfLast and all gap filters agree**: this
gives injectivity of the fiber-product map.

If `blockOfLast π₁ hs = blockOfLast π₂ hs` and the gap filters
(blocks ⊆ each gap) agree, then `π₁.val.parts = π₂.val.parts`. -/
theorem parts_eq_of_blockOfLast_and_gap_filters_eq (π₁ π₂ : NC s)
    (hs : s.Nonempty)
    (hL : blockOfLast π₁ hs = blockOfLast π₂ hs)
    (hgaps : ∀ x ∈ blockOfLast π₁ hs,
      π₁.val.parts.filter (· ⊆ gapBefore s (blockOfLast π₁ hs) x) =
      π₂.val.parts.filter (· ⊆ gapBefore s (blockOfLast π₂ hs) x)) :
    π₁.val.parts = π₂.val.parts := by
  rw [parts_eq_insert_biUnion_gap π₁ hs, parts_eq_insert_biUnion_gap π₂ hs]
  rw [hL]
  congr 1
  apply Finset.biUnion_congr rfl
  intro x hx
  rw [← hL] at hx
  have h := hgaps x hx
  rw [hL] at h
  exact h

/-- **Finpartition determined by parts**: two Finpartitions of the
same finset with the same parts are equal. -/
theorem Finpartition.eq_of_parts_eq {P₁ P₂ : Finpartition s}
    (h : P₁.parts = P₂.parts) : P₁ = P₂ := by
  cases P₁; cases P₂
  simp only at h
  congr

/-- **NC equality via parts** (uses `Subsingleton` of `IsNoncrossing`
proof). -/
theorem nc_eq_of_parts_eq (π₁ π₂ : NC s)
    (h : π₁.val.parts = π₂.val.parts) : π₁ = π₂ := by
  cases π₁; cases π₂
  simp only at h
  congr
  exact Finpartition.eq_of_parts_eq h

/-- **Injectivity of fiber-product map**: if `π₁, π₂` have the same
`blockOfLast` and the same gap filters, then `π₁ = π₂`. -/
theorem nc_eq_of_blockOfLast_and_gap_filters_eq (π₁ π₂ : NC s)
    (hs : s.Nonempty)
    (hL : blockOfLast π₁ hs = blockOfLast π₂ hs)
    (hgaps : ∀ x ∈ blockOfLast π₁ hs,
      π₁.val.parts.filter (· ⊆ gapBefore s (blockOfLast π₁ hs) x) =
      π₂.val.parts.filter (· ⊆ gapBefore s (blockOfLast π₂ hs) x)) :
    π₁ = π₂ :=
  nc_eq_of_parts_eq π₁ π₂
    (parts_eq_of_blockOfLast_and_gap_filters_eq π₁ π₂ hs hL hgaps)

end NC

end Hamilton.Infrastructure
