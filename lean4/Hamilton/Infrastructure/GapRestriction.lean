/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.FiberStraddle
import Hamilton.Infrastructure.GapIntervals
import Hamilton.Infrastructure.Restriction



namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore mem_gapBefore gapBefore_subset_self
  gapBefore_disjoint_S gapBefore_lt gapBefore_disjoint
  exists_gap_of_mem_sdiff)

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- For a non-`blockOfLast` block `B`, every element of `B` lies in
`s \ blockOfLast π hs` (i.e., not in `S`) and has some element of `S`
above it.  Hence by `exists_gap_of_mem_sdiff`, `B` intersects some
gap. -/
theorem nonRoot_block_elem_in_some_gap (π : NC s) (hs : s.Nonempty)
    {B : Finset α} (hB_mem : B ∈ π.val.parts)
    (hB_ne : B ≠ blockOfLast π hs)
    {y₀ : α} (hy₀ : y₀ ∈ B) :
    ∃ x ∈ blockOfLast π hs,
      y₀ ∈ gapBefore s (blockOfLast π hs) x := by
  -- y₀ ∈ s.
  have hy₀_s : y₀ ∈ s := (π.val.subset hB_mem) hy₀
  -- y₀ ∉ blockOfLast (by block disjointness).
  have hL_mem : blockOfLast π hs ∈ π.val.parts := blockOfLast_mem π hs
  have hy₀_notL : y₀ ∉ blockOfLast π hs := by
    intro h
    have hdisj := π.val.disjoint hB_mem hL_mem hB_ne
    exact (Finset.disjoint_left.mp hdisj hy₀) h
  -- s.max' hs ∈ blockOfLast π hs.
  have hmax_L : s.max' hs ∈ blockOfLast π hs :=
    blockOfLast_contains_max π hs
  -- s.max' is strictly above y₀: y₀ ≠ s.max' (since y₀ ∉ L, max ∈ L)
  -- and y₀ ≤ s.max'.
  have hy₀_ne_max : y₀ ≠ s.max' hs := fun h => hy₀_notL (h ▸ hmax_L)
  have hy₀_le_max : y₀ ≤ s.max' hs := s.le_max' _ hy₀_s
  have hy₀_lt_max : y₀ < s.max' hs :=
    lt_of_le_of_ne hy₀_le_max hy₀_ne_max
  exact exists_gap_of_mem_sdiff s (blockOfLast π hs) y₀ hy₀_s
    hy₀_notL ⟨s.max' hs, hmax_L, hy₀_lt_max⟩

/-- **Compatibility**: for each `x ∈ blockOfLast π hs`, every block
`B` of `π` is either contained in `gapBefore s S x` or disjoint
from it.

The `blockOfLast` itself is disjoint (since `gapBefore_disjoint_S`).
For other blocks `B`, all elements of `B` are on the same side of
`x` (by `block_does_not_straddle_blockOfLast`), and all elements
behave the same way w.r.t. the `S`-predecessor condition.  Either
the entire block is in the gap or entirely outside. -/
theorem gap_isCompatible (π : NC s) (hs : s.Nonempty)
    {x : α} (hx : x ∈ blockOfLast π hs) :
    Finpartition.IsCompatible π.val (gapBefore s (blockOfLast π hs) x) := by
  intro B hB_mem
  by_cases h_eq : B = blockOfLast π hs
  · -- B = blockOfLast: disjoint from any gap (by `gapBefore_disjoint_S`).
    right
    rw [h_eq]
    exact (gapBefore_disjoint_S s (blockOfLast π hs) x).symm
  · -- B ≠ blockOfLast.  Use straddling lemma.
    -- Case split on whether B ∩ gap is empty.
    by_cases h_empty : (B ∩ gapBefore s (blockOfLast π hs) x).Nonempty
    · -- B intersects gap; show B ⊆ gap.
      left
      obtain ⟨y₀, hy₀_int⟩ := h_empty
      rw [Finset.mem_inter] at hy₀_int
      obtain ⟨hy₀_B, hy₀_gap⟩ := hy₀_int
      rw [mem_gapBefore] at hy₀_gap
      obtain ⟨hy₀_s, hy₀_lt_x, hy₀_above_preds⟩ := hy₀_gap
      intro y hy_B
      rw [mem_gapBefore]
      have hy_s : y ∈ s := (π.val.subset hB_mem) hy_B
      refine ⟨hy_s, ?_, ?_⟩
      · -- y < x: from block_same_side, y₀ ∈ B and y₀ < x.
        have h_iff := block_same_side_of_blockOfLast π hs hB_mem h_eq
          hy_B hy₀_B hx
        exact h_iff.mpr hy₀_lt_x
      · intro z hz_S hz_lt_x
        -- Want: z < y.  Use block_same_side at z.
        -- y₀ has the property z < y₀ (from hy₀_above_preds).
        have hz_lt_y₀ : z < y₀ := hy₀_above_preds z hz_S hz_lt_x
        have h_iff := block_same_side_of_blockOfLast π hs hB_mem h_eq
          hy_B hy₀_B hz_S
        -- h_iff: y < z ↔ y₀ < z.  We want z < y.
        -- y₀ > z, so NOT y₀ < z, so NOT y < z, so y ≥ z.
        have hy₀_not_lt_z : ¬ y₀ < z := not_lt_of_gt hz_lt_y₀
        have hy_not_lt_z : ¬ y < z := fun h => hy₀_not_lt_z (h_iff.mp h)
        -- y ≥ z, and y ≠ z (since y ∈ B disjoint from S).
        have hy_ge_z : z ≤ y := not_lt.mp hy_not_lt_z
        have hL_mem : blockOfLast π hs ∈ π.val.parts :=
          blockOfLast_mem π hs
        have hy_notS : y ∉ blockOfLast π hs := by
          intro h
          have hdisj := π.val.disjoint hB_mem hL_mem h_eq
          exact (Finset.disjoint_left.mp hdisj hy_B) h
        have hy_ne_z : y ≠ z := fun h => hy_notS (h ▸ hz_S)
        exact lt_of_le_of_ne hy_ge_z (Ne.symm hy_ne_z)
    · -- B ∩ gap empty: B disjoint from gap.
      right
      rw [Finset.not_nonempty_iff_eq_empty] at h_empty
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact h_empty

/-- The gap `gapBefore s S x` is a subset of `s`. -/
theorem gap_subset_self (π : NC s) (hs : s.Nonempty) (x : α) :
    gapBefore s (blockOfLast π hs) x ⊆ s :=
  gapBefore_subset_self s (blockOfLast π hs) x

/-- The **gap-restriction** of `π`: the Finpartition of
`gapBefore s S x` consisting of blocks contained in the gap. -/
noncomputable def gapRestrict (π : NC s) (hs : s.Nonempty)
    {x : α} (hx : x ∈ blockOfLast π hs) :
    Finpartition (gapBefore s (blockOfLast π hs) x) :=
  Finpartition.restrictCompat π.val (gapBefore s (blockOfLast π hs) x)
    (gap_isCompatible π hs hx) (gap_subset_self π hs x)

@[simp]
theorem gapRestrict_parts (π : NC s) (hs : s.Nonempty)
    {x : α} (hx : x ∈ blockOfLast π hs) :
    (gapRestrict π hs hx).parts =
      π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x) := by
  unfold gapRestrict
  rw [Finpartition.restrictCompat_parts]

/-- Gap-restriction is **noncrossing**. -/
theorem gapRestrict_isNoncrossing (π : NC s) (hs : s.Nonempty)
    {x : α} (hx : x ∈ blockOfLast π hs) :
    IsNoncrossing (gapRestrict π hs hx) :=
  IsNoncrossing.restrictCompat π.property
    (gap_isCompatible π hs hx) (gap_subset_self π hs x)

/-- The **gap NC**: the noncrossing partition of `gapBefore s S x`
obtained by restricting `π`. -/
noncomputable def gapNC (π : NC s) (hs : s.Nonempty)
    {x : α} (hx : x ∈ blockOfLast π hs) :
    NC (gapBefore s (blockOfLast π hs) x) :=
  ⟨gapRestrict π hs hx, gapRestrict_isNoncrossing π hs hx⟩

end NC

end Hamilton.Infrastructure
