/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.FiberDecomposition



namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- **The core fiber-decomposition lemma**: for non-`blockOfLast`
block `B`, no element `a ∈ blockOfLast π hs` is *straddled* by `B`. -/
theorem block_does_not_straddle_blockOfLast (π : NC s) (hs : s.Nonempty)
    {B : Finset α} (hB_mem : B ∈ π.val.parts)
    (hB_ne : B ≠ blockOfLast π hs)
    {a : α} (ha : a ∈ blockOfLast π hs) :
    (∀ x ∈ B, x < a) ∨ (∀ y ∈ B, a < y) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨x, hx_in, hx_ge⟩, ⟨y, hy_in, hy_le⟩⟩ := hcon
  -- y, x ∈ B; y ≤ a ≤ x in some order.
  have hL_mem : blockOfLast π hs ∈ π.val.parts := blockOfLast_mem π hs
  have ha_notin_B : a ∉ B := by
    intro h
    have hdisj := π.val.disjoint hB_mem hL_mem hB_ne
    exact (Finset.disjoint_left.mp hdisj h) ha
  have hx_ne_a : x ≠ a := fun h => ha_notin_B (h ▸ hx_in)
  have hy_ne_a : y ≠ a := fun h => ha_notin_B (h ▸ hy_in)
  have hx_gt : a < x := lt_of_le_of_ne hx_ge (Ne.symm hx_ne_a)
  have hy_lt : y < a := lt_of_le_of_ne hy_le hy_ne_a
  -- Witness: s.max' hs ∈ blockOfLast π hs.
  have hmax_in_L : s.max' hs ∈ blockOfLast π hs :=
    blockOfLast_contains_max π hs
  have hmax_notin_B : s.max' hs ∉ B := by
    intro h
    have hdisj := π.val.disjoint hB_mem hL_mem hB_ne
    exact (Finset.disjoint_left.mp hdisj h) hmax_in_L
  have hx_ne_max : x ≠ s.max' hs := fun h => hmax_notin_B (h ▸ hx_in)
  have hy_ne_max : y ≠ s.max' hs := fun h => hmax_notin_B (h ▸ hy_in)
  -- x ≤ s.max' (since x ∈ B ⊆ s), and x ≠ s.max', so x < s.max'.
  have hx_in_s : x ∈ s := (π.val.subset hB_mem) hx_in
  have hx_le_max : x ≤ s.max' hs := s.le_max' _ hx_in_s
  have hx_lt_max : x < s.max' hs := lt_of_le_of_ne hx_le_max hx_ne_max
  -- a < x < s.max', so a < s.max'.
  have ha_lt_max : a < s.max' hs := lt_trans hx_gt hx_lt_max
  -- Apply IsNoncrossing π to (y, a, x, s.max') over (B, blockOfLast).
  have hπ_nc : IsNoncrossing π.val := π.property
  have heq : B = blockOfLast π hs :=
    hπ_nc hB_mem hL_mem hy_lt hx_gt hx_lt_max
      hy_in hx_in ha hmax_in_L
  exact hB_ne heq

/-- Two elements `x, y` of a non-`blockOfLast` block `B` are on the
SAME SIDE of every element `a ∈ blockOfLast π hs`. -/
theorem block_same_side_of_blockOfLast (π : NC s) (hs : s.Nonempty)
    {B : Finset α} (hB_mem : B ∈ π.val.parts)
    (hB_ne : B ≠ blockOfLast π hs)
    {x y : α} (hx : x ∈ B) (hy : y ∈ B)
    {a : α} (ha : a ∈ blockOfLast π hs) :
    (x < a) ↔ (y < a) := by
  rcases block_does_not_straddle_blockOfLast π hs hB_mem hB_ne ha
    with hlt | hgt
  · simp [hlt x hx, hlt y hy]
  · have hx_gt : a < x := hgt x hx
    have hy_gt : a < y := hgt y hy
    constructor
    · intro hxa; exact absurd (lt_trans hx_gt hxa) (lt_irrefl _)
    · intro hya; exact absurd (lt_trans hy_gt hya) (lt_irrefl _)

/-- The interval `[min B, max B]` of a non-`blockOfLast` block `B`
avoids every element `a ∈ blockOfLast π hs`. -/
theorem block_interval_avoids_blockOfLast (π : NC s) (hs : s.Nonempty)
    {B : Finset α} (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (hB_ne : B ≠ blockOfLast π hs)
    {a : α} (ha : a ∈ blockOfLast π hs) :
    (B.max' hne < a) ∨ (a < B.min' hne) := by
  rcases block_does_not_straddle_blockOfLast π hs hB_mem hB_ne ha
    with hlt | hgt
  · left; exact hlt _ (B.max'_mem hne)
  · right; exact hgt _ (B.min'_mem hne)

end NC

end Hamilton.Infrastructure
