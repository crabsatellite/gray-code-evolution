/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NestingForest

/-!
# Root block of a noncrossing partition

For a noncrossing partition `π : NC s` of a nonempty `s`, the **root
block** is the unique block of `π` containing the minimum element of
`s`.  All other blocks are non-root (their min is strictly greater
than `min s`).

## Main definitions

* `NC.rootBlock` — the root block (concrete: `π.val.part (s.min' hs)`).
* `NC.nonRootBlocks` — the Finset of non-root blocks.

## Main results

* `NC.rootBlock_mem` — the root block is in `π.val.parts`.
* `NC.rootBlock_isRoot` — the root block satisfies `IsRoot`.
* `NC.nonRootBlocks_card` — `|nonRootBlocks π hs| = numBlocks π − 1`.
* `NC.mem_nonRootBlocks_isNonRoot` — every element of `nonRootBlocks` is non-root.

## Tags

noncrossing partition, root block, nesting forest
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The **root block** of `π : NC s` (for nonempty `s`): the unique
block of `π` containing the minimum element of `s`. -/
noncomputable def rootBlock (π : NC s) (hs : s.Nonempty) : Finset α :=
  π.val.part (s.min' hs)

theorem rootBlock_mem (π : NC s) (hs : s.Nonempty) :
    rootBlock π hs ∈ π.val.parts :=
  π.val.part_mem.mpr (s.min'_mem hs)

theorem rootBlock_contains_min (π : NC s) (hs : s.Nonempty) :
    s.min' hs ∈ rootBlock π hs :=
  π.val.mem_part_self.mpr (s.min'_mem hs)

theorem rootBlock_nonempty (π : NC s) (hs : s.Nonempty) :
    (rootBlock π hs).Nonempty :=
  ⟨_, rootBlock_contains_min π hs⟩

/-- The root block satisfies `IsRoot`: no s-element is less than
its min (since its min is `min s` itself). -/
theorem rootBlock_isRoot (π : NC s) (hs : s.Nonempty) :
    IsRoot (s := s) (rootBlock π hs) (rootBlock_nonempty π hs) := by
  intro q hq_in
  -- (rootBlock).min ≤ min s ≤ q.
  have hmin_in : s.min' hs ∈ rootBlock π hs := rootBlock_contains_min π hs
  have hmin_le : (rootBlock π hs).min' (rootBlock_nonempty π hs) ≤ s.min' hs :=
    (rootBlock π hs).min'_le _ hmin_in
  -- We need: ¬ q < (rootBlock).min.
  intro hq_lt
  have : q < s.min' hs := lt_of_lt_of_le hq_lt hmin_le
  exact absurd this (not_lt.mpr (s.min'_le _ hq_in))

/-- Any block `B ≠ rootBlock π hs` of `π` satisfies `¬ IsRoot`.

Reason: if `B` were root (`min s ∉ ` any earlier), then `B` would
contain `min s`, but `min s ∈ rootBlock π hs`, so by partition
disjointness `B = rootBlock π hs`. -/
theorem ne_rootBlock_isNonRoot (π : NC s) (hs : s.Nonempty)
    {B : Finset α} (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (hB_ne : B ≠ rootBlock π hs) :
    ¬ IsRoot (s := s) B hne := by
  intro h_root
  -- min B ≤ min s (since IsRoot says no s-element < min B, so
  -- min s ≥ min B by contraposition).
  -- Also min B ∈ B ⊆ s, so min B ≥ min s.  Hence min B = min s.
  have hmin_B_in_s : B.min' hne ∈ s := (π.val.subset hB_mem) (B.min'_mem hne)
  have hmin_B_ge : s.min' hs ≤ B.min' hne := s.min'_le _ hmin_B_in_s
  have hmin_s_not_lt : ¬ s.min' hs < B.min' hne := h_root _ (s.min'_mem hs)
  have hmin_eq : s.min' hs = B.min' hne :=
    le_antisymm hmin_B_ge (not_lt.mp hmin_s_not_lt)
  -- min s ∈ B.
  have hmin_in_B : s.min' hs ∈ B := hmin_eq ▸ B.min'_mem hne
  -- min s ∈ rootBlock.
  have hmin_in_R : s.min' hs ∈ rootBlock π hs :=
    rootBlock_contains_min π hs
  -- Partition disjointness → B = rootBlock.
  have hdisj := π.val.disjoint hB_mem (rootBlock_mem π hs) hB_ne
  exact (Finset.disjoint_left.mp hdisj hmin_in_B) hmin_in_R

/-- The Finset of **non-root blocks** of `π`. -/
noncomputable def nonRootBlocks (π : NC s) (hs : s.Nonempty) :
    Finset (Finset α) :=
  π.val.parts.erase (rootBlock π hs)

@[simp]
theorem mem_nonRootBlocks {π : NC s} (hs : s.Nonempty) {B : Finset α} :
    B ∈ nonRootBlocks π hs ↔ B ≠ rootBlock π hs ∧ B ∈ π.val.parts := by
  unfold nonRootBlocks
  rw [Finset.mem_erase]

/-- The number of non-root blocks equals `numBlocks π − 1`. -/
theorem nonRootBlocks_card (π : NC s) (hs : s.Nonempty) :
    (nonRootBlocks π hs).card + 1 = numBlocks π := by
  unfold nonRootBlocks
  rw [Finset.card_erase_of_mem (rootBlock_mem π hs)]
  unfold numBlocks
  have h1 : 1 ≤ π.val.parts.card := one_le_numBlocks π hs
  omega

end NC

end Hamilton.Infrastructure
