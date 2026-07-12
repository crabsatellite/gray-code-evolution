/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.FiberDecomposition

/-!
# Fiber decomposition by "block containing min"

Mirror of `FiberDecomposition.lean` (`blockOfLast`), but indexing by the
block containing the **minimum** element of `s`.  This is the version
used in the standard Kreweras-Speicher decomposition for constructing
the bijection `NC s ↔ DyckWord_{semilength s.card}`.

For NC π of [n], element 1 (the minimum) is in some block `B₁ = {1, b₂, ..., bₗ}`.
The "gaps" between consecutive elements of B₁ define `l + 1` sub-intervals,
each carrying its own sub-NC.  This recursive decomposition matches the
`firstReturn` decomposition of Dyck words.

## Main definitions

* `NC.blockOfFirst π hs` — the block containing `s.min'`.

## Main results

* `NC.blockOfFirst_mem` — `blockOfFirst π hs ∈ π.val.parts`.
* `NC.blockOfFirst_contains_min` — `s.min' hs ∈ blockOfFirst π hs`.
* `NC.blockOfFirst_min_eq` — `min' (blockOfFirst π hs) = s.min' hs`.

## Tags

noncrossing partition, fiber, block of first, decomposition, KS
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The block of `π` containing the minimum element of `s`. -/
noncomputable def blockOfFirst (π : NC s) (hs : s.Nonempty) :
    Finset α :=
  π.val.part (s.min' hs)

theorem blockOfFirst_mem (π : NC s) (hs : s.Nonempty) :
    blockOfFirst π hs ∈ π.val.parts :=
  π.val.part_mem.mpr (s.min'_mem hs)

theorem blockOfFirst_contains_min (π : NC s) (hs : s.Nonempty) :
    s.min' hs ∈ blockOfFirst π hs :=
  π.val.mem_part_self.mpr (s.min'_mem hs)

theorem blockOfFirst_nonempty (π : NC s) (hs : s.Nonempty) :
    (blockOfFirst π hs).Nonempty :=
  ⟨_, blockOfFirst_contains_min π hs⟩

/-- The min of `blockOfFirst π hs` equals `s.min'`. -/
theorem blockOfFirst_min_eq (π : NC s) (hs : s.Nonempty) :
    (blockOfFirst π hs).min' (blockOfFirst_nonempty π hs) = s.min' hs := by
  apply le_antisymm
  · -- min' (blockOfFirst π hs) ≤ s.min' hs since s.min' is in blockOfFirst
    apply (blockOfFirst π hs).min'_le
    exact blockOfFirst_contains_min π hs
  · -- s.min' hs ≤ min' (blockOfFirst π hs) since blockOfFirst ⊆ s
    apply s.min'_le
    apply (π.val.subset (blockOfFirst_mem π hs))
    exact (blockOfFirst π hs).min'_mem _

/-- Size of the first block. -/
noncomputable def firstBlockSize (π : NC s) (hs : s.Nonempty) : ℕ :=
  (blockOfFirst π hs).card

/-- `firstBlockSize` is positive. -/
theorem firstBlockSize_pos (π : NC s) (hs : s.Nonempty) :
    0 < firstBlockSize π hs :=
  Finset.card_pos.mpr (blockOfFirst_nonempty π hs)

/-- `firstBlockSize ≤ s.card`. -/
theorem firstBlockSize_le_card (π : NC s) (hs : s.Nonempty) :
    firstBlockSize π hs ≤ s.card :=
  Finset.card_le_card (π.val.subset (blockOfFirst_mem π hs))

/-- The "remaining" elements: `s` minus the first block. -/
noncomputable def afterFirstBlock (π : NC s) (hs : s.Nonempty) : Finset α :=
  s \ blockOfFirst π hs

/-- `afterFirstBlock ⊆ s`. -/
theorem afterFirstBlock_subset (π : NC s) (hs : s.Nonempty) :
    afterFirstBlock π hs ⊆ s := Finset.sdiff_subset

/-- `afterFirstBlock.card = s.card - firstBlockSize`. -/
theorem afterFirstBlock_card (π : NC s) (hs : s.Nonempty) :
    (afterFirstBlock π hs).card = s.card - firstBlockSize π hs := by
  unfold afterFirstBlock firstBlockSize
  exact Finset.card_sdiff_of_subset (π.val.subset (blockOfFirst_mem π hs))

/-- **Termination measure**: `afterFirstBlock.card < s.card` for non-empty `s`.

This is the key well-foundedness property: the recursion `π → afterFirstBlock_NC π`
strictly decreases `s.card`, hence terminates. -/
theorem afterFirstBlock_card_lt (π : NC s) (hs : s.Nonempty) :
    (afterFirstBlock π hs).card < s.card := by
  rw [afterFirstBlock_card]
  have h_pos := firstBlockSize_pos π hs
  have h_le := firstBlockSize_le_card π hs
  omega

/-- `firstBlockSize = s.card` iff `blockOfFirst = s` (i.e., the partition is indiscrete). -/
theorem firstBlockSize_eq_card_iff_blockOfFirst_eq_s
    (π : NC s) (hs : s.Nonempty) :
    firstBlockSize π hs = s.card ↔ blockOfFirst π hs = s := by
  constructor
  · intro h_eq
    apply Finset.eq_of_subset_of_card_le (π.val.subset (blockOfFirst_mem π hs))
    exact le_of_eq h_eq.symm
  · intro h_eq
    unfold firstBlockSize
    rw [h_eq]

/-- `afterFirstBlock = ∅` iff `blockOfFirst = s`. -/
theorem afterFirstBlock_eq_empty_iff (π : NC s) (hs : s.Nonempty) :
    afterFirstBlock π hs = ∅ ↔ blockOfFirst π hs = s := by
  unfold afterFirstBlock
  constructor
  · intro h_eq
    -- s \ blockOfFirst = ∅ means s ⊆ blockOfFirst.
    -- Combined with blockOfFirst ⊆ s, we get equality.
    have h_sub : s ⊆ blockOfFirst π hs := Finset.sdiff_eq_empty_iff_subset.mp h_eq
    apply le_antisymm (π.val.subset (blockOfFirst_mem π hs)) h_sub
  · intro h_eq
    rw [h_eq, Finset.sdiff_self]

/-- `firstBlockSize = 1` iff `blockOfFirst = {s.min'}`. -/
theorem firstBlockSize_eq_one_iff_blockOfFirst_singleton (π : NC s) (hs : s.Nonempty) :
    firstBlockSize π hs = 1 ↔ blockOfFirst π hs = {s.min' hs} := by
  unfold firstBlockSize
  constructor
  · intro h_card
    rw [Finset.card_eq_one] at h_card
    obtain ⟨a, ha⟩ := h_card
    have h_min : s.min' hs ∈ blockOfFirst π hs := blockOfFirst_contains_min π hs
    rw [ha] at h_min
    rw [Finset.mem_singleton] at h_min
    rw [ha, h_min]
  · intro h_eq
    rw [h_eq, Finset.card_singleton]

/-- `blockOfFirst = s` iff `numBlocks π = 1` (the indiscrete-partition characterization). -/
theorem blockOfFirst_eq_s_iff_numBlocks_one (π : NC s) (hs : s.Nonempty) :
    blockOfFirst π hs = s ↔ numBlocks π = 1 := by
  constructor
  · intro h_eq
    have h_mem : s ∈ π.val.parts := by
      have h := blockOfFirst_mem π hs
      rw [h_eq] at h
      exact h
    have h_parts_eq : π.val.parts = {s} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨h_mem, ?_⟩
      intro B hB
      by_contra h_ne
      have h_disj := π.val.disjoint hB h_mem h_ne
      have h_B_sub : B ⊆ s := π.val.subset hB
      have h_B_empty : B = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx =>
        Finset.disjoint_left.mp h_disj hx (h_B_sub hx))
      have h_bot_mem : (∅ : Finset α) ∈ π.val.parts := h_B_empty ▸ hB
      exact π.val.bot_notMem h_bot_mem
    unfold numBlocks
    rw [h_parts_eq]
    simp
  · intro h_one
    unfold numBlocks at h_one
    rw [Finset.card_eq_one] at h_one
    obtain ⟨B, hB⟩ := h_one
    have h_B_eq_s : B = s := by
      have hsup : π.val.parts.sup id = s := π.val.sup_parts
      rw [hB] at hsup
      simpa using hsup
    have h_blockOfFirst_mem : blockOfFirst π hs ∈ π.val.parts := blockOfFirst_mem π hs
    rw [hB, Finset.mem_singleton] at h_blockOfFirst_mem
    rw [h_blockOfFirst_mem, h_B_eq_s]

/-- Every block of `π` other than `blockOfFirst` is contained in `afterFirstBlock`. -/
theorem block_subset_afterFirstBlock_of_ne_first (π : NC s) (hs : s.Nonempty)
    (B : Finset α) (hB : B ∈ π.val.parts) (hne : B ≠ blockOfFirst π hs) :
    B ⊆ afterFirstBlock π hs := by
  intro x hx
  have h_x_in_s : x ∈ s := π.val.subset hB hx
  rw [afterFirstBlock, Finset.mem_sdiff]
  refine ⟨h_x_in_s, ?_⟩
  intro h_x_in_first
  have h_disj := π.val.disjoint hB (blockOfFirst_mem π hs) hne
  exact Finset.disjoint_left.mp h_disj hx h_x_in_first

/-- Block-count decomposition: `numBlocks π = 1 + (# blocks ≠ blockOfFirst)`. -/
theorem numBlocks_eq_one_plus_nonFirst (π : NC s) (hs : s.Nonempty) :
    numBlocks π = 1 + (π.val.parts.erase (blockOfFirst π hs)).card := by
  unfold numBlocks
  have h_card : π.val.parts.card =
      (π.val.parts.erase (blockOfFirst π hs)).card + 1 := by
    rw [← Finset.card_insert_of_notMem (Finset.notMem_erase _ _)]
    rw [Finset.insert_erase (blockOfFirst_mem π hs)]
  omega

/-- `firstBlockSize < s.card` iff `numBlocks π ≥ 2` (the recursive case). -/
theorem firstBlockSize_lt_card_iff (π : NC s) (hs : s.Nonempty) :
    firstBlockSize π hs < s.card ↔ 2 ≤ numBlocks π := by
  constructor
  · intro h_lt
    have h_ne_s : blockOfFirst π hs ≠ s := by
      intro h_eq
      have : firstBlockSize π hs = s.card := by
        unfold firstBlockSize; rw [h_eq]
      omega
    have h_ne_one : numBlocks π ≠ 1 := fun h =>
      h_ne_s ((blockOfFirst_eq_s_iff_numBlocks_one π hs).mpr h)
    have h_pos := one_le_numBlocks π hs
    omega
  · intro h_ge
    have h_ne_one : numBlocks π ≠ 1 := by omega
    have h_ne_s : blockOfFirst π hs ≠ s := fun h =>
      h_ne_one ((blockOfFirst_eq_s_iff_numBlocks_one π hs).mp h)
    have h_le := firstBlockSize_le_card π hs
    have h_ne_size : firstBlockSize π hs ≠ s.card := fun h =>
      h_ne_s ((firstBlockSize_eq_card_iff_blockOfFirst_eq_s π hs).mp h)
    omega

end NC

end Hamilton.Infrastructure
