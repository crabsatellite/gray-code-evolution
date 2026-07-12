/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.GapBlockDecomp
import Hamilton.Infrastructure.FiberCompatible

/-!
# Additive identity: `numBlocks π = 1 + ∑_x numBlocks(gapNC π hs hx)`

The non-`blockOfLast` blocks of `π : NC s` partition into the
gap-restrictions: each non-`blockOfLast` block lies in exactly one
gap `gapBefore s S x` for some `x ∈ S = blockOfLast π hs`.

This gives the additive identity:
  numBlocks π = 1 + ∑_{x ∈ S} numBlocks(gapNC π hs hx).

## Main results

* `NC.sum_gap_numBlocks_eq_complement` — ∑_x numBlocks(gapNC) =
  numBlocks(complementNC).
* `NC.sum_gap_numBlocks_plus_one` — ∑_x numBlocks(gapNC) + 1 =
  numBlocks π.

## Tags

noncrossing partition, gap decomposition, additive Kreweras-Simion
-/

namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore mem_gapBefore gapBefore_subset_self
  gapBefore_disjoint_S gapBefore_disjoint
  exists_gap_of_mem_sdiff)

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- `(gapRestrict π hs hx).parts` = blocks of `π` contained in
`gapBefore s S x`. -/
theorem gapRestrict_parts_eq (π : NC s) (hs : s.Nonempty)
    {x : α} (hx : x ∈ blockOfLast π hs) :
    (gapRestrict π hs hx).parts =
      π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x) := by
  unfold gapRestrict
  rw [Finpartition.restrictCompat_parts]

/-- `numBlocks (gapNC π hs hx)` = count of `π`-blocks ⊆ gap. -/
theorem gapNC_numBlocks_eq (π : NC s) (hs : s.Nonempty)
    {x : α} (hx : x ∈ blockOfLast π hs) :
    numBlocks (gapNC π hs hx) =
      (π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x)).card := by
  show (gapRestrict π hs hx).parts.card = _
  rw [gapRestrict_parts_eq]

/-- Distinct gaps yield disjoint block-filter sets: a block of `π`
contained in `gapBefore s S x₁` is disjoint from one contained in
`gapBefore s S x₂` (for `x₁ ≠ x₂`).  Since blocks of `π` are already
disjoint, what we need is: a single block can't be ⊆ both gaps. -/
theorem filter_gap_disjoint (π : NC s) (hs : s.Nonempty)
    {x₁ x₂ : α} (hx₁ : x₁ ∈ blockOfLast π hs) (hx₂ : x₂ ∈ blockOfLast π hs)
    (hne : x₁ ≠ x₂) :
    Disjoint (π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x₁))
             (π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x₂)) := by
  rw [Finset.disjoint_left]
  intro B hB₁ hB₂
  rw [Finset.mem_filter] at hB₁ hB₂
  obtain ⟨hB_mem, hsub₁⟩ := hB₁
  obtain ⟨_, hsub₂⟩ := hB₂
  exact hne (nonRoot_block_in_unique_gap π hs hB_mem hx₁ hx₂ hsub₁ hsub₂)

/-- The blockOfLast itself is not contained in any gap. -/
theorem blockOfLast_not_in_filter_gap (π : NC s) (hs : s.Nonempty)
    {x : α} (hx : x ∈ blockOfLast π hs) :
    blockOfLast π hs ∉
      π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x) := by
  intro h
  rw [Finset.mem_filter] at h
  obtain ⟨_, hsub⟩ := h
  -- blockOfLast contains x, but gapBefore is disjoint from S = blockOfLast.
  have hx_gap : x ∈ gapBefore s (blockOfLast π hs) x := hsub hx
  have hdisj := gapBefore_disjoint_S s (blockOfLast π hs) x
  exact (Finset.disjoint_left.mp hdisj hx_gap) hx

/-- **Union-of-gap-filters = erase blockOfLast**: the union of all
gap filter-sets (over `x ∈ S`) is exactly `parts.erase blockOfLast`. -/
theorem biUnion_filter_gap_eq_erase (π : NC s) (hs : s.Nonempty) :
    (blockOfLast π hs).biUnion (fun x =>
        π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x)) =
      π.val.parts.erase (blockOfLast π hs) := by
  ext B
  rw [Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · intro ⟨x, hx_S, hB⟩
    rw [Finset.mem_filter] at hB
    obtain ⟨hB_mem, hsub⟩ := hB
    refine ⟨?_, hB_mem⟩
    intro h_eq
    -- B = blockOfLast ⊆ gap x — contradicts gapBefore_disjoint_S.
    rw [h_eq] at hsub
    have : x ∈ gapBefore s (blockOfLast π hs) x := hsub hx_S
    exact (Finset.disjoint_left.mp
      (gapBefore_disjoint_S s (blockOfLast π hs) x) this) hx_S
  · intro ⟨hne, hmem⟩
    obtain ⟨x, hx_S, hsub⟩ := nonRoot_block_subset_some_gap π hs hmem hne
    refine ⟨x, hx_S, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hmem, hsub⟩

/-- **Sum-of-gap-numBlocks = numBlocks(parts.erase blockOfLast)**.

By disjointness of gap filters (`filter_gap_disjoint`), the sum
equals the cardinality of the biUnion, which equals
`(parts.erase blockOfLast).card` by `biUnion_filter_gap_eq_erase`. -/
theorem sum_gap_numBlocks_eq_erase_card (π : NC s) (hs : s.Nonempty) :
    ∑ x ∈ blockOfLast π hs,
      (π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x)).card =
      (π.val.parts.erase (blockOfLast π hs)).card := by
  rw [← biUnion_filter_gap_eq_erase π hs]
  rw [Finset.card_biUnion]
  intros x₁ hx₁ x₂ hx₂ hne
  exact filter_gap_disjoint π hs hx₁ hx₂ hne


theorem sum_gap_numBlocks_attach_plus_one (π : NC s) (hs : s.Nonempty) :
    (∑ x ∈ (blockOfLast π hs).attach,
      numBlocks (gapNC π hs x.2)) + 1 = numBlocks π := by
  -- Rewrite the sum over attach as sum over S of fiber-cards.
  have hattach :
      (∑ x ∈ (blockOfLast π hs).attach, numBlocks (gapNC π hs x.2)) =
      ∑ x ∈ blockOfLast π hs,
        (π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x)).card := by
    rw [← Finset.sum_attach (blockOfLast π hs) (fun x =>
      (π.val.parts.filter (· ⊆ gapBefore s (blockOfLast π hs) x)).card)]
    apply Finset.sum_congr rfl
    intro ⟨x, hx⟩ _
    exact gapNC_numBlocks_eq π hs hx
  rw [hattach, sum_gap_numBlocks_eq_erase_card π hs]
  -- Now: (parts.erase blockOfLast).card + 1 = numBlocks π.
  unfold numBlocks
  have h_mem : blockOfLast π hs ∈ π.val.parts := blockOfLast_mem π hs
  rw [Finset.card_erase_of_mem h_mem]
  have h1 : 1 ≤ π.val.parts.card := one_le_numBlocks π hs
  omega

end NC

end Hamilton.Infrastructure
