/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCFirstBlock
import Hamilton.Infrastructure.NoncrossingPartition

/-!
# Restriction of NC to a saturated subset

For an NC `π` of `s` and a subset `T ⊆ s` such that every block of `π`
is either ⊆ T or disjoint from T (we call this **saturation**), the
parts of `π` that lie in `T` form an NC of `T`.

This is the foundational structural lemma for the recursive NC ↔ DyckWord
bijection: the recursion descends to sub-NCs on saturated subsets (the
"gaps" between consecutive elements of `blockOfFirst`).

## Main definitions

* `NC.restrict π T hT h_sat` — the sub-NC of `π` on a saturated subset `T`.

## Main results

* `NC.restrict_parts` — the parts of the restriction are the parts of `π`
  contained in `T`.
* `NC.restrict_numBlocks` — number of blocks of the restriction is the
  number of blocks of `π` contained in `T`.

## Tags

NC, restriction, saturated subset, sub-NC, KS decomposition
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α]

/-- Restriction of an NC to a saturated subset.

Given `π : NC s` and `T ⊆ s` such that every block of `π` is either ⊆ T or
disjoint from T, the parts of `π` that lie in `T` form an NC of `T`. -/
noncomputable def restrict {s : Finset α} (π : NC s) (T : Finset α) (hT : T ⊆ s)
    (h_sat : ∀ B ∈ π.val.parts, B ⊆ T ∨ Disjoint B T) : NC T := by
  refine ⟨{
    parts := π.val.parts.filter (· ⊆ T)
    supIndep := π.val.supIndep.subset (Finset.filter_subset _ _)
    sup_parts := ?_
    bot_notMem := by
      intro h
      rw [Finset.mem_filter] at h
      exact π.val.bot_notMem h.1
  }, ?_⟩
  · -- sup_parts = T
    apply le_antisymm
    · -- sup of filter ⊆ T
      apply Finset.sup_le
      intros B hB
      rw [Finset.mem_filter] at hB
      exact hB.2
    · -- T ⊆ sup of filter
      intros x hx
      have h_x_in_s : x ∈ s := hT hx
      -- x ∈ π.val.parts.sup id (= s)
      have h_x_in_sup : x ∈ π.val.parts.sup id := by
        rw [π.val.sup_parts]; exact h_x_in_s
      rw [Finset.mem_sup] at h_x_in_sup
      obtain ⟨B, hB, h_x_in_B⟩ := h_x_in_sup
      -- B contains x, x ∈ T, so by saturation B ⊆ T
      cases h_sat B hB with
      | inl h_subset =>
        rw [Finset.mem_sup]
        exact ⟨B, Finset.mem_filter.mpr ⟨hB, h_subset⟩, h_x_in_B⟩
      | inr h_disj =>
        exfalso
        exact Finset.disjoint_left.mp h_disj h_x_in_B hx
  · -- IsNoncrossing
    intros B₁ h₁ B₂ h₂ i j k l hij hjk hkl hi hk hj hl
    rw [Finset.mem_filter] at h₁ h₂
    exact π.prop h₁.1 h₂.1 hij hjk hkl hi hk hj hl

/-- The parts of `restrict π T` are the parts of `π` contained in `T`. -/
theorem restrict_parts {s : Finset α} (π : NC s) (T : Finset α) (hT : T ⊆ s)
    (h_sat : ∀ B ∈ π.val.parts, B ⊆ T ∨ Disjoint B T) :
    (restrict π T hT h_sat).val.parts = π.val.parts.filter (· ⊆ T) := rfl

/-- Number of blocks of `restrict π T` equals the number of `π`-blocks contained in `T`. -/
theorem restrict_numBlocks {s : Finset α} (π : NC s) (T : Finset α) (hT : T ⊆ s)
    (h_sat : ∀ B ∈ π.val.parts, B ⊆ T ∨ Disjoint B T) :
    numBlocks (restrict π T hT h_sat) = (π.val.parts.filter (· ⊆ T)).card := by
  unfold numBlocks
  rw [restrict_parts]

/-- **`afterFirstBlock` is saturated**: every block of `π` is either
contained in `afterFirstBlock` or disjoint from it. -/
theorem afterFirstBlock_saturated {s : Finset α} (π : NC s) (hs : s.Nonempty) :
    ∀ B ∈ π.val.parts, B ⊆ afterFirstBlock π hs ∨ Disjoint B (afterFirstBlock π hs) := by
  intros B hB
  by_cases h_eq : B = blockOfFirst π hs
  · -- B = blockOfFirst: disjoint from afterFirstBlock = s \ blockOfFirst
    right
    rw [h_eq, afterFirstBlock]
    exact Finset.disjoint_sdiff
  · -- B ≠ blockOfFirst: B ⊆ afterFirstBlock (by block_subset_afterFirstBlock_of_ne_first)
    left
    exact block_subset_afterFirstBlock_of_ne_first π hs B hB h_eq

/-- The sub-NC on `afterFirstBlock` (the gap structure after removing blockOfFirst). -/
noncomputable def afterFirstBlock_NC {s : Finset α} (π : NC s) (hs : s.Nonempty) :
    NC (afterFirstBlock π hs) :=
  restrict π (afterFirstBlock π hs) (afterFirstBlock_subset π hs)
    (afterFirstBlock_saturated π hs)

/-- The blocks of `afterFirstBlock_NC` are exactly the non-first blocks of `π`. -/
theorem afterFirstBlock_NC_parts {s : Finset α} (π : NC s) (hs : s.Nonempty) :
    (afterFirstBlock_NC π hs).val.parts =
      π.val.parts.filter (· ⊆ afterFirstBlock π hs) := rfl

/-- **KEY RECURSION**: `numBlocks π = 1 + numBlocks (afterFirstBlock_NC π hs)`. -/
theorem numBlocks_eq_one_plus_afterFirstBlock_NC
    {s : Finset α} (π : NC s) (hs : s.Nonempty) :
    numBlocks π = 1 + numBlocks (afterFirstBlock_NC π hs) := by
  rw [numBlocks_eq_one_plus_nonFirst π hs]
  congr 1
  unfold afterFirstBlock_NC
  rw [restrict_numBlocks]
  -- Goal: (parts.erase blockOfFirst).card = (parts.filter (· ⊆ afterFirstBlock)).card
  -- Show the two Finsets are equal.
  congr 1
  ext B
  simp only [Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro ⟨h_ne, hB⟩
    exact ⟨hB, block_subset_afterFirstBlock_of_ne_first π hs B hB h_ne⟩
  · rintro ⟨hB, h_sub⟩
    refine ⟨?_, hB⟩
    intro h_eq
    -- B = blockOfFirst and B ⊆ afterFirstBlock = s \ blockOfFirst
    -- B is non-empty (since B ∈ parts and ⊥ ∉ parts), but also B ⊆ s \ B
    -- which forces B to be empty. Contradiction.
    rw [h_eq] at h_sub
    have h_B_nonempty : (blockOfFirst π hs).Nonempty := blockOfFirst_nonempty π hs
    have h_disj : Disjoint (blockOfFirst π hs) (afterFirstBlock π hs) := by
      rw [afterFirstBlock]; exact Finset.disjoint_sdiff
    obtain ⟨x, hx⟩ := h_B_nonempty
    have h_x_in_after : x ∈ afterFirstBlock π hs := h_sub hx
    exact Finset.disjoint_left.mp h_disj hx h_x_in_after

end NC

end Hamilton.Infrastructure
