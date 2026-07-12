/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.FiberDecomposition
import Hamilton.Infrastructure.Restriction

/-!
# Compatibility of `s \ blockOfLast` with the partition

For a noncrossing partition `π : NC s` (nonempty `s`), the *complement*
of `blockOfLast π hs` in `s` (i.e., `s \ blockOfLast π hs`) is
**compatible** with `π.val`: every block of `π` is either contained
in the complement (when it's a non-`blockOfLast` block) or disjoint
from the complement (when it IS `blockOfLast`).

This gives a clean restriction of `π` to its complement.

## Main results

* `NC.complement_isCompatible` — `π.val` is compatible with
  `s \ blockOfLast π hs`.

## Tags

noncrossing partition, fiber decomposition, restriction
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- `π.val` is compatible with `s \ blockOfLast π hs`: every block
is either contained in the complement or disjoint from it. -/
theorem complement_isCompatible (π : NC s) (hs : s.Nonempty) :
    Finpartition.IsCompatible π.val (s \ blockOfLast π hs) := by
  intro B hB_mem
  -- Two cases: B = blockOfLast π hs, or B ≠ blockOfLast π hs.
  by_cases h_eq : B = blockOfLast π hs
  · -- B = blockOfLast π hs: disjoint from s \ blockOfLast π hs.
    right
    rw [h_eq]
    exact Finset.disjoint_sdiff
  · -- B ≠ blockOfLast π hs: B ⊆ s \ blockOfLast π hs.
    left
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨(π.val.subset hB_mem) hx, ?_⟩
    -- x ∉ blockOfLast π hs (since B disjoint from blockOfLast).
    intro h_in_L
    have hdisj :=
      π.val.disjoint hB_mem (blockOfLast_mem π hs) h_eq
    exact (Finset.disjoint_left.mp hdisj hx) h_in_L

/-- For nonempty `s`, the complement `s \ blockOfLast π hs` is a
subset of `s`. -/
theorem complement_subset_self (π : NC s) (hs : s.Nonempty) :
    s \ blockOfLast π hs ⊆ s := Finset.sdiff_subset

/-- The **complement-restriction** of `π`: the Finpartition of
`s \ blockOfLast π hs` consisting of the non-`blockOfLast` blocks. -/
noncomputable def complementRestrict (π : NC s) (hs : s.Nonempty) :
    Finpartition (s \ blockOfLast π hs) :=
  Finpartition.restrictCompat π.val (s \ blockOfLast π hs)
    (complement_isCompatible π hs)
    (complement_subset_self π hs)

@[simp]
theorem complementRestrict_parts (π : NC s) (hs : s.Nonempty) :
    (complementRestrict π hs).parts =
      π.val.parts.filter (· ⊆ s \ blockOfLast π hs) := by
  unfold complementRestrict
  rw [Finpartition.restrictCompat_parts]

/-- The complement-restriction is noncrossing.  Direct from
`IsNoncrossing.restrictCompat`. -/
theorem complementRestrict_isNoncrossing (π : NC s) (hs : s.Nonempty) :
    IsNoncrossing (complementRestrict π hs) :=
  IsNoncrossing.restrictCompat π.property
    (complement_isCompatible π hs) (complement_subset_self π hs)

/-- The **complement NC**: the noncrossing partition of `s \
blockOfLast π hs` obtained by restricting `π`. -/
noncomputable def complementNC (π : NC s) (hs : s.Nonempty) :
    NC (s \ blockOfLast π hs) :=
  ⟨complementRestrict π hs, complementRestrict_isNoncrossing π hs⟩

/-- The complement NC has exactly one fewer block: removing the
`blockOfLast` from `π.val.parts` gives `numBlocks π - 1`. -/
theorem complementNC_numBlocks (π : NC s) (hs : s.Nonempty) :
    numBlocks (complementNC π hs) + 1 = numBlocks π := by
  show (complementRestrict π hs).parts.card + 1 = numBlocks π
  rw [complementRestrict_parts]
  -- The filter (· ⊆ s \ blockOfLast) keeps non-blockOfLast blocks.
  -- Equivalently, this equals parts.erase blockOfLast.
  have hroot_mem : blockOfLast π hs ∈ π.val.parts :=
    blockOfLast_mem π hs
  have heq : π.val.parts.filter (fun B => B ⊆ s \ blockOfLast π hs) =
      π.val.parts.erase (blockOfLast π hs) := by
    ext B
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · intro ⟨hB_mem, hB_sub⟩
      refine ⟨?_, hB_mem⟩
      -- B ⊆ s \ blockOfLast: if B = blockOfLast, then blockOfLast ⊆
      -- s \ blockOfLast, which means blockOfLast disjoint from itself,
      -- impossible since blockOfLast is nonempty.
      intro h_eq
      have : blockOfLast π hs ⊆ s \ blockOfLast π hs := h_eq ▸ hB_sub
      have hne_L : (blockOfLast π hs).Nonempty := blockOfLast_nonempty π hs
      obtain ⟨x, hx⟩ := hne_L
      have hx_sub : x ∈ s \ blockOfLast π hs := this hx
      rw [Finset.mem_sdiff] at hx_sub
      exact hx_sub.2 hx
    · intro ⟨hB_ne, hB_mem⟩
      refine ⟨hB_mem, ?_⟩
      -- B ⊆ s \ blockOfLast.
      have h_comp := complement_isCompatible π hs B hB_mem
      rcases h_comp with hsub | hdisj
      · exact hsub
      · -- B disjoint from s \ blockOfLast.  But B ⊆ s, so B ⊆ blockOfLast.
        -- By partition disjointness with blockOfLast, B = blockOfLast,
        -- contradicting hB_ne.
        exfalso
        have hB_ne_empty : B.Nonempty := π.val.nonempty_of_mem_parts hB_mem
        obtain ⟨x, hx⟩ := hB_ne_empty
        have hx_in_s : x ∈ s := (π.val.subset hB_mem) hx
        have : x ∉ s \ blockOfLast π hs :=
          Finset.disjoint_left.mp hdisj hx
        rw [Finset.mem_sdiff] at this
        push_neg at this
        have hx_in_L : x ∈ blockOfLast π hs := this hx_in_s
        -- Now x ∈ B and x ∈ blockOfLast π hs, with B ≠ blockOfLast.
        -- Partition disjointness gives contradiction.
        have hdisj' :=
          π.val.disjoint hB_mem (blockOfLast_mem π hs) hB_ne
        exact (Finset.disjoint_left.mp hdisj' hx) hx_in_L
  rw [heq, Finset.card_erase_of_mem hroot_mem]
  unfold numBlocks
  have h1 : 1 ≤ π.val.parts.card := one_le_numBlocks π hs
  omega

end NC

end Hamilton.Infrastructure
