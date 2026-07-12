/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCRestrict

/-!
# `IsBlockMax`: when an element is the maximum of its block

For an NC `π` of `s` and an element `i ∈ s`, `IsBlockMax π i h_in` says that
every element of the block of `π` containing `i` is `≤ i`.  Equivalently:
`i` is the maximum of its block.

This predicate is the key building block for the **stack-based encoding**
`NC → DyckWord`:

  For each element `i` of `s` (in increasing order):
  - Emit `U`.
  - If `IsBlockMax π i`, emit `|block of i|` `D`'s.

This encoding has length `2 · s.card`, `peakCount = numBlocks π` (each
block contributes one peak at its block-max).

## Main definitions

* `NC.IsBlockMax π i h_in` — `i` is the maximum of its block in `π`.

## Main results

* `NC.IsBlockMax` is decidable.
* `NC.max'_block_isBlockMax` — the max of each block satisfies `IsBlockMax`.

## Tags

NC, block, maximum, stack encoding, DyckWord bijection
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

set_option linter.unusedVariables false in
/-- `IsBlockMax π i h_in` says `i ∈ s` is the maximum of the block of `π`
containing it: every element of that block is `≤ i`.

The `h_in : i ∈ s` argument fixes the intended domain of the predicate
(`i` ranges over members of `s`); it is part of the API shape consumed by
`mem_blockMaxes_iff_isBlockMax` (whose RHS is `∃ h : i ∈ s, IsBlockMax π i h`)
even though the propositional body does not mention it.  The binder is
kept (not underscored) so the on-chain underscore-parameter audit (I2)
sees an honest, intentionally-unused API argument rather than a hidden
`_h_atom`; the `unusedVariables` linter is silenced for this one def. -/
def IsBlockMax (π : NC s) (i : α) (h_in : i ∈ s) : Prop :=
  ∀ j ∈ π.val.part i, j ≤ i

/-- `IsBlockMax` is decidable for `LinearOrder` `α`. -/
instance (π : NC s) (i : α) (h_in : i ∈ s) :
    Decidable (IsBlockMax π i h_in) := by
  unfold IsBlockMax
  infer_instance

/-- The maximum of each block `B` satisfies `IsBlockMax`. -/
theorem max'_block_isBlockMax (π : NC s) (B : Finset α) (hB : B ∈ π.val.parts)
    (h_ne : B.Nonempty) :
    IsBlockMax π (B.max' h_ne) (π.val.subset hB (B.max'_mem h_ne)) := by
  intro j hj
  have h_part_eq : π.val.part (B.max' h_ne) = B :=
    π.val.part_eq_of_mem hB (B.max'_mem h_ne)
  rw [h_part_eq] at hj
  exact B.le_max' j hj

/-- If `i` is the block-max in its block, then `i = (block of i).max'`. -/
theorem isBlockMax_iff_eq_max' (π : NC s) (i : α) (h_in : i ∈ s) :
    IsBlockMax π i h_in ↔
      i = (π.val.part i).max' ⟨i, π.val.mem_part_self.mpr h_in⟩ := by
  unfold IsBlockMax
  constructor
  · intro h_le
    apply le_antisymm
    · exact (π.val.part i).le_max' i (π.val.mem_part_self.mpr h_in)
    · apply (π.val.part i).max'_le
      exact h_le
  · intro h_eq j hj
    rw [h_eq]
    exact (π.val.part i).le_max' j hj

/-- **`s.max'` is always a block-max**: the global maximum of `s` is the
max of its block (since it's ≥ all elements of `s`, including its block's
elements). -/
theorem isBlockMax_s_max' (π : NC s) (hs : s.Nonempty) :
    IsBlockMax π (s.max' hs) (s.max'_mem hs) := by
  intro j hj
  -- j ∈ π.val.part (s.max' hs) ⊆ s
  have h_part_sub_s : π.val.part (s.max' hs) ⊆ s :=
    π.val.subset (π.val.part_mem.mpr (s.max'_mem hs))
  exact s.le_max' j (h_part_sub_s hj)

/-- **The block containing `s.max'` is `blockOfLast π hs`**. -/
theorem part_s_max'_eq_blockOfLast (π : NC s) (hs : s.Nonempty) :
    π.val.part (s.max' hs) = blockOfLast π hs := rfl

/-- The set of block-max elements of `π`. -/
noncomputable def blockMaxes (π : NC s) : Finset α :=
  s.filter (fun i => ∀ j ∈ π.val.part i, j ≤ i)

/-- Membership in `blockMaxes`. -/
theorem mem_blockMaxes_iff (π : NC s) (i : α) :
    i ∈ blockMaxes π ↔ i ∈ s ∧ ∀ j ∈ π.val.part i, j ≤ i := by
  unfold blockMaxes
  rw [Finset.mem_filter]

/-- `i ∈ blockMaxes π` iff `IsBlockMax π i (mem_proof)`. -/
theorem mem_blockMaxes_iff_isBlockMax (π : NC s) (i : α) :
    i ∈ blockMaxes π ↔ ∃ h : i ∈ s, IsBlockMax π i h := by
  rw [mem_blockMaxes_iff]
  constructor
  · rintro ⟨h_in, h_max⟩
    exact ⟨h_in, h_max⟩
  · rintro ⟨h_in, h_max⟩
    exact ⟨h_in, h_max⟩

/-- **KEY STRUCTURAL THEOREM**: `numBlocks π = (blockMaxes π).card`.

Bijection blocks ↔ block-maxes via `B ↦ B.max'` (forward) and `i ↦ π.val.part i` (backward).
Both maps are well-defined, injective, and inverse of each other. -/
theorem numBlocks_eq_blockMaxes_card (π : NC s) :
    numBlocks π = (blockMaxes π).card := by
  unfold numBlocks
  symm
  refine Finset.card_bij (fun i hi => π.val.part i) ?_ ?_ ?_
  · -- i ∈ blockMaxes → π.val.part i ∈ parts
    intros i hi
    rw [mem_blockMaxes_iff] at hi
    exact π.val.part_mem.mpr hi.1
  · -- Injectivity
    intros i hi j hj h_eq_part
    rw [mem_blockMaxes_iff] at hi hj
    have h_i_max : i = (π.val.part i).max' ⟨i, π.val.mem_part_self.mpr hi.1⟩ := by
      apply le_antisymm
      · exact (π.val.part i).le_max' i (π.val.mem_part_self.mpr hi.1)
      · apply (π.val.part i).max'_le
        exact hi.2
    have h_j_max : j = (π.val.part j).max' ⟨j, π.val.mem_part_self.mpr hj.1⟩ := by
      apply le_antisymm
      · exact (π.val.part j).le_max' j (π.val.mem_part_self.mpr hj.1)
      · apply (π.val.part j).max'_le
        exact hj.2
    -- Now use h_eq_part to identify the two maxes
    have h_combined : (π.val.part i).max' ⟨i, π.val.mem_part_self.mpr hi.1⟩ =
        (π.val.part j).max' ⟨j, π.val.mem_part_self.mpr hj.1⟩ := by
      congr 1
    rw [← h_i_max, ← h_j_max] at h_combined
    exact h_combined
  · -- Surjectivity
    intros B hB
    have h_B_ne : B.Nonempty := π.val.nonempty_of_mem_parts hB
    refine ⟨B.max' h_B_ne, ?_, ?_⟩
    · rw [mem_blockMaxes_iff]
      refine ⟨π.val.subset hB (B.max'_mem _), ?_⟩
      intros j hj
      have h_part_eq : π.val.part (B.max' h_B_ne) = B :=
        π.val.part_eq_of_mem hB (B.max'_mem _)
      rw [h_part_eq] at hj
      exact B.le_max' j hj
    · exact π.val.part_eq_of_mem hB (B.max'_mem _)

end NC

end Hamilton.Infrastructure
