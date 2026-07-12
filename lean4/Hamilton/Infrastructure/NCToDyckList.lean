/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCBlockMax
import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Stack-encoding list for NC

The **list level** of the bijection `NC s → DyckWord`.  Defines the
underlying `List DyckStep` and proves:

* `toDyckList π` has length `2 · s.card`.
* `toDyckList π` has `s.card` `U`s and `s.card` `D`s.

The full DyckWord packaging (which additionally requires the
**non-negativity** of all prefixes) is in `NCToDyckWord.lean`.

## Stack encoding

Process elements of `s` in increasing order.  For each `i ∈ s`:

* Emit `U`.
* If `i` is block-max of its block, emit `|block of i|` `D`s.

## Main definitions

* `NC.stepEncoding π i` — the per-element contribution.
* `NC.toDyckList π` — the underlying list.

## Main results

* `NC.toDyckList_count_U` — total count of `U`s is `s.card`.
* `NC.toDyckList_count_D` — total count of `D`s is `s.card`.
* `NC.toDyckList_length` — list length is `2 · s.card`.

## Tags

NC, DyckWord, list, stack encoding, bijection
-/

namespace Hamilton.Infrastructure

namespace NC

open DyckStep List

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- `U ≠ D` (decidable). -/
theorem dyckStep_U_ne_D : (U : DyckStep) ≠ D := by decide

/-- `D ≠ U` (decidable). -/
theorem dyckStep_D_ne_U : (D : DyckStep) ≠ U := by decide

/-- The per-element contribution to `toDyckList`:
- `[U]` if `i` is not the block-max of its part.
- `U :: replicate |part i| D` if `i` is the block-max. -/
noncomputable def stepEncoding (π : NC s) (i : α) : List DyckStep :=
  if ∀ j ∈ π.val.part i, j ≤ i then
    U :: List.replicate (π.val.part i).card D
  else
    [U]

/-- The underlying list of the stack-encoding Dyck word for `π : NC s`. -/
noncomputable def toDyckList (π : NC s) : List DyckStep :=
  (s.sort (· ≤ ·)).flatMap (stepEncoding π)

/-! ### `count U` and `count D` of a single step -/

/-- A single step contributes exactly one `U`. -/
theorem stepEncoding_count_U (π : NC s) (i : α) :
    (stepEncoding π i).count U = 1 := by
  unfold stepEncoding
  split_ifs with h
  · -- branch: U :: replicate (part i).card D
    have h_rep : (List.replicate (π.val.part i).card D).count U = 0 := by
      rw [List.count_replicate]
      simp [dyckStep_D_ne_U]
    rw [List.count_cons, h_rep]
    simp
  · -- branch: [U]
    simp

/-- A single step contributes `|part i|` `D`s when `i` is block-max, `0` otherwise. -/
theorem stepEncoding_count_D (π : NC s) (i : α) :
    (stepEncoding π i).count D =
      if ∀ j ∈ π.val.part i, j ≤ i then (π.val.part i).card else 0 := by
  unfold stepEncoding
  split_ifs with h
  · -- branch: U :: replicate (part i).card D
    have h_rep : (List.replicate (π.val.part i).card D).count D = (π.val.part i).card := by
      rw [List.count_replicate]
      simp
    rw [List.count_cons, h_rep]
    simp [dyckStep_U_ne_D]
  · -- branch: [U]
    simp

/-- Length of a single step: `1 + |part i|` if block-max, `1` otherwise. -/
theorem stepEncoding_length (π : NC s) (i : α) :
    (stepEncoding π i).length =
      if ∀ j ∈ π.val.part i, j ≤ i then 1 + (π.val.part i).card else 1 := by
  unfold stepEncoding
  split_ifs with h
  · rw [List.length_cons, List.length_replicate, Nat.add_comm]
  · rfl

/-! ### `count U` of the full list -/

/-- Helper: `count U` of `l.flatMap (stepEncoding π)` equals `l.length`. -/
theorem count_U_flatMap_stepEncoding (π : NC s) (l : List α) :
    (l.flatMap (stepEncoding π)).count U = l.length := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    rw [List.flatMap_cons, List.count_append, stepEncoding_count_U, ih,
        List.length_cons]
    omega

/-- Total `U` count in `toDyckList`: equal to `s.card`. -/
theorem toDyckList_count_U (π : NC s) :
    (toDyckList π).count U = s.card := by
  unfold toDyckList
  rw [count_U_flatMap_stepEncoding, Finset.length_sort]

/-! ### `count D` of the full list (via summing block sizes) -/

/-- Helper: `count D` of `l.flatMap (stepEncoding π)` equals the sum of step-D-counts. -/
theorem count_D_flatMap_stepEncoding (π : NC s) (l : List α) :
    (l.flatMap (stepEncoding π)).count D =
      (l.map (fun i => if ∀ j ∈ π.val.part i, j ≤ i then (π.val.part i).card else 0)).sum := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    rw [List.flatMap_cons, List.count_append, stepEncoding_count_D, ih]
    simp

/-- Sum of `((s.sort r).map f).sum` equals `Finset.sum s f` (general bridge). -/
theorem sum_sort_map_eq_finsetSum {β : Type*} [AddCommMonoid β] (f : α → β) :
    ((s.sort (· ≤ ·)).map f).sum = ∑ i ∈ s, f i := by
  rw [Finset.sum_eq_multiset_sum]
  rw [show s.val = ((s.sort (· ≤ ·)) : Multiset α) from (Finset.sort_eq _ _).symm]
  rw [Multiset.map_coe, Multiset.sum_coe]

/-- The list-sum of step-D-counts equals the Finset-sum over `blockMaxes`. -/
theorem sum_step_D_counts_eq_blockMaxes_sum (π : NC s) :
    ((s.sort (· ≤ ·)).map
        (fun i => if ∀ j ∈ π.val.part i, j ≤ i then (π.val.part i).card else 0)).sum =
      ∑ i ∈ blockMaxes π, (π.val.part i).card := by
  rw [sum_sort_map_eq_finsetSum]
  unfold blockMaxes
  rw [Finset.sum_filter]

/-- Sum of `|part i|` over `i ∈ blockMaxes π` equals `s.card`.

By the bijection `B ↦ B.max'` between parts and block-maxes, this sum equals
`∑ B ∈ parts, |B| = |⋃ parts| = |s|`. -/
theorem sum_partCard_blockMaxes_eq_card (π : NC s) :
    ∑ i ∈ blockMaxes π, (π.val.part i).card = s.card := by
  -- Step 1: rewrite as ∑ B ∈ parts, B.card via bijection i ↦ part i.
  have h_bij : ∑ i ∈ blockMaxes π, (π.val.part i).card =
      ∑ B ∈ π.val.parts, B.card := by
    apply Finset.sum_bij (fun i _ => π.val.part i)
    · intros i hi
      rw [mem_blockMaxes_iff] at hi
      exact π.val.part_mem.mpr hi.1
    · intros i hi j hj h_eq_part
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
      have h_combined : (π.val.part i).max' ⟨i, π.val.mem_part_self.mpr hi.1⟩ =
          (π.val.part j).max' ⟨j, π.val.mem_part_self.mpr hj.1⟩ := by
        congr 1
      rw [← h_i_max, ← h_j_max] at h_combined
      exact h_combined
    · intros B hB
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
    · intros i hi
      rfl
  rw [h_bij]
  -- Step 2: ∑ B ∈ parts, B.card = s.card via card_biUnion
  have h_card : (π.val.parts.biUnion id).card = ∑ B ∈ π.val.parts, B.card := by
    rw [Finset.card_biUnion π.val.supIndep.pairwiseDisjoint]
    rfl
  rw [← h_card]
  -- biUnion parts id = sup parts id = s
  have h_eq : π.val.parts.biUnion id = π.val.parts.sup id := by
    rw [Finset.sup_eq_biUnion]
  rw [h_eq, π.val.sup_parts]

/-- Total `D` count in `toDyckList`: equal to `s.card`. -/
theorem toDyckList_count_D (π : NC s) :
    (toDyckList π).count D = s.card := by
  unfold toDyckList
  rw [count_D_flatMap_stepEncoding, sum_step_D_counts_eq_blockMaxes_sum,
      sum_partCard_blockMaxes_eq_card]

/-! ### Length of the full list -/

/-- `count U + count D = length` for any list of `DyckStep`. -/
theorem List.count_U_add_count_D (l : List DyckStep) :
    l.count U + l.count D = l.length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    cases a with
    | U =>
      have hU : ((U :: rest) : List DyckStep).count U = rest.count U + 1 := by
        rw [List.count_cons]; simp
      have hD : ((U :: rest) : List DyckStep).count D = rest.count D := by
        rw [List.count_cons]; simp [dyckStep_U_ne_D]
      rw [hU, hD, List.length_cons]
      omega
    | D =>
      have hU : ((D :: rest) : List DyckStep).count U = rest.count U := by
        rw [List.count_cons]; simp [dyckStep_D_ne_U]
      have hD : ((D :: rest) : List DyckStep).count D = rest.count D + 1 := by
        rw [List.count_cons]; simp
      rw [hU, hD, List.length_cons]
      omega

/-- Total length of `toDyckList`: `2 * s.card`. -/
theorem toDyckList_length (π : NC s) :
    (toDyckList π).length = 2 * s.card := by
  have h := List.count_U_add_count_D (toDyckList π)
  rw [toDyckList_count_U, toDyckList_count_D] at h
  omega

/-- The U-count equals the D-count. -/
theorem toDyckList_count_U_eq_count_D (π : NC s) :
    (toDyckList π).count U = (toDyckList π).count D := by
  rw [toDyckList_count_U, toDyckList_count_D]

end NC

end Hamilton.Infrastructure
