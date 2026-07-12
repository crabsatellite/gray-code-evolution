/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCToDyckPeaks

/-!
# Prefix non-negativity of the stack-encoding list

The technical part of the bijection: every prefix of `toDyckList π` has
`count D ≤ count U`.  This makes `toDyckList π` a valid Dyck word.

## Structural argument (global view)

Process elements of `s` in increasing order.  After `j` complete steps,
let `sum_j = ∑ {|part i| : i ∈ first j elements ∧ i is block-max}`.
Then:

* `count U after j steps = j`.
* `count D after j steps = sum_j`.
* Height after step `j` = `j - sum_j`.

**KEY INEQUALITY**: `sum_j ≤ j`.

Why: each block-max `i` in first `j` elements has `part i ⊆ {x ≤ i} ⊆
first j elements` (since `i ≤ first j` means rank `i ≤ j-1`, and `x ≤ i`
forces `rank x ≤ rank i ≤ j-1`).  Blocks (`part i`) for different
block-maxes are disjoint.  So the union of all completed-block elements
has size = `sum_j` AND is ⊆ first j elements, hence `sum_j ≤ j`.

Within step j+1:
* After U: height = (j - sum_j) + 1 ≥ 1.
* After m D's (only if block-max with size c, m ≤ c):
  height = j + 1 - sum_j - m ≥ j + 1 - sum_{j+1} = height at end of step j+1 ≥ 0.

So prefix non-neg reduces to **step-boundary non-neg** (`sum_j ≤ j`).

## Main result

* `NC.toDyckList_count_D_take_le_count_U_take` — prefix non-negativity.

## Tags

NC, DyckWord, prefix, non-negativity, bijection
-/

namespace Hamilton.Infrastructure

namespace NC

open DyckStep List

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-! ### First `j` elements of sorted `s` as a Finset -/

/-- The Finset of the first `j` elements of sorted `s` (or all of `s` if `j ≥ s.card`). -/
noncomputable def firstNElts (s : Finset α) (j : ℕ) : Finset α :=
  ((s.sort (· ≤ ·)).take j).toFinset

theorem firstNElts_subset (s : Finset α) (j : ℕ) :
    firstNElts s j ⊆ s := by
  intro x hx
  unfold firstNElts at hx
  rw [List.mem_toFinset, List.mem_take_iff_getElem] at hx
  obtain ⟨n, _, hn_eq⟩ := hx
  rw [← hn_eq]
  have h_in_sort : (s.sort (· ≤ ·))[n] ∈ s.sort (· ≤ ·) := List.getElem_mem _
  exact (Finset.mem_sort _).mp h_in_sort

theorem firstNElts_card_le (s : Finset α) (j : ℕ) :
    (firstNElts s j).card ≤ j := by
  unfold firstNElts
  have h_sort_nodup : (s.sort (· ≤ ·)).Nodup := s.sort_nodup _
  have h_nodup : ((s.sort (· ≤ ·)).take j).Nodup :=
    h_sort_nodup.sublist (List.take_sublist j _)
  rw [List.toFinset_card_of_nodup h_nodup]
  exact List.length_take_le j _

/-- **Key**: An element `x ∈ s` is in `firstNElts s j` iff its rank in sorted `s` is `< j`.
Equivalently: `x ∈ firstNElts s j ↔ x ∈ s ∧ |{y ∈ s : y < x}| < j` (assuming distinct elements).
We use a weaker but sufficient form: if `x ≤ i` and `i ∈ firstNElts s j`, then `x ∈ firstNElts s j`. -/
theorem firstNElts_downward_closed (s : Finset α) (j : ℕ) {x i : α}
    (hi : i ∈ firstNElts s j) (hx_in_s : x ∈ s) (hx_le : x ≤ i) :
    x ∈ firstNElts s j := by
  unfold firstNElts at *
  rw [List.mem_toFinset] at hi ⊢
  -- i ∈ take j (s.sort), so i = s.sort[n] for some n < j.
  -- We need to show x ∈ take j (s.sort), i.e., x = s.sort[m] for some m < j.
  -- x is at some position m in s.sort (since x ∈ s).
  -- By sortedness and x ≤ i, m ≤ n.
  -- Hence m < j.
  rw [List.mem_take_iff_getElem] at hi
  obtain ⟨n, hn, hni⟩ := hi
  have h_x_in_sort : x ∈ s.sort (· ≤ ·) := (Finset.mem_sort _).mpr hx_in_s
  rw [List.mem_iff_getElem] at h_x_in_sort
  obtain ⟨m, hm, hmx⟩ := h_x_in_sort
  -- Now we have: s.sort[n] = i (hni), s.sort[m] = x (hmx), x ≤ i.
  -- Need: m < j.
  -- If m ≤ n: done since n < j.
  -- If m > n: by sortedness, x = s.sort[m] ≥ s.sort[n] = i. Combined with x ≤ i: x = i.
  --          But sort is Nodup, so m = n, contradiction.
  rw [List.mem_take_iff_getElem]
  by_cases h_mn : m ≤ n
  · exact ⟨m, by omega, hmx⟩
  · push Not at h_mn
    -- m > n. Sort is sorted, so s.sort[n] ≤ s.sort[m], i.e., i ≤ x.
    have h_sort_le : (s.sort (· ≤ ·))[n] ≤ (s.sort (· ≤ ·))[m] := by
      have h_sorted := Finset.pairwise_sort s (· ≤ ·)
      exact h_sorted.rel_get_of_le (Nat.le_of_lt h_mn)
    rw [hni, hmx] at h_sort_le
    have h_x_eq_i : x = i := le_antisymm hx_le h_sort_le
    -- Now s.sort[n] = i = x = s.sort[m], but Nodup means n = m. Contradiction.
    have h_nodup : (s.sort (· ≤ ·)).Nodup := s.sort_nodup _
    have h_eq : (s.sort (· ≤ ·))[n] = (s.sort (· ≤ ·))[m] := by
      rw [hni, hmx]; exact h_x_eq_i.symm
    -- Use nodup: distinct indices give distinct elements
    rw [List.Nodup.getElem_inj_iff h_nodup] at h_eq
    omega

/-! ### Completed blocks at step j -/

/-- The set of `π`-blocks "completed" by step `j`: blocks whose maximum is among
the first `j` elements of sorted `s`. -/
noncomputable def completedBlocks (π : NC s) (j : ℕ) : Finset (Finset α) :=
  π.val.parts.filter (fun B => ∃ h : B.Nonempty, B.max' h ∈ firstNElts s j)

/-- A completed block is contained in `firstNElts s j`. -/
theorem completedBlock_subset_firstNElts (π : NC s) (j : ℕ)
    (B : Finset α) (hB : B ∈ completedBlocks π j) :
    B ⊆ firstNElts s j := by
  unfold completedBlocks at hB
  rw [Finset.mem_filter] at hB
  obtain ⟨hB_part, h_ne, h_max_in⟩ := hB
  intro x hx
  -- x ∈ B, B.max' ∈ firstNElts s j, x ≤ B.max'.
  -- Need: x ∈ firstNElts s j.
  have h_x_in_s : x ∈ s := π.val.subset hB_part hx
  have h_x_le_max : x ≤ B.max' h_ne := B.le_max' x hx
  exact firstNElts_downward_closed s j h_max_in h_x_in_s h_x_le_max

/-- Completed blocks are pairwise disjoint (inherited from `π.val.parts`). -/
theorem completedBlocks_pairwiseDisjoint (π : NC s) (j : ℕ) :
    (completedBlocks π j : Set (Finset α)).PairwiseDisjoint id := by
  apply Set.PairwiseDisjoint.subset π.val.supIndep.pairwiseDisjoint
  intro B hB
  unfold completedBlocks at hB
  exact (Finset.mem_filter.mp hB).1

/-- **Sum of completed block sizes** equals the cardinality of their biUnion. -/
theorem sum_completedBlocks_card_eq_biUnion (π : NC s) (j : ℕ) :
    ∑ B ∈ completedBlocks π j, B.card = ((completedBlocks π j).biUnion id).card := by
  rw [Finset.card_biUnion (completedBlocks_pairwiseDisjoint π j)]
  rfl

/-- **Biunion of completed blocks is contained in `firstNElts s j`**. -/
theorem biUnion_completedBlocks_subset (π : NC s) (j : ℕ) :
    (completedBlocks π j).biUnion id ⊆ firstNElts s j := by
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨B, hB, hxB⟩ := hx
  exact completedBlock_subset_firstNElts π j B hB hxB

/-- **KEY LEMMA**: Sum of completed block sizes ≤ step count. -/
theorem sum_completedBlocks_card_le (π : NC s) (j : ℕ) :
    ∑ B ∈ completedBlocks π j, B.card ≤ j := by
  rw [sum_completedBlocks_card_eq_biUnion]
  calc ((completedBlocks π j).biUnion id).card
      ≤ (firstNElts s j).card := Finset.card_le_card (biUnion_completedBlocks_subset π j)
    _ ≤ j := firstNElts_card_le s j

/-! ### Bridge to list-level step-D counts

The list-level sum equals the Finset-level sum via the bijection
`i ↦ part i` between (block-maxes ∩ firstNElts) and `completedBlocks`. -/

/-- The list-level step-D-count sum over `(s.sort).take j` equals the Finset-level
sum over `completedBlocks π j`.

Proof: convert list-sum to Finset-sum over `firstNElts s j`, then apply the
block-max ↔ parts bijection (restricted to "completed" entries on each side). -/
theorem list_sum_step_D_take_eq_completedBlocks_sum (π : NC s) (j : ℕ) :
    (((s.sort (· ≤ ·)).take j).map
        (fun i => if ∀ k ∈ π.val.part i, k ≤ i then (π.val.part i).card else 0)).sum =
      ∑ B ∈ completedBlocks π j, B.card := by
  -- Step 1: convert list-sum to Finset-sum over the Finset `firstNElts s j`.
  set f : α → ℕ := fun i => if ∀ k ∈ π.val.part i, k ≤ i then (π.val.part i).card else 0
    with h_f_def
  have h_take_nodup : ((s.sort (· ≤ ·)).take j).Nodup :=
    (s.sort_nodup _).sublist (List.take_sublist j _)
  have h_list_to_finset :
      (((s.sort (· ≤ ·)).take j).map f).sum = ∑ i ∈ firstNElts s j, f i := by
    unfold firstNElts
    rw [Finset.sum_eq_multiset_sum]
    -- For Nodup l: l.toFinset.val = ↑l (via List.toFinset_eq).
    have h_val_eq : (((s.sort (· ≤ ·)).take j).toFinset).val =
        ↑((s.sort (· ≤ ·)).take j) := by
      rw [← List.toFinset_eq h_take_nodup]
    rw [h_val_eq, Multiset.map_coe, Multiset.sum_coe]
  rw [h_list_to_finset]
  -- Step 2: split the Finset-sum by the if-condition, then apply the bijection.
  -- For i ∈ firstNElts s j: f i = |part i| if block-max, else 0.
  -- So ∑ i ∈ firstNElts s j, f i = ∑ i ∈ firstNElts s j ∩ blockMaxes, |part i|.
  have h_filter_sum :
      ∑ i ∈ firstNElts s j, f i =
      ∑ i ∈ (firstNElts s j).filter (fun i => ∀ k ∈ π.val.part i, k ≤ i),
        (π.val.part i).card := by
    rw [Finset.sum_filter]
  rw [h_filter_sum]
  -- Step 3: bijection `i ↦ part i` from (block-max ∩ firstNElts) to completedBlocks.
  apply Finset.sum_bij (fun i _ => π.val.part i)
  · -- well-defined
    intros i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hi_first, hi_max⟩ := hi
    have hi_in_s : i ∈ s := firstNElts_subset s j hi_first
    have h_part_mem : π.val.part i ∈ π.val.parts := π.val.part_mem.mpr hi_in_s
    unfold completedBlocks
    rw [Finset.mem_filter]
    refine ⟨h_part_mem, ⟨i, π.val.mem_part_self.mpr hi_in_s⟩, ?_⟩
    -- Goal: (part i).max' ⟨i, ...⟩ ∈ firstNElts s j
    -- We have i ∈ firstNElts. We need to show (part i).max' = i.
    have h_eq : (π.val.part i).max' ⟨i, π.val.mem_part_self.mpr hi_in_s⟩ = i := by
      apply le_antisymm
      · apply (π.val.part i).max'_le
        exact hi_max
      · exact (π.val.part i).le_max' i (π.val.mem_part_self.mpr hi_in_s)
    rw [h_eq]
    exact hi_first
  · -- injectivity
    intros i hi j' hj' h_eq_part
    rw [Finset.mem_filter] at hi hj'
    have hi_in_s : i ∈ s := firstNElts_subset s j hi.1
    have hj_in_s : j' ∈ s := firstNElts_subset s j hj'.1
    have h_i_max : i = (π.val.part i).max' ⟨i, π.val.mem_part_self.mpr hi_in_s⟩ := by
      apply le_antisymm
      · exact (π.val.part i).le_max' i (π.val.mem_part_self.mpr hi_in_s)
      · apply (π.val.part i).max'_le
        exact hi.2
    have h_j_max : j' = (π.val.part j').max' ⟨j', π.val.mem_part_self.mpr hj_in_s⟩ := by
      apply le_antisymm
      · exact (π.val.part j').le_max' j' (π.val.mem_part_self.mpr hj_in_s)
      · apply (π.val.part j').max'_le
        exact hj'.2
    have h_combined : (π.val.part i).max' ⟨i, π.val.mem_part_self.mpr hi_in_s⟩ =
        (π.val.part j').max' ⟨j', π.val.mem_part_self.mpr hj_in_s⟩ := by
      congr 1
    rw [← h_i_max, ← h_j_max] at h_combined
    exact h_combined
  · -- surjectivity
    intros B hB
    unfold completedBlocks at hB
    rw [Finset.mem_filter] at hB
    obtain ⟨hB_part, h_ne, h_max_in⟩ := hB
    refine ⟨B.max' h_ne, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨h_max_in, ?_⟩
      have h_part_eq : π.val.part (B.max' h_ne) = B :=
        π.val.part_eq_of_mem hB_part (B.max'_mem _)
      intros k hk
      rw [h_part_eq] at hk
      exact B.le_max' k hk
    · exact π.val.part_eq_of_mem hB_part (B.max'_mem _)
  · -- same value
    intros i _
    rfl

/-! ### Step-boundary non-negativity (list-level) -/

/-! ### Step-boundary non-negativity (list-level) -/

/-- count_U of first j-step prefix equals `min j s.card`. -/
theorem step_count_U_eq (π : NC s) (j : ℕ) :
    (((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π)).count U =
      min j s.card := by
  rw [count_U_flatMap_stepEncoding, List.length_take, Finset.length_sort]

/-- count_D of first j-step prefix equals `∑ B ∈ completedBlocks π j, B.card`. -/
theorem step_count_D_eq (π : NC s) (j : ℕ) :
    (((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π)).count D =
      ∑ B ∈ completedBlocks π j, B.card := by
  rw [count_D_flatMap_stepEncoding, list_sum_step_D_take_eq_completedBlocks_sum]

/-- **STEP-BOUNDARY NON-NEG**: For prefix at step boundary `j`, count_D ≤ count_U.

count_D = sum of completed block sizes ≤ j.
count_U = min j s.card.
For j ≤ s.card: count_U = j ≥ count_D. ✓
For j > s.card: count_U = s.card; but completedBlocks π j = completedBlocks π s.card
(saturated at s.card), so count_D ≤ s.card = count_U. -/
theorem step_count_D_le_count_U (π : NC s) (j : ℕ) :
    (((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π)).count D ≤
    (((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π)).count U := by
  rw [step_count_U_eq, step_count_D_eq]
  -- Show ∑ B ∈ completedBlocks π j, B.card ≤ min j s.card.
  -- The completed blocks are subsets of firstNElts s j, and firstNElts s j ⊆ s.
  -- So biUnion ⊆ firstNElts s j AND biUnion ⊆ s, hence its card ≤ min |firstNElts j| s.card.
  rw [sum_completedBlocks_card_eq_biUnion]
  have h1 : ((completedBlocks π j).biUnion id).card ≤ (firstNElts s j).card :=
    Finset.card_le_card (biUnion_completedBlocks_subset π j)
  have h2 : (firstNElts s j).card ≤ j := firstNElts_card_le s j
  have h3 : (firstNElts s j).card ≤ s.card :=
    Finset.card_le_card (firstNElts_subset s j)
  have h4 : ((completedBlocks π j).biUnion id).card ≤ s.card := h1.trans h3
  have h5 : ((completedBlocks π j).biUnion id).card ≤ j := h1.trans h2
  omega

end NC

end Hamilton.Infrastructure
