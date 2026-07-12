/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCToDyckPrefix

/-!
# Packaging `toDyckList` as a `DyckWord`

Combines balance + prefix non-negativity into the `DyckWord` structure.

## Strategy for within-step prefix non-negativity

For prefix at step `j+1` after `m` characters of `stepEncoding(l_j)`:

* `m = 0`: at step boundary `j`, use `step_count_D_le_count_U` at `j`.
* `m ≥ 1`: at least the `U` of step `j+1` is emitted.
  - count_U(prefix) = count_U(j_flat) + 1.
  - count_D(prefix) = count_D(j_flat) + (m-1 D's, capped at block size).
  - Bound: count_D(prefix) ≤ count_D(j_flat) + count_D(step) = (j+1)-step count_D
    ≤ (j+1)-step count_U = count_U(prefix). ← step boundary at j+1.

## Main results

* `NC.toDyckList_prefix_count_D_le_count_U` — prefix non-negativity.
* `NC.toDyckWord` — the canonical `DyckWord` for `π`.
* `NC.toDyckWord_semilength` — `(toDyckWord π).semilength = s.card`.
* `NC.toDyckWord_peakCount` — `peakCount (toDyckWord π) = numBlocks π`.

## Tags

NC, DyckWord, bijection, stack encoding, package, non-negativity
-/

namespace Hamilton.Infrastructure

namespace NC

open DyckStep List

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-! ### Sublist count bounds -/

/-- count_U of `(U :: replicate k D).take m` for `m ≥ 1` equals 1. -/
theorem count_U_take_U_cons_replicate_D (k m : ℕ) (hm : 1 ≤ m) :
    ((U :: List.replicate k D).take m).count U = 1 := by
  rcases m with _ | m'
  · omega
  · simp only [List.take_succ_cons, List.count_cons]
    have h_rep : ((List.replicate k D).take m').count U = 0 := by
      rw [List.take_replicate, List.count_replicate]
      simp [dyckStep_D_ne_U]
    rw [h_rep]
    simp

/-- count_U of `[U].take m` for `m ≥ 1` equals 1. -/
theorem count_U_take_U_singleton (m : ℕ) (hm : 1 ≤ m) :
    (([U] : List DyckStep).take m).count U = 1 := by
  have h_le : ([U] : List DyckStep).length ≤ m := by
    rw [List.length_singleton]; omega
  rw [List.take_of_length_le h_le]
  simp


/-- count of an element in `l.take m` is at most count in `l`. -/
theorem take_count_le_count {β : Type*} [DecidableEq β] (l : List β) (m : ℕ) (b : β) :
    (l.take m).count b ≤ l.count b :=
  (List.take_sublist m l).count_le b

/-- count_U of a step prefix is at most 1. -/
theorem stepEncoding_take_count_U_le_one (π : NC s) (i : α) (m : ℕ) :
    ((stepEncoding π i).take m).count U ≤ 1 := by
  calc ((stepEncoding π i).take m).count U
      ≤ (stepEncoding π i).count U := take_count_le_count _ m U
    _ = 1 := stepEncoding_count_U π i

/-! ### Inductive prefix non-negativity -/

/-- **PREFIX NON-NEGATIVITY (parameterized)**: For any `j` and any prefix length `m`
of the first `j`-step flatMap, count_D ≤ count_U. -/
theorem partialDyck_prefix_le (π : NC s) : ∀ j m,
    ((((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π)).take m).count D ≤
    ((((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π)).take m).count U := by
  intro j
  induction j with
  | zero =>
    intros m
    simp
  | succ j_pred ih =>
    intro m
    by_cases h_in : j_pred < (s.sort (· ≤ ·)).length
    · -- decompose take (j_pred+1) = take j_pred ++ [sort[j_pred]]
      have h_take_succ :
          (s.sort (· ≤ ·)).take (j_pred + 1) =
            (s.sort (· ≤ ·)).take j_pred ++ [(s.sort (· ≤ ·))[j_pred]'h_in] :=
        List.take_succ_eq_append_getElem h_in
      rw [h_take_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      -- Goal: ((take j_pred).flatMap ++ stepEncoding new_elt).take m has count_D ≤ count_U
      by_cases h_m : m ≤ (((s.sort (· ≤ ·)).take j_pred).flatMap (stepEncoding π)).length
      · -- prefix is within j_pred_flat
        rw [List.take_append_of_le_length h_m]
        exact ih m
      · -- prefix extends into the new step
        push Not at h_m
        rw [List.take_append]
        rw [List.take_of_length_le (le_of_lt h_m)]
        rw [List.count_append, List.count_append]
        -- Goal: count_D(j_flat) + count_D(step.take m') ≤ count_U(j_flat) + count_U(step.take m')
        -- where m' = m - j_flat.length, m' ≥ 1.
        -- Apply step boundary at j_pred + 1:
        have h_bound :
            (((s.sort (· ≤ ·)).take (j_pred + 1)).flatMap (stepEncoding π)).count D ≤
            (((s.sort (· ≤ ·)).take (j_pred + 1)).flatMap (stepEncoding π)).count U :=
          step_count_D_le_count_U π (j_pred + 1)
        rw [h_take_succ, List.flatMap_append] at h_bound
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h_bound
        rw [List.count_append, List.count_append] at h_bound
        -- h_bound: count_D(j_flat) + count_D(step) ≤ count_U(j_flat) + count_U(step)
        -- where count_U(step) = 1.
        have h_step_U : (stepEncoding π ((s.sort (· ≤ ·))[j_pred]'h_in)).count U = 1 :=
          stepEncoding_count_U π _
        rw [h_step_U] at h_bound
        -- Now: count_D(j_flat) + count_D(step) ≤ count_U(j_flat) + 1.
        -- And: count_D(step.take m') ≤ count_D(step).
        have h_step_take_D :
            ((stepEncoding π ((s.sort (· ≤ ·))[j_pred]'h_in)).take
              (m - (((s.sort (· ≤ ·)).take j_pred).flatMap (stepEncoding π)).length)).count D
            ≤ (stepEncoding π ((s.sort (· ≤ ·))[j_pred]'h_in)).count D :=
          take_count_le_count _ _ D
        -- And the step.take has count_U = 1 (since m' ≥ 1).
        have hm'_pos : 1 ≤ m - (((s.sort (· ≤ ·)).take j_pred).flatMap (stepEncoding π)).length := by
          omega
        have h_step_take_U_eq :
            ((stepEncoding π ((s.sort (· ≤ ·))[j_pred]'h_in)).take
              (m - (((s.sort (· ≤ ·)).take j_pred).flatMap (stepEncoding π)).length)).count U = 1 := by
          unfold stepEncoding
          split_ifs with h_bmax
          · exact count_U_take_U_cons_replicate_D _ _ hm'_pos
          · exact count_U_take_U_singleton _ hm'_pos
        rw [h_step_take_U_eq]
        -- Final: count_D(j_flat) + count_D(step.take m') ≤ count_U(j_flat) + 1.
        omega
    · -- j_pred ≥ length: take saturates.
      push Not at h_in
      have h_eq : (s.sort (· ≤ ·)).take (j_pred + 1) = (s.sort (· ≤ ·)).take j_pred := by
        rw [List.take_of_length_le (h_in.trans (Nat.le_succ _)),
            List.take_of_length_le h_in]
      rw [h_eq]
      exact ih m

/-- For `j ≥ s.card`, `(s.sort).take j = s.sort`. -/
theorem take_sort_card_eq_sort (s : Finset α) :
    (s.sort (· ≤ ·)).take s.card = s.sort (· ≤ ·) := by
  rw [List.take_of_length_le]
  rw [Finset.length_sort]

/-- **PREFIX NON-NEGATIVITY**: For any `k`, count_D ≤ count_U of `toDyckList.take k`. -/
theorem toDyckList_prefix_count_D_le_count_U (π : NC s) (k : ℕ) :
    ((toDyckList π).take k).count D ≤ ((toDyckList π).take k).count U := by
  have h := partialDyck_prefix_le π s.card k
  rw [take_sort_card_eq_sort] at h
  exact h

/-! ### Package as `DyckWord` -/

/-- The canonical `DyckWord` for `π : NC s` via the stack encoding. -/
noncomputable def toDyckWord (π : NC s) : DyckWord where
  toList := toDyckList π
  count_U_eq_count_D := toDyckList_count_U_eq_count_D π
  count_D_le_count_U := toDyckList_prefix_count_D_le_count_U π

@[simp] theorem toDyckWord_toList (π : NC s) :
    (toDyckWord π).toList = toDyckList π := rfl

/-- **SEMILENGTH OF `toDyckWord`**: equals `s.card`. -/
theorem toDyckWord_semilength (π : NC s) :
    (toDyckWord π).semilength = s.card := by
  unfold DyckWord.semilength
  rw [toDyckWord_toList, toDyckList_count_U]

/-- **PEAK COUNT OF `toDyckWord`**: equals `numBlocks π` — the structural correspondence. -/
theorem toDyckWord_peakCount (π : NC s) :
    DyckWord.peakCount (toDyckWord π) = numBlocks π := by
  unfold DyckWord.peakCount
  rw [toDyckWord_toList]
  exact countPeaksAux_toDyckList_eq_numBlocks π

end NC

end Hamilton.Infrastructure
