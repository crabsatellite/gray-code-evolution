/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.DyckPeaks
import Hamilton.Infrastructure.NCToDyckList

/-!
# Peak count of the stack-encoding list equals `numBlocks`

The **structural heart** of the bijection `NC s ↔ DyckWord`:

For any `π : NC s`, the number of peaks (`U :: D` patterns) in
`toDyckList π` equals `numBlocks π`.

## Main results

* `NC.countPeaksAux_stepEncoding` — per-element peak contribution.
* `NC.countPeaksAux_flatMap_stepEncoding` — flatMap is additive
  for `stepEncoding` (key boundary lemma).
* `NC.countPeaksAux_toDyckList_eq_numBlocks` — total peak count = `numBlocks`.

## Tags

NC, DyckWord, peak count, block-max, bijection
-/

namespace Hamilton.Infrastructure

namespace NC

open DyckStep List DyckWord

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-! ### Auxiliary peak lemmas for our specific shapes -/

/-- `countPeaksAux` of a list of all `D`s is `0`. -/
theorem countPeaksAux_replicate_D (n : ℕ) :
    countPeaksAux (List.replicate n D) = 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases k with _ | k'
    · -- replicate 1 D = [D]
      rfl
    · -- replicate (k'+2) D = D :: D :: replicate k' D
      rw [List.replicate_succ, List.replicate_succ]
      rw [countPeaksAux_cons_cons]
      have h_if : (if (D : DyckStep) = U ∧ (D : DyckStep) = D then 1 else 0) = 0 := by
        rw [if_neg]
        rintro ⟨h, _⟩
        exact dyckStep_D_ne_U h
      rw [h_if, Nat.zero_add]
      -- Now the goal is countPeaksAux (D :: replicate k' D) = 0
      have h_eq : (D :: List.replicate k' D) = List.replicate (k' + 1) D := by
        rw [List.replicate_succ]
      rw [h_eq]
      exact ih

/-- `countPeaksAux (U :: replicate k D) = 1` for `k ≥ 1`, `0` for `k = 0`. -/
theorem countPeaksAux_U_replicate_D (k : ℕ) :
    countPeaksAux (U :: List.replicate k D) = if k = 0 then 0 else 1 := by
  cases k with
  | zero =>
    show countPeaksAux [U] = 0
    rfl
  | succ n =>
    rw [List.replicate_succ]
    rw [countPeaksAux_cons_cons]
    have h_if : (if (U : DyckStep) = U ∧ (D : DyckStep) = D then 1 else 0) = 1 := by
      rw [if_pos]
      exact ⟨rfl, rfl⟩
    rw [h_if]
    have h_no_peak : countPeaksAux (D :: List.replicate n D) = 0 := by
      have h_eq : (D :: List.replicate n D) = List.replicate (n + 1) D := by
        rw [List.replicate_succ]
      rw [h_eq]
      exact countPeaksAux_replicate_D _
    rw [h_no_peak]
    -- 1 + 0 = if (n+1 = 0) then 0 else 1 — RHS is 1, LHS is 1
    simp

/-! ### Per-element peak contribution -/

/-- The peak count of a single step:
- 1 if `i ∈ s` and `i` is block-max (the encoding is `[U, D, ..., D]`).
- 0 otherwise. -/
theorem countPeaksAux_stepEncoding_of_mem (π : NC s) (i : α) (h_in : i ∈ s) :
    countPeaksAux (stepEncoding π i) =
      if ∀ j ∈ π.val.part i, j ≤ i then 1 else 0 := by
  unfold stepEncoding
  split_ifs with h
  · -- branch: U :: replicate (part i).card D
    rw [countPeaksAux_U_replicate_D]
    -- (part i).card > 0 since i ∈ part i
    have h_mem_self : i ∈ π.val.part i := π.val.mem_part_self.mpr h_in
    have h_card_pos : (π.val.part i).card ≠ 0 := by
      intro h_zero
      rw [Finset.card_eq_zero] at h_zero
      rw [h_zero] at h_mem_self
      exact (Finset.notMem_empty _) h_mem_self
    rw [if_neg h_card_pos]
  · -- branch: [U]
    rfl

/-! ### `countPeaksAux` distributes over `flatMap` of `stepEncoding`

The key observation: every `stepEncoding π i` starts with `U`, so
the boundary between consecutive `stepEncoding π a` and `stepEncoding π b`
(in `(a :: b :: ...).flatMap (stepEncoding π)`) cannot create a peak:
the boundary pair is `(last of f(a), U)`, never `(U, D)`. -/

/-- Every step encoding starts with `U`. -/
theorem stepEncoding_head_eq_U (π : NC s) (i : α) :
    (stepEncoding π i).head? = some U := by
  unfold stepEncoding
  split_ifs with h
  · -- branch: U :: replicate ... D
    rfl
  · -- branch: [U]
    rfl

/-- Every step encoding is non-empty. -/
theorem stepEncoding_ne_nil (π : NC s) (i : α) :
    stepEncoding π i ≠ [] := by
  unfold stepEncoding
  split_ifs with h
  all_goals (intro h_nil; cases h_nil)

/-- **KEY BOUNDARY LEMMA**: For two consecutive lists where the second starts
with `U`, the peak count is additive (no boundary peak). -/
theorem countPeaksAux_append_of_second_starts_U (l1 l2 : List DyckStep)
    (h_l2 : l2.head? = some U) :
    countPeaksAux (l1 ++ l2) = countPeaksAux l1 + countPeaksAux l2 := by
  rw [countPeaksAux_append]
  rw [h_l2]
  -- Boundary indicator: l1.getLast? = some U ∧ some U = some D → false
  have h_some_ne : some U ≠ (some D : Option DyckStep) := by decide
  simp [h_some_ne]

/-- **MAIN LEMMA**: `countPeaksAux` of `l.flatMap (stepEncoding π)` equals
the sum of per-step peak contributions. -/
theorem countPeaksAux_flatMap_stepEncoding (π : NC s) (l : List α) :
    countPeaksAux (l.flatMap (stepEncoding π)) =
      (l.map (fun i => countPeaksAux (stepEncoding π i))).sum := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons]
    -- Now: countPeaksAux (stepEncoding π a ++ tail.flatMap (stepEncoding π))
    --    = countPeaksAux (stepEncoding π a) + ((tail.flatMap (stepEncoding π))-count)
    by_cases h_tail : tail = []
    · subst h_tail
      simp
    · -- tail nonempty; use the boundary lemma
      have h_tail_head : (tail.flatMap (stepEncoding π)).head? = some U := by
        rcases tail with _ | ⟨b, rest⟩
        · contradiction
        · rw [List.flatMap_cons]
          have h_step_ne := stepEncoding_ne_nil π b
          rw [List.head?_append]
          rw [List.head?_eq_some_head h_step_ne]
          rw [show ((stepEncoding π b).head h_step_ne : DyckStep) = U from ?_]
          · simp
          · -- (stepEncoding π b).head h_step_ne = U
            have h_head_opt := stepEncoding_head_eq_U π b
            -- h_head_opt : (stepEncoding π b).head? = some U
            -- We want (stepEncoding π b).head h_step_ne = U
            rw [List.head?_eq_some_head h_step_ne] at h_head_opt
            exact Option.some.inj h_head_opt
      rw [countPeaksAux_append_of_second_starts_U _ _ h_tail_head, ih]

/-! ### Connection to `blockMaxes` -/

/-- The sum of per-step peak contributions over `s.sort` equals the size of
`blockMaxes π`. -/
theorem sum_step_peaks_eq_blockMaxes_card (π : NC s) :
    ((s.sort (· ≤ ·)).map (fun i => countPeaksAux (stepEncoding π i))).sum =
      (blockMaxes π).card := by
  -- Step 1: per-step count = indicator of block-max (using mem of s)
  have h_rewrite : (s.sort (· ≤ ·)).map (fun i => countPeaksAux (stepEncoding π i)) =
      (s.sort (· ≤ ·)).map
        (fun i => if ∀ j ∈ π.val.part i, j ≤ i then 1 else 0) := by
    apply List.map_congr_left
    intros i hi
    rw [countPeaksAux_stepEncoding_of_mem π i ((Finset.mem_sort _).mp hi)]
  rw [h_rewrite]
  -- Step 2: list-sum to Finset-sum
  rw [sum_sort_map_eq_finsetSum]
  -- Step 3: ∑ ite ... = card filter
  unfold blockMaxes
  rw [Finset.card_filter]

/-! ### Final theorem: `peakCount (toDyckList π) = numBlocks π` -/

/-- **STRUCTURAL THEOREM**: The peak count of the stack-encoding list of `π`
equals `numBlocks π`. -/
theorem countPeaksAux_toDyckList_eq_numBlocks (π : NC s) :
    countPeaksAux (toDyckList π) = numBlocks π := by
  unfold toDyckList
  rw [countPeaksAux_flatMap_stepEncoding, sum_step_peaks_eq_blockMaxes_card,
      numBlocks_eq_blockMaxes_card]

end NC

end Hamilton.Infrastructure
