/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.GapIntervals
import Mathlib.Order.Interval.Finset.Fin

/-!
# `gapBefore` cardinality for singleton S

For `S = {x}` in `Finset.univ : Finset (Fin (n+1))`, the gap before
`x` has cardinality `x.val` (i.e., `{y : Fin (n+1) | y < x}`).

## Main results

* `NC.gap_singleton_card` — `(gapBefore univ {x} x).card = x.val`.

## Tags

NC, gapBefore, Fin, cardinality
-/

namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore mem_gapBefore)

/-- For `S = {x}` in `Finset.univ : Finset (Fin (n+1))`, the gap
before `x` equals `Iio x` (as `Finset (Fin (n+1))`). -/
theorem gap_singleton_eq_Iio (n : ℕ) (x : Fin (n+1)) :
    gapBefore (Finset.univ : Finset (Fin (n+1))) {x} x = Finset.Iio x := by
  ext y
  rw [mem_gapBefore, Finset.mem_Iio]
  constructor
  · rintro ⟨_, hy_lt, _⟩
    exact hy_lt
  · intro hy_lt
    refine ⟨Finset.mem_univ _, hy_lt, ?_⟩
    intro z hz_mem hz_lt
    rw [Finset.mem_singleton] at hz_mem
    subst hz_mem
    exact absurd hz_lt (lt_irrefl _)

/-- For `S = {x}` in `Finset.univ : Finset (Fin (n+1))`, the gap
before `x` has cardinality `x.val`. -/
theorem gap_singleton_card (n : ℕ) (x : Fin (n+1)) :
    (gapBefore (Finset.univ : Finset (Fin (n+1))) {x} x).card = x.val := by
  rw [gap_singleton_eq_Iio]
  exact Fin.card_Iio x

/-- For S with min = j, the gap before j in (Finset.univ, S) equals
`Finset.Iio j` (since no S-element is less than j). -/
theorem gap_at_min_eq_Iio (n : ℕ) (j : Fin (n+1))
    (S : Finset (Fin (n+1))) (hj_in : j ∈ S)
    (h_min : ∀ z ∈ S, j ≤ z) :
    gapBefore (Finset.univ : Finset (Fin (n+1))) S j = Finset.Iio j := by
  ext y
  rw [mem_gapBefore, Finset.mem_Iio]
  constructor
  · rintro ⟨_, hy_lt, _⟩
    exact hy_lt
  · intro hy_lt
    refine ⟨Finset.mem_univ _, hy_lt, ?_⟩
    intro z hz_S hz_lt_j
    exact absurd hz_lt_j (not_lt_of_ge (h_min z hz_S))

/-- For S with min = j, the gap before j has cardinality `j.val`. -/
theorem gap_at_min_card (n : ℕ) (j : Fin (n+1))
    (S : Finset (Fin (n+1))) (hj_in : j ∈ S)
    (h_min : ∀ z ∈ S, j ≤ z) :
    (gapBefore (Finset.univ : Finset (Fin (n+1))) S j).card = j.val := by
  rw [gap_at_min_eq_Iio n j S hj_in h_min]
  exact Fin.card_Iio j

/-- For `x ∈ T` with `T ⊆ Ioi j`, the gap before x in `(Finset.univ,
insert j T)` equals the gap before x in `(Finset.Ioi j, T)`. -/
theorem gap_above_j_eq (n : ℕ) (j : Fin (n+1)) (T : Finset (Fin (n+1)))
    (hT_sub : T ⊆ Finset.Ioi j) (x : Fin (n+1)) (hx_T : x ∈ T) :
    gapBefore (Finset.univ : Finset (Fin (n+1))) (insert j T) x =
      gapBefore (Finset.Ioi j) T x := by
  ext y
  rw [mem_gapBefore, mem_gapBefore, Finset.mem_Ioi]
  constructor
  · rintro ⟨_, hy_lt, hy_all⟩
    have hx_gt_j : j < x := Finset.mem_Ioi.mp (hT_sub hx_T)
    have hy_gt_j : j < y := hy_all j (Finset.mem_insert_self _ _) hx_gt_j
    refine ⟨hy_gt_j, hy_lt, ?_⟩
    intro z hz_T hz_lt_x
    exact hy_all z (Finset.mem_insert_of_mem hz_T) hz_lt_x
  · rintro ⟨hy_gt_j, hy_lt, hy_all⟩
    refine ⟨Finset.mem_univ _, hy_lt, ?_⟩
    intro z hz_S hz_lt_x
    rw [Finset.mem_insert] at hz_S
    rcases hz_S with rfl | hz_T
    · exact hy_gt_j
    · exact hy_all z hz_T hz_lt_x

end NC

end Hamilton.Infrastructure
