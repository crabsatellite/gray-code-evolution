/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCType
import Mathlib.Algebra.BigOperators.Group.Finset.Basic



namespace Hamilton.Infrastructure

namespace NC

/-- Every `S` in the K-S filter is nonempty. -/
theorem min_of_KS_filter_nonempty (n : ℕ)
    {S : Finset (Fin (n+1))}
    (hS_mem : S ∈ (Finset.univ : Finset (Fin (n+1))).powerset.filter
      (fun S => S.Nonempty ∧ Fin.last n ∈ S)) :
    S.Nonempty := by
  rw [Finset.mem_filter] at hS_mem
  exact hS_mem.2.1

/-- Every `S` in the K-S filter contains `Fin.last n`. -/
theorem max_in_KS_filter (n : ℕ)
    {S : Finset (Fin (n+1))}
    (hS_mem : S ∈ (Finset.univ : Finset (Fin (n+1))).powerset.filter
      (fun S => S.Nonempty ∧ Fin.last n ∈ S)) :
    Fin.last n ∈ S := by
  rw [Finset.mem_filter] at hS_mem
  exact hS_mem.2.2

/-- For S in the K-S filter, `S.min'` is at most `Fin.last n`. -/
theorem KS_filter_min_le_last (n : ℕ)
    {S : Finset (Fin (n+1))}
    (hS_mem : S ∈ (Finset.univ : Finset (Fin (n+1))).powerset.filter
      (fun S => S.Nonempty ∧ Fin.last n ∈ S))
    (hne : S.Nonempty) :
    S.min' hne ≤ Fin.last n :=
  S.min'_le _ (max_in_KS_filter n hS_mem)

/-- Total "min" function: `S.min.getD 0` defaults to `0` for empty `S`. -/
noncomputable def minOrZero (n : ℕ) (S : Finset (Fin (n+1))) : Fin (n+1) :=
  S.min.getD 0

/-- For nonempty `S`, `minOrZero S = S.min' h`. -/
theorem minOrZero_eq_min' (n : ℕ) {S : Finset (Fin (n+1))} (h : S.Nonempty) :
    minOrZero n S = S.min' h := by
  unfold minOrZero
  have h_min : S.min = (S.min' h : WithTop (Fin (n+1))) := (Finset.coe_min' h).symm
  rw [h_min]
  rfl

/-- **K-S sum partition by minOrZero**: partition the K-S filter sum
by the `minOrZero` of S (which equals `S.min'` for S in the filter). -/
theorem KS_sum_by_minOrZero (n : ℕ) (f : Finset (Fin (n+1)) → ℕ) :
    ∑ S ∈ (Finset.univ : Finset (Fin (n+1))).powerset.filter
      (fun S => S.Nonempty ∧ Fin.last n ∈ S),
      f S =
    ∑ j : Fin (n+1),
      ∑ S ∈ ((Finset.univ : Finset (Fin (n+1))).powerset.filter
        (fun S => S.Nonempty ∧ Fin.last n ∈ S)) with minOrZero n S = j,
        f S :=
  (Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin (n+1))).powerset.filter
      (fun S => S.Nonempty ∧ Fin.last n ∈ S))
    (t := (Finset.univ : Finset (Fin (n+1))))
    (g := minOrZero n)
    (fun S _ => Finset.mem_univ _) f).symm

/-- **At j = Fin.last n, the K-S fiber is the singleton `{S = {Fin.last n}}`**. -/
theorem KS_fiber_at_max (n : ℕ) (S : Finset (Fin (n+1)))
    (hS_mem : S ∈ (Finset.univ : Finset (Fin (n+1))).powerset.filter
      (fun S => S.Nonempty ∧ Fin.last n ∈ S))
    (h_min : minOrZero n S = Fin.last n) :
    S = {Fin.last n} := by
  have hS_ne : S.Nonempty := min_of_KS_filter_nonempty n hS_mem
  have hmax_in : Fin.last n ∈ S := max_in_KS_filter n hS_mem
  have h_min' : S.min' hS_ne = Fin.last n := by
    rw [← minOrZero_eq_min' n hS_ne]; exact h_min
  -- S contains Fin.last n; min(S) = Fin.last n means everything is ≥ Fin.last n.
  -- But Fin.last n is max of Fin (n+1).  So S = {Fin.last n}.
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hmax_in, ?_⟩
  intro x hx_S
  have hx_ge : S.min' hS_ne ≤ x := S.min'_le _ hx_S
  rw [h_min'] at hx_ge
  exact le_antisymm (Fin.le_last x) hx_ge

end NC

end Hamilton.Infrastructure
