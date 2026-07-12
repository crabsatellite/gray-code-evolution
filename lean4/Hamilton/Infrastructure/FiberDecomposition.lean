/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.Roots
import Mathlib.Data.Finset.Sort



namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The block of `π` containing the maximum element of `s`. -/
noncomputable def blockOfLast (π : NC s) (hs : s.Nonempty) :
    Finset α :=
  π.val.part (s.max' hs)

theorem blockOfLast_mem (π : NC s) (hs : s.Nonempty) :
    blockOfLast π hs ∈ π.val.parts :=
  π.val.part_mem.mpr (s.max'_mem hs)

theorem blockOfLast_contains_max (π : NC s) (hs : s.Nonempty) :
    s.max' hs ∈ blockOfLast π hs :=
  π.val.mem_part_self.mpr (s.max'_mem hs)

theorem blockOfLast_nonempty (π : NC s) (hs : s.Nonempty) :
    (blockOfLast π hs).Nonempty :=
  ⟨_, blockOfLast_contains_max π hs⟩

/-- The max of `blockOfLast π hs` equals `s.max'`. -/
theorem blockOfLast_max_eq (π : NC s) (hs : s.Nonempty) :
    (blockOfLast π hs).max' (blockOfLast_nonempty π hs) = s.max' hs := by
  apply le_antisymm
  · -- max' (blockOfLast) ≤ max' s.  blockOfLast ⊆ s.
    apply (blockOfLast π hs).max'_le
    intro a ha
    exact s.le_max' a ((π.val.subset (blockOfLast_mem π hs)) ha)
  · -- s.max' ≤ max' (blockOfLast).
    exact (blockOfLast π hs).le_max' _ (blockOfLast_contains_max π hs)

/-- Any block `B ≠ blockOfLast π hs` has `max' B < s.max'`.

Reason: if `max' B = s.max'`, then `s.max' ∈ B` (since max' is in B),
but `s.max' ∈ blockOfLast π hs`; by partition disjointness, `B =
blockOfLast π hs`, contradiction. -/
theorem nonLast_max_lt (π : NC s) (hs : s.Nonempty)
    {B : Finset α} (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (hB_ne : B ≠ blockOfLast π hs) :
    B.max' hne < s.max' hs := by
  have hmax_B_in_s : B.max' hne ∈ s :=
    (π.val.subset hB_mem) (B.max'_mem hne)
  have hmax_B_le : B.max' hne ≤ s.max' hs := s.le_max' _ hmax_B_in_s
  by_contra hcon
  push_neg at hcon
  have hmax_eq : B.max' hne = s.max' hs := le_antisymm hmax_B_le hcon
  have hmax_s_in_B : s.max' hs ∈ B := hmax_eq ▸ B.max'_mem hne
  have hmax_s_in_L : s.max' hs ∈ blockOfLast π hs :=
    blockOfLast_contains_max π hs
  have hdisj := π.val.disjoint hB_mem (blockOfLast_mem π hs) hB_ne
  exact (Finset.disjoint_left.mp hdisj hmax_s_in_B) hmax_s_in_L

end NC

end Hamilton.Infrastructure
