/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.ParentMerge
import Hamilton.Infrastructure.ParentNoOverlap



namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}


theorem parent_merge_noncrossing (π : NC s)
    {B : Finset α} (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    IsNoncrossing (parentMergeFinpartition π B hne hB_mem h_nonRoot) := by
  intro B₁ hB₁ B₂ hB₂ i j k l hij hjk hkl hi hk hj hl
  have hπ_nc : IsNoncrossing π.val := π.property
  -- Abbreviations.
  set p := parentBlock π B hne
  have hp_mem : p ∈ π.val.parts := parentBlock_mem π B hne h_nonRoot
  have hp_ne_B : p ≠ B := parentBlock_ne_self π B hne h_nonRoot
  have hB_ne_p : B ≠ p := Ne.symm hp_ne_B
  -- Predecessor element of p.
  set pred := (s.filter (· < B.min' hne)).max'
    (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot)
  have hpred_in_p : pred ∈ p := parent_contains_pred π B hne h_nonRoot
  have hpred_lt_min : pred < B.min' hne :=
    (Finset.mem_filter.mp
      ((s.filter (· < B.min' hne)).max'_mem _)).2
  -- Min/max of B.
  have hmin_in_B : B.min' hne ∈ B := B.min'_mem hne
  have hmax_in_B : B.max' hne ∈ B := B.max'_mem hne
  have hmin_le_max : B.min' hne ≤ B.max' hne :=
    B.min'_le _ hmax_in_B
  -- Unfold σ.parts memberships.
  rw [parentMergeFinpartition_parts] at hB₁ hB₂
  rw [Finset.mem_insert] at hB₁
  rw [Finset.mem_insert] at hB₂
  rcases hB₁ with hB₁_M | hB₁_in
  · rcases hB₂ with hB₂_M | hB₂_in
    · -- (d) Both = M.
      rw [hB₁_M, hB₂_M]
    · -- (b) B₁ = M, B₂ = C in erased.
      rw [Finset.mem_erase] at hB₂_in
      obtain ⟨hC_ne_p, hB₂_erase'⟩ := hB₂_in
      rw [Finset.mem_erase] at hB₂_erase'
      obtain ⟨hC_ne_B, hC_mem⟩ := hB₂_erase'
      rw [hB₁_M] at hi hk
      rw [Finset.mem_union] at hi hk
      exfalso
      rcases hi with hi_B | hi_p
      · rcases hk with hk_B | hk_p
        · -- (b1) i, k ∈ B.
          have := hπ_nc hB_mem hC_mem hij hjk hkl hi_B hk_B hj hl
          exact hC_ne_B this.symm
        · -- (b3) i ∈ B, k ∈ p.
          have hi_ge_min : B.min' hne ≤ i := B.min'_le i hi_B
          have hpred_lt_j : pred < j :=
            lt_of_le_of_lt (le_of_lt hpred_lt_min) (lt_of_le_of_lt hi_ge_min hij)
          have := hπ_nc hp_mem hC_mem hpred_lt_j hjk hkl
            hpred_in_p hk_p hj hl
          exact hC_ne_p this.symm
      · rcases hk with hk_B | hk_p
        · -- (b4) i ∈ p, k ∈ B.
          have hi_lt_or := parent_elements_split π hB_mem hne h_nonRoot hi_p
          have hk_le_max : k ≤ B.max' hne := B.le_max' k hk_B
          have hi_lt_min : i < B.min' hne := by
            rcases hi_lt_or with h | h
            · exact h
            · exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h (le_of_lt hij))
                  (le_of_lt (lt_of_lt_of_le hjk hk_le_max))) (lt_irrefl _)
          by_cases hj_lt_min : j < B.min' hne
          · -- (b4a) j < min B.
            have hj_ne_pred : j ≠ pred := by
              intro heq
              have hdisj := π.val.disjoint hC_mem hp_mem hC_ne_p
              rw [heq] at hj
              exact (Finset.disjoint_left.mp hdisj hj) hpred_in_p
            have hj_le_pred : j ≤ pred := by
              -- j ∈ s.filter (· < min B); pred is max' of that.
              -- We need j ∈ s.  We have j ∈ C ⊆ s (since C ⊆ s).
              have hj_in_s : j ∈ s := (π.val.subset hC_mem) hj
              exact (s.filter (· < B.min' hne)).le_max' j
                (Finset.mem_filter.mpr ⟨hj_in_s, hj_lt_min⟩)
            have hj_lt_pred : j < pred := lt_of_le_of_ne hj_le_pred hj_ne_pred
            have hpred_lt_l : pred < l := by
              have hk_ge_min : B.min' hne ≤ k := B.min'_le k hk_B
              exact lt_of_lt_of_le (lt_of_lt_of_le hpred_lt_min
                (le_of_lt (lt_of_le_of_lt hk_ge_min hkl))) (le_refl l)
            have := hπ_nc hp_mem hC_mem hij hj_lt_pred hpred_lt_l
              hi_p hpred_in_p hj hl
            exact hC_ne_p this.symm
          · -- (b4b) j ≥ min B.
            push_neg at hj_lt_min
            have hj_ne_min : j ≠ B.min' hne := by
              intro heq
              have hdisj := π.val.disjoint hC_mem hB_mem hC_ne_B
              rw [heq] at hj
              exact (Finset.disjoint_left.mp hdisj hj) hmin_in_B
            have hmin_lt_j : B.min' hne < j :=
              lt_of_le_of_ne hj_lt_min (Ne.symm hj_ne_min)
            have := hπ_nc hB_mem hC_mem hmin_lt_j hjk hkl
              hmin_in_B hk_B hj hl
            exact hC_ne_B this.symm
        · -- (b2) i, k ∈ p.
          have := hπ_nc hp_mem hC_mem hij hjk hkl hi_p hk_p hj hl
          exact hC_ne_p this.symm
  · -- B₁ = C in erased.
    rw [Finset.mem_erase] at hB₁_in
    obtain ⟨hC_ne_p, hB₁_erase'⟩ := hB₁_in
    rw [Finset.mem_erase] at hB₁_erase'
    obtain ⟨hC_ne_B, hC_mem⟩ := hB₁_erase'
    rcases hB₂ with hB₂_M | hB₂_in
    · -- (c) B₁ = C, B₂ = M.
      rw [hB₂_M] at hj hl
      rw [Finset.mem_union] at hj hl
      exfalso
      rcases hj with hj_B | hj_p
      · rcases hl with hl_B | hl_p
        · -- (c1) j, l ∈ B.
          have := hπ_nc hC_mem hB_mem hij hjk hkl hi hk hj_B hl_B
          exact hC_ne_B this
        · -- (c3) j ∈ B, l ∈ p.
          have hj_ge_min : B.min' hne ≤ j := B.min'_le j hj_B
          have hl_lt_or := parent_elements_split π hB_mem hne h_nonRoot hl_p
          have hl_gt_max : B.max' hne < l := by
            rcases hl_lt_or with h | h
            · exfalso
              have hl_lt_min : l < B.min' hne := h
              exact absurd (lt_of_le_of_lt hj_ge_min
                (lt_of_lt_of_le hjk (le_of_lt hkl))) (asymm hl_lt_min)
            · exact h
          by_cases hk_lt_max : k < B.max' hne
          · -- (c3-a) k < max B.
            have := hπ_nc hC_mem hB_mem hij hjk hk_lt_max
              hi hk hj_B hmax_in_B
            exact hC_ne_B this
          · push_neg at hk_lt_max
            have hk_ne_max : k ≠ B.max' hne := by
              intro heq
              have hdisj := π.val.disjoint hC_mem hB_mem hC_ne_B
              rw [heq] at hk
              exact (Finset.disjoint_left.mp hdisj hk) hmax_in_B
            have hk_gt_max : B.max' hne < k :=
              lt_of_le_of_ne hk_lt_max (Ne.symm hk_ne_max)
            -- (c3-b) k > max B.
            by_cases hi_lt_pred : i < pred
            · -- (c3-b-1) i < pred.
              have hpred_lt_k : pred < k := by
                -- pred < min B ≤ max B < k.
                exact lt_of_lt_of_le hpred_lt_min (le_trans hmin_le_max
                  (le_of_lt hk_gt_max))
              have := hπ_nc hC_mem hp_mem hi_lt_pred hpred_lt_k hkl
                hi hk hpred_in_p hl_p
              exact hC_ne_p this
            · push_neg at hi_lt_pred
              have hi_ne_pred : i ≠ pred := by
                intro heq
                have hdisj := π.val.disjoint hC_mem hp_mem hC_ne_p
                rw [heq] at hi
                exact (Finset.disjoint_left.mp hdisj hi) hpred_in_p
              have hpred_lt_i : pred < i :=
                lt_of_le_of_ne hi_lt_pred (Ne.symm hi_ne_pred)
              -- pred < i.  Since pred is max' of {x ∈ s | x < min B},
              -- any x ∈ s with x < min B is ≤ pred.  Contrapositive:
              -- if x > pred then x ≥ min B (assuming x ∈ s).
              have hi_in_s : i ∈ s := (π.val.subset hC_mem) hi
              have hi_ge_min : B.min' hne ≤ i := by
                by_contra h
                push_neg at h
                have : i ≤ pred := (s.filter (· < B.min' hne)).le_max' i
                  (Finset.mem_filter.mpr ⟨hi_in_s, h⟩)
                exact absurd (lt_of_le_of_lt this hpred_lt_i) (lt_irrefl _)
              have hi_ne_min : i ≠ B.min' hne := by
                intro heq
                have hdisj := π.val.disjoint hC_mem hB_mem hC_ne_B
                rw [heq] at hi
                exact (Finset.disjoint_left.mp hdisj hi) hmin_in_B
              have hmin_lt_i : B.min' hne < i :=
                lt_of_le_of_ne hi_ge_min (Ne.symm hi_ne_min)
              have hi_le_max : i ≤ B.max' hne := by
                have hi_lt_j : i < j := hij
                exact le_of_lt (lt_of_lt_of_le hi_lt_j
                  (le_trans (B.le_max' j hj_B) (le_refl _)))
              have hi_ne_max : i ≠ B.max' hne := by
                intro heq
                have hdisj := π.val.disjoint hC_mem hB_mem hC_ne_B
                rw [heq] at hi
                exact (Finset.disjoint_left.mp hdisj hi) hmax_in_B
              have hi_lt_max : i < B.max' hne :=
                lt_of_le_of_ne hi_le_max hi_ne_max
              -- Use (min B, i, max B, k) on (B, C).
              have := hπ_nc hB_mem hC_mem
                hmin_lt_i hi_lt_max hk_gt_max
                hmin_in_B hmax_in_B hi hk
              exact hC_ne_B this.symm
      · rcases hl with hl_B | hl_p
        · -- (c4) j ∈ p, l ∈ B.
          have hj_lt_or := parent_elements_split π hB_mem hne h_nonRoot hj_p
          have hl_le_max : l ≤ B.max' hne := B.le_max' l hl_B
          have hj_lt_min : j < B.min' hne := by
            rcases hj_lt_or with h | h
            · exact h
            · -- j > max B.  But j < k < l ≤ max B.
              exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h (le_refl _))
                (le_trans (le_of_lt hjk) (le_trans (le_of_lt hkl) hl_le_max))) (lt_irrefl _)
          by_cases hk_lt_min : k < B.min' hne
          · -- (c4-a) k < min B.
            by_cases hk_lt_pred : k < pred
            · have hk_lt_pred_lift : k < pred := hk_lt_pred
              have hpred_lt_l : pred < l := by
                have hl_ge_min : B.min' hne ≤ l := B.min'_le l hl_B
                exact lt_of_lt_of_le hpred_lt_min hl_ge_min
              have := hπ_nc hC_mem hp_mem hij hjk hk_lt_pred
                hi hk hj_p hpred_in_p
              exact hC_ne_p this
            · push_neg at hk_lt_pred
              have hk_ne_pred : k ≠ pred := by
                intro heq
                have hdisj := π.val.disjoint hC_mem hp_mem hC_ne_p
                rw [heq] at hk
                exact (Finset.disjoint_left.mp hdisj hk) hpred_in_p
              have hk_gt_pred : pred < k :=
                lt_of_le_of_ne hk_lt_pred (Ne.symm hk_ne_pred)
              -- pred < k < min B.  Then k ≥ min B by max' property.
              -- But hk_lt_min : k < min B.  Contradiction.
              have hk_in_s : k ∈ s := (π.val.subset hC_mem) hk
              have : k ≤ pred := (s.filter (· < B.min' hne)).le_max' k
                (Finset.mem_filter.mpr ⟨hk_in_s, hk_lt_min⟩)
              exact absurd (lt_of_le_of_lt this hk_gt_pred) (lt_irrefl _)
          · push_neg at hk_lt_min
            have hk_ne_min : k ≠ B.min' hne := by
              intro heq
              have hdisj := π.val.disjoint hC_mem hB_mem hC_ne_B
              rw [heq] at hk
              exact (Finset.disjoint_left.mp hdisj hk) hmin_in_B
            have hk_gt_min : B.min' hne < k :=
              lt_of_le_of_ne hk_lt_min (Ne.symm hk_ne_min)
            have hk_lt_max : k < B.max' hne := by
              have hk_le_max' : k ≤ B.max' hne := le_trans (le_of_lt hkl) hl_le_max
              have hk_ne_max : k ≠ B.max' hne := by
                intro heq
                have hdisj := π.val.disjoint hC_mem hB_mem hC_ne_B
                rw [heq] at hk
                exact (Finset.disjoint_left.mp hdisj hk) hmax_in_B
              exact lt_of_le_of_ne hk_le_max' hk_ne_max
            by_cases hi_lt_pred : i < pred
            · -- Use (i, min B, k, l) on (C, B).
              have hi_lt_min : i < B.min' hne :=
                lt_trans hi_lt_pred hpred_lt_min
              have := hπ_nc hC_mem hB_mem hi_lt_min hk_gt_min hkl
                hi hk hmin_in_B hl_B
              exact hC_ne_B this
            · push_neg at hi_lt_pred
              have hi_ne_pred : i ≠ pred := by
                intro heq
                have hdisj := π.val.disjoint hC_mem hp_mem hC_ne_p
                rw [heq] at hi
                exact (Finset.disjoint_left.mp hdisj hi) hpred_in_p
              have hpred_lt_i : pred < i :=
                lt_of_le_of_ne hi_lt_pred (Ne.symm hi_ne_pred)
              have hi_in_s : i ∈ s := (π.val.subset hC_mem) hi
              have hi_ge_min : B.min' hne ≤ i := by
                by_contra h
                push_neg at h
                have : i ≤ pred := (s.filter (· < B.min' hne)).le_max' i
                  (Finset.mem_filter.mpr ⟨hi_in_s, h⟩)
                exact absurd (lt_of_le_of_lt this hpred_lt_i) (lt_irrefl _)
              -- i ≥ min B and i < j ∈ p with j < min B.
              -- Contradiction: i < j < min B ≤ i, impossible.
              exact absurd (lt_of_le_of_lt hi_ge_min (lt_of_lt_of_le hij
                (le_of_lt hj_lt_min))) (lt_irrefl _)
        · -- (c2) j, l ∈ p.
          have := hπ_nc hC_mem hp_mem hij hjk hkl hi hk hj_p hl_p
          exact hC_ne_p this
    · -- (a) Both in erased.
      rw [Finset.mem_erase] at hB₂_in
      obtain ⟨_, hB₂_erase'⟩ := hB₂_in
      rw [Finset.mem_erase] at hB₂_erase'
      obtain ⟨_, hB₂_mem⟩ := hB₂_erase'
      exact hπ_nc hC_mem hB₂_mem hij hjk hkl hi hk hj hl

end NC

end Hamilton.Infrastructure
