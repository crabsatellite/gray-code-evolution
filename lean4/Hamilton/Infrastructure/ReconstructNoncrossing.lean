/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.Reconstruct
import Hamilton.Infrastructure.NoncrossingPartition

/-!
# Reconstruction preserves noncrossing

If `Ps x` are all noncrossing (over `x ∈ S`), then
`reconstructFromGaps s S ... Ps` is noncrossing.

## Proof structure

Given a quadruple `i < j < k < l` with `i, k ∈ B₁` and `j, l ∈ B₂`,
each of `B₁`, `B₂` is either `S` or contained in some
`gapBefore s S x`.  Case analysis:

* **Both `= S`**: trivially `B₁ = B₂`.
* **`B₁ = S`, `B₂ ⊆ gap x`** (or symmetric):  We have `i, k ∈ S`,
  `j, l < x`, and `i < j` & `k < l` & `i < k`.  By the gap condition
  on `j`: `∀ z ∈ S, z < x → z < j`.  If `k < x`, then `k < j`,
  contradicting `j < k`.  If `k ≥ x`, then `l < x ≤ k`, contradicting
  `k < l`.  So no valid quadruple.
* **`B₁ ⊆ gap x₁`, `B₂ ⊆ gap x₂`**:
  * Same gap (`x₁ = x₂`): `Ps x₁` is noncrossing, gives `B₁ = B₂`.
  * Different gaps: WLOG `x₁ < x₂`.  Then `B₁ < x₁ < B₂`, so
    `k < x₁ < j`, contradicting `j < k`.

## Tags

noncrossing partition, reconstruction, Kreweras-Simion, gap interval
-/

namespace Hamilton.Infrastructure

namespace Finpartition

open Finset (gapBefore mem_gapBefore gapBefore_subset_self
  gapBefore_disjoint_S gapBefore_disjoint
  sup_gapBefore_eq_sdiff gapBefore_supIndep)

variable {α : Type*} [LinearOrder α]

/-- **Classification of reconstructed parts**: every part is either
`S` itself or a block of some gap-NC `Ps x`. -/
theorem reconstructFromGaps_part_classify (s S : _root_.Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s)
    (hcover : ∀ y ∈ s, y ∉ S → ∃ z ∈ S, y < z)
    (Ps : ∀ x : α, _root_.Finpartition (gapBefore s S x))
    {B : _root_.Finset α}
    (hB : B ∈ (reconstructFromGaps s S hS_ne hS_sub hcover Ps).parts) :
    B = S ∨ ∃ x ∈ S, B ∈ (Ps x).parts := by
  rw [reconstructFromGaps_parts] at hB
  rw [_root_.Finset.mem_insert] at hB
  rcases hB with h_eq | h_biUnion
  · left; exact h_eq
  · right
    rw [_root_.Finset.mem_biUnion] at h_biUnion
    obtain ⟨x, hx_S, hB_Px⟩ := h_biUnion
    exact ⟨x, hx_S, hB_Px⟩

/-- **In-gap block satisfies gap properties**: `B ∈ (Ps x).parts` with
`Ps x` a Finpartition of `gapBefore s S x` ⇒ `B ⊆ gapBefore s S x`. -/
theorem in_gap_part_subset_gap (s S : _root_.Finset α)
    (Ps : ∀ x : α, _root_.Finpartition (gapBefore s S x))
    {x : α} {B : _root_.Finset α} (hB : B ∈ (Ps x).parts) :
    B ⊆ gapBefore s S x :=
  (Ps x).le hB

/-- **Reconstruction is noncrossing**: if each `Ps x` (for `x ∈ S`)
is noncrossing, then `reconstructFromGaps` is noncrossing. -/
theorem reconstructFromGaps_isNoncrossing (s S : _root_.Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s)
    (hcover : ∀ y ∈ s, y ∉ S → ∃ z ∈ S, y < z)
    (Ps : ∀ x : α, _root_.Finpartition (gapBefore s S x))
    (hPs_nc : ∀ x ∈ S, IsNoncrossing (Ps x)) :
    IsNoncrossing (reconstructFromGaps s S hS_ne hS_sub hcover Ps) := by
  intro B₁ hB₁ B₂ hB₂ i j k l hij hjk hkl hi_B₁ hk_B₁ hj_B₂ hl_B₂
  have hcl₁ := reconstructFromGaps_part_classify s S hS_ne hS_sub hcover Ps hB₁
  have hcl₂ := reconstructFromGaps_part_classify s S hS_ne hS_sub hcover Ps hB₂
  rcases hcl₁ with hB₁_eq_S | ⟨x₁, hx₁_S, hB₁_in⟩
  · -- B₁ = S case.
    rcases hcl₂ with hB₂_eq_S | ⟨x₂, hx₂_S, hB₂_in⟩
    · rw [hB₁_eq_S, hB₂_eq_S]  -- Both S, equal.
    · -- B₁ = S, B₂ ⊆ gap x₂.  Show contradiction.
      exfalso
      have hB₂_sub : B₂ ⊆ gapBefore s S x₂ := in_gap_part_subset_gap s S Ps hB₂_in
      have hj_gap : j ∈ gapBefore s S x₂ := hB₂_sub hj_B₂
      have hl_gap : l ∈ gapBefore s S x₂ := hB₂_sub hl_B₂
      rw [mem_gapBefore] at hj_gap hl_gap
      obtain ⟨_, hj_lt_x₂, hj_above⟩ := hj_gap
      obtain ⟨_, hl_lt_x₂, _⟩ := hl_gap
      have hi_S : i ∈ S := hB₁_eq_S ▸ hi_B₁
      have hk_S : k ∈ S := hB₁_eq_S ▸ hk_B₁
      -- Case split on k vs x₂.
      by_cases hk_lt_x₂ : k < x₂
      · -- k < x₂, so k < j (by gap j condition with z = k).
        have hk_lt_j : k < j := hj_above k hk_S hk_lt_x₂
        exact absurd hk_lt_j (not_lt_of_gt hjk)
      · -- k ≥ x₂.  Then l < x₂ ≤ k, contradicting k < l.
        push_neg at hk_lt_x₂
        exact absurd hl_lt_x₂ (not_lt_of_ge (le_trans hk_lt_x₂ (le_of_lt hkl)))
  · -- B₁ ⊆ gap x₁.
    have hB₁_sub : B₁ ⊆ gapBefore s S x₁ := in_gap_part_subset_gap s S Ps hB₁_in
    rcases hcl₂ with hB₂_eq_S | ⟨x₂, hx₂_S, hB₂_in⟩
    · -- B₁ ⊆ gap x₁, B₂ = S.
      exfalso
      have hi_gap : i ∈ gapBefore s S x₁ := hB₁_sub hi_B₁
      have hk_gap : k ∈ gapBefore s S x₁ := hB₁_sub hk_B₁
      rw [mem_gapBefore] at hi_gap hk_gap
      obtain ⟨_, hi_lt_x₁, hi_above⟩ := hi_gap
      obtain ⟨_, hk_lt_x₁, _⟩ := hk_gap
      have hj_S : j ∈ S := hB₂_eq_S ▸ hj_B₂
      have hl_S : l ∈ S := hB₂_eq_S ▸ hl_B₂
      -- Case on j vs x₁.
      by_cases hj_lt_x₁ : j < x₁
      · -- j ∈ S, j < x₁, so by gap_i condition: j < i.  Contradicts i < j.
        have hj_lt_i : j < i := hi_above j hj_S hj_lt_x₁
        exact absurd hj_lt_i (not_lt_of_gt hij)
      · -- j ≥ x₁.  But k < x₁ ≤ j, so k < j, contradicting j < k.
        push_neg at hj_lt_x₁
        have hk_lt_j : k < j := lt_of_lt_of_le hk_lt_x₁ hj_lt_x₁
        exact lt_irrefl _ (lt_trans hjk hk_lt_j)
    · -- Both blocks in gaps.
      have hB₂_sub : B₂ ⊆ gapBefore s S x₂ := in_gap_part_subset_gap s S Ps hB₂_in
      by_cases hx_eq : x₁ = x₂
      · -- Same gap: use noncrossing of Ps x₁.
        subst hx_eq
        -- Ps x₁ is noncrossing on its parts (gapBefore s S x₁).
        have h_nc := hPs_nc x₁ hx₁_S
        exact h_nc hB₁_in hB₂_in hij hjk hkl hi_B₁ hk_B₁ hj_B₂ hl_B₂
      · -- Different gaps.  WLOG x₁ < x₂ or x₂ < x₁; both give contradictions.
        exfalso
        rcases lt_or_gt_of_ne hx_eq with h_lt | h_gt
        · -- x₁ < x₂.  Then B₁ < x₁ < B₂.  k ∈ B₁ < x₁ < B₂ ∋ j.
          -- So k < x₁ and x₁ < j (j ∈ gap x₂ with x₁ ∈ S, x₁ < x₂ ⇒ x₁ < j).
          have hk_gap : k ∈ gapBefore s S x₁ := hB₁_sub hk_B₁
          rw [mem_gapBefore] at hk_gap
          obtain ⟨_, hk_lt_x₁, _⟩ := hk_gap
          have hj_gap : j ∈ gapBefore s S x₂ := hB₂_sub hj_B₂
          rw [mem_gapBefore] at hj_gap
          obtain ⟨_, _, hj_above⟩ := hj_gap
          have hx₁_lt_j : x₁ < j := hj_above x₁ hx₁_S h_lt
          -- So j > x₁ > k, contradicting j < k.
          exact absurd hjk (not_lt_of_gt (lt_trans hk_lt_x₁ hx₁_lt_j))
        · -- x₂ < x₁.  Symmetric: B₂ < x₂ < B₁, so l < x₂ < i, contradicting i < l.
          have hl_gap : l ∈ gapBefore s S x₂ := hB₂_sub hl_B₂
          rw [mem_gapBefore] at hl_gap
          obtain ⟨_, hl_lt_x₂, _⟩ := hl_gap
          have hi_gap : i ∈ gapBefore s S x₁ := hB₁_sub hi_B₁
          rw [mem_gapBefore] at hi_gap
          obtain ⟨_, _, hi_above⟩ := hi_gap
          have hx₂_lt_i : x₂ < i := hi_above x₂ hx₂_S h_gt
          -- So i > x₂ > l. But i < j < k < l, so i < l, contradicting i > l.
          have hi_lt_l : i < l := lt_trans hij (lt_trans hjk hkl)
          exact absurd hi_lt_l (not_lt_of_gt (lt_trans hl_lt_x₂ hx₂_lt_i))

end Finpartition

end Hamilton.Infrastructure
