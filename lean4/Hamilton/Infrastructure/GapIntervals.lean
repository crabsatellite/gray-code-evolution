/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Max



namespace Hamilton.Infrastructure

namespace Finset

open Finset

variable {α : Type*} [LinearOrder α]

/-- The **gap before `x` in `s` w.r.t. `S`**: the elements of `s`
strictly less than `x` and strictly greater than all `S`-elements
less than `x`.

When `x ∈ S` has a predecessor `p` in `S`, this is the open
`s`-interval `(p, x) ∩ s`.  When `x` has no `S`-predecessor (e.g.
`x = min S`), this is `{y ∈ s : y < x}`. -/
def gapBefore (s S : _root_.Finset α) (x : α) : _root_.Finset α :=
  s.filter (fun y => y < x ∧ ∀ z ∈ S, z < x → z < y)

@[simp]
theorem mem_gapBefore (s S : _root_.Finset α) (x y : α) :
    y ∈ gapBefore s S x ↔
      y ∈ s ∧ y < x ∧ ∀ z ∈ S, z < x → z < y := by
  unfold gapBefore
  simp [_root_.Finset.mem_filter]

theorem gapBefore_subset_self (s S : _root_.Finset α) (x : α) :
    gapBefore s S x ⊆ s := by
  intro y hy
  rw [mem_gapBefore] at hy
  exact hy.1

/-- Gaps are disjoint from `S` (for nonempty gaps, more precisely:
no element of a gap is in `S`). -/
theorem gapBefore_disjoint_S (s S : _root_.Finset α) (x : α) :
    Disjoint (gapBefore s S x) S := by
  rw [_root_.Finset.disjoint_left]
  intro y hy hyS
  rw [mem_gapBefore] at hy
  obtain ⟨_, hy_lt_x, hy_all⟩ := hy
  have : y < y := hy_all y hyS hy_lt_x
  exact absurd this (lt_irrefl y)

/-- The gap before `x` is contained in the open `(-∞, x)` interval. -/
theorem gapBefore_lt (s S : _root_.Finset α) (x y : α)
    (hy : y ∈ gapBefore s S x) : y < x := by
  rw [mem_gapBefore] at hy
  exact hy.2.1

/-- Gaps before *distinct* `S`-elements are disjoint.

If `x₁ < x₂` (both in `S`), then `gapBefore s S x₁` and
`gapBefore s S x₂` are disjoint: an element of the latter must be
≥ `x₁` (since `x₁ ∈ S` and `x₁ < x₂`, the "all S-elements < x₂ are
< y" condition forces `x₁ < y`, in particular `y > x₁`), but an
element of the former is `< x₁`. -/
theorem gapBefore_disjoint (s S : _root_.Finset α) {x₁ x₂ : α}
    (hx₁ : x₁ ∈ S) (hx₂ : x₂ ∈ S) (hne : x₁ ≠ x₂) :
    Disjoint (gapBefore s S x₁) (gapBefore s S x₂) := by
  -- WLOG x₁ < x₂.
  wlog h_lt : x₁ < x₂ with H
  · push_neg at h_lt
    have h_lt' : x₂ < x₁ := lt_of_le_of_ne h_lt (Ne.symm hne)
    exact (H s S hx₂ hx₁ hne.symm h_lt').symm
  rw [_root_.Finset.disjoint_left]
  intro y hy₁ hy₂
  rw [mem_gapBefore] at hy₁ hy₂
  obtain ⟨_, hy_lt_x₁, _⟩ := hy₁
  obtain ⟨_, _, hy_above⟩ := hy₂
  -- y > x₁ (from x₁ ∈ S, x₁ < x₂, "all S-elem < x₂ are < y")
  have hx₁_lt_y : x₁ < y := hy_above x₁ hx₁ h_lt
  exact absurd hy_lt_x₁ (not_lt_of_gt hx₁_lt_y)

/-- **Gap-covering**: for `S ⊆ s` such that every `y ∈ s \ S` has
some `S`-element above it, the gaps cover `s \ S`.

This is one direction of the union characterization `⋃_{x ∈ S}
gapBefore s S x = s \ S`. -/
theorem exists_gap_of_mem_sdiff (s S : _root_.Finset α)
    (y : α) (hy_s : y ∈ s) (hy_notS : y ∉ S)
    (hmax : ∃ z ∈ S, y < z) :
    ∃ x ∈ S, y ∈ gapBefore s S x := by
  -- Let `above = S.filter (y < ·)`; nonempty by hmax.
  set above := S.filter (y < ·) with above_def
  have habove_ne : above.Nonempty := by
    obtain ⟨z, hz_S, hy_lt_z⟩ := hmax
    exact ⟨z, _root_.Finset.mem_filter.mpr ⟨hz_S, hy_lt_z⟩⟩
  -- Take `x = min'` of `above`.
  set x := above.min' habove_ne with x_def
  have hx_mem : x ∈ above := above.min'_mem habove_ne
  rw [above_def, _root_.Finset.mem_filter] at hx_mem
  obtain ⟨hx_S, hy_lt_x⟩ := hx_mem
  refine ⟨x, hx_S, ?_⟩
  rw [mem_gapBefore]
  refine ⟨hy_s, hy_lt_x, ?_⟩
  intro z hz_S hz_lt_x
  -- z ∈ S and z < x.  We want z < y.
  -- If y < z, then z ∈ above, so z ≥ x = min' above, contradicting z < x.
  -- So z ≤ y.  And z ≠ y (since y ∉ S, z ∈ S).
  by_contra h_ge
  push_neg at h_ge
  -- h_ge : y ≤ z.
  have h_lt_or_eq : y < z ∨ y = z := lt_or_eq_of_le h_ge
  rcases h_lt_or_eq with h_lt | h_eq
  · -- y < z, so z ∈ above, so x ≤ z, contradicting hz_lt_x.
    have hz_in_above : z ∈ above := by
      rw [above_def, _root_.Finset.mem_filter]
      exact ⟨hz_S, h_lt⟩
    have hx_le_z : x ≤ z := above.min'_le z hz_in_above
    exact absurd hz_lt_x (not_lt_of_ge hx_le_z)
  · -- y = z, but y ∉ S and z ∈ S — contradiction.
    rw [← h_eq] at hz_S
    exact hy_notS hz_S

end Finset

end Hamilton.Infrastructure
