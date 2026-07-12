/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.GapIntervals
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Order.SupIndep

/-!
# Sup of gap intervals = `s \ S`

When `S ⊆ s` is such that every `y ∈ s \ S` has some `S`-element
above it, the sup (= biUnion) of all gap intervals `gapBefore s S x`
over `x ∈ S` equals `s \ S`.

This is the cover-side of the gap decomposition.

## Main results

* `Finset.sup_gapBefore_eq_sdiff` — `S.sup (gapBefore s S) = s \ S`
  (under `max(s) ∈ S` hypothesis or equivalent).
* `Finset.gapBefore_supIndep` — pairwise gap disjointness lifted to
  `SupIndep`.

## Tags

gap interval, sup, supIndep, fiber decomposition
-/

namespace Hamilton.Infrastructure

namespace Finset

open _root_.Finset

variable {α : Type*} [LinearOrder α]

/-- **Sup-cover**: the supremum (= biUnion) of gap intervals equals
`s \ S`, when every element of `s \ S` has some `S`-element above. -/
theorem sup_gapBefore_eq_sdiff (s S : _root_.Finset α)
    (hcover : ∀ y ∈ s, y ∉ S → ∃ z ∈ S, y < z) :
    S.sup (fun x => gapBefore s S x) = s \ S := by
  rw [_root_.Finset.sup_eq_biUnion]
  ext y
  rw [_root_.Finset.mem_biUnion, _root_.Finset.mem_sdiff]
  constructor
  · rintro ⟨x, hx_S, hy_gap⟩
    have hy_data := (mem_gapBefore s S x y).mp hy_gap
    obtain ⟨hy_s, _, _⟩ := hy_data
    refine ⟨hy_s, ?_⟩
    intro hy_S
    have hdisj := gapBefore_disjoint_S s S x
    exact (_root_.Finset.disjoint_left.mp hdisj hy_gap) hy_S
  · intro ⟨hy_s, hy_notS⟩
    obtain ⟨z, hz_S, hy_lt_z⟩ := hcover y hy_s hy_notS
    obtain ⟨x, hx_S, hy_gap⟩ :=
      exists_gap_of_mem_sdiff s S y hy_s hy_notS ⟨z, hz_S, hy_lt_z⟩
    exact ⟨x, hx_S, hy_gap⟩

/-- **SupIndep** for the gap family: pairwise disjointness lifted. -/
theorem gapBefore_supIndep (s S : _root_.Finset α) :
    _root_.Finset.SupIndep S (fun x => gapBefore s S x) := by
  rw [_root_.Finset.supIndep_iff_pairwiseDisjoint]
  intro x₁ hx₁ x₂ hx₂ hne
  rw [_root_.Finset.mem_coe] at hx₁ hx₂
  exact gapBefore_disjoint s S hx₁ hx₂ hne

end Finset

end Hamilton.Infrastructure
