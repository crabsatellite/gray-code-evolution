/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.ReconstructNoncrossing
import Hamilton.Infrastructure.FiberDecomposition

/-!
# Reconstruction's `blockOfLast` equals `S`

When `s.max' hs ∈ S`, the `blockOfLast` of the reconstructed NC is
exactly `S`.

This completes the surjective inverse: given `S ⊆ s` with `s.max' ∈ S`
and a noncrossing family `Ps x` for `x ∈ S`, the reconstruction
lands in `fiberOf hs S`.

## Main results

* `NC.reconstructNC` — package the reconstructed Finpartition + its
  noncrossing proof into an `NC s`.
* `NC.reconstructNC_blockOfLast` — `blockOfLast (reconstructNC) hs = S`.

## Tags

NC, reconstruction, blockOfLast, Kreweras-Simion
-/

namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore mem_gapBefore gapBefore_subset_self
  gapBefore_disjoint_S gapBefore_disjoint
  sup_gapBefore_eq_sdiff gapBefore_supIndep)

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- Helper: `hcover` is automatic when `s.max' hs ∈ S`. -/
theorem reconstruct_hcover (hs : s.Nonempty) (S : Finset α)
    (hmax : s.max' hs ∈ S) :
    ∀ y ∈ s, y ∉ S → ∃ z ∈ S, y < z := fun y hy_s hy_notS =>
  ⟨s.max' hs, hmax, lt_of_le_of_ne (s.le_max' y hy_s)
    (fun h => hy_notS (h ▸ hmax))⟩

/-- The **NC reconstruction**: given `S ⊆ s` nonempty with `s.max' hs
∈ S` and a noncrossing family `Ps x : NC (gapBefore s S x)` for `x
∈ S`, produce an `NC s`. -/
noncomputable def reconstructNC (hs : s.Nonempty) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s)
    (hmax : s.max' hs ∈ S)
    (Ps : ∀ x : α, NC (gapBefore s S x)) : NC s :=
  ⟨Finpartition.reconstructFromGaps s S hS_ne hS_sub
     (reconstruct_hcover hs S hmax) (fun x => (Ps x).val),
   Finpartition.reconstructFromGaps_isNoncrossing s S hS_ne hS_sub
     (reconstruct_hcover hs S hmax) (fun x => (Ps x).val)
     (fun x _ => (Ps x).property)⟩

/-- **`S` is a part of the reconstruction**. -/
theorem reconstructNC_parts_mem_S (hs : s.Nonempty) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s)
    (hmax : s.max' hs ∈ S)
    (Ps : ∀ x : α, NC (gapBefore s S x)) :
    S ∈ (reconstructNC hs S hS_ne hS_sub hmax Ps).val.parts := by
  show S ∈ (Finpartition.reconstructFromGaps s S hS_ne hS_sub
              (reconstruct_hcover hs S hmax) _).parts
  rw [Finpartition.reconstructFromGaps_parts]
  exact Finset.mem_insert_self _ _

/-- **`blockOfLast` of reconstruction = `S`**. -/
theorem reconstructNC_blockOfLast (hs : s.Nonempty) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s)
    (hmax : s.max' hs ∈ S)
    (Ps : ∀ x : α, NC (gapBefore s S x)) :
    blockOfLast (reconstructNC hs S hS_ne hS_sub hmax Ps) hs = S := by
  show (reconstructNC hs S hS_ne hS_sub hmax Ps).val.part (s.max' hs) = S
  exact (reconstructNC hs S hS_ne hS_sub hmax Ps).val.part_eq_of_mem
    (reconstructNC_parts_mem_S hs S hS_ne hS_sub hmax Ps) hmax

end NC

end Hamilton.Infrastructure
