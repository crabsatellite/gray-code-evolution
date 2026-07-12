/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.GapSupCover
import Mathlib.Order.Partition.Finpartition

/-!
# Reconstruction: assemble a Finpartition from gap-NCs

Given `S ⊆ s` nonempty (with each `y ∈ s \ S` having an `S`-element
above) and a family of Finpartitions `(NCs x : Finpartition (gapBefore
s S x))` for `x ∈ S`, this file constructs:

  `reconstructFinpartition` — a `Finpartition s` whose parts are
  `{S} ∪ ⋃_x (NCs x).parts`.

Noncrossing-ness and `blockOfLast = S` will be handled in later
rounds.

## Main definitions

* `Finpartition.combineGaps` — combine the gap Finpartitions via
  `Finpartition.combine`, getting a `Finpartition (S.sup (gapBefore
  s S))`.
* `Finpartition.reconstructFromGaps` — extend `combineGaps` to add
  `S` as a block, getting a `Finpartition s`.

## Tags

Finpartition, reconstruction, gap interval, fiber decomposition
-/

namespace Hamilton.Infrastructure

namespace Finpartition

open Finset (gapBefore mem_gapBefore gapBefore_subset_self
  gapBefore_disjoint_S gapBefore_disjoint
  sup_gapBefore_eq_sdiff gapBefore_supIndep)

variable {α : Type*} [LinearOrder α]

/-- **Combine gap Finpartitions**: given a family of Finpartitions
of each gap interval, combine them into a Finpartition of
`S.sup (gapBefore s S)`.

By `gapBefore_supIndep`, the gaps are SupIndep, so `combine` applies. -/
noncomputable def combineGaps (s S : _root_.Finset α)
    (Ps : ∀ x : α, _root_.Finpartition (gapBefore s S x)) :
    _root_.Finpartition (S.sup (fun x => gapBefore s S x)) :=
  _root_.Finpartition.combine Ps (gapBefore_supIndep s S)

@[simp]
theorem combineGaps_parts (s S : _root_.Finset α)
    (Ps : ∀ x : α, _root_.Finpartition (gapBefore s S x)) :
    (combineGaps s S Ps).parts =
      S.biUnion (fun x => (Ps x).parts) := by
  unfold combineGaps
  rfl

/-- **Reconstruct Finpartition**: assemble `S` and the combined gap
parts into a Finpartition of `s` (assuming `S ⊆ s` and gaps cover
`s \ S`).

Specifically: take `combineGaps`, copy to `Finpartition (s \ S)`
using `sup_gapBefore_eq_sdiff`, then `extend` to add `S`. -/
noncomputable def reconstructFromGaps (s S : _root_.Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s)
    (hcover : ∀ y ∈ s, y ∉ S → ∃ z ∈ S, y < z)
    (Ps : ∀ x : α, _root_.Finpartition (gapBefore s S x)) :
    _root_.Finpartition s :=
  -- Step 1: combine gives Finpartition (S.sup (gapBefore s S)).
  -- Step 2: copy to Finpartition (s \ S) using sup_gapBefore_eq_sdiff.
  -- Step 3: extend to add S, getting Finpartition s.
  let P_sdiff : _root_.Finpartition (s \ S) :=
    (combineGaps s S Ps).copy (sup_gapBefore_eq_sdiff s S hcover)
  P_sdiff.extend (hb := _root_.Finset.Nonempty.ne_empty hS_ne)
    (hab := _root_.Finset.sdiff_disjoint) (hc := by
      show s \ S ⊔ S = s
      rw [_root_.Finset.sup_eq_union, _root_.Finset.sdiff_union_of_subset hS_sub])

@[simp]
theorem reconstructFromGaps_parts (s S : _root_.Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s)
    (hcover : ∀ y ∈ s, y ∉ S → ∃ z ∈ S, y < z)
    (Ps : ∀ x : α, _root_.Finpartition (gapBefore s S x)) :
    (reconstructFromGaps s S hS_ne hS_sub hcover Ps).parts =
      insert S (S.biUnion (fun x => (Ps x).parts)) := by
  unfold reconstructFromGaps
  simp [combineGaps_parts]

end Finpartition

end Hamilton.Infrastructure
