/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.FiberCompatible

/-!
# Fibers partition `NC s`

For a nonempty `s : Finset α`, the fibers `{π : NC s // blockOfLast π
hs = S}` (indexed by `S : Finset α`) **partition** the set of all
noncrossing partitions of `s`.

This gives the cardinality identity

  |NC s| = ∑_{S ⊆ s, s.max' ∈ S} |fiber S|

which combined with the (deeper, Kreweras-Simion) fiber-product
identity |fiber S| = ∏ Catalan(gap_i) gives the Catalan recursion.

## Main definitions

* `NC.fiberOf hs S` — the Finset of `π : NC s` with `blockOfLast π hs = S`.

## Main results

* `NC.mem_fiberOf` — membership characterization.
* `NC.fiberOf_disjoint` — distinct `S` give disjoint fibers.
* `NC.mem_fiberOf_blockOfLast` — every `π` lies in `fiberOf hs
  (blockOfLast π hs)`.
* `NC.sum_fiberOf_card` — `∑_S |fiberOf hs S| = Fintype.card (NC s)`.

## Tags

noncrossing partition, fiber, partition identity, Catalan
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The **fiber** of `π : NC s` with `blockOfLast π hs = S`. -/
noncomputable def fiberOf (hs : s.Nonempty) (S : Finset α) :
    Finset (NC s) :=
  (Finset.univ : Finset (NC s)).filter (fun π => blockOfLast π hs = S)

@[simp]
theorem mem_fiberOf (hs : s.Nonempty) (S : Finset α) (π : NC s) :
    π ∈ fiberOf hs S ↔ blockOfLast π hs = S := by
  unfold fiberOf
  rw [Finset.mem_filter]
  simp

theorem fiberOf_disjoint (hs : s.Nonempty)
    {S T : Finset α} (hne : S ≠ T) :
    Disjoint (fiberOf hs S) (fiberOf hs T) := by
  rw [Finset.disjoint_left]
  intro π hπS hπT
  rw [mem_fiberOf] at hπS hπT
  exact hne (hπS.symm.trans hπT)

theorem mem_fiberOf_blockOfLast (hs : s.Nonempty) (π : NC s) :
    π ∈ fiberOf hs (blockOfLast π hs) := by
  rw [mem_fiberOf]

/-- **Fibers partition `NC s`**: the sum of fiber cardinalities over
all subsets `S ⊆ s` equals `Fintype.card (NC s)`.

Since `blockOfLast π hs ⊆ s` for every `π`, only `S ⊆ s` are
relevant.  We use `Finset.card_eq_sum_card_fiberwise` on the map
`π ↦ blockOfLast π hs` from `Finset.univ : Finset (NC s)` to `s.powerset`. -/
theorem sum_fiberOf_card_powerset (hs : s.Nonempty) :
    ∑ S ∈ s.powerset, (fiberOf hs S).card = Fintype.card (NC s) := by
  classical
  have h_maps : ((Finset.univ : Finset (NC s)) : Set (NC s)).MapsTo
      (fun π => blockOfLast π hs) (s.powerset : Set (Finset α)) := by
    intro π _
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset]
    exact π.val.subset (blockOfLast_mem π hs)
  have h_card := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (NC s)))
    (t := s.powerset) (f := fun π => blockOfLast π hs) h_maps
  rw [Finset.card_univ] at h_card
  -- `h_card`: `Fintype.card (NC s) = ∑ S ∈ s.powerset, {a ∈ Finset.univ | blockOfLast a hs = S}.card`
  -- Goal LHS: `∑ S ∈ s.powerset, (fiberOf hs S).card`
  -- `fiberOf hs S = Finset.univ.filter (fun π => blockOfLast π hs = S)` = the fiber set.
  rw [h_card]
  apply Finset.sum_congr rfl
  intros S _
  rfl

end NC

end Hamilton.Infrastructure
