/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Max

/-!
# Noncrossing partitions

This file introduces the **noncrossing predicate** `IsNoncrossing` on a
`Finpartition` of a `Finset α`, where `α` is a `LinearOrder`.  This
generalises the classical noncrossing-partition lattice on `[n]`
(Kreweras 1972) to arbitrary linearly-ordered finite carriers.

## Main definitions

* `IsNoncrossing P` — the noncrossing predicate.  Two distinct
  blocks `B₁ ≠ B₂` of `P` *cross* iff `B₁` and `B₂` admit an
  alternating quadruple `i < j < k < l` with `i, k ∈ B₁` and
  `j, l ∈ B₂`.  Noncrossing means no such alternating quadruple
  exists between distinct blocks.  We state this contrapositively:
  every quadruple matching the alternation pattern lies in a single
  block.

## Main results

* `isNoncrossing_bot` — the discrete partition (every element a
  singleton block) is noncrossing.

## Implementation notes

The carrier `s : Finset α` of the partition (i.e. the underlying set
of `P : Finpartition s`) is `LinearOrder`-equipped.  The classical
case is `α = Fin n` with `s = Finset.univ`.

For decidability: when `α` is additionally `Fintype + DecidableEq`,
the predicate is decidable (universal over all four-tuples in `α`).
For unbounded `α`, decidability is not given here.

## References

* G. Kreweras, *Sur les partitions non croisées d'un cycle*,
  Discrete Mathematics **1** (1972), 333-350.
* R. Simion, *Noncrossing partitions*, Discrete Mathematics **217**
  (2000), 367-409.

## Tags

noncrossing partition, Finpartition, linear order, Kreweras
-/

namespace Hamilton.Infrastructure

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The **noncrossing predicate** on a `Finpartition` of a finite set
`s ⊆ α` (where `α` is a `LinearOrder`).

A partition `P` is *noncrossing* iff whenever `i < j < k < l` are four
elements with `i, k` in one block and `j, l` in another block, those
two blocks coincide.  Equivalently: no two distinct blocks contain
elements in an alternating quadruple pattern. -/
def IsNoncrossing (P : Finpartition s) : Prop :=
  ∀ ⦃B₁⦄, B₁ ∈ P.parts → ∀ ⦃B₂⦄, B₂ ∈ P.parts →
    ∀ ⦃i j k l : α⦄, i < j → j < k → k < l →
      i ∈ B₁ → k ∈ B₁ → j ∈ B₂ → l ∈ B₂ → B₁ = B₂

/-! ### Basic properties -/

/-- The bottom partition `⊥` (singleton blocks) is trivially
noncrossing.  In `⊥`, each block is a singleton `{a}`, so for any
block and four elements `i < j < k < l` with `i, k` in this
configuration, we'd need `i = a = k`, but `i < k` from `i < j < k`
contradicts `i = k`. -/
theorem isNoncrossing_bot (s : Finset α) :
    IsNoncrossing (⊥ : Finpartition s) := by
  intro B₁ h₁ B₂ _h₂ i j k l hij hjk _hkl hi hk _hj _hl
  rw [Finpartition.parts_bot] at h₁
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp h₁
  -- B₁ = singleton a (which unfolds to {a}).
  simp only [Function.Embedding.coeFn_mk] at hi hk
  rw [Finset.mem_singleton] at hi hk
  -- Now hi : i = a and hk : k = a.
  exfalso
  subst hi
  subst hk
  exact absurd (hij.trans hjk) (lt_irrefl _)

/-! ### Computable decidability of `IsNoncrossing`

The `IsNoncrossing` predicate quantifies over `α` (potentially
infinite); to make it decidable, restrict to elements of `s` (a
`Finset`).  This is equivalent because the hypotheses `i ∈ B₁`,
`k ∈ B₁` (with `B₁ ⊆ s`) automatically force `i, k ∈ s`.

The following finite formulation supplies the computable instances used by
`NCType.lean`. -/

/-- **`IsNoncrossing_dec`**: equivalent finite-quantifier form of
`IsNoncrossing` with all variables restricted to elements of `s`. -/
def IsNoncrossing_dec (P : Finpartition s) : Prop :=
  ∀ B₁ ∈ P.parts, ∀ B₂ ∈ P.parts,
    ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, ∀ l ∈ s,
      i < j → j < k → k < l →
      i ∈ B₁ → k ∈ B₁ → j ∈ B₂ → l ∈ B₂ → B₁ = B₂

/-- **`mem_part_subset`**: every part of a `Finpartition s` is a
subset of `s`. -/
theorem mem_part_subset {P : Finpartition s} {B : Finset α}
    (hB : B ∈ P.parts) : B ⊆ s := by
  rw [← P.biUnion_parts]
  exact Finset.subset_biUnion_of_mem id hB

/-- **`isNoncrossing_iff_dec`**: equivalence of `IsNoncrossing` and
its computable form `IsNoncrossing_dec`. -/
theorem isNoncrossing_iff_dec (P : Finpartition s) :
    IsNoncrossing P ↔ IsNoncrossing_dec P := by
  constructor
  · intro h B₁ hB₁ B₂ hB₂ i _hi j _hj k _hk l _hl hij hjk hkl
      hiB₁ hkB₁ hjB₂ hlB₂
    exact h hB₁ hB₂ hij hjk hkl hiB₁ hkB₁ hjB₂ hlB₂
  · intro h B₁ hB₁ B₂ hB₂ i j k l hij hjk hkl hiB₁ hkB₁ hjB₂ hlB₂
    have hi_s : i ∈ s := mem_part_subset hB₁ hiB₁
    have hj_s : j ∈ s := mem_part_subset hB₂ hjB₂
    have hk_s : k ∈ s := mem_part_subset hB₁ hkB₁
    have hl_s : l ∈ s := mem_part_subset hB₂ hlB₂
    exact h B₁ hB₁ B₂ hB₂ i hi_s j hj_s k hk_s l hl_s hij hjk hkl
      hiB₁ hkB₁ hjB₂ hlB₂

/-- **`decidableIsNoncrossing_dec`**: `IsNoncrossing_dec` is decidable
(all quantifiers are `∀ ∈ Finset` with decidable body).

Note: declared without the `Finpartition.` namespace prefix to avoid
shadowing the global `Finpartition` namespace (which contains
Mathlib's lemmas like `splitBlock_parts`) in downstream files. -/
instance decidableIsNoncrossing_dec (P : Finpartition s) :
    Decidable (IsNoncrossing_dec P) := by
  unfold IsNoncrossing_dec
  infer_instance

/-- **`decidableIsNoncrossing`**: computable `Decidable` instance for
`IsNoncrossing P`, via the equivalence with `IsNoncrossing_dec`.
Declared without the `Finpartition.` namespace prefix; see
`decidableIsNoncrossing_dec`. -/
instance decidableIsNoncrossing (P : Finpartition s) :
    Decidable (IsNoncrossing P) :=
  decidable_of_iff _ (isNoncrossing_iff_dec P).symm

end Hamilton.Infrastructure
