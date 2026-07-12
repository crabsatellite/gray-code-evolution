/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCOperations

/-!
# The top (indiscrete) noncrossing partition

For a nonempty `s : Finset α`, the **indiscrete partition** has `s`
itself as its unique block.  It is trivially noncrossing (only one
block, so the antecedent of `IsNoncrossing` is vacuous) and serves as
the *top* element in the refinement-order on `NC s`.

## Main definitions

* `NC.top` — the indiscrete partition `{s}` as an `NC α s`.

## Main results

* `NC.numBlocks_top` — `numBlocks (NC.top hs) = 1`.
* `NC.numBlocks_one_eq_top` — converse: a one-block NC partition
  equals `NC.top`.

## Tags

noncrossing partition, top, indiscrete partition
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The **top** noncrossing partition: the indiscrete partition whose
unique block is `s` itself.  Defined when `s` is nonempty (else `s = ⊥`
and `Finpartition.indiscrete` is undefined). -/
def top {α : Type*} [LinearOrder α] {s : Finset α} (hs : s.Nonempty) :
    NC s :=
  ⟨Finpartition.indiscrete hs.ne_empty, by
    intro B₁ h₁ B₂ h₂ _ _ _ _ _ _ _ _ _ _ _
    -- B₁ = B₂ = s by mem_singleton (both belong to {s}).
    rw [Finpartition.indiscrete_parts, Finset.mem_singleton] at h₁ h₂
    exact h₁.trans h₂.symm⟩

/-- The top partition has exactly one block. -/
@[simp]
theorem numBlocks_top (hs : s.Nonempty) : numBlocks (top hs) = 1 := by
  unfold numBlocks top
  rw [Finpartition.indiscrete_parts]
  rfl

/-- Converse of `numBlocks_top`: a one-block NC partition equals
`NC.top`.

If `numBlocks π = 1`, then `π.val.parts` is a singleton `{B}`.  By
`Finpartition.sup_parts`, the supremum of parts equals `s`, and
`Finset.sup_singleton` gives `B = s`.  Hence the parts match
`(top hs).val.parts = {s}`. -/
theorem numBlocks_one_eq_top (π : NC s) (hs : s.Nonempty)
    (h : numBlocks π = 1) : π = top hs := by
  unfold numBlocks at h
  obtain ⟨B, hB_eq⟩ := Finset.card_eq_one.mp h
  have hsup : π.val.parts.sup id = s := π.val.sup_parts
  rw [hB_eq, Finset.sup_singleton, id_def] at hsup
  apply Subtype.ext
  unfold top
  apply Finpartition.ext
  rw [hB_eq, hsup]
  rfl

end NC

end Hamilton.Infrastructure
