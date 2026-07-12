/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCType
import Hamilton.Infrastructure.NoncrossingPartition
import Hamilton.Infrastructure.GapPartsDecomp

/-!
# Boundary cardinalities: `|NC ∅| = 1` and `|NC {x}| = 1`

Two simple cardinality results used as base cases for inductive
arguments (e.g., the Catalan recursion).

## Main results

* `NC.card_empty` — `Fintype.card (NC ∅) = 1`.
* `NC.card_singleton` — `Fintype.card (NC {x}) = 1`.

## Tags

NC, cardinality, base case, Catalan
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α]

/-- The unique Finpartition of `∅` has empty parts. -/
theorem finpartition_empty_parts_empty (P : Finpartition (∅ : Finset α)) :
    P.parts = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro B hB_mem
  -- B ∈ P.parts ⇒ B ⊆ ∅ ⇒ B = ∅.  But ∅ ∉ P.parts.
  have hB_sub : B ⊆ ∅ := P.le hB_mem
  have hB_empty : B = ∅ := Finset.subset_empty.mp hB_sub
  rw [hB_empty] at hB_mem
  exact P.bot_notMem hB_mem

/-- The unique Finpartition of `∅` is the empty one. -/
theorem finpartition_empty_unique (P : Finpartition (∅ : Finset α)) :
    P = (⊥ : Finpartition (∅ : Finset α)) := by
  apply Finpartition.eq_of_parts_eq
  rw [finpartition_empty_parts_empty]
  exact (finpartition_empty_parts_empty _).symm

/-- `|NC ∅| = 1`. -/
theorem card_empty : Fintype.card (NC (∅ : Finset α)) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨bot _, ?_⟩
  intro π
  apply Subtype.ext
  exact finpartition_empty_unique π.val

/-- The unique Finpartition of `{x}` has parts `{{x}}`. -/
theorem finpartition_singleton_parts (x : α) (P : Finpartition ({x} : Finset α)) :
    P.parts = {({x} : Finset α)} := by
  -- Each B ∈ P.parts is ⊆ {x} and nonempty, so B = {x}.
  -- P.parts is nonempty (covers {x}); contains only {x}.
  ext B
  rw [Finset.mem_singleton]
  constructor
  · intro hB_mem
    have hB_sub : B ⊆ {x} := P.le hB_mem
    have hB_ne : B.Nonempty := P.nonempty_of_mem_parts hB_mem
    obtain ⟨a, ha⟩ := hB_ne
    have ha_x : a = x := Finset.mem_singleton.mp (hB_sub ha)
    -- So x ∈ B.  And B ⊆ {x}.  So B = {x}.
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨ha_x ▸ ha, ?_⟩
    intro b hb
    exact Finset.mem_singleton.mp (hB_sub hb)
  · intro hB_eq
    subst hB_eq
    have hx_in : x ∈ ({x} : Finset α) := Finset.mem_singleton.mpr rfl
    have hP : x ∈ P.part x := P.mem_part hx_in
    have hpart_mem : P.part x ∈ P.parts := P.part_mem.mpr hx_in
    have hpart_sub : P.part x ⊆ {x} := P.le hpart_mem
    -- P.part x = {x} (it must contain x and be ⊆ {x}).
    have heq : P.part x = {x} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hP, ?_⟩
      intro b hb
      exact Finset.mem_singleton.mp (hpart_sub hb)
    rwa [heq] at hpart_mem

/-- `|NC {x}| = 1`. -/
theorem card_singleton (x : α) :
    Fintype.card (NC ({x} : Finset α)) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨bot _, ?_⟩
  intro π
  apply Subtype.ext
  apply Finpartition.eq_of_parts_eq
  rw [finpartition_singleton_parts x π.val,
      finpartition_singleton_parts x (bot ({x} : Finset α)).val]

end NC

end Hamilton.Infrastructure
