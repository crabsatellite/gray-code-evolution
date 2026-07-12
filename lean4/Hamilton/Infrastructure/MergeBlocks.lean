/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Partition.Finpartition

/-!
# Merging two blocks of a Finpartition

For a `Finpartition s` and two distinct blocks `B₁, B₂`, the
**merge** is a new Finpartition obtained by replacing `B₁` and `B₂`
with their union.

This file provides the construction generic for any Finpartition
(no noncrossing assumption).  The noncrossing-preservation of the
merge — a non-trivial paper-§5 result — is treated separately
in `Hamilton.Infrastructure.ParentMerge`.

## Main definitions

* `Finpartition.mergeBlocks P hB₁ hB₂ hne` — the merged
  Finpartition.

## Main results

* `Finpartition.mergeBlocks_parts` — the parts of the merged
  partition.
* `Finpartition.mergeBlocks_card` — the merge reduces `parts.card`
  by exactly 1.

## Tags

Finpartition, merge, blocks
-/

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- Helper: the union of two distinct blocks is not among the
remaining blocks (i.e., parts.erase B₁ .erase B₂). -/
private theorem _union_notMem_erase (P : Finpartition s)
    {B₁ B₂ : Finset α} (hB₁ : B₁ ∈ P.parts)
    (hB₂ : B₂ ∈ P.parts) (hne : B₁ ≠ B₂) :
    B₁ ∪ B₂ ∉ ((P.parts.erase B₁).erase B₂) := by
  intro hin
  rw [Finset.mem_erase] at hin
  obtain ⟨_, hin_e1⟩ := hin
  rw [Finset.mem_erase] at hin_e1
  obtain ⟨hne_B₁, hC⟩ := hin_e1
  have hdisj : Disjoint B₁ (B₁ ∪ B₂) :=
    P.disjoint hB₁ hC (Ne.symm hne_B₁)
  have hB₁_sub : B₁ ⊆ B₁ ∪ B₂ := Finset.subset_union_left
  have hinf : B₁ ⊓ (B₁ ∪ B₂) = B₁ := inf_eq_left.mpr hB₁_sub
  have hbot : B₁ ≤ ⊥ := by rw [← hinf]; exact hdisj.le_bot
  have hB₁_emp : B₁ = ⊥ := le_bot_iff.mp hbot
  exact P.bot_notMem (hB₁_emp ▸ hB₁)

/-- The **merge** of two distinct blocks `B₁, B₂` of a Finpartition:
replace them with `B₁ ∪ B₂` in the parts list. -/
def mergeBlocks (P : Finpartition s)
    {B₁ B₂ : Finset α} (hB₁ : B₁ ∈ P.parts) (hB₂ : B₂ ∈ P.parts)
    (hne : B₁ ≠ B₂) : Finpartition s where
  parts := insert (B₁ ∪ B₂) ((P.parts.erase B₁).erase B₂)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro X hX Y hY hXY
    simp only [Finset.coe_insert, Set.mem_insert_iff,
               Finset.mem_coe, Finset.mem_erase] at hX hY
    have hP_disj := P.disjoint
    rcases hX with hX_BC | hX_in
    · rcases hY with hY_BC | hY_in
      · exact absurd (hX_BC.trans hY_BC.symm) hXY
      · subst hX_BC
        obtain ⟨hY_ne_C, hY_ne_B, hY_in_parts⟩ := hY_in
        have hB_disj_Y : Disjoint B₁ Y :=
          hP_disj hB₁ hY_in_parts (Ne.symm hY_ne_B)
        have hC_disj_Y : Disjoint B₂ Y :=
          hP_disj hB₂ hY_in_parts (Ne.symm hY_ne_C)
        exact hB_disj_Y.sup_left hC_disj_Y
    · rcases hY with hY_BC | hY_in
      · subst hY_BC
        obtain ⟨hX_ne_C, hX_ne_B, hX_in_parts⟩ := hX_in
        have hX_disj_B : Disjoint X B₁ :=
          hP_disj hX_in_parts hB₁ hX_ne_B
        have hX_disj_C : Disjoint X B₂ :=
          hP_disj hX_in_parts hB₂ hX_ne_C
        exact hX_disj_B.sup_right hX_disj_C
      · obtain ⟨_, _, hX_p⟩ := hX_in
        obtain ⟨_, _, hY_p⟩ := hY_in
        exact hP_disj hX_p hY_p hXY
  sup_parts := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_sup, id_eq]
    constructor
    · rintro ⟨D, hD_mem, hx_in_D⟩
      rw [Finset.mem_insert] at hD_mem
      rcases hD_mem with hD_eq | hD_in
      · subst hD_eq
        rw [Finset.mem_union] at hx_in_D
        rcases hx_in_D with hx_B | hx_C
        · exact (P.subset hB₁) hx_B
        · exact (P.subset hB₂) hx_C
      · rw [Finset.mem_erase, Finset.mem_erase] at hD_in
        exact (P.subset hD_in.2.2) hx_in_D
    · intro hx
      obtain ⟨D, hD_mem, hx_in_D⟩ := P.exists_mem hx
      by_cases hD_eq_B : D = B₁
      · exact ⟨B₁ ∪ B₂, Finset.mem_insert_self _ _,
               Finset.mem_union.mpr (Or.inl (hD_eq_B ▸ hx_in_D))⟩
      by_cases hD_eq_C : D = B₂
      · exact ⟨B₁ ∪ B₂, Finset.mem_insert_self _ _,
               Finset.mem_union.mpr (Or.inr (hD_eq_C ▸ hx_in_D))⟩
      · refine ⟨D, ?_, hx_in_D⟩
        rw [Finset.mem_insert]
        right
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨hD_eq_C, hD_eq_B, hD_mem⟩
  bot_notMem := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with hEq | hIn
    · have hne_BC : (B₁ ∪ B₂).Nonempty :=
        (P.nonempty_of_mem_parts hB₁).mono Finset.subset_union_left
      rw [Finset.bot_eq_empty] at hEq
      exact hne_BC.ne_empty hEq.symm
    · have hbot_in_parts : (⊥ : Finset α) ∈ P.parts := by
        rw [Finset.mem_erase] at hIn
        rw [Finset.mem_erase] at hIn
        exact hIn.2.2
      exact P.bot_notMem hbot_in_parts

@[simp]
theorem mergeBlocks_parts (P : Finpartition s)
    {B₁ B₂ : Finset α} (hB₁ : B₁ ∈ P.parts) (hB₂ : B₂ ∈ P.parts)
    (hne : B₁ ≠ B₂) :
    (P.mergeBlocks hB₁ hB₂ hne).parts =
      insert (B₁ ∪ B₂) ((P.parts.erase B₁).erase B₂) := rfl

/-- The merge decreases `parts.card` by exactly 1. -/
theorem mergeBlocks_card (P : Finpartition s)
    {B₁ B₂ : Finset α} (hB₁ : B₁ ∈ P.parts) (hB₂ : B₂ ∈ P.parts)
    (hne : B₁ ≠ B₂) :
    (P.mergeBlocks hB₁ hB₂ hne).parts.card + 1 = P.parts.card := by
  rw [mergeBlocks_parts]
  have hnotin := _union_notMem_erase P hB₁ hB₂ hne
  rw [Finset.card_insert_of_notMem hnotin]
  have hB₂_in_erase : B₂ ∈ P.parts.erase B₁ :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, hB₂⟩
  rw [Finset.card_erase_of_mem hB₂_in_erase,
      Finset.card_erase_of_mem hB₁]
  have hge2 : 2 ≤ P.parts.card := by
    have hsub : ({B₁, B₂} : Finset _) ⊆ P.parts := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc (2 : ℕ) = ({B₁, B₂} : Finset _).card :=
            (Finset.card_pair hne).symm
      _ ≤ P.parts.card := Finset.card_le_card hsub
  omega

end Finpartition
