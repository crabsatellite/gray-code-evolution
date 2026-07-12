/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.CatalanBase
import Hamilton.Infrastructure.Top
import Hamilton.Infrastructure.NoncrossingPartition
import Hamilton.Infrastructure.FinHelpers
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `|NC(Fin 2)| = 2 = catalan 2`

The first non-trivial Catalan cardinality: `|NC s| = 2` for `|s| = 2`.

For `s` with 2 elements, every Finpartition is trivially noncrossing
(no alternating quadruple is possible).  So `|NC s| = #Finpartition s
= 2` (bot = two singletons, top = one block).

## Main results

* `NC.card_NC_univ_fin_two` — `|NC (Finset.univ : Finset (Fin 2))| = 2`.

## Tags

NC, Catalan, Fin 2
-/

namespace Hamilton.Infrastructure

namespace NC

/-- The two NCs of `Fin 2` are `bot _` (two singletons) and `top _`
(one block).  They are distinct (different `numBlocks`). -/
theorem bot_ne_top_fin_two :
    bot (Finset.univ : Finset (Fin 2)) ≠
      top (fin_univ_succ_nonempty 1) := by
  intro h
  have hb : numBlocks (bot (Finset.univ : Finset (Fin 2))) = 2 := by
    show (⊥ : Finpartition (Finset.univ : Finset (Fin 2))).parts.card = 2
    rw [Finpartition.parts_bot]
    rw [Finset.card_map]
    decide
  have ht : numBlocks (top (fin_univ_succ_nonempty 1)) = 1 := by
    show ({(Finset.univ : Finset (Fin 2))} : Finset _).card = 1
    exact Finset.card_singleton _
  rw [h] at hb
  omega

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- For `|s| ≤ 2`, every `Finpartition s` is noncrossing (trivially —
no alternating quadruple `i < j < k < l` is possible). -/
theorem isNoncrossing_of_card_le_two {P : Finpartition s} (h : s.card ≤ 2) :
    IsNoncrossing P := by
  intro B₁ _ B₂ _ i j k l hij hjk hkl hi hk hj hl
  -- All four i, j, k, l ∈ s (transitively via P.le and block membership).
  -- They are distinct (strict inequalities).  So |s| ≥ 4 > 2.  Contradiction.
  exfalso
  have hP_le_B₁ : B₁ ⊆ s := P.le (by assumption)
  have hP_le_B₂ : B₂ ⊆ s := P.le (by assumption)
  have hi_s : i ∈ s := hP_le_B₁ hi
  have hj_s : j ∈ s := hP_le_B₂ hj
  have hk_s : k ∈ s := hP_le_B₁ hk
  have hl_s : l ∈ s := hP_le_B₂ hl
  have h4 : ({i, j, k, l} : Finset α).card ≤ s.card := by
    apply Finset.card_le_card
    intro x hx
    rw [show ({i, j, k, l} : Finset α) = insert i (insert j (insert k {l}))
      from rfl] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({i, j, k, l} : Finset α).card = 4 := by
    have hij_ne : i ≠ j := ne_of_lt hij
    have hik_ne : i ≠ k := ne_of_lt (lt_trans hij hjk)
    have hil_ne : i ≠ l := ne_of_lt (lt_trans hij (lt_trans hjk hkl))
    have hjk_ne : j ≠ k := ne_of_lt hjk
    have hjl_ne : j ≠ l := ne_of_lt (lt_trans hjk hkl)
    have hkl_ne : k ≠ l := ne_of_lt hkl
    rw [show ({i, j, k, l} : Finset α) = insert i (insert j (insert k {l}))
      from rfl]
    rw [Finset.card_insert_of_notMem (by simp [hij_ne, hik_ne, hil_ne])]
    rw [Finset.card_insert_of_notMem (by simp [hjk_ne, hjl_ne])]
    rw [Finset.card_insert_of_notMem (by simp [hkl_ne])]
    rfl
  rw [hcard] at h4
  omega

/-- For `|s| ≤ 3`, every `Finpartition s` is noncrossing (trivially —
no alternating quadruple `i < j < k < l` is possible). -/
theorem isNoncrossing_of_card_le_three {P : Finpartition s} (h : s.card ≤ 3) :
    IsNoncrossing P := by
  intro B₁ _ B₂ _ i j k l hij hjk hkl hi hk hj hl
  exfalso
  have hP_le_B₁ : B₁ ⊆ s := P.le (by assumption)
  have hP_le_B₂ : B₂ ⊆ s := P.le (by assumption)
  have hi_s : i ∈ s := hP_le_B₁ hi
  have hj_s : j ∈ s := hP_le_B₂ hj
  have hk_s : k ∈ s := hP_le_B₁ hk
  have hl_s : l ∈ s := hP_le_B₂ hl
  have h4 : ({i, j, k, l} : Finset α).card ≤ s.card := by
    apply Finset.card_le_card
    intro x hx
    rw [show ({i, j, k, l} : Finset α) = insert i (insert j (insert k {l}))
      from rfl] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({i, j, k, l} : Finset α).card = 4 := by
    have hij_ne : i ≠ j := ne_of_lt hij
    have hik_ne : i ≠ k := ne_of_lt (lt_trans hij hjk)
    have hil_ne : i ≠ l := ne_of_lt (lt_trans hij (lt_trans hjk hkl))
    have hjk_ne : j ≠ k := ne_of_lt hjk
    have hjl_ne : j ≠ l := ne_of_lt (lt_trans hjk hkl)
    have hkl_ne : k ≠ l := ne_of_lt hkl
    rw [show ({i, j, k, l} : Finset α) = insert i (insert j (insert k {l}))
      from rfl]
    rw [Finset.card_insert_of_notMem (by simp [hij_ne, hik_ne, hil_ne])]
    rw [Finset.card_insert_of_notMem (by simp [hjk_ne, hjl_ne])]
    rw [Finset.card_insert_of_notMem (by simp [hkl_ne])]
    rfl
  rw [hcard] at h4
  omega

/-- For `|s| = 2`, the unique nonempty Finpartition of `s` with
`numBlocks = 1` is `top`. -/
theorem nc_with_one_block_eq_top
    (hs : (Finset.univ : Finset (Fin 2)).Nonempty)
    (π : NC (Finset.univ : Finset (Fin 2))) (h : numBlocks π = 1) :
    π = top hs := by
  apply Subtype.ext
  apply Finpartition.eq_of_parts_eq
  -- π.parts has 1 element, top.parts = {Finset.univ}.
  show π.val.parts = {Finset.univ}
  obtain ⟨B, hB_eq⟩ := Finset.card_eq_one.mp h
  rw [hB_eq]
  congr 1
  -- B ∈ π.val.parts, B ⊆ Finset.univ, B.sup = Finset.univ ⇒ B = Finset.univ.
  have hB_mem : B ∈ π.val.parts := by rw [hB_eq]; exact Finset.mem_singleton.mpr rfl
  have hsup : π.val.parts.sup id = Finset.univ := π.val.sup_parts
  rw [hB_eq, Finset.sup_singleton, id] at hsup
  exact hsup

/-- For `|s| = 2`, the unique Finpartition with `numBlocks = 2` is
`bot` (= all singletons). -/
theorem nc_with_two_blocks_eq_bot
    (π : NC (Finset.univ : Finset (Fin 2))) (h : numBlocks π = 2) :
    π = bot _ := by
  apply Subtype.ext
  apply Finpartition.eq_of_parts_eq
  show π.val.parts = (⊥ : Finpartition (Finset.univ : Finset (Fin 2))).parts
  rw [Finpartition.parts_bot]
  -- (⊥ : Finpartition _).parts = Finset.univ.map ⟨singleton, ...⟩ = {{0}, {1}}.
  -- π.parts has 2 elements, each nonempty, disjoint, covering {0,1}.
  -- ⇒ π.parts = {{0}, {1}}.
  -- Each part has size ≥ 1, total size = 2 (sum), so each part has size exactly 1.
  have h_sum : ∑ B ∈ π.val.parts, B.card = 2 := by
    have h1 : ∑ B ∈ π.val.parts, B.card =
        (π.val.parts.biUnion id).card := by
      rw [Finset.card_biUnion (fun B₁ hB₁ B₂ hB₂ hne =>
        π.val.disjoint hB₁ hB₂ hne)]
      simp
    have h2 : π.val.parts.biUnion id = Finset.univ := by
      rw [← Finset.sup_eq_biUnion]
      exact π.val.sup_parts
    rw [h1, h2]
    decide
  have h_ge : ∀ B ∈ π.val.parts, 1 ≤ B.card := fun B hB =>
    Finset.card_pos.mpr (π.val.nonempty_of_mem_parts hB)
  -- Sum of 1's over 2 elements = 2; sum of B.card = 2 with each ≥ 1.  So each B.card = 1.
  have h_each_one : ∀ B ∈ π.val.parts, B.card = 1 := by
    intro B hB
    by_contra h_ne
    have h_gt : 2 ≤ B.card := by
      have := h_ge B hB
      omega
    have h_split :
        ∑ B' ∈ π.val.parts, B'.card =
        ∑ B' ∈ π.val.parts.erase B, B'.card + B.card :=
      (Finset.sum_erase_add _ _ hB).symm
    have h_other_ge :
        (π.val.parts.erase B).card ≤ ∑ B' ∈ π.val.parts.erase B, B'.card := by
      calc (π.val.parts.erase B).card
          = ∑ _ ∈ π.val.parts.erase B, (1 : ℕ) := by rw [Finset.sum_const]; simp
        _ ≤ ∑ B' ∈ π.val.parts.erase B, B'.card := by
            apply Finset.sum_le_sum
            intro B' hB'
            exact h_ge B' (Finset.mem_of_mem_erase hB')
    have h_erase_card : (π.val.parts.erase B).card = 1 := by
      rw [Finset.card_erase_of_mem hB, show π.val.parts.card = 2 from h]
    rw [h_erase_card] at h_other_ge
    have h_final : ∑ B' ∈ π.val.parts.erase B, B'.card + B.card = 2 := by
      rw [← h_split]; exact h_sum
    omega
  -- Now: each block of π has card 1.  And π.parts has 2 elements.
  -- Each block of size 1 is a singleton {x} for some x ∈ {0, 1}.
  -- So π.parts = {{0}, {1}} (or the same).
  ext B
  constructor
  · intro hB_π
    -- B has card 1.
    have hB_card : B.card = 1 := h_each_one B hB_π
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hB_card
    rw [ha]
    -- a ∈ Finset.univ : Finset (Fin 2), so a ∈ {(0 : Fin 2), 1}.
    have ha_univ : a ∈ (Finset.univ : Finset (Fin 2)) := by
      apply π.val.le hB_π
      rw [ha]
      exact Finset.mem_singleton.mpr rfl
    rw [Finset.mem_map]
    refine ⟨a, ha_univ, ?_⟩
    rfl
  · intro hB_bot
    rw [Finset.mem_map] at hB_bot
    obtain ⟨a, _, hB_eq⟩ := hB_bot
    -- a ∈ Finset.univ, so a = 0 or a = 1.
    -- B = {a} via ⟨singleton, _⟩.
    have hB_eq' : B = {a} := hB_eq.symm
    -- a ∈ π.part a ∈ π.parts (since a ∈ Finset.univ).
    have ha_univ : a ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ a
    have hpa : π.val.part a ∈ π.val.parts := π.val.part_mem.mpr ha_univ
    have ha_pa : a ∈ π.val.part a := π.val.mem_part ha_univ
    have hpa_card : (π.val.part a).card = 1 := h_each_one _ hpa
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hpa_card
    have : a = b := by
      have : a ∈ ({b} : Finset (Fin 2)) := hb ▸ ha_pa
      exact Finset.mem_singleton.mp this
    subst this
    have : π.val.part a = {a} := hb
    rw [hB_eq', ← this]
    exact hpa

/-- An NC of `Fin 2` has `numBlocks ≤ 2`. -/
theorem nc_numBlocks_le_two (π : NC (Finset.univ : Finset (Fin 2))) :
    numBlocks π ≤ 2 := by
  show π.val.parts.card ≤ 2
  have h_card_univ : (Finset.univ : Finset (Fin 2)).card = 2 := by decide
  -- The parts are disjoint subsets covering Finset.univ.
  -- ∑ B ∈ parts, B.card = parts.sup.card = |Finset.univ|.
  -- Each B has card ≥ 1, so parts.card ≤ ∑ B.card = |Finset.univ| = 2.
  have h_sum : ∑ B ∈ π.val.parts, B.card = 2 := by
    have h1 : ∑ B ∈ π.val.parts, B.card =
        (π.val.parts.biUnion id).card := by
      rw [Finset.card_biUnion (fun B₁ hB₁ B₂ hB₂ hne =>
        π.val.disjoint hB₁ hB₂ hne)]
      simp
    have h2 : π.val.parts.biUnion id = Finset.univ := by
      rw [← Finset.sup_eq_biUnion]
      exact π.val.sup_parts
    rw [h1, h2, h_card_univ]
  have h_ge : ∀ B ∈ π.val.parts, 1 ≤ B.card := fun B hB =>
    Finset.card_pos.mpr (π.val.nonempty_of_mem_parts hB)
  have h_chain : π.val.parts.card ≤ ∑ B ∈ π.val.parts, B.card := by
    calc π.val.parts.card
        = ∑ _ ∈ π.val.parts, (1 : ℕ) := by rw [Finset.sum_const]; simp
      _ ≤ ∑ B ∈ π.val.parts, B.card :=
          Finset.sum_le_sum (fun B hB => h_ge B hB)
  omega

end NC

end Hamilton.Infrastructure
