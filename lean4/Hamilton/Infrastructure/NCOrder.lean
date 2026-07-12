/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCType
import Hamilton.Infrastructure.NCOperations
import Hamilton.Infrastructure.Top
import Hamilton.Infrastructure.Adjacency
import Hamilton.Infrastructure.GapPartsDecomp
import Hamilton.Infrastructure.NCBoundary
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Partial order on `NC s` via refinement

`NC s` inherits a partial order from `Finpartition s` (refinement
order): `π ≤ σ` iff every block of `π` is contained in some block
of `σ`.

## Main results

* `NC` has `PartialOrder` via `Subtype.partialOrder`.
* `NC.bot_le` — `bot ≤ π` for any `π : NC s`.

## Tags

NC, partial order, refinement, Finpartition
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- `NC s` inherits the refinement order from `Finpartition s`. -/
instance : PartialOrder (NC s) := Subtype.partialOrder _

/-- `bot ≤ π` for any `π : NC s`. -/
theorem bot_le_NC (π : NC s) : bot s ≤ π := by
  show (⊥ : Finpartition s) ≤ π.val
  exact bot_le

/-- `NC s` has `OrderBot` with `⊥ = bot s`. -/
instance : OrderBot (NC s) where
  bot := bot s
  bot_le := bot_le_NC

end NC

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- `π ≤ top hs` for any `π : NC s` (top is the maximum). -/
theorem le_top_NC (hs : s.Nonempty) (π : NC s) : π ≤ top hs := by
  show π.val ≤ (top hs).val
  intro B hB_mem
  refine ⟨s, ?_, π.val.le hB_mem⟩
  show s ∈ (top hs).val.parts
  show s ∈ ({s} : Finset (Finset α))
  exact Finset.mem_singleton.mpr rfl

/-- For nonempty `s`, `numBlocks π = 1 ↔ π = top hs`. -/
theorem numBlocks_eq_one_iff_top (hs : s.Nonempty) (π : NC s) :
    numBlocks π = 1 ↔ π = top hs := by
  constructor
  · exact numBlocks_one_eq_top π hs
  · intro h
    rw [h]
    exact numBlocks_top hs

/-- `numBlocks (bot s) = s.card`. -/
@[simp]
theorem numBlocks_bot (s : Finset α) : numBlocks (bot s) = s.card := by
  show (⊥ : Finpartition s).parts.card = s.card
  exact Finpartition.card_bot s

/-- If `numBlocks π = s.card`, then `π = bot`. -/
theorem numBlocks_eq_card_eq_bot (π : NC s) (h : numBlocks π = s.card) :
    π = bot s := by
  apply Subtype.ext
  apply Finpartition.eq_of_parts_eq
  show π.val.parts = (⊥ : Finpartition s).parts
  -- Each block of π has size 1 (sum = s.card, count = s.card, all ≥ 1).
  -- π.parts = (⊥).parts = {{x} | x ∈ s}.
  have h_sum : ∑ B ∈ π.val.parts, B.card = s.card := by
    have h1 : ∑ B ∈ π.val.parts, B.card =
        (π.val.parts.biUnion id).card := by
      rw [Finset.card_biUnion (fun B₁ hB₁ B₂ hB₂ hne =>
        π.val.disjoint hB₁ hB₂ hne)]
      simp
    have h2 : π.val.parts.biUnion id = s := by
      rw [← Finset.sup_eq_biUnion]
      exact π.val.sup_parts
    rw [h1, h2]
  have h_ge : ∀ B ∈ π.val.parts, 1 ≤ B.card := fun B hB =>
    Finset.card_pos.mpr (π.val.nonempty_of_mem_parts hB)
  have h_each_one : ∀ B ∈ π.val.parts, B.card = 1 := by
    intro B hB
    by_contra h_ne
    have h_gt : 2 ≤ B.card := by have := h_ge B hB; omega
    have h_card_eq : π.val.parts.card = s.card := h
    have h_other_ge : (π.val.parts.erase B).card ≤
        ∑ B' ∈ π.val.parts.erase B, B'.card := by
      calc (π.val.parts.erase B).card
          = ∑ _ ∈ π.val.parts.erase B, (1 : ℕ) := by rw [Finset.sum_const]; simp
        _ ≤ ∑ B' ∈ π.val.parts.erase B, B'.card :=
            Finset.sum_le_sum (fun B' hB' => h_ge B' (Finset.mem_of_mem_erase hB'))
    have h_erase_card : (π.val.parts.erase B).card = s.card - 1 := by
      rw [Finset.card_erase_of_mem hB, h_card_eq]
    rw [h_erase_card] at h_other_ge
    have h_split : ∑ B' ∈ π.val.parts, B'.card =
        ∑ B' ∈ π.val.parts.erase B, B'.card + B.card :=
      (Finset.sum_erase_add _ _ hB).symm
    have h_final : ∑ B' ∈ π.val.parts.erase B, B'.card + B.card = s.card := by
      rw [← h_split]; exact h_sum
    -- s.card - 1 ≤ erase sum ≤ erase + B.card = s.card. So erase sum = s.card - B.card.
    -- And erase sum ≥ s.card - 1 ≥ s.card - B.card iff B.card ≥ 1. But also erase ≤ ...
    -- Combined with h_gt (B.card ≥ 2): conflict.
    -- We have: erase + B.card = s.card. erase ≥ s.card - 1. So B.card ≤ 1.
    -- But h_gt: B.card ≥ 2.  Contradiction.
    omega
  -- π.parts = {{x} | x ∈ s} = ⊥.parts via the singleton-correspondence.
  rw [Finpartition.parts_bot]
  -- Show π.parts = Finset.univ.map ⟨singleton, _⟩ where univ is s viewed as
  -- Finset α.  This is s.image singleton (since singleton injective).
  ext B
  rw [Finset.mem_map]
  constructor
  · intro hB_π
    have hB_card : B.card = 1 := h_each_one B hB_π
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hB_card
    have ha_s : a ∈ s := (π.val.le hB_π) (ha ▸ Finset.mem_singleton.mpr rfl)
    exact ⟨a, ha_s, by rw [ha]; rfl⟩
  · rintro ⟨a, ha_s, hB_eq⟩
    -- ⟨singleton, ...⟩.toFun a = {a}.  So B = {a}.
    have hB_eq' : B = {a} := hB_eq.symm
    rw [hB_eq']
    have ha_part : a ∈ π.val.part a := π.val.mem_part ha_s
    have hpart_mem : π.val.part a ∈ π.val.parts := π.val.part_mem.mpr ha_s
    have hpart_card : (π.val.part a).card = 1 := h_each_one _ hpart_mem
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hpart_card
    have hab : a = b := by
      have : a ∈ ({b} : Finset α) := hb ▸ ha_part
      exact Finset.mem_singleton.mp this
    rw [← hab] at hb
    rw [← hb]
    exact hpart_mem

/-- For any `s`, `numBlocks π = s.card ↔ π = bot s`. -/
theorem numBlocks_eq_card_iff_bot (π : NC s) :
    numBlocks π = s.card ↔ π = bot s :=
  ⟨numBlocks_eq_card_eq_bot π, fun h => by rw [h]; exact numBlocks_bot s⟩

/-- For `s` with `s.card ≥ 2`, `bot s ≠ top hs`. -/
theorem bot_ne_top_generic (hs : s.Nonempty) (hcard : 2 ≤ s.card) :
    bot s ≠ top hs := by
  intro h
  have hb : numBlocks (bot s) = s.card := numBlocks_bot s
  have ht : numBlocks (top hs) = 1 := numBlocks_top hs
  rw [h, ht] at hb
  omega

/-- For `s.card = 1`, `bot s = top hs`. -/
theorem bot_eq_top_of_card_one (hs : s.Nonempty) (hcard : s.card = 1) :
    bot s = top hs := by
  have h_card_bot : numBlocks (bot s) = s.card := numBlocks_bot s
  rw [hcard] at h_card_bot
  exact numBlocks_one_eq_top (bot s) hs h_card_bot

/-- `NC s` is `Nontrivial` for `s.card ≥ 2`. -/
theorem nontrivial_NC (hs : s.Nonempty) (hcard : 2 ≤ s.card) :
    Nontrivial (NC s) :=
  ⟨bot s, top hs, bot_ne_top_generic hs hcard⟩

/-- `bot s = top hs ↔ s.card ≤ 1` (for nonempty s). -/
theorem bot_eq_top_iff_card_le_one (hs : s.Nonempty) :
    bot s = top hs ↔ s.card ≤ 1 := by
  constructor
  · intro h_eq
    by_contra h
    push_neg at h
    exact bot_ne_top_generic hs h h_eq
  · intro h_le
    have h_pos : 1 ≤ s.card := Finset.card_pos.mpr hs
    have h_eq : s.card = 1 := by omega
    exact bot_eq_top_of_card_one hs h_eq

/-- For `s` with `s.card ≥ 2`, `NC s` is not subsingleton. -/
theorem not_subsingleton_NC (hs : s.Nonempty) (hcard : 2 ≤ s.card) :
    ¬ Subsingleton (NC s) := by
  intro h
  haveI := h
  exact bot_ne_top_generic hs hcard (Subsingleton.elim _ _)

/-- `NC ∅` is subsingleton (only the empty Finpartition). -/
instance : Subsingleton (NC (∅ : Finset α)) :=
  ⟨fun π σ => by
    apply Subtype.ext
    apply Finpartition.eq_of_parts_eq
    rw [finpartition_empty_parts_empty π.val,
        finpartition_empty_parts_empty σ.val]⟩

/-- `mergesTo π σ` implies `π ≤ σ` in the refinement order. -/
theorem mergesTo_le {π σ : NC s} (h : mergesTo π σ) : π ≤ σ := by
  obtain ⟨B₁, hB₁_mem, B₂, hB₂_mem, hne, hparts⟩ := h
  show π.val ≤ σ.val
  intro B hB_mem
  -- B is a block of π. In σ, B might be in (B₁ ∪ B₂) or unchanged.
  by_cases h_eq_B₁ : B = B₁
  · -- B = B₁: in σ, this block is part of B₁ ∪ B₂.
    refine ⟨B₁ ∪ B₂, ?_, ?_⟩
    · rw [hparts]
      exact Finset.mem_insert_self _ _
    · rw [h_eq_B₁]
      exact Finset.subset_union_left
  · by_cases h_eq_B₂ : B = B₂
    · refine ⟨B₁ ∪ B₂, ?_, ?_⟩
      · rw [hparts]
        exact Finset.mem_insert_self _ _
      · rw [h_eq_B₂]
        exact Finset.subset_union_right
    · -- B ≠ B₁, B ≠ B₂: B remains in σ.parts (just erased others).
      refine ⟨B, ?_, le_refl _⟩
      rw [hparts]
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨h_eq_B₂, h_eq_B₁, hB_mem⟩

end NC

end Hamilton.Infrastructure
