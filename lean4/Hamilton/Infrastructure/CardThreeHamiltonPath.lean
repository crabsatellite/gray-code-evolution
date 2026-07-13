/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.CardFin2Final
import Hamilton.Infrastructure.CardNCInduction
import Hamilton.Infrastructure.HamiltonPath
import Hamilton.Infrastructure.Adjacency
import Hamilton.Infrastructure.NCOrder

/-!
# The explicit Hamilton path at order three

For a three-element ground set, this module constructs the three two-block
vertices of the noncrossing-partition refinement graph and verifies the
five-vertex path

`twoBlock(a) -- top -- twoBlock(c) -- bot -- twoBlock(b)`.

The construction uses only the semantic definitions of noncrossing partitions,
refinement adjacency, and Hamilton paths.
-/

namespace Hamilton.Infrastructure
namespace NC

open SimpleGraph

universe u_α

/-- The two-block `Finpartition` of `t` with singleton block `{a}` and
the complement `t \ {a}`, valid when `t.card ≥ 2` so the complement
is nonempty. -/
noncomputable def cardThreeTwoBlockByElemFP
    {α : Type u_α} [LinearOrder α] (t : Finset α)
    (a : α) (ha : a ∈ t) (h_card_ge_two : 2 ≤ t.card) :
    Finpartition t := by
  classical
  refine Finpartition.ofExistsUnique
    (insert ({a} : Finset α) ({t \ ({a} : Finset α)}))
    ?_ ?_ ?_
  · -- ⊆ t.
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp_mem
    · exact Finset.singleton_subset_iff.mpr ha
    · rw [Finset.mem_singleton] at hp_mem
      subst hp_mem
      exact Finset.sdiff_subset
  · -- ∃! membership.
    intro b hb
    by_cases h_b_a : b = a
    · refine ⟨({a} : Finset α),
        ⟨Finset.mem_insert_self _ _, Finset.mem_singleton.mpr h_b_a⟩, ?_⟩
      rintro p ⟨hp, hb_p⟩
      rcases Finset.mem_insert.mp hp with rfl | hp_eq
      · rfl
      · rw [Finset.mem_singleton] at hp_eq
        subst hp_eq
        exfalso
        rw [h_b_a] at hb_p
        exact (Finset.mem_sdiff.mp hb_p).2 (Finset.mem_singleton.mpr rfl)
    · refine ⟨t \ ({a} : Finset α),
        ⟨Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl),
         Finset.mem_sdiff.mpr ⟨hb, fun h => h_b_a (Finset.mem_singleton.mp h)⟩⟩, ?_⟩
      rintro p ⟨hp, hb_p⟩
      rcases Finset.mem_insert.mp hp with rfl | hp_eq
      · exfalso
        rw [Finset.mem_singleton] at hb_p
        exact h_b_a hb_p
      · rw [Finset.mem_singleton] at hp_eq
        exact hp_eq
  · -- ∅ ∉ parts.
    intro h_empty
    rcases Finset.mem_insert.mp h_empty with h_eq | h_eq
    · exact Finset.singleton_ne_empty _ h_eq.symm
    · rw [Finset.mem_singleton] at h_eq
      have h_rest_ne : (t \ ({a} : Finset α)).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff_of_subset
          (Finset.singleton_subset_iff.mpr ha), Finset.card_singleton]
        omega
      exact h_rest_ne.ne_empty h_eq.symm

/-- The parts of `cardThreeTwoBlockByElemFP` (literal form). -/
theorem cardThreeTwoBlockByElemFP_parts
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    {a : α} (ha : a ∈ t) (h_card_ge_two : 2 ≤ t.card) :
    (cardThreeTwoBlockByElemFP t a ha h_card_ge_two).parts =
      insert ({a} : Finset α) ({t \ ({a} : Finset α)}) := rfl

/-- **`cardThreeTwoBlockNCByElem`** — the 2-block NC of a 3-element `t` with
singleton block `{a}`.  Noncrossing is automatic at `t.card ≤ 3`. -/
noncomputable def cardThreeTwoBlockNCByElem
    {α : Type u_α} [LinearOrder α] (t : Finset α)
    (h_card : t.card = 3) (a : α) (ha : a ∈ t) :
    NC t :=
  ⟨cardThreeTwoBlockByElemFP t a ha (by omega),
   isNoncrossing_of_card_le_three (by omega)⟩

/-- `cardThreeTwoBlockNCByElem` has parts `insert {a} {t \ {a}}`. -/
theorem cardThreeTwoBlockNCByElem_parts
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) {a : α} (ha : a ∈ t) :
    (cardThreeTwoBlockNCByElem t h_card a ha).val.parts =
      insert ({a} : Finset α) ({t \ ({a} : Finset α)}) := rfl

/-- A singleton is never equal to its complement inside a set containing its
element. -/
theorem cardThreeSingleton_ne_sdiff
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    {a : α} :
    ({a} : Finset α) ≠ t \ ({a} : Finset α) := by
  intro h_eq
  have h_mem : a ∈ ({a} : Finset α) := Finset.mem_singleton.mpr rfl
  rw [h_eq] at h_mem
  exact (Finset.mem_sdiff.mp h_mem).2 (Finset.mem_singleton.mpr rfl)

/-- `cardThreeTwoBlockNCByElem` has exactly 2 blocks. -/
theorem cardThreeTwoBlockNCByElem_numBlocks
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) {a : α} (ha : a ∈ t) :
    numBlocks (cardThreeTwoBlockNCByElem t h_card a ha) = 2 := by
  show ((cardThreeTwoBlockNCByElem t h_card a ha).val.parts).card = 2
  rw [cardThreeTwoBlockNCByElem_parts h_card ha]
  rw [Finset.card_insert_of_notMem
    (by rw [Finset.mem_singleton]; exact cardThreeSingleton_ne_sdiff)]
  rfl

/-! ### Two-block adjacency at `t.card = 3`

Every 2-block NC `cardThreeTwoBlockNCByElem t a` is adjacent to both `top` and
`bot`: merging its two blocks gives the indiscrete (top); splitting
the size-2 block `t \ {a}` into singletons relates it to `bot`. -/

/-- **`cardThreeTwoBlockNCByElem_mergesTo_top`** — `cardThreeTwoBlockNCByElem t a` merges
to `top h_t_ne` (merge the two blocks → indiscrete). -/
theorem cardThreeTwoBlockNCByElem_mergesTo_top
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) (h_t_ne : t.Nonempty) {a : α} (ha : a ∈ t) :
    mergesTo (cardThreeTwoBlockNCByElem t h_card a ha) (top h_t_ne) := by
  classical
  have h_B1_mem :
      ({a} : Finset α) ∈ (cardThreeTwoBlockNCByElem t h_card a ha).val.parts := by
    rw [cardThreeTwoBlockNCByElem_parts]
    exact Finset.mem_insert_self _ _
  have h_B2_mem :
      (t \ ({a} : Finset α)) ∈ (cardThreeTwoBlockNCByElem t h_card a ha).val.parts := by
    rw [cardThreeTwoBlockNCByElem_parts]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
  have h_neq : ({a} : Finset α) ≠ t \ ({a} : Finset α) :=
    cardThreeSingleton_ne_sdiff
  refine ⟨({a} : Finset α), h_B1_mem, t \ ({a} : Finset α), h_B2_mem, h_neq, ?_⟩
  -- top's parts = {t}; {a} ∪ (t \ {a}) = t; erase both → ∅.
  have h_top_parts : (top h_t_ne).val.parts = ({t} : Finset (Finset α)) := by
    show (Finpartition.indiscrete h_t_ne.ne_empty).parts = {t}
    rw [Finpartition.indiscrete_parts]
  have h_union : ({a} : Finset α) ∪ (t \ ({a} : Finset α)) = t := by
    rw [Finset.union_sdiff_of_subset (Finset.singleton_subset_iff.mpr ha)]
  rw [h_top_parts, h_union, cardThreeTwoBlockNCByElem_parts]
  -- erase {a} from insert {a} {t\{a}} → {t\{a}}; erase (t\{a}) → ∅.
  rw [Finset.erase_insert (by
        rw [Finset.mem_singleton]; exact h_neq)]
  rw [Finset.erase_singleton]
  -- Goal: {t} = insert t ∅.
  rw [Finset.insert_empty]

/-- **`bot_mergesTo_cardThreeTwoBlockNCByElem`** — `bot t` merges to
`cardThreeTwoBlockNCByElem t a`.

`bot t` is all-singletons; the 2-element block `t \ {a}` of
`cardThreeTwoBlockNCByElem t a` is the union of the two singletons in
`t \ {a}`.  Merging those two singletons of `bot` yields
`cardThreeTwoBlockNCByElem t a`. -/
theorem cardThreeBot_mergesToTwoBlock
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) {a : α} (ha : a ∈ t) :
    mergesTo (NC.bot t) (cardThreeTwoBlockNCByElem t h_card a ha) := by
  classical
  -- t \ {a} has exactly 2 elements; name them.
  have h_rest_card : (t \ ({a} : Finset α)).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr ha),
        Finset.card_singleton, h_card]
  obtain ⟨b, c, h_bc_ne, h_rest_eq⟩ := Finset.card_eq_two.mp h_rest_card
  have hb_t : b ∈ t := by
    have : b ∈ t \ ({a} : Finset α) := by
      rw [h_rest_eq]; exact Finset.mem_insert_self _ _
    exact (Finset.mem_sdiff.mp this).1
  have hc_t : c ∈ t := by
    have : c ∈ t \ ({a} : Finset α) := by
      rw [h_rest_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
    exact (Finset.mem_sdiff.mp this).1
  -- Membership in bot t's parts is `∃ y ∈ t, {y} = B` (Finpartition.mem_bot_iff).
  have h_mem_bot_iff : ∀ B : Finset α,
      B ∈ (NC.bot t).val.parts ↔ ∃ y ∈ t, ({y} : Finset α) = B := by
    intro B
    show B ∈ (⊥ : Finpartition t).parts ↔ _
    exact Finpartition.mem_bot_iff
  have h_b_sing_mem : ({b} : Finset α) ∈ (NC.bot t).val.parts :=
    (h_mem_bot_iff _).mpr ⟨b, hb_t, rfl⟩
  have h_c_sing_mem : ({c} : Finset α) ∈ (NC.bot t).val.parts :=
    (h_mem_bot_iff _).mpr ⟨c, hc_t, rfl⟩
  have h_sing_ne : ({b} : Finset α) ≠ ({c} : Finset α) := by
    intro h
    exact h_bc_ne (Finset.singleton_injective h)
  -- a ∉ t \ {a}, but b, c ∈ t \ {a}, so a ≠ b and a ≠ c.
  have h_a_ne_b : a ≠ b := by
    intro h
    have h_b_rest : b ∈ t \ ({a} : Finset α) := by
      rw [h_rest_eq]; exact Finset.mem_insert_self _ _
    exact (Finset.mem_sdiff.mp h_b_rest).2 (Finset.mem_singleton.mpr h.symm)
  have h_a_ne_c : a ≠ c := by
    intro h
    have h_c_rest : c ∈ t \ ({a} : Finset α) := by
      rw [h_rest_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
    exact (Finset.mem_sdiff.mp h_c_rest).2 (Finset.mem_singleton.mpr h.symm)
  have h_sing_a_ne_b : ({a} : Finset α) ≠ ({b} : Finset α) := by
    intro h; exact h_a_ne_b (Finset.singleton_injective h)
  have h_sing_a_ne_c : ({a} : Finset α) ≠ ({c} : Finset α) := by
    intro h; exact h_a_ne_c (Finset.singleton_injective h)
  refine ⟨({b} : Finset α), h_b_sing_mem, ({c} : Finset α), h_c_sing_mem,
    h_sing_ne, ?_⟩
  -- cardThreeTwoBlockNCByElem's parts = insert {a} {t\{a}};
  -- {b} ∪ {c} = {b,c} = t\{a}; bot's parts erase {b}, {c} → { {a} }.
  rw [cardThreeTwoBlockNCByElem_parts]
  have h_bc_union : ({b} : Finset α) ∪ ({c} : Finset α) = t \ ({a} : Finset α) := by
    rw [h_rest_eq]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  rw [h_bc_union]
  -- Now show: insert {a} {t\{a}} = insert (t\{a}) ((bot.parts.erase {b}).erase {c}).
  -- (bot.parts.erase {b}).erase {c} = { {a} }.
  have h_erase : ((NC.bot t).val.parts.erase ({b} : Finset α)).erase ({c} : Finset α)
      = ({({a} : Finset α)} : Finset (Finset α)) := by
    ext B
    simp only [Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨h_ne_c, h_ne_b, h_mem⟩
      obtain ⟨y, hy_t, hy_eq⟩ := (h_mem_bot_iff B).mp h_mem
      -- B = {y}; y ≠ b, y ≠ c; y ∈ t; so y = a.
      have h_y_ne_b : y ≠ b := by
        intro h; apply h_ne_b; rw [← hy_eq, h]
      have h_y_ne_c : y ≠ c := by
        intro h; apply h_ne_c; rw [← hy_eq, h]
      have h_y_not_rest : y ∉ t \ ({a} : Finset α) := by
        rw [h_rest_eq]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨h_y_ne_b, h_y_ne_c⟩
      have h_y_a : y = a := by
        by_contra h_y_ne_a
        exact h_y_not_rest (Finset.mem_sdiff.mpr ⟨hy_t,
          fun h => h_y_ne_a (Finset.mem_singleton.mp h)⟩)
      rw [← hy_eq, h_y_a]
    · intro h_B_eq
      subst h_B_eq
      exact ⟨h_sing_a_ne_c, h_sing_a_ne_b, (h_mem_bot_iff _).mpr ⟨a, ha, rfl⟩⟩
  rw [h_erase]
  ext B
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-! ### A five-vertex Hamilton path between two distinct two-block partitions

At `t.card = 3`, the path alternates between `{top, bot}` and the three
two-block noncrossing partitions.  Given two distinct two-block NCs
`π = cardThreeTwoBlockNCByElem t aπ` and
`σ = cardThreeTwoBlockNCByElem t aσ`, the third 2-block NC
`τ = cardThreeTwoBlockNCByElem t aτ` (`aτ` the element of `t` outside
`{aπ, aσ}`) gives the Hamilton path `[π, top, τ, bot, σ]`. -/

/-- **`cardThree_exists_third_elem`** — at `t.card = 3`, for any
two distinct `aπ, aσ ∈ t`, there is a third element `aτ ∈ t` distinct
from both. -/
theorem cardThree_exists_third_elem
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) {aπ aσ : α} (haπ : aπ ∈ t) (haσ : aσ ∈ t)
    (h_ne : aπ ≠ aσ) :
    ∃ aτ ∈ t, aτ ≠ aπ ∧ aτ ≠ aσ := by
  classical
  -- t \ {aπ, aσ} is nonempty (card 3 - 2 = 1).
  have h_pair_sub : ({aπ, aσ} : Finset α) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h_pair_card : ({aπ, aσ} : Finset α).card = 2 := by
    rw [Finset.card_insert_of_notMem (by
          rw [Finset.mem_singleton]; exact h_ne), Finset.card_singleton]
  have h_diff_card : (t \ ({aπ, aσ} : Finset α)).card = 1 := by
    rw [Finset.card_sdiff_of_subset h_pair_sub, h_card, h_pair_card]
  obtain ⟨aτ, h_aτ_mem⟩ := Finset.card_pos.mp (by rw [h_diff_card]; decide)
  refine ⟨aτ, (Finset.mem_sdiff.mp h_aτ_mem).1, ?_, ?_⟩
  · intro h
    exact (Finset.mem_sdiff.mp h_aτ_mem).2
      (by rw [h]; exact Finset.mem_insert_self _ _)
  · intro h
    exact (Finset.mem_sdiff.mp h_aτ_mem).2
      (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))

/-- **`cardThreeTwoBlockNCByElem_inj`** — distinct singleton elements give
distinct 2-block NCs.  (`{a₁}` is a block of one but not the other.) -/
theorem cardThreeTwoBlockNCByElem_inj
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) {a₁ a₂ : α} (ha₁ : a₁ ∈ t) (ha₂ : a₂ ∈ t)
    (h_ne : a₁ ≠ a₂) :
    cardThreeTwoBlockNCByElem t h_card a₁ ha₁ ≠ cardThreeTwoBlockNCByElem t h_card a₂ ha₂ := by
  classical
  intro h_eq
  have h_parts : (cardThreeTwoBlockNCByElem t h_card a₁ ha₁).val.parts
      = (cardThreeTwoBlockNCByElem t h_card a₂ ha₂).val.parts :=
    congrArg (fun π => π.val.parts) h_eq
  rw [cardThreeTwoBlockNCByElem_parts h_card ha₁, cardThreeTwoBlockNCByElem_parts h_card ha₂] at h_parts
  -- {a₁} ∈ lhs; so {a₁} ∈ rhs = insert {a₂} {t\{a₂}}.
  have h_a1_lhs : ({a₁} : Finset α) ∈
      insert ({a₁} : Finset α) ({t \ ({a₁} : Finset α)}) :=
    Finset.mem_insert_self _ _
  rw [h_parts] at h_a1_lhs
  rw [Finset.mem_insert, Finset.mem_singleton] at h_a1_lhs
  rcases h_a1_lhs with h | h
  · -- {a₁} = {a₂} ⇒ a₁ = a₂.
    exact h_ne (Finset.singleton_injective h)
  · -- {a₁} = t \ {a₂}: card 1 = card 2.
    have h_card_eq : ({a₁} : Finset α).card = (t \ ({a₂} : Finset α)).card :=
      congrArg Finset.card h
    rw [Finset.card_singleton, Finset.card_sdiff_of_subset
      (Finset.singleton_subset_iff.mpr ha₂), Finset.card_singleton, h_card] at h_card_eq
    omega

/-- **`cardThreeTwoBlock_adj_top`** — every 2-block NC is `NCRefinementGraph`-adjacent
to `top`. -/
theorem cardThreeTwoBlock_adj_top
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) (h_t_ne : t.Nonempty) {a : α} (ha : a ∈ t) :
    (NCRefinementGraph t).Adj (cardThreeTwoBlockNCByElem t h_card a ha) (top h_t_ne) :=
  Or.inl (cardThreeTwoBlockNCByElem_mergesTo_top h_card h_t_ne ha)

/-- **`cardThreeTop_adj_twoBlock`** — `top` is adjacent to every 2-block NC. -/
theorem cardThreeTop_adj_twoBlock
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) (h_t_ne : t.Nonempty) {a : α} (ha : a ∈ t) :
    (NCRefinementGraph t).Adj (top h_t_ne) (cardThreeTwoBlockNCByElem t h_card a ha) :=
  Or.inr (cardThreeTwoBlockNCByElem_mergesTo_top h_card h_t_ne ha)

/-- **`cardThreeTwoBlock_adj_bot`** — every 2-block NC is adjacent to `bot`. -/
theorem cardThreeTwoBlock_adj_bot
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) {a : α} (ha : a ∈ t) :
    (NCRefinementGraph t).Adj (cardThreeTwoBlockNCByElem t h_card a ha) (NC.bot t) :=
  Or.inr (cardThreeBot_mergesToTwoBlock h_card ha)

/-- **`cardThreeBot_adj_twoBlock`** — `bot` is adjacent to every 2-block NC. -/
theorem cardThreeBot_adj_twoBlock
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) {a : α} (ha : a ∈ t) :
    (NCRefinementGraph t).Adj (NC.bot t) (cardThreeTwoBlockNCByElem t h_card a ha) :=
  Or.inl (cardThreeBot_mergesToTwoBlock h_card ha)

/-- **`hamiltonianPath_of_five_vertices`** — generic assembler: from
five pairwise-distinct `NC t` vertices `v0, v1, v2, v3, v4` with
consecutive `NCRefinementGraph`-adjacency and `Fintype.card (NC t) = 5`,
construct `HamiltonianPathBetween v0 v4`.

The Hamilton path is the literal four-edge walk
`[v0, v1, v2, v3, v4]`. -/
theorem hamiltonianPath_of_five_vertices
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card_NC : Fintype.card (NC t) = 5)
    (v0 v1 v2 v3 v4 : NC t)
    (h01 : (NCRefinementGraph t).Adj v0 v1)
    (h12 : (NCRefinementGraph t).Adj v1 v2)
    (h23 : (NCRefinementGraph t).Adj v2 v3)
    (h34 : (NCRefinementGraph t).Adj v3 v4)
    (h_nd : ([v0, v1, v2, v3, v4] : List (NC t)).Nodup) :
    (NCRefinementGraph t).HamiltonianPathBetween v0 v4 := by
  let p : (NCRefinementGraph t).Walk v0 v4 :=
    SimpleGraph.Walk.cons h01
      (SimpleGraph.Walk.cons h12
        (SimpleGraph.Walk.cons h23
          (SimpleGraph.Walk.cons h34 SimpleGraph.Walk.nil)))
  refine ⟨p, ?_⟩
  intro v
  have h_mem : v ∈ ([v0, v1, v2, v3, v4] : List (NC t)) := by
    have h_card : ([v0, v1, v2, v3, v4] : List (NC t)).toFinset.card =
        Fintype.card (NC t) := by
      rw [List.toFinset_card_of_nodup h_nd]
      simpa using h_card_NC.symm
    have h_univ : ([v0, v1, v2, v3, v4] : List (NC t)).toFinset =
        Finset.univ := Finset.eq_univ_of_card _ h_card
    rw [← List.mem_toFinset, h_univ]
    exact Finset.mem_univ v
  have h_count := List.count_eq_one_of_mem h_nd h_mem
  simpa [p] using h_count

/-- **`cardThree_hamiltonianPath_between_twoBlock`** — for any
two distinct 2-block NCs `π, σ` at `t.card = 3`, a Hamilton path
`π → σ` exists in `NCRefinementGraph t`.

The path code is `[π, top, τ, bot, σ]` where `τ` is the third 2-block
NC.  Visits all 5 NC vertices (`top`, `bot`, three 2-block NCs)
exactly once. -/
theorem cardThree_hamiltonianPath_between_twoBlock
    {α : Type u_α} [LinearOrder α] {t : Finset α}
    (h_card : t.card = 3) (h_t_ne : t.Nonempty)
    {aπ aσ : α} (haπ : aπ ∈ t) (haσ : aσ ∈ t) (h_ne : aπ ≠ aσ) :
    (NCRefinementGraph t).HamiltonianPathBetween
      (cardThreeTwoBlockNCByElem t h_card aπ haπ) (cardThreeTwoBlockNCByElem t h_card aσ haσ) := by
  classical
  -- The third element and third 2-block NC.
  obtain ⟨aτ, haτ_t, h_aτ_ne_aπ, h_aτ_ne_aσ⟩ :=
    cardThree_exists_third_elem h_card haπ haσ h_ne
  set π := cardThreeTwoBlockNCByElem t h_card aπ haπ with hπ_def
  set σ := cardThreeTwoBlockNCByElem t h_card aσ haσ with hσ_def
  set τ := cardThreeTwoBlockNCByElem t h_card aτ haτ_t with hτ_def
  set tp := top h_t_ne with htp_def
  set bt := NC.bot t with hbt_def
  -- |NC t| = 5.
  have h_card_NC : Fintype.card (NC t) = 5 := by
    rw [card_NC_eq_catalan_card t, h_card, catalan_three]
  -- Distinctness facts.
  have h_π_ne_τ : π ≠ τ := cardThreeTwoBlockNCByElem_inj h_card haπ haτ_t (Ne.symm h_aτ_ne_aπ)
  have h_σ_ne_τ : σ ≠ τ := cardThreeTwoBlockNCByElem_inj h_card haσ haτ_t (Ne.symm h_aτ_ne_aσ)
  have h_π_ne_σ : π ≠ σ := cardThreeTwoBlockNCByElem_inj h_card haπ haσ h_ne
  -- top ≠ bot, and top/bot ≠ any 2-block NC (parity / numBlocks).
  have h_nb_π : numBlocks π = 2 := cardThreeTwoBlockNCByElem_numBlocks h_card haπ
  have h_nb_σ : numBlocks σ = 2 := cardThreeTwoBlockNCByElem_numBlocks h_card haσ
  have h_nb_τ : numBlocks τ = 2 := cardThreeTwoBlockNCByElem_numBlocks h_card haτ_t
  have h_nb_tp : numBlocks tp = 1 := numBlocks_top h_t_ne
  have h_nb_bt : numBlocks bt = 3 := by
    rw [hbt_def, numBlocks_bot, h_card]
  have h_tp_ne_bt : tp ≠ bt := by
    intro h
    have := congrArg numBlocks h
    rw [h_nb_tp, h_nb_bt] at this
    omega
  have h_π_ne_tp : π ≠ tp := by
    intro h; have := congrArg numBlocks h; rw [h_nb_π, h_nb_tp] at this; omega
  have h_π_ne_bt : π ≠ bt := by
    intro h; have := congrArg numBlocks h; rw [h_nb_π, h_nb_bt] at this; omega
  have h_σ_ne_tp : σ ≠ tp := by
    intro h; have := congrArg numBlocks h; rw [h_nb_σ, h_nb_tp] at this; omega
  have h_σ_ne_bt : σ ≠ bt := by
    intro h; have := congrArg numBlocks h; rw [h_nb_σ, h_nb_bt] at this; omega
  have h_τ_ne_tp : τ ≠ tp := by
    intro h; have := congrArg numBlocks h; rw [h_nb_τ, h_nb_tp] at this; omega
  have h_τ_ne_bt : τ ≠ bt := by
    intro h; have := congrArg numBlocks h; rw [h_nb_τ, h_nb_bt] at this; omega
  -- Nodup of [π, tp, τ, bt, σ].
  have h_nd : ([π, tp, τ, bt, σ] : List (NC t)).Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h | h | h)
      · exact h_π_ne_tp h
      · exact h_π_ne_τ h
      · exact h_π_ne_bt h
      · exact h_π_ne_σ h
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h | h)
      · exact h_τ_ne_tp h.symm
      · exact h_tp_ne_bt h
      · exact h_σ_ne_tp h.symm
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h)
      · exact h_τ_ne_bt h
      · exact h_σ_ne_τ h.symm
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro h
      exact h_σ_ne_bt h.symm
    exact List.nodup_singleton _
  -- Assemble via the generic five-list helper.
  exact hamiltonianPath_of_five_vertices h_card_NC π tp τ bt σ
    (cardThreeTwoBlock_adj_top h_card h_t_ne haπ)
    (cardThreeTop_adj_twoBlock h_card h_t_ne haτ_t)
    (cardThreeTwoBlock_adj_bot h_card haτ_t)
    (cardThreeBot_adj_twoBlock h_card haσ)
    h_nd

end NC
end Hamilton.Infrastructure
