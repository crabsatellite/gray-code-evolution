/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCBlockMax
import Hamilton.Infrastructure.NCReconstructFromProfile
import Hamilton.Infrastructure.NCToDyckPrefix

/-!
# NC stack invariant for reconstructFromProfile

This file defines the precise **stack invariant** for the reconstruction
algorithm applied to an NC `π`'s profile `(blockMaxes π, sizes_π)`.

## The invariant

After processing first `j` elements of `s.sort`:
* `state.stack` = elements `x ∈ s.sort.take j` with `block_max π x > l_j`
  (= block hasn't closed yet), in LIFO order: the element with **largest
  value** on top.
* `state.blocks` = list of `π.val.part b` for `b ∈ blockMaxes π` with
  `b ∈ s.sort.take j`.

## Key structural lemma (NC closure)

In NC, when `l_j` is itself a block-max (size `k`), the top `k` of the
stack (after pushing `l_j`) equal `part π l_j` precisely.  Proof uses the
non-crossing structure: outer-block elements are pushed earlier (lower
in stack); inner-block elements (= part l_j \ {l_j}) are at the top.

## Main definitions

* `NC.blockMaxOf π x` — `block_max π x = (π.val.part x).max' _`.
* `NC.stackInvariantSet π j` — the SET of stack contents at step `j`.
* `NC.blocksInvariantSet π j` — the SET of finalized blocks at step `j`.

## Strategy

We start with the SET-level invariants (cardinalities, set equalities),
which are easier than the order-level invariant.  The order-level
invariant follows once we have the set-level + the LIFO push-order
structural lemma.

## Tags

NC, stack invariant, reconstruction, uniqueness, bijection
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The block-max of `x ∈ s` in NC `π`: the max of `x`'s block. -/
noncomputable def blockMaxOf' (π : NC s) (x : α) (hx : x ∈ s) : α :=
  (π.val.part x).max' ⟨x, π.val.mem_part_self.mpr hx⟩

/-- `blockMaxOf' π x hx ∈ π.val.part x`. -/
theorem blockMaxOf'_mem_part (π : NC s) (x : α) (hx : x ∈ s) :
    blockMaxOf' π x hx ∈ π.val.part x :=
  (π.val.part x).max'_mem _

/-- `blockMaxOf' π x hx ∈ s`. -/
theorem blockMaxOf'_mem_s (π : NC s) (x : α) (hx : x ∈ s) :
    blockMaxOf' π x hx ∈ s :=
  π.val.subset (π.val.part_mem.mpr hx) (blockMaxOf'_mem_part π x hx)

/-- `blockMaxOf' π x hx ≥ x`. -/
theorem blockMaxOf'_ge (π : NC s) (x : α) (hx : x ∈ s) :
    x ≤ blockMaxOf' π x hx :=
  (π.val.part x).le_max' x (π.val.mem_part_self.mpr hx)

/-- `x ∈ blockMaxes π ↔ blockMaxOf' π x hx = x`. -/
theorem mem_blockMaxes_iff_blockMaxOf'_eq (π : NC s) (x : α) (hx : x ∈ s) :
    x ∈ blockMaxes π ↔ blockMaxOf' π x hx = x := by
  unfold blockMaxOf'
  rw [mem_blockMaxes_iff_isBlockMax]
  unfold IsBlockMax
  constructor
  · rintro ⟨_, h_max⟩
    apply le_antisymm
    · apply (π.val.part x).max'_le _ _ h_max
    · exact (π.val.part x).le_max' x (π.val.mem_part_self.mpr hx)
  · intro h_eq
    refine ⟨hx, ?_⟩
    intros k hk
    rw [← h_eq]
    exact (π.val.part x).le_max' k hk

/-! ### Expected stack contents at step `j` -/

open Hamilton.Infrastructure.NC in
/-- The expected SET of stack contents at step `j` for NC `π`'s reconstruction:
elements of the first `j` of `s.sort` whose `block_max` is not yet processed. -/
noncomputable def expectedStackSet (π : NC s) (j : ℕ) : Finset α :=
  firstNElts s j |>.filter (fun x => ∀ hx : x ∈ s, blockMaxOf' π x hx ∉ firstNElts s j)

/-- Expected blocks at step `j`: parts of π whose `block-max` is in first `j` elements. -/
noncomputable def expectedBlocksSet (π : NC s) (j : ℕ) : Finset (Finset α) :=
  π.val.parts.filter (fun B => ∃ h_ne : B.Nonempty, B.max' h_ne ∈ firstNElts s j)

/-- For `j = 0`: empty stack set. -/
theorem expectedStackSet_zero (π : NC s) :
    expectedStackSet π 0 = ∅ := by
  unfold expectedStackSet firstNElts
  simp

/-- For `j = 0`: empty blocks set. -/
theorem expectedBlocksSet_zero (π : NC s) :
    expectedBlocksSet π 0 = ∅ := by
  unfold expectedBlocksSet firstNElts
  apply Finset.eq_empty_of_forall_notMem
  intros B hB
  rw [Finset.mem_filter] at hB
  obtain ⟨_, h_ne, h_in⟩ := hB
  rw [List.take_zero, List.toFinset_nil] at h_in
  exact (Finset.notMem_empty _) h_in

/-! ### firstNElts successor structure -/

/-- `firstNElts s (j+1) = insert l_j (firstNElts s j)` when `j < s.card`. -/
theorem firstNElts_succ (j : ℕ) (hj : j < s.card) :
    firstNElts s (j + 1) =
      insert ((s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj))
        (firstNElts s j) := by
  unfold firstNElts
  have h_sort_len : j < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hj
  rw [List.take_succ_eq_append_getElem h_sort_len]
  rw [List.toFinset_append]
  simp

/-- For `j < s.card`, `l_j ∈ firstNElts s (j+1)`. -/
theorem getElem_mem_firstNElts_succ (j : ℕ) (hj : j < s.card) :
    (s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj) ∈ firstNElts s (j + 1) := by
  rw [firstNElts_succ j hj]
  exact Finset.mem_insert_self _ _

/-- For `j < s.card`, `l_j ∉ firstNElts s j` (since `l_j` is the (j+1)-th smallest,
not among the first `j` smallest). -/
theorem getElem_not_mem_firstNElts (j : ℕ) (hj : j < s.card) :
    (s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj) ∉ firstNElts s j := by
  intro h_mem
  unfold firstNElts at h_mem
  rw [List.mem_toFinset, List.mem_take_iff_getElem] at h_mem
  obtain ⟨n, hn, h_eq⟩ := h_mem
  have h_nodup : (s.sort (· ≤ ·)).Nodup := s.sort_nodup _
  have h_n_lt : n < (s.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; omega
  have h_inj : n = j := by
    have h_sort_len : j < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hj
    rw [List.Nodup.getElem_inj_iff h_nodup] at h_eq
    exact h_eq
  omega

/-! ### Helper: `nthSorted` — clean getElem on `s.sort` -/

/-- The `j`-th smallest element of `s` (0-indexed). -/
noncomputable def nthSorted (s : Finset α) (j : ℕ) (hj : j < s.card) : α :=
  (s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj)

/-- `nthSorted s j hj ∈ s`. -/
theorem nthSorted_mem (j : ℕ) (hj : j < s.card) : nthSorted s j hj ∈ s := by
  unfold nthSorted
  have h_mem := List.getElem_mem
    (l := s.sort (· ≤ ·)) (h := by rw [Finset.length_sort]; exact hj)
  rwa [Finset.mem_sort] at h_mem

/-- `nthSorted` equals `getElem` of `s.sort`. -/
theorem nthSorted_eq_getElem (j : ℕ) (hj : j < s.card) :
    nthSorted s j hj = (s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj) := rfl

/-- For backward compat: `getElem_sort_mem` (alias of `nthSorted_mem`). -/
theorem getElem_sort_mem (j : ℕ) (hj : j < s.card) :
    (s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj) ∈ s :=
  nthSorted_mem j hj

/-! ### expectedBlocksSet successor transitions -/

/-- firstNElts succ using nthSorted. -/
theorem firstNElts_succ' (j : ℕ) (hj : j < s.card) :
    firstNElts s (j + 1) = insert (nthSorted s j hj) (firstNElts s j) :=
  firstNElts_succ j hj

/-- For `l_j ∈ blockMaxes π`: `expectedBlocksSet π (j+1) = insert (part π l_j) (expectedBlocksSet π j)`. -/
theorem expectedBlocksSet_succ_blockMax (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∈ blockMaxes π) :
    expectedBlocksSet π (j + 1) =
      insert (π.val.part (nthSorted s j hj)) (expectedBlocksSet π j) := by
  have h_l_j_in_s : nthSorted s j hj ∈ s := nthSorted_mem j hj
  have h_l_j_max_eq : (π.val.part (nthSorted s j hj)).max'
      ⟨nthSorted s j hj, π.val.mem_part_self.mpr h_l_j_in_s⟩ = nthSorted s j hj := by
    rw [mem_blockMaxes_iff_isBlockMax] at h
    obtain ⟨_, h_max⟩ := h
    apply le_antisymm
    · apply (π.val.part _).max'_le _ _ h_max
    · exact (π.val.part _).le_max' _ (π.val.mem_part_self.mpr h_l_j_in_s)
  unfold expectedBlocksSet
  rw [firstNElts_succ' j hj]
  apply Finset.ext
  intro B
  rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
  constructor
  · rintro ⟨hB_part, h_ne, h_max_in⟩
    rw [Finset.mem_insert] at h_max_in
    rcases h_max_in with h_eq | h_in_old
    · -- B.max' = nthSorted s j hj ⟹ B = π.val.part (nthSorted ...)
      left
      have h_max_mem : B.max' h_ne ∈ B := B.max'_mem h_ne
      rw [h_eq] at h_max_mem
      symm
      exact π.val.part_eq_of_mem hB_part h_max_mem
    · right; exact ⟨hB_part, h_ne, h_in_old⟩
  · rintro (h_eq | ⟨hB_part, h_ne, h_in⟩)
    · rw [h_eq]
      refine ⟨π.val.part_mem.mpr h_l_j_in_s,
        ⟨nthSorted s j hj, π.val.mem_part_self.mpr h_l_j_in_s⟩, ?_⟩
      rw [Finset.mem_insert]
      left
      exact h_l_j_max_eq
    · refine ⟨hB_part, h_ne, ?_⟩
      rw [Finset.mem_insert]
      right; exact h_in

/-- For `l_j ∉ blockMaxes π`: `expectedBlocksSet` doesn't change. -/
theorem expectedBlocksSet_succ_not_blockMax (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∉ blockMaxes π) :
    expectedBlocksSet π (j + 1) = expectedBlocksSet π j := by
  have h_l_j_in_s : nthSorted s j hj ∈ s := nthSorted_mem j hj
  unfold expectedBlocksSet
  rw [firstNElts_succ' j hj]
  apply Finset.ext
  intro B
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hB_part, h_ne, h_max_in⟩
    rw [Finset.mem_insert] at h_max_in
    rcases h_max_in with h_eq | h_in_old
    · -- B.max' = nthSorted s j hj ⟹ l_j is a block-max, contradicting h.
      exfalso
      have h_max_mem : B.max' h_ne ∈ B := B.max'_mem h_ne
      rw [h_eq] at h_max_mem
      have h_part_eq : π.val.part (nthSorted s j hj) = B :=
        π.val.part_eq_of_mem hB_part h_max_mem
      apply h
      rw [mem_blockMaxes_iff_isBlockMax]
      refine ⟨h_l_j_in_s, ?_⟩
      unfold IsBlockMax
      intros k hk
      rw [h_part_eq] at hk
      have h_le := B.le_max' k hk
      rw [h_eq] at h_le
      exact h_le
    · exact ⟨hB_part, h_ne, h_in_old⟩
  · rintro ⟨hB_part, h_ne, h_in⟩
    refine ⟨hB_part, h_ne, ?_⟩
    rw [Finset.mem_insert]
    right; exact h_in

/-! ### expectedStackSet successor transitions -/

/-- Key fact: if `l_j ∉ BM` then no element has block-max equal to `l_j`. -/
theorem no_block_max_eq_l_j_of_not_blockMax (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∉ blockMaxes π) (x : α) (hx : x ∈ s) :
    blockMaxOf' π x hx ≠ nthSorted s j hj := by
  intro h_eq
  apply h
  -- nthSorted is the max of x's block, hence in BM.
  -- We have blockMaxOf' π x hx ∈ π.val.part x (proven).
  -- It's also the max. So x ∈ same block; this block has max = nthSorted.
  -- That makes nthSorted a block-max.
  have h_max_mem : blockMaxOf' π x hx ∈ π.val.part x := blockMaxOf'_mem_part π x hx
  rw [h_eq] at h_max_mem
  -- Now nthSorted ∈ π.val.part x. The parts containing nthSorted are unique.
  -- π.val.part x = π.val.part (nthSorted) [same block].
  have h_part_eq : π.val.part x = π.val.part (nthSorted s j hj) := by
    have h_nth_in_s : nthSorted s j hj ∈ s := nthSorted_mem j hj
    have h_part_x_mem : π.val.part x ∈ π.val.parts := π.val.part_mem.mpr hx
    have h_nth_mem_self : nthSorted s j hj ∈ π.val.part (nthSorted s j hj) :=
      π.val.mem_part_self.mpr h_nth_in_s
    have h_part_nth_mem : π.val.part (nthSorted s j hj) ∈ π.val.parts :=
      π.val.part_mem.mpr h_nth_in_s
    apply π.val.part_eq_of_mem h_part_nth_mem
    -- need: x ∈ π.val.part (nthSorted s j hj)
    -- We have: nthSorted s j hj ∈ π.val.part x.
    -- By disjointness of parts: if they share an element, they're equal.
    by_contra h_ne
    have h_disj := π.val.disjoint h_part_x_mem h_part_nth_mem (fun h_eq2 => h_ne (by rw [← h_eq2]; exact π.val.mem_part_self.mpr hx))
    exact Finset.disjoint_left.mp h_disj h_max_mem h_nth_mem_self
  -- Now: blockMaxOf' π x hx = (π.val.part x).max' _ = (π.val.part nthSorted).max' _.
  -- We have blockMaxOf' π x hx = nthSorted s j hj.
  -- So (π.val.part nthSorted).max' _ = nthSorted s j hj.
  -- Hence nthSorted is the max of its block — i.e., it's a block-max.
  rw [mem_blockMaxes_iff_isBlockMax]
  refine ⟨nthSorted_mem j hj, ?_⟩
  unfold IsBlockMax
  intros k hk
  -- Goal: k ≤ nthSorted s j hj
  -- hk : k ∈ π.val.part (nthSorted s j hj).
  -- By h_part_eq: π.val.part (nthSorted s j hj) = π.val.part x.
  -- So k ∈ π.val.part x, hence k ≤ (π.val.part x).max' _ = blockMaxOf' π x hx = nthSorted.
  rw [← h_part_eq] at hk
  unfold blockMaxOf' at h_eq
  rw [← h_eq]
  exact (π.val.part x).le_max' k hk

/-! ### Sorted order: elements of `firstNElts s j` are ≤ `nthSorted s j hj`

When `j < s.card`, every element of `firstNElts s j` (= first j sorted elements)
is `< nthSorted s j hj` (the (j+1)-th element). This is the sorted-order
monotonicity used to derive ordering contradictions. -/

theorem mem_firstNElts_lt_nthSorted (j : ℕ) (hj : j < s.card)
    {x : α} (hx : x ∈ firstNElts s j) :
    x < nthSorted s j hj := by
  unfold firstNElts at hx
  rw [List.mem_toFinset, List.mem_take_iff_getElem] at hx
  obtain ⟨n, hn_lt_j, h_get_eq⟩ := hx
  -- n < j, so by sort's strict ascending order, (s.sort).get n < (s.sort).get j
  have h_sort_len_j : j < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hj
  have h_sort_len_n : n < (s.sort (· ≤ ·)).length := by omega
  have h_pairwise_lt : (s.sort (· ≤ ·)).Pairwise (· < ·) :=
    (Finset.sortedLT_sort s).pairwise
  rw [← h_get_eq]
  unfold nthSorted
  -- Use Pairwise.rel_get_of_lt with the strict order
  have h_fin_lt : (⟨n, h_sort_len_n⟩ : Fin _) < ⟨j, h_sort_len_j⟩ := by
    show n < j
    omega
  exact h_pairwise_lt.rel_get_of_lt (a := ⟨n, h_sort_len_n⟩) (b := ⟨j, h_sort_len_j⟩) h_fin_lt

/-- Contrapositive: if `x ≥ nthSorted s j hj`, then `x ∉ firstNElts s j`. -/
theorem not_mem_firstNElts_of_ge (j : ℕ) (hj : j < s.card)
    {x : α} (hx : nthSorted s j hj ≤ x) :
    x ∉ firstNElts s j := by
  intro h_in
  exact absurd (mem_firstNElts_lt_nthSorted j hj h_in) (not_lt.mpr hx)

/-! ### expectedStackSet successor: non-BM case (PROVEN) -/

/-- For `l_j ∉ blockMaxes π`: `expectedStackSet π (j+1) = insert l_j (expectedStackSet π j)`.

When `l_j` is not a block-max, processing `l_j` pushes it onto the stack
without popping anything. The set of pending elements grows by `{l_j}`. -/
theorem expectedStackSet_succ_not_blockMax (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∉ blockMaxes π) :
    expectedStackSet π (j + 1) =
      insert (nthSorted s j hj) (expectedStackSet π j) := by
  have h_l_j_in_s : nthSorted s j hj ∈ s := nthSorted_mem j hj
  have h_l_j_max_gt : nthSorted s j hj < blockMaxOf' π (nthSorted s j hj) h_l_j_in_s := by
    -- l_j not BM means blockMaxOf' l_j ≠ l_j, combined with blockMaxOf' ≥ l_j gives strict.
    have h_ge := blockMaxOf'_ge π (nthSorted s j hj) h_l_j_in_s
    rcases lt_or_eq_of_le h_ge with h_lt | h_eq
    · exact h_lt
    · exfalso
      apply h
      rw [mem_blockMaxes_iff_blockMaxOf'_eq π _ h_l_j_in_s]
      exact h_eq.symm
  unfold expectedStackSet
  apply Finset.ext
  intro x
  rw [firstNElts_succ' j hj]
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · -- x ∈ filter (insert l_j (firstNElts j)) ⟹ x = l_j ∨ x ∈ filter (firstNElts j)
    rintro ⟨h_x_in, h_x_max⟩
    rcases h_x_in with h_eq | h_in_old
    · left; exact h_eq
    · right
      refine ⟨h_in_old, ?_⟩
      intros hx_in_s h_max_in_old_first
      -- h_x_max: ∀ hx, blockMaxOf' π x hx ∉ insert l_j (firstNElts j)
      apply h_x_max hx_in_s
      right; exact h_max_in_old_first
  · -- x = l_j ∨ x ∈ filter (firstNElts j) ⟹ x ∈ filter (insert l_j (firstNElts j))
    rintro (h_eq | ⟨h_in_old, h_x_max⟩)
    · -- x = l_j case
      refine ⟨Or.inl h_eq, ?_⟩
      intros hx_in_s h_max_in_new
      subst h_eq  -- substitute x → nthSorted s j hj everywhere
      rcases h_max_in_new with h_max_eq | h_max_in_old
      · -- blockMaxOf' π (nthSorted ...) hx_in_s = l_j: contradicts no_block_max_eq_l_j
        exact no_block_max_eq_l_j_of_not_blockMax π j hj h (nthSorted s j hj) hx_in_s h_max_eq
      · -- blockMaxOf' π (nthSorted ...) hx_in_s ∈ firstNElts j: contradicts blockMaxOf' ≥ l_j
        have h_bm_gt_l_j : nthSorted s j hj < blockMaxOf' π (nthSorted s j hj) hx_in_s := by
          convert h_l_j_max_gt
        exact not_mem_firstNElts_of_ge j hj (le_of_lt h_bm_gt_l_j) h_max_in_old
    · -- x ∈ filter (firstNElts j): still satisfies for (insert l_j (firstNElts j))
      refine ⟨Or.inr h_in_old, ?_⟩
      intros hx_in_s h_max_in_new
      rcases h_max_in_new with h_max_eq | h_max_in_old
      · -- blockMaxOf' π x hx_in_s = l_j: contradicts no_block_max_eq_l_j
        exact no_block_max_eq_l_j_of_not_blockMax π j hj h x hx_in_s h_max_eq
      · -- blockMaxOf' π x hx_in_s ∈ firstNElts j: contradicts h_x_max
        exact h_x_max hx_in_s h_max_in_old

/-! ### blockMaxOf' equals a block-max iff in that part -/

/-- `blockMaxOf' π x hx = b` (for `b` block-max) iff `x ∈ π.val.part b`. -/
theorem blockMaxOf'_eq_iff_mem_part (π : NC s) {x b : α} (hx : x ∈ s) (hb : b ∈ s)
    (h_bm : b ∈ blockMaxes π) :
    blockMaxOf' π x hx = b ↔ x ∈ π.val.part b := by
  rw [mem_blockMaxes_iff_isBlockMax] at h_bm
  obtain ⟨_, h_part_max⟩ := h_bm
  constructor
  · intro h_eq
    have h_max_mem : blockMaxOf' π x hx ∈ π.val.part x := blockMaxOf'_mem_part π x hx
    rw [h_eq] at h_max_mem
    -- h_max_mem : b ∈ π.val.part x; conclude π.val.part x = π.val.part b.
    have h_part_x_mem : π.val.part x ∈ π.val.parts := π.val.part_mem.mpr hx
    have h_part_b_mem : π.val.part b ∈ π.val.parts := π.val.part_mem.mpr hb
    have h_b_in_part_b : b ∈ π.val.part b := π.val.mem_part_self.mpr hb
    by_contra h_ne
    have h_disj := π.val.disjoint h_part_x_mem h_part_b_mem
      (fun h_eq2 => h_ne (h_eq2 ▸ π.val.mem_part_self.mpr hx))
    exact Finset.disjoint_left.mp h_disj h_max_mem h_b_in_part_b
  · intro h_in_part
    have h_part_eq : π.val.part x = π.val.part b :=
      π.val.part_eq_of_mem (π.val.part_mem.mpr hb) h_in_part
    unfold blockMaxOf'
    -- Goal: (π.val.part x).max' ⟨x, ...⟩ = b
    apply le_antisymm
    · apply (π.val.part x).max'_le _ _
      intros k hk
      rw [h_part_eq] at hk
      exact h_part_max k hk
    · apply (π.val.part x).le_max' b
      rw [h_part_eq]
      exact π.val.mem_part_self.mpr hb

/-! ### expectedStackSet successor: BM case (PROVEN) -/

/-- For `l_j ∈ blockMaxes π`: `expectedStackSet π (j+1) = expectedStackSet π j \ π.val.part l_j`.

When `l_j` is a block-max, processing it pops the elements of `part π l_j \ {l_j}`
(which are exactly the elements of `expectedStackSet π j` with `blockMaxOf' = l_j`).
Additionally, `l_j` itself is processed (pushed then popped), so it's not in the
new stack set either.

Note: for `x ∈ expectedStackSet π j`, `x ≠ l_j` (since `l_j ∉ firstNElts s j`),
so `expectedStackSet π j \ π.val.part l_j = expectedStackSet π j \ (π.val.part l_j \ {l_j})`. -/
theorem expectedStackSet_succ_blockMax (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∈ blockMaxes π) :
    expectedStackSet π (j + 1) =
      expectedStackSet π j \ π.val.part (nthSorted s j hj) := by
  have h_l_j_in_s : nthSorted s j hj ∈ s := nthSorted_mem j hj
  have h_l_j_blockmax_eq : blockMaxOf' π (nthSorted s j hj) h_l_j_in_s = nthSorted s j hj := by
    rw [← mem_blockMaxes_iff_blockMaxOf'_eq π _ h_l_j_in_s]
    exact h
  unfold expectedStackSet
  apply Finset.ext
  intro x
  rw [firstNElts_succ' j hj]
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_sdiff]
  constructor
  · -- x in filter (insert l_j (firstNElts j)) ⟹ x ∈ filter (firstNElts j) AND x ∉ part l_j
    rintro ⟨h_x_in, h_x_max⟩
    rcases h_x_in with h_eq | h_in_old
    · -- x = l_j: but l_j has blockMaxOf' = l_j ∈ insert l_j (firstNElts j). So h_x_max fails.
      exfalso
      apply h_x_max (h_eq ▸ h_l_j_in_s)
      left
      -- blockMaxOf' π l_j _ = l_j
      have := h_l_j_blockmax_eq
      -- Want: blockMaxOf' π x (h_eq ▸ h_l_j_in_s) = nthSorted s j hj
      subst h_eq
      exact h_l_j_blockmax_eq
    · -- x ∈ firstNElts j
      refine ⟨⟨h_in_old, ?_⟩, ?_⟩
      · -- blockMaxOf' π x hx ∉ firstNElts j
        intros hx_in_s h_max_in_old
        apply h_x_max hx_in_s
        right; exact h_max_in_old
      · -- x ∉ part π l_j
        intro h_in_part
        -- x ∈ part π l_j ⟹ blockMaxOf' π x = l_j.
        have h_x_in_s := firstNElts_subset s j h_in_old
        have h_bm_eq_l_j : blockMaxOf' π x h_x_in_s = nthSorted s j hj :=
          (blockMaxOf'_eq_iff_mem_part π h_x_in_s h_l_j_in_s h).mpr h_in_part
        -- h_x_max says blockMaxOf' x ∉ insert l_j (firstNElts j). With blockMaxOf' = l_j, contradicts.
        apply h_x_max h_x_in_s
        left
        exact h_bm_eq_l_j
  · -- x ∈ expectedStackSet j AND x ∉ part π l_j ⟹ x ∈ expectedStackSet (j+1)
    rintro ⟨⟨h_in_old, h_x_max⟩, h_x_not_in_part⟩
    refine ⟨Or.inr h_in_old, ?_⟩
    intros hx_in_s h_max_in_new
    rcases h_max_in_new with h_max_eq | h_max_in_old
    · -- blockMaxOf' π x hx_in_s = l_j ⟹ x ∈ part π l_j. Contradicts h_x_not_in_part.
      apply h_x_not_in_part
      exact (blockMaxOf'_eq_iff_mem_part π hx_in_s h_l_j_in_s h).mp h_max_eq
    · -- blockMaxOf' π x hx_in_s ∈ firstNElts j: contradicts h_x_max
      exact h_x_max hx_in_s h_max_in_old

/-! ### LIFO order: expectedStackList

We now define the LIFO order on the stack: at step `j`, the stack is
`expectedStackSet π j` sorted in **descending** order (top = head = largest
value). Pushes happen in ascending value order, so the top of the stack is
always the most recently pushed element. -/

/-- The expected stack contents at step `j`, as a list in LIFO order
(top = head, descending order). -/
noncomputable def expectedStackList (π : NC s) (j : ℕ) : List α :=
  (expectedStackSet π j).sort (· ≥ ·)

/-- For `j = 0`: empty stack list. -/
theorem expectedStackList_zero (π : NC s) :
    expectedStackList π 0 = [] := by
  unfold expectedStackList
  rw [expectedStackSet_zero]
  exact Finset.sort_empty _

/-- `(expectedStackList π j).toFinset = expectedStackSet π j`. -/
theorem expectedStackList_toFinset (π : NC s) (j : ℕ) :
    (expectedStackList π j).toFinset = expectedStackSet π j := by
  unfold expectedStackList
  exact Finset.sort_toFinset _ _

/-- `expectedStackList π j` has no duplicates. -/
theorem expectedStackList_nodup (π : NC s) (j : ℕ) :
    (expectedStackList π j).Nodup := by
  unfold expectedStackList
  exact Finset.sort_nodup _ _

/-- `expectedStackList π j` has length `(expectedStackSet π j).card`. -/
theorem expectedStackList_length (π : NC s) (j : ℕ) :
    (expectedStackList π j).length = (expectedStackSet π j).card := by
  unfold expectedStackList
  exact Finset.length_sort _

/-- `x ∈ expectedStackList π j ↔ x ∈ expectedStackSet π j`. -/
theorem mem_expectedStackList_iff (π : NC s) (j : ℕ) {x : α} :
    x ∈ expectedStackList π j ↔ x ∈ expectedStackSet π j := by
  unfold expectedStackList
  exact Finset.mem_sort _

/-! ### Non-BM push case: expectedStackList grows by cons -/

/-- Every element of `expectedStackSet π j` is in `firstNElts s j`. -/
theorem expectedStackSet_subset_firstNElts (π : NC s) (j : ℕ) :
    expectedStackSet π j ⊆ firstNElts s j := by
  intro x hx
  unfold expectedStackSet at hx
  rw [Finset.mem_filter] at hx
  exact hx.1

/-- Every element of `expectedStackSet π j` is `< nthSorted s j hj`. -/
theorem expectedStackSet_lt_nthSorted (π : NC s) (j : ℕ) (hj : j < s.card)
    {x : α} (hx : x ∈ expectedStackSet π j) :
    x < nthSorted s j hj :=
  mem_firstNElts_lt_nthSorted j hj (expectedStackSet_subset_firstNElts π j hx)

/-- For `l_j ∉ blockMaxes π`: `expectedStackList π (j+1) = l_j :: expectedStackList π j`. -/
theorem expectedStackList_succ_not_blockMax (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∉ blockMaxes π) :
    expectedStackList π (j + 1) =
      nthSorted s j hj :: expectedStackList π j := by
  unfold expectedStackList
  rw [expectedStackSet_succ_not_blockMax π j hj h]
  -- Goal: (insert l_j (expectedStackSet π j)).sort (· ≥ ·) = l_j :: (expectedStackSet π j).sort (· ≥ ·)
  apply Finset.sort_insert
  · -- ∀ b ∈ expectedStackSet π j, l_j ≥ b
    intros b hb
    exact le_of_lt (expectedStackSet_lt_nthSorted π j hj hb)
  · -- l_j ∉ expectedStackSet π j
    intro h_in
    exact getElem_not_mem_firstNElts j hj (expectedStackSet_subset_firstNElts π j h_in)

/-! ### Auxiliary: characterization of firstNElts -/

/-- An element `x ∈ s` is in `firstNElts s j` iff `x < nthSorted s j hj`. -/
theorem mem_firstNElts_of_lt_nthSorted (j : ℕ) (hj : j < s.card)
    {x : α} (hx_in_s : x ∈ s) (hx_lt : x < nthSorted s j hj) :
    x ∈ firstNElts s j := by
  unfold firstNElts
  rw [List.mem_toFinset]
  have h_x_in_sort : x ∈ s.sort (· ≤ ·) := (Finset.mem_sort _).mpr hx_in_s
  rw [List.mem_iff_getElem] at h_x_in_sort
  obtain ⟨n, hn, hx_eq⟩ := h_x_in_sort
  -- hn : n < (s.sort _).length
  have h_sort_j_lt : j < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hj
  have h_n_lt_j : n < j := by
    by_contra h_n_ge
    push Not at h_n_ge
    -- h_n_ge : j ≤ n. So sort[j] ≤ sort[n] (sorted), i.e., nthSorted ≤ x.
    have h_sort_le : (s.sort (· ≤ ·))[j]'h_sort_j_lt ≤ (s.sort (· ≤ ·))[n]'hn := by
      have h_sorted := Finset.pairwise_sort s (· ≤ ·)
      exact h_sorted.rel_get_of_le (a := ⟨j, h_sort_j_lt⟩) (b := ⟨n, hn⟩) h_n_ge
    rw [hx_eq] at h_sort_le
    unfold nthSorted at hx_lt
    exact absurd h_sort_le (not_le.mpr hx_lt)
  rw [List.mem_take_iff_getElem]
  refine ⟨n, ?_, hx_eq⟩
  rw [Nat.lt_min]
  exact ⟨h_n_lt_j, hn⟩

/-! ### Block-max part minus its max is contained in expectedStackSet -/

/-- For `l_j ∈ blockMaxes π`: `part π l_j \ {l_j} ⊆ expectedStackSet π j`. -/
theorem part_subset_expectedStackSet (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∈ blockMaxes π) :
    π.val.part (nthSorted s j hj) \ {nthSorted s j hj} ⊆ expectedStackSet π j := by
  intros x hx
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
  obtain ⟨h_x_in_part, h_x_ne⟩ := hx
  have h_l_j_in_s : nthSorted s j hj ∈ s := nthSorted_mem j hj
  have h_x_in_s : x ∈ s := π.val.subset (π.val.part_mem.mpr h_l_j_in_s) h_x_in_part
  -- x ≤ l_j (l_j is max of its block).
  have h_x_le_l_j : x ≤ nthSorted s j hj := by
    rw [mem_blockMaxes_iff_isBlockMax] at h
    obtain ⟨_, h_max_prop⟩ := h
    exact h_max_prop x h_x_in_part
  have h_x_lt : x < nthSorted s j hj := lt_of_le_of_ne h_x_le_l_j h_x_ne
  have h_x_in_first : x ∈ firstNElts s j :=
    mem_firstNElts_of_lt_nthSorted j hj h_x_in_s h_x_lt
  unfold expectedStackSet
  rw [Finset.mem_filter]
  refine ⟨h_x_in_first, ?_⟩
  intros hx_in_s_arg
  -- blockMaxOf' π x hx_in_s_arg = l_j (proof irrelevance for the membership).
  have h_bm_eq : blockMaxOf' π x hx_in_s_arg = nthSorted s j hj :=
    (blockMaxOf'_eq_iff_mem_part π hx_in_s_arg h_l_j_in_s h).mpr h_x_in_part
  intro h_bm_in_first
  rw [h_bm_eq] at h_bm_in_first
  exact getElem_not_mem_firstNElts j hj h_bm_in_first

/-! ### KEY NC STRUCTURAL LEMMA: part π l_j elements top the stack

The deep non-crossing property: at step `j` with `l_j ∈ BM`, every element
of `part π l_j \ {l_j}` is strictly greater than every element of
`expectedStackSet π j \ part π l_j`.

This means in the LIFO descending stack list, `part π l_j \ {l_j}` occupies
the TOP positions, and the remaining elements occupy the BOTTOM positions.
This is the crucial fact for correctness of the pop operation. -/
theorem nc_part_top_of_blockMax (π : NC s) (j : ℕ) (hj : j < s.card)
    (h_bm : nthSorted s j hj ∈ blockMaxes π)
    {x : α} (hx_part : x ∈ π.val.part (nthSorted s j hj)) (hx_ne : x ≠ nthSorted s j hj)
    {y : α} (hy_stack : y ∈ expectedStackSet π j)
    (hy_not_part : y ∉ π.val.part (nthSorted s j hj)) :
    y < x := by
  have h_l_j_in_s : nthSorted s j hj ∈ s := nthSorted_mem j hj
  have h_x_in_s : x ∈ s := π.val.subset (π.val.part_mem.mpr h_l_j_in_s) hx_part
  have h_y_stack_set := hy_stack
  unfold expectedStackSet at h_y_stack_set
  rw [Finset.mem_filter] at h_y_stack_set
  obtain ⟨h_y_in_first, h_y_max⟩ := h_y_stack_set
  have h_y_in_s : y ∈ s := firstNElts_subset s j h_y_in_first
  -- x ≠ y since x ∈ part π l_j, y ∉.
  have h_x_ne_y : x ≠ y := fun h_eq => hy_not_part (h_eq ▸ hx_part)
  -- y < l_j (sorted order).
  have h_y_lt_l_j : y < nthSorted s j hj := mem_firstNElts_lt_nthSorted j hj h_y_in_first
  -- x < l_j.
  have h_x_lt_l_j : x < nthSorted s j hj := by
    rw [mem_blockMaxes_iff_isBlockMax] at h_bm
    obtain ⟨_, h_max_prop⟩ := h_bm
    exact lt_of_le_of_ne (h_max_prop x hx_part) hx_ne
  -- by contradiction y ≥ x.
  by_contra h_not_lt
  push Not at h_not_lt
  have h_x_lt_y : x < y := lt_of_le_of_ne h_not_lt h_x_ne_y
  -- blockMaxOf' y > l_j: since blockMaxOf' y ∉ firstNElts j and ≠ l_j (else y ∈ part π l_j).
  have h_bm_y_def := blockMaxOf'_mem_part π y h_y_in_s
  have h_bm_y_ne_l_j : blockMaxOf' π y h_y_in_s ≠ nthSorted s j hj := by
    intro h_eq
    apply hy_not_part
    have h_bm_in : nthSorted s j hj ∈ blockMaxes π := h_bm
    exact (blockMaxOf'_eq_iff_mem_part π h_y_in_s h_l_j_in_s h_bm_in).mp h_eq
  have h_bm_y_not_in_first : blockMaxOf' π y h_y_in_s ∉ firstNElts s j := h_y_max h_y_in_s
  have h_bm_y_in_s : blockMaxOf' π y h_y_in_s ∈ s := blockMaxOf'_mem_s π y h_y_in_s
  have h_bm_y_gt_l_j : nthSorted s j hj < blockMaxOf' π y h_y_in_s := by
    by_contra h_not_gt
    push Not at h_not_gt
    rcases lt_or_eq_of_le h_not_gt with h_lt | h_eq
    · apply h_bm_y_not_in_first
      exact mem_firstNElts_of_lt_nthSorted j hj h_bm_y_in_s h_lt
    · exact h_bm_y_ne_l_j h_eq
  -- NC violation: x < y < l_j < bm_y, with x, l_j ∈ A and y, bm_y ∈ B, A ≠ B.
  -- Apply π.property (= IsNoncrossing) to conclude A = B.
  -- Then deduce y ∈ A = part π l_j, contradicting hy_not_part.
  set A := π.val.part (nthSorted s j hj) with hA_def
  set B := π.val.part y with hB_def
  have h_l_j_in_A : nthSorted s j hj ∈ A := π.val.mem_part_self.mpr h_l_j_in_s
  have h_y_in_B : y ∈ B := π.val.mem_part_self.mpr h_y_in_s
  have h_A_part : A ∈ π.val.parts := π.val.part_mem.mpr h_l_j_in_s
  have h_B_part : B ∈ π.val.parts := π.val.part_mem.mpr h_y_in_s
  -- Apply noncrossing: i = x, j = y, k = l_j, l = bm_y.
  have h_A_eq_B : A = B :=
    π.property h_A_part h_B_part h_x_lt_y h_y_lt_l_j h_bm_y_gt_l_j
      hx_part h_l_j_in_A h_y_in_B h_bm_y_def
  -- Then y ∈ A = part π l_j, contradicting hy_not_part.
  apply hy_not_part
  show y ∈ A
  rw [h_A_eq_B]
  exact h_y_in_B

/-! ### Generic sort lemma: top |A| of sort_desc B = sort_desc A -/

/-- If `A ⊆ B` and `A` consists of the `|A|` largest elements of `B`
(every element of `A` is strictly greater than every element of `B \ A`),
then the descending sort of `B` decomposes as `A.sort (· ≥ ·) ++ (B \ A).sort (· ≥ ·)`. -/
theorem sort_ge_append_of_top {B A : Finset α} (h_sub : A ⊆ B)
    (h_top : ∀ a ∈ A, ∀ b ∈ B \ A, b < a) :
    B.sort (· ≥ ·) = A.sort (· ≥ ·) ++ (B \ A).sort (· ≥ ·) := by
  have h_disj : Disjoint A (B \ A) := Finset.disjoint_sdiff
  have h_union : A ∪ (B \ A) = B := Finset.union_sdiff_of_subset h_sub
  refine List.Perm.eq_of_sortedGE ?_ ?_ ?_
  · -- sortedGE of LHS (B.sort (· ≥ ·))
    exact (Finset.pairwise_sort _ _).sortedGE
  · -- sortedGE of RHS (A.sort (· ≥ ·) ++ (B \ A).sort (· ≥ ·))
    apply List.Pairwise.sortedGE
    rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort _ _, Finset.pairwise_sort _ _, ?_⟩
    intros a ha b hb
    rw [Finset.mem_sort] at ha hb
    exact le_of_lt (h_top a ha b hb)
  · -- Perm
    rw [← Multiset.coe_eq_coe]
    show ((B.sort (· ≥ ·) : List α) : Multiset α) =
         ((A.sort (· ≥ ·) ++ (B \ A).sort (· ≥ ·) : List α) : Multiset α)
    rw [← Multiset.coe_add]
    simp only [Finset.sort_eq]
    -- Goal: B.val = A.val + (B \ A).val
    rw [Multiset.add_eq_union_iff_disjoint.mpr (Finset.disjoint_val.mpr h_disj)]
    rw [← Finset.union_val, h_union]

/-! ### Application: top of expectedStackList = part π l_j \ {l_j} -/

/-- The descending sort split: for `l_j ∈ blockMaxes π`, the descending sort of
`expectedStackSet π j` splits as `(part π l_j \ {l_j}).sort_desc ++ (expectedStackSet π (j+1)).sort_desc`. -/
theorem expectedStackList_split_at_blockMax (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∈ blockMaxes π) :
    expectedStackList π j =
      (π.val.part (nthSorted s j hj) \ {nthSorted s j hj}).sort (· ≥ ·) ++
      expectedStackList π (j + 1) := by
  unfold expectedStackList
  -- Need: expectedStackSet π j sort_desc = (part \ {l_j}) sort_desc ++ expectedStackSet π (j+1) sort_desc.
  -- Use sort_ge_append_of_top with A = part \ {l_j}, B = expectedStackSet π j.
  -- Then expectedStackSet π (j+1) = B \ A.
  have h_sub : π.val.part (nthSorted s j hj) \ {nthSorted s j hj} ⊆ expectedStackSet π j :=
    part_subset_expectedStackSet π j hj h
  have h_top : ∀ a ∈ π.val.part (nthSorted s j hj) \ {nthSorted s j hj},
      ∀ b ∈ expectedStackSet π j \ (π.val.part (nthSorted s j hj) \ {nthSorted s j hj}), b < a := by
    intros a ha b hb
    rw [Finset.mem_sdiff, Finset.mem_singleton] at ha
    obtain ⟨h_a_in_part, h_a_ne⟩ := ha
    rw [Finset.mem_sdiff] at hb
    obtain ⟨h_b_in_B, h_b_not_A⟩ := hb
    -- b ∉ part π l_j (else b = l_j or b ∈ A, both contradict).
    have h_b_not_part : b ∉ π.val.part (nthSorted s j hj) := by
      intro h_b_in_part
      by_cases h_b_eq : b = nthSorted s j hj
      · have h_b_in_first := expectedStackSet_subset_firstNElts π j h_b_in_B
        rw [h_b_eq] at h_b_in_first
        exact getElem_not_mem_firstNElts j hj h_b_in_first
      · apply h_b_not_A
        rw [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨h_b_in_part, h_b_eq⟩
    exact nc_part_top_of_blockMax π j hj h h_a_in_part h_a_ne h_b_in_B h_b_not_part
  rw [sort_ge_append_of_top h_sub h_top]
  congr 1
  -- Goal: (expectedStackSet π j \ (part π l_j \ {l_j})).sort _ = (expectedStackSet π (j+1)).sort _
  congr 1
  -- Goal: expectedStackSet π j \ (part π l_j \ {l_j}) = expectedStackSet π (j+1)
  rw [expectedStackSet_succ_blockMax π j hj h]
  -- Goal: expectedStackSet π j \ (part π l_j \ {l_j}) = expectedStackSet π j \ part π l_j
  apply Finset.ext
  intro x
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨h_x_in_B, h_x_not_A⟩
    refine ⟨h_x_in_B, ?_⟩
    intro h_x_in_part
    by_cases h_x_eq : x = nthSorted s j hj
    · subst h_x_eq
      exact getElem_not_mem_firstNElts j hj (expectedStackSet_subset_firstNElts π j h_x_in_B)
    · exact h_x_not_A ⟨h_x_in_part, h_x_eq⟩
  · rintro ⟨h_x_in_B, h_x_not_part⟩
    refine ⟨h_x_in_B, ?_⟩
    rintro ⟨h_x_in_part, _⟩
    exact h_x_not_part h_x_in_part

/-! ### BM successor case for expectedStackList -/

/-- For `l_j ∈ blockMaxes π`: `expectedStackList π (j+1) = (expectedStackList π j).drop (|part π l_j| - 1)`.
This is the **POP STEP** at the LIFO level: when `l_j` is a block-max, the top
`|part π l_j| - 1` elements of the stack are exactly `part π l_j \ {l_j}` (by NC
structural fact), and after pushing `l_j` and popping `|part π l_j|`, the
remaining stack is the bottom of the original stack. -/
theorem expectedStackList_succ_blockMax (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∈ blockMaxes π) :
    expectedStackList π (j + 1) =
      (expectedStackList π j).drop ((π.val.part (nthSorted s j hj)).card - 1) := by
  rw [expectedStackList_split_at_blockMax π j hj h]
  -- Goal: expectedStackList π (j+1) = ((part \ {l_j}).sort _ ++ expectedStackList π (j+1)).drop n
  -- where n = (part π l_j).card - 1.
  have h_card_eq : (π.val.part (nthSorted s j hj)).card - 1 =
      ((π.val.part (nthSorted s j hj) \ {nthSorted s j hj}).sort (· ≥ ·)).length := by
    rw [Finset.length_sort, Finset.card_sdiff_of_subset
      (by rw [Finset.singleton_subset_iff]; exact π.val.mem_part_self.mpr (nthSorted_mem j hj)),
      Finset.card_singleton]
  rw [h_card_eq, List.drop_append_length]

/-! ### Reconstruction state invariant -/

/-- The reconstruction state after processing the first `j` elements of `s.sort`. -/
noncomputable def reconstructStateAt (π : NC s) (j : ℕ) : RecState α :=
  ((s.sort (· ≤ ·)).take j).foldl
    (reconstructStep (blockMaxes π) (fun i => (π.val.part i).card))
    (RecState.empty α)

/-- Initial state at step 0 is empty. -/
theorem reconstructStateAt_zero (π : NC s) :
    reconstructStateAt π 0 = RecState.empty α := by
  unfold reconstructStateAt
  simp

/-- Successor formula: state at `j+1` is one `reconstructStep` from state at `j`. -/
theorem reconstructStateAt_succ (π : NC s) (j : ℕ) (hj : j < s.card) :
    reconstructStateAt π (j + 1) =
      reconstructStep (blockMaxes π) (fun i => (π.val.part i).card)
        (reconstructStateAt π j) (nthSorted s j hj) := by
  unfold reconstructStateAt
  have h_sort_len : j < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hj
  rw [List.take_succ_eq_append_getElem h_sort_len, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

/-! ### Key NC fact: part π l_j ∉ expectedBlocksSet π j when l_j ∈ BM -/

/-- For `l_j ∈ blockMaxes π`: `part π l_j ∉ expectedBlocksSet π j`. -/
theorem part_not_mem_expectedBlocksSet (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∈ blockMaxes π) :
    π.val.part (nthSorted s j hj) ∉ expectedBlocksSet π j := by
  intro h_in
  unfold expectedBlocksSet at h_in
  rw [Finset.mem_filter] at h_in
  obtain ⟨_, h_ne, h_max_in⟩ := h_in
  -- The max of part π l_j is l_j (since l_j ∈ BM), and l_j ∉ firstNElts j.
  have h_l_j_in_s : nthSorted s j hj ∈ s := nthSorted_mem j hj
  have h_max_eq : (π.val.part (nthSorted s j hj)).max' h_ne = nthSorted s j hj := by
    rw [mem_blockMaxes_iff_isBlockMax] at h
    obtain ⟨_, h_max_prop⟩ := h
    apply le_antisymm
    · exact (π.val.part (nthSorted s j hj)).max'_le _ _ h_max_prop
    · exact (π.val.part (nthSorted s j hj)).le_max' _ (π.val.mem_part_self.mpr h_l_j_in_s)
  rw [h_max_eq] at h_max_in
  exact getElem_not_mem_firstNElts j hj h_max_in

/-! ### Helpers for the BM case (push + take/drop produces correct block) -/

/-- Helper: cons-cons-rearrangement using the LIFO split. -/
theorem cons_expectedStackList_eq_at_blockMax (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∈ blockMaxes π) :
    nthSorted s j hj :: expectedStackList π j =
    (nthSorted s j hj ::
      (π.val.part (nthSorted s j hj) \ {nthSorted s j hj}).sort (· ≥ ·)) ++
    expectedStackList π (j + 1) := by
  rw [expectedStackList_split_at_blockMax π j hj h]
  rfl

/-- Helper: length of the "head" list = part.card (needed for take/drop). -/
theorem cons_part_minus_singleton_length (π : NC s) (j : ℕ) (hj : j < s.card) :
    (nthSorted s j hj ::
      (π.val.part (nthSorted s j hj) \ {nthSorted s j hj}).sort (· ≥ ·)).length =
    (π.val.part (nthSorted s j hj)).card := by
  have h_l_j_mem : nthSorted s j hj ∈ π.val.part (nthSorted s j hj) :=
    π.val.mem_part_self.mpr (nthSorted_mem j hj)
  have h_subset_singleton : ({nthSorted s j hj} : Finset α) ⊆ π.val.part (nthSorted s j hj) :=
    Finset.singleton_subset_iff.mpr h_l_j_mem
  have h_card_pos : 0 < (π.val.part (nthSorted s j hj)).card :=
    Finset.card_pos.mpr ⟨nthSorted s j hj, h_l_j_mem⟩
  rw [List.length_cons, Finset.length_sort,
    Finset.card_sdiff_of_subset h_subset_singleton, Finset.card_singleton]
  omega

/-- Helper: take part.card of push gives part π l_j as Finset. -/
theorem pop_block_eq_part (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∈ blockMaxes π) :
    ((nthSorted s j hj :: expectedStackList π j).take
      ((π.val.part (nthSorted s j hj)).card)).toFinset =
    π.val.part (nthSorted s j hj) := by
  rw [cons_expectedStackList_eq_at_blockMax π j hj h]
  rw [← cons_part_minus_singleton_length π j hj]
  rw [List.take_append_length]
  rw [List.toFinset_cons]
  rw [show ((π.val.part (nthSorted s j hj) \ {nthSorted s j hj}).sort (· ≥ ·)).toFinset =
      π.val.part (nthSorted s j hj) \ {nthSorted s j hj} from Finset.sort_toFinset _ _]
  ext x
  simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro (rfl | ⟨h_in_part, _⟩)
    · exact π.val.mem_part_self.mpr (nthSorted_mem j hj)
    · exact h_in_part
  · intro h_in_part
    by_cases h_eq : x = nthSorted s j hj
    · left; exact h_eq
    · right; exact ⟨h_in_part, h_eq⟩

/-- Helper: drop part.card of push gives expectedStackList π (j+1). -/
theorem pop_remaining_eq_next (π : NC s) (j : ℕ) (hj : j < s.card)
    (h : nthSorted s j hj ∈ blockMaxes π) :
    (nthSorted s j hj :: expectedStackList π j).drop
      ((π.val.part (nthSorted s j hj)).card) =
    expectedStackList π (j + 1) := by
  rw [cons_expectedStackList_eq_at_blockMax π j hj h]
  rw [← cons_part_minus_singleton_length π j hj]
  rw [List.drop_append_length]

/-! ### Main invariant: stack + blocks at step j -/

/-- The full state invariant: after processing `j` elements, the stack matches
the LIFO order list and the blocks match the expected block set. -/
theorem reconstructStateAt_invariant (π : NC s) (j : ℕ) (hj : j ≤ s.card) :
    (reconstructStateAt π j).stack = expectedStackList π j ∧
    (reconstructStateAt π j).blocks.toFinset = expectedBlocksSet π j ∧
    (reconstructStateAt π j).blocks.Nodup := by
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [reconstructStateAt_zero, expectedStackList_zero]
      rfl
    · rw [reconstructStateAt_zero, expectedBlocksSet_zero]
      rfl
    · rw [reconstructStateAt_zero]
      exact List.nodup_nil
  | succ j ih =>
    have hj' : j ≤ s.card := Nat.le_of_succ_le hj
    have hj'' : j < s.card := hj
    obtain ⟨ih_stack, ih_blocks, ih_nodup⟩ := ih hj'
    rw [reconstructStateAt_succ π j hj'']
    by_cases h_bm : nthSorted s j hj'' ∈ blockMaxes π
    · -- BM case: push then pop
      rw [reconstructStep_blockMax _ _ _ h_bm]
      refine ⟨?_, ?_, ?_⟩
      · -- stack equality
        change (nthSorted s j hj'' :: (reconstructStateAt π j).stack).drop _ = _
        rw [ih_stack, pop_remaining_eq_next π j hj'' h_bm]
      · -- blocks equality
        change ((reconstructStateAt π j).blocks ++ [_]).toFinset = _
        rw [List.toFinset_append, ih_blocks, ih_stack, pop_block_eq_part π j hj'' h_bm]
        rw [expectedBlocksSet_succ_blockMax π j hj'' h_bm]
        -- Goal: expectedBlocksSet π j ∪ [part π l_j].toFinset = insert (part π l_j) (expectedBlocksSet π j)
        simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
        rw [Finset.union_singleton]
      · -- Nodup of new blocks list
        change ((reconstructStateAt π j).blocks ++ [_]).Nodup
        rw [List.nodup_append]
        refine ⟨ih_nodup, List.nodup_singleton _, ?_⟩
        intros a h_a b h_b
        rw [List.mem_singleton] at h_b
        subst h_b
        intro h_eq
        -- popped.toFinset = part π l_j.
        rw [ih_stack, pop_block_eq_part π j hj'' h_bm] at h_eq
        -- a = part π l_j, but a ∈ old blocks → a ∈ expectedBlocksSet π j → part π l_j ∈ ... contradicts.
        have h_a_in_old : a ∈ (reconstructStateAt π j).blocks.toFinset :=
          List.mem_toFinset.mpr h_a
        rw [ih_blocks, h_eq] at h_a_in_old
        exact part_not_mem_expectedBlocksSet π j hj'' h_bm h_a_in_old
    · -- Non-BM case: push only
      rw [reconstructStep_not_blockMax _ _ _ h_bm]
      refine ⟨?_, ?_, ?_⟩
      · -- stack
        change nthSorted s j hj'' :: (reconstructStateAt π j).stack = _
        rw [ih_stack, expectedStackList_succ_not_blockMax π j hj'' h_bm]
      · -- blocks
        change (reconstructStateAt π j).blocks.toFinset = _
        rw [ih_blocks, expectedBlocksSet_succ_not_blockMax π j hj'' h_bm]
      · -- nodup
        change (reconstructStateAt π j).blocks.Nodup
        exact ih_nodup

/-! ### Final correctness theorem -/

/-- **MAIN THEOREM**: the reconstruction's blocks (as a Finset of Finsets)
equals `π.val.parts`. -/
theorem reconstructFromProfile_eq_parts (π : NC s) :
    (reconstructFromProfile (blockMaxes π) (fun i => (π.val.part i).card)
      (s.sort (· ≤ ·))).toFinset = π.val.parts := by
  unfold reconstructFromProfile
  -- The result is (sortedS.foldl ... empty).blocks = (reconstructStateAt π s.card).blocks.
  have h_eq : (s.sort (· ≤ ·)).foldl
      (reconstructStep (blockMaxes π) (fun i => (π.val.part i).card))
      (RecState.empty α) = reconstructStateAt π s.card := by
    unfold reconstructStateAt
    rw [List.take_of_length_le (by rw [Finset.length_sort])]
  rw [h_eq]
  obtain ⟨_, h_blocks, _⟩ := reconstructStateAt_invariant π s.card le_rfl
  rw [h_blocks]
  -- expectedBlocksSet π s.card = π.val.parts
  unfold expectedBlocksSet
  -- All parts have their max in firstNElts s s.card = s.
  apply Finset.ext
  intro B
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hB_part, _⟩
    exact hB_part
  · intro hB_part
    refine ⟨hB_part, ?_, ?_⟩
    · -- B nonempty
      exact π.val.nonempty_of_mem_parts hB_part
    · -- B.max' ∈ firstNElts s s.card = s
      have h_B_max_in_s : B.max' (π.val.nonempty_of_mem_parts hB_part) ∈ s :=
        π.val.subset hB_part (B.max'_mem _)
      -- firstNElts s s.card = s
      have h_full : firstNElts s s.card = s := by
        unfold firstNElts
        rw [List.take_of_length_le (by rw [Finset.length_sort])]
        exact Finset.sort_toFinset _ _
      rw [h_full]
      exact h_B_max_in_s

/-! ### NC injectivity from profile -/

/-- `reconstructStep` depends only on `f`'s values on `BM`. -/
theorem reconstructStep_ext (BM : Finset α) [DecidablePred (· ∈ BM)]
    (f g : α → ℕ) (h : ∀ i ∈ BM, f i = g i) (st : RecState α) (i : α) :
    reconstructStep BM f st i = reconstructStep BM g st i := by
  unfold reconstructStep
  by_cases hi : i ∈ BM
  · simp only [if_pos hi, h i hi]
  · simp only [if_neg hi]

/-- `reconstructFromProfile` depends only on `f`'s values on `BM`. -/
theorem reconstructFromProfile_ext (BM : Finset α) [DecidablePred (· ∈ BM)]
    (f g : α → ℕ) (h : ∀ i ∈ BM, f i = g i) (sortedS : List α) :
    reconstructFromProfile BM f sortedS = reconstructFromProfile BM g sortedS := by
  unfold reconstructFromProfile
  suffices h_gen : ∀ init, sortedS.foldl (reconstructStep BM f) init =
                            sortedS.foldl (reconstructStep BM g) init by
    rw [h_gen]
  intro init
  induction sortedS generalizing init with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldl_cons, List.foldl_cons, reconstructStep_ext BM f g h init head, ih]

/-- **NC INJECTIVITY FROM PROFILE**: if two NCs have the same `blockMaxes` and the
same block-sizes on those block-maxes, they are equal. -/
theorem eq_of_profile_eq (π π' : NC s)
    (h_bm : blockMaxes π = blockMaxes π')
    (h_sizes : ∀ i ∈ blockMaxes π, (π.val.part i).card = (π'.val.part i).card) :
    π = π' := by
  -- Step 1: reconstructFromProfile produces the same list for both.
  have h_recon_eq :
      reconstructFromProfile (blockMaxes π) (fun i => (π.val.part i).card) (s.sort (· ≤ ·)) =
      reconstructFromProfile (blockMaxes π') (fun i => (π'.val.part i).card) (s.sort (· ≤ ·)) := by
    rw [← h_bm]
    -- Now: reconstructFromProfile (BM π) (sizes π) ... = reconstructFromProfile (BM π) (sizes π') ...
    exact reconstructFromProfile_ext (blockMaxes π) _ _ h_sizes _
  -- Step 2: their toFinsets equal both parts.
  have h_parts_π : (reconstructFromProfile (blockMaxes π) (fun i => (π.val.part i).card)
                    (s.sort (· ≤ ·))).toFinset = π.val.parts :=
    reconstructFromProfile_eq_parts π
  have h_parts_π' : (reconstructFromProfile (blockMaxes π') (fun i => (π'.val.part i).card)
                    (s.sort (· ≤ ·))).toFinset = π'.val.parts :=
    reconstructFromProfile_eq_parts π'
  -- Step 3: parts are equal.
  have h_parts_eq : π.val.parts = π'.val.parts := by
    rw [← h_parts_π, h_recon_eq, h_parts_π']
  -- Step 4: Finpartition equality via ext.
  apply Subtype.ext
  apply Finpartition.ext
  exact h_parts_eq

end NC

end Hamilton.Infrastructure
