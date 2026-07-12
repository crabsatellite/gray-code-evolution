/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCOperations

/-!
# Nesting forest on noncrossing partitions

For an `NC α s` partition, the **nesting forest** assigns to each
non-root block `B` a *parent block* — the block containing the
predecessor of `min B` in `s`.  Root blocks are those whose `min`
has no predecessor in `s`.

This is the structural foundation for:
* The lattice-theoretic structure of `NC α s`.
* Counting NCR-neighbours of a partition (each non-root block gives
  one parent-merge).
* The Catalan recurrence on NC partitions.

## Main definitions

* `NC.parentBlock π B hne` — the parent block of `B` in `π`.
* `NC.IsRoot π B` — predicate: `B` is a root block.

## Main results

* `NC.parentBlock_mem` — for non-root `B`, `parentBlock π B ∈ π.val.parts`.
* `NC.parent_min_lt` — `min (parentBlock π B) < min B` (strict).
* `NC.parentBlock_ne_self` — the parent is distinct from `B`.

## Tags

noncrossing partition, nesting forest, parent block
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- `B` is a **root block** of `π : NC s` iff `min B` has no
predecessor in `s` — i.e., `B` contains the minimum of `s`. -/
def IsRoot (B : Finset α) (hne : B.Nonempty) : Prop :=
  ∀ q ∈ s, ¬ q < B.min' hne

instance (B : Finset α) (hne : B.Nonempty) :
    Decidable (IsRoot (s := s) B hne) := by
  unfold IsRoot; infer_instance

/-- For a non-root block, the predecessor filter is nonempty. -/
theorem filter_lt_min_nonempty_of_nonRoot {B : Finset α} (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    (s.filter (· < B.min' hne)).Nonempty := by
  by_contra h
  apply h_nonRoot
  intro q hq_in hq_lt
  apply h
  exact ⟨q, Finset.mem_filter.mpr ⟨hq_in, hq_lt⟩⟩

/-- The **parent block** of `B` in `π : NC s`: the block containing
the predecessor of `min B` in `s`, if such a predecessor exists.
For root blocks (no predecessor), returns `B` itself. -/
noncomputable def parentBlock (π : NC s) (B : Finset α)
    (hne : B.Nonempty) : Finset α :=
  if h : (s.filter (· < B.min' hne)).Nonempty then
    π.val.part ((s.filter (· < B.min' hne)).max' h)
  else
    B

/-- For a non-root block `B`, the parent block is in `π.val.parts`. -/
theorem parentBlock_mem (π : NC s) (B : Finset α) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    parentBlock π B hne ∈ π.val.parts := by
  unfold parentBlock
  rw [dif_pos (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot)]
  apply π.val.part_mem.mpr
  exact (Finset.mem_filter.mp
    ((s.filter (· < B.min' hne)).max'_mem _)).1

/-- The predecessor element is contained in `parentBlock π B`. -/
theorem parent_contains_pred (π : NC s) (B : Finset α) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    (s.filter (· < B.min' hne)).max'
      (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot) ∈
        parentBlock π B hne := by
  unfold parentBlock
  rw [dif_pos (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot)]
  apply π.val.mem_part_self.mpr
  exact (Finset.mem_filter.mp
    ((s.filter (· < B.min' hne)).max'_mem _)).1

/-- For a non-root block `B`, the parent block is *distinct* from `B`. -/
theorem parentBlock_ne_self (π : NC s) (B : Finset α) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    parentBlock π B hne ≠ B := by
  intro hpart_eq
  have h_pred_in_par := parent_contains_pred π B hne h_nonRoot
  rw [hpart_eq] at h_pred_in_par
  -- pred ∈ B, so pred ≥ min B.  But pred < min B by definition of the filter.
  have h_pred_ge : B.min' hne ≤
      (s.filter (· < B.min' hne)).max'
        (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot) :=
    B.min'_le _ h_pred_in_par
  have h_pred_lt : (s.filter (· < B.min' hne)).max'
      (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot) < B.min' hne :=
    (Finset.mem_filter.mp
      ((s.filter (· < B.min' hne)).max'_mem _)).2
  exact absurd (lt_of_le_of_lt h_pred_ge h_pred_lt) (lt_irrefl _)

/-- The min of `parentBlock π B` is strictly less than `min B`
for non-root `B`. -/
theorem parent_min_lt (π : NC s) (B : Finset α) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    ∃ hne_par : (parentBlock π B hne).Nonempty,
      (parentBlock π B hne).min' hne_par < B.min' hne := by
  have h_pred_in_par := parent_contains_pred π B hne h_nonRoot
  have hne_par : (parentBlock π B hne).Nonempty :=
    ⟨_, h_pred_in_par⟩
  refine ⟨hne_par, ?_⟩
  have h_min_le_pred : (parentBlock π B hne).min' hne_par ≤
      (s.filter (· < B.min' hne)).max'
        (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot) :=
    (parentBlock π B hne).min'_le _ h_pred_in_par
  have h_pred_lt : (s.filter (· < B.min' hne)).max'
      (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot) < B.min' hne :=
    (Finset.mem_filter.mp
      ((s.filter (· < B.min' hne)).max'_mem _)).2
  exact lt_of_le_of_lt h_min_le_pred h_pred_lt



theorem parentBlock_nests_or_disjoint_below (π : NC s) (B : Finset α)
    (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    let hne_par : (parentBlock π B hne).Nonempty :=
      (parent_min_lt π B hne h_nonRoot).fst
    (B.max' hne ≤ (parentBlock π B hne).max' hne_par) ∨
    ((parentBlock π B hne).max' hne_par < B.min' hne) := by
  intro hne_par
  -- Let p = predecessor of min B, parent = block containing p.
  set p := (s.filter (· < B.min' hne)).max'
    (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot) with hp_def
  set par := parentBlock π B hne with hpar_def
  have hp_in_par : p ∈ par := parent_contains_pred π B hne h_nonRoot
  have hp_lt_min : p < B.min' hne := (Finset.mem_filter.mp
    ((s.filter (· < B.min' hne)).max'_mem _)).2
  have hpar_mem : par ∈ π.val.parts := parentBlock_mem π B hne h_nonRoot
  have hpar_ne_B : par ≠ B := parentBlock_ne_self π B hne h_nonRoot
  -- Suppose for contradiction: par.max' is in the "middle" range
  -- B.min' ≤ par.max' < B.max'.  This forces a crossing.
  by_contra h_neither
  push_neg at h_neither
  -- h_neither (after push_neg) : par.max' < B.max' ∧ B.min' ≤ par.max'
  have h_par_max_lt_or_eq : (parentBlock π B hne).max' hne_par < B.max' hne :=
    h_neither.1
  have h_par_max_ge_min : B.min' hne ≤ (parentBlock π B hne).max' hne_par :=
    h_neither.2
  -- Now we have: B.min' ≤ par.max' < B.max'. Set up crossing:
  -- a = p ∈ par (a < B.min')
  -- b = B.min' ∈ B
  -- c = par.max' ∈ par (B.min' ≤ c < B.max')
  -- d = B.max' ∈ B (c < d)
  -- Pattern: par-B-par-B = crossing.
  have h_max_in_par : par.max' hne_par ∈ par := par.max'_mem _
  have h_par_max_ne_min : par.max' hne_par ≠ B.min' hne := by
    intro h_eq
    -- If par.max' = B.min', then B.min' ∈ par. But B.min' ∈ B and par ≠ B.
    have h_min_in_par : B.min' hne ∈ par := h_eq ▸ h_max_in_par
    have h_min_in_B : B.min' hne ∈ B := B.min'_mem hne
    have h_disjoint := π.val.disjoint hpar_mem hB_mem hpar_ne_B
    exact (Finset.disjoint_left.mp h_disjoint h_min_in_par) h_min_in_B
  have h_par_max_gt_min : B.min' hne < par.max' hne_par :=
    lt_of_le_of_ne h_par_max_ge_min (Ne.symm h_par_max_ne_min)
  -- Apply NC of π to a < b < c < d with a, c ∈ par and b, d ∈ B.
  -- Pattern: p ∈ par, B.min' ∈ B, par.max' ∈ par, B.max' ∈ B.
  -- Need: p < B.min' < par.max' < B.max'.
  -- p < B.min': from hp_lt_min.
  -- B.min' < par.max': from h_par_max_gt_min.
  -- par.max' < B.max': from h_par_max_lt_or_eq.
  have h_eq_BC := π.property hpar_mem hB_mem
    hp_lt_min h_par_max_gt_min h_par_max_lt_or_eq
    hp_in_par h_max_in_par
    (B.min'_mem hne) (B.max'_mem hne)
  exact hpar_ne_B h_eq_BC

/-- **Nested-parent interval containment**: in the nested case, the
parent's `[min, max]` interval contains all of `B`'s `[min, max]`
interval.

For any element `x` of `s` with `B.min' ≤ x ≤ B.max'`, the parent's
interval also contains `x` (as a NUMERIC range, not as
membership in the block). -/
theorem parentBlock_interval_contains_of_nested (π : NC s) (B : Finset α)
    (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne)
    (h_nested :
      let hne_par := (parent_min_lt π B hne h_nonRoot).fst
      B.max' hne ≤ (parentBlock π B hne).max' hne_par) :
    let hne_par := (parent_min_lt π B hne h_nonRoot).fst
    (parentBlock π B hne).min' hne_par < B.min' hne ∧
    B.max' hne ≤ (parentBlock π B hne).max' hne_par := by
  intro hne_par
  refine ⟨?_, h_nested⟩
  exact (parent_min_lt π B hne h_nonRoot).snd

/-- **Disjoint-below interval separation**: in the disjoint-below case,
the parent's interval is entirely below `B`'s. -/
theorem parentBlock_interval_disjoint_below (π : NC s) (B : Finset α)
    (hne : B.Nonempty) (h_nonRoot : ¬ IsRoot (s := s) B hne)
    (h_disj :
      let hne_par := (parent_min_lt π B hne h_nonRoot).fst
      (parentBlock π B hne).max' hne_par < B.min' hne) :
    let hne_par := (parent_min_lt π B hne h_nonRoot).fst
    (parentBlock π B hne).min' hne_par < B.min' hne ∧
    (parentBlock π B hne).max' hne_par < B.min' hne := by
  intro hne_par
  refine ⟨(parent_min_lt π B hne h_nonRoot).snd, h_disj⟩

/-- **DISJOINT-BELOW: parent's max equals predecessor of B.min**.

In the DISJOINT-BELOW case, `parent.max' = predecessor of B.min' in
s` — the largest `s`-element strictly less than `B.min'`.

Proof: predecessor ∈ parent (`parent_contains_pred`) gives
`predecessor ≤ parent.max'`. Conversely, parent.max' < B.min'
(`h_disj`) and parent.max' ∈ s (since `parent ⊆ s`), so parent.max'
is in `s.filter (· < B.min')`, hence parent.max' ≤ predecessor (the
filter's max). Antisymmetry closes. -/
theorem parentBlock_max_eq_predecessor_of_disjoint_below
    (π : NC s) (B : Finset α) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne)
    (h_disj :
      have hne_par : (parentBlock π B hne).Nonempty :=
        (parent_min_lt π B hne h_nonRoot).fst
      (parentBlock π B hne).max' hne_par < B.min' hne) :
    have hne_par : (parentBlock π B hne).Nonempty :=
      (parent_min_lt π B hne h_nonRoot).fst
    (parentBlock π B hne).max' hne_par =
      (s.filter (· < B.min' hne)).max'
        (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot) := by
  have hne_par : (parentBlock π B hne).Nonempty :=
    (parent_min_lt π B hne h_nonRoot).fst
  set p := (s.filter (· < B.min' hne)).max'
    (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot) with hp_def
  -- predecessor ∈ parent.
  have hp_in_par : p ∈ parentBlock π B hne :=
    parent_contains_pred π B hne h_nonRoot
  have hp_le_max : p ≤ (parentBlock π B hne).max' hne_par :=
    (parentBlock π B hne).le_max' p hp_in_par
  -- parent.max' < B.min' and parent.max' ∈ s.
  have h_parent_mem : parentBlock π B hne ∈ π.val.parts :=
    parentBlock_mem π B hne h_nonRoot
  have h_parent_sub_s : (parentBlock π B hne : Finset α) ⊆ s :=
    π.val.subset h_parent_mem
  have h_max_in_s : (parentBlock π B hne).max' hne_par ∈ s :=
    h_parent_sub_s ((parentBlock π B hne).max'_mem hne_par)
  have h_max_in_filter : (parentBlock π B hne).max' hne_par ∈
      s.filter (· < B.min' hne) :=
    Finset.mem_filter.mpr ⟨h_max_in_s, h_disj⟩
  have h_max_le_p : (parentBlock π B hne).max' hne_par ≤ p := by
    apply Finset.le_max'
    exact h_max_in_filter
  exact le_antisymm h_max_le_p hp_le_max

/-- **DISJOINT-BELOW: no `s`-element strictly between `parent.max` and
`B.min`**.

The "gap" `Ioo (parent.max') (B.min')` in `s` is empty.  This is the
structural reason that the parent-merge preserves NC in this case:
no block of `π` can have elements in this gap (since the gap is
empty), so the merged block `B ∪ parent` has no "crossing" with any
other block via the gap interval. -/
theorem parentBlock_no_gap_element_of_disjoint_below
    (π : NC s) (B : Finset α) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne)
    (h_disj :
      have hne_par : (parentBlock π B hne).Nonempty :=
        (parent_min_lt π B hne h_nonRoot).fst
      (parentBlock π B hne).max' hne_par < B.min' hne)
    {x : α} (hx_s : x ∈ s)
    (hx_gt : (parentBlock π B hne).max' (parent_min_lt π B hne h_nonRoot).fst < x)
    (hx_lt : x < B.min' hne) :
    False := by
  -- x ∈ s with parent.max' < x < B.min'.
  -- Since parent.max' = predecessor (max of s.filter < B.min'),
  -- x being in s.filter (< B.min') gives x ≤ predecessor = parent.max'.
  -- But x > parent.max', contradiction.
  have h_pred_eq :
      (parentBlock π B hne).max' (parent_min_lt π B hne h_nonRoot).fst =
      (s.filter (· < B.min' hne)).max'
        (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot) :=
    parentBlock_max_eq_predecessor_of_disjoint_below π B hne h_nonRoot h_disj
  have hx_in_filter : x ∈ s.filter (· < B.min' hne) :=
    Finset.mem_filter.mpr ⟨hx_s, hx_lt⟩
  have hx_le_pred : x ≤ (s.filter (· < B.min' hne)).max'
        (filter_lt_min_nonempty_of_nonRoot hne h_nonRoot) := by
    apply Finset.le_max'
    exact hx_in_filter
  rw [← h_pred_eq] at hx_le_pred
  exact absurd hx_gt (not_lt.mpr hx_le_pred)

/-! ### Parent's elements avoid `B`'s interval (NESTED case real math)

In the NESTED case (`B.max' ≤ parent.max'`), the parent's `max'` is
strictly greater than `B`'s `max'` (since `B.max' ∈ B`,
`parent.max' ∈ parent`, and `B ∩ parent = ∅`).

Moreover, **no element of parent lies in `[B.min', B.max']`**.  Proof
sketch: if `x ∈ parent` with `B.min' ≤ x ≤ B.max'`:

* If `x = B.min'` or `x = B.max'`, then `x ∈ B ∩ parent = ∅`,
  contradiction.
* If `B.min' < x < B.max'`, then the four-tuple
  `(B.min', x, B.max', parent.max')` with `B.min', B.max' ∈ B` and
  `x, parent.max' ∈ parent` (and `B.max' < parent.max'`) gives a
  B-par-B-par crossing pattern → `IsNoncrossing π` forces `B =
  parent` → contradicts `parentBlock_ne_self`.

This is real combinatorial math on the NC nesting structure. -/

/-- **Strict max separation in NESTED case**: `B.max' < parent.max'`.

In the NESTED case (`h_nested : B.max' ≤ parent.max'`), since both
`B.max' ∈ B` and `parent.max' ∈ parent` with `B ∩ parent = ∅`, the
two values are distinct, so the `≤` strengthens to `<`. -/
theorem parentBlock_nested_max_lt (π : NC s) (B : Finset α)
    (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne)
    (h_nested :
      have hne_par : (parentBlock π B hne).Nonempty :=
        (parent_min_lt π B hne h_nonRoot).fst
      B.max' hne ≤ (parentBlock π B hne).max' hne_par) :
    have hne_par : (parentBlock π B hne).Nonempty :=
      (parent_min_lt π B hne h_nonRoot).fst
    B.max' hne < (parentBlock π B hne).max' hne_par := by
  have hne_par : (parentBlock π B hne).Nonempty :=
    (parent_min_lt π B hne h_nonRoot).fst
  have h_parent_mem : parentBlock π B hne ∈ π.val.parts :=
    parentBlock_mem π B hne h_nonRoot
  have h_parent_ne_B : parentBlock π B hne ≠ B :=
    parentBlock_ne_self π B hne h_nonRoot
  have h_disjoint : Disjoint B (parentBlock π B hne) :=
    π.val.disjoint hB_mem h_parent_mem (Ne.symm h_parent_ne_B)
  have hB_max : B.max' hne ∈ B := B.max'_mem hne
  have h_parent_max : (parentBlock π B hne).max' hne_par ∈ parentBlock π B hne :=
    (parentBlock π B hne).max'_mem hne_par
  have h_ne : B.max' hne ≠ (parentBlock π B hne).max' hne_par := by
    intro h_eq
    have : B.max' hne ∈ parentBlock π B hne := h_eq ▸ h_parent_max
    exact (Finset.disjoint_left.mp h_disjoint) hB_max this
  exact lt_of_le_of_ne h_nested h_ne

/-- **Parent avoids B's interval (NESTED case)**: in the NESTED case,
every element of `parent` is either strictly less than `B.min'` or
strictly greater than `B.max'`.

This is the structural heart of NC's nesting forest in the
NESTED case: parent surrounds B by having elements both BELOW
`B.min'` (since `parent.min' < B.min'`) and ABOVE `B.max'` (since
`B.max' < parent.max'`), with NO element in the interior of B's
interval. -/
theorem parentBlock_nested_avoids_B_interval (π : NC s) (B : Finset α)
    (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne)
    (h_nested :
      have hne_par : (parentBlock π B hne).Nonempty :=
        (parent_min_lt π B hne h_nonRoot).fst
      B.max' hne ≤ (parentBlock π B hne).max' hne_par)
    {x : α} (hx_par : x ∈ parentBlock π B hne) :
    x < B.min' hne ∨ B.max' hne < x := by
  have hne_par : (parentBlock π B hne).Nonempty :=
    (parent_min_lt π B hne h_nonRoot).fst
  have h_parent_mem : parentBlock π B hne ∈ π.val.parts :=
    parentBlock_mem π B hne h_nonRoot
  have h_parent_ne_B : parentBlock π B hne ≠ B :=
    parentBlock_ne_self π B hne h_nonRoot
  have h_disjoint : Disjoint B (parentBlock π B hne) :=
    π.val.disjoint hB_mem h_parent_mem (Ne.symm h_parent_ne_B)
  have hB_max_lt : B.max' hne < (parentBlock π B hne).max' hne_par :=
    parentBlock_nested_max_lt π B hB_mem hne h_nonRoot h_nested
  by_contra h_in_interval
  push_neg at h_in_interval
  obtain ⟨hx_ge, hx_le⟩ := h_in_interval
  have hx_ne_min : x ≠ B.min' hne := by
    intro h_eq
    have hx_B : x ∈ B := h_eq ▸ B.min'_mem hne
    exact (Finset.disjoint_left.mp h_disjoint) hx_B hx_par
  have hx_ne_max : x ≠ B.max' hne := by
    intro h_eq
    have hx_B : x ∈ B := h_eq ▸ B.max'_mem hne
    exact (Finset.disjoint_left.mp h_disjoint) hx_B hx_par
  have hx_gt_min : B.min' hne < x := lt_of_le_of_ne hx_ge (Ne.symm hx_ne_min)
  have hx_lt_max : x < B.max' hne := lt_of_le_of_ne hx_le hx_ne_max
  have h_parent_max_mem : (parentBlock π B hne).max' hne_par ∈ parentBlock π B hne :=
    (parentBlock π B hne).max'_mem hne_par
  have h_eq_BP := π.property hB_mem h_parent_mem
    hx_gt_min hx_lt_max hB_max_lt
    (B.min'_mem hne) (B.max'_mem hne)
    hx_par h_parent_max_mem
  exact h_parent_ne_B h_eq_BP.symm

/-- **Parent below B (DISJOINT-BELOW case)**: in the disjoint-below
case, every element of `parent` is strictly less than `B.min'`.

Trivial corollary of `h_disj` combined with `Finset.le_max'`. -/
theorem parentBlock_disjoint_below_all_lt (π : NC s) (B : Finset α)
    (hne : B.Nonempty) (h_nonRoot : ¬ IsRoot (s := s) B hne)
    (h_disj :
      have hne_par : (parentBlock π B hne).Nonempty :=
        (parent_min_lt π B hne h_nonRoot).fst
      (parentBlock π B hne).max' hne_par < B.min' hne)
    {x : α} (hx_par : x ∈ parentBlock π B hne) :
    x < B.min' hne := by
  have hne_par : (parentBlock π B hne).Nonempty :=
    (parent_min_lt π B hne h_nonRoot).fst
  exact lt_of_le_of_lt ((parentBlock π B hne).le_max' x hx_par) h_disj

/-- **`(parentBlock).card ≥ 2` in NESTED case**: in NESTED, parent has
both an element below `B.min'` (parent's `min'`) AND an element above
`B.max'` (parent's `max'`), which are distinct.  Hence card ≥ 2. -/
theorem parentBlock_card_ge_two_of_nested (π : NC s) (B : Finset α)
    (hB_mem : B ∈ π.val.parts) (hne : B.Nonempty)
    (h_nonRoot : ¬ IsRoot (s := s) B hne)
    (h_nested :
      have hne_par : (parentBlock π B hne).Nonempty :=
        (parent_min_lt π B hne h_nonRoot).fst
      B.max' hne ≤ (parentBlock π B hne).max' hne_par) :
    2 ≤ (parentBlock π B hne).card := by
  have hne_par : (parentBlock π B hne).Nonempty :=
    (parent_min_lt π B hne h_nonRoot).fst
  have h_min_lt_B : (parentBlock π B hne).min' hne_par < B.min' hne :=
    (parent_min_lt π B hne h_nonRoot).snd
  have hB_max_lt : B.max' hne < (parentBlock π B hne).max' hne_par :=
    parentBlock_nested_max_lt π B hB_mem hne h_nonRoot h_nested
  have h_B_min_le_max : B.min' hne ≤ B.max' hne :=
    Finset.min'_le_max' B hne
  have h_par_min_lt_max :
      (parentBlock π B hne).min' hne_par <
        (parentBlock π B hne).max' hne_par :=
    lt_trans (lt_of_lt_of_le h_min_lt_B h_B_min_le_max) hB_max_lt
  have h_par_min_ne_max :
      (parentBlock π B hne).min' hne_par ≠
        (parentBlock π B hne).max' hne_par := ne_of_lt h_par_min_lt_max
  -- card ≥ 2 since min' ≠ max'.
  have h_card_pos : 1 ≤ (parentBlock π B hne).card :=
    hne_par.card_pos
  by_contra h_card_lt
  push_neg at h_card_lt
  -- h_card_lt : card < 2, h_card_pos : 1 ≤ card.  So card = 1.
  have h_card_eq_one : (parentBlock π B hne).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_card_eq_one
  have h_min_eq : (parentBlock π B hne).min' hne_par = a := by
    apply le_antisymm
    · apply Finset.min'_le; rw [ha]; exact Finset.mem_singleton.mpr rfl
    · apply Finset.le_min'
      intro y hy
      rw [ha, Finset.mem_singleton] at hy
      exact le_of_eq hy.symm
  have h_max_eq : (parentBlock π B hne).max' hne_par = a := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      rw [ha, Finset.mem_singleton] at hy
      exact le_of_eq hy
    · apply Finset.le_max'; rw [ha]; exact Finset.mem_singleton.mpr rfl
  exact h_par_min_ne_max (h_min_eq.trans h_max_eq.symm)



/-- **Merged-block min for parent-merge**: the min of `B ∪
parentBlock π B` is always `parentBlock.min'`.

Independent of the dichotomy: parent's min < B.min' always
(`parent_min_lt`), so parent contributes the smaller min. -/
theorem parentBlock_merge_min (π : NC s) (B : Finset α)
    (hne : B.Nonempty) (h_nonRoot : ¬ IsRoot (s := s) B hne) :
    have hne_par : (parentBlock π B hne).Nonempty :=
      (parent_min_lt π B hne h_nonRoot).fst
    have hne_merge : (B ∪ parentBlock π B hne).Nonempty :=
      ⟨(parentBlock π B hne).min' hne_par,
        Finset.mem_union_right _ ((parentBlock π B hne).min'_mem hne_par)⟩
    (B ∪ parentBlock π B hne).min' hne_merge =
      (parentBlock π B hne).min' hne_par := by
  have hne_par : (parentBlock π B hne).Nonempty :=
    (parent_min_lt π B hne h_nonRoot).fst
  have hne_merge : (B ∪ parentBlock π B hne).Nonempty :=
    ⟨(parentBlock π B hne).min' hne_par,
      Finset.mem_union_right _ ((parentBlock π B hne).min'_mem hne_par)⟩
  have h_par_lt_B : (parentBlock π B hne).min' hne_par < B.min' hne :=
    (parent_min_lt π B hne h_nonRoot).snd
  apply le_antisymm
  · apply Finset.min'_le
    apply Finset.mem_union_right
    exact (parentBlock π B hne).min'_mem hne_par
  · apply Finset.le_min'
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx_B | hx_par
    · exact le_of_lt (lt_of_lt_of_le h_par_lt_B (B.min'_le x hx_B))
    · exact (parentBlock π B hne).min'_le x hx_par

/-- **Merged-block max for parent-merge (NESTED case)**: max equals
parent's max. -/
theorem parentBlock_merge_max_nested (π : NC s) (B : Finset α)
    (hne : B.Nonempty) (h_nonRoot : ¬ IsRoot (s := s) B hne)
    (h_nested :
      have hne_par : (parentBlock π B hne).Nonempty :=
        (parent_min_lt π B hne h_nonRoot).fst
      B.max' hne ≤ (parentBlock π B hne).max' hne_par) :
    have hne_par : (parentBlock π B hne).Nonempty :=
      (parent_min_lt π B hne h_nonRoot).fst
    have hne_merge : (B ∪ parentBlock π B hne).Nonempty :=
      ⟨(parentBlock π B hne).min' hne_par,
        Finset.mem_union_right _ ((parentBlock π B hne).min'_mem hne_par)⟩
    (B ∪ parentBlock π B hne).max' hne_merge =
      (parentBlock π B hne).max' hne_par := by
  have hne_par : (parentBlock π B hne).Nonempty :=
    (parent_min_lt π B hne h_nonRoot).fst
  have hne_merge : (B ∪ parentBlock π B hne).Nonempty :=
    ⟨(parentBlock π B hne).min' hne_par,
      Finset.mem_union_right _ ((parentBlock π B hne).min'_mem hne_par)⟩
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx_B | hx_par
    · exact le_trans (B.le_max' x hx_B) h_nested
    · exact (parentBlock π B hne).le_max' x hx_par
  · apply Finset.le_max'
    apply Finset.mem_union_right
    exact (parentBlock π B hne).max'_mem hne_par

/-- **Merged-block max for parent-merge (DISJOINT-BELOW case)**: max
equals B's max. -/
theorem parentBlock_merge_max_disjoint (π : NC s) (B : Finset α)
    (hne : B.Nonempty) (h_nonRoot : ¬ IsRoot (s := s) B hne)
    (h_disj :
      have hne_par : (parentBlock π B hne).Nonempty :=
        (parent_min_lt π B hne h_nonRoot).fst
      (parentBlock π B hne).max' hne_par < B.min' hne) :
    have hne_par : (parentBlock π B hne).Nonempty :=
      (parent_min_lt π B hne h_nonRoot).fst
    have hne_merge : (B ∪ parentBlock π B hne).Nonempty :=
      ⟨(parentBlock π B hne).min' hne_par,
        Finset.mem_union_right _ ((parentBlock π B hne).min'_mem hne_par)⟩
    (B ∪ parentBlock π B hne).max' hne_merge = B.max' hne := by
  have hne_par : (parentBlock π B hne).Nonempty :=
    (parent_min_lt π B hne h_nonRoot).fst
  have hne_merge : (B ∪ parentBlock π B hne).Nonempty :=
    ⟨(parentBlock π B hne).min' hne_par,
      Finset.mem_union_right _ ((parentBlock π B hne).min'_mem hne_par)⟩
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx_B | hx_par
    · exact B.le_max' x hx_B
    · exact le_of_lt (lt_of_le_of_lt
        ((parentBlock π B hne).le_max' x hx_par)
        (lt_of_lt_of_le h_disj (Finset.min'_le_max' B hne)))
  · apply Finset.le_max'
    apply Finset.mem_union_left
    exact B.max'_mem hne

end NC

end Hamilton.Infrastructure
