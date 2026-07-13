/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.ParentMergeNC
import Hamilton.Infrastructure.Top
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectivity of the noncrossing refinement graph

The **refinement graph** `NCRefinementGraph s` on `NC α s` is
**connected** (for nonempty `s`): every two partitions are connected
by a sequence of single-merge / single-split steps.

The proof uses the *nesting forest*: starting from any `π`, we
repeatedly apply parent-merges (each reducing `numBlocks` by 1) until
reaching `NC.top` (the indiscrete partition with `numBlocks = 1`).
Two partitions reach `NC.top`, hence reach each other.

## Main results

* `NC.exists_nonRoot_block` — for `numBlocks π ≥ 2`, there exists a
  non-root block.
* `NC.reachable_to_top` — every `π : NC s` is reachable from
  `NC.top hs` in `NCRefinementGraph s`.
* `NCRefinementGraph_preconnected` — preconnectedness.
* `NCRefinementGraph_connected` — full `SimpleGraph.Connected`.

## Tags

noncrossing partition, refinement graph, connectivity, nesting forest
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- For a partition `π : NC s` with `numBlocks π ≥ 2`, there exists
a block of `π` that is non-root.

Reason: there are at least 2 blocks; at most one is the *root* (the
block containing the minimum of `s`), so at least one is non-root.
This requires `s.Nonempty` (else `numBlocks π = 0 < 2`). -/
theorem exists_nonRoot_block (hs : s.Nonempty) (π : NC s)
    (hk : 2 ≤ numBlocks π) :
    ∃ B ∈ π.val.parts, ∃ hne : B.Nonempty,
      ¬ IsRoot (s := s) B hne := by
  -- The block containing min s.
  let m := s.min' hs
  have hm_in_s : m ∈ s := s.min'_mem hs
  let R := π.val.part m
  have hR_mem : R ∈ π.val.parts := π.val.part_mem.mpr hm_in_s
  -- erase R has cardinality ≥ 1.
  have herase_card : 1 ≤ (π.val.parts.erase R).card := by
    rw [Finset.card_erase_of_mem hR_mem]
    unfold numBlocks at hk
    omega
  obtain ⟨B, hB_in⟩ := Finset.card_pos.mp herase_card
  rw [Finset.mem_erase] at hB_in
  obtain ⟨hB_ne_R, hB_mem⟩ := hB_in
  have hne : B.Nonempty := π.val.nonempty_of_mem_parts hB_mem
  refine ⟨B, hB_mem, hne, ?_⟩
  -- B ≠ R, and R contains min s, so B cannot contain min s.
  intro h_root
  -- h_root : ∀ q ∈ s, ¬ q < min B; we'll derive m ∈ B then m = min B then B = R.
  -- Actually IsRoot says no s-element is < min B.  In particular min s ≥ min B.
  -- Since min B ∈ B ⊆ s, min B ≥ min s = m.  So min B = m (both directions).
  have hmin_B_in_s : B.min' hne ∈ s := (π.val.subset hB_mem) (B.min'_mem hne)
  have hmin_B_ge : m ≤ B.min' hne := s.min'_le _ hmin_B_in_s
  have hm_not_lt : ¬ m < B.min' hne := h_root m hm_in_s
  have hm_eq : m = B.min' hne := le_antisymm hmin_B_ge (not_lt.mp hm_not_lt)
  -- Now m ∈ B (since min B = m).
  have hm_in_B : m ∈ B := hm_eq ▸ B.min'_mem hne
  -- And m ∈ R by definition.
  have hm_in_R : m ∈ R := π.val.mem_part_self.mpr hm_in_s
  -- So B ∩ R ≠ ∅, contradicting disjointness B ≠ R.
  have hdisj := π.val.disjoint hB_mem hR_mem hB_ne_R
  exact (Finset.disjoint_left.mp hdisj hm_in_B) hm_in_R

/-- **Reachability to top** via parent-merges.  Every `π : NC s` is
`NCRefinementGraph s`-reachable from `NC.top hs`.

Proof by strong induction on `numBlocks π`:
* Base (`numBlocks π = 1`): `π = NC.top hs` directly.
* Inductive: pick a non-root block, parent-merge to a smaller partition,
  recurse. -/
theorem reachable_to_top (hs : s.Nonempty) (π : NC s) :
    (NCRefinementGraph s).Reachable π (NC.top hs) := by
  induction hm : numBlocks π using Nat.strong_induction_on
    generalizing π with
  | _ k ih =>
    by_cases hk_one : k = 1
    · subst hk_one
      have heq : π = NC.top hs := numBlocks_one_eq_top π hs hm
      rw [heq]
    · have hk_pos : 1 ≤ k := by
        have h := one_le_numBlocks π hs
        omega
      have hk_two : 2 ≤ k := by omega
      have hk_two_π : 2 ≤ numBlocks π := hm ▸ hk_two
      obtain ⟨B, hB_mem, hne, h_nonRoot⟩ :=
        exists_nonRoot_block hs π hk_two_π
      have hadj : (NCRefinementGraph s).Adj π
          (parentMergeNC π B hne hB_mem h_nonRoot) :=
        NCRefinementGraph_adj_parentMergeNC π B hne hB_mem h_nonRoot
      have hσ_card :
          numBlocks (parentMergeNC π B hne hB_mem h_nonRoot) + 1 =
            numBlocks π :=
        parentMergeNC_numBlocks π B hne hB_mem h_nonRoot
      have hσ_lt :
          numBlocks (parentMergeNC π B hne hB_mem h_nonRoot) < k := by
        have h1 : numBlocks (parentMergeNC π B hne hB_mem h_nonRoot) + 1 = k :=
          hm ▸ hσ_card
        omega
      exact (SimpleGraph.Adj.reachable hadj).trans
        (ih _ hσ_lt _ rfl)

end NC

/-- `NCRefinementGraph s` is preconnected (for nonempty `s`):
two partitions both reach `NC.top hs`, hence reach each other. -/
theorem NCRefinementGraph_preconnected {α : Type*} [LinearOrder α]
    {s : Finset α} (hs : s.Nonempty) :
    (NCRefinementGraph s).Preconnected := by
  intro π σ
  exact (NC.reachable_to_top hs π).trans (NC.reachable_to_top hs σ).symm

/-- `NCRefinementGraph s` is connected (for nonempty `s`). -/
theorem NCRefinementGraph_connected {α : Type*} [LinearOrder α]
    {s : Finset α} (hs : s.Nonempty) :
    (NCRefinementGraph s).Connected := by
  haveI : Nonempty (NC s) := ⟨NC.top hs⟩
  exact ⟨NCRefinementGraph_preconnected hs⟩

end Hamilton.Infrastructure
