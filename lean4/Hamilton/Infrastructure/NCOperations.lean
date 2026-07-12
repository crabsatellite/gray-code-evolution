/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCType
import Mathlib.Data.Multiset.Basic

/-!
# Basic operations on noncrossing partitions

This file develops the **basic operations** on `NC α s` — the
noncrossing partition type from `NCType.lean`:

* `NC.blockSizes` — the multiset of block cardinalities.
* `NC.top` — the indiscrete partition (one single block = `s`),
  when `s.Nonempty`.

## Main results

* `NC.blockSizes_pos` — every block size is positive.
* `NC.blockSizes_sum` — the multiset sums to `s.card`.
* `NC.blockSizes_card` — the multiset has `numBlocks π` entries.
* `NC.one_le_numBlocks` — for nonempty `s`, `numBlocks ≥ 1`.
* `NC.numBlocks_le_card` — `numBlocks π ≤ s.card`.

## Tags

noncrossing partition, block sizes, numBlocks, top, bot
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The **block sizes** of an `NC` partition as a `Multiset ℕ` —
each block of `π` contributes its cardinality. -/
def blockSizes (π : NC s) : Multiset ℕ :=
  π.val.parts.val.map Finset.card

/-- Every block of an `NC` partition is nonempty (inherited from
`Finpartition.bot_notMem`).  Hence every entry in `blockSizes π` is
at least `1`. -/
theorem blockSizes_pos (π : NC s) :
    ∀ k ∈ blockSizes π, 1 ≤ k := by
  intro k hk
  unfold blockSizes at hk
  rw [Multiset.mem_map] at hk
  obtain ⟨B, hB, rfl⟩ := hk
  -- B ∈ π.val.parts.val ↔ B ∈ π.val.parts
  have hB_mem : B ∈ π.val.parts := hB
  have hB_ne : B.Nonempty := π.val.nonempty_of_mem_parts hB_mem
  exact hB_ne.card_pos

/-- The sum of block sizes equals the cardinality of the carrier set.
This is `Finpartition`'s defining property: blocks partition the
carrier. -/
theorem blockSizes_sum (π : NC s) :
    (blockSizes π).sum = s.card := by
  unfold blockSizes
  rw [← π.val.sum_card_parts]
  rfl

/-- The multiset of block sizes has `numBlocks π` entries (one per
block). -/
theorem blockSizes_card (π : NC s) :
    Multiset.card (blockSizes π) = numBlocks π := by
  unfold blockSizes numBlocks
  rw [Multiset.card_map]
  rfl

/-- For a `Finpartition` of a nonempty set, `numBlocks ≥ 1`.

If `parts` were empty, the sup over parts would be `⊥` ≠ `s`,
contradicting `Finpartition.sup_parts`. -/
theorem one_le_numBlocks (π : NC s) (hs : s.Nonempty) :
    1 ≤ numBlocks π := by
  rw [Nat.one_le_iff_ne_zero]
  unfold numBlocks
  intro h
  rw [Finset.card_eq_zero] at h
  have hsup : π.val.parts.sup id = s := π.val.sup_parts
  rw [h, Finset.sup_empty] at hsup
  -- hsup : ⊥ = s
  rw [eq_comm] at hsup
  rw [Finset.bot_eq_empty] at hsup
  exact hs.ne_empty hsup

/-- Helper: For any `Multiset ℕ` with all entries ≥ 1, the cardinality
bounds the sum. -/
private theorem _card_le_sum_of_one_le (m : Multiset ℕ)
    (hpos : ∀ k ∈ m, 1 ≤ k) : Multiset.card m ≤ m.sum := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m' ih =>
    have ha : 1 ≤ a := hpos a (Multiset.mem_cons_self a m')
    have ih' : Multiset.card m' ≤ m'.sum := ih (fun k hk =>
      hpos k (Multiset.mem_cons_of_mem hk))
    rw [Multiset.card_cons, Multiset.sum_cons]
    omega

/-- The number of blocks is bounded above by the cardinality of the
carrier (each block has ≥ 1 element). -/
theorem numBlocks_le_card (π : NC s) :
    numBlocks π ≤ s.card := by
  rw [← blockSizes_sum π, ← blockSizes_card π]
  exact _card_le_sum_of_one_le _ (blockSizes_pos π)

end NC

end Hamilton.Infrastructure
