/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.FiberCardinality
import Hamilton.Infrastructure.FiberPartitionIdentity



namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore)

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- **Kreweras-Simion recursion**:

`|NC s| = ∑_{S ⊆ s with max(s) ∈ S} ∏_{x ∈ S} |NC(gapBefore s S x)|`. -/
theorem card_eq_sum_prod_gap (hs : s.Nonempty) :
    Fintype.card (NC s) =
      ∑ S ∈ s.powerset.filter (fun S => S.Nonempty ∧ s.max' hs ∈ S),
        ∏ x ∈ S.attach, Fintype.card (NC (gapBefore s S x.1)) := by
  -- Step 1: Partition identity: |NC s| = ∑_{S ⊆ s} |fiberOf hs S|.
  rw [← sum_fiberOf_card_powerset hs]
  -- Step 2: Only S with max ∈ S contribute (otherwise the fiber is empty).
  -- For S not containing max: blockOfLast contains max, so no π satisfies blockOfLast = S.
  rw [show ∑ S ∈ s.powerset, (fiberOf hs S).card =
        ∑ S ∈ s.powerset.filter (fun S => S.Nonempty ∧ s.max' hs ∈ S),
          (fiberOf hs S).card from ?_]
  · -- Step 3: Apply the K-S multiplicative identity to each fiber.
    apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hS_sub, hS_ne, hmax⟩ := hS
    exact fiberOf_card_eq_prod hs S hS_ne hS_sub hmax
  · -- Step 2 proof: zero contribution when max ∉ S or S empty.
    apply (Finset.sum_filter_of_ne ?_).symm
    intro S hS hne
    rw [Finset.mem_powerset] at hS
    -- (fiberOf hs S).card ≠ 0 ⇒ S nonempty ∧ max ∈ S.
    have h_card_pos : 0 < (fiberOf hs S).card :=
      Nat.pos_of_ne_zero hne
    obtain ⟨π, hπ⟩ := Finset.card_pos.mp h_card_pos
    rw [mem_fiberOf] at hπ
    -- blockOfLast π hs = S; blockOfLast contains max; blockOfLast nonempty.
    refine ⟨?_, ?_⟩
    · rw [← hπ]; exact blockOfLast_nonempty π hs
    · rw [← hπ]; exact blockOfLast_contains_max π hs

end NC

end Hamilton.Infrastructure
