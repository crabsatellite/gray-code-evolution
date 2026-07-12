/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCType
import Hamilton.Infrastructure.NCOperations
import Hamilton.Infrastructure.CardNCInduction



namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α]

/-- Set of NCs with even number of blocks. -/
noncomputable def evenBlocks (s : Finset α) : Finset (NC s) :=
  (Finset.univ : Finset (NC s)).filter (fun π => Even (numBlocks π))

/-- Set of NCs with odd number of blocks. -/
noncomputable def oddBlocks (s : Finset α) : Finset (NC s) :=
  (Finset.univ : Finset (NC s)).filter (fun π => Odd (numBlocks π))

/-- `|evenBlocks s| + |oddBlocks s| = |NC s|`. -/
theorem evenBlocks_add_oddBlocks (s : Finset α) :
    (evenBlocks s).card + (oddBlocks s).card = Fintype.card (NC s) := by
  rw [show Fintype.card (NC s) = (Finset.univ : Finset (NC s)).card from
        (Finset.card_univ).symm]
  unfold evenBlocks oddBlocks
  rw [show ((Finset.univ : Finset (NC s)).filter (fun π => Odd (numBlocks π))) =
        ((Finset.univ : Finset (NC s)).filter (fun π => ¬ Even (numBlocks π))) from ?_]
  · exact Finset.card_filter_add_card_filter_not (fun π => Even (numBlocks π))
  · ext π
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨h_mem, h_odd⟩
      exact ⟨h_mem, Nat.not_even_iff_odd.mpr h_odd⟩
    · rintro ⟨h_mem, h_not_even⟩
      exact ⟨h_mem, Nat.not_even_iff_odd.mp h_not_even⟩

/-- `|evenBlocks s| + |oddBlocks s| = catalan s.card`. -/
theorem evenBlocks_add_oddBlocks_eq_catalan (s : Finset α) :
    (evenBlocks s).card + (oddBlocks s).card = catalan s.card := by
  rw [evenBlocks_add_oddBlocks]
  exact card_NC_eq_catalan_card s



/-- The signed NC count: integer-valued alternating sum
`∑_π (-1)^{numBlocks π}`. -/
noncomputable def signedNCCount (s : Finset α) : ℤ :=
  ∑ π ∈ (Finset.univ : Finset (NC s)), (-1 : ℤ) ^ (numBlocks π)

/-- `signedNCCount s = |evenBlocks s| - |oddBlocks s|` (as integers). -/
theorem signedNCCount_eq_evenBlocks_sub_oddBlocks (s : Finset α) :
    signedNCCount s =
      ((evenBlocks s).card : ℤ) - ((oddBlocks s).card : ℤ) := by
  unfold signedNCCount evenBlocks oddBlocks
  -- Split the sum into even and odd parts.
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (NC s))
        (fun π => Even (numBlocks π)) (fun π => (-1 : ℤ) ^ numBlocks π)]
  -- Even part: each summand is 1, so sum = card.
  have h_even_each : ∀ π ∈ (Finset.univ : Finset (NC s)).filter
        (fun π => Even (numBlocks π)),
        (-1 : ℤ) ^ numBlocks π = (1 : ℤ) := by
    intro π hπ
    rw [Finset.mem_filter] at hπ
    have : Even (numBlocks π) := hπ.2
    exact this.neg_one_pow
  -- Odd part (¬Even): each summand is -1.
  have h_odd_each : ∀ π ∈ (Finset.univ : Finset (NC s)).filter
        (fun π => ¬ Even (numBlocks π)),
        (-1 : ℤ) ^ numBlocks π = (-1 : ℤ) := by
    intro π hπ
    rw [Finset.mem_filter] at hπ
    have : Odd (numBlocks π) := Nat.not_even_iff_odd.mp hπ.2
    exact this.neg_one_pow
  rw [Finset.sum_congr rfl h_even_each, Finset.sum_congr rfl h_odd_each]
  -- ¬Even filter = Odd filter
  have h_odd_filter : (Finset.univ : Finset (NC s)).filter
      (fun π => ¬ Even (numBlocks π)) =
      (Finset.univ : Finset (NC s)).filter (fun π => Odd (numBlocks π)) := by
    ext π
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨h_mem, h_not_even⟩
      exact ⟨h_mem, Nat.not_even_iff_odd.mp h_not_even⟩
    · rintro ⟨h_mem, h_odd⟩
      exact ⟨h_mem, Nat.not_even_iff_odd.mpr h_odd⟩
  rw [h_odd_filter]
  simp [Finset.sum_const]
  ring

end NC

end Hamilton.Infrastructure
