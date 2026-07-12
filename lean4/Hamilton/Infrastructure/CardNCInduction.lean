/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.KSPairCatalan
import Hamilton.Infrastructure.CardNCCatalan

/-!
# Induction toward `card_NC = catalan`

Conditional: assuming the inner sum formula (`KS_inner_sum_at n j =
card_NC j.val * card_NC (n - j.val)`), derive `card_NC n = catalan n`
for all `n` by strong induction.

## Main results

* `NC.card_NC_eq_catalan_of_inner_sum` — conditional.

## Tags

NC, Catalan, induction
-/

namespace Hamilton.Infrastructure

namespace NC

/-- **Conditional card_NC = catalan**: if the inner sum formula holds
for all (n, j), then `card_NC n = catalan n` for all n. -/
theorem card_NC_eq_catalan_of_inner_sum
    (h_inner : ∀ (n : ℕ) (j : Fin (n+1)),
      KS_inner_sum_at n j = card_NC j.val * card_NC (n - j.val)) :
    ∀ n : ℕ, card_NC n = catalan n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match h_n : n with
    | 0 => exact card_NC_eq_catalan_le_two 0 (by omega)
    | 1 => exact card_NC_eq_catalan_le_two 1 (by omega)
    | m + 2 =>
      rw [card_NC_eq_sum_inner]
      have h_inner_at : ∀ j : Fin (m+2),
          KS_inner_sum_at (m+1) j = card_NC j.val * card_NC (m+1 - j.val) :=
        h_inner (m+1)
      rw [Finset.sum_congr rfl (fun j _ => h_inner_at j)]
      have h_ih : ∀ k : Fin (m+2), card_NC k.val = catalan k.val := by
        intro k
        exact ih k.val (Nat.lt_succ_of_le (Nat.le_of_lt_succ k.is_lt))
      have h_ih_sub : ∀ k : Fin (m+2), card_NC (m+1 - k.val) = catalan (m+1 - k.val) := by
        intro k
        exact ih (m+1 - k.val) (by omega)
      rw [Finset.sum_congr rfl (fun j _ => by rw [h_ih j, h_ih_sub j])]
      rw [show (m + 2 : ℕ) = (m + 1) + 1 from rfl]
      rw [catalan_succ (m+1)]

/-- **`card_NC n = catalan n` FOR ALL n** — unconditional closure. -/
theorem card_NC_eq_catalan : ∀ n : ℕ, card_NC n = catalan n :=
  card_NC_eq_catalan_of_inner_sum KS_inner_sum_at_pair

/-- **`|NC(Finset.univ : Finset (Fin n))| = catalan n`** for all n. -/
theorem card_NC_univ_fin_eq_catalan (n : ℕ) :
    Fintype.card (NC (Finset.univ : Finset (Fin n))) = catalan n :=
  card_NC_eq_catalan n

/-- **`|NC s| = catalan s.card`** for any `s : Finset α`
(`α : LinearOrder`). -/
theorem card_NC_eq_catalan_card {α : Type*} [LinearOrder α] (s : Finset α) :
    Fintype.card (NC s) = catalan s.card := by
  rw [card_NC_eq s, card_NC_eq_catalan]

/-- `(s.card + 1) * |NC s| = centralBinom s.card`. -/
theorem card_NC_mul_succ_eq_centralBinom {α : Type*} [LinearOrder α]
    (s : Finset α) :
    (s.card + 1) * Fintype.card (NC s) = Nat.centralBinom s.card := by
  rw [card_NC_eq_catalan_card]
  exact succ_mul_catalan_eq_centralBinom s.card

/-- `card_NC 3 = 5`. -/
@[simp]
theorem card_NC_three : card_NC 3 = 5 := by
  rw [card_NC_eq_catalan, catalan_three]

/-- `card_NC 4 = 14`. -/
@[simp]
theorem card_NC_four : card_NC 4 = 14 := by
  rw [card_NC_eq_catalan, catalan_four]

/-- `card_NC 5 = 42`. -/
@[simp]
theorem card_NC_five : card_NC 5 = 42 := by
  rw [card_NC_eq_catalan, catalan_five]

/-- `card_NC 6 = 132`. -/
@[simp]
theorem card_NC_six : card_NC 6 = 132 := by
  rw [card_NC_eq_catalan, catalan_six]

/-- `card_NC 7 = 429`. -/
@[simp]
theorem card_NC_seven : card_NC 7 = 429 := by
  rw [card_NC_eq_catalan, catalan_seven]

end NC

end Hamilton.Infrastructure
