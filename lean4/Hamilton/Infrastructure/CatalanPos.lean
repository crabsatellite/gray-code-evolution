/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Central



namespace Nat

/-- `0 < catalan n` for all n. -/
theorem catalan_pos : ∀ n : ℕ, 0 < catalan n
  | 0 => by rw [catalan_zero]; omega
  | n + 1 => by
    rw [catalan_succ]
    -- ∑ i : Fin n.succ, catalan i * catalan (n - i.val).
    -- The i = 0 term: catalan 0 * catalan n = catalan n > 0 (by IH).
    have h_pos : 0 < catalan n := catalan_pos n
    have h_le : catalan n ≤ ∑ i : Fin n.succ, catalan i.val * catalan (n - i.val) := by
      have h := Finset.single_le_sum
        (f := fun i : Fin n.succ => catalan i.val * catalan (n - i.val))
        (s := Finset.univ)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (0 : Fin n.succ))
      simpa using h
    exact lt_of_lt_of_le h_pos h_le

/-- `1 ≤ catalan n` for all n. -/
theorem one_le_catalan (n : ℕ) : 1 ≤ catalan n := catalan_pos n

/-- `catalan n ≤ catalan (n+1)` — catalan is non-decreasing across
  successor. -/
theorem catalan_le_succ (n : ℕ) : catalan n ≤ catalan (n+1) := by
  rw [catalan_succ]
  have h := Finset.single_le_sum
    (f := fun i : Fin (n+1) => catalan i.val * catalan (n - i.val))
    (s := Finset.univ)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (0 : Fin (n+1)))
  simpa using h

/-- `catalan` is monotone (non-decreasing). -/
theorem catalan_mono : Monotone catalan := by
  apply monotone_nat_of_le_succ
  exact catalan_le_succ

/-- For `n ≥ 1`, `2 * catalan n ≤ catalan (n+1)`.

Proof: in `catalan_succ`, the `i = 0` and `i = n` terms each equal
`catalan n` (using `catalan_zero = 1`).  For `n ≥ 1`, these indices
are distinct in `Fin (n+1)`, contributing `2 * catalan n` to the sum. -/
theorem two_mul_catalan_le_catalan_succ (n : ℕ) (hn : 1 ≤ n) :
    2 * catalan n ≤ catalan (n + 1) := by
  rw [catalan_succ]
  -- Use the i=0 and i=n terms.
  have h_pair : (catalan (0 : Fin (n+1)).val * catalan (n - (0 : Fin (n+1)).val))
      + (catalan (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1)).val *
         catalan (n - (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1)).val))
      = 2 * catalan n := by
    simp [catalan_zero]
    ring
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
    (s := ({0, ⟨n, Nat.lt_succ_self n⟩} : Finset (Fin (n+1))))
    (t := Finset.univ)
    (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _))
  rw [Finset.sum_insert (by
    rw [Finset.mem_singleton]
    intro h_eq
    have : (0 : Fin (n+1)).val = (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1)).val :=
      congrArg Fin.val h_eq
    simp at this
    omega)]
  rw [Finset.sum_singleton]
  rw [h_pair]

/-- For `n ≥ 1`, `catalan n < catalan (n+1)` — catalan strictly
increases. -/
theorem catalan_lt_succ (n : ℕ) (hn : 1 ≤ n) :
    catalan n < catalan (n+1) := by
  have h_two := two_mul_catalan_le_catalan_succ n hn
  have h_pos := catalan_pos n
  omega

/-- `catalan n ≤ centralBinom n`. -/
theorem catalan_le_centralBinom (n : ℕ) : catalan n ≤ n.centralBinom := by
  rw [catalan_eq_centralBinom_div]
  exact Nat.div_le_self _ _

/-- `catalan n ≤ 4 ^ n` (exponential upper bound). -/
theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n :=
  (catalan_le_centralBinom n).trans (centralBinom_le_four_pow n)

/-- `2 ^ (n - 1) ≤ catalan n` for `n ≥ 1` (exponential lower bound). -/
theorem two_pow_le_catalan : ∀ n : ℕ, 1 ≤ n → 2 ^ (n - 1) ≤ catalan n
  | 0, h => by omega
  | 1, _ => by rw [catalan_one]; norm_num
  | n + 2, _ => by
    have ih := two_pow_le_catalan (n + 1) (by omega)
    have h_step := two_mul_catalan_le_catalan_succ (n + 1) (by omega)
    have h_simp_ih : (n + 1) - 1 = n := by omega
    rw [h_simp_ih] at ih
    have h_simp_goal : (n + 2) - 1 = n + 1 := by omega
    rw [h_simp_goal]
    calc 2 ^ (n + 1)
        = 2 * 2 ^ n := by ring
      _ ≤ 2 * catalan (n + 1) := by omega
      _ ≤ catalan (n + 2) := h_step

end Nat
