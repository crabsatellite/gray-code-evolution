/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCBipartiteCounts
import Hamilton.Infrastructure.NCOrder

/-!
# Narayana number counting infrastructure

For `NC(s)`, the number of NCs with exactly `k` blocks is the
**Narayana number** `N(|s|, k)`.  This file builds the basic counting
infrastructure indexing NC by `numBlocks`.

The Narayana formula `N(n, k) = (1/n) * C(n, k) * C(n, k-1)` is not
established here — only the counting bijection (number of NCs with
given block count) and its summation properties.

## Main definitions

* `NC.numNCWithKBlocks s k` — `|{π : NC s | numBlocks π = k}|`.

## Main results

* `NC.sum_numNCWithKBlocks_eq_catalan` — `∑_k N(|s|, k) = catalan |s|`.
* `NC.evenBlocks_card_eq_sum_numNCWithKBlocks` — `|evenBlocks s|` is
  the sum over even `k` of `numNCWithKBlocks s k`.
* `NC.oddBlocks_card_eq_sum_numNCWithKBlocks` — likewise for odd `k`.

## Tags

NC, Narayana number, block count, Catalan, bipartite
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α]

open Finset

/-- The Narayana count: number of NCs of `s` with exactly `k` blocks. -/
noncomputable def numNCWithKBlocks (s : Finset α) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (NC s)).filter (fun π => numBlocks π = k)).card

private lemma numBlocks_filter_pairwiseDisjoint (s : Finset α)
    (T : Finset ℕ) :
    (T : Set ℕ).PairwiseDisjoint
      (fun k => (Finset.univ : Finset (NC s)).filter (fun π => numBlocks π = k)) := by
  intro k1 _ k2 _ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_filter]
  intro π _ hk1_eq hk2_eq
  exact hne (hk1_eq.symm.trans hk2_eq)

/-- Sum over `k` of `numNCWithKBlocks s k` = total `|NC s|` = `catalan s.card`. -/
theorem sum_numNCWithKBlocks_eq_catalan (s : Finset α) :
    ∑ k ∈ Finset.range (s.card + 1), numNCWithKBlocks s k = catalan s.card := by
  unfold numNCWithKBlocks
  rw [← Finset.card_biUnion (numBlocks_filter_pairwiseDisjoint s _)]
  rw [show (Finset.range (s.card + 1)).biUnion
            (fun k => (Finset.univ : Finset (NC s)).filter (fun π => numBlocks π = k))
          = Finset.univ from ?_]
  · exact (Finset.card_univ).trans (card_NC_eq_catalan_card s)
  · ext π
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    refine ⟨numBlocks π, ?_, rfl⟩
    have := numBlocks_le_card π
    omega

/-- `|evenBlocks s|` is the sum of Narayana counts over even `k`. -/
theorem evenBlocks_card_eq_sum_numNCWithKBlocks (s : Finset α) :
    (evenBlocks s).card =
      ∑ k ∈ (Finset.range (s.card + 1)).filter Even, numNCWithKBlocks s k := by
  unfold evenBlocks numNCWithKBlocks
  rw [← Finset.card_biUnion (numBlocks_filter_pairwiseDisjoint s _)]
  congr 1
  ext π
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_biUnion,
    Finset.mem_range, true_and]
  constructor
  · intro h_even
    refine ⟨numBlocks π, ⟨?_, h_even⟩, rfl⟩
    have := numBlocks_le_card π
    omega
  · rintro ⟨k, ⟨_, h_even⟩, h_eq⟩
    exact h_eq ▸ h_even

/-- `|oddBlocks s|` is the sum of Narayana counts over odd `k`. -/
theorem oddBlocks_card_eq_sum_numNCWithKBlocks (s : Finset α) :
    (oddBlocks s).card =
      ∑ k ∈ (Finset.range (s.card + 1)).filter Odd, numNCWithKBlocks s k := by
  unfold oddBlocks numNCWithKBlocks
  rw [← Finset.card_biUnion (numBlocks_filter_pairwiseDisjoint s _)]
  congr 1
  ext π
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_biUnion,
    Finset.mem_range, true_and]
  constructor
  · intro h_odd
    refine ⟨numBlocks π, ⟨?_, h_odd⟩, rfl⟩
    have := numBlocks_le_card π
    omega
  · rintro ⟨k, ⟨_, h_odd⟩, h_eq⟩
    exact h_eq ▸ h_odd

/-- For non-empty `s`, there are no NCs with `0` blocks. -/
theorem numNCWithKBlocks_zero_of_pos (s : Finset α) (hs : 1 ≤ s.card) :
    numNCWithKBlocks s 0 = 0 := by
  unfold numNCWithKBlocks
  rw [Finset.card_eq_zero]
  ext π
  have hs_ne : s.Nonempty := Finset.card_pos.mp hs
  have h_pos : 1 ≤ numBlocks π := one_le_numBlocks π hs_ne
  simp [Finset.mem_filter]
  omega

/-! ## Narayana count formula (axiom)

The classical Narayana number formula:
`s.card · numNCWithKBlocks s k = C(s.card, k) · C(s.card, k - 1)` for `k ≥ 1`.

Equivalently `numNCWithKBlocks s k = N(s.card, k)` where the Narayana
number is `N(n, k) = (1/n) C(n, k) C(n, k-1)` (Narayana 1955).

Multiple classical proofs:
* Cycle-lemma on bracket sequences (uses cyclic rotation of n-step paths).
* Bijection NC ↔ Dyck paths + peak-count formula.
* Plane tree bijection + internal-vertex count.
* LGV lemma + 2×2 binomial determinant.

This axiom (Cat 1 Mathlib-derivable, deferred for Phase 0) collapses the
entire negative direction of the NCR Hamilton conjecture for **all odd**
`n ≥ 3` into a SINGLE classical identity — no NCR-specific axiom needed. -/

/-! ### Binomial-Catalan identity (kernel-pure)

The classical identity `(2m+1) · C_m = C(2m+1, m)` connecting the
"odd-central binomial" to Catalan numbers.  Derived from Mathlib's
`succ_mul_catalan_eq_centralBinom` + `Nat.choose_mul_succ_eq`.  Used
in the explicit-Catalan form of the bipartite imbalance. -/

/-- `m · catalan m = C(2m, m - 1)` for `m ≥ 1`.

This is the "predecessor central" identity: a kernel-pure piece of
Catalan-binomial structure relevant for the Narayana count formula proof. -/
theorem choose_two_mul_pred_eq_mul_catalan (m : ℕ) (hm : 1 ≤ m) :
    (2 * m).choose (m - 1) = m * catalan m := by
  have h1 : (m + 1) * catalan m = (2 * m).choose m := by
    have := succ_mul_catalan_eq_centralBinom m
    unfold Nat.centralBinom at this
    exact this
  have h2 : (2 * m).choose m * m = (2 * m).choose (m - 1) * (m + 1) := by
    have h := Nat.choose_succ_right_eq (2 * m) (m - 1)
    have h_eq : (m - 1) + 1 = m := by omega
    rw [h_eq] at h
    have h_sub : 2 * m - (m - 1) = m + 1 := by omega
    rw [h_sub] at h
    exact h
  have h3 : (m + 1) * (m * catalan m) = (m + 1) * (2 * m).choose (m - 1) := by
    rw [show (m + 1) * (m * catalan m) = m * ((m + 1) * catalan m) from by ring]
    rw [h1, show m * (2 * m).choose m = (2 * m).choose m * m from mul_comm _ _, h2]
    ring
  exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) h3).symm

/-- `(2m+1) · catalan m = C(2m+1, m)`. -/
theorem choose_succ_two_mul_eq_succ_two_mul_catalan (m : ℕ) :
    (2 * m + 1).choose m = (2 * m + 1) * catalan m := by
  have h_binomial : (2 * m).choose m * (2 * m + 1) =
      (2 * m + 1).choose m * (m + 1) := by
    have h := Nat.choose_mul_succ_eq (2 * m) m
    have h_sub : 2 * m + 1 - m = m + 1 := by omega
    rw [h_sub] at h
    exact h
  have h_catalan : (m + 1) * catalan m = (2 * m).choose m := by
    have := succ_mul_catalan_eq_centralBinom m
    unfold Nat.centralBinom at this
    exact this
  have h_eq : (m + 1) * ((2 * m + 1) * catalan m) =
      (m + 1) * (2 * m + 1).choose m := by
    rw [show (m + 1) * ((2 * m + 1) * catalan m) =
            ((m + 1) * catalan m) * (2 * m + 1) from by ring]
    rw [h_catalan, h_binomial, mul_comm]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) h_eq).symm

/-- Symmetric form: `(2m+1) · catalan m = C(2m+1, m+1)`. -/
theorem choose_succ_two_mul_succ_eq_succ_two_mul_catalan (m : ℕ) :
    (2 * m + 1).choose (m + 1) = (2 * m + 1) * catalan m := by
  rw [show (m + 1 : ℕ) = (2 * m + 1) - m from by omega]
  rw [Nat.choose_symm (by omega : m ≤ 2 * m + 1)]
  exact choose_succ_two_mul_eq_succ_two_mul_catalan m



/-! ### Boundary case `k = 1`: unconditional proof

The Narayana formula for `k = 1`:
`n · numNCWithKBlocks s 1 = C(n, 1) · C(n, 0) = n`.
Since `numNCWithKBlocks s 1 = 1` (the unique 1-block NC is `top hs`), both
sides equal `s.card`. This case does NOT need the Narayana axiom — it
follows directly from `numBlocks_eq_one_iff_top` (already in `NCOrder.lean`). -/

/-- For non-empty `s`, the number of NCs with exactly `1` block is `1`
(it's the indiscrete partition `top hs`). -/
theorem numNCWithKBlocks_one (s : Finset α) (hs : s.Nonempty) :
    numNCWithKBlocks s 1 = 1 := by
  unfold numNCWithKBlocks
  rw [Finset.card_eq_one]
  refine ⟨top hs, ?_⟩
  ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact numBlocks_eq_one_iff_top hs π

/-- **Narayana formula at `k = 1`** (unconditional): `n · N(n, 1) = n`. -/
theorem narayana_count_formula_one (s : Finset α) (hs : s.Nonempty) :
    (s.card : ℤ) * (numNCWithKBlocks s 1 : ℤ) =
      (s.card.choose 1 : ℤ) * (s.card.choose 0 : ℤ) := by
  rw [numNCWithKBlocks_one s hs]
  push_cast
  rw [Nat.choose_one_right, Nat.choose_zero_right]
  ring

/-- For any `s`, the number of NCs with exactly `s.card` blocks is `1`
(it's the discrete partition `bot s` with all singletons). -/
theorem numNCWithKBlocks_card (s : Finset α) :
    numNCWithKBlocks s s.card = 1 := by
  unfold numNCWithKBlocks
  rw [Finset.card_eq_one]
  refine ⟨bot s, ?_⟩
  ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact numBlocks_eq_card_iff_bot π

/-- **Narayana formula at `k = s.card`** (unconditional):
`n · N(n, n) = 1 · n = n`. -/
theorem narayana_count_formula_card (s : Finset α) (hs : 1 ≤ s.card) :
    (s.card : ℤ) * (numNCWithKBlocks s s.card : ℤ) =
      (s.card.choose s.card : ℤ) * (s.card.choose (s.card - 1) : ℤ) := by
  rw [numNCWithKBlocks_card s]
  have h2 : s.card.choose (s.card - 1) = s.card := by
    rw [Nat.choose_symm hs, Nat.choose_one_right]
  push_cast
  rw [Nat.choose_self, h2]
  ring

/-! ### Specific small-`n` instances: unconditional proofs

These provide concrete instances of the Narayana count formula
for small `n`, derived from `sum_numNCWithKBlocks_eq_catalan` plus
the boundary cases. -/

/-- For `n = 3`, the middle case `numNCWithKBlocks ... 2 = 3`. -/
theorem numNCWithKBlocks_fin_three_two :
    numNCWithKBlocks (Finset.univ : Finset (Fin 3)) 2 = 3 := by
  have hs : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
  have hs_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty :=
    Finset.univ_nonempty
  have h_total :
      ∑ k ∈ Finset.range 4,
        numNCWithKBlocks (Finset.univ : Finset (Fin 3)) k = 5 := by
    have h_sum := sum_numNCWithKBlocks_eq_catalan
      (Finset.univ : Finset (Fin 3))
    rw [hs, catalan_three] at h_sum
    convert h_sum using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h_total
  have h_zero : numNCWithKBlocks (Finset.univ : Finset (Fin 3)) 0 = 0 :=
    numNCWithKBlocks_zero_of_pos _ (by rw [hs]; norm_num)
  have h_one : numNCWithKBlocks (Finset.univ : Finset (Fin 3)) 1 = 1 :=
    numNCWithKBlocks_one _ hs_nonempty
  have h_three : numNCWithKBlocks (Finset.univ : Finset (Fin 3)) 3 = 1 := by
    have h_eq : (3 : ℕ) = (Finset.univ : Finset (Fin 3)).card := hs.symm
    rw [h_eq]
    exact numNCWithKBlocks_card _
  rw [h_zero, h_one, h_three] at h_total
  omega

/-- **Narayana formula verified for `n = 3, k = 2`** (unconditional):
`3 · 3 = C(3, 2) · C(3, 1) = 9`. -/
theorem narayana_count_formula_fin_three_two :
    ((Finset.univ : Finset (Fin 3)).card : ℤ) *
      (numNCWithKBlocks (Finset.univ : Finset (Fin 3)) 2 : ℤ) =
    ((Finset.univ : Finset (Fin 3)).card.choose 2 : ℤ) *
      ((Finset.univ : Finset (Fin 3)).card.choose 1 : ℤ) := by
  have hs : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
  rw [numNCWithKBlocks_fin_three_two, hs]
  norm_num

/-- **Alternating decomposition of `signedNCCount`**:
`signedNCCount s = ∑_{k=0}^{s.card} (-1)^k · numNCWithKBlocks s k`.

This regroups the sum `∑_π (-1)^numBlocks π` by block count, which is
the standard step preceding application of the Narayana formula. -/
theorem signedNCCount_eq_sum_alt (s : Finset α) :
    signedNCCount s =
      ∑ k ∈ Finset.range (s.card + 1),
        (-1 : ℤ) ^ k * (numNCWithKBlocks s k : ℤ) := by
  unfold signedNCCount
  have h_biUnion :
      ((Finset.range (s.card + 1)).biUnion
        (fun k => (Finset.univ : Finset (NC s)).filter
          (fun π => numBlocks π = k))) = Finset.univ := by
    ext π
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
               Finset.mem_univ, true_and, iff_true]
    refine ⟨numBlocks π, ?_, rfl⟩
    have := numBlocks_le_card π
    omega
  conv_lhs => rw [← h_biUnion]
  rw [Finset.sum_biUnion (numBlocks_filter_pairwiseDisjoint s _)]
  apply Finset.sum_congr rfl
  intros k _
  trans (∑ _π ∈ (Finset.univ : Finset (NC s)).filter
      (fun π => numBlocks π = k), (-1 : ℤ) ^ k)
  · apply Finset.sum_congr rfl
    intros π hπ
    rw [Finset.mem_filter] at hπ
    rw [hπ.2]
  · rw [Finset.sum_const]
    unfold numNCWithKBlocks
    rw [nsmul_eq_mul]
    ring


theorem signedNCCount_fin_one :
    signedNCCount (Finset.univ : Finset (Fin 1)) = -1 := by
  rw [signedNCCount_eq_sum_alt]
  have hs : (Finset.univ : Finset (Fin 1)).card = 1 := by simp
  rw [hs]
  have h_zero : numNCWithKBlocks (Finset.univ : Finset (Fin 1)) 0 = 0 :=
    numNCWithKBlocks_zero_of_pos _ (by rw [hs])
  have h_one : numNCWithKBlocks (Finset.univ : Finset (Fin 1)) 1 = 1 :=
    numNCWithKBlocks_one _ Finset.univ_nonempty
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h_zero, h_one]
  norm_num


theorem signedNCCount_fin_two :
    signedNCCount (Finset.univ : Finset (Fin 2)) = 0 := by
  rw [signedNCCount_eq_sum_alt]
  have hs : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
  rw [hs]
  have h_zero : numNCWithKBlocks (Finset.univ : Finset (Fin 2)) 0 = 0 :=
    numNCWithKBlocks_zero_of_pos _ (by rw [hs]; norm_num)
  have h_one : numNCWithKBlocks (Finset.univ : Finset (Fin 2)) 1 = 1 :=
    numNCWithKBlocks_one _ Finset.univ_nonempty
  have h_two : numNCWithKBlocks (Finset.univ : Finset (Fin 2)) 2 = 1 := by
    have h_eq : (2 : ℕ) = (Finset.univ : Finset (Fin 2)).card := hs.symm
    rw [h_eq]
    exact numNCWithKBlocks_card _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h_zero, h_one, h_two]
  norm_num


theorem signedNCCount_fin_three :
    signedNCCount (Finset.univ : Finset (Fin 3)) = 1 := by
  rw [signedNCCount_eq_sum_alt]
  have hs : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
  rw [hs]
  have h_zero : numNCWithKBlocks (Finset.univ : Finset (Fin 3)) 0 = 0 :=
    numNCWithKBlocks_zero_of_pos _ (by rw [hs]; norm_num)
  have h_one : numNCWithKBlocks (Finset.univ : Finset (Fin 3)) 1 = 1 :=
    numNCWithKBlocks_one _ Finset.univ_nonempty
  have h_two : numNCWithKBlocks (Finset.univ : Finset (Fin 3)) 2 = 3 :=
    numNCWithKBlocks_fin_three_two
  have h_three : numNCWithKBlocks (Finset.univ : Finset (Fin 3)) 3 = 1 := by
    have h_eq : (3 : ℕ) = (Finset.univ : Finset (Fin 3)).card := hs.symm
    rw [h_eq]
    exact numNCWithKBlocks_card _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h_zero, h_one, h_two, h_three]
  norm_num

end NC

end Hamilton.Infrastructure
