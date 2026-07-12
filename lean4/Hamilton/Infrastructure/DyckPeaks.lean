/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Peak count of Dyck words

A **peak** of a Dyck word is a position where a `U` step is immediately followed
by a `D` step.  Counting peaks refines the Catalan count by the Narayana
distribution: the number of Dyck words of semilength `n` with exactly `k`
peaks is the Narayana number `N(n, k) = (1/n) · C(n, k) · C(n, k-1)`.

This file defines `DyckWord.peakCount` and proves its basic properties,
serving as the **first step** toward the Lean formalization of the Narayana
count formula (eliminating the corresponding axiom in `NarayanaCounts.lean`).

## Main definitions

* `DyckWord.countPeaksAux` — count `U :: D :: _` patterns in a list of steps.
* `DyckWord.peakCount` — number of peaks in a Dyck word.

## Main results

* `DyckWord.peakCount_zero` — empty Dyck word has no peaks.
* `DyckWord.peakCount_le_semilength` — peak count is bounded by semilength.

## Future work

* Bijection `NC s ↔ DyckWord_{semilength s.card}` preserving peak count.
* Count `# {p : DyckWord | semilength p = n ∧ peakCount p = k} = N(n, k)`
  via cycle lemma or LGV.
* Conclude `narayana_count_formula` as theorem (closing the axiom).

## Tags

Dyck word, peak count, Narayana, Catalan, bijection
-/

namespace DyckWord

open DyckStep List

/-- Auxiliary: count occurrences of consecutive `U :: D` patterns in a list of
Dyck steps. -/
def countPeaksAux : List DyckStep → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    (if a = U ∧ b = D then 1 else 0) + countPeaksAux (b :: rest)

@[simp] theorem countPeaksAux_nil : countPeaksAux [] = 0 := rfl
@[simp] theorem countPeaksAux_single (s : DyckStep) : countPeaksAux [s] = 0 := rfl

theorem countPeaksAux_cons_cons (a b : DyckStep) (rest : List DyckStep) :
    countPeaksAux (a :: b :: rest) =
      (if a = U ∧ b = D then 1 else 0) + countPeaksAux (b :: rest) := rfl

/-- Number of peaks (consecutive UD pairs) in a Dyck word. -/
def peakCount (p : DyckWord) : ℕ := countPeaksAux p.toList

@[simp] theorem peakCount_zero : peakCount 0 = 0 := rfl

/-- Peak count of a list of Dyck steps is bounded by the count of `U` steps. -/
theorem countPeaksAux_le_count_U : ∀ (l : List DyckStep),
    countPeaksAux l ≤ l.count U := by
  intro l
  induction l with
  | nil => simp
  | cons a tail ih =>
    cases tail with
    | nil => simp [countPeaksAux]
    | cons b rest =>
      rw [countPeaksAux_cons_cons]
      have h_pa_le : countPeaksAux (b :: rest) ≤ (b :: rest).count U := ih
      have h_count_ge : (a :: b :: rest).count U ≥ (b :: rest).count U := by
        rw [count_cons]; omega
      by_cases h_peak : a = U ∧ b = D
      · rw [if_pos h_peak]
        have h_count_eq : (a :: b :: rest).count U = (b :: rest).count U + 1 := by
          rw [count_cons, h_peak.1]; simp
        omega
      · rw [if_neg h_peak]; omega

/-- `peakCount p ≤ p.semilength`. -/
theorem peakCount_le_semilength (p : DyckWord) :
    p.peakCount ≤ p.semilength := by
  unfold peakCount semilength
  exact countPeaksAux_le_count_U p.toList

/-- The "simplest" non-empty Dyck word `nest 0 = [U, D]` has exactly one peak. -/
theorem peakCount_nest_zero : peakCount (nest 0) = 1 := by
  unfold peakCount nest
  -- (nest 0).toList = [U] ++ (0 : DyckWord).toList ++ [D] = [U] ++ [] ++ [D] = [U, D]
  show countPeaksAux ([U] ++ (0 : DyckWord).toList ++ [D]) = 1
  have h_zero : (0 : DyckWord).toList = [] := rfl
  rw [h_zero]
  simp [countPeaksAux]

/-- `countPeaksAux` of a singleton list is `0`. -/
@[simp] theorem countPeaksAux_singleton_eq (a : DyckStep) :
    countPeaksAux [a] = 0 := rfl

/-- `countPeaksAux` of a two-element list `[a, b]` equals the indicator of `a = U ∧ b = D`. -/
theorem countPeaksAux_pair (a b : DyckStep) :
    countPeaksAux [a, b] = (if a = U ∧ b = D then 1 else 0) := by
  rw [countPeaksAux_cons_cons]
  simp [countPeaksAux]

/-- `countPeaksAux` of `[U, D]` (one peak). -/
theorem countPeaksAux_UD : countPeaksAux [U, D] = 1 := by
  rw [countPeaksAux_pair]; simp

/-- `countPeaksAux` of `[U, U]` (no peak). -/
theorem countPeaksAux_UU : countPeaksAux [U, U] = 0 := by
  rw [countPeaksAux_pair]; simp

/-- `countPeaksAux` of `[D, U]` (no peak). -/
theorem countPeaksAux_DU : countPeaksAux [D, U] = 0 := by
  rw [countPeaksAux_pair]; simp

/-- `countPeaksAux` of `[D, D]` (no peak). -/
theorem countPeaksAux_DD : countPeaksAux [D, D] = 0 := by
  rw [countPeaksAux_pair]; simp

/-- **Append lemma for `countPeaksAux`**: peak count of concatenation equals
sum of peak counts plus boundary indicator. -/
theorem countPeaksAux_append : ∀ (l1 l2 : List DyckStep),
    countPeaksAux (l1 ++ l2) = countPeaksAux l1 + countPeaksAux l2 +
      (if l1.getLast? = some U ∧ l2.head? = some D then 1 else 0) := by
  intro l1
  induction l1 with
  | nil =>
    intro l2
    simp [countPeaksAux]
  | cons a tail ih =>
    intro l2
    cases tail with
    | nil =>
      cases l2 with
      | nil => simp [countPeaksAux]
      | cons b rest =>
        show countPeaksAux (a :: b :: rest) =
          countPeaksAux [a] + countPeaksAux (b :: rest) +
            (if [a].getLast? = some U ∧ (b :: rest).head? = some D then 1 else 0)
        rw [countPeaksAux_cons_cons, countPeaksAux_singleton_eq]
        simp only [List.getLast?_singleton, List.head?_cons, Option.some.injEq, zero_add]
        ring
    | cons b rest_tail =>
      have ih' := ih l2
      show countPeaksAux (a :: b :: (rest_tail ++ l2)) =
        countPeaksAux (a :: b :: rest_tail) + countPeaksAux l2 +
          (if (a :: b :: rest_tail).getLast? = some U ∧ l2.head? = some D then 1 else 0)
      rw [countPeaksAux_cons_cons, countPeaksAux_cons_cons]
      show (if a = U ∧ b = D then 1 else 0) + countPeaksAux ((b :: rest_tail) ++ l2) =
        (if a = U ∧ b = D then 1 else 0) + countPeaksAux (b :: rest_tail) + countPeaksAux l2 +
          (if (a :: b :: rest_tail).getLast? = some U ∧ l2.head? = some D then 1 else 0)
      rw [ih']
      have h_lastEq : (a :: b :: rest_tail).getLast? = (b :: rest_tail).getLast? := by
        simp [List.getLast?]
      rw [h_lastEq]
      ring

/-- **Peak count under DyckWord addition** for non-empty words: no peak at
the boundary, since `p` ends with `D` and `q` starts with `U`. -/
theorem peakCount_add_of_nonzero (p q : DyckWord) (hp : p ≠ 0) (hq : q ≠ 0) :
    peakCount (p + q) = peakCount p + peakCount q := by
  unfold peakCount
  show countPeaksAux (p.toList ++ q.toList) =
    countPeaksAux p.toList + countPeaksAux q.toList
  rw [countPeaksAux_append]
  have h_p_ne := toList_ne_nil.mpr hp
  have h_q_ne := toList_ne_nil.mpr hq
  have h_last : p.toList.getLast? = some D := by
    rw [List.getLast?_eq_getLast_of_ne_nil h_p_ne, getLast_eq_D p h_p_ne]
  have h_head : q.toList.head? = some U := by
    rw [List.head?_eq_some_head h_q_ne, head_eq_U q h_q_ne]
  rw [h_last, h_head]
  simp

/-- **Peak count of `nest p`** for non-empty `p`: same as `p` (the wrapping
`[U] ... [D]` adds no peaks since `p` starts with `U` and ends with `D`). -/
theorem peakCount_nest_of_ne_zero (p : DyckWord) (hp : p ≠ 0) :
    peakCount (nest p) = peakCount p := by
  unfold peakCount nest
  show countPeaksAux ([U] ++ p.toList ++ [D]) = countPeaksAux p.toList
  have h_ne := toList_ne_nil.mpr hp
  have h_head : p.toList.head? = some U := by
    rw [List.head?_eq_some_head h_ne, head_eq_U p h_ne]
  have h_last : p.toList.getLast? = some D := by
    rw [List.getLast?_eq_getLast_of_ne_nil h_ne, getLast_eq_D p h_ne]
  -- (U ≠ D) and (D ≠ U) for simp.
  have h_UD : (U : DyckStep) ≠ D := by decide
  -- [U] ++ p.toList ends with last of p.toList = D
  have h_concat_ne : ([U] ++ p.toList : List DyckStep) ≠ [] := by simp
  have h_concat_last : ([U] ++ p.toList : List DyckStep).getLast? = some D := by
    rw [List.getLast?_eq_getLast_of_ne_nil h_concat_ne]
    have h_eq : List.getLast ([U] ++ p.toList) h_concat_ne = p.toList.getLast h_ne :=
      List.getLast_append_of_right_ne_nil [U] p.toList h_ne
    rw [h_eq, getLast_eq_D p h_ne]
  rw [countPeaksAux_append, countPeaksAux_append]
  simp only [countPeaksAux_singleton_eq, zero_add]
  rw [h_concat_last]
  rw [show ([U] : List DyckStep).getLast? = some U from rfl]
  rw [h_head]
  rw [show ([D] : List DyckStep).head? = some D from rfl]
  simp [h_UD]

/-- **Peak count of `nest p`** (combined): `peakCount p + 1` if `p = 0`, else `peakCount p`. -/
theorem peakCount_nest (p : DyckWord) :
    peakCount (nest p) = peakCount p + (if p = 0 then 1 else 0) := by
  by_cases h : p = 0
  · subst h
    rw [peakCount_nest_zero, peakCount_zero, if_pos rfl]
  · rw [peakCount_nest_of_ne_zero p h, if_neg h, Nat.add_zero]

/-! ### Computational tests / specific small Dyck word peak counts -/

/-- `peakCount [U, U, D, D] = 1` (one peak in `nest (nest 0)`). -/
theorem peakCount_nest_nest_zero : peakCount (nest (nest 0)) = 1 := by
  rw [peakCount_nest, peakCount_nest_zero]
  rw [if_neg nest_ne_zero]

/-- `peakCount (nest 0 + nest 0) = 2` (two peaks in `[U, D, U, D]`). -/
theorem peakCount_nest_zero_add_nest_zero :
    peakCount (nest 0 + nest 0) = 2 := by
  rw [peakCount_add_of_nonzero (nest 0) (nest 0) nest_ne_zero nest_ne_zero,
      peakCount_nest_zero]

end DyckWord
