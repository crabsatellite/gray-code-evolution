/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCToDyckWord

/-!
# Injectivity of `toDyckWord`

`toDyckWord : NC s → DyckWord` is injective.

## Strategy

For any two NCs π, π' on `s` with `toDyckList π = toDyckList π'`:

1. They have the same step lengths: `length(stepEncoding π i) = length(stepEncoding π' i)`
   for each `i ∈ s` (via comparing cumulative lengths).
2. They have the same "is block-max" and "block size" data.
3. By the **NC determined by (blockMaxes, block sizes)** lemma, the partitions are equal.

The third step requires showing that for a non-crossing partition, the data
(blockMaxes, |part b| for each b ∈ blockMaxes) uniquely determines the partition.

## Main results

* `NC.toDyckList_eq_implies_stepEncoding_lengths_eq` — step lengths agree.
* `NC.toDyckList_injective` — `toDyckList` is injective (planned).

## Tags

NC, DyckWord, injective, stack encoding, bijection
-/

namespace Hamilton.Infrastructure

namespace NC

open DyckStep List

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-! ### Cumulative step lengths -/

/-- Cumulative length of stepEncoding over first `j` elements of sorted `s`. -/
noncomputable def cumStepLength (π : NC s) (j : ℕ) : ℕ :=
  (((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π)).length

/-- Cumulative length equals 0 for j = 0. -/
@[simp] theorem cumStepLength_zero (π : NC s) : cumStepLength π 0 = 0 := by
  unfold cumStepLength
  simp

/-- Cumulative length is monotone in j. -/
theorem cumStepLength_mono (π : NC s) {j₁ j₂ : ℕ} (h : j₁ ≤ j₂) :
    cumStepLength π j₁ ≤ cumStepLength π j₂ := by
  unfold cumStepLength
  exact ((List.take_sublist_take_left h).flatMap (stepEncoding π)).length_le

/-- Successor: `cumStepLength π (j+1) = cumStepLength π j + length(stepEncoding π i_j)`
    when `j < s.card`. -/
theorem cumStepLength_succ (π : NC s) (j : ℕ) (h : j < (s.sort (· ≤ ·)).length) :
    cumStepLength π (j + 1) =
      cumStepLength π j + (stepEncoding π ((s.sort (· ≤ ·))[j]'h)).length := by
  unfold cumStepLength
  rw [List.take_succ_eq_append_getElem h, List.flatMap_append]
  simp [List.flatMap_cons, List.flatMap_nil, List.length_append]

/-- Cumulative length at `s.card` equals the total `toDyckList` length. -/
theorem cumStepLength_s_card (π : NC s) :
    cumStepLength π s.card = (toDyckList π).length := by
  unfold cumStepLength toDyckList
  rw [take_sort_card_eq_sort]

/-- Cumulative length at step `s.card` equals `2 * s.card`. -/
theorem cumStepLength_s_card_eq (π : NC s) :
    cumStepLength π s.card = 2 * s.card := by
  rw [cumStepLength_s_card, toDyckList_length]

/-- Cumulative length at step `j` is bounded by `2 * s.card`. -/
theorem cumStepLength_le (π : NC s) (j : ℕ) :
    cumStepLength π j ≤ 2 * s.card := by
  by_cases h : j ≤ s.card
  · calc cumStepLength π j ≤ cumStepLength π s.card := cumStepLength_mono π h
      _ = 2 * s.card := cumStepLength_s_card_eq π
  · push Not at h
    have h_eq : cumStepLength π j = cumStepLength π s.card := by
      unfold cumStepLength
      congr 1
      rw [List.take_of_length_le (by rw [Finset.length_sort]; omega : (s.sort (· ≤ ·)).length ≤ j),
          take_sort_card_eq_sort]
    rw [h_eq, cumStepLength_s_card_eq]

/-- Count of `U` in the first `j`-step flatMap: equals `min j s.card`. -/
theorem cumStepLength_count_U_take (π : NC s) (j : ℕ) :
    ((toDyckList π).take (cumStepLength π j)).count U = min j s.card := by
  unfold cumStepLength toDyckList
  -- (toDyckList).take (length of j-step flatMap) = j-step flatMap.
  have h_take_eq :
      (((s.sort (· ≤ ·)).flatMap (stepEncoding π)).take
        (((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π)).length) =
        ((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π) := by
    have h_eq : (s.sort (· ≤ ·)).flatMap (stepEncoding π) =
        ((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π) ++
        ((s.sort (· ≤ ·)).drop j).flatMap (stepEncoding π) := by
      rw [← List.flatMap_append, List.take_append_drop]
    rw [h_eq]
    rw [List.take_append_of_le_length (le_refl _)]
    rw [List.take_of_length_le (le_refl _)]
  rw [h_take_eq]
  rw [count_U_flatMap_stepEncoding]
  rw [List.length_take, Finset.length_sort]

/-! ### Drop characterization: toDyckList after cumStepLength chars -/

/-- The drop of `toDyckList π` after `cumStepLength π j` chars equals the flatMap
over the **remaining** elements `(s.sort).drop j`. -/
theorem toDyckList_drop_cumStepLength (π : NC s) (j : ℕ) :
    (toDyckList π).drop (cumStepLength π j) =
      ((s.sort (· ≤ ·)).drop j).flatMap (stepEncoding π) := by
  unfold toDyckList cumStepLength
  have h_decomp : (s.sort (· ≤ ·)).flatMap (stepEncoding π) =
      ((s.sort (· ≤ ·)).take j).flatMap (stepEncoding π) ++
      ((s.sort (· ≤ ·)).drop j).flatMap (stepEncoding π) := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [h_decomp]
  exact List.drop_left

/-! ### stepEncoding's structural shape -/

/-- stepEncoding is `[U]` exactly when `i` is not block-max. -/
theorem stepEncoding_eq_singleton_iff (π : NC s) (i : α) :
    stepEncoding π i = [U] ↔ ¬ (∀ k ∈ π.val.part i, k ≤ i) ∨ (π.val.part i).card = 0 := by
  unfold stepEncoding
  split_ifs with h
  · -- block-max branch: encoding = U :: replicate card D
    constructor
    · intro h_eq
      -- (U :: replicate card D) = [U] implies replicate card D = [] implies card = 0.
      right
      have h_len : (U :: List.replicate (π.val.part i).card D).length = ([U] : List DyckStep).length := by
        rw [h_eq]
      rw [List.length_cons, List.length_singleton, List.length_replicate] at h_len
      omega
    · intro h_or
      rcases h_or with h_not | h_card
      · exact absurd h h_not
      · rw [h_card, List.replicate_zero]
  · -- non-block-max: encoding = [U]
    simp [h]

/-- For elements `i ∈ s`, stepEncoding is `[U]` iff `i` is not block-max. -/
theorem stepEncoding_eq_singleton_iff_of_mem (π : NC s) {i : α} (h_in : i ∈ s) :
    stepEncoding π i = [U] ↔ ¬ (∀ k ∈ π.val.part i, k ≤ i) := by
  rw [stepEncoding_eq_singleton_iff]
  constructor
  · rintro (h | h)
    · exact h
    · -- card = 0 contradicts i ∈ s (then part i is non-empty since i ∈ part i).
      exfalso
      have h_i_in_part : i ∈ π.val.part i := π.val.mem_part_self.mpr h_in
      rw [Finset.card_eq_zero] at h
      rw [h] at h_i_in_part
      exact (Finset.notMem_empty _) h_i_in_part
  · intro h
    left; exact h

/-! ### Length of `stepEncoding` characterization -/

/-- For non-block-max `i`, stepEncoding length is `1`. -/
theorem stepEncoding_length_eq_one_of_not_blockMax (π : NC s) (i : α)
    (h : ¬ ∀ k ∈ π.val.part i, k ≤ i) :
    (stepEncoding π i).length = 1 := by
  unfold stepEncoding
  rw [if_neg h]
  rfl

/-- For block-max `i ∈ s`, stepEncoding length is `1 + |part i|`. -/
theorem stepEncoding_length_eq_succ_card_of_blockMax (π : NC s) (i : α)
    (h : ∀ k ∈ π.val.part i, k ≤ i) :
    (stepEncoding π i).length = 1 + (π.val.part i).card := by
  unfold stepEncoding
  rw [if_pos h, List.length_cons, List.length_replicate, Nat.add_comm]

/-- `stepEncoding` length is at least 1. -/
theorem stepEncoding_length_pos (π : NC s) (i : α) :
    1 ≤ (stepEncoding π i).length := by
  unfold stepEncoding
  split_ifs with h
  · rw [List.length_cons, List.length_replicate]; omega
  · rfl

/-! ### When both NCs have non-block-max at position `j`, step encodings agree -/

/-- If `i ∈ s` and both `π, π'` have `i` not as block-max, then their stepEncodings
at `i` are both `[U]`, hence equal. -/
theorem stepEncoding_eq_of_both_not_blockMax (π π' : NC s) {i : α} (h_in : i ∈ s)
    (hbm : ¬ ∀ k ∈ π.val.part i, k ≤ i)
    (hbm' : ¬ ∀ k ∈ π'.val.part i, k ≤ i) :
    stepEncoding π i = stepEncoding π' i := by
  rw [(stepEncoding_eq_singleton_iff_of_mem π h_in).mpr hbm,
      (stepEncoding_eq_singleton_iff_of_mem π' h_in).mpr hbm']

/-! ### When both NCs have block-max at position `j` with same block size, agree -/

/-- For block-max `i`, the stepEncoding has the explicit form `U :: replicate |part i| D`. -/
theorem stepEncoding_blockMax_form (π : NC s) (i : α) (h : ∀ k ∈ π.val.part i, k ≤ i) :
    stepEncoding π i = U :: List.replicate (π.val.part i).card D := by
  unfold stepEncoding
  rw [if_pos h]

/-- If both `π, π'` have `i` as block-max with the same block size, their stepEncodings agree. -/
theorem stepEncoding_eq_of_both_blockMax_same_size (π π' : NC s) {i : α}
    (hbm : ∀ k ∈ π.val.part i, k ≤ i)
    (hbm' : ∀ k ∈ π'.val.part i, k ≤ i)
    (h_size : (π.val.part i).card = (π'.val.part i).card) :
    stepEncoding π i = stepEncoding π' i := by
  rw [stepEncoding_blockMax_form π i hbm, stepEncoding_blockMax_form π' i hbm', h_size]

/-! ### "rest" structure: flatMap of non-empty list starts with U -/

/-- A non-empty list flat-mapped by `stepEncoding` produces a list starting with `U`. -/
theorem flatMap_stepEncoding_head_eq_U (π : NC s) (l : List α) (h : l ≠ []) :
    (l.flatMap (stepEncoding π)).head? = some U := by
  rcases l with _ | ⟨head, tail⟩
  · exact (h rfl).elim
  · rw [List.flatMap_cons, List.head?_append]
    rw [stepEncoding_head_eq_U π head]
    rfl

/-- For `j+1 < (s.sort).length`, the "rest after step `j`" starts with `U`. -/
theorem flatMap_drop_succ_head_eq_U (π : NC s) {j : ℕ}
    (h : j + 1 < (s.sort (· ≤ ·)).length) :
    (((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π)).head? = some U := by
  apply flatMap_stepEncoding_head_eq_U
  intro h_eq
  have h_len : ((s.sort (· ≤ ·)).drop (j + 1)).length = 0 := by rw [h_eq]; simp
  rw [List.length_drop] at h_len
  omega

/-! ### List equality decomposition for stepEncoding-style suffixes -/

/-- A foundational list lemma: if `a ++ x = a ++ replicate n D ++ y`,
where `x` either starts with `U` or is empty, then `n = 0` and `x = y`.

Used to show two block-max stepEncodings (both `U :: replicate D`) must have
the same `replicate` size — the "extra" D's would conflict with the `U`-head
of the rest list. -/
theorem append_replicate_D_eq_iff_n_zero {a x y : List DyckStep} (n : ℕ)
    (h_eq : a ++ x = a ++ List.replicate n D ++ y)
    (h_x : x = [] ∨ x.head? = some U) :
    n = 0 := by
  have h_cancel : x = List.replicate n D ++ y := by
    rw [List.append_assoc] at h_eq
    exact List.append_cancel_left h_eq
  by_contra h_ne
  have h_pos : 1 ≤ n := Nat.pos_of_ne_zero h_ne
  rcases h_x with h_empty | h_head
  · -- x = []
    rw [h_empty] at h_cancel
    have h_len : (List.replicate n D ++ y).length = ([] : List DyckStep).length :=
      congrArg List.length h_cancel.symm
    rw [List.length_append, List.length_replicate, List.length_nil] at h_len
    omega
  · -- x.head? = some U
    rw [h_cancel] at h_head
    -- (replicate n D ++ y).head? = some D (since n ≥ 1)
    have h_head_D : (List.replicate n D ++ y).head? = some D := by
      cases n with
      | zero => omega
      | succ n_pred =>
        rw [List.replicate_succ, List.cons_append]
        rfl
    rw [h_head_D] at h_head
    exact dyckStep_D_ne_U (Option.some.inj h_head)

/-! ### Symmetric version and "rest" structure helper -/

/-- Symmetric version of `append_replicate_D_eq_iff_n_zero`. -/
theorem append_replicate_D_eq_iff_n_zero_symm {a x y : List DyckStep} (n : ℕ)
    (h_eq : a ++ List.replicate n D ++ y = a ++ x)
    (h_x : x = [] ∨ x.head? = some U) :
    n = 0 :=
  append_replicate_D_eq_iff_n_zero n h_eq.symm h_x

/-- The "rest" `flatMap` of `(s.sort).drop (j+1)` is either empty or starts with `U`. -/
theorem rest_drop_succ_or (π : NC s) (j : ℕ) :
    ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π) = [] ∨
    (((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π)).head? = some U := by
  by_cases h_last : j + 1 < s.card
  · right
    exact flatMap_drop_succ_head_eq_U π (by rw [Finset.length_sort]; exact h_last)
  · left
    push Not at h_last
    have h_drop_empty : (s.sort (· ≤ ·)).drop (j + 1) = [] := by
      apply List.drop_eq_nil_of_le
      rw [Finset.length_sort]; omega
    rw [h_drop_empty]
    rfl

/-! ### Step length agreement -/

private lemma getElem_sort_mem_s {s : Finset α} (j : ℕ) (hj : j < s.card) :
    (s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj) ∈ s := by
  have h_mem := List.getElem_mem
    (l := s.sort (· ≤ ·)) (h := by rw [Finset.length_sort]; exact hj)
  rwa [Finset.mem_sort] at h_mem

private lemma part_card_pos_of_mem (π : NC s) {i : α} (h : i ∈ s) :
    1 ≤ (π.val.part i).card :=
  Finset.card_pos.mpr ⟨i, π.val.mem_part_self.mpr h⟩

/-- **STEP LENGTH AGREEMENT**: For two NCs `π, π'` with the same drop, the stepEncoding
lengths at position `j` agree.  Case analysis on block-max status, using
`append_replicate_D_eq_iff_n_zero` for contradictions/size derivation. -/
theorem stepEncoding_length_eq_of_drops_eq (π π' : NC s) (j : ℕ) (hj : j < s.card)
    (h : ((s.sort (· ≤ ·)).drop j).flatMap (stepEncoding π) =
         ((s.sort (· ≤ ·)).drop j).flatMap (stepEncoding π')) :
    (stepEncoding π ((s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj))).length =
    (stepEncoding π' ((s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj))).length := by
  set i := (s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj) with h_i_def
  have h_sort_len : j < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hj
  have h_drop_split : (s.sort (· ≤ ·)).drop j = i :: ((s.sort (· ≤ ·)).drop (j + 1)) :=
    List.drop_eq_getElem_cons h_sort_len
  rw [h_drop_split, List.flatMap_cons, List.flatMap_cons] at h
  have h_i_in_s : i ∈ s := getElem_sort_mem_s j hj
  have h_card_π_pos := part_card_pos_of_mem π h_i_in_s
  have h_card_π'_pos := part_card_pos_of_mem π' h_i_in_s
  have h_rest_π_or := rest_drop_succ_or π j
  have h_rest_π'_or := rest_drop_succ_or π' j
  by_cases hbm : ∀ k ∈ π.val.part i, k ≤ i
  · by_cases hbm' : ∀ k ∈ π'.val.part i, k ≤ i
    · -- both block-max: show same size via the lemma.
      rw [stepEncoding_length_eq_succ_card_of_blockMax π i hbm,
          stepEncoding_length_eq_succ_card_of_blockMax π' i hbm']
      congr 1
      rw [stepEncoding_blockMax_form π i hbm, stepEncoding_blockMax_form π' i hbm'] at h
      have h_tail : List.replicate (π.val.part i).card D ++
            ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π) =
          List.replicate (π'.val.part i).card D ++
            ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π') := by
        have h_t := congrArg List.tail h
        simpa using h_t
      by_cases h_le : (π.val.part i).card ≤ (π'.val.part i).card
      · -- π card ≤ π' card. Use lemma.
        have h_split : List.replicate (π'.val.part i).card D =
            List.replicate (π.val.part i).card D ++
            List.replicate ((π'.val.part i).card - (π.val.part i).card) D := by
          rw [← List.replicate_add]; congr 1; omega
        rw [h_split] at h_tail
        have h_zero := append_replicate_D_eq_iff_n_zero
          ((π'.val.part i).card - (π.val.part i).card) h_tail h_rest_π_or
        omega
      · -- π' card < π card. Symmetric.
        push Not at h_le
        have h_split : List.replicate (π.val.part i).card D =
            List.replicate (π'.val.part i).card D ++
            List.replicate ((π.val.part i).card - (π'.val.part i).card) D := by
          rw [← List.replicate_add]; congr 1; omega
        rw [h_split] at h_tail
        have h_zero := append_replicate_D_eq_iff_n_zero_symm
          ((π.val.part i).card - (π'.val.part i).card) h_tail h_rest_π'_or
        omega
    · -- π block-max, π' not. Contradiction.
      exfalso
      rw [stepEncoding_blockMax_form π i hbm,
          (stepEncoding_eq_singleton_iff_of_mem π' h_i_in_s).mpr hbm'] at h
      have h_tail : List.replicate (π.val.part i).card D ++
            ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π) =
          ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π') := by
        have h_t := congrArg List.tail h
        simpa using h_t
      have h_zero := append_replicate_D_eq_iff_n_zero
        (a := []) (x := ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π'))
        (y := ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π))
        (π.val.part i).card (by simpa using h_tail.symm) h_rest_π'_or
      omega
  · by_cases hbm' : ∀ k ∈ π'.val.part i, k ≤ i
    · -- π not block-max, π' block-max. Symmetric contradiction.
      exfalso
      rw [(stepEncoding_eq_singleton_iff_of_mem π h_i_in_s).mpr hbm,
          stepEncoding_blockMax_form π' i hbm'] at h
      have h_tail : ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π) =
          List.replicate (π'.val.part i).card D ++
            ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π') := by
        have h_t := congrArg List.tail h
        simpa using h_t
      have h_zero := append_replicate_D_eq_iff_n_zero
        (a := []) (x := ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π))
        (y := ((s.sort (· ≤ ·)).drop (j + 1)).flatMap (stepEncoding π'))
        (π'.val.part i).card (by simpa using h_tail) h_rest_π_or
      omega
    · -- both not block-max: both [U], length 1.
      rw [stepEncoding_length_eq_one_of_not_blockMax π i hbm,
          stepEncoding_length_eq_one_of_not_blockMax π' i hbm']

/-! ### Step encoding agreement -/

/-- **STEP ENCODING AGREEMENT**: For two NCs `π, π'` with the same drop, the stepEncodings
at position `j` agree (as lists). Follows from `stepEncoding_length_eq_of_drops_eq` and
`List.append_inj_left`. -/
theorem stepEncoding_eq_of_drops_eq (π π' : NC s) (j : ℕ) (hj : j < s.card)
    (h : ((s.sort (· ≤ ·)).drop j).flatMap (stepEncoding π) =
         ((s.sort (· ≤ ·)).drop j).flatMap (stepEncoding π')) :
    stepEncoding π ((s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj)) =
    stepEncoding π' ((s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj)) := by
  set i := (s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj) with h_i_def
  have h_sort_len : j < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hj
  have h_drop_split : (s.sort (· ≤ ·)).drop j = i :: ((s.sort (· ≤ ·)).drop (j + 1)) :=
    List.drop_eq_getElem_cons h_sort_len
  rw [h_drop_split, List.flatMap_cons, List.flatMap_cons] at h
  -- h: stepEncoding π i ++ rest_π = stepEncoding π' i ++ rest_π'.
  have h_len_eq : (stepEncoding π i).length = (stepEncoding π' i).length := by
    apply stepEncoding_length_eq_of_drops_eq π π' j hj
    rw [h_drop_split, List.flatMap_cons, List.flatMap_cons]
    exact h
  exact (List.append_inj h h_len_eq).1

/-! ### cumStepLength agreement from toDyckList equality -/

/-- **CUMULATIVE LENGTH AGREEMENT**: For two NCs `π, π'` with the same `toDyckList`,
`cumStepLength` agrees at every `j`. -/
theorem cumStepLength_eq_of_toDyckList_eq (π π' : NC s)
    (h : toDyckList π = toDyckList π') (j : ℕ) :
    cumStepLength π j = cumStepLength π' j := by
  induction j with
  | zero => simp [cumStepLength_zero]
  | succ j_pred ih =>
    by_cases hj_pred : j_pred < s.card
    · rw [cumStepLength_succ π j_pred (by rw [Finset.length_sort]; exact hj_pred),
          cumStepLength_succ π' j_pred (by rw [Finset.length_sort]; exact hj_pred)]
      rw [ih]
      congr 1
      -- Need step encoding lengths equal, which follows from drops equal.
      apply stepEncoding_length_eq_of_drops_eq π π' j_pred hj_pred
      rw [← toDyckList_drop_cumStepLength π j_pred,
          ← toDyckList_drop_cumStepLength π' j_pred, ih, h]
    · -- j_pred ≥ s.card, both saturate.
      push Not at hj_pred
      have h_eq_π : cumStepLength π (j_pred + 1) = cumStepLength π s.card := by
        unfold cumStepLength
        congr 1
        rw [List.take_of_length_le (by rw [Finset.length_sort]; omega : (s.sort (· ≤ ·)).length ≤ j_pred + 1),
            take_sort_card_eq_sort]
      have h_eq_π' : cumStepLength π' (j_pred + 1) = cumStepLength π' s.card := by
        unfold cumStepLength
        congr 1
        rw [List.take_of_length_le (by rw [Finset.length_sort]; omega : (s.sort (· ≤ ·)).length ≤ j_pred + 1),
            take_sort_card_eq_sort]
      rw [h_eq_π, h_eq_π']
      rw [cumStepLength_s_card, cumStepLength_s_card, h]

/-! ### stepEncoding agreement from toDyckList equality -/

/-- **STEP ENCODING AGREEMENT FROM toDyckList**: For two NCs with same `toDyckList`,
the stepEncodings at every position agree. -/
theorem stepEncoding_eq_of_toDyckList_eq (π π' : NC s)
    (h : toDyckList π = toDyckList π') (j : ℕ) (hj : j < s.card) :
    stepEncoding π ((s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj)) =
    stepEncoding π' ((s.sort (· ≤ ·))[j]'(by rw [Finset.length_sort]; exact hj)) := by
  apply stepEncoding_eq_of_drops_eq π π' j hj
  rw [← toDyckList_drop_cumStepLength π j,
      ← toDyckList_drop_cumStepLength π' j,
      cumStepLength_eq_of_toDyckList_eq π π' h j, h]

/-! ### Per-element stepEncoding agreement (full form) -/

/-- **PER-ELEMENT stepEncoding AGREEMENT**: For two NCs with same `toDyckList`,
the stepEncodings agree for every element of `s`. -/
theorem stepEncoding_eq_of_toDyckList_eq_at_mem (π π' : NC s)
    (h : toDyckList π = toDyckList π') {i : α} (h_in : i ∈ s) :
    stepEncoding π i = stepEncoding π' i := by
  have h_mem : i ∈ s.sort (· ≤ ·) := (Finset.mem_sort _).mpr h_in
  rw [List.mem_iff_getElem] at h_mem
  obtain ⟨k, hk, hk_eq⟩ := h_mem
  rw [Finset.length_sort] at hk
  have h_step_eq := stepEncoding_eq_of_toDyckList_eq π π' h k hk
  rw [hk_eq] at h_step_eq
  exact h_step_eq

/-- **toDyckWord_injective UP TO NC UNIQUENESS**: If, given equal stepEncodings
for each element of `s`, the two NCs are equal, then `toDyckWord` is injective. -/
theorem toDyckWord_injective_of_nc_uniqueness
    (h_nc_uniq : ∀ {π π' : NC s},
      (∀ {i : α}, i ∈ s → stepEncoding π i = stepEncoding π' i) → π = π') :
    Function.Injective (toDyckWord : NC s → DyckWord) := by
  intros π π' h_eq
  have h_list_eq : toDyckList π = toDyckList π' := by
    have h_to_list := congrArg DyckWord.toList h_eq
    rwa [toDyckWord_toList, toDyckWord_toList] at h_to_list
  exact h_nc_uniq (fun h_in => stepEncoding_eq_of_toDyckList_eq_at_mem π π' h_list_eq h_in)

end NC

end Hamilton.Infrastructure
