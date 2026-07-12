/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.KSPartitionByMin
import Hamilton.Infrastructure.CardNCSize
import Hamilton.Infrastructure.GapSingletonCard

/-!
# K-S sum reformulated as pair Catalan

The conjectured form: under IH `card_NC m = catalan m` for m ≤ n,
the K-S sum at n+1 equals the pair Catalan sum.

## Main results

* `NC.KS_pair_form_target` — target statement (proof: deferred to
  future rounds via inner sum evaluation).

## Tags

NC, K-S, pair Catalan, target
-/

namespace Hamilton.Infrastructure

namespace NC

/-- The **inner sum at fixed j** of the K-S sum partition.

For each `j : Fin (n+1)`, the contribution from S with `min(S) = j`
to the K-S sum.  Conjectured to equal `card_NC j.val * card_NC (n -
j.val)`. -/
noncomputable def KS_inner_sum_at (n : ℕ) (j : Fin (n+1)) : ℕ :=
  ∑ S ∈ ((Finset.univ : Finset (Fin (n+1))).powerset.filter
    (fun S => S.Nonempty ∧ Fin.last n ∈ S)) with minOrZero n S = j,
    ∏ x ∈ S.attach, card_NC
      (Finset.gapBefore (Finset.univ : Finset (Fin (n+1))) S x.1).card

/-- The full K-S sum at n+1 equals the sum of `KS_inner_sum_at j` for
`j : Fin (n+1)`. -/
theorem card_NC_eq_sum_inner (n : ℕ) :
    card_NC (n+1) = ∑ j : Fin (n+1), KS_inner_sum_at n j := by
  rw [KS_recursion_card_NC]
  exact KS_sum_by_minOrZero n _

/-- The K-S inner sum filter set at `j = Fin.last n` is `{{Fin.last n}}`. -/
theorem KS_inner_filter_at_max_eq (n : ℕ) :
    ((Finset.univ : Finset (Fin (n+1))).powerset.filter
      (fun S => S.Nonempty ∧ Fin.last n ∈ S)).filter
      (fun S => minOrZero n S = Fin.last n) =
    {({Fin.last n} : Finset (Fin (n+1)))} := by
  ext S
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hS_filter, h_min⟩
    exact KS_fiber_at_max n S hS_filter h_min
  · intro hS_eq
    subst hS_eq
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_, ?_⟩
      · exact ⟨Fin.last n, Finset.mem_singleton.mpr rfl⟩
      · exact Finset.mem_singleton.mpr rfl
    · rw [minOrZero_eq_min' n ⟨Fin.last n, Finset.mem_singleton.mpr rfl⟩]
      apply le_antisymm
      · exact Finset.min'_le _ _ (Finset.mem_singleton.mpr rfl)
      · exact Finset.le_min' _ _ _ (fun y hy => by
          rw [Finset.mem_singleton] at hy
          rw [hy])

/-- For j < Fin.last n and T ⊆ Ioi j with Fin.last n ∈ T,
`insert j T` is in the K-S filter with min = j. -/
theorem insert_j_T_in_KS_filter (n : ℕ) (j : Fin (n+1))
    {T : Finset (Fin (n+1))}
    (hT_sub : T ⊆ Finset.Ioi j) (hT_max : Fin.last n ∈ T) :
    (insert j T ∈ (Finset.univ : Finset (Fin (n+1))).powerset.filter
      (fun S => S.Nonempty ∧ Fin.last n ∈ S)) ∧
    minOrZero n (insert j T) = j := by
  have hjT_ne : (insert j T).Nonempty := ⟨j, Finset.mem_insert_self _ _⟩
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hjT_ne, ?_⟩
    exact Finset.mem_insert_of_mem hT_max
  · rw [minOrZero_eq_min' n hjT_ne]
    apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    · apply Finset.le_min' _ _ _
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx_T
      · exact le_refl _
      · exact le_of_lt (Finset.mem_Ioi.mp (hT_sub hx_T))

/-- **K-S filter S at min = j decomposes as `{j} ∪ (S \ {j})`**. -/
theorem KS_filter_at_min_decompose (n : ℕ) (j : Fin (n+1))
    {S : Finset (Fin (n+1))}
    (hS_filter : S ∈ (Finset.univ : Finset (Fin (n+1))).powerset.filter
      (fun S => S.Nonempty ∧ Fin.last n ∈ S))
    (h_min : minOrZero n S = j) :
    j ∈ S ∧ S.erase j ⊆ Finset.Ioi j := by
  have hS_ne : S.Nonempty := min_of_KS_filter_nonempty n hS_filter
  have h_min' : S.min' hS_ne = j := by
    rw [← minOrZero_eq_min' n hS_ne]; exact h_min
  refine ⟨?_, ?_⟩
  · rw [← h_min']
    exact S.min'_mem hS_ne
  · intro x hx_S
    rw [Finset.mem_erase] at hx_S
    obtain ⟨hx_ne_j, hx_mem⟩ := hx_S
    rw [Finset.mem_Ioi]
    have hx_ge : j ≤ x := h_min' ▸ S.min'_le _ hx_mem
    exact lt_of_le_of_ne hx_ge (Ne.symm hx_ne_j)

/-- The "K-S filter restricted to min = j" set. -/
noncomputable def filter_at_min_j (n : ℕ) (j : Fin (n+1)) :
    Finset (Finset (Fin (n+1))) :=
  ((Finset.univ : Finset (Fin (n+1))).powerset.filter
    (fun S => S.Nonempty ∧ Fin.last n ∈ S)).filter
    (fun S => minOrZero n S = j)

/-- The "K-S filter on Ioi j" set. -/
def filter_above_j (n : ℕ) (j : Fin (n+1)) :
    Finset (Finset (Fin (n+1))) :=
  (Finset.Ioi j).powerset.filter (fun T => T.Nonempty ∧ Fin.last n ∈ T)

/-- **Bijection between `filter_at_min_j` and `filter_above_j`** via
`insert j` / `Finset.erase j`. -/
theorem filter_at_min_j_image_eq (n : ℕ) (j : Fin (n+1)) (hj : j < Fin.last n) :
    (filter_above_j n j).image (insert j) = filter_at_min_j n j := by
  ext S
  rw [Finset.mem_image]
  unfold filter_at_min_j filter_above_j
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨T, hT_mem, hT_eq⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at hT_mem
    obtain ⟨hT_sub, hT_ne, hT_max⟩ := hT_mem
    obtain ⟨h_filter, h_min⟩ := insert_j_T_in_KS_filter n j hT_sub hT_max
    rw [← hT_eq]
    exact ⟨h_filter, h_min⟩
  · rintro ⟨h_filter, h_min⟩
    obtain ⟨hj_in, hT_sub⟩ := KS_filter_at_min_decompose n j h_filter h_min
    -- Extract Fin.last n ∈ S from h_filter.
    rw [Finset.mem_filter] at h_filter
    obtain ⟨_, _, hmax_S⟩ := h_filter
    refine ⟨S.erase j, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨hT_sub, ?_, ?_⟩
      · refine ⟨Fin.last n, ?_⟩
        rw [Finset.mem_erase]
        refine ⟨?_, hmax_S⟩
        intro h_eq
        rw [h_eq] at hj
        exact lt_irrefl _ hj
      · rw [Finset.mem_erase]
        refine ⟨?_, hmax_S⟩
        intro h_eq
        rw [h_eq] at hj
        exact lt_irrefl _ hj
    · rw [Finset.insert_erase hj_in]

/-- **At j = Fin.last n, the K-S inner sum equals `card_NC n`**. -/
theorem KS_inner_sum_at_max (n : ℕ) :
    KS_inner_sum_at n (Fin.last n) = card_NC n := by
  unfold KS_inner_sum_at
  rw [KS_inner_filter_at_max_eq, Finset.sum_singleton]
  -- prod over attach of {Fin.last n}.
  have h_attach : ({Fin.last n} : Finset (Fin (n+1))).attach =
      {⟨Fin.last n, Finset.mem_singleton.mpr rfl⟩} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_attach _ _, ?_⟩
    intro ⟨x, hx⟩ _
    apply Subtype.ext
    rw [Finset.mem_singleton] at hx
    exact hx
  rw [h_attach, Finset.prod_singleton]
  rw [gap_singleton_card]
  simp [Fin.val_last]

/-- **KS_inner_sum_at j = pair Catalan term** at `j = Fin.last n`. -/
theorem KS_inner_sum_at_max_pair (n : ℕ) :
    KS_inner_sum_at n (Fin.last n) =
      card_NC (Fin.last n).val * card_NC (n - (Fin.last n).val) := by
  rw [KS_inner_sum_at_max]
  rw [Fin.val_last]
  rw [Nat.sub_self, card_NC_zero, mul_one]

/-- For `j < Fin.last n`, `Finset.Ioi j` is nonempty. -/
theorem Ioi_j_nonempty (n : ℕ) (j : Fin (n+1)) (hj : j < Fin.last n) :
    (Finset.Ioi j).Nonempty :=
  ⟨Fin.last n, Finset.mem_Ioi.mpr hj⟩

/-- `(Finset.Ioi j).card = n - j.val` for `j : Fin (n+1)`. -/
theorem Ioi_j_card (n : ℕ) (j : Fin (n+1)) :
    (Finset.Ioi j).card = n - j.val := by
  have := Fin.card_Ioi j
  rwa [show (n + 1) - 1 = n from rfl] at this

/-- **Product decomposition over `insert j T`** via `prod_attach`
+ `prod_insert`: the K-S product over `(insert j T).attach` factors
as `card_NC j.val` times the K-S product over `T.attach` (in the
restricted Ioi j context). -/
theorem product_over_insert_j_T (n : ℕ) (j : Fin (n+1))
    {T : Finset (Fin (n+1))} (hT_sub : T ⊆ Finset.Ioi j) :
    ∏ x ∈ (insert j T).attach,
      card_NC (Finset.gapBefore (Finset.univ : Finset (Fin (n+1)))
        (insert j T) x.1).card =
    card_NC j.val * ∏ x ∈ T.attach,
      card_NC (Finset.gapBefore (Finset.Ioi j) T x.1).card := by
  have hj_notin_T : j ∉ T := fun h =>
    lt_irrefl _ (Finset.mem_Ioi.mp (hT_sub h))
  rw [Finset.prod_attach (insert j T)
    (fun x => card_NC (Finset.gapBefore (Finset.univ : Finset (Fin (n+1)))
      (insert j T) x).card)]
  rw [Finset.prod_insert hj_notin_T]
  congr 1
  · congr 1
    apply gap_at_min_card
    · exact Finset.mem_insert_self _ _
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz_T
      · exact le_refl _
      · exact le_of_lt (Finset.mem_Ioi.mp (hT_sub hz_T))
  rw [Finset.prod_attach T
    (fun x => card_NC (Finset.gapBefore (Finset.Ioi j) T x).card)]
  apply Finset.prod_congr rfl
  intro x hx_T
  rw [gap_above_j_eq n j T hT_sub x hx_T]


theorem KS_sum_on_Ioi_j (n : ℕ) (j : Fin (n+1)) (hj : j < Fin.last n) :
    (∑ T ∈ filter_above_j n j,
      ∏ x ∈ T.attach,
        card_NC (Finset.gapBefore (Finset.Ioi j) T x.1).card) =
    card_NC (n - j.val) := by
  unfold filter_above_j
  have hIoi_ne : (Finset.Ioi j).Nonempty := Ioi_j_nonempty n j hj
  have h_max : (Finset.Ioi j).max' hIoi_ne = Fin.last n := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y _
      exact Fin.le_last y
    · exact Finset.le_max' _ _ (Finset.mem_Ioi.mpr hj)
  have hKS := card_eq_sum_prod_gap (s := Finset.Ioi j) hIoi_ne
  rw [h_max] at hKS
  rw [card_NC_eq, Ioi_j_card] at hKS
  rw [hKS]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.prod_congr rfl
  intro x _
  exact (card_NC_eq _).symm

/-- **KS_inner_sum_at j = pair Catalan term** at `j < Fin.last n`. -/
theorem KS_inner_sum_at_lt_max_pair (n : ℕ) (j : Fin (n+1)) (hj : j < Fin.last n) :
    KS_inner_sum_at n j = card_NC j.val * card_NC (n - j.val) := by
  unfold KS_inner_sum_at
  show ∑ S ∈ filter_at_min_j n j, _ = _
  rw [← filter_at_min_j_image_eq n j hj]
  rw [Finset.sum_image]
  swap
  · intro T₁ hT₁ T₂ hT₂ h_eq
    rw [Finset.mem_coe] at hT₁ hT₂
    unfold filter_above_j at hT₁ hT₂
    have hT₁_sub : T₁ ⊆ Finset.Ioi j := by
      rw [Finset.mem_filter] at hT₁
      exact Finset.mem_powerset.mp hT₁.1
    have hT₂_sub : T₂ ⊆ Finset.Ioi j := by
      rw [Finset.mem_filter] at hT₂
      exact Finset.mem_powerset.mp hT₂.1
    have hj_notin_T₁ : j ∉ T₁ := fun h =>
      lt_irrefl _ (Finset.mem_Ioi.mp (hT₁_sub h))
    have hj_notin_T₂ : j ∉ T₂ := fun h =>
      lt_irrefl _ (Finset.mem_Ioi.mp (hT₂_sub h))
    have h_erase : (insert j T₁).erase j = (insert j T₂).erase j := by
      rw [h_eq]
    rw [Finset.erase_insert hj_notin_T₁, Finset.erase_insert hj_notin_T₂] at h_erase
    exact h_erase
  have h_sum_eq : (∑ T ∈ filter_above_j n j,
      ∏ x ∈ (insert j T).attach,
        card_NC (Finset.gapBefore (Finset.univ : Finset (Fin (n+1)))
          (insert j T) x.1).card)
    = (∑ T ∈ filter_above_j n j,
      card_NC j.val * ∏ x ∈ T.attach,
        card_NC (Finset.gapBefore (Finset.Ioi j) T x.1).card) := by
    apply Finset.sum_congr rfl
    intro T hT
    unfold filter_above_j at hT
    have hT_sub : T ⊆ Finset.Ioi j :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    exact product_over_insert_j_T n j hT_sub
  rw [h_sum_eq]
  rw [← Finset.mul_sum]
  rw [KS_sum_on_Ioi_j n j hj]

/-- **Universal inner sum formula**: for any `j : Fin (n+1)`,
`KS_inner_sum_at n j = card_NC j.val * card_NC (n - j.val)`. -/
theorem KS_inner_sum_at_pair (n : ℕ) (j : Fin (n+1)) :
    KS_inner_sum_at n j = card_NC j.val * card_NC (n - j.val) := by
  by_cases hj : j < Fin.last n
  · exact KS_inner_sum_at_lt_max_pair n j hj
  · push_neg at hj
    have h_le : j ≤ Fin.last n := Fin.le_last j
    have h_eq : j = Fin.last n := le_antisymm h_le hj
    rw [h_eq]
    exact KS_inner_sum_at_max_pair n

end NC

end Hamilton.Infrastructure
