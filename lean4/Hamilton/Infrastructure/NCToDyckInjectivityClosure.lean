/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCStackInvariant
import Hamilton.Infrastructure.NCToDyckInjective
import Hamilton.Infrastructure.NCDyckCountBridge

/-!
# toDyckWord injectivity closure

Combines two infrastructure pieces:
1. **NC uniqueness from (BM, sizes) profile** (`NCStackInvariant.eq_of_profile_eq`):
   if two NCs share `blockMaxes` and block-sizes-on-blockMaxes, they are equal.
2. **Per-element stepEncoding agreement** (`NCToDyckInjective.stepEncoding_eq_of_toDyckList_eq_at_mem`):
   if two NCs have equal `toDyckList`, their stepEncodings agree on every element of `s`.

The bridge: per-element stepEncoding equality determines (BM ↔ BM, sizes-on-BM).
Length 1 → both non-BM. Length ≥ 2 → both BM with the same size.

## Main results

* `NC.profile_eq_of_stepEncoding_eq_on_mem` — stepEncoding equality on `s` implies profile equality.
* `NC.eq_of_stepEncoding_eq_on_mem` — combining with `NC.eq_of_profile_eq` gives NC equality.
* `NC.toDyckWord_injective` — `toDyckWord` is injective (UNCONDITIONAL).

## Consequences

Applying `numNCWithKBlocks_eq_numDyckWithKPeaks_of_injective` then gives the
refined-count equality `numNCWithKBlocks s k = numDyckWithKPeaks s.card k`.

## Tags

NC, DyckWord, injective, profile, bijection
-/

namespace Hamilton.Infrastructure

namespace NC

open DyckStep List

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-! ### Per-element stepEncoding equality → profile equality -/

/-- If `stepEncoding π i = stepEncoding π' i` for `i ∈ s`, then
`i ∈ blockMaxes π ↔ i ∈ blockMaxes π'`, and (if so) the block sizes match. -/
theorem profile_eq_of_stepEncoding_eq (π π' : NC s) {i : α} (h_in : i ∈ s)
    (h_eq : stepEncoding π i = stepEncoding π' i) :
    (i ∈ blockMaxes π ↔ i ∈ blockMaxes π') ∧
    (i ∈ blockMaxes π → (π.val.part i).card = (π'.val.part i).card) := by
  refine ⟨?_, ?_⟩
  · -- Membership equivalence: via length.
    constructor
    · intro h_bm_π
      -- π's stepEncoding is U :: replicate (size) D (length ≥ 2 since size ≥ 1).
      -- π''s stepEncoding has same length → π' i ∈ BM.
      rw [mem_blockMaxes_iff_isBlockMax] at h_bm_π
      obtain ⟨_, h_max⟩ := h_bm_π
      have h_len_π : (stepEncoding π i).length = 1 + (π.val.part i).card :=
        stepEncoding_length_eq_succ_card_of_blockMax π i h_max
      have h_len_π' : (stepEncoding π' i).length = (stepEncoding π i).length := by
        rw [h_eq]
      rw [h_len_π] at h_len_π'
      -- If π' i ∉ BM: length 1. If ∈ BM: length 1 + size.
      rw [mem_blockMaxes_iff_isBlockMax]
      refine ⟨h_in, ?_⟩
      by_contra h_not_bm
      -- Then stepEncoding π' i has length 1.
      have h_len_one : (stepEncoding π' i).length = 1 :=
        stepEncoding_length_eq_one_of_not_blockMax π' i h_not_bm
      -- But h_len_π' says length = 1 + (π.val.part i).card ≥ 2 (since (π.val.part i).card ≥ 1).
      have h_card_pos : 0 < (π.val.part i).card :=
        Finset.card_pos.mpr ⟨i, π.val.mem_part_self.mpr h_in⟩
      omega
    · -- Symmetric.
      intro h_bm_π'
      rw [mem_blockMaxes_iff_isBlockMax] at h_bm_π'
      obtain ⟨_, h_max⟩ := h_bm_π'
      have h_len_π' : (stepEncoding π' i).length = 1 + (π'.val.part i).card :=
        stepEncoding_length_eq_succ_card_of_blockMax π' i h_max
      have h_len_π : (stepEncoding π i).length = (stepEncoding π' i).length := by
        rw [h_eq]
      rw [h_len_π'] at h_len_π
      rw [mem_blockMaxes_iff_isBlockMax]
      refine ⟨h_in, ?_⟩
      by_contra h_not_bm
      have h_len_one : (stepEncoding π i).length = 1 :=
        stepEncoding_length_eq_one_of_not_blockMax π i h_not_bm
      have h_card_pos : 0 < (π'.val.part i).card :=
        Finset.card_pos.mpr ⟨i, π'.val.mem_part_self.mpr h_in⟩
      omega
  · -- Size equality on BM.
    intro h_bm_π
    rw [mem_blockMaxes_iff_isBlockMax] at h_bm_π
    obtain ⟨_, h_max⟩ := h_bm_π
    have h_len_π : (stepEncoding π i).length = 1 + (π.val.part i).card :=
      stepEncoding_length_eq_succ_card_of_blockMax π i h_max
    have h_len_π_eq : (stepEncoding π i).length = (stepEncoding π' i).length := by
      rw [h_eq]
    -- π' i must be in BM (from the iff above; but here let me derive directly).
    have h_bm_π' : ∀ k ∈ π'.val.part i, k ≤ i := by
      by_contra h_not_bm
      have h_len_one : (stepEncoding π' i).length = 1 :=
        stepEncoding_length_eq_one_of_not_blockMax π' i h_not_bm
      rw [h_len_one] at h_len_π_eq
      rw [h_len_π_eq] at h_len_π
      have h_card_pos : 0 < (π.val.part i).card :=
        Finset.card_pos.mpr ⟨i, π.val.mem_part_self.mpr h_in⟩
      omega
    have h_len_π' : (stepEncoding π' i).length = 1 + (π'.val.part i).card :=
      stepEncoding_length_eq_succ_card_of_blockMax π' i h_bm_π'
    rw [h_len_π, h_len_π'] at h_len_π_eq
    omega

/-! ### Combine: NC equality from per-element stepEncoding agreement -/

/-- If `stepEncoding π i = stepEncoding π' i` for every `i ∈ s`, then `π = π'`. -/
theorem eq_of_stepEncoding_eq_on_mem (π π' : NC s)
    (h : ∀ {i : α}, i ∈ s → stepEncoding π i = stepEncoding π' i) :
    π = π' := by
  apply eq_of_profile_eq
  · -- blockMaxes π = blockMaxes π'.
    apply Finset.ext
    intro i
    by_cases hi : i ∈ s
    · exact (profile_eq_of_stepEncoding_eq π π' hi (h hi)).1
    · constructor
      · intro h_bm
        unfold blockMaxes at h_bm
        rw [Finset.mem_filter] at h_bm
        exact absurd h_bm.1 hi
      · intro h_bm
        unfold blockMaxes at h_bm
        rw [Finset.mem_filter] at h_bm
        exact absurd h_bm.1 hi
  · -- Sizes on blockMaxes π.
    intros i hi
    have h_in_s : i ∈ s := by
      unfold blockMaxes at hi
      rw [Finset.mem_filter] at hi
      exact hi.1
    exact (profile_eq_of_stepEncoding_eq π π' h_in_s (h h_in_s)).2 hi

/-! ### MAIN: toDyckWord injectivity (UNCONDITIONAL) -/

/-- **toDyckWord IS INJECTIVE** (unconditional, from real math closure). -/
theorem toDyckWord_injective :
    Function.Injective (toDyckWord : NC s → DyckWord) :=
  toDyckWord_injective_of_nc_uniqueness (fun {π π'} h => eq_of_stepEncoding_eq_on_mem π π' h)

/-! ### Unconditional refined count equality -/

/-- **UNCONDITIONAL REFINED COUNT EQUALITY**: `numNCWithKBlocks s k = numDyckWithKPeaks s.card k`.

This closes one of the two open hypotheses for the Narayana count formula. -/
theorem numNCWithKBlocks_eq_numDyckWithKPeaks (k : ℕ) :
    numNCWithKBlocks s k = numDyckWithKPeaks s.card k :=
  numNCWithKBlocks_eq_numDyckWithKPeaks_of_injective s toDyckWord_injective k

/-- **NARAYANA COUNT FORMULA — closed modulo the cycle lemma only**:

If the cycle lemma for Dyck words holds (a classical 1947 Dvoretzky-Motzkin
result), then the Narayana count formula for NCs follows. -/
theorem narayana_count_formula_modulo_cycle
    (h_cycle : ∀ k, 1 ≤ k →
      s.card * numDyckWithKPeaks s.card k = Nat.choose s.card k * Nat.choose s.card (k - 1))
    (k : ℕ) (hk : 1 ≤ k) :
    (s.card : ℤ) * (numNCWithKBlocks s k : ℤ) =
      (s.card.choose k : ℤ) * (s.card.choose (k - 1) : ℤ) :=
  narayana_count_formula_of_injective_and_cycle s toDyckWord_injective h_cycle k hk

end NC

end Hamilton.Infrastructure
