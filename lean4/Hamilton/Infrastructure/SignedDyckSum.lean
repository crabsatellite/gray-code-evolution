/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCToDyckInjectivityClosure
import Hamilton.Infrastructure.DyckPeaks
import Hamilton.Infrastructure.NCBipartiteCounts
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Signed Dyck Sum — bypass route for bipartite imbalance

Instead of going through the full Narayana formula (cycle lemma), we directly
compute `signedNCCount(Fin n)` via the toDyckWord bijection and a firstReturn
recurrence on `signedDyckSum`.

This route gives an UNCONDITIONAL proof of `signedNCCount ≠ 0` for odd `n ≥ 1`,
bypassing the cycle lemma entirely. The Narayana formula itself remains open,
but for the **bipartite imbalance application** (which is what the negative
direction of NCR Hamilton conjecture needs), we close it directly.

## Strategy

1. `signedDyckSum n` = `∑_{D : DyckWord, semilength = n} (-1)^{peakCount D}`.
2. Via toDyckWord (peakCount = numBlocks, INJECTIVE, hence BIJECTIVE by
   Catalan count): `signedNCCount(Fin n) = signedDyckSum n`.
3. firstReturn recurrence:
   `signedDyckSum n = -signedDyckSum (n-1) + ∑_{i=1}^{n-1} signedDyckSum i · signedDyckSum (n-1-i)`.
4. Closed form by induction:
   - `signedDyckSum (2m) = 0` for `m ≥ 1`.
   - `signedDyckSum (2m+1) = (-1)^{m+1} · Catalan m`.
5. Conclude `signedNCCount(Fin n) ≠ 0` for odd `n ≥ 1`.

## Main definitions

* `signedDyckSum n` — the integer alternating sum.

## Main results (planned)

* `signedDyckSum_zero` — base value.
* `signedDyckSum_recurrence` — firstReturn-based recurrence.
* `signedDyckSum_even_pos` — vanishes for even `n ≥ 2`.
* `signedDyckSum_odd` — closed form for odd `n`.
* `signedNCCount_eq_signedDyckSum` — bijection bridge.
* `signedNCCount_fin_odd_ne_zero_unconditional` — final consequence.

## Tags

DyckWord, signed sum, Catalan, bipartite imbalance, Narayana bypass
-/

namespace Hamilton.Infrastructure

namespace NC

open DyckWord DyckStep

/-- Signed sum over Dyck words: `∑ (-1)^{peakCount D}` for `D` of semilength `n`. -/
noncomputable def signedDyckSum (n : ℕ) : ℤ :=
  ∑ p ∈ (Finset.univ : Finset { p : DyckWord // p.semilength = n }),
    (-1 : ℤ) ^ p.val.peakCount

/-- For `n = 0`: only the empty Dyck word, peakCount 0, sign +1. -/
theorem signedDyckSum_zero : signedDyckSum 0 = 1 := by
  unfold signedDyckSum
  -- Sum over the subtype, which has only one element: ⟨0, _⟩.
  have h_zero_sl : (0 : DyckWord).semilength = 0 := by
    unfold DyckWord.semilength
    show List.count U (0 : DyckWord).toList = 0
    rfl
  rw [Finset.sum_eq_single (⟨0, h_zero_sl⟩ : { p : DyckWord // p.semilength = 0 })]
  · -- The special element gives (-1)^0 = 1.
    show (-1 : ℤ) ^ (0 : DyckWord).peakCount = 1
    rw [DyckWord.peakCount_zero]
    rfl
  · -- All other elements: there are none (subtype has only one element).
    intros p _ h_ne
    exfalso
    apply h_ne
    apply Subtype.ext
    -- p.val has semilength 0, so p.val = 0.
    rw [← DyckWord.toList_eq_nil]
    show p.val.toList = []
    have h_sl : p.val.semilength = 0 := p.property
    unfold DyckWord.semilength at h_sl
    have h_count_D : p.val.toList.count D = 0 := by
      rw [← p.val.semilength_eq_count_D]
      exact h_sl
    apply List.eq_nil_iff_forall_not_mem.mpr
    intros x hx
    rcases x.dichotomy with hxU | hxD
    · subst hxU
      rw [List.count_eq_zero] at h_sl
      exact h_sl hx
    · subst hxD
      rw [List.count_eq_zero] at h_count_D
      exact h_count_D hx
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Base case: n = 1 -/

/-- For `n = 1`: only the Dyck word `nest 0` (= "UD") of peakCount 1, sign -1. -/
theorem signedDyckSum_one : signedDyckSum 1 = -1 := by
  unfold signedDyckSum
  -- The subtype {p : DyckWord // semilength p = 1} has exactly one element: nest 0.
  have h_nest0_sl : (nest 0).semilength = 1 := by
    rw [semilength_nest]
    show (0 : DyckWord).semilength + 1 = 1
    show List.count U (0 : DyckWord).toList + 1 = 1
    rfl
  rw [Finset.sum_eq_single (⟨nest 0, h_nest0_sl⟩ : { p : DyckWord // p.semilength = 1 })]
  · -- (-1)^{peakCount (nest 0)} = (-1)^1 = -1.
    show (-1 : ℤ) ^ (nest 0).peakCount = -1
    rw [peakCount_nest_zero]; rfl
  · -- All other elements: none (subtype is a singleton).
    intros p _ h_ne
    exfalso
    apply h_ne
    -- p.val has semilength 1, so p.val = nest 0.
    apply Subtype.ext
    -- p has semilength 1. By card_dyckWord_semilength_eq_catalan, there's only 1 such word.
    -- The element we know: nest 0. So p.val = nest 0.
    have h_card : Fintype.card { q : DyckWord // q.semilength = 1 } = 1 := by
      rw [card_dyckWord_semilength_eq_catalan]
      exact catalan_one
    have h_subsingleton : Subsingleton { q : DyckWord // q.semilength = 1 } :=
      Fintype.card_le_one_iff_subsingleton.mp (by rw [h_card])
    have : p = ⟨nest 0, h_nest0_sl⟩ := h_subsingleton.allEq _ _
    exact congrArg Subtype.val this
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Key decomposition lemma: peakCount of `nest D₁ + D₂` -/

/-- The peakCount decomposition for the firstReturn factorization: -/
theorem peakCount_nest_add (D₁ D₂ : DyckWord) :
    DyckWord.peakCount (D₁.nest + D₂) =
      DyckWord.peakCount D₁ + DyckWord.peakCount D₂ +
        (if D₁ = 0 then 1 else 0) := by
  by_cases hD₂ : D₂ = 0
  · subst hD₂
    rw [add_zero, peakCount_nest, peakCount_zero, add_zero]
  · rw [peakCount_add_of_nonzero D₁.nest D₂ D₁.nest_ne_zero hD₂]
    rw [peakCount_nest]
    ring

/-! ### Semilength facts for the firstReturn decomposition -/

/-- For `p` of semilength `n ≥ 1`, `p` is nonzero. -/
theorem ne_zero_of_semilength_pos {p : DyckWord} {n : ℕ} (hn : 1 ≤ n)
    (hp : p.semilength = n) : p ≠ 0 := by
  intro h_zero
  rw [h_zero] at hp
  have h0 : (0 : DyckWord).semilength = 0 := rfl
  omega

/-- For `p` of semilength `n ≥ 1`, `p.insidePart.semilength < n`. -/
theorem insidePart_semilength_lt_of_sl (p : DyckWord) (n : ℕ) (hn : 1 ≤ n)
    (hp : p.semilength = n) :
    p.insidePart.semilength < n := by
  have hp_ne : p ≠ 0 := ne_zero_of_semilength_pos hn hp
  rw [← hp]
  exact DyckWord.semilength_insidePart_lt hp_ne

/-- For `p` of semilength `n ≥ 1`, `p.outsidePart.semilength = n - 1 - p.insidePart.semilength`. -/
theorem outsidePart_semilength_of_sl (p : DyckWord) (n : ℕ) (hn : 1 ≤ n)
    (hp : p.semilength = n) :
    p.outsidePart.semilength = n - 1 - p.insidePart.semilength := by
  have hp_ne : p ≠ 0 := ne_zero_of_semilength_pos hn hp
  have h_sum := DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one hp_ne
  omega

/-! ### Inverse: nest D₁ + D₂ has semilength D₁.sl + D₂.sl + 1 -/

/-- The semilength of `nest D₁ + D₂` is `D₁.semilength + D₂.semilength + 1`. -/
theorem semilength_nest_add (D₁ D₂ : DyckWord) :
    (D₁.nest + D₂).semilength = D₁.semilength + D₂.semilength + 1 := by
  rw [DyckWord.semilength_add, DyckWord.semilength_nest, Nat.add_right_comm]

/-! ### firstReturn decomposition: insidePart and outsidePart of `nest D₁ + D₂` -/

/-- For `nest D₁ + D₂`, the insidePart is `D₁`. -/
theorem insidePart_nest_add (D₁ D₂ : DyckWord) :
    (D₁.nest + D₂).insidePart = D₁ := by
  rw [DyckWord.insidePart_add D₁.nest_ne_zero, DyckWord.insidePart_nest]

/-- For `nest D₁ + D₂`, the outsidePart is `D₂`. -/
theorem outsidePart_nest_add (D₁ D₂ : DyckWord) :
    (D₁.nest + D₂).outsidePart = D₂ := by
  rw [DyckWord.outsidePart_add D₁.nest_ne_zero, DyckWord.outsidePart_nest, zero_add]


/-! ### Bijection bridge: signedNCCount = signedDyckSum -/

variable {α : Type*} [LinearOrder α]

/-- **MAIN BRIDGE**: `signedNCCount s = signedDyckSum s.card`.

Via the (unconditional) `toDyckWord` bijection between `NC s` and Dyck words
of semilength `s.card`, with `peakCount = numBlocks` preservation. -/
theorem signedNCCount_eq_signedDyckSum (s : Finset α) :
    signedNCCount s = signedDyckSum s.card := by
  unfold signedNCCount signedDyckSum
  -- toDyckWord bijection NC s ≃ {D : DyckWord // semilength D = s.card}.
  let e : NC s ≃ { p : DyckWord // p.semilength = s.card } :=
    toDyckWordEquiv s toDyckWord_injective
  -- Use sum_bij with e.
  apply Finset.sum_bij (fun π _ => e π)
  · -- well-defined: e π ∈ univ.
    intros π _
    exact Finset.mem_univ _
  · -- injectivity.
    intros π _ π' _ h_eq
    exact e.injective h_eq
  · -- surjectivity.
    intros p _
    refine ⟨e.symm p, Finset.mem_univ _, ?_⟩
    exact e.apply_symm_apply p
  · -- equation: (-1)^numBlocks π = (-1)^peakCount (e π).val.
    intros π _
    show (-1 : ℤ) ^ numBlocks π = (-1 : ℤ) ^ (e π).val.peakCount
    have h_eq : (e π).val = toDyckWord π := rfl
    rw [h_eq, toDyckWord_peakCount]

end NC

end Hamilton.Infrastructure
