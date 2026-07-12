/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCToDyckInjective
import Hamilton.Infrastructure.NumDyckWithKPeaks
import Hamilton.Infrastructure.NCDyckCard
import Hamilton.Infrastructure.NarayanaCounts

/-!
# Bridge: `numNCWithKBlocks` = `numDyckWithKPeaks` (conditional on injectivity)

If `toDyckWord` is injective, the peak-preserving bijection identifies
`numNCWithKBlocks s k` with `numDyckWithKPeaks s.card k`.

## Strategy

1. Inject `toDyckWord' : NC s → {p : DyckWord // p.semilength = s.card}`.
2. By `|NC s| = |{p // p.semilength = s.card}|` (`card_eq_card_dyckWord`),
   the injection is a bijection.
3. The bijection preserves `numBlocks ↔ peakCount` (`toDyckWord_peakCount`).
4. Hence `|{π // numBlocks = k}| = |{(p, h) // peakCount p = k}|` for each k.

## Main results

* `NC.toDyckWord_subtype_inj_iff_inj` — injection ↔ bijection of the subtype map.
* `NC.numNCWithKBlocks_eq_numDyckWithKPeaks_of_injective` — the bridge.

## Tags

NC, DyckWord, bijection, peak count, Narayana
-/

namespace Hamilton.Infrastructure

namespace NC

open DyckWord

variable {α : Type*} [LinearOrder α] (s : Finset α)

/-- Subtype variant of `toDyckWord`: maps to Dyck words with `semilength = s.card`. -/
noncomputable def toDyckWordSubtype (π : NC s) : { p : DyckWord // p.semilength = s.card } :=
  ⟨toDyckWord π, toDyckWord_semilength π⟩

/-- `toDyckWordSubtype` is injective iff `toDyckWord` is. -/
theorem toDyckWordSubtype_injective_iff :
    Function.Injective (toDyckWordSubtype s) ↔ Function.Injective (toDyckWord : NC s → DyckWord) := by
  constructor
  · intro h_inj π π' h_eq
    apply h_inj
    apply Subtype.ext
    exact h_eq
  · intro h_inj π π' h_eq
    apply h_inj
    exact congrArg Subtype.val h_eq

/-! ### Bijection (conditional on injectivity) -/

/-- If `toDyckWord` is injective, then `toDyckWordSubtype` is a bijection.

Reason: the source and target are finite types of equal cardinality (`|NC s| =
catalan s.card = |{p : DyckWord // p.semilength = s.card}|`), and an injection
between finite types of equal cardinality is automatically a bijection. -/
theorem toDyckWordSubtype_bijective_of_injective
    (h_inj : Function.Injective (toDyckWord : NC s → DyckWord)) :
    Function.Bijective (toDyckWordSubtype s) := by
  have h_inj_sub : Function.Injective (toDyckWordSubtype s) :=
    (toDyckWordSubtype_injective_iff s).mpr h_inj
  -- Use Fintype.bijective_iff_injective_and_card.
  have h_card : Fintype.card (NC s) =
      Fintype.card { p : DyckWord // p.semilength = s.card } :=
    card_eq_card_dyckWord s
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨h_inj_sub, h_card⟩

/-! ### Refined count equality (conditional on injectivity) -/

/-- The equivalence `NC s ≃ {p : DyckWord // p.semilength = s.card}` from injectivity. -/
noncomputable def toDyckWordEquiv
    (h_inj : Function.Injective (toDyckWord : NC s → DyckWord)) :
    NC s ≃ { p : DyckWord // p.semilength = s.card } :=
  Equiv.ofBijective (toDyckWordSubtype s) (toDyckWordSubtype_bijective_of_injective s h_inj)

/-- Under the equivalence, peak count equals numBlocks. -/
theorem toDyckWordEquiv_apply_peakCount
    (h_inj : Function.Injective (toDyckWord : NC s → DyckWord)) (π : NC s) :
    ((toDyckWordEquiv s h_inj) π).val.peakCount = numBlocks π := by
  show (toDyckWord π).peakCount = numBlocks π
  exact toDyckWord_peakCount π

/-- **REFINED COUNT EQUALITY**: if `toDyckWord` is injective, the refined counts agree. -/
theorem numNCWithKBlocks_eq_numDyckWithKPeaks_of_injective
    (h_inj : Function.Injective (toDyckWord : NC s → DyckWord)) (k : ℕ) :
    numNCWithKBlocks s k = numDyckWithKPeaks s.card k := by
  unfold numNCWithKBlocks numDyckWithKPeaks
  -- Both are filtered cardinalities. Use the equivalence.
  apply Finset.card_bij (fun π _ => (toDyckWordEquiv s h_inj) π)
  · -- well-defined: π with numBlocks = k maps to p with peakCount = k.
    intros π hπ
    rw [Finset.mem_filter] at hπ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [toDyckWordEquiv_apply_peakCount]
    exact hπ.2
  · -- injectivity
    intros π hπ π' hπ' h_eq
    exact (toDyckWordEquiv s h_inj).injective h_eq
  · -- surjectivity
    intros p hp
    rw [Finset.mem_filter] at hp
    set π := (toDyckWordEquiv s h_inj).symm p with hπ_def
    refine ⟨π, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      -- numBlocks π = k.
      have h_apply : (toDyckWordEquiv s h_inj) π = p := by
        rw [hπ_def]; exact (toDyckWordEquiv s h_inj).apply_symm_apply p
      have h_peak := toDyckWordEquiv_apply_peakCount s h_inj π
      rw [h_apply] at h_peak
      rw [← h_peak]
      exact hp.2
    · rw [hπ_def]; exact (toDyckWordEquiv s h_inj).apply_symm_apply p

/-! ### FINAL: Narayana count formula (conditional on injectivity + cycle lemma) -/

/-- **NARAYANA AXIOM CLOSED** (conditional on the two open hypotheses):

If `toDyckWord` is injective AND the cycle lemma holds for Dyck words by peaks,
then the Narayana count formula for NCs follows:
   `s.card · numNCWithKBlocks s k = C(s.card, k) · C(s.card, k - 1)`. -/
theorem narayana_count_formula_of_injective_and_cycle
    (h_inj : Function.Injective (toDyckWord : NC s → DyckWord))
    (h_cycle : ∀ k, 1 ≤ k →
      s.card * numDyckWithKPeaks s.card k = Nat.choose s.card k * Nat.choose s.card (k - 1))
    (k : ℕ) (hk : 1 ≤ k) :
    (s.card : ℤ) * (numNCWithKBlocks s k : ℤ) =
      (s.card.choose k : ℤ) * (s.card.choose (k - 1) : ℤ) := by
  rw [numNCWithKBlocks_eq_numDyckWithKPeaks_of_injective s h_inj k]
  have h_nat := h_cycle k hk
  exact_mod_cast h_nat

end NC

end Hamilton.Infrastructure
