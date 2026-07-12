/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.DyckPeaks
import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Count of Dyck words by peak count: the Narayana refinement

For `n, k : ℕ`, the count of Dyck words of semilength `n` with exactly `k` peaks.

This is the **Dyck-side companion** to `numNCWithKBlocks`.  Via the
peak-preserving bijection `toDyckWord` (`NCToDyckWord.lean`), these
two counts coincide — closing one closes the other.

## Main definitions

* `numDyckWithKPeaks n k` — `|{p : DyckWord // p.semilength = n ∧ p.peakCount = k}|`.

## Target theorem (multi-round future work)

* Cycle lemma / Narayana count: `n · numDyckWithKPeaks n k = C(n, k) · C(n, k-1)` for `k ≥ 1`.

  Standard proofs: cycle lemma (Dvoretzky-Motzkin 1947), Lindström-Gessel-Viennot,
  or direct bijection with two-rowed standard Young tableaux.

## Tags

DyckWord, peak count, Narayana, Catalan refinement
-/

namespace Hamilton.Infrastructure

open DyckWord

/-- The count of Dyck words of semilength `n` with exactly `k` peaks. -/
noncomputable def numDyckWithKPeaks (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset { p : DyckWord // p.semilength = n }).filter
    (fun p => p.val.peakCount = k)).card

/-- `numDyckWithKPeaks n k = 0` for `k > n` (no Dyck word has more than
semilength peaks). -/
theorem numDyckWithKPeaks_eq_zero_of_gt (n k : ℕ) (hk : n < k) :
    numDyckWithKPeaks n k = 0 := by
  unfold numDyckWithKPeaks
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intros p _ h_eq
  have h_le := peakCount_le_semilength p.val
  rw [p.property, h_eq] at h_le
  omega

end Hamilton.Infrastructure
