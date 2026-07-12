/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCFinErase
import Hamilton.Infrastructure.NCBoundary
import Hamilton.Infrastructure.CardFin2Final
import Hamilton.Infrastructure.KSForFin

/-!
# Size-only NC cardinality

Define `NC.card_NC : ℕ → ℕ` as `|NC(Finset.univ : Finset (Fin n))|`,
and show `|NC s| = card_NC s.card` for any `s : Finset α`.

This is the canonical "size-only" cardinality function for NC.  The
eventual goal is `card_NC n = catalan n`.

## Main definitions

* `NC.card_NC` — the cardinality function.

## Main results

* `NC.card_NC_eq` — `|NC s| = card_NC s.card`.

## Tags

NC, size, Catalan
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α]

/-- `card_NC n` = `|NC(Finset.univ : Finset (Fin n))|` (the size-only
NC cardinality function). -/
noncomputable def card_NC (n : ℕ) : ℕ :=
  Fintype.card (NC (Finset.univ : Finset (Fin n)))

/-- `|NC s| = card_NC s.card`. -/
theorem card_NC_eq (s : Finset α) :
    Fintype.card (NC s) = card_NC s.card :=
  card_eq_card_univ_fin s

/-- Base case: `card_NC 0 = 1`. -/
@[simp]
theorem card_NC_zero : card_NC 0 = 1 := by
  show Fintype.card (NC (Finset.univ : Finset (Fin 0))) = 1
  have : (Finset.univ : Finset (Fin 0)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x _
    exact Fin.elim0 x
  rw [this]
  exact card_empty

/-- Base case: `card_NC 1 = 1`. -/
@[simp]
theorem card_NC_one : card_NC 1 = 1 := by
  show Fintype.card (NC (Finset.univ : Finset (Fin 1))) = 1
  have : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro x _
    exact Subsingleton.elim x 0
  rw [this]
  exact card_singleton _


@[simp]
theorem card_NC_two : card_NC 2 = 2 :=
  card_NC_univ_fin_two

/-- **K-S recursion in size-only form**: for Fin (n+1), the K-S sum
becomes a sum of card_NC values indexed by gap sizes. -/
theorem KS_recursion_card_NC (n : ℕ) :
    card_NC (n+1) =
      ∑ S ∈ (Finset.univ : Finset (Fin (n+1))).powerset.filter
        (fun S => S.Nonempty ∧ Fin.last n ∈ S),
        ∏ x ∈ S.attach, card_NC
          (Finset.gapBefore (Finset.univ : Finset (Fin (n+1))) S x.1).card := by
  show Fintype.card (NC (Finset.univ : Finset (Fin (n+1)))) = _
  rw [KS_recursion_fin]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.prod_congr rfl
  intro x _
  exact card_NC_eq _

end NC

end Hamilton.Infrastructure
