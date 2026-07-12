/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCTransportCross
import Mathlib.Data.Finset.Sort

/-!
# `|NC s| = |NC (Finset.univ : Finset (Fin s.card))|`

The cardinality of NC depends only on the size of the underlying
Finset.  For any `s : Finset α`, `|NC s|` equals the canonical
`|NC(Finset.univ : Finset (Fin s.card))|`.

This is the **type-erased order-invariance** result.

## Main results

* `NC.card_eq_card_univ_fin` — `|NC s| = |NC (Finset.univ : Finset
  (Fin s.card))|`.

## Tags

NC, order-invariance, Fin, Catalan
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α]

/-- The composed OrderIso between any Finset and `Finset.univ : Finset
(Fin s.card)`. -/
noncomputable def sToUnivFinOrderIso (s : Finset α) :
    (s : Type _) ≃o (Finset.univ : Finset (Fin s.card)) :=
  (Finset.orderIsoOfFin s rfl).symm.trans
    (Finset.orderIsoOfFin (Finset.univ : Finset (Fin s.card))
      (by simp [Finset.card_univ]))

/-- **Type-erased order-invariance**: `|NC s| = |NC (Finset.univ :
Finset (Fin s.card))|`. -/
theorem card_eq_card_univ_fin (s : Finset α) :
    Fintype.card (NC s) =
      Fintype.card (NC (Finset.univ : Finset (Fin s.card))) :=
  card_eq_of_orderIsoCross (sToUnivFinOrderIso s)

end NC

end Hamilton.Infrastructure
