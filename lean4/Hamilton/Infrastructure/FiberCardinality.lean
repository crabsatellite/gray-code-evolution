/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.FiberEquiv
import Mathlib.Data.Fintype.BigOperators



namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore)

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- **K-S multiplicative cardinality identity**.

`|fiberOf hs S| = ∏_{x ∈ S} |NC (gapBefore s S x)|`. -/
theorem fiberOf_card_eq_prod (hs : s.Nonempty) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s) (hmax : s.max' hs ∈ S) :
    (fiberOf hs S).card =
      ∏ x ∈ (S : Finset α).attach, Fintype.card (NC (gapBefore s S x.1)) := by
  -- (fiberOf hs S).card = Fintype.card {π : NC s // π ∈ fiberOf hs S}.
  rw [← Fintype.card_coe (fiberOf hs S)]
  
  rw [Fintype.card_congr (fiberEquiv hs S hS_ne hS_sub hmax)]
  -- Fintype.card_pi: card (∀ x, f x) = ∏ card (f x).
  rw [Fintype.card_pi]
  -- Product over {y // y ∈ S} = product over S.attach (via Finset.prod_attach).
  rw [Finset.univ_eq_attach]

end NC

end Hamilton.Infrastructure
