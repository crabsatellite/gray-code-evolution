/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.CardNCSize
import Hamilton.Infrastructure.CatalanBase
import Hamilton.Infrastructure.NCPositive

/-!
# `card_NC n = catalan n` (partial: n ≤ 2)

For n ≤ 2, we have `card_NC n = catalan n`.

This establishes the start of the eventual `card_NC = catalan`
identity.  The full inductive step requires the K-S sum to pair-Catalan
sum re-indexing (parameterizing by min of S).

## Main results

* `NC.card_NC_eq_catalan_le_two` — `card_NC n = catalan n` for n ≤ 2.

## Tags

NC, Catalan, card_NC, base case
-/

namespace Hamilton.Infrastructure

namespace NC

/-- `card_NC n = catalan n` for n ≤ 2.

This is a partial result; the full `card_NC n = catalan n` for all
n requires the K-S sum to pair-Catalan re-indexing. -/
theorem card_NC_eq_catalan_le_two : ∀ n ≤ 2, card_NC n = catalan n
  | 0, _ => by rw [card_NC_zero, catalan_zero]
  | 1, _ => by rw [card_NC_one, catalan_one]
  | 2, _ => by rw [card_NC_two, catalan_two]
  | n + 3, h => by omega

/-- **n = 3 case**: `card_NC 3 ≥ 1` via existence of `bot _`. -/
theorem card_NC_three_pos : 1 ≤ card_NC 3 := by
  show 1 ≤ Fintype.card (NC (Finset.univ : Finset (Fin 3)))
  exact zero_lt_card _

end NC

end Hamilton.Infrastructure
