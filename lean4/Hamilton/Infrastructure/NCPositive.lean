/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCType
import Hamilton.Infrastructure.Top
import Hamilton.Infrastructure.NoncrossingPartition

/-!
# `|NC s|` is positive

For any `s : Finset α`, `NC s` is inhabited (by `bot s`), so
`0 < Fintype.card (NC s)`.

## Main results

* `NC.zero_lt_card` — `0 < Fintype.card (NC s)`.
* `NC.card_ne_zero` — `Fintype.card (NC s) ≠ 0`.

## Tags

NC, cardinality, positive
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] (s : Finset α)

/-- `0 < |NC s|`: `NC s` is always inhabited (by `bot s`). -/
theorem zero_lt_card : 0 < Fintype.card (NC s) := by
  rw [Fintype.card_pos_iff]
  exact ⟨bot s⟩

/-- `|NC s| ≠ 0`. -/
theorem card_ne_zero : Fintype.card (NC s) ≠ 0 :=
  (zero_lt_card s).ne'

end NC

end Hamilton.Infrastructure
