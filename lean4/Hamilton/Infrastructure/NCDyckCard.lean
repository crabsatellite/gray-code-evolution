/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.CardNCInduction
import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Cardinality bijection NC ↔ DyckWord

For any `s : Finset α` with `α : LinearOrder`:
`|NC s| = catalan s.card = |{p : DyckWord // p.semilength = s.card}|`.

By `Fintype.equivOfCardEq`, there exists a (non-canonical) bijection.

This file provides the abstract bijection as a scaffold.  The
**structured** bijection (preserving block-count ↔ peak-count) requires
the recursive `NC.toDyckWord` construction (multi-session future work).

## Main results

* `NC.card_eq_card_dyckWord` — the cardinality equality.
* `NC.equivDyckWord` — abstract bijection via `Fintype.equivOfCardEq`.

## Tags

NC, DyckWord, Catalan, bijection, cardinality
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] (s : Finset α)

/-- The cardinality of `NC s` equals the cardinality of Dyck words of
semilength `s.card`, both being `catalan s.card`. -/
theorem card_eq_card_dyckWord :
    Fintype.card (NC s) =
      Fintype.card { p : DyckWord // p.semilength = s.card } := by
  rw [card_NC_eq_catalan_card, DyckWord.card_dyckWord_semilength_eq_catalan]

/-- An abstract (non-canonical) bijection `NC s ≃ {p : DyckWord // p.semilength = s.card}`.

This bijection comes from `Fintype.equivOfCardEq` applied to
`card_eq_card_dyckWord`.  It does NOT preserve any structure
(block count ↔ peak count, etc.).

For the structured bijection needed to prove the Narayana count formula,
see the future `NC.toDyckWord` constructive definition.  -/
noncomputable def equivDyckWord :
    NC s ≃ { p : DyckWord // p.semilength = s.card } :=
  Fintype.equivOfCardEq (card_eq_card_dyckWord s)

end NC

end Hamilton.Infrastructure
