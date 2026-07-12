/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCOperations

/-!
# Lightweight parity color for noncrossing partitions

This file contains only the parity color derived from the number of
blocks of an `NC s`.  Keep this layer below graph adjacency and
bipartiteness proofs so route audits can mention `numBlocksParity`
without importing the whole refinement graph infrastructure.

## Main definitions

* `NC.numBlocksParity` - `numBlocks π mod 2` as a `Fin 2`.
* `NC.numBlocksParityBool` - the same color as a `Bool`.

## Tags

noncrossing partition, parity, numBlocks
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The 2-coloring of `NC s` via `numBlocks` parity. -/
def numBlocksParity (π : NC s) : Fin 2 :=
  ⟨numBlocks π % 2, Nat.mod_lt _ (by decide)⟩

/-- `Bool`-valued parity color, true exactly on even `numBlocks`. -/
def numBlocksParityBool (π : NC s) : Bool :=
  numBlocks π % 2 = 0

end NC

end Hamilton.Infrastructure
