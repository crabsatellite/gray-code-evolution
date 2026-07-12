/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NoncrossingPartition

/-!
# The type of noncrossing partitions

This file introduces `NC α s` — the **subtype of `Finpartition s`
satisfying `IsNoncrossing`**, for a `LinearOrder α` carrier with
finite ground set `s : Finset α`.

## Main definitions

* `NC α s` — the subtype `{P : Finpartition s // IsNoncrossing P}`.

## Main results

* `NC.bot` — the discrete partition (all singletons) as an `NC`.

## Implementation notes

The subtype packages a `Finpartition` with its noncrossing proof.
When `α = Fin n` and `s = Finset.univ`, this is the classical
noncrossing-partition type used in the Catalan-counting literature.

For `Fintype α` and `DecidableEq α`, `NC α s` inherits `Fintype` and
`DecidableEq` via subtype lifting through the decidable
`IsNoncrossing` predicate.  For the generic `LinearOrder α` (without
`Fintype`), these instances are unavailable since the universal
quantifier in `IsNoncrossing` is not decidable.

## Tags

noncrossing partition, NC type, Finpartition subtype
-/

namespace Hamilton.Infrastructure

variable {α : Type*} [LinearOrder α] (s : Finset α)

/-- The type of **noncrossing partitions** of `s : Finset α`.

A `NC α s` is a `Finpartition` of `s` together with a proof that it
satisfies `IsNoncrossing`. -/
def NC : Type _ := {P : Finpartition s // IsNoncrossing P}

/-- `NC s` has computable decidable equality, via `Subtype.ext_iff`
and computable equality for `Finpartition s`. -/
instance : DecidableEq (NC s) :=
  fun π σ => decidable_of_iff (π.val = σ.val) Subtype.ext_iff.symm

/-- `NC s` is a computable `Fintype`: a subtype of `Finpartition s`
with the computable `Decidable IsNoncrossing` predicate from
`NoncrossingPartition.lean`. -/
instance : Fintype (NC s) := by
  unfold NC
  exact @Subtype.fintype _ _
    (fun P => decidableIsNoncrossing P) _

namespace NC

/-- Extract the underlying `Finpartition` from an `NC` element. -/
def toFinpartition {α : Type*} [LinearOrder α] {s : Finset α}
    (π : NC s) : Finpartition s := π.val

/-- The parts of an `NC` element. -/
def parts {α : Type*} [LinearOrder α] {s : Finset α}
    (π : NC s) : Finset (Finset α) := π.val.parts

/-- The number of blocks of an `NC` partition. -/
def numBlocks {α : Type*} [LinearOrder α] {s : Finset α}
    (π : NC s) : ℕ := π.val.parts.card

/-- An `NC` partition satisfies its `IsNoncrossing` proof. -/
theorem noncrossing {α : Type*} [LinearOrder α] {s : Finset α}
    (π : NC s) : IsNoncrossing π.val := π.property

/-- Coercion from `NC s` to `Finpartition s` (forgets the noncrossing
proof). -/
instance {α : Type*} [LinearOrder α] {s : Finset α} :
    CoeHead (NC s) (Finpartition s) :=
  ⟨fun π => π.val⟩

/-- The **bottom** `NC` partition: the discrete partition where each
element of `s` is its own block.  This is noncrossing by
`isNoncrossing_bot`. -/
def bot {α : Type*} [LinearOrder α] (s : Finset α) : NC s :=
  ⟨⊥, isNoncrossing_bot s⟩

end NC

end Hamilton.Infrastructure
