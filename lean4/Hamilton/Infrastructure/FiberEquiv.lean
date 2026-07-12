/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.ReconstructRoundTrip
import Hamilton.Infrastructure.FiberPartitionIdentity



namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore mem_gapBefore gapBefore_subset_self
  gapBefore_disjoint_S gapBefore_disjoint
  sup_gapBefore_eq_sdiff gapBefore_supIndep)

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- **Total extension** of a partial gap-NC family.

Given `f : ∀ x : { y : α // y ∈ S }, NC (gapBefore s S x.1)`,
extend to `∀ x : α, NC (gapBefore s S x)` by using `NC.bot` for
`x ∉ S`. -/
noncomputable def extendFamily (S : Finset α)
    (f : ∀ x : { y : α // y ∈ S }, NC (gapBefore s S x.1)) :
    ∀ x : α, NC (gapBefore s S x) :=
  fun x => if hx : x ∈ S then f ⟨x, hx⟩ else NC.bot _

/-- For `x ∈ S`, `extendFamily f x = f ⟨x, hx⟩`. -/
theorem extendFamily_apply_mem (S : Finset α)
    (f : ∀ x : { y : α // y ∈ S }, NC (gapBefore s S x.1))
    {x : α} (hx : x ∈ S) :
    extendFamily S f x = f ⟨x, hx⟩ := by
  unfold extendFamily
  simp [hx]

/-! ### Forward map: fiber element → gap-NC family -/

/-- Given `π : NC s` with `blockOfLast π hs = S`, and `x ∈ S`, produce
an `NC (gapBefore s S x)`.  This is `gapNC π hs` with the carrier
type fixed via the propositional equality. -/
noncomputable def fiberFromNC (hs : s.Nonempty) (S : Finset α)
    (π : NC s) (hπ : blockOfLast π hs = S)
    (x : { y : α // y ∈ S }) :
    NC (gapBefore s S x.1) := by
  have hx_bol : x.1 ∈ blockOfLast π hs := hπ.symm ▸ x.2
  have hgap_eq : gapBefore s (blockOfLast π hs) x.1 = gapBefore s S x.1 := by
    rw [hπ]
  exact hgap_eq ▸ gapNC π hs hx_bol

/-! ### Inverse map: gap-NC family → fiber element -/

/-- Given a gap-NC family, the reconstructed `NC s` lies in `fiberOf hs S`. -/
theorem reconstructNC_mem_fiberOf (hs : s.Nonempty) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s) (hmax : s.max' hs ∈ S)
    (Ps : ∀ x : α, NC (gapBefore s S x)) :
    reconstructNC hs S hS_ne hS_sub hmax Ps ∈ fiberOf hs S := by
  rw [mem_fiberOf]
  exact reconstructNC_blockOfLast hs S hS_ne hS_sub hmax Ps

/-- **Parts of `fiberFromNC`**: equal to `π.val.parts.filter (· ⊆
gap)`.

The `▸` cast in `fiberFromNC` only transports the carrier type; it
does not change the underlying `Finset (Finset α)` of parts. -/
theorem fiberFromNC_val_parts (hs : s.Nonempty) (S : Finset α)
    (π : NC s) (hπ : blockOfLast π hs = S)
    (x : { y : α // y ∈ S }) :
    (fiberFromNC hs S π hπ x).val.parts =
      π.val.parts.filter (· ⊆ gapBefore s S x.1) := by
  subst hπ
  unfold fiberFromNC
  show (gapRestrict π hs x.2).parts =
       π.val.parts.filter (· ⊆ gapBefore s _ x.1)
  rw [gapRestrict_parts_eq]

/-! ### The Equiv -/

/-- **Forward map**: from fiber elements to gap-NC families. -/
noncomputable def fiberSubtypeToProd (hs : s.Nonempty) (S : Finset α) :
    {π : NC s // π ∈ fiberOf hs S} →
      ∀ x : { y : α // y ∈ S }, NC (gapBefore s S x.1) :=
  fun π x => fiberFromNC hs S π.val ((mem_fiberOf hs S π.val).mp π.property) x

/-- **Inverse map**: from gap-NC families to fiber elements. -/
noncomputable def prodToFiberSubtype (hs : s.Nonempty) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s) (hmax : s.max' hs ∈ S) :
    (∀ x : { y : α // y ∈ S }, NC (gapBefore s S x.1)) →
      {π : NC s // π ∈ fiberOf hs S} :=
  fun f => ⟨reconstructNC hs S hS_ne hS_sub hmax (extendFamily S f),
    reconstructNC_mem_fiberOf hs S hS_ne hS_sub hmax (extendFamily S f)⟩

/-- **Round-trip 1**: `fiberSubtypeToProd (prodToFiberSubtype f) = f`. -/
theorem fiberSubtypeToProd_prodToFiberSubtype (hs : s.Nonempty) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s) (hmax : s.max' hs ∈ S)
    (f : ∀ x : { y : α // y ∈ S }, NC (gapBefore s S x.1)) :
    fiberSubtypeToProd hs S
      (prodToFiberSubtype hs S hS_ne hS_sub hmax f) = f := by
  funext x
  -- Both NC (gapBefore s S x.1).  Show parts equal.
  apply Subtype.ext
  apply Finpartition.eq_of_parts_eq
  unfold fiberSubtypeToProd prodToFiberSubtype
  rw [fiberFromNC_val_parts]
  rw [show (reconstructNC hs S hS_ne hS_sub hmax (extendFamily S f)).val.parts.filter
        (· ⊆ gapBefore s S x.1) = (extendFamily S f x.1).val.parts from
        reconstructNC_filter_eq hs S hS_ne hS_sub hmax (extendFamily S f) x.2]
  rw [extendFamily_apply_mem S f x.2]

/-- **Round-trip 2**: `prodToFiberSubtype (fiberSubtypeToProd π) = π`. -/
theorem prodToFiberSubtype_fiberSubtypeToProd (hs : s.Nonempty) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s) (hmax : s.max' hs ∈ S)
    (π : {π : NC s // π ∈ fiberOf hs S}) :
    prodToFiberSubtype hs S hS_ne hS_sub hmax
      (fiberSubtypeToProd hs S π) = π := by
  apply Subtype.ext
  unfold prodToFiberSubtype fiberSubtypeToProd
  have hπ : blockOfLast π.val hs = S := (mem_fiberOf hs S π.val).mp π.property
  apply reconstructNC_eq_of_filter_match π.val hs S hS_ne hS_sub hmax hπ
  intros x hx_S
  rw [extendFamily_apply_mem S _ hx_S]
  exact fiberFromNC_val_parts hs S π.val hπ ⟨x, hx_S⟩


noncomputable def fiberEquiv (hs : s.Nonempty) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s) (hmax : s.max' hs ∈ S) :
    {π : NC s // π ∈ fiberOf hs S} ≃
      ∀ x : { y : α // y ∈ S }, NC (gapBefore s S x.1) where
  toFun := fiberSubtypeToProd hs S
  invFun := prodToFiberSubtype hs S hS_ne hS_sub hmax
  left_inv := prodToFiberSubtype_fiberSubtypeToProd hs S hS_ne hS_sub hmax
  right_inv := fiberSubtypeToProd_prodToFiberSubtype hs S hS_ne hS_sub hmax

end NC

end Hamilton.Infrastructure
