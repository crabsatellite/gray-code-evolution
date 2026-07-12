/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.ReconstructBlockOfLast
import Hamilton.Infrastructure.GapRestriction
import Hamilton.Infrastructure.GapAdditiveBlocks
import Hamilton.Infrastructure.GapPartsDecomp



namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore mem_gapBefore gapBefore_subset_self
  gapBefore_disjoint_S gapBefore_disjoint
  sup_gapBefore_eq_sdiff gapBefore_supIndep)

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- **Reconstruction's filter at `x` = `Ps x` blocks**:
`(reconstructNC ...).val.parts.filter (· ⊆ gap x) = (Ps x).val.parts`.

For the filter:
- `S` (the inserted block) is not ⊆ gap `x` (disjoint).
- `(Ps x').val.parts` for `x' ≠ x` are ⊆ gap `x'` which is disjoint
  from gap `x`, so no part is ⊆ gap `x`.
- `(Ps x).val.parts` are all ⊆ gap `x` by definition. -/
theorem reconstructNC_filter_eq (hs : s.Nonempty) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ s) (hmax : s.max' hs ∈ S)
    (Ps : ∀ x : α, NC (gapBefore s S x))
    {x : α} (hx : x ∈ S) :
    (reconstructNC hs S hS_ne hS_sub hmax Ps).val.parts.filter
      (· ⊆ gapBefore s S x) = (Ps x).val.parts := by
  ext B
  rw [Finset.mem_filter]
  constructor
  · intro ⟨hB_mem, hB_sub⟩
    -- Classify B: either S or in (Ps x').parts for some x'.
    show B ∈ (Ps x).val.parts
    rw [show (reconstructNC hs S hS_ne hS_sub hmax Ps).val =
            Finpartition.reconstructFromGaps s S hS_ne hS_sub
              (reconstruct_hcover hs S hmax) (fun x' => (Ps x').val) from rfl] at hB_mem
    have hcl := Finpartition.reconstructFromGaps_part_classify s S hS_ne hS_sub
      (reconstruct_hcover hs S hmax) (fun x' => (Ps x').val) hB_mem
    rcases hcl with hB_eq_S | ⟨x', hx'_S, hB_in⟩
    · -- B = S: not ⊆ gap x (since S ⊆ gap x would mean x ∈ gap x ⊆ s \ S,
      -- but x ∈ S, contradiction).
      exfalso
      rw [hB_eq_S] at hB_sub
      have hx_gap : x ∈ gapBefore s S x := hB_sub hx
      have hdisj := gapBefore_disjoint_S s S x
      exact (Finset.disjoint_left.mp hdisj hx_gap) hx
    · -- B ∈ (Ps x').parts ⊆ gap x'.  If x' = x, done.  Else contradiction.
      have hB_sub_x' : B ⊆ gapBefore s S x' := (Ps x').val.le hB_in
      by_cases hx_eq : x' = x
      · subst hx_eq; exact hB_in
      · -- x' ≠ x; B ⊆ gap x' ∩ gap x.  Disjoint.
        exfalso
        have hdisj := gapBefore_disjoint s S hx'_S hx hx_eq
        have hB_ne : B.Nonempty := (Ps x').val.nonempty_of_mem_parts hB_in
        obtain ⟨y, hy⟩ := hB_ne
        exact (Finset.disjoint_left.mp hdisj (hB_sub_x' hy)) (hB_sub hy)
  · intro hB_Px
    refine ⟨?_, ?_⟩
    · -- B ∈ (Ps x).parts ⊆ reconstructNC parts (via biUnion).
      show B ∈ (Finpartition.reconstructFromGaps s S hS_ne hS_sub
                  (reconstruct_hcover hs S hmax) (fun x' => (Ps x').val)).parts
      rw [Finpartition.reconstructFromGaps_parts]
      rw [Finset.mem_insert]
      right
      rw [Finset.mem_biUnion]
      exact ⟨x, hx, hB_Px⟩
    · -- B ⊆ gap x.
      exact (Ps x).val.le hB_Px

/-- **Round-trip 1 (parts-level)**: parts of `gapRestrict
(reconstructNC ... Ps) hs _` equal parts of `Ps x` (as
`Finset (Finset α)`).

This avoids the awkward dependent type of `gapNC`, which has carrier
`gapBefore s (blockOfLast (reconstructNC ...)) x` (= `gapBefore s S x`
only propositionally). -/
theorem gapRestrict_reconstructNC_parts_eq (hs : s.Nonempty)
    (S : Finset α) (hS_ne : S.Nonempty) (hS_sub : S ⊆ s)
    (hmax : s.max' hs ∈ S)
    (Ps : ∀ x : α, NC (gapBefore s S x))
    {x : α} (hx : x ∈ S) :
    (gapRestrict (reconstructNC hs S hS_ne hS_sub hmax Ps) hs
      (reconstructNC_blockOfLast hs S hS_ne hS_sub hmax Ps ▸ hx)).parts =
      (Ps x).val.parts := by
  rw [gapRestrict_parts_eq]
  have hbol : blockOfLast (reconstructNC hs S hS_ne hS_sub hmax Ps) hs = S :=
    reconstructNC_blockOfLast hs S hS_ne hS_sub hmax Ps
  rw [hbol]
  exact reconstructNC_filter_eq hs S hS_ne hS_sub hmax Ps hx

/-- **Round-trip 2**: if `π ∈ fiberOf hs S` and `Ps x` is chosen so
that its parts match `π`'s blocks in gap `x` (for `x ∈ S`), then
`reconstructNC hs S ... Ps = π`.

This is the surjectivity side of the Kreweras-Simion bijection. -/
theorem reconstructNC_eq_of_filter_match (π : NC s) (hs : s.Nonempty)
    (S : Finset α) (hS_ne : S.Nonempty) (hS_sub : S ⊆ s)
    (hmax : s.max' hs ∈ S)
    (hπ : blockOfLast π hs = S)
    (Ps : ∀ x : α, NC (gapBefore s S x))
    (hPs : ∀ x ∈ S, (Ps x).val.parts =
      π.val.parts.filter (· ⊆ gapBefore s S x)) :
    reconstructNC hs S hS_ne hS_sub hmax Ps = π := by
  apply nc_eq_of_blockOfLast_and_gap_filters_eq _ _ hs
  · rw [reconstructNC_blockOfLast, hπ]
  · intros x hx_recon_bol
    -- hx_recon_bol : x ∈ blockOfLast (reconstructNC ...) hs = S.
    -- After rewriting blockOfLast = S, this gives x ∈ S.
    have hbol : blockOfLast (reconstructNC hs S hS_ne hS_sub hmax Ps) hs = S :=
      reconstructNC_blockOfLast hs S hS_ne hS_sub hmax Ps
    rw [hbol] at hx_recon_bol
    -- Now hx_recon_bol : x ∈ S.
    rw [hbol]
    -- Goal: filter (· ⊆ gap x) reconstruct.parts = filter (· ⊆ gap x) π.parts.
    -- After rewriting blockOfLast π = S (hπ):
    rw [hπ]
    rw [reconstructNC_filter_eq hs S hS_ne hS_sub hmax Ps hx_recon_bol]
    -- Now: (Ps x).val.parts = filter (· ⊆ gap x) π.parts.
    exact hPs x hx_recon_bol

end NC

end Hamilton.Infrastructure
