/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.GapRestriction



namespace Hamilton.Infrastructure

namespace NC

open Finset (gapBefore mem_gapBefore gapBefore_subset_self
  gapBefore_disjoint_S gapBefore_lt gapBefore_disjoint
  exists_gap_of_mem_sdiff)

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- **Block-level gap assignment**: each non-`blockOfLast` block `B`
of `π` is contained in some gap `gapBefore s (blockOfLast π hs) x`. -/
theorem nonRoot_block_subset_some_gap (π : NC s) (hs : s.Nonempty)
    {B : Finset α} (hB_mem : B ∈ π.val.parts)
    (hB_ne : B ≠ blockOfLast π hs) :
    ∃ x ∈ blockOfLast π hs,
      B ⊆ gapBefore s (blockOfLast π hs) x := by
  -- Pick any y₀ ∈ B (B is nonempty).
  have hB_ne_empty : B.Nonempty := π.val.nonempty_of_mem_parts hB_mem
  obtain ⟨y₀, hy₀⟩ := hB_ne_empty
  -- Get a gap containing y₀.
  obtain ⟨x, hx_L, hy₀_gap⟩ :=
    nonRoot_block_elem_in_some_gap π hs hB_mem hB_ne hy₀
  refine ⟨x, hx_L, ?_⟩
  -- By gap_isCompatible, B ⊆ gap or B ∩ gap = ∅.
  rcases gap_isCompatible π hs hx_L B hB_mem with hsub | hdisj
  · exact hsub
  · -- Disjoint, but y₀ ∈ B ∩ gap — contradiction.
    exfalso
    exact (Finset.disjoint_left.mp hdisj hy₀) hy₀_gap

/-- **Uniqueness of gap assignment**: a nonempty block `B` is
contained in at most one gap.

If `B ⊆ gapBefore s S x₁ ∩ gapBefore s S x₂` with `x₁, x₂ ∈ S`, then
by `gapBefore_disjoint`, either `x₁ = x₂` or both gaps are disjoint
(so the intersection is empty, forcing `B = ∅`, contradiction). -/
theorem nonRoot_block_in_unique_gap (π : NC s) (hs : s.Nonempty)
    {B : Finset α} (hB_mem : B ∈ π.val.parts)
    {x₁ x₂ : α} (hx₁ : x₁ ∈ blockOfLast π hs) (hx₂ : x₂ ∈ blockOfLast π hs)
    (hsub₁ : B ⊆ gapBefore s (blockOfLast π hs) x₁)
    (hsub₂ : B ⊆ gapBefore s (blockOfLast π hs) x₂) :
    x₁ = x₂ := by
  by_contra hne
  have hdisj := gapBefore_disjoint s (blockOfLast π hs) hx₁ hx₂ hne
  have hB_ne_empty : B.Nonempty := π.val.nonempty_of_mem_parts hB_mem
  obtain ⟨y, hy⟩ := hB_ne_empty
  exact (Finset.disjoint_left.mp hdisj (hsub₁ hy)) (hsub₂ hy)

/-- **Block-erase = filter**: the blocks of `π` not equal to
`blockOfLast` are exactly the blocks contained in some gap.

Each such block is in `π.val.parts.erase (blockOfLast π hs)`, and
also in exactly one `gapRestrict π hs hx`-parts for some
`x ∈ blockOfLast π hs`. -/
theorem nonRoot_block_iff_in_some_gap (π : NC s) (hs : s.Nonempty)
    {B : Finset α} :
    B ∈ π.val.parts.erase (blockOfLast π hs) ↔
      B ∈ π.val.parts ∧ ∃ x ∈ blockOfLast π hs,
        B ⊆ gapBefore s (blockOfLast π hs) x := by
  rw [Finset.mem_erase]
  constructor
  · intro ⟨hne, hmem⟩
    refine ⟨hmem, ?_⟩
    exact nonRoot_block_subset_some_gap π hs hmem hne
  · intro ⟨hmem, hx⟩
    refine ⟨?_, hmem⟩
    intro h_eq
    obtain ⟨x, hx_L, hsub⟩ := hx
    rw [h_eq] at hsub
    -- blockOfLast ⊆ gapBefore — but blockOfLast contains x ∈ S,
    -- and gapBefore is disjoint from S.
    have : x ∈ gapBefore s (blockOfLast π hs) x := hsub hx_L
    have hdisj := gapBefore_disjoint_S s (blockOfLast π hs) x
    exact (Finset.disjoint_left.mp hdisj this) hx_L

end NC

end Hamilton.Infrastructure
