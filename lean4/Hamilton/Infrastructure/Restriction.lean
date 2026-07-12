/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NoncrossingPartition
import Mathlib.Order.Partition.Finpartition



namespace Hamilton.Infrastructure

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- A Finpartition `P` is **compatible** with a subset `I` if every
block is either contained in `I` or disjoint from `I`. -/
def IsCompatible (P : Finpartition s) (I : Finset α) : Prop :=
  ∀ B ∈ P.parts, B ⊆ I ∨ Disjoint B I

/-- The **restriction** of `P` to a compatible subset `I ⊆ s`: the
Finpartition of `I` consisting of `P`-blocks contained in `I`. -/
def restrictCompat (P : Finpartition s) (I : Finset α)
    (hcomp : IsCompatible P I) (hsub : I ⊆ s) : Finpartition I where
  parts := P.parts.filter (· ⊆ I)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro X hX Y hY hXY
    rw [Finset.coe_filter] at hX hY
    have hX_p : X ∈ P.parts := hX.1
    have hY_p : Y ∈ P.parts := hY.1
    exact P.disjoint hX_p hY_p hXY
  sup_parts := by
    apply Finset.ext
    intro x
    rw [Finset.mem_sup]
    constructor
    · intro hx
      obtain ⟨B, hB_filter, hx_in_B⟩ := hx
      rw [Finset.mem_filter] at hB_filter
      exact hB_filter.2 hx_in_B
    · intro hx_in_I
      have hx_in_s : x ∈ s := hsub hx_in_I
      obtain ⟨B, hB_p, hx_B⟩ := P.exists_mem hx_in_s
      refine ⟨B, ?_, hx_B⟩
      rw [Finset.mem_filter]
      refine ⟨hB_p, ?_⟩
      rcases hcomp B hB_p with hsub_I | hdisj
      · exact hsub_I
      · exact absurd hx_in_I ((Finset.disjoint_left.mp hdisj) hx_B)
  bot_notMem := by
    intro hmem
    rw [Finset.mem_filter] at hmem
    exact P.bot_notMem hmem.1

@[simp]
theorem restrictCompat_parts (P : Finpartition s) (I : Finset α)
    (hcomp : IsCompatible P I) (hsub : I ⊆ s) :
    (restrictCompat P I hcomp hsub).parts =
      P.parts.filter (· ⊆ I) := rfl

end Finpartition

/-! ### Restriction preserves noncrossing -/

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- If `P : Finpartition s` is noncrossing and `I ⊆ s` is compatible
with `P`, then `Finpartition.restrictCompat P I hcomp hsub` is also
noncrossing. -/
theorem IsNoncrossing.restrictCompat {P : Finpartition s}
    (hP : IsNoncrossing P) {I : Finset α}
    (hcomp : Finpartition.IsCompatible P I) (hsub : I ⊆ s) :
    IsNoncrossing (Finpartition.restrictCompat P I hcomp hsub) := by
  intro B₁ h₁ B₂ h₂ i j k l hij hjk hkl hi hk hj hl
  rw [Finpartition.restrictCompat_parts, Finset.mem_filter] at h₁ h₂
  exact hP h₁.1 h₂.1 hij hjk hkl hi hk hj hl

end NC

end Hamilton.Infrastructure
