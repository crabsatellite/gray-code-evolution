/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.BlockImageCross
import Mathlib.Order.Partition.Finpartition



namespace Hamilton.Infrastructure

namespace Finpartition

open Hamilton.Infrastructure (blockImageCross blockImageCross_subset
  blockImageCross_card mem_blockImageCross)

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
  {s : Finset α} {t : Finset β}

/-- **Cross-type Finpartition transport** via `e : ↥s ≃ ↥t`. -/
noncomputable def transportCross (e : (↥s : Type _) ≃ (↥t : Type _))
    (P : _root_.Finpartition s) : _root_.Finpartition t where
  parts := P.parts.image (blockImageCross e)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro X hX Y hY hXY
    rw [Finset.coe_image] at hX hY
    obtain ⟨B₁, hB₁_mem, hB₁_eq⟩ := hX
    obtain ⟨B₂, hB₂_mem, hB₂_eq⟩ := hY
    have hne : B₁ ≠ B₂ := fun h_eq => hXY (hB₁_eq.symm.trans (h_eq ▸ hB₂_eq))
    have hdisj := P.disjoint hB₁_mem hB₂_mem hne
    show Disjoint X Y
    rw [← hB₁_eq, ← hB₂_eq]
    rw [Finset.disjoint_left]
    intro y hy₁ hy₂
    rw [mem_blockImageCross] at hy₁ hy₂
    obtain ⟨x₁, hx₁_B, hx₁_eq⟩ := hy₁
    obtain ⟨x₂, hx₂_B, hx₂_eq⟩ := hy₂
    have h_e_eq : e x₁ = e x₂ := Subtype.ext (hx₁_eq.trans hx₂_eq.symm)
    have h_x_eq : x₁ = x₂ := e.injective h_e_eq
    subst h_x_eq
    exact (Finset.disjoint_left.mp hdisj) hx₁_B hx₂_B
  sup_parts := by
    ext y
    constructor
    · intro hy_sup
      rw [Finset.mem_sup] at hy_sup
      obtain ⟨B', hB'_mem, hy_B'⟩ := hy_sup
      rw [Finset.mem_image] at hB'_mem
      obtain ⟨B, _, hB_eq⟩ := hB'_mem
      have : y ∈ blockImageCross e B := hB_eq ▸ hy_B'
      exact blockImageCross_subset e B this
    · intro hy_t
      rw [Finset.mem_sup]
      let x : ↥t := ⟨y, hy_t⟩
      let a : ↥s := e.symm x
      have ha_s : a.1 ∈ s := a.2
      obtain ⟨B, hB_mem, ha_B⟩ := P.exists_mem ha_s
      refine ⟨blockImageCross e B, ?_, ?_⟩
      · rw [Finset.mem_image]; exact ⟨B, hB_mem, rfl⟩
      · show y ∈ blockImageCross e B
        rw [mem_blockImageCross]
        refine ⟨a, ha_B, ?_⟩
        show (e (e.symm x)).1 = y
        rw [Equiv.apply_symm_apply]
  bot_notMem := by
    intro hbot
    rw [Finset.mem_image] at hbot
    obtain ⟨B, hB_mem, hB_eq⟩ := hbot
    have hB_card : (blockImageCross e B).card = B.card :=
      blockImageCross_card e (P.le hB_mem)
    rw [hB_eq] at hB_card
    have hbot_card : (⊥ : Finset β).card = 0 := rfl
    rw [hbot_card] at hB_card
    have hB_ne : 0 < B.card :=
      Finset.card_pos.mpr (P.nonempty_of_mem_parts hB_mem)
    omega

end Finpartition

end Hamilton.Infrastructure
