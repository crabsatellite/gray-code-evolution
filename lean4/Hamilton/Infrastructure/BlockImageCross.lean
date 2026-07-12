/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Order.Hom.Basic



namespace Hamilton.Infrastructure

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {s : Finset α} {t : Finset β}

/-- Cross-type block image: `Finset α → Finset β` via subtype equiv. -/
noncomputable def blockImageCross (e : (↥s : Type _) ≃ (↥t : Type _))
    (B : Finset α) : Finset β :=
  ((B.subtype (· ∈ s)).map e.toEmbedding).image Subtype.val

theorem blockImageCross_subset (e : (↥s : Type _) ≃ (↥t : Type _))
    (B : Finset α) : blockImageCross e B ⊆ t := by
  intro x hx
  unfold blockImageCross at hx
  rw [Finset.mem_image] at hx
  obtain ⟨y, hy_mem, hy_eq⟩ := hx
  rw [Finset.mem_map] at hy_mem
  obtain ⟨z, hz_mem, hz_eq⟩ := hy_mem
  rw [← hy_eq, ← hz_eq]
  exact (e z).2

theorem mem_blockImageCross (e : (↥s : Type _) ≃ (↥t : Type _))
    (B : Finset α) (y : β) :
    y ∈ blockImageCross e B ↔ ∃ x : ↥s, x.1 ∈ B ∧ (e x).1 = y := by
  unfold blockImageCross
  simp only [Finset.mem_image, Finset.mem_map, Finset.mem_subtype,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨b, ⟨a, ha_B, ha_eq⟩, hb_eq⟩
    exact ⟨a, ha_B, ha_eq ▸ hb_eq⟩
  · rintro ⟨a, ha_B, ha_eq⟩
    exact ⟨e a, ⟨a, ha_B, rfl⟩, ha_eq⟩

theorem blockImageCross_card (e : (↥s : Type _) ≃ (↥t : Type _)) {B : Finset α}
    (hB : B ⊆ s) : (blockImageCross e B).card = B.card := by
  unfold blockImageCross
  rw [Finset.card_image_of_injective _ Subtype.val_injective]
  rw [Finset.card_map]
  rw [Finset.card_subtype]
  exact congrArg Finset.card (Finset.filter_eq_self.mpr (fun x hx => hB hx))

/-- Cross-type round trip: `blockImageCross e.symm (blockImageCross e B) = B`
for `B ⊆ s`. -/
theorem blockImageCross_symm_blockImageCross
    (e : (↥s : Type _) ≃ (↥t : Type _))
    {B : Finset α} (hB : B ⊆ s) :
    blockImageCross e.symm (blockImageCross e B) = B := by
  ext a
  rw [mem_blockImageCross]
  constructor
  · rintro ⟨x, hx_blockImg, hx_eq⟩
    rw [mem_blockImageCross] at hx_blockImg
    obtain ⟨y, hy_B, hy_eq⟩ := hx_blockImg
    have hx_y : x = e y := Subtype.ext hy_eq.symm
    have : e.symm x = y := by rw [hx_y, Equiv.symm_apply_apply]
    rw [this] at hx_eq
    rw [← hx_eq]
    exact hy_B
  · intro ha_B
    have ha_s : a ∈ s := hB ha_B
    refine ⟨e ⟨a, ha_s⟩, ?_, ?_⟩
    · rw [mem_blockImageCross]
      exact ⟨⟨a, ha_s⟩, ha_B, rfl⟩
    · show (e.symm (e ⟨a, ha_s⟩)).1 = a
      rw [Equiv.symm_apply_apply]

end Hamilton.Infrastructure
