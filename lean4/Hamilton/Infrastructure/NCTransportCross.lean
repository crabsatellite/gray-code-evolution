/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.FinpartitionTransportCross
import Hamilton.Infrastructure.NoncrossingPartition
import Hamilton.Infrastructure.NCType
import Hamilton.Infrastructure.GapPartsDecomp



namespace Hamilton.Infrastructure

namespace NC

open Hamilton.Infrastructure (blockImageCross mem_blockImageCross
  blockImageCross_symm_blockImageCross)

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {s : Finset α} {t : Finset β}

/-- Cross-type noncrossing preservation under OrderIso. -/
theorem transportCross_isNoncrossing (e : (↥s : Type _) ≃o (↥t : Type _))
    {P : Finpartition s} (hP : IsNoncrossing P) :
    IsNoncrossing (Finpartition.transportCross e.toEquiv P) := by
  intro B₁' hB₁' B₂' hB₂' i' j' k' l' hij hjk hkl hi hk hj hl
  show B₁' = B₂'
  have h_parts_eq : (Finpartition.transportCross e.toEquiv P).parts =
      P.parts.image (blockImageCross e.toEquiv) := rfl
  rw [h_parts_eq, Finset.mem_image] at hB₁' hB₂'
  obtain ⟨B₁, hB₁_mem, hB₁_eq⟩ := hB₁'
  obtain ⟨B₂, hB₂_mem, hB₂_eq⟩ := hB₂'
  rw [← hB₁_eq] at hi hk
  rw [← hB₂_eq] at hj hl
  rw [mem_blockImageCross] at hi hk hj hl
  obtain ⟨a_i, ha_i_B, ha_i_eq⟩ := hi
  obtain ⟨a_k, ha_k_B, ha_k_eq⟩ := hk
  obtain ⟨a_j, ha_j_B, ha_j_eq⟩ := hj
  obtain ⟨a_l, ha_l_B, ha_l_eq⟩ := hl
  have h_a_i_a_j : a_i.1 < a_j.1 := by
    have : i' < j' := hij
    rw [← ha_i_eq, ← ha_j_eq] at this
    exact e.lt_iff_lt.mp this
  have h_a_j_a_k : a_j.1 < a_k.1 := by
    have : j' < k' := hjk
    rw [← ha_j_eq, ← ha_k_eq] at this
    exact e.lt_iff_lt.mp this
  have h_a_k_a_l : a_k.1 < a_l.1 := by
    have : k' < l' := hkl
    rw [← ha_k_eq, ← ha_l_eq] at this
    exact e.lt_iff_lt.mp this
  have hB_eq : B₁ = B₂ :=
    hP hB₁_mem hB₂_mem h_a_i_a_j h_a_j_a_k h_a_k_a_l ha_i_B ha_k_B ha_j_B ha_l_B
  rw [← hB₁_eq, ← hB₂_eq, hB_eq]

/-- **Cross-type NC transport** along OrderIso `↥s ≃o ↥t`. -/
noncomputable def transportCross (e : (↥s : Type _) ≃o (↥t : Type _))
    (π : NC s) : NC t :=
  ⟨Finpartition.transportCross e.toEquiv π.val,
    transportCross_isNoncrossing e π.property⟩

@[simp]
theorem transportCross_parts (e : (↥s : Type _) ≃o (↥t : Type _))
    (π : NC s) :
    (transportCross e π).val.parts =
      π.val.parts.image (blockImageCross e.toEquiv) :=
  rfl

/-- Cross-type round trip: `transportCross e.symm (transportCross e π) = π`. -/
theorem transportCross_symm_transportCross
    (e : (↥s : Type _) ≃o (↥t : Type _)) (π : NC s) :
    transportCross e.symm (transportCross e π) = π := by
  apply Subtype.ext
  apply NC.Finpartition.eq_of_parts_eq
  rw [transportCross_parts, transportCross_parts]
  rw [Finset.image_image]
  conv_rhs => rw [show π.val.parts = π.val.parts.image id from Finset.image_id.symm]
  apply Finset.image_congr
  intro B hB_mem
  show (blockImageCross e.symm.toEquiv ∘ blockImageCross e.toEquiv) B = id B
  simp only [Function.comp_apply, id]
  have hB_sub : B ⊆ s := π.val.le hB_mem
  have h_symm : e.symm.toEquiv = e.toEquiv.symm := rfl
  rw [h_symm]
  exact blockImageCross_symm_blockImageCross e.toEquiv hB_sub

/-- **Cross-type NC equivalence**. -/
noncomputable def transportEquivCross (e : (↥s : Type _) ≃o (↥t : Type _)) :
    NC s ≃ NC t where
  toFun := transportCross e
  invFun := transportCross e.symm
  left_inv := transportCross_symm_transportCross e
  right_inv := by
    intro π'
    have h := transportCross_symm_transportCross e.symm π'
    simp only [OrderIso.symm_symm] at h
    exact h

/-- **|NC s| = |NC t|** for cross-type OrderIso of subtypes. -/
theorem card_eq_of_orderIsoCross (e : (↥s : Type _) ≃o (↥t : Type _)) :
    Fintype.card (NC s) = Fintype.card (NC t) :=
  Fintype.card_eq.mpr ⟨transportEquivCross e⟩

end NC

end Hamilton.Infrastructure
