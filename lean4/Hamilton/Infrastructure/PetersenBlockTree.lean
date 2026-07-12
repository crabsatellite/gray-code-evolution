/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.PetersenGrayCycle

/-!
# Canonical matching deletion and the local Petersen diamond
-/

namespace Hamilton.Infrastructure
namespace Petersen
namespace Tree

open Finset

variable {n : Nat} [NeZero n]

section Relabel

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def keyPartition (f : α → α) :
    Finpartition (Finset.univ : Finset α) :=
  Finpartition.ofSetoid (Setoid.ker f)

noncomputable def relabelKey (f : α → α) (a b x : α) : α :=
  if f x = a then b else f x

theorem mem_part_keyPartition_iff (f : α → α) (x y : α) :
    y ∈ (keyPartition f).part x ↔ f x = f y := by
  exact Finpartition.mem_part_ofSetoid_iff_rel

theorem keyPartition_relabel_eq_mergeBlocks (f : α → α) (a b : α)
    (ha : f a = a) (hb : f b = b) (hab : a ≠ b) :
    let P := keyPartition f
    keyPartition (relabelKey f a b) =
      P.mergeBlocks (P.part_mem.mpr (Finset.mem_univ a))
        (P.part_mem.mpr (Finset.mem_univ b))
        (by
          intro h
          have habmem : b ∈ P.part a := by
            rw [h]
            exact P.mem_part (Finset.mem_univ b)
          have hkeys := (mem_part_keyPartition_iff f a b).1 habmem
          exact hab (ha.symm.trans (hkeys.trans hb))) := by
  let P := keyPartition f
  let B₁ := P.part a
  let B₂ := P.part b
  have hB₁ : B₁ ∈ P.parts := P.part_mem.mpr (Finset.mem_univ a)
  have hB₂ : B₂ ∈ P.parts := P.part_mem.mpr (Finset.mem_univ b)
  have hne : B₁ ≠ B₂ := by
    intro h
    have habmem : b ∈ P.part a := by
      change b ∈ B₁
      rw [h]
      exact P.mem_part (Finset.mem_univ b)
    have hkeys := (mem_part_keyPartition_iff f a b).1 habmem
    exact hab (ha.symm.trans (hkeys.trans hb))
  apply Encoding.finpartition_eq_of_part_eq
  intro x _hx
  rw [Encoding.mergeBlocks_part_eq P hB₁ hB₂ hne (Finset.mem_univ x)]
  by_cases hxunion : x ∈ B₁ ∪ B₂
  · rw [if_pos hxunion]
    have hxClass : f x = a ∨ f x = b := by
      rcases Finset.mem_union.mp hxunion with hx1 | hx2
      · left
        have h := (mem_part_keyPartition_iff f a x).1 (by
          change x ∈ P.part a
          exact hx1)
        exact h.symm.trans ha
      · right
        have h := (mem_part_keyPartition_iff f b x).1 (by
          change x ∈ P.part b
          exact hx2)
        exact h.symm.trans hb
    have hnew : relabelKey f a b x = b := by
      rcases hxClass with h | h
      · simp [relabelKey, h]
      · simp [relabelKey, h, hab]
    have hxmem : x ∈ (keyPartition (relabelKey f a b)).part a := by
      rw [mem_part_keyPartition_iff, relabelKey, ha, if_pos rfl, hnew]
    have hpart := (keyPartition (relabelKey f a b)).part_eq_of_mem
      ((keyPartition (relabelKey f a b)).part_mem.mpr (Finset.mem_univ a)) hxmem
    rw [hpart]
    ext y
    rw [mem_part_keyPartition_iff]
    rw [relabelKey, ha, if_pos rfl]
    constructor
    · intro hy
      by_cases hya : f y = a
      · exact Finset.mem_union_left _
          ((mem_part_keyPartition_iff f a y).2 (ha.trans hya.symm))
      · have hyb : f y = b := by simpa [relabelKey, hya] using hy.symm
        exact Finset.mem_union_right _
          ((mem_part_keyPartition_iff f b y).2 (hb.trans hyb.symm))
    · intro hy
      rcases Finset.mem_union.mp hy with hy1 | hy2
      · have hfy := (mem_part_keyPartition_iff f a y).1 hy1
        have hya : f y = a := hfy.symm.trans ha
        rw [relabelKey, if_pos hya]
      · have hfy := (mem_part_keyPartition_iff f b y).1 hy2
        have hfyb : f y = b := hfy.symm.trans hb
        have hfyna : f y ≠ a := by
          rw [hfyb]
          exact Ne.symm hab
        rw [relabelKey, if_neg hfyna, hfyb]
  · rw [if_neg hxunion]
    have hxa : f x ≠ a := by
      intro h
      apply hxunion
      apply Finset.mem_union_left
      exact (mem_part_keyPartition_iff f a x).2 (ha.trans h.symm)
    have hxb : f x ≠ b := by
      intro h
      apply hxunion
      apply Finset.mem_union_right
      exact (mem_part_keyPartition_iff f b x).2 (hb.trans h.symm)
    ext y
    rw [mem_part_keyPartition_iff, P.mem_part_iff_part_eq_part
      (Finset.mem_univ y) (Finset.mem_univ x)]
    rw [relabelKey, if_neg hxa]
    constructor
    · intro hnew
      by_cases hya : f y = a
      · rw [relabelKey, if_pos hya] at hnew
        exact (hxb hnew).elim
      · rw [relabelKey, if_neg hya] at hnew
        exact (P.mem_part_iff_part_eq_part (Finset.mem_univ y)
          (Finset.mem_univ x)).1 ((mem_part_keyPartition_iff f x y).2 hnew)
    · intro hparts
      have hold := (mem_part_keyPartition_iff f x y).1
        ((P.mem_part_iff_part_eq_part (Finset.mem_univ y)
          (Finset.mem_univ x)).2 hparts)
      have hya : f y ≠ a := fun h => hxa (hold.trans h)
      rw [relabelKey, if_neg hya]
      exact hold

theorem decodedFinpartition_eq_keyPartition (C : CanonicalMatching n)
    (A : Finset C.free) :
    C.decodedFinpartition A = keyPartition (C.decodeKey A) := by
  apply Encoding.finpartition_eq_of_part_eq
  intro x _hx
  ext y
  rw [C.mem_part_decodedFinpartition_iff, mem_part_keyPartition_iff]

end Relabel

theorem isCanonicalMatching_mono {Q R : Finset (Fin n × Fin n)}
    (hR : IsCanonicalMatching R) (hQR : Q ⊆ R) : IsCanonicalMatching Q := by
  constructor
  · intro e he
    exact hR.1 e (hQR he)
  · constructor
    · intro e he f hf hef
      exact hR.2.1 e (hQR he) f (hQR hf) hef
    · intro e he f hf hefl
      exact hR.2.2 e (hQR he) f (hQR hf) hefl

/-- Delete one chord from a canonical matching. -/
noncomputable def eraseChord (C : CanonicalMatching n)
    (e : Fin n × Fin n) : CanonicalMatching n :=
  ⟨C.1.erase e, isCanonicalMatching_mono C.2 (Finset.erase_subset e C.1)⟩

@[simp]
theorem eraseChord_val (C : CanonicalMatching n) (e : Fin n × Fin n) :
    (eraseChord C e).1 = C.1.erase e := rfl

theorem mem_eraseChord_iff (C : CanonicalMatching n) (e f : Fin n × Fin n) :
    f ∈ (eraseChord C e).1 ↔ f ≠ e ∧ f ∈ C.1 := by
  simp [eraseChord]

theorem erased_left_free (C : CanonicalMatching n) {e : Fin n × Fin n}
    (he : e ∈ C.1) : e.1 ∈ (eraseChord C e).free := by
  rw [(eraseChord C e).mem_free_iff]
  constructor
  · exact (C.2.1 e he).1.ne'
  · rw [(eraseChord C e).mem_endpoints_iff]
    rintro ⟨f, hf, hshare⟩
    have hf' := (mem_eraseChord_iff C e f).1 hf
    have hcommon : e.1 ∈ chordEnds e ∧ e.1 ∈ chordEnds f := by
      constructor
      · simp [chordEnds]
      · simpa [chordEnds] using hshare
    exact hf'.1 (C.chord_eq_of_common_endpoint he hf'.2 hcommon.1 hcommon.2).symm

theorem erased_right_free (C : CanonicalMatching n) {e : Fin n × Fin n}
    (he : e ∈ C.1) : e.2 ∈ (eraseChord C e).free := by
  rw [(eraseChord C e).mem_free_iff]
  constructor
  · exact ((C.2.1 e he).1.trans (C.2.1 e he).2).ne'
  · rw [(eraseChord C e).mem_endpoints_iff]
    rintro ⟨f, hf, hshare⟩
    have hf' := (mem_eraseChord_iff C e f).1 hf
    have hcommon : e.2 ∈ chordEnds e ∧ e.2 ∈ chordEnds f := by
      constructor
      · simp [chordEnds]
      · simpa [chordEnds] using hshare
    exact hf'.1 (C.chord_eq_of_common_endpoint he hf'.2 hcommon.1 hcommon.2).symm

@[simp]
theorem decodeKey_empty (C : CanonicalMatching n) (x : Fin n) :
    C.decodeKey (∅ : Finset C.free) x =
      if x ∈ C.endpoints then C.endpointKey x else x := by
  rw [CanonicalMatching.decodeKey]
  by_cases hx : x ∈ C.endpoints
  · simp [hx]
  · simp [hx, CanonicalMatching.maskPoints]

theorem endpoint_mem_of_eraseChord (C : CanonicalMatching n)
    {e : Fin n × Fin n} {x : Fin n}
    (hx : x ∈ (eraseChord C e).endpoints) : x ∈ C.endpoints := by
  obtain ⟨f, hf, hxf⟩ := ((eraseChord C e).mem_endpoints_iff x).1 hx
  exact (C.mem_endpoints_iff x).2
    ⟨f, (mem_eraseChord_iff C e f).1 hf |>.2, hxf⟩

theorem eraseChord_endpointKey_eq (C : CanonicalMatching n)
    {e : Fin n × Fin n} {x : Fin n}
    (hx : x ∈ (eraseChord C e).endpoints) :
    (eraseChord C e).endpointKey x = C.endpointKey x := by
  obtain ⟨f, hf, hxf⟩ := ((eraseChord C e).mem_endpoints_iff x).1 hx
  have hfC : f ∈ C.1 := (mem_eraseChord_iff C e f).1 hf |>.2
  rw [(eraseChord C e).endpointKey_eq_left_of_mem hf hxf,
    C.endpointKey_eq_left_of_mem hfC hxf]

theorem erased_endpoint_iff (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (x : Fin n) :
    x ∈ (eraseChord C e).endpoints ↔
      x ∈ C.endpoints ∧ x ≠ e.1 ∧ x ≠ e.2 := by
  constructor
  · intro hx
    refine ⟨endpoint_mem_of_eraseChord C hx, ?_, ?_⟩
    · intro hxe
      obtain ⟨f, hf, hxf⟩ := ((eraseChord C e).mem_endpoints_iff x).1 hx
      have hf' := (mem_eraseChord_iff C e f).1 hf
      have hcommon : e.1 ∈ chordEnds e ∧ e.1 ∈ chordEnds f := by
        constructor
        · simp [chordEnds]
        · simpa [chordEnds, hxe] using hxf
      exact hf'.1 (C.chord_eq_of_common_endpoint he hf'.2 hcommon.1 hcommon.2).symm
    · intro hxe
      obtain ⟨f, hf, hxf⟩ := ((eraseChord C e).mem_endpoints_iff x).1 hx
      have hf' := (mem_eraseChord_iff C e f).1 hf
      have hcommon : e.2 ∈ chordEnds e ∧ e.2 ∈ chordEnds f := by
        constructor
        · simp [chordEnds]
        · simpa [chordEnds, hxe] using hxf
      exact hf'.1 (C.chord_eq_of_common_endpoint he hf'.2 hcommon.1 hcommon.2).symm
  · rintro ⟨hxC, hxl, hxr⟩
    obtain ⟨f, hf, hxf⟩ := (C.mem_endpoints_iff x).1 hxC
    have hfe : f ≠ e := by
      intro h
      subst f
      exact hxf.elim hxl hxr
    exact ((eraseChord C e).mem_endpoints_iff x).2
      ⟨f, (mem_eraseChord_iff C e f).2 ⟨hfe, hf⟩, hxf⟩

theorem containing_left_implies_containing_right
    (C : CanonicalMatching n) {e f : Fin n × Fin n}
    (he : e ∈ C.1) (hf : f ∈ (eraseChord C e).1)
    (hcontains : f.1 < e.1 ∧ e.1 < f.2) :
    f.1 < e.2 ∧ e.2 < f.2 := by
  have hf' := (mem_eraseChord_iff C e f).1 hf
  have hef : e ≠ f := hf'.1.symm
  have hd := C.2.2.1 e he f hf'.2 hef
  refine ⟨hcontains.1.trans (C.2.1 e he).2, ?_⟩
  by_contra hnot
  have hle : f.2 ≤ e.2 := le_of_not_gt hnot
  have hne : f.2 ≠ e.2 := by
    intro hEq
    have hnotmem := Finset.disjoint_left.mp hd
      (show e.2 ∈ chordEnds e by simp [chordEnds])
    exact hnotmem (show e.2 ∈ chordEnds f by simp [chordEnds, ← hEq])
  have hlt : f.2 < e.2 := lt_of_le_of_ne hle hne
  have hcross := C.2.2.2 f hf'.2 e he hcontains.1
  exact hcross ⟨hcontains.1, hcontains.2, hlt⟩

theorem erased_precedingLefts_eq_erase (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (x : Fin n) :
    (eraseChord C e).precedingLefts x = (C.precedingLefts x).erase e.1 := by
  ext a
  rw [(eraseChord C e).mem_precedingLefts_iff,
    Finset.mem_erase, C.mem_precedingLefts_iff]
  constructor
  · rintro ⟨f, hf, hfx, rfl⟩
    have hf' := (mem_eraseChord_iff C e f).1 hf
    refine ⟨?_, ⟨f, hf'.2, hfx, rfl⟩⟩
    intro hleft
    exact hf'.1 (C.chord_eq_of_left_eq hf'.2 he hleft)
  · rintro ⟨hae, f, hf, hfx, hfa⟩
    have hfe : f ≠ e := by
      intro h
      subst f
      exact hae hfa.symm
    exact ⟨f, (mem_eraseChord_iff C e f).2 ⟨hfe, hf⟩, hfx, hfa⟩

theorem erased_anchor_eq_of_anchor_ne (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) {x : Fin n}
    (hne : C.anchorKey x ≠ e.1) :
    (eraseChord C e).anchorKey x = C.anchorKey x := by
  rw [CanonicalMatching.anchorKey, erased_precedingLefts_eq_erase C he,
    CanonicalMatching.anchorKey]
  by_cases hC : (C.precedingLefts x).Nonempty
  · have hmaxmem := (C.precedingLefts x).max'_mem hC
    have hmaxne : (C.precedingLefts x).max' hC ≠ e.1 := by
      simpa [CanonicalMatching.anchorKey, dif_pos hC] using hne
    have hP : ((C.precedingLefts x).erase e.1).Nonempty :=
      ⟨(C.precedingLefts x).max' hC,
        Finset.mem_erase.mpr ⟨hmaxne, hmaxmem⟩⟩
    rw [dif_pos hP, dif_pos hC]
    exact (Finset.max'_eq_iff
      (s := (C.precedingLefts x).erase e.1) (H := hP)
      ((C.precedingLefts x).max' hC)).2
      ⟨Finset.mem_erase.mpr ⟨hmaxne, hmaxmem⟩, fun b hb =>
        Finset.le_max' _ b (Finset.mem_of_mem_erase hb)⟩
  · have hP : ¬((C.precedingLefts x).erase e.1).Nonempty := by
      intro h
      exact hC (Finset.Nonempty.mono (Finset.erase_subset _ _) h)
    rw [dif_neg hP, dif_neg hC]

theorem erased_precedingLefts_eq_of_anchor_eq_left
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1)
    {x : Fin n} (hanchor : C.anchorKey x = e.1) :
    (eraseChord C e).precedingLefts x =
      (eraseChord C e).precedingLefts e.1 := by
  have hex : e.1 < x ∧ x < e.2 := by
    rcases C.anchorKey_eq_root_or_chord x with hroot | ⟨f, hf, hfx, hfkey⟩
    · exact ((C.2.1 e he).1.ne' (hanchor.symm.trans hroot)).elim
    · have hleft : f.1 = e.1 := hfkey.trans hanchor
      have hfe : f = e := C.chord_eq_of_left_eq hf he hleft
      simpa [hfe] using hfx
  ext a
  rw [(eraseChord C e).mem_precedingLefts_iff,
    (eraseChord C e).mem_precedingLefts_iff]
  constructor
  · rintro ⟨f, hf, hfx, hfa⟩
    have hfC := (mem_eraseChord_iff C e f).1 hf |>.2
    have hfle : f.1 ≤ e.1 := by
      have hmem : f.1 ∈ C.precedingLefts x :=
        (C.mem_precedingLefts_iff x f.1).2 ⟨f, hfC, hfx, rfl⟩
      have hC : (C.precedingLefts x).Nonempty := ⟨f.1, hmem⟩
      have hmax : (C.precedingLefts x).max' hC = e.1 := by
        simpa [CanonicalMatching.anchorKey, dif_pos hC] using hanchor
      rw [← hmax]
      exact Finset.le_max' _ _ hmem
    have hflne : f.1 ≠ e.1 := by
      intro h
      have hfe := C.chord_eq_of_left_eq hfC he h
      exact (mem_eraseChord_iff C e f).1 hf |>.1 hfe
    have hflt : f.1 < e.1 := lt_of_le_of_ne hfle hflne
    exact ⟨f, hf, ⟨hflt, hex.1.trans hfx.2⟩, hfa⟩
  · rintro ⟨f, hf, hfe1, hfa⟩
    have hfe2 := containing_left_implies_containing_right C he hf hfe1
    exact ⟨f, hf, ⟨hfe1.1.trans hex.1, hex.2.trans hfe2.2⟩, hfa⟩

theorem erased_anchor_eq_of_anchor_eq_left
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1)
    {x : Fin n} (hanchor : C.anchorKey x = e.1) :
    (eraseChord C e).anchorKey x = (eraseChord C e).anchorKey e.1 := by
  unfold CanonicalMatching.anchorKey
  rw [erased_precedingLefts_eq_of_anchor_eq_left C he hanchor]

theorem erased_anchor_eq_if (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (x : Fin n) :
    (eraseChord C e).anchorKey x =
      if C.anchorKey x = e.1 then (eraseChord C e).anchorKey e.1
      else C.anchorKey x := by
  split_ifs with h
  · exact erased_anchor_eq_of_anchor_eq_left C he h
  · exact erased_anchor_eq_of_anchor_ne C he h

def freeEmbedding (C : CanonicalMatching n) (e : Fin n × Fin n) :
    C.free ↪ (eraseChord C e).free where
  toFun x := ⟨x.1, by
    rw [(eraseChord C e).mem_free_iff]
    exact ⟨(C.mem_free_iff x.1).1 x.2 |>.1,
      fun hx => ((C.mem_free_iff x.1).1 x.2 |>.2)
        (endpoint_mem_of_eraseChord C hx)⟩⟩
  inj' := by
    intro x y h
    exact Subtype.ext (congrArg
      (fun z : (eraseChord C e).free => z.1) h)

def liftMask (C : CanonicalMatching n) (e : Fin n × Fin n)
    (A : Finset C.free) : Finset (eraseChord C e).free :=
  A.map (freeEmbedding C e)

theorem mem_maskPoints_liftMask_iff (C : CanonicalMatching n)
    (e : Fin n × Fin n) (A : Finset C.free) (x : Fin n) :
    x ∈ (eraseChord C e).maskPoints (liftMask C e A) ↔
      x ∈ C.maskPoints A := by
  constructor
  · intro hx
    rw [CanonicalMatching.maskPoints, Finset.mem_image] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [liftMask, Finset.mem_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [CanonicalMatching.maskPoints, Finset.mem_image]
    refine ⟨z, hz, ?_⟩
    exact congrArg Subtype.val hzy |>.trans hyx
  · intro hx
    rw [CanonicalMatching.maskPoints, Finset.mem_image] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    rw [CanonicalMatching.maskPoints, Finset.mem_image]
    refine ⟨freeEmbedding C e z, ?_, ?_⟩
    · rw [liftMask, Finset.mem_map]
      exact ⟨z, hz, rfl⟩
    · exact hzx

theorem containing_right_implies_containing_left
    (C : CanonicalMatching n) {e f : Fin n × Fin n}
    (he : e ∈ C.1) (hf : f ∈ (eraseChord C e).1)
    (hcontains : f.1 < e.2 ∧ e.2 < f.2) :
    f.1 < e.1 ∧ e.1 < f.2 := by
  have hf' := (mem_eraseChord_iff C e f).1 hf
  have hef : e ≠ f := hf'.1.symm
  have hd := C.2.2.1 e he f hf'.2 hef
  refine ⟨?_, (C.2.1 e he).2.trans hcontains.2⟩
  by_contra hnot
  have hle : e.1 ≤ f.1 := le_of_not_gt hnot
  have hne : e.1 ≠ f.1 := by
    intro hEq
    have hnotmem := Finset.disjoint_left.mp hd
      (show e.1 ∈ chordEnds e by simp [chordEnds])
    exact hnotmem (show e.1 ∈ chordEnds f by simp [chordEnds, hEq])
  have hlt : e.1 < f.1 := lt_of_le_of_ne hle hne
  have hcross := C.2.2.2 e he f hf'.2 hlt
  exact hcross ⟨hlt, hcontains.1, hcontains.2⟩

theorem erased_endpoints_anchor_eq (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) :
    (eraseChord C e).anchorKey e.1 =
      (eraseChord C e).anchorKey e.2 := by
  have hsets : (eraseChord C e).precedingLefts e.1 =
      (eraseChord C e).precedingLefts e.2 := by
    ext a
    rw [(eraseChord C e).mem_precedingLefts_iff,
      (eraseChord C e).mem_precedingLefts_iff]
    constructor
    · rintro ⟨f, hf, hcontains, hfa⟩
      exact ⟨f, hf, containing_left_implies_containing_right C he hf hcontains, hfa⟩
    · rintro ⟨f, hf, hcontains, hfa⟩
      exact ⟨f, hf, containing_right_implies_containing_left C he hf hcontains, hfa⟩
  unfold CanonicalMatching.anchorKey
  rw [hsets]

noncomputable def parentMask (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (A : Finset C.free) :
    Finset (eraseChord C e).free :=
  insert ⟨e.1, erased_left_free C he⟩
    (insert ⟨e.2, erased_right_free C he⟩ (liftMask C e A))

theorem mem_parentMask_maskPoints_iff (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (A : Finset C.free) (x : Fin n) :
    x ∈ (eraseChord C e).maskPoints (parentMask C he A) ↔
      x = e.1 ∨ x = e.2 ∨ x ∈ C.maskPoints A := by
  rw [parentMask, CanonicalMatching.maskPoints, Finset.image_insert,
    Finset.image_insert]
  simp only [Finset.mem_insert, Subtype.exists, exists_and_right,
    exists_eq_right]
  rw [← CanonicalMatching.maskPoints, mem_maskPoints_liftMask_iff]

theorem parent_decodeKey_eq_relabel_child (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (A : Finset C.free) (x : Fin n) :
    (eraseChord C e).decodeKey (parentMask C he A) x =
      relabelKey (C.decodeKey A) e.1
        ((eraseChord C e).anchorKey e.1) x := by
  by_cases hxl : x = e.1
  · subst x
    have hleftC : e.1 ∈ C.endpoints :=
      (C.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩
    have hleftP : e.1 ∉ (eraseChord C e).endpoints := by
      simpa [erased_endpoint_iff C he e.1, (C.2.1 e he).2.ne']
    have hleftMask : e.1 ∈ (eraseChord C e).maskPoints (parentMask C he A) :=
      (mem_parentMask_maskPoints_iff C he A e.1).2 (Or.inl rfl)
    rw [CanonicalMatching.decodeKey, if_neg hleftP, if_pos hleftMask,
      relabelKey, CanonicalMatching.decodeKey, if_pos hleftC,
      C.endpointKey_left he, if_pos rfl]
  · by_cases hxr : x = e.2
    · subst x
      have hrightC : e.2 ∈ C.endpoints :=
        (C.mem_endpoints_iff e.2).2 ⟨e, he, Or.inr rfl⟩
      have hrightP : e.2 ∉ (eraseChord C e).endpoints := by
        simpa [erased_endpoint_iff C he e.2, hxl]
      have hrightMask : e.2 ∈ (eraseChord C e).maskPoints (parentMask C he A) :=
        (mem_parentMask_maskPoints_iff C he A e.2).2 (Or.inr (Or.inl rfl))
      rw [CanonicalMatching.decodeKey, if_neg hrightP, if_pos hrightMask,
        erased_endpoints_anchor_eq C he, relabelKey, CanonicalMatching.decodeKey,
        if_pos hrightC, C.endpointKey_right he, if_pos rfl]
    · by_cases hxP : x ∈ (eraseChord C e).endpoints
      · have hxC := endpoint_mem_of_eraseChord C hxP
        rw [CanonicalMatching.decodeKey, if_pos hxP, relabelKey,
          CanonicalMatching.decodeKey, if_pos hxC,
          eraseChord_endpointKey_eq C hxP]
        obtain ⟨f, hf, hxf⟩ := ((eraseChord C e).mem_endpoints_iff x).1 hxP
        have hf' := (mem_eraseChord_iff C e f).1 hf
        have hkey : C.endpointKey x = f.1 :=
          C.endpointKey_eq_left_of_mem hf'.2 hxf
        have hne : C.endpointKey x ≠ e.1 := by
          rw [hkey]
          intro h
          exact hf'.1 (C.chord_eq_of_left_eq hf'.2 he h)
        rw [if_neg hne]
      · have hxC : x ∉ C.endpoints := by
          intro hxC
          exact hxP ((erased_endpoint_iff C he x).2 ⟨hxC, hxl, hxr⟩)
        have hmask :
            x ∈ (eraseChord C e).maskPoints (parentMask C he A) ↔
              x ∈ C.maskPoints A := by
          rw [mem_parentMask_maskPoints_iff]
          simp [hxl, hxr]
        by_cases hxA : x ∈ C.maskPoints A
        · have hxPA := hmask.mpr hxA
          rw [CanonicalMatching.decodeKey, if_neg hxP, if_pos hxPA,
            erased_anchor_eq_if C he, relabelKey,
            CanonicalMatching.decodeKey, if_neg hxC, if_pos hxA]
        · have hxPA : x ∉ (eraseChord C e).maskPoints (parentMask C he A) :=
            fun h => hxA (hmask.mp h)
          rw [CanonicalMatching.decodeKey, if_neg hxP, if_neg hxPA,
            relabelKey, CanonicalMatching.decodeKey, if_neg hxC, if_neg hxA,
            if_neg hxl]

theorem anchorKey_lt_left_endpoint (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) : C.anchorKey e.1 < e.1 := by
  by_cases hroot : C.anchorKey e.1 = 0
  · rw [hroot]
    exact (C.2.1 e he).1
  · exact C.anchorKey_lt hroot

theorem erased_anchor_left_eq_child (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) :
    (eraseChord C e).anchorKey e.1 = C.anchorKey e.1 :=
  erased_anchor_eq_of_anchor_ne C he (anchorKey_lt_left_endpoint C he).ne

theorem decodedFinpartition_parentMask_eq_mergeBlocks
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1)
    (A : Finset C.free) :
    let P := C.decodedFinpartition A
    (eraseChord C e).decodedFinpartition (parentMask C he A) =
      P.mergeBlocks (P.part_mem.mpr (Finset.mem_univ e.1))
        (P.part_mem.mpr (Finset.mem_univ (C.anchorKey e.1)))
        (by
          intro h
          have hemem : e.1 ∈ P.part (C.anchorKey e.1) := by
            rw [← h]
            exact P.mem_part (Finset.mem_univ e.1)
          have hkeys := (C.mem_part_decodedFinpartition_iff A
            (C.anchorKey e.1) e.1).1 hemem
          have hleft : C.decodeKey A e.1 = e.1 := by
            have hend : e.1 ∈ C.endpoints :=
              (C.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩
            rw [CanonicalMatching.decodeKey, if_pos hend, C.endpointKey_left he]
          rw [Encoding.decodeKey_anchorKey C A e.1, hleft] at hkeys
          exact (anchorKey_lt_left_endpoint C he).ne hkeys) := by
  let P := C.decodedFinpartition A
  let f := C.decodeKey A
  let b := C.anchorKey e.1
  have ha : f e.1 = e.1 := by
    change C.decodeKey A e.1 = e.1
    have hend : e.1 ∈ C.endpoints :=
      (C.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩
    rw [CanonicalMatching.decodeKey, if_pos hend, C.endpointKey_left he]
  have hb : f b = b := by
    change C.decodeKey A (C.anchorKey e.1) = C.anchorKey e.1
    exact Encoding.decodeKey_anchorKey C A e.1
  have hab : e.1 ≠ b := (anchorKey_lt_left_endpoint C he).ne'
  have hmerge := keyPartition_relabel_eq_mergeBlocks f e.1 b ha hb hab
  have hrel : relabelKey f e.1 b =
      (eraseChord C e).decodeKey (parentMask C he A) := by
    funext x
    rw [parent_decodeKey_eq_relabel_child C he A x,
      erased_anchor_left_eq_child C he]
  rw [hrel] at hmerge
  simpa only [P, f, b, decodedFinpartition_eq_keyPartition] using hmerge

theorem decodedNC_child_mergesTo_parentMask
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1)
    (A : Finset C.free) :
    NC.mergesTo (C.decodedNC A)
      ((eraseChord C e).decodedNC (parentMask C he A)) := by
  let P := C.decodedFinpartition A
  let B₁ := P.part e.1
  let B₂ := P.part (C.anchorKey e.1)
  have hB₁ : B₁ ∈ P.parts := P.part_mem.mpr (Finset.mem_univ e.1)
  have hB₂ : B₂ ∈ P.parts :=
    P.part_mem.mpr (Finset.mem_univ (C.anchorKey e.1))
  have hne : B₁ ≠ B₂ := by
    intro h
    have hemem : e.1 ∈ P.part (C.anchorKey e.1) := by
      change e.1 ∈ B₂
      rw [← h]
      exact P.mem_part (Finset.mem_univ e.1)
    have hkeys := (C.mem_part_decodedFinpartition_iff A
      (C.anchorKey e.1) e.1).1 hemem
    have hleft : C.decodeKey A e.1 = e.1 := by
      have hend : e.1 ∈ C.endpoints :=
        (C.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩
      rw [CanonicalMatching.decodeKey, if_pos hend, C.endpointKey_left he]
    rw [Encoding.decodeKey_anchorKey C A e.1, hleft] at hkeys
    exact (anchorKey_lt_left_endpoint C he).ne hkeys
  refine ⟨B₁, hB₁, B₂, hB₂, hne, ?_⟩
  have hmerge := decodedFinpartition_parentMask_eq_mergeBlocks C he A
  have hparts := congrArg Finpartition.parts hmerge
  simpa [P, B₁, B₂, Finpartition.mergeBlocks_parts] using hparts

theorem decodedNC_child_adj_parentMask
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1)
    (A : Finset C.free) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj
      (C.decodedNC A)
      ((eraseChord C e).decodedNC (parentMask C he A)) :=
  Or.inl (decodedNC_child_mergesTo_parentMask C he A)

theorem anchorKey_ne_free_point (C : CanonicalMatching n)
    {q : Fin n} (hq : q ∈ C.free) (x : Fin n) : C.anchorKey x ≠ q := by
  rcases C.anchorKey_eq_root_or_chord x with hroot | ⟨f, hf, _hfx, hleft⟩
  · exact fun h => ((C.mem_free_iff q).1 hq |>.1) (h.symm.trans hroot)
  · intro h
    have hqend : q ∈ C.endpoints :=
      (C.mem_endpoints_iff q).2 ⟨f, hf, Or.inl (h.symm.trans hleft.symm)⟩
    exact ((C.mem_free_iff q).1 hq |>.2) hqend

theorem anchorKey_eq_chord_left_implies_inside (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) {x : Fin n}
    (hanchor : C.anchorKey x = e.1) : e.1 < x ∧ x < e.2 := by
  rcases C.anchorKey_eq_root_or_chord x with hroot | ⟨f, hf, hfx, hfkey⟩
  · exact ((C.2.1 e he).1.ne' (hanchor.symm.trans hroot)).elim
  · have hleft : f.1 = e.1 := hfkey.trans hanchor
    have hfe : f = e := C.chord_eq_of_left_eq hf he hleft
    simpa [hfe] using hfx

theorem decodeKey_rightMask_erase_relabel (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (A : Finset C.free)
    (hA : ∀ q ∈ A, e.2 < q.1) (x : Fin n) :
    C.decodeKey A x =
      relabelKey ((eraseChord C e).decodeKey (liftMask C e A)) e.2 e.1 x := by
  by_cases hxl : x = e.1
  · subst x
    have hleftC : e.1 ∈ C.endpoints :=
      (C.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩
    have hleftP : e.1 ∉ (eraseChord C e).endpoints := by
      simpa [erased_endpoint_iff C he e.1, (C.2.1 e he).2.ne']
    have hleftMask : e.1 ∉ (eraseChord C e).maskPoints (liftMask C e A) := by
      rw [mem_maskPoints_liftMask_iff]
      intro h
      obtain ⟨q, hqA, hq⟩ := Finset.mem_image.mp h
      exact ((C.mem_free_iff q.1).1 q.2 |>.2)
        ((C.mem_endpoints_iff q.1).2 ⟨e, he, Or.inl hq⟩)
    rw [CanonicalMatching.decodeKey, if_pos hleftC, C.endpointKey_left he,
      relabelKey, CanonicalMatching.decodeKey, if_neg hleftP, if_neg hleftMask]
    split_ifs with h
    · exact ((C.2.1 e he).2.ne h).elim
    · rfl
  · by_cases hxr : x = e.2
    · subst x
      have hrightC : e.2 ∈ C.endpoints :=
        (C.mem_endpoints_iff e.2).2 ⟨e, he, Or.inr rfl⟩
      have hrightP : e.2 ∉ (eraseChord C e).endpoints := by
        simpa [erased_endpoint_iff C he e.2, hxl]
      have hrightMask : e.2 ∉ (eraseChord C e).maskPoints (liftMask C e A) := by
        rw [mem_maskPoints_liftMask_iff]
        intro h
        obtain ⟨q, hqA, hq⟩ := Finset.mem_image.mp h
        exact ((C.mem_free_iff q.1).1 q.2 |>.2)
          ((C.mem_endpoints_iff q.1).2 ⟨e, he, Or.inr hq⟩)
      have hchild : C.decodeKey A e.2 = e.1 := by
        rw [CanonicalMatching.decodeKey, if_pos hrightC, C.endpointKey_right he]
      have hparent : (eraseChord C e).decodeKey (liftMask C e A) e.2 = e.2 := by
        rw [CanonicalMatching.decodeKey, if_neg hrightP, if_neg hrightMask]
      rw [hchild, relabelKey, hparent, if_pos rfl]
    · by_cases hxP : x ∈ (eraseChord C e).endpoints
      · have hxC := endpoint_mem_of_eraseChord C hxP
        rw [CanonicalMatching.decodeKey, if_pos hxC, relabelKey,
          CanonicalMatching.decodeKey, if_pos hxP,
          eraseChord_endpointKey_eq C hxP]
        obtain ⟨f, hf, hxf⟩ := ((eraseChord C e).mem_endpoints_iff x).1 hxP
        have hf' := (mem_eraseChord_iff C e f).1 hf
        have hkey : C.endpointKey x = f.1 :=
          C.endpointKey_eq_left_of_mem hf'.2 hxf
        have hne : C.endpointKey x ≠ e.2 := by
          rw [hkey]
          intro h
          have hd := C.2.2.1 f hf'.2 e he hf'.1
          exact (Finset.disjoint_left.mp hd
            (show f.1 ∈ chordEnds f by simp [chordEnds]))
            (show f.1 ∈ chordEnds e by simp [chordEnds, h])
        rw [if_neg hne]
      · have hxC : x ∉ C.endpoints := by
          intro hxC
          exact hxP ((erased_endpoint_iff C he x).2 ⟨hxC, hxl, hxr⟩)
        have hmask :
            x ∈ (eraseChord C e).maskPoints (liftMask C e A) ↔
              x ∈ C.maskPoints A := mem_maskPoints_liftMask_iff C e A x
        by_cases hxA : x ∈ C.maskPoints A
        · have hxPA := hmask.mpr hxA
          obtain ⟨q, hqA, hqx⟩ := Finset.mem_image.mp hxA
          have hex : e.2 < x := hqx ▸ hA q hqA
          have hanchorNe : C.anchorKey x ≠ e.1 := by
            intro h
            exact (not_lt_of_ge
              (le_of_lt (anchorKey_eq_chord_left_implies_inside C he h).2)) hex
          have hanchor := erased_anchor_eq_of_anchor_ne C he hanchorNe
          have hfreeRight : e.2 ∈ (eraseChord C e).free := erased_right_free C he
          have hparentNe : (eraseChord C e).anchorKey x ≠ e.2 :=
            anchorKey_ne_free_point (eraseChord C e) hfreeRight x
          rw [CanonicalMatching.decodeKey, if_neg hxC, if_pos hxA,
            relabelKey, CanonicalMatching.decodeKey, if_neg hxP, if_pos hxPA,
            if_neg hparentNe, hanchor]
        · have hxPA : x ∉ (eraseChord C e).maskPoints (liftMask C e A) :=
            fun h => hxA (hmask.mp h)
          rw [CanonicalMatching.decodeKey, if_neg hxC, if_neg hxA,
            relabelKey, CanonicalMatching.decodeKey, if_neg hxP, if_neg hxPA,
            if_neg hxr]

theorem decodedNC_rightMask_parent_mergesTo_child
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1)
    (A : Finset C.free) (hA : ∀ q ∈ A, e.2 < q.1) :
    NC.mergesTo
      ((eraseChord C e).decodedNC (liftMask C e A))
      (C.decodedNC A) := by
  let Q := eraseChord C e
  let P := Q.decodedFinpartition (liftMask C e A)
  let f := Q.decodeKey (liftMask C e A)
  have ha : f e.2 = e.2 := by
    change Q.decodeKey (liftMask C e A) e.2 = e.2
    have hend : e.2 ∉ Q.endpoints := by
      simpa [Q, erased_endpoint_iff C he e.2, (C.2.1 e he).2.ne]
    have hmask : e.2 ∉ Q.maskPoints (liftMask C e A) := by
      rw [mem_maskPoints_liftMask_iff]
      intro h
      obtain ⟨q, _hq, hq⟩ := Finset.mem_image.mp h
      exact ((C.mem_free_iff q.1).1 q.2 |>.2)
        ((C.mem_endpoints_iff q.1).2 ⟨e, he, Or.inr hq⟩)
    rw [CanonicalMatching.decodeKey, if_neg hend, if_neg hmask]
  have hb : f e.1 = e.1 := by
    change Q.decodeKey (liftMask C e A) e.1 = e.1
    have hend : e.1 ∉ Q.endpoints := by
      simpa [Q, erased_endpoint_iff C he e.1, (C.2.1 e he).2.ne']
    have hmask : e.1 ∉ Q.maskPoints (liftMask C e A) := by
      rw [mem_maskPoints_liftMask_iff]
      intro h
      obtain ⟨q, _hq, hq⟩ := Finset.mem_image.mp h
      exact ((C.mem_free_iff q.1).1 q.2 |>.2)
        ((C.mem_endpoints_iff q.1).2 ⟨e, he, Or.inl hq⟩)
    rw [CanonicalMatching.decodeKey, if_neg hend, if_neg hmask]
  have hrel : relabelKey f e.2 e.1 = C.decodeKey A := by
    funext x
    exact (decodeKey_rightMask_erase_relabel C he A hA x).symm
  have hmerge := keyPartition_relabel_eq_mergeBlocks f e.2 e.1 ha hb
    (C.2.1 e he).2.ne'
  rw [hrel] at hmerge
  have haQ : Q.decodeKey (liftMask C e A) e.2 = e.2 := ha
  have hbQ : Q.decodeKey (liftMask C e A) e.1 = e.1 := hb
  have hfin : C.decodedFinpartition A =
      P.mergeBlocks (P.part_mem.mpr (Finset.mem_univ e.2))
        (P.part_mem.mpr (Finset.mem_univ e.1)) (by
          intro h
          have hemem : e.2 ∈ P.part e.1 := by
            rw [← h]
            exact P.mem_part (Finset.mem_univ e.2)
          have hkeys := (Q.mem_part_decodedFinpartition_iff
            (liftMask C e A) e.1 e.2).1 hemem
          rw [hbQ, haQ] at hkeys
          exact (C.2.1 e he).2.ne hkeys) := by
    simpa only [P, f, Q, decodedFinpartition_eq_keyPartition] using hmerge
  let B₁ := P.part e.2
  let B₂ := P.part e.1
  have hB₁ : B₁ ∈ P.parts := P.part_mem.mpr (Finset.mem_univ e.2)
  have hB₂ : B₂ ∈ P.parts := P.part_mem.mpr (Finset.mem_univ e.1)
  have hne : B₁ ≠ B₂ := by
    intro h
    have hemem : e.2 ∈ P.part e.1 := by
      change e.2 ∈ B₂
      rw [← h]
      exact P.mem_part (Finset.mem_univ e.2)
    have hkeys := (Q.mem_part_decodedFinpartition_iff
      (liftMask C e A) e.1 e.2).1 hemem
    rw [hbQ, haQ] at hkeys
    exact (C.2.1 e he).2.ne hkeys
  refine ⟨B₁, hB₁, B₂, hB₂, hne, ?_⟩
  have hparts := congrArg Finpartition.parts hfin
  simpa [P, B₁, B₂, Finpartition.mergeBlocks_parts] using hparts

theorem decodedNC_rightMask_parent_adj_child
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1)
    (A : Finset C.free) (hA : ∀ q ∈ A, e.2 < q.1) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj
      ((eraseChord C e).decodedNC (liftMask C e A))
      (C.decodedNC A) :=
  Or.inl (decodedNC_rightMask_parent_mergesTo_child C he A hA)

theorem decodeKey_empty_erase_relabel (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (x : Fin n) :
    C.decodeKey (∅ : Finset C.free) x =
      relabelKey ((eraseChord C e).decodeKey
        (∅ : Finset (eraseChord C e).free)) e.2 e.1 x := by
  by_cases hxl : x = e.1
  · subst x
    have hleftC : e.1 ∈ C.endpoints :=
      (C.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩
    have hleftP : e.1 ∉ (eraseChord C e).endpoints := by
      simpa [erased_endpoint_iff C he e.1, (C.2.1 e he).2.ne']
    rw [decodeKey_empty C, if_pos hleftC, C.endpointKey_left he,
      relabelKey, decodeKey_empty (eraseChord C e), if_neg hleftP]
    split_ifs with h
    · exact ((C.2.1 e he).2.ne h).elim
    · rfl
  · by_cases hxr : x = e.2
    · subst x
      have hrightC : e.2 ∈ C.endpoints :=
        (C.mem_endpoints_iff e.2).2 ⟨e, he, Or.inr rfl⟩
      have hrightP : e.2 ∉ (eraseChord C e).endpoints := by
        simpa [erased_endpoint_iff C he e.2, hxl]
      rw [decodeKey_empty C, if_pos hrightC, C.endpointKey_right he,
        relabelKey, decodeKey_empty (eraseChord C e), if_neg hrightP, if_pos rfl]
    · by_cases hxP : x ∈ (eraseChord C e).endpoints
      · have hxC := endpoint_mem_of_eraseChord C hxP
        rw [decodeKey_empty C, if_pos hxC, relabelKey,
          decodeKey_empty (eraseChord C e), if_pos hxP,
          eraseChord_endpointKey_eq C hxP]
        have hkeyne : C.endpointKey x ≠ e.2 := by
          obtain ⟨f, hf, hxf⟩ := ((eraseChord C e).mem_endpoints_iff x).1 hxP
          have hf' := (mem_eraseChord_iff C e f).1 hf
          have hfC := hf'.2
          rw [C.endpointKey_eq_left_of_mem hfC hxf]
          intro h
          have hd := C.2.2.1 f hfC e he hf'.1
          exact (Finset.disjoint_left.mp hd
            (show f.1 ∈ chordEnds f by simp [chordEnds]))
            (show f.1 ∈ chordEnds e by simp [chordEnds, h])
        rw [if_neg hkeyne]
      · have hxC : x ∉ C.endpoints := by
          intro hxC
          exact hxP ((erased_endpoint_iff C he x).2 ⟨hxC, hxl, hxr⟩)
        rw [decodeKey_empty C, if_neg hxC, relabelKey,
          decodeKey_empty (eraseChord C e), if_neg hxP, if_neg hxr]

theorem decodedFinpartition_empty_eq_mergeBlocks_erase
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1) :
    let P := (eraseChord C e).decodedFinpartition
      (∅ : Finset (eraseChord C e).free)
    C.decodedFinpartition (∅ : Finset C.free) =
      P.mergeBlocks (P.part_mem.mpr (Finset.mem_univ e.2))
        (P.part_mem.mpr (Finset.mem_univ e.1))
        (by
          intro h
          have her : e.2 ∈ P.part e.1 := by
            rw [← h]
            exact P.mem_part (Finset.mem_univ e.2)
          have hkeys := ((eraseChord C e).mem_part_decodedFinpartition_iff
            (∅ : Finset (eraseChord C e).free) e.1 e.2).1 her
          have hl : (eraseChord C e).decodeKey
              (∅ : Finset (eraseChord C e).free) e.1 = e.1 := by
            rw [decodeKey_empty, if_neg (by
              simpa [erased_endpoint_iff C he e.1,
                (C.2.1 e he).2.ne'])]
          have hr : (eraseChord C e).decodeKey
              (∅ : Finset (eraseChord C e).free) e.2 = e.2 := by
            rw [decodeKey_empty, if_neg (by
              simpa [erased_endpoint_iff C he e.2,
                (C.2.1 e he).2.ne])]
          rw [hl, hr] at hkeys
          exact (C.2.1 e he).2.ne hkeys) := by
  let P := (eraseChord C e).decodedFinpartition
    (∅ : Finset (eraseChord C e).free)
  let f := (eraseChord C e).decodeKey
    (∅ : Finset (eraseChord C e).free)
  have hl : f e.1 = e.1 := by
    change (eraseChord C e).decodeKey
      (∅ : Finset (eraseChord C e).free) e.1 = e.1
    rw [decodeKey_empty, if_neg (by
      simpa [erased_endpoint_iff C he e.1, (C.2.1 e he).2.ne'])]
  have hr : f e.2 = e.2 := by
    change (eraseChord C e).decodeKey
      (∅ : Finset (eraseChord C e).free) e.2 = e.2
    rw [decodeKey_empty, if_neg (by
      simpa [erased_endpoint_iff C he e.2, (C.2.1 e he).2.ne])]
  have hmerge := keyPartition_relabel_eq_mergeBlocks f e.2 e.1
    hr hl (C.2.1 e he).2.ne'
  have hrel : relabelKey f e.2 e.1 =
      C.decodeKey (∅ : Finset C.free) := by
    funext x
    exact (decodeKey_empty_erase_relabel C he x).symm
  rw [hrel] at hmerge
  simpa only [P, f, decodedFinpartition_eq_keyPartition] using hmerge

theorem decodedNC_empty_parent_mergesTo_child
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1) :
    NC.mergesTo
      ((eraseChord C e).decodedNC (∅ : Finset (eraseChord C e).free))
      (C.decodedNC (∅ : Finset C.free)) := by
  let P := (eraseChord C e).decodedFinpartition
    (∅ : Finset (eraseChord C e).free)
  let B₁ := P.part e.2
  let B₂ := P.part e.1
  have hB₁ : B₁ ∈ P.parts := P.part_mem.mpr (Finset.mem_univ e.2)
  have hB₂ : B₂ ∈ P.parts := P.part_mem.mpr (Finset.mem_univ e.1)
  have hne : B₁ ≠ B₂ := by
    intro h
    have her : e.2 ∈ P.part e.1 := by
      change e.2 ∈ B₂
      rw [← h]
      exact P.mem_part (Finset.mem_univ e.2)
    have hkeys := ((eraseChord C e).mem_part_decodedFinpartition_iff
      (∅ : Finset (eraseChord C e).free) e.1 e.2).1 her
    have hl : (eraseChord C e).decodeKey
        (∅ : Finset (eraseChord C e).free) e.1 = e.1 := by
      rw [decodeKey_empty, if_neg (by
        simpa [erased_endpoint_iff C he e.1, (C.2.1 e he).2.ne'])]
    have hr : (eraseChord C e).decodeKey
        (∅ : Finset (eraseChord C e).free) e.2 = e.2 := by
      rw [decodeKey_empty, if_neg (by
        simpa [erased_endpoint_iff C he e.2, (C.2.1 e he).2.ne])]
    rw [hl, hr] at hkeys
    exact (C.2.1 e he).2.ne hkeys
  refine ⟨B₁, hB₁, B₂, hB₂, hne, ?_⟩
  have hmerge := decodedFinpartition_empty_eq_mergeBlocks_erase C he
  have hparts := congrArg Finpartition.parts hmerge
  simpa [P, B₁, B₂, Finpartition.mergeBlocks_parts] using hparts

theorem decodedNC_empty_parent_adj_child
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj
      ((eraseChord C e).decodedNC (∅ : Finset (eraseChord C e).free))
      (C.decodedNC (∅ : Finset C.free)) :=
  Or.inl (decodedNC_empty_parent_mergesTo_child C he)

theorem containing_left_iff_containing_right
    (C : CanonicalMatching n) {e f : Fin n × Fin n}
    (he : e ∈ C.1) (hf : f ∈ (eraseChord C e).1) :
    (f.1 < e.1 ∧ e.1 < f.2) ↔ (f.1 < e.2 ∧ e.2 < f.2) := by
  have hf' := (mem_eraseChord_iff C e f).1 hf
  have hef : e ≠ f := hf'.1.symm
  have hd := C.2.2.1 e he f hf'.2 hef
  constructor
  · rintro ⟨hfl, hlf⟩
    refine ⟨hfl.trans (C.2.1 e he).2, ?_⟩
    by_contra hnot
    have hle : f.2 ≤ e.2 := le_of_not_gt hnot
    have hne : f.2 ≠ e.2 := by
      intro hEq
      have hnotmem := Finset.disjoint_left.mp hd
        (show e.2 ∈ chordEnds e by simp [chordEnds])
      exact hnotmem (show e.2 ∈ chordEnds f by simp [chordEnds, ← hEq])
    have hlt : f.2 < e.2 := lt_of_le_of_ne hle hne
    have hcross := C.2.2.2 f hf'.2 e he hfl
    exact hcross ⟨hfl, hlf, hlt⟩
  · rintro ⟨hfl, hrf⟩
    refine ⟨?_, (C.2.1 e he).2.trans hrf⟩
    by_contra hnot
    have hle : e.1 ≤ f.1 := le_of_not_gt hnot
    have hne : e.1 ≠ f.1 := by
      intro hEq
      have hnotmem := Finset.disjoint_left.mp hd
        (show e.1 ∈ chordEnds e by simp [chordEnds])
      exact hnotmem (show e.1 ∈ chordEnds f by simp [chordEnds, hEq])
    have hlt : e.1 < f.1 := lt_of_le_of_ne hle hne
    have hcross := C.2.2.2 e he f hf'.2 hlt
    exact hcross ⟨hlt, hfl, hrf⟩

theorem erased_precedingLefts_eq (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) :
    (eraseChord C e).precedingLefts e.1 =
      (eraseChord C e).precedingLefts e.2 := by
  ext a
  rw [(eraseChord C e).mem_precedingLefts_iff,
    (eraseChord C e).mem_precedingLefts_iff]
  constructor
  · rintro ⟨f, hf, hcontains, hfa⟩
    exact ⟨f, hf, (containing_left_iff_containing_right C he hf).1 hcontains, hfa⟩
  · rintro ⟨f, hf, hcontains, hfa⟩
    exact ⟨f, hf, (containing_left_iff_containing_right C he hf).2 hcontains, hfa⟩

theorem erased_anchor_eq (C : CanonicalMatching n) {e : Fin n × Fin n}
    (he : e ∈ C.1) :
    (eraseChord C e).anchorKey e.1 = (eraseChord C e).anchorKey e.2 := by
  unfold CanonicalMatching.anchorKey
  rw [erased_precedingLefts_eq C he]

end Tree
end Petersen
end Hamilton.Infrastructure
