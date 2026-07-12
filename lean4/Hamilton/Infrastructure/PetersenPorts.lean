/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.PetersenBlockTree
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Fin

/-!
# Lexicographic Petersen block ports

This file turns the local cross-block refinement edges into the three explicit
ports of the binary-reflected Gray cycles.
-/

namespace Hamilton.Infrastructure
namespace Petersen
namespace Ports

open Finset

variable {n : Nat} [NeZero n]

theorem chordLex_nonempty (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    (C.1.map toLex.toEmbedding).Nonempty := by
  obtain ⟨e, he⟩ := hC
  exact ⟨toLex e, Finset.mem_map.mpr ⟨e, he, rfl⟩⟩

noncomputable def firstChord (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    Fin n × Fin n :=
  ofLex ((C.1.map toLex.toEmbedding).min'
    (chordLex_nonempty C hC))

theorem firstChord_mem (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    firstChord C hC ∈ C.1 := by
  have hmem := (C.1.map toLex.toEmbedding).min'_mem
    (chordLex_nonempty C hC)
  rw [Finset.mem_map] at hmem
  obtain ⟨e, he, hEq⟩ := hmem
  simpa [firstChord, ← hEq] using he

noncomputable def parent (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    CanonicalMatching n := Tree.eraseChord C (firstChord C hC)

@[simp]
theorem parent_val (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    (parent C hC).1 = C.1.erase (firstChord C hC) := rfl

theorem parent_card (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    (parent C hC).1.card + 1 = C.1.card := by
  rw [parent_val, Finset.card_erase_of_mem (firstChord_mem C hC)]
  have hpos : 0 < C.1.card := Finset.card_pos.mpr hC
  omega

theorem parent_free_card (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    (parent C hC).free.card = C.free.card + 2 := by
  have hCledger := Encoding.free_card_ledger C
  have hPledger := Encoding.free_card_ledger (parent C hC)
  have hcard := parent_card C hC
  omega

noncomputable def firstLeft (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    (parent C hC).free :=
  ⟨(firstChord C hC).1,
    Tree.erased_left_free C (firstChord_mem C hC)⟩

noncomputable def firstRight (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    (parent C hC).free :=
  ⟨(firstChord C hC).2,
    Tree.erased_right_free C (firstChord_mem C hC)⟩

/-- The increasing enumeration of the free points. -/
noncomputable def freeAt (C : CanonicalMatching n) :
    Fin C.free.card → C.free := C.free.orderIsoOfFin rfl

/-- The rank of a free point in increasing ambient order. -/
noncomputable def freeRank (C : CanonicalMatching n) :
    C.free → Fin C.free.card := (C.free.orderIsoOfFin rfl).symm

@[simp]
theorem freeAt_freeRank (C : CanonicalMatching n) (x : C.free) :
    freeAt C (freeRank C x) = x := by
  exact (C.free.orderIsoOfFin rfl).apply_symm_apply x

@[simp]
theorem freeRank_freeAt (C : CanonicalMatching n) (i : Fin C.free.card) :
    freeRank C (freeAt C i) = i := by
  exact (C.free.orderIsoOfFin rfl).symm_apply_apply i

theorem freeAt_strictMono (C : CanonicalMatching n) :
    StrictMono (fun i : Fin C.free.card => (freeAt C i).1) :=
  (C.free.orderIsoOfFin rfl).strictMono

noncomputable def firstLeftRank (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    Fin (parent C hC).free.card := freeRank (parent C hC) (firstLeft C hC)

noncomputable def firstRightRank (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    Fin (parent C hC).free.card := freeRank (parent C hC) (firstRight C hC)

theorem firstLeftRank_lt_firstRightRank (C : CanonicalMatching n)
    (hC : C.1.Nonempty) : firstLeftRank C hC < firstRightRank C hC := by
  change ((parent C hC).free.orderIsoOfFin rfl).symm (firstLeft C hC) <
    ((parent C hC).free.orderIsoOfFin rfl).symm (firstRight C hC)
  exact ((parent C hC).free.orderIsoOfFin rfl).symm.strictMono (C.2.1
    (firstChord C hC) (firstChord_mem C hC) |>.2)

theorem firstChord_rank_cases (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    0 < (firstLeftRank C hC).val ∨
      ((firstLeftRank C hC).val = 0 ∧ 2 ≤ (firstRightRank C hC).val) ∨
      ((firstLeftRank C hC).val = 0 ∧ (firstRightRank C hC).val = 1) := by
  have hlt := firstLeftRank_lt_firstRightRank C hC
  omega

theorem freeRank_lt_iff (C : CanonicalMatching n) (x y : C.free) :
    freeRank C x < freeRank C y ↔ x.1 < y.1 := by
  exact (C.free.orderIsoOfFin rfl).symm.lt_iff_lt

theorem free_card_pos_of_even (C : CanonicalMatching n) (hn : Even n) :
    0 < C.free.card := by
  obtain ⟨k, hk⟩ := Encoding.free_card_odd_of_even C hn
  omega

noncomputable def lowestFree (C : CanonicalMatching n) (h : 0 < C.free.card) : C.free :=
  freeAt C ⟨0, h⟩

noncomputable def highestFree (C : CanonicalMatching n) (h : 0 < C.free.card) : C.free :=
  freeAt C ⟨C.free.card - 1, Nat.sub_lt h (Nat.succ_pos 0)⟩

noncomputable def secondFree (C : CanonicalMatching n) (h : 2 ≤ C.free.card) : C.free :=
  freeAt C ⟨1, h⟩

@[simp]
theorem freeRank_lowestFree (C : CanonicalMatching n) (h : 0 < C.free.card) :
    freeRank C (lowestFree C h) = ⟨0, h⟩ := freeRank_freeAt C _

@[simp]
theorem freeRank_highestFree (C : CanonicalMatching n) (h : 0 < C.free.card) :
    freeRank C (highestFree C h) =
      ⟨C.free.card - 1, Nat.sub_lt h (Nat.succ_pos 0)⟩ := freeRank_freeAt C _

@[simp]
theorem freeRank_secondFree (C : CanonicalMatching n) (h : 2 ≤ C.free.card) :
    freeRank C (secondFree C h) = ⟨1, h⟩ := freeRank_freeAt C _

theorem orderEmb_filter_lt_card {α : Type*} [LinearOrder α]
    (G : Finset α) (i : Fin G.card) :
    (G.filter (fun t => t < G.orderEmbOfFin rfl i)).card = i.val := by
  let F := Finset.univ.filter (fun j : Fin G.card => (j : Nat) < i.val)
  have himage : Finset.image (G.orderEmbOfFin rfl) F =
      G.filter (fun t => t < G.orderEmbOfFin rfl i) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, hjF, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem G rfl j,
        (G.orderEmbOfFin rfl).strictMono (Finset.mem_filter.mp hjF).2⟩
    · rintro ⟨htG, htt⟩
      have htrange : t ∈ Set.range (G.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin G rfl]
        exact htG
      obtain ⟨j, rfl⟩ := htrange
      have hjlt : (j : Nat) < i.val :=
        (OrderEmbedding.lt_iff_lt (G.orderEmbOfFin rfl)).mp htt
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjlt⟩, rfl⟩
  have hcardImage : (Finset.image (G.orderEmbOfFin rfl) F).card = F.card :=
    Finset.card_image_of_injOn
      (fun _ _ _ _ h => (G.orderEmbOfFin rfl).injective h)
  have hcardF : F.card = i.val := by
    have h := Fin.card_filter_val_lt (n := G.card) (m := i.val)
    simpa [F, Nat.min_eq_right (Nat.le_of_lt i.2)] using h
  rw [← himage, hcardImage, hcardF]

theorem freeRank_eq_filter_card (C : CanonicalMatching n) (x : C.free) :
    (C.free.filter (fun t => t < x.1)).card = (freeRank C x).val := by
  have h := orderEmb_filter_lt_card C.free (freeRank C x)
  have hx : C.free.orderEmbOfFin rfl (freeRank C x) = x.1 := by
    change (freeAt C (freeRank C x)).1 = x.1
    rw [freeAt_freeRank]
  simpa [hx] using h

theorem child_free_iff_parent_free (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (x : Fin n) :
    x ∈ C.free ↔
      x ∈ (Tree.eraseChord C e).free ∧ x ≠ e.1 ∧ x ≠ e.2 := by
  constructor
  · intro hx
    have hx' := (C.mem_free_iff x).1 hx
    refine ⟨?_, ?_, ?_⟩
    · rw [(Tree.eraseChord C e).mem_free_iff]
      exact ⟨hx'.1, fun h => hx'.2 (Tree.endpoint_mem_of_eraseChord C h)⟩
    · intro h
      exact hx'.2 ((C.mem_endpoints_iff x).2 ⟨e, he, Or.inl h⟩)
    · intro h
      exact hx'.2 ((C.mem_endpoints_iff x).2 ⟨e, he, Or.inr h⟩)
  · rintro ⟨hxP, hxl, hxr⟩
    rw [C.mem_free_iff]
    refine ⟨((Tree.eraseChord C e).mem_free_iff x).1 hxP |>.1, ?_⟩
    intro hxC
    exact ((Tree.eraseChord C e).mem_free_iff x).1 hxP |>.2
      ((Tree.erased_endpoint_iff C he x).2 ⟨hxC, hxl, hxr⟩)

theorem freeRank_parent_eq_child_of_lt_left (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (x : C.free) (hx : x.1 < e.1) :
    (freeRank (Tree.eraseChord C e) (Tree.freeEmbedding C e x)).val =
      (freeRank C x).val := by
  let P := Tree.eraseChord C e
  have hsets : C.free.filter (fun z => z < x.1) =
      P.free.filter (fun z => z < x.1) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hzC, hzx⟩
      exact ⟨(child_free_iff_parent_free C he z).1 hzC |>.1, hzx⟩
    · rintro ⟨hzP, hzx⟩
      have hzl : z ≠ e.1 := fun h => (not_lt_of_ge (h ▸ le_of_lt hx)) hzx
      have hzr : z ≠ e.2 := fun h =>
        (not_lt_of_ge (h ▸ le_of_lt (hx.trans (C.2.1 e he).2))) hzx
      exact ⟨(child_free_iff_parent_free C he z).2 ⟨hzP, hzl, hzr⟩, hzx⟩
  rw [← freeRank_eq_filter_card C x,
    ← freeRank_eq_filter_card P (Tree.freeEmbedding C e x)]
  exact congrArg Finset.card hsets.symm

theorem freeRank_parent_eq_child_add_one_of_between
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1)
    (x : C.free) (hl : e.1 < x.1) (hr : x.1 < e.2) :
    (freeRank (Tree.eraseChord C e) (Tree.freeEmbedding C e x)).val =
      (freeRank C x).val + 1 := by
  let P := Tree.eraseChord C e
  change (freeRank P (Tree.freeEmbedding C e x)).val =
    (freeRank C x).val + 1
  have hsets : P.free.filter (fun z => z < x.1) =
      insert e.1 (C.free.filter (fun z => z < x.1)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hzP, hzx⟩
      by_cases hzl : z = e.1
      · exact Or.inl hzl
      · right
        have hzr : z ≠ e.2 := fun h => (not_lt_of_ge (h ▸ le_of_lt hr)) hzx
        exact ⟨(child_free_iff_parent_free C he z).2 ⟨hzP, hzl, hzr⟩, hzx⟩
    · rintro (rfl | ⟨hzC, hzx⟩)
      · exact ⟨Tree.erased_left_free C he, hl⟩
      · exact ⟨(child_free_iff_parent_free C he z).1 hzC |>.1, hzx⟩
  have hnot : e.1 ∉ C.free.filter (fun z => z < x.1) := by
    intro h
    exact ((child_free_iff_parent_free C he e.1).1
      (Finset.mem_filter.mp h).1 |>.2.1) rfl
  have hcard := congrArg Finset.card hsets
  rw [Finset.card_insert_of_notMem hnot] at hcard
  have hrankC := freeRank_eq_filter_card C x
  have hrankP := freeRank_eq_filter_card P (Tree.freeEmbedding C e x)
  change (P.free.filter (fun z => z < x.1)).card =
    (freeRank P (Tree.freeEmbedding C e x)).val at hrankP
  omega

theorem freeRank_parent_eq_child_add_two_of_right
    (C : CanonicalMatching n) {e : Fin n × Fin n} (he : e ∈ C.1)
    (x : C.free) (hx : e.2 < x.1) :
    (freeRank (Tree.eraseChord C e) (Tree.freeEmbedding C e x)).val =
      (freeRank C x).val + 2 := by
  let P := Tree.eraseChord C e
  change (freeRank P (Tree.freeEmbedding C e x)).val =
    (freeRank C x).val + 2
  have hsets : P.free.filter (fun z => z < x.1) =
      insert e.1 (insert e.2 (C.free.filter (fun z => z < x.1))) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hzP, hzx⟩
      by_cases hzl : z = e.1
      · exact Or.inl hzl
      · by_cases hzr : z = e.2
        · exact Or.inr (Or.inl hzr)
        · exact Or.inr (Or.inr
            ⟨(child_free_iff_parent_free C he z).2 ⟨hzP, hzl, hzr⟩, hzx⟩)
    · rintro (rfl | rfl | ⟨hzC, hzx⟩)
      · exact ⟨Tree.erased_left_free C he, (C.2.1 e he).2.trans hx⟩
      · exact ⟨Tree.erased_right_free C he, hx⟩
      · exact ⟨(child_free_iff_parent_free C he z).1 hzC |>.1, hzx⟩
  have hnotR : e.2 ∉ C.free.filter (fun z => z < x.1) := by
    intro h
    exact ((child_free_iff_parent_free C he e.2).1
      (Finset.mem_filter.mp h).1 |>.2.2) rfl
  have hnotL : e.1 ∉ insert e.2 (C.free.filter (fun z => z < x.1)) := by
    simp only [Finset.mem_insert]
    intro h
    rcases h with h | h
    · exact (C.2.1 e he).2.ne h
    · exact ((child_free_iff_parent_free C he e.1).1
        (Finset.mem_filter.mp h).1 |>.2.1) rfl
  have hcard := congrArg Finset.card hsets
  rw [Finset.card_insert_of_notMem hnotL,
    Finset.card_insert_of_notMem hnotR] at hcard
  have hrankC := freeRank_eq_filter_card C x
  have hrankP := freeRank_eq_filter_card P (Tree.freeEmbedding C e x)
  change (P.free.filter (fun z => z < x.1)).card =
    (freeRank P (Tree.freeEmbedding C e x)).val at hrankP
  omega

theorem lowestFree_lt_firstLeft_of_leftRank_pos
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : 0 < (firstLeftRank C hC).val) :
    (lowestFree C (free_card_pos_of_even C hn)).1 < (firstChord C hC).1 := by
  let e := firstChord C hC
  let P := parent C hC
  let t := lowestFree C (free_card_pos_of_even C hn)
  have he : e ∈ C.1 := firstChord_mem C hC
  have htRank : (freeRank C t).val = 0 := by simp [t]
  have htl : t.1 ≠ e.1 := fun h =>
    ((child_free_iff_parent_free C he t.1).1 t.2 |>.2.1) h
  have htr : t.1 ≠ e.2 := fun h =>
    ((child_free_iff_parent_free C he t.1).1 t.2 |>.2.2) h
  rcases lt_or_gt_of_ne htl with hlt | hgt
  · exact hlt
  · rcases lt_or_gt_of_ne htr with hbetween | hright
    · have hshift := freeRank_parent_eq_child_add_one_of_between C he t hgt hbetween
      have hleftOrder : firstLeftRank C hC <
          freeRank P (Tree.freeEmbedding C e t) :=
        (freeRank_lt_iff P _ _).2 hgt
      change (freeRank P (Tree.freeEmbedding C e t)).val =
        (freeRank C t).val + 1 at hshift
      omega
    · have hshift := freeRank_parent_eq_child_add_two_of_right C he t hright
      have hrightOrder : firstRightRank C hC <
          freeRank P (Tree.freeEmbedding C e t) :=
        (freeRank_lt_iff P _ _).2 hright
      have hLR := firstLeftRank_lt_firstRightRank C hC
      change (freeRank P (Tree.freeEmbedding C e t)).val =
        (freeRank C t).val + 2 at hshift
      omega

theorem firstLeft_lt_lowestFree_lt_firstRight_of_rank_zero_ge_two
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : (firstLeftRank C hC).val = 0)
    (hj : 2 ≤ (firstRightRank C hC).val) :
    (firstChord C hC).1 < (lowestFree C (free_card_pos_of_even C hn)).1 ∧
      (lowestFree C (free_card_pos_of_even C hn)).1 < (firstChord C hC).2 := by
  let e := firstChord C hC
  let P := parent C hC
  let t := lowestFree C (free_card_pos_of_even C hn)
  have he : e ∈ C.1 := firstChord_mem C hC
  have htRank : (freeRank C t).val = 0 := by simp [t]
  have htl : t.1 ≠ e.1 := fun h =>
    ((child_free_iff_parent_free C he t.1).1 t.2 |>.2.1) h
  have htr : t.1 ≠ e.2 := fun h =>
    ((child_free_iff_parent_free C he t.1).1 t.2 |>.2.2) h
  have hleft : e.1 < t.1 := by
    rcases lt_or_gt_of_ne htl with hlt | hgt
    · have hshift := freeRank_parent_eq_child_of_lt_left C he t hlt
      have horder : freeRank P (Tree.freeEmbedding C e t) <
          firstLeftRank C hC := (freeRank_lt_iff P _ _).2 hlt
      change (freeRank P (Tree.freeEmbedding C e t)).val =
        (freeRank C t).val at hshift
      omega
    · exact hgt
  refine ⟨hleft, ?_⟩
  rcases lt_or_gt_of_ne htr with hbetween | hright
  · exact hbetween
  · have hshift := freeRank_parent_eq_child_add_two_of_right C he t hright
    have horder : firstRightRank C hC <
        freeRank P (Tree.freeEmbedding C e t) :=
      (freeRank_lt_iff P _ _).2 hright
    change (freeRank P (Tree.freeEmbedding C e t)).val =
      (freeRank C t).val + 2 at hshift
    omega

theorem lowestFree_parent_rank_one_of_rank_zero_ge_two
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : (firstLeftRank C hC).val = 0)
    (hj : 2 ≤ (firstRightRank C hC).val) :
    (freeRank (parent C hC)
      (Tree.freeEmbedding C (firstChord C hC)
        (lowestFree C (free_card_pos_of_even C hn)))).val = 1 := by
  have hbetween := firstLeft_lt_lowestFree_lt_firstRight_of_rank_zero_ge_two
    C hC hn hi hj
  have hshift := freeRank_parent_eq_child_add_one_of_between C
    (firstChord_mem C hC) (lowestFree C (free_card_pos_of_even C hn))
    hbetween.1 hbetween.2
  have htRank : (freeRank C (lowestFree C (free_card_pos_of_even C hn))).val = 0 := by
    simp
  simpa [parent] using hshift

theorem firstRight_lt_childFree_of_special_ranks
    (C : CanonicalMatching n) (hC : C.1.Nonempty)
    (hi : (firstLeftRank C hC).val = 0)
    (hj : (firstRightRank C hC).val = 1) (x : C.free) :
    (firstChord C hC).2 < x.1 := by
  let e := firstChord C hC
  let P := parent C hC
  have he : e ∈ C.1 := firstChord_mem C hC
  have hxl : x.1 ≠ e.1 := fun h =>
    ((child_free_iff_parent_free C he x.1).1 x.2 |>.2.1) h
  have hxr : x.1 ≠ e.2 := fun h =>
    ((child_free_iff_parent_free C he x.1).1 x.2 |>.2.2) h
  rcases lt_or_gt_of_ne hxl with hleft | hafterLeft
  · have horder : freeRank P (Tree.freeEmbedding C e x) <
        firstLeftRank C hC := (freeRank_lt_iff P _ _).2 hleft
    omega
  · rcases lt_or_gt_of_ne hxr with hbetween | hright
    · have hleftOrder : firstLeftRank C hC <
          freeRank P (Tree.freeEmbedding C e x) :=
        (freeRank_lt_iff P _ _).2 hafterLeft
      have hrightOrder : freeRank P (Tree.freeEmbedding C e x) <
          firstRightRank C hC :=
        (freeRank_lt_iff P _ _).2 hbetween
      omega
    · exact hright

/-- BRGC coordinates in descending free-point rank, so coordinate zero is the
last list entry and the highest rank is the closing coordinate. -/
noncomputable def rankCoords (C : CanonicalMatching n) : List C.free :=
  (List.finRange C.free.card).reverse.map (freeAt C)

noncomputable def rankGrayMasks (C : CanonicalMatching n) :
    List (Finset C.free) := Gray.grayList (rankCoords C)

theorem rankCoords_nodup (C : CanonicalMatching n) :
    (rankCoords C).Nodup := by
  have hnd : (List.finRange C.free.card).reverse.Nodup :=
    List.nodup_reverse.mpr (List.nodup_finRange C.free.card)
  rw [rankCoords, List.nodup_map_iff_inj_on hnd]
  intro i _ j _ h
  exact (C.free.orderIsoOfFin rfl).injective h

theorem rankCoords_toFinset (C : CanonicalMatching n) :
    (rankCoords C).toFinset = C.free.attach := by
  ext x
  constructor
  · intro _
    exact Finset.mem_attach C.free x
  · intro _
    obtain ⟨i, rfl⟩ := (C.free.orderIsoOfFin rfl).surjective x
    simp [rankCoords, freeAt]

theorem rankCoords_ne_nil (C : CanonicalMatching n) (h : 0 < C.free.card) :
    rankCoords C ≠ [] := by
  intro hnil
  have hmem : lowestFree C h ∈ (rankCoords C).toFinset := by
    rw [rankCoords_toFinset]
    exact Finset.mem_attach _ _
  rw [hnil] at hmem
  simp at hmem

theorem finRange_head_val {m : Nat} (h : 0 < m) :
    ((List.finRange m).head (by
      intro hm
      have : m = 0 := by simpa using hm
      omega)).val = 0 := by
  cases m with
  | zero => omega
  | succ k => simp [List.finRange_succ]

theorem rankCoords_getLast (C : CanonicalMatching n) (h : 0 < C.free.card) :
    (rankCoords C).getLast (rankCoords_ne_nil C h) = lowestFree C h := by
  simp [rankCoords, lowestFree, freeAt]
  apply Fin.ext
  exact finRange_head_val h

theorem rankCoords_dropLast_append_lowest (C : CanonicalMatching n)
    (h : 0 < C.free.card) :
    (rankCoords C).dropLast ++ [lowestFree C h] = rankCoords C := by
  rw [← rankCoords_getLast C h]
  exact List.dropLast_append_getLast (rankCoords_ne_nil C h)

theorem rankCoords_dropLast_ne_nil (C : CanonicalMatching n)
    (h : 2 ≤ C.free.card) : (rankCoords C).dropLast ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp [rankCoords] at hlen
  omega

theorem finRange_tail_head_val {m : Nat} (h : 2 ≤ m) :
    ((List.finRange m).tail.head (by
      intro hm
      have hlen := congrArg List.length hm
      simp at hlen
      omega)).val = 1 := by
  rcases m with _ | _ | k
  · omega
  · omega
  · simp [List.finRange_succ]

theorem rankCoords_dropLast_getLast (C : CanonicalMatching n)
    (h : 2 ≤ C.free.card) :
    (rankCoords C).dropLast.getLast (rankCoords_dropLast_ne_nil C h) =
      secondFree C h := by
  simp [rankCoords, secondFree, freeAt]

theorem rankCoords_two_low_decomposition (C : CanonicalMatching n)
    (h : 2 ≤ C.free.card) :
    (rankCoords C).dropLast.dropLast ++ [secondFree C h, lowestFree C (by omega)] =
      rankCoords C := by
  calc
    (rankCoords C).dropLast.dropLast ++ [secondFree C h, lowestFree C (by omega)] =
        ((rankCoords C).dropLast.dropLast ++ [secondFree C h]) ++
          [lowestFree C (by omega)] := by simp [List.append_assoc]
    _ = (rankCoords C).dropLast ++ [lowestFree C (by omega)] := by
      rw [← rankCoords_dropLast_getLast C h]
      rw [List.dropLast_append_getLast (rankCoords_dropLast_ne_nil C h)]
    _ = rankCoords C := rankCoords_dropLast_append_lowest C (by omega)

theorem finRange_getLast_val {m : Nat} (h : 0 < m) :
    ((List.finRange m).getLast (by
      intro hm
      have : m = 0 := by
        have hlen := congrArg List.length hm
        simpa using hlen
      omega)).val = m - 1 := by
  rw [List.getLast_eq_getElem]
  simp

theorem rankCoords_head (C : CanonicalMatching n) (h : 0 < C.free.card) :
    (rankCoords C).head (rankCoords_ne_nil C h) = highestFree C h := by
  simp [rankCoords, highestFree, freeAt]
  apply Fin.ext
  exact finRange_getLast_val h

theorem rankCoords_highest_cons_tail (C : CanonicalMatching n)
    (h : 0 < C.free.card) :
    highestFree C h :: (rankCoords C).tail = rankCoords C := by
  rw [← rankCoords_head C h]
  exact List.cons_head_tail (rankCoords_ne_nil C h)

theorem coordinateZero_rankGray_consecutive (C : CanonicalMatching n)
    (h : 0 < C.free.card) (H : Finset C.free)
    (hH : H ⊆ (rankCoords C).dropLast.toFinset) :
    Gray.Consecutive (rankGrayMasks C) H (insert (lowestFree C h) H) := by
  have hdecomp := rankCoords_dropLast_append_lowest C h
  have hnd : ((rankCoords C).dropLast ++ [lowestFree C h]).Nodup := by
    rw [hdecomp]
    exact rankCoords_nodup C
  have hc := Gray.coordinateZero_consecutive (rankCoords C).dropLast
    (lowestFree C h) hnd H hH
  rw [hdecomp] at hc
  exact hc

theorem coordinateOne_rankGray_consecutive (C : CanonicalMatching n)
    (h : 2 ≤ C.free.card) (H : Finset C.free)
    (hH : H ⊆ (rankCoords C).dropLast.dropLast.toFinset) :
    Gray.Consecutive (rankGrayMasks C)
      (insert (lowestFree C (by omega)) H)
      (insert (secondFree C h) (insert (lowestFree C (by omega)) H)) := by
  have hdecomp := rankCoords_two_low_decomposition C h
  have hnd : ((rankCoords C).dropLast.dropLast ++
      [secondFree C h, lowestFree C (by omega)]).Nodup := by
    rw [hdecomp]
    exact rankCoords_nodup C
  have hc := Gray.coordinateOne_consecutive (rankCoords C).dropLast.dropLast
    (secondFree C h) (lowestFree C (by omega)) hnd H hH
  rw [hdecomp] at hc
  exact hc

theorem rankGray_closing_flip (C : CanonicalMatching n)
    (h : 0 < C.free.card) :
    Cube.flipAdj ({highestFree C h} : Finset C.free) ∅ := by
  have hdecomp := rankCoords_highest_cons_tail C h
  have hnd : (highestFree C h :: (rankCoords C).tail).Nodup := by
    rw [hdecomp]
    exact rankCoords_nodup C
  exact Gray.grayList_closing_flip (highestFree C h) (rankCoords C).tail hnd

theorem freeRank_injective (C : CanonicalMatching n) :
    Function.Injective (freeRank C) := (C.free.orderIsoOfFin rfl).symm.injective

theorem eq_of_freeRank_val_eq (C : CanonicalMatching n) (x y : C.free)
    (h : (freeRank C x).val = (freeRank C y).val) : x = y := by
  apply freeRank_injective C
  exact Fin.ext h

theorem firstLeft_eq_lowest_of_rank_zero
    (C : CanonicalMatching n) (hC : C.1.Nonempty)
    (hi : (firstLeftRank C hC).val = 0) :
    firstLeft C hC = lowestFree (parent C hC) (by
      rw [parent_free_card C hC]
      omega) := by
  apply eq_of_freeRank_val_eq (parent C hC)
  have hlo := freeRank_lowestFree (parent C hC) (by
    rw [parent_free_card C hC]
    omega)
  change (freeRank (parent C hC) (firstLeft C hC)).val = _
  rw [show (freeRank (parent C hC) (firstLeft C hC)).val = 0 from hi]
  simp

theorem firstRight_eq_second_of_rank_one
    (C : CanonicalMatching n) (hC : C.1.Nonempty)
    (hj : (firstRightRank C hC).val = 1) :
    firstRight C hC = secondFree (parent C hC) (by
      have hlt := firstLeftRank_lt_firstRightRank C hC
      omega) := by
  apply eq_of_freeRank_val_eq (parent C hC)
  change (freeRank (parent C hC) (firstRight C hC)).val = _
  rw [show (freeRank (parent C hC) (firstRight C hC)).val = 1 from hj]
  simp

theorem lift_lowest_eq_parent_lowest_of_leftRank_pos
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : 0 < (firstLeftRank C hC).val) :
    Tree.freeEmbedding C (firstChord C hC)
        (lowestFree C (free_card_pos_of_even C hn)) =
      lowestFree (parent C hC) (by
        rw [parent_free_card C hC]
        omega) := by
  apply eq_of_freeRank_val_eq
  have hlt := lowestFree_lt_firstLeft_of_leftRank_pos C hC hn hi
  have hshift := freeRank_parent_eq_child_of_lt_left C
    (firstChord_mem C hC) (lowestFree C (free_card_pos_of_even C hn)) hlt
  simpa [parent] using hshift

theorem lift_lowest_eq_parent_second_of_rank_zero_ge_two
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : (firstLeftRank C hC).val = 0)
    (hj : 2 ≤ (firstRightRank C hC).val) :
    Tree.freeEmbedding C (firstChord C hC)
        (lowestFree C (free_card_pos_of_even C hn)) =
      secondFree (parent C hC) (by
        rw [parent_free_card C hC]
        omega) := by
  apply eq_of_freeRank_val_eq (parent C hC)
  have h := lowestFree_parent_rank_one_of_rank_zero_ge_two C hC hn hi hj
  change (freeRank (parent C hC)
    (Tree.freeEmbedding C (firstChord C hC)
      (lowestFree C (free_card_pos_of_even C hn)))).val = _
  rw [h]
  simp

theorem lift_highest_eq_parent_highest_of_special
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : (firstLeftRank C hC).val = 0)
    (hj : (firstRightRank C hC).val = 1) :
    Tree.freeEmbedding C (firstChord C hC)
        (highestFree C (free_card_pos_of_even C hn)) =
      highestFree (parent C hC) (by
        rw [parent_free_card C hC]
        omega) := by
  apply eq_of_freeRank_val_eq (parent C hC)
  have hright := firstRight_lt_childFree_of_special_ranks C hC hi hj
    (highestFree C (free_card_pos_of_even C hn))
  have hshift := freeRank_parent_eq_child_add_two_of_right C
    (firstChord_mem C hC) (highestFree C (free_card_pos_of_even C hn)) hright
  have hcard := parent_free_card C hC
  change (freeRank (parent C hC)
      (Tree.freeEmbedding C (firstChord C hC)
        (highestFree C (free_card_pos_of_even C hn)))).val =
    (freeRank C (highestFree C (free_card_pos_of_even C hn))).val + 2 at hshift
  have hchild : (freeRank C
      (highestFree C (free_card_pos_of_even C hn))).val = C.free.card - 1 := by
    simp
  have hparent : (freeRank (parent C hC)
      (highestFree (parent C hC) (by
        rw [parent_free_card C hC]
        omega))).val = (parent C hC).free.card - 1 := by
    simp
  omega

theorem mem_rankCoords (C : CanonicalMatching n) (x : C.free) :
    x ∈ rankCoords C := by
  rw [← List.mem_toFinset, rankCoords_toFinset]
  exact Finset.mem_attach _ _

theorem mem_rankCoords_dropLast_of_ne_lowest (C : CanonicalMatching n)
    (h : 0 < C.free.card) (x : C.free) (hx : x ≠ lowestFree C h) :
    x ∈ (rankCoords C).dropLast := by
  apply List.mem_dropLast_of_mem_of_ne_getLast (mem_rankCoords C x)
  simpa [rankCoords_getLast C h] using hx

theorem mem_rankCoords_dropLast_dropLast_of_ne_lowest_second
    (C : CanonicalMatching n) (h : 2 ≤ C.free.card) (x : C.free)
    (hx0 : x ≠ lowestFree C (by omega)) (hx1 : x ≠ secondFree C h) :
    x ∈ (rankCoords C).dropLast.dropLast := by
  have hm := mem_rankCoords_dropLast_of_ne_lowest C (by omega) x hx0
  exact List.mem_dropLast_of_mem_of_ne_getLast hm (by
    simpa [rankCoords_dropLast_getLast C h] using hx1)

theorem parentMask_empty_eq_pair (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) :
    Tree.parentMask C he (∅ : Finset C.free) =
      {⟨e.1, Tree.erased_left_free C he⟩,
        ⟨e.2, Tree.erased_right_free C he⟩} := by
  ext x
  simp [Tree.parentMask, Tree.liftMask]

theorem parentMask_insert_eq (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) (A : Finset C.free) (x : C.free) :
    Tree.parentMask C he (insert x A) =
      insert (Tree.freeEmbedding C e x) (Tree.parentMask C he A) := by
  ext y
  simp [Tree.parentMask, Tree.liftMask, Tree.freeEmbedding]
  tauto

inductive AmbientPortKey (n : Nat)
  | coordinate (q : Fin n) (lower : Finset (Fin n))
  | closing
  deriving DecidableEq

def ambientMask {Q : CanonicalMatching n} (A : Finset Q.free) :
    Finset (Fin n) := A.image Subtype.val

theorem ambientMask_parentMask_empty (C : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ C.1) :
    ambientMask (Tree.parentMask C he (∅ : Finset C.free)) = chordEnds e := by
  rw [parentMask_empty_eq_pair C he]
  ext x
  simp [ambientMask, chordEnds, Tree.erased_left_free, Tree.erased_right_free]

/-- A key denotes an actual distinguished occurrence of a rank Gray edge.
The coordinate case records the lower mask and the flipped ambient point;
the closing case records the distinguished closing copy. -/
def RealizesPortKey (Q : CanonicalMatching n) (h : 0 < Q.free.card)
    (key : AmbientPortKey n) (A B : Finset Q.free) : Prop :=
  match key with
  | .coordinate q lower =>
      ∃ x : Q.free, x.1 = q ∧
        ((ambientMask A = lower ∧ B = insert x A) ∨
         (ambientMask B = lower ∧ A = insert x B))
  | .closing =>
      (A = ∅ ∧ B = {highestFree Q h}) ∨
      (B = ∅ ∧ A = {highestFree Q h})

theorem coordinatePortKey_unique_of_ne (Q : CanonicalMatching n)
    (h : 0 < Q.free.card) {q r : Fin n} {H K : Finset (Fin n)}
    {A B : Finset Q.free} (hne : A ≠ B)
    (hq : RealizesPortKey Q h (.coordinate q H) A B)
    (hr : RealizesPortKey Q h (.coordinate r K) A B) :
    q = r ∧ H = K := by
  rcases hq with ⟨x, hxq, hx⟩
  rcases hr with ⟨y, hyr, hy⟩
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · have hxy : x = y := by
        have hxA : x ∉ A := by
          intro hxA
          exact hne (by simpa [Finset.insert_eq_self.mpr hxA] using hx.2.symm)
        have hmem : x ∈ insert y A := by rw [← hy.2, hx.2]; simp
        rcases Finset.mem_insert.mp hmem with h | h
        · exact h
        · exact (hxA h).elim
      exact ⟨hxq.symm.trans (congrArg Subtype.val hxy |>.trans hyr),
        hx.1.symm.trans hy.1⟩
    · have hAB : A ⊆ B := by
        rw [hx.2]
        exact Finset.subset_insert _ _
      have hBA : B ⊆ A := by
        rw [hy.2]
        exact Finset.subset_insert _ _
      exact (hne (Finset.Subset.antisymm hAB hBA)).elim
  · rcases hy with hy | hy
    · have hBA : B ⊆ A := by
        rw [hx.2]
        exact Finset.subset_insert _ _
      have hAB : A ⊆ B := by
        rw [hy.2]
        exact Finset.subset_insert _ _
      exact (hne (Finset.Subset.antisymm hAB hBA)).elim
    · have hxy : x = y := by
        have hxB : x ∉ B := by
          intro hxB
          exact hne (by simpa [Finset.insert_eq_self.mpr hxB] using hx.2)
        have hmem : x ∈ insert y B := by rw [← hy.2, hx.2]; simp
        rcases Finset.mem_insert.mp hmem with h | h
        · exact h
        · exact (hxB h).elim
      exact ⟨hxq.symm.trans (congrArg Subtype.val hxy |>.trans hyr),
        hx.1.symm.trans hy.1⟩

theorem firstLeft_ne_lowest_of_rank_pos (C : CanonicalMatching n)
    (hC : C.1.Nonempty) (hi : 0 < (firstLeftRank C hC).val) :
    firstLeft C hC ≠ lowestFree (parent C hC) (by
      rw [parent_free_card C hC]
      omega) := by
  intro h
  have hr : (firstLeftRank C hC).val = 0 := by
    change (freeRank (parent C hC) (firstLeft C hC)).val = 0
    rw [h]
    simp
  omega

theorem firstRight_ne_lowest_of_leftRank_pos (C : CanonicalMatching n)
    (hC : C.1.Nonempty) (hi : 0 < (firstLeftRank C hC).val) :
    firstRight C hC ≠ lowestFree (parent C hC) (by
      rw [parent_free_card C hC]
      omega) := by
  intro h
  have hr : (firstRightRank C hC).val = 0 := by
    change (freeRank (parent C hC) (firstRight C hC)).val = 0
    rw [h]
    simp
  have hLR := firstLeftRank_lt_firstRightRank C hC
  omega

theorem firstRight_ne_lowest_of_rank_ge_two (C : CanonicalMatching n)
    (hC : C.1.Nonempty) (hj : 2 ≤ (firstRightRank C hC).val) :
    firstRight C hC ≠ lowestFree (parent C hC) (by
      rw [parent_free_card C hC]
      omega) := by
  intro h
  have hr : (firstRightRank C hC).val = 0 := by
    change (freeRank (parent C hC) (firstRight C hC)).val = 0
    rw [h]
    simp
  omega

theorem firstRight_ne_second_of_rank_ge_two (C : CanonicalMatching n)
    (hC : C.1.Nonempty) (hj : 2 ≤ (firstRightRank C hC).val) :
    firstRight C hC ≠ secondFree (parent C hC) (by
      rw [parent_free_card C hC]
      omega) := by
  intro h
  have hr : (firstRightRank C hC).val = 1 := by
    change (freeRank (parent C hC) (firstRight C hC)).val = 1
    rw [h]
    simp
  omega

/-- An edge of the cyclic reflected Gray code, including its closing edge. -/
def OnRankGrayCycle (C : CanonicalMatching n) (h : 0 < C.free.card)
    (A B : Finset C.free) : Prop :=
  Gray.Consecutive (rankGrayMasks C) A B ∨
    (A = ∅ ∧ B = {highestFree C h}) ∨
    (B = ∅ ∧ A = {highestFree C h})

/-- A literal parent-child diamond whose horizontal edges are fixed edges of
the two cyclic reflected Gray codes. -/
structure JoiningDiamond (C : CanonicalMatching n) (hC : C.1.Nonempty)
    (hn : Even n) where
  parentLower : Finset (parent C hC).free
  parentUpper : Finset (parent C hC).free
  childLower : Finset C.free
  childUpper : Finset C.free
  parentEdge : OnRankGrayCycle (parent C hC)
    (free_card_pos_of_even (parent C hC) hn) parentLower parentUpper
  childEdge : OnRankGrayCycle C (free_card_pos_of_even C hn) childLower childUpper
  parentKey : AmbientPortKey n
  childKey : AmbientPortKey n
  parentKey_realizes : RealizesPortKey (parent C hC)
    (free_card_pos_of_even (parent C hC) hn) parentKey parentLower parentUpper
  childKey_realizes : RealizesPortKey C (free_card_pos_of_even C hn)
    childKey childLower childUpper
  parentCoordinate_edge : ∀ q lower, parentKey = .coordinate q lower →
    Gray.Consecutive (rankGrayMasks (parent C hC)) parentLower parentUpper
  parentClosing_edge : parentKey = .closing →
    (parentLower = ∅ ∧ parentUpper =
      {highestFree (parent C hC) (free_card_pos_of_even (parent C hC) hn)}) ∨
    (parentUpper = ∅ ∧ parentLower =
      {highestFree (parent C hC) (free_card_pos_of_even (parent C hC) hn)})
  childCoordinate_edge : ∀ q lower, childKey = .coordinate q lower →
    Gray.Consecutive (rankGrayMasks C) childLower childUpper
  childClosing_edge : childKey = .closing →
    (childLower = ∅ ∧ childUpper =
      {highestFree C (free_card_pos_of_even C hn)}) ∨
    (childUpper = ∅ ∧ childLower =
      {highestFree C (free_card_pos_of_even C hn)})
  crossLower : (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj
    ((parent C hC).decodedNC parentLower) (C.decodedNC childLower)
  crossUpper : (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj
    ((parent C hC).decodedNC parentUpper) (C.decodedNC childUpper)

noncomputable def joiningDiamond_leftRankPos
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : 0 < (firstLeftRank C hC).val) : JoiningDiamond C hC hn := by
  let e := firstChord C hC
  let P := parent C hC
  let t := lowestFree C (free_card_pos_of_even C hn)
  have he : e ∈ C.1 := firstChord_mem C hC
  have hp : 0 < P.free.card := free_card_pos_of_even P hn
  have hc : 0 < C.free.card := free_card_pos_of_even C hn
  have hlift : Tree.freeEmbedding C e t = lowestFree P hp := by
    simpa [e, P, t] using lift_lowest_eq_parent_lowest_of_leftRank_pos C hC hn hi
  let H := Tree.parentMask C he (∅ : Finset C.free)
  have hH : H ⊆ (rankCoords P).dropLast.toFinset := by
    intro x hx
    have hpair := parentMask_empty_eq_pair C he
    change x ∈ Tree.parentMask C he (∅ : Finset C.free) at hx
    rw [hpair] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · subst x
      apply List.mem_toFinset.mpr
      exact mem_rankCoords_dropLast_of_ne_lowest P hp (firstLeft C hC)
        (firstLeft_ne_lowest_of_rank_pos C hC hi)
    · subst x
      apply List.mem_toFinset.mpr
      exact mem_rankCoords_dropLast_of_ne_lowest P hp (firstRight C hC)
        (firstRight_ne_lowest_of_leftRank_pos C hC hi)
  have hpEdge0 := coordinateZero_rankGray_consecutive P hp H hH
  have hpMask : Tree.parentMask C he ({t} : Finset C.free) =
      insert (lowestFree P hp) H := by
    have hm := parentMask_insert_eq C he (∅ : Finset C.free) t
    simpa [H, hlift] using hm
  have hpEdge : Gray.Consecutive (rankGrayMasks P)
      (Tree.parentMask C he ∅) (Tree.parentMask C he {t}) := by
    change Gray.Consecutive (rankGrayMasks P) H _
    rw [hpMask]
    exact hpEdge0
  have hcEdge0 := coordinateZero_rankGray_consecutive C hc
    (∅ : Finset C.free) (by simp)
  have hcEdge : Gray.Consecutive (rankGrayMasks C) (∅ : Finset C.free) {t} := by
    simpa [t] using hcEdge0
  refine
    { parentLower := Tree.parentMask C he ∅
      parentUpper := Tree.parentMask C he {t}
      childLower := ∅
      childUpper := {t}
      parentEdge := Or.inl (by simpa [P] using hpEdge)
      childEdge := Or.inl hcEdge
      parentKey := .coordinate (lowestFree P hp).1 (chordEnds e)
      childKey := .coordinate t.1 ∅
      parentKey_realizes := by
        refine ⟨lowestFree P hp, rfl, Or.inl ⟨?_, ?_⟩⟩
        · simpa [P, e] using ambientMask_parentMask_empty C he
        · simpa [H] using hpMask
      childKey_realizes := by
        refine ⟨t, rfl, Or.inl ⟨?_, ?_⟩⟩
        · simp [ambientMask]
        · simp
      parentCoordinate_edge := by intro _ _ _; simpa [P] using hpEdge
      parentClosing_edge := by intro h; contradiction
      childCoordinate_edge := by intro _ _ _; exact hcEdge
      childClosing_edge := by intro h; contradiction
      crossLower := ?_
      crossUpper := ?_ }
  · exact NC.Adj_symm (by
      simpa [P, e, parent] using Tree.decodedNC_child_adj_parentMask C he
        (∅ : Finset C.free))
  · exact NC.Adj_symm (by
      simpa [P, e, parent] using Tree.decodedNC_child_adj_parentMask C he
        ({t} : Finset C.free))

noncomputable def joiningDiamond_leftZero_rightGeTwo
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : (firstLeftRank C hC).val = 0)
    (hj : 2 ≤ (firstRightRank C hC).val) : JoiningDiamond C hC hn := by
  let e := firstChord C hC
  let P := parent C hC
  let t := lowestFree C (free_card_pos_of_even C hn)
  have he : e ∈ C.1 := firstChord_mem C hC
  have hp : 0 < P.free.card := free_card_pos_of_even P hn
  have hp2 : 2 ≤ P.free.card := by
    rw [parent_free_card C hC]
    omega
  have hc : 0 < C.free.card := free_card_pos_of_even C hn
  have hlow : firstLeft C hC = lowestFree P hp := by
    simpa [P] using firstLeft_eq_lowest_of_rank_zero C hC hi
  have hsecond : Tree.freeEmbedding C e t = secondFree P hp2 := by
    simpa [e, P, t] using
      lift_lowest_eq_parent_second_of_rank_zero_ge_two C hC hn hi hj
  let H : Finset P.free := {firstRight C hC}
  have hH : H ⊆ (rankCoords P).dropLast.dropLast.toFinset := by
    intro x hx
    have hx' : x = firstRight C hC := by simpa [H] using hx
    subst x
    apply List.mem_toFinset.mpr
    exact mem_rankCoords_dropLast_dropLast_of_ne_lowest_second P hp2
      (firstRight C hC)
      (firstRight_ne_lowest_of_rank_ge_two C hC hj)
      (firstRight_ne_second_of_rank_ge_two C hC hj)
  have hpEdge0 := coordinateOne_rankGray_consecutive P hp2 H hH
  have hpLower : Tree.parentMask C he (∅ : Finset C.free) =
      insert (lowestFree P hp) H := by
    rw [parentMask_empty_eq_pair C he]
    ext x
    simp only [H, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hx | hx)
      · have hx' : x = lowestFree P hp :=
          (Subtype.ext (congrArg Subtype.val hx)).trans hlow
        rw [hx']
        exact Finset.mem_insert_self _ _
      · have hx' : x = firstRight C hC :=
          Subtype.ext (congrArg Subtype.val hx)
        rw [hx']
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · intro hx
      rcases Finset.mem_insert.mp hx with hx' | hx'
      · left
        exact Subtype.ext (congrArg Subtype.val (hx'.trans hlow.symm))
      · right
        exact Subtype.ext (congrArg Subtype.val (Finset.mem_singleton.mp hx'))
  have hpUpper : Tree.parentMask C he ({t} : Finset C.free) =
      insert (secondFree P hp2) (insert (lowestFree P hp) H) := by
    have hm := parentMask_insert_eq C he (∅ : Finset C.free) t
    rw [hsecond, hpLower] at hm
    simpa using hm
  have hpEdge : Gray.Consecutive (rankGrayMasks P)
      (Tree.parentMask C he ∅) (Tree.parentMask C he {t}) := by
    rw [hpLower, hpUpper]
    exact hpEdge0
  have hcEdge0 := coordinateZero_rankGray_consecutive C hc
    (∅ : Finset C.free) (by simp)
  have hcEdge : Gray.Consecutive (rankGrayMasks C) (∅ : Finset C.free) {t} := by
    simpa [t] using hcEdge0
  refine
    { parentLower := Tree.parentMask C he ∅
      parentUpper := Tree.parentMask C he {t}
      childLower := ∅
      childUpper := {t}
      parentEdge := Or.inl (by simpa [P] using hpEdge)
      childEdge := Or.inl hcEdge
      parentKey := .coordinate (secondFree P hp2).1 (chordEnds e)
      childKey := .coordinate t.1 ∅
      parentKey_realizes := by
        refine ⟨secondFree P hp2, rfl, Or.inl ⟨?_, ?_⟩⟩
        · simpa [P, e] using ambientMask_parentMask_empty C he
        · rw [hpLower]
          simpa using hpUpper
      childKey_realizes := by
        refine ⟨t, rfl, Or.inl ⟨?_, ?_⟩⟩
        · simp [ambientMask]
        · simp
      parentCoordinate_edge := by intro _ _ _; simpa [P] using hpEdge
      parentClosing_edge := by intro h; contradiction
      childCoordinate_edge := by intro _ _ _; exact hcEdge
      childClosing_edge := by intro h; contradiction
      crossLower := ?_
      crossUpper := ?_ }
  · exact NC.Adj_symm (by
      simpa [P, e, parent] using Tree.decodedNC_child_adj_parentMask C he
        (∅ : Finset C.free))
  · exact NC.Adj_symm (by
      simpa [P, e, parent] using Tree.decodedNC_child_adj_parentMask C he
        ({t} : Finset C.free))

noncomputable def joiningDiamond_special
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : (firstLeftRank C hC).val = 0)
    (hj : (firstRightRank C hC).val = 1) : JoiningDiamond C hC hn := by
  let e := firstChord C hC
  let P := parent C hC
  let t := highestFree C (free_card_pos_of_even C hn)
  have he : e ∈ C.1 := firstChord_mem C hC
  have hp : 0 < P.free.card := free_card_pos_of_even P hn
  have hc : 0 < C.free.card := free_card_pos_of_even C hn
  have hright : e.2 < t.1 := by
    simpa [e, t] using firstRight_lt_childFree_of_special_ranks C hC hi hj t
  have hlift : Tree.freeEmbedding C e t = highestFree P hp := by
    simpa [e, P, t] using lift_highest_eq_parent_highest_of_special C hC hn hi hj
  have hA : ∀ q ∈ ({t} : Finset C.free), e.2 < q.1 := by
    intro q hq
    have hqt : q = t := Finset.mem_singleton.mp hq
    simpa [hqt] using hright
  refine
    { parentLower := ∅
      parentUpper := {highestFree P hp}
      childLower := ∅
      childUpper := {t}
      parentEdge := Or.inr (Or.inl ⟨rfl, rfl⟩)
      childEdge := Or.inr (Or.inl ⟨rfl, by simp [t]⟩)
      parentKey := .closing
      childKey := .closing
      parentKey_realizes := Or.inl ⟨rfl, rfl⟩
      childKey_realizes := Or.inl ⟨rfl, by simp [t]⟩
      parentCoordinate_edge := by intro _ _ h; contradiction
      parentClosing_edge := fun _ ↦ Or.inl ⟨rfl, rfl⟩
      childCoordinate_edge := by intro _ _ h; contradiction
      childClosing_edge := fun _ ↦ Or.inl ⟨rfl, by simp [t]⟩
      crossLower := ?_
      crossUpper := ?_ }
  · simpa [P, e, parent] using Tree.decodedNC_empty_parent_adj_child C he
  · have hcross := Tree.decodedNC_rightMask_parent_adj_child C he
      ({t} : Finset C.free) hA
    simpa [P, e, parent, Tree.liftMask, hlift] using hcross

theorem joiningDiamond_nonempty
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n) :
    Nonempty (JoiningDiamond C hC hn) := by
  rcases firstChord_rank_cases C hC with hi | hrest
  · exact ⟨joiningDiamond_leftRankPos C hC hn hi⟩
  · rcases hrest with hmid | hspecial
    · exact ⟨joiningDiamond_leftZero_rightGeTwo C hC hn hmid.1 hmid.2⟩
    · exact ⟨joiningDiamond_special C hC hn hspecial.1 hspecial.2⟩

noncomputable def joiningDiamond
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n) :
    JoiningDiamond C hC hn :=
  if hi : 0 < (firstLeftRank C hC).val then
    joiningDiamond_leftRankPos C hC hn hi
  else if hj : 2 ≤ (firstRightRank C hC).val then
    joiningDiamond_leftZero_rightGeTwo C hC hn (by omega) hj
  else
    joiningDiamond_special C hC hn (by omega)
      (by
        have hlt := firstLeftRank_lt_firstRightRank C hC
        omega)

theorem joiningDiamond_eq_leftRankPos
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : 0 < (firstLeftRank C hC).val) :
    joiningDiamond C hC hn = joiningDiamond_leftRankPos C hC hn hi := by
  simp [joiningDiamond, hi]

theorem joiningDiamond_eq_leftZero_rightGeTwo
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : (firstLeftRank C hC).val = 0)
    (hj : 2 ≤ (firstRightRank C hC).val) :
    joiningDiamond C hC hn =
      joiningDiamond_leftZero_rightGeTwo C hC hn hi hj := by
  simp [joiningDiamond, hi, hj]

theorem joiningDiamond_eq_special
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n)
    (hi : (firstLeftRank C hC).val = 0)
    (hj : (firstRightRank C hC).val = 1) :
    joiningDiamond C hC hn = joiningDiamond_special C hC hn hi hj := by
  simp [joiningDiamond, hi, hj]

theorem firstChord_lex_le (C : CanonicalMatching n) (hC : C.1.Nonempty)
    {f : Fin n × Fin n} (hf : f ∈ C.1) :
    toLex (firstChord C hC) ≤ toLex f := by
  have hfmap : toLex f ∈ C.1.map toLex.toEmbedding :=
    Finset.mem_map.mpr ⟨f, hf, rfl⟩
  have hle := Finset.min'_le (C.1.map toLex.toEmbedding) (toLex f) hfmap
  simpa [firstChord] using hle

structure ChildData (Q : CanonicalMatching n) where
  child : CanonicalMatching n
  child_nonempty : child.1.Nonempty
  parent_eq : parent child child_nonempty = Q

namespace ChildData

noncomputable def chord {Q : CanonicalMatching n} (d : ChildData Q) :
    Fin n × Fin n := firstChord d.child d.child_nonempty

theorem chord_mem {Q : CanonicalMatching n} (d : ChildData Q) :
    d.chord ∈ d.child.1 := firstChord_mem d.child d.child_nonempty

theorem child_val_eq_insert {Q : CanonicalMatching n} (d : ChildData Q) :
    d.child.1 = insert d.chord Q.1 := by
  calc
    d.child.1 = insert d.chord (d.child.1.erase d.chord) :=
      (Finset.insert_erase d.chord_mem).symm
    _ = insert d.chord Q.1 := by
      have hp := congrArg Subtype.val d.parent_eq
      exact congrArg (insert d.chord) hp

theorem child_eq_of_chord_eq {Q : CanonicalMatching n} (d₁ d₂ : ChildData Q)
    (h : d₁.chord = d₂.chord) : d₁.child = d₂.child := by
  apply Subtype.ext
  rw [d₁.child_val_eq_insert, d₂.child_val_eq_insert, h]

theorem ext_child {Q : CanonicalMatching n} (d₁ d₂ : ChildData Q)
    (h : d₁.child = d₂.child) : d₁ = d₂ := by
  cases d₁
  cases d₂
  cases h
  rfl

end ChildData

theorem special_block_has_no_child
    (Q : CanonicalMatching n) (hQ : Q.1.Nonempty)
    (hi : (firstLeftRank Q hQ).val = 0)
    (hj : (firstRightRank Q hQ).val = 1) : ¬ Nonempty (ChildData Q) := by
  rintro ⟨d⟩
  let e := firstChord Q hQ
  let f := d.chord
  have hfD : f ∈ d.child.1 := d.chord_mem
  have hfLeftQ : f.1 ∈ Q.free := by
    have hfree := Tree.erased_left_free d.child hfD
    have hp : Tree.eraseChord d.child f = Q := by
      simpa [parent, f, ChildData.chord] using d.parent_eq
    rw [hp] at hfree
    exact hfree
  have hright : e.2 < f.1 := by
    simpa [e, f] using firstRight_lt_childFree_of_special_ranks Q hQ hi hj
      ⟨f.1, hfLeftQ⟩
  have heQ : e ∈ Q.1 := firstChord_mem Q hQ
  have heD : e ∈ d.child.1 := by
    rw [d.child_val_eq_insert]
    exact Finset.mem_insert_of_mem heQ
  have hfe : toLex f ≤ toLex e := by
    simpa [f, ChildData.chord] using
      firstChord_lex_le d.child d.child_nonempty heD
  have hef : toLex e < toLex f := by
    exact Prod.Lex.left _ _ ((Q.2.1 e heQ).2.trans hright)
  exact (not_lt_of_ge hfe) hef

theorem chord_eq_of_chordEnds_eq {e f : Fin n × Fin n}
    (he : e.1 < e.2) (hf : f.1 < f.2)
    (hends : chordEnds e = chordEnds f) : e = f := by
  have he1 : e.1 = f.1 ∨ e.1 = f.2 := by
    have : e.1 ∈ chordEnds f := by
      rw [← hends]
      simp [chordEnds]
    simpa [chordEnds] using this
  have he2 : e.2 = f.1 ∨ e.2 = f.2 := by
    have : e.2 ∈ chordEnds f := by
      rw [← hends]
      simp [chordEnds]
    simpa [chordEnds] using this
  rcases he1 with h11 | h12
  · rcases he2 with h21 | h22
    · exact (he.ne (h11.trans h21.symm)).elim
    · exact Prod.ext h11 h22
  · rcases he2 with h21 | h22
    · rw [h12, h21] at he
      exact (not_lt_of_ge (le_of_lt hf) he).elim
    · exact (he.ne (h12.trans h22.symm)).elim

noncomputable def incomingPortKey {Q : CanonicalMatching n}
    (d : ChildData Q) : AmbientPortKey n :=
  if hi : 0 < (firstLeftRank d.child d.child_nonempty).val then
    .coordinate (lowestFree (parent d.child d.child_nonempty) (by
      rw [parent_free_card d.child d.child_nonempty]
      omega)).1 (chordEnds d.chord)
  else if hj : 2 ≤ (firstRightRank d.child d.child_nonempty).val then
    .coordinate (secondFree (parent d.child d.child_nonempty) (by
      rw [parent_free_card d.child d.child_nonempty]
      omega)).1 (chordEnds d.chord)
  else .closing

noncomputable def outgoingPortKey (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n) : AmbientPortKey n :=
  if hi : 0 < (firstLeftRank Q hQ).val then
    .coordinate (lowestFree Q (free_card_pos_of_even Q hn)).1 ∅
  else if hj : 2 ≤ (firstRightRank Q hQ).val then
    .coordinate (lowestFree Q (free_card_pos_of_even Q hn)).1 ∅
  else .closing

theorem incomingPortKey_eq_leftRankPos {Q : CanonicalMatching n}
    (d : ChildData Q) (hi : 0 < (firstLeftRank d.child d.child_nonempty).val) :
    incomingPortKey d =
      .coordinate (lowestFree (parent d.child d.child_nonempty) (by
        rw [parent_free_card d.child d.child_nonempty]
        omega)).1 (chordEnds d.chord) := by
  simp [incomingPortKey, hi]

theorem incomingPortKey_eq_leftZero_rightGeTwo {Q : CanonicalMatching n}
    (d : ChildData Q) (hi : (firstLeftRank d.child d.child_nonempty).val = 0)
    (hj : 2 ≤ (firstRightRank d.child d.child_nonempty).val) :
    incomingPortKey d =
      .coordinate (secondFree (parent d.child d.child_nonempty) (by
        rw [parent_free_card d.child d.child_nonempty]
        omega)).1 (chordEnds d.chord) := by
  simp [incomingPortKey, hi, hj]

theorem incomingPortKey_eq_special {Q : CanonicalMatching n}
    (d : ChildData Q) (hi : (firstLeftRank d.child d.child_nonempty).val = 0)
    (hj : (firstRightRank d.child d.child_nonempty).val = 1) :
    incomingPortKey d = .closing := by
  simp [incomingPortKey, hi, hj]

theorem ChildData.eq_of_coordinate_keys {Q : CanonicalMatching n}
    (d₁ d₂ : ChildData Q) {q₁ q₂ : Fin n}
    (h₁ : incomingPortKey d₁ = .coordinate q₁ (chordEnds d₁.chord))
    (h₂ : incomingPortKey d₂ = .coordinate q₂ (chordEnds d₂.chord))
    (hkey : incomingPortKey d₁ = incomingPortKey d₂) : d₁ = d₂ := by
  have hcoord : AmbientPortKey.coordinate q₁ (chordEnds d₁.chord) =
      AmbientPortKey.coordinate q₂ (chordEnds d₂.chord) := h₁.symm.trans (hkey.trans h₂)
  have hends : chordEnds d₁.chord = chordEnds d₂.chord := by
    exact (AmbientPortKey.coordinate.injEq _ _ _ _).mp hcoord |>.2
  have hchord : d₁.chord = d₂.chord := chord_eq_of_chordEnds_eq
    (d₁.child.2.1 d₁.chord d₁.chord_mem |>.2)
    (d₂.child.2.1 d₂.chord d₂.chord_mem |>.2) hends
  exact d₁.ext_child d₂ (d₁.child_eq_of_chord_eq d₂ hchord)

theorem lowestFree_val_congr (P R : CanonicalMatching n) (hPR : P = R)
    (hP : 0 < P.free.card) (hR : 0 < R.free.card) :
    (lowestFree P hP).1 = (lowestFree R hR).1 := by
  subst R
  rfl

theorem secondFree_val_congr (P R : CanonicalMatching n) (hPR : P = R)
    (hP : 2 ≤ P.free.card) (hR : 2 ≤ R.free.card) :
    (secondFree P hP).1 = (secondFree R hR).1 := by
  subst R
  rfl

theorem ChildData.special_chord_eq {Q : CanonicalMatching n}
    (d₁ d₂ : ChildData Q)
    (hi₁ : (firstLeftRank d₁.child d₁.child_nonempty).val = 0)
    (hj₁ : (firstRightRank d₁.child d₁.child_nonempty).val = 1)
    (hi₂ : (firstLeftRank d₂.child d₂.child_nonempty).val = 0)
    (hj₂ : (firstRightRank d₂.child d₂.child_nonempty).val = 1) :
    d₁.chord = d₂.chord := by
  apply Prod.ext
  · have h₁ := congrArg Subtype.val
      (firstLeft_eq_lowest_of_rank_zero d₁.child d₁.child_nonempty hi₁)
    have h₂ := congrArg Subtype.val
      (firstLeft_eq_lowest_of_rank_zero d₂.child d₂.child_nonempty hi₂)
    have hp : parent d₁.child d₁.child_nonempty =
        parent d₂.child d₂.child_nonempty := d₁.parent_eq.trans d₂.parent_eq.symm
    exact h₁.trans ((lowestFree_val_congr _ _ hp _ _).trans h₂.symm)
  · have h₁ := congrArg Subtype.val
      (firstRight_eq_second_of_rank_one d₁.child d₁.child_nonempty hj₁)
    have h₂ := congrArg Subtype.val
      (firstRight_eq_second_of_rank_one d₂.child d₂.child_nonempty hj₂)
    have hp : parent d₁.child d₁.child_nonempty =
        parent d₂.child d₂.child_nonempty := d₁.parent_eq.trans d₂.parent_eq.symm
    exact h₁.trans ((secondFree_val_congr _ _ hp _ _).trans h₂.symm)

theorem incomingPortKey_injective (Q : CanonicalMatching n) :
    Function.Injective (incomingPortKey : ChildData Q → AmbientPortKey n) := by
  intro d₁ d₂ hkey
  rcases firstChord_rank_cases d₁.child d₁.child_nonempty with hi₁ | hrest₁
  · have hk₁ := incomingPortKey_eq_leftRankPos d₁ hi₁
    rcases firstChord_rank_cases d₂.child d₂.child_nonempty with hi₂ | hrest₂
    · exact d₁.eq_of_coordinate_keys d₂ hk₁
        (incomingPortKey_eq_leftRankPos d₂ hi₂) hkey
    · rcases hrest₂ with hmid₂ | hspecial₂
      · exact d₁.eq_of_coordinate_keys d₂ hk₁
          (incomingPortKey_eq_leftZero_rightGeTwo d₂ hmid₂.1 hmid₂.2) hkey
      · have hk₂ := incomingPortKey_eq_special d₂ hspecial₂.1 hspecial₂.2
        rw [hk₁, hk₂] at hkey
        contradiction
  · rcases hrest₁ with hmid₁ | hspecial₁
    · have hk₁ := incomingPortKey_eq_leftZero_rightGeTwo d₁ hmid₁.1 hmid₁.2
      rcases firstChord_rank_cases d₂.child d₂.child_nonempty with hi₂ | hrest₂
      · exact d₁.eq_of_coordinate_keys d₂ hk₁
          (incomingPortKey_eq_leftRankPos d₂ hi₂) hkey
      · rcases hrest₂ with hmid₂ | hspecial₂
        · exact d₁.eq_of_coordinate_keys d₂ hk₁
            (incomingPortKey_eq_leftZero_rightGeTwo d₂ hmid₂.1 hmid₂.2) hkey
        · have hk₂ := incomingPortKey_eq_special d₂ hspecial₂.1 hspecial₂.2
          rw [hk₁, hk₂] at hkey
          contradiction
    · have hk₁ := incomingPortKey_eq_special d₁ hspecial₁.1 hspecial₁.2
      rcases firstChord_rank_cases d₂.child d₂.child_nonempty with hi₂ | hrest₂
      · have hk₂ := incomingPortKey_eq_leftRankPos d₂ hi₂
        rw [hk₁, hk₂] at hkey
        contradiction
      · rcases hrest₂ with hmid₂ | hspecial₂
        · have hk₂ := incomingPortKey_eq_leftZero_rightGeTwo d₂ hmid₂.1 hmid₂.2
          rw [hk₁, hk₂] at hkey
          contradiction
        · exact d₁.ext_child d₂ (d₁.child_eq_of_chord_eq d₂
            (d₁.special_chord_eq d₂ hspecial₁.1 hspecial₁.2
              hspecial₂.1 hspecial₂.2))

theorem outgoingPortKey_eq_leftRankPos (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n)
    (hi : 0 < (firstLeftRank Q hQ).val) :
    outgoingPortKey Q hQ hn =
      .coordinate (lowestFree Q (free_card_pos_of_even Q hn)).1 ∅ := by
  simp [outgoingPortKey, hi]

theorem outgoingPortKey_eq_leftZero_rightGeTwo (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n)
    (hi : (firstLeftRank Q hQ).val = 0)
    (hj : 2 ≤ (firstRightRank Q hQ).val) :
    outgoingPortKey Q hQ hn =
      .coordinate (lowestFree Q (free_card_pos_of_even Q hn)).1 ∅ := by
  simp [outgoingPortKey, hi, hj]

theorem outgoingPortKey_eq_special (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n)
    (hi : (firstLeftRank Q hQ).val = 0)
    (hj : (firstRightRank Q hQ).val = 1) :
    outgoingPortKey Q hQ hn = .closing := by
  simp [outgoingPortKey, hi, hj]

theorem joiningDiamond_parentKey_eq_incoming {Q : CanonicalMatching n}
    (d : ChildData Q) (hn : Even n) :
    (joiningDiamond d.child d.child_nonempty hn).parentKey = incomingPortKey d := by
  rcases firstChord_rank_cases d.child d.child_nonempty with hi | hrest
  · rw [joiningDiamond_eq_leftRankPos d.child d.child_nonempty hn hi,
      incomingPortKey_eq_leftRankPos d hi]
    rfl
  · rcases hrest with hmid | hspecial
    · rw [joiningDiamond_eq_leftZero_rightGeTwo d.child d.child_nonempty hn
        hmid.1 hmid.2,
        incomingPortKey_eq_leftZero_rightGeTwo d hmid.1 hmid.2]
      rfl
    · rw [joiningDiamond_eq_special d.child d.child_nonempty hn
        hspecial.1 hspecial.2,
        incomingPortKey_eq_special d hspecial.1 hspecial.2]
      rfl

theorem joiningDiamond_childKey_eq_outgoing
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n) :
    (joiningDiamond C hC hn).childKey = outgoingPortKey C hC hn := by
  rcases firstChord_rank_cases C hC with hi | hrest
  · rw [joiningDiamond_eq_leftRankPos C hC hn hi,
      outgoingPortKey_eq_leftRankPos C hC hn hi]
    rfl
  · rcases hrest with hmid | hspecial
    · rw [joiningDiamond_eq_leftZero_rightGeTwo C hC hn hmid.1 hmid.2,
        outgoingPortKey_eq_leftZero_rightGeTwo C hC hn hmid.1 hmid.2]
      rfl
    · rw [joiningDiamond_eq_special C hC hn hspecial.1 hspecial.2,
        outgoingPortKey_eq_special C hC hn hspecial.1 hspecial.2]
      rfl

theorem chordEnds_ne_empty {e : Fin n × Fin n} : chordEnds e ≠ ∅ := by
  intro h
  have : e.1 ∈ (∅ : Finset (Fin n)) := by
    rw [← h]
    simp [chordEnds]
  simpa using this

theorem incomingPortKey_ne_outgoing (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n) (d : ChildData Q) :
    incomingPortKey d ≠ outgoingPortKey Q hQ hn := by
  rcases firstChord_rank_cases Q hQ with hiQ | hrestQ
  · have hout := outgoingPortKey_eq_leftRankPos Q hQ hn hiQ
    rcases firstChord_rank_cases d.child d.child_nonempty with hi | hrest
    · have hin := incomingPortKey_eq_leftRankPos d hi
      intro h
      have hk := hin.symm.trans (h.trans hout)
      have hempty : chordEnds d.chord = ∅ :=
        (AmbientPortKey.coordinate.injEq _ _ _ _).mp hk |>.2
      exact chordEnds_ne_empty hempty
    · rcases hrest with hmid | hspecial
      · have hin := incomingPortKey_eq_leftZero_rightGeTwo d hmid.1 hmid.2
        intro h
        have hk := hin.symm.trans (h.trans hout)
        have hempty : chordEnds d.chord = ∅ :=
          (AmbientPortKey.coordinate.injEq _ _ _ _).mp hk |>.2
        exact chordEnds_ne_empty hempty
      · rw [incomingPortKey_eq_special d hspecial.1 hspecial.2, hout]
        intro h
        contradiction
  · rcases hrestQ with hmidQ | hspecialQ
    · have hout := outgoingPortKey_eq_leftZero_rightGeTwo Q hQ hn hmidQ.1 hmidQ.2
      rcases firstChord_rank_cases d.child d.child_nonempty with hi | hrest
      · have hin := incomingPortKey_eq_leftRankPos d hi
        intro h
        have hk := hin.symm.trans (h.trans hout)
        have hempty : chordEnds d.chord = ∅ :=
          (AmbientPortKey.coordinate.injEq _ _ _ _).mp hk |>.2
        exact chordEnds_ne_empty hempty
      · rcases hrest with hmid | hspecial
        · have hin := incomingPortKey_eq_leftZero_rightGeTwo d hmid.1 hmid.2
          intro h
          have hk := hin.symm.trans (h.trans hout)
          have hempty : chordEnds d.chord = ∅ :=
            (AmbientPortKey.coordinate.injEq _ _ _ _).mp hk |>.2
          exact chordEnds_ne_empty hempty
        · rw [incomingPortKey_eq_special d hspecial.1 hspecial.2, hout]
          intro h
          contradiction
    · exact fun _ => special_block_has_no_child Q hQ hspecialQ.1 hspecialQ.2 ⟨d⟩

theorem rankGrayMasks_cubeListOn (C : CanonicalMatching n) :
    Cube.CubeListOn (fun _ => True) ∅ (Gray.firstSingleton (rankCoords C))
      (rankGrayMasks C) := by
  have h := Gray.grayList_cubeListOn (rankCoords C) (rankCoords_nodup C)
  exact Gray.CubeListOn.congrCover h (fun S => by
    rw [rankCoords_toFinset]
    constructor
    · intro _
      trivial
    · intro _ x _hx
      exact Finset.mem_attach _ x)

end Ports
end Petersen
end Hamilton.Infrastructure
