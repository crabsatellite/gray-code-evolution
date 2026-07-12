/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.PetersenMatchingCode
import Hamilton.Infrastructure.HypercubeLaceability

/-!
# The explicit reflected Gray cycles used by Petersen blocks
-/

namespace Hamilton.Infrastructure
namespace Petersen
namespace Gray

open Finset
open Cube

variable {ι : Type*} [DecidableEq ι]

/-- Binary-reflected Gray order, with the list head used as the newest high
coordinate. -/
def grayList : List ι → List (Finset ι)
  | [] => [∅]
  | a :: rest =>
      grayList rest ++ (grayList rest).reverse.map (insert a)

def firstSingleton : List ι → Finset ι
  | [] => ∅
  | a :: _ => {a}

@[simp] theorem grayList_nil : grayList ([] : List ι) = [∅] := rfl

@[simp] theorem grayList_cons (a : ι) (rest : List ι) :
    grayList (a :: rest) =
      grayList rest ++ (grayList rest).reverse.map (insert a) := rfl

theorem CubeListOn.congrCover {c d : Finset ι → Prop} {u v : Finset ι}
    {L : List (Finset ι)} (h : CubeListOn c u v L)
    (hcd : ∀ S, c S ↔ d S) : CubeListOn d u v L := by
  refine ⟨h.head_eq, h.last_eq, h.nodup, h.chain, ?_⟩
  intro S
  exact (h.cover_iff S).trans (hcd S)

theorem grayList_cubeListOn : ∀ (coords : List ι), coords.Nodup →
    CubeListOn (fun S => S ⊆ coords.toFinset) ∅
      (firstSingleton coords) (grayList coords)
  | [], _ => by
      refine ⟨rfl, rfl, by simp, by simp, ?_⟩
      intro S
      simp
  | a :: rest, hnodup => by
      have ha : a ∉ rest.toFinset := by simpa using (List.nodup_cons.mp hnodup).1
      have ih := grayList_cubeListOn rest (List.nodup_cons.mp hnodup).2
      have ih' : CubeListOn (fun S => S ⊆ rest.toFinset) ∅
          (firstSingleton rest) (grayList rest) := ih
      have haCover : ∀ S, S ⊆ rest.toFinset → a ∉ S := by
        intro S hS haS
        exact ha (hS haS)
      have upper := (ih'.mapInsert haCover).reverse
      have htail_a : a ∉ firstSingleton rest := by
        exact haCover (firstSingleton rest) ih'.last_mem_cover
      have joined := ih'.append upper (flipAdj_insert htail_a)
        (fun S hlow hupp => (haCover S hlow) hupp.1)
      have hcover : ∀ S : Finset ι,
          (S ⊆ rest.toFinset ∨ a ∈ S ∧ S.erase a ⊆ rest.toFinset) ↔
            S ⊆ insert a rest.toFinset := by
        intro S
        constructor
        · rintro (hS | hS)
          · intro x hx
            exact Finset.mem_insert_of_mem (hS hx)
          · intro x hx
            by_cases hxa : x = a
            · subst x
              exact Finset.mem_insert_self _ _
            · have hxErase : x ∈ S.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
              exact Finset.mem_insert_of_mem (hS.2 hxErase)
        · intro hS
          by_cases haS : a ∈ S
          · right
            refine ⟨haS, ?_⟩
            intro x hx
            obtain ⟨hxa, hxS⟩ := Finset.mem_erase.mp hx
            rcases Finset.mem_insert.mp (hS hxS) with hEq | hrest
            · exact (hxa hEq).elim
            · exact hrest
          · left
            intro x hx
            rcases Finset.mem_insert.mp (hS hx) with hEq | hrest
            · subst x
              exact (haS hx).elim
            · exact hrest
      have result := CubeListOn.congrCover joined hcover
      simpa [firstSingleton, List.map_reverse] using result

theorem grayList_nodup (coords : List ι) (h : coords.Nodup) :
    (grayList coords).Nodup := (grayList_cubeListOn coords h).nodup

theorem mem_grayList_iff (coords : List ι) (h : coords.Nodup) (S : Finset ι) :
    S ∈ grayList coords ↔ S ⊆ coords.toFinset :=
  (grayList_cubeListOn coords h).cover_iff S

theorem grayList_chain (coords : List ι) (h : coords.Nodup) :
    List.IsChain flipAdj (grayList coords) :=
  (grayList_cubeListOn coords h).chain

theorem grayList_head (coords : List ι) (h : coords.Nodup) :
    (grayList coords).head? = some ∅ :=
  (grayList_cubeListOn coords h).head_eq

theorem grayList_last_cons (a : ι) (rest : List ι)
    (h : (a :: rest).Nodup) :
    (grayList (a :: rest)).getLast? = some {a} :=
  (grayList_cubeListOn (a :: rest) h).last_eq

theorem grayList_closing_flip (a : ι) (rest : List ι)
    (h : (a :: rest).Nodup) : flipAdj ({a} : Finset ι) ∅ := by
  exact flipAdj_symm (flipAdj_insert (Finset.notMem_empty a))

/-- Two masks occur consecutively in either orientation. -/
def Consecutive (L : List (Finset ι)) (A B : Finset ι) : Prop :=
  (∃ pre post, L = pre ++ A :: B :: post) ∨
  (∃ pre post, L = pre ++ B :: A :: post)

theorem Consecutive.symm {L : List (Finset ι)} {A B : Finset ι}
    (h : Consecutive L A B) : Consecutive L B A := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem Consecutive.append_right {L K : List (Finset ι)} {A B : Finset ι}
    (h : Consecutive L A B) : Consecutive (L ++ K) A B := by
  rcases h with ⟨pre, post, h⟩ | ⟨pre, post, h⟩
  · left
    refine ⟨pre, post ++ K, ?_⟩
    rw [h]
    simp [List.append_assoc]
  · right
    refine ⟨pre, post ++ K, ?_⟩
    rw [h]
    simp [List.append_assoc]

theorem Consecutive.reverse_map_insert {L : List (Finset ι)} {A B : Finset ι}
    (a : ι) (h : Consecutive L A B) :
    Consecutive (L.reverse.map (insert a)) (insert a A) (insert a B) := by
  rcases h with ⟨pre, post, h⟩ | ⟨pre, post, h⟩
  · right
    refine ⟨post.reverse.map (insert a), pre.reverse.map (insert a), ?_⟩
    rw [h]
    simp [List.map_append, List.append_assoc]
  · left
    refine ⟨post.reverse.map (insert a), pre.reverse.map (insert a), ?_⟩
    rw [h]
    simp [List.map_append, List.append_assoc]

theorem Consecutive.grayList_lift_lower {rest : List ι} {A B : Finset ι}
    (a : ι) (h : Consecutive (grayList rest) A B) :
    Consecutive (grayList (a :: rest)) A B := by
  exact h.append_right

theorem Consecutive.grayList_lift_upper {rest : List ι} {A B : Finset ι}
    (a : ι) (h : Consecutive (grayList rest) A B) :
    Consecutive (grayList (a :: rest)) (insert a A) (insert a B) := by
  have hu := h.reverse_map_insert a
  rcases hu with h1 | h2
  · left
    obtain ⟨pre, post, hp⟩ := h1
    refine ⟨grayList rest ++ pre, post, ?_⟩
    simp [grayList, hp, List.append_assoc]
  · right
    obtain ⟨pre, post, hp⟩ := h2
    refine ⟨grayList rest ++ pre, post, ?_⟩
    simp [grayList, hp, List.append_assoc]

/-- Every coordinate-zero edge occurs in reflected Gray order.  Here `c` is
the last (lowest) coordinate and `H` is an arbitrary high-coordinate mask. -/
theorem coordinateZero_consecutive : ∀ (high : List ι) (c : ι)
    (hnd : (high ++ [c]).Nodup) (H : Finset ι), H ⊆ high.toFinset →
    Consecutive (grayList (high ++ [c])) H (insert c H)
  | [], c, _hnd, H, hH => by
      have hEmpty : H = ∅ := Finset.subset_empty.mp (by simpa using hH)
      subst H
      left
      exact ⟨[], [], rfl⟩
  | a :: rest, c, hnd, H, hH => by
      have hndTail : (rest ++ [c]).Nodup := by
        simpa using (List.nodup_cons.mp hnd).2
      by_cases haH : a ∈ H
      · have hsub : H.erase a ⊆ rest.toFinset := by
          intro x hx
          have hxH := Finset.mem_of_mem_erase hx
          have hxAll := hH hxH
          simpa [Finset.mem_insert, (Finset.ne_of_mem_erase hx)] using hxAll
        have ih := coordinateZero_consecutive rest c hndTail (H.erase a) hsub
        have hu := ih.grayList_lift_upper a
        have hH : insert a (H.erase a) = H := Finset.insert_erase haH
        have hC : insert a (insert c (H.erase a)) = insert c H := by
          rw [Finset.insert_comm a c, Finset.insert_erase haH]
        rw [hH, hC] at hu
        exact hu
      · have hsub : H ⊆ rest.toFinset := by
          intro x hx
          have hxAll := hH hx
          have hxIns : x ∈ insert a rest.toFinset := by simpa using hxAll
          rcases Finset.mem_insert.mp hxIns with hxa | hxr
          · exact (haH (hxa ▸ hx)).elim
          · exact hxr
        exact (coordinateZero_consecutive rest c hndTail H hsub).grayList_lift_lower a

/-- Every required coordinate-one port occurs: the lower mask contains the
lowest coordinate `c0` and omits `c1`. -/
theorem coordinateOne_consecutive : ∀ (high : List ι) (c1 c0 : ι)
    (hnd : (high ++ [c1, c0]).Nodup) (H : Finset ι), H ⊆ high.toFinset →
    Consecutive (grayList (high ++ [c1, c0]))
      (insert c0 H) (insert c1 (insert c0 H))
  | [], c1, c0, _hnd, H, hH => by
      have hEmpty : H = ∅ := Finset.subset_empty.mp (by simpa using hH)
      subst H
      left
      exact ⟨[∅], [{c1}], by simp [grayList, Finset.insert_comm]⟩
  | a :: rest, c1, c0, hnd, H, hH => by
      have hndTail : (rest ++ [c1, c0]).Nodup := by
        simpa using (List.nodup_cons.mp hnd).2
      by_cases haH : a ∈ H
      · have hsub : H.erase a ⊆ rest.toFinset := by
          intro x hx
          have hxH := Finset.mem_of_mem_erase hx
          have hxAll := hH hxH
          simpa [Finset.mem_insert, (Finset.ne_of_mem_erase hx)] using hxAll
        have ih := coordinateOne_consecutive rest c1 c0 hndTail (H.erase a) hsub
        have hu := ih.grayList_lift_upper a
        have hH : insert a (H.erase a) = H := Finset.insert_erase haH
        have h0 : insert a (insert c0 (H.erase a)) = insert c0 H := by
          rw [Finset.insert_comm a c0, Finset.insert_erase haH]
        have h1 : insert a (insert c1 (insert c0 (H.erase a))) =
            insert c1 (insert c0 H) := by
          rw [Finset.insert_comm a c1, Finset.insert_comm a c0,
            Finset.insert_erase haH]
        rw [h0, h1] at hu
        exact hu
      · have hsub : H ⊆ rest.toFinset := by
          intro x hx
          have hxAll := hH hx
          have hxIns : x ∈ insert a rest.toFinset := by simpa using hxAll
          rcases Finset.mem_insert.mp hxIns with hxa | hxr
          · exact (haH (hxa ▸ hx)).elim
          · exact hxr
        exact (coordinateOne_consecutive rest c1 c0 hndTail H hsub).grayList_lift_lower a

theorem flipAdj_insert_cases {A B : Finset ι} (h : flipAdj A B) :
    (∃ q ∉ A, B = insert q A) ∨ (∃ q ∉ B, A = insert q B) := by
  have hsum := Cube.card_symmDiff_eq A B
  unfold flipAdj at h
  rw [h] at hsum
  by_cases hAB : (A \ B).card = 0
  · have hBA : (B \ A).card = 1 := by omega
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hBA
    left
    have hqmem : q ∈ B \ A := by rw [hq]; simp
    refine ⟨q, (Finset.mem_sdiff.mp hqmem).2, ?_⟩
    ext x
    constructor
    · intro hx
      by_cases hxA : x ∈ A
      · exact Finset.mem_insert_of_mem hxA
      · have hxDiff : x ∈ B \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
        rw [hq] at hxDiff
        exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hxDiff))
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hxA
      · exact (Finset.mem_sdiff.mp hqmem).1
      · have hzero : A \ B = ∅ := Finset.card_eq_zero.mp hAB
        by_contra hxB
        have : x ∈ A \ B := Finset.mem_sdiff.mpr ⟨hxA, hxB⟩
        rw [hzero] at this
        simp at this
  · have hAB1 : (A \ B).card = 1 := by omega
    have hBA0 : (B \ A).card = 0 := by omega
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hAB1
    right
    have hqmem : q ∈ A \ B := by rw [hq]; simp
    refine ⟨q, (Finset.mem_sdiff.mp hqmem).2, ?_⟩
    ext x
    constructor
    · intro hx
      by_cases hxB : x ∈ B
      · exact Finset.mem_insert_of_mem hxB
      · have hxDiff : x ∈ A \ B := Finset.mem_sdiff.mpr ⟨hx, hxB⟩
        rw [hq] at hxDiff
        exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hxDiff))
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hxB
      · exact (Finset.mem_sdiff.mp hqmem).1
      · have hzero : B \ A = ∅ := Finset.card_eq_zero.mp hBA0
        by_contra hxA
        have : x ∈ B \ A := Finset.mem_sdiff.mpr ⟨hxB, hxA⟩
        rw [hzero] at this
        simp at this

theorem decodedNC_adj_of_flipAdj {n : Nat} [NeZero n]
    (Q : CanonicalMatching n) {A B : Finset Q.free} (h : flipAdj A B) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj
      (Q.decodedNC A) (Q.decodedNC B) := by
  rcases flipAdj_insert_cases h with ⟨q, hqA, rfl⟩ | ⟨q, hqB, rfl⟩
  · exact Encoding.decodedNC_adj_insert Q A q hqA
  · exact NC.Adj_symm (Encoding.decodedNC_adj_insert Q B q hqB)

section Blocks

variable {n : Nat} [NeZero n]

def blockCoords (Q : CanonicalMatching n) : List Q.free :=
  Q.free.attach.sort (fun x y => x ≥ y)

def blockGrayMasks (Q : CanonicalMatching n) : List (Finset Q.free) :=
  grayList (blockCoords Q)

noncomputable def blockGrayVertices (Q : CanonicalMatching n) :
    List (NC (Finset.univ : Finset (Fin n))) :=
  (blockGrayMasks Q).map Q.decodedNC

theorem blockCoords_nodup (Q : CanonicalMatching n) : (blockCoords Q).Nodup :=
  Finset.sort_nodup _ _

theorem blockCoords_toFinset (Q : CanonicalMatching n) :
    (blockCoords Q).toFinset = Q.free.attach :=
  Finset.sort_toFinset _ _

theorem blockGrayMasks_cubeListOn (Q : CanonicalMatching n) :
    CubeListOn (fun _ => True) ∅ (firstSingleton (blockCoords Q))
      (blockGrayMasks Q) := by
  have h := grayList_cubeListOn (blockCoords Q) (blockCoords_nodup Q)
  exact Hamilton.Infrastructure.Petersen.Gray.CubeListOn.congrCover h (fun S => by
    rw [blockCoords_toFinset]
    constructor
    · intro _; trivial
    · intro _ x _hx
      exact Finset.mem_attach _ x)

theorem decodedNC_fixed_injective (Q : CanonicalMatching n) :
    Function.Injective Q.decodedNC := by
  intro A B h
  ext q
  rw [← Encoding.decoded_part_card_ge_two_iff_mem_mask Q A q,
    ← Encoding.decoded_part_card_ge_two_iff_mem_mask Q B q]
  have hval : Q.decodedFinpartition A = Q.decodedFinpartition B :=
    congrArg Subtype.val h
  rw [hval]

theorem blockGrayVertices_nodup (Q : CanonicalMatching n) :
    (blockGrayVertices Q).Nodup := by
  rw [blockGrayVertices, List.nodup_map_iff_inj_on
    (blockGrayMasks_cubeListOn Q).nodup]
  intro A _ B _ h
  exact decodedNC_fixed_injective Q h

theorem blockGrayVertices_chain (Q : CanonicalMatching n) :
    List.IsChain (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj
      (blockGrayVertices Q) := by
  rw [blockGrayVertices, List.isChain_map]
  exact (blockGrayMasks_cubeListOn Q).chain.imp
    (fun _A _B h => decodedNC_adj_of_flipAdj Q h)

theorem mem_blockGrayVertices_iff (Q : CanonicalMatching n)
    (π : NC (Finset.univ : Finset (Fin n))) :
    π ∈ blockGrayVertices Q ↔ ∃ A : Finset Q.free, Q.decodedNC A = π := by
  rw [blockGrayVertices, List.mem_map]
  constructor
  · rintro ⟨A, _hA, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨A, (blockGrayMasks_cubeListOn Q).cover_iff A |>.2 trivial, rfl⟩

end Blocks

end Gray
end Petersen
end Hamilton.Infrastructure
