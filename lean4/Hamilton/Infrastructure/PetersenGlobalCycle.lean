/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.PetersenTreeSwitch
import Hamilton.Infrastructure.CardNCInduction
import Hamilton.Infrastructure.CatalanPos

/-!
# The global Petersen block-tree cycle

This file performs the well-founded simultaneous square switching over the
canonical matching tree.  The recursion measure is the number of free
points: every child has exactly two fewer free points than its parent.
-/

namespace Hamilton.Infrastructure
namespace Petersen
namespace Global

open Ports
open Switch

variable {n : Nat} [NeZero n]

def rootMatching : CanonicalMatching n := ⟨∅, by
  constructor
  · simp
  constructor <;> simp⟩

@[simp] theorem rootMatching_val : (rootMatching : CanonicalMatching n).1 = ∅ := rfl

theorem eq_rootMatching_iff (Q : CanonicalMatching n) :
    Q = rootMatching ↔ Q.1 = ∅ := by
  constructor
  · rintro rfl
    rfl
  · intro h
    exact Subtype.ext h

noncomputable def parentOption (C : CanonicalMatching n) :
    Option (CanonicalMatching n) :=
  if hC : C.1.Nonempty then some (parent C hC) else none

theorem parentOption_eq_some (C : CanonicalMatching n) (hC : C.1.Nonempty) :
    parentOption C = some (parent C hC) := by
  simp [parentOption, hC]

theorem parentOption_eq_none_iff (C : CanonicalMatching n) :
    parentOption C = none ↔ C = rootMatching := by
  rw [eq_rootMatching_iff]
  constructor
  · intro h
    by_contra hne
    have hC : C.1.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    rw [parentOption_eq_some C hC] at h
    contradiction
  · intro h
    have hn : ¬ C.1.Nonempty := by simpa [Finset.not_nonempty_iff_eq_empty]
    simp [parentOption, hn]

noncomputable def children (Q : CanonicalMatching n) :
    Finset (CanonicalMatching n) :=
  Finset.univ.filter fun C ↦ parentOption C = some Q

@[simp] theorem mem_children_iff (Q C : CanonicalMatching n) :
    C ∈ children Q ↔ parentOption C = some Q := by
  simp [children]

theorem child_nonempty {Q C : CanonicalMatching n} (hC : C ∈ children Q) :
    C.1.Nonempty := by
  by_contra hne
  have hp := (mem_children_iff Q C).mp hC
  simp [parentOption, hne] at hp

theorem parent_eq_of_mem_children {Q C : CanonicalMatching n}
    (hC : C ∈ children Q) :
    parent C (child_nonempty hC) = Q := by
  have hp := (mem_children_iff Q C).mp hC
  rw [parentOption_eq_some C (child_nonempty hC)] at hp
  exact Option.some.inj hp

noncomputable def childDataOfMem {Q C : CanonicalMatching n}
    (hC : C ∈ children Q) : ChildData Q where
  child := C
  child_nonempty := child_nonempty hC
  parent_eq := parent_eq_of_mem_children hC

theorem child_free_lt_parent {Q C : CanonicalMatching n}
    (hC : C ∈ children Q) : C.free.card < Q.free.card := by
  have hfree := parent_free_card C (child_nonempty hC)
  rw [parent_eq_of_mem_children hC] at hfree
  omega

theorem child_ne_parent {Q C : CanonicalMatching n}
    (hC : C ∈ children Q) : C ≠ Q := by
  intro h
  subst C
  exact (Nat.lt_irrefl _) (child_free_lt_parent hC)

theorem child_parent_unique {Q R C : CanonicalMatching n}
    (hQ : C ∈ children Q) (hR : C ∈ children R) : Q = R := by
  rw [mem_children_iff] at hQ hR
  exact Option.some.inj (hQ.symm.trans hR)

theorem childData_mem_children {Q : CanonicalMatching n} (d : ChildData Q) :
    d.child ∈ children Q := by
  rw [mem_children_iff, parentOption_eq_some d.child d.child_nonempty,
    d.parent_eq]

def ParentStep (C Q : CanonicalMatching n) : Prop :=
  parentOption C = some Q

def InSubtree (Q C : CanonicalMatching n) : Prop :=
  Relation.ReflTransGen ParentStep C Q

theorem parentStep_rightUnique : Relator.RightUnique (@ParentStep n _) := by
  intro C Q R hQ hR
  exact Option.some.inj (hQ.symm.trans hR)

theorem parentStep_free_lt {C Q : CanonicalMatching n} (h : ParentStep C Q) :
    C.free.card < Q.free.card := by
  have hC : C ∈ children Q := (mem_children_iff Q C).mpr h
  exact child_free_lt_parent hC

theorem inSubtree_free_le {Q C : CanonicalMatching n} (h : InSubtree Q C) :
    C.free.card ≤ Q.free.card := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
      exact ih.trans (Nat.le_of_lt (parentStep_free_lt hstep))

theorem eq_of_inSubtree_of_free_card_eq {Q C : CanonicalMatching n}
    (h : InSubtree Q C) (hcard : C.free.card = Q.free.card) : C = Q := by
  induction h with
  | refl => rfl
  | @tail B D hCB hBD ih =>
      have hle : C.free.card ≤ B.free.card := inSubtree_free_le hCB
      have hlt : B.free.card < D.free.card := parentStep_free_lt hBD
      omega

theorem inSubtree_child_decomposition {Q C : CanonicalMatching n}
    (h : InSubtree Q C) (hne : C ≠ Q) :
    ∃ D, D ∈ children Q ∧ InSubtree D C := by
  rcases Relation.ReflTransGen.cases_tail h with hEq | ⟨D, hCD, hDQ⟩
  · exact (hne hEq.symm).elim
  · exact ⟨D, (mem_children_iff Q D).mpr hDQ, hCD⟩

theorem child_subtrees_disjoint {Q D₁ D₂ C : CanonicalMatching n}
    (hD₁ : D₁ ∈ children Q) (hD₂ : D₂ ∈ children Q)
    (hC₁ : InSubtree D₁ C) (hC₂ : InSubtree D₂ C) : D₁ = D₂ := by
  rcases Relation.ReflTransGen.total_of_right_unique parentStep_rightUnique hC₁ hC₂ with
    h₁₂ | h₂₁
  · apply eq_of_inSubtree_of_free_card_eq h₁₂
    have h₁ := parent_free_card D₁ (child_nonempty hD₁)
    have h₂ := parent_free_card D₂ (child_nonempty hD₂)
    rw [parent_eq_of_mem_children hD₁] at h₁
    rw [parent_eq_of_mem_children hD₂] at h₂
    omega
  · symm
    apply eq_of_inSubtree_of_free_card_eq h₂₁
    have h₁ := parent_free_card D₁ (child_nonempty hD₁)
    have h₂ := parent_free_card D₂ (child_nonempty hD₂)
    rw [parent_eq_of_mem_children hD₁] at h₁
    rw [parent_eq_of_mem_children hD₂] at h₂
    omega

structure IncomingPort (Q : CanonicalMatching n) (hn : Even n) where
  childData : ChildData Q
  parentLower : Finset Q.free
  parentUpper : Finset Q.free
  childLower : Finset childData.child.free
  childUpper : Finset childData.child.free
  key : AmbientPortKey n
  childKey : AmbientPortKey n
  parentEdge : OnRankGrayCycle Q (free_card_pos_of_even Q hn)
    parentLower parentUpper
  childEdge : OnRankGrayCycle childData.child
    (free_card_pos_of_even childData.child hn) childLower childUpper
  key_realizes : RealizesPortKey Q (free_card_pos_of_even Q hn)
    key parentLower parentUpper
  childKey_realizes : RealizesPortKey childData.child
    (free_card_pos_of_even childData.child hn) childKey childLower childUpper
  coordinate_edge : ∀ q lower, key = .coordinate q lower →
    Gray.Consecutive (rankGrayMasks Q) parentLower parentUpper
  closing_edge : key = .closing →
    (parentLower = ∅ ∧ parentUpper =
      {highestFree Q (free_card_pos_of_even Q hn)}) ∨
    (parentUpper = ∅ ∧ parentLower =
      {highestFree Q (free_card_pos_of_even Q hn)})
  childCoordinate_edge : ∀ q lower, childKey = .coordinate q lower →
    Gray.Consecutive (rankGrayMasks childData.child) childLower childUpper
  childClosing_edge : childKey = .closing →
    (childLower = ∅ ∧ childUpper =
      {highestFree childData.child
        (free_card_pos_of_even childData.child hn)}) ∨
    (childUpper = ∅ ∧ childLower =
      {highestFree childData.child
        (free_card_pos_of_even childData.child hn)})
  crossLower : (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj
    (Q.decodedNC parentLower) (childData.child.decodedNC childLower)
  crossUpper : (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj
    (Q.decodedNC parentUpper) (childData.child.decodedNC childUpper)

noncomputable def incomingPort {Q : CanonicalMatching n} (hn : Even n)
    (d : ChildData Q) : IncomingPort Q hn := by
  rcases d with ⟨C, hC, hp⟩
  subst Q
  let D := joiningDiamond C hC hn
  exact
    { childData := ⟨C, hC, rfl⟩
      parentLower := D.parentLower
      parentUpper := D.parentUpper
      childLower := D.childLower
      childUpper := D.childUpper
      key := D.parentKey
      childKey := D.childKey
      parentEdge := D.parentEdge
      childEdge := D.childEdge
      key_realizes := D.parentKey_realizes
      childKey_realizes := D.childKey_realizes
      coordinate_edge := D.parentCoordinate_edge
      closing_edge := D.parentClosing_edge
      childCoordinate_edge := D.childCoordinate_edge
      childClosing_edge := D.childClosing_edge
      crossLower := D.crossLower
      crossUpper := D.crossUpper }

@[simp] theorem incomingPort_childData {Q : CanonicalMatching n} (hn : Even n)
    (d : ChildData Q) : (incomingPort hn d).childData = d := by
  rcases d with ⟨C, hC, hp⟩
  subst Q
  rfl

theorem incomingPort_key (hn : Even n) {Q : CanonicalMatching n}
    (d : ChildData Q) : (incomingPort hn d).key = incomingPortKey d := by
  rcases d with ⟨C, hC, hp⟩
  subst Q
  exact joiningDiamond_parentKey_eq_incoming ⟨C, hC, rfl⟩ hn

theorem incomingPort_childKey (hn : Even n) {Q : CanonicalMatching n}
    (d : ChildData Q) :
    (incomingPort hn d).childKey = outgoingPortKey d.child d.child_nonempty hn := by
  rcases d with ⟨C, hC, hp⟩
  subst Q
  exact joiningDiamond_childKey_eq_outgoing C hC hn

theorem incomingPort_key_injective (Q : CanonicalMatching n) (hn : Even n) :
    Function.Injective (fun d : ChildData Q ↦ (incomingPort hn d).key) := by
  intro d₁ d₂ h
  apply incomingPortKey_injective Q
  rw [← incomingPort_key hn d₁, ← incomingPort_key hn d₂]
  exact h

theorem mem_rankGrayVertices_iff_canonicalMatching
    (Q : CanonicalMatching n) (pi : NC (Finset.univ : Finset (Fin n))) :
    pi ∈ rankGrayVertices Q ↔ Encoding.canonicalMatching pi = Q := by
  constructor
  · intro hpi
    rcases List.mem_map.mp hpi with ⟨A, _hA, rfl⟩
    exact Encoding.canonicalMatching_decodedNC Q A
  · intro hQ
    subst Q
    refine List.mem_map.mpr ⟨Encoding.canonicalMask pi, ?_, Encoding.decode_encode pi⟩
    exact (rankGrayMasks_cubeListOn (Encoding.canonicalMatching pi)).cover_iff _ |>.2 trivial

abbrev NCRAdj (n : Nat) :=
  (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj

structure SubtreeCycle (Q : CanonicalMatching n) (hn : Even n) where
  cycle : CycleCode (NCRAdj n)
  support_iff : ∀ pi, pi ∈ cycle.vertices ↔
    InSubtree Q (Encoding.canonicalMatching pi)
  outgoing : ∀ (hQ : Q.1.Nonempty),
    let D := joiningDiamond Q hQ hn
    CyclicEdge cycle.vertices
      (Q.decodedNC D.childLower) (Q.decodedNC D.childUpper)

theorem SubtreeCycle.vertex_canonical_in_subtree {Q : CanonicalMatching n}
    {hn : Even n} (S : SubtreeCycle Q hn) {pi : NC (Finset.univ : Finset (Fin n))}
    (hpi : pi ∈ S.cycle.vertices) :
    InSubtree Q (Encoding.canonicalMatching pi) :=
  (S.support_iff pi).mp hpi

theorem subtreeCycles_disjoint {Q D₁ D₂ : CanonicalMatching n}
    {hn : Even n} (hD₁ : D₁ ∈ children Q) (hD₂ : D₂ ∈ children Q)
    (hne : D₁ ≠ D₂) (S₁ : SubtreeCycle D₁ hn) (S₂ : SubtreeCycle D₂ hn) :
    List.Disjoint S₁.cycle.vertices S₂.cycle.vertices := by
  rw [List.disjoint_left]
  intro pi hpi₁ hpi₂
  exact hne (child_subtrees_disjoint hD₁ hD₂
    (S₁.vertex_canonical_in_subtree hpi₁)
    (S₂.vertex_canonical_in_subtree hpi₂))

theorem block_disjoint_subtree {Q D : CanonicalMatching n} {hn : Even n}
    (hD : D ∈ children Q) (S : SubtreeCycle D hn) :
    List.Disjoint (rankGrayVertices Q) S.cycle.vertices := by
  rw [List.disjoint_left]
  intro pi hpiQ hpiD
  have hcanonQ := (mem_rankGrayVertices_iff_canonicalMatching Q pi).mp hpiQ
  have hsub := S.vertex_canonical_in_subtree hpiD
  rw [hcanonQ] at hsub
  have hle := inSubtree_free_le hsub
  have hlt := child_free_lt_parent hD
  omega

noncomputable def rankGrayMaskCycle (Q : CanonicalMatching n)
    (h : 0 < Q.free.card) :
    CycleCode (fun A B : Finset Q.free ↦ Cube.flipAdj A B) where
  vertices := rankGrayMasks Q
  nonempty := rankGrayMasks_ne_nil Q
  nodup := (rankGrayMasks_cubeListOn Q).nodup
  chain := (rankGrayMasks_cubeListOn Q).chain
  closing := by
    rw [(List.getLast_eq_iff_getLast?_eq_some _).mpr (rankGrayMasks_last Q h),
      (List.head_eq_iff_head?_eq_some _).mpr (rankGrayMasks_head Q)]
    exact rankGray_closing_flip Q h

theorem rankGrayCyclicPair_ne (Q : CanonicalMatching n) (h : 0 < Q.free.card)
    {e : Finset Q.free × Finset Q.free}
    (he : e ∈ cyclicPairs (rankGrayMasks Q)) : e.1 ≠ e.2 := by
  intro heq
  have hflip := cyclicPairs_rel (rankGrayMaskCycle Q h) e he
  rw [heq] at hflip
  exact Cube.flipAdj_irrefl _ hflip

def PortAssignedToPair (Q : CanonicalMatching n) (hn : Even n)
    (d : ChildData Q) (e : Finset Q.free × Finset Q.free) : Prop :=
  let P := incomingPort hn d
  match P.key with
  | .coordinate _ _ =>
      e ≠ (cyclicPairs (rankGrayMasks Q)).getLast
        (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q)) ∧
      ((P.parentLower = e.1 ∧ P.parentUpper = e.2) ∨
       (P.parentLower = e.2 ∧ P.parentUpper = e.1))
  | .closing =>
      e = (cyclicPairs (rankGrayMasks Q)).getLast
        (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q))

theorem portAssignedToPair_injective (Q : CanonicalMatching n) (hn : Even n)
    {e : Finset Q.free × Finset Q.free}
    (he : e ∈ cyclicPairs (rankGrayMasks Q))
    {d₁ d₂ : ChildData Q}
    (h₁ : PortAssignedToPair Q hn d₁ e)
    (h₂ : PortAssignedToPair Q hn d₂ e) : d₁ = d₂ := by
  cases hk₁ : (incomingPort hn d₁).key with
  | closing =>
      cases hk₂ : (incomingPort hn d₂).key with
      | closing =>
          apply incomingPort_key_injective Q hn
          simpa [hk₁, hk₂]
      | coordinate q H =>
          simp only [PortAssignedToPair, hk₁, hk₂] at h₁ h₂
          exact (h₂.1 h₁).elim
  | coordinate q H =>
      cases hk₂ : (incomingPort hn d₂).key with
      | closing =>
          simp only [PortAssignedToPair, hk₁, hk₂] at h₁ h₂
          exact (h₁.1 h₂).elim
      | coordinate r K =>
          simp only [PortAssignedToPair, hk₁] at h₁
          simp only [PortAssignedToPair, hk₂] at h₂
          have hreal₁ := (incomingPort hn d₁).key_realizes
          have hreal₂ := (incomingPort hn d₂).key_realizes
          rw [hk₁] at hreal₁
          rw [hk₂] at hreal₂
          have hr₁ : RealizesPortKey Q (free_card_pos_of_even Q hn)
              (.coordinate q H) e.1 e.2 := by
            rcases h₁.2 with hdir | hdir
            · rcases hreal₁ with ⟨x, hx, hreal⟩
              rw [hdir.1, hdir.2] at hreal
              exact ⟨x, hx, hreal⟩
            · rcases hreal₁ with ⟨x, hx, hreal | hreal⟩
              · rw [hdir.1, hdir.2] at hreal
                exact ⟨x, hx, Or.inr hreal⟩
              · rw [hdir.1, hdir.2] at hreal
                exact ⟨x, hx, Or.inl hreal⟩
          have hr₂ : RealizesPortKey Q (free_card_pos_of_even Q hn)
              (.coordinate r K) e.1 e.2 := by
            rcases h₂.2 with hdir | hdir
            · rcases hreal₂ with ⟨x, hx, hreal⟩
              rw [hdir.1, hdir.2] at hreal
              exact ⟨x, hx, hreal⟩
            · rcases hreal₂ with ⟨x, hx, hreal | hreal⟩
              · rw [hdir.1, hdir.2] at hreal
                exact ⟨x, hx, Or.inr hreal⟩
              · rw [hdir.1, hdir.2] at hreal
                exact ⟨x, hx, Or.inl hreal⟩
          have hkeys := coordinatePortKey_unique_of_ne Q
            (free_card_pos_of_even Q hn) (rankGrayCyclicPair_ne Q
              (free_card_pos_of_even Q hn) he) hr₁ hr₂
          apply incomingPort_key_injective Q hn
          change (incomingPort hn d₁).key = (incomingPort hn d₂).key
          rw [hk₁, hk₂, hkeys.1, hkeys.2]

theorem portAssignedToPair_exists (Q : CanonicalMatching n) (hn : Even n)
    (d : ChildData Q) :
    ∃ e ∈ cyclicPairs (rankGrayMasks Q), PortAssignedToPair Q hn d e := by
  let P := incomingPort hn d
  cases hk : P.key with
  | coordinate q H =>
      have hcon := P.coordinate_edge q H hk
      rcases hcon with ⟨pre, post, hlist⟩ | ⟨pre, post, hlist⟩
      · let e := (P.parentLower, P.parentUpper)
        have he : e ∈ cyclicPairs (rankGrayMasks Q) := by
          rw [hlist]
          exact pair_mem_cyclicPairs_append pre post _ _
        have hlast : e ≠ (cyclicPairs (rankGrayMasks Q)).getLast
            (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q)) := by
          exact internal_pair_ne_cyclicPairs_last hlist
            (rankGrayMasks_cubeListOn Q).nodup
        refine ⟨e, he, ?_⟩
        simp [PortAssignedToPair, P, hk, e, hlast]
      · let e := (P.parentUpper, P.parentLower)
        have he : e ∈ cyclicPairs (rankGrayMasks Q) := by
          rw [hlist]
          exact pair_mem_cyclicPairs_append pre post _ _
        have hlast : e ≠ (cyclicPairs (rankGrayMasks Q)).getLast
            (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q)) := by
          exact internal_pair_ne_cyclicPairs_last hlist
            (rankGrayMasks_cubeListOn Q).nodup
        refine ⟨e, he, ?_⟩
        simp [PortAssignedToPair, P, hk, e, hlast]
  | closing =>
      let e := (cyclicPairs (rankGrayMasks Q)).getLast
        (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q))
      refine ⟨e, List.getLast_mem _, ?_⟩
      simp [PortAssignedToPair, P, hk, e]

noncomputable def assignedPair (Q : CanonicalMatching n) (hn : Even n)
    (d : ChildData Q) : {e // e ∈ cyclicPairs (rankGrayMasks Q)} :=
  ⟨Classical.choose (portAssignedToPair_exists Q hn d),
    (Classical.choose_spec (portAssignedToPair_exists Q hn d)).1⟩

theorem assignedPair_assigned (Q : CanonicalMatching n) (hn : Even n)
    (d : ChildData Q) : PortAssignedToPair Q hn d (assignedPair Q hn d).1 :=
  (Classical.choose_spec (portAssignedToPair_exists Q hn d)).2

theorem assignedPair_injective (Q : CanonicalMatching n) (hn : Even n) :
    Function.Injective (assignedPair Q hn) := by
  intro d₁ d₂ h
  apply portAssignedToPair_injective Q hn (assignedPair Q hn d₁).2
    (assignedPair_assigned Q hn d₁)
  simpa [h] using assignedPair_assigned Q hn d₂

/-- The child occupying the canonical directed edge occurrence selected for
its port.  The canonical choice prevents the same undirected edge from being
counted twice in the dimension-one Gray cycle. -/
structure AssignedChild (Q : CanonicalMatching n) (hn : Even n)
    (e : Finset Q.free × Finset Q.free) where
  data : ChildData Q
  pair_eq : (assignedPair Q hn data).1 = e

theorem AssignedChild.assigned {Q : CanonicalMatching n} {hn : Even n}
    {e : Finset Q.free × Finset Q.free} (a : AssignedChild Q hn e) :
    PortAssignedToPair Q hn a.data e := by
  have h := assignedPair_assigned Q hn a.data
  rw [a.pair_eq] at h
  exact h

theorem AssignedChild.ext {Q : CanonicalMatching n} {hn : Even n}
    {e : Finset Q.free × Finset Q.free} (a b : AssignedChild Q hn e)
    (he : e ∈ cyclicPairs (rankGrayMasks Q)) : a = b := by
  cases a with
  | mk da ha =>
      cases b with
      | mk db hb =>
          have hp : assignedPair Q hn da = assignedPair Q hn db := by
            apply Subtype.ext
            exact ha.trans hb.symm
          have hd : da = db := assignedPair_injective Q hn hp
          subst db
          rfl

theorem assignedChild_subsingleton {Q : CanonicalMatching n} {hn : Even n}
    {e : Finset Q.free × Finset Q.free}
    (he : e ∈ cyclicPairs (rankGrayMasks Q)) :
    Subsingleton (AssignedChild Q hn e) :=
  ⟨fun a b => AssignedChild.ext a b he⟩

noncomputable def assignedChild? (Q : CanonicalMatching n) (hn : Even n)
    (e : Finset Q.free × Finset Q.free) : Option (AssignedChild Q hn e) := by
  classical
  exact if h : Nonempty (AssignedChild Q hn e) then
    some (Classical.choice h) else none

theorem assignedChild?_eq_some_iff {Q : CanonicalMatching n} {hn : Even n}
    {e : Finset Q.free × Finset Q.free}
    (he : e ∈ cyclicPairs (rankGrayMasks Q)) (a : AssignedChild Q hn e) :
    assignedChild? Q hn e = some a := by
  simp only [assignedChild?]
  split
  · rename_i h
    rw [show Classical.choice h = a from
      (assignedChild_subsingleton he).allEq _ _]
  · rename_i h
    exact (h ⟨a⟩).elim

theorem assignedChild?_exists_for_data (Q : CanonicalMatching n) (hn : Even n)
    (d : ChildData Q) :
    ∃ e ∈ cyclicPairs (rankGrayMasks Q),
      ∃ a, assignedChild? Q hn e = some a ∧ a.data = d := by
  let ep := assignedPair Q hn d
  let a : AssignedChild Q hn ep.1 := ⟨d, rfl⟩
  exact ⟨ep.1, ep.2, a, assignedChild?_eq_some_iff ep.2 a, rfl⟩

theorem SubtreeCycle.incoming_child_edge {Q : CanonicalMatching n}
    {hn : Even n} (d : ChildData Q) (S : SubtreeCycle d.child hn) :
    let P := incomingPort hn d
    CyclicEdge S.cycle.vertices
      (P.childData.child.decodedNC P.childLower)
      (P.childData.child.decodedNC P.childUpper) := by
  rcases d with ⟨C, hC, hp⟩
  subst Q
  simpa [incomingPort] using S.outgoing hC

theorem portAssigned_parent_orientation {Q : CanonicalMatching n}
    (hn : Even n) {e : Finset Q.free × Finset Q.free}
    (he : e ∈ cyclicPairs (rankGrayMasks Q)) (d : ChildData Q)
    (ha : PortAssignedToPair Q hn d e) :
    let P := incomingPort hn d
    (P.parentLower = e.1 ∧ P.parentUpper = e.2) ∨
      (P.parentLower = e.2 ∧ P.parentUpper = e.1) := by
  cases hk : (incomingPort hn d).key with
  | coordinate q lower =>
      simp only [PortAssignedToPair, hk] at ha
      exact ha.2
  | closing =>
      have hlast := cyclicPairs_last_fst
        (L := rankGrayMasks Q) (rankGrayMasks_ne_nil Q)
      have hclose := cyclicPairs_closing
        (L := rankGrayMasks Q) (rankGrayMasks_ne_nil Q)
      have heLast : e = (cyclicPairs (rankGrayMasks Q)).getLast
          (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q)) := by
        simpa [PortAssignedToPair, hk] using ha
      have hmaskLast := rankGrayMasks_last Q (free_card_pos_of_even Q hn)
      have hmaskHead := rankGrayMasks_head Q
      have heFst : e.1 = {highestFree Q (free_card_pos_of_even Q hn)} := by
        rw [heLast, hlast]
        exact (List.getLast_eq_iff_getLast?_eq_some _).mpr hmaskLast
      have heSnd : e.2 = ∅ := by
        rw [heLast, hclose]
        have hpairHead :
            ((cyclicPairs (rankGrayMasks Q)).head
              (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q))).1 =
              (rankGrayMasks Q).head (rankGrayMasks_ne_nil Q) := by
          exact cyclicPairs_head_fst (rankGrayMasks_ne_nil Q)
        rw [hpairHead]
        exact (List.head_eq_iff_head?_eq_some _).mpr hmaskHead
      rcases (incomingPort hn d).closing_edge hk with hdir | hdir
      · right
        exact ⟨hdir.1.trans heSnd.symm, hdir.2.trans heFst.symm⟩
      · left
        exact ⟨hdir.2.trans heFst.symm, hdir.1.trans heSnd.symm⟩

def OutgoingPortAssignedToPair (Q : CanonicalMatching n) (hQ : Q.1.Nonempty)
    (hn : Even n) (e : Finset Q.free × Finset Q.free) : Prop :=
  let D := joiningDiamond Q hQ hn
  match D.childKey with
  | .coordinate _ _ =>
      e ≠ (cyclicPairs (rankGrayMasks Q)).getLast
        (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q)) ∧
      ((D.childLower = e.1 ∧ D.childUpper = e.2) ∨
       (D.childLower = e.2 ∧ D.childUpper = e.1))
  | .closing =>
      e = (cyclicPairs (rankGrayMasks Q)).getLast
        (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q))

theorem outgoingPortAssignedToPair_exists (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n) :
    ∃ e ∈ cyclicPairs (rankGrayMasks Q), OutgoingPortAssignedToPair Q hQ hn e := by
  let D := joiningDiamond Q hQ hn
  cases hk : D.childKey with
  | coordinate q lower =>
      have hcon := D.childCoordinate_edge q lower hk
      rcases hcon with ⟨pre, post, hlist⟩ | ⟨pre, post, hlist⟩
      · let e := (D.childLower, D.childUpper)
        have he : e ∈ cyclicPairs (rankGrayMasks Q) := by
          rw [hlist]
          exact pair_mem_cyclicPairs_append pre post _ _
        have hlast : e ≠ (cyclicPairs (rankGrayMasks Q)).getLast
            (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q)) :=
          internal_pair_ne_cyclicPairs_last hlist
            (rankGrayMasks_cubeListOn Q).nodup
        exact ⟨e, he, by simp [OutgoingPortAssignedToPair, D, hk, e, hlast]⟩
      · let e := (D.childUpper, D.childLower)
        have he : e ∈ cyclicPairs (rankGrayMasks Q) := by
          rw [hlist]
          exact pair_mem_cyclicPairs_append pre post _ _
        have hlast : e ≠ (cyclicPairs (rankGrayMasks Q)).getLast
            (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q)) :=
          internal_pair_ne_cyclicPairs_last hlist
            (rankGrayMasks_cubeListOn Q).nodup
        exact ⟨e, he, by simp [OutgoingPortAssignedToPair, D, hk, e, hlast]⟩
  | closing =>
      let e := (cyclicPairs (rankGrayMasks Q)).getLast
        (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q))
      exact ⟨e, List.getLast_mem _, by
        simp [OutgoingPortAssignedToPair, D, hk, e]⟩

private theorem coordinateRealizes_reorient {Q : CanonicalMatching n}
    (hfree : 0 < Q.free.card) {q : Fin n} {H : Finset (Fin n)}
    {A B e₁ e₂ : Finset Q.free}
    (hreal : RealizesPortKey Q hfree (.coordinate q H) A B)
    (hdir : (A = e₁ ∧ B = e₂) ∨ (A = e₂ ∧ B = e₁)) :
    RealizesPortKey Q hfree (.coordinate q H) e₁ e₂ := by
  rcases hdir with hdir | hdir
  · simpa [hdir.1, hdir.2] using hreal
  · rcases hreal with ⟨x, hx, hr | hr⟩
    · exact ⟨x, hx, Or.inr (by simpa [hdir.1, hdir.2] using hr)⟩
    · exact ⟨x, hx, Or.inl (by simpa [hdir.1, hdir.2] using hr)⟩

theorem portAssignedToPair_ne_outgoing (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n) (d : ChildData Q)
    {e : Finset Q.free × Finset Q.free}
    (he : e ∈ cyclicPairs (rankGrayMasks Q))
    (hin : PortAssignedToPair Q hn d e)
    (hout : OutgoingPortAssignedToPair Q hQ hn e) : False := by
  have hkeyne : (incomingPort hn d).key ≠
      (joiningDiamond Q hQ hn).childKey := by
    intro hkey
    apply incomingPortKey_ne_outgoing Q hQ hn d
    rw [← incomingPort_key hn d, ← joiningDiamond_childKey_eq_outgoing Q hQ hn]
    exact hkey
  cases hkin : (incomingPort hn d).key with
  | closing =>
      simp only [PortAssignedToPair, hkin] at hin
      cases hkout : (joiningDiamond Q hQ hn).childKey with
      | closing => exact hkeyne (by rw [hkin, hkout])
      | coordinate q H =>
          simp only [OutgoingPortAssignedToPair, hkout] at hout
          exact hout.1 hin
  | coordinate q H =>
      simp only [PortAssignedToPair, hkin] at hin
      cases hkout : (joiningDiamond Q hQ hn).childKey with
      | closing =>
          simp only [OutgoingPortAssignedToPair, hkout] at hout
          exact hin.1 hout
      | coordinate r K =>
          simp only [OutgoingPortAssignedToPair, hkout] at hout
          have hrealIn := (incomingPort hn d).key_realizes
          rw [hkin] at hrealIn
          have hrealOut := (joiningDiamond Q hQ hn).childKey_realizes
          rw [hkout] at hrealOut
          have hrIn := coordinateRealizes_reorient
            (free_card_pos_of_even Q hn) hrealIn hin.2
          have hrOut := coordinateRealizes_reorient
            (free_card_pos_of_even Q hn) hrealOut hout.2
          have hkeys := coordinatePortKey_unique_of_ne Q
            (free_card_pos_of_even Q hn)
            (rankGrayCyclicPair_ne Q (free_card_pos_of_even Q hn)
              he) hrIn hrOut
          apply hkeyne
          rw [hkin, hkout, hkeys.1, hkeys.2]

noncomputable def outgoingPair (Q : CanonicalMatching n) (hQ : Q.1.Nonempty)
    (hn : Even n) : {e // e ∈ cyclicPairs (rankGrayMasks Q)} :=
  ⟨Classical.choose (outgoingPortAssignedToPair_exists Q hQ hn),
    (Classical.choose_spec (outgoingPortAssignedToPair_exists Q hQ hn)).1⟩

theorem outgoingPair_assigned (Q : CanonicalMatching n) (hQ : Q.1.Nonempty)
    (hn : Even n) :
    OutgoingPortAssignedToPair Q hQ hn (outgoingPair Q hQ hn).1 :=
  (Classical.choose_spec (outgoingPortAssignedToPair_exists Q hQ hn)).2

theorem outgoingPair_not_assigned (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n) (d : ChildData Q) :
    (assignedPair Q hn d).1 ≠ (outgoingPair Q hQ hn).1 := by
  intro heq
  have hin := assignedPair_assigned Q hn d
  rw [heq] at hin
  exact portAssignedToPair_ne_outgoing Q hQ hn d (outgoingPair Q hQ hn).2
    hin (outgoingPair_assigned Q hQ hn)

theorem outgoingPair_orientation (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n) :
    let D := joiningDiamond Q hQ hn
    let e := (outgoingPair Q hQ hn).1
    (D.childLower = e.1 ∧ D.childUpper = e.2) ∨
      (D.childLower = e.2 ∧ D.childUpper = e.1) := by
  let D := joiningDiamond Q hQ hn
  let e := (outgoingPair Q hQ hn).1
  have ha := outgoingPair_assigned Q hQ hn
  cases hk : D.childKey with
  | coordinate q H =>
      simp only [OutgoingPortAssignedToPair, D, hk] at ha
      exact ha.2
  | closing =>
      simp only [OutgoingPortAssignedToPair, D, hk] at ha
      have hlast := cyclicPairs_last_fst
        (L := rankGrayMasks Q) (rankGrayMasks_ne_nil Q)
      have hclose := cyclicPairs_closing
        (L := rankGrayMasks Q) (rankGrayMasks_ne_nil Q)
      have heFst : e.1 = {highestFree Q (free_card_pos_of_even Q hn)} := by
        rw [show e = (cyclicPairs (rankGrayMasks Q)).getLast
          (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q)) from ha, hlast]
        exact (List.getLast_eq_iff_getLast?_eq_some _).mpr
          (rankGrayMasks_last Q (free_card_pos_of_even Q hn))
      have heSnd : e.2 = ∅ := by
        rw [show e = (cyclicPairs (rankGrayMasks Q)).getLast
          (cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q)) from ha, hclose,
          cyclicPairs_head_fst (rankGrayMasks_ne_nil Q)]
        exact (List.head_eq_iff_head?_eq_some _).mpr (rankGrayMasks_head Q)
      rcases D.childClosing_edge hk with hdir | hdir
      · right
        exact ⟨hdir.1.trans heSnd.symm, hdir.2.trans heFst.symm⟩
      · left
        exact ⟨hdir.2.trans heFst.symm, hdir.1.trans heSnd.symm⟩

def EdgePieceSupport (Q : CanonicalMatching n) (hn : Even n)
    (e : Finset Q.free × Finset Q.free)
    (pi : NC (Finset.univ : Finset (Fin n))) : Prop :=
  pi = Q.decodedNC e.1 ∨
    ∃ d : ChildData Q, (assignedPair Q hn d).1 = e ∧
      InSubtree d.child (Encoding.canonicalMatching pi)

structure EdgePieceData (Q : CanonicalMatching n) (hn : Even n)
    (e : {e // e ∈ cyclicPairs (rankGrayMasks Q)}) where
  vertices : List (NC (Finset.univ : Finset (Fin n)))
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  chain : vertices.IsChain (NCRAdj n)
  head_eq : vertices.head? = some (Q.decodedNC e.1.1)
  exit : NCRAdj n (vertices.getLast nonempty) (Q.decodedNC e.1.2)
  support_iff : ∀ pi, pi ∈ vertices ↔ EdgePieceSupport Q hn e.1 pi

private theorem cutPath_mem_iff_cycle_mem {Q : CanonicalMatching n}
    {hn : Even n} {d : ChildData Q} (S : SubtreeCycle d.child hn)
    {a b : NC (Finset.univ : Finset (Fin n))}
    (P : CutPath (NCRAdj n) S.cycle.vertices a b)
    (pi : NC (Finset.univ : Finset (Fin n))) :
    pi ∈ P.vertices ↔ pi ∈ S.cycle.vertices := by
  rw [← List.mem_toFinset, P.support_eq, List.mem_toFinset]

theorem edgePieceData_exists (Q : CanonicalMatching n) (hn : Even n)
    (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn)
    (e : {e // e ∈ cyclicPairs (rankGrayMasks Q)}) :
    Nonempty (EdgePieceData Q hn e) := by
  classical
  cases hopt : assignedChild? Q hn e.1 with
  | none =>
      refine ⟨
        { vertices := [Q.decodedNC e.1.1]
          nonempty := by simp
          nodup := by simp
          chain := by simp
          head_eq := by simp
          exit := Gray.decodedNC_adj_of_flipAdj Q
            (cyclicPairs_rel (rankGrayMaskCycle Q
              (free_card_pos_of_even Q hn)) e.1 e.2)
          support_iff := ?_ }⟩
      intro pi
      constructor
      · intro hpi
        have hEq : pi = Q.decodedNC e.1.1 := by simpa using hpi
        left
        exact hEq
      · intro hpi
        rcases hpi with hQ | ⟨d, hd, hsub⟩
        · simpa [hQ]
        · let a : AssignedChild Q hn e.1 := ⟨d, hd⟩
          have hs := assignedChild?_eq_some_iff e.2 a
          rw [hopt] at hs
          contradiction
  | some a =>
      have ha : assignedChild? Q hn e.1 = some a := hopt
      let P := incomingPort hn a.data
      let S := IH a.data
      have hedge : CyclicEdge S.cycle.vertices
          (P.childData.child.decodedNC P.childLower)
          (P.childData.child.decodedNC P.childUpper) := by
        simpa [P, S] using SubtreeCycle.incoming_child_edge a.data S
      rcases portAssigned_parent_orientation hn e.2 a.data a.assigned with hdir | hdir
      · let K := cutPathOfCyclicEdge NC.Adj_symm S.cycle hedge
        have hKne : K.vertices ≠ [] := by
          intro h
          have hh := K.head_eq
          rw [h] at hh
          simp at hh
        have hbaseNot : Q.decodedNC e.1.1 ∉ K.vertices := by
          intro hmem
          have hmemS := (cutPath_mem_iff_cycle_mem S K _).mp hmem
          have hsub := S.vertex_canonical_in_subtree hmemS
          have hcanon : Encoding.canonicalMatching (Q.decodedNC e.1.1) = Q :=
            Encoding.canonicalMatching_decodedNC Q e.1.1
          rw [hcanon] at hsub
          have hle := inSubtree_free_le hsub
          have hlt := child_free_lt_parent (childData_mem_children a.data)
          omega
        refine ⟨
          { vertices := Q.decodedNC e.1.1 :: K.vertices
            nonempty := by simp
            nodup := List.nodup_cons.mpr ⟨hbaseNot, K.nodup⟩
            chain := ?_
            head_eq := by simp
            exit := ?_
            support_iff := ?_ }⟩
        · rw [List.isChain_cons]
          refine ⟨?_, K.chain⟩
          intro y hy
          have hyEq : y = P.childData.child.decodedNC P.childLower := by
            rw [K.head_eq] at hy
            simpa using hy.symm
          rw [hyEq, ← hdir.1]
          simpa [P] using P.crossLower
        · have hlast : (Q.decodedNC e.1.1 :: K.vertices).getLast (by simp) =
              P.childData.child.decodedNC P.childUpper := by
            rw [List.getLast_cons hKne]
            exact (List.getLast_eq_iff_getLast?_eq_some _).mpr K.last_eq
          rw [hlast, ← hdir.2]
          simpa [P] using P.crossUpper.symm
        · intro pi
          rw [List.mem_cons, cutPath_mem_iff_cycle_mem S K,
            S.support_iff]
          constructor
          · rintro (rfl | hsub)
            · exact Or.inl rfl
            · exact Or.inr ⟨a.data, a.pair_eq, hsub⟩
          · rintro (hQ | ⟨d, hd, hsub⟩)
            · exact Or.inl hQ
            · right
              have hda : d = a.data := by
                apply assignedPair_injective Q hn
                apply Subtype.ext
                exact hd.trans a.pair_eq.symm
              simpa [hda] using hsub
      · let K := cutPathOfCyclicEdge NC.Adj_symm S.cycle
          (cyclicEdge_symm hedge)
        change P.parentLower = e.1.2 ∧ P.parentUpper = e.1.1 at hdir
        have hKne : K.vertices ≠ [] := by
          intro h
          have hh := K.head_eq
          rw [h] at hh
          simp at hh
        have hbaseNot : Q.decodedNC e.1.1 ∉ K.vertices := by
          intro hmem
          have hmemS := (cutPath_mem_iff_cycle_mem S K _).mp hmem
          have hsub := S.vertex_canonical_in_subtree hmemS
          have hcanon : Encoding.canonicalMatching (Q.decodedNC e.1.1) = Q :=
            Encoding.canonicalMatching_decodedNC Q e.1.1
          rw [hcanon] at hsub
          have hle := inSubtree_free_le hsub
          have hlt := child_free_lt_parent (childData_mem_children a.data)
          omega
        refine ⟨
          { vertices := Q.decodedNC e.1.1 :: K.vertices
            nonempty := by simp
            nodup := List.nodup_cons.mpr ⟨hbaseNot, K.nodup⟩
            chain := ?_
            head_eq := by simp
            exit := ?_
            support_iff := ?_ }⟩
        · rw [List.isChain_cons]
          refine ⟨?_, K.chain⟩
          intro y hy
          have hyEq : y = P.childData.child.decodedNC P.childUpper := by
            rw [K.head_eq] at hy
            simpa using hy.symm
          rw [hyEq, ← hdir.2]
          simpa [P] using P.crossUpper
        · have hlast : (Q.decodedNC e.1.1 :: K.vertices).getLast (by simp) =
              P.childData.child.decodedNC P.childLower := by
            rw [List.getLast_cons hKne]
            exact (List.getLast_eq_iff_getLast?_eq_some _).mpr K.last_eq
          rw [hlast, ← hdir.1]
          simpa [P] using P.crossLower.symm
        · intro pi
          rw [List.mem_cons, cutPath_mem_iff_cycle_mem S K,
            S.support_iff]
          constructor
          · rintro (rfl | hsub)
            · exact Or.inl rfl
            · exact Or.inr ⟨a.data, a.pair_eq, hsub⟩
          · rintro (hQ | ⟨d, hd, hsub⟩)
            · exact Or.inl hQ
            · right
              have hda : d = a.data := by
                apply assignedPair_injective Q hn
                apply Subtype.ext
                exact hd.trans a.pair_eq.symm
              simpa [hda] using hsub

noncomputable def edgePieceData (Q : CanonicalMatching n) (hn : Even n)
    (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn)
    (e : {e // e ∈ cyclicPairs (rankGrayMasks Q)}) : EdgePieceData Q hn e :=
  Classical.choice (edgePieceData_exists Q hn IH e)

theorem rankGrayCyclicPairs_nodup (Q : CanonicalMatching n) :
    (cyclicPairs (rankGrayMasks Q)).Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [cyclicPairs_fst]
  exact (rankGrayMasks_cubeListOn Q).nodup

theorem rankGrayCyclicPair_eq_of_fst_eq (Q : CanonicalMatching n)
    {e f : Finset Q.free × Finset Q.free}
    (he : e ∈ cyclicPairs (rankGrayMasks Q))
    (hf : f ∈ cyclicPairs (rankGrayMasks Q)) (hfst : e.1 = f.1) : e = f := by
  have hmap : (cyclicPairs (rankGrayMasks Q)).map Prod.fst |>.Nodup := by
    rw [cyclicPairs_fst]
    exact (rankGrayMasks_cubeListOn Q).nodup
  exact (List.nodup_map_iff_inj_on (rankGrayCyclicPairs_nodup Q)).mp
    hmap e he f hf hfst

theorem ChildData.eq_of_child_eq {Q : CanonicalMatching n} (d₁ d₂ : ChildData Q)
    (h : d₁.child = d₂.child) : d₁ = d₂ := by
  cases d₁
  cases d₂
  cases h
  rfl

noncomputable def edgePieceVertices (Q : CanonicalMatching n) (hn : Even n)
    (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn)
    (e : Finset Q.free × Finset Q.free) :
    List (NC (Finset.univ : Finset (Fin n))) := by
  classical
  exact if he : e ∈ cyclicPairs (rankGrayMasks Q) then
    (edgePieceData Q hn IH ⟨e, he⟩).vertices else []

theorem edgePieceVertices_eq (Q : CanonicalMatching n) (hn : Even n)
    (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn)
    {e : Finset Q.free × Finset Q.free}
    (he : e ∈ cyclicPairs (rankGrayMasks Q)) :
    edgePieceVertices Q hn IH e = (edgePieceData Q hn IH ⟨e, he⟩).vertices := by
  simp [edgePieceVertices, he]

theorem edgePieces_pairwise_disjoint (Q : CanonicalMatching n) (hn : Even n)
    (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn) :
    (cyclicPairs (rankGrayMasks Q)).map
      (edgePieceVertices Q hn IH) |>.Pairwise List.Disjoint := by
  rw [List.pairwise_map]
  have hne := (List.nodup_iff_pairwise_ne.mp
    (rankGrayCyclicPairs_nodup Q))
  apply List.Pairwise.imp_of_mem (p := hne)
  intro e f he hf hef
  rw [edgePieceVertices_eq Q hn IH he, edgePieceVertices_eq Q hn IH hf]
  rw [List.disjoint_left]
  intro pi hpiE hpiF
  have hsE := ((edgePieceData Q hn IH ⟨e, he⟩).support_iff pi).mp hpiE
  have hsF := ((edgePieceData Q hn IH ⟨f, hf⟩).support_iff pi).mp hpiF
  rcases hsE with hbaseE | ⟨dE, hslotE, hsubE⟩
  · rcases hsF with hbaseF | ⟨dF, _hslotF, hsubF⟩
    · apply hef
      apply rankGrayCyclicPair_eq_of_fst_eq Q he hf
      apply Gray.decodedNC_fixed_injective Q
      exact hbaseE.symm.trans hbaseF
    · subst pi
      have hcanon :
          Encoding.canonicalMatching (Q.decodedNC e.1) = Q :=
        Encoding.canonicalMatching_decodedNC Q e.1
      rw [hcanon] at hsubF
      have hle := inSubtree_free_le hsubF
      have hlt := child_free_lt_parent (childData_mem_children dF)
      omega
  · rcases hsF with hbaseF | ⟨dF, hslotF, hsubF⟩
    · subst pi
      have hcanon :
          Encoding.canonicalMatching (Q.decodedNC f.1) = Q :=
        Encoding.canonicalMatching_decodedNC Q f.1
      rw [hcanon] at hsubE
      have hle := inSubtree_free_le hsubE
      have hlt := child_free_lt_parent (childData_mem_children dE)
      omega
    · have hchild : dE.child = dF.child := child_subtrees_disjoint
          (childData_mem_children dE) (childData_mem_children dF) hsubE hsubF
      have hd : dE = dF := ChildData.eq_of_child_eq dE dF hchild
      subst dF
      apply hef
      exact hslotE.symm.trans hslotF

noncomputable def subtreeEdgePieceSystem (Q : CanonicalMatching n) (hn : Even n)
    (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn) :
    EdgePieceSystem (Finset Q.free × Finset Q.free) (NCRAdj n) where
  edges := cyclicPairs (rankGrayMasks Q)
  edges_nonempty := cyclicPairs_ne_nil (rankGrayMasks_ne_nil Q)
  source e := Q.decodedNC e.1
  target e := Q.decodedNC e.2
  edge_chain := (cyclicPairs_chain (rankGrayMasks Q)).imp fun _ _ h => by
    simpa [h]
  edge_closing := by
    apply congrArg Q.decodedNC
    exact cyclicPairs_closing (rankGrayMasks_ne_nil Q)
  piece := edgePieceVertices Q hn IH
  piece_nonempty e he := by
    rw [edgePieceVertices_eq Q hn IH he]
    exact (edgePieceData Q hn IH ⟨e, he⟩).nonempty
  piece_nodup e he := by
    rw [edgePieceVertices_eq Q hn IH he]
    exact (edgePieceData Q hn IH ⟨e, he⟩).nodup
  pieces_disjoint := edgePieces_pairwise_disjoint Q hn IH
  piece_chain e he := by
    rw [edgePieceVertices_eq Q hn IH he]
    exact (edgePieceData Q hn IH ⟨e, he⟩).chain
  piece_head e he := by
    rw [edgePieceVertices_eq Q hn IH he]
    exact (edgePieceData Q hn IH ⟨e, he⟩).head_eq
  piece_exit e he := by
    simpa [edgePieceVertices, he] using
      (edgePieceData Q hn IH ⟨e, he⟩).exit

theorem mem_subtreeEdgePieces_iff (Q : CanonicalMatching n) (hn : Even n)
    (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn)
    (pi : NC (Finset.univ : Finset (Fin n))) :
    pi ∈ ((cyclicPairs (rankGrayMasks Q)).map
        (edgePieceVertices Q hn IH)).flatten ↔
      InSubtree Q (Encoding.canonicalMatching pi) := by
  constructor
  · intro hpiFlat
    rcases List.mem_flatten.mp hpiFlat with ⟨K, hK, hpi⟩
    rcases List.mem_map.mp hK with ⟨e, he, rfl⟩
    rw [edgePieceVertices_eq Q hn IH he] at hpi
    rcases ((edgePieceData Q hn IH ⟨e, he⟩).support_iff pi).mp hpi with
      hbase | ⟨d, _hslot, hsub⟩
    · subst pi
      rw [Encoding.canonicalMatching_decodedNC]
      exact Relation.ReflTransGen.refl
    · exact hsub.tail ((mem_children_iff Q d.child).mp
        (childData_mem_children d))
  · intro hsub
    by_cases hQ : Encoding.canonicalMatching pi = Q
    · have hbase : pi ∈ rankGrayVertices Q :=
        (mem_rankGrayVertices_iff_canonicalMatching Q pi).mpr hQ
      rcases List.mem_map.mp hbase with ⟨A, hA, hdecode⟩
      have hfst : A ∈
          (cyclicPairs (rankGrayMasks Q)).map Prod.fst := by
        simpa [cyclicPairs_fst] using hA
      rcases List.mem_map.mp hfst with ⟨e, he, heq⟩
      apply List.mem_flatten.mpr
      refine ⟨edgePieceVertices Q hn IH e, ?_, ?_⟩
      · apply List.mem_map.mpr
        exact ⟨e, he, rfl⟩
      · rw [edgePieceVertices_eq Q hn IH he]
        apply ((edgePieceData Q hn IH ⟨e, he⟩).support_iff pi).mpr
        left
        exact hdecode.symm.trans (congrArg Q.decodedNC heq.symm)
    · rcases inSubtree_child_decomposition hsub hQ with ⟨D, hD, hsubD⟩
      let d := childDataOfMem hD
      let ep := assignedPair Q hn d
      apply List.mem_flatten.mpr
      refine ⟨edgePieceVertices Q hn IH ep.1, ?_, ?_⟩
      · apply List.mem_map.mpr
        exact ⟨ep.1, ep.2, rfl⟩
      · rw [edgePieceVertices_eq Q hn IH ep.2]
        apply ((edgePieceData Q hn IH ep).support_iff pi).mpr
        right
        exact ⟨d, rfl, by simpa [d] using hsubD⟩

noncomputable def assembledSubtreeCycleCode (Q : CanonicalMatching n)
    (hn : Even n) (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn) :
    CycleCode (NCRAdj n) :=
  (subtreeEdgePieceSystem Q hn IH).toCycleCode

theorem assembledSubtreeCycleCode_support (Q : CanonicalMatching n)
    (hn : Even n) (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn)
    (pi : NC (Finset.univ : Finset (Fin n))) :
    pi ∈ (assembledSubtreeCycleCode Q hn IH).vertices ↔
      InSubtree Q (Encoding.canonicalMatching pi) := by
  change pi ∈ ((cyclicPairs (rankGrayMasks Q)).map
      (edgePieceVertices Q hn IH)).flatten ↔ _
  exact mem_subtreeEdgePieces_iff Q hn IH pi

theorem edgePieceData_eq_singleton_of_unassigned (Q : CanonicalMatching n)
    (hn : Even n) (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn)
    {e : Finset Q.free × Finset Q.free}
    (he : e ∈ cyclicPairs (rankGrayMasks Q))
    (hunassigned : ∀ d : ChildData Q, (assignedPair Q hn d).1 ≠ e) :
    (edgePieceData Q hn IH ⟨e, he⟩).vertices = [Q.decodedNC e.1] := by
  let E := edgePieceData Q hn IH ⟨e, he⟩
  have hall : ∀ pi ∈ E.vertices, pi = Q.decodedNC e.1 := by
    intro pi hpi
    rcases (E.support_iff pi).mp hpi with hbase | ⟨d, hslot, _hsub⟩
    · exact hbase
    · exact (hunassigned d hslot).elim
  cases hL : E.vertices with
  | nil => exact (E.nonempty hL).elim
  | cons a rest =>
      have ha : a = Q.decodedNC e.1 := hall a (by rw [hL]; simp)
      subst a
      have hrest : rest = [] := by
        by_contra hne
        let b := rest.head hne
        have hbmem : b ∈ rest := List.head_mem hne
        have hb : b = Q.decodedNC e.1 := hall b (by rw [hL]; simp [hbmem])
        have hnot := (List.nodup_cons.mp (by simpa [hL] using E.nodup)).1
        exact hnot (by simpa [hb] using hbmem)
      simpa [E, hL, hrest]

theorem outgoing_edgePiece_singleton (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n)
    (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn) :
    edgePieceVertices Q hn IH (outgoingPair Q hQ hn).1 =
      [Q.decodedNC (outgoingPair Q hQ hn).1.1] := by
  rw [edgePieceVertices_eq Q hn IH (outgoingPair Q hQ hn).2]
  exact edgePieceData_eq_singleton_of_unassigned Q hn IH
    (outgoingPair Q hQ hn).2
    (fun d => outgoingPair_not_assigned Q hQ hn d)

theorem assembledSubtreeCycleCode_outgoing (Q : CanonicalMatching n)
    (hQ : Q.1.Nonempty) (hn : Even n)
    (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn) :
    let D := joiningDiamond Q hQ hn
    CyclicEdge (assembledSubtreeCycleCode Q hn IH).vertices
      (Q.decodedNC D.childLower) (Q.decodedNC D.childUpper) := by
  let e := outgoingPair Q hQ hn
  let S := subtreeEdgePieceSystem Q hn IH
  have hedge : CyclicEdge S.toCycleCode.vertices
      (Q.decodedNC e.1.1) (Q.decodedNC e.1.2) := by
    apply S.cyclicEdge_of_singleton_piece e.2
    exact outgoing_edgePiece_singleton Q hQ hn IH
  rcases outgoingPair_orientation Q hQ hn with hdir | hdir
  · simpa [assembledSubtreeCycleCode, S, e, hdir.1, hdir.2] using hedge
  · simpa [assembledSubtreeCycleCode, S, e, hdir.1, hdir.2] using
      cyclicEdge_symm hedge

noncomputable def assembleSubtreeCycle (Q : CanonicalMatching n)
    (hn : Even n) (IH : ∀ d : ChildData Q, SubtreeCycle d.child hn) :
    SubtreeCycle Q hn where
  cycle := assembledSubtreeCycleCode Q hn IH
  support_iff := assembledSubtreeCycleCode_support Q hn IH
  outgoing hQ := assembledSubtreeCycleCode_outgoing Q hQ hn IH

noncomputable def subtreeCycle (Q : CanonicalMatching n) (hn : Even n) :
    SubtreeCycle Q hn := by
  apply assembleSubtreeCycle Q hn
  intro d
  exact subtreeCycle d.child hn
termination_by Q.free.card
decreasing_by
  exact child_free_lt_parent (childData_mem_children d)

theorem inSubtree_root (C : CanonicalMatching n) : InSubtree rootMatching C := by
  induction hcard : C.1.card using Nat.strong_induction_on generalizing C with
  | h k ih =>
      by_cases hC : C.1.Nonempty
      · let P := parent C hC
        have hpCard : P.1.card < C.1.card := by
          have h := parent_card C hC
          change P.1.card + 1 = C.1.card at h
          omega
        have hpRoot : InSubtree rootMatching P :=
          ih P.1.card (by omega) P rfl
        apply Relation.ReflTransGen.head (b := P)
        · exact parentOption_eq_some C hC
        · exact hpRoot
      · have hEmpty : C.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
        have hRoot : C = rootMatching := (eq_rootMatching_iff C).mpr hEmpty
        subst C
        exact Relation.ReflTransGen.refl

noncomputable def rootCycleCode (hn : Even n) : CycleCode (NCRAdj n) :=
  (subtreeCycle rootMatching hn).cycle

theorem rootCycleCode_support (hn : Even n)
    (pi : NC (Finset.univ : Finset (Fin n))) :
    pi ∈ (rootCycleCode hn).vertices := by
  exact ((subtreeCycle rootMatching hn).support_iff pi).mpr
    (inSubtree_root (Encoding.canonicalMatching pi))

theorem NCRefinementGraph_fin_even_geq4_isHamiltonian_petersen
    (hn : Even n) (hn4 : 4 ≤ n) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).IsHamiltonian := by
  let C := rootCycleCode hn
  let p := C.toWalk
  have hp : p.IsHamiltonian := by
    apply C.toWalk_isHamiltonian_of_mem
    exact rootCycleCode_support hn
  have hcard : 3 ≤ Fintype.card
      (NC (Finset.univ : Finset (Fin n))) := by
    rw [NC.card_NC_univ_fin_eq_catalan]
    calc
      3 ≤ catalan 3 := by rw [NC.catalan_three]; omega
      _ ≤ catalan n := Nat.catalan_mono (by omega)
  exact SimpleGraph.Walk.IsHamiltonian.isHamiltonian_of_adj_endpoints
    hcard hp (by simpa [p, C] using C.closing)

theorem NCRefinementGraph_fin_even_geq8_isHamiltonian_petersen
    (hn : Even n) (hn8 : 8 ≤ n) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).IsHamiltonian :=
  NCRefinementGraph_fin_even_geq4_isHamiltonian_petersen hn (by omega)

end Global
end Petersen

namespace NC

/-- Every even-order Kreweras refinement graph of order at least four is
Hamiltonian, by the Petersen Boolean-block cycle joining construction. -/
theorem NCRefinementGraph_fin_even_geq4_isHamiltonian_petersen
    (n : ℕ) (hn : Even n) (hn4 : 4 ≤ n) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).IsHamiltonian := by
  letI : NeZero n := ⟨by omega⟩
  exact Petersen.Global.NCRefinementGraph_fin_even_geq4_isHamiltonian_petersen
    hn hn4

/-- Backward-compatible restriction of the uniform theorem to `n >= 8`. -/
theorem NCRefinementGraph_fin_even_geq8_isHamiltonian
    (n : ℕ) (hn : Even n) (hn8 : 8 ≤ n) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).IsHamiltonian := by
  letI : NeZero n := ⟨by omega⟩
  exact NCRefinementGraph_fin_even_geq4_isHamiltonian_petersen n hn (by omega)

end NC
end Hamilton.Infrastructure
