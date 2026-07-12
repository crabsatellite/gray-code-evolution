/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCType
import Hamilton.Infrastructure.MergeBlocks
import Hamilton.Infrastructure.Adjacency
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Petersen Boolean-block coordinates

This file gives the concrete coordinates used by Petersen's Boolean
decomposition.  A canonical block is a noncrossing partial matching on the
non-root points of `Fin n`.  A mask chooses which unmatched non-root points
are hopped.  The function `decodeKey` assigns every point to its resulting
partition block; `decodedFinpartition` is the partition into equal-key
classes.

Nothing in this file assumes Hamiltonicity or endpoint steering.
-/

namespace Hamilton.Infrastructure
namespace Petersen

variable {n : Nat} [NeZero n]

/-- Total minimum of a finite block; the empty fallback is irrelevant for
partition blocks. -/
noncomputable def blockMin (B : Finset (Fin n)) : Fin n :=
  if h : B.Nonempty then B.min' h else 0

/-- Total maximum of a finite block; the empty fallback is irrelevant for
partition blocks. -/
noncomputable def blockMax (B : Finset (Fin n)) : Fin n :=
  if h : B.Nonempty then B.max' h else 0

@[simp]
theorem blockMin_eq_min' (B : Finset (Fin n)) (h : B.Nonempty) :
    blockMin B = B.min' h := by
  simp [blockMin, h]

@[simp]
theorem blockMax_eq_max' (B : Finset (Fin n)) (h : B.Nonempty) :
    blockMax B = B.max' h := by
  simp [blockMax, h]

theorem blockMin_mem (B : Finset (Fin n)) (h : B.Nonempty) : blockMin B ∈ B := by
  rw [blockMin_eq_min' B h]
  exact B.min'_mem h

theorem blockMax_mem (B : Finset (Fin n)) (h : B.Nonempty) : blockMax B ∈ B := by
  rw [blockMax_eq_max' B h]
  exact B.max'_mem h

theorem blockMin_le (B : Finset (Fin n)) (h : B.Nonempty) {x : Fin n}
    (hx : x ∈ B) : blockMin B ≤ x := by
  rw [blockMin_eq_min' B h]
  exact B.min'_le x hx

theorem le_blockMax (B : Finset (Fin n)) (h : B.Nonempty) {x : Fin n}
    (hx : x ∈ B) : x ≤ blockMax B := by
  rw [blockMax_eq_max' B h]
  exact B.le_max' x hx

/-- The extremal chord retained from a non-root nonsingleton block. -/
noncomputable def blockChord (B : Finset (Fin n)) : Fin n × Fin n :=
  (blockMin B, blockMax B)

/-- The two endpoints of an ordered chord. -/
def chordEnds {n : Nat} (e : Fin n × Fin n) : Finset (Fin n) :=
  {e.1, e.2}

/-- A finite set of ordered chords is a canonical Petersen matching when the
root is unused, chord endpoints are disjoint, and chords do not cross. -/
def IsCanonicalMatching {n : Nat} [NeZero n]
    (Q : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ Q, (0 : Fin n) < e.1 ∧ e.1 < e.2) ∧
  (∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (chordEnds e) (chordEnds f)) ∧
  (∀ e ∈ Q, ∀ f ∈ Q, e.1 < f.1 →
    ¬ (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2))

noncomputable instance {n : Nat} [NeZero n] (Q : Finset (Fin n × Fin n)) :
    Decidable (IsCanonicalMatching Q) := Classical.dec _

/-- Canonical partial matchings indexing Petersen Boolean blocks. -/
def CanonicalMatching (n : Nat) [NeZero n] :=
  {Q : Finset (Fin n × Fin n) // IsCanonicalMatching Q}

instance {n : Nat} [NeZero n] : DecidableEq (CanonicalMatching n) :=
  Subtype.instDecidableEq

noncomputable instance {n : Nat} [NeZero n] : Fintype (CanonicalMatching n) :=
  by
    unfold CanonicalMatching
    letI : DecidablePred (IsCanonicalMatching (n := n)) := fun Q => Classical.dec _
    exact Subtype.fintype _

namespace CanonicalMatching

/-- Points used as endpoints of matching chords. -/
def endpoints (Q : CanonicalMatching n) : Finset (Fin n) :=
  Q.1.biUnion chordEnds

/-- The unmatched non-root points, in ambient order. -/
def free (Q : CanonicalMatching n) : Finset (Fin n) :=
  Finset.univ.filter fun x => x ≠ 0 ∧ x ∉ Q.endpoints

@[simp]
theorem mem_endpoints_iff (Q : CanonicalMatching n) (x : Fin n) :
    x ∈ Q.endpoints ↔ ∃ e ∈ Q.1, x = e.1 ∨ x = e.2 := by
  simp [endpoints, chordEnds]

@[simp]
theorem mem_free_iff (Q : CanonicalMatching n) (x : Fin n) :
    x ∈ Q.free ↔ x ≠ 0 ∧ x ∉ Q.endpoints := by
  simp [free]

theorem root_not_mem_endpoints (Q : CanonicalMatching n) :
    (0 : Fin n) ∉ Q.endpoints := by
  rw [mem_endpoints_iff]
  rintro ⟨e, he, h | h⟩
  · exact (Q.2.1 e he).1.ne' h.symm
  · exact ((Q.2.1 e he).1.trans (Q.2.1 e he).2).ne' h.symm

theorem root_not_mem_free (Q : CanonicalMatching n) :
    (0 : Fin n) ∉ Q.free := by
  simp

/-- Left endpoints of chords incident with `x`.  Matching disjointness will
make this finset have cardinality at most one. -/
def incidentLefts (Q : CanonicalMatching n) (x : Fin n) : Finset (Fin n) :=
  (Q.1.filter fun e => x = e.1 ∨ x = e.2).image Prod.fst

@[simp]
theorem mem_incidentLefts_iff (Q : CanonicalMatching n) (x a : Fin n) :
    a ∈ Q.incidentLefts x ↔
      ∃ e ∈ Q.1, (x = e.1 ∨ x = e.2) ∧ e.1 = a := by
  simp [incidentLefts]

theorem chord_eq_of_common_endpoint (Q : CanonicalMatching n)
    {e f : Fin n × Fin n} (he : e ∈ Q.1) (hf : f ∈ Q.1)
    {x : Fin n} (hxe : x ∈ chordEnds e) (hxf : x ∈ chordEnds f) :
    e = f := by
  by_contra hne
  have hd := Q.2.2.1 e he f hf hne
  exact (Finset.disjoint_left.mp hd hxe) hxf

theorem incidentLefts_eq_singleton_of_mem (Q : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ Q.1) {x : Fin n}
    (hx : x = e.1 ∨ x = e.2) :
    Q.incidentLefts x = {e.1} := by
  ext a
  rw [mem_incidentLefts_iff]
  constructor
  · rintro ⟨f, hf, hxf, rfl⟩
    have hxe : x ∈ chordEnds e := by simpa [chordEnds, hx]
    have hxff : x ∈ chordEnds f := by simpa [chordEnds, hxf]
    have hef := Q.chord_eq_of_common_endpoint he hf hxe hxff
    simpa [hef]
  · intro ha
    have hae : a = e.1 := by simpa using ha
    exact ⟨e, he, hx, hae.symm⟩

/-- The left endpoint of the chord incident with `x`; it is `x` when `x` is
unmatched. -/
noncomputable def endpointKey (Q : CanonicalMatching n) (x : Fin n) : Fin n :=
  if h : (Q.incidentLefts x).Nonempty then (Q.incidentLefts x).max' h else x

theorem endpointKey_eq_left_of_mem (Q : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ Q.1) {x : Fin n}
    (hx : x = e.1 ∨ x = e.2) :
    Q.endpointKey x = e.1 := by
  rw [endpointKey, Q.incidentLefts_eq_singleton_of_mem he hx]
  simp

theorem endpointKey_left (Q : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ Q.1) :
    Q.endpointKey e.1 = e.1 :=
  Q.endpointKey_eq_left_of_mem he (Or.inl rfl)

theorem endpointKey_right (Q : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ Q.1) :
    Q.endpointKey e.2 = e.1 :=
  Q.endpointKey_eq_left_of_mem he (Or.inr rfl)

theorem endpointKey_eq_self_of_not_mem (Q : CanonicalMatching n) {x : Fin n}
    (hx : x ∉ Q.endpoints) : Q.endpointKey x = x := by
  rw [endpointKey, dif_neg]
  intro hne
  obtain ⟨a, ha⟩ := hne
  rw [mem_incidentLefts_iff] at ha
  obtain ⟨e, he, hxe, _⟩ := ha
  exact hx ((Q.mem_endpoints_iff x).2 ⟨e, he, hxe⟩)

/-- Ordered matching chords are either disjoint or properly nested. -/
theorem chord_disjoint_or_nested (Q : CanonicalMatching n)
    {e f : Fin n × Fin n} (he : e ∈ Q.1) (hf : f ∈ Q.1)
    (hef : e.1 < f.1) :
    e.2 < f.1 ∨ f.2 < e.2 := by
  have hef_ne : e ≠ f := by
    intro h
    simpa [h] using hef
  have hd := Q.2.2.1 e he f hf hef_ne
  have her_ne_fl : e.2 ≠ f.1 := by
    intro h
    have hnot := Finset.disjoint_left.mp hd
      (show e.2 ∈ chordEnds e by simp [chordEnds])
    exact hnot (show e.2 ∈ chordEnds f by simp [chordEnds, h])
  rcases lt_or_gt_of_ne her_ne_fl with h | h
  · exact Or.inl h
  · right
    have hn : ¬ e.2 < f.2 := by
      intro herf
      exact Q.2.2.2 e he f hf hef ⟨hef, h, herf⟩
    have hle : f.2 ≤ e.2 := le_of_not_gt hn
    have hrights : f.2 ≠ e.2 := by
      intro hEq
      have hnot := Finset.disjoint_left.mp hd
        (show f.2 ∈ chordEnds e by simp [chordEnds, hEq])
      exact hnot (show f.2 ∈ chordEnds f by simp [chordEnds])
    exact lt_of_le_of_ne hle hrights

/-- Left endpoints of chords whose open interval contains `x`. -/
def precedingLefts (Q : CanonicalMatching n) (x : Fin n) : Finset (Fin n) :=
  (Q.1.filter fun e => e.1 < x ∧ x < e.2).image Prod.fst

@[simp]
theorem mem_precedingLefts_iff (Q : CanonicalMatching n) (x a : Fin n) :
    a ∈ Q.precedingLefts x ↔
      ∃ e ∈ Q.1, (e.1 < x ∧ x < e.2) ∧ e.1 = a := by
  simp [precedingLefts]

/-- The anchor of a free point: the innermost matching chord containing it,
or the root point when it lies in no matching chord. -/
noncomputable def anchorKey (Q : CanonicalMatching n) (x : Fin n) : Fin n :=
  if h : (Q.precedingLefts x).Nonempty then (Q.precedingLefts x).max' h else 0

theorem anchorKey_eq_root_or_chord (Q : CanonicalMatching n) (x : Fin n) :
    Q.anchorKey x = 0 ∨
      ∃ e ∈ Q.1, (e.1 < x ∧ x < e.2) ∧ e.1 = Q.anchorKey x := by
  rw [anchorKey]
  split_ifs with h
  · right
    have hm := (Q.precedingLefts x).max'_mem h
    exact (Q.mem_precedingLefts_iff x _).mp hm
  · exact Or.inl rfl

theorem left_le_anchorKey_of_contains (Q : CanonicalMatching n)
    {e : Fin n × Fin n} (he : e ∈ Q.1) {x : Fin n}
    (hex : e.1 < x) (hxe : x < e.2) :
    e.1 ≤ Q.anchorKey x := by
  have hmem : e.1 ∈ Q.precedingLefts x :=
    (Q.mem_precedingLefts_iff x e.1).2 ⟨e, he, ⟨hex, hxe⟩, rfl⟩
  have hne : (Q.precedingLefts x).Nonempty := ⟨e.1, hmem⟩
  rw [anchorKey, dif_pos hne]
  exact Finset.le_max' _ _ hmem

theorem anchorKey_lt (Q : CanonicalMatching n) {x : Fin n}
    (hx0 : Q.anchorKey x ≠ 0) : Q.anchorKey x < x := by
  rcases Q.anchorKey_eq_root_or_chord x with h | ⟨e, _he, hex, heq⟩
  · exact (hx0 h).elim
  · simpa [← heq] using hex.1

theorem endpointKey_le (Q : CanonicalMatching n) (x : Fin n) :
    Q.endpointKey x ≤ x := by
  by_cases hx : x ∈ Q.endpoints
  · obtain ⟨e, he, hxe⟩ := (Q.mem_endpoints_iff x).1 hx
    rw [Q.endpointKey_eq_left_of_mem he hxe]
    rcases hxe with h | h
    · exact le_of_eq h.symm
    · rw [h]
      exact le_of_lt (Q.2.1 e he).2
  · rw [Q.endpointKey_eq_self_of_not_mem hx]

theorem anchorKey_le (Q : CanonicalMatching n) (x : Fin n) :
    Q.anchorKey x ≤ x := by
  by_cases h0 : Q.anchorKey x = 0
  · rw [h0]
    exact Fin.zero_le _
  · exact le_of_lt (Q.anchorKey_lt h0)

/-- Underlying points selected by a mask on the free-point subtype. -/
def maskPoints (Q : CanonicalMatching n) (A : Finset Q.free) : Finset (Fin n) :=
  A.image (fun x => x.1)

/-- Block key of a point in the decoded Petersen state.  Chord endpoints use
their chord's left endpoint, selected free points use their anchor, and every
other point remains its own key. -/
noncomputable def decodeKey (Q : CanonicalMatching n) (A : Finset Q.free)
    (x : Fin n) : Fin n :=
  if x ∈ Q.endpoints then Q.endpointKey x
  else if x ∈ Q.maskPoints A then Q.anchorKey x
  else x

theorem decodeKey_le (Q : CanonicalMatching n) (A : Finset Q.free) (x : Fin n) :
    Q.decodeKey A x ≤ x := by
  unfold decodeKey
  split_ifs
  · exact Q.endpointKey_le x
  · exact Q.anchorKey_le x
  · exact le_rfl

theorem chord_eq_of_left_eq (Q : CanonicalMatching n)
    {e f : Fin n × Fin n} (he : e ∈ Q.1) (hf : f ∈ Q.1)
    (hleft : e.1 = f.1) : e = f := by
  apply Q.chord_eq_of_common_endpoint he hf (x := e.1)
  · simp [chordEnds]
  · simp [chordEnds, hleft]

/-- If two distinct ordered points decode to the same block, that block is
either the root block or is based at the left endpoint of a matching chord. -/
theorem commonKey_root_or_chord (Q : CanonicalMatching n) (A : Finset Q.free)
    {x y : Fin n} (hxy : x < y)
    (hkey : Q.decodeKey A x = Q.decodeKey A y) :
    Q.decodeKey A x = 0 ∨
      ∃ e ∈ Q.1, e.1 = Q.decodeKey A x := by
  have hnotfixed : Q.decodeKey A y ≠ y := by
    intro hfixed
    have hle := Q.decodeKey_le A x
    rw [hkey, hfixed] at hle
    exact (not_le_of_gt hxy) hle
  unfold decodeKey at hkey hnotfixed
  by_cases hend : y ∈ Q.endpoints
  · rw [if_pos hend] at hkey hnotfixed
    obtain ⟨e, he, hye⟩ := (Q.mem_endpoints_iff y).1 hend
    right
    refine ⟨e, he, ?_⟩
    rw [Q.endpointKey_eq_left_of_mem he hye] at hkey
    exact hkey.symm
  · rw [if_neg hend] at hkey hnotfixed
    by_cases hmask : y ∈ Q.maskPoints A
    · rw [if_pos hmask] at hkey hnotfixed
      rcases Q.anchorKey_eq_root_or_chord y with hroot | ⟨e, he, _hy, heq⟩
      · exact Or.inl (hkey.trans hroot)
      · exact Or.inr ⟨e, he, heq.trans hkey.symm⟩
    · rw [if_neg hmask] at hkey hnotfixed
      exact (hnotfixed rfl).elim

/-- Every point in a chord block lies in that chord's closed interval. -/
theorem point_in_chord_hull (Q : CanonicalMatching n) (A : Finset Q.free)
    {e : Fin n × Fin n} (he : e ∈ Q.1) {x : Fin n}
    (hkey : Q.decodeKey A x = e.1) : e.1 ≤ x ∧ x ≤ e.2 := by
  by_cases hend : x ∈ Q.endpoints
  · obtain ⟨f, hf, hxf⟩ := (Q.mem_endpoints_iff x).1 hend
    have hleft : f.1 = e.1 := by
      rw [decodeKey, if_pos hend, Q.endpointKey_eq_left_of_mem hf hxf] at hkey
      exact hkey
    have hfe : f = e := Q.chord_eq_of_left_eq hf he hleft
    subst f
    rcases hxf with rfl | rfl
    · exact ⟨le_rfl, le_of_lt (Q.2.1 e he).2⟩
    · exact ⟨le_of_lt (Q.2.1 e he).2, le_rfl⟩
  · by_cases hmask : x ∈ Q.maskPoints A
    · have hanchor : Q.anchorKey x = e.1 := by
        rw [decodeKey, if_neg hend, if_pos hmask] at hkey
        exact hkey
      rcases Q.anchorKey_eq_root_or_chord x with hroot | ⟨f, hf, hfx, hfkey⟩
      · have he0 : e.1 = 0 := hanchor.symm.trans hroot
        exact ((Q.2.1 e he).1.ne' he0).elim
      · have hleft : f.1 = e.1 := hfkey.trans hanchor
        have hfe : f = e := Q.chord_eq_of_left_eq hf he hleft
        subst f
        exact ⟨le_of_lt hfx.1, le_of_lt hfx.2⟩
    · rw [decodeKey, if_neg hend, if_neg hmask] at hkey
      rw [hkey]
      exact ⟨le_rfl, le_of_lt (Q.2.1 e he).2⟩

/-- An outer chord block has no point strictly inside a nested chord. -/
theorem point_avoids_nested_chord (Q : CanonicalMatching n) (A : Finset Q.free)
    {e f : Fin n × Fin n} (he : e ∈ Q.1) (hf : f ∈ Q.1)
    (hleft : e.1 < f.1) (hright : f.2 < e.2) {x : Fin n}
    (hkey : Q.decodeKey A x = e.1) :
    ¬ (f.1 < x ∧ x < f.2) := by
  intro hinside
  by_cases hend : x ∈ Q.endpoints
  · obtain ⟨g, hg, hxg⟩ := (Q.mem_endpoints_iff x).1 hend
    have hgleft : g.1 = e.1 := by
      rw [decodeKey, if_pos hend, Q.endpointKey_eq_left_of_mem hg hxg] at hkey
      exact hkey
    have hge : g = e := Q.chord_eq_of_left_eq hg he hgleft
    subst g
    rcases hxg with rfl | rfl
    · exact (not_lt_of_ge (le_of_lt hleft)) hinside.1
    · exact (not_lt_of_ge (le_of_lt hright)) hinside.2
  · by_cases hmask : x ∈ Q.maskPoints A
    · have hanchor : Q.anchorKey x = e.1 := by
        rw [decodeKey, if_neg hend, if_pos hmask] at hkey
        exact hkey
      have hle := Q.left_le_anchorKey_of_contains hf hinside.1 hinside.2
      rw [hanchor] at hle
      exact (not_le_of_gt hleft) hle
    · rw [decodeKey, if_neg hend, if_neg hmask] at hkey
      rw [hkey] at hinside
      exact (not_lt_of_ge (le_of_lt hleft)) hinside.1

/-- A root-block point lies in no matching chord's open interval. -/
theorem root_point_avoids_chord (Q : CanonicalMatching n) (A : Finset Q.free)
    {e : Fin n × Fin n} (he : e ∈ Q.1) {x : Fin n}
    (hkey : Q.decodeKey A x = 0) :
    ¬ (e.1 < x ∧ x < e.2) := by
  intro hinside
  by_cases hend : x ∈ Q.endpoints
  · obtain ⟨f, hf, hxf⟩ := (Q.mem_endpoints_iff x).1 hend
    have hf0 : f.1 = 0 := by
      rw [decodeKey, if_pos hend, Q.endpointKey_eq_left_of_mem hf hxf] at hkey
      exact hkey
    exact (Q.2.1 f hf).1.ne' hf0
  · by_cases hmask : x ∈ Q.maskPoints A
    · have hanchor : Q.anchorKey x = 0 := by
        rw [decodeKey, if_neg hend, if_pos hmask] at hkey
        exact hkey
      have hle := Q.left_le_anchorKey_of_contains he hinside.1 hinside.2
      rw [hanchor] at hle
      exact (not_le_of_gt (Q.2.1 e he).1) hle
    · rw [decodeKey, if_neg hend, if_neg hmask] at hkey
      rw [hkey] at hinside
      exact (not_lt_of_ge (Fin.zero_le _)) hinside.1

/-- The equivalence relation induced by equal decoded block keys. -/
noncomputable def decodeSetoid (Q : CanonicalMatching n) (A : Finset Q.free) :
    Setoid (Fin n) := Setoid.ker (Q.decodeKey A)

noncomputable instance decodeSetoidDecidableRel (Q : CanonicalMatching n)
    (A : Finset Q.free) : DecidableRel (Q.decodeSetoid A).r :=
  Classical.decRel _

/-- The actual set partition represented by a matching and a hop mask. -/
noncomputable def decodedFinpartition (Q : CanonicalMatching n)
    (A : Finset Q.free) : Finpartition (Finset.univ : Finset (Fin n)) :=
  Finpartition.ofSetoid (Q.decodeSetoid A)

@[simp]
theorem mem_part_decodedFinpartition_iff (Q : CanonicalMatching n)
    (A : Finset Q.free) (x y : Fin n) :
    y ∈ (Q.decodedFinpartition A).part x ↔
      Q.decodeKey A x = Q.decodeKey A y := by
  exact Finpartition.mem_part_ofSetoid_iff_rel

/-- The key-class partition of every canonical matching and mask is genuinely
noncrossing.  This is the geometric core of the Petersen decoder. -/
theorem decodedFinpartition_isNoncrossing (Q : CanonicalMatching n)
    (A : Finset Q.free) : IsNoncrossing (Q.decodedFinpartition A) := by
  let P := Q.decodedFinpartition A
  intro B₁ hB₁ B₂ hB₂ i j k l hij hjk hkl hi hk hj hl
  have hik_mem : k ∈ P.part i := by
    rw [P.part_eq_of_mem hB₁ hi]
    exact hk
  have hjl_mem : l ∈ P.part j := by
    rw [P.part_eq_of_mem hB₂ hj]
    exact hl
  have hik : Q.decodeKey A i = Q.decodeKey A k :=
    (Q.mem_part_decodedFinpartition_iff A i k).1 hik_mem
  have hjl : Q.decodeKey A j = Q.decodeKey A l :=
    (Q.mem_part_decodedFinpartition_iff A j l).1 hjl_mem
  have finish (hijKey : Q.decodeKey A i = Q.decodeKey A j) : B₁ = B₂ := by
    have hji : j ∈ P.part i :=
      (Q.mem_part_decodedFinpartition_iff A i j).2 hijKey
    rw [P.part_eq_of_mem hB₁ hi] at hji
    exact P.eq_of_mem_parts hB₁ hB₂ hji hj
  have hik_order : i < k := hij.trans hjk
  have hjl_order : j < l := hjk.trans hkl
  rcases Q.commonKey_root_or_chord A hik_order hik with
      hroot₁ | ⟨e, he, heKey⟩
  · rcases Q.commonKey_root_or_chord A hjl_order hjl with
        hroot₂ | ⟨f, hf, hfKey⟩
    · exact finish (hroot₁.trans hroot₂.symm)
    · have hkRoot : Q.decodeKey A k = 0 := hik.symm.trans hroot₁
      have hjHull := Q.point_in_chord_hull A hf hfKey.symm
      have hlHull := Q.point_in_chord_hull A hf (hjl.symm.trans hfKey.symm)
      exact ((Q.root_point_avoids_chord A hf hkRoot)
        ⟨lt_of_le_of_lt hjHull.1 hjk, lt_of_lt_of_le hkl hlHull.2⟩).elim
  · rcases Q.commonKey_root_or_chord A hjl_order hjl with
        hroot₂ | ⟨f, hf, hfKey⟩
    · have hjRoot : Q.decodeKey A j = 0 := hroot₂
      have hiHull := Q.point_in_chord_hull A he heKey.symm
      have hkHull := Q.point_in_chord_hull A he (hik.symm.trans heKey.symm)
      exact ((Q.root_point_avoids_chord A he hjRoot)
        ⟨lt_of_le_of_lt hiHull.1 hij, lt_of_lt_of_le hjk hkHull.2⟩).elim
    · by_cases hef : e = f
      · subst f
        exact finish (heKey.symm.trans hfKey)
      · have hleft_ne : e.1 ≠ f.1 := by
          intro h
          exact hef (Q.chord_eq_of_left_eq he hf h)
        rcases lt_or_gt_of_ne hleft_ne with hefl | hfel
        · rcases Q.chord_disjoint_or_nested he hf hefl with hdisj | hnested
          · have hkHull := Q.point_in_chord_hull A he (hik.symm.trans heKey.symm)
            have hjHull := Q.point_in_chord_hull A hf hfKey.symm
            exact ((not_lt_of_ge
              (le_trans hjHull.1 (le_of_lt hjk)))
              (lt_of_le_of_lt hkHull.2 hdisj)).elim
          · have hkKey : Q.decodeKey A k = e.1 := hik.symm.trans heKey.symm
            have hjHull := Q.point_in_chord_hull A hf hfKey.symm
            have hlHull := Q.point_in_chord_hull A hf (hjl.symm.trans hfKey.symm)
            exact ((Q.point_avoids_nested_chord A he hf hefl hnested hkKey)
              ⟨lt_of_le_of_lt hjHull.1 hjk, lt_of_lt_of_le hkl hlHull.2⟩).elim
        · rcases Q.chord_disjoint_or_nested hf he hfel with hdisj | hnested
          · have hiHull := Q.point_in_chord_hull A he heKey.symm
            have hlHull := Q.point_in_chord_hull A hf (hjl.symm.trans hfKey.symm)
            exact ((not_lt_of_ge
              (le_trans hiHull.1 (le_of_lt (hij.trans (hjk.trans hkl)))))
              (lt_of_le_of_lt hlHull.2 hdisj)).elim
          · have hjKey : Q.decodeKey A j = f.1 := hfKey.symm
            have hiHull := Q.point_in_chord_hull A he heKey.symm
            have hkHull := Q.point_in_chord_hull A he (hik.symm.trans heKey.symm)
            exact ((Q.point_avoids_nested_chord A hf he hfel hnested hjKey)
              ⟨lt_of_le_of_lt hiHull.1 hij, lt_of_lt_of_le hjk hkHull.2⟩).elim

/-- Petersen decoding as an actual vertex of the Kreweras refinement graph. -/
noncomputable def decodedNC (Q : CanonicalMatching n) (A : Finset Q.free) :
    NC (Finset.univ : Finset (Fin n)) :=
  ⟨Q.decodedFinpartition A, Q.decodedFinpartition_isNoncrossing A⟩

@[simp]
theorem decodedNC_val (Q : CanonicalMatching n) (A : Finset Q.free) :
    (Q.decodedNC A).val = Q.decodedFinpartition A := rfl

@[simp]
theorem decodeKey_root (Q : CanonicalMatching n) (A : Finset Q.free) :
    Q.decodeKey A 0 = 0 := by
  rw [decodeKey, if_neg (root_not_mem_endpoints Q)]
  rw [if_neg]
  intro h
  rw [maskPoints, Finset.mem_image] at h
  obtain ⟨y, _hy, hy0⟩ := h
  exact ((Q.mem_free_iff y.1).mp y.2).1 hy0

theorem maskPoints_subset_free (Q : CanonicalMatching n) (A : Finset Q.free) :
    Q.maskPoints A ⊆ Q.free := by
  intro x hx
  rw [maskPoints, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact y.2

end CanonicalMatching

namespace Encoding

variable {n : Nat} [NeZero n]

theorem finpartition_eq_of_part_eq {α : Type*} [DecidableEq α]
    {s : Finset α} {P R : Finpartition s}
    (hpart : ∀ x ∈ s, P.part x = R.part x) : P = R := by
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨x, hxB⟩ := P.nonempty_of_mem_parts hB
    have hxs : x ∈ s := P.le hB hxB
    have hPB : P.part x = B := P.part_eq_of_mem hB hxB
    have hRB : R.part x = B := (hpart x hxs).symm.trans hPB
    rw [← hRB]
    exact R.part_mem.mpr hxs
  · intro hB
    obtain ⟨x, hxB⟩ := R.nonempty_of_mem_parts hB
    have hxs : x ∈ s := R.le hB hxB
    have hRB : R.part x = B := R.part_eq_of_mem hB hxB
    have hPB : P.part x = B := (hpart x hxs).trans hRB
    rw [← hPB]
    exact P.part_mem.mpr hxs

theorem mergeBlocks_part_eq {α : Type*} [DecidableEq α] {s : Finset α}
    (P : Finpartition s) {B₁ B₂ : Finset α}
    (hB₁ : B₁ ∈ P.parts) (hB₂ : B₂ ∈ P.parts) (hne : B₁ ≠ B₂)
    {x : α} (hxs : x ∈ s) :
    (P.mergeBlocks hB₁ hB₂ hne).part x =
      if x ∈ B₁ ∪ B₂ then B₁ ∪ B₂ else P.part x := by
  by_cases hx : x ∈ B₁ ∪ B₂
  · rw [if_pos hx]
    apply (P.mergeBlocks hB₁ hB₂ hne).part_eq_of_mem
      (Finset.mem_insert_self _ _)
    exact hx
  · rw [if_neg hx]
    have hPxmem : P.part x ∈ P.parts := P.part_mem.mpr hxs
    have hPx_ne_B₁ : P.part x ≠ B₁ := by
      intro h
      have hxP := P.mem_part hxs
      rw [h] at hxP
      exact hx (Finset.mem_union_left _ hxP)
    have hPx_ne_B₂ : P.part x ≠ B₂ := by
      intro h
      have hxP := P.mem_part hxs
      rw [h] at hxP
      exact hx (Finset.mem_union_right _ hxP)
    apply (P.mergeBlocks hB₁ hB₂ hne).part_eq_of_mem
    · rw [Finpartition.mergeBlocks_parts, Finset.mem_insert]
      right
      exact Finset.mem_erase.mpr
        ⟨hPx_ne_B₂, Finset.mem_erase.mpr ⟨hPx_ne_B₁, hPxmem⟩⟩
    · exact P.mem_part hxs

theorem decodeKey_idempotent (Q : CanonicalMatching n) (A : Finset Q.free)
    (x : Fin n) : Q.decodeKey A (Q.decodeKey A x) = Q.decodeKey A x := by
  by_cases hend : x ∈ Q.endpoints
  · obtain ⟨e, he, hxe⟩ := (Q.mem_endpoints_iff x).1 hend
    have hkey : Q.decodeKey A x = e.1 := by
      rw [CanonicalMatching.decodeKey, if_pos hend,
        Q.endpointKey_eq_left_of_mem he hxe]
    rw [hkey]
    have hleftEnd : e.1 ∈ Q.endpoints :=
      (Q.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩
    rw [CanonicalMatching.decodeKey, if_pos hleftEnd, Q.endpointKey_left he]
  · by_cases hmask : x ∈ Q.maskPoints A
    · have hkey : Q.decodeKey A x = Q.anchorKey x := by
        rw [CanonicalMatching.decodeKey, if_neg hend, if_pos hmask]
      rw [hkey]
      rcases Q.anchorKey_eq_root_or_chord x with hroot | ⟨e, he, _hex, heq⟩
      · rw [hroot, Q.decodeKey_root]
      · rw [← heq]
        have hleftEnd : e.1 ∈ Q.endpoints :=
          (Q.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩
        rw [CanonicalMatching.decodeKey, if_pos hleftEnd, Q.endpointKey_left he]
    · have hxkey : Q.decodeKey A x = x := by
        rw [CanonicalMatching.decodeKey, if_neg hend, if_neg hmask]
      exact congrArg (Q.decodeKey A) hxkey

theorem decodeKey_mem_own_part (Q : CanonicalMatching n) (A : Finset Q.free)
    (x : Fin n) :
    Q.decodeKey A x ∈ (Q.decodedFinpartition A).part x := by
  rw [Q.mem_part_decodedFinpartition_iff]
  exact (decodeKey_idempotent Q A x).symm

theorem chord_endpoints_mem_decoded_part (Q : CanonicalMatching n)
    (A : Finset Q.free) {e : Fin n × Fin n} (he : e ∈ Q.1) :
    e.1 ∈ (Q.decodedFinpartition A).part e.1 ∧
      e.2 ∈ (Q.decodedFinpartition A).part e.1 := by
  constructor
  · exact (Q.decodedFinpartition A).mem_part (Finset.mem_univ e.1)
  · rw [Q.mem_part_decodedFinpartition_iff,
      CanonicalMatching.decodeKey, if_pos
        ((Q.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩),
      Q.endpointKey_left he,
      CanonicalMatching.decodeKey, if_pos
        ((Q.mem_endpoints_iff e.2).2 ⟨e, he, Or.inr rfl⟩),
      Q.endpointKey_right he]

theorem decoded_chord_part_extrema (Q : CanonicalMatching n)
    (A : Finset Q.free) {e : Fin n × Fin n} (he : e ∈ Q.1) :
    let B := (Q.decodedFinpartition A).part e.1
    blockMin B = e.1 ∧ blockMax B = e.2 ∧ 2 ≤ B.card := by
  let B := (Q.decodedFinpartition A).part e.1
  have hends := chord_endpoints_mem_decoded_part Q A he
  have hBne : B.Nonempty := ⟨e.1, hends.1⟩
  have hmin : blockMin B = e.1 := by
    apply le_antisymm
    · exact blockMin_le B hBne hends.1
    · have hminMem := blockMin_mem B hBne
      have hkey : Q.decodeKey A (blockMin B) = e.1 := by
        have := (Q.mem_part_decodedFinpartition_iff A e.1 (blockMin B)).1 hminMem
        rw [CanonicalMatching.decodeKey,
          if_pos ((Q.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩),
          Q.endpointKey_left he] at this
        exact this.symm
      exact (Q.point_in_chord_hull A he hkey).1
  have hmax : blockMax B = e.2 := by
    apply le_antisymm
    · have hmaxMem := blockMax_mem B hBne
      have hkey : Q.decodeKey A (blockMax B) = e.1 := by
        have := (Q.mem_part_decodedFinpartition_iff A e.1 (blockMax B)).1 hmaxMem
        rw [CanonicalMatching.decodeKey,
          if_pos ((Q.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩),
          Q.endpointKey_left he] at this
        exact this.symm
      exact (Q.point_in_chord_hull A he hkey).2
    · exact le_blockMax B hBne hends.2
  refine ⟨hmin, hmax, ?_⟩
  have hpair : ({e.1, e.2} : Finset (Fin n)) ⊆ B := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hends.1
    · exact hends.2
  rw [← Finset.card_pair (Q.2.1 e he).2.ne]
  exact Finset.card_le_card hpair

theorem chordEnds_blockChord_subset (B : Finset (Fin n)) (hB : B.Nonempty) :
    chordEnds (blockChord B) ⊆ B := by
  intro x hx
  simp only [chordEnds, blockChord, blockMin_eq_min' B hB,
    blockMax_eq_max' B hB, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact B.min'_mem hB
  · exact B.max'_mem hB

/-- Nonsingleton non-root blocks of an NC partition. -/
noncomputable def chordBlocks
    (π : NC (Finset.univ : Finset (Fin n))) : Finset (Finset (Fin n)) :=
  π.val.parts.filter fun B => blockMin B ≠ 0 ∧ 2 ≤ B.card

/-- The extremal matching extracted from an NC partition. -/
noncomputable def canonicalEdges
    (π : NC (Finset.univ : Finset (Fin n))) : Finset (Fin n × Fin n) :=
  (chordBlocks π).image blockChord

theorem canonicalEdges_isCanonicalMatching
    (π : NC (Finset.univ : Finset (Fin n))) :
    IsCanonicalMatching (canonicalEdges π) := by
  constructor
  · intro e he
    rw [canonicalEdges, Finset.mem_image] at he
    obtain ⟨B, hB, rfl⟩ := he
    rw [chordBlocks, Finset.mem_filter] at hB
    have hBne : B.Nonempty := π.val.nonempty_of_mem_parts hB.1
    have hmin0 := hB.2.1
    rw [blockMin_eq_min' B hBne] at hmin0
    simp only [blockChord, blockMin_eq_min' B hBne, blockMax_eq_max' B hBne]
    constructor
    · exact lt_of_le_of_ne (Fin.zero_le _) hmin0.symm
    · exact B.min'_lt_max'_of_card (by omega)
  · constructor
    · intro e he f hf hef
      rw [canonicalEdges, Finset.mem_image] at he hf
      obtain ⟨B, hB, rfl⟩ := he
      obtain ⟨C, hC, rfl⟩ := hf
      rw [chordBlocks, Finset.mem_filter] at hB hC
      have hBC : B ≠ C := by
        intro h
        subst C
        exact hef rfl
      exact (π.val.disjoint hB.1 hC.1 hBC).mono
        (chordEnds_blockChord_subset B (π.val.nonempty_of_mem_parts hB.1))
        (chordEnds_blockChord_subset C (π.val.nonempty_of_mem_parts hC.1))
    · intro e he f hf hefl hcross
      rw [canonicalEdges, Finset.mem_image] at he hf
      obtain ⟨B, hB, rfl⟩ := he
      obtain ⟨C, hC, rfl⟩ := hf
      rw [chordBlocks, Finset.mem_filter] at hB hC
      have hBne : B.Nonempty := π.val.nonempty_of_mem_parts hB.1
      have hCne : C.Nonempty := π.val.nonempty_of_mem_parts hC.1
      have hBC : B ≠ C := by
        intro h
        subst C
        simpa using hefl
      have hBsub := chordEnds_blockChord_subset B hBne
      have hCsub := chordEnds_blockChord_subset C hCne
      exact hBC (π.property hB.1 hC.1
        hcross.1 hcross.2.1 hcross.2.2
        (hBsub (by simp [chordEnds]))
        (hBsub (by simp [chordEnds]))
        (hCsub (by simp [chordEnds]))
        (hCsub (by simp [chordEnds])))

/-- The canonical matching extracted from an NC partition. -/
noncomputable def canonicalMatching
    (π : NC (Finset.univ : Finset (Fin n))) : CanonicalMatching n :=
  ⟨canonicalEdges π, canonicalEdges_isCanonicalMatching π⟩

@[simp]
theorem canonicalMatching_val
    (π : NC (Finset.univ : Finset (Fin n))) :
    (canonicalMatching π).1 = canonicalEdges π := rfl

theorem mem_canonicalEdges_iff
    (π : NC (Finset.univ : Finset (Fin n))) (e : Fin n × Fin n) :
    e ∈ canonicalEdges π ↔
      ∃ B ∈ π.val.parts,
        blockMin B ≠ 0 ∧ 2 ≤ B.card ∧ blockChord B = e := by
  simp only [canonicalEdges, chordBlocks, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨B, ⟨hB, hroot, hcard⟩, hBe⟩
    exact ⟨B, hB, hroot, hcard, hBe⟩
  · rintro ⟨B, hB, hroot, hcard, hBe⟩
    exact ⟨B, ⟨hB, hroot, hcard⟩, hBe⟩

theorem mem_canonical_endpoints_iff
    (π : NC (Finset.univ : Finset (Fin n))) (x : Fin n) :
    x ∈ (canonicalMatching π).endpoints ↔
      let B := π.val.part x
      blockMin B ≠ 0 ∧ 2 ≤ B.card ∧
        (x = blockMin B ∨ x = blockMax B) := by
  let B := π.val.part x
  have hxuniv : x ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ x
  have hBmem : B ∈ π.val.parts := π.val.part_mem.mpr hxuniv
  have hxB : x ∈ B := π.val.mem_part hxuniv
  have hBne : B.Nonempty := ⟨x, hxB⟩
  constructor
  · intro hx
    obtain ⟨e, he, hxe⟩ :=
      ((canonicalMatching π).mem_endpoints_iff x).1 hx
    obtain ⟨C, hCmem, hCroot, hCcard, hCe⟩ :=
      (mem_canonicalEdges_iff π e).1 he
    have hCne : C.Nonempty := π.val.nonempty_of_mem_parts hCmem
    have hxeC : x = (blockChord C).1 ∨ x = (blockChord C).2 := by
      simpa only [hCe] using hxe
    have hxC : x ∈ C := by
      exact chordEnds_blockChord_subset C hCne (by simpa [chordEnds] using hxeC)
    have hCB : C = B := π.val.eq_of_mem_parts hCmem hBmem hxC hxB
    subst C
    exact ⟨hCroot, hCcard, by simpa only [blockChord] using hxeC⟩
  · rintro ⟨hBroot, hBcard, hxextreme⟩
    apply ((canonicalMatching π).mem_endpoints_iff x).2
    refine ⟨blockChord B, ?_, ?_⟩
    · exact (mem_canonicalEdges_iff π (blockChord B)).2
        ⟨B, hBmem, hBroot, hBcard, rfl⟩
    · simpa only [blockChord] using hxextreme

/-- The recovered mask consists exactly of free points belonging to a
nonsingleton block of the original partition. -/
noncomputable def canonicalMask
    (π : NC (Finset.univ : Finset (Fin n))) :
    Finset (canonicalMatching π).free :=
  (canonicalMatching π).free.attach.filter fun x => 2 ≤ (π.val.part x.1).card

@[simp]
theorem mem_canonicalMask_iff
    (π : NC (Finset.univ : Finset (Fin n)))
    (x : (canonicalMatching π).free) :
    x ∈ canonicalMask π ↔ 2 ≤ (π.val.part x.1).card := by
  simp [canonicalMask]

theorem mem_canonicalMaskPoints_iff
    (π : NC (Finset.univ : Finset (Fin n))) (x : Fin n) :
    x ∈ (canonicalMatching π).maskPoints (canonicalMask π) ↔
      x ∈ (canonicalMatching π).free ∧ 2 ≤ (π.val.part x).card := by
  constructor
  · intro hx
    rw [CanonicalMatching.maskPoints, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y.2, (mem_canonicalMask_iff π y).1 hy⟩
  · rintro ⟨hfree, hcard⟩
    rw [CanonicalMatching.maskPoints, Finset.mem_image]
    let y : (canonicalMatching π).free := ⟨x, hfree⟩
    exact ⟨y, (mem_canonicalMask_iff π y).2 hcard, rfl⟩

/-- On every selected free point, the geometric anchor is exactly the minimum
of its original NC block. -/
theorem canonical_anchorKey_eq_blockMin
    (π : NC (Finset.univ : Finset (Fin n))) (x : Fin n)
    (hfree : x ∈ (canonicalMatching π).free)
    (hcard : 2 ≤ (π.val.part x).card) :
    (canonicalMatching π).anchorKey x = blockMin (π.val.part x) := by
  let Q := canonicalMatching π
  let B := π.val.part x
  have hxuniv : x ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ x
  have hBmem : B ∈ π.val.parts := π.val.part_mem.mpr hxuniv
  have hxB : x ∈ B := π.val.mem_part hxuniv
  have hBne : B.Nonempty := ⟨x, hxB⟩
  have hx_not_endpoint : x ∉ Q.endpoints := (Q.mem_free_iff x).1 hfree |>.2
  by_cases hroot : blockMin B = 0
  · rw [hroot]
    rw [CanonicalMatching.anchorKey, dif_neg]
    intro hne
    obtain ⟨a, ha⟩ := hne
    obtain ⟨e, he, hex, _⟩ := (Q.mem_precedingLefts_iff x a).1 ha
    obtain ⟨C, hCmem, hCroot, _hCcard, hCe⟩ :=
      (mem_canonicalEdges_iff π e).1 he
    have hCne : C.Nonempty := π.val.nonempty_of_mem_parts hCmem
    have hcross := π.property hBmem hCmem
      (by simpa [hroot] using (Q.2.1 e he).1)
      (by simpa [← hCe, blockChord] using hex.1)
      (by simpa [← hCe, blockChord] using hex.2)
      (by simpa [hroot] using blockMin_mem B hBne)
      hxB
      (by simpa [← hCe, blockChord] using blockMin_mem C hCne)
      (by simpa [← hCe, blockChord] using blockMax_mem C hCne)
    subst C
    exact hCroot hroot
  · have hx_not_extreme : ¬ (x = blockMin B ∨ x = blockMax B) := by
      intro h
      exact hx_not_endpoint ((mem_canonical_endpoints_iff π x).2
        ⟨hroot, hcard, h⟩)
    have hminx : blockMin B < x :=
      lt_of_le_of_ne (blockMin_le B hBne hxB)
        (fun h => hx_not_extreme (Or.inl h.symm))
    have hxmax : x < blockMax B :=
      lt_of_le_of_ne (le_blockMax B hBne hxB)
        (fun h => hx_not_extreme (Or.inr h))
    have he : blockChord B ∈ canonicalEdges π :=
      (mem_canonicalEdges_iff π (blockChord B)).2
        ⟨B, hBmem, hroot, hcard, rfl⟩
    have hmin_mem : blockMin B ∈ Q.precedingLefts x :=
      (Q.mem_precedingLefts_iff x (blockMin B)).2
        ⟨blockChord B, he, by simpa [blockChord] using And.intro hminx hxmax, rfl⟩
    have hne : (Q.precedingLefts x).Nonempty := ⟨blockMin B, hmin_mem⟩
    rw [CanonicalMatching.anchorKey, dif_pos hne]
    apply le_antisymm
    · apply Finset.max'_le
      intro a ha
      obtain ⟨e, he', hex, hea⟩ := (Q.mem_precedingLefts_iff x a).1 ha
      obtain ⟨C, hCmem, _hCroot, _hCcard, hCe⟩ :=
        (mem_canonicalEdges_iff π e).1 he'
      have hCne : C.Nonempty := π.val.nonempty_of_mem_parts hCmem
      rw [← hea]
      rw [← hCe]
      simp only [blockChord]
      by_contra hnot
      have hlt : blockMin B < blockMin C := lt_of_not_ge hnot
      have hEq := π.property hBmem hCmem
        hlt
        (by simpa [← hCe, blockChord] using hex.1)
        (by simpa [← hCe, blockChord] using hex.2)
        (blockMin_mem B hBne) hxB
        (blockMin_mem C hCne) (blockMax_mem C hCne)
      subst C
      exact (lt_irrefl _) hlt
    · exact Finset.le_max' _ _ hmin_mem

theorem canonical_decodeKey_eq_blockMin_part
    (π : NC (Finset.univ : Finset (Fin n))) (x : Fin n) :
    (canonicalMatching π).decodeKey (canonicalMask π) x =
      blockMin (π.val.part x) := by
  let Q := canonicalMatching π
  let B := π.val.part x
  have hxuniv : x ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ x
  have hxB : x ∈ B := π.val.mem_part hxuniv
  have hBne : B.Nonempty := ⟨x, hxB⟩
  by_cases hend : x ∈ Q.endpoints
  · obtain ⟨hroot, hcard, hxextreme⟩ :=
      (mem_canonical_endpoints_iff π x).1 hend
    have he : blockChord B ∈ canonicalEdges π :=
      (mem_canonicalEdges_iff π (blockChord B)).2
        ⟨B, π.val.part_mem.mpr hxuniv, hroot, hcard, rfl⟩
    have hxchord : x = (blockChord B).1 ∨ x = (blockChord B).2 := by
      simpa only [blockChord] using hxextreme
    rw [CanonicalMatching.decodeKey, if_pos hend,
      Q.endpointKey_eq_left_of_mem he hxchord]
    rfl
  · by_cases hmask : x ∈ Q.maskPoints (canonicalMask π)
    · have hm := (mem_canonicalMaskPoints_iff π x).1 hmask
      rw [CanonicalMatching.decodeKey, if_neg hend, if_pos hmask]
      exact canonical_anchorKey_eq_blockMin π x hm.1 hm.2
    · rw [CanonicalMatching.decodeKey, if_neg hend, if_neg hmask]
      by_cases hx0 : x = 0
      · subst x
        exact le_antisymm (Fin.zero_le _) (blockMin_le B hBne hxB)
      · have hfree : x ∈ Q.free := (Q.mem_free_iff x).2 ⟨hx0, hend⟩
        by_contra hxmin
        have hpair : ({x, blockMin B} : Finset (Fin n)) ⊆ B := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hxB
          · exact blockMin_mem B hBne
        have hcard : 2 ≤ B.card := by
          rw [← Finset.card_pair hxmin]
          exact Finset.card_le_card hpair
        exact hmask ((mem_canonicalMaskPoints_iff π x).2 ⟨hfree, hcard⟩)

theorem canonical_decoded_part_eq
    (π : NC (Finset.univ : Finset (Fin n))) (x : Fin n) :
    ((canonicalMatching π).decodedFinpartition (canonicalMask π)).part x =
      π.val.part x := by
  ext y
  rw [(canonicalMatching π).mem_part_decodedFinpartition_iff]
  rw [canonical_decodeKey_eq_blockMin_part π x,
    canonical_decodeKey_eq_blockMin_part π y]
  rw [π.val.mem_part_iff_part_eq_part (Finset.mem_univ y) (Finset.mem_univ x)]
  constructor
  · intro hmin
    let Bx := π.val.part x
    let By := π.val.part y
    have hBxmem : Bx ∈ π.val.parts := π.val.part_mem.mpr (Finset.mem_univ x)
    have hBymem : By ∈ π.val.parts := π.val.part_mem.mpr (Finset.mem_univ y)
    have hBxne : Bx.Nonempty := π.val.nonempty_of_mem_parts hBxmem
    have hByne : By.Nonempty := π.val.nonempty_of_mem_parts hBymem
    have hcommonX : blockMin Bx ∈ Bx := blockMin_mem Bx hBxne
    have hcommonY : blockMin Bx ∈ By := by
      rw [hmin]
      exact blockMin_mem By hByne
    exact π.val.eq_of_mem_parts hBymem hBxmem hcommonY hcommonX
  · intro hparts
    rw [hparts]

/-- Decoding the matching and mask extracted from an NC partition returns
that partition literally. -/
theorem decode_encode
    (π : NC (Finset.univ : Finset (Fin n))) :
    (canonicalMatching π).decodedNC (canonicalMask π) = π := by
  apply Subtype.ext
  apply finpartition_eq_of_part_eq
  intro x _hx
  exact canonical_decoded_part_eq π x

theorem canonicalEdges_decodedNC (Q : CanonicalMatching n) (A : Finset Q.free) :
    canonicalEdges (Q.decodedNC A) = Q.1 := by
  ext e
  constructor
  · intro he
    obtain ⟨B, hBmem, hBroot, hBcard, hBe⟩ :=
      (mem_canonicalEdges_iff (Q.decodedNC A) e).1 he
    have hBne : B.Nonempty := (Q.decodedNC A).val.nonempty_of_mem_parts hBmem
    have hminltmax : blockMin B < blockMax B := by
      rw [blockMin_eq_min' B hBne, blockMax_eq_max' B hBne]
      exact B.min'_lt_max'_of_card (by omega)
    have hminMem : blockMin B ∈ B := blockMin_mem B hBne
    have hmaxMem : blockMax B ∈ B := blockMax_mem B hBne
    have hpartMin : (Q.decodedFinpartition A).part (blockMin B) = B :=
      (Q.decodedFinpartition A).part_eq_of_mem hBmem hminMem
    have hkeyMinMem := decodeKey_mem_own_part Q A (blockMin B)
    rw [hpartMin] at hkeyMinMem
    have hmin_le_key : blockMin B ≤ Q.decodeKey A (blockMin B) :=
      blockMin_le B hBne hkeyMinMem
    have hkey_le_min := Q.decodeKey_le A (blockMin B)
    have hkeyMin : Q.decodeKey A (blockMin B) = blockMin B :=
      le_antisymm hkey_le_min hmin_le_key
    have hmaxInPart : blockMax B ∈
        (Q.decodedFinpartition A).part (blockMin B) := by
      rw [hpartMin]
      exact hmaxMem
    have hkeys : Q.decodeKey A (blockMin B) = Q.decodeKey A (blockMax B) :=
      (Q.mem_part_decodedFinpartition_iff A (blockMin B) (blockMax B)).1 hmaxInPart
    rcases Q.commonKey_root_or_chord A hminltmax hkeys with
        hroot | ⟨f, hf, hfKey⟩
    · exact (hBroot (hkeyMin.symm.trans hroot)).elim
    · have hfleft : f.1 = blockMin B := hfKey.trans hkeyMin
      have hfext := decoded_chord_part_extrema Q A hf
      have hpartF : (Q.decodedFinpartition A).part f.1 = B := by
        rw [hfleft, hpartMin]
      have hfright : f.2 = blockMax B := by
        have h := hfext.2.1
        rw [hpartF] at h
        exact h.symm
      have hfe : f = e := by
        rw [← hBe]
        apply Prod.ext
        · exact hfleft
        · exact hfright
      simpa [← hfe] using hf
  · intro he
    let B := (Q.decodedFinpartition A).part e.1
    have hBmem : B ∈ (Q.decodedNC A).val.parts :=
      (Q.decodedFinpartition A).part_mem.mpr (Finset.mem_univ e.1)
    have hext := decoded_chord_part_extrema Q A he
    have hroot : blockMin B ≠ 0 := by
      rw [hext.1]
      exact (Q.2.1 e he).1.ne'
    have hchord : blockChord B = e := by
      apply Prod.ext
      · exact hext.1
      · exact hext.2.1
    exact (mem_canonicalEdges_iff (Q.decodedNC A) e).2
      ⟨B, hBmem, hroot, hext.2.2, hchord⟩

theorem canonicalMatching_decodedNC (Q : CanonicalMatching n) (A : Finset Q.free) :
    canonicalMatching (Q.decodedNC A) = Q := by
  apply Subtype.ext
  exact canonicalEdges_decodedNC Q A

theorem mem_maskPoints_iff (Q : CanonicalMatching n) (A : Finset Q.free)
    (q : Q.free) : q.1 ∈ Q.maskPoints A ↔ q ∈ A := by
  constructor
  · intro h
    rw [CanonicalMatching.maskPoints, Finset.mem_image] at h
    obtain ⟨r, hr, hrq⟩ := h
    have : r = q := Subtype.ext hrq
    simpa [this] using hr
  · intro h
    rw [CanonicalMatching.maskPoints, Finset.mem_image]
    exact ⟨q, h, rfl⟩

theorem maskPoints_insert (Q : CanonicalMatching n) (A : Finset Q.free)
    (q : Q.free) :
    Q.maskPoints (insert q A) = insert q.1 (Q.maskPoints A) := by
  simp [CanonicalMatching.maskPoints]

theorem decodeKey_insert (Q : CanonicalMatching n) (A : Finset Q.free)
    (q : Q.free) (hqA : q ∉ A) (x : Fin n) :
    Q.decodeKey (insert q A) x =
      if x = q.1 then Q.anchorKey q.1 else Q.decodeKey A x := by
  have hqEnd : q.1 ∉ Q.endpoints := (Q.mem_free_iff q.1).1 q.2 |>.2
  have hqMask : q.1 ∉ Q.maskPoints A := by
    intro h
    exact hqA ((mem_maskPoints_iff Q A q).1 h)
  rw [CanonicalMatching.decodeKey, maskPoints_insert,
    CanonicalMatching.decodeKey]
  by_cases hx : x = q.1
  · subst x
    simp [hqEnd, hqMask]
  · by_cases hend : x ∈ Q.endpoints
    · simp [hx, hend]
    · simp [hx, hend]

theorem decoded_part_eq_singleton_of_not_mem
    (Q : CanonicalMatching n) (A : Finset Q.free) (q : Q.free)
    (hqA : q ∉ A) :
    (Q.decodedFinpartition A).part q.1 = {q.1} := by
  have hqEnd : q.1 ∉ Q.endpoints := (Q.mem_free_iff q.1).1 q.2 |>.2
  have hqMask : q.1 ∉ Q.maskPoints A := by
    intro h
    exact hqA ((mem_maskPoints_iff Q A q).1 h)
  have hqKey : Q.decodeKey A q.1 = q.1 := by
    rw [CanonicalMatching.decodeKey, if_neg hqEnd, if_neg hqMask]
  ext y
  constructor
  · intro hy
    have hkeys := (Q.mem_part_decodedFinpartition_iff A q.1 y).1 hy
    rw [hqKey] at hkeys
    rcases lt_trichotomy y q.1 with hyq | heq | hqy
    · have hle := Q.decodeKey_le A y
      rw [← hkeys] at hle
      exact ((not_le_of_gt hyq) hle).elim
    · simpa using heq
    · have hkeys' : Q.decodeKey A q.1 = Q.decodeKey A y := by
        simpa [hqKey] using hkeys
      rcases Q.commonKey_root_or_chord A hqy hkeys' with
          hroot | ⟨e, he, heKey⟩
      · exact (((Q.mem_free_iff q.1).1 q.2).1 (hqKey.symm.trans hroot)).elim
      · have hqEndpoint : q.1 ∈ Q.endpoints :=
          (Q.mem_endpoints_iff q.1).2 ⟨e, he, Or.inl (heKey.trans hqKey).symm⟩
        exact (hqEnd hqEndpoint).elim
  · intro hy
    have hyq : y = q.1 := by simpa using hy
    subst y
    exact (Q.decodedFinpartition A).mem_part (Finset.mem_univ q.1)

theorem anchorKey_lt_of_free (Q : CanonicalMatching n) {q : Fin n}
    (hq : q ∈ Q.free) : Q.anchorKey q < q := by
  by_cases hroot : Q.anchorKey q = 0
  · rw [hroot]
    exact lt_of_le_of_ne (Fin.zero_le _) ((Q.mem_free_iff q).1 hq).1.symm
  · exact Q.anchorKey_lt hroot

theorem decodeKey_anchorKey (Q : CanonicalMatching n) (A : Finset Q.free)
    (x : Fin n) : Q.decodeKey A (Q.anchorKey x) = Q.anchorKey x := by
  rcases Q.anchorKey_eq_root_or_chord x with hroot | ⟨e, he, _hex, heq⟩
  · rw [hroot, Q.decodeKey_root]
  · rw [← heq]
    have hleftEnd : e.1 ∈ Q.endpoints :=
      (Q.mem_endpoints_iff e.1).2 ⟨e, he, Or.inl rfl⟩
    rw [CanonicalMatching.decodeKey, if_pos hleftEnd, Q.endpointKey_left he]

theorem decodedFinpartition_insert_eq_mergeBlocks
    (Q : CanonicalMatching n) (A : Finset Q.free) (q : Q.free) (hqA : q ∉ A) :
    let P := Q.decodedFinpartition A
    let Bq := P.part q.1
    let Ba := P.part (Q.anchorKey q.1)
    Q.decodedFinpartition (insert q A) =
      P.mergeBlocks (P.part_mem.mpr (Finset.mem_univ q.1))
        (P.part_mem.mpr (Finset.mem_univ (Q.anchorKey q.1)))
        (by
          intro h
          have hqIn : q.1 ∈ Ba := by
            change q.1 ∈ P.part (Q.anchorKey q.1)
            rw [← h]
            exact P.mem_part (Finset.mem_univ q.1)
          have hkeys := (Q.mem_part_decodedFinpartition_iff A
            (Q.anchorKey q.1) q.1).1 hqIn
          have hqKey : Q.decodeKey A q.1 = q.1 := by
            have hqEnd := (Q.mem_free_iff q.1).1 q.2 |>.2
            have hqMask : q.1 ∉ Q.maskPoints A := by
              intro hm
              exact hqA ((mem_maskPoints_iff Q A q).1 hm)
            rw [CanonicalMatching.decodeKey, if_neg hqEnd, if_neg hqMask]
          rw [decodeKey_anchorKey, hqKey] at hkeys
          exact (anchorKey_lt_of_free Q q.2).ne hkeys) := by
  let P := Q.decodedFinpartition A
  let R := Q.decodedFinpartition (insert q A)
  let Bq := P.part q.1
  let Ba := P.part (Q.anchorKey q.1)
  have hBqmem : Bq ∈ P.parts := P.part_mem.mpr (Finset.mem_univ q.1)
  have hBamem : Ba ∈ P.parts :=
    P.part_mem.mpr (Finset.mem_univ (Q.anchorKey q.1))
  have hBq : Bq = {q.1} := decoded_part_eq_singleton_of_not_mem Q A q hqA
  have hqKey : Q.decodeKey A q.1 = q.1 := by
    have hqEnd := (Q.mem_free_iff q.1).1 q.2 |>.2
    have hqMask : q.1 ∉ Q.maskPoints A := by
      intro hm
      exact hqA ((mem_maskPoints_iff Q A q).1 hm)
    rw [CanonicalMatching.decodeKey, if_neg hqEnd, if_neg hqMask]
  have haKey : Q.decodeKey A (Q.anchorKey q.1) = Q.anchorKey q.1 :=
    decodeKey_anchorKey Q A q.1
  have hne : Bq ≠ Ba := by
    intro h
    have hqIn : q.1 ∈ Ba := by
      rw [← h]
      exact P.mem_part (Finset.mem_univ q.1)
    have hkeys := (Q.mem_part_decodedFinpartition_iff A
      (Q.anchorKey q.1) q.1).1 hqIn
    rw [haKey, hqKey] at hkeys
    exact (anchorKey_lt_of_free Q q.2).ne hkeys
  have hRq : R.part q.1 = Bq ∪ Ba := by
    ext y
    rw [Q.mem_part_decodedFinpartition_iff]
    rw [decodeKey_insert Q A q hqA q.1, if_pos rfl]
    rw [hBq]
    simp only [Finset.singleton_union, Finset.mem_insert]
    by_cases hyq : y = q.1
    · subst y
      simp [decodeKey_insert Q A q hqA]
    · rw [decodeKey_insert Q A q hqA y, if_neg hyq]
      have hmem : y ∈ Ba ↔ Q.anchorKey q.1 = Q.decodeKey A y := by
        change y ∈ P.part (Q.anchorKey q.1) ↔ _
        rw [Q.mem_part_decodedFinpartition_iff, haKey]
      simpa [hyq] using hmem.symm
  apply finpartition_eq_of_part_eq
  intro x _hx
  rw [mergeBlocks_part_eq P hBqmem hBamem hne (Finset.mem_univ x)]
  by_cases hxunion : x ∈ Bq ∪ Ba
  · rw [if_pos hxunion]
    have hxR : x ∈ R.part q.1 := by
      rw [hRq]
      exact hxunion
    exact ((R.mem_part_iff_part_eq_part (Finset.mem_univ x)
      (Finset.mem_univ q.1)).1 hxR).trans hRq
  · rw [if_neg hxunion]
    have hxq : x ≠ q.1 := by
      intro h
      subst x
      exact hxunion (Finset.mem_union_left _ (P.mem_part (Finset.mem_univ q.1)))
    ext y
    rw [Q.mem_part_decodedFinpartition_iff,
      P.mem_part_iff_part_eq_part (Finset.mem_univ y) (Finset.mem_univ x)]
    rw [decodeKey_insert Q A q hqA x, if_neg hxq]
    by_cases hyq : y = q.1
    · subst y
      rw [decodeKey_insert Q A q hqA q.1, if_pos rfl]
      have hxNotBa : x ∉ Ba := fun hxBa =>
        hxunion (Finset.mem_union_right _ hxBa)
      have hxNotBq : x ∉ Bq := fun hxBq =>
        hxunion (Finset.mem_union_left _ hxBq)
      constructor
      · intro hkey
        have hxBa : x ∈ Ba := by
          change x ∈ P.part (Q.anchorKey q.1)
          rw [Q.mem_part_decodedFinpartition_iff, haKey]
          exact hkey.symm
        exact (hxNotBa hxBa).elim
      · intro hparts
        have hxBq' : x ∈ Bq := by
          change x ∈ P.part q.1
          rw [hparts]
          exact P.mem_part (Finset.mem_univ x)
        exact (hxNotBq hxBq').elim
    · rw [decodeKey_insert Q A q hqA y, if_neg hyq]
      exact (Q.mem_part_decodedFinpartition_iff A x y).symm.trans
        (P.mem_part_iff_part_eq_part (Finset.mem_univ y) (Finset.mem_univ x))

theorem decodedNC_mergesTo_insert
    (Q : CanonicalMatching n) (A : Finset Q.free) (q : Q.free) (hqA : q ∉ A) :
    NC.mergesTo (Q.decodedNC A) (Q.decodedNC (insert q A)) := by
  let P := Q.decodedFinpartition A
  let Bq := P.part q.1
  let Ba := P.part (Q.anchorKey q.1)
  have hBqmem : Bq ∈ P.parts := P.part_mem.mpr (Finset.mem_univ q.1)
  have hBamem : Ba ∈ P.parts :=
    P.part_mem.mpr (Finset.mem_univ (Q.anchorKey q.1))
  have hne : Bq ≠ Ba := by
    intro h
    change P.part q.1 = P.part (Q.anchorKey q.1) at h
    have hqIn : q.1 ∈ Ba := by
      change q.1 ∈ P.part (Q.anchorKey q.1)
      rw [← h]
      exact P.mem_part (Finset.mem_univ q.1)
    have hkeys := (Q.mem_part_decodedFinpartition_iff A
      (Q.anchorKey q.1) q.1).1 hqIn
    have hqEnd := (Q.mem_free_iff q.1).1 q.2 |>.2
    have hqMask : q.1 ∉ Q.maskPoints A := by
      intro hm
      exact hqA ((mem_maskPoints_iff Q A q).1 hm)
    have hqKey : Q.decodeKey A q.1 = q.1 := by
      rw [CanonicalMatching.decodeKey, if_neg hqEnd, if_neg hqMask]
    rw [decodeKey_anchorKey, hqKey] at hkeys
    exact (anchorKey_lt_of_free Q q.2).ne hkeys
  refine ⟨Bq, hBqmem, Ba, hBamem, hne, ?_⟩
  have hmerge := decodedFinpartition_insert_eq_mergeBlocks Q A q hqA
  have hparts := congrArg Finpartition.parts hmerge
  simpa [P, Bq, Ba, Finpartition.mergeBlocks_parts] using hparts

theorem decodedNC_adj_insert
    (Q : CanonicalMatching n) (A : Finset Q.free) (q : Q.free) (hqA : q ∉ A) :
    (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj
      (Q.decodedNC A) (Q.decodedNC (insert q A)) :=
  Or.inl (decodedNC_mergesTo_insert Q A q hqA)

theorem decoded_part_card_ge_two_iff_mem_mask
    (Q : CanonicalMatching n) (A : Finset Q.free) (q : Q.free) :
    2 ≤ ((Q.decodedFinpartition A).part q.1).card ↔ q ∈ A := by
  constructor
  · intro hcard
    by_contra hqA
    have hqEnd : q.1 ∉ Q.endpoints := (Q.mem_free_iff q.1).1 q.2 |>.2
    have hqMask : q.1 ∉ Q.maskPoints A := by
      simpa [mem_maskPoints_iff Q A q] using hqA
    have hqKey : Q.decodeKey A q.1 = q.1 := by
      rw [CanonicalMatching.decodeKey, if_neg hqEnd, if_neg hqMask]
    let B := (Q.decodedFinpartition A).part q.1
    have hBsingle : B = {q.1} := by
      ext y
      constructor
      · intro hy
        have hkeys := (Q.mem_part_decodedFinpartition_iff A q.1 y).1 hy
        rw [hqKey] at hkeys
        rcases lt_trichotomy y q.1 with hyq | heq | hqy
        · have hle := Q.decodeKey_le A y
          rw [← hkeys] at hle
          exact ((not_le_of_gt hyq) hle).elim
        · simpa using heq
        · have hkeys' : Q.decodeKey A q.1 = Q.decodeKey A y := by
            simpa [hqKey] using hkeys
          rcases Q.commonKey_root_or_chord A hqy hkeys' with
              hroot | ⟨e, he, heKey⟩
          · exact (((Q.mem_free_iff q.1).1 q.2).1 (hqKey.symm.trans hroot)).elim
          · have hqEndpoint : q.1 ∈ Q.endpoints :=
              (Q.mem_endpoints_iff q.1).2 ⟨e, he, Or.inl (heKey.trans hqKey).symm⟩
            exact (hqEnd hqEndpoint).elim
      · intro hy
        have hyq : y = q.1 := by simpa using hy
        subst y
        exact (Q.decodedFinpartition A).mem_part (Finset.mem_univ q.1)
    change 2 ≤ B.card at hcard
    rw [hBsingle] at hcard
    simp at hcard
  · intro hqA
    have hqEnd : q.1 ∉ Q.endpoints := (Q.mem_free_iff q.1).1 q.2 |>.2
    have hqMask : q.1 ∈ Q.maskPoints A := (mem_maskPoints_iff Q A q).2 hqA
    have hqKey : Q.decodeKey A q.1 = Q.anchorKey q.1 := by
      rw [CanonicalMatching.decodeKey, if_neg hqEnd, if_pos hqMask]
    have hanchorMem := decodeKey_mem_own_part Q A q.1
    rw [hqKey] at hanchorMem
    have hqMem := (Q.decodedFinpartition A).mem_part (Finset.mem_univ q.1)
    have hne : q.1 ≠ Q.anchorKey q.1 :=
      (anchorKey_lt_of_free Q q.2).ne'
    have hpair : ({q.1, Q.anchorKey q.1} : Finset (Fin n)) ⊆
        (Q.decodedFinpartition A).part q.1 := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hqMem
      · exact hanchorMem
    rw [← Finset.card_pair hne]
    exact Finset.card_le_card hpair

/-- The Petersen state decoder is injective: both the canonical matching and
the mask are recovered from the decoded NC partition. -/
theorem decodedNC_injective :
    Function.Injective
      (fun st : Sigma (fun Q : CanonicalMatching n => Finset Q.free) =>
        st.1.decodedNC st.2) := by
  rintro ⟨Q, A⟩ ⟨R, C⟩ hdecode
  change Q.decodedNC A = R.decodedNC C at hdecode
  have hQR : Q = R := by
    apply Subtype.ext
    rw [← canonicalEdges_decodedNC Q A, hdecode, canonicalEdges_decodedNC R C]
  subst R
  have hval : Q.decodedFinpartition A = Q.decodedFinpartition C :=
    congrArg Subtype.val hdecode
  have hAC : A = C := by
    ext q
    rw [← decoded_part_card_ge_two_iff_mem_mask Q A q,
      ← decoded_part_card_ge_two_iff_mem_mask Q C q]
    rw [hval]
  subst C
  rfl

/-- Total Petersen coordinate state: one canonical matching and one mask on
its unmatched non-root points. -/
def State (n : Nat) [NeZero n] :=
  Sigma (fun Q : CanonicalMatching n => Finset Q.free)

noncomputable instance : Fintype (State n) := by
  unfold State
  infer_instance

noncomputable def decodeState (st : State n) :
    NC (Finset.univ : Finset (Fin n)) := st.1.decodedNC st.2

noncomputable def encodeState (π : NC (Finset.univ : Finset (Fin n))) : State n :=
  ⟨canonicalMatching π, canonicalMask π⟩

theorem decodeState_bijective : Function.Bijective (decodeState (n := n)) := by
  constructor
  · exact decodedNC_injective
  · intro π
    refine ⟨encodeState π, ?_⟩
    exact decode_encode π

/-- The kernel-checked Petersen Boolean decomposition of all NC partitions. -/
noncomputable def stateEquivNC :
    State n ≃ NC (Finset.univ : Finset (Fin n)) :=
  Equiv.ofBijective decodeState decodeState_bijective

@[simp]
theorem stateEquivNC_apply (st : State n) :
    stateEquivNC st = st.1.decodedNC st.2 := rfl

theorem endpoints_card (Q : CanonicalMatching n) :
    Q.endpoints.card = 2 * Q.1.card := by
  have hpairwise : (Q.1 : Set (Fin n × Fin n)).PairwiseDisjoint chordEnds := by
    intro e he f hf hef
    exact Q.2.2.1 e he f hf hef
  rw [CanonicalMatching.endpoints, Finset.card_biUnion hpairwise]
  calc
    (∑ e ∈ Q.1, (chordEnds e).card) = ∑ _e ∈ Q.1, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.card_pair (Q.2.1 e he).2.ne
    _ = 2 * Q.1.card := by simp [Nat.mul_comm]

theorem free_card_ledger (Q : CanonicalMatching n) :
    Q.free.card + (1 + 2 * Q.1.card) = n := by
  have hfree : Q.free =
      (Finset.univ : Finset (Fin n)) \ insert 0 Q.endpoints := by
    ext x
    simp [CanonicalMatching.free, and_assoc, and_left_comm]
  have hsub : insert (0 : Fin n) Q.endpoints ⊆ Finset.univ :=
    Finset.subset_univ _
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [← hfree, Finset.card_insert_of_notMem Q.root_not_mem_endpoints,
    endpoints_card Q] at hcard
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcard

theorem free_card_odd_of_even (Q : CanonicalMatching n) (hn : Even n) :
    Odd Q.free.card := by
  have hledger := free_card_ledger Q
  have hodd : Odd (1 + 2 * Q.1.card) :=
    (even_two_mul Q.1.card).one_add
  have hle : 1 + 2 * Q.1.card ≤ n := by omega
  have heq : Q.free.card = n - (1 + 2 * Q.1.card) := by omega
  rw [heq]
  exact Nat.Even.sub_odd hle hn hodd

end Encoding
end Petersen
end Hamilton.Infrastructure
