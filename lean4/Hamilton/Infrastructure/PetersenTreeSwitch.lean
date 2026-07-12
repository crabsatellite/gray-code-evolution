/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.PetersenPorts
import Mathlib.Data.List.Rotate

/-!
# Tree switching for Petersen Boolean cycles

The generic lemmas here cut an undirected simple cycle at a prescribed edge
and splice two such cuts across a literal square.
-/

namespace Hamilton.Infrastructure
namespace Petersen
namespace Switch

variable {V : Type*} [DecidableEq V]

def CyclicEdge (L : List V) (a b : V) : Prop :=
  ((∃ pre post, L = pre ++ a :: b :: post) ∨
    (∃ pre post, L = pre ++ b :: a :: post)) ∨
    (L.head? = some a ∧ L.getLast? = some b) ∨
    (L.head? = some b ∧ L.getLast? = some a)

theorem cyclicEdge_symm {L : List V} {a b : V} :
    CyclicEdge L a b → CyclicEdge L b a := by
  rintro (h | h)
  · left
    exact h.elim Or.inr Or.inl
  · right
    exact h.elim Or.inr Or.inl

theorem isChain_rotate_of_cyclic {R : V → V → Prop} {L : List V}
    (hsymm : ∀ {x y}, R x y → R y x)
    (hL : L.IsChain R) (hne : L ≠ [])
    (hclose : R (L.getLast hne) (L.head hne)) (k : Nat) :
    (L.rotate k).IsChain R := by
  by_cases hk0 : k % L.length = 0
  · rw [List.rotate_eq_drop_append_take_mod, hk0]
    simp
    exact hL
  have hlen : 0 < L.length := List.length_pos_of_ne_nil hne
  have hklt : k % L.length < L.length := Nat.mod_lt _ hlen
  have hkpos : 0 < k % L.length := Nat.pos_of_ne_zero hk0
  rw [List.rotate_eq_drop_append_take_mod]
  apply List.IsChain.append
  · exact hL.drop _
  · exact hL.take _
  intro x hx y hy
  have hxlast : x = L.getLast hne := by
    have hdrop : L.drop (k % L.length) ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp only [List.length_drop]
      omega
    have hx' : (L.drop (k % L.length)).getLast hdrop = x := by
      simpa [List.getLast?_eq_some_getLast hdrop] using hx
    rw [← hx', List.getLast_drop]
  have hyhead : y = L.head hne := by
    have htake : L.take (k % L.length) ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp only [List.length_take]
      omega
    have hy' : (L.take (k % L.length)).head htake = y := by
      simpa [List.head?_eq_some_head htake] using hy
    rw [← hy', List.head_take]
  simpa [hxlast, hyhead] using hclose

theorem nodup_rotate {L : List V} (h : L.Nodup) (k : Nat) :
    (L.rotate k).Nodup := by simpa using h

theorem toFinset_rotate (L : List V) (k : Nat) :
    (L.rotate k).toFinset = L.toFinset := by
  ext x
  simp

/-- A finite simple cycle written as a cyclic vertex list.  Lists of length
two are intentionally allowed: their chain edge and closing edge are the two
distinguished copies of the same undirected edge. -/
structure CycleCode (R : V → V → Prop) where
  vertices : List V
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  chain : vertices.IsChain R
  closing : R (vertices.getLast nonempty) (vertices.head nonempty)

noncomputable def CycleCode.toWalk {G : SimpleGraph V}
    (C : CycleCode G.Adj) : G.Walk (C.vertices.head C.nonempty)
      (C.vertices.getLast C.nonempty) :=
  SimpleGraph.Walk.ofSupport C.vertices C.nonempty C.chain

@[simp] theorem CycleCode.toWalk_support {G : SimpleGraph V}
    (C : CycleCode G.Adj) : C.toWalk.support = C.vertices :=
  SimpleGraph.Walk.support_ofSupport C.nonempty C.chain

theorem CycleCode.toWalk_isHamiltonian_of_mem {G : SimpleGraph V}
    (C : CycleCode G.Adj) (hcover : ∀ v, v ∈ C.vertices) :
    C.toWalk.IsHamiltonian := by
  apply SimpleGraph.Walk.IsPath.isHamiltonian_of_mem
  · apply SimpleGraph.Walk.IsPath.mk'
    simpa using C.nodup
  · simpa using hcover

/-- The path left after deleting the distinguished edge `lower--upper` from
a cyclic code, oriented from `lower` to `upper`. -/
structure CutPath (R : V → V → Prop) (L : List V) (lower upper : V) where
  vertices : List V
  nodup : vertices.Nodup
  chain : vertices.IsChain R
  head_eq : vertices.head? = some lower
  last_eq : vertices.getLast? = some upper
  support_eq : vertices.toFinset = L.toFinset

private theorem rotate_after_pair {L pre post : List V} {a b : V}
    (hL : L = pre ++ a :: b :: post) :
    L.rotate (pre.length + 1) = b :: post ++ pre ++ [a] := by
  have hk : pre.length + 1 < L.length := by
    rw [hL]
    simp
  rw [List.rotate_eq_drop_append_take_mod, Nat.mod_eq_of_lt hk, hL]
  have hshape : pre ++ a :: b :: post = (pre ++ [a]) ++ b :: post := by simp
  calc
    List.drop (pre.length + 1) (pre ++ a :: b :: post) ++
        List.take (pre.length + 1) (pre ++ a :: b :: post) =
      List.drop (pre ++ [a]).length ((pre ++ [a]) ++ b :: post) ++
        List.take (pre ++ [a]).length ((pre ++ [a]) ++ b :: post) := by
          simp only [List.length_append, List.length_singleton]
          rw [← hshape]
    _ = (b :: post) ++ (pre ++ [a]) := by
      rw [List.drop_append_length, List.take_append_length]
    _ = b :: post ++ pre ++ [a] := by simp [List.append_assoc]

theorem cutPath_exists_of_cyclicEdge {R : V → V → Prop}
    (hsymm : ∀ {x y}, R x y → R y x)
    (hcycle : CycleCode R) {lower upper : V}
    (hedge : CyclicEdge hcycle.vertices lower upper) :
    Nonempty (CutPath R hcycle.vertices lower upper) := by
  let L := hcycle.vertices
  change CyclicEdge L lower upper at hedge
  change Nonempty (CutPath R L lower upper)
  rcases hedge with hinside | hclosing
  · rcases hinside with ⟨pre, post, hL⟩ | ⟨pre, post, hL⟩
    · let K := (L.rotate (pre.length + 1)).reverse
      have hrot : L.rotate (pre.length + 1) =
          upper :: post ++ pre ++ [lower] := rotate_after_pair hL
      refine ⟨
        { vertices := K
          nodup := List.nodup_reverse.mpr (nodup_rotate hcycle.nodup _)
          chain := ?_
          head_eq := ?_
          last_eq := ?_
          support_eq := ?_ }⟩
      · rw [List.isChain_reverse]
        exact (isChain_rotate_of_cyclic hsymm hcycle.chain hcycle.nonempty
          hcycle.closing _).imp (fun _ _ h => hsymm h)
      · simp [K, hrot]
      · rw [List.getLast?_eq_some_iff]
        refine ⟨lower :: (pre.reverse ++ post.reverse), ?_⟩
        simp [K, hrot, List.reverse_append, List.append_assoc]
      · simp [K, toFinset_rotate]
    · let K := L.rotate (pre.length + 1)
      have hrot : L.rotate (pre.length + 1) =
          lower :: post ++ pre ++ [upper] := rotate_after_pair hL
      refine ⟨
        { vertices := K
          nodup := nodup_rotate hcycle.nodup _
          chain := isChain_rotate_of_cyclic hsymm hcycle.chain hcycle.nonempty
            hcycle.closing _
          head_eq := ?_
          last_eq := ?_
          support_eq := toFinset_rotate L _ }⟩
      · simp [K, hrot]
      · rw [List.getLast?_eq_some_iff]
        refine ⟨lower :: post ++ pre, ?_⟩
        simp [K, hrot, List.append_assoc]
  · rcases hclosing with ⟨hhead, hlast⟩ | ⟨hhead, hlast⟩
    · refine ⟨
        { vertices := L
          nodup := hcycle.nodup
          chain := hcycle.chain
          head_eq := hhead
          last_eq := hlast
          support_eq := rfl }⟩
    · refine ⟨
        { vertices := L.reverse
          nodup := List.nodup_reverse.mpr hcycle.nodup
          chain := ?_
          head_eq := ?_
          last_eq := ?_
          support_eq := by simp }⟩
      · rw [List.isChain_reverse]
        exact hcycle.chain.imp (fun _ _ h => hsymm h)
      · simpa using hlast
      · simpa using hhead

noncomputable def cutPathOfCyclicEdge {R : V → V → Prop}
    (hsymm : ∀ {x y}, R x y → R y x)
    (hcycle : CycleCode R) {lower upper : V}
    (hedge : CyclicEdge hcycle.vertices lower upper) :
    CutPath R hcycle.vertices lower upper :=
  Classical.choice (cutPath_exists_of_cyclicEdge hsymm hcycle hedge)

/-- A square switch joins two disjoint cut cycles.  The upper cross edge is
the internal join and the lower cross edge closes the resulting cycle. -/
def spliceAcrossSquare {R : V → V → Prop}
    {L₁ L₂ : List V} {lower₁ upper₁ lower₂ upper₂ : V}
    (P₁ : CutPath R L₁ lower₁ upper₁)
    (P₂ : CutPath R L₂ lower₂ upper₂) : List V :=
  P₁.vertices ++ P₂.vertices

theorem cycleCode_spliceAcrossSquare_exists {R : V → V → Prop}
    {L₁ L₂ : List V} {lower₁ upper₁ lower₂ upper₂ : V}
    (P₁ : CutPath R L₁ lower₁ upper₁)
    (P₂ : CutPath R L₂ lower₂ upper₂)
    (hdisjoint : Disjoint L₁.toFinset L₂.toFinset)
    (hupper : R upper₁ lower₂) (hlower : R upper₂ lower₁) :
    Nonempty (CycleCode R) := by
  have hP₁ : P₁.vertices ≠ [] := by
    intro h
    have hh := P₁.head_eq
    rw [h] at hh
    simp at hh
  have hP₂ : P₂.vertices ≠ [] := by
    intro h
    have hh := P₂.head_eq
    rw [h] at hh
    simp at hh
  refine ⟨
    { vertices := spliceAcrossSquare P₁ P₂
      nonempty := by simp [spliceAcrossSquare, hP₁]
      nodup := ?_
      chain := ?_
      closing := ?_ }⟩
  · rw [spliceAcrossSquare, List.nodup_append]
    refine ⟨P₁.nodup, P₂.nodup, ?_⟩
    intro x hx₁ y hx₂ hxy
    subst y
    have hx₁' : x ∈ L₁.toFinset := by
      rw [← P₁.support_eq]
      simpa using hx₁
    have hx₂' : x ∈ L₂.toFinset := by
      rw [← P₂.support_eq]
      simpa using hx₂
    exact Finset.disjoint_left.mp hdisjoint hx₁' hx₂'
  · rw [spliceAcrossSquare]
    apply List.IsChain.append P₁.chain P₂.chain
    intro x hx y hy
    have hx' : x = upper₁ := by
      rw [P₁.last_eq] at hx
      simpa using hx.symm
    have hy' : y = lower₂ := by
      rw [P₂.head_eq] at hy
      simpa using hy.symm
    simpa [hx', hy'] using hupper
  · have hlast : (P₁.vertices ++ P₂.vertices).getLast
        (by simp [hP₁]) = upper₂ := by
      rw [List.getLast_append_of_ne_nil _ hP₂]
      exact (List.getLast_eq_iff_getLast?_eq_some hP₂).mpr P₂.last_eq
    have hhead : (P₁.vertices ++ P₂.vertices).head
        (by simp [hP₁]) = lower₁ := by
      rw [List.head_append_of_ne_nil hP₁]
      exact (List.head_eq_iff_head?_eq_some hP₁).mpr P₁.head_eq
    simpa [spliceAcrossSquare, hlast, hhead] using hlower

noncomputable def cycleCodeSpliceAcrossSquare {R : V → V → Prop}
    {L₁ L₂ : List V} {lower₁ upper₁ lower₂ upper₂ : V}
    (P₁ : CutPath R L₁ lower₁ upper₁)
    (P₂ : CutPath R L₂ lower₂ upper₂)
    (hdisjoint : Disjoint L₁.toFinset L₂.toFinset)
    (hupper : R upper₁ lower₂) (hlower : R upper₂ lower₁) :
    CycleCode R :=
  Classical.choice
    (cycleCode_spliceAcrossSquare_exists P₁ P₂ hdisjoint hupper hlower)

theorem spliceAcrossSquare_support {R : V → V → Prop}
    {L₁ L₂ : List V} {lower₁ upper₁ lower₂ upper₂ : V}
    (P₁ : CutPath R L₁ lower₁ upper₁)
    (P₂ : CutPath R L₂ lower₂ upper₂) :
    (spliceAcrossSquare P₁ P₂).toFinset = L₁.toFinset ∪ L₂.toFinset := by
  simp [spliceAcrossSquare, P₁.support_eq, P₂.support_eq]

/-- A cycle decomposed into an ordered list of nonempty path pieces.  This is
the simultaneous-switch interface: each piece may consist of one base-cycle
vertex followed by an entire child-subtree excursion. -/
structure CyclicPieceSystem (R : V → V → Prop) where
  pieces : List (List V)
  pieces_nonempty : pieces ≠ []
  piece_nonempty : ∀ K ∈ pieces, K ≠ []
  piece_nodup : ∀ K ∈ pieces, K.Nodup
  pieces_disjoint : pieces.Pairwise List.Disjoint
  piece_chain : ∀ K ∈ pieces, K.IsChain R
  bridge_chain : pieces.IsChain
    (fun K L ↦ ∀ᵉ (x ∈ K.getLast?) (y ∈ L.head?), R x y)
  closing : R
    ((pieces.getLast pieces_nonempty).getLast (by
      exact piece_nonempty _ (List.getLast_mem pieces_nonempty)))
    ((pieces.head pieces_nonempty).head (by
      exact piece_nonempty _ (List.head_mem pieces_nonempty)))

theorem CyclicPieceSystem.flatten_nonempty {R : V → V → Prop}
    (S : CyclicPieceSystem R) : S.pieces.flatten ≠ [] := by
  have hfirst : S.pieces.head S.pieces_nonempty ∈ S.pieces :=
    List.head_mem S.pieces_nonempty
  have hfirstNonempty := S.piece_nonempty _ hfirst
  exact List.flatten_ne_nil_iff.mpr ⟨_, hfirst, hfirstNonempty⟩

theorem CyclicPieceSystem.flatten_nodup {R : V → V → Prop}
    (S : CyclicPieceSystem R) : S.pieces.flatten.Nodup := by
  rw [List.nodup_flatten]
  exact ⟨S.piece_nodup, S.pieces_disjoint⟩

theorem CyclicPieceSystem.flatten_chain {R : V → V → Prop}
    (S : CyclicPieceSystem R) : S.pieces.flatten.IsChain R := by
  have hempty : [] ∉ S.pieces := by
    intro h
    exact S.piece_nonempty [] h rfl
  rw [List.isChain_flatten hempty]
  exact ⟨S.piece_chain, S.bridge_chain⟩

noncomputable def CyclicPieceSystem.toCycleCode {R : V → V → Prop}
    (S : CyclicPieceSystem R) : CycleCode R where
  vertices := S.pieces.flatten
  nonempty := S.flatten_nonempty
  nodup := S.flatten_nodup
  chain := S.flatten_chain
  closing := by
    have hpLast : S.pieces.getLast S.pieces_nonempty ≠ [] :=
      S.piece_nonempty _ (List.getLast_mem S.pieces_nonempty)
    have hpHead : S.pieces.head S.pieces_nonempty ≠ [] :=
      S.piece_nonempty _ (List.head_mem S.pieces_nonempty)
    have hlast : S.pieces.flatten.getLast S.flatten_nonempty =
        (S.pieces.getLast S.pieces_nonempty).getLast hpLast := by
      exact List.getLast_flatten_eq_getLast_getLast S.flatten_nonempty hpLast
    have hhead : S.pieces.flatten.head S.flatten_nonempty =
        (S.pieces.head S.pieces_nonempty).head hpHead := by
      exact List.head_flatten_eq_head_head S.flatten_nonempty hpHead
    simpa [hlast, hhead] using S.closing

/-- Directed edge occurrences around a cyclic list.  For `[a,b]` this is
`[(a,b),(b,a)]`, retaining the two distinguished copies of the doubled
dimension-one cycle. -/
def cyclicPairsAux (first : V) : List V → List (V × V)
  | [] => []
  | [a] => [(a, first)]
  | a :: b :: rest => (a, b) :: cyclicPairsAux first (b :: rest)

def cyclicPairs : List V → List (V × V)
  | [] => []
  | a :: rest => cyclicPairsAux a (a :: rest)

theorem cyclicPairsAux_fst (first : V) : ∀ L,
    (cyclicPairsAux first L).map Prod.fst = L := by
  intro L
  induction L using cyclicPairsAux.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b rest ih => simp [cyclicPairsAux, ih]

theorem cyclicPairs_fst (L : List V) :
    (cyclicPairs L).map Prod.fst = L := by
  cases L with
  | nil => rfl
  | cons a rest => exact cyclicPairsAux_fst a (a :: rest)

theorem cyclicPairsAux_ne_nil (first : V) : ∀ {L : List V},
    L ≠ [] → cyclicPairsAux first L ≠ [] := by
  intro L hL
  cases L with
  | nil => contradiction
  | cons a rest => cases rest <;> simp [cyclicPairsAux]

theorem cyclicPairs_ne_nil {L : List V} (hL : L ≠ []) :
    cyclicPairs L ≠ [] := by
  cases L with
  | nil => contradiction
  | cons a rest => exact cyclicPairsAux_ne_nil a (by simp)

theorem cyclicPairs_head_fst {L : List V} (hL : L ≠ []) :
    ((cyclicPairs L).head (cyclicPairs_ne_nil hL)).1 = L.head hL := by
  have hmap := congrArg List.head? (cyclicPairs_fst L)
  rw [List.head?_map,
    List.head?_eq_some_head (cyclicPairs_ne_nil hL),
    List.head?_eq_some_head hL] at hmap
  exact Option.some.inj hmap

theorem cyclicPairsAux_head_fst (first : V) : ∀ {L : List V} (hL : L ≠ []),
    ((cyclicPairsAux first L).head (cyclicPairsAux_ne_nil first hL)).1 =
      (L.head hL) := by
  intro L hL
  cases L with
  | nil => contradiction
  | cons a rest => cases rest <;> rfl

theorem cyclicPairsAux_last_snd (first : V) : ∀ {L : List V} (hL : L ≠ []),
    ((cyclicPairsAux first L).getLast (cyclicPairsAux_ne_nil first hL)).2 = first := by
  intro L hL
  induction L using cyclicPairsAux.induct with
  | case1 => contradiction
  | case2 a => rfl
  | case3 a b rest ih =>
      cases rest with
      | nil => simp [cyclicPairsAux]
      | cons c rest =>
          simp only [cyclicPairsAux, List.getLast_cons_cons]
          exact ih (by simp)

theorem cyclicPairsAux_chain (first : V) : ∀ L,
    (cyclicPairsAux first L).IsChain (fun e f ↦ e.2 = f.1) := by
  intro L
  induction L using cyclicPairsAux.induct with
  | case1 => simp [cyclicPairsAux]
  | case2 a => simp [cyclicPairsAux]
  | case3 a b rest ih =>
      cases rest with
      | nil => simp [cyclicPairsAux]
      | cons c rest => simpa [cyclicPairsAux] using ih

theorem cyclicPairs_chain (L : List V) :
    (cyclicPairs L).IsChain (fun e f ↦ e.2 = f.1) := by
  cases L with
  | nil => simp [cyclicPairs]
  | cons a rest => exact cyclicPairsAux_chain a (a :: rest)

theorem cyclicPairs_closing {L : List V} (hL : L ≠ []) :
    ((cyclicPairs L).getLast (cyclicPairs_ne_nil hL)).2 =
      ((cyclicPairs L).head (cyclicPairs_ne_nil hL)).1 := by
  cases L with
  | nil => contradiction
  | cons a rest =>
      change ((cyclicPairsAux a (a :: rest)).getLast _).2 =
        ((cyclicPairsAux a (a :: rest)).head _).1
      have hlast := cyclicPairsAux_last_snd a (L := a :: rest) (by simp)
      have hhead := cyclicPairsAux_head_fst a (L := a :: rest) (by simp)
      exact hlast.trans hhead.symm

theorem cyclicPairsAux_rel {R : V → V → Prop} (first : V) :
    ∀ {L : List V} (hL : L ≠ []), L.IsChain R →
      R (L.getLast hL) first →
      ∀ e ∈ cyclicPairsAux first L, R e.1 e.2 := by
  intro L hL hchain hclose
  induction L using cyclicPairsAux.induct with
  | case1 => contradiction
  | case2 a => simpa [cyclicPairsAux] using hclose
  | case3 a b rest ih =>
      rw [List.isChain_cons_cons] at hchain
      intro e he
      change e ∈ (a, b) :: cyclicPairsAux first (b :: rest) at he
      simp only [List.mem_cons] at he
      rcases he with heq | he
      · subst e
        exact hchain.1
      · apply ih (by simp) hchain.2
        · simpa using hclose
        · exact he

theorem cyclicPairs_rel {R : V → V → Prop} (C : CycleCode R) :
    ∀ e ∈ cyclicPairs C.vertices, R e.1 e.2 := by
  cases hL : C.vertices with
  | nil => exact (C.nonempty hL).elim
  | cons a rest =>
      change ∀ e ∈ cyclicPairsAux a (a :: rest), R e.1 e.2
      apply cyclicPairsAux_rel (R := R) a (L := a :: rest) (by simp)
      · simpa [hL] using C.chain
      · have hc := C.closing
        simpa [hL] using hc

theorem pair_mem_cyclicPairsAux_append (first : V) (pre post : List V) (a b : V) :
    (a, b) ∈ cyclicPairsAux first (pre ++ a :: b :: post) := by
  induction pre with
  | nil => simp [cyclicPairsAux]
  | cons c pre ih =>
      cases pre with
      | nil =>
          change (a, b) ∈ (c, a) :: cyclicPairsAux first (a :: b :: post)
          rw [List.mem_cons]
          right
          change (a, b) ∈ (a, b) :: cyclicPairsAux first (b :: post)
          exact List.mem_cons_self
      | cons d pre =>
          change (a, b) ∈ (c, d) ::
            cyclicPairsAux first (d :: (pre ++ a :: b :: post))
          rw [List.mem_cons]
          right
          simpa only [List.cons_append] using ih

theorem pair_mem_cyclicPairs_append (pre post : List V) (a b : V) :
    (a, b) ∈ cyclicPairs (pre ++ a :: b :: post) := by
  cases pre with
  | nil => exact pair_mem_cyclicPairsAux_append a [] post a b
  | cons c pre => exact pair_mem_cyclicPairsAux_append c (c :: pre) post a b

theorem cyclicPairs_last_fst {L : List V} (hL : L ≠ []) :
    ((cyclicPairs L).getLast (cyclicPairs_ne_nil hL)).1 = L.getLast hL := by
  have hmap := congrArg List.getLast? (cyclicPairs_fst L)
  rw [List.getLast?_map,
    List.getLast?_eq_some_getLast (cyclicPairs_ne_nil hL),
    List.getLast?_eq_some_getLast hL] at hmap
  exact Option.some.inj hmap

theorem internal_pair_ne_cyclicPairs_last {L pre post : List V} {a b : V}
    (hL : L = pre ++ a :: b :: post) (hnd : L.Nodup) :
    (a, b) ≠ (cyclicPairs L).getLast (cyclicPairs_ne_nil (by
      rw [hL]
      simp)) := by
  intro heq
  have hafst : a = L.getLast (by rw [hL]; simp) := by
    exact congrArg Prod.fst heq |>.trans (cyclicPairs_last_fst _)
  rw [hL, List.nodup_append] at hnd
  have haNot : a ∉ b :: post := (List.nodup_cons.mp hnd.2.1).1
  have haMem : a ∈ b :: post := by
    have hget : L.getLast (by rw [hL]; simp) =
        (b :: post).getLast (by simp) := by
      subst L
      exact List.getLast_append_of_ne_nil _ (by simp)
    rw [hafst, hget]
    exact List.getLast_mem (by simp : b :: post ≠ [])
  exact haNot haMem

theorem isChain_attach_of_isChain {W : Type*} {r : W → W → Prop}
    {L : List W} (h : L.IsChain r) :
    L.attach.IsChain (fun x y ↦ r x.1 y.1) := by
  rw [List.isChain_attach]
  induction L with
  | nil => simp
  | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b rest =>
          rw [List.isChain_cons_cons] at h ⊢
          refine ⟨⟨by simp, by simp, h.1⟩, ?_⟩
          exact (ih h.2).imp (by
            intro x y hxy
            exact ⟨by simp [hxy.1], by simp [hxy.2.1], hxy.2.2⟩)

structure EdgePieceSystem (E : Type*) (R : V → V → Prop) where
  edges : List E
  edges_nonempty : edges ≠ []
  source : E → V
  target : E → V
  edge_chain : edges.IsChain (fun e f ↦ target e = source f)
  edge_closing : target (edges.getLast edges_nonempty) =
    source (edges.head edges_nonempty)
  piece : E → List V
  piece_nonempty : ∀ e ∈ edges, piece e ≠ []
  piece_nodup : ∀ e ∈ edges, (piece e).Nodup
  pieces_disjoint : edges.map piece |>.Pairwise List.Disjoint
  piece_chain : ∀ e ∈ edges, (piece e).IsChain R
  piece_head : ∀ e ∈ edges, (piece e).head? = some (source e)
  piece_exit : ∀ e (he : e ∈ edges),
    R ((piece e).getLast (piece_nonempty e he)) (target e)

theorem isChain_imp_of_mem {E : Type*} {r s : E → E → Prop} {L : List E}
    (h : L.IsChain r)
    (H : ∀ a ∈ L, ∀ b ∈ L, r a b → s a b) : L.IsChain s := by
  induction L with
  | nil => simp
  | cons a rest ih =>
      rw [List.isChain_cons] at h ⊢
      refine ⟨?_, ih h.2 ?_⟩
      · intro b hb
        have hbmem : b ∈ rest := List.mem_of_mem_head? (by simpa using hb)
        exact H a (by simp) b (by simp [hbmem]) (h.1 b hb)
      · intro x hx y hy hxy
        exact H x (by simp [hx]) y (by simp [hy]) hxy

noncomputable def EdgePieceSystem.toCyclicPieceSystem {E : Type*}
    {R : V → V → Prop} (S : EdgePieceSystem E R) : CyclicPieceSystem R := by
  have hE : S.edges ≠ [] := S.edges_nonempty
  refine
    { pieces := S.edges.map S.piece
      pieces_nonempty := by simp [hE]
      piece_nonempty := ?_
      piece_nodup := ?_
      pieces_disjoint := S.pieces_disjoint
      piece_chain := ?_
      bridge_chain := ?_
      closing := ?_ }
  · intro K hK
    rcases List.mem_map.mp hK with ⟨e, he, rfl⟩
    exact S.piece_nonempty e he
  · intro K hK
    rcases List.mem_map.mp hK with ⟨e, he, rfl⟩
    exact S.piece_nodup e he
  · intro K hK
    rcases List.mem_map.mp hK with ⟨e, he, rfl⟩
    exact S.piece_chain e he
  · rw [List.isChain_map]
    exact isChain_imp_of_mem S.edge_chain (by
      intro e' he' f' hf' hef
      intro x hx y hy
      have hx' : x = (S.piece e').getLast (S.piece_nonempty e' he') := by
        simpa [List.getLast?_eq_some_getLast (S.piece_nonempty e' he')] using hx.symm
      have hy' : y = S.source f' := by
        rw [S.piece_head f' hf'] at hy
        simpa using hy.symm
      simpa [hx', hy', hef] using S.piece_exit e' he')
  · let eLast := S.edges.getLast hE
    let eHead := S.edges.head hE
    have heLast : eLast ∈ S.edges := List.getLast_mem hE
    have heHead : eHead ∈ S.edges := List.head_mem hE
    have hpair : S.target eLast = S.source eHead := by
      simpa [eLast, eHead] using S.edge_closing
    have hlastPiece : (S.edges.map S.piece).getLast (by simp [hE]) =
        S.piece eLast := by
      simp [eLast]
    have hheadPiece : (S.edges.map S.piece).head (by simp [hE]) =
        S.piece eHead := by
      simp [eHead]
    have hlastVertex : ((S.edges.map S.piece).getLast (by simp [hE])).getLast
        (by
          rw [hlastPiece]
          exact S.piece_nonempty eLast heLast) =
        (S.piece eLast).getLast (S.piece_nonempty eLast heLast) := by
      apply Option.some.inj
      rw [← List.getLast?_eq_some_getLast, ← List.getLast?_eq_some_getLast,
        hlastPiece]
    have hheadVertex0 : ((S.edges.map S.piece).head (by simp [hE])).head
        (by
          rw [hheadPiece]
          exact S.piece_nonempty eHead heHead) =
        (S.piece eHead).head (S.piece_nonempty eHead heHead) := by
      apply Option.some.inj
      rw [← List.head?_eq_some_head, ← List.head?_eq_some_head,
        hheadPiece]
    have hheadVertex : (S.piece eHead).head
        (S.piece_nonempty eHead heHead) = S.source eHead :=
      (List.head_eq_iff_head?_eq_some _).mpr (S.piece_head eHead heHead)
    rw [hlastVertex, hheadVertex0, hheadVertex, ← hpair]
    exact S.piece_exit eLast heLast

noncomputable def EdgePieceSystem.toCycleCode {E : Type*} {R : V → V → Prop}
    (S : EdgePieceSystem E R) : CycleCode R :=
  S.toCyclicPieceSystem.toCycleCode

set_option maxRecDepth 2000 in
theorem EdgePieceSystem.cyclicEdge_of_singleton_piece {E : Type*}
    {R : V → V → Prop} (S : EdgePieceSystem E R) {e : E}
    (he : e ∈ S.edges) (hpiece : S.piece e = [S.source e]) :
    CyclicEdge S.toCycleCode.vertices (S.source e) (S.target e) := by
  rcases List.mem_iff_append.mp he with ⟨pre, post, hshape⟩
  cases post with
  | nil =>
      right
      right
      have hlast : S.toCycleCode.vertices.getLast? = some (S.source e) := by
        change ((S.edges.map S.piece).flatten).getLast? = _
        rw [hshape]
        simp [hpiece]
      have hhead : S.toCycleCode.vertices.head? = some (S.target e) := by
        change ((S.edges.map S.piece).flatten).head? = _
        cases pre with
        | nil =>
            have hclose : S.target e = S.source e := by
              simpa [hshape] using S.edge_closing
            simp [hshape, hpiece, hclose]
        | cons a rest =>
            have ha : a ∈ S.edges := by
              rw [hshape]
              simp
            have hclose : S.target e = S.source a := by
              simpa [hshape] using S.edge_closing
            have hane : S.piece a ≠ [] := S.piece_nonempty a ha
            have hahead := S.piece_head a ha
            rw [hshape]
            simp only [List.map_append, List.map_cons, List.map_nil,
              List.flatten_append, List.flatten_cons, List.flatten_nil,
              List.append_nil]
            simpa [hane, hclose] using hahead
      exact ⟨hhead, hlast⟩
  | cons f rest =>
      left
      left
      have hf : f ∈ S.edges := by
        rw [hshape]
        simp
      have hef : S.target e = S.source f :=
        (List.isChain_iff_forall_rel_of_append_cons_cons.mp S.edge_chain)
          hshape
      have hfne : S.piece f ≠ [] := S.piece_nonempty f hf
      have hfhead : (S.piece f).head? = some (S.target e) := by
        rw [hef]
        exact S.piece_head f hf
      have hfshape : S.piece f = S.target e :: (S.piece f).tail := by
        have hcons := List.cons_head_tail hfne
        rw [(List.head_eq_iff_head?_eq_some _).mpr hfhead] at hcons
        exact hcons.symm
      refine ⟨(pre.map S.piece).flatten,
        (S.piece f).tail ++ (rest.map S.piece).flatten, ?_⟩
      change (S.edges.map S.piece).flatten = _
      rw [hshape, List.map_append, List.flatten_append]
      rw [List.map_cons, List.flatten_cons, List.map_cons, List.flatten_cons]
      change (pre.map S.piece).flatten ++
          (S.piece e ++ (S.piece f ++ (rest.map S.piece).flatten)) = _
      rw [hpiece, hfshape]
      simp only [List.nil_append, List.tail_cons, List.cons_append]

section PetersenBlocks

open Ports

variable {n : Nat} [NeZero n]

abbrev NCRVertex (n : Nat) := NC (Finset.univ : Finset (Fin n))

noncomputable def rankGrayVertices (Q : CanonicalMatching n) :
    List (NCRVertex n) :=
  (rankGrayMasks Q).map Q.decodedNC

theorem rankGrayMasks_ne_nil (Q : CanonicalMatching n) :
    rankGrayMasks Q ≠ [] := by
  have hhead := Gray.grayList_head (rankCoords Q) (rankCoords_nodup Q)
  change (rankGrayMasks Q).head? = some ∅ at hhead
  intro hnil
  rw [hnil] at hhead
  simp at hhead

theorem rankGrayVertices_ne_nil (Q : CanonicalMatching n) :
    rankGrayVertices Q ≠ [] := by
  simp [rankGrayVertices, rankGrayMasks_ne_nil Q]

theorem rankGrayVertices_nodup (Q : CanonicalMatching n) :
    (rankGrayVertices Q).Nodup := by
  rw [rankGrayVertices, rankGrayMasks, List.nodup_map_iff_inj_on
    (Gray.grayList_nodup (rankCoords Q) (rankCoords_nodup Q))]
  intro A _ B _ h
  exact Gray.decodedNC_fixed_injective Q h

theorem rankGrayVertices_chain (Q : CanonicalMatching n) :
    (rankGrayVertices Q).IsChain
      (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj := by
  rw [rankGrayVertices, List.isChain_map]
  exact (Gray.grayList_chain (rankCoords Q) (rankCoords_nodup Q)).imp
    (fun _ _ h => Gray.decodedNC_adj_of_flipAdj Q h)

theorem rankGrayMasks_head (Q : CanonicalMatching n) :
    (rankGrayMasks Q).head? = some ∅ := by
  exact Gray.grayList_head (rankCoords Q) (rankCoords_nodup Q)

theorem rankGrayMasks_last (Q : CanonicalMatching n) (h : 0 < Q.free.card) :
    (rankGrayMasks Q).getLast? = some {highestFree Q h} := by
  have hcoords := rankCoords_highest_cons_tail Q h
  have hnd : (highestFree Q h :: (rankCoords Q).tail).Nodup := by
    rw [hcoords]
    exact rankCoords_nodup Q
  have hlast := Gray.grayList_last_cons (highestFree Q h) (rankCoords Q).tail hnd
  simpa [rankGrayMasks, hcoords] using hlast

theorem rankGrayVertices_head (Q : CanonicalMatching n) :
    (rankGrayVertices Q).head? = some (Q.decodedNC ∅) := by
  simp [rankGrayVertices, rankGrayMasks_head Q]

theorem rankGrayVertices_last (Q : CanonicalMatching n) (h : 0 < Q.free.card) :
    (rankGrayVertices Q).getLast? = some (Q.decodedNC {highestFree Q h}) := by
  simp [rankGrayVertices, rankGrayMasks_last Q h]

noncomputable def rankGrayCycle (Q : CanonicalMatching n) (h : 0 < Q.free.card) :
    CycleCode (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj where
  vertices := rankGrayVertices Q
  nonempty := rankGrayVertices_ne_nil Q
  nodup := rankGrayVertices_nodup Q
  chain := rankGrayVertices_chain Q
  closing := by
    have hlast := rankGrayVertices_last Q h
    have hhead := rankGrayVertices_head Q
    have hadj := Gray.decodedNC_adj_of_flipAdj Q (rankGray_closing_flip Q h)
    rw [(List.getLast_eq_iff_getLast?_eq_some _).mpr hlast,
      (List.head_eq_iff_head?_eq_some _).mpr hhead]
    exact hadj

theorem cyclicEdge_map_decoded_of_onRankGrayCycle
    (Q : CanonicalMatching n) (h : 0 < Q.free.card)
    {A B : Finset Q.free} (hedge : OnRankGrayCycle Q h A B) :
    CyclicEdge (rankGrayVertices Q) (Q.decodedNC A) (Q.decodedNC B) := by
  rcases hedge with hinside | hclosing
  · left
    rcases hinside with ⟨pre, post, hlist⟩ | ⟨pre, post, hlist⟩
    · left
      refine ⟨pre.map Q.decodedNC, post.map Q.decodedNC, ?_⟩
      simp [rankGrayVertices, hlist]
    · right
      refine ⟨pre.map Q.decodedNC, post.map Q.decodedNC, ?_⟩
      simp [rankGrayVertices, hlist]
  · rcases hclosing with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · right
      left
      exact ⟨rankGrayVertices_head Q, rankGrayVertices_last Q h⟩
    · right
      right
      exact ⟨rankGrayVertices_head Q, rankGrayVertices_last Q h⟩

set_option maxHeartbeats 800000 in
/-- One parent-child edge of the canonical block tree is a literal, fully
decoded square switch between the two NCR block cycles. -/
noncomputable def cycleAcrossJoiningDiamond
    (C : CanonicalMatching n) (hC : C.1.Nonempty) (hn : Even n) :
    CycleCode (NCRefinementGraph (Finset.univ : Finset (Fin n))).Adj := by
  let D := joiningDiamond C hC hn
  let P := parent C hC
  have hp : 0 < P.free.card := free_card_pos_of_even P hn
  have hc : 0 < C.free.card := free_card_pos_of_even C hn
  let parentCycle := rankGrayCycle P hp
  let childCycle := rankGrayCycle C hc
  have hpEdge : CyclicEdge parentCycle.vertices
      (P.decodedNC D.parentLower) (P.decodedNC D.parentUpper) := by
    simpa [parentCycle, P] using
      cyclicEdge_map_decoded_of_onRankGrayCycle P hp D.parentEdge
  have hcEdge : CyclicEdge childCycle.vertices
      (C.decodedNC D.childLower) (C.decodedNC D.childUpper) := by
    simpa [childCycle] using
      cyclicEdge_map_decoded_of_onRankGrayCycle C hc D.childEdge
  let parentPath := cutPathOfCyclicEdge NC.Adj_symm parentCycle hpEdge
  let childPath := cutPathOfCyclicEdge NC.Adj_symm childCycle
    (cyclicEdge_symm hcEdge)
  have hdisjoint : Disjoint parentCycle.vertices.toFinset childCycle.vertices.toFinset := by
    apply Finset.disjoint_left.mpr
    intro π hπP hπC
    have hPmem : ∃ A : Finset P.free, P.decodedNC A = π := by
      have hlist : π ∈ rankGrayVertices P := by
        simpa [parentCycle, rankGrayCycle] using hπP
      rcases List.mem_map.mp hlist with ⟨A, _hA, hA⟩
      exact ⟨A, hA⟩
    have hCmem : ∃ A : Finset C.free, C.decodedNC A = π := by
      have hlist : π ∈ rankGrayVertices C := by
        simpa [childCycle, rankGrayCycle] using hπC
      rcases List.mem_map.mp hlist with ⟨A, _hA, hA⟩
      exact ⟨A, hA⟩
    rcases hPmem with ⟨A, rfl⟩
    rcases hCmem with ⟨B, hEq⟩
    have hmatch := congrArg Encoding.canonicalMatching hEq
    have hCP : C = P := by
      simpa [Encoding.canonicalMatching_decodedNC] using hmatch
    have hparent : P.1.card + 1 = C.1.card := by
      simpa [P] using parent_card C hC
    rw [← hCP] at hparent
    omega
  exact cycleCodeSpliceAcrossSquare parentPath childPath hdisjoint
    (by simpa [P, D] using D.crossUpper)
    (by simpa [P, D] using D.crossLower.symm)

end PetersenBlocks

end Switch
end Petersen
end Hamilton.Infrastructure
