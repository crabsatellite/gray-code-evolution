/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Data.Bool.Count

/-!
# Hamilton paths with prescribed endpoints

Mathlib has `SimpleGraph.Walk.IsHamiltonian` (path visiting each
vertex exactly once) and `SimpleGraph.IsHamiltonian` (has Hamilton
cycle).  This file adds:

* `SimpleGraph.HamiltonianPathBetween a b` — graph has a Hamilton
  path from `a` to `b`.
* `SimpleGraph.IsHamiltonianPath` — graph has some Hamilton path.

Used for recursive Hamilton constructions where specific endpoints
matter (e.g., gluing two Hamilton paths into a longer path).

## Main definitions

* `SimpleGraph.HamiltonianPathBetween`
* `SimpleGraph.IsHamiltonianPath`

## Main results

* `SimpleGraph.HamiltonianPathBetween.self` — for singleton vertex
  type, trivial Hamilton path.

## Tags

SimpleGraph, Hamilton path, Mathlib contribution
-/

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}

/-- `G` has a Hamiltonian path from `a` to `b`: a walk visiting every
vertex exactly once. -/
def HamiltonianPathBetween (G : SimpleGraph α) (a b : α) : Prop :=
  ∃ p : G.Walk a b, p.IsHamiltonian

/-- `G` has some Hamiltonian path. -/
def IsHamiltonianPath (G : SimpleGraph α) : Prop :=
  ∃ a b : α, G.HamiltonianPathBetween a b

/-- For singleton vertex type, every graph has trivial Hamilton path
(of length 0). -/
theorem HamiltonianPathBetween.of_subsingleton (G : SimpleGraph α)
    [Subsingleton α] (a b : α) : G.HamiltonianPathBetween a b := by
  refine ⟨(Walk.nil : G.Walk a a).copy rfl (Subsingleton.elim a b), ?_⟩
  exact Walk.IsHamiltonian.of_subsingleton

/-- Length of a Hamilton path is `Fintype.card α - 1`. -/
theorem HamiltonianPathBetween.exists_length_eq [Fintype α]
    {a b : α} (h : G.HamiltonianPathBetween a b) :
    ∃ p : G.Walk a b, p.IsHamiltonian ∧ p.length = Fintype.card α - 1 := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp, hp.length_eq⟩

/-- Hamilton path is symmetric: if `G.HamiltonianPathBetween a b`,
then `G.HamiltonianPathBetween b a`. -/
theorem HamiltonianPathBetween.symm {a b : α} (h : G.HamiltonianPathBetween a b) :
    G.HamiltonianPathBetween b a := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.reverse, ?_⟩
  intro v
  rw [Walk.support_reverse]
  rw [List.count_reverse]
  exact hp v

/-- A graph with a Hamilton cycle and more than one vertex has a Hamilton
path.  Delete one edge from the cycle by taking its tail. -/
theorem IsHamiltonian.isHamiltonianPath [Fintype α]
    (hG : G.IsHamiltonian) (h_card_ne_one : Fintype.card α ≠ 1) :
    G.IsHamiltonianPath := by
  obtain ⟨a, c, hc⟩ := hG h_card_ne_one
  exact ⟨c.snd, a, c.tail, hc.isHamiltonian_tail⟩

/-- Along a Hamilton path in a properly two-coloured finite graph, the two
colour classes differ in size by at most one. -/
theorem Walk.IsHamiltonian.classes_card_diff_at_most_one [Fintype α]
    {a b : α} {p : G.Walk a b} (hp : p.IsHamiltonian)
    (c : G.Coloring Bool) :
    ((Finset.univ : Finset α).filter (fun v => c v = true)).card ≤
        ((Finset.univ : Finset α).filter (fun v => c v = false)).card + 1 ∧
      ((Finset.univ : Finset α).filter (fun v => c v = false)).card ≤
        ((Finset.univ : Finset α).filter (fun v => c v = true)).card + 1 := by
  classical
  have h_supp_nodup : p.support.Nodup := hp.isPath.support_nodup
  have h_supp_len : p.support.length = Fintype.card α := hp.length_support
  have h_supp_mem : ∀ v, v ∈ p.support := hp.mem_support
  have h_chain_map : List.IsChain (· ≠ ·) (p.support.map c) :=
    List.isChain_map_of_isChain c (fun _ _ h => c.valid h) p.isChain_adj_support
  have h_true_le_false :
      (p.support.map c).count true ≤ (p.support.map c).count false + 1 := by
    simpa using h_chain_map.count_not_le_count_add_one false
  have h_false_le_true :
      (p.support.map c).count false ≤ (p.support.map c).count true + 1 := by
    simpa using h_chain_map.count_not_le_count_add_one true
  have h_supp_val : (p.support : Multiset α) = Finset.univ.val := by
    refine Multiset.eq_of_le_of_card_le ?_ ?_
    · rw [Multiset.le_iff_count]
      intro v
      have hc1 : (p.support : Multiset α).count v = 1 := by
        rw [Multiset.coe_count]
        exact List.count_eq_one_of_mem h_supp_nodup (h_supp_mem v)
      have hc2 : (Finset.univ.val : Multiset α).count v = 1 :=
        Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ v)
      omega
    · simp [Multiset.coe_card, h_supp_len]
  have h_to_finset : ∀ x : Bool,
      (p.support.map c).count x =
        ((Finset.univ : Finset α).filter (fun v => c v = x)).card := by
    intro x
    have h1 : (p.support.map c).count x =
        ((p.support : Multiset α).map c).count x := by
      rw [Multiset.map_coe, Multiset.coe_count]
    rw [h1, Multiset.count_map, h_supp_val]
    rw [show Multiset.filter (fun v => x = c v) Finset.univ.val =
          Multiset.filter (fun v => c v = x) Finset.univ.val from
        Multiset.filter_congr (fun v _ => eq_comm)]
    rfl
  constructor
  · rwa [h_to_finset true, h_to_finset false] at h_true_le_false
  · rwa [h_to_finset false, h_to_finset true] at h_false_le_true

/-- A Hamilton path in a properly two-coloured finite graph forces its two
colour classes to differ in size by at most one. -/
theorem HamiltonianPathBetween.classes_card_diff_at_most_one [Fintype α]
    {a b : α} (h : G.HamiltonianPathBetween a b) (c : G.Coloring Bool) :
    ((Finset.univ : Finset α).filter (fun v => c v = true)).card ≤
        ((Finset.univ : Finset α).filter (fun v => c v = false)).card + 1 ∧
      ((Finset.univ : Finset α).filter (fun v => c v = false)).card ≤
        ((Finset.univ : Finset α).filter (fun v => c v = true)).card + 1 := by
  obtain ⟨p, hp⟩ := h
  exact hp.classes_card_diff_at_most_one c

/-- If a properly two-coloured finite graph has some Hamilton path, its two
colour classes differ in size by at most one. -/
theorem IsHamiltonianPath.classes_card_diff_at_most_one [Fintype α]
    (h : G.IsHamiltonianPath) (c : G.Coloring Bool) :
    ((Finset.univ : Finset α).filter (fun v => c v = true)).card ≤
        ((Finset.univ : Finset α).filter (fun v => c v = false)).card + 1 ∧
      ((Finset.univ : Finset α).filter (fun v => c v = false)).card ≤
        ((Finset.univ : Finset α).filter (fun v => c v = true)).card + 1 := by
  obtain ⟨a, b, hab⟩ := h
  exact hab.classes_card_diff_at_most_one c

/-- For `G.IsHamiltonian`, the vertex type cardinality is either `1`
or `≥ 3`.

(`= 0` is excluded by `not_isHamiltonian_of_isEmpty`; `= 2` is
excluded by `not_isHamiltonian_of_card_eq_two`.)  -/
theorem IsHamiltonian.card_eq_one_or_three_le [Fintype α]
    (hG : G.IsHamiltonian) :
    Fintype.card α = 1 ∨ 3 ≤ Fintype.card α := by
  by_cases h1 : Fintype.card α = 1
  · left; exact h1
  · right
    obtain ⟨a, p, hp⟩ := hG h1
    have h_cyc : 3 ≤ p.length := hp.isCycle.three_le_length
    have h_len : p.length = Fintype.card α := hp.length_eq
    omega

/-- **Bipartite Hamilton necessary condition**: if `G` is 2-colorable
and has a Hamilton cycle (and `card α ≠ 1`), then `card α` is even.

Proof: along the Hamilton cycle, colors alternate.  For a closed walk
(start = end), the # of edges is even.  Hamilton cycle has length =
`card α`, so `card α` is even. -/
theorem IsHamiltonian.even_card_of_colorable_two [Fintype α]
    (hG : G.IsHamiltonian) (h_bipart : G.Colorable 2)
    (hn1 : Fintype.card α ≠ 1) :
    Even (Fintype.card α) := by
  obtain ⟨a, p, hp⟩ := hG hn1
  have h_len : p.length = Fintype.card α := hp.length_eq
  rw [← h_len]
  obtain ⟨c⟩ := h_bipart
  let c' : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv c
  exact (c'.even_length_iff_congr p).mpr Iff.rfl

/-- For an `α` of odd cardinality (≥ 3), a 2-colorable graph
cannot be Hamiltonian. -/
theorem not_isHamiltonian_of_colorable_two_odd [Fintype α]
    (h_bipart : G.Colorable 2) (h_odd : Odd (Fintype.card α))
    (h3 : 3 ≤ Fintype.card α) :
    ¬ G.IsHamiltonian := by
  intro hG
  have hn1 : Fintype.card α ≠ 1 := by omega
  have h_even := hG.even_card_of_colorable_two h_bipart hn1
  exact (Nat.not_even_iff_odd.mpr h_odd) h_even

/-! ### Walk-getVert index recovery and Pósa rotated-walk construction -/

/-- **Index recovery via `getVert` on a path**: for any path `p :
G.Walk a b`, `idxOf (p.getVert i) p.support = i` whenever `i ≤
p.length`.

Pure Mathlib-quality generic graph theory; underpins the
Pósa rotated-walk construction. -/
theorem idxOf_getVert_eq_of_isPath {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) (i : ℕ) (hi : i ≤ p.length) :
    List.idxOf (p.getVert i) p.support = i := by
  have hmem : p.getVert i ∈ p.support :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨i, rfl, hi⟩
  have h_eq : p.getVert (p.support.idxOf (p.getVert i)) = p.getVert i :=
    p.getVert_support_idxOf hmem
  have hidx_lt : p.support.idxOf (p.getVert i) < p.support.length :=
    List.idxOf_lt_length_of_mem hmem
  have hlen : p.support.length = p.length + 1 :=
    SimpleGraph.Walk.length_support p
  have hidx_le : p.support.idxOf (p.getVert i) ≤ p.length := by omega
  exact hp.getVert_injOn hidx_le hi h_eq


theorem Walk.IsHamiltonian.posa_rotated {α : Type*} [DecidableEq α]
    [Fintype α] {G : SimpleGraph α} {s a : α} (p : G.Walk s a)
    (hp : p.IsHamiltonian) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i + 1 < p.length)
    (hadj : G.Adj (p.getVert i) a) :
    ∃ p' : G.Walk s (p.getVert (i + 1)), p'.IsHamiltonian := by
  have hp_path : p.IsPath := hp.isPath
  have hvi_mem : p.getVert i ∈ p.support := hp.mem_support _
  have hvi1_mem : p.getVert (i + 1) ∈ p.support := hp.mem_support _
  have hidx_vi : p.support.idxOf (p.getVert i) = i :=
    idxOf_getVert_eq_of_isPath hp_path i (by omega)
  have hidx_vi1 : p.support.idxOf (p.getVert (i + 1)) = i + 1 :=
    idxOf_getVert_eq_of_isPath hp_path (i + 1) (by omega)
  set prefix_w : G.Walk s (p.getVert i) := p.takeUntil _ hvi_mem with hprefix_def
  set suffix_w : G.Walk (p.getVert (i + 1)) a := p.dropUntil _ hvi1_mem with hsuffix_def
  set rotated : G.Walk s (p.getVert (i + 1)) :=
    (prefix_w.concat hadj).append suffix_w.reverse with hrotated_def
  -- prefix.support = take (i+1) of p.support
  have h_prefix_support :
      prefix_w.support = p.support.take (i + 1) := by
    rw [hprefix_def, SimpleGraph.Walk.takeUntil_eq_take,
        SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.take_support_eq_support_take_succ, hidx_vi]
  -- suffix.support = drop (i+1) of p.support
  have h_suffix_support :
      suffix_w.support = p.support.drop (i + 1) := by
    rw [hsuffix_def, SimpleGraph.Walk.dropUntil_eq_drop,
        SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.drop_support_eq_support_drop_min, hidx_vi1]
    congr 1
    omega
  -- L₂ := drop (i+1) p.support nonempty
  have hL₂_ne : p.support.drop (i + 1) ≠ [] := by
    rw [← List.length_pos_iff, List.length_drop,
        SimpleGraph.Walk.length_support]
    omega
  have h_L₂_last :
      (p.support.drop (i + 1)).getLast hL₂_ne = a := by
    rw [List.getLast_drop]
    exact p.getLast_support
  have h_L₂_reverse :
      a :: (p.support.drop (i + 1)).reverse.tail =
        (p.support.drop (i + 1)).reverse := by
    conv_rhs =>
      rw [show p.support.drop (i + 1) =
              (p.support.drop (i + 1)).dropLast ++
                [(p.support.drop (i + 1)).getLast hL₂_ne] from
            (List.dropLast_append_getLast hL₂_ne).symm,
          List.reverse_append, h_L₂_last]
    simp
  have h_rotated_support :
      rotated.support =
        p.support.take (i + 1) ++ ((p.support.drop (i + 1)).reverse) := by
    rw [hrotated_def, SimpleGraph.Walk.support_append,
        SimpleGraph.Walk.support_concat,
        SimpleGraph.Walk.support_reverse, h_prefix_support, h_suffix_support]
    rw [List.append_assoc, ← h_L₂_reverse]
    rfl
  -- support permutation
  have h_perm : rotated.support.Perm p.support := by
    rw [h_rotated_support]
    have hperm_rev :
        (p.support.drop (i + 1)).reverse.Perm (p.support.drop (i + 1)) :=
      List.reverse_perm _
    have hperm := hperm_rev.append_left (p.support.take (i + 1))
    rwa [List.take_append_drop] at hperm
  have h_rotated_isPath : rotated.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    exact (h_perm.nodup_iff).mpr hp_path.support_nodup
  have h_rotated_length : rotated.length = Fintype.card α - 1 := by
    have hP_len : p.length = Fintype.card α - 1 := hp.length_eq
    have h_prefix_len : prefix_w.length = i := by
      rw [hprefix_def, SimpleGraph.Walk.length_takeUntil, hidx_vi]
    have h_suffix_len : suffix_w.length = p.length - (i + 1) := by
      rw [hsuffix_def, SimpleGraph.Walk.length_dropUntil, hidx_vi1]
    rw [hrotated_def, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse,
        h_prefix_len, h_suffix_len]
    omega
  refine ⟨rotated, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonian_iff_isPath_and_length_eq]
  exact ⟨h_rotated_isPath, h_rotated_length⟩

/-! ### Closable Hamilton path → Hamilton cycle

A Hamilton path whose endpoints are adjacent can be closed into a
Hamilton cycle (provided the vertex count is `≥ 3`). -/

/-- **Path with `s(a,b)`-wrap-edge has length 1**: a path `p : G.Walk
a b` containing `s(a, b)` in its edge list must have length 1.

This is the "no wrap-around" lemma for paths: a non-trivial path
cannot return to the edge between its endpoints.

Generic pure graph theory; suitable for Mathlib. -/
theorem path_no_wrap_edge {V : Type*} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) :
    p.IsPath → s(a, b) ∈ p.edges → p.length = 1 := by
  induction p with
  | nil => intro _ he; simp at he
  | cons h q _ =>
    intro hp he
    rw [SimpleGraph.Walk.edges_cons] at he
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    obtain ⟨hq, ha_notin⟩ := hp
    rcases List.mem_cons.mp he with heq | hmem
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, hbc⟩ | ⟨hac, _⟩
      · subst hbc
        rw [SimpleGraph.Walk.isPath_iff_eq_nil] at hq
        subst hq
        rfl
      · subst hac
        exact absurd h G.irrefl
    · exact absurd (q.fst_mem_support_of_mem_edges hmem) ha_notin

/-- **Closable Hamilton path yields Hamilton cycle**: given a graph
`G` with `≥ 3` vertices and a Hamilton walk from `a` to `b` with the
endpoints adjacent (`G.Adj b a`), the closing edge produces a
Hamilton cycle.

Generic pure graph theory, building block for paper-style Hamilton
cycle constructions via Hamilton paths. -/
theorem Walk.IsHamiltonian.isHamiltonian_of_adj_endpoints {α : Type*}
    [DecidableEq α] [Fintype α] {G : SimpleGraph α}
    (hcard : 3 ≤ Fintype.card α) {a b : α} {p : G.Walk a b}
    (hp : p.IsHamiltonian) (hadj : G.Adj b a) :
    G.IsHamiltonian := by
  intro _hcard_ne
  have hlen : p.length = Fintype.card α - 1 := hp.length_eq
  refine ⟨a, SimpleGraph.Walk.cons (G.symm hadj) p.reverse, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨hp.isPath.reverse, ?_⟩
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
    intro hmem
    have h_one := path_no_wrap_edge p hp.isPath hmem
    omega
  · rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse]
    omega

/-- `HamiltonianPathBetween` with adjacent endpoints implies the
graph has a Hamilton cycle (given vertex count ≥ 3). -/
theorem HamiltonianPathBetween.isHamiltonian_of_adj {α : Type*}
    [DecidableEq α] [Fintype α] {G : SimpleGraph α}
    (hcard : 3 ≤ Fintype.card α) {a b : α}
    (hp : G.HamiltonianPathBetween a b) (hadj : G.Adj b a) :
    G.IsHamiltonian := by
  obtain ⟨p, hp_ham⟩ := hp
  exact Walk.IsHamiltonian.isHamiltonian_of_adj_endpoints hcard hp_ham hadj

/-! ### Hamilton-laceability (generic, Mathlib-quality)

A `Coloring α`-laceable graph has a Hamilton path between every pair
of differently-colored vertices.  When the graph is connected on ≥ 3
vertices, laceability implies a Hamilton cycle: pick an edge (which
exists by connectivity + ≥ 2 vertices), endpoints have different
colors (any proper coloring satisfies this on edges), and the
laceable Hamilton path closes via the edge. -/

/-- A graph `G` is **`c`-Hamilton-laceable** (w.r.t. a 2-coloring
`c`) iff every pair of differently-colored vertices is connected by
a Hamilton path.

The cleanest formulation: parameterized by a `Bool`-valued coloring.
Generalizes the bipartite Hamilton-laceability conjecture (paper
Conjecture `conj:hampath` for NCR). -/
def IsHamiltonianLaceable {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (c : G.Coloring Bool) : Prop :=
  ∀ a b : α, c a ≠ c b → G.HamiltonianPathBetween a b

/-- **Laceable + connected + size ≥ 3 ⇒ Hamilton cycle**.

Pure graph theory: pick any edge (exists by connectivity on ≥ 2
vertices); its endpoints are oppositely colored (every edge in a
proper coloring); laceability gives a Hamilton path between them;
close with the edge.

This is the generic Mathlib-quality version of paper Conjecture
`conj:hampath` ⇒ paper Conjecture `conj:main`. -/
theorem IsHamiltonianLaceable.isHamiltonian {α : Type*} [DecidableEq α]
    [Fintype α] {G : SimpleGraph α} {c : G.Coloring Bool}
    (h_conn : G.Connected) (h_card3 : 3 ≤ Fintype.card α)
    (h_lace : G.IsHamiltonianLaceable c) :
    G.IsHamiltonian := by
  -- Get two distinct vertices (card ≥ 3 ≥ 2).
  obtain ⟨a, b, h_ne⟩ : ∃ a b : α, a ≠ b := by
    by_contra h
    have h_all : ∀ x y : α, x = y := fun x y => not_not.mp (fun hne => h ⟨x, y, hne⟩)
    have : Subsingleton α := ⟨fun x y => h_all x y⟩
    have hcard1 : Fintype.card α ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr this
    omega
  -- Walk a → b by connectivity; pick first edge.
  obtain ⟨w⟩ := h_conn.preconnected a b
  let t : α := w.snd
  have h_adj : G.Adj a t := w.adj_snd (SimpleGraph.Walk.not_nil_of_ne h_ne)
  -- Endpoints of an edge get different colors.
  have h_color_ne : c t ≠ c a := by
    have := c.valid h_adj
    intro h
    exact this h.symm
  -- Laceability: Hamilton path t → a.
  obtain ⟨p, hp⟩ := h_lace t a h_color_ne
  -- Close via the edge.
  exact Walk.IsHamiltonian.isHamiltonian_of_adj_endpoints h_card3 hp h_adj

/-! ### Hamilton-laceability cardinality conditions

For a bipartite graph `G` (2-colored by `c : G.Coloring Bool`), if `G`
is `c`-Hamilton-laceable AND both color classes are nonempty, then
`Fintype.card α` must be **even** — because every Hamilton path goes
between vertices of different colors, has length `|V| - 1`, and walk
parity along a 2-coloring forces opposite colors at odd-length
endpoints (hence `|V| - 1` odd, hence `|V|` even). -/

/-- **Laceable + both classes nonempty ⇒ even cardinality**.

For any bipartite graph with both color classes nonempty, if it is
Hamilton-laceable, then `|V|` is even.

This is the bipartite analogue of `IsHamiltonian.even_card_of_colorable_two`
for laceability (which gives strictly stronger conclusion than
Hamilton cycle does — laceability requires `|class₀| = |class₁| =
|V|/2` exactly). -/
theorem IsHamiltonianLaceable.even_card {α : Type*} [DecidableEq α]
    [Fintype α] {G : SimpleGraph α} {c : G.Coloring Bool}
    (h_lace : G.IsHamiltonianLaceable c)
    {a b : α} (h_ne_color : c a ≠ c b) :
    Even (Fintype.card α) := by
  -- Get Hamilton path a → b via laceability.
  obtain ⟨p, hp⟩ := h_lace a b h_ne_color
  -- Length = |V| - 1; colors differ at endpoints; hence length odd.
  have h_len : p.length = Fintype.card α - 1 := hp.length_eq
  have h_odd : Odd p.length := by
    rw [c.odd_length_iff_not_congr]
    cases hca : c a <;> cases hcb : c b <;> simp_all
  -- length odd → length + 1 even → |V| even.
  rcases h_odd with ⟨k, hk⟩
  refine ⟨k + 1, ?_⟩
  -- |V| - 1 = 2k + 1, so |V| = 2k + 2 = 2(k+1)
  have h_card_pos : 1 ≤ Fintype.card α := by
    by_contra h
    have h0 : Fintype.card α = 0 := by omega
    have h_empty : IsEmpty α := Fintype.card_eq_zero_iff.mp h0
    exact h_empty.false a
  omega

/-! ### Graph-iso transport of Hamilton paths -/

/-- Hamilton path between specific endpoints transports under a graph
isomorphism. -/
theorem HamiltonianPathBetween.map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G : SimpleGraph α} {H : SimpleGraph β} (φ : G ≃g H)
    {a b : α} (h : G.HamiltonianPathBetween a b) :
    H.HamiltonianPathBetween (φ a) (φ b) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.map φ.toHom, ?_⟩
  exact hp.map _ φ.toEquiv.bijective

/-- `IsHamiltonianPath` transports under a graph isomorphism. -/
theorem IsHamiltonianPath.map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G : SimpleGraph α} {H : SimpleGraph β} (φ : G ≃g H)
    (h : G.IsHamiltonianPath) : H.IsHamiltonianPath := by
  obtain ⟨a, b, h_path⟩ := h
  exact ⟨φ a, φ b, h_path.map φ⟩

/-- **Complement coloring** of a `Bool`-valued graph coloring: just
negates each color.  Still a valid graph coloring (since adjacent
endpoints had different colors, their negations are also different). -/
def Coloring.complement {α : Type*} {G : SimpleGraph α} (c : G.Coloring Bool) :
    G.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun v => !(c v))
    (fun {u v} h_adj => by
      have h_ne := c.valid h_adj
      intro h_eq
      apply h_ne
      cases h_u : c u <;> cases h_v : c v <;> simp_all)

/-- **Apply lemma** for `Coloring.complement`: `c.complement v = !(c v)`. -/
theorem Coloring.complement_eq {α : Type*} {G : SimpleGraph α}
    (c : G.Coloring Bool) (v : α) :
    Coloring.complement c v = !(c v) := rfl

/-- **Laceability is preserved under coloring complement**: if `G` is
`c`-laceable, then `G` is `c.complement`-laceable.

Useful: shows Hamilton-laceability is a property of the bipartition
(both classes), not the specific direction. -/
theorem IsHamiltonianLaceable.complement {α : Type*} [DecidableEq α]
    {G : SimpleGraph α} {c : G.Coloring Bool}
    (h_lace : G.IsHamiltonianLaceable c) :
    G.IsHamiltonianLaceable c.complement := by
  intro a b h_ne
  apply h_lace a b
  intro h_c_eq
  apply h_ne
  rw [Coloring.complement_eq, Coloring.complement_eq, h_c_eq]

/-- **`IsHamiltonianLaceable` transports under a coloring-preserving
graph isomorphism**.

If `G ≃g H` via `φ`, and `H`'s coloring `c'` corresponds to `G`'s
coloring `c` via `φ` (`c' (φ v) = c v` for all `v`), then `G`-laceable
implies `H`-laceable.

Useful for transporting laceability through graph automorphisms
(e.g., NCR rotation symmetry preserving the `numBlocksParity`
coloring). -/
theorem IsHamiltonianLaceable.map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G : SimpleGraph α} {H : SimpleGraph β} (φ : G ≃g H)
    {c : G.Coloring Bool} {c' : H.Coloring Bool}
    (h_color : ∀ v : α, c' (φ v) = c v)
    (h_lace : G.IsHamiltonianLaceable c) :
    H.IsHamiltonianLaceable c' := by
  intro a' b' h_color_ne
  -- a', b' ∈ β. Get preimages a = φ.symm a', b = φ.symm b'.
  let a := φ.symm a'
  let b := φ.symm b'
  have h_φa : φ a = a' := φ.apply_symm_apply a'
  have h_φb : φ b = b' := φ.apply_symm_apply b'
  -- Coloring on a vs b differs.
  have h_c_ne : c a ≠ c b := by
    intro h_eq
    apply h_color_ne
    rw [← h_φa, ← h_φb, h_color a, h_color b, h_eq]
  -- Laceability on G gives a Hamilton path a → b.
  obtain ⟨p, hp⟩ := h_lace a b h_c_ne
  -- Transport via φ to a Hamilton path φ a → φ b = a' → b'.
  rw [← h_φa, ← h_φb]
  refine ⟨p.map φ.toHom, ?_⟩
  exact hp.map _ φ.toEquiv.bijective

end SimpleGraph
