/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.HamiltonPath
import Mathlib.Data.Bool.Count

/-!
# Bipartite Hamilton cycle: color classes have equal cardinality

If a graph `G` has a Hamilton cycle and is 2-colorable, then the two
color classes have equal size.

This is a refinement of `SimpleGraph.IsHamiltonian.even_card_of_colorable_two`:
the cycle alternates colors, and for an even-length cycle, half the
vertices are each color.

## Main results

* `SimpleGraph.Walk.IsHamiltonianCycle.classes_card_eq` — bipartite +
  Hamilton cycle ⇒ |E| = |O|.
* `SimpleGraph.IsHamiltonian.classes_card_eq` — bipartite + Hamilton
  graph ⇒ |E| = |O|.
* `SimpleGraph.not_isHamiltonian_of_classes_card_ne` — corollary for
  use as a Hamilton obstruction.

## Tags

SimpleGraph, Hamilton cycle, bipartite, parity, Mathlib contribution
-/

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}

namespace Walk

namespace IsHamiltonianCycle

/-- For a Hamilton cycle and a 2-coloring, the two color classes have
equal cardinality. -/
theorem classes_card_eq [Fintype α] {a : α} {p : G.Walk a a}
    (hp : p.IsHamiltonianCycle) (c : G.Coloring Bool) :
    (Finset.univ.filter (fun v => c v = true)).card =
    (Finset.univ.filter (fun v => c v = false)).card := by
  -- Setup: support.tail visits each vertex exactly once
  have hcyc : p.IsCycle := hp.isCycle
  have hnnil : ¬ p.Nil := hcyc.not_nil
  have h_path : p.tail.IsHamiltonian := hp.isHamiltonian_tail
  have h_tail_eq : p.tail.support = p.support.tail :=
    p.support_tail_of_not_nil hnnil
  have h_tail_nodup : p.support.tail.Nodup :=
    h_tail_eq ▸ h_path.isPath.support_nodup
  have h_tail_mem : ∀ v, v ∈ p.support.tail := fun v =>
    h_tail_eq ▸ h_path.mem_support v
  have h_len_tail : p.support.tail.length = Fintype.card α := by
    rw [← h_tail_eq]; exact h_path.length_support
  -- p.support.tail.map c is an alternating Bool list
  have h_adj_chain : List.IsChain G.Adj p.support := p.isChain_adj_support
  have h_chain_tail : List.IsChain G.Adj p.support.tail := h_adj_chain.tail
  have h_chain_map : List.IsChain (· ≠ ·) (p.support.tail.map c) :=
    List.isChain_map_of_isChain c (fun _ _ h => c.valid h) h_chain_tail
  
  have h_card_ge3 : 3 ≤ Fintype.card α := hp.length_eq ▸ hcyc.three_le_length
  have hn1 : Fintype.card α ≠ 1 := by omega
  have h_even_card : Even (Fintype.card α) := by
    have hG : G.IsHamiltonian := fun _ => ⟨a, p, hp⟩
    exact hG.even_card_of_colorable_two
      ⟨SimpleGraph.recolorOfEquiv G finTwoEquiv.symm c⟩ hn1
  have h_even_map_len : Even (p.support.tail.map c).length := by
    rw [List.length_map, h_len_tail]; exact h_even_card
  -- Apply IsChain.count_not_eq_count to get count false = count true
  have h_count_eq : (p.support.tail.map c).count false =
      (p.support.tail.map c).count true := by
    have h := h_chain_map.count_not_eq_count h_even_map_len true
    simpa using h
  -- Bridge: list count to Finset filter card
  -- Use Multiset: (p.support.tail : Multiset α) = Finset.univ.val
  have h_supp_val : (↑p.support.tail : Multiset α) = Finset.univ.val := by
    refine Multiset.eq_of_le_of_card_le ?_ ?_
    · rw [Multiset.le_iff_count]
      intro v
      have hc1 : (↑p.support.tail : Multiset α).count v = 1 := by
        rw [Multiset.coe_count]
        exact List.count_eq_one_of_mem h_tail_nodup (h_tail_mem v)
      have hc2 : (Finset.univ.val : Multiset α).count v = 1 :=
        Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ v)
      omega
    · simp [Multiset.coe_card, h_len_tail]
  -- Now bridge to Finset filter via Multiset.count_map
  have h_to_finset : ∀ (x : Bool),
      (p.support.tail.map c).count x =
        (Finset.univ.filter (fun v => c v = x)).card := by
    intro x
    have h1 : (p.support.tail.map c).count x =
        ((↑p.support.tail : Multiset α).map c).count x := by
      rw [Multiset.map_coe, Multiset.coe_count]
    rw [h1, Multiset.count_map, h_supp_val]
    -- Goal: (Finset.univ.val.filter (fun a => x = c a)).card = (Finset.univ.filter (c · = x)).card
    rw [show Multiset.filter (fun a => x = c a) Finset.univ.val =
            Multiset.filter (fun a => c a = x) Finset.univ.val from
       Multiset.filter_congr (fun v _ => eq_comm)]
    rfl
  rw [← h_to_finset true, ← h_to_finset false, h_count_eq]

end IsHamiltonianCycle

end Walk

variable [Fintype α]

/-- **Bipartite Hamilton classes balanced**: if `G` is 2-colorable and
`G.IsHamiltonian`, then the two color classes have equal cardinality.
(Modulo `card α = 1` exception, which is the trivial Hamilton case.) -/
theorem IsHamiltonian.classes_card_eq (hG : G.IsHamiltonian)
    (c : G.Coloring Bool) (hn1 : Fintype.card α ≠ 1) :
    (Finset.univ.filter (fun v => c v = true)).card =
    (Finset.univ.filter (fun v => c v = false)).card := by
  obtain ⟨_, p, hp⟩ := hG hn1
  exact hp.classes_card_eq c

/-- For a 2-colorable graph with unequal color classes, the graph is
not Hamiltonian. -/
theorem not_isHamiltonian_of_classes_card_ne
    (c : G.Coloring Bool) (hn1 : Fintype.card α ≠ 1)
    (h_ne : (Finset.univ.filter (fun v => c v = true)).card ≠
            (Finset.univ.filter (fun v => c v = false)).card) :
    ¬ G.IsHamiltonian := fun hG => h_ne (hG.classes_card_eq c hn1)

/-- **Class size formula**: for a Hamiltonian 2-colorable graph (with
`card α ≠ 1`), each color class has cardinality exactly `card α / 2`. -/
theorem IsHamiltonian.classes_card_eq_half (hG : G.IsHamiltonian)
    (c : G.Coloring Bool) (hn1 : Fintype.card α ≠ 1) :
    (Finset.univ.filter (fun v => c v = true)).card = Fintype.card α / 2 ∧
    (Finset.univ.filter (fun v => c v = false)).card = Fintype.card α / 2 := by
  have h_eq := hG.classes_card_eq c hn1
  have h_sum :
      (Finset.univ.filter (fun v => c v = true)).card +
        (Finset.univ.filter (fun v => c v = false)).card = Fintype.card α := by
    rw [show ((Finset.univ : Finset α).filter (fun v => c v = false)) =
            ((Finset.univ : Finset α).filter (fun v => ¬ (c v = true))) from ?_]
    · rw [Finset.card_filter_add_card_filter_not]
      exact Finset.card_univ
    · ext v
      simp [Bool.not_eq_true]
  have h_even := hG.even_card_of_colorable_two
    ⟨SimpleGraph.recolorOfEquiv G finTwoEquiv.symm c⟩ hn1
  rcases h_even with ⟨k, hk⟩
  rw [hk] at h_sum
  refine ⟨?_, ?_⟩ <;> omega

end SimpleGraph
