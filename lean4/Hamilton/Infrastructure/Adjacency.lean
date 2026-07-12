/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCOperations
import Mathlib.Combinatorics.SimpleGraph.Basic



namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- `π` *merges to* `σ` if `σ.val.parts` equals `π.val.parts` with
two distinct blocks `B₁, B₂` replaced by their union `B₁ ∪ B₂`. -/
def mergesTo (π σ : NC s) : Prop :=
  ∃ B₁ ∈ π.val.parts, ∃ B₂ ∈ π.val.parts, B₁ ≠ B₂ ∧
    σ.val.parts = insert (B₁ ∪ B₂) ((π.val.parts.erase B₁).erase B₂)

/-- The **refinement adjacency** on `NC s` — `π` and `σ` are
adjacent iff they differ by a single merge in either direction. -/
def Adj (π σ : NC s) : Prop := mergesTo π σ ∨ mergesTo σ π

/-- Adjacency is symmetric.  Trivial via `Or.symm`. -/
theorem Adj_symm {π σ : NC s} (h : Adj π σ) : Adj σ π := Or.symm h

/-- Decidability of `Adj` via classical reasoning (the existential
quantifier over Finsets is decidable, but Lean's `decide` needs
extra structure to discharge directly).  -/
noncomputable instance adj_decidable : DecidableRel (Adj (s := s)) :=
  Classical.decRel _

/-! ### Cardinality change under a merge

Merging two blocks decreases the number of blocks by exactly 1. -/

/-- Helper: for distinct blocks `B₁, B₂` of a `Finpartition`, the
union `B₁ ∪ B₂` is not among the remaining blocks
`(parts.erase B₁).erase B₂`. -/
private theorem union_notMem_erase {α : Type*} [DecidableEq α]
    {s : Finset α} (P : Finpartition s)
    {B₁ B₂ : Finset α} (hB₁ : B₁ ∈ P.parts)
    (hB₂ : B₂ ∈ P.parts) (hne : B₁ ≠ B₂) :
    B₁ ∪ B₂ ∉ ((P.parts.erase B₁).erase B₂) := by
  intro hin
  rw [Finset.mem_erase] at hin
  obtain ⟨_, hin_e1⟩ := hin
  rw [Finset.mem_erase] at hin_e1
  obtain ⟨hne_B₁, hC⟩ := hin_e1
  have hdisj : Disjoint B₁ (B₁ ∪ B₂) :=
    P.disjoint hB₁ hC (Ne.symm hne_B₁)
  have hB₁_sub : B₁ ⊆ B₁ ∪ B₂ := Finset.subset_union_left
  have hinf : B₁ ⊓ (B₁ ∪ B₂) = B₁ := inf_eq_left.mpr hB₁_sub
  have hbot : B₁ ≤ ⊥ := by
    rw [← hinf]; exact hdisj.le_bot
  have hB₁_emp : B₁ = ⊥ := le_bot_iff.mp hbot
  exact P.bot_notMem (hB₁_emp ▸ hB₁)

/-- `mergesTo π σ` implies `numBlocks σ + 1 = numBlocks π` — the
merge replaces two blocks with one, reducing `numBlocks` by 1. -/
theorem mergesTo_numBlocks {π σ : NC s} (h : mergesTo π σ) :
    numBlocks σ + 1 = numBlocks π := by
  obtain ⟨B₁, hB₁, B₂, hB₂, hne, hparts⟩ := h
  unfold numBlocks
  rw [hparts]
  have hB₂_e : B₂ ∈ π.val.parts.erase B₁ :=
    Finset.mem_erase.mpr ⟨hne.symm, hB₂⟩
  have hcard_e :
      ((π.val.parts.erase B₁).erase B₂).card = π.val.parts.card - 2 := by
    rw [Finset.card_erase_of_mem hB₂_e, Finset.card_erase_of_mem hB₁]
    omega
  have hnotin := union_notMem_erase π.val hB₁ hB₂ hne
  rw [Finset.card_insert_of_notMem hnotin, hcard_e]
  have hge2 : 2 ≤ π.val.parts.card := by
    have hsub : ({B₁, B₂} : Finset _) ⊆ π.val.parts := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc (2 : ℕ) = ({B₁, B₂} : Finset _).card :=
            (Finset.card_pair hne).symm
      _ ≤ π.val.parts.card := Finset.card_le_card hsub
  omega

/-- An `Adj`-step changes `numBlocks` by exactly 1 (in one direction
or the other). -/
theorem Adj_numBlocks_diff {π σ : NC s} (h : Adj π σ) :
    (numBlocks π = numBlocks σ + 1) ∨ (numBlocks σ = numBlocks π + 1) := by
  rcases h with hm | hm
  · left; exact (mergesTo_numBlocks hm).symm
  · right; exact (mergesTo_numBlocks hm).symm

/-- Adjacency is irreflexive: `mergesTo π π` is impossible (it would
require `numBlocks π = numBlocks π + 1`). -/
theorem Adj_irrefl (π : NC s) : ¬ Adj π π := by
  intro h
  rcases h with hm | hm <;>
    (have := mergesTo_numBlocks hm; omega)

end NC

/-! ### The refinement graph as a `SimpleGraph` -/

/-- The **refinement graph** on `NC α s` — Mathlib `SimpleGraph`
constructed from `NC.Adj`. -/
def NCRefinementGraph {α : Type*} [LinearOrder α] (s : Finset α) :
    SimpleGraph (NC s) where
  Adj π σ := NC.Adj π σ
  symm _ _ := NC.Adj_symm
  loopless := ⟨NC.Adj_irrefl⟩

/-- The adjacency in the refinement graph is exactly `NC.Adj`. -/
@[simp]
theorem NCRefinementGraph_adj_def {α : Type*} [LinearOrder α]
    {s : Finset α} (π σ : NC s) :
    (NCRefinementGraph s).Adj π σ ↔ NC.Adj π σ := Iff.rfl

/-- Public paper-to-Lean bridge: adjacency in the refinement graph is
exactly one explicit merge of two distinct blocks, in either direction.

The manuscript separately proves, using the rank of the noncrossing
partition lattice, that these single-merge steps are precisely its cover
relations. This theorem records the operational characterization used by
the formal graph without leaving `NC.Adj` or `NC.mergesTo` opaque. -/
theorem NCRefinementGraph_adj_iff_single_merge
    {α : Type*} [LinearOrder α] {s : Finset α} (π σ : NC s) :
    (NCRefinementGraph s).Adj π σ ↔
      (∃ B₁ ∈ π.val.parts, ∃ B₂ ∈ π.val.parts, B₁ ≠ B₂ ∧
          σ.val.parts = insert (B₁ ∪ B₂) ((π.val.parts.erase B₁).erase B₂)) ∨
      (∃ B₁ ∈ σ.val.parts, ∃ B₂ ∈ σ.val.parts, B₁ ≠ B₂ ∧
          π.val.parts = insert (B₁ ∪ B₂) ((σ.val.parts.erase B₁).erase B₂)) :=
  Iff.rfl

end Hamilton.Infrastructure
