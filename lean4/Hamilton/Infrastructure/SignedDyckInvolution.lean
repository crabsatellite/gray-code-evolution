/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.SignedDyckSum
import Hamilton.Infrastructure.CatalanPos
import Mathlib.Combinatorics.Enumerative.Catalan.Tree

/-!
# Sign-reversing involution on `Tree Unit` for `signedDyckSum`

A sign-reversing involution on `Tree Unit` (the inductive type bijecting with
DyckWords via Mathlib's `equivTreesOfNumNodesEq`) that pairs Dyck words of
opposite peak parity, except at fixed points.

## Main results

* `invTree` — the involution.
* `invTree_eq_nil_iff` — `invTree t = nil ↔ t = nil`.
* `invTree_invTree` — involution property.
* `numNodes_invTree` — size preserved.

## Tags

DyckWord, Tree, sign-reversing involution
-/

namespace Hamilton.Infrastructure

namespace NC

/-- The sign-reversing involution on `Tree Unit`. -/
def invTree : Tree Unit → Tree Unit
  | Tree.nil => Tree.nil
  | Tree.node () l r =>
    if l = Tree.nil then
      if r = Tree.nil then Tree.node () Tree.nil Tree.nil
      else Tree.node () r Tree.nil
    else
      if r = Tree.nil then Tree.node () Tree.nil l
      else Tree.node () l (invTree r)

/-! ### Unfolding equation lemmas for invTree -/

@[simp] theorem invTree_nil : invTree Tree.nil = Tree.nil := rfl

@[simp] theorem invTree_node_nil_nil :
    invTree (Tree.node () Tree.nil Tree.nil) = Tree.node () Tree.nil Tree.nil := rfl

theorem invTree_node_nil_right (r : Tree Unit) (hr : r ≠ Tree.nil) :
    invTree (Tree.node () Tree.nil r) = Tree.node () r Tree.nil := by
  show (if (Tree.nil : Tree Unit) = Tree.nil then
         (if r = Tree.nil then Tree.node () Tree.nil Tree.nil
          else Tree.node () r Tree.nil)
       else (if r = Tree.nil then Tree.node () Tree.nil Tree.nil
             else Tree.node () Tree.nil (invTree r))) =
       Tree.node () r Tree.nil
  rw [if_pos rfl, if_neg hr]

theorem invTree_node_left_nil (l : Tree Unit) (hl : l ≠ Tree.nil) :
    invTree (Tree.node () l Tree.nil) = Tree.node () Tree.nil l := by
  show (if l = Tree.nil then
         (if (Tree.nil : Tree Unit) = Tree.nil then Tree.node () Tree.nil Tree.nil
          else Tree.node () Tree.nil Tree.nil)
       else (if (Tree.nil : Tree Unit) = Tree.nil then Tree.node () Tree.nil l
             else Tree.node () l (invTree Tree.nil))) =
       Tree.node () Tree.nil l
  rw [if_neg hl, if_pos rfl]

theorem invTree_node_both_ne (l r : Tree Unit) (hl : l ≠ Tree.nil) (hr : r ≠ Tree.nil) :
    invTree (Tree.node () l r) = Tree.node () l (invTree r) := by
  show (if l = Tree.nil then
         (if r = Tree.nil then Tree.node () Tree.nil Tree.nil
          else Tree.node () r Tree.nil)
       else (if r = Tree.nil then Tree.node () Tree.nil l
             else Tree.node () l (invTree r))) =
       Tree.node () l (invTree r)
  rw [if_neg hl, if_neg hr]

/-- `invTree` returns `nil` iff input is `nil`. -/
theorem invTree_eq_nil_iff (t : Tree Unit) : invTree t = Tree.nil ↔ t = Tree.nil := by
  cases t with
  | nil => simp
  | node u l r =>
    cases u
    constructor
    · intro h
      exfalso
      by_cases hl : l = Tree.nil
      · by_cases hr : r = Tree.nil
        · subst hl; subst hr
          exact (nomatch h)
        · subst hl
          rw [invTree_node_nil_right r hr] at h
          exact (nomatch h)
      · by_cases hr : r = Tree.nil
        · subst hr
          rw [invTree_node_left_nil l hl] at h
          exact (nomatch h)
        · rw [invTree_node_both_ne l r hl hr] at h
          exact (nomatch h)
    · intro h
      exact (nomatch h)

/-- `invTree` is an involution. -/
theorem invTree_invTree (t : Tree Unit) : invTree (invTree t) = t := by
  induction t with
  | nil => rfl
  | node u l r _ ih_r =>
    cases u
    by_cases hl : l = Tree.nil
    · by_cases hr : r = Tree.nil
      · subst hl; subst hr; rfl
      · subst hl
        rw [invTree_node_nil_right r hr]
        exact invTree_node_left_nil r hr
    · by_cases hr : r = Tree.nil
      · subst hr
        rw [invTree_node_left_nil l hl]
        exact invTree_node_nil_right l hl
      · rw [invTree_node_both_ne l r hl hr]
        have h_ir_ne : invTree r ≠ Tree.nil := fun h => hr ((invTree_eq_nil_iff r).mp h)
        rw [invTree_node_both_ne l (invTree r) hl h_ir_ne, ih_r]

/-! ### peakCountTree: peak count on trees, matching DyckWord peakCount -/

/-- Peak count on trees, matching the Dyck word peak count via `equivTreesOfNumNodesEq`.

For tree `node () l r` corresponding to Dyck word `D = (toDyck l).nest + (toDyck r)`:
* If `l = nil`: `peakCount D = peakCount (toDyck r) + 1` (using `peakCount_nest_add`).
* If `l ≠ nil`: `peakCount D = peakCount (toDyck l) + peakCount (toDyck r)`. -/
def peakCountTree : Tree Unit → ℕ
  | Tree.nil => 0
  | Tree.node () l r =>
    if l = Tree.nil then 1 + peakCountTree r
    else peakCountTree l + peakCountTree r

@[simp] theorem peakCountTree_nil : peakCountTree Tree.nil = 0 := rfl

@[simp] theorem peakCountTree_node_nil_nil :
    peakCountTree (Tree.node () Tree.nil Tree.nil) = 1 := rfl

theorem peakCountTree_node_nil_right (r : Tree Unit) :
    peakCountTree (Tree.node () Tree.nil r) = 1 + peakCountTree r := by
  show (if (Tree.nil : Tree Unit) = Tree.nil then 1 + peakCountTree r
       else peakCountTree Tree.nil + peakCountTree r) = 1 + peakCountTree r
  rw [if_pos rfl]

theorem peakCountTree_node_left_ne (l r : Tree Unit) (hl : l ≠ Tree.nil) :
    peakCountTree (Tree.node () l r) = peakCountTree l + peakCountTree r := by
  show (if l = Tree.nil then 1 + peakCountTree r
       else peakCountTree l + peakCountTree r) = peakCountTree l + peakCountTree r
  rw [if_neg hl]

/-! ### Sign-flip property of `invTree` -/

/-- Under `invTree`, on the non-recursive cases (excluding both-nonzero), peak count
changes by exactly ±1. Concretely, when `l = nil ∧ r ≠ nil` (or symmetric),
`peakCountTree (invTree t) = peakCountTree t ± 1`.

For the both-nonzero case, the change is propagated to the right subtree. -/
theorem peakCountTree_invTree_node_nil_right (r : Tree Unit) (hr : r ≠ Tree.nil) :
    peakCountTree (invTree (Tree.node () Tree.nil r)) + 1 =
    peakCountTree (Tree.node () Tree.nil r) := by
  rw [invTree_node_nil_right r hr]
  rw [peakCountTree_node_left_ne r Tree.nil hr]
  rw [peakCountTree_node_nil_right r]
  simp [peakCountTree_nil]
  omega

theorem peakCountTree_invTree_node_left_nil (l : Tree Unit) (hl : l ≠ Tree.nil) :
    peakCountTree (invTree (Tree.node () l Tree.nil)) =
    peakCountTree (Tree.node () l Tree.nil) + 1 := by
  rw [invTree_node_left_nil l hl]
  rw [peakCountTree_node_nil_right l]
  rw [peakCountTree_node_left_ne l Tree.nil hl]
  simp [peakCountTree_nil]
  omega

/-- For the both-nonzero case, peak count differs by the inner difference (propagation). -/
theorem peakCountTree_invTree_node_both_ne (l r : Tree Unit) (hl : l ≠ Tree.nil) (hr : r ≠ Tree.nil) :
    peakCountTree (invTree (Tree.node () l r)) =
      peakCountTree l + peakCountTree (invTree r) := by
  rw [invTree_node_both_ne l r hl hr]
  rw [peakCountTree_node_left_ne l (invTree r) hl]

/-! ### Bridge: peakCountTree matches DyckWord.peakCount via ofTree -/

/-- `ofTree Tree.nil = 0` (Mathlib def). -/
@[simp] theorem ofTree_nil_eq_zero : DyckWord.ofTree Tree.nil = 0 := rfl

/-- `ofTree (node () l r) = (ofTree l).nest + ofTree r`. -/
theorem ofTree_node (l r : Tree Unit) :
    DyckWord.ofTree (Tree.node () l r) = (DyckWord.ofTree l).nest + DyckWord.ofTree r := rfl

/-- The tree-to-DyckWord conversion `ofTree` returns `0` iff input is `nil`. -/
theorem ofTree_eq_zero_iff (t : Tree Unit) : DyckWord.ofTree t = 0 ↔ t = Tree.nil := by
  refine ⟨fun h => ?_, fun h => h ▸ ofTree_nil_eq_zero⟩
  have h_tree : (DyckWord.ofTree t).toTree = (0 : DyckWord).toTree := by rw [h]
  rw [DyckWord.toTree_ofTree] at h_tree
  have h_zero_tree : (0 : DyckWord).toTree = Tree.nil := by simp [DyckWord.toTree]
  rw [h_zero_tree] at h_tree
  exact h_tree

/-- **BRIDGE**: `peakCountTree t = (ofTree t).peakCount`. -/
theorem peakCountTree_eq_peakCount_ofTree (t : Tree Unit) :
    peakCountTree t = (DyckWord.ofTree t).peakCount := by
  induction t with
  | nil =>
    show 0 = (0 : DyckWord).peakCount
    rw [DyckWord.peakCount_zero]
  | node u l r ih_l ih_r =>
    cases u
    rw [ofTree_node]
    rw [peakCount_nest_add]
    by_cases hl : l = Tree.nil
    · subst hl
      rw [peakCountTree_node_nil_right r]
      rw [ofTree_nil_eq_zero, DyckWord.peakCount_zero]
      rw [if_pos rfl]
      rw [ih_r]
      omega
    · rw [peakCountTree_node_left_ne l r hl]
      have h_ofl_ne : DyckWord.ofTree l ≠ 0 := by
        rw [Ne, ofTree_eq_zero_iff]
        exact hl
      rw [if_neg h_ofl_ne, ih_l, ih_r]
      omega

/-- `invTree` preserves `numNodes`. -/
theorem numNodes_invTree (t : Tree Unit) : (invTree t).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node u l r _ ih_r =>
    cases u
    by_cases hl : l = Tree.nil
    · by_cases hr : r = Tree.nil
      · subst hl; subst hr; rfl
      · subst hl
        rw [invTree_node_nil_right r hr]
        show r.numNodes + Tree.nil.numNodes + 1 = Tree.nil.numNodes + r.numNodes + 1
        simp [Tree.numNodes]
    · by_cases hr : r = Tree.nil
      · subst hr
        rw [invTree_node_left_nil l hl]
        show Tree.nil.numNodes + l.numNodes + 1 = l.numNodes + Tree.nil.numNodes + 1
        simp [Tree.numNodes]
      · rw [invTree_node_both_ne l r hl hr]
        show l.numNodes + (invTree r).numNodes + 1 = l.numNodes + r.numNodes + 1
        rw [ih_r]

/-! ### Sign-reversing parity flip under invTree -/

/-- **Sign-reversing property**: for non-fixed `t`, `invTree t` has opposite peak parity.
Equivalently, `(-1)^{peakCountTree (invTree t)} = -(-1)^{peakCountTree t}`. -/
theorem signed_invTree_eq_neg (t : Tree Unit) (h : invTree t ≠ t) :
    (-1 : ℤ) ^ (peakCountTree (invTree t)) = -((-1 : ℤ) ^ (peakCountTree t)) := by
  induction t with
  | nil =>
    exfalso; exact h rfl
  | node u l r _ ih_r =>
    cases u
    by_cases hl : l = Tree.nil
    · by_cases hr : r = Tree.nil
      · subst hl; subst hr; exfalso; exact h rfl
      · subst hl
        rw [invTree_node_nil_right r hr]
        rw [peakCountTree_node_left_ne r Tree.nil hr]
        rw [peakCountTree_node_nil_right r]
        rw [peakCountTree_nil]
        show (-1 : ℤ) ^ (peakCountTree r + 0) = -((-1 : ℤ) ^ (1 + peakCountTree r))
        ring
    · by_cases hr : r = Tree.nil
      · subst hr
        rw [invTree_node_left_nil l hl]
        rw [peakCountTree_node_left_ne l Tree.nil hl]
        rw [peakCountTree_node_nil_right l]
        rw [peakCountTree_nil]
        show (-1 : ℤ) ^ (1 + peakCountTree l) = -((-1 : ℤ) ^ (peakCountTree l + 0))
        ring
      · -- Both nonzero: outer non-fixed iff r non-fixed.
        rw [invTree_node_both_ne l r hl hr]
        rw [peakCountTree_node_left_ne l (invTree r) hl]
        rw [peakCountTree_node_left_ne l r hl]
        have h_r_non_fixed : invTree r ≠ r := by
          intro h_r_fixed
          apply h
          rw [invTree_node_both_ne l r hl hr, h_r_fixed]
        have h_ih := ih_r h_r_non_fixed
        rw [pow_add, pow_add, h_ih]
        ring

/-! ### Tree-level signedDyckSum -/

/-- The tree-version of `signedDyckSum`: sum of `(-1)^{peakCountTree t}` over
trees with `n` nodes. -/
noncomputable def signedDyckSumTree (n : ℕ) : ℤ :=
  ∑ t ∈ Tree.treesOfNumNodesEq n, (-1 : ℤ) ^ (peakCountTree t)

/-! ### Sum over trees via the involution: fixed-point reduction -/

/-- **CORE INVOLUTION LEMMA**: `signedDyckSumTree n` equals the sum of
`(-1)^{peakCountTree t}` over **only the fixed points** of `invTree`. -/
theorem signedDyckSumTree_eq_fixed_sum (n : ℕ) :
    signedDyckSumTree n =
      ∑ t ∈ (Tree.treesOfNumNodesEq n).filter (fun t => invTree t = t),
        (-1 : ℤ) ^ (peakCountTree t) := by
  unfold signedDyckSumTree
  rw [← Finset.sum_filter_add_sum_filter_not (Tree.treesOfNumNodesEq n)
        (fun t => invTree t = t) (fun t => (-1 : ℤ) ^ peakCountTree t)]
  -- Need: the sum over non-fixed = 0.
  have h_nf : ∑ t ∈ (Tree.treesOfNumNodesEq n).filter (fun t => ¬ invTree t = t),
      (-1 : ℤ) ^ peakCountTree t = 0 := by
    apply Finset.sum_involution (g := fun t _ => invTree t)
    · -- hg₁: f(t) + f(invTree t) = 0.
      intros t ht
      rw [Finset.mem_filter] at ht
      have h_neg := signed_invTree_eq_neg t ht.2
      linarith
    · -- hg₃: f(t) ≠ 0 → invTree t ≠ t.
      intros t ht _
      rw [Finset.mem_filter] at ht
      exact ht.2
    · -- g_mem: invTree t ∈ filter.
      intros t ht
      rw [Finset.mem_filter] at ht
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Tree.mem_treesOfNumNodesEq] at *
        rw [numNodes_invTree]
        exact ht.1
      · intro h_eq
        apply ht.2
        rw [← h_eq, invTree_invTree]
    · -- hg₄: invTree (invTree t) = t.
      intros t _
      exact invTree_invTree t
  rw [h_nf, add_zero]

/-- **BRIDGE**: `signedDyckSumTree n = signedDyckSum n` via the
`DyckWord ≃ Tree Unit` bijection. -/
theorem signedDyckSumTree_eq_signedDyckSum (n : ℕ) :
    signedDyckSumTree n = signedDyckSum n := by
  unfold signedDyckSumTree signedDyckSum
  symm
  apply Finset.sum_bij (fun p _ => p.val.toTree)
  · -- Well-defined: p.val.toTree ∈ treesOfNumNodesEq n.
    intros p _
    rw [Tree.mem_treesOfNumNodesEq]
    rw [DyckWord.numNodes_toTree]
    exact p.property
  · -- Injective.
    intros p₁ _ p₂ _ h_eq
    apply Subtype.ext
    have h_eq' : DyckWord.ofTree p₁.val.toTree = DyckWord.ofTree p₂.val.toTree := by rw [h_eq]
    rw [DyckWord.ofTree_toTree, DyckWord.ofTree_toTree] at h_eq'
    exact h_eq'
  · -- Surjective.
    intros t ht
    rw [Tree.mem_treesOfNumNodesEq] at ht
    refine ⟨⟨DyckWord.ofTree t, ?_⟩, Finset.mem_univ _, ?_⟩
    · rw [← DyckWord.numNodes_toTree]
      rw [DyckWord.toTree_ofTree]
      exact ht
    · exact DyckWord.toTree_ofTree t
  · -- Equation: (-1)^{pc p.val} = (-1)^{pcTree p.val.toTree}.
    intros p _
    rw [peakCountTree_eq_peakCount_ofTree]
    rw [DyckWord.ofTree_toTree]

/-! ### Sum over pairwiseNode -/

/-- The sum over `pairwiseNode a b` is a double sum over the product. -/
theorem sum_pairwiseNode (a b : Finset (Tree Unit)) (f : Tree Unit → ℤ) :
    ∑ t ∈ Tree.pairwiseNode a b, f t = ∑ l ∈ a, ∑ r ∈ b, f (Tree.node () l r) := by
  unfold Tree.pairwiseNode
  rw [Finset.sum_map]
  rw [Finset.sum_product]
  rfl

/-! ### firstReturn recurrence for signedDyckSumTree -/

/-- Disjointness of the `pairwiseNode` family for different `(i, j)`. -/
theorem pairwiseNode_disjoint (n : ℕ) :
    ((Finset.antidiagonal n) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun ij => Tree.pairwiseNode (Tree.treesOfNumNodesEq ij.1) (Tree.treesOfNumNodesEq ij.2)) := by
  intros ij₁ hij₁ ij₂ hij₂ h_ne
  show Disjoint
    (Tree.pairwiseNode (Tree.treesOfNumNodesEq ij₁.1) (Tree.treesOfNumNodesEq ij₁.2))
    (Tree.pairwiseNode (Tree.treesOfNumNodesEq ij₂.1) (Tree.treesOfNumNodesEq ij₂.2))
  rw [Finset.disjoint_left]
  intros t ht₁ ht₂
  unfold Tree.pairwiseNode at ht₁ ht₂
  rw [Finset.mem_map] at ht₁ ht₂
  obtain ⟨⟨l₁, r₁⟩, hlr₁, h_eq₁⟩ := ht₁
  obtain ⟨⟨l₂, r₂⟩, hlr₂, h_eq₂⟩ := ht₂
  simp only [Function.Embedding.coeFn_mk] at h_eq₁ h_eq₂
  simp only [Finset.mem_product, Tree.mem_treesOfNumNodesEq] at hlr₁ hlr₂
  have h_eq : Tree.node () l₁ r₁ = Tree.node () l₂ r₂ := by rw [h_eq₁, h_eq₂]
  injection h_eq with _ h_l h_r
  have h_fst : ij₁.1 = ij₂.1 := by rw [← hlr₁.1, ← hlr₂.1, h_l]
  have h_snd : ij₁.2 = ij₂.2 := by rw [← hlr₁.2, ← hlr₂.2, h_r]
  apply h_ne
  ext
  · exact h_fst
  · exact h_snd

/-- **FIRSTRETURN RECURRENCE** for `signedDyckSumTree`:

`signedDyckSumTree (n + 1) = ∑_{ij ∈ antidiagonal n} ∑_{l, r} (-1)^{pcT (node l r)}`. -/
theorem signedDyckSumTree_succ (n : ℕ) :
    signedDyckSumTree (n + 1) =
      ∑ ij ∈ Finset.antidiagonal n,
        ∑ l ∈ Tree.treesOfNumNodesEq ij.1,
        ∑ r ∈ Tree.treesOfNumNodesEq ij.2,
          (-1 : ℤ) ^ peakCountTree (Tree.node () l r) := by
  unfold signedDyckSumTree
  rw [Tree.treesOfNumNodesEq_succ]
  rw [Finset.sum_biUnion (pairwiseNode_disjoint n)]
  apply Finset.sum_congr rfl
  intros ij _
  exact sum_pairwiseNode _ _ _

/-! ### Inner sum simplification -/

/-- The inner sum at `(0, j)`: l = nil, so `(-1)^{pc (node nil r)} = -(-1)^{pc r}`. -/
theorem inner_sum_zero (j : ℕ) :
    (∑ l ∈ Tree.treesOfNumNodesEq 0, ∑ r ∈ Tree.treesOfNumNodesEq j,
        (-1 : ℤ) ^ peakCountTree (Tree.node () l r)) =
      -signedDyckSumTree j := by
  rw [Tree.treesOfNumNodesEq_zero]
  rw [Finset.sum_singleton]
  unfold signedDyckSumTree
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intros r _
  show (-1 : ℤ) ^ peakCountTree (Tree.node () Tree.nil r) = -(-1) ^ peakCountTree r
  -- peakCountTree (node () nil r):
  -- Case r = nil: peakCount = 1 (= node nil nil); -(-1)^0 = -1. ✓
  -- Case r ≠ nil: peakCount = 1 + pcT r; -(-1)^{pcT r}.
  by_cases hr : r = Tree.nil
  · subst hr
    show (-1 : ℤ) ^ peakCountTree (Tree.node () Tree.nil Tree.nil) = -(-1) ^ peakCountTree Tree.nil
    rw [peakCountTree_node_nil_nil, peakCountTree_nil]
    rfl
  · rw [peakCountTree_node_nil_right r]
    show (-1 : ℤ) ^ (1 + peakCountTree r) = -(-1) ^ peakCountTree r
    ring

/-- The inner sum at `(i, j)` with `i ≥ 1`: all `l` are non-nil. -/
theorem inner_sum_pos (i j : ℕ) (hi : 1 ≤ i) :
    (∑ l ∈ Tree.treesOfNumNodesEq i, ∑ r ∈ Tree.treesOfNumNodesEq j,
        (-1 : ℤ) ^ peakCountTree (Tree.node () l r)) =
      signedDyckSumTree i * signedDyckSumTree j := by
  unfold signedDyckSumTree
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intros l hl
  apply Finset.sum_congr rfl
  intros r _
  -- l ≠ nil since numNodes l = i ≥ 1.
  have hl_ne : l ≠ Tree.nil := by
    rw [Tree.mem_treesOfNumNodesEq] at hl
    intro h_eq
    subst h_eq
    simp [Tree.numNodes] at hl
    omega
  rw [peakCountTree_node_left_ne l r hl_ne]
  rw [pow_add]

/-! ### Clean firstReturn recurrence -/

/-- **CLEAN FIRSTRETURN RECURRENCE**:
`signedDyckSumTree (n+1) = -signedDyckSumTree n + ∑_{k=0..n-1} signedDyckSumTree (k+1) · signedDyckSumTree (n-1-k)`. -/
theorem signedDyckSumTree_recurrence (n : ℕ) :
    signedDyckSumTree (n + 1) =
      -signedDyckSumTree n +
      ∑ k ∈ Finset.range n,
        signedDyckSumTree (k + 1) * signedDyckSumTree (n - 1 - k) := by
  rw [signedDyckSumTree_succ]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => ∑ l ∈ Tree.treesOfNumNodesEq i, ∑ r ∈ Tree.treesOfNumNodesEq j,
        (-1 : ℤ) ^ peakCountTree (Tree.node () l r)) n]
  rw [Finset.sum_range_succ' _ n]
  -- Now: ∑ k ∈ range n, f (k+1) (n - (k+1)) + f 0 n.
  -- f 0 n = inner_sum_zero n = -signedDyckSumTree n.
  rw [show (n - 0 : ℕ) = n from Nat.sub_zero n]
  rw [inner_sum_zero n]
  -- Now: ∑ k ∈ range n, f (k+1) (n - (k+1)) + (-signedDyckSumTree n) = -signedDyckSumTree n + ...
  -- Equivalently: rearrange.
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intros k hk
  rw [Finset.mem_range] at hk
  rw [inner_sum_pos (k + 1) (n - (k + 1)) (by omega)]
  have h_eq : n - (k + 1) = n - 1 - k := by omega
  rw [h_eq]

/-! ### Boundary cases for signedDyckSumTree -/

/-- `signedDyckSumTree 0 = 1` via bridge to signedDyckSum. -/
theorem signedDyckSumTree_zero : signedDyckSumTree 0 = 1 := by
  rw [signedDyckSumTree_eq_signedDyckSum]
  exact signedDyckSum_zero

/-- `signedDyckSumTree 1 = -1` via bridge to signedDyckSum. -/
theorem signedDyckSumTree_one : signedDyckSumTree 1 = -1 := by
  rw [signedDyckSumTree_eq_signedDyckSum]
  exact signedDyckSum_one

/-- `signedDyckSumTree 2 = 0` via firstReturn recurrence. -/
theorem signedDyckSumTree_two : signedDyckSumTree 2 = 0 := by
  show signedDyckSumTree (1 + 1) = 0
  rw [signedDyckSumTree_recurrence 1]
  rw [signedDyckSumTree_one]
  simp [Finset.sum_range_one, signedDyckSumTree_one, signedDyckSumTree_zero]

/-- `signedDyckSumTree 3 = 1` via firstReturn recurrence. -/
theorem signedDyckSumTree_three : signedDyckSumTree 3 = 1 := by
  show signedDyckSumTree (2 + 1) = 1
  rw [signedDyckSumTree_recurrence 2]
  rw [signedDyckSumTree_two]
  -- Goal: -0 + ∑ k ∈ range 2, signedDyckSumTree (k+1) * signedDyckSumTree (2 - 1 - k) = 1.
  show (-(0 : ℤ)) +
       (∑ k ∈ Finset.range 2, signedDyckSumTree (k + 1) * signedDyckSumTree (2 - 1 - k)) = 1
  rw [neg_zero, zero_add]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  show signedDyckSumTree 1 * signedDyckSumTree 1 +
       signedDyckSumTree (1 + 1) * signedDyckSumTree (2 - 1 - 1) = 1
  rw [signedDyckSumTree_one, signedDyckSumTree_two, signedDyckSumTree_zero]
  show (-1 : ℤ) * (-1) + 0 * 1 = 1
  ring

/-- `signedDyckSumTree 4 = 0` via firstReturn recurrence. -/
theorem signedDyckSumTree_four : signedDyckSumTree 4 = 0 := by
  show signedDyckSumTree (3 + 1) = 0
  rw [signedDyckSumTree_recurrence 3]
  rw [signedDyckSumTree_three]
  show (-(1 : ℤ)) +
       (∑ k ∈ Finset.range 3, signedDyckSumTree (k + 1) * signedDyckSumTree (3 - 1 - k)) = 0
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  show (-(1 : ℤ)) +
       (signedDyckSumTree 1 * signedDyckSumTree (3 - 1 - 0) +
        signedDyckSumTree (1 + 1) * signedDyckSumTree (3 - 1 - 1) +
        signedDyckSumTree (2 + 1) * signedDyckSumTree (3 - 1 - 2)) = 0
  rw [signedDyckSumTree_one, signedDyckSumTree_two, signedDyckSumTree_three, signedDyckSumTree_zero]
  show (-(1 : ℤ)) + ((-1) * 0 + 0 * (-1) + 1 * 1) = 0
  ring

/-! ### Direct bridge: signedNCCount on Fin n = signedDyckSumTree n -/

/-- **DOUBLE BRIDGE**: `signedNCCount(Finset.univ : Finset (Fin n)) = signedDyckSumTree n`.

Composition of `signedNCCount_eq_signedDyckSum` and `signedDyckSumTree_eq_signedDyckSum`. -/
theorem signedNCCount_univ_eq_signedDyckSumTree (n : ℕ) :
    signedNCCount (Finset.univ : Finset (Fin n)) = signedDyckSumTree n := by
  have h_card : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [signedNCCount_eq_signedDyckSum]
  rw [h_card]
  rw [← signedDyckSumTree_eq_signedDyckSum]

/-- `signedDyckSumTree 5 = -2 = (-1)^3 · catalan 2`. -/
theorem signedDyckSumTree_five : signedDyckSumTree 5 = -2 := by
  show signedDyckSumTree (4 + 1) = -2
  rw [signedDyckSumTree_recurrence 4]
  rw [signedDyckSumTree_four]
  show (-(0 : ℤ)) +
       (∑ k ∈ Finset.range 4, signedDyckSumTree (k + 1) * signedDyckSumTree (4 - 1 - k)) = -2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  show (-(0 : ℤ)) +
       (signedDyckSumTree 1 * signedDyckSumTree (4 - 1 - 0) +
        signedDyckSumTree (1 + 1) * signedDyckSumTree (4 - 1 - 1) +
        signedDyckSumTree (2 + 1) * signedDyckSumTree (4 - 1 - 2) +
        signedDyckSumTree (3 + 1) * signedDyckSumTree (4 - 1 - 3)) = -2
  rw [signedDyckSumTree_one, signedDyckSumTree_two, signedDyckSumTree_three,
      signedDyckSumTree_four, signedDyckSumTree_zero]
  show (-(0 : ℤ)) + ((-1) * 1 + 0 * 0 + 1 * (-1) + 0 * 1) = -2
  ring

/-! ### Bipartite imbalance closure for small odd n (UNCONDITIONAL, NO Narayana axiom) -/

/-- **n=1 case**: `signedNCCount(univ Fin 1) = -1 ≠ 0` UNCONDITIONALLY. -/
theorem signedNCCount_fin_one_ne_zero :
    signedNCCount (Finset.univ : Finset (Fin 1)) ≠ 0 := by
  rw [signedNCCount_univ_eq_signedDyckSumTree, signedDyckSumTree_one]
  decide

/-- **n=3 case**: `signedNCCount(univ Fin 3) = 1 ≠ 0` UNCONDITIONALLY. -/
theorem signedNCCount_fin_three_ne_zero :
    signedNCCount (Finset.univ : Finset (Fin 3)) ≠ 0 := by
  rw [signedNCCount_univ_eq_signedDyckSumTree, signedDyckSumTree_three]
  decide

/-- **n=5 case**: `signedNCCount(univ Fin 5) = -2 ≠ 0` UNCONDITIONALLY. -/
theorem signedNCCount_fin_five_ne_zero :
    signedNCCount (Finset.univ : Finset (Fin 5)) ≠ 0 := by
  rw [signedNCCount_univ_eq_signedDyckSumTree, signedDyckSumTree_five]
  decide

/-! ### Strong-induction closed form: EVEN case

We prove `signedDyckSumTree (2 * m) = 0` for `m ≥ 1` by strong induction,
assuming the ODD closed form for smaller arguments.

The key insight: in the recurrence
  signedDyckSumTree(2m) = -signedDyckSumTree(2m-1) + ∑_{k=0..2m-2} f(k+1)·f(2m-2-k)
each summand has factors `(k+1)` and `(2m-2-k)` summing to `2m-1` odd.
So one factor is even and one is odd. The even factor is `0` (by IH on EVEN)
unless it equals `signedDyckSumTree 0 = 1`. The only such case is `(2m-2-k) = 0`,
giving the single non-trivial term `signedDyckSumTree(2m-1)` which cancels
`-signedDyckSumTree(2m-1)`.
-/

/-- Hypothesis package for the strong induction step. -/
structure SignedDyckSumTreeIH (m : ℕ) : Prop where
  even_ih : ∀ j, 1 ≤ j → j < m → signedDyckSumTree (2 * j) = 0
  odd_ih : ∀ p, p < m → signedDyckSumTree (2 * p + 1) = (-1 : ℤ) ^ (p + 1) * (catalan p : ℤ)

/-- **EVEN case helper**: under the IH for `m`, every "off-diagonal" term in the
EVEN-case recurrence sum is `0`.

For `k ∈ range (2m-1)` with `k ≠ 2m-2`, we have
  `signedDyckSumTree(k+1) · signedDyckSumTree(2m-2-k) = 0`.

Reason: `(k+1) + (2m-2-k) = 2m-1` is odd, so one factor is even-indexed.
If `k+1 ∈ {2, 4, ..., 2m-2}` then by IH `signedDyckSumTree(k+1) = 0`.
Otherwise `k+1` is odd, so `2m-2-k` is even. If `k = 2m-2` we have the
diagonal term (excluded); otherwise `2m-2-k ∈ {2, ..., 2m-2}` even ≥ 2,
so by IH `signedDyckSumTree(2m-2-k) = 0`. -/
theorem even_case_off_diagonal_zero (m : ℕ) (hm : 1 ≤ m) (ih : SignedDyckSumTreeIH m)
    (k : ℕ) (hk : k < 2 * m - 1) (h_ne : k + 1 ≠ 2 * m - 1) :
    signedDyckSumTree (k + 1) * signedDyckSumTree (2 * m - 2 - k) = 0 := by
  -- We have h_ne : k+1 ≠ 2m-1, i.e., k ≠ 2m-2.
  by_cases h_par : Even (k + 1)
  · -- k+1 even, so k+1 = 2j for some j ≥ 1, j ≤ m-1.
    obtain ⟨j, hj⟩ := h_par
    have h_k1_eq : k + 1 = 2 * j := by omega
    have h_j_pos : 1 ≤ j := by omega
    have h_j_lt : j < m := by omega
    rw [h_k1_eq]
    rw [ih.even_ih j h_j_pos h_j_lt]
    ring
  · -- k+1 odd. So k is even. 2m-2-k = 2m-2-even = even.
    rw [Nat.not_even_iff_odd] at h_par
    obtain ⟨p, hp⟩ := h_par
    -- k+1 = 2p+1, so k = 2p.
    have h_k_eq : k = 2 * p := by omega
    -- 2m-2-k = 2m-2-2p = 2*(m-1-p).
    -- Bounds: k ≤ 2m-2 since hk and h_ne; specifically k = 2p ≤ 2m-3 (since k ≠ 2m-2 and k even).
    -- Wait: hk says k < 2m-1, i.e., k ≤ 2m-2. h_ne (via k = 2p) means 2p ≠ 2m-2, i.e., p ≠ m-1.
    -- So either p < m-1 or p > m-1; combined with k ≤ 2m-2, p ≤ m-1. So p ≤ m-2.
    have h_p_le : p ≤ m - 2 := by omega
    have h_p_lt_m : 1 ≤ m - 1 - p := by omega
    have h_jlt : m - 1 - p < m := by omega
    have h_diff : 2 * m - 2 - k = 2 * (m - 1 - p) := by omega
    rw [h_diff]
    rw [ih.even_ih (m - 1 - p) h_p_lt_m h_jlt]
    ring

/-- **ODD case helper**: for `k+1` even in the ODD-case sum, `signedDyckSumTree(k+1) = 0`.

When `k + 1` is even with `k ∈ range (2m)`, we have `k+1 ∈ {2, 4, ..., 2m}`.
For `k+1 ∈ [2, 2m-2]`: IH gives `signedDyckSumTree = 0`.
For `k+1 = 2m`: use the just-proven `signedDyckSumTree (2*m) = 0`. -/
theorem odd_case_even_factor_zero (m : ℕ) (hm : 1 ≤ m) (ih : SignedDyckSumTreeIH m)
    (h_2m : signedDyckSumTree (2 * m) = 0)
    (k : ℕ) (hk : k < 2 * m) (h_even : Even (k + 1)) :
    signedDyckSumTree (k + 1) = 0 := by
  obtain ⟨j, hj⟩ := h_even
  -- k+1 = 2j (from even).
  have h_k1 : k + 1 = 2 * j := by omega
  have h_j_pos : 1 ≤ j := by omega
  have h_j_le_m : j ≤ m := by omega
  rcases lt_or_eq_of_le h_j_le_m with h_j_lt | h_j_eq
  · rw [h_k1]
    exact ih.even_ih j h_j_pos h_j_lt
  · rw [h_k1, h_j_eq]
    exact h_2m

/-- **ODD case sum simplification**: the odd-odd part of the sum reduces to a Catalan-recurrence form. -/
theorem odd_case_odd_factor_eq (m : ℕ) (hm : 1 ≤ m) (ih : SignedDyckSumTreeIH m)
    (k : ℕ) (hk : k < 2 * m) (h_odd : Odd (k + 1)) :
    signedDyckSumTree (k + 1) * signedDyckSumTree (2 * m - 1 - k) =
      (-1 : ℤ) ^ (m + 1) * ((catalan (k / 2) : ℤ) * (catalan (m - 1 - k / 2) : ℤ)) := by
  obtain ⟨p, hp⟩ := h_odd
  -- k + 1 = 2p + 1, so k = 2p, p ∈ [0, m-1].
  have h_k_eq : k = 2 * p := by omega
  have h_p_lt : p < m := by omega
  have h_p_le : p ≤ m - 1 := by omega
  -- k+1 = 2p+1, signedDyckSumTree(k+1) = (-1)^(p+1) * catalan p by IH.
  have h_fst : signedDyckSumTree (k + 1) = (-1 : ℤ) ^ (p + 1) * (catalan p : ℤ) := by
    rw [show k + 1 = 2 * p + 1 from by omega]
    exact ih.odd_ih p h_p_lt
  -- 2m-1-k = 2(m-1-p)+1, signedDyckSumTree(2m-1-k) = (-1)^(m-p) * catalan(m-1-p) by IH.
  have h_diff : 2 * m - 1 - k = 2 * (m - 1 - p) + 1 := by omega
  have h_mp_lt : m - 1 - p < m := by omega
  have h_snd : signedDyckSumTree (2 * m - 1 - k) =
      (-1 : ℤ) ^ ((m - 1 - p) + 1) * (catalan (m - 1 - p) : ℤ) := by
    rw [h_diff]
    exact ih.odd_ih (m - 1 - p) h_mp_lt
  rw [h_fst, h_snd]
  -- k / 2 = p (since k = 2p).
  have h_k2 : k / 2 = p := by omega
  rw [h_k2]
  -- Exponent: (p+1) + (m-1-p+1) = m+1.
  have h_exp : (p + 1) + ((m - 1 - p) + 1) = m + 1 := by omega
  rw [show (-1 : ℤ) ^ (p + 1) * ↑(catalan p) * ((-1 : ℤ) ^ ((m - 1 - p) + 1) * ↑(catalan (m - 1 - p))) =
       (-1 : ℤ) ^ ((p + 1) + ((m - 1 - p) + 1)) * (↑(catalan p) * ↑(catalan (m - 1 - p))) from by
    rw [pow_add]; ring]
  rw [h_exp]

/-- **EVEN STEP**: under the IH for `m`, `signedDyckSumTree (2 * m) = 0` for `m ≥ 1`. -/
theorem signedDyckSumTree_even_step (m : ℕ) (hm : 1 ≤ m) (ih : SignedDyckSumTreeIH m) :
    signedDyckSumTree (2 * m) = 0 := by
  -- Apply recurrence at n = 2m-1 (so n+1 = 2m).
  have h_eq : 2 * m = (2 * m - 1) + 1 := by omega
  rw [h_eq, signedDyckSumTree_recurrence (2 * m - 1)]
  -- Use odd-IH for signedDyckSumTree(2m-1).
  have h_2m1_eq : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  have h_p_lt : m - 1 < m := by omega
  have h_exp_eq : (m - 1) + 1 = m := by omega
  have h_odd : signedDyckSumTree (2 * m - 1) = (-1 : ℤ) ^ m * (catalan (m - 1) : ℤ) := by
    rw [h_2m1_eq, ih.odd_ih (m - 1) h_p_lt, h_exp_eq]
  rw [h_odd]
  -- Sum collapses via Finset.sum_eq_single at index k = 2m-2.
  have h_sum : ∑ k ∈ Finset.range (2 * m - 1),
      signedDyckSumTree (k + 1) * signedDyckSumTree (2 * m - 1 - 1 - k) =
      (-1 : ℤ) ^ m * (catalan (m - 1) : ℤ) := by
    have h_simp : ∀ k, 2 * m - 1 - 1 - k = 2 * m - 2 - k := by intro k; omega
    simp only [h_simp]
    rw [Finset.sum_eq_single (2 * m - 2)]
    · -- The non-trivial term.
      have h_arg1 : 2 * m - 2 + 1 = 2 * m - 1 := by omega
      have h_arg2 : 2 * m - 2 - (2 * m - 2) = 0 := by omega
      rw [h_arg1, h_arg2, h_odd, signedDyckSumTree_zero]
      ring
    · -- Other terms are 0.
      intros k hk h_ne
      rw [Finset.mem_range] at hk
      have h_k1_ne : k + 1 ≠ 2 * m - 1 := fun h => h_ne (by omega)
      exact even_case_off_diagonal_zero m hm ih k hk h_k1_ne
    · -- 2m-2 ∈ range (2m-1).
      intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  rw [h_sum]
  ring

/-- **ODD STEP**: under the IH for `m`, signedDyckSumTree (2*m + 1) = (-1)^(m+1) · catalan m.

For `m = 0`: base case via `signedDyckSumTree_one` and `catalan_zero`.
For `m ≥ 1`: apply firstReturn recurrence at `n = 2m`. Use EVEN step to zero
`signedDyckSumTree(2m)`. Split sum by parity: even-even terms vanish (by helper);
odd-odd terms reindex via `k = 2p` and apply Catalan recurrence `catalan_succ'`. -/
theorem signedDyckSumTree_odd_step (m : ℕ) (ih : SignedDyckSumTreeIH m) :
    signedDyckSumTree (2 * m + 1) = (-1 : ℤ) ^ (m + 1) * (catalan m : ℤ) := by
  match m with
  | 0 =>
    rw [signedDyckSumTree_one, catalan_zero]
    simp
  | m' + 1 =>
    have hm' : 1 ≤ m' + 1 := by omega
    have h_2m1 : signedDyckSumTree (2 * (m' + 1)) = 0 :=
      signedDyckSumTree_even_step (m' + 1) hm' ih
    rw [show 2 * (m' + 1) + 1 = (2 * (m' + 1)) + 1 from rfl]
    rw [signedDyckSumTree_recurrence (2 * (m' + 1))]
    rw [h_2m1, neg_zero, zero_add]
    -- Split sum by parity.
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * (m' + 1)))
        (fun k => Even (k + 1))
        (fun k => signedDyckSumTree (k + 1) * signedDyckSumTree (2 * (m' + 1) - 1 - k))]
    -- Even part = 0.
    have h_even_sum : ∑ k ∈ (Finset.range (2 * (m' + 1))).filter (fun k => Even (k + 1)),
        signedDyckSumTree (k + 1) * signedDyckSumTree (2 * (m' + 1) - 1 - k) = 0 := by
      apply Finset.sum_eq_zero
      intros k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [odd_case_even_factor_zero (m' + 1) hm' ih h_2m1 k hk.1 hk.2]
      ring
    rw [h_even_sum, zero_add]
    -- Express each odd term via odd_case_odd_factor_eq.
    have h_odd_term : ∀ k ∈ (Finset.range (2 * (m' + 1))).filter (fun k => ¬ Even (k + 1)),
        signedDyckSumTree (k + 1) * signedDyckSumTree (2 * (m' + 1) - 1 - k) =
          (-1 : ℤ) ^ ((m' + 1) + 1) *
            ((catalan (k / 2) : ℤ) * (catalan ((m' + 1) - 1 - k / 2) : ℤ)) := by
      intros k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      have h_odd : Odd (k + 1) := Nat.not_even_iff_odd.mp hk.2
      exact odd_case_odd_factor_eq (m' + 1) hm' ih k hk.1 h_odd
    rw [Finset.sum_congr rfl h_odd_term]
    -- Factor out (-1)^(m'+2) constant.
    rw [← Finset.mul_sum]
    -- Now reindex the inner sum via k = 2p.
    congr 1
    -- The filter set equals range(m'+1).image (·*2).
    have h_set_eq : (Finset.range (2 * (m' + 1))).filter (fun k => ¬ Even (k + 1)) =
        (Finset.range (m' + 1)).image (fun p => 2 * p) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hk_lt, hk_not_even⟩
        rw [Nat.not_even_iff_odd] at hk_not_even
        obtain ⟨p, hp⟩ := hk_not_even
        exact ⟨p, by omega, by omega⟩
      · rintro ⟨p, hp_lt, hp_eq⟩
        refine ⟨by omega, ?_⟩
        rw [← hp_eq]
        intro h_even
        obtain ⟨j, hj⟩ := h_even
        omega
    rw [h_set_eq]
    rw [Finset.sum_image (fun a _ b _ h => by
      show a = b
      have h' : 2 * a = 2 * b := h
      omega)]
    -- Simplify: ∑ p ∈ range (m'+1), catalan ((2p)/2) * catalan (m' - (2p)/2).
    have h_simp_inner : ∀ p ∈ Finset.range (m' + 1),
        (catalan ((2 * p) / 2) : ℤ) * (catalan ((m' + 1) - 1 - (2 * p) / 2) : ℤ) =
        (catalan p : ℤ) * (catalan (m' - p) : ℤ) := by
      intros p hp
      rw [Finset.mem_range] at hp
      have h_div : (2 * p) / 2 = p := by omega
      rw [h_div]
      have h_arg : (m' + 1) - 1 - p = m' - p := by omega
      rw [h_arg]
    rw [Finset.sum_congr rfl h_simp_inner]
    -- Apply Catalan recurrence.
    have h_cat_range : catalan (m' + 1) =
        ∑ p ∈ Finset.range (m' + 1), catalan p * catalan (m' - p) := by
      rw [catalan_succ' m']
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun p q => catalan p * catalan q) m'
    rw [h_cat_range]
    push_cast
    rfl

/-! ### Combined closed form via Nat.strong_induction -/

/-- **CLOSED FORM** for `signedDyckSumTree`, PROVEN UNCONDITIONALLY via mutual strong induction:

For all `m : ℕ`:
* `signedDyckSumTree (2 * m) = 0` for `m ≥ 1`.
* `signedDyckSumTree (2 * m + 1) = (-1)^(m+1) · catalan m`. -/
theorem signedDyckSumTree_closed_form : ∀ m : ℕ,
    (1 ≤ m → signedDyckSumTree (2 * m) = 0) ∧
    (signedDyckSumTree (2 * m + 1) = (-1 : ℤ) ^ (m + 1) * (catalan m : ℤ)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have IH : SignedDyckSumTreeIH m := {
      even_ih := fun j h1 h2 => (ih j h2).1 h1
      odd_ih := fun p hp => (ih p hp).2
    }
    refine ⟨fun hm => signedDyckSumTree_even_step m hm IH, signedDyckSumTree_odd_step m IH⟩

/-- `signedDyckSumTree (2m) = 0` for `m ≥ 1`, UNCONDITIONAL. -/
theorem signedDyckSumTree_two_mul (m : ℕ) (hm : 1 ≤ m) : signedDyckSumTree (2 * m) = 0 :=
  (signedDyckSumTree_closed_form m).1 hm

/-- `signedDyckSumTree (2m+1) = (-1)^(m+1) · catalan m`, UNCONDITIONAL. -/
theorem signedDyckSumTree_two_mul_succ (m : ℕ) :
    signedDyckSumTree (2 * m + 1) = (-1 : ℤ) ^ (m + 1) * (catalan m : ℤ) :=
  (signedDyckSumTree_closed_form m).2

/-! ### FINAL: Bipartite imbalance UNCONDITIONAL for ALL odd n -/

/-- **MAIN UNCONDITIONAL THEOREM**: for any odd `n ≥ 1`,
`signedNCCount(univ Fin n) ≠ 0`.

This BYPASSES the Narayana count formula axiom entirely. -/
theorem signedNCCount_fin_odd_ne_zero_unconditional (n : ℕ) (hn : Odd n) :
    signedNCCount (Finset.univ : Finset (Fin n)) ≠ 0 := by
  obtain ⟨m, hm⟩ := hn
  -- n = 2*m + 1.
  rw [signedNCCount_univ_eq_signedDyckSumTree]
  rw [hm]
  rw [signedDyckSumTree_two_mul_succ m]
  -- Need: (-1)^(m+1) * catalan m ≠ 0.
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0)
  · exact_mod_cast (Nat.catalan_pos m).ne'

/-! ### UNCONDITIONAL bipartite imbalance for Fin n -/

/-- **UNCONDITIONAL bipartite imbalance** for `Fin n` with odd `n`:
`|evenBlocks(univ Fin n)| ≠ |oddBlocks(univ Fin n)|`.

This closes the bipartite imbalance UNCONDITIONALLY for any odd `n ≥ 1`,
BYPASSING the Narayana count formula axiom. -/
theorem evenBlocks_card_ne_oddBlocks_card_fin_odd_unconditional (n : ℕ) (hn : Odd n) :
    (evenBlocks (Finset.univ : Finset (Fin n))).card ≠
      (oddBlocks (Finset.univ : Finset (Fin n))).card := by
  intro h_eq
  apply signedNCCount_fin_odd_ne_zero_unconditional n hn
  rw [signedNCCount_eq_evenBlocks_sub_oddBlocks, h_eq]
  ring

end NC

end Hamilton.Infrastructure
