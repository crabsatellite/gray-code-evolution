/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.NCToDyckList

/-!
# Stack-process reconstruction of NC from `(BM, sizes)` profile

The **stack-process determinism** fact: for non-crossing partitions, the
`(blockMaxes, block-size)` profile uniquely determines the partition.

This is the **deep combinatorial fact** at the heart of NC uniqueness.
The reconstruction is implemented as a `List.foldl` with state, processing
elements of `s.sort` in increasing order.  At each element:
- Push onto stack.
- If it's a block-max: pop `f(i)` elements as a block.

## Main definitions

* `NC.RecState` — fold state (stack + accumulated blocks).
* `NC.reconstructStep` — one step of the fold.
* `NC.reconstructFromProfile` — the full reconstruction.

## Main theorem (target)

* `NC.reconstructFromProfile_eq_parts` — for any NC π, the reconstruction
  using its (BM, sizes) profile equals `π.val.parts`.

## Consequence

NCs with same `(BM, sizes)` profile produce same reconstruction, hence equal.
This is the LAST piece for `toDyckWord` injectivity, which completes the
NC ↔ DyckWord bijection.

## Tags

NC, stack process, reconstruction, uniqueness, NC injectivity
-/

namespace Hamilton.Infrastructure

namespace NC

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- State of the stack-process reconstruction fold. -/
structure RecState (α : Type*) where
  /-- Elements pushed but not yet popped (stack, top first). -/
  stack : List α
  /-- Finalized blocks so far. -/
  blocks : List (Finset α)

namespace RecState
/-- Empty initial state. -/
def empty (α : Type*) : RecState α := ⟨[], []⟩
end RecState

/-- One step of the reconstruction: push `i`, then if `i` is in BM, pop `f i` elements
as a finalized block. -/
def reconstructStep (BM : Finset α) [DecidablePred (· ∈ BM)] (f : α → ℕ)
    (st : RecState α) (i : α) : RecState α :=
  let new_stack := i :: st.stack
  if i ∈ BM then
    let popped := new_stack.take (f i)
    let remaining := new_stack.drop (f i)
    ⟨remaining, st.blocks ++ [popped.toFinset]⟩
  else
    ⟨new_stack, st.blocks⟩

/-- The full reconstruction: process `sortedS` with the stack algorithm. -/
def reconstructFromProfile (BM : Finset α) [DecidablePred (· ∈ BM)] (f : α → ℕ)
    (sortedS : List α) : List (Finset α) :=
  (sortedS.foldl (reconstructStep BM f) (RecState.empty α)).blocks

/-! ### Basic properties -/

/-- Empty input gives empty blocks. -/
@[simp] theorem reconstructFromProfile_nil (BM : Finset α) [DecidablePred (· ∈ BM)] (f : α → ℕ) :
    reconstructFromProfile BM f [] = [] := rfl

/-- Reconstruction respects cons-decomposition of the input. -/
theorem reconstructFromProfile_cons (BM : Finset α) [DecidablePred (· ∈ BM)] (f : α → ℕ)
    (head : α) (tail : List α) :
    reconstructFromProfile BM f (head :: tail) =
      (tail.foldl (reconstructStep BM f) (reconstructStep BM f (RecState.empty α) head)).blocks := by
  unfold reconstructFromProfile
  rw [List.foldl_cons]

/-! ### Unfolding lemmas for reconstructStep -/

/-- Block-max case: push then pop. -/
theorem reconstructStep_blockMax (BM : Finset α) [DecidablePred (· ∈ BM)]
    (f : α → ℕ) (st : RecState α) {i : α} (h : i ∈ BM) :
    reconstructStep BM f st i =
      ⟨(i :: st.stack).drop (f i),
       st.blocks ++ [((i :: st.stack).take (f i)).toFinset]⟩ := by
  unfold reconstructStep
  rw [if_pos h]

/-- Non-block-max case: just push. -/
theorem reconstructStep_not_blockMax (BM : Finset α) [DecidablePred (· ∈ BM)]
    (f : α → ℕ) (st : RecState α) {i : α} (h : i ∉ BM) :
    reconstructStep BM f st i = ⟨i :: st.stack, st.blocks⟩ := by
  unfold reconstructStep
  rw [if_neg h]

/-- After the empty fold (= start), stack = [] and blocks = []. -/
theorem reconstructFromProfile_state_at_start (BM : Finset α)
    [DecidablePred (· ∈ BM)] (f : α → ℕ) :
    ([] : List α).foldl (reconstructStep BM f) (RecState.empty α) = RecState.empty α := rfl

/-- After processing a singleton with i ∈ BM and f(i) = 1: blocks = [{i}], stack = []. -/
theorem reconstructFromProfile_singleton_blockMax (BM : Finset α) [DecidablePred (· ∈ BM)]
    (f : α → ℕ) {i : α} (h_bm : i ∈ BM) (h_f : f i = 1) :
    reconstructFromProfile BM f [i] = [({i} : Finset α)] := by
  unfold reconstructFromProfile
  rw [show [i].foldl (reconstructStep BM f) (RecState.empty α) =
        reconstructStep BM f (RecState.empty α) i from rfl]
  rw [reconstructStep_blockMax BM f (RecState.empty α) h_bm]
  show ([(i :: ([] : List α)).take (f i)].map List.toFinset) = _
  rw [h_f]
  rfl

/-- After processing a singleton with i ∉ BM: stack = [i], blocks = []. -/
theorem reconstructFromProfile_singleton_not_blockMax (BM : Finset α) [DecidablePred (· ∈ BM)]
    (f : α → ℕ) {i : α} (h_bm : i ∉ BM) :
    reconstructFromProfile BM f [i] = [] := by
  unfold reconstructFromProfile
  rw [show [i].foldl (reconstructStep BM f) (RecState.empty α) =
        reconstructStep BM f (RecState.empty α) i from rfl]
  rw [reconstructStep_not_blockMax BM f (RecState.empty α) h_bm]
  rfl

/-! ### Documentation: invariant framework for correctness proof

The stack-process correctness invariant: after processing first `j` elements
of `s.sort`, the state should satisfy:

* `state.blocks` = list of parts of `π` whose `block-max` is in the first
  `j` elements (= already-closed blocks).
* `state.stack` = list of elements in first `j` elements whose `block-max`
  is NOT in the first `j` elements (= elements still pending pop), in
  LIFO order (top = most recently pushed unpopped).

For NC π, this invariant is the structural foundation: at every block-max
step, the top `|part i|` of stack are EXACTLY the elements of `part i`,
ensuring the pop produces the correct block.

**Why the invariant holds in NC**: By non-crossing, when `l_{j+1}` is processed
(block-max), any element `x` with `x < l_{j+1}` and `x` still on stack has
either:
- `block_max π x = l_{j+1}` (i.e., x is in part l_{j+1}), OR
- `block_max π x > l_{j+1}` (x is in an "outer" block).

For NC, outer-block elements with `max > l_{j+1}` that are `< l_{j+1}` are
pushed BEFORE the inner-block elements (by the sorted-order interleaving),
hence lie BELOW the part-l_{j+1} elements in the LIFO stack.

So the top `|part l_{j+1}|` of stack (after pushing `l_{j+1}` itself) are
exactly part l_{j+1}.  Popping them produces the correct block.

The full formalization is left as multi-round future work.
-/

/-! ### Verified special case: all-singletons profile -/

/-- When every element of `sortedS` is in `BM` with `f = 1`, the reconstruction
produces all singletons.

This is the simplest non-trivial verification of `reconstructFromProfile`,
corresponding to the NC where every block is a singleton (the finest partition).
The stack invariant in this case is trivial: stack is always empty after each
step (push i, pop f(i) = 1 ⟹ pop i ⟹ stack same as before). -/
theorem reconstructFromProfile_all_singletons (BM : Finset α) [DecidablePred (· ∈ BM)]
    (f : α → ℕ) (sortedS : List α)
    (h_all_bm : ∀ i ∈ sortedS, i ∈ BM) (h_all_one : ∀ i ∈ sortedS, f i = 1) :
    reconstructFromProfile BM f sortedS = sortedS.map (fun i => ({i} : Finset α)) := by
  -- We prove a stronger invariant: after processing any prefix, stack = [] and
  -- blocks = (prefix.map singletons). Then specialize to full input.
  -- The invariant: for any initial state ⟨[], init_blocks⟩, fold gives
  -- ⟨[], init_blocks ++ (input.map singletons)⟩.
  suffices h : ∀ (init_blocks : List (Finset α)),
      sortedS.foldl (reconstructStep BM f) ⟨[], init_blocks⟩ =
      ⟨[], init_blocks ++ sortedS.map (fun i => ({i} : Finset α))⟩ by
    unfold reconstructFromProfile
    have h' := h []
    rw [show (RecState.empty α : RecState α) = ⟨[], []⟩ from rfl] at *
    rw [h']
    simp
  induction sortedS with
  | nil =>
    intros init_blocks
    simp
  | cons head tail ih =>
    intros init_blocks
    have h_head_bm : head ∈ BM := h_all_bm head List.mem_cons_self
    have h_head_one : f head = 1 := h_all_one head List.mem_cons_self
    rw [List.foldl_cons]
    rw [reconstructStep_blockMax BM f ⟨[], init_blocks⟩ h_head_bm]
    rw [show (head :: ([] : List α)).take (f head) = [head] from by
        rw [h_head_one]; rfl]
    rw [show (head :: ([] : List α)).drop (f head) = [] from by
        rw [h_head_one]; rfl]
    rw [ih (fun i hi => h_all_bm i (List.mem_cons_of_mem _ hi))
           (fun i hi => h_all_one i (List.mem_cons_of_mem _ hi))]
    simp [List.toFinset_cons]

/-! ### Verified special case: all-stack (no block-max) -/

/-- When NO element of `sortedS` is in `BM`, the reconstruction never pops:
all elements accumulate on the stack, no blocks finalized. -/
theorem reconstructFromProfile_no_blockMax (BM : Finset α) [DecidablePred (· ∈ BM)]
    (f : α → ℕ) (sortedS : List α) (h_none_bm : ∀ i ∈ sortedS, i ∉ BM) :
    sortedS.foldl (reconstructStep BM f) (RecState.empty α) =
    ⟨sortedS.reverse, []⟩ := by
  -- Strengthened induction with arbitrary initial stack and empty blocks.
  suffices h : ∀ (init_stack : List α),
      sortedS.foldl (reconstructStep BM f) ⟨init_stack, []⟩ =
      ⟨sortedS.reverse ++ init_stack, []⟩ by
    have h' := h []
    simp at h'
    rw [show (RecState.empty α : RecState α) = ⟨[], []⟩ from rfl]
    rw [h']
  induction sortedS with
  | nil =>
    intros init_stack
    simp
  | cons head tail ih =>
    intros init_stack
    have h_head_not_bm : head ∉ BM := h_none_bm head List.mem_cons_self
    rw [List.foldl_cons]
    rw [reconstructStep_not_blockMax BM f ⟨init_stack, []⟩ h_head_not_bm]
    rw [ih (fun i hi => h_none_bm i (List.mem_cons_of_mem _ hi))]
    -- Show: ⟨tail.reverse ++ (head :: init_stack), []⟩ =
    --       ⟨(head :: tail).reverse ++ init_stack, []⟩
    simp [List.reverse_cons]

/-! ### Conservation laws (universally true regardless of input validity) -/

/-- After a single step, the stack length changes by `1 - f(i)` (block-max case)
or `1` (non-block-max case), bounded by what's available. -/
theorem reconstructStep_stack_length (BM : Finset α) [DecidablePred (· ∈ BM)]
    (f : α → ℕ) (st : RecState α) (i : α) :
    (reconstructStep BM f st i).stack.length =
      if i ∈ BM then (st.stack.length + 1) - (f i)
      else st.stack.length + 1 := by
  unfold reconstructStep
  split_ifs with h
  · simp [List.length_drop, List.length_cons]
  · simp [List.length_cons]

/-- After a single step, blocks count changes by `1` (if block-max) or `0`. -/
theorem reconstructStep_blocks_length (BM : Finset α) [DecidablePred (· ∈ BM)]
    (f : α → ℕ) (st : RecState α) (i : α) :
    (reconstructStep BM f st i).blocks.length =
      if i ∈ BM then st.blocks.length + 1 else st.blocks.length := by
  unfold reconstructStep
  split_ifs <;> simp

/-- The block count after processing equals the number of block-maxes in the input. -/
theorem reconstructFromProfile_blocks_length_eq_filter_card
    (BM : Finset α) [DecidablePred (· ∈ BM)] (f : α → ℕ) (sortedS : List α) :
    (reconstructFromProfile BM f sortedS).length =
      (sortedS.filter (· ∈ BM)).length := by
  -- Generalize: for any init state, fold accumulates `init.blocks.length` + bm-count.
  suffices h : ∀ (init : RecState α),
      (sortedS.foldl (reconstructStep BM f) init).blocks.length =
      init.blocks.length + (sortedS.filter (· ∈ BM)).length by
    unfold reconstructFromProfile
    have h_init := h (RecState.empty α)
    rw [h_init]
    show (0 + (sortedS.filter (· ∈ BM)).length = (sortedS.filter (· ∈ BM)).length)
    omega
  induction sortedS with
  | nil =>
    intro init
    simp
  | cons head tail ih =>
    intro init
    rw [List.foldl_cons]
    rw [ih]
    rw [reconstructStep_blocks_length]
    split_ifs with h
    · rw [List.filter_cons_of_pos (by simpa using h)]
      simp; omega
    · rw [List.filter_cons_of_neg (by simpa using h)]

/-! ### NC-specific conservation: block count matches numBlocks -/

/-- For NC `π` with input `s.sort`, the reconstruction's block count equals
`numBlocks π` — the number of block-maxes. -/
theorem reconstructFromProfile_blocks_length_eq_numBlocks
    {α : Type*} [LinearOrder α] {s : Finset α} (π : NC s) :
    (reconstructFromProfile (blockMaxes π) (fun i => (π.val.part i).card)
      (s.sort (· ≤ ·))).length = numBlocks π := by
  rw [reconstructFromProfile_blocks_length_eq_filter_card]
  rw [numBlocks_eq_blockMaxes_card]
  -- |sortedS.filter (· ∈ blockMaxes π)| = (blockMaxes π).card
  have h_nodup : ((s.sort (· ≤ ·)).filter (· ∈ blockMaxes π)).Nodup :=
    (s.sort_nodup (· ≤ ·)).filter _
  rw [← List.toFinset_card_of_nodup h_nodup]
  congr 1
  -- (s.sort.filter (· ∈ BM)).toFinset = BM
  rw [List.toFinset_filter, Finset.sort_toFinset]
  -- s.filter (· ∈ BM) = BM (since BM ⊆ s)
  have h_sub : blockMaxes π ⊆ s := by
    intros b hb
    unfold blockMaxes at hb
    rw [Finset.mem_filter] at hb
    exact hb.1
  -- Apply: s.filter (· ∈ T) = T when T ⊆ s.
  have h_eq : s.filter (fun x => x ∈ blockMaxes π) = blockMaxes π := by
    ext b
    constructor
    · intro hb
      rw [Finset.mem_filter] at hb
      exact hb.2
    · intro hb
      rw [Finset.mem_filter]
      exact ⟨h_sub hb, hb⟩
  simpa using h_eq

end NC

end Hamilton.Infrastructure
