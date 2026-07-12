/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.HamiltonPath
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Powerset

/-!
# Hamilton laceability of the hypercube

The vertices are finite subsets and two vertices are adjacent when their
symmetric difference has cardinality one.  The main theorem constructs a
Hamilton path between every pair of opposite-parity vertices.  The construction
is an induction on the ground set and is carried out at the list level before
being converted to a graph walk.
-/
namespace Hamilton.Infrastructure

namespace Cube

open Finset
open scoped symmDiff

universe u_ι

variable {ι : Type u_ι} [DecidableEq ι]

/-! ## §0 — generic list→walk Hamilton bridge (self-contained) -/

/-- **`walkOfChain`** — build a `Walk` from a nonempty list whose
consecutive entries are `G.Adj`-adjacent (`List.IsChain G.Adj`)
(`\label{def:walkOfChain}`, §0).

Recursion on the list: `[v]` is `nil`; `v :: w :: rest` is `cons` of the
`v–w` edge onto the recursive walk.  `Walk.copy` realigns the dependent
endpoints to `L.head`/`L.getLast`. -/
def walkOfChain {V : Type*} {G : SimpleGraph V} :
    ∀ (L : List V) (hne : L ≠ []) (_hc : List.IsChain G.Adj L),
      G.Walk (L.head hne) (L.getLast hne)
  | [_], _, _ => (SimpleGraph.Walk.nil).copy rfl (by simp)
  | v :: w :: rest, _, hc => by
      rw [List.isChain_cons] at hc
      have hadj : G.Adj v w := hc.1 w (by simp)
      have tail := walkOfChain (w :: rest) (by simp) hc.2
      refine (SimpleGraph.Walk.cons hadj tail).copy rfl ?_
      simp [List.getLast_cons]

/-- **`walkOfChain_support`** — the support of `walkOfChain` is exactly
the list (`\label{thm:walkOfChain_support}`, §0).  Structural induction. -/
theorem walkOfChain_support {V : Type*} {G : SimpleGraph V} :
    ∀ (L : List V) (hne : L ≠ []) (hc : List.IsChain G.Adj L),
      (walkOfChain L hne hc).support = L
  | [_], _, _ => by simp [walkOfChain]
  | _ :: w :: rest, _, hc => by
      have ih := walkOfChain_support (w :: rest) (by simp) (List.isChain_cons.mp hc).2
      simp only [walkOfChain, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons]
      congr 1

/-- **`hamiltonianPathBetween_of_chain_list`** — **THE §0 BRIDGE**: a
`Nodup`, type-covering, single-step (`IsChain G.Adj`) list with head `u`
and last `v` yields a `G.HamiltonianPathBetween u v`
(`\label{thm:hamiltonianPathBetween_of_chain_list}`, §0).

The walk is `\ref{def:walkOfChain}`; its support is the list
(`\ref{thm:walkOfChain_support}`); `Nodup` + coverage give each vertex
count exactly `1` — the Hamilton condition. -/
theorem hamiltonianPathBetween_of_chain_list {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (L : List V) (hne : L ≠ [])
    (hc : List.IsChain G.Adj L) (hnd : L.Nodup) (hcov : ∀ x, x ∈ L) {u v : V}
    (hu : L.head hne = u) (hv : L.getLast hne = v) :
    G.HamiltonianPathBetween u v := by
  subst hu hv
  refine ⟨walkOfChain L hne hc, ?_⟩
  intro x
  rw [walkOfChain_support]
  exact List.count_eq_one_of_mem hnd (hcov x)

/-! ## §B.1 — the hypercube graph `Q_m`, single-flip adjacency, parity -/

/-- **`flipAdj`** — the single-flip adjacency on subsets: `A` and `B`
differ by a symmetric difference of cardinality `1`
(`\label{def:flipAdj}`, B.1).  This is the hypercube edge relation:
exactly one element is added or removed. -/
def flipAdj (A B : Finset ι) : Prop := (A ∆ B).card = 1

/-- `flipAdj` is symmetric (symmetric difference is symmetric)
(`\label{thm:flipAdj_symm}`). -/
theorem flipAdj_symm {A B : Finset ι} (h : flipAdj A B) : flipAdj B A := by
  unfold flipAdj at *; rwa [symmDiff_comm]

/-- `flipAdj` is irreflexive (`A ∆ A = ∅` has card `0`)
(`\label{thm:flipAdj_irrefl}`). -/
theorem flipAdj_irrefl (A : Finset ι) : ¬ flipAdj A A := by
  unfold flipAdj; simp

/-- **`Qgraph`** — **THE B.1 HYPERCUBE GRAPH** `Q` on `Finset ι`:
vertices are finite subsets, edges are single-element flips
(`\ref{def:flipAdj}`) (`\label{def:Qgraph}`, B.1).  For `ι = Fin m` this
is the `m`-cube `Q_m`. -/
def Qgraph (ι : Type u_ι) [DecidableEq ι] : SimpleGraph (Finset ι) where
  Adj := flipAdj
  symm _ _ := flipAdj_symm
  loopless := ⟨flipAdj_irrefl⟩

@[simp] theorem Qgraph_adj {A B : Finset ι} : (Qgraph ι).Adj A B ↔ flipAdj A B := Iff.rfl

/-- **`cubeParity`** — **B.1 PARITY**: the parity colour of a cube vertex
is `card mod 2` (`\label{def:cubeParity}`, B.1).  Opposite parity is the
bipartition class condition for laceability. -/
def cubeParity (A : Finset ι) : ℕ := A.card % 2

/-- The symmetric difference splits as the disjoint union of the two
one-sided differences, so its card is the sum
(`\label{thm:card_symmDiff_eq}`, B.1 helper). -/
theorem card_symmDiff_eq (A B : Finset ι) :
    (A ∆ B).card = (A \ B).card + (B \ A).card := by
  rw [symmDiff_def, sup_eq_union, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]

/-- A single flip toggles parity: adjacent vertices have opposite parity
(`\label{thm:flipAdj_parity_ne}`, B.1) — `Q` is bipartite by `cubeParity`. -/
theorem flipAdj_parity_ne {A B : Finset ι} (h : flipAdj A B) :
    cubeParity A ≠ cubeParity B := by
  -- |A| + |B| = |A ∆ B| + 2·|A ∩ B|, and |A ∆ B| = 1 is odd.
  have hAB := card_symmDiff_eq A B
  have hA := card_sdiff_add_card_inter A B
  have hB := card_sdiff_add_card_inter B A
  rw [inter_comm] at hB
  unfold flipAdj at h
  unfold cubeParity
  omega

/-- A single insertion of a fresh element is a flip
(`\label{thm:flipAdj_insert}`, B.1).  Foundational for the induction's
add/remove edges. -/
theorem flipAdj_insert {A : Finset ι} {a : ι} (ha : a ∉ A) :
    flipAdj A (insert a A) := by
  unfold flipAdj
  have h_eq : A ∆ (insert a A) = {a} := by
    ext x
    simp only [mem_symmDiff, mem_insert, mem_singleton]
    by_cases hxa : x = a
    · subst hxa; simp [ha]
    · simp [hxa]
  rw [h_eq]; simp

/-- `flipAdj` is preserved under `insert a` when `a` is absent from both
sides (`\label{thm:flipAdj_map_insert}`, B.1).  Used when lifting a
lower-half path to the upper half. -/
theorem flipAdj_map_insert {A B : Finset ι} {a : ι} (haA : a ∉ A)
    (haB : a ∉ B) (h : flipAdj A B) :
    flipAdj (insert a A) (insert a B) := by
  unfold flipAdj at *
  have key : (insert a A) ∆ (insert a B) = A ∆ B := by
    ext x
    simp only [mem_symmDiff, mem_insert]
    by_cases hx : x = a
    · subst hx; simp [haA, haB]
    · simp only [hx, false_or]
  rw [key, h]

/-! ## §0' — member-aware `List.IsChain` implication (Mathlib helper) -/

/-- **`isChain_imp_of_mem`** — refine an `IsChain` predicate when the
implication only holds for elements of the list
(`\label{thm:isChain_imp_of_mem}`, §0').  Slight generalisation of
Mathlib's `List.IsChain.imp` to a member-aware hypothesis; proved by
structural induction. -/
theorem isChain_imp_of_mem {α : Type*} {R S : α → α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∀ b ∈ l, R a b → S a b) →
      List.IsChain R l → List.IsChain S l
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: rest, H, h => by
    rw [List.isChain_cons] at h ⊢
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hy
      exact H a (by simp) b (by simp) (h.1 b (by simp))
    · apply isChain_imp_of_mem _ h.2
      intro x hx y hy hR
      exact H x (by simp [hx]) y (by simp [hy]) hR

/-! ## §B.2 / §B.3 — `CubeListOn`: a Hamilton-path-on-the-cube as a list
+ structural lemmas (reverse, map-insert, append-at-cross-edge, splice) -/

/-- **`CubeListOn cover u v L`** — **THE B.2 CARRIER**: the list `L` is a
single-flip Hamilton path covering exactly the subsets satisfying
`cover`, from `u` to `v` (`\label{def:CubeListOn}`, B.2).

* `head_eq` / `last_eq`: endpoints `u` / `v`;
* `nodup`: each vertex appears at most once;
* `chain`: every consecutive pair is `\ref{def:flipAdj}`-adjacent;
* `cover_iff`: membership in `L` is exactly the cover predicate.

When `cover = (· ⊆ ground)` over `ground = Finset.univ` (whole cube),
`cover_iff` reduces to "every vertex appears (and only those, by
`nodup`)" — the Hamilton condition the graph bridge consumes. -/
structure CubeListOn (cover : Finset ι → Prop) (u v : Finset ι)
    (L : List (Finset ι)) : Prop where
  head_eq : L.head? = some u
  last_eq : L.getLast? = some v
  nodup : L.Nodup
  chain : List.IsChain flipAdj L
  cover_iff : ∀ S, S ∈ L ↔ cover S

/-- Nonemptiness from the `head_eq` field (`\label{thm:CubeListOn_ne_nil}`). -/
theorem CubeListOn.ne_nil {cover : Finset ι → Prop} {u v : Finset ι}
    {L : List (Finset ι)} (h : CubeListOn cover u v L) : L ≠ [] := by
  rintro rfl
  exact absurd h.head_eq (by simp)

/-- The starting endpoint `u` is in the cover (it's the head)
(`\label{thm:CubeListOn_head_mem_cover}`). -/
theorem CubeListOn.head_mem_cover {cover : Finset ι → Prop} {u v : Finset ι}
    {L : List (Finset ι)} (h : CubeListOn cover u v L) : cover u := by
  apply (h.cover_iff u).mp
  have hne := h.ne_nil
  have h_eq : L.head hne = u := by
    have := h.head_eq
    rw [List.head?_eq_some_head hne, Option.some_inj] at this
    exact this
  rw [← h_eq]
  exact List.head_mem hne

/-- The ending endpoint `v` is in the cover
(`\label{thm:CubeListOn_last_mem_cover}`). -/
theorem CubeListOn.last_mem_cover {cover : Finset ι → Prop} {u v : Finset ι}
    {L : List (Finset ι)} (h : CubeListOn cover u v L) : cover v := by
  apply (h.cover_iff v).mp
  have hne := h.ne_nil
  have h_eq : L.getLast hne = v := by
    have := h.last_eq
    rw [List.getLast?_eq_some_getLast hne, Option.some_inj] at this
    exact this
  rw [← h_eq]
  exact List.getLast_mem hne

/-- **Reverse a `CubeListOn`**: head/last swap, all other fields
preserved (`\label{thm:CubeListOn_reverse}`). -/
theorem CubeListOn.reverse {cover : Finset ι → Prop} {u v : Finset ι}
    {L : List (Finset ι)} (h : CubeListOn cover u v L) :
    CubeListOn cover v u L.reverse := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_reverse]; exact h.last_eq
  · rw [List.getLast?_reverse]; exact h.head_eq
  · exact List.nodup_reverse.mpr h.nodup
  · rw [List.isChain_reverse]
    have : (fun a b => flipAdj b a) = (flipAdj : Finset ι → Finset ι → Prop) := by
      funext a b; exact propext ⟨flipAdj_symm, flipAdj_symm⟩
    rw [this]; exact h.chain
  · intro S; rw [List.mem_reverse]; exact h.cover_iff S

/-- **Map a `CubeListOn` by `insert a`**: given a fresh element `a`
absent from every cover member, lift the list to the "upper half"
(subsets containing `a` whose erasure satisfies the old cover)
(`\label{thm:CubeListOn_mapInsert}`).

Used to transport a lower-half Hamilton path to the upper half — the
key structural building block for both the cross-half and same-half
inductive steps. -/
theorem CubeListOn.mapInsert {cover : Finset ι → Prop} {u v : Finset ι}
    {L : List (Finset ι)} {a : ι}
    (ha : ∀ S, cover S → a ∉ S) (h : CubeListOn cover u v L) :
    CubeListOn (fun S => a ∈ S ∧ cover (S.erase a))
      (insert a u) (insert a v) (L.map (insert a)) := by
  have haL : ∀ S ∈ L, a ∉ S := fun S hS => ha S ((h.cover_iff S).mp hS)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_map, h.head_eq]; rfl
  · rw [List.getLast?_map, h.last_eq]; rfl
  · rw [List.nodup_map_iff_inj_on h.nodup]
    intro x hx y hy hxy
    have hax := haL x hx
    have hay := haL y hy
    have := congrArg (·.erase a) hxy
    simpa [Finset.erase_insert hax, Finset.erase_insert hay] using this
  · rw [List.isChain_map]
    -- IsChain (fun A B => flipAdj (insert a A) (insert a B)) L
    apply isChain_imp_of_mem _ h.chain
    intro A hA B hB hAB
    exact flipAdj_map_insert (haL A hA) (haL B hB) hAB
  · intro S
    rw [List.mem_map]
    constructor
    · rintro ⟨T, hT, rfl⟩
      have haT := haL T hT
      refine ⟨Finset.mem_insert_self a T, ?_⟩
      rw [Finset.erase_insert haT]
      exact (h.cover_iff T).mp hT
    · rintro ⟨haS, hcov⟩
      refine ⟨S.erase a, (h.cover_iff _).mpr hcov, ?_⟩
      exact Finset.insert_erase haS

/-- **Append two `CubeListOn`s at a cross edge** (with disjoint covers):
`L1` ends at `v1`, `L2` starts at `u2`, the edge `v1—u2` is a flip, and
the covers are disjoint
(`\label{thm:CubeListOn_append}`). -/
theorem CubeListOn.append {c1 c2 : Finset ι → Prop} {u1 v1 u2 v2 : Finset ι}
    {L1 L2 : List (Finset ι)}
    (h1 : CubeListOn c1 u1 v1 L1) (h2 : CubeListOn c2 u2 v2 L2)
    (hcross : flipAdj v1 u2)
    (hdisj : ∀ S, c1 S → c2 S → False) :
    CubeListOn (fun S => c1 S ∨ c2 S) u1 v2 (L1 ++ L2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_append, h1.head_eq]; rfl
  · rw [List.getLast?_append, h2.last_eq]; rfl
  · rw [List.nodup_append]
    refine ⟨h1.nodup, h2.nodup, ?_⟩
    intro x hx1 y hy2 hxy
    subst hxy
    exact hdisj x ((h1.cover_iff x).mp hx1) ((h2.cover_iff x).mp hy2)
  · rw [List.isChain_append]
    refine ⟨h1.chain, h2.chain, ?_⟩
    intro x hx y hy
    rw [h1.last_eq] at hx
    rw [h2.head_eq] at hy
    simp only [Option.mem_some_iff] at hx hy
    subst hx; subst hy
    exact hcross
  · intro S
    rw [List.mem_append, h1.cover_iff, h2.cover_iff]

/-- **Splice a detour into a main covering path** — the **same-half**
inductive case in its fully symmetric form
(`\label{thm:CubeListOn_splice}`).

Generic shape: a main covering path of the form `u :: w :: tail`
(length ≥ 2), together with a detour `Q` from `u'` to `w'` over a
DISJOINT cover, with single-flip cross edges `u → u'` and `w' → w`.
Output: the spliced single-flip Hamilton path
```
u :: Q ++ (w :: tail) = [u, u', …, w', w, …, v]
```
covering the union of the two covers.

For "same-half" (both endpoints in the lower half), instantiate with
`covM = lower`, `covD = upper`, `u' = insert a u`, `w' = insert a w`,
`Q = (lower path u→w).map (insert a)`.  For "same-half upper",
instantiate with `covM = upper`, `covD = lower`, `u' = u.erase a`,
`w' = w.erase a`, `Q = lower path (u.erase a)→(w.erase a)`. -/
theorem CubeListOn.splice {covM covD : Finset ι → Prop} {u v w u' w' : Finset ι}
    {tail : List (Finset ι)} {Q : List (Finset ι)}
    (h_main : CubeListOn covM u v (u :: w :: tail))
    (h_detour : CubeListOn covD u' w' Q)
    (h_cross_uu' : flipAdj u u')
    (h_cross_w'w : flipAdj w' w)
    (hdisj : ∀ S, covM S → covD S → False) :
    CubeListOn (fun S => covM S ∨ covD S) u v (u :: Q ++ (w :: tail)) := by
  -- Last element of (w :: tail) is some y (nonempty)
  have hwt_ne_none : (w :: tail).getLast? ≠ none := by
    rw [Ne, List.getLast?_eq_none_iff]; simp
  rcases hwt : (w :: tail).getLast? with _ | y
  · exact absurd hwt hwt_ne_none
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · -- last
    rw [show u :: Q ++ (w :: tail) = (u :: Q) ++ (w :: tail) from rfl,
      List.getLast?_append, hwt]
    have hlow := h_main.last_eq
    rw [show u :: w :: tail = [u] ++ (w :: tail) from rfl,
      List.getLast?_append, hwt] at hlow
    simpa using hlow
  · -- nodup
    rw [show u :: Q ++ (w :: tail) = u :: (Q ++ (w :: tail)) from rfl,
      List.nodup_cons]
    refine ⟨?_, ?_⟩
    · rw [List.mem_append]
      intro hu
      rcases hu with huQ | huwt
      · -- u ∈ Q ⟹ u ∈ covD; but u ∈ covM (head of main) ⟹ contradiction.
        exact hdisj u h_main.head_mem_cover ((h_detour.cover_iff u).mp huQ)
      · -- u ∈ w :: tail: contradicts nodup of (u :: w :: tail).
        have hnd := h_main.nodup
        rw [List.nodup_cons] at hnd
        exact hnd.1 huwt
    · rw [List.nodup_append]
      refine ⟨h_detour.nodup, ?_, ?_⟩
      · have hnd := h_main.nodup
        rw [List.nodup_cons] at hnd
        exact hnd.2
      · -- disjoint Q (detour, covD) and w :: tail (main, covM)
        intro x hxQ z hzwt hxz
        subst hxz
        have hxD : covD x := (h_detour.cover_iff x).mp hxQ
        have hxM : covM x :=
          (h_main.cover_iff x).mp (by simp [hzwt])
        exact hdisj x hxM hxD
  · rw [show u :: Q ++ (w :: tail) = u :: (Q ++ (w :: tail)) from rfl,
      List.isChain_cons]
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [List.head?_append, h_detour.head_eq] at hy
      simp only [Option.some_or, Option.mem_some_iff] at hy
      subst hy
      exact h_cross_uu'
    · rw [List.isChain_append]
      refine ⟨h_detour.chain, ?_, ?_⟩
      · have hch := h_main.chain
        rw [List.isChain_cons] at hch
        exact hch.2
      · intro x hx y hy
        rw [h_detour.last_eq] at hx
        rw [show (w :: tail).head? = some w from rfl] at hy
        simp only [Option.mem_some_iff] at hx hy
        subst hx; subst hy
        exact h_cross_w'w
  · intro S
    rw [show u :: Q ++ (w :: tail) = u :: (Q ++ (w :: tail)) from rfl,
      List.mem_cons, List.mem_append, h_detour.cover_iff]
    constructor
    · rintro (rfl | hQ | hwt')
      · exact Or.inl h_main.head_mem_cover
      · exact Or.inr hQ
      · exact Or.inl ((h_main.cover_iff S).mp (by simp [hwt']))
    · rintro (hM | hD)
      · have hSmem : S ∈ (u :: w :: tail) := (h_main.cover_iff S).mpr hM
        rw [List.mem_cons] at hSmem
        rcases hSmem with hSu | hSwt
        · exact Or.inl hSu
        · exact Or.inr (Or.inr hSwt)
      · exact Or.inr (Or.inl hD)

/-! ## §B.3' — extract cons-cons form from a `CubeListOn` with distinct
endpoints (for the same-half splice) -/

/-- **`CubeListOn.cons_cons_form`** — a `CubeListOn` with distinct
endpoints `u ≠ v` is of the form `u :: w :: tail` for some second vertex
`w` and tail (`\label{thm:CubeListOn_cons_cons_form}`, B.3').  Used to
extract the splice argument's second element. -/
theorem CubeListOn.cons_cons_form {cov : Finset ι → Prop} {u v : Finset ι}
    {L : List (Finset ι)} (h : CubeListOn cov u v L) (hne : u ≠ v) :
    ∃ w tail, L = u :: w :: tail ∧ CubeListOn cov u v (u :: w :: tail) := by
  rcases L with _ | ⟨x, _ | ⟨w, tail⟩⟩
  · exact absurd h.head_eq (by simp)
  · exfalso
    have hx_eq_u : x = u := by have := h.head_eq; simp at this; exact this
    have hx_eq_v : x = v := by have := h.last_eq; simp at this; exact this
    exact hne (hx_eq_u ▸ hx_eq_v)
  · have hx_eq_u : x = u := by have := h.head_eq; simp at this; exact this
    refine ⟨w, tail, by rw [hx_eq_u], ?_⟩
    rw [hx_eq_u] at h; exact h

/-! ## §B.4 — auxiliary: opposite-parity subset exists when ground nonempty -/

/-- **`exists_opposite_parity_subset`** — for any nonempty `ground` and
target parity `p ∈ {0, 1}`, there is a subset of `ground` with that
parity (`\label{thm:exists_opposite_parity_subset}`, B.4 helper).

If `p = 0`, take `∅`.  If `p = 1`, take `{b}` for some `b ∈ ground`. -/
theorem exists_opposite_parity_subset {ground : Finset ι} (hne : ground.Nonempty)
    (p : ℕ) (hp : p < 2) :
    ∃ S, S ⊆ ground ∧ cubeParity S = p := by
  have : p = 0 ∨ p = 1 := by omega
  rcases this with hp0 | hp1
  · subst hp0
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    simp [cubeParity]
  · subst hp1
    obtain ⟨b, hb⟩ := hne
    refine ⟨{b}, ?_, ?_⟩
    · intro x hx; rw [Finset.mem_singleton] at hx; rwa [hx]
    · simp [cubeParity]

/-! ## §B.5 — the core induction (full cube laceability on a ground set) -/

/-- **`cube_lace_aux`** — **THE B.5 CORE INDUCTION**: for every finite
`ground : Finset ι` and every pair `u, v ⊆ ground` of opposite parity,
there is a `\ref{def:CubeListOn}`-style Hamilton list covering all
subsets of `ground`, from `u` to `v`
(`\label{thm:cube_lace_aux}`, B.5).

Proof: `Finset.induction_on ground`.

* **Base `∅`**: vacuous — only subset is `∅`, parity equal.
* **Step `insert a ground'`** (`a ∉ ground'`, IH for `ground'`): split
  on `(a ∈ u, a ∈ v)` into four subcases.  All four reduce to either an
  `append`-at-cross-edge construction (when `a` membership differs:
  cross-half) or a `splice` construction (when `a` membership matches:
  same-half, in two mirror forms).  Each subcase calls the IH at most
  twice on `ground'`.

Kernel-pure (`[propext, Classical.choice, Quot.sound]`). -/
theorem cube_lace_aux (ground : Finset ι) :
    ∀ {u v : Finset ι}, u ⊆ ground → v ⊆ ground →
      cubeParity u ≠ cubeParity v →
      ∃ L, CubeListOn (· ⊆ ground) u v L := by
  induction ground using Finset.induction_on with
  | empty =>
    intro u v hu hv hpar
    -- u ⊆ ∅ ⟹ u = ∅; same for v; parity equal; contradicts hpar.
    have hu0 : u = ∅ := Finset.subset_empty.mp hu
    have hv0 : v = ∅ := Finset.subset_empty.mp hv
    subst hu0; subst hv0
    exact absurd rfl hpar
  | insert a ground' ha_notin ih =>
    intro u v hu hv hpar
    -- Helpers
    have ha_subset_iff : ∀ {S : Finset ι}, S ⊆ insert a ground' ↔
        (a ∈ S → S.erase a ⊆ ground') ∧ (a ∉ S → S ⊆ ground') := by
      intro S
      constructor
      · intro hS
        refine ⟨?_, ?_⟩
        · intro haS x hx
          rw [Finset.mem_erase] at hx
          have hxS : x ∈ insert a ground' := hS hx.2
          rw [Finset.mem_insert] at hxS
          rcases hxS with hxa | hxg
          · exact absurd hxa hx.1
          · exact hxg
        · intro haS' x hx
          have hxS : x ∈ insert a ground' := hS hx
          rw [Finset.mem_insert] at hxS
          rcases hxS with hxa | hxg
          · exact absurd (hxa ▸ hx) haS'
          · exact hxg
      · rintro ⟨h1, h2⟩
        by_cases haS : a ∈ S
        · intro x hx
          by_cases hxa : x = a
          · rw [hxa]; exact Finset.mem_insert_self a ground'
          · have : x ∈ S.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
            exact Finset.mem_insert_of_mem (h1 haS this)
        · intro x hx; exact Finset.mem_insert_of_mem (h2 haS hx)
    -- "lower" = subsets of ground' (not containing a, equiv. ⊆ ground').
    -- "upper" = subsets of insert a ground' containing a, ⟺ insert a (T : T ⊆ ground').
    -- Below, we case-split on a ∈ u, a ∈ v.
    by_cases hau : a ∈ u
    · by_cases hav : a ∈ v
      · -- (2) both upper: u = insert a u', v = insert a v'.
        set u' := u.erase a with hu'_def
        set v' := v.erase a with hv'_def
        have hu'sub : u' ⊆ ground' := by
          intro x hx; rw [hu'_def] at hx
          rw [Finset.mem_erase] at hx
          have := hu hx.2
          rw [Finset.mem_insert] at this
          exact this.resolve_left hx.1
        have hv'sub : v' ⊆ ground' := by
          intro x hx; rw [hv'_def] at hx
          rw [Finset.mem_erase] at hx
          have := hv hx.2
          rw [Finset.mem_insert] at this
          exact this.resolve_left hx.1
        have hu_eq : u = insert a u' := (Finset.insert_erase hau).symm
        have hv_eq : v = insert a v' := (Finset.insert_erase hav).symm
        have hu'_card : u.card = u'.card + 1 := by
          rw [hu_eq]; exact Finset.card_insert_of_notMem (by simp [hu'_def])
        have hv'_card : v.card = v'.card + 1 := by
          rw [hv_eq]; exact Finset.card_insert_of_notMem (by simp [hv'_def])
        have hpar' : cubeParity u' ≠ cubeParity v' := by
          unfold cubeParity at *; omega
        -- IH for (u', v') on ground': get lower path P'.
        obtain ⟨P', hP'⟩ := ih hu'sub hv'sub hpar'
        -- P' has length ≥ 2 since u' ≠ v' (opposite parity).
        have hu'ne_v' : u' ≠ v' := by
          intro h_eq; rw [h_eq] at hpar'; exact hpar' rfl
        -- mapInsert P' to upper.
        have ha_low : ∀ S, (S ⊆ ground') → a ∉ S := fun S hS haS =>
          ha_notin (hS haS)
        -- Extract w' = second of P', tail' = tail.
        obtain ⟨w', tail', hP'_eq, hP'_ccf⟩ := hP'.cons_cons_form hu'ne_v'
        -- IH for (u', w') on ground'.
        have hw'sub : w' ⊆ ground' := by
          apply (hP'_ccf.cover_iff w').mp; simp
        have hu'_w'_par : cubeParity u' ≠ cubeParity w' := by
          have hch := hP'_ccf.chain
          rw [List.isChain_cons] at hch
          exact flipAdj_parity_ne (hch.1 w' (by simp))
        obtain ⟨Q, hQ⟩ := ih hu'sub hw'sub hu'_w'_par
        -- mapInsert P'_ccf to upper main path.
        have ha_low : ∀ S, (S ⊆ ground') → a ∉ S := fun S hS haS =>
          ha_notin (hS haS)
        have hP_up := hP'_ccf.mapInsert ha_low
        -- (insert a u') :: (insert a w') :: tail'.map (insert a) = u :: (insert a w') :: ...
        have hu_param : (insert a u') = u := hu_eq.symm
        rw [show ((u' :: w' :: tail').map (insert a)) =
              insert a u' :: insert a w' :: tail'.map (insert a) from rfl, hu_param] at hP_up
        -- Now hP_up : CubeListOn (...) u v (u :: insert a w' :: tail'.map (insert a)),
        -- after also rewriting (insert a v') to v in the endpoint:
        rw [show insert a v' = v from hv_eq.symm] at hP_up
        -- Cross edges.
        have hau' : a ∉ u' := by simp [hu'_def]
        have haw' : a ∉ w' := ha_low w' hw'sub
        have h_cross_uu' : flipAdj u u' := by
          rw [hu_eq]; exact flipAdj_symm (flipAdj_insert hau')
        have h_cross_w'w : flipAdj w' (insert a w') := flipAdj_insert haw'
        have h_spliced := CubeListOn.splice hP_up hQ h_cross_uu' h_cross_w'w
          (fun S hM hD => (ha_low S hD) hM.1)
        refine ⟨u :: Q ++ (insert a w' :: tail'.map (insert a)), ?_⟩
        refine ⟨h_spliced.head_eq, h_spliced.last_eq, h_spliced.nodup,
          h_spliced.chain, ?_⟩
        intro S
        rw [h_spliced.cover_iff]
        constructor
        · rintro (⟨haS, hSe⟩ | hS)
          · intro x hx
            by_cases hxa : x = a
            · rw [hxa]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (hSe (Finset.mem_erase.mpr ⟨hxa, hx⟩))
          · intro x hx; exact Finset.mem_insert_of_mem (hS hx)
        · intro hS
          by_cases haS : a ∈ S
          · left
            refine ⟨haS, ?_⟩
            intro x hx
            rw [Finset.mem_erase] at hx
            have := hS hx.2
            rw [Finset.mem_insert] at this
            exact this.resolve_left hx.1
          · right
            intro x hx
            have := hS hx
            rw [Finset.mem_insert] at this
            exact this.resolve_left (fun heq => haS (heq ▸ hx))
      · -- (3) a ∈ u, a ∉ v: cross-half upper-to-lower.
        -- u = insert a u', u' ⊆ ground'. v ⊆ ground'.
        set u' := u.erase a with hu'_def
        have hu'sub : u' ⊆ ground' := by
          intro x hx; rw [hu'_def] at hx
          rw [Finset.mem_erase] at hx
          have := hu hx.2
          rw [Finset.mem_insert] at this
          exact this.resolve_left hx.1
        have hu_eq : u = insert a u' := (Finset.insert_erase hau).symm
        have hvsub : v ⊆ ground' := by
          intro x hx
          have := hv hx
          rw [Finset.mem_insert] at this
          exact this.resolve_left (fun heq => hav (heq ▸ hx))
        have hu'_card : u.card = u'.card + 1 := by
          rw [hu_eq]; exact Finset.card_insert_of_notMem (by simp [hu'_def])
        have hpar' : cubeParity u' = cubeParity v := by
          unfold cubeParity at *; omega
        -- Need ground' nonempty to pick w of opposite parity OR handle special case.
        by_cases hground' : ground'.Nonempty
        · -- Pick w ⊆ ground' with cubeParity w ≠ cubeParity v.
          have hpw_lt : (1 - cubeParity v) < 2 := by
            unfold cubeParity
            have : v.card % 2 < 2 := Nat.mod_lt _ (by decide)
            omega
          obtain ⟨w, hwsub, hw_par⟩ :=
            exists_opposite_parity_subset hground' (1 - cubeParity v) hpw_lt
          have hw_par_ne_v : cubeParity w ≠ cubeParity v := by
            unfold cubeParity at *
            have : v.card % 2 < 2 := Nat.mod_lt _ (by decide)
            omega
          have hw_par_ne_u' : cubeParity w ≠ cubeParity u' := by
            rw [hpar']; exact hw_par_ne_v
          -- IH: lower path from v to w (covers ground').
          obtain ⟨L_low, hL_low⟩ := ih hvsub hwsub hw_par_ne_v.symm
          -- IH: lower path from u' to w (covers ground').
          obtain ⟨L'_uw, hL'_uw⟩ := ih hu'sub hwsub hw_par_ne_u'.symm
          -- mapInsert L'_uw to upper: L_up : u → insert a w.
          have ha_low : ∀ S, (S ⊆ ground') → a ∉ S := fun S hS haS =>
            ha_notin (hS haS)
          have hL_up := hL'_uw.mapInsert ha_low
          have hu_param : (insert a u') = u := hu_eq.symm
          -- Reformulate hL_up endpoints.
          have hL_up' : CubeListOn (fun S => a ∈ S ∧ S.erase a ⊆ ground')
              u (insert a w) (L'_uw.map (insert a)) := by
            rw [← hu_param]; exact hL_up
          -- L_low.reverse : w → v
          have hL_low_rev := hL_low.reverse
          -- Cross edge: insert a w → w
          have haw : a ∉ w := ha_low w hwsub
          have h_cross : flipAdj (insert a w) w := flipAdj_symm (flipAdj_insert haw)
          -- Append: (L'_uw.map (insert a)) ++ L_low.reverse : u → v
          have h_appended := hL_up'.append hL_low_rev h_cross
            (fun S hM hD => (ha_low S hD) hM.1)
          refine ⟨L'_uw.map (insert a) ++ L_low.reverse, ?_⟩
          refine ⟨h_appended.head_eq, h_appended.last_eq, h_appended.nodup,
            h_appended.chain, ?_⟩
          intro S
          rw [h_appended.cover_iff]
          constructor
          · rintro (⟨haS, hSe⟩ | hS)
            · intro x hx
              by_cases hxa : x = a
              · rw [hxa]; exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (hSe (Finset.mem_erase.mpr ⟨hxa, hx⟩))
            · intro x hx; exact Finset.mem_insert_of_mem (hS hx)
          · intro hS
            by_cases haS : a ∈ S
            · left
              refine ⟨haS, ?_⟩
              intro x hx
              rw [Finset.mem_erase] at hx
              have := hS hx.2
              rw [Finset.mem_insert] at this
              exact this.resolve_left hx.1
            · right
              intro x hx
              have := hS hx
              rw [Finset.mem_insert] at this
              exact this.resolve_left (fun heq => haS (heq ▸ hx))
        · -- ground' empty: ground = {a}. u' ⊆ ∅, v ⊆ ∅.
          rw [Finset.not_nonempty_iff_eq_empty] at hground'
          subst hground'
          have hu'0 : u' = ∅ := Finset.subset_empty.mp hu'sub
          have hv0 : v = ∅ := Finset.subset_empty.mp hvsub
          subst hv0
          have hu_eq2 : u = {a} := by
            rw [hu_eq, hu'0]
            rfl
          subst hu_eq2
          -- L = [{a}, ∅]
          refine ⟨[{a}, ∅], ?_⟩
          refine ⟨rfl, rfl, ?_, ?_, ?_⟩
          · rw [List.nodup_cons, List.mem_singleton]
            refine ⟨?_, List.nodup_singleton _⟩
            intro h
            exact Finset.singleton_ne_empty a (by simpa using h)

          · -- IsChain on [{a}, ∅]: just flipAdj {a} ∅
            rw [List.isChain_cons]
            refine ⟨?_, by simp⟩
            intro y hy
            simp only [List.head?_cons, Option.mem_some_iff] at hy
            subst hy
            -- flipAdj {a} ∅: {a} = insert a ∅, use symm of flipAdj_insert
            have : ({a} : Finset ι) = insert a ∅ := rfl
            rw [this]
            exact flipAdj_symm (flipAdj_insert (Finset.notMem_empty a))
          · -- cover_iff: S ∈ [{a}, ∅] ↔ S ⊆ {a}
            intro S
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (rfl | rfl)
              · exact subset_refl _
              · exact Finset.empty_subset _
            · intro hS
              -- S ⊆ {a} ⟹ S = ∅ or S = {a}
              rcases Finset.subset_singleton_iff.mp hS with h | h
              · right; exact h
              · left; exact h
    · by_cases hav : a ∈ v
      · -- (4) a ∉ u, a ∈ v: cross-half, mirror of (3).
        -- Reduce by swapping u, v: invoke (3) with roles swapped (call with v, u),
        -- then reverse the resulting list.
        -- Rebuild the cross-half argument with u ↔ v.
        set v' := v.erase a with hv'_def
        have hv'sub : v' ⊆ ground' := by
          intro x hx; rw [hv'_def] at hx
          rw [Finset.mem_erase] at hx
          have := hv hx.2
          rw [Finset.mem_insert] at this
          exact this.resolve_left hx.1
        have hv_eq : v = insert a v' := (Finset.insert_erase hav).symm
        have husub : u ⊆ ground' := by
          intro x hx
          have := hu hx
          rw [Finset.mem_insert] at this
          exact this.resolve_left (fun heq => hau (heq ▸ hx))
        have hv'_card : v.card = v'.card + 1 := by
          rw [hv_eq]; exact Finset.card_insert_of_notMem (by simp [hv'_def])
        have hpar' : cubeParity v' = cubeParity u := by
          unfold cubeParity at *; omega
        by_cases hground' : ground'.Nonempty
        · have hpw_lt : (1 - cubeParity u) < 2 := by
            unfold cubeParity
            have : u.card % 2 < 2 := Nat.mod_lt _ (by decide)
            omega
          obtain ⟨w, hwsub, hw_par⟩ :=
            exists_opposite_parity_subset hground' (1 - cubeParity u) hpw_lt
          have hw_par_ne_u : cubeParity w ≠ cubeParity u := by
            unfold cubeParity at *
            have : u.card % 2 < 2 := Nat.mod_lt _ (by decide)
            omega
          have hw_par_ne_v' : cubeParity w ≠ cubeParity v' := by
            rw [hpar']; exact hw_par_ne_u
          obtain ⟨L_low, hL_low⟩ := ih husub hwsub hw_par_ne_u.symm
          obtain ⟨L'_vw, hL'_vw⟩ := ih hv'sub hwsub hw_par_ne_v'.symm
          have ha_low : ∀ S, (S ⊆ ground') → a ∉ S := fun S hS haS =>
            ha_notin (hS haS)
          have hL_up := hL'_vw.mapInsert ha_low
          have hv_param : (insert a v') = v := hv_eq.symm
          have hL_up' : CubeListOn (fun S => a ∈ S ∧ S.erase a ⊆ ground')
              v (insert a w) (L'_vw.map (insert a)) := by
            rw [← hv_param]; exact hL_up
          have hL_low_rev := hL_low.reverse
          have haw : a ∉ w := ha_low w hwsub
          have h_cross : flipAdj (insert a w) w := flipAdj_symm (flipAdj_insert haw)
          -- This gives a path v → u, we'll reverse for u → v.
          have h_appended := hL_up'.append hL_low_rev h_cross
            (fun S hM hD => (ha_low S hD) hM.1)
          -- Reverse to get u → v.
          have h_reversed := h_appended.reverse
          refine ⟨(L'_vw.map (insert a) ++ L_low.reverse).reverse, ?_⟩
          refine ⟨h_reversed.head_eq, h_reversed.last_eq, h_reversed.nodup,
            h_reversed.chain, ?_⟩
          intro S
          rw [h_reversed.cover_iff]
          constructor
          · rintro (⟨haS, hSe⟩ | hS)
            · intro x hx
              by_cases hxa : x = a
              · rw [hxa]; exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (hSe (Finset.mem_erase.mpr ⟨hxa, hx⟩))
            · intro x hx; exact Finset.mem_insert_of_mem (hS hx)
          · intro hS
            by_cases haS : a ∈ S
            · left
              refine ⟨haS, ?_⟩
              intro x hx
              rw [Finset.mem_erase] at hx
              have := hS hx.2
              rw [Finset.mem_insert] at this
              exact this.resolve_left hx.1
            · right
              intro x hx
              have := hS hx
              rw [Finset.mem_insert] at this
              exact this.resolve_left (fun heq => haS (heq ▸ hx))
        · -- ground' empty: ground = {a}. u ⊆ ∅, v' ⊆ ∅.
          rw [Finset.not_nonempty_iff_eq_empty] at hground'
          subst hground'
          have hu0 : u = ∅ := Finset.subset_empty.mp husub
          have hv'0 : v' = ∅ := Finset.subset_empty.mp hv'sub
          subst hu0
          have hv_eq2 : v = {a} := by
            rw [hv_eq, hv'0]
            rfl
          subst hv_eq2
          -- L = [∅, {a}]
          refine ⟨[∅, {a}], ?_⟩
          refine ⟨rfl, rfl, ?_, ?_, ?_⟩
          · rw [List.nodup_cons, List.mem_singleton]
            refine ⟨?_, List.nodup_singleton _⟩
            intro h
            exact Finset.singleton_ne_empty a (by simpa using h)

          · rw [List.isChain_cons]
            refine ⟨?_, by simp⟩
            intro y hy
            simp only [List.head?_cons, Option.mem_some_iff] at hy
            subst hy
            -- flipAdj ∅ {a}: {a} = insert a ∅
            have : ({a} : Finset ι) = insert a ∅ := rfl
            rw [this]
            exact flipAdj_insert (Finset.notMem_empty a)
          · intro S
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (rfl | rfl)
              · exact Finset.empty_subset _
              · exact subset_refl _
            · intro hS
              rcases Finset.subset_singleton_iff.mp hS with h | h
              · left; exact h
              · right; exact h
      · -- (1) both lower: a ∉ u, a ∉ v. u, v ⊆ ground'.
        have hu_sub : u ⊆ ground' := by
          intro x hx
          have := hu hx
          rw [Finset.mem_insert] at this
          exact this.resolve_left (fun heq => hau (heq ▸ hx))
        have hv_sub : v ⊆ ground' := by
          intro x hx
          have := hv hx
          rw [Finset.mem_insert] at this
          exact this.resolve_left (fun heq => hav (heq ▸ hx))
        have hu_ne_v : u ≠ v := by
          intro h_eq; rw [h_eq] at hpar; exact hpar rfl
        -- IH lower path u → v.
        obtain ⟨P, hP⟩ := ih hu_sub hv_sub hpar
        -- Extract w = second, tail = remainder.
        obtain ⟨w, tail, _, hP_ccf⟩ := hP.cons_cons_form hu_ne_v
        have hwsub : w ⊆ ground' := by
          apply (hP_ccf.cover_iff w).mp; simp
        have hu_w_par : cubeParity u ≠ cubeParity w := by
          have hch := hP_ccf.chain
          rw [List.isChain_cons] at hch
          exact flipAdj_parity_ne (hch.1 w (by simp))
        -- IH for (u, w) on ground'.
        obtain ⟨Q, hQ⟩ := ih hu_sub hwsub hu_w_par
        have ha_low : ∀ S, (S ⊆ ground') → a ∉ S := fun S hS haS =>
          ha_notin (hS haS)
        have hau_notin : a ∉ u := ha_low u hu_sub
        have haw_notin : a ∉ w := ha_low w hwsub
        have hQ_up := hQ.mapInsert ha_low
        have h_cross_uu' : flipAdj u (insert a u) := flipAdj_insert hau_notin
        have h_cross_w'w : flipAdj (insert a w) w :=
          flipAdj_symm (flipAdj_insert haw_notin)
        have h_spliced := CubeListOn.splice hP_ccf hQ_up h_cross_uu' h_cross_w'w
          (fun S hM hD => (ha_low S hM) hD.1)
        refine ⟨u :: (Q.map (insert a)) ++ (w :: tail), ?_⟩
        refine ⟨h_spliced.head_eq, h_spliced.last_eq, h_spliced.nodup,
          h_spliced.chain, ?_⟩
        intro S
        rw [h_spliced.cover_iff]
        constructor
        · rintro (hS | ⟨haS, hSe⟩)
          · intro x hx; exact Finset.mem_insert_of_mem (hS hx)
          · intro x hx
            by_cases hxa : x = a
            · rw [hxa]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (hSe (Finset.mem_erase.mpr ⟨hxa, hx⟩))
        · intro hS
          by_cases haS : a ∈ S
          · right
            refine ⟨haS, ?_⟩
            intro x hx
            rw [Finset.mem_erase] at hx
            have := hS hx.2
            rw [Finset.mem_insert] at this
            exact this.resolve_left hx.1
          · left
            intro x hx
            have := hS hx
            rw [Finset.mem_insert] at this
            exact this.resolve_left (fun heq => haS (heq ▸ hx))

/-! ## §B.2 — the headline hypercube laceability theorem -/

/-- **`HypercubeHamiltonLaceable_opposite_parity`** — **THE B.2 HEADLINE**:
the hypercube `\ref{def:Qgraph}` over `Finset ι` (for a `Fintype ι`) is
**Hamilton-laceable** between any two opposite-parity subsets — for `u, v`
with `\ref{def:cubeParity} u ≠ \ref{def:cubeParity} v`, there is a
Hamilton path in `\ref{def:Qgraph}` from `u` to `v` visiting every
subset exactly once
(`\label{thm:HypercubeHamiltonLaceable_opposite_parity}`, B.2).

The proof packages the list-level Hamilton path from
`\ref{thm:cube_lace_aux}` (over `ground = univ`) into a Mathlib
`SimpleGraph.HamiltonianPathBetween` via the `\ref{def:walkOfChain}`
bridge (`\ref{thm:hamiltonianPathBetween_of_chain_list}`).

Kernel-pure (`[propext, Classical.choice, Quot.sound]`). -/
theorem HypercubeHamiltonLaceable_opposite_parity {ι : Type u_ι}
    [DecidableEq ι] [Fintype ι] {u v : Finset ι}
    (hpar : cubeParity u ≠ cubeParity v) :
    (Qgraph ι).HamiltonianPathBetween u v := by
  -- Apply core induction with ground = univ.
  obtain ⟨L, hL⟩ := cube_lace_aux (Finset.univ : Finset ι)
    (Finset.subset_univ u) (Finset.subset_univ v) hpar
  -- Bridge to graph via chain-list bridge.
  have hL_ne := hL.ne_nil
  have hchain : List.IsChain (Qgraph ι).Adj L := hL.chain
  have hnd : L.Nodup := hL.nodup
  have hcov : ∀ x : Finset ι, x ∈ L :=
    fun x => (hL.cover_iff x).mpr (Finset.subset_univ x)
  have hu : L.head hL_ne = u := by
    have := hL.head_eq
    rw [List.head?_eq_some_head hL_ne, Option.some_inj] at this
    exact this
  have hv : L.getLast hL_ne = v := by
    have := hL.last_eq
    rw [List.getLast?_eq_some_getLast hL_ne, Option.some_inj] at this
    exact this
  exact hamiltonianPathBetween_of_chain_list L hL_ne hchain hnd hcov hu hv

/-! ## §B.3 — small base case instances (m = 1, 2 immediate corollaries) -/

/-- The 2-vertex cube `Q_1` (= `Qgraph (Fin 1)`) is Hamilton-laceable
between `∅` and `{0}` (`\label{thm:Q1_laceable}`, B.3).  Immediate
corollary of B.2. -/
theorem Q1_laceable :
    (Qgraph (Fin 1)).HamiltonianPathBetween (∅ : Finset (Fin 1))
      ({0} : Finset (Fin 1)) := by
  apply HypercubeHamiltonLaceable_opposite_parity
  simp [cubeParity]

/-! ## §B.5 — export shape for downstream cube-laceability transport
(`Qgraph ι` with `ι = Fin m`) -/

/-- **`Qm_laceable_export`** — the finite-dimensional export used by the
Petersen block construction: for the `m`-dimensional hypercube
`Q_m = Qgraph (Fin m)`,
between every pair of opposite-parity vertices there is a Hamilton path
(`\label{thm:Qm_laceable_export}`, B.5).

This is the opposite-parity Hamilton-laceability of `Q_m` for general `m`. -/
theorem Qm_laceable_export (m : ℕ) {u v : Finset (Fin m)}
    (hpar : cubeParity u ≠ cubeParity v) :
    (Qgraph (Fin m)).HamiltonianPathBetween u v :=
  HypercubeHamiltonLaceable_opposite_parity hpar


end Cube

end Hamilton.Infrastructure
