/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Topology.Compactness.Compact

/-!
# One parameter for a whole compact set

A condition that holds near every point of a compact set, each time for *some* parameter, holds
on the whole set for a **single** parameter — provided the family of conditions is directed: any
two admissible parameters are dominated by a third, admissible, one that works wherever either
of them does.

This is the "finite cover, then take the maximum of finitely many constants" step, stated once.
The two halves are independent and both are needed: compactness turns the local hypothesis into
finitely many parameters, and directedness collapses those finitely many into one.

Admissibility is carried by a set `s : Set ι` rather than by a monotone order on `ι`, because the
constants that occur in practice are *not* upward closed.  A geometric bound `C q ^ m` weakens as
`C` and `q` grow, so the pair `(C, q)` may be replaced by any larger pair — but only while `q`
stays below `1`, and `q < 1` is exactly the clause an order-theoretic `SemilatticeSup` hypothesis
would lose.  Directedness on a set keeps it.

## Main results

* `Shields.exists_mem_forall_imp_of_directedOn` — finitely many admissible parameters are
  dominated by one.
* `Shields.exists_forall_of_isCompact_of_directedOn` — local satisfiability on a compact set,
  plus directedness, gives one parameter for the whole set.

## Implementation notes

The local hypothesis is stated against `𝓝[K] x` rather than `𝓝 x`, which is the weaker of the
two and the one a relative statement supplies.  It costs nothing: `mem_nhdsWithin` trades it for
an ambient open set intersected with `K`, and `IsCompact.elim_nhds_subcover` runs on that.

## Tags

compact, directed, uniform, cover
-/

open Set Topology

namespace Shields

variable {X ι : Type*}

/-- **Finitely many admissible parameters are dominated by one.**  With `s` nonempty this holds
for the empty `Finset` as well, which is where the nonemptiness is spent. -/
theorem exists_mem_forall_imp_of_directedOn {α : Type*} {p : ι → α → Prop} {s : Set ι}
    (hs : s.Nonempty) (hdir : ∀ c ∈ s, ∀ d ∈ s, ∃ e ∈ s, ∀ x, p c x ∨ p d x → p e x)
    {β : Type*} (t : Finset β) (c : β → ι) (hc : ∀ b ∈ t, c b ∈ s) :
    ∃ e ∈ s, ∀ b ∈ t, ∀ x, p (c b) x → p e x := by
  classical
  induction t using Finset.induction with
  | empty =>
      obtain ⟨e, he⟩ := hs
      exact ⟨e, he, by simp⟩
  | insert b t hb ih =>
      obtain ⟨e, hes, he⟩ := ih fun b' hb' => hc b' (Finset.mem_insert_of_mem hb')
      obtain ⟨e', hes', he'⟩ := hdir (c b) (hc b (Finset.mem_insert_self b t)) e hes
      refine ⟨e', hes', fun b' hb' x hx => ?_⟩
      rcases Finset.mem_insert.mp hb' with rfl | hb'
      · exact he' x (Or.inl hx)
      · exact he' x (Or.inr (he b' hb' x hx))

/-- **One parameter for a whole compact set.**  If every point of `K` has a relative
neighborhood on which some admissible parameter works, and admissible parameters are directed,
then one of them works on all of `K`. -/
theorem exists_forall_of_isCompact_of_directedOn [TopologicalSpace X] {K : Set X}
    {p : ι → X → Prop} {s : Set ι} (hs : s.Nonempty) (hK : IsCompact K)
    (hdir : ∀ c ∈ s, ∀ d ∈ s, ∃ e ∈ s, ∀ x, p c x ∨ p d x → p e x)
    (hloc : ∀ x ∈ K, ∃ U ∈ 𝓝[K] x, ∃ c ∈ s, ∀ y ∈ U, p c y) :
    ∃ c ∈ s, ∀ y ∈ K, p c y := by
  -- `choose!` needs a default value to make the chosen parameter total, and `s` supplies one.
  haveI : Nonempty ι := ⟨hs.choose⟩
  choose! U hU c hcs hc using hloc
  have hVex : ∀ x ∈ K, ∃ V, IsOpen V ∧ x ∈ V ∧ V ∩ K ⊆ U x :=
    fun x hx => mem_nhdsWithin.mp (hU x hx)
  choose! V hVo hxV hVK using hVex
  obtain ⟨t, hts, hsub⟩ :=
    hK.elim_nhds_subcover V fun x hx => (hVo x hx).mem_nhds (hxV x hx)
  obtain ⟨e, hes, he⟩ :=
    exists_mem_forall_imp_of_directedOn hs hdir t c fun b hb => hcs b (hts b hb)
  refine ⟨e, hes, fun y hy => ?_⟩
  obtain ⟨x, hxt, hyV⟩ := Set.mem_iUnion₂.mp (hsub hy)
  exact he x hxt y (hc x (hts x hxt) y (hVK x (hts x hxt) ⟨hyV, hy⟩))

/-! ### Axiom footprint -/

/-- info: 'Shields.exists_mem_forall_imp_of_directedOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_mem_forall_imp_of_directedOn

/-- info: 'Shields.exists_forall_of_isCompact_of_directedOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_forall_of_isCompact_of_directedOn

end Shields
