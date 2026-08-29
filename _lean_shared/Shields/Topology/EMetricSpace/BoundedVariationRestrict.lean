/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Reading the total variation off subintervals

`eVariationOn f s` is a supremum over finite monotone tuples in `s`, and every such tuple
lies in the closed interval its own endpoints span.  Four consequences, none of them in
Mathlib:

* a bound on every compact subinterval of an order-connected set is a bound on the set --
  nothing has to be attained at an open end;
* a bound on the closed intervals reaching into a half-open one bounds the half-open one;
* and disjoint pieces, ordered by their index, have variations summing below the whole,
  which `eVariationOn.union` does not give because it needs the pieces to meet.

The gaps between the pieces are exactly what deleting a finite set of parameters creates,
which is where the last statement is used.

## Main results

* `Shields.eVariationOn_le_of_forall_Icc` -- a variation bound on every `Icc u v ⊆ s`, for
  `s` order-connected, is a variation bound on `s`.
* `Shields.eVariationOn_sum_le` -- ordered disjoint pieces sum below the whole.
* `Shields.eVariationOn_Ico_le`, `Shields.eVariationOn_Ioc_le` -- a half-open interval is
  controlled by the closed intervals inside it.

Used by `forgacs-tran-numerators`.

## Tags

bounded variation, total variation, order connected, half-open interval
-/

open Set
open scoped ENNReal

namespace Shields

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/-- **A variation bound on every compact subinterval is a variation bound on the set.**
`eVariationOn` is a supremum over finite monotone tuples, and a finite tuple lies in the
compact interval spanned by its own endpoints -- so nothing is lost at the open ends, and
the constant does not have to be attained there. -/
theorem eVariationOn_le_of_forall_Icc {f : α → E} {s : Set α} {K : ℝ≥0∞}
    (hs : s.OrdConnected)
    (h : ∀ u ∈ s, ∀ v ∈ s, u ≤ v → eVariationOn f (Icc u v) ≤ K) :
    eVariationOn f s ≤ K := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  refine iSup_le fun p => iSup_le fun hp => ?_
  have heq : s ∩ Icc p.1 p.2 = Icc p.1 p.2 :=
    inter_eq_right.2 (hs.out hp.1 hp.2.1)
  rw [heq]
  exact h p.1 hp.1 p.2 hp.2.1 hp.2.2

/-- **Ordered disjoint pieces sum below the whole.**  If the sets `J i`, `i ∈ t`, sit inside
`s` and are ordered by their index, their variations add up to at most the variation over `s`.
`eVariationOn.union` needs the pieces to meet; here they need not, and the gaps between them
are unconstrained. -/
theorem eVariationOn_sum_le {f : α → E} {J : ℕ → Set α} (t : Finset ℕ) :
    ∀ s : Set α, (∀ i ∈ t, J i ⊆ s) →
      (∀ i ∈ t, ∀ j ∈ t, i < j → ∀ x ∈ J i, ∀ y ∈ J j, x ≤ y) →
      ∑ i ∈ t, eVariationOn f (J i) ≤ eVariationOn f s := by
  classical
  induction t using Finset.induction_on_max with
  | empty => intro s _ _; simp
  | insert n t hmax ih =>
      intro s hJs hord
      have hnt : n ∉ t := fun h => lt_irrefl n (hmax n h)
      set T : Set α := {x | ∃ i ∈ t, x ∈ J i} with hT
      have hTs : T ⊆ s := by
        rintro x ⟨i, hi, hx⟩
        exact hJs i (Finset.mem_insert_of_mem hi) hx
      have hsum : ∑ i ∈ t, eVariationOn f (J i) ≤ eVariationOn f T :=
        ih T (fun i hi => fun x hx => ⟨i, hi, hx⟩)
          (fun i hi j hj hij => hord i (Finset.mem_insert_of_mem hi) j
            (Finset.mem_insert_of_mem hj) hij)
      have hcross : ∀ x ∈ T, ∀ y ∈ J n, x ≤ y := by
        rintro x ⟨i, hi, hx⟩ y hy
        exact hord i (Finset.mem_insert_of_mem hi) n (Finset.mem_insert_self n t)
          (hmax i hi) x hx y hy
      have hunion : T ∪ J n ⊆ s :=
        Set.union_subset hTs (hJs n (Finset.mem_insert_self n t))
      calc ∑ i ∈ insert n t, eVariationOn f (J i)
          = eVariationOn f (J n) + ∑ i ∈ t, eVariationOn f (J i) := Finset.sum_insert hnt
        _ ≤ eVariationOn f (J n) + eVariationOn f T := by gcongr
        _ = eVariationOn f T + eVariationOn f (J n) := add_comm _ _
        _ ≤ eVariationOn f (T ∪ J n) := eVariationOn.add_le_union f hcross
        _ ≤ eVariationOn f s := eVariationOn.mono f hunion

/-- The variation over a half-open interval is controlled by the variations over its closed
subintervals: a half-open interval is order-connected, and every closed subinterval of it sits
inside one reaching to the left end. -/
theorem eVariationOn_Ico_le {f : α → E} {a m : α} {C : ℝ≥0∞}
    (h : ∀ c ∈ Set.Ico a m, eVariationOn f (Icc a c) ≤ C) :
    eVariationOn f (Set.Ico a m) ≤ C :=
  eVariationOn_le_of_forall_Icc Set.ordConnected_Ico fun _u hu v hv _ =>
    (eVariationOn.mono f (Set.Icc_subset_Icc hu.1 le_rfl)).trans (h v hv)

/-- The mirror of `Shields.eVariationOn_Ico_le` at the other end. -/
theorem eVariationOn_Ioc_le {f : α → E} {m b : α} {C : ℝ≥0∞}
    (h : ∀ d ∈ Set.Ioc m b, eVariationOn f (Icc d b) ≤ C) :
    eVariationOn f (Set.Ioc m b) ≤ C :=
  eVariationOn_le_of_forall_Icc Set.ordConnected_Ioc fun u hu _v hv _ =>
    (eVariationOn.mono f (Set.Icc_subset_Icc le_rfl hv.2)).trans (h u hu)


/-! ### Axiom footprint -/

/-- info: 'Shields.eVariationOn_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eVariationOn_sum_le

/-- info: 'Shields.eVariationOn_Ico_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eVariationOn_Ico_le

/-- info: 'Shields.eVariationOn_Ioc_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eVariationOn_Ioc_le

end Shields
