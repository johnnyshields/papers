/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Algebraic operations on the total variation

`eVariationOn` is defined for maps into a `PseudoEMetricSpace`, so Mathlib states its
multiplicative theory only: `eVariationOn_bilinear_comp_le` and its `smul` and `mul`
corollaries.  The **additive** theory is missing, and this file supplies it for a
seminormed additive group: variation is subadditive, blind to a constant shift, and
blind to a sign.  The last of these turns Mathlib's `MonotoneOn.eVariationOn_eq` into
its antitone counterpart.

Every proof runs on one increment identity, applied under the supremum defining
`eVariationOn`.  Nothing here needs the domain to be `ℝ`.

## Main results

* `Shields.eVariationOn_add_le`, `Shields.eVariationOn_finsetSum_le`,
  `Shields.eVariationOn_multisetSum_le` -- subadditivity, for two summands and for a
  `Finset`- or `Multiset`-indexed family.
* `Shields.eVariationOn_add_const`, `Shields.eVariationOn_congr_add_const` -- a constant
  shift leaves the variation alone; the second asks for the shift on `s` only.
* `Shields.eVariationOn_neg` -- so does a sign.
* `AntitoneOn.eVariationOn_eq` -- the variation of an antitone real function on
  `s ∩ Icc a b` is `f a - f b`, the mirror of Mathlib's `MonotoneOn.eVariationOn_eq`.

## Implementation notes

`eVariationOn_add_le` is stated on `fun x => f x + g x` rather than on `f + g` so that it
applies to a sum written pointwise, which is how a branch decomposition presents itself.

Used by `forgacs-tran-numerators`.

## Tags

bounded variation, total variation, subadditive, antitone
-/

open Set

namespace Shields

variable {α : Type*} [LinearOrder α] {E : Type*} [SeminormedAddCommGroup E]

/-! ### Subadditivity -/

/-- **The variation is subadditive.**  Each increment of `f + g` is bounded by the sum of the
increments, and the two sums are bounded separately over the same monotone tuple. -/
theorem eVariationOn_add_le (f g : α → E) (s : Set α) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
          + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)

/-- The constant function has zero variation. -/
theorem eVariationOn_zero (s : Set α) : eVariationOn (fun _ : α => (0 : E)) s = 0 := by
  refine eVariationOn.constant_on ?_
  rintro x ⟨a, -, rfl⟩ y ⟨b, -, rfl⟩
  rfl

/-- Subadditivity over a `Finset`-indexed family. -/
theorem eVariationOn_finsetSum_le {ι : Type*} (t : Finset ι) (ψ : ι → α → E) (s : Set α) :
    eVariationOn (fun x => ∑ ℓ ∈ t, ψ ℓ x) s ≤ ∑ ℓ ∈ t, eVariationOn (ψ ℓ) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [eVariationOn_zero]
  | insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      exact le_trans (eVariationOn_add_le _ _ _) (by gcongr)

/-- Subadditivity over a `Multiset`-indexed family, where the count is a multiplicity. -/
theorem eVariationOn_multisetSum_le {ι : Type*} (m : Multiset ι) (ψ : ι → α → E) (s : Set α) :
    eVariationOn (fun x => (m.map (fun ℓ => ψ ℓ x)).sum) s
      ≤ (m.map (fun ℓ => eVariationOn (ψ ℓ) s)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [eVariationOn_zero]
  | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact le_trans (eVariationOn_add_le _ _ _) (by gcongr)

/-! ### A constant shift -/

private theorem edist_add_const (x y k : E) : edist (x + k) (y + k) = edist x y := by
  rw [edist_dist, edist_dist, dist_add_right]

/-- **Adding a constant leaves `eVariationOn` alone.**  Every increment
`edist (f (u (i+1)) + k) (f (u i) + k)` is the increment of `f`, and the supremum is over
the same sequences.  Mathlib carries `eVariationOn.eq_of_eqOn` but not this. -/
theorem eVariationOn_add_const (f : α → E) (k : E) (s : Set α) :
    eVariationOn (fun x => f x + k) s = eVariationOn f s := by
  unfold eVariationOn
  refine iSup_congr fun p => Finset.sum_congr rfl fun i _ => ?_
  exact edist_add_const _ _ k

/-- The same for two functions that differ by a constant **on `s`** only. -/
theorem eVariationOn_congr_add_const {f g : α → E} {k : E} {s : Set α}
    (h : ∀ x ∈ s, g x = f x + k) :
    eVariationOn g s = eVariationOn f s := by
  rw [eVariationOn.eq_of_eqOn (f' := fun x => f x + k) h, eVariationOn_add_const]

/-! ### A sign, and the antitone variation -/

/-- **The variation does not see a sign.** -/
theorem eVariationOn_neg (f : α → E) (s : Set α) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  simp only [eVariationOn]
  exact iSup_congr fun p => Finset.sum_congr rfl fun i _ => by
    rw [edist_dist, edist_dist, dist_neg_neg]

end Shields

/-- The variation of an antitone real-valued function on `s ∩ Icc a b` equals its **drop**
`f a - f b`.  The mirror of `MonotoneOn.eVariationOn_eq`, reached from it through
`Shields.eVariationOn_neg`. -/
theorem AntitoneOn.eVariationOn_eq {α : Type*} [LinearOrder α] {f : α → ℝ} {s : Set α} {a b : α}
    (hf : AntitoneOn f s) (as : a ∈ s) (bs : b ∈ s) :
    eVariationOn f (s ∩ Icc a b) = ENNReal.ofReal (f a - f b) := by
  have h : MonotoneOn (fun x => -f x) s := fun x hx y hy hxy => neg_le_neg (hf hx hy hxy)
  have h2 := h.eVariationOn_eq as bs
  -- `Shields.eVariationOn_neg` carries `ℝ`'s metric through its normed-group instance, so
  -- the rewrite is staged through a statement elaborated at the canonical instance.
  have hneg : eVariationOn (fun x => -f x) (s ∩ Icc a b) = eVariationOn f (s ∩ Icc a b) :=
    Shields.eVariationOn_neg f _
  rw [hneg] at h2
  rw [h2]
  congr 1
  ring

/-! ### Axiom footprint -/

/-- info: 'Shields.eVariationOn_finsetSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shields.eVariationOn_finsetSum_le

/-- info: 'Shields.eVariationOn_multisetSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shields.eVariationOn_multisetSum_le

/-- info: 'Shields.eVariationOn_congr_add_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shields.eVariationOn_congr_add_const

/-- info: 'AntitoneOn.eVariationOn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AntitoneOn.eVariationOn_eq
