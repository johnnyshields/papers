/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# An involution defined only off a subpredicate

Mathlib's `Finset.prod_involution` takes an involution `g` defined on the whole of a `Finset`,
pairing each value of `f` with its inverse, and concludes that the product is `1`.  Several
cancellation arguments produce an involution that is defined -- and fixed-point-free -- only
off a distinguished subpredicate `P`, the remaining part of the product being the object of
interest rather than a term that vanishes.  The statement below is that relativization: the
product over `s` collapses onto `s.filter P`.

The additive form is the sign-reversing involution of Lindström--Gessel--Viennot, where `s` is a
set of path families, `P` selects the non-crossing ones, and `g` swaps the tails of a crossing
pair.

## Main results

* `Shields.prod_eq_prod_filter_of_invPairing` and its additive form
  `Shields.sum_eq_sum_filter_of_signReversing`: `Finset.prod_involution` relativized to a
  subpredicate, the big operator collapsing onto that subpredicate rather than to the unit.

## Tags

big operators, involution, sign-reversing involution, cancellation
-/

namespace Shields

open Finset

variable {ι M : Type*} [CommGroup M]

/-- If `g` maps the part of `s` where `P` fails into itself without fixed points, is
involutive there, and pairs each value of `f` with its inverse, then only the part where `P`
holds survives.

The four hypotheses are exactly the four obligations of `Finset.prod_involution`, relativized
to `¬ P`; `gP` is the extra one, that the involution does not escape the part it is defined
on. -/
@[to_additive sum_eq_sum_filter_of_signReversing
/-- If `g` maps the part of `s` where `P` fails into itself without fixed points, is
involutive there, and reverses the sign of `f`, then only the part where `P` holds survives.

The four hypotheses are exactly the four obligations of `Finset.sum_involution`, relativized
to `¬ P`; `gP` is the extra one, that the involution does not escape the part it is defined
on. -/]
theorem prod_eq_prod_filter_of_invPairing (s : Finset ι) (f : ι → M) (P : ι → Prop)
    [DecidablePred P] (g : ι → ι) (gmem : ∀ a ∈ s, ¬ P a → g a ∈ s)
    (gP : ∀ a ∈ s, ¬ P a → ¬ P (g a)) (gne : ∀ a ∈ s, ¬ P a → g a ≠ a)
    (ginv : ∀ a ∈ s, ¬ P a → g (g a) = a) (gsign : ∀ a ∈ s, ¬ P a → f a * f (g a) = 1) :
    ∏ a ∈ s, f a = ∏ a ∈ s.filter P, f a := by
  have hone : ∏ a ∈ s.filter (fun a => ¬ P a), f a = 1 := by
    have hmem : ∀ a ∈ s.filter (fun a => ¬ P a), g a ∈ s.filter (fun a => ¬ P a) := by
      intro a ha
      rw [mem_filter] at ha ⊢
      exact ⟨gmem a ha.1 ha.2, gP a ha.1 ha.2⟩
    refine Finset.prod_involution (fun a _ => g a) (fun a ha => gsign a ?_ ?_)
      (fun a ha _ => gne a ?_ ?_) (fun a ha => hmem a ha) (fun a ha => ginv a ?_ ?_) <;>
      first
        | exact (mem_filter.mp ha).1
        | exact (mem_filter.mp ha).2
  rw [← Finset.prod_filter_mul_prod_filter_not s P f, hone, mul_one]


/-! ### Axiom footprint -/

/-- info: 'Shields.prod_eq_prod_filter_of_invPairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_eq_prod_filter_of_invPairing

/-- info: 'Shields.sum_eq_sum_filter_of_signReversing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_eq_sum_filter_of_signReversing

end Shields
