/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.PolynomialChambers
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Algebra.MonoidAlgebra.Cardinal

/-!
# Faithful rational polynomial evaluation inside any real open chamber

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
The dense open nonvanishing sets of all nonzero rational polynomials have
dense intersection. A nonempty real open chamber therefore contains an assignment
at which evaluation of the whole rational polynomial algebra is injective.
This permits genuine fraction-field maps, not merely finite-expression
specialization with unverified denominators. Sorry-free.
-/

namespace SkewCornerDescent

/-- Any nonempty open chamber in countably many real coordinates contains
a point preserving every nonzero rational polynomial simultaneously. -/
theorem exists_faithful_rational_evaluation_on_open {σ : Type*} [Countable σ]
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, Function.Injective (MvPolynomial.eval₂Hom (Rat.castHom ℝ) x) := by
  classical
  let I := {p : MvPolynomial σ ℚ // p ≠ 0}
  let V := fun p : I => {x : σ → ℝ | MvPolynomial.eval x (p.val.map (Rat.castHom ℝ)) ≠ 0}
  have hopen (p : I) : IsOpen (V p) :=
    isOpen_ne.preimage (p.val.map (Rat.castHom ℝ)).continuous_eval
  have hdense (p : I) : Dense (V p) := by
    apply dense_iff_inter_open.mpr
    intro W hW hWne
    have hp : p.val.map (Rat.castHom ℝ) ≠ 0 := by
      simpa only [map_zero] using
        (MvPolynomial.map_injective (Rat.castHom ℝ) (Rat.castHom ℝ).injective).ne p.property
    obtain ⟨x, hx, hpx⟩ := exists_polynomial_ne_zero_on_open
      (p.val.map (Rat.castHom ℝ)) hp W hW hWne
    exact ⟨x, hx, hpx⟩
  have hd := dense_iInter_of_isOpen hopen hdense
  obtain ⟨x, hxU, hx⟩ := dense_iff_inter_open.mp hd U hU hne
  refine ⟨x, hxU, ?_⟩
  intro p q he
  apply sub_eq_zero.mp
  by_contra hne
  have hnonzero := Set.mem_iInter.mp hx (⟨p-q, hne⟩ : I)
  apply hnonzero
  change MvPolynomial.eval x ((p-q).map (Rat.castHom ℝ)) = 0
  rw [MvPolynomial.eval_map]
  change MvPolynomial.eval₂Hom (Rat.castHom ℝ) x (p-q) = 0
  rw [map_sub, he, sub_self]

end SkewCornerDescent
