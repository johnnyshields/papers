/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

/-!
# Algebraic constants in an actual rational generator field

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). An algebraic element of a field generated
by an algebraically independent family belongs to the original coefficient field.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

variable {ι k E : Type*} [Field k] [Field E] [Algebra k E]

/-- No new algebraic constants arise from rational functions of independent generators. -/
theorem algebraic_constant_of_mem_adjoin {x : ι → E}
    (hx : AlgebraicIndependent k x) {z : E}
    (hz : z ∈ IntermediateField.adjoin k (Set.range x)) (ha : IsAlgebraic k z) :
    ∃ c : k, algebraMap k E c = z := by
  classical
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_range_iff k x z).mp hz
  by_cases hq : MvPolynomial.aeval x q = 0
  · exact ⟨0, by simpa only [hq, div_zero, map_zero] using hpq.symm⟩
  let A := algebraicClosure k E
  let z' : A := ⟨z, mem_algebraicClosure_iff.mpr ha⟩
  let f := algebraMap k A
  have heval (r : MvPolynomial ι k) :
      (MvPolynomial.aeval x : MvPolynomial ι A →ₐ[A] E) (MvPolynomial.map f r) =
        MvPolynomial.aeval x r := by
    induction r using MvPolynomial.induction_on with
    | C c => simp only [map_C, aeval_C]; exact IsScalarTower.algebraMap_apply k A E c
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, map_X, aeval_X, hp]
  have he : MvPolynomial.map f p = C z' * MvPolynomial.map f q := by
    apply hx.algebraicClosure
    rw [map_mul, aeval_C, heval, heval]
    change MvPolynomial.aeval x p = z * MvPolynomial.aeval x q
    exact (eq_div_iff hq).mp hpq |>.symm
  have hq' : q ≠ 0 := by intro h; exact hq (h ▸ map_zero _)
  obtain ⟨m, hqm⟩ := MvPolynomial.exists_coeff_ne_zero hq'
  have hcoeff : f (p.coeff m) = z' * f (q.coeff m) := by
    simpa only [coeff_map, coeff_C_mul] using congrArg (fun r => r.coeff m) he
  refine ⟨p.coeff m / q.coeff m, ?_⟩
  have hcoeffE := congrArg (fun a : A => (a : E)) hcoeff
  change algebraMap k E (p.coeff m) = z * algebraMap k E (q.coeff m) at hcoeffE
  rw [map_div₀ (algebraMap k E)]
  exact (div_eq_iff ((map_ne_zero (algebraMap k E)).mpr hqm)).mpr hcoeffE

/-- An irreducible coefficient polynomial with a rational-generator-field root is linear.
The label is produced in the original coefficient field, rather than assumed there. -/
theorem irreducible_rational_generator_root {x : ι → E}
    (hx : AlgebraicIndependent k x) {z : E}
    (hz : z ∈ IntermediateField.adjoin k (Set.range x)) {p : Polynomial k}
    (hp : Irreducible p) (hr : Polynomial.aeval z p = 0) :
    p.natDegree = 1 ∧ ∃ c : k, algebraMap k E c = z ∧ p.IsRoot c := by
  obtain ⟨c, hc⟩ := algebraic_constant_of_mem_adjoin hx hz ⟨p, hp.ne_zero, hr⟩
  have hroot : p.IsRoot c :=
    Polynomial.isRoot_of_aeval_algebraMap_eq_zero (hc.symm ▸ hr)
  exact ⟨Polynomial.natDegree_eq_of_degree_eq_some
    (Polynomial.degree_eq_one_of_irreducible_of_root hp hroot), c, hc, hroot⟩

end SkewCornerDescent
