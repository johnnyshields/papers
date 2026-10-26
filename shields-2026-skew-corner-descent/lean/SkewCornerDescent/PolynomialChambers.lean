/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Nonvanishing inside real polynomial chambers

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

A nonzero polynomial cannot vanish on a nonempty open coordinate chamber. Finite products
then avoid all denominator and distinct-label zero sets simultaneously without losing openness.

Sorry-free.
-/

namespace SkewCornerDescent

/-- Every nonempty open real coordinate chamber contains a nonzero value of a nonzero polynomial. -/
theorem exists_polynomial_ne_zero_on_open {σ : Type*} (p : MvPolynomial σ ℝ) (hp : p ≠ 0)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, MvPolynomial.eval x p ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ x ∈ U, MvPolynomial.eval x p = 0 := by
    intro x hx
    by_contra he
    exact h ⟨x, hx, he⟩
  obtain ⟨a, ha⟩ := hne
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU a ha
  let v : σ → Set ℝ := fun j => if j ∈ I then u j else Set.univ
  have hv (j : σ) : (v j).Infinite := by
    by_cases hj : j ∈ I
    · simp only [v, ite_eq_left hj]
      exact infinite_of_mem_nhds (a j) ((hu j hj).1.mem_nhds (hu j hj).2)
    · simp only [v, ite_eq_right hj]
      exact Set.infinite_univ
  apply hp
  apply MvPolynomial.funext_set v hv
  intro x hx
  have hxU : x ∈ U := hsub (by
    intro j hj
    change j ∈ I at hj
    have h := hx j (Set.mem_univ j)
    change x j ∈ (if j ∈ I then u j else Set.univ) at h
    simpa only [ite_eq_left hj] using h)
  simpa only [map_zero] using hz x hxU

/-- A finite nonzero polynomial family is simultaneously nonzero inside any open chamber. -/
theorem exists_finite_polynomials_ne_zero_on_open {σ ι : Type*} [Finite ι]
    (p : ι → MvPolynomial σ ℝ) (hp : ∀ i, p i ≠ 0)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ i, MvPolynomial.eval x (p i) ≠ 0 := by
  classical
  let _ := Fintype.ofFinite ι
  have hprod : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  obtain ⟨x, hx, he⟩ := exists_polynomial_ne_zero_on_open (∏ i, p i) hprod U hU hne
  rw [map_prod] at he
  exact ⟨x, hx, fun i => Finset.prod_ne_zero_iff.mp he i (Finset.mem_univ i)⟩

/-- Avoiding a finite polynomial family retains an actual nonempty open chamber. -/
theorem finite_polynomial_avoidance_chamber {σ ι : Type*} [Finite ι]
    (p : ι → MvPolynomial σ ℝ) (hp : ∀ i, p i ≠ 0)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    IsOpen {x | x ∈ U ∧ ∀ i, MvPolynomial.eval x (p i) ≠ 0} ∧
      ({x | x ∈ U ∧ ∀ i, MvPolynomial.eval x (p i) ≠ 0} : Set (σ → ℝ)).Nonempty := by
  constructor
  · change IsOpen (U ∩ {x | ∀ i, MvPolynomial.eval x (p i) ≠ 0})
    apply hU.inter
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_ne.preimage (p i).continuous_eval
  · exact exists_finite_polynomials_ne_zero_on_open p hp U hU hne

end SkewCornerDescent
