/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RegularFractionExpressions
import SkewCornerDescent.CyclicWindows

/-!
# Specializing complete dependent detectors

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`, `lem:peeling`).
All original numerators and denominators are specialized together. A zero detector in the
original field remains zero on a regular coordinate slice, without extending the specialization
to a map of the entire fraction field. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

/-- A complete reciprocal detector can be transferred through the actual regular polynomial
representatives. The two expression coordinates encode a response and its inverse, not
independent response variables.

**Differs from the paper's route.** Clears one finite expression before specializing rather
than transferring a prime valuation through the complete original fraction field. -/
theorem shortDetector_zero_specialize {G α R F K : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [CommRing R] [Field F] [Field K]
    (ι : R →+* F) (φ : R →+* K) (hι : Function.Injective ι)
    (num den : α → R) (word : G → α) (e : α → R)
    (step : G) (j prefixLength : ℕ) (start : G) (s m : R)
    (hnF : ∀ a, ι (num a) ≠ 0) (hdF : ∀ a, ι (den a) ≠ 0)
    (hnK : ∀ a, φ (num a) ≠ 0) (hdK : ∀ a, φ (den a) ≠ 0)
    (hzero :
      let response := fun a => ι (num a) / ι (den a)
      ι s * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        ι m * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ a, ι (e a) * (response a)⁻¹) = 0) :
    let response := fun a => φ (num a) / φ (den a)
    φ s * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
      φ m * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
        (∑ a, φ (e a) * (response a)⁻¹) = 0 := by
  classical
  let numerator : α × Bool → R := fun a => if a.2 then den a.1 else num a.1
  let denominator : α × Bool → R := fun a => if a.2 then num a.1 else den a.1
  let inverse : α → MvPolynomial (α × Bool) R := fun a => MvPolynomial.X (a, true)
  let P : MvPolynomial (α × Bool) R :=
    MvPolynomial.C s * (∑ i, windowProduct (inverse ∘ word) step j i) -
      MvPolynomial.C m * windowProduct (inverse ∘ word) step prefixLength start *
        (∑ a, MvPolynomial.C (e a) * inverse a)
  have hd₁ (a : α × Bool) : ι (denominator a) ≠ 0 := by
    rcases a with ⟨a, b⟩; cases b <;> exact (by first | exact hdF a | exact hnF a)
  have hd₂ (a : α × Bool) : φ (denominator a) ≠ 0 := by
    rcases a with ⟨a, b⟩; cases b <;> exact (by first | exact hdK a | exact hnK a)
  have hsource : P.eval₂ ι (fun a => ι (numerator a) / ι (denominator a)) = 0 := by
    simpa [P, windowProduct, inverse, numerator, denominator, ← Finset.prod_inv_distrib,
      div_eq_mul_inv, mul_comm] using hzero
  have htarget := eval₂_fraction_zero_transfer ι φ hι numerator denominator hd₁ hd₂ P hsource
  simpa [P, windowProduct, inverse, numerator, denominator, ← Finset.prod_inv_distrib,
    div_eq_mul_inv, mul_comm] using htarget

/-- The complete cross-multiplied full-period detector survives the same regular specialization.
Its forward and inverse occurrences use the same actual dependent response family.

**Differs from the paper's route.** Transfers a cleared finite expression to the coordinate
slice, without asserting that the specialization extends to the full original field. -/
theorem fullDetector_zero_specialize {G α R F K : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [CommRing R] [Field F] [Field K]
    (ι : R →+* F) (φ : R →+* K) (hι : Function.Injective ι)
    (num den : α → R) (word : G → α) (e : α → R)
    (step : G) (fullLength periodLength prefixLength k : ℕ) (start : G) (scalar : R)
    (hnF : ∀ a, ι (num a) ≠ 0) (hdF : ∀ a, ι (den a) ≠ 0)
    (hnK : ∀ a, φ (num a) ≠ 0) (hdK : ∀ a, φ (den a) ≠ 0)
    (hzero :
      let response := fun a => ι (num a) / ι (den a)
      ι scalar * (windowProduct (response ∘ word) step periodLength start) ^ (k - 1) *
          windowProduct (response ∘ word) step prefixLength start -
        (∑ a, ι (e a) * (response a)⁻¹) *
          (∑ i, windowProduct (response ∘ word) step fullLength i) = 0) :
    let response := fun a => φ (num a) / φ (den a)
    φ scalar * (windowProduct (response ∘ word) step periodLength start) ^ (k - 1) *
        windowProduct (response ∘ word) step prefixLength start -
      (∑ a, φ (e a) * (response a)⁻¹) *
        (∑ i, windowProduct (response ∘ word) step fullLength i) = 0 := by
  classical
  let numerator : α × Bool → R := fun a => if a.2 then den a.1 else num a.1
  let denominator : α × Bool → R := fun a => if a.2 then num a.1 else den a.1
  let response : α → MvPolynomial (α × Bool) R := fun a => MvPolynomial.X (a, false)
  let inverse : α → MvPolynomial (α × Bool) R := fun a => MvPolynomial.X (a, true)
  let P : MvPolynomial (α × Bool) R :=
    MvPolynomial.C scalar * (windowProduct (response ∘ word) step periodLength start) ^ (k - 1) *
        windowProduct (response ∘ word) step prefixLength start -
      (∑ a, MvPolynomial.C (e a) * inverse a) *
        (∑ i, windowProduct (response ∘ word) step fullLength i)
  have hd₁ (a : α × Bool) : ι (denominator a) ≠ 0 := by
    rcases a with ⟨a, b⟩; cases b <;> exact (by first | exact hdF a | exact hnF a)
  have hd₂ (a : α × Bool) : φ (denominator a) ≠ 0 := by
    rcases a with ⟨a, b⟩; cases b <;> exact (by first | exact hdK a | exact hnK a)
  have hsource : P.eval₂ ι (fun a => ι (numerator a) / ι (denominator a)) = 0 := by
    simpa [P, windowProduct, response, inverse, numerator, denominator,
      div_eq_mul_inv, mul_comm] using hzero
  have htarget := eval₂_fraction_zero_transfer ι φ hι numerator denominator hd₁ hd₂ P hsource
  simpa [P, windowProduct, response, inverse, numerator, denominator,
    div_eq_mul_inv, mul_comm] using htarget

end SkewCornerDescent.CyclicWindows
