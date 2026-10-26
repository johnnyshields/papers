/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueEndpointGradient
import SkewCornerDescent.FirstProfileDifference

/-!
# First profile discrepancies of equal actual residue responses

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Actual
response equality produces the product coefficient; positive original endpoint
distances produce the normalized ordinary profiles. No product-coefficient or
opposite-difference conclusion is carried as an assumption. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete incoming residue endpoint polynomial, with the original inverse. -/
noncomputable def residueIntervalLeftPolynomial {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)] :
    Polynomial (OtherField c.top) :=
  ordinaryEndpointProfile (fun i => (x - row i).toNat)
    (fun i => (vertexOutgoing c.residueMap col x *
      ⅟(vertexBetaMatrix c.residueMap row col)) () i)

/-- Complete outgoing residue endpoint polynomial, with the same full inverse. -/
noncomputable def residueIntervalRightPolynomial {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (y : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)] :
    Polynomial (OtherField c.top) :=
  ordinaryEndpointProfile (fun i => (col i - y).toNat)
    (fun i => (⅟(vertexBetaMatrix c.residueMap row col) *
      vertexIncoming c.residueMap row y) i ())

private theorem ordinary_profile_constant {ν F : Type*} [Fintype ν] [CommRing F]
    (distance : ν → ℤ) (v : ν → F) (hd : ∀ i, 0 < distance i) :
    (ordinaryEndpointProfile (fun i => (distance i).toNat) v).coeff 0 = 1 := by
  classical
  have hz (i) : (distance i).toNat ≠ 0 := by have := hd i; omega
  simp [ordinaryEndpointProfile, Polynomial.coeff_monomial, hz]

private theorem coeff_toLaurent_nat {F : Type*} [CommRing F] (p : Polynomial F) (k : ℕ) :
    p.toLaurent.coeff (k : ℤ) = p.coeff k := by
  change (Finsupp.mapDomain (fun x : ℕ => (x : ℤ)) p.toFinsupp.coeff) (k : ℤ) = _
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k

/-- Equal actual responses force opposite first endpoint differences whenever
their raw differentiating generator is above the selected span. Under `K > 2N`
this holds throughout the degrees below half-span. -/
theorem residue_response_first_differences_opposite {ν μ : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ]
    (row col : ν → ℤ) (row' col' : μ → ℤ) (x y : ℤ)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    [Invertible (vertexBetaMatrix c.residueMap row' col')]
    (hx : ∀ i, row i < x) (hy : ∀ i, y < col i)
    (hx' : ∀ i, row' i < x) (hy' : ∀ i, y < col' i)
    (hresponse :
      c.residueMap (hh (x - y)) -
        (vertexOutgoing c.residueMap col x * ⅟(vertexBetaMatrix c.residueMap row col) *
          vertexIncoming c.residueMap row y) () () =
      c.residueMap (hh (x - y)) -
        (vertexOutgoing c.residueMap col' x * ⅟(vertexBetaMatrix c.residueMap row' col') *
          vertexIncoming c.residueMap row' y) () ())
    (w : ℕ) (hw : (c.top : ℤ) < x - y - (w : ℤ))
    (hleft : ∀ k < w, (c.residueIntervalLeftPolynomial row col x).coeff k =
      (c.residueIntervalLeftPolynomial row' col' x).coeff k)
    (hright : ∀ k < w, (c.residueIntervalRightPolynomial row col y).coeff k =
      (c.residueIntervalRightPolynomial row' col' y).coeff k) :
    (c.residueIntervalLeftPolynomial row col x).coeff w -
        (c.residueIntervalLeftPolynomial row' col' x).coeff w =
      -((c.residueIntervalRightPolynomial row col y).coeff w -
        (c.residueIntervalRightPolynomial row' col' y).coeff w) := by
  let A := c.residueIntervalLeftPolynomial row col x
  let B := c.residueIntervalRightPolynomial row col y
  let C := c.residueIntervalLeftPolynomial row' col' x
  let E := c.residueIntervalRightPolynomial row' col' y
  have hA : A.toLaurent = endpointProfile (fun i => x - row i)
      (fun i => (vertexOutgoing c.residueMap col x *
        ⅟(vertexBetaMatrix c.residueMap row col)) () i) :=
    (endpointProfile_eq_toLaurent_of_nonneg _ _ (fun i => by have := hx i; omega)).symm
  have hB : B.toLaurent = endpointProfile (fun i => col i - y)
      (fun i => (⅟(vertexBetaMatrix c.residueMap row col) *
        vertexIncoming c.residueMap row y) i ()) :=
    (endpointProfile_eq_toLaurent_of_nonneg _ _ (fun i => by have := hy i; omega)).symm
  have hC : C.toLaurent = endpointProfile (fun i => x - row' i)
      (fun i => (vertexOutgoing c.residueMap col' x *
        ⅟(vertexBetaMatrix c.residueMap row' col')) () i) :=
    (endpointProfile_eq_toLaurent_of_nonneg _ _ (fun i => by have := hx' i; omega)).symm
  have hE : E.toLaurent = endpointProfile (fun i => col' i - y)
      (fun i => (⅟(vertexBetaMatrix c.residueMap row' col') *
        vertexIncoming c.residueMap row' y) i ()) :=
    (endpointProfile_eq_toLaurent_of_nonneg _ _ (fun i => by have := hy' i; omega)).symm
  have hp := c.residue_equal_response_profile_products row col row' col' x y x y rfl
    hresponse (w : ℤ) hw
  rw [← hA, ← hB, ← hC, ← hE, ← map_mul, ← map_mul,
    coeff_toLaurent_nat, coeff_toLaurent_nat] at hp
  have hA0 : A.coeff 0 = 1 := ordinary_profile_constant _ _ (fun i => by have := hx i; omega)
  have hE0 : E.coeff 0 = 1 := ordinary_profile_constant _ _ (fun i => by have := hy' i; omega)
  have h := SkewCornerDescent.first_profile_differences_opposite
    (A : PowerSeries (OtherField c.top)) B C E w
    (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using hA0)
    (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using hE0)
    (by simpa only [Polynomial.coeff_coe] using hleft)
    (by simpa only [Polynomial.coeff_coe] using hright)
    (by simpa only [← Polynomial.coe_mul, Polynomial.coeff_coe] using hp)
  simpa only [map_sub, Polynomial.coeff_coe] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
