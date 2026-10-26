/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SelectedCoreGradient
import SkewCornerDescent.Matrix.SelectedCoreRecovery
import SkewCornerDescent.TruncatedUnitTorsion
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Ordinary series of the complete proper selected cores

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). Positive original integer distances are proved before their
conversion to natural exponents. The common raw gradient supplies the finite
product jet; no common-product hypothesis is added. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Ordinary polynomial of the actual incoming selected core. -/
noncomputable def selectedCoreLeftPolynomial {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) : Polynomial (OtherField c.top) :=
  ordinaryEndpointProfile (fun i : Fin n => (P.xi 0 - P.xi i.succ).toNat)
    (fun i => c.selectedCoreIncoming P hP () i)

/-- Ordinary polynomial of the actual outgoing selected core. -/
noncomputable def selectedCoreRightPolynomial {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) : Polynomial (OtherField c.top) :=
  ordinaryEndpointProfile (fun i : Fin n => (P.zeta i.castSucc - P.zeta (Fin.last n)).toNat)
    (fun i => c.selectedCoreOutgoing P hP i ())

/-- The natural-exponent left polynomial retains the original integer profile. -/
theorem selected_core_left_toLaurent {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    (c.selectedCoreLeftPolynomial P hP).toLaurent = c.selectedCoreLeftProfile P hP := by
  exact (endpointProfile_eq_toLaurent_of_nonneg _ _
    (fun i => (c.selected_core_left_distances P hP i).1.le)).symm

/-- The same exact representation bridge for the right polynomial. -/
theorem selected_core_right_toLaurent {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    (c.selectedCoreRightPolynomial P hP).toLaurent = c.selectedCoreRightProfile P hP := by
  exact (endpointProfile_eq_toLaurent_of_nonneg _ _
    (fun i => (c.selected_core_right_distances P hP i).1.le)).symm

private theorem coeff_toLaurent_nat {F : Type*} [CommRing F] (p : Polynomial F) (k : ℕ) :
    p.toLaurent.coeff (k : ℤ) = p.coeff k := by
  change (Finsupp.mapDomain (fun x : ℕ => (x : ℤ)) p.toFinsupp.coeff) (k : ℤ) = _
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k

/-- The complete selected-core polynomial products have identical coefficients
below the selected span, supplied by the common selected-function gradient. -/
theorem selected_core_polynomial_product_coeff_eq {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur)
    (k : ℕ) (hk : k < (c.top : ℕ)) :
    (c.selectedCoreLeftPolynomial P hP * c.selectedCoreRightPolynomial P hP).coeff k =
      (c.selectedCoreLeftPolynomial Q hQ * c.selectedCoreRightPolynomial Q hQ).coeff k := by
  let j : ℕ+ := ⟨(c.top : ℕ) - k, by omega⟩
  have hj : (c.top : ℤ) - (j : ℤ) = (k : ℤ) := by
    change ((c.top : ℕ) : ℤ) - (((c.top : ℕ) - k : ℕ) : ℤ) = (k : ℤ)
    omega
  have he := c.selected_core_product_coeff_eq P Q hP hQ j
  rw [hj, ← c.selected_core_left_toLaurent P hP, ← c.selected_core_right_toLaurent P hP,
    ← c.selected_core_left_toLaurent Q hQ, ← c.selected_core_right_toLaurent Q hQ,
    ← map_mul, ← map_mul, coeff_toLaurent_nat, coeff_toLaurent_nat] at he
  exact he

/-- The original left profile has constant coefficient one. -/
theorem selected_core_left_constant {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    (c.selectedCoreLeftPolynomial P hP).coeff 0 = 1 := by
  classical
  have hd (i : Fin n) : (P.xi 0 - P.xi i.succ).toNat ≠ 0 := by
    have h := (c.selected_core_left_distances P hP i).1
    omega
  simp [selectedCoreLeftPolynomial, ordinaryEndpointProfile, Polynomial.coeff_monomial, hd]

/-- The original right profile also has constant coefficient one. -/
theorem selected_core_right_constant {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    (c.selectedCoreRightPolynomial P hP).coeff 0 = 1 := by
  classical
  have hd (i : Fin n) : (P.zeta i.castSucc - P.zeta (Fin.last n)).toNat ≠ 0 := by
    have h := (c.selected_core_right_distances P hP i).1
    omega
  simp [selectedCoreRightPolynomial, ordinaryEndpointProfile, Polynomial.coeff_monomial, hd]

/-- One actual selected-core profile determines its mate to the whole precision
of the common selected gradient. No product jet is taken as a new hypothesis. -/
theorem selected_core_right_jet_of_left {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur)
    (hleft : ∀ k < (c.top : ℕ),
      (c.selectedCoreLeftPolynomial P hP).coeff k =
        (c.selectedCoreLeftPolynomial Q hQ).coeff k) :
    ∀ k < (c.top : ℕ),
      (c.selectedCoreRightPolynomial P hP).coeff k =
        (c.selectedCoreRightPolynomial Q hQ).coeff k := by
  have h := SkewCornerDescent.unit_jet_product_right
    (c.selectedCoreLeftPolynomial P hP : PowerSeries (OtherField c.top))
    (c.selectedCoreRightPolynomial P hP : PowerSeries (OtherField c.top))
    (c.selectedCoreLeftPolynomial Q hQ : PowerSeries (OtherField c.top))
    (c.selectedCoreRightPolynomial Q hQ : PowerSeries (OtherField c.top))
    (c.top : ℕ) ?_ ?_ ?_
  · simpa only [Polynomial.coeff_coe] using h
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      Polynomial.coeff_coe, c.selected_core_left_constant P hP]
    exact one_ne_zero
  · intro k hk
    simpa only [Polynomial.coeff_coe] using hleft k hk
  · intro k hk
    simpa only [← Polynomial.coe_mul, Polynomial.coeff_coe] using
      c.selected_core_polynomial_product_coeff_eq P Q hP hQ k hk

/-- Every left-core coefficient at or above the selected span vanishes. -/
theorem selected_core_left_coeff_of_top_le {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (k : ℕ) (hk : (c.top : ℕ) ≤ k) :
    (c.selectedCoreLeftPolynomial P hP).coeff k = 0 := by
  classical
  have hk0 : k ≠ 0 := by have := c.top.pos; omega
  have hd (i : Fin n) : (P.xi 0 - P.xi i.succ).toNat ≠ k := by
    have h := c.selected_core_left_distances P hP i
    omega
  simp [selectedCoreLeftPolynomial, ordinaryEndpointProfile,
    Polynomial.coeff_monomial, Polynomial.coeff_one, hd, hk0]

/-- Every right-core coefficient at or above the selected span also vanishes. -/
theorem selected_core_right_coeff_of_top_le {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (k : ℕ) (hk : (c.top : ℕ) ≤ k) :
    (c.selectedCoreRightPolynomial P hP).coeff k = 0 := by
  classical
  have hk0 : k ≠ 0 := by have := c.top.pos; omega
  have hd (i : Fin n) : (P.zeta i.castSucc - P.zeta (Fin.last n)).toNat ≠ k := by
    have h := c.selected_core_right_distances P hP i
    omega
  simp [selectedCoreRightPolynomial, ordinaryEndpointProfile,
    Polynomial.coeff_monomial, Polynomial.coeff_one, hd, hk0]

/-- A single complete proper left-profile jet below the selected span recovers
the selected component's literal cells. The common gradient supplies the mate,
and the protected original supports supply both beta lists. -/
theorem selected_core_literal_of_left_jet {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur)
    (hleft : ∀ k < (c.top : ℕ),
      (c.selectedCoreLeftPolynomial P hP).coeff k =
        (c.selectedCoreLeftPolynomial Q hQ).coeff k) : P.cells = Q.cells := by
  have hr := c.selected_core_right_jet_of_left P Q hP hQ hleft
  have hlpoly : c.selectedCoreLeftPolynomial P hP = c.selectedCoreLeftPolynomial Q hQ := by
    ext k
    by_cases hk : k < (c.top : ℕ)
    · exact hleft k hk
    · rw [c.selected_core_left_coeff_of_top_le P hP k (Nat.le_of_not_gt hk),
        c.selected_core_left_coeff_of_top_le Q hQ k (Nat.le_of_not_gt hk)]
  have hrpoly : c.selectedCoreRightPolynomial P hP = c.selectedCoreRightPolynomial Q hQ := by
    ext k
    by_cases hk : k < (c.top : ℕ)
    · exact hr k hk
    · rw [c.selected_core_right_coeff_of_top_le P hP k (Nat.le_of_not_gt hk),
        c.selected_core_right_coeff_of_top_le Q hQ k (Nat.le_of_not_gt hk)]
  have hlprofile : c.selectedCoreLeftProfile P hP = c.selectedCoreLeftProfile Q hQ := by
    rw [← c.selected_core_left_toLaurent P hP, ← c.selected_core_left_toLaurent Q hQ, hlpoly]
  have hrprofile : c.selectedCoreRightProfile P hP = c.selectedCoreRightProfile Q hQ := by
    rw [← c.selected_core_right_toLaurent P hP, ← c.selected_core_right_toLaurent Q hQ, hrpoly]
  apply c.selected_core_early_literal P Q hP hQ (2 * (c.top : ℤ) + 1) (by omega)
  · intro z _ _
    rw [hlprofile]
  · intro z _ _
    rw [hrprofile]

end SkewCornerDescent.Matrix.SelectedCoordinate
