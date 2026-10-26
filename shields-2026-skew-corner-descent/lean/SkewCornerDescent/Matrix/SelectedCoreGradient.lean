/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SelectedCoreProfiles
import SkewCornerDescent.Matrix.DeterminantDerivation

/-!
# Raw generator gradients of original selected-core determinants

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). The raw polynomial generator derivative is taken before
selected residue substitution. Its complete signed cofactors specialize through
the actual polynomial homomorphism; it is never confused with a tangent derivative
of the identically zero selected residue. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every raw generator derivative of a complete original profile determinant
has its actual signed cofactor sum at the selected residue. No residue-zero inverse
entry or cofactor is deleted. -/
theorem original_profile_raw_gradient {n : ℕ} (P : Profile n) (j : ℕ+) :
    c.residueMap (MvPolynomial.pderiv j P.schur) =
      ∑ i, ∑ k, if P.xi i - P.zeta k = (j : ℤ) then
        ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate k i else 0 := by
  classical
  have hd := derivation_det_cofactors (MvPolynomial.pderiv j) (jtMatrix P.xi P.zeta)
  change MvPolynomial.pderiv j P.schur = ∑ i, ∑ k,
    (jtMatrix P.xi P.zeta).adjugate k i * MvPolynomial.pderiv j (hh (P.xi i - P.zeta k)) at hd
  have h := congrArg c.residueMap hd
  have hcofactor (i k : Fin (n + 1)) :
      c.residueMap ((jtMatrix P.xi P.zeta).adjugate k i) =
        ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate k i := by
    have hm := congrArg (fun M => M k i) (c.residueMap.map_adjugate (jtMatrix P.xi P.zeta))
    exact hm
  rw [h, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul]
  by_cases hik : P.xi i - P.zeta k = (j : ℤ)
  · rw [pderiv_hh, ite_eq_left hik, map_one, mul_one, ite_eq_left hik, hcofactor]
  · rw [pderiv_hh, ite_eq_right hik, map_zero, mul_zero, ite_eq_right hik]

/-- The raw top-generator derivative is the complete original corner cofactor,
including the zero-row proper-minor boundary. -/
theorem original_profile_top_gradient {n : ℕ} (P : Profile n) :
    c.residueMap (MvPolynomial.pderiv P.topVar P.schur) =
      ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate (Fin.last n) 0 := by
  rw [P.pderiv_schur_top, map_mul, map_pow, map_neg, map_one,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, Fin.val_last, zero_add, Fin.succAbove_zero,
    Fin.succAbove_last]
  congr 1
  exact c.residueMap.map_det _

/-- Equal selected functions have equal actual corner normalizers, independently
of the two diagram realizations. -/
theorem selected_core_corner_eq {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur) :
    ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate (Fin.last n) 0 =
      ((jtMatrix Q.xi Q.zeta).map c.residueMap).adjugate (Fin.last m) 0 := by
  rw [← c.original_profile_top_gradient P, ← c.original_profile_top_gradient Q,
    ← c.top_eq_profile P hP, ← c.top_eq_profile Q hQ, ← hP, ← hQ]

/-- The product of the actual proper selected-core profiles is the normalized
raw selected-function gradient (`lem:early-recovery`, `prop:closure-pin`).
The corner cofactor is retained explicitly, and the raw derivative is taken
before quotienting by the selected prime. -/
theorem selected_core_profile_product_gradient {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (j : ℕ+) :
    ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate (Fin.last n) 0 *
        (c.selectedCoreLeftProfile P hP * c.selectedCoreRightProfile P hP).coeff
          ((c.top : ℤ) - (j : ℤ)) =
      c.residueMap (MvPolynomial.pderiv j P.schur) := by
  classical
  let A := (jtMatrix P.xi P.zeta).map c.residueMap
  let a := A.adjugate (Fin.last n) 0
  let L := fun i : Fin n => c.selectedCoreIncoming P hP () i
  let R := fun i : Fin n => c.selectedCoreOutgoing P hP i ()
  let w := (c.top : ℤ) - (j : ℤ)
  let : Invertible (A.submatrix Fin.succ Fin.castSucc) := c.selectedMinorResidueInverse P hP
  have hdet := c.selected_core_residue_det_zero P hP
  have hleftCof (i : Fin n) : A.adjugate (Fin.last n) i.succ = -a * L i := by
    exact selected_core_incoming_adjugate A hdet (Fin.last n) i
  have hrightCof (k : Fin n) : A.adjugate k.castSucc 0 = -a * R k := by
    exact selected_core_outgoing_adjugate A hdet k
  have hmixedCof (i k : Fin n) : A.adjugate k.castSucc i.succ = a * (L i * R k) := by
    exact selected_core_mixed_adjugate A hdet i k
  have htop := P.topVar_coe
  rw [← c.top_eq_profile P hP] at htop
  have hzeroIndex : (P.xi 0 - P.zeta (Fin.last n) = (j : ℤ)) ↔ w = 0 := by
    dsimp only [w]
    rw [P.zeta_last]
    omega
  have hleftIndex (i : Fin n) : (P.xi i.succ - P.zeta (Fin.last n) = (j : ℤ)) ↔
      P.xi 0 - P.xi i.succ = w := by
    dsimp only [w]
    rw [P.zeta_last]
    omega
  have hrightIndex (k : Fin n) : (P.xi 0 - P.zeta k.castSucc = (j : ℤ)) ↔
      P.zeta k.castSucc - P.zeta (Fin.last n) = w := by
    dsimp only [w]
    rw [P.zeta_last]
    omega
  have hmixedIndex (i k : Fin n) : (P.xi i.succ - P.zeta k.castSucc = (j : ℤ)) ↔
      (P.xi 0 - P.xi i.succ) + (P.zeta k.castSucc - P.zeta (Fin.last n)) = w := by
    dsimp only [w]
    rw [P.zeta_last]
    omega
  have hg := c.original_profile_raw_gradient P j
  change c.residueMap (MvPolynomial.pderiv j P.schur) =
    ∑ i, ∑ k, if P.xi i - P.zeta k = (j : ℤ) then A.adjugate k i else 0 at hg
  rw [Fin.sum_univ_succ] at hg
  simp_rw [Fin.sum_univ_castSucc] at hg
  simp_rw [hzeroIndex, hleftIndex, hrightIndex, hmixedIndex,
    hleftCof, hrightCof, hmixedCof] at hg
  have hzeroScale : (if w = 0 then a else 0) = a * (if w = 0 then 1 else 0) := by
    split_ifs <;> simp
  have hleftScale (i : Fin n) :
      (if P.xi 0 - P.xi i.succ = w then -a * L i else 0) =
        -a * (if P.xi 0 - P.xi i.succ = w then L i else 0) := by
    split_ifs <;> simp
  have hrightScale (k : Fin n) :
      (if P.zeta k.castSucc - P.zeta (Fin.last n) = w then -a * R k else 0) =
        -a * (if P.zeta k.castSucc - P.zeta (Fin.last n) = w then R k else 0) := by
    split_ifs <;> simp
  have hmixedScale (i k : Fin n) :
      (if (P.xi 0 - P.xi i.succ) + (P.zeta k.castSucc - P.zeta (Fin.last n)) = w
        then a * (L i * R k) else 0) =
      a * (if (P.xi 0 - P.xi i.succ) + (P.zeta k.castSucc - P.zeta (Fin.last n)) = w
        then L i * R k else 0) := by
    split_ifs <;> simp
  have hcorner : A.adjugate (Fin.last n) 0 = a := rfl
  rw [hcorner] at hg
  simp_rw [hzeroScale, hleftScale, hrightScale, hmixedScale] at hg
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hg
  change a * (c.selectedCoreLeftProfile P hP * c.selectedCoreRightProfile P hP).coeff w = _
  rw [hg]
  simp only [selectedCoreLeftProfile, selectedCoreRightProfile, endpointProfile_mul_coeff]
  change a * ((if w = 0 then 1 else 0) -
    (∑ i, if P.xi 0 - P.xi i.succ = w then L i else 0) -
    (∑ k, if P.zeta k.castSucc - P.zeta (Fin.last n) = w then R k else 0) +
    ∑ i, ∑ k, if (P.xi 0 - P.xi i.succ) + (P.zeta k.castSucc - P.zeta (Fin.last n)) = w
      then L i * R k else 0) = _
  ring

/-- The common selected Schur function fixes every proper-profile product
coefficient below its top. The corner multiplier is canceled using an actual
protected cofactor, not a generic nonvanishing premise. -/
theorem selected_core_product_coeff_eq {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur) (j : ℕ+) :
    (c.selectedCoreLeftProfile P hP * c.selectedCoreRightProfile P hP).coeff
        ((c.top : ℤ) - (j : ℤ)) =
      (c.selectedCoreLeftProfile Q hQ * c.selectedCoreRightProfile Q hQ).coeff
        ((c.top : ℤ) - (j : ℤ)) := by
  have hn := c.residue_least_column_cofactor_ne_zero P
    (le_of_eq (c.top_eq_profile P hP).symm) 0
  apply mul_left_cancel₀ hn
  rw [c.selected_core_profile_product_gradient P hP j, c.selected_core_corner_eq P Q hP hQ,
    c.selected_core_profile_product_gradient Q hQ j, ← hP, ← hQ]

end SkewCornerDescent.Matrix.SelectedCoordinate
