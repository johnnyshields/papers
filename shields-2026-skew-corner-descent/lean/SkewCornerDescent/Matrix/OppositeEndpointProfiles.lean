/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.EndpointCoreProfile
import SkewGluing.InteriorCofactor

/-!
# Whole Schur determinants of opposite content-end extensions

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
An endpoint extension changes the unmatched top row or bottom starting endpoint
and adds complete rows outside the original content interval. Each normalized
parent has its own common content offset; both beta lists shift together, so
every original entry is unchanged. Strict source beta ordering produces all
three zero rectangles. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Constitutive equality of both complete original beta lists, after a common
content offset, with the indicated endpoint splice. This describes the actual
profiles, not a determinant relation. -/
def endpointProfileMatches {n : ℕ} (P : Profile n) (a b c : ℕ)
    (hsize : n + 1 = a + 1 + (b + 1 + c)) (shift : ℤ)
    (upperRows : Fin a ⊕ Unit → ℤ) (coreRows : Unit ⊕ Fin b → ℤ)
    (lowerRows : Fin c → ℤ) (upperCols : Fin a → ℤ)
    (coreCols : Unit ⊕ Fin b → ℤ) (lowerCols : Unit ⊕ Fin c → ℤ) : Prop :=
  (∀ i, P.xi (((commonCoreFiniteRows a b c).trans (finCongr hsize.symm)) i) + shift =
    endpointBorderRows upperRows coreRows lowerRows i) ∧
  (∀ j, P.zeta (((commonCoreFiniteCols a b c).trans (finCongr hsize.symm)) j) + shift =
    endpointBorderCols upperCols coreCols lowerCols j)

/-- Opposite content-end extensions preserve divisibility by the entire actual
source cofactor. The complete beta-list splice is the standing extension data;
all zero rectangles and determinant orientations are produced inside the proof. -/
theorem oppositeEndpointProfiles_cross_difference_dvd {a b c nL nR nF : ℕ}
    (U : Profile (b + 1)) (L : Profile nL) (R : Profile nR) (F : Profile nF)
    (hsizeL : nL + 1 = a + 1 + (b + 1 + 0))
    (hsizeR : nR + 1 = 0 + 1 + (b + 1 + c))
    (hsizeF : nF + 1 = a + 1 + (b + 1 + c))
    (shiftL shiftR shiftF : ℤ)
    (upperRows : Fin a ⊕ Unit → ℤ) (upperCols : Fin a → ℤ)
    (lowerRows : Fin c → ℤ) (lowerCols : Unit ⊕ Fin c → ℤ)
    (hUpper : ∀ j, U.xi 0 ≤ upperCols j)
    (hLower : ∀ i, lowerRows i ≤ U.zeta (Fin.last (b + 1)))
    (hL : endpointProfileMatches L a b 0 hsizeL shiftL upperRows
      (fun i => U.xi (commonCoreFinEquiv b i).succ) (fun i : Fin 0 => i.elim0)
      upperCols (fun j => U.zeta (commonCoreFinEquiv b j).castSucc)
      (fun (_ : Unit ⊕ Fin 0) => U.zeta (Fin.last (b + 1))))
    (hR : endpointProfileMatches R 0 b c hsizeR shiftR (fun (_ : Fin 0 ⊕ Unit) => U.xi 0)
      (fun i => U.xi (commonCoreFinEquiv b i).succ) lowerRows (fun i : Fin 0 => i.elim0)
      (fun j => U.zeta (commonCoreFinEquiv b j).castSucc) lowerCols)
    (hF : endpointProfileMatches F a b c hsizeF shiftF upperRows
      (fun i => U.xi (commonCoreFinEquiv b i).succ) lowerRows upperCols
      (fun j => U.zeta (commonCoreFinEquiv b j).castSucc) lowerCols) :
    cellSchur (diagramInterior U.cells) U.isSkew_cells.interior ∣
      F.schur * U.schur - L.schur * R.schur := by
  rw [← U.minorDet_eq_interiorSchur]
  change (jtMatrix (fun j : Fin (b + 1) => U.xi j.succ)
    (fun j => U.zeta j.castSucc)).det ∣ _
  have hxy : U.zeta (Fin.last (b + 1)) < U.xi 0 := by
    have hz := U.zeta_nonneg 0
    have hr := U.r_pos 0
    have he := U.xi_sub_zeta 0
    rw [U.zeta_last]
    omega
  have hCL : ∀ i j, U.xi (commonCoreFinEquiv b i).succ < upperCols j := by
    intro i j
    exact (U.xi_strictAnti (show (0 : Fin (b + 2)) < (commonCoreFinEquiv b i).succ by
      change 0 < (commonCoreFinEquiv b i).val + 1
      omega)).trans_le (hUpper j)
  have hBC : ∀ i j, lowerRows i < U.zeta (commonCoreFinEquiv b j).castSucc := by
    intro i j
    exact (hLower i).trans_lt (U.zeta_strictAnti (show
      (commonCoreFinEquiv b j).castSucc < Fin.last (b + 1) by
        change (commonCoreFinEquiv b j).val < b + 1
        exact (commonCoreFinEquiv b j).isLt))
  have hBL : ∀ i j, lowerRows i < upperCols j := by
    intro i j
    exact (hLower i).trans_lt (hxy.trans_le (hUpper j))
  have hd := endpointCore_cross_difference_dvd upperRows
    (fun i => U.xi (commonCoreFinEquiv b i).succ) lowerRows upperCols
    (fun j => U.zeta (commonCoreFinEquiv b j).castSucc) lowerCols
    (U.xi 0) (U.zeta (Fin.last (b + 1))) hCL hBL hBC
  rw [endpointCoreFrame_eq_originalProfileFrame F hsizeF shiftF _ _ _ _ _ _ hF.1 hF.2,
    endpointCoreFrame_base_profile U,
    endpointCoreFrame_eq_originalProfileFrame L hsizeL shiftL _ _ _ _ _ _ hL.1 hL.2,
    endpointCoreFrame_eq_originalProfileFrame R hsizeR shiftR _ _ _ _ _ _ hR.1 hR.2] at hd
  simp only [det_originalProfileFrame] at hd
  have hs : (Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) *
      (Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) = 1 := by
    simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, Int.cast_one]
  have he : ((Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) * F.schur) *
        ((Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) * U.schur) -
      ((Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) * L.schur) *
        ((Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) * R.schur) =
      F.schur * U.schur - L.schur * R.schur := by
    calc
      _ = ((Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) *
          (Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda)) *
          (F.schur * U.schur - L.schur * R.schur) := by ring
      _ = _ := by rw [hs, one_mul]
  rw [he] at hd
  change ((jtMatrix (fun j : Fin (b + 1) => U.xi j.succ)
    (fun j => U.zeta j.castSucc)).submatrix (commonCoreFinEquiv b)
      (commonCoreFinEquiv b)).det ∣ _ at hd
  simpa only [Matrix.det_submatrix_equiv_self] using hd

/-- A one-row source has empty corner core and hence unit cofactor. The
opposite-extension divisibility includes this boundary without an extra premise. -/
theorem single_row_source_cross_difference_dvd {nL nR nF : ℕ}
    (U : Profile 0) (L : Profile nL) (R : Profile nR) (F : Profile nF) :
    cellSchur (diagramInterior U.cells) U.isSkew_cells.interior ∣
      F.schur * U.schur - L.schur * R.schur := by
  rw [← U.minorDet_eq_interiorSchur]
  change (jtMatrix (fun j : Fin 0 => U.xi j.succ)
    (fun j => U.zeta j.castSucc)).det ∣ _
  rw [Matrix.det_isEmpty]
  exact one_dvd _

end SkewCornerDescent.Matrix
