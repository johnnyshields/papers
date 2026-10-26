/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.BetaTableau
import SkewGluing.InteriorProfile

/-!
# Interior component factorization of the corner cofactor

Formalizes `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `eq:corner-factors`, `lem:cofactor`). The complementary beta determinant
is the Schur product of the actual southeast interior, including the empty interior.
The top partial derivative is its signed corner cofactor. Sorry-free.
-/

namespace SkewGluing
open MvPolynomial

namespace Profile
variable {n : ℕ}

/-- The complementary beta determinant is the function of the actual interior components. -/
theorem minorDet_eq_interiorSchur (P : Profile n) :
    betaDet (fun i : Fin n => P.xi i.succ) (fun i : Fin n => P.zeta i.castSucc) =
      cellSchur (diagramInterior P.cells) P.isSkew_cells.interior := by
  cases n with
  | zero =>
    have he : diagramInterior P.cells = ∅ := by
      rw [P.interior_cells_eq_minorCells]
      simp [minorCells]
    have hs0 : IsSkew (∅ : Diagram) := by simp [IsSkew]
    have hc : cellSchur (diagramInterior P.cells) P.isSkew_cells.interior = 1 :=
      (cellSchur_congr he _ hs0).trans (cellSchur_empty hs0)
    rw [hc]
    simp [betaDet]
  | succ m =>
    have h := betaDet_eq_cellSchur P.minor_strictAnti.1 P.minor_strictAnti.2
      (fun i => P.zeta_nonneg i.castSucc) (fun i => P.zeta_le_xi_succ i)
    have he : betaCells (fun i : Fin (m + 1) => P.xi i.succ)
        (fun i : Fin (m + 1) => P.zeta i.castSucc) = diagramInterior P.cells :=
      P.interior_cells_eq_minorCells.symm
    exact h.trans (cellSchur_congr he _ P.isSkew_cells.interior)

/-- The top-variable derivative is the signed product of the interior-component functions. -/
theorem pderiv_schur_eq_interiorSchur (P : Profile n) :
    pderiv P.topVar P.schur =
      (-1) ^ n * cellSchur (diagramInterior P.cells) P.isSkew_cells.interior := by
  rw [P.pderiv_schur_top, P.minorDet_eq_interiorSchur]

end Profile

/-- The cofactor identity is independent of the translated profile presentation. -/
theorem pderiv_cellSchur_eq_interiorSchur {D : Diagram} (hD : IsConnectedSkew D)
    {n : ℕ} (P : Profile n) (v : ℤ × ℤ) (hp : D = translate v P.cells) :
    pderiv P.topVar (cellSchur D hD.1) =
      (-1) ^ n * cellSchur (diagramInterior D) hD.1.interior := by
  rw [cellSchur_eq_profile hD P v hp, P.pderiv_schur_eq_interiorSchur]
  congr 1
  have he : diagramInterior D = translate v (diagramInterior P.cells) := by
    rw [hp, interior_translate]
  exact ((cellSchur_congr he hD.1.interior
    (isSkew_translate v P.isSkew_cells.interior)).trans
    (cellSchur_translate _ _ v)).symm

end SkewGluing
