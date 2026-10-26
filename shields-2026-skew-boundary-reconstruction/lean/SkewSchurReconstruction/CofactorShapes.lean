/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.YoungShapes
import SkewSchurReconstruction.CofactorActions

/-!
# The Young shape of a capped cofactor

Formalizes «Cofactors as skew Schur functions» (`sec:geometry`,
`lem:cofactor-factorization`, `eq:nu-j`, `eq:cofactor-support`, `eq:cofactor-schur`)
in `shields-2026-skew-boundary-reconstruction.tex`.  Connectivity is not assumed:
the initial retained columns determine exactly which shear is contained in the outer shape.
Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

variable {n : ℕ}

/-- The sheared inner boundary in `eq:nu-j`, with all original zero padding retained. -/
def cofactorInner (X : Diagram n) (j : Fin (n + 1)) (i : Fin n) : ℕ :=
  if i.val < j.val then
    if hi : i.val = 0 then X.top else X.inner ⟨i.val - 1, by omega⟩ + 1
  else X.inner i

theorem cofactorInner_coordinates (X : Diagram n) (j : Fin (n + 1)) (i : Fin n) :
    (X.cofactorInner j i : ℤ) = X.top + i.val - X.capShift (j.succAbove i) := by
  by_cases hij : i.val < j.val
  · rw [Fin.succAbove_of_castSucc_lt j i (show i.castSucc < j from hij)]
    by_cases hi : i.val = 0
    · simp only [cofactorInner, ite_eq_left hij, dite_eq_left hi,
        capShift, Fin.val_castSucc]
      omega
    · simp only [cofactorInner, ite_eq_left hij, dite_eq_right hi,
        capShift, Fin.val_castSucc]
      push_cast
      ring
  · rw [Fin.succAbove_of_le_castSucc j i
      (show j ≤ i.castSucc by change j.val ≤ i.val; omega), capShift_succ]
    simp only [cofactorInner, ite_eq_right hij]
    ring

theorem cofactorInner_antitone (X : Diagram n) (j : Fin (n + 1)) :
    Antitone (X.cofactorInner j) := by
  intro i k hik
  have hiv : i.val ≤ k.val := hik
  by_cases hij : i.val < j.val
  · by_cases hkj : k.val < j.val
    · by_cases hi : i.val = 0
      · by_cases hk : k.val = 0
        · have he : i = k := Fin.ext (hi.trans hk.symm)
          subst k
          exact le_refl _
        · have hp : k.val - 1 < n := by have := k.isLt; omega
          have hrow := X.row_nonempty ⟨k.val - 1, hp⟩
          have htop := X.outer_le_top ⟨k.val - 1, hp⟩
          simp only [cofactorInner, ite_eq_left hij, ite_eq_left hkj,
            dite_eq_left hi, dite_eq_right hk]
          omega
      · have hk : k.val ≠ 0 := by omega
        have hip : i.val - 1 < n := by have := i.isLt; omega
        have hkp : k.val - 1 < n := by have := k.isLt; omega
        have hinner := X.inner_antitone (show (⟨i.val - 1, hip⟩ : Fin n) ≤
            ⟨k.val - 1, hkp⟩ by change i.val - 1 ≤ k.val - 1; omega)
        simp only [cofactorInner, ite_eq_left hij, ite_eq_left hkj,
          dite_eq_right hi, dite_eq_right hk]
        omega
    · by_cases hi : i.val = 0
      · have hr := X.row_nonempty k
        have ht := X.outer_le_top k
        simp only [cofactorInner, ite_eq_left hij, ite_eq_right hkj, dite_eq_left hi]
        omega
      · have hip : i.val - 1 < n := by have := i.isLt; omega
        have hinner := X.inner_antitone (show (⟨i.val - 1, hip⟩ : Fin n) ≤ k by
          change i.val - 1 ≤ k.val; omega)
        simp only [cofactorInner, ite_eq_left hij, ite_eq_right hkj, dite_eq_right hi]
        omega
  · have hkj : ¬ k.val < j.val := by omega
    simpa only [cofactorInner, ite_eq_right hij, ite_eq_right hkj] using X.inner_antitone hik

/-- The standard partition `nu^(j)` belonging to the deleted cap column. -/
def cofactorInnerShape (X : Diagram n) (j : Fin (n + 1)) : YoungDiagram :=
  boundaryShape (X.cofactorInner j) (X.cofactorInner_antitone j)

/-- The deleted maximal minor is the shared Jacobi--Trudi determinant of the sheared shape. -/
theorem cofactor_shear_determinant (X : Diagram n) (j : Fin (n + 1)) :
    X.cofactor j = (-1 : CompleteRing) ^ j.val *
      Shields.jacobiTrudiDet (fun k => complete (k : ℤ)) X.outerShape
        (X.cofactorInnerShape j) n := by
  unfold cofactor signedMaximalCofactor
  congr 1
  unfold Shields.jacobiTrudiDet
  congr 1
  apply Matrix.ext
  intro i k
  simp only [capMatrix, Matrix.submatrix_apply, Matrix.of_apply, id_eq,
    outerShape_rowLen, cofactorInnerShape, boundaryShape_rowLen]
  rw [← complete_sub_eq_jtCoeff]
  congr 1
  have h := X.cofactorInner_coordinates j k
  dsimp [rowParam]
  linarith

private theorem omission_strictMono (j : Fin (n + 1)) : StrictMono j.succAbove := by
  intro i k hik
  simp only [Fin.succAbove]
  split_ifs <;> simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;> omega

/-- Feasibility, rather than connectedness, characterizes every individual cofactor. -/
theorem cofactor_ne_zero_iff_matching (X : Diagram n) (j : Fin (n + 1)) :
    X.cofactor j ≠ 0 ↔ ∀ i, X.rowParam i ≤ X.capShift (j.succAbove i) := by
  have hs : (-1 : CompleteRing) ^ j.val ≠ 0 := pow_ne_zero _ (by simp)
  rw [cofactor, signedMaximalCofactor]
  have hi := monge_minor_ne_zero_iff squareWeight X.rowParam_strictMono
    (X.capShift_strictMono.comp (omission_strictMono j))
  constructor
  · intro h
    have hm := right_ne_zero_of_mul h
    rw [capMatrix_minor_eq_staircase] at hm
    exact hi.mp hm
  · intro h
    apply mul_ne_zero hs
    rw [capMatrix_minor_eq_staircase]
    exact hi.mpr h

/-- The cofactor support criterion identifies precisely when the sheared partition is contained. -/
theorem cofactor_ne_zero_iff_contained (X : Diagram n) (j : Fin (n + 1)) :
    X.cofactor j ≠ 0 ↔ ∀ i, X.cofactorInner j i ≤ X.outer i := by
  rw [cofactor_ne_zero_iff_matching]
  apply forall_congr'
  intro i
  have h := X.cofactorInner_coordinates j i
  dsimp [rowParam]
  omega

/-- Nonzero cofactors specialize to signed genuine skew-tableau generating functions. -/
theorem cofactor_tableau_factorization {R : Type*} [CommRing R]
    (X : Diagram n) (j : Fin (n + 1)) (hj : X.cofactor j ≠ 0) (b : ℕ) (β : ℕ → R) :
    tableauSpecialization b β (X.cofactor j) =
      (-1 : R) ^ j.val * Shields.skewSchur X.outerShape (X.cofactorInnerShape j) b β := by
  rw [cofactor_shear_determinant, map_mul, map_pow, map_neg, map_one]
  congr 1
  apply tableauSpecialization_jacobiTrudiDet
  · intro c hc
    obtain ⟨hi, hcell⟩ := (YoungDiagram.mem_ofRowLens
      (w := List.ofFn (X.cofactorInner j))
      (hw := (X.cofactorInner_antitone j).sortedGE_ofFn) (c := c)).mp hc
    have hi' : c.1 < n := by simpa only [List.length_ofFn] using hi
    apply (YoungDiagram.mem_ofRowLens (w := List.ofFn X.outer)
      (hw := X.outer_antitone.sortedGE_ofFn)).mpr
    refine ⟨(by simpa only [List.length_ofFn] using hi'), ?_⟩
    have hb := (cofactor_ne_zero_iff_contained X j).mp hj ⟨c.1, hi'⟩
    simpa only [List.getElem_ofFn] using (show c.2 < X.outer ⟨c.1, hi'⟩ from
      (show c.2 < X.cofactorInner j ⟨c.1, hi'⟩ by
        simpa only [List.getElem_ofFn] using hcell).trans_le hb)
  · intro i hi
    exact boundaryShape_rowLen_outside _ _ i hi

end Diagram
end SkewSchurReconstruction
