/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationFrameRight
import SkewCornerDescent.Matrix.IntegralCommonCore
import SkewCornerDescent.Matrix.OriginalMultiplicity

/-!
# Four original Jacobi--Trudi determinants with their full common cofactor

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`, `lem:original-transfer`). All compatible core and border
blocks are produced from complete literal windows. The whole determinant
orientations cancel before integral cofactor divisibility is concluded. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate

/-- Complete literal windows supply divisibility by the entire common cofactor
of all four whole original matrices. Size equalities only identify finite frames. -/
theorem originalWindow_frame_cross_difference_dvd {n m : ℕ}
    (P : Profile n) (a b : ℕ) (W : Profile (b + 1)) (A : Profile m)
    (q : ℤ) (v u z : ℤ × ℤ) (hq : 0 ≤ q) (hqtop : q < P.xi 0) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hsource : n = a + (b + 1)) (hunion : m = n + a) :
    (jtMatrix (fun j : Fin (b + 1) => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det ∣ A.schur * W.schur - P.schur ^ 2 := by
  classical
  let M00 := originalProfileFrame W 0 b 0 (by omega)
  let M10 := originalProfileFrame P a b 0 (by omega)
  let M01 := originalProfileFrame P 0 b a (by omega)
  let M11 := originalProfileFrame A a b a (by omega)
  let C := (jtMatrix (fun j : Fin (b + 1) => W.xi j.succ)
    (fun j => W.zeta j.castSucc)).submatrix (commonCoreFinEquiv b) (commonCoreFinEquiv b)
  let L := M11.submatrix Sum.inl
    (fun j => commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inl j))
  let R := M11.submatrix Sum.inl
    (fun j => commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j)))
  let T := M11.submatrix Sum.inl
    (fun j => commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inr j)))
  let S := M11.submatrix (fun i => .inr (.inl i))
    (fun j => commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inr j)))
  let B := M11.submatrix (fun i => .inr (.inr i))
    (fun j => commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inr j)))
  let r := fun j => M00 (.inl (.inr ()))
    (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0) (.inr (.inl j)))
  let s := fun i => M00 (.inr (.inl i))
    (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0) (.inr (.inr (.inl ()))))
  let t := fun i => M10 (.inl i)
    (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inr (.inl ()))))
  let p := fun j => M01 (.inl (.inr ()))
    (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inr j)))
  let z0 := M00 (.inl (.inr ()))
    (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0) (.inr (.inr (.inl ()))))
  have hlower : W.cells = translate (-z) (P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q)) := by
    rw [← hW, translate_translate, neg_add_cancel, translate_zero]
  have hupper : W.cells = translate (-(v + z)) (P.cells.filter
      (fun x => q ≤ content x ∧ content x < P.xi 0)) := by
    rw [hwindow, ← hW, translate_translate, translate_translate,
      add_assoc, neg_add_cancel, translate_zero]
  have hwhole : W.cells = translate 0 (W.cells.filter
      (fun x => 0 ≤ content x ∧ content x < W.xi 0)) := by
    rw [translate_zero]
    symm
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact W.content_bounds_cells hx
  have hWpos : 0 < W.xi 0 := by
    have hr := W.r_pos 0
    have hz := W.zeta_nonneg 0
    have he := W.xi_sub_zeta 0
    omega
  have hC00 := originalLowerWindow_frame_core W 0 b W (W.xi 0) 0 hWpos hwhole (by omega)
  have hC10 := originalLowerWindow_frame_core P a b W (P.xi 0 - q) (-z)
    (by omega) hlower hsource
  have hC01 := originalUpperWindow_frame_core P a b W q (-(v + z)) hqtop hupper hsource
  have hC11 := originalAmalgamation_frame_core P a b W A q v u z hq hqtop hv
    hwindow hW hA hsource hunion
  have hleft := originalAmalgamation_frame_left P A a b q v u hq hv hwindow hA hsource hunion
  have hR := originalAmalgamation_frame_upper_core P a b W A q v u z hq hqtop hv
    hwindow hW hA hsource hunion
  have hright := originalAmalgamation_frame_right P A a b q v u hq hv hwindow hA hsource hunion
  have hfirst := originalUpperWindow_frame_first P a b W q (-(v + z)) hqtop hupper hsource
  have hlast := originalLowerWindow_frame_last P a b W (P.xi 0 - q) (-z)
    (by omega) hlower hsource
  have hzero10 := originalLowerWindow_frame_zero P a b W (P.xi 0 - q) (-z)
    (by omega) hlower hsource
  have hzero01 := originalUpperWindow_frame_zero P a b W q (-(v + z)) hqtop hupper hsource
  have hzero11 := originalAmalgamation_frame_zeros P A a b q v u hq hv hwindow hA hsource hunion
  have h11 : M11 = borderedCoreMatrix L R T C S B := by
    have he := borderedCoreMatrix_of_zero_rectangles M11 hzero11.1 hzero11.2.1 hzero11.2.2
    rw [hC11] at he
    exact he
  have h00 : M00 = borderedCoreMatrix (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) Lambda)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j)
      (Matrix.of fun _ (_ : Unit ⊕ Fin 0) => z0) C
      (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i)
      (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) Lambda) := by
    apply Matrix.ext
    intro i j
    obtain ⟨j, rfl⟩ := (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0)).surjective j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp only [borderedCoreMatrix, Equiv.symm_apply_apply, Matrix.of_apply, Matrix.zero_apply]
    · exact j.elim0
    · rcases i with i | u
      · exact i.elim0
      · cases u; rfl
    · rcases i with i | u
      · exact i.elim0
      · cases u
        rcases j with u | j
        · cases u; rfl
        · exact j.elim0
    · exact j.elim0
    · exact congrArg (fun N => N i j) hC00
    · rcases j with u | j
      · cases u; rfl
      · exact j.elim0
    · exact i.elim0
    · exact i.elim0
    · exact i.elim0
  have h10 : M10 = borderedCoreMatrix L R (Matrix.of fun i (_ : Unit ⊕ Fin 0) => t i) C
      (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i)
      (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) Lambda) := by
    apply Matrix.ext
    intro i j
    obtain ⟨j, rfl⟩ := (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0)).surjective j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp only [borderedCoreMatrix, Equiv.symm_apply_apply, Matrix.of_apply, Matrix.zero_apply]
    · exact (hleft i j).symm
    · exact (hR i j).symm
    · rcases j with u | j
      · cases u; rfl
      · exact j.elim0
    · exact hzero10 i j
    · exact congrArg (fun N => N i j) hC10
    · rcases j with u | j
      · cases u; exact hlast i
      · exact j.elim0
    · exact i.elim0
    · exact i.elim0
    · exact i.elim0
  have h01 : M01 = borderedCoreMatrix (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) Lambda)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) (Matrix.of fun _ j => p j) C S B := by
    apply Matrix.ext
    intro i j
    obtain ⟨j, rfl⟩ := (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a)).surjective j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp only [borderedCoreMatrix, Equiv.symm_apply_apply, Matrix.of_apply, Matrix.zero_apply]
    · exact j.elim0
    · rcases i with i | u
      · exact i.elim0
      · cases u; exact hfirst j
    · rcases i with i | u
      · exact i.elim0
      · cases u; rfl
    · exact j.elim0
    · exact congrArg (fun N => N i j) hC01
    · exact (hright (.inl i) j).symm
    · exact j.elim0
    · exact hzero01 i j
    · exact (hright (.inr i) j).symm
  have he := commonCoreDifference_dvd L R T C S B r s t p z0
  unfold commonCoreDifference at he
  rw [← h11, ← h00, ← h10, ← h01] at he
  dsimp only [M11, M00, M10, M01] at he
  rw [det_originalProfileFrame, det_originalProfileFrame, det_originalProfileFrame,
    det_originalProfileFrame] at he
  have hs : (Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) *
      (Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) = 1 := by
    simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hsign (x y w : Lambda) :
      ((Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) * x) *
          ((Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) * y) -
        ((Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) * w) *
          ((Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) * w) = x * y - w ^ 2 := by
    calc
      _ = ((Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda) *
          (Equiv.Perm.sign (commonCoreFiniteCycle b) : Lambda)) * (x * y - w ^ 2) := by ring
      _ = _ := by rw [hs, one_mul]
  dsimp only [C] at he
  rwa [Matrix.det_submatrix_equiv_self, hsign] at he

end SkewCornerDescent.Matrix
