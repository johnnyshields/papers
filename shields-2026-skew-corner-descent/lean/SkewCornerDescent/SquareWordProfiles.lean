/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCompletedGaps
import SkewCornerDescent.Matrix.OriginalHorizontalSplice

/-!
# Actual profiles and complete corner powers of the five-copy square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The displayed source and window are actual normalized profiles. Their
complete original corner matrices give the stated h-one powers. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial

/-- The actual five-copy source with successive joins H,V,V,H. -/
def source : Profile 7 where
  r := ![2,4,2,2,2,2,4,2]
  g := ![1,1,0,1,0,1,1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The actual complete two-copy horizontal end window. -/
def window : Profile 2 where
  r := ![2,4,2]
  g := ![1,1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The square base of the displayed empty-copy word. -/
def square : Profile 1 where
  r := ![2,2]
  g := ![1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The actual union of the two sources sharing their complete end window. -/
def amalgamation : Profile 12 where
  r := ![2,4,2,2,2,2,4,2,2,2,2,4,2]
  g := ![1,1,0,1,0,1,1,0,1,0,1,1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The actual complete two-source horizontal closure. -/
def closure : Profile 14 where
  r := ![2,4,2,2,2,2,4,4,4,2,2,2,2,4,2]
  g := ![1,1,0,1,0,1,1,1,1,0,1,0,1,1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- All five literal square copies, not merely their symmetric functions. -/
theorem source_literal_copies :
    source.cells = translate (6,6) square.cells ∪ translate (5,8) square.cells ∪
      translate (3,9) square.cells ∪ translate (1,10) square.cells ∪
      translate (0,12) square.cells := by decide

/-- The displayed two-copy window is the complete ordinary horizontal attachment. -/
theorem window_literal_copies :
    window.cells = translate (1,1) square.cells ∪ translate (0,3) square.cells := by decide

/-- Both full end windows have the stated literal placements. -/
theorem source_full_windows :
    source.cells.filter (fun x => content x < 6) = translate (5,5) window.cells ∧
      source.cells.filter (fun x => 9 ≤ content x) = translate (0,9) window.cells := by decide

/-- Both sources are kept in the actual shared-window union. -/
theorem amalgamation_literal_union :
    amalgamation.cells = translate (5,5) source.cells ∪ translate (0,9) source.cells := by decide

/-- Both sources are kept in the full horizontal closure. -/
theorem closure_literal_union :
    closure.cells = translate (7,7) source.cells ∪ translate (0,15) source.cells := by decide

/-- Every lower off-diagonal source corner index is negative. -/
theorem source_corner_negative (i j : Fin 7) (hij : j < i) :
    source.xi i.succ - source.zeta j.castSucc < 0 := by
  have h : ∀ i j : Fin 7, j < i → source.xi i.succ - source.zeta j.castSucc < 0 := by decide
  exact h i j hij

/-- The entire source corner determinant is the exact fifth h-one power. -/
theorem source_corner_power :
    (jtMatrix (fun i : Fin 7 => source.xi i.succ) (fun j => source.zeta j.castSucc)).det =
      (X (1 : ℕ+)) ^ 5 := by
  have htri : (jtMatrix (fun i : Fin 7 => source.xi i.succ)
      (fun j => source.zeta j.castSucc)).IsUpperTriangular := by
    intro i j hij
    exact hh_of_neg (source_corner_negative i j hij)
  rw [Matrix.det_of_isUpperTriangular htri]
  change (∏ i : Fin 7, hh (source.xi i.succ - source.zeta i.castSucc)) = _
  have hdiag : (fun i : Fin 7 => hh (source.xi i.succ - source.zeta i.castSucc)) =
      ![X (1 : ℕ+),X 1,1,X 1,1,X 1,X 1] := by
    funext i
    have hind : (fun i : Fin 7 => source.xi i.succ - source.zeta i.castSucc) =
        ![1,1,0,1,0,1,1] := by decide
    rw [congrFun hind i]
    fin_cases i <;> norm_num [hh, hPos]
  rw [hdiag]
  norm_num [Fin.prod_univ_succ]
  ring

/-- The entire window corner determinant is the exact second h-one power. -/
theorem window_corner_power :
    (jtMatrix (fun i : Fin 2 => window.xi i.succ) (fun j => window.zeta j.castSucc)).det =
      (X (1 : ℕ+)) ^ 2 := by
  have htri : (jtMatrix (fun i : Fin 2 => window.xi i.succ)
      (fun j => window.zeta j.castSucc)).IsUpperTriangular := by
    intro i j hij
    apply hh_of_neg
    have h : ∀ i j : Fin 2, j < i → window.xi i.succ - window.zeta j.castSucc < 0 := by decide
    exact h i j hij
  rw [Matrix.det_of_isUpperTriangular htri]
  have hdiag : (fun i : Fin 2 => hh (window.xi i.succ - window.zeta i.castSucc)) =
      ![X (1 : ℕ+),X 1] := by
    funext i
    have hind : (fun i : Fin 2 => window.xi i.succ - window.zeta i.castSucc) =
        ![1,1] := by decide
    rw [congrFun hind i]
    fin_cases i <;> norm_num [hh, hPos]
  change (∏ i : Fin 2, hh (window.xi i.succ - window.zeta i.castSucc)) = _
  rw [hdiag]
  norm_num [Fin.prod_univ_succ]
  ring

/-- The complete source has the actual five-copy span. -/
theorem source_top : source.xi 0 = 15 := by decide

/-- The complete window has the actual two-copy span. -/
theorem window_top : window.xi 0 = 6 := by decide

end SkewCornerDescent.SquareWordProfiles
