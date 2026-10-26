/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.ProfileCells
import SkewGluing.SchurFunction

/-!
# The infinite ordinary-mark profile family

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:non-v-family`, `eq:non-v-jt`). The actual three-row profile has lengths
`(2,k,2)` and overlaps `(1,1)` for every `k ≥ 3`. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing
open scoped BigOperators

/-- The connected three-row profile of `(k,k,2)/(k-2)`, for every admissible `k`. -/
def nonVProfile (k : ℕ) (hk : 3 ≤ k) : Profile 2 where
  r := ![2, k, 2]
  g := ![1, 1]
  r_pos := by intro i; fin_cases i <;> simp; all_goals omega
  g_lt_castSucc := by intro i; fin_cases i <;> simp; all_goals omega
  g_lt_succ := by intro i; fin_cases i <;> simp; all_goals omega

/-- The normalized lower beta list is computed from the actual overlaps. -/
theorem nonVProfile_zeta (k : ℕ) (hk : 3 ≤ k) :
    (nonVProfile k hk).zeta = ![(k : ℤ), 1, 0] := by
  funext i
  fin_cases i <;> simp [Profile.zeta, nonVProfile, Fin.sum_univ_succ]

/-- The upper beta list is the lower list plus the actual row lengths. -/
theorem nonVProfile_xi (k : ℕ) (hk : 3 ≤ k) :
    (nonVProfile k hk).xi = ![(k : ℤ) + 2, (k : ℤ) + 1, 2] := by
  funext i
  rw [Profile.xi, nonVProfile_zeta]
  fin_cases i <;> simp [nonVProfile]
  all_goals ring

/-- The displayed Jacobi--Trudi matrix follows from the profile, not from a supplied matrix. -/
theorem nonVProfile_matrix (k : ℕ) (hk : 3 ≤ k) :
    (Matrix.of fun i j : Fin 3 => hh ((nonVProfile k hk).xi i -
      (nonVProfile k hk).zeta j)) =
      !![hh 2, hh ((k : ℤ) + 1), hh ((k : ℤ) + 2);
        hh 1, hh k, hh ((k : ℤ) + 1); 0, hh 1, hh 2] := by
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hneg : hh (2 - (k : ℤ)) = 0 := hh_of_neg (by omega)
  apply Matrix.ext
  intro i j
  rw [nonVProfile_xi, nonVProfile_zeta]
  fin_cases i <;> fin_cases j <;> simp [hneg]
  all_goals congr 1
  all_goals omega

/-- The complete determinant formula holds throughout the infinite family. -/
theorem nonVProfile_schur (k : ℕ) (hk : 3 ≤ k) :
    (nonVProfile k hk).schur =
      (hh 2)^2 * hh k - 2 * hh 1 * hh 2 * hh ((k : ℤ) + 1) +
        (hh 1)^2 * hh ((k : ℤ) + 2) := by
  rw [Profile.schur, nonVProfile_matrix, Matrix.det_fin_three]
  simp
  ring

end SkewCornerDescent
