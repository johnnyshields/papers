/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.CornerMinors

/-!
# Strict generator bound for the actual maximal-corner residual

The residual-generator clause of `eq:private-saturation-corner` in
`shields-2026-skew-class-inflation.tex`.  Every residual determinant
term avoids the unique full-interval site, so all its actual indices
are strictly smaller.  Sorry-free.
-/

namespace SkewJacobiNegative.BetaDiagram

open SkewJacobiNegative

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/CornerMinors.lean,
-- largest_not_mem_residual, generalized to every residual generator's strict index bound.

/-- Every generator in the actual corner residual lies strictly below the private largest label. -/
theorem cornerResidual_vars_lt {n : ℕ} (D : BetaDiagram (n + 1)) (v : ℕ+)
    (hv : v ∈ D.cornerResidual.vars) : (v.val : ℤ) < D.largestLabel := by
  classical
  by_contra! hlarge
  suffices hnot : v ∉ D.cornerResidual.vars from hnot hv
  apply not_mem_vars_sum
  intro j hj
  have hjl : j ≠ Fin.last n := (Finset.mem_erase.mp hj).1
  have he : v ∉ (D.matrix 0 j).vars := by
    change v ∉ (complete (D.row 0 - D.col j)).vars
    rw [mem_vars_complete_iff]
    intro he
    have hlt := D.index_lt_largestLabel 0 j (Or.inr hjl)
    omega
  have hm : v ∉ (D.matrix.submatrix Fin.succ j.succAbove).det.vars := by
    apply not_mem_vars_det
    intro a b
    change v ∉ (complete (D.row a.succ - D.col (j.succAbove b))).vars
    rw [mem_vars_complete_iff]
    intro he
    have hlt := D.index_lt_largestLabel a.succ (j.succAbove b)
      (Or.inl (Fin.succ_ne_zero a))
    omega
  intro hterm
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hterm) with hterm | hterm
  · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hterm) with hterm | hterm
    · have hp := MvPolynomial.vars_pow (-1 : CompleteRing) j.val hterm
      simp only [MvPolynomial.vars_neg, MvPolynomial.vars_one, Finset.notMem_empty] at hp
    · exact he hterm
  · exact hm hterm

end SkewJacobiNegative.BetaDiagram
