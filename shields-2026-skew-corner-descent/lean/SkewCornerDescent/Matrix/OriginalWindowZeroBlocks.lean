/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowProfileEndpoints

/-!
# Literal end-window zero rectangles

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). The complete literal profile windows produce strict
negative Jacobi--Trudi indices outside the shared corner core. Boundary unit pivots
remain in the borders. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- Every lower-window core row has strictly negative index against each omitted
parent prefix column. Ordinary zero-gap pivots are not discarded. -/
theorem originalLiteralWindow_lower_core_negative {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi)) :
    ∃ h : m ≤ n, ∀ i : Fin (n + 1), ∀ j : Fin m, i.val < n - m →
      P.xi ⟨n - m + j.val + 1, by have := j.isLt; omega⟩ - P.zeta i < 0 := by
  obtain ⟨hn, hc⟩ := originalLiteralWindow_lower_core_xi P Q hi v hhi hwindow
  obtain ⟨_, hx⟩ := originalLiteralWindow_lower_xi P Q hi v hhi hwindow
  have htop := hx 0
  have hbound := min_le_right
    (P.xi ⟨n - m + (0 : Fin (m + 1)).val, by omega⟩) hi
  rw [← htop] at hbound
  refine ⟨hn, ?_⟩
  intro i j hirow
  have hz := originalLiteralWindow_lower_prefix_bound P Q hi v hhi hwindow i hirow
  have hstrict : Q.xi j.succ < Q.xi 0 := Q.xi_strictAnti (by
    change 0 < j.val + 1
    omega)
  have he := hc j
  omega

/-- Every omitted suffix row has strictly negative index against the upper
window's complete core columns. The clipped last column stays in the border. -/
theorem originalLiteralWindow_upper_core_negative {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0)) :
    ∃ h : m ≤ n, ∀ i : Fin (n + 1), ∀ j : Fin m, m < i.val →
      P.xi i - P.zeta ⟨j.val, by have := j.isLt; omega⟩ < 0 := by
  obtain ⟨hn, hc⟩ := originalLiteralWindow_upper_core_zeta P Q lo v hlo hwindow
  obtain ⟨_, he⟩ := originalLiteralWindow_upper_endpoints P Q lo v hlo hwindow
  have hlast := (he (Fin.last m)).1
  have hbound := le_max_right (P.zeta ⟨m, by omega⟩) lo
  refine ⟨hn, ?_⟩
  intro i j hirow
  have hx := originalLiteralWindow_upper_suffix_bound P Q lo v hlo hwindow i hirow
  have hstrict : Q.zeta (Fin.last m) < Q.zeta j.castSucc := Q.zeta_strictAnti (by
    change j.val < m
    exact j.isLt)
  have hz := hc j
  omega

/-- The lower common-core rectangle consists of genuine zero entries, not unit
pivots suppressed by a block-shape convention. -/
theorem originalLiteralWindow_lower_core_zero {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi)) :
    ∃ h : m ≤ n, ∀ i : Fin (n + 1), ∀ j : Fin m, i.val < n - m →
      hh (P.xi ⟨n - m + j.val + 1, by have := j.isLt; omega⟩ - P.zeta i) = 0 := by
  obtain ⟨hn, hz⟩ := originalLiteralWindow_lower_core_negative P Q hi v hhi hwindow
  exact ⟨hn, fun i j hirow => hh_of_neg (hz i j hirow)⟩

/-- The upper common-core rectangle vanishes at every omitted suffix row. -/
theorem originalLiteralWindow_upper_core_zero {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0)) :
    ∃ h : m ≤ n, ∀ i : Fin (n + 1), ∀ j : Fin m, m < i.val →
      hh (P.xi i - P.zeta ⟨j.val, by have := j.isLt; omega⟩) = 0 := by
  obtain ⟨hn, hz⟩ := originalLiteralWindow_upper_core_negative P Q lo v hlo hwindow
  exact ⟨hn, fun i j hirow => hh_of_neg (hz i j hirow)⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
