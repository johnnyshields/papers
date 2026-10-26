/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowFrameZeros
import SkewCornerDescent.Matrix.OriginalAmalgamationRowAlignment

/-!
# All three original amalgamation zero rectangles

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). The two complete source windows inside the literal union
produce every required zero block in its full Jacobi--Trudi matrix. Boundary
unit pivots and every other entry remain present. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- All three zero rectangles of the actual union matrix are supplied by its
complete literal source windows. The size equalities only identify finite frames. -/
theorem originalAmalgamation_frame_zeros {n m : ℕ}
    (P : Profile n) (A : Profile m) (a b : ℕ) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hsource : n = a + (b + 1)) (hunion : m = n + a) :
    let M := originalProfileFrame A a b a (by omega)
    (∀ (i : Unit ⊕ Fin b) (j : Fin a),
      M (.inr (.inl i)) (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inl j)) = 0) ∧
    (∀ (i : Fin a) (j : Fin a),
      M (.inr (.inr i)) (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inl j)) = 0) ∧
    (∀ (i : Fin a) (j : Unit ⊕ Fin b),
      M (.inr (.inr i))
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j))) = 0) := by
  obtain ⟨hlower, hupper⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  obtain ⟨_, hwidth⟩ := originalAmalgamation_profile_extrema P A q v u hq hv hA
  have hpos : 0 < P.xi 0 := by
    have hr := P.r_pos 0
    have hz := P.zeta_nonneg 0
    have he := P.xi_sub_zeta 0
    omega
  have hupper' : P.cells = translate (u - v) (A.cells.filter
      (fun x => q ≤ content x ∧ content x < A.xi 0)) := by
    apply translate_injective v
    rw [translate_translate, show v + (u - v) = u by
      ext <;> dsimp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega]
    exact hupper.symm
  obtain ⟨_, hCL⟩ := originalLiteralWindow_lower_core_zero A P (A.xi 0 - q) u
    (by omega) hlower.symm
  obtain ⟨_, hBC⟩ := originalLiteralWindow_upper_core_zero A P q (u - v)
    (by omega) hupper'
  have hd : m + 1 = a + 1 + (b + 1 + a) := by omega
  let row := (commonCoreFiniteRows a b a).trans (finCongr hd.symm)
  let col := (commonCoreFiniteCols a b a).trans (finCongr hd.symm)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    change hh (A.xi (row (.inr (.inl i))) - A.zeta (col (.inl (.inl j)))) = 0
    have hr : (row (.inr (.inl i))).val = a + 1 + (commonCoreFinEquiv b i).val := by
      change (commonCoreFiniteRows a b a (.inr (.inl i))).val = _
      exact commonCoreFiniteRows_core a b a i
    have hc : (col (.inl (.inl j))).val = j.val := by
      change (commonCoreFiniteCols a b a (.inl (.inl j))).val = _
      exact commonCoreFiniteCols_left a b a j
    let k : Fin n := ⟨(commonCoreFinEquiv b i).val, by
      have := (commonCoreFinEquiv b i).isLt; omega⟩
    have hrow : row (.inr (.inl i)) = ⟨m - n + k.val + 1, by have := k.isLt; omega⟩ := by
      apply Fin.ext
      change (row (.inr (.inl i))).val = m - n + k.val + 1
      dsimp only [k]
      omega
    have hcol : col (.inl (.inl j)) = ⟨j.val, by have := j.isLt; omega⟩ := Fin.ext hc
    rw [hrow, hcol]
    exact hCL ⟨j.val, by have := j.isLt; omega⟩ k (by have := j.isLt; omega)
  · intro i j
    change hh (A.xi (row (.inr (.inr i))) - A.zeta (col (.inl (.inl j)))) = 0
    have hr : (row (.inr (.inr i))).val = a + 1 + (b + 1 + i.val) := by
      change (commonCoreFiniteRows a b a (.inr (.inr i))).val = _
      exact commonCoreFiniteRows_right a b a i
    have hc : (col (.inl (.inl j))).val = j.val := by
      change (commonCoreFiniteCols a b a (.inl (.inl j))).val = _
      exact commonCoreFiniteCols_left a b a j
    let k : Fin n := ⟨j.val, by have := j.isLt; omega⟩
    have hcol : col (.inl (.inl j)) = ⟨k.val, by have := k.isLt; omega⟩ := by
      apply Fin.ext
      exact hc
    rw [hcol]
    exact hBC (row (.inr (.inr i))) k (by omega)
  · intro i j
    change hh (A.xi (row (.inr (.inr i))) -
      A.zeta (col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j))))) = 0
    have hr : (row (.inr (.inr i))).val = a + 1 + (b + 1 + i.val) := by
      change (commonCoreFiniteRows a b a (.inr (.inr i))).val = _
      exact commonCoreFiniteRows_right a b a i
    have hc : (col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j)))).val =
        a + (commonCoreFinEquiv b j).val := by
      change (commonCoreFiniteCols a b a
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j)))).val = _
      exact commonCoreFiniteCols_core a b a j
    let k : Fin n := ⟨a + (commonCoreFinEquiv b j).val, by
      have := (commonCoreFinEquiv b j).isLt; omega⟩
    have hcol : col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j))) =
        ⟨k.val, by have := k.isLt; omega⟩ := by
      apply Fin.ext
      exact hc
    rw [hcol]
    exact hBC (row (.inr (.inr i))) k (by omega)

end SkewCornerDescent.Matrix.SelectedCoordinate
