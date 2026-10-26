/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowFrameCore
import SkewCornerDescent.Matrix.OriginalAmalgamationFrameZeros

/-!
# The genuine common window core inside the original amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). Complete literal end windows identify the union's extracted
core with the actual window's corner matrix. The translation cancels entrywise.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- The entire actual union core is the genuine corner matrix of its literal
common window, rather than an assumed common-core surrogate. -/
theorem originalAmalgamation_frame_core {n m : ℕ}
    (P : Profile n) (a b : ℕ) (W : Profile (b + 1)) (A : Profile m)
    (q : ℤ) (v u z : ℤ × ℤ) (hq : 0 ≤ q) (hqtop : q < P.xi 0) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hsource : n = a + (b + 1)) (hunion : m = n + a) :
    (originalProfileFrame A a b a (by omega)).submatrix
        (fun i => .inr (.inl i))
        (fun j => commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j))) =
      (jtMatrix (fun j : Fin (b + 1) => W.xi j.succ) (fun j => W.zeta j.castSucc)).submatrix
        (commonCoreFinEquiv b) (commonCoreFinEquiv b) := by
  have hlower : W.cells = translate (-z) (P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q)) := by
    rw [← hW, translate_translate, neg_add_cancel, translate_zero]
  have hupper : W.cells = translate (-(v + z)) (P.cells.filter
      (fun x => q ≤ content x ∧ content x < P.xi 0)) := by
    rw [hwindow, ← hW, translate_translate, translate_translate,
      add_assoc, neg_add_cancel, translate_zero]
  have hz0 := (originalWindow_row_alignment P W q v z hqtop hwindow hW).2.2.2
  have hc : content (-(v + z)) = -q := by
    dsimp only [content, Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add] at hz0 hv ⊢
    omega
  obtain ⟨hn, hx⟩ := originalLiteralWindow_lower_core_xi P W (P.xi 0 - q) (-z)
    (by omega) hlower
  obtain ⟨_, hz⟩ := originalLiteralWindow_upper_core_zeta P W q (-(v + z)) hqtop hupper
  obtain ⟨hparent, hends⟩ := originalAmalgamation_prefix_xi_suffix_zeta P A q v u hq hv hwindow hA
  apply Matrix.ext
  intro i j
  have hd : m + 1 = a + 1 + (b + 1 + a) := by omega
  let row := (commonCoreFiniteRows a b a).trans (finCongr hd.symm)
  let col := (commonCoreFiniteCols a b a).trans (finCongr hd.symm)
  let pi : Fin (n + 1) := ⟨n - (b + 1) + (commonCoreFinEquiv b i).val + 1, by
    have := (commonCoreFinEquiv b i).isLt; omega⟩
  let pj : Fin (n + 1) := ⟨(commonCoreFinEquiv b j).val, by
    have := (commonCoreFinEquiv b j).isLt; omega⟩
  have hxi := hx (commonCoreFinEquiv b i)
  change W.xi (commonCoreFinEquiv b i).succ = P.xi pi at hxi
  have hzeta := hz (commonCoreFinEquiv b j)
  change W.zeta (commonCoreFinEquiv b j).castSucc = P.zeta pj + content (-(v + z)) at hzeta
  rw [hc] at hzeta
  have hr : (row (.inr (.inl i))).val = a + 1 + (commonCoreFinEquiv b i).val := by
    change (commonCoreFiniteRows a b a (.inr (.inl i))).val = _
    exact commonCoreFiniteRows_core a b a i
  have hcolval : (col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j)))).val =
      a + (commonCoreFinEquiv b j).val := by
    change (commonCoreFiniteCols a b a
      (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j)))).val = _
    exact commonCoreFiniteCols_core a b a j
  have hrow : row (.inr (.inl i)) = ⟨pi.val, by have := pi.isLt; omega⟩ := by
    apply Fin.ext
    change (row (.inr (.inl i))).val = pi.val
    dsimp only [pi]
    omega
  have hcol : col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j))) =
      ⟨m - n + pj.val, by have := pj.isLt; omega⟩ := by
    apply Fin.ext
    change (col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j)))).val =
      m - n + pj.val
    dsimp only [pj]
    omega
  have hAxi : A.xi (row (.inr (.inl i))) = W.xi (commonCoreFinEquiv b i).succ + q := by
    rw [hrow, (hends pi).1, hxi]
  have hAzeta : A.zeta (col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j)))) =
      W.zeta (commonCoreFinEquiv b j).castSucc + q := by
    rw [hcol, (hends pj).2]
    omega
  change hh (A.xi (row (.inr (.inl i))) -
      A.zeta (col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j))))) = _
  rw [hAxi, hAzeta, add_sub_add_right_eq_sub]
  rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
