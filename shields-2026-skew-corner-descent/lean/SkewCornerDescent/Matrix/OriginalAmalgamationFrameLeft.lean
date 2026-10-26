/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowFrameBorderEntries
import SkewCornerDescent.Matrix.OriginalAmalgamationFrameCore

/-!
# Actual compatible left borders of the literal amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). Complete original matrices have the same left border and
upper/core block. Beta correspondence is produced from the literal windows.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- The complete union's left border equals the original lower-window extension's
left border, with the content shift canceled in every entry. -/
theorem originalAmalgamation_frame_left {n m : ℕ}
    (P : Profile n) (A : Profile m) (a b : ℕ) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hsource : n = a + (b + 1)) (hunion : m = n + a) :
    ∀ (i : Fin a ⊕ Unit) (j : Fin a),
      originalProfileFrame A a b a (by omega) (.inl i)
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inl j)) =
      originalProfileFrame P a b 0 (by omega) (.inl i)
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inl j)) := by
  obtain ⟨_, hends⟩ := originalAmalgamation_prefix_xi_suffix_zeta P A q v u hq hv hwindow hA
  obtain ⟨_, hcore⟩ := originalAmalgamation_suffix_xi_prefix_zeta P A q v u hq hv hwindow hA
  intro i j
  let r : Fin (n + 1) := ⟨(commonCoreTopFinEquiv a i).val, by
    have := (commonCoreTopFinEquiv a i).isLt; omega⟩
  let s : Fin (n + 1) := ⟨j.val, by have := j.isLt; omega⟩
  let rA : Fin (m + 1) := ⟨r.val, by have := r.isLt; omega⟩
  let sA : Fin (m + 1) := ⟨s.val, by have := s.isLt; omega⟩
  let sCore : Fin n := ⟨j.val, by have := j.isLt; omega⟩
  have hP := originalProfileFrame_entry_of_val P a b 0 (by omega)
    (.inl i) (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inl j)) r s
    (by rfl) (commonCoreFiniteCols_left a b 0 j)
  have hU := originalProfileFrame_entry_of_val A a b a (by omega)
    (.inl i) (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inl j)) rA sA
    (by rfl) (commonCoreFiniteCols_left a b a j)
  have hx := (hends r).1
  change A.xi rA = P.xi r + q at hx
  have hz := (hcore sCore).2
  change A.zeta sA = P.zeta s + q at hz
  rw [hU, hP, hx, hz, add_sub_add_right_eq_sub]

/-- The complete union's upper/core block equals the original lower-window
extension's block. The required beta alignment is derived from the actual windows. -/
theorem originalAmalgamation_frame_upper_core {n m : ℕ}
    (P : Profile n) (a b : ℕ) (W : Profile (b + 1)) (A : Profile m)
    (q : ℤ) (v u z : ℤ × ℤ) (hq : 0 ≤ q) (hqtop : q < P.xi 0) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hsource : n = a + (b + 1)) (hunion : m = n + a) :
    ∀ (i : Fin a ⊕ Unit) (j : Unit ⊕ Fin b),
      originalProfileFrame A a b a (by omega) (.inl i)
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j))) =
      originalProfileFrame P a b 0 (by omega) (.inl i)
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inl j))) := by
  obtain ⟨_, hends⟩ := originalAmalgamation_prefix_xi_suffix_zeta P A q v u hq hv hwindow hA
  obtain ⟨hn, hbeta⟩ := originalWindow_zeta_alignment P W q v z hqtop hv hwindow hW
  intro i j
  let r : Fin (n + 1) := ⟨(commonCoreTopFinEquiv a i).val, by
    have := (commonCoreTopFinEquiv a i).isLt; omega⟩
  let s : Fin (n + 1) := ⟨a + (commonCoreFinEquiv b j).val, by
    have := (commonCoreFinEquiv b j).isLt; omega⟩
  let sj : Fin (n + 1) := ⟨(commonCoreFinEquiv b j).val, by
    have := (commonCoreFinEquiv b j).isLt; omega⟩
  let rA : Fin (m + 1) := ⟨r.val, by have := r.isLt; omega⟩
  let sA : Fin (m + 1) := ⟨a + (commonCoreFinEquiv b j).val, by
    have := (commonCoreFinEquiv b j).isLt; omega⟩
  have hP := originalProfileFrame_entry_of_val P a b 0 (by omega)
    (.inl i) (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inl j))) r s
    (by rfl) (commonCoreFiniteCols_core a b 0 j)
  have hU := originalProfileFrame_entry_of_val A a b a (by omega)
    (.inl i) (commonCoreColumnEquiv (Fin a) (Fin b) (Fin a) (.inr (.inl j))) rA sA
    (by rfl) (commonCoreFiniteCols_core a b a j)
  have hx := (hends r).1
  change A.xi rA = P.xi r + q at hx
  have hz := (hends sj).2
  have hs : (⟨m - n + sj.val, by have := sj.isLt; omega⟩ : Fin (m + 1)) = sA := by
    apply Fin.ext
    change m - n + sj.val = sA.val
    dsimp only [sj, sA]
    omega
  rw [hs] at hz
  have hb := hbeta (commonCoreFinEquiv b j)
  have hi : (⟨n - (b + 1) + (commonCoreFinEquiv b j).val, by
      have := (commonCoreFinEquiv b j).isLt; omega⟩ : Fin (n + 1)) = s := by
    apply Fin.ext
    change n - (b + 1) + (commonCoreFinEquiv b j).val = s.val
    dsimp only [s]
    omega
  rw [hi] at hb
  change P.zeta sj = P.zeta s + q at hb
  rw [hU, hP, hx, hz, hb, add_sub_add_right_eq_sub]

end SkewCornerDescent.Matrix.SelectedCoordinate
