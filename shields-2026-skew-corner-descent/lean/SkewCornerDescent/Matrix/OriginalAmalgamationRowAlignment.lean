/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowRowAlignment
import SkewCornerDescent.Matrix.OriginalAmalgamationWindows

/-!
# Literal amalgamation row and beta alignment

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). The complete union windows produce the actual row count,
normalization displacement, and the unaltered prefix/suffix beta endpoints.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- The literal overlap union determines its normalization row and its full row
count. No amalgamation size or normalization coordinate is supplied. -/
theorem originalAmalgamation_row_alignment {n k m : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hqtop : q < P.xi 0) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells) :
    n ≤ m ∧ k ≤ n ∧ m = n + (n - k) ∧ u.1 = v.1 ∧ content u = 0 := by
  obtain ⟨hk, _, hvrow, _⟩ := originalWindow_row_alignment P W q v z hqtop hwindow hW
  obtain ⟨hlo, hhi⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  obtain ⟨hu, hwidth⟩ := originalAmalgamation_profile_extrema P A q v u hq hv hA
  have hpos : 0 < P.xi 0 := by
    have hr := P.r_pos 0
    have hz := P.zeta_nonneg 0
    have he := P.xi_sub_zeta 0
    omega
  obtain ⟨hn, hrow⟩ := originalLiteralWindow_lower_row_offset A P (A.xi 0 - q) u
    (by omega) hlo.symm
  have hupper : P.cells = translate (u - v) (A.cells.filter
      (fun x => q ≤ content x ∧ content x < A.xi 0)) := by
    apply translate_injective v
    rw [translate_translate, show v + (u - v) = u by
      ext <;> dsimp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega]
    exact hhi.symm
  have hrow' := (originalLiteralWindow_upper_row_offset A P q (u - v)
    (by omega) hupper).2
  simp only [Prod.fst_sub] at hrow'
  exact ⟨hn, hk, by omega, by omega, hu⟩

/-- The source copies determine every amalgamation prefix ending endpoint and
suffix starting endpoint. The full content shift is retained. -/
theorem originalAmalgamation_prefix_xi_suffix_zeta {n m : ℕ}
    (P : Profile n) (A : Profile m) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells) :
    ∃ h : n ≤ m, ∀ j : Fin (n + 1),
      A.xi ⟨j.val, by have := j.isLt; omega⟩ = P.xi j + q ∧
      A.zeta ⟨m - n + j.val, by have := j.isLt; omega⟩ = P.zeta j := by
  obtain ⟨hlo, hhi⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  obtain ⟨hu, hwidth⟩ := originalAmalgamation_profile_extrema P A q v u hq hv hA
  have hpos : 0 < P.xi 0 := by
    have hr := P.r_pos 0
    have hz := P.zeta_nonneg 0
    have he := P.xi_sub_zeta 0
    omega
  have hupper : P.cells = translate (u - v) (A.cells.filter
      (fun x => q ≤ content x ∧ content x < A.xi 0)) := by
    apply translate_injective v
    rw [translate_translate, show v + (u - v) = u by
      ext <;> dsimp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega]
    exact hhi.symm
  obtain ⟨hn, hz⟩ := originalLiteralWindow_lower_zeta A P (A.xi 0 - q) u
    (by omega) hlo.symm
  obtain ⟨_, hx⟩ := originalLiteralWindow_upper_endpoints A P q (u - v) (by omega) hupper
  have hc : content (u - v) = -q := by
    dsimp only [content, Prod.fst_sub, Prod.snd_sub] at hu hv ⊢
    omega
  refine ⟨hn, ?_⟩
  intro j
  have he := (hx j).2
  rw [hc] at he
  exact ⟨by omega, (hz j).symm⟩

/-- The complete source windows also produce the other two core endpoint
families. Strict profile ordering removes clipping without assuming a union cut. -/
theorem originalAmalgamation_suffix_xi_prefix_zeta {n m : ℕ}
    (P : Profile n) (A : Profile m) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells) :
    ∃ h : n ≤ m, ∀ j : Fin n,
      A.xi ⟨m - n + j.val + 1, by have := j.isLt; omega⟩ = P.xi j.succ ∧
      A.zeta ⟨j.val, by have := j.isLt; omega⟩ = P.zeta j.castSucc + q := by
  obtain ⟨hlo, hhi⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  obtain ⟨hu, hwidth⟩ := originalAmalgamation_profile_extrema P A q v u hq hv hA
  have hpos : 0 < P.xi 0 := by
    have hr := P.r_pos 0
    have hz := P.zeta_nonneg 0
    have he := P.xi_sub_zeta 0
    omega
  have hupper : P.cells = translate (u - v) (A.cells.filter
      (fun x => q ≤ content x ∧ content x < A.xi 0)) := by
    apply translate_injective v
    rw [translate_translate, show v + (u - v) = u by
      ext <;> dsimp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega]
    exact hhi.symm
  obtain ⟨hn, hx⟩ := originalLiteralWindow_lower_core_xi A P (A.xi 0 - q) u
    (by omega) hlo.symm
  obtain ⟨_, hz⟩ := originalLiteralWindow_upper_core_zeta A P q (u - v) (by omega) hupper
  have hc : content (u - v) = -q := by
    dsimp only [content, Prod.fst_sub, Prod.snd_sub] at hu hv ⊢
    omega
  refine ⟨hn, ?_⟩
  intro j
  have he := hz j
  rw [hc] at he
  exact ⟨(hx j).symm, by omega⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
