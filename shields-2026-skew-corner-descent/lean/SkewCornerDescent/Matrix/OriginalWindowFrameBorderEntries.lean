/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowFrameCore

/-!
# Compatible original end-window border entries

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). Complete literal windows produce the starting-endpoint
alignment and both unchanged border vectors of the original matrices. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- Congruent complete end windows produce the raw starting beta correspondence.
The content shift is retained; no endpoint period is an input. -/
theorem originalWindow_zeta_alignment {n k : ℕ} (P : Profile n) (W : Profile k)
    (q : ℤ) (v z : ℤ × ℤ) (hqtop : q < P.xi 0) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q)) :
    ∃ h : k ≤ n, ∀ j : Fin k,
      P.zeta ⟨j.val, by have := j.isLt; omega⟩ =
        P.zeta ⟨n - k + j.val, by have := j.isLt; omega⟩ + q := by
  obtain ⟨hn, _, _, hz0⟩ := originalWindow_row_alignment P W q v z hqtop hwindow hW
  have hlower : W.cells = translate (-z) (P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q)) := by
    rw [← hW, translate_translate, neg_add_cancel, translate_zero]
  have hupper : W.cells = translate (-(v + z)) (P.cells.filter
      (fun x => q ≤ content x ∧ content x < P.xi 0)) := by
    rw [hwindow, ← hW, translate_translate, translate_translate,
      add_assoc, neg_add_cancel, translate_zero]
  obtain ⟨_, hl⟩ := originalLiteralWindow_lower_zeta P W (P.xi 0 - q) (-z) (by omega) hlower
  obtain ⟨_, hu⟩ := originalLiteralWindow_upper_core_zeta P W q (-(v + z)) hqtop hupper
  have hc : content (-(v + z)) = -q := by
    dsimp only [content, Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add] at hz0 hv ⊢
    omega
  refine ⟨hn, ?_⟩
  intro j
  have hleft := hl j.castSucc
  change W.zeta j.castSucc = P.zeta ⟨n - k + j.val, by have := j.isLt; omega⟩ at hleft
  have hright := hu j
  rw [hc] at hright
  omega

/-- The last column adjacent to the lower-window core is the unchanged literal
window's last column, including every ordinary unit boundary entry. -/
theorem originalLowerWindow_frame_last {n : ℕ} (P : Profile n) (a b : ℕ)
    (W : Profile (b + 1)) (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : W.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi))
    (hsize : n = a + (b + 1)) :
    ∀ i : Unit ⊕ Fin b,
      originalProfileFrame P a b 0 (by omega) (.inr (.inl i))
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inr (.inl ())))) =
      originalProfileFrame W 0 b 0 (by omega) (.inr (.inl i))
        (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0) (.inr (.inr (.inl ())))) := by
  obtain ⟨hn, hx⟩ := originalLiteralWindow_lower_core_xi P W hi v hhi hwindow
  intro i
  let r : Fin (n + 1) := ⟨n - (b + 1) + (commonCoreFinEquiv b i).val + 1, by
    have := (commonCoreFinEquiv b i).isLt; omega⟩
  have hP := originalProfileFrame_entry_of_val P a b 0 (by omega)
    (.inr (.inl i))
    (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inr (.inl ()))))
    r (Fin.last n) (by
      have he := commonCoreFiniteRows_core a b 0 i
      dsimp only [r]
      omega) (by
      have he := commonCoreFiniteCols_border a b 0 (.inl ())
      change (commonCoreFiniteCols a b 0
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inr (.inl ()))))).val = n
      change (commonCoreFiniteCols a b 0
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inr (.inl ()))))).val =
        a + (b + 1) + 0 at he
      omega)
  have hW' := originalProfileFrame_entry_of_val W 0 b 0 (by omega)
    (.inr (.inl i))
    (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0) (.inr (.inr (.inl ()))))
    (commonCoreFinEquiv b i).succ (Fin.last (b + 1)) (by
      have he := commonCoreFiniteRows_core 0 b 0 i
      change (commonCoreFiniteRows 0 b 0 (.inr (.inl i))).val = (commonCoreFinEquiv b i).val + 1
      omega) (by
      have he := commonCoreFiniteCols_border 0 b 0 (.inl ())
      change (commonCoreFiniteCols 0 b 0
        (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0) (.inr (.inr (.inl ()))))).val = b + 1
      change (commonCoreFiniteCols 0 b 0
        (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0) (.inr (.inr (.inl ()))))).val =
        0 + (b + 1) + 0 at he
      omega)
  have hxi := hx (commonCoreFinEquiv b i)
  change W.xi (commonCoreFinEquiv b i).succ = P.xi r at hxi
  rw [hP, hW', P.zeta_last, W.zeta_last, hxi]

/-- The first row adjacent to the upper-window core is the unchanged literal
window's first row. The common content translation cancels entrywise. -/
theorem originalUpperWindow_frame_first {n : ℕ} (P : Profile n) (a b : ℕ)
    (W : Profile (b + 1)) (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : W.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0))
    (hsize : n = a + (b + 1)) :
    ∀ j : Unit ⊕ Fin b,
      originalProfileFrame P 0 b a (by omega) (.inl (.inr ()))
        (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j))) =
      originalProfileFrame W 0 b 0 (by omega) (.inl (.inr ()))
        (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0) (.inr (.inl j))) := by
  have ht := originalLiteralWindow_upper_top P W lo v hlo hwindow
  obtain ⟨hn, hz⟩ := originalLiteralWindow_upper_core_zeta P W lo v hlo hwindow
  intro j
  let s : Fin (n + 1) := ⟨(commonCoreFinEquiv b j).val, by
    have := (commonCoreFinEquiv b j).isLt; omega⟩
  have hP := originalProfileFrame_entry_of_val P 0 b a (by omega)
    (.inl (.inr ()))
    (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j)))
    0 s (commonCoreFiniteRows_top 0 b a) (by
      simpa only [Nat.zero_add, s] using commonCoreFiniteCols_core 0 b a j)
  have hW' := originalProfileFrame_entry_of_val W 0 b 0 (by omega)
    (.inl (.inr ()))
    (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin 0) (.inr (.inl j)))
    0 (commonCoreFinEquiv b j).castSucc (commonCoreFiniteRows_top 0 b 0) (by
      simpa only [Nat.zero_add, Fin.val_castSucc] using commonCoreFiniteCols_core 0 b 0 j)
  have hζ := hz (commonCoreFinEquiv b j)
  change W.zeta (commonCoreFinEquiv b j).castSucc = P.zeta s + content v at hζ
  rw [hP, hW', ht, hζ, add_sub_add_right_eq_sub]

end SkewCornerDescent.Matrix.SelectedCoordinate
