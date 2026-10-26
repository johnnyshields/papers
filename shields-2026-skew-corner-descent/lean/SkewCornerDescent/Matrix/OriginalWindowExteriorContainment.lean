/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowConvexity

/-!
# Complete actual exterior-cap blocks lie in their end windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). An actual
selected endpoint in an end window keeps every whole block between it and the true
exterior endpoint inside that same window, including empty unit pivots. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Actual endpoint bounds give the complete cell band; empty pivots require strict bounds. -/
theorem originalBlockInWindow_of_endpoint_bounds {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (a : OriginalBlocks P)
    (hlo : lo ≤ P.zeta (interiorBlockLast P a.val).castSucc)
    (hhi : P.xi a.val.succ ≤ hi)
    (hunit : P.xi a.val.succ = P.zeta a.val.castSucc →
      lo < P.zeta a.val.castSucc ∧ P.xi a.val.succ < hi) :
    originalBlockInWindow P lo hi a := by
  by_cases hne : P.zeta a.val.castSucc < P.xi a.val.succ
  · refine Or.inl ⟨hne, ?_⟩
    intro x hx
    rcases x with ⟨r, s⟩
    obtain ⟨i, hl, hr, hleft, hright⟩ := (mem_interiorBlockCells P a.val r s).mp hx
    have hib := (mem_interiorBlockFiber_iff P a.val i).mp
      ((mem_interiorBlockFiber P a.val i).mpr hl)
    rw [a.property] at hib
    have hzi := P.zeta_strictAnti.antitone (show i.castSucc ≤
      (interiorBlockLast P a.val).castSucc from hib.2)
    have hxi := P.xi_strictAnti.antitone (Fin.succ_le_succ_iff.mpr hib.1)
    dsimp only [content]
    omega
  · have he : P.xi a.val.succ = P.zeta a.val.castSucc := by
      have hg := P.zeta_le_xi_succ a.val
      omega
    exact Or.inr ⟨he, hunit he⟩

/-- Every actual block up to a selected upper-window endpoint remains in its complete window. -/
theorem originalBlockInWindow_before_selected {n : ℕ} (P : Profile n) (lo : ℤ)
    (b : OriginalSelectedBlocks (hD := hD) P) (a : OriginalBlocks P)
    (hb : originalBlockInWindow P lo (P.xi 0) b.val) (hab : a ≤ b.val) :
    originalBlockInWindow P lo (P.xi 0) a := by
  have hbb := originalBlockInWindow_bounds P lo (P.xi 0) b.val hb
  have hlu := originalBlocks_last_mono P hab
  have hzl := P.zeta_strictAnti.antitone (show
    (interiorBlockLast P a.val).castSucc ≤ (interiorBlockLast P b.val.val).castSucc from hlu)
  have htop : P.xi a.val.succ < P.xi 0 :=
    P.xi_strictAnti (by change (0 : ℕ) < a.val.val + 1; omega)
  apply originalBlockInWindow_of_endpoint_bounds P lo (P.xi 0) a
    (hbb.1.trans hzl) htop.le
  intro he
  have hab' : a < b.val := by
    apply lt_of_le_of_ne hab
    intro heq
    have hs := originalBlockSelected_nonempty P b.val b.property
    rw [← heq] at hs
    omega
  have hlast := interiorBlockFirst_le_last P b.val.val
  rw [b.val.property] at hlast
  have hfin : a.val < interiorBlockLast P b.val.val := lt_of_lt_of_le hab' hlast
  have hs := P.zeta_strictAnti (show a.val.castSucc <
    (interiorBlockLast P b.val.val).castSucc from hfin)
  exact ⟨hbb.1.trans_lt hs, htop⟩

/-- Every actual block after a selected lower-window endpoint remains in its complete window. -/
theorem originalBlockInWindow_after_selected {n : ℕ} (P : Profile n) (hi : ℤ)
    (b : OriginalSelectedBlocks (hD := hD) P) (a : OriginalBlocks P)
    (hb : originalBlockInWindow P 0 hi b.val) (hba : b.val ≤ a) :
    originalBlockInWindow P 0 hi a := by
  have hbb := originalBlockInWindow_bounds P 0 hi b.val hb
  have hxu := P.xi_strictAnti.antitone (Fin.succ_le_succ_iff.mpr
    (show b.val.val ≤ a.val from hba))
  have hbottom : 0 < P.zeta (interiorBlockLast P a.val).castSucc := by
    have h := P.zeta_strictAnti (show (interiorBlockLast P a.val).castSucc < Fin.last n from
      by change (interiorBlockLast P a.val).val < n; exact (interiorBlockLast P a.val).isLt)
    rw [P.zeta_last] at h
    exact h
  apply originalBlockInWindow_of_endpoint_bounds P 0 hi a hbottom.le (hxu.trans hbb.2)
  intro he
  have hba' : b.val < a := by
    apply lt_of_le_of_ne hba
    intro heq
    have hs := originalBlockSelected_nonempty P b.val b.property
    rw [heq] at hs
    omega
  have hs := P.xi_strictAnti (Fin.succ_lt_succ_iff.mpr
    (show b.val.val < a.val from hba'))
  have heLast := (interior_empty_block_extremes P a.val he).2
  rw [heLast] at hbottom
  exact ⟨by omega, hs.trans_le hbb.2⟩

/-- Every complete original block lies strictly between the actual normalized exterior bounds. -/
theorem originalBlockInWindow_full_profile {n : ℕ} (P : Profile n) (a : OriginalBlocks P) :
    originalBlockInWindow P 0 (P.xi 0) a := by
  have htop : P.xi a.val.succ < P.xi 0 :=
    P.xi_strictAnti (by change (0 : ℕ) < a.val.val + 1; omega)
  have hbottom : 0 < P.zeta (interiorBlockLast P a.val).castSucc := by
    have h := P.zeta_strictAnti (show (interiorBlockLast P a.val).castSucc < Fin.last n from
      by change (interiorBlockLast P a.val).val < n; exact (interiorBlockLast P a.val).isLt)
    rw [P.zeta_last] at h
    exact h
  apply originalBlockInWindow_of_endpoint_bounds P 0 (P.xi 0) a hbottom.le htop.le
  intro he
  have heLast := (interior_empty_block_extremes P a.val he).2
  rw [heLast] at hbottom
  exact ⟨by omega, htop⟩

/-- Enlarging a complete window preserves every whole block, including its strict unit bounds. -/
theorem originalBlockInWindow_mono {n : ℕ} (P : Profile n) (lo hi lo' hi' : ℤ)
    (a : OriginalBlocks P) (ha : originalBlockInWindow P lo hi a)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : originalBlockInWindow P lo' hi' a := by
  rcases ha with ⟨hne, hband⟩ | ⟨he, hl, hh⟩
  · refine Or.inl ⟨hne, fun x hx => ?_⟩
    have h := hband x hx
    exact ⟨hlo.trans h.1, h.2.trans_le hhi⟩
  · exact Or.inr ⟨he, hlo.trans_lt hl, hh.trans_le hhi⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
