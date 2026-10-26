/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowRemainingOccurrences

/-!
# Whole-window containment between actual source blocks

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). A complete window
contains every whole block between two of its actual occurrences, including all empty
unit pivots and selected boundary proper minors. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Last positions of canonical original blocks follow their first-position order. -/
theorem originalBlocks_last_mono {n : ℕ} (P : Profile n) :
    Monotone (fun b : OriginalBlocks P => interiorBlockLast P b.val) := by
  intro b d hbd
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hf := interiorBlockFirst_le_last P d.val
  rw [d.property] at hf
  have he := interiorBlock_interval P (show b.val ≤ d.val from hbd)
    (le_trans hf hlt.le)
    ((mem_interiorBlockFiber P b.val _).mp (interiorBlockLast_mem P b.val)).symm
  have hdb := originalBlocks_label_injective P he
  subst d
  exact (lt_irrefl _) hlt

namespace SelectedCoordinate

/-- A nonempty complete block's literal cell bounds are its original endpoint bounds. -/
theorem originalBlock_window_bounds {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (b : OriginalBlocks P) (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hband : ∀ x ∈ interiorBlockCells P b.val, lo ≤ content x ∧ content x < hi) :
    lo ≤ P.zeta (interiorBlockLast P b.val).castSucc ∧ P.xi b.val.succ ≤ hi := by
  have hl := (mem_interiorBlockFiber P b.val _).mp (interiorBlockLast_mem P b.val)
  have hne := interior_block_row_nonempty P hb hl
  have hleft : (((interiorBlockLast P b.val : Fin n) : ℤ),
      P.zeta (interiorBlockLast P b.val).castSucc + interiorBlockLast P b.val) ∈
      interiorBlockCells P b.val :=
    (mem_interiorBlockCells P b.val _ _).mpr ⟨_, hl, rfl, le_rfl, by omega⟩
  have hright : ((b.val : ℤ), P.xi b.val.succ + b.val - 1) ∈
      interiorBlockCells P b.val :=
    (mem_interiorBlockCells P b.val _ _).mpr ⟨b.val, rfl, rfl, by omega, by omega⟩
  have hlb := hband _ hleft
  have hrb := hband _ hright
  dsimp only [content] at hlb hrb
  omega

/-- Whole-window membership always supplies the weak source endpoint bounds. -/
theorem originalBlockInWindow_bounds {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (b : OriginalBlocks P) (hb : originalBlockInWindow P lo hi b) :
    lo ≤ P.zeta (interiorBlockLast P b.val).castSucc ∧ P.xi b.val.succ ≤ hi := by
  rcases hb with ⟨hne, hband⟩ | ⟨he, hl, hh⟩
  · exact originalBlock_window_bounds P lo hi b hne hband
  · rw [(interior_empty_block_extremes P b.val he).2]
    exact ⟨hl.le, hh.le⟩

/-- All whole blocks between two actual window occurrences stay in the same complete window. -/
theorem originalBlockInWindow_between {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (b a d : OriginalBlocks P) (hb : originalBlockInWindow P lo hi b)
    (hd : originalBlockInWindow P lo hi d) (hba : b ≤ a) (had : a ≤ d) :
    originalBlockInWindow P lo hi a := by
  have hbb := originalBlockInWindow_bounds P lo hi b hb
  have hdd := originalBlockInWindow_bounds P lo hi d hd
  have hlu := originalBlocks_last_mono P had
  have hzl := P.zeta_strictAnti.antitone (show
    (interiorBlockLast P a.val).castSucc ≤ (interiorBlockLast P d.val).castSucc from hlu)
  have hxu := P.xi_strictAnti.antitone (Fin.succ_le_succ_iff.mpr
    (show b.val ≤ a.val from hba))
  have hlo : lo ≤ P.zeta (interiorBlockLast P a.val).castSucc := le_trans hdd.1 hzl
  have hhi : P.xi a.val.succ ≤ hi := le_trans hxu hbb.2
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
    have haLast := (interior_empty_block_extremes P a.val he).2
    rw [haLast] at hlo
    refine Or.inr ⟨he, ?_, ?_⟩
    · by_cases had' : a = d
      · subst d
        rcases hd with ⟨hn, _⟩ | ⟨_, hl, _⟩
        · omega
        · exact hl
      · have haLt : a.val < d.val := (show a < d from lt_of_le_of_ne had had')
        have hlast := interiorBlockFirst_le_last P d.val
        rw [d.property] at hlast
        have hfin : a.val < interiorBlockLast P d.val := lt_of_lt_of_le haLt hlast
        have hs := P.zeta_strictAnti (show a.val.castSucc <
          (interiorBlockLast P d.val).castSucc from hfin)
        exact lt_of_le_of_lt hdd.1 hs
    · by_cases hba' : b = a
      · subst b
        rcases hb with ⟨hn, _⟩ | ⟨_, _, hh⟩
        · omega
        · exact hh
      · have hbLt : b.val < a.val := (show b < a from lt_of_le_of_ne hba hba')
        have hs := P.xi_strictAnti (Fin.succ_lt_succ_iff.mpr hbLt)
        exact lt_of_lt_of_le hs hbb.2

end SelectedCoordinate
end SkewCornerDescent.Matrix
