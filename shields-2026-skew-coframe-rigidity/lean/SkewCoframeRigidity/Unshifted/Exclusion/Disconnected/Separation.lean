/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Extract

/-!
# Strict separation of the two end components

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner): the least column `A` of the top strict component
of `V` and the least column `B` of the top strict component of its rotation satisfy `A + B > M`.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- A cut of a diagram transfers to the same cut position of its rotation, reversed. -/
theorem isCut_rot {V W : BetaDiagram (n + 1)} {c0 : ℤ} (hr : ∀ i, W.row i = c0 - V.col i.rev)
    (hc : ∀ i, W.col i = c0 - V.row i.rev) {c : Fin n} (hcV : IsCut V c) :
    ∃ hc' : n - c.val < n, IsCut W ⟨n - c.val, hc'⟩ := by
  obtain ⟨j, hj, hlt⟩ := hcV
  have hc1 : 1 ≤ c.val := by omega
  have hcn := c.isLt
  refine ⟨by omega, ⟨n - c.val - 1, by omega⟩, by simp; omega, ?_⟩
  rw [hr, hc]
  have e1 : (Fin.succ (⟨n - c.val, by omega⟩ : Fin n)).rev = Fin.castSucc j := by
    ext; simp [Fin.val_rev]; omega
  have e2 : (Fin.castSucc (⟨n - c.val - 1, by omega⟩ : Fin n)).rev = c.succ := by
    ext; simp [Fin.val_rev]; omega
  rw [e1, e2]
  omega

/-- The first cut after the top block. -/
theorem top_cut (D : BetaDiagram (n + 1)) (hDn : D.col (Fin.last n) = 0) (cnt : ℕ)
    (hb : ∀ i : Fin n, blockIdx D i = 0 ↔ i.val < cnt) (hcnt : 0 < cnt) (hlt : cnt < n) :
    IsCut D ⟨cnt, hlt⟩ ∧ rowPos D ⟨cnt, hlt⟩ < colPos D ⟨cnt - 1, by omega⟩ := by
  have h1 : blockIdx D ⟨cnt - 1, by omega⟩ = 0 := (hb _).mpr (by simp; omega)
  have h2 : blockIdx D ⟨cnt, hlt⟩ ≠ 0 := fun e => by have := (hb _).mp e; simp at this
  obtain ⟨c, hjc, hcc, hcut⟩ := exists_cut_of_blockIdx_lt D (i := ⟨cnt, hlt⟩) (j := ⟨cnt - 1, by omega⟩)
    (by omega)
  have hceq : c = ⟨cnt, hlt⟩ := by
    apply Fin.ext
    have a := Fin.lt_def.mp hjc
    have b := Fin.le_iff_val_le_val.mp hcc
    simp only [Fin.val_mk] at a b ⊢
    omega
  subst hceq
  refine ⟨hcut, ?_⟩
  obtain ⟨j, hj, hlt'⟩ := hcut
  have hjeq : j = ⟨cnt - 1, by omega⟩ := Fin.ext (by simp only [Fin.val_mk] at hj ⊢; omega)
  rw [hjeq] at hlt'
  have a := rowPos_cast D ⟨cnt, hlt⟩
  have b := colPos_cast D ⟨cnt - 1, by omega⟩
  rw [hDn] at a b
  have : (rowPos D ⟨cnt, hlt⟩ : ℤ) < colPos D ⟨cnt - 1, by omega⟩ := by omega
  exact_mod_cast this

/-- The two least columns satisfy `A + B > M`. -/
theorem separation {V W : BetaDiagram (n + 1)} {c0 : ℤ} (hr : ∀ i, W.row i = c0 - V.col i.rev)
    (hc : ∀ i, W.col i = c0 - V.row i.rev) (hVn : V.col (Fin.last n) = 0)
    (hWn : W.col (Fin.last n) = 0) (cV cW : ℕ)
    (hbV : ∀ i : Fin n, blockIdx V i = 0 ↔ i.val < cV)
    (hbW : ∀ i : Fin n, blockIdx W i = 0 ↔ i.val < cW) (hcV : 0 < cV) (hcW : 0 < cW)
    (hcWn : cW ≤ n) (hlt : cV < n) :
    span V < colPos V ⟨cV - 1, by omega⟩ + colPos W ⟨cW - 1, by omega⟩ ∧ cW + cV ≤ n := by
  obtain ⟨hcutV, hrow⟩ := top_cut V hVn cV hbV hcV hlt
  obtain ⟨hc', hcutW⟩ := isCut_rot hr hc hcutV
  simp only [Fin.val_mk] at hc' hcutW
  have hcW' : cW ≤ n - cV := by
    by_contra hcon
    have h1 : blockIdx W ⟨n - cV - 1, by omega⟩ = 0 := (hbW _).mpr (by simp; omega)
    have h2 : blockIdx W ⟨n - cV, hc'⟩ = 0 := (hbW _).mpr (by simp; omega)
    have := blockIdx_lt_of_cut W (i := ⟨n - cV - 1, by omega⟩) (j := ⟨n - cV, hc'⟩)
      (c := ⟨n - cV, hc'⟩) (by rw [Fin.lt_def]; simp; omega) le_rfl hcutW
    omega
  have hmono : colPos W ⟨n - cV - 1, by omega⟩ ≤ colPos W ⟨cW - 1, by omega⟩ := by
    have a := colPos_cast W ⟨n - cV - 1, by omega⟩
    have b := colPos_cast W ⟨cW - 1, by omega⟩
    have := W.col_strictAnti.antitone (show (⟨cW - 1, by omega⟩ : Fin n).castSucc ≤
      (⟨n - cV - 1, by omega⟩ : Fin n).castSucc from by
        rw [Fin.castSucc_le_castSucc_iff, Fin.le_iff_val_le_val]; simp; omega)
    have : (colPos W ⟨n - cV - 1, by omega⟩ : ℤ) ≤ colPos W ⟨cW - 1, by omega⟩ := by omega
    exact_mod_cast this
  have hrot := colPos_rot hc hWn ⟨n - cV - 1, by omega⟩
  have hrev : (⟨n - cV - 1, by omega⟩ : Fin n).rev = ⟨cV, hlt⟩ := by
    ext; simp [Fin.val_rev]; omega
  rw [hrev] at hrot
  have := rowPos_lt_span V ⟨cV, hlt⟩
  exact ⟨by omega, by omega⟩

end SkewCoframeRigidity.Unshifted
