/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroCutReassembly

/-!
# Actual beta supports under whole-profile rotation

The orientation transport used in `lem:total-contraction-inverse` of
`shields-2026-skew-class-inflation.tex`.  Whole-profile rotation exchanges
and reflects the two complete normalized beta supports and preserves
Hessenberg thickness.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Staircase

private theorem image_fin_reverse {A : Type*} [DecidableEq A] {n : ℕ} (f : Fin n → A) :
    Finset.univ.image (fun i : Fin n => f i.rev) = Finset.univ.image f := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, by rw [Fin.rev_rev]⟩

/-- Rotation reflects the complete column support into the complete upper support. -/
theorem profile_rotate_rowSet {n : ℕ} (P : Profile n) :
    P.rotate.toBetaDiagram.rowSet =
      P.toBetaDiagram.colSet.image (fun x => P.xi 0 - x) := by
  change Finset.univ.image P.rotate.xi = _
  rw [P.xi_rotate_zeta_rotate.1]
  change Finset.univ.image (fun i : Fin (n + 1) => P.xi 0 - P.zeta i.rev) =
    (Finset.univ.image P.zeta).image (fun x => P.xi 0 - x)
  rw [Finset.image_image]
  exact image_fin_reverse (fun i : Fin (n + 1) => P.xi 0 - P.zeta i)

/-- The same reflection exchanges the complete upper support with the rotated columns. -/
theorem profile_rotate_colSet {n : ℕ} (P : Profile n) :
    P.rotate.toBetaDiagram.colSet =
      P.toBetaDiagram.rowSet.image (fun x => P.xi 0 - x) := by
  change Finset.univ.image P.rotate.zeta = _
  rw [P.xi_rotate_zeta_rotate.2]
  change Finset.univ.image (fun i : Fin (n + 1) => P.xi 0 - P.xi i.rev) =
    (Finset.univ.image P.xi).image (fun x => P.xi 0 - x)
  rw [Finset.image_image]
  exact image_fin_reverse (fun i : Fin (n + 1) => P.xi 0 - P.xi i)

/-- Reversing both actual profile words preserves every local thickness inequality. -/
theorem profile_rotate_thick {n : ℕ} (P : Profile n) (hP : Thick P) : Thick P.rotate := by
  intro j k hjk
  have hv : j.val + 1 = k.val := by
    have hh := congrArg Fin.val hjk
    simpa only [Fin.val_succ, Fin.val_castSucc] using hh
  have hrev : k.rev.succ = j.rev.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_rev, Fin.val_castSucc]
    have hj := j.isLt
    have hk := k.isLt
    omega
  have hrow : k.rev.succ = j.succ.rev := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_rev]
    have hj := j.isLt
    have hk := k.isLt
    omega
  have hh := hP k.rev j.rev hrev
  rw [hrow] at hh
  change P.g j.rev + P.g k.rev < P.r j.succ.rev
  omega

end SkewClassInflation
