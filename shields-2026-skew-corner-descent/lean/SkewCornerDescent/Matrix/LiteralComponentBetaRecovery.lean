/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.ProfileCells
import Mathlib.Data.Finset.Sort

/-!
# Literal component recovery from complete translated beta sets

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Both
original beta sets recover the row count, translation parameter, and literal
normalized cells, without any assumed Schur-function equality. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Complete translated row and column beta sets recover the literal normalized
component and its actual translation, not merely a Schur-equivalence class. -/
theorem literal_component_of_beta_sets {n m : ℕ} (P : Profile n) (Q : Profile m)
    (τ υ : ℤ)
    (hrows : Finset.univ.image (fun i => P.xi i + τ) =
      Finset.univ.image (fun j => Q.xi j + υ))
    (hcols : Finset.univ.image (fun i => P.zeta i + τ) =
      Finset.univ.image (fun j => Q.zeta j + υ)) :
    n = m ∧ τ = υ ∧ P.cells = Q.cells := by
  have hτ : τ ∈ Finset.univ.image (fun i => P.zeta i + τ) :=
    Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, by rw [P.zeta_last, zero_add]⟩
  have hυ : υ ∈ Finset.univ.image (fun j => Q.zeta j + υ) :=
    Finset.mem_image.mpr ⟨Fin.last m, Finset.mem_univ _, by rw [Q.zeta_last, zero_add]⟩
  rw [hcols] at hτ
  rw [← hcols] at hυ
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hτ
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hυ
  have hzi := P.zeta_nonneg i
  have hzj := Q.zeta_nonneg j
  have hshift : τ = υ := by omega
  have hP : Function.Injective (fun i => P.xi i + τ) := by
    intro i j he
    exact P.xi_strictAnti.injective (add_right_cancel he)
  have hQ : Function.Injective (fun j => Q.xi j + υ) := by
    intro i j he
    exact Q.xi_strictAnti.injective (add_right_cancel he)
  have hcard := congrArg Finset.card hrows
  rw [Finset.card_image_of_injective _ hP, Finset.card_image_of_injective _ hQ,
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at hcard
  have hnm : n = m := by omega
  refine ⟨hnm, hshift, ?_⟩
  subst m
  rw [← hshift] at hrows hcols
  have hrows' : Finset.univ.image P.xi = Finset.univ.image Q.xi := by
    have h := congrArg (Finset.image (fun z : ℤ => z - τ)) hrows
    simpa only [Finset.image_image, Function.comp_def, add_sub_cancel_right] using h
  have hcols' : Finset.univ.image P.zeta = Finset.univ.image Q.zeta := by
    have h := congrArg (Finset.image (fun z : ℤ => z - τ)) hcols
    simpa only [Finset.image_image, Function.comp_def, add_sub_cancel_right] using h
  have hrowRange : Set.range P.xi = Set.range Q.xi := by
    have h := congrArg (fun s : Finset ℤ => (s : Set ℤ)) hrows'
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using h
  have hcolRange : Set.range P.zeta = Set.range Q.zeta := by
    have h := congrArg (fun s : Finset ℤ => (s : Set ℤ)) hcols'
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using h
  have hxi : P.xi = Q.xi :=
    (P.xi_strictAnti.range_inj_of_wellFoundedLT Q.xi_strictAnti).mp hrowRange
  have hzeta : P.zeta = Q.zeta :=
    (P.zeta_strictAnti.range_inj_of_wellFoundedLT Q.zeta_strictAnti).mp hcolRange
  have hprofile : P = Q := by
    apply Profile.ext
    · funext i
      have h := P.xi_sub_zeta i
      rw [hxi, hzeta] at h
      exact_mod_cast h.symm.trans (Q.xi_sub_zeta i)
    · funext i
      have h := P.xi_succ_sub_zeta_castSucc i
      rw [hxi, hzeta] at h
      exact_mod_cast h.symm.trans (Q.xi_succ_sub_zeta_castSucc i)
  exact congrArg Profile.cells hprofile

end SkewCornerDescent.Matrix
