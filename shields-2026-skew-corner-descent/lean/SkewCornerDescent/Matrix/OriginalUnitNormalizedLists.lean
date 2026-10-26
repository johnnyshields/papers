/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitSetExtremes

/-!
# Whole original unit lists in their normalized beta frames

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Every original nonselected row and column is identified with its actual
normalized component coordinate. Finite index casts retain the entire source
list and its true endpoint translation.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The complete original incoming row list is the entire normalized unit
component row list in its actual beta frame, with no omitted positions. -/
theorem original_unit_row_distances_normalized {n : ℕ} (P : Profile n)
    (a : OriginalSelectedBlocks (hD := hD) P) (u : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ) :
    originalUnitRowDistances P a u = Finset.univ.image
      (fun i : Fin (interiorBlockLength P u.val + 1) =>
        P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
          ((interiorBlockProfile P u.val hne).xi i + originalComponentTau P u)) := by
  classical
  have hsize : originalRemovedSize (hD := hD) P u = interiorBlockLength P u.val + 1 := by
    simp only [originalRemovedSize, ite_eq_right hu]
  unfold originalUnitRowDistances
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨k, _, hkz⟩ := Finset.mem_image.mp hz
    let i := Fin.cast hsize k
    have hi : originalUnitIndex P u hu i = k := by apply Fin.ext; rfl
    have hb := (original_unit_component_beta P u hu hne i).1
    rw [hi] at hb
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rw [← hb]
    exact hkz
  · intro z hz
    obtain ⟨i, _, hiz⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨originalUnitIndex P u hu i, Finset.mem_univ _, ?_⟩
    change _ - P.xi (originalRemovedRow P u (originalUnitIndex P u hu i)).succ = z
    rw [(original_unit_component_beta P u hu hne i).1]
    exact hiz

/-- The complete original outgoing column list has the same exact normalized
component interpretation, retaining its original endpoint translation. -/
theorem original_unit_col_distances_normalized {n : ℕ} (P : Profile n)
    (d : OriginalSelectedBlocks (hD := hD) P) (u : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ) :
    originalUnitColDistances P d u = Finset.univ.image
      (fun i : Fin (interiorBlockLength P u.val + 1) =>
        (interiorBlockProfile P u.val hne).zeta i + originalComponentTau P u -
          P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))) := by
  classical
  have hsize : originalRemovedSize (hD := hD) P u = interiorBlockLength P u.val + 1 := by
    simp only [originalRemovedSize, ite_eq_right hu]
  unfold originalUnitColDistances
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨k, _, hkz⟩ := Finset.mem_image.mp hz
    let i := Fin.cast hsize k
    have hi : originalUnitIndex P u hu i = k := by apply Fin.ext; rfl
    have hb := (original_unit_component_beta P u hu hne i).2
    rw [hi] at hb
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rw [← hb]
    exact hkz
  · intro z hz
    obtain ⟨i, _, hiz⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨originalUnitIndex P u hu i, Finset.mem_univ _, ?_⟩
    change P.zeta (originalRemovedCol P u (originalUnitIndex P u hu i)).castSucc - _ = z
    rw [(original_unit_component_beta P u hu hne i).2]
    exact hiz

end SkewCornerDescent.Matrix.SelectedCoordinate
