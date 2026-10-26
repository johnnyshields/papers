/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitComponentBeta
import SkewCornerDescent.Matrix.UnitVertexGeometry

/-!
# Full original prefix and suffix matrices around a unit component

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
All earlier and later remaining indices are retained, including zero-gap pivots.
The full original submatrices and the strict beta separation are produced from
actual component order; no diagonal-only matrix or endpoint matching is assumed.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Every surviving index in a component strictly earlier than the current one. -/
abbrev OriginalUnitPrefix {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :=
  {j : OriginalRemainingIndices (hD := hD) P // j.1 < b}

/-- Every surviving index in a component strictly later than the current one. -/
abbrev OriginalUnitSuffix {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :=
  {j : OriginalRemainingIndices (hD := hD) P // b < j.1}

/-- Original rows of any surviving index, including selected proper-minor rows. -/
def originalRemainingRowBeta {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) : ℤ :=
  P.xi (originalRemovedRow (hD := hD) P j.1 j.2).succ

/-- Original columns of any surviving index, including selected proper-minor columns. -/
def originalRemainingColBeta {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) : ℤ :=
  P.zeta (originalRemovedCol (hD := hD) P j.1 j.2).castSucc

/-- Strict component order produces a strict lower-left beta separation. -/
theorem original_remaining_beta_separated {n : ℕ} (P : Profile n)
    (b d : OriginalBlocks P) (hdb : d < b)
    (i : Fin (originalRemovedSize (hD := hD) P b))
    (j : Fin (originalRemovedSize (hD := hD) P d)) :
    originalRemainingRowBeta P ⟨b, i⟩ < originalRemainingColBeta P ⟨d, j⟩ := by
  have hle := interiorBlock_mono P (show d.val ≤ b.val from hdb.le)
  have hne : interiorBlock P d.val ≠ interiorBlock P b.val := by
    intro he
    exact (ne_of_lt hdb) (originalBlocks_label_injective P he)
  have hlt : interiorBlock P d.val < interiorBlock P b.val := lt_of_le_of_ne hle hne
  have hr := originalRemovedRow_block (hD := hD) P b i
  have hc := originalRemovedCol_block (hD := hD) P d j
  obtain ⟨k, hk, hjk, hki⟩ := exists_interiorCut_of_block_lt P
    (originalRemovedRow (hD := hD) P b i) (originalRemovedCol (hD := hD) P d j)
    (by rw [hr, hc]; exact hlt)
  have hb := (Finset.mem_filter.mp hk).2.2
  have hx := P.xi_strictAnti.antitone
    (show k.succ ≤ (originalRemovedRow (hD := hD) P b i).succ by
      change k.val + 1 ≤ (originalRemovedRow (hD := hD) P b i).val + 1
      exact Nat.add_le_add_right (Fin.le_def.mp hki) 1)
  have hz := P.zeta_strictAnti.antitone
    (show (originalRemovedCol (hD := hD) P d j).castSucc ≤ (previousIndex k).castSucc by
      change (originalRemovedCol (hD := hD) P d j).val ≤ k.val - 1
      have h := Fin.lt_def.mp hjk
      omega)
  change P.xi (originalRemovedRow (hD := hD) P b i).succ <
    P.zeta (originalRemovedCol (hD := hD) P d j).castSucc
  omega

/-- The complete normalized current component is strictly below every actual prefix column. -/
theorem original_unit_prefix_separation {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ)
    (i : Fin (interiorBlockLength P b.val + 1)) (j : OriginalUnitPrefix (hD := hD) P b) :
    (interiorBlockProfile P b.val hne).xi i + originalComponentTau P b <
      originalRemainingColBeta P j.val := by
  rw [← (original_unit_component_beta P b hs hne i).1]
  exact original_remaining_beta_separated P b j.val.1 j.property _ _

/-- Every actual suffix row is strictly below every normalized current component column. -/
theorem original_unit_suffix_separation {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ)
    (i : Fin (interiorBlockLength P b.val + 1)) (j : OriginalUnitSuffix (hD := hD) P b) :
    originalRemainingRowBeta P j.val <
      (interiorBlockProfile P b.val hne).zeta i + originalComponentTau P b := by
  rw [← (original_unit_component_beta P b hs hne i).2]
  exact original_remaining_beta_separated P j.val.1 b j.property _ _

/-- Literal original indices of the complete prefix together with the current full component. -/
def originalUnitPrefixIndex {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b) :
    OriginalUnitPrefix (hD := hD) P b ⊕ Fin (interiorBlockLength P b.val + 1) →
      OriginalRemainingIndices (hD := hD) P :=
  Sum.elim Subtype.val (fun i => ⟨b, originalUnitIndex P b hs i⟩)

/-- Literal original indices of the current full component together with its complete suffix. -/
def originalUnitSuffixIndex {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b) :
    Fin (interiorBlockLength P b.val + 1) ⊕ OriginalUnitSuffix (hD := hD) P b →
      OriginalRemainingIndices (hD := hD) P :=
  Sum.elim (fun i => ⟨b, originalUnitIndex P b hs i⟩) Subtype.val

/-- The complete original prefix/current matrix is the consumer's full beta matrix.
Every cross-component entry is retained under the literal index map. -/
theorem original_unit_prefix_matrix {R : Type*} [CommRing R] (φ : Lambda →+* R)
    {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ) :
    ((originalRemovedMatrix (hD := hD) P).map φ).submatrix
      (originalUnitPrefixIndex P b hs) (originalUnitPrefixIndex P b hs) =
    vertexBetaMatrix φ
      (Sum.elim (fun j : OriginalUnitPrefix (hD := hD) P b => originalRemainingRowBeta P j.val)
        (fun i => (interiorBlockProfile P b.val hne).xi i + originalComponentTau P b))
      (Sum.elim (fun j : OriginalUnitPrefix (hD := hD) P b => originalRemainingColBeta P j.val)
        (fun i => (interiorBlockProfile P b.val hne).zeta i + originalComponentTau P b)) := by
  have hx i := (original_unit_component_beta P b hs hne i).1
  have hz i := (original_unit_component_beta P b hs hne i).2
  ext i j : 1
  cases i <;> cases j <;>
    simp only [Matrix.submatrix_apply, Matrix.map_apply, originalRemovedMatrix, Matrix.of_apply,
      originalUnitPrefixIndex, vertexBetaMatrix, Sum.elim_inl, Sum.elim_inr,
      originalRemainingRowBeta, originalRemainingColBeta, hx, hz]

/-- The complete current/suffix matrix is the consumer's full beta matrix.
No later-block coupling is dropped or replaced by a fresh submatrix inverse. -/
theorem original_unit_suffix_matrix {R : Type*} [CommRing R] (φ : Lambda →+* R)
    {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ) :
    ((originalRemovedMatrix (hD := hD) P).map φ).submatrix
      (originalUnitSuffixIndex P b hs) (originalUnitSuffixIndex P b hs) =
    vertexBetaMatrix φ
      (Sum.elim (fun i => (interiorBlockProfile P b.val hne).xi i + originalComponentTau P b)
        (fun j : OriginalUnitSuffix (hD := hD) P b => originalRemainingRowBeta P j.val))
      (Sum.elim (fun i => (interiorBlockProfile P b.val hne).zeta i + originalComponentTau P b)
        (fun j : OriginalUnitSuffix (hD := hD) P b => originalRemainingColBeta P j.val)) := by
  have hx i := (original_unit_component_beta P b hs hne i).1
  have hz i := (original_unit_component_beta P b hs hne i).2
  ext i j : 1
  cases i <;> cases j <;>
    simp only [Matrix.submatrix_apply, Matrix.map_apply, originalRemovedMatrix, Matrix.of_apply,
      originalUnitSuffixIndex, vertexBetaMatrix, Sum.elim_inl, Sum.elim_inr,
      originalRemainingRowBeta, originalRemainingColBeta, hx, hz]

end SkewCornerDescent.Matrix.SelectedCoordinate
