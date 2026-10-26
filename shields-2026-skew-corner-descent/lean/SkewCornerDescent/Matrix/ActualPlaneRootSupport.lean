/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowPlaneLabels
import SkewCornerDescent.Matrix.OriginalWindowClassInclusion
import SkewCornerDescent.SignedRationalRootSupport

/-!
# Actual rational-plane class labels in the signed support

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The original internal occurrence counts identify each active class with its
signed support coefficient after the produced closure-orientation sign.
No matching of independently substituted response values is used. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

noncomputable local instance actualPlaneSupportRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The signed support coefficient at an actual active class's rational
label is its original source/window exponent, including negative counts. -/
theorem original_class_label_signed_exponent {n m t : ℕ}
    (P : Profile n) (W : Profile m) (Q : Profile t)
    (middle : Fin (originalSelectedCount (hD := hD) Q + 1))
    (a b : ℕ) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (label : c.OriginalResponseClass P → ℚ) (e : ℚ → ℤ)
    (hcounts : ∀ α, e α =
      (a : ℤ) * (Finset.univ.filter fun i =>
        c.regularResidue (c.originalHessenbergResponse Q middle middle) -
            (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
          c.originalInternalResidue P i).card -
      (b : ℤ) * (Finset.univ.filter fun i =>
        c.regularResidue (c.originalHessenbergResponse Q middle middle) -
            (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
          c.originalInternalResidue W i).card)
    (X : c.OriginalResponseClass P)
    (hlabel : X.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
      (label X : OtherField c.top) * c.originalTrueCapProduct P) :
    e ((δ : ℚ) * label X) = c.originalResponseClassExponent P W a b X := by
  classical
  have hd : (δ : ℚ) * (δ : ℚ) = 1 := by
    rcases hδ with rfl | rfl <;> norm_num
  have hscalar : (δ : ℚ) * ((δ : ℚ) * label X) = label X := by
    rw [← mul_assoc, hd, one_mul]
  have hc := hcounts ((δ : ℚ) * label X)
  simp only [hscalar, ← hlabel] at hc
  have hP : (Finset.univ.filter fun i => X.val = c.originalInternalResidue P i) =
      (Finset.univ.filter fun i => c.originalInternalResidue P i = X.val) := by
    apply Finset.filter_congr
    intro i _
    exact eq_comm
  have hW : (Finset.univ.filter fun i => X.val = c.originalInternalResidue W i) =
      (Finset.univ.filter fun i => c.originalInternalResidue W i = X.val) := by
    apply Finset.filter_congr
    intro i _
    exact eq_comm
  rw [hP, hW] at hc
  exact hc

/-- Every actual class with nonzero original signed exponent belongs to the
produced signed support at its orientation-adjusted rational label. -/
theorem original_active_class_label_mem_support {n m t : ℕ}
    (P : Profile n) (W : Profile m) (Q : Profile t)
    (middle : Fin (originalSelectedCount (hD := hD) Q + 1))
    (a b : ℕ) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (label : c.OriginalResponseClass P → ℚ) (s : Finset ℚ) (e : ℚ → ℤ)
    (hs : ∀ α, α ∈ s ↔ e α ≠ 0)
    (hcounts : ∀ α, e α =
      (a : ℤ) * (Finset.univ.filter fun i =>
        c.regularResidue (c.originalHessenbergResponse Q middle middle) -
            (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
          c.originalInternalResidue P i).card -
      (b : ℤ) * (Finset.univ.filter fun i =>
        c.regularResidue (c.originalHessenbergResponse Q middle middle) -
            (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
          c.originalInternalResidue W i).card)
    (X : c.OriginalResponseClass P)
    (hX : c.originalResponseClassExponent P W a b X ≠ 0)
    (hlabel : X.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
      (label X : OtherField c.top) * c.originalTrueCapProduct P) :
    (δ : ℚ) * label X ∈ s := by
  apply (hs _).mpr
  rw [c.original_class_label_signed_exponent P W Q middle a b δ hδ label e hcounts X hlabel]
  exact hX

/-- Every retained signed support point comes from an actual original active
class. Complete literal window restriction supplies negative-only occurrences;
the actual nonzero cap product then identifies the orientation-adjusted label. -/
theorem original_signed_support_label_exists {n m t : ℕ}
    (P : Profile n) (W : Profile m) (Q : Profile t)
    (middle : Fin (originalSelectedCount (hD := hD) Q + 1))
    (q : ℤ) (v : ℤ × ℤ)
    (hW : W.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcut : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (a b : ℕ) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (label : c.OriginalResponseClass P → ℚ) (s : Finset ℚ) (e : ℚ → ℤ)
    (hs : ∀ α, α ∈ s ↔ e α ≠ 0)
    (hcounts : ∀ α, e α =
      (a : ℤ) * (Finset.univ.filter fun i =>
        c.regularResidue (c.originalHessenbergResponse Q middle middle) -
            (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
          c.originalInternalResidue P i).card -
      (b : ℤ) * (Finset.univ.filter fun i =>
        c.regularResidue (c.originalHessenbergResponse Q middle middle) -
            (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
          c.originalInternalResidue W i).card)
    (hlabels : ∀ X, c.originalResponseClassExponent P W a b X ≠ 0 →
      X.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
        (label X : OtherField c.top) * c.originalTrueCapProduct P)
    (α : ℚ) (hα : α ∈ s) :
    ∃ X : c.OriginalResponseClass P, c.originalResponseClassExponent P W a b X ≠ 0 ∧
      α = (δ : ℚ) * label X := by
  classical
  let x := c.regularResidue (c.originalHessenbergResponse Q middle middle) -
    (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P
  have hc := hcounts α
  have hP : (Finset.univ.filter fun i => x = c.originalInternalResidue P i) =
      (Finset.univ.filter fun i => c.originalInternalResidue P i = x) := by
    apply Finset.filter_congr
    intro i _
    exact eq_comm
  have hW' : (Finset.univ.filter fun i => x = c.originalInternalResidue W i) =
      (Finset.univ.filter fun i => c.originalInternalResidue W i = x) := by
    apply Finset.filter_congr
    intro i _
    exact eq_comm
  change e α = (a : ℤ) * (Finset.univ.filter fun i => x = c.originalInternalResidue P i).card -
    (b : ℤ) * (Finset.univ.filter fun i => x = c.originalInternalResidue W i).card at hc
  rw [hP, hW'] at hc
  have hexp : c.originalResponseValueExponent P W a b x ≠ 0 := by
    change (a : ℤ) * (Finset.univ.filter fun i => c.originalInternalResidue P i = x).card -
      (b : ℤ) * (Finset.univ.filter fun i => c.originalInternalResidue W i = x).card ≠ 0
    rw [← hc]
    exact (hs α).mp hα
  have hm : x ∈ c.originalResponseClasses P := by
    by_cases hi : ∃ i, c.originalInternalResidue P i = x
    · obtain ⟨i, he⟩ := hi
      exact he ▸ c.originalInternalResidue_mem_classes P i
    · have hpempty : (Finset.univ.filter fun i => c.originalInternalResidue P i = x) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro i hmem
        exact hi ⟨i, (Finset.mem_filter.mp hmem).2⟩
      have hwcount : (Finset.univ.filter fun i => c.originalInternalResidue W i = x).card ≠ 0 := by
        intro hz
        apply hexp
        simp only [originalResponseValueExponent, hpempty, Finset.card_empty, Nat.cast_zero,
          hz, mul_zero, sub_self]
      obtain ⟨i, hmem⟩ := Finset.card_ne_zero.mp hwcount
      exact (Finset.mem_filter.mp hmem).2 ▸
        c.originalWindow_internal_residue_mem_classes P W q v hW hcut i
  let X : c.OriginalResponseClass P := ⟨x, hm⟩
  have hX : c.originalResponseClassExponent P W a b X ≠ 0 := hexp
  refine ⟨X, hX, ?_⟩
  have hl := hlabels X hX
  change c.regularResidue (c.originalHessenbergResponse Q middle middle) -
      (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
    c.regularResidue (c.originalHessenbergResponse Q middle middle) -
      (label X : OtherField c.top) * c.originalTrueCapProduct P at hl
  have hmul := sub_right_injective hl
  have hfield : (((δ : ℚ) * α : ℚ) : OtherField c.top) = (label X : OtherField c.top) :=
    mul_right_cancel₀ (c.originalTrueCapProduct_ne_zero P hB hmax) hmul
  have hrat : (δ : ℚ) * α = label X := by exact_mod_cast hfield
  have hd : (δ : ℚ) * (δ : ℚ) = 1 := by
    rcases hδ with rfl | rfl <;> norm_num
  calc
    α = (δ : ℚ) * ((δ : ℚ) * α) := by rw [← mul_assoc, hd, one_mul]
    _ = (δ : ℚ) * label X := congrArg ((δ : ℚ) * ·) hrat

/-- Two produced rational labels of the same actual class agree because the
actual full cap product is nonzero. This compares the residue classifier's
choice with the inverse-projection label choice at their consuming seam. -/
theorem original_plane_labels_eq {n t : ℕ}
    (P : Profile n) (Q : Profile t)
    (middle : Fin (originalSelectedCount (hD := hD) Q + 1))
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (X : c.OriginalResponseClass P) (α β : ℚ)
    (hα : X.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
      (α : OtherField c.top) * c.originalTrueCapProduct P)
    (hβ : X.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
      (β : OtherField c.top) * c.originalTrueCapProduct P) : α = β := by
  have hm := sub_right_injective (hα.symm.trans hβ)
  have hfield : (α : OtherField c.top) = (β : OtherField c.top) :=
    mul_right_cancel₀ (c.originalTrueCapProduct_ne_zero P hB hmax) hm
  exact_mod_cast hfield

end SkewCornerDescent.Matrix.SelectedCoordinate
