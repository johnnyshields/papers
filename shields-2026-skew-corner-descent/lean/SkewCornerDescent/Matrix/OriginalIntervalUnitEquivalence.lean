/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIntervalUnitMatrices

/-!
# Complete index equivalence for an actual interval prefix and unit component

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Every original interval index through the current full block is either in the
known prefix or in that complete component. The actual nonselection size and
endpoint containment supply the bijection, without assuming a partition or inverse match.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Exact actual indices of all complete interval blocks through the current block. -/
abbrev OriginalIntervalThroughUnit {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P) :=
  {j : OriginalResponseInterval (hD := hD) P b d // j.1.1.1 ≤ u}

/-- Prefix/current interval indexing is injective, including across their original block seam. -/
theorem originalIntervalUnitPrefixIndex_injective {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d) :
    Function.Injective (originalIntervalUnitPrefixIndex P b d u hs hu) := by
  rintro (i | i) (j | j) he
  · have h : i.val = j.val := he
    exact congrArg Sum.inl (Subtype.ext h)
  · have h := congrArg (fun z : OriginalResponseInterval (hD := hD) P b d => z.1.1.1) he
    change i.val.1.1.1 = u at h
    exact False.elim ((ne_of_lt i.property) h)
  · have h := congrArg (fun z : OriginalResponseInterval (hD := hD) P b d => z.1.1.1) he
    change u = j.val.1.1.1 at h
    exact False.elim ((ne_of_lt j.property) h.symm)
  · have h := congrArg (fun z : OriginalResponseInterval (hD := hD) P b d => z.1.1.2.val) he
    change i.val = j.val at h
    exact congrArg Sum.inr (Fin.ext h)

/-- Every actual interval index in a block through the current block is reached by the
complete prefix/current map; current-block indices are transported by their genuine full size. -/
theorem originalIntervalUnitPrefixIndex_surjective_through {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d)
    (j : OriginalResponseInterval (hD := hD) P b d) (hj : j.1.1.1 ≤ u) :
    ∃ i, originalIntervalUnitPrefixIndex P b d u hs hu i = j := by
  by_cases hlt : j.1.1.1 < u
  · exact ⟨.inl ⟨j, hlt⟩, rfl⟩
  · rcases j with ⟨⟨⟨z, k⟩, hupper⟩, hlower⟩
    change z ≤ u at hj
    change ¬z < u at hlt
    have he : z = u := le_antisymm hj (le_of_not_gt hlt)
    subst z
    have hsize : originalRemovedSize (hD := hD) P u = interiorBlockLength P u.val + 1 := by
      simp only [originalRemovedSize, ite_eq_right hs]
    let i : Fin (interiorBlockLength P u.val + 1) := Fin.cast hsize k
    refine ⟨.inr i, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (⟨u, originalUnitIndex P u hs i⟩ : OriginalRemainingIndices (hD := hD) P) = ⟨u, k⟩
    rfl

/-- The complete actual prefix/current index map is a proved equivalence with all interval
blocks through the current one. No retained index or endpoint is supplied as matching data. -/
def originalIntervalUnitPrefixEquiv {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d) :
    OriginalIntervalUnitPrefix (hD := hD) P b d u ⊕ Fin (interiorBlockLength P u.val + 1) ≃
      OriginalIntervalThroughUnit (hD := hD) P b d u :=
  Equiv.ofBijective
    (fun i => ⟨originalIntervalUnitPrefixIndex P b d u hs hu i, by
      cases i with
      | inl i => exact i.property.le
      | inr i => exact le_rfl⟩)
    ⟨by
      intro i j he
      exact originalIntervalUnitPrefixIndex_injective P b d u hs hu (congrArg Subtype.val he),
    by
      intro j
      obtain ⟨i, hi⟩ :=
        originalIntervalUnitPrefixIndex_surjective_through P b d u hs hu j.val j.property
      exact ⟨i, Subtype.ext hi⟩⟩

/-- Complete actual indices from the current block through the interval's end. -/
abbrev OriginalIntervalFromUnit {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P) :=
  {j : OriginalResponseInterval (hD := hD) P b d // u ≤ j.1.1.1}

/-- The current/suffix index map is injective across its genuine original block seam. -/
theorem originalIntervalUnitSuffixIndex_injective {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d) :
    Function.Injective (originalIntervalUnitSuffixIndex P b d u hs hu) := by
  rintro (i | i) (j | j) he
  · have h := congrArg (fun z : OriginalResponseInterval (hD := hD) P b d => z.1.1.2.val) he
    change i.val = j.val at h
    exact congrArg Sum.inl (Fin.ext h)
  · have h := congrArg (fun z : OriginalResponseInterval (hD := hD) P b d => z.1.1.1) he
    change u = j.val.1.1.1 at h
    exact False.elim ((ne_of_gt j.property) h.symm)
  · have h := congrArg (fun z : OriginalResponseInterval (hD := hD) P b d => z.1.1.1) he
    change i.val.1.1.1 = u at h
    exact False.elim ((ne_of_gt i.property) h)
  · have h : i.val = j.val := he
    exact congrArg Sum.inr (Subtype.ext h)

/-- The full nonselected size supplies every current-block index in the suffix domain. -/
theorem originalIntervalUnitSuffixIndex_surjective_from {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d)
    (j : OriginalResponseInterval (hD := hD) P b d) (hj : u ≤ j.1.1.1) :
    ∃ i, originalIntervalUnitSuffixIndex P b d u hs hu i = j := by
  by_cases hlt : u < j.1.1.1
  · exact ⟨.inr ⟨j, hlt⟩, rfl⟩
  · rcases j with ⟨⟨⟨z, k⟩, hupper⟩, hlower⟩
    change u ≤ z at hj
    change ¬u < z at hlt
    have he : z = u := le_antisymm (le_of_not_gt hlt) hj
    subst z
    have hsize : originalRemovedSize (hD := hD) P u = interiorBlockLength P u.val + 1 := by
      simp only [originalRemovedSize, ite_eq_right hs]
    let i : Fin (interiorBlockLength P u.val + 1) := Fin.cast hsize k
    refine ⟨.inl i, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (⟨u, originalUnitIndex P u hs i⟩ : OriginalRemainingIndices (hD := hD) P) = ⟨u, k⟩
    rfl

/-- Every actual interval index from the current block is supplied by the complete
current/suffix map, not by an assumed list or matching inverse. -/
def originalIntervalUnitSuffixEquiv {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d) :
    Fin (interiorBlockLength P u.val + 1) ⊕ OriginalIntervalUnitSuffix (hD := hD) P b d u ≃
      OriginalIntervalFromUnit (hD := hD) P b d u :=
  Equiv.ofBijective
    (fun i => ⟨originalIntervalUnitSuffixIndex P b d u hs hu i, by
      cases i with
      | inl i => exact le_rfl
      | inr i => exact i.property.le⟩)
    ⟨by
      intro i j he
      exact originalIntervalUnitSuffixIndex_injective P b d u hs hu (congrArg Subtype.val he),
    by
      intro j
      obtain ⟨i, hi⟩ :=
        originalIntervalUnitSuffixIndex_surjective_from P b d u hs hu j.val j.property
      exact ⟨i, Subtype.ext hi⟩⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
