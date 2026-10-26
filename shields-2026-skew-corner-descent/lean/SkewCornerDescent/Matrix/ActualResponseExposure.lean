/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.RealResponseChart

/-!
# Exposure supplied by complete original response elimination

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

A finite actual retained-response family is partitioned by its literal top indices.
Complete original-matrix elimination supplies every rational correction. Distinct
same-top residue classes then admit either prescribed real exposure sign.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual retained responses, not assumed abstract triangular functions, admit either exposure. -/
theorem originalResponses_exposure {ι : Type*} [Finite ι]
    (n : ι → ℕ) (P : ∀ i, Profile (n i))
    (b d : ∀ i, Option (OriginalSelectedBlocks (hD := hD) (P i)))
    (top : ι → ℕ+) (htop : ∀ i, c.top < top i)
    (hindices : ∀ i, (P i).xi (originalRowSplitEquiv (hD := hD) (P i) (.inl (b i))) -
      (P i).zeta (originalColSplitEquiv (hD := hD) (P i) (.inl (d i))) = (top i : ℤ))
    (hmax : ∀ i C, C ∈ edgeComponents (diagramInterior (P i).cells) →
      span C ≤ (c.top : ℕ))
    (K : ℕ+) (hanchor : ∃ i, top i = K)
    (hdistinct : ∀ i j, top i = K → top j = K → i ≠ j →
      c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) ≠
        c.regularResidue (c.originalLocalResponse (P j) (b j) (d j)))
    (positive : Bool) :
    ∃ p q : ι → OtherPolynomial c.top,
      (∀ i j, j ∈ (realResiduePolynomial c.top (p i)).vars → j < (top i : ℕ)) ∧
      (∀ i j, j ∈ (realResiduePolynomial c.top (q i)).vars → j < (c.top : ℕ)) ∧
      (∀ i, q i ≠ 0) ∧
      (∀ i, c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) =
        residueGenerator c.top ⟨top i, ne_of_gt (htop i)⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (p i) /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) (q i)) ∧
      ∃ (y : ℕ → ℝ) (a : ι), top a = K ∧
        (∀ i, MvPolynomial.eval y (realResiduePolynomial c.top (q i)) ≠ 0) ∧
        rationalTriangularResponse (K : ℕ) (realResiduePolynomial c.top (p a))
          (realResiduePolynomial c.top (q a)) y = 0 ∧
        ∀ i, i ≠ a → responseSign positive
          (rationalTriangularResponse (top i : ℕ) (realResiduePolynomial c.top (p i))
            (realResiduePolynomial c.top (q i)) y) := by
  classical
  obtain ⟨p, q, hp, hq, hq0, hqreal, he⟩ :=
    c.originalResponses_real_representatives n P b d top htop hindices hmax
  let lo := {i : ι // top i < K}
  let hi := {i : ι // K < top i}
  let anchors := {i : ι // top i = K}
  obtain ⟨i0, hi0⟩ := hanchor
  let _ : Nonempty anchors := ⟨⟨i0, hi0⟩⟩
  have hNK : c.top < K := hi0 ▸ htop i0
  let rp := fun i => realResiduePolynomial c.top (p i)
  let rq := fun i => realResiduePolynomial c.top (q i)
  have hap : ∀ a : anchors, ∀ j ∈ (rp a.val).vars, j < (K : ℕ) := by
    intro a j hj
    simpa only [a.property] using hp a.val j hj
  have hdiff : ∀ a b : anchors, a ≠ b →
      rp a.val * rq b.val - rp b.val * rq a.val ≠ 0 := by
    intro a z haz
    have hai : a.val ≠ z.val := fun he => haz (Subtype.ext he)
    apply c.originalResponses_real_cross_difference K hNK
      (p a.val) (q a.val) (p z.val) (q z.val) (hq0 a.val) (hq0 z.val)
    · simpa only [a.property] using he a.val
    · simpa only [z.property] using he z.val
    · exact hdistinct a.val z.val a.property z.property hai
  obtain ⟨y, a, hlowq, hhighq, hanchorq, hzero, hlow, hhigh, hother⟩ :=
    exists_rational_exposure (lo := lo) (hi := hi) (α := anchors)
      (c.top : ℕ) (K : ℕ) hNK.le
      (fun i => (top i.val : ℕ)) (fun i => (top i.val : ℕ))
      (fun i => rp i.val) (fun i => rq i.val)
      (fun i => rp i.val) (fun i => rq i.val)
      (fun i => rp i.val) (fun i => rq i.val)
      (fun i => ⟨(htop i.val).le, i.property⟩) (fun i => i.property)
      (fun i => hp i.val) (fun i => hq i.val) (fun i => hqreal i.val)
      (fun i => hp i.val) (fun i => hq i.val) (fun i => hqreal i.val)
      hap (fun i => hq i.val) (fun i => hqreal i.val) hdiff positive
  refine ⟨p, q, hp, hq, hq0, he, y, a.val, a.property, ?_, hzero, ?_⟩
  · intro i
    rcases lt_trichotomy (top i) K with h | h | h
    · exact hlowq ⟨i, h⟩
    · exact hanchorq ⟨i, h⟩
    · exact hhighq ⟨i, h⟩
  · intro i hia
    rcases lt_trichotomy (top i) K with h | h | h
    · exact hlow ⟨i, h⟩
    · have hi' : (⟨i, h⟩ : anchors) ≠ a := fun he => hia (congrArg Subtype.val he)
      simpa only [h] using hother ⟨i, h⟩ hi'
    · exact hhigh ⟨i, h⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
