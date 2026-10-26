/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowActiveClasses
import SkewCornerDescent.SignedRationalFactors
import SkewCornerDescent.TranscendentalRationalFunctions

/-!
# Rational factors in the original horizontal-closure coordinate

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`). The
actual residue ratio factors uniquely in the original transcendental coordinate `β / f²`,
with distinct rational labels, nonzero integer exponents, signed degree `d`, and unit `±1`.
Both the cap normalization and the closure orientation sign are produced from
the actual matrices. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

noncomputable local instance windowRationalFactorsRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Exact standing residue dependence has the paper's signed rational factorization
in the original coordinate, not merely in a separately normalized monic plane. -/
theorem originalWindow_rational_factorization {n k m : ℕ}
    (P : Profile n) (W : Profile k) (H : Profile m) (q : ℤ) (v z h : ℤ × ℤ)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hH : originalHorizontalClosure P = translate h H.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hQ : ∀ C ∈ edgeComponents (diagramInterior W.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a d : ℕ) (hd : d + a = b)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin k => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p t : Polynomial ℚ) (hpt : IsCoprime p t)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) t) :
    let middle : Fin (originalSelectedCount (hD := hD) H + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P H h hH]; omega⟩
    Transcendental ℚ (c.residueMap H.schur / c.residueMap P.schur ^ 2) ∧
    (∀ p₁ q₁ p₂ q₂ : Polynomial ℚ, q₁ ≠ 0 → q₂ ≠ 0 →
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁ /
          Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) q₁ =
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₂ /
          Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) q₂ →
      p₁ * q₂ = p₂ * q₁) ∧
    ∃ ε δ : ℤ, ∃ s : Finset ℚ, ∃ e : ℚ → ℤ,
      (δ = 1 ∨ δ = -1) ∧
      (ε = 1 ∨ ε = -1) ∧ (∀ α ∈ s, e α ≠ 0) ∧ (∑ α ∈ s, e α) = d ∧
      (∀ α, α ∈ s ↔ e α ≠ 0) ∧
      (∀ α, e α =
        (a : ℤ) * (Finset.univ.filter fun i =>
          c.regularResidue (c.originalHessenbergResponse H middle middle) -
              (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
            c.originalInternalResidue P i).card -
        (b : ℤ) * (Finset.univ.filter fun i =>
          c.regularResidue (c.originalHessenbergResponse H middle middle) -
              (((δ : ℚ) * α : ℚ) : OtherField c.top) * c.originalTrueCapProduct P =
            c.originalInternalResidue W i).card) ∧
      (c.regularResidue (c.originalHessenbergResponse H middle middle) /
        c.originalTrueCapProduct P =
          (δ : OtherField c.top) * (c.residueMap H.schur / c.residueMap P.schur ^ 2)) ∧
      c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
        (ε : OtherField c.top) * ∏ α ∈ s,
          (c.residueMap H.schur / c.residueMap P.schur ^ 2 -
            (α : OtherField c.top)) ^ e α := by
  dsimp only
  obtain ⟨hB, _⟩ := c.originalWindow_true_cap_product P W q v z hwindow hW hcutq hcutLq hC
  obtain ⟨ε, s, e, htrans, hε, he, hdegree, hsupport, hcounts, hfactor, _⟩ :=
    (c.originalWindow_active_classes P W H q v z h hwindow hW hH hcutq hcutLq hC hP hQ
      Λ b a d hd hKU hKW p t hpt hdep).2
  obtain ⟨δ, hδ, hquot⟩ := c.originalHorizontalClosure_residue_quotient P H h hH hB hP
  have hcoord : c.regularResidue (c.originalHessenbergResponse H
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P H h hH]; omega⟩
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P H h hH]; omega⟩) /
        c.originalTrueCapProduct P =
      (δ : OtherField c.top) * (c.residueMap H.schur / c.residueMap P.schur ^ 2) := by
    rcases hδ with rfl | rfl
    · simpa only [Int.cast_one, one_mul] using hquot.symm
    · simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_div] at hquot ⊢
      linear_combination hquot
  have htransOriginal : Transcendental ℚ
      (c.residueMap H.schur / c.residueMap P.schur ^ 2) := by
    have hδQ : (δ : ℚ) ≠ 0 := by rcases hδ with rfl | rfl <;> norm_num
    have ht := htrans.aeval (Polynomial.C (δ : ℚ) * Polynomial.X)
      (by rw [Polynomial.natDegree_C_mul_X _ hδQ]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero hδQ)
    simpa only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      map_intCast, mul_div_assoc, hquot] using ht
  refine ⟨htransOriginal, ?_, ?_⟩
  · intro p₁ q₁ p₂ q₂ hq₁ hq₂ heq
    exact transcendental_rational_representation_unique htransOriginal p₁ q₁ p₂ q₂
      hq₁ hq₂ heq
  · obtain ⟨ε', s', e', hε', he', hdegree', hexp, hs', hfactor'⟩ :=
      signedRationalFactors_change_coordinate _ _ _ ε δ s e d hε hδ he hdegree
        hfactor hcoord
    refine ⟨ε', δ, s', e', hδ, hε', he', hdegree', ?_, ?_, hcoord, hfactor'⟩
    · intro α
      rw [hs', hexp, hsupport]
    · intro α
      rw [hexp]
      exact hcounts _

end SkewCornerDescent.Matrix.SelectedCoordinate
