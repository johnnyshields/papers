/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/MarkFacts/Positivity.lean
import SkewMarkedFactor.Gluing.CellSchurTableau
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MarkFacts.Translate

/-!
# Positivity of the skew Schur function of a skew diagram

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
the paragraph on profiles: the function `s_X` of a skew diagram `X` is the generating function
of semistandard tableaux of the shape `X`, so at the all-ones alphabet in enough variables it
is a positive number.  Consequently `s_X ≠ 0`, and `s_X + s_{X'} ≠ 0` for skew `X`, `X'`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan.MarkFacts

open Shields

/-- A skew diagram in the quadrant: every skew diagram has a translate in the quadrant. -/
theorem exists_translate_nonneg (X : Diagram) :
    ∃ t : ℤ × ℤ, ∀ x ∈ translate t X, 0 ≤ x.1 ∧ 0 ≤ x.2 := by
  obtain ⟨m1, hm1⟩ := Finset.exists_le (X.image fun x => -x.1)
  obtain ⟨m2, hm2⟩ := Finset.exists_le (X.image fun x => -x.2)
  refine ⟨(m1, m2), fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have h1 := hm1 (-y.1) (Finset.mem_image_of_mem (fun x : ℤ × ℤ => -x.1) hy)
  have h2 := hm2 (-y.2) (Finset.mem_image_of_mem (fun x : ℤ × ℤ => -x.2) hy)
  exact ⟨by simp only [Prod.fst_add]; omega, by simp only [Prod.snd_add]; omega⟩

/-- **The skew Schur function of a skew diagram is positive at the all-ones alphabet**, once
the alphabet has at least as many variables as the diagram has rows. -/
theorem exists_aeval_cellSchur_pos {X : Diagram} (hX : IsSkew X) :
    ∃ C : ℕ, ∀ n : ℕ, C ≤ n →
      0 < MvPolynomial.aeval (fun k : ℕ+ => Shields.completeHom n k (fun _ => (1 : ℝ)))
        (cellSchur X) := by
  obtain ⟨t, ht⟩ := exists_translate_nonneg X
  obtain ⟨lam, mu, hmu, hX'⟩ := exists_young_pair_of_isSkew (isSkew_translate t hX) ht
  refine ⟨lam.colLen 0, fun n hn => ?_⟩
  rw [← cellSchur_translate t X, ← hX', aeval_cellSchur_skewDiagram_all hmu]
  refine skewSchur_pos (fun _ _ => one_pos) fun j => ?_
  have := YoungDiagram.colLen_anti lam 0 j (Nat.zero_le j)
  unfold skewColLen
  omega

/-- The skew Schur function of a skew diagram is nonzero. -/
theorem cellSchur_ne_zero {X : Diagram} (hX : IsSkew X) : cellSchur X ≠ 0 := by
  obtain ⟨C, hC⟩ := exists_aeval_cellSchur_pos hX
  intro h
  have := hC C le_rfl
  rw [h, map_zero] at this
  exact lt_irrefl _ this

/-- **Two skew Schur functions never cancel.** -/
theorem cellSchur_add_cellSchur_ne_zero {X X' : Diagram} (hX : IsSkew X) (hX' : IsSkew X') :
    cellSchur X + cellSchur X' ≠ 0 := by
  obtain ⟨C, hC⟩ := exists_aeval_cellSchur_pos hX
  obtain ⟨C', hC'⟩ := exists_aeval_cellSchur_pos hX'
  intro h
  have h1 := hC (max C C') (le_max_left _ _)
  have h2 := hC' (max C C') (le_max_right _ _)
  have h3 := congrArg (MvPolynomial.aeval
    (fun k : ℕ+ => Shields.completeHom (max C C') k (fun _ => (1 : ℝ)))) h
  rw [map_add, map_zero] at h3
  linarith

end Plan.MarkFacts

end SkewMarkedFactor.Gluing
