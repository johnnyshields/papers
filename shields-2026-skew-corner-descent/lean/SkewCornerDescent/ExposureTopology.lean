/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.RationalExposure

/-!
# Open chambers on rational anchor sections

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

A regular rational anchor section is continuous. Pulling back finite strict response
chambers gives open sets in its free coordinates, with denominators retained explicitly.

Sorry-free.
-/

namespace SkewCornerDescent

/-- Updating one coordinate to a regular rational root is continuous on its regular locus. -/
theorem rational_anchor_assignment_continuousOn (K : ℕ) (p q : MvPolynomial ℕ ℝ) :
    ContinuousOn (fun x : ℕ → ℝ => Function.update x K
      (-(MvPolynomial.eval x p / MvPolynomial.eval x q)))
      {x | MvPolynomial.eval x q ≠ 0} := by
  have hroot : ContinuousOn (fun x : ℕ → ℝ =>
      -(MvPolynomial.eval x p / MvPolynomial.eval x q))
      {x | MvPolynomial.eval x q ≠ 0} :=
    ((p.continuous_eval.continuousOn).div (q.continuous_eval.continuousOn)
      (fun _ hx => hx)).neg
  exact (continuous_update K).continuousOn.comp
    (continuousOn_id.prodMk hroot) (fun _ _ => Set.mem_univ _)

/-- The regular strict-sign locus is open even without triangularity assumptions. -/
theorem rational_response_locus_open {ι : Type*} [Finite ι]
    (top : ι → ℕ) (p q : ι → MvPolynomial ℕ ℝ) (positive : Bool) :
    IsOpen {x : ℕ → ℝ | ∀ i, MvPolynomial.eval x (q i) ≠ 0 ∧
      responseSign positive (rationalTriangularResponse (top i) (p i) (q i) x)} := by
  have he : {x : ℕ → ℝ | ∀ i, MvPolynomial.eval x (q i) ≠ 0 ∧
      responseSign positive (rationalTriangularResponse (top i) (p i) (q i) x)} =
      {x : ℕ → ℝ | ∀ i, MvPolynomial.eval x (q i) ≠ 0 ∧
        responseSign positive (MvPolynomial.eval x
          (clearedTriangularResponse (top i) (p i) (q i)))} := by
    ext x
    constructor <;> intro hx i
    · refine ⟨(hx i).1, ?_⟩
      simp only [clearedTriangularResponse, map_mul, map_add, MvPolynomial.eval_X]
      exact (responseSign_div_iff_cleared positive _ _ _ (hx i).1).mp (hx i).2
    · refine ⟨(hx i).1, ?_⟩
      apply (responseSign_div_iff_cleared positive _ _ _ (hx i).1).mpr
      simpa only [clearedTriangularResponse, map_mul, map_add, MvPolynomial.eval_X]
        using (hx i).2
  rw [he]
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply (isOpen_ne.preimage (q i).continuous_eval).inter
  have hc := (clearedTriangularResponse (top i) (p i) (q i)).continuous_eval
  cases positive
  · exact isOpen_lt hc continuous_const
  · exact isOpen_lt continuous_const hc

/-- Strict signs on an anchor section form an open chamber in the free coordinates. -/
theorem rational_anchor_chamber_open {ι : Type*} [Finite ι]
    (K : ℕ) (ap aq : MvPolynomial ℕ ℝ)
    (top : ι → ℕ) (p q : ι → MvPolynomial ℕ ℝ) (positive : Bool) :
    IsOpen {x : ℕ → ℝ | MvPolynomial.eval x aq ≠ 0 ∧
      ∀ i, let y := Function.update x K (-(MvPolynomial.eval x ap / MvPolynomial.eval x aq))
        MvPolynomial.eval y (q i) ≠ 0 ∧
          responseSign positive (rationalTriangularResponse (top i) (p i) (q i) y)} := by
  exact (rational_anchor_assignment_continuousOn K ap aq).isOpen_inter_preimage
    (isOpen_ne.preimage aq.continuous_eval) (rational_response_locus_open top p q positive)

/-- A regular exposed point inhabits its open root-section chamber. -/
theorem rational_anchor_chamber_nonempty {ι : Type*} [Finite ι]
    (K : ℕ) (ap aq : MvPolynomial ℕ ℝ)
    (top : ι → ℕ) (p q : ι → MvPolynomial ℕ ℝ) (positive : Bool)
    (y : ℕ → ℝ) (haq : MvPolynomial.eval y aq ≠ 0)
    (hz : rationalTriangularResponse K ap aq y = 0)
    (hq : ∀ i, MvPolynomial.eval y (q i) ≠ 0)
    (hs : ∀ i, responseSign positive (rationalTriangularResponse (top i) (p i) (q i) y)) :
    ({x : ℕ → ℝ | MvPolynomial.eval x aq ≠ 0 ∧
      ∀ i, let z := Function.update x K (-(MvPolynomial.eval x ap / MvPolynomial.eval x aq))
        MvPolynomial.eval z (q i) ≠ 0 ∧
          responseSign positive (rationalTriangularResponse (top i) (p i) (q i) z)} :
      Set (ℕ → ℝ)).Nonempty := by
  have hroot : -(MvPolynomial.eval y ap / MvPolynomial.eval y aq) = y K := by
    change y K + MvPolynomial.eval y ap / MvPolynomial.eval y aq = 0 at hz
    linarith
  refine ⟨y, haq, fun i => ?_⟩
  simp only [hroot, Function.update_eq_self]
  exact ⟨hq i, hs i⟩

end SkewCornerDescent
