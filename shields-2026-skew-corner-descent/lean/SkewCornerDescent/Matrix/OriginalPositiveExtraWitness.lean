/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassRepresentatives
import SkewCornerDescent.SeparatedPositiveChambers

/-!
# A common actual positive chamber avoiding extra algebraic zeros

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
Faithful original response-class representatives produce one common positive
regular assignment at which any prescribed nonzero polynomial in surviving
generators also stays nonzero.  The polynomial is avoided on the open chamber,
not treated as independent of the actual response functions.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- One common positive regular specialization of all actual response classes
avoids any prescribed nonzero polynomial in the original surviving generators.
This permits genuine discrepancy numerators and their denominators to remain
nonzero without treating them as independent response coordinates. -/
theorem originalResponseClasses_positive_avoiding {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (G : OtherPolynomial c.top) (hG : G ≠ 0) :
    ∃ num den : c.OriginalResponseClass P → OtherPolynomial c.top,
    ∃ x : ℕ → ℝ,
      let ι := algebraMap (OtherPolynomial c.top) (OtherField c.top)
      let φ := (MvPolynomial.eval x).comp (realResiduePolynomial c.top)
      (∀ X, X.val = ι (num X) / ι (den X)) ∧
      (∀ X, ι (num X) ≠ 0) ∧ (∀ X, ι (den X) ≠ 0) ∧
      (∀ X, φ (num X) ≠ 0) ∧ (∀ X, φ (den X) ≠ 0) ∧
      (∀ X, 0 < φ (num X) / φ (den X)) ∧ φ G ≠ 0 := by
  classical
  obtain ⟨p, q, hp, hq, hq0, hqreal, hrep⟩ :=
    c.originalResponseClasses_real_representatives P hB hmax
  let top := c.originalResponseClassTop P hB
  let num := fun X => MvPolynomial.X ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ *
    q X + p X
  let ι := algebraMap (OtherPolynomial c.top) (OtherField c.top)
  have hd : ∀ X, ι (q X) ≠ 0 := fun X =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hq0 X)
  have hrep' : ∀ X : c.OriginalResponseClass P, X.val = ι (num X) / ι (q X) := by
    intro X
    rw [hrep X]
    dsimp only [num]
    simp only [map_add, map_mul]
    change residueGenerator c.top ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ +
      ι (p X) / ι (q X) =
      (residueGenerator c.top ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ *
        ι (q X) + ι (p X)) / ι (q X)
    field_simp [hd X]
  have hn : ∀ X, ι (num X) ≠ 0 := by
    intro X hz
    have hunit := c.originalResponseClass_ne_zero P hB hmax X
    rw [hrep' X, hz, zero_div] at hunit
    exact hunit rfl
  have hnumReal (X : c.OriginalResponseClass P) : realResiduePolynomial c.top (num X) =
      MvPolynomial.X (top X : ℕ) * realResiduePolynomial c.top (q X) +
        realResiduePolynomial c.top (p X) := by
    simp [num, realResiduePolynomial]
  obtain ⟨hopen, hnonempty⟩ := rational_triangular_chamber
    (fun X => (top X : ℕ)) (fun X => realResiduePolynomial c.top (p X))
    (fun X => realResiduePolynomial c.top (q X)) (c.top : ℕ)
    (fun X => (c.originalResponseClassTop_gt P hB X).le) hp hq hqreal true
  obtain ⟨x, hx, havoid⟩ := exists_polynomial_ne_zero_on_open
    (realResiduePolynomial c.top G) (realResiduePolynomial_ne_zero c.top hG) _ hopen hnonempty
  let φ : OtherPolynomial c.top →+* ℝ := (MvPolynomial.eval x).comp (realResiduePolynomial c.top)
  have hden : ∀ X, φ (q X) ≠ 0 := fun X => (hx X).1
  have hpos (X) : 0 < φ (num X) / φ (q X) := by
    have hs := (hx X).2
    simp only [clearedTriangularResponse, map_mul, map_add, MvPolynomial.eval_X] at hs
    have hvalue : φ (num X) / φ (q X) =
        rationalTriangularResponse (top X : ℕ) (realResiduePolynomial c.top (p X))
          (realResiduePolynomial c.top (q X)) x := by
      simp only [φ, RingHom.comp_apply, hnumReal, map_add, map_mul, MvPolynomial.eval_X]
      unfold rationalTriangularResponse
      field_simp [(hx X).1]
    rw [hvalue]
    exact (responseSign_div_iff_cleared true _ _ _ (hden X)).mpr hs
  refine ⟨num, q, x, hrep', hn, hd, ?_, hden, hpos, havoid⟩
  intro X hz
  have h := hpos X
  rw [hz, zero_div] at h
  exact (lt_irrefl 0) h

end SkewCornerDescent.Matrix.SelectedCoordinate
