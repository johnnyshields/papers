/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassRepresentatives
import SkewCornerDescent.SeparatedPositiveChambers

/-!
# One positive assignment separating two actual response classes

Supports `shields-2026-skew-corner-descent.tex` (`lem:two-support`,
`cor:one-positive-short`). Faithful representatives of every complete source
response class supply a simultaneous positive chamber. The two distinct full
functions supply a nonzero cleared difference to avoid inside that chamber.
Every numerator and denominator stays regular. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Distinct actual classes admit one common positive regular specialization.
The numerator/denominator representation is faithful in the original field, and
the chosen pair remains unequal at that same positive assignment. -/
theorem originalResponseClasses_positive_separated {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (a b : c.OriginalResponseClass P) (hne : a ≠ b) :
    ∃ num den : c.OriginalResponseClass P → OtherPolynomial c.top,
    ∃ x : ℕ → ℝ,
      let ι := algebraMap (OtherPolynomial c.top) (OtherField c.top)
      let φ := (MvPolynomial.eval x).comp (realResiduePolynomial c.top)
      (∀ X, X.val = ι (num X) / ι (den X)) ∧
      (∀ X, ι (num X) ≠ 0) ∧ (∀ X, ι (den X) ≠ 0) ∧
      (∀ X, φ (num X) ≠ 0) ∧ (∀ X, φ (den X) ≠ 0) ∧
      (∀ X, 0 < φ (num X) / φ (den X)) ∧
      φ (num a) / φ (den a) ≠ φ (num b) / φ (den b) := by
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
  have hdiff := real_cross_difference_ne_zero c.top (num a) (q a) (num b) (q b)
    (hq0 a) (hq0 b) (by rw [← hrep' a, ← hrep' b]; exact fun h => hne (Subtype.ext h))
  rw [hnumReal a, hnumReal b] at hdiff
  obtain ⟨x, hx, hpositive, hsep⟩ := exists_positive_rational_family_separated
    (fun X => (top X : ℕ)) (fun X => realResiduePolynomial c.top (p X))
    (fun X => realResiduePolynomial c.top (q X)) (c.top : ℕ)
    (fun X => (c.originalResponseClassTop_gt P hB X).le) hp hq hqreal a b hdiff
  let φ : OtherPolynomial c.top →+* ℝ := (MvPolynomial.eval x).comp (realResiduePolynomial c.top)
  have hvalue (X : c.OriginalResponseClass P) : φ (num X) / φ (q X) =
      rationalTriangularResponse (top X : ℕ) (realResiduePolynomial c.top (p X))
        (realResiduePolynomial c.top (q X)) x := by
    simp only [φ, RingHom.comp_apply, hnumReal, map_add, map_mul, MvPolynomial.eval_X]
    unfold rationalTriangularResponse
    field_simp [hx X]
  have hpos : ∀ X, 0 < φ (num X) / φ (q X) := fun X => by rw [hvalue X]; exact hpositive X
  refine ⟨num, q, x, hrep', hn, hd, ?_, hx, hpos, ?_⟩
  · intro X hz
    have h := hpos X
    rw [hz, zero_div] at h
    exact (lt_irrefl 0) h
  · rw [hvalue a, hvalue b]
    exact hsep

end SkewCornerDescent.Matrix.SelectedCoordinate
