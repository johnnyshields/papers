/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassChambers
import SkewCornerDescent.Matrix.OriginalCapNormalization

/-!
# A common polynomial scale for actual active response classes

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:dual-identities`).
One active representative supplies the monic base. The two actual cap numerators
and their lower denominators supply one common scale. Every real specialization
uses these same representatives and actual coordinates. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Faithful actual representatives and the produced active-label equations yield
one common base, cap, and denominator. Regular cap-positive assignments remain
regular and cap-positive after this exact polynomial conversion. -/
theorem originalResponseClasses_affine_scale {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (p q : c.OriginalResponseClass P → OtherPolynomial c.top)
    (hq : ∀ X, q X ≠ 0)
    (hrep : ∀ X, X.val = residueGenerator c.top
        ⟨c.originalResponseClassTop P hB X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ +
      algebraMap (OtherPolynomial c.top) (OtherField c.top) (p X) /
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (q X))
    (active : c.OriginalResponseClass P → Prop) (a0 : c.OriginalResponseClass P)
    (ha0 : active a0) (label : c.OriginalResponseClass P → ℚ) (S : OtherField c.top)
    (htop : ∀ X, active X → c.originalResponseClassTop P hB X =
      c.originalResponseClassTop P hB a0)
    (hlinear : ∀ X, active X → X.val = S - (label X : OtherField c.top) *
      c.originalTrueCapProduct P) :
    ∃ base cap scaleDen : OtherPolynomial c.top,
      (∀ X, active X →
        let ι := algebraMap (OtherPolynomial c.top) (OtherField c.top)
        residueGenerator c.top
            ⟨c.originalResponseClassTop P hB X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ +
          ι (p X) / ι (q X) =
        residueGenerator c.top
            ⟨c.originalResponseClassTop P hB X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ +
          ι base / ι scaleDen - ((label X - label a0 : ℚ) : OtherField c.top) *
            (ι cap / ι scaleDen)) ∧
      (∀ X Y, active X → active Y → label X - label a0 = label Y - label a0 → X = Y) ∧
      ∀ x : ℕ → ℝ,
        (∀ X, MvPolynomial.eval x (realResiduePolynomial c.top (q X)) ≠ 0) →
        (0 < rationalTriangularResponse (c.originalResponseClassTop P hB
            (c.originalResponseClassOf P 0) : ℕ)
          (realResiduePolynomial c.top (p (c.originalResponseClassOf P 0)))
          (realResiduePolynomial c.top (q (c.originalResponseClassOf P 0))) x *
          rationalTriangularResponse (c.originalResponseClassTop P hB
            (c.originalResponseClassOf P (Fin.last _)) : ℕ)
          (realResiduePolynomial c.top (p (c.originalResponseClassOf P (Fin.last _))))
          (realResiduePolynomial c.top (q (c.originalResponseClassOf P (Fin.last _)))) x) →
        MvPolynomial.eval x (realResiduePolynomial c.top scaleDen) ≠ 0 ∧
        0 < MvPolynomial.eval x (realResiduePolynomial c.top cap) /
          MvPolynomial.eval x (realResiduePolynomial c.top scaleDen) := by
  classical
  let top := c.originalResponseClassTop P hB
  let left := c.originalResponseClassOf P 0
  let right := c.originalResponseClassOf P (Fin.last _)
  let ι := algebraMap (OtherPolynomial c.top) (OtherField c.top)
  let num := fun X : c.OriginalResponseClass P =>
    MvPolynomial.X ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ * q X + p X
  let scaleDen := q a0 * q left * q right
  let base := p a0 * q left * q right
  let cap := num left * num right * q a0
  have hqF : ∀ X, ι (q X) ≠ 0 := fun X =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hq X)
  have hnum (X : c.OriginalResponseClass P) : ι (num X) / ι (q X) = X.val := by
    rw [hrep X]
    simp only [num, map_add, map_mul]
    change (residueGenerator c.top
        ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ * ι (q X) + ι (p X)) /
        ι (q X) = residueGenerator c.top
          ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ + ι (p X) / ι (q X)
    field_simp [hqF X]
  have hbase : ι base / ι scaleDen = ι (p a0) / ι (q a0) := by
    simp only [base, scaleDen, map_mul]
    field_simp [hqF a0, hqF left, hqF right]
  have hcap : ι cap / ι scaleDen = c.originalTrueCapProduct P := by
    change ι cap / ι scaleDen = left.val * right.val
    rw [← hnum left, ← hnum right]
    simp only [cap, scaleDen, map_mul]
    field_simp [hqF a0, hqF left, hqF right]
  have hshift (X : c.OriginalResponseClass P) (hX : active X) :
      X.val = a0.val - ((label X - label a0 : ℚ) : OtherField c.top) *
        c.originalTrueCapProduct P := by
    rw [hlinear X hX, hlinear a0 ha0, Rat.cast_sub]
    ring
  dsimp only
  refine ⟨base, cap, scaleDen, ?_, ?_, ?_⟩
  · intro X hX
    have hg : residueGenerator c.top
        ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ =
        residueGenerator c.top
          ⟨top a0, ne_of_gt (c.originalResponseClassTop_gt P hB a0)⟩ := by
      apply congrArg (residueGenerator c.top)
      exact Subtype.ext (htop X hX)
    rw [← hrep X, hbase, hcap, hshift X hX, hrep a0, hg]
  · intro X Y hX hY he
    have he' : label X = label Y := by linarith
    apply Subtype.ext
    rw [hlinear X hX, hlinear Y hY, he']
  · intro x hqx hpos
    let φ : OtherPolynomial c.top →+* ℝ := (MvPolynomial.eval x).comp (realResiduePolynomial c.top)
    have hnumReal (X : c.OriginalResponseClass P) : φ (num X) / φ (q X) =
        rationalTriangularResponse (top X : ℕ) (realResiduePolynomial c.top (p X))
          (realResiduePolynomial c.top (q X)) x := by
      simp only [num, map_add, map_mul, φ, RingHom.comp_apply]
      have hX : MvPolynomial.eval x (realResiduePolynomial c.top
          (MvPolynomial.X ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩)) =
          x (top X : ℕ) := by simp [realResiduePolynomial]
      rw [hX]
      unfold rationalTriangularResponse
      field_simp [hqx X]
    have hrealcap : φ cap / φ scaleDen =
        rationalTriangularResponse (top left : ℕ) (realResiduePolynomial c.top (p left))
          (realResiduePolynomial c.top (q left)) x *
        rationalTriangularResponse (top right : ℕ) (realResiduePolynomial c.top (p right))
          (realResiduePolynomial c.top (q right)) x := by
      rw [← hnumReal left, ← hnumReal right]
      simp only [cap, scaleDen, map_mul, φ, RingHom.comp_apply]
      field_simp [hqx a0, hqx left, hqx right]
    constructor
    · change φ scaleDen ≠ 0
      simp only [scaleDen, map_mul]
      exact mul_ne_zero (mul_ne_zero (hqx a0) (hqx left)) (hqx right)
    · change 0 < φ cap / φ scaleDen
      rw [hrealcap]
      exact hpos

end SkewCornerDescent.Matrix.SelectedCoordinate
