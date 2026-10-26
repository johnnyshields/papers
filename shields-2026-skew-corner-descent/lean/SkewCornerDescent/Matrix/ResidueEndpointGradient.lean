/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalDerivative
import SkewCornerDescent.Matrix.UnitVertexDetection
import SkewCornerDescent.Matrix.EndpointProfiles

/-!
# Higher-generator gradients of complete residue interval responses

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Above
the selected span the chart substitution has no generator derivative of its own.
Thus equal actual residue responses give equal full profile-product coefficients
in the corresponding early degrees. Complete inverse derivatives remain.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A higher surviving generator differentiates actual mapped JT entries by
exact index equality. The selected generator is handled through its produced
lower-field image rather than by treating it as an independent variable. -/
theorem residue_hh_higher_derivative (j : ℕ+) (hj : c.top < j) (z : ℤ) :
    residueGeneratorDeriv c.top ⟨j, ne_of_gt hj⟩ (c.residueMap (hh z)) =
      if z = (j : ℤ) then 1 else 0 := by
  by_cases hz : z < (j : ℤ)
  · have hd := residueGeneratorDeriv_lower c.top ⟨j, ne_of_gt hj⟩
      (c.residue_hh_mem_lower j hj z hz)
    rw [hd, ite_eq_right (ne_of_lt hz)]
  · have hpos : 0 < z := by have := j.pos; omega
    let k : ℕ+ := ⟨z.toNat, by omega⟩
    have hk : (k : ℤ) = z := Int.toNat_of_nonneg hpos.le
    have hkN : k ≠ c.top := by
      intro he
      have he' := congrArg (fun t : ℕ+ => (t : ℤ)) he
      have hNj : (c.top : ℤ) < (j : ℤ) := by exact_mod_cast hj
      omega
    rw [← hk, hh_pnat, c.residueMap_other k hkN]
    change residueGeneratorDeriv c.top ⟨j, ne_of_gt hj⟩
      (residueGenerator c.top ⟨k, hkN⟩) = _
    have hindex : (⟨k, hkN⟩ : {t : ℕ+ // t ≠ c.top}) = ⟨j, ne_of_gt hj⟩ ↔
        (k : ℤ) = (j : ℤ) :=
      ⟨fun he => congrArg (fun t : {t : ℕ+ // t ≠ c.top} => (t.val : ℤ)) he,
        fun he => Subtype.ext (by exact_mod_cast he)⟩
    simp only [residueGeneratorDeriv_generator, hindex]

set_option backward.isDefEq.respectTransparency false in
/-- The full original residue interval has the endpoint-product gradient at
every surviving generator above the selected span. Both off-diagonal inverse
couplings and the derivative of the removed inverse are retained. -/
theorem residue_interval_profile_gradient {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x y : ℤ) (j : ℕ+) (hj : c.top < j)
    [Invertible (vertexBetaMatrix c.residueMap row col)] :
    residueGeneratorDeriv c.top ⟨j, ne_of_gt hj⟩
        (c.residueMap (hh (x - y)) -
          (vertexOutgoing c.residueMap col x * ⅟(vertexBetaMatrix c.residueMap row col) *
            vertexIncoming c.residueMap row y) () ()) =
      (endpointProfile (fun i => x - row i)
          (fun i => (vertexOutgoing c.residueMap col x *
            ⅟(vertexBetaMatrix c.residueMap row col)) () i) *
        endpointProfile (fun i => col i - y)
          (fun i => (⅟(vertexBetaMatrix c.residueMap row col) *
            vertexIncoming c.residueMap row y) i ())).coeff (x - y - (j : ℤ)) := by
  classical
  let δ₀ := residueGeneratorDeriv c.top ⟨j, ne_of_gt hj⟩
  let dhom : OtherField c.top →+ OtherField c.top := δ₀.toLinearMap.toAddMonoidHom
  have hadd (f g : OtherField c.top) : δ₀ (f + g) = δ₀ f + δ₀ g := δ₀.map_add f g
  have hone : δ₀ 1 = 0 := δ₀.map_one_eq_zero
  have hmul (f g : OtherField c.top) : δ₀ (f * g) = f * δ₀ g + g * δ₀ f := by
    simpa only [smul_eq_mul] using δ₀.leibniz f g
  let : Module ℚ (OtherField c.top) :=
    (DivisionRing.toRatAlgebra : Algebra ℚ (OtherField c.top)).toModule
  let δ : Derivation ℚ (OtherField c.top) (OtherField c.top) :=
    { toFun := δ₀
      map_add' := hadd
      map_smul' := map_rat_smul dhom
      map_one_eq_zero' := hone
      leibniz' := by intro f g; exact hmul f g }
  have hδ (f : OtherField c.top) : δ f = residueGeneratorDeriv c.top ⟨j, ne_of_gt hj⟩ f := rfl
  let B := vertexOutgoing c.residueMap col x
  let C := vertexIncoming c.residueMap row y
  let P := vertexBetaMatrix c.residueMap row col
  let Q := ⅟P
  have h := congrFun (congrFun (entryDeriv_retainedResponse (R := ℚ) δ
    (fun _ _ : Unit => c.residueMap (hh (x - y))) B C P) ()) ()
  change δ (retainedResponse (fun _ _ : Unit => c.residueMap (hh (x - y))) B C P () ()) =
    (entryDeriv δ (fun _ _ : Unit => c.residueMap (hh (x - y))) -
      entryDeriv δ B * Q * C - B * Q * entryDeriv δ C +
      B * Q * entryDeriv δ P * Q * C) () () at h
  have hL : (entryDeriv δ B * (Q * C)) () () =
      ∑ i, if x - col i = (j : ℤ) then (Q * C) i () else 0 := by
    rw [Matrix.mul_apply]
    simp only [B, entryDeriv, vertexOutgoing, Matrix.of_apply, hδ,
      c.residue_hh_higher_derivative j hj, ite_mul, one_mul, zero_mul]
  have hR : ((B * Q) * entryDeriv δ C) () () =
      ∑ i, if row i - y = (j : ℤ) then (B * Q) () i else 0 := by
    rw [Matrix.mul_apply]
    simp only [C, entryDeriv, vertexIncoming, Matrix.of_apply, hδ,
      c.residue_hh_higher_derivative j hj, mul_ite, mul_one, mul_zero]
  have hI : ((B * Q) * entryDeriv δ P * (Q * C)) () () =
      ∑ i, ∑ k, if row i - col k = (j : ℤ) then
        (B * Q) () i * (Q * C) k () else 0 := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply (M := B * Q) (N := entryDeriv δ P), Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [P, entryDeriv, vertexBetaMatrix, Matrix.of_apply, hδ,
      c.residue_hh_higher_derivative j hj, mul_ite, ite_mul, mul_one,
      zero_mul, mul_zero]
  change δ (retainedResponse (fun _ _ : Unit => c.residueMap (hh (x - y))) B C P () ()) =
    (endpointProfile (fun i => x - row i) (fun i => (B * Q) () i) *
      endpointProfile (fun i => col i - y) (fun i => (Q * C) i ())).coeff _
  rw [h, endpointProfile_mul_coeff]
  change (entryDeriv δ (fun _ _ : Unit => c.residueMap (hh (x - y))) -
    entryDeriv δ B * Q * C - B * Q * entryDeriv δ C +
    B * Q * entryDeriv δ P * Q * C) () () = _
  rw [Matrix.mul_assoc (entryDeriv δ B) Q C,
    Matrix.mul_assoc (B * Q * entryDeriv δ P) Q C]
  simp only [Matrix.add_apply, Matrix.sub_apply, hL, hR, hI, entryDeriv, hδ,
    c.residue_hh_higher_derivative j hj]
  have hz : (x - y - (j : ℤ) = 0) ↔ x - y = (j : ℤ) := by omega
  have hl (i : ν) : (x - row i = x - y - (j : ℤ)) ↔ row i - y = (j : ℤ) := by omega
  have hr (i : ν) : (col i - y = x - y - (j : ℤ)) ↔ x - col i = (j : ℤ) := by omega
  have hi (i k : ν) : (x - row i + (col k - y) = x - y - (j : ℤ)) ↔
      row i - col k = (j : ℤ) := by omega
  simp only [hz, hl, hr, hi]
  abel

/-- Equal complete actual residue responses of the same span have equal
profile-product coefficients wherever the differentiating generator is above
the selected span. This includes all degrees below half-span when `K > 2N`. -/
theorem residue_equal_response_profile_products {ν μ : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ]
    (row col : ν → ℤ) (row' col' : μ → ℤ) (x y x' y' : ℤ)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    [Invertible (vertexBetaMatrix c.residueMap row' col')]
    (hspan : x - y = x' - y')
    (hresponse :
      c.residueMap (hh (x - y)) -
        (vertexOutgoing c.residueMap col x * ⅟(vertexBetaMatrix c.residueMap row col) *
          vertexIncoming c.residueMap row y) () () =
      c.residueMap (hh (x' - y')) -
        (vertexOutgoing c.residueMap col' x' * ⅟(vertexBetaMatrix c.residueMap row' col') *
          vertexIncoming c.residueMap row' y') () ())
    (w : ℤ) (hw : (c.top : ℤ) < x - y - w) :
    (endpointProfile (fun i => x - row i)
        (fun i => (vertexOutgoing c.residueMap col x *
          ⅟(vertexBetaMatrix c.residueMap row col)) () i) *
      endpointProfile (fun i => col i - y)
        (fun i => (⅟(vertexBetaMatrix c.residueMap row col) *
          vertexIncoming c.residueMap row y) i ())).coeff w =
    (endpointProfile (fun i => x' - row' i)
        (fun i => (vertexOutgoing c.residueMap col' x' *
          ⅟(vertexBetaMatrix c.residueMap row' col')) () i) *
      endpointProfile (fun i => col' i - y')
        (fun i => (⅟(vertexBetaMatrix c.residueMap row' col') *
          vertexIncoming c.residueMap row' y') i ())).coeff w := by
  have hN := c.top.pos
  let j : ℕ+ := ⟨(x - y - w).toNat, by omega⟩
  have hj : (j : ℤ) = x - y - w := Int.toNat_of_nonneg (by omega)
  have hNj : c.top < j := by
    have he : ((c.top : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by rw [hj]; exact hw
    exact_mod_cast he
  have h := congrArg (residueGeneratorDeriv c.top ⟨j, ne_of_gt hNj⟩) hresponse
  rw [c.residue_interval_profile_gradient row col x y j hNj,
    c.residue_interval_profile_gradient row' col' x' y' j hNj] at h
  have hdegree : x - y - (j : ℤ) = w := by omega
  have hdegree' : x' - y' - (j : ℤ) = w := by omega
  rwa [hdegree, hdegree'] at h

end SkewCornerDescent.Matrix.SelectedCoordinate
