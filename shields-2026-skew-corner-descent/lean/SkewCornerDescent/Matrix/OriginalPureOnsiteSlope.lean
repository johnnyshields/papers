/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalResolvingResidue
import SkewCornerDescent.Matrix.OriginalWeightedSelfCorrection
import SkewCornerDescent.Matrix.OriginalNormalDerivative

/-!
# Actual resolving slope of the cleared onsite normal term

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The normal coefficient is strictly lower, the full positive onsite jet
has zero resolving derivative, and the actual residue slope is produced
from matching proper cores. Leibniz therefore retains exactly the raw
selected-function derivative times the original onsite jet. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual affine normal coefficient omits every later generator. -/
theorem normalCoefficient_resolving_derivative (H : ℕ+) (hH : c.top < H) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩ c.normalCoefficient = 0 := by
  apply residueGeneratorDeriv_lower
  rw [← c.residue_coefficient_eq_normal]
  exact residueLowerField_mono hH.le (c.residue_lower_polynomial c.coefficient_lower)

/-- Differentiate the genuine cleared onsite term. The possibly generator-
dependent residue is differentiated, not frozen; both other derivative
terms vanish by their actual original support and full normal suppliers. -/
theorem originalInternal_cleared_onsite_derivative {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (H J : ℕ+) (hH : c.top < H)
    (hdegree : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) - (H : ℤ) =
        (c.top : ℤ) - (J : ℤ))
    (hright : c.originalSelectedCoreRight P ⟨i.val + 1, by have := i.isLt; omega⟩ =
      c.originalSelectedCoreRight P ⟨i.val, by have := i.isLt; omega⟩) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.normalCoefficient * c.originalInternalResidue P i *
        PowerSeries.coeff 1 (c.normalSeries (c.originalInternalResponseMatrix P i i))) =
      c.residueMap (pderiv J (cellSchur D hD.1)) *
        PowerSeries.coeff 1 (c.normalSeries (c.originalInternalResponseMatrix P i i)) := by
  have ha := c.normalCoefficient_resolving_derivative H hH
  have hjet := c.originalInternal_positive_normal_resolving_derivative P i H hH
    (by rw [hdegree]; have := J.pos; omega) 1 (by omega)
  have hres := c.originalInternal_resolving_residue_gradient P i H J hH hdegree hright
  simp only [Derivation.leibniz, ha, hjet, smul_eq_mul, mul_zero,
    add_zero, zero_add]
  linear_combination
    PowerSeries.coeff 1 (c.normalSeries (c.originalInternalResponseMatrix P i i)) * hres

/-- The full cleared weighted onsite term differentiates to the full weighted
self-profile coefficient. Only one actual matching proper-core pair is needed:
the common residue then supplies the same slope on both complete cycles. -/
theorem originalInternal_weighted_cleared_onsite_derivative
    {pn qn b d : ℕ} [NeZero b] [NeZero d]
    (P : Profile pn) (Q : Profile qn)
    (ip : ZMod d → Fin (originalSelectedCount (hD := hD) P - 1))
    (iq : ZMod b → Fin (originalSelectedCount (hD := hD) Q - 1))
    (S : OtherField c.top) (H J : ℕ+) (hH : c.top < H) (K : ℤ) (k : ℕ)
    (hP : ∀ i, c.originalInternalResidue P (ip i) = S)
    (hQ : ∀ i, c.originalInternalResidue Q (iq i) = S)
    (hheightP : ∀ i, originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P (ip i)) (originalInternalStateIndex P (ip i)) = K)
    (hheightQ : ∀ i, originalHessenbergDistance (hD := hD) Q
      (originalInternalStateIndex Q (iq i)) (originalInternalStateIndex Q (iq i)) = K)
    (hself : K - (J : ℤ) = (k : ℤ))
    (hresolve : K - (H : ℤ) = (c.top : ℤ) - (J : ℤ))
    (hright : c.originalSelectedCoreRight P
        ⟨(ip 0).val + 1, by have := (ip 0).isLt; omega⟩ =
      c.originalSelectedCoreRight P ⟨(ip 0).val, by have := (ip 0).isLt; omega⟩) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.normalCoefficient * S *
        ((b : OtherField c.top) * (∑ i, PowerSeries.coeff 1
          (c.normalSeries (c.originalInternalResponseMatrix P (ip i) (ip i)))) -
        (d : OtherField c.top) * (∑ i, PowerSeries.coeff 1
          (c.normalSeries (c.originalInternalResponseMatrix Q (iq i) (iq i)))))) =
      (b : OtherField c.top) * (∑ i,
        ((c.originalInternalEndpointProfiles P (ip i)).1 *
          (c.originalInternalEndpointProfiles P (ip i)).2).coeff k) -
      (d : OtherField c.top) * (∑ i,
        ((c.originalInternalEndpointProfiles Q (iq i)).1 *
          (c.originalInternalEndpointProfiles Q (iq i)).2).coeff k) := by
  let V := (b : OtherField c.top) * (∑ i, PowerSeries.coeff 1
      (c.normalSeries (c.originalInternalResponseMatrix P (ip i) (ip i)))) -
    (d : OtherField c.top) * (∑ i, PowerSeries.coeff 1
      (c.normalSeries (c.originalInternalResponseMatrix Q (iq i) (iq i))))
  have hjetP (i : ZMod d) := c.originalInternal_positive_normal_resolving_derivative
    P (ip i) H hH (by rw [hheightP, hresolve]; have := J.pos; omega) 1 (by omega)
  have hjetQ (i : ZMod b) := c.originalInternal_positive_normal_resolving_derivative
    Q (iq i) H hH (by rw [hheightQ, hresolve]; have := J.pos; omega) 1 (by omega)
  have hV : residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩ V = 0 := by
    simp only [V, map_sub, Derivation.leibniz, Derivation.map_natCast, map_sum,
      hjetP, hjetQ, smul_eq_mul, mul_zero, add_zero,
      Finset.sum_const_zero, sub_self]
  have ha := c.normalCoefficient_resolving_derivative H hH
  have hs := c.originalInternal_resolving_residue_gradient P (ip 0) H J hH
    (by rw [hheightP, hresolve]) hright
  rw [hP] at hs
  have hw := c.originalInternal_weighted_self_correction P Q ip iq S J k hP hQ
    (fun i => by rw [hheightP, hself]) (fun i => by rw [hheightQ, hself])
  rw [hw]
  change residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
    (c.normalCoefficient * S * V) = c.residueMap (pderiv J (cellSchur D hD.1)) * V
  simp only [Derivation.leibniz, ha, hV, smul_eq_mul, mul_zero, add_zero, zero_add]
  linear_combination V * hs

end SkewCornerDescent.Matrix.SelectedCoordinate
