/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPureOnsiteSlope
import SkewCornerDescent.Matrix.OriginalInternalCyclicEnergy
import SkewCornerDescent.Matrix.NormalCyclicClearedCharge

/-!
# Nonzero first-normal charge from actual pure internal cycles

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The complete original onsite and pair suppliers differentiate the genuinely
cleared charge. The raw chart terms cancel at the two actual cardinalities;
complete binary cross energy gives its nonzero resolving derivative.
The common-response, proper-core, prefix and binary-data suppliers remain
explicit inputs for the original pure-window assembly. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing BinaryTransitions
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

set_option maxHeartbeats 800000 in
-- Elaborating both complete inverse-profile cycles and their sums exceeds the default limit.
/-- A genuine pair of complete original internal cycles has nonzero weighted
first-normal charge once its actual pure-phase data have been supplied.
The derivative is of the cleared expression, not a defined coefficient. -/
theorem originalInternal_pure_cyclic_first_nonzero
    {pn qn b d : ℕ} [NeZero b] [NeZero d]
    (P : Profile pn) (Q : Profile qn) (hcop : Nat.Coprime b d)
    (hTP : d ≤ originalSelectedCount (hD := hD) P - 1 - 1)
    (hTQ : b ≤ originalSelectedCount (hD := hD) Q - 1 - 1)
    (S : OtherField c.top) (hS : S ≠ 0) (K w : ℕ)
    (hN : (c.top : ℕ) < w) (hhalf : 2 * w < K)
    (H : ℕ+) (hH : c.top < H)
    (hresolve : (H : ℤ) = 2 * (K : ℤ) - (c.top : ℤ) - 2 * (w : ℤ))
    (hP : ∀ i, c.originalInternalResidue P i = S)
    (hQ : ∀ i, c.originalInternalResidue Q i = S)
    (hheightP : ∀ i, originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) = (K : ℤ))
    (hheightQ : ∀ i, originalHessenbergDistance (hD := hD) Q
      (originalInternalStateIndex Q i) (originalInternalStateIndex Q i) = (K : ℤ))
    (hpP : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1), j.val = i.val + d →
      (c.originalInternalEndpointProfiles P i).2 = (c.originalInternalEndpointProfiles P j).2)
    (hpQ : ∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1), j.val = i.val + b →
      (c.originalInternalEndpointProfiles Q i).2 = (c.originalInternalEndpointProfiles Q j).2)
    (hright : c.originalSelectedCoreRight P ⟨1, by have := NeZero.pos d; omega⟩ =
      c.originalSelectedCoreRight P ⟨0, by have := NeZero.pos d; omega⟩)
    (hmatchP : ∀ z k, k < w →
      (c.originalInternalEndpointCycle P (by omega) z).1.coeff k =
        (c.originalInternalEndpointCycle P (by omega) (z + (1 : ZMod d))).1.coeff k)
    (hmatchQ : ∀ z k, k < w →
      (c.originalInternalEndpointCycle Q (by omega) z).1.coeff k =
        (c.originalInternalEndpointCycle Q (by omega) (z + (1 : ZMod b))).1.coeff k)
    (η : OtherField c.top) (hη : η ≠ 0)
    (bitsP : ZMod d → Bool) (bitsQ : ZMod b → Bool)
    (hbitsP : ∀ z : ZMod d, (c.originalInternalEndpointCycle P (by omega) z).1.coeff w -
      (c.originalInternalEndpointCycle P (by omega) (0 : ZMod d)).1.coeff w =
        if bitsP z then η else 0)
    (hbitsQ : ∀ z : ZMod b, (c.originalInternalEndpointCycle Q (by omega) z).1.coeff w -
      (c.originalInternalEndpointCycle Q (by omega) (0 : ZMod b)).1.coeff w =
        if bitsQ z then η else 0)
    (hnonconstant : ∃ i j, bitsQ i ≠ bitsQ j) :
    let fP := normalDiagonalCycle ((c.originalInternalResponseMatrix P).map c.normalSeries)
      (show d ≤ originalSelectedCount (hD := hD) P - 1 by omega)
    let qP := normalAdjacentCycle ((c.originalInternalResponseMatrix P).map c.normalSeries) hTP
    let fQ := normalDiagonalCycle ((c.originalInternalResponseMatrix Q).map c.normalSeries)
      (show b ≤ originalSelectedCount (hD := hD) Q - 1 by omega)
    let qQ := normalAdjacentCycle ((c.originalInternalResponseMatrix Q).map c.normalSeries) hTQ
    let C := b • normalCyclicFirstCharge fP qP c.normalCoefficient⁻¹ -
      d • normalCyclicFirstCharge fQ qQ c.normalCoefficient⁻¹
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩ (c.normalCoefficient * S^2 * C) =
      -(1/2 : OtherField c.top) * η^2 *
        ((b : OtherField c.top)*transitionCount bitsP 1 -
          (d : OtherField c.top)*transitionCount bitsQ 1) ∧ C ≠ 0 := by
  let hp : d ≤ originalSelectedCount (hD := hD) P - 1 := by omega
  let hq : b ≤ originalSelectedCount (hD := hD) Q - 1 := by omega
  let ip := originalInternalCycleIndex P hp
  let iq := originalInternalCycleIndex Q hq
  let fP := normalDiagonalCycle ((c.originalInternalResponseMatrix P).map c.normalSeries) hp
  let fQ := normalDiagonalCycle ((c.originalInternalResponseMatrix Q).map c.normalSeries) hq
  let qP := normalAdjacentCycle ((c.originalInternalResponseMatrix P).map c.normalSeries) hTP
  let qQ := normalAdjacentCycle ((c.originalInternalResponseMatrix Q).map c.normalSeries) hTQ
  let V := (b : OtherField c.top)*(∑ z, PowerSeries.coeff 1 (fP z)) -
    (d : OtherField c.top)*(∑ z, PowerSeries.coeff 1 (fQ z))
  let CP := fun z : ZMod d => ((c.originalInternalEndpointCycle P hp z).1 *
    (c.originalInternalEndpointCycle P hp (z+1)).2).coeff (2*w)
  let CQ := fun z : ZMod b => ((c.originalInternalEndpointCycle Q hq z).1 *
    (c.originalInternalEndpointCycle Q hq (z+1)).2).coeff (2*w)
  let SP := fun z : ZMod d => ((c.originalInternalEndpointCycle P hp z).1 *
    (c.originalInternalEndpointCycle P hp z).2).coeff (2*w)
  let SQ := fun z : ZMod b => ((c.originalInternalEndpointCycle Q hq z).1 *
    (c.originalInternalEndpointCycle Q hq z).2).coeff (2*w)
  let C := b • normalCyclicFirstCharge fP qP c.normalCoefficient⁻¹ -
    d • normalCyclicFirstCharge fQ qQ c.normalCoefficient⁻¹
  let δ := residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
  have hfP (z : ZMod d) : PowerSeries.constantCoeff (fP z) = S :=
    (c.originalInternal_normal_constant P (ip z)).trans (hP (ip z))
  have hfQ (z : ZMod b) : PowerSeries.constantCoeff (fQ z) = S :=
    (c.originalInternal_normal_constant Q (iq z)).trans (hQ (iq z))
  have hclear := weighted_normalCyclicFirstCharge_clear_common_residue
    fP qP fQ qQ c.normalCoefficient S c.normalCoefficient_ne_zero hS hfP hfQ
  change c.normalCoefficient*S^2*C = c.normalCoefficient*S*V -
    ((b : OtherField c.top)*(∑ z, PowerSeries.constantCoeff (qP z)) -
      (d : OtherField c.top)*(∑ z, PowerSeries.constantCoeff (qQ z))) at hclear
  let J : ℕ+ := ⟨K-2*w, by omega⟩
  have hJe : (J : ℤ) = (K : ℤ)-2*(w : ℤ) := by
    change ((K-2*w : ℕ) : ℤ) = _
    omega
  have honsite := c.originalInternal_weighted_cleared_onsite_derivative
    P Q ip iq S H J hH K (2*w) (fun z => hP (ip z)) (fun z => hQ (iq z))
    (fun z => hheightP (ip z)) (fun z => hheightQ (iq z))
    (by rw [hJe]; push_cast; ring) (by rw [hJe, hresolve]; ring)
    (by simpa only [ip, originalInternalCycleIndex, ZMod.val_zero] using hright)
  change δ (c.normalCoefficient*S*V) =
    (b : OtherField c.top)*(∑ z, SP z) - (d : OtherField c.top)*(∑ z, SQ z) at honsite
  have hpairP (z : ZMod d) : δ (PowerSeries.constantCoeff (qP z)) = CP z :=
    c.originalInternal_cyclic_resolving_cross_gradient P hTP H hH K w hhalf.le
      hresolve hpP hheightP z
  have hpairQ (z : ZMod b) : δ (PowerSeries.constantCoeff (qQ z)) = CQ z :=
    c.originalInternal_cyclic_resolving_cross_gradient Q hTQ H hH K w hhalf.le
      hresolve hpQ hheightQ z
  have hpair : δ ((b : OtherField c.top)*(∑ z, PowerSeries.constantCoeff (qP z)) -
      (d : OtherField c.top)*(∑ z, PowerSeries.constantCoeff (qQ z))) =
      (b : OtherField c.top)*(∑ z, CP z) - (d : OtherField c.top)*(∑ z, CQ z) := by
    simp only [map_sub, Derivation.leibniz, Derivation.map_natCast, map_sum,
      hpairP, hpairQ, smul_eq_mul, mul_zero, add_zero]
  have hd : δ (c.normalCoefficient*S^2*C) =
      ((b : OtherField c.top)*(∑ z, SP z) - (d : OtherField c.top)*(∑ z, SQ z)) -
        ((b : OtherField c.top)*(∑ z, CP z) - (d : OtherField c.top)*(∑ z, CQ z)) := by
    rw [hclear, map_sub, honsite, hpair]
  have hhigh : (c.top : ℕ)+w < K := by omega
  have hw : 0 < w := lt_trans c.top.pos hN
  have heP := c.originalInternal_cyclic_binary_energy P hp K w hw hhigh
    (fun z => hheightP (ip z)) (fun z => (hP (ip z)).trans (hP (ip 0)).symm)
    hmatchP η bitsP hbitsP
  have heQ := c.originalInternal_cyclic_binary_energy Q hq K w hw hhigh
    (fun z => hheightQ (iq z)) (fun z => (hQ (iq z)).trans (hQ (iq 0)).symm)
    hmatchQ η bitsQ hbitsQ
  simp only [Polynomial.coeff_sub, Finset.sum_sub_distrib] at heP heQ
  change (∑ z, CP z) - ∑ z, SP z =
    (1/2 : OtherField c.top)*η^2*(transitionCount bitsP 1 : OtherField c.top) at heP
  change (∑ z, CQ z) - ∑ z, SQ z =
    (1/2 : OtherField c.top)*η^2*(transitionCount bitsQ 1 : OtherField c.top) at heQ
  have hder : δ (c.normalCoefficient*S^2*C) = -(1/2 : OtherField c.top)*η^2*
      ((b : OtherField c.top)*transitionCount bitsP 1 -
        (d : OtherField c.top)*transitionCount bitsQ 1) := by
    rw [hd]
    linear_combination -(b : OtherField c.top)*heP + (d : OtherField c.top)*heQ
  have hnonzero := weighted_binary_profile_energy_ne_zero hcop bitsP bitsQ η hη hnonconstant
  have hc : C ≠ 0 := by
    intro hz
    rw [hz, mul_zero, map_zero] at hder
    apply hnonzero
    linear_combination hder
  exact ⟨hder, hc⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
