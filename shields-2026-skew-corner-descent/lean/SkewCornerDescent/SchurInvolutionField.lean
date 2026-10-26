/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SchurInvolutionSupport
import SkewCornerDescent.Matrix.GeneratorDerivation

/-!
# Schur involution on the complete original rational field

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The polynomial automorphism extends to the same full rational function field.
Actual Schur quotients and genuine regular-denominator conditions transport,
without introducing independent response values. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing SkewCornerDescent.Matrix

/-- The original-ring Schur involution extended to its complete fraction field. -/
noncomputable def originalSchurFieldEquiv : actualField ≃+* actualField :=
  IsFractionRing.ringEquivOfRingEquiv schurInvolutionEquiv.toRingEquiv

/-- The fraction-field equivalence agrees with the actual original polynomial embedding. -/
theorem originalSchurFieldEquiv_originalMap (f : Lambda) :
    originalSchurFieldEquiv (originalMap f) = originalMap (schurInvolution f) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap schurInvolutionEquiv.toRingEquiv f

/-- Full fraction-field transpose is involutive, not merely injective on polynomials. -/
theorem originalSchurFieldEquiv_involutive : Function.Involutive originalSchurFieldEquiv := by
  intro f
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective Lambda f
  change originalSchurFieldEquiv (originalSchurFieldEquiv (originalMap a / originalMap b)) =
    originalMap a / originalMap b
  simp only [map_div₀, originalSchurFieldEquiv_originalMap]
  rw [schurInvolution_involutive a, schurInvolution_involutive b]

/-- Every actual full skew function in the original field becomes the function
of its whole transposed diagram, including disconnected functions. -/
theorem originalSchurFieldEquiv_cellSchur (D : Diagram) (hs : IsSkew D) :
    originalSchurFieldEquiv (originalMap (cellSchur D hs)) =
      originalMap (cellSchur (transpose D) (isSkew_transpose hs)) := by
  rw [originalSchurFieldEquiv_originalMap, schurInvolution_skew_cellSchur]

/-- All original polynomial divisibilities transport in both directions. -/
theorem schurInvolution_dvd_iff (f g : Lambda) :
    schurInvolution f ∣ schurInvolution g ↔ f ∣ g := by
  exact map_dvd_iff schurInvolutionEquiv

/-- Genuine regularity at an actual connected selected prime is preserved by
whole-diagram transpose. No lower-polynomial regularity is substituted for it. -/
theorem selected_prime_regularity_transpose {D : Diagram} (hD : IsConnectedSkew D)
    (f : Lambda) :
    ¬ cellSchur (transpose D) (isSkew_transpose hD.1) ∣ schurInvolution f ↔
      ¬ cellSchur D hD.1 ∣ f := by
  rw [← schurInvolution_cellSchur hD, schurInvolution_dvd_iff]

end SkewCornerDescent
