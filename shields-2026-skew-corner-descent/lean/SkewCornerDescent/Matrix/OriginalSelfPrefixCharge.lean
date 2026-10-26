/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalSelfJet
import SkewCornerDescent.Matrix.NormalPrefixChargeFactorization
import SkewCornerDescent.Matrix.OriginalNormalResidueCycles

/-!
# Complete actual self-profile prefix charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every original internal self-product coefficient keeps its integer Laurent
offset and actual inverse residue. The original raw/chart producer supplies
the full onsite normal correction, including selected resolving directions.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Full self-profile coefficients at the actual internal prefix positions,
with the additional original diagonal inverse retained. -/
noncomputable def originalSelfPrefixCharge {n : ℕ} (P : Profile n) (J : ℕ+)
    (T : ℕ) (hT : T ≤ originalSelectedCount (hD := hD) P - 1) : OtherField c.top :=
  ∑ s : Fin T,
    let i : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨s.val, s.isLt.trans_le hT⟩
    let p := c.originalInternalEndpointProfiles P i
    ((p.1 * p.2).toLaurent).coeff
      (originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) - (J : ℤ)) *
      (c.originalInternalResidue P i)⁻¹

/-- The full self-profile prefix has its actual chart-gradient sum plus the
complete onsite first-normal correction, with no assumed jet identity. -/
theorem originalSelfPrefixCharge_split {n : ℕ} (P : Profile n) (J : ℕ+)
    (T : ℕ) (hT : T ≤ originalSelectedCount (hD := hD) P - 1) :
    c.originalSelfPrefixCharge P J T hT =
      (∑ s : Fin T, residueChartDeriv c.top J
        (c.originalInternalResidue P ⟨s.val, s.isLt.trans_le hT⟩) *
          (c.originalInternalResidue P ⟨s.val, s.isLt.trans_le hT⟩)⁻¹) +
      c.residueMap (pderiv J (cellSchur D hD.1)) *
        normalOnsitePrefixCharge ((c.originalInternalResponseMatrix P).map c.normalSeries)
          T hT := by
  unfold originalSelfPrefixCharge normalOnsitePrefixCharge
  dsimp only
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [c.originalInternal_self_chart_correction P ⟨s.val, s.isLt.trans_le hT⟩ J,
    c.originalInternal_normal_constant P]
  have hm : ((c.originalInternalResponseMatrix P).map c.normalSeries)
      ⟨s.val, s.isLt.trans_le hT⟩ ⟨s.val, s.isLt.trans_le hT⟩ =
      c.normalSeries (c.originalInternalResponseMatrix P
        ⟨s.val, s.isLt.trans_le hT⟩ ⟨s.val, s.isLt.trans_le hT⟩) := rfl
  rw [hm]
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
