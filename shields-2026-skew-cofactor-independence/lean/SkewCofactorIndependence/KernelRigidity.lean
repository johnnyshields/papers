/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.RestorationRigidity
import SkewCofactorIndependence.DenseDilation
import SkewCofactorIndependence.SymmetricUnitCoordinates

/-!
# Zero kernels and restoration rigidity

The doubled modulus-one specialization after `cor:independent-restorations`
and the vanishing criterion for symmetric dense kernels in the concluding
remarks of `shields-2026-skew-cofactor-independence.tex`.
-/

namespace SkewCofactorIndependence.BetaDiagram
variable {n : ℕ}

/-- A symmetric dense core has no unit relations exactly when at most one position is available. -/
theorem symmetric_unitKernel_eq_bot_iff (D : BetaDiagram (n + 1))
    (hd : D.Dense) (hn : D.Normalized) (hs : D.Symmetric) :
    D.unitKernel = ⊥ ↔ D.availablePositions.card ≤ 1 := by
  rw [← Submodule.finrank_eq_zero, D.symmetric_unitKernel_finrank hd hn hs]
  omega

/-- Doubling preserves a trivial unit kernel on nonsymmetric dense modulus-one cores. -/
theorem dense_double_unitKernel_eq_bot (D : BetaDiagram (n + 1))
    (hn : 1 ≤ n) (hd : D.Dense) (hs : ¬ D.Symmetric)
    (hg : D.normalizeBetas.endpointModulus = 1) (hk : D.unitKernel = ⊥) :
    (D.dilate 2).unitKernel = ⊥ := by
  have h := D.dense_nonsymmetric_dilation_nullity_modulus_one 2 hn hd hs hg
  have hb : Module.finrank ℚ D.unitKernel = 0 := Submodule.finrank_eq_zero.mpr hk
  simp only [hb, Nat.sub_zero] at h
  norm_num at h
  exact h

/-- Every restoration of the doubled core has only translation or rotation mates. -/
theorem dense_double_independent_restorations (D : BetaDiagram (n + 1))
    (hn : 1 ≤ n) (hd : D.Dense) (hs : ¬ D.Symmetric)
    (hg : D.normalizeBetas.endpointModulus = 1) (hk : D.unitKernel = ⊥)
    (Z : Finset ℤ) (hZ : Z ⊆ (D.dilate 2).availablePositions)
    {m : ℕ} (E : BetaDiagram m) (hE : E.Connected)
    (he : E.schur = ((D.dilate 2).restore ((hd.dilate 2).connected (by omega))
      (hd.dilate 2).zeroFree Z hZ).schur) :
    ∃ horder : n + 1 + Z.card = m,
      (((D.dilate 2).restore ((hd.dilate 2).connected (by omega))
        (hd.dilate 2).zeroFree Z hZ).castOrder horder).TranslationEquivalent E ∨
      (((D.dilate 2).restore ((hd.dilate 2).connected (by omega))
        (hd.dilate 2).zeroFree Z hZ).castOrder horder).RotationEquivalent E :=
  (D.dilate 2).independent_restorations (hd.dilate 2)
    (D.dense_double_unitKernel_eq_bot hn hd hs hg hk) Z hZ E hE he

end SkewCofactorIndependence.BetaDiagram
