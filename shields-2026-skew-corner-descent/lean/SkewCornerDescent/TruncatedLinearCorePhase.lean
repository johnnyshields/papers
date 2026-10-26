/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.LinearUnitPhase
import SkewCornerDescent.TruncatedUnitTorsion

/-!
# Finite proper-core phase rigidity from literal window matching

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Internal shifted mixed products and a matched window suffice; no identity at
the actual closure is assumed. All equalities are finite jets, lifted through
the power-series quotient and discharged by characteristic-zero unit torsion.
Sorry-free.
-/

namespace SkewCornerDescent

private noncomputable def linearNormalizedUnit {F : Type*} [Field F]
    (A : PowerSeries F) (hA : PowerSeries.constantCoeff A = 1) : (PowerSeries F)ˣ where
  val := A
  inv := A⁻¹
  val_inv := PowerSeries.mul_inv_cancel A (by rw [hA]; exact one_ne_zero)
  inv_val := PowerSeries.inv_mul_cancel A (by rw [hA]; exact one_ne_zero)

/-- Finite normalized core jets repeat on every internal phase shift when
an actual matched window closes a positive number of those shifts. -/
theorem truncated_linear_core_phase_periodic {F : Type*} [Field F] [CharZero F]
    (r d L N : ℕ) (hd : 0 < d) (hwindowSize : r * d < L)
    (A B : ℕ → PowerSeries F)
    (hA : ∀ i, PowerSeries.constantCoeff (A i) = 1)
    (hB : ∀ i, PowerSeries.constantCoeff (B i) = 1)
    (hself : ∀ i, i < L → ∀ k, k < N → PowerSeries.coeff k (A i * B i) =
      PowerSeries.coeff k (A 0 * B 0))
    (hedge : ∀ i, i + r + 1 < L → ∀ k, k < N →
      PowerSeries.coeff k (A i * B (i + 1)) =
        PowerSeries.coeff k (A (i + r) * B (i + r + 1)))
    (hwindow : ∀ k, k < N → PowerSeries.coeff k (A (r * d)) = PowerSeries.coeff k (A 0)) :
    ∀ i, i + r < L → ∀ k, k < N →
      PowerSeries.coeff k (A (i + r)) = PowerSeries.coeff k (A i) ∧
      PowerSeries.coeff k (B (i + r)) = PowerSeries.coeff k (B i) := by
  classical
  let I : Ideal (PowerSeries F) := Ideal.span {PowerSeries.X ^ N}
  let q := Ideal.Quotient.mk I
  let UA := fun i => linearNormalizedUnit (A i) (hA i)
  let UB := fun i => linearNormalizedUnit (B i) (hB i)
  let QA := fun i => Units.map q.toMonoidHom (UA i)
  let QB := fun i => Units.map q.toMonoidHom (UB i)
  have hjet (p t : PowerSeries F)
      (hc : ∀ k < N, PowerSeries.coeff k p = PowerSeries.coeff k t) : q p = q t := by
    apply Ideal.Quotient.eq.mpr
    change p - t ∈ Ideal.span {PowerSeries.X ^ N}
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hc k hk, sub_self]
  have hselfQ (i) (hi : i < L) : QA i * QB i = QA 0 * QB 0 := by
    apply Units.ext
    change q (A i) * q (B i) = q (A 0) * q (B 0)
    rw [← map_mul, ← map_mul]
    exact hjet _ _ (hself i hi)
  have hedgeQ (i) (hi : i + r + 1 < L) :
      QA i * QB (i + 1) = QA (i + r) * QB (i + r + 1) := by
    apply Units.ext
    change q (A i) * q (B (i + 1)) = q (A (i + r)) * q (B (i + r + 1))
    rw [← map_mul, ← map_mul]
    exact hjet _ _ (hedge i hi)
  have hwindowQ : QA (r * d) = QA 0 := by
    apply Units.ext
    exact hjet _ _ hwindow
  have hpower := linear_core_ratio_power r d L hwindowSize QA QB hselfQ hedgeQ hwindowQ
  have hperiodA (i) (hi : i + r < L) : ∀ k < N,
      PowerSeries.coeff k (A (i + r)) = PowerSeries.coeff k (A i) := by
    let Z := A (i + r) * (A i)⁻¹
    have hq := congrArg (fun u : (PowerSeries F ⧸ I)ˣ => (u : PowerSeries F ⧸ I)) (hpower i hi)
    change (q (A (i + r)) * q ((A i)⁻¹)) ^ d = 1 at hq
    rw [← map_mul, ← map_pow] at hq
    have hdiv : PowerSeries.X ^ N ∣ Z ^ d - 1 := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq.mp
      simpa only [map_one] using hq
    have hZ : PowerSeries.constantCoeff Z = 1 := by
      rw [map_mul, PowerSeries.constantCoeff_inv, hA, hA]
      simp
    obtain ⟨W, hW⟩ := normalized_unit_power_dvd Z d N hd hZ hdiv
    have he : A (i + r) - A i = (Z - 1) * A i := by
      dsimp only [Z]
      rw [sub_mul, mul_assoc, PowerSeries.inv_mul_cancel (A i)
        (by rw [hA]; exact one_ne_zero), mul_one, one_mul]
    have hdA : PowerSeries.X ^ N ∣ A (i + r) - A i := by
      refine ⟨W * A i, ?_⟩
      rw [he, hW, mul_assoc]
    rw [PowerSeries.X_pow_dvd_iff] at hdA
    intro k hk
    exact sub_eq_zero.mp (by simpa only [map_sub] using hdA k hk)
  intro i hi k hk
  refine ⟨hperiodA i hi k hk, ?_⟩
  have hright := unit_jet_product_right (A i) (B i) (A (i + r)) (B (i + r)) N
    (by rw [hA]; exact one_ne_zero)
    (fun k hk => (hperiodA i hi k hk).symm)
    (fun k hk => (hself i (by omega) k hk).trans (hself (i + r) hi k hk).symm)
  exact (hright k hk).symm

end SkewCornerDescent
