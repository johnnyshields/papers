/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicUnitPhase
import SkewCornerDescent.TruncatedUnitTorsion

/-!
# Finite normalized proper-core phase periodicity

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`). Common
self-product jets and periodic neighboring mixed-product jets force both core
jets periodic. Unit ratios are computed in the actual finite quotient, then
lifted to normalized series and discharged by characteristic-zero unit torsion.
Sorry-free.
-/

namespace SkewCornerDescent

private noncomputable def normalizedSeriesUnit {F : Type*} [Field F]
    (A : PowerSeries F) (hA : PowerSeries.constantCoeff A = 1) : (PowerSeries F)ˣ where
  val := A
  inv := A⁻¹
  val_inv := PowerSeries.mul_inv_cancel A (by rw [hA]; exact one_ne_zero)
  inv_val := PowerSeries.inv_mul_cancel A (by rw [hA]; exact one_ne_zero)

/-- Normalized proper-core jets with common self-products and periodic mixed
neighbors repeat at the phase shift. No full-series product equality is assumed. -/
theorem truncated_core_phase_periodic {F : Type*} [Field F] [CharZero F]
    (r b N : ℕ) [NeZero (r * b)] (A B : ZMod (r * b) → PowerSeries F)
    (hA : ∀ i, PowerSeries.constantCoeff (A i) = 1)
    (hB : ∀ i, PowerSeries.constantCoeff (B i) = 1)
    (hself : ∀ i k, k < N → PowerSeries.coeff k (A i * B i) =
      PowerSeries.coeff k (A 0 * B 0))
    (hedge : ∀ i k, k < N → PowerSeries.coeff k (A i * B (i + 1)) =
      PowerSeries.coeff k (A (i + r) * B (i + r + 1))) :
    ∀ i k, k < N →
      PowerSeries.coeff k (A (i + r)) = PowerSeries.coeff k (A i) ∧
      PowerSeries.coeff k (B (i + r)) = PowerSeries.coeff k (B i) := by
  classical
  let I : Ideal (PowerSeries F) := Ideal.span {PowerSeries.X ^ N}
  let q := Ideal.Quotient.mk I
  let UA := fun i => normalizedSeriesUnit (A i) (hA i)
  let UB := fun i => normalizedSeriesUnit (B i) (hB i)
  let QA := fun i => Units.map q.toMonoidHom (UA i)
  let QB := fun i => Units.map q.toMonoidHom (UB i)
  have hjet (p t : PowerSeries F)
      (hcoeff : ∀ k < N, PowerSeries.coeff k p = PowerSeries.coeff k t) : q p = q t := by
    apply Ideal.Quotient.eq.mpr
    change p - t ∈ Ideal.span {PowerSeries.X ^ N}
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hcoeff k hk, sub_self]
  have hselfQ (i) : QA i * QB i = QA 0 * QB 0 := by
    apply Units.ext
    change q (A i) * q (B i) = q (A 0) * q (B 0)
    rw [← map_mul, ← map_mul]
    exact hjet _ _ (hself i)
  have hedgeQ (i) : QA i * QB (i + 1) = QA (i + r) * QB (i + r + 1) := by
    apply Units.ext
    change q (A i) * q (B (i + 1)) = q (A (i + r)) * q (B (i + r + 1))
    rw [← map_mul, ← map_mul]
    exact hjet _ _ (hedge i)
  have hpower := cyclic_core_ratio_power r b QA QB hselfQ hedgeQ
  have hb : 0 < b := Nat.pos_of_ne_zero (by
    intro hb
    have hM := NeZero.ne (r * b)
    exact hM (by rw [hb, Nat.mul_zero]))
  have hperiodA (i) : ∀ k < N,
      PowerSeries.coeff k (A (i + r)) = PowerSeries.coeff k (A i) := by
    let Z := A (i + r) * (A i)⁻¹
    have hq := congrArg (fun u : (PowerSeries F ⧸ I)ˣ => (u : PowerSeries F ⧸ I)) (hpower i)
    change (q (A (i + r)) * q ((A i)⁻¹)) ^ b = 1 at hq
    rw [← map_mul, ← map_pow] at hq
    have hd : PowerSeries.X ^ N ∣ Z ^ b - 1 := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq.mp
      simpa only [map_one] using hq
    have hZ : PowerSeries.constantCoeff Z = 1 := by
      rw [map_mul, PowerSeries.constantCoeff_inv, hA, hA]
      simp
    have hnorm := normalized_unit_power_dvd Z b N hb hZ hd
    obtain ⟨W, hW⟩ := hnorm
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
  intro i k hk
  refine ⟨hperiodA i k hk, ?_⟩
  have hright := unit_jet_product_right (A i) (B i) (A (i + r)) (B (i + r)) N
    (by rw [hA]; exact one_ne_zero)
    (fun k hk => (hperiodA i k hk).symm)
    (fun k hk => (hself i k hk).trans (hself (i + r) k hk).symm)
  exact (hright k hk).symm

end SkewCornerDescent
