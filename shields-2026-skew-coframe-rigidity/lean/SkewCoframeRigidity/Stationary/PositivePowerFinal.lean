/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.UnitCase.Main

/-!
# `sc:positive-power`, assembled

The span `L ≥ 2` and cell cases are in `PositivePower`; the unit case is `unit_case_main`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- `sc:positive-power`. -/
theorem positive_power_main {A B : BetaDiagram (n + 1)} (hA : A.Connected)
    (hAn : A.col (Fin.last n) = 0) (hBn : B.col (Fin.last n) = 0) (h : A.schur = B.schur)
    {p : ℕ} (hp : 2 ≤ p) (P Q : ℚ[X]) (hQ : Q ≠ 0)
    (heq : ∀ k < 2 * span A, PowerSeries.coeff k
      (((clippedOp (span A) (coframe A) (coframe B) (PowerSeries.X * letterSeries ^ p) :
          CohField[X]) : PowerSeries CohField) +
        PowerSeries.X * ((defect A B : CohField[X]) : PowerSeries CohField) * potential P Q) = 0) :
    A = B := by
  by_contra hne
  have hB : B.Connected := A.connected_of_schur_eq B hA h
  obtain ⟨-, -, hs, hq, hd, -⟩ := coequal_data hA h
  obtain ⟨hM, hn, hcf, hdeg, -, hcop, -⟩ := coequal_distinct hA hAn hBn h hne
  obtain ⟨sD, sE, hm, hg, hrel⟩ := pole_relation hA hB hn hs hM hcf hdeg hcop hq hd hp P Q hQ heq
  rcases Nat.lt_or_ge sD.c.L 2 with hl | hl
  · have : sD.c.L = 0 ∨ sD.c.L = 1 := by omega
    rcases this with h0 | h1
    · exact unit_case_main hA hB hAn hBn h hn hs hM hcf hdeg hcop hq hd hp P Q hQ heq sD sE hm hg hrel h0
    · exact cell_case hA hB hn hs hM hcf hdeg hcop hq hd hp P Q hQ heq sD sE hm hg hrel h1
  · apply ratio_not_mem sD.c hp hl
    have : sD.c.ratio = -PowerSeries.constantCoeff (potential P Q) := by linear_combination hrel
    rw [this]
    exact (lowerField _).neg_mem (potential_const_mem _ (by omega) P Q)

/-- The rational potential `r(H) = P(H) / Q(H)` evaluated at a power series. -/
noncomputable def ratSeries {L : Type*} [Field L] [Algebra ℚ L] (P Q : ℚ[X]) (H : PowerSeries L) :
    PowerSeries L :=
  Polynomial.aeval H P * (Polynomial.aeval H Q)⁻¹

/-- `sc:positive-power`. -/
theorem positive_power {n : ℕ} {A B : BetaDiagram (n + 1)} (hA : A.Connected)
    (hAn : A.col (Fin.last n) = 0) (hBn : B.col (Fin.last n) = 0) (h : A.schur = B.schur)
    {p : ℕ} (hp : 2 ≤ p) (P Q : ℚ[X]) (hQ : Q ≠ 0)
    (heq : ∀ k < 2 * span A,
      PowerSeries.coeff k
        (((clippedOp (span A) (coframe A) (coframe B)
            (PowerSeries.X * letterSeries ^ p) : CohField[X]) : PowerSeries CohField) +
          PowerSeries.X * ((defect A B : CohField[X]) : PowerSeries CohField) *
            ratSeries P Q letterSeries) = 0) :
    A = B :=
  positive_power_main hA hAn hBn h hp P Q hQ heq

end SkewCoframeRigidity.Coframe
