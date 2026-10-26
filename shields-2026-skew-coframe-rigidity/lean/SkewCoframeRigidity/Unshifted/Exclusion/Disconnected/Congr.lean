/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Branch
import SkewCoframeRigidity.Unshifted.Components
import SkewCoframeRigidity.Unshifted.Endpoints
import SkewCoframeRigidity.Coframe.Atlas

/-!
# Locality of the coframe and of `α` in the letters

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner).  The coframe of a diagram of span `L` reads only
the letters below `L`; the coordinate `α_{E,p}` of a component of span `L` reads only the letters
up to `L + 1`.  The Jacobi–Trudi determinant of every diagram is nonzero at the generic letters.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem topVecOf_congr {K : Type*} [Zero K] {h h' : ℕ → K} (D : BetaDiagram (n + 1))
    (hh : ∀ k, k < span D → h k = h' k) : topVecOf h D = topVecOf h' D := by
  ext i
  simp only [topVecOf]
  have h1 := rowPos_cast D i
  have h2 := rowPos_lt_span D i
  have h3 := rowPos_pos D i
  unfold letterOf
  split_ifs with hneg
  · rfl
  · apply hh
    have := col_last_le D i.succ
    omega

theorem coframeOf_congr {K : Type*} [Field K] {h h' : ℕ → K} (D : BetaDiagram (n + 1))
    (hh : ∀ k, k < span D → h k = h' k) : coframeOf h D = coframeOf h' D := by
  have hP : properMatrixOf h D = properMatrixOf h' D :=
    properMatrixOf_congr D fun k hk => hh k (by omega)
  have hT : topVecOf h D = topVecOf h' D := topVecOf_congr D hh
  unfold coframeOf coframeVecOf
  rw [hP, hT]

theorem coeff_seriesOf_pow_congr {K : Type*} [CommRing K] {h h' : ℕ → K} {N : ℕ}
    (hh : ∀ k ≤ N, h k = h' k) (p : ℕ) {i : ℕ} (hi : i ≤ N) :
    PowerSeries.coeff i (seriesOf h ^ p) = PowerSeries.coeff i (seriesOf h' ^ p) := by
  have hd : (PowerSeries.X ^ (N + 1) : PowerSeries K) ∣ seriesOf h - seriesOf h' := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    rw [map_sub]
    simp only [seriesOf, PowerSeries.coeff_mk]
    rw [hh j (by omega), sub_self]
  have := hd.trans (sub_dvd_pow_sub_pow (seriesOf h) (seriesOf h') p)
  rw [PowerSeries.X_pow_dvd_iff] at this
  have := this i (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.mp this

theorem coeff_mul_congr_left {K : Type*} [CommRing K] {F F' G : PowerSeries K} {N : ℕ}
    (hF : ∀ i ≤ N, PowerSeries.coeff i F = PowerSeries.coeff i F') {i : ℕ} (hi : i ≤ N) :
    PowerSeries.coeff i (F * G) = PowerSeries.coeff i (F' * G) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [hF x.1 (by omega)]

theorem alphaOf_congr {K : Type*} [CommRing K] {h h' : ℕ → K} (G : K[X]) (p L : ℕ)
    (hh : ∀ k ≤ L + 1, h k = h' k) : alphaOf h G p L = alphaOf h' G p L := by
  have s1 : ∀ i ≤ L + 1, PowerSeries.coeff i (seriesOf h) = PowerSeries.coeff i (seriesOf h') := by
    intro i hi; simp only [seriesOf, PowerSeries.coeff_mk]; exact hh i hi
  have h0 := hh 0 (by omega)
  have h1 := hh 1 (by omega)
  unfold alphaOf
  rw [h0, h1]
  congr 1
  · rw [sub_mul, sub_mul, map_sub, map_sub]
    congr 1
    · exact coeff_mul_congr_left (F := seriesOf h ^ p) (F' := seriesOf h' ^ p)
        (fun i hi => coeff_seriesOf_pow_congr hh p hi) le_rfl
    · rw [mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
      congr 1
      exact coeff_mul_congr_left s1 le_rfl
  · congr 1
    exact coeff_mul_congr_left s1 (by omega)

theorem schurOf_cohLetters_ne_zero {m : ℕ} (E : BetaDiagram m) : schurOf cohLetters E ≠ 0 := by
  rw [← algebraMap_cohSchur]
  refine (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2 ?_
  intro h
  have := congrArg physSpec h
  rw [map_zero] at this
  change physSpec (schurOf (MvPolynomial.X : ℕ → CohRing) E) = 0 at this
  rw [physSpec_schurOf] at this
  exact E.schur_ne_zero (physInclude_injective (by simpa using this))

/-- The port is the top proper row. -/
theorem rowPos_zero_succ {D : BetaDiagram (n + 1)} (hDn : D.col (Fin.last n) = 0)
    (hport : ∃ i, rowPos D i + 1 = span D) (hn : 0 < n) :
    rowPos D ⟨0, hn⟩ + 1 = span D := by
  obtain ⟨i, hi⟩ := hport
  have h1 : rowPos D i ≤ rowPos D ⟨0, hn⟩ := by
    have := D.row_strictAnti.antitone (show (⟨0, hn⟩ : Fin n).succ ≤ i.succ from
      Fin.succ_le_succ_iff.mpr (Fin.mk_le_of_le_val (Nat.zero_le _)))
    have a := rowPos_cast D i
    have b := rowPos_cast D ⟨0, hn⟩
    omega
  have := rowPos_lt_span D ⟨0, hn⟩
  omega

end SkewCoframeRigidity.Unshifted
