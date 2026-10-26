/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Defs
import SkewCoframeRigidity.Unshifted.Exclusion.Shift

/-!
# The expansion of the unshifted identity in the top letter

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`): for a letter sequence `h₀` with `h₀ m = 0`, `m = M - 1`, and a scalar
`u`, the unshifted identity at the letters `h = h₀[m ↦ u]` is the polynomial
`[y^0] + u [y^1] + u² [y^2]` of degree two in `u`, up to a multiple of `z^{2M}`.  Sorry-free.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem coframeOf_coeff_zero (h : ℕ → K) (D : BetaDiagram (n + 1)) : (coframeOf h D).coeff 0 = 1 :=
  uniPoly_coeff_zero_of_pos _ _ (colPos_pos D)

theorem constantCoeff_seriesOf (h : ℕ → K) : PowerSeries.constantCoeff (seriesOf h) = h 0 := rfl

theorem endpointB_congr {h h' : ℕ → K} (D : BetaDiagram (n + 1))
    (hh : ∀ k, k + 1 < span D → h k = h' k) : endpointB h D = endpointB h' D := by
  unfold endpointB
  rw [properMatrixOf_congr D hh]

/-- The coefficient `[y^0]` for a letter sequence `h₀` with `h₀ m = 0`. -/
noncomputable def genY0 (p : ℕ) (h₀ : ℕ → K) (V W : BetaDiagram (n + 1)) : PowerSeries K :=
  Eop p (span V) (coframeOf h₀ V) (coframeOf h₀ W) (seriesOf h₀)

/-- The factor `p (ϑ^{p-1} - h^{p-1}) z^m` for a letter sequence `h₀`. -/
noncomputable def genPDiff (p : ℕ) (h₀ : ℕ → K) (V : BetaDiagram (n + 1)) : PowerSeries K :=
  PowerSeries.C (p : K) * (PowerSeries.C (h₀ 0) ^ (p - 1) - seriesOf h₀ ^ (p - 1)) *
    PowerSeries.X ^ (span V - 1)

/-- The coefficient `[y^1]` for a letter sequence `h₀` with `h₀ m = 0`. -/
noncomputable def genY1 (p : ℕ) (h₀ : ℕ → K) (V W : BetaDiagram (n + 1)) : PowerSeries K :=
  Eop p (span V) (endpointA h₀ V) (coframeOf h₀ W) (seriesOf h₀) +
    Eop p (span V) (coframeOf h₀ V) (endpointB h₀ V) (seriesOf h₀) +
    genPDiff p h₀ V * ((coframeOf h₀ V - coframeOf h₀ W : K[X]) : PowerSeries K)

/-- The coefficient `[y^2]` for a letter sequence `h₀` with `h₀ m = 0`. -/
noncomputable def genY2 (p : ℕ) (h₀ : ℕ → K) (V W : BetaDiagram (n + 1)) : PowerSeries K :=
  Eop p (span V) (endpointA h₀ V) (endpointB h₀ V) (seriesOf h₀) +
    genPDiff p h₀ V * ((endpointA h₀ V - endpointB h₀ V : K[X]) : PowerSeries K)

/-- The unshifted identity at the letters `h₀[m ↦ u]` is `[y^0] + u [y^1] + u² [y^2]` up to
precision `2M`. -/
theorem expand_at {V W : BetaDiagram (n + 1)} {c : ℤ}
    (hr : ∀ i, W.row i = c - V.col i.rev) (hc : ∀ i, W.col i = c - V.row i.rev)
    (hW : W.col (Fin.last n) = 0) (p : ℕ) (hp : 2 ≤ p) (h₀ : ℕ → K)
    (hz : h₀ (span V - 1) = 0) (hm : 3 ≤ span V) (u : K)
    (hD : ∀ k ≤ span V,
      (clippedOp (span V) (coframeOf (Function.update h₀ (span V - 1) u) V)
        (coframeOf (Function.update h₀ (span V - 1) u) W)
        (seriesOf (Function.update h₀ (span V - 1) u))).coeff k = 0)
    (hid : UnshiftedEq p (Function.update h₀ (span V - 1) u) V W) :
    ∀ k < 2 * span V, PowerSeries.coeff k
      (genY0 p h₀ V W + PowerSeries.C u * genY1 p h₀ V W +
        PowerSeries.C (u ^ 2) * genY2 p h₀ V W) = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  set M := span V with hMdef
  set m := M - 1 with hmdef
  have hM : M = m + 1 := by omega
  set h := Function.update h₀ m u with hh
  have hu : h m = u := by rw [hh]; exact Function.update_self _ _ _
  have hspW : span W = M := span_rot hr hc hW
  have hupd0 : Function.update h m 0 = h₀ := by
    rw [hh, Function.update_idem]
    exact Function.update_eq_self_iff.2 hz.symm
  have hlow : ∀ k, k + 1 < M → h k = h₀ k := fun k hk => by
    rw [hh, Function.update_of_ne (by omega)]
  have eV : coframeOf h V = coframeOf h₀ V + C u * endpointA h₀ V := by
    rw [coframeOf_eq h V, ← hMdef, hupd0, endpointA_congr V hlow]
    rw [show h (M - 1) = u from hu]
  have eW : coframeOf h W = coframeOf h₀ W + C u * endpointB h₀ V := by
    rw [coframeOf_rot_eq h hr hc hW, ← hMdef, hupd0, endpointB_congr V hlow]
    rw [show h (M - 1) = u from hu]
  have hs : seriesOf h = seriesOf h₀ + PowerSeries.C u * PowerSeries.X ^ m := by
    ext k
    simp only [seriesOf, hh, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow]
    by_cases hk : k = m
    · subst hk; simp [hz]
    · simp [Function.update_of_ne hk, hk]
  have hG : (coframeOf h V).coeff 0 = 1 := coframeOf_coeff_zero h V
  have hC : (coframeOf h W).coeff 0 = 1 := coframeOf_coeff_zero h W
  have hT := clippedOp_power_expand m q (by omega) (coframeOf h V) (coframeOf h W)
    (seriesOf h₀) u
  rw [← hs, ← hM, hG, hC] at hT
  have hDD : clippedOp M (coframeOf h V) (coframeOf h W) (seriesOf h) =
      clippedOp M (coframeOf h V) (coframeOf h W) (seriesOf h₀) +
        C u * X ^ m * (coframeOf h V - coframeOf h W) := by
    have := clippedOp_X_pow_mul_of_const_one m (coframeOf h V) (coframeOf h W) hG hC
      (PowerSeries.C u)
    rw [← hM] at this
    rw [hs, clippedOp_add_right, this]
    simp
  obtain ⟨w, hw⟩ : (seriesOf h - seriesOf h₀) ∣ seriesOf h ^ (q + 1) - seriesOf h₀ ^ (q + 1) :=
    sub_dvd_pow_sub_pow _ _ _
  have hsub : seriesOf h - seriesOf h₀ = PowerSeries.C u * PowerSeries.X ^ m := by
    rw [hs]; ring
  rw [hsub] at hw
  have hDvd : PowerSeries.X ^ (M + 1) ∣
      ((clippedOp M (coframeOf h V) (coframeOf h W) (seriesOf h) : K[X]) : PowerSeries K) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [Polynomial.coeff_coe]
    exact hD k (by omega)
  obtain ⟨D', hD'⟩ := hDvd
  have key : genY0 (q + 2) h₀ V W + PowerSeries.C u * genY1 (q + 2) h₀ V W +
      PowerSeries.C (u ^ 2) * genY2 (q + 2) h₀ V W =
      ((clippedOp M (coframeOf h V) (coframeOf h W) (seriesOf h ^ (q + 2)) : K[X]) :
        PowerSeries K) - PowerSeries.C ((q + 2 : ℕ) : K) * seriesOf h₀ ^ (q + 1) *
        ((clippedOp M (coframeOf h V) (coframeOf h W) (seriesOf h) : K[X]) : PowerSeries K) := by
    rw [hT, hDD, eV, eW]
    simp only [genY0, genY1, genY2, genPDiff, Eop, clippedOp_expand, Polynomial.coe_add,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_X, map_pow, map_mul, map_add, constantCoeff_seriesOf, ← hMdef, ← hmdef,
      show q + 2 - 1 = q + 1 from rfl]
    simp only [Nat.cast_add, Nat.cast_ofNat, map_add, map_one, map_ofNat, map_natCast, map_mul,
      map_pow]
    push_cast
    ring
  intro k hk
  rw [key]
  have hid' := hid k hk
  rw [show q + 2 - 1 = q + 1 from rfl] at hid'
  have hsplit : seriesOf h ^ (q + 1) *
      ((clippedOp M (coframeOf h V) (coframeOf h W) (seriesOf h) : K[X]) : PowerSeries K) =
      seriesOf h₀ ^ (q + 1) *
        ((clippedOp M (coframeOf h V) (coframeOf h W) (seriesOf h) : K[X]) : PowerSeries K) +
      PowerSeries.X ^ (2 * M) * (PowerSeries.C u * w * D') := by
    rw [sub_eq_iff_eq_add] at hw
    rw [hw, hD']
    have : 2 * M = m + (M + 1) := by omega
    rw [this, pow_add]
    ring
  have hzero : PowerSeries.coeff k (PowerSeries.X ^ (2 * M) * (PowerSeries.C u * w * D')) = 0 := by
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [map_sub, Polynomial.coeff_coe, hid', hsplit, map_add, hzero, add_zero, mul_assoc,
    PowerSeries.coeff_C_mul, sub_self]

end SkewCoframeRigidity.Unshifted
