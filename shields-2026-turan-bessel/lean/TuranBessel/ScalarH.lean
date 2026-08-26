/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity

/-!
# The second diagonal direction as a scalar quadratic

Formalizes `shields-2026-turan-bessel.tex`, «Classical scalar Bessel
directions» (`sec:scalar`, `prop:scalar-H`), in the ratio variable.

Writing `r_ν(z) = z I_{ν+1}(z)/I_ν(z)`, the modified Bessel equation turns the
second diagonal entry into a quadratic (`eq:H-r-forms`),
```
  H_ν^{(κ)} = r_ν² + 2(ν+κ) r_ν - z² .
```
Everything `prop:scalar-H` then asserts is a statement about that quadratic and
about the ratio recurrence `R_{ν+1} = R_ν^{-1} - 2(ν+1)/z`, so it is proved here
for a real variable `r`, with no Bessel function involved:

* `Hratio_pos_iff` — positivity is exactly `r` exceeding the positive root
  (`eq:H-Amos-general`), and at `κ = 1` the Amos-type bound
  `eq:Amos-bound-exact`;
* `Hratio_eq_turan` — the Turánian form `eq:H-turan-exact`,
  `z² R(R - R_{ν+1})`, from the recurrence alone;
* `Hratio_pos_of_one_le` — the `κ ≥ 1` half of `eq:H-kappa-global`, from the
  shift `H^{(κ)} = H^{(1)} + 2(κ-1) r`.

The identification of `H_ν^{(κ)}` with this quadratic, and the `κ < 1` half of
`eq:H-kappa-global` (an ascending-series expansion at `z ↓ 0`), need the modified
Bessel functions; the coefficient-level `κ < 1` failure is proved in `Threshold`.

Sorry-free and axiom-clean.
-/

namespace TuranBessel

/-! ### The quadratic and its positive root -/

/-- `H_ν^{(κ)}` in the ratio variable `r` (`eq:H-r-forms`). -/
noncomputable def Hratio (ν κ z r : ℝ) : ℝ := r ^ 2 + 2 * (ν + κ) * r - z ^ 2

/-- The positive root of `r² + 2c r - z²`, i.e. the Amos-type lower bound for
`r_ν` (`eq:H-Amos-general`, `eq:Amos-bound-exact`). -/
noncomputable def amosRoot (c z : ℝ) : ℝ := Real.sqrt (c ^ 2 + z ^ 2) - c

theorem sqrt_sq_add_sq_gt {c z : ℝ} (hz : z ≠ 0) : |c| < Real.sqrt (c ^ 2 + z ^ 2) := by
  have hz2 : 0 < z ^ 2 := by
    rcases lt_trichotomy z 0 with h | h | h
    · nlinarith
    · exact absurd h hz
    · nlinarith
  have h : c ^ 2 < c ^ 2 + z ^ 2 := by linarith
  calc |c| = Real.sqrt (c ^ 2) := (Real.sqrt_sq_eq_abs c).symm
    _ < Real.sqrt (c ^ 2 + z ^ 2) := by
        exact Real.sqrt_lt_sqrt (sq_nonneg c) h

theorem amosRoot_pos {c z : ℝ} (hz : z ≠ 0) : 0 < amosRoot c z := by
  have := sqrt_sq_add_sq_gt (c := c) hz
  have hc : c ≤ |c| := le_abs_self c
  simp only [amosRoot]
  linarith

/-- The root in the rationalized form printed in `eq:H-Amos-general`. -/
theorem amosRoot_eq_div {c z : ℝ} (hz : z ≠ 0) :
    amosRoot c z = z ^ 2 / (c + Real.sqrt (c ^ 2 + z ^ 2)) := by
  have hgt := sqrt_sq_add_sq_gt (c := c) hz
  have hc : -|c| ≤ c := neg_abs_le c
  have hden : 0 < c + Real.sqrt (c ^ 2 + z ^ 2) := by linarith
  have hsq : Real.sqrt (c ^ 2 + z ^ 2) ^ 2 = c ^ 2 + z ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [amosRoot, eq_div_iff (ne_of_gt hden)]
  nlinarith [hsq]

/-- The quadratic factors through its roots. -/
theorem Hratio_eq_factored (ν κ z r : ℝ) :
    Hratio ν κ z r
      = (r - amosRoot (ν + κ) z) * (r + (ν + κ) + Real.sqrt ((ν + κ) ^ 2 + z ^ 2)) := by
  have hsq : Real.sqrt ((ν + κ) ^ 2 + z ^ 2) ^ 2 = (ν + κ) ^ 2 + z ^ 2 :=
    Real.sq_sqrt (by positivity)
  simp only [Hratio, amosRoot]
  nlinarith [hsq]

/-- **`eq:H-Amos-general`.**  For `z ≠ 0` and `r ≥ 0`, the second diagonal
direction is positive exactly when `r` exceeds the positive root. -/
theorem Hratio_pos_iff {ν κ z r : ℝ} (hz : z ≠ 0) (hr : 0 ≤ r) :
    0 < Hratio ν κ z r ↔ amosRoot (ν + κ) z < r := by
  have hgt := sqrt_sq_add_sq_gt (c := ν + κ) hz
  have hc : -|ν + κ| ≤ ν + κ := neg_abs_le _
  have hpos : 0 < r + (ν + κ) + Real.sqrt ((ν + κ) ^ 2 + z ^ 2) := by linarith
  rw [Hratio_eq_factored]
  constructor
  · intro h
    nlinarith
  · intro h
    have : 0 < r - amosRoot (ν + κ) z := by linarith
    exact mul_pos this hpos

/-- **`eq:H-Amos-general` in the ratio `R = r/z`.**  For `z > 0` and `R ≥ 0`,
positivity of `H_ν^{(κ)}` is the quotient bound
`R > z/((ν+κ) + √((ν+κ)² + z²))`. -/
theorem Hratio_pos_iff_ratio {ν κ z R : ℝ} (hz : 0 < z) (hR : 0 ≤ R) :
    0 < Hratio ν κ z (z * R) ↔ z / ((ν + κ) + Real.sqrt ((ν + κ) ^ 2 + z ^ 2)) < R := by
  have hz' : z ≠ 0 := ne_of_gt hz
  have hgt := sqrt_sq_add_sq_gt (c := ν + κ) hz'
  have hc : -|ν + κ| ≤ ν + κ := neg_abs_le _
  have hden : 0 < (ν + κ) + Real.sqrt ((ν + κ) ^ 2 + z ^ 2) := by linarith
  rw [Hratio_pos_iff hz' (by positivity), amosRoot_eq_div hz', div_lt_iff₀ hden,
    div_lt_iff₀ hden]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **`eq:Amos-bound-exact`.**  The `κ = 1` case: `H_ν > 0` is the classical
Amos-type lower bound `R_ν(z) > z/(ν+1+√((ν+1)²+z²))`. -/
theorem Hratio_one_pos_iff_amos {ν z R : ℝ} (hz : 0 < z) (hR : 0 ≤ R) :
    0 < Hratio ν 1 z (z * R) ↔ z / ((ν + 1) + Real.sqrt ((ν + 1) ^ 2 + z ^ 2)) < R :=
  Hratio_pos_iff_ratio hz hR

/-! ### The Turánian form -/

/-- **`eq:H-turan-exact`.**  With `R' = R_{ν+1}` supplied by the ratio recurrence
`R_{ν+1} = R_ν^{-1} - 2(ν+1)/z`, the `κ = 1` quadratic is the shifted
modified-Bessel Turánian `z² R(R - R')`. -/
theorem Hratio_eq_turan {ν z R R' : ℝ} (hz : z ≠ 0) (hR : R ≠ 0)
    (hrec : R' = R⁻¹ - 2 * (ν + 1) / z) :
    z ^ 2 * R * (R - R') = Hratio ν 1 z (z * R) := by
  subst hrec
  simp only [Hratio]
  field

/-! ### The deformation parameter -/

/-- `H^{(κ)} = H^{(1)} + 2(κ-1) r`. -/
theorem Hratio_shift (ν κ z r : ℝ) :
    Hratio ν κ z r = Hratio ν 1 z r + 2 * (κ - 1) * r := by
  simp only [Hratio]; ring

/-- **The `κ ≥ 1` half of `eq:H-kappa-global`.**  Positivity at the endpoint
propagates to every `κ ≥ 1`, because `r_ν > 0`. -/
theorem Hratio_pos_of_one_le {ν κ z r : ℝ} (hκ : 1 ≤ κ) (hr : 0 < r)
    (h : 0 < Hratio ν 1 z r) : 0 < Hratio ν κ z r := by
  rw [Hratio_shift]
  nlinarith

/-- The endpoint bound is the weakest of the family: for `κ ≥ 1` the admissible
region for `r` only grows. -/
theorem amosRoot_antitone {c c' z : ℝ} (h : c ≤ c') : amosRoot c' z ≤ amosRoot c z := by
  simp only [amosRoot]
  have hsq : Real.sqrt (c' ^ 2 + z ^ 2) - Real.sqrt (c ^ 2 + z ^ 2) ≤ c' - c := by
    rcases le_or_gt (Real.sqrt (c' ^ 2 + z ^ 2)) (Real.sqrt (c ^ 2 + z ^ 2)) with hle | hgt
    · linarith
    · have h1 : Real.sqrt (c ^ 2 + z ^ 2) ^ 2 = c ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
      have h2 : Real.sqrt (c' ^ 2 + z ^ 2) ^ 2 = c' ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
      have hc0 : 0 ≤ Real.sqrt (c ^ 2 + z ^ 2) := Real.sqrt_nonneg _
      have hcc : |c| ≤ Real.sqrt (c ^ 2 + z ^ 2) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg z])
      have hle : c ≤ Real.sqrt (c ^ 2 + z ^ 2) := le_trans (le_abs_self c) hcc
      nlinarith
  linarith

/-! ### The rank-one boundary limit -/

/-- **`rem:schur-correction`.**  The `z ↓ 0` limit of the Bessel–Schur matrix is
`((g, 2), (2, 4τ/g))`, whose determinant is `4(τ-1)`: the correction `4/g`
supplies exactly the Schur amount that closes the mixed deficit at the rank-one
boundary, and nothing more. -/
theorem schur_boundary_det {g τ : ℝ} (hg : g ≠ 0) :
    g * (4 * τ / g) - 2 * 2 = 4 * (τ - 1) := by
  field

end TuranBessel
