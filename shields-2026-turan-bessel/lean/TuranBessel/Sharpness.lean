/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.TuranDetKT
import TuranBessel.Bridge
import TuranBessel.BesselLaw

/-!
# Sharpness of the two-parameter quadrant

Formalizes `shields-2026-turan-bessel.tex`, «Reciprocal-gamma formulation and positivity phase
diagram»
(`sec:main`, `thm:two-parameter-coeff`, `cor:bessel-matrix`,
`prop:bessel-sharpness`, `eq:Dnu-kt-def`, `eq:Dkappa-tau-Delta`) and «Classical
scalar Bessel directions» (`sec:scalar`, `prop:scalar-H`, `eq:H-kappa-global`,
`rem:schur-correction`).

Four things, all resting on the general-`(κ,τ)` series of `TuranDetKT`.

* **The `τ` half of `thm:two-parameter-coeff`'s converse.**
  `Phase.DcoeffKT_affine` makes every coefficient affine in `τ` with slope
  `2p_n/g > 0`, and `Phase.DcoeffKT_degree_one_boundary` puts the degree-one zero
  exactly at `τ_cw`.  So `τ < τ_cw` forces the degree-one coefficient strictly
  negative, and on each `κ ≥ 1` slice the theorem is an iff.
* **`eq:Dkappa-tau-Delta` and the `κ,τ ≥ 1` half of `prop:bessel-sharpness`.**
  `H_ν^{(κ)}` is `BesselLaw.besselHkappa`, already carried at general `κ` and
  already tied to `eq:Hnu-kappa`'s log-derivative form there; nothing new is
  needed on that side.  The dictionary identity holds at general `(κ,τ)` for
  exactly the reason it holds at the endpoint: `BesselDictPH.algebra_D` is stated
  in five free reals, and `τ` enters `eq:Ckt-def` only through `τZ²`, so `4τ/g`
  is precisely what that term contributes and the defect is `4Δ^{(κ,τ)}/(gZ⁴)`
  verbatim.  Note the correction is `4τ/g`, not `4/g`, as `eq:bessel-congruence`
  writes it.
  Positivity is then `TuranDetKT.turanDetKT_pos`.  The least-constant converse in
  `κ` needs `lem:large-argument-limit` and is not attempted; the converse in `τ`
  **is** available, from the negative degree-zero coefficient of
  `TuranDetKT.turanDetKT_lam_zero`.
* **The limit clause of `cor:bessel-matrix`, and `rem:schur-correction`.**  Each
  entry is a ratio of series whose value at `λ = 0` is its degree-zero
  coefficient, so the matrix extends continuously to `((g,2),(2,4τ/g))` — rank
  one exactly at `τ = 1`.
* **`eq:H-kappa-global`, both halves.**  The Euler series of `Z` shift the
  parameter rather than the argument, `Z_Θ(a,λ) = λZ(a+1,λ)` and
  `Z_{ΘΘ}(a,λ) = λ(λZ(a+2,λ) + Z(a+1,λ))`, whence
  `H_ν^{(κ)} = 4λ[(κ-1)Z_1/Z - λ(ZZ_2 - Z_1²)/Z²]`.
  **Differs from the paper's route.**  The paper reads the `κ = 1` positivity off the classical
  modified-Bessel Turán inequality; here `Z_1² > ZZ_2` is the midpoint case of
  strict concavity of `a ↦ log Z(a,λ)`, which is `-L_{aa} = A/Z² > 0` — the very
  positivity the paper's own `G_ν` carries.  So the `κ ≥ 1` half becomes
  unconditional rather than cited, and the `κ < 1` half is the `λ ↓ 0` value
  `(κ-1)/a` of the bracket.

Sorry-free.
-/

open Filter Topology Set

namespace TuranBessel

variable {a κ τ ν x lam : ℝ}

/-! ## The `τ` half of `thm:two-parameter-coeff` -/

/-- Below the wall the degree-one coefficient is strictly negative: `DcoeffKT` is
affine in `τ` with slope `2p_1/g > 0` and vanishes at `τ_cw`. -/
theorem DcoeffKT_degree_one_neg_of_lt (ha : 0 < a) (κ : ℝ) (hτ : τ < tauCw a κ) :
    DcoeffKT a κ τ 1 < 0 := by
  have hg := trigamma_pos ha
  have hp := pRed_pos ha 1
  have hid : DcoeffKT a κ τ 1
      = DcoeffKT a κ (tauCw a κ) 1 + 2 * ((τ - tauCw a κ) / trigamma a) * pRed a 1 := by
    rw [DcoeffKT_affine ha, DcoeffKT_affine ha]
    have : 2 * ((τ - 1) / trigamma a) * pRed a 1
        = 2 * ((tauCw a κ - 1) / trigamma a) * pRed a 1
          + 2 * ((τ - tauCw a κ) / trigamma a) * pRed a 1 := by
      field
    linarith
  rw [hid, DcoeffKT_degree_one_boundary ha κ, zero_add]
  have hneg : (τ - tauCw a κ) / trigamma a < 0 := div_neg_of_neg_of_pos (by linarith) hg
  nlinarith

/-- **`thm:two-parameter-coeff`, the strict iff on a `κ ≥ 1` slice.**  Every
positive-degree coefficient of `Δ^{(κ,τ)}` is strictly positive exactly when
`τ > τ_cw(a,κ)`.

The remaining exclusion of `κ < 1` at fixed `a` is not available here: it runs
through `lem:large-argument-limit`, whose two-term Hankel expansion has no
substrate in the pinned Mathlib.  `Threshold.MDkappa_neg_exists` gives the weaker
statement that for each `κ < 1` *some* `a` fails. -/
theorem DcoeffKT_pos_iff_of_one_le (ha : 0 < a) (hκ : 1 ≤ κ) :
    (∀ n : ℕ, 1 ≤ n → 0 < DcoeffKT a κ τ n) ↔ tauCw a κ < τ := by
  refine ⟨fun h => ?_, fun h n hn => DcoeffKT_pos_of_gt ha hκ h hn⟩
  by_contra hle
  rw [not_lt] at hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact absurd (heq ▸ DcoeffKT_degree_one_boundary ha κ) (h 1 le_rfl).ne'
  · exact absurd (DcoeffKT_degree_one_neg_of_lt ha κ hlt) (by linarith [h 1 le_rfl])

/-- **`thm:two-parameter-coeff`, the non-strict iff on a `κ ≥ 1` slice.** -/
theorem DcoeffKT_nonneg_iff_of_one_le (ha : 0 < a) (hκ : 1 ≤ κ) :
    (∀ n : ℕ, 1 ≤ n → 0 ≤ DcoeffKT a κ τ n) ↔ tauCw a κ ≤ τ := by
  refine ⟨fun h => ?_, fun h n hn => DcoeffKT_nonneg_of_ge ha hκ h hn⟩
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (DcoeffKT_degree_one_neg_of_lt ha κ hlt) (by linarith [h 1 le_rfl])

/-! ## Values and continuity of the `Z`-series in `λ` -/

/-- Every weighted `Z`-series collapses to its degree-zero term at `λ = 0`. -/
theorem tsum_weighted_zterm_lam_zero (a : ℝ) (c : ℕ → ℝ) :
    ∑' k : ℕ, c k * zterm a (0 : ℝ) k = c 0 / Real.Gamma a := by
  have hz : ∀ k : ℕ, k ≠ 0 → c k * zterm a (0 : ℝ) k = 0 := by
    intro k hk
    rw [zterm, zero_pow hk, zero_div, mul_zero]
  rw [tsum_eq_single 0 (fun k hk => hz k hk), zterm]
  simp [div_eq_mul_inv]

theorem Zfun_lam_zero (a : ℝ) : Zfun a 0 = 1 / Real.Gamma a := by
  rw [Zfun_eq_weighted, tsum_weighted_zterm_lam_zero]

theorem ZEulerSeries_lam_zero (a : ℝ) : ZEulerSeries a 0 = 0 := by
  rw [ZEulerSeries, tsum_weighted_zterm_lam_zero a (fun k => (k : ℝ))]
  simp

theorem ZEuler2Series_lam_zero (a : ℝ) : ZEuler2Series a 0 = 0 := by
  rw [ZEuler2Series, tsum_weighted_zterm_lam_zero a (fun k => ((k : ℝ)) ^ 2)]
  simp

theorem ZParamEulerSeries_lam_zero (a : ℝ) : ZParamEulerSeries a 0 = 0 := by
  rw [ZParamEulerSeries,
    tsum_weighted_zterm_lam_zero a (fun k => -realDigamma (a + (k : ℝ)) * (k : ℝ))]
  simp

theorem Zparam1_lam_zero (ha : 0 < a) :
    Zparam1 a 0 = -realDigamma a / Real.Gamma a := by
  rw [Zparam1_eq ha, tsum_weighted_zterm_lam_zero]
  simp

theorem Zparam2_lam_zero (ha : 0 < a) :
    Zparam2 a 0 = (realDigamma a ^ 2 - trigamma a) / Real.Gamma a := by
  rw [Zparam2_eq ha, tsum_weighted_zterm_lam_zero]
  simp

/-- `A(a,0) = ψ₁(a)/Γ(a)²`: the degree-zero coefficient `S_0α_0` of `eq:alpha`. -/
theorem Afun_lam_zero (ha : 0 < a) : Afun a 0 = trigamma a / Real.Gamma a ^ 2 := by
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  rw [Afun, Zparam1_lam_zero ha, Zparam2_lam_zero ha, Zfun_lam_zero]
  field

/-- `B(a,0) = 1/Γ(a)²`: the degree-zero coefficient `S_0β_0` of `eq:beta`. -/
theorem Bseries_lam_zero (a : ℝ) : Bseries a 0 = 1 / Real.Gamma a ^ 2 := by
  rw [Bseries, ZEulerSeries_lam_zero, ZParamEulerSeries_lam_zero, Zfun_lam_zero]
  ring

/-- Continuity in `λ` of a weighted `Z`-series with a polynomially bounded weight. -/
theorem continuousAt_weightedZ (ha : 0 < a) {c : ℕ → ℝ} {C : ℝ} (j : ℕ)
    (hc : ∀ k, |c k| ≤ C * ((k : ℝ) + 1) ^ j) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => ∑' k : ℕ, c k * zterm a y k) lam :=
  (hasDerivAt_weightedZ ha j hc lam).continuousAt

private theorem bd_one (k : ℕ) : |(1 : ℝ)| ≤ 1 * ((k : ℝ) + 1) ^ 2 := by
  have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  simpa using this

private theorem bd_idx (k : ℕ) : |(k : ℝ)| ≤ 1 * ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [abs_of_nonneg hk]; nlinarith

private theorem bd_sq (k : ℕ) : |((k : ℝ)) ^ 2| ≤ 1 * ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [abs_of_nonneg (by positivity)]; nlinarith

private theorem bd_psi (ha : 0 < a) (k : ℕ) :
    |(-realDigamma (a + (k : ℝ)))| ≤ (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1) ^ 2 := by
  have h := abs_realDigamma_add_nat_le_linear ha k
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hC : 0 ≤ 2 * |realDigamma a| + 1 / a := by positivity
  have hstep : (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1)
      ≤ (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hC
  rw [abs_neg]
  linarith [h, hstep]

private theorem bd_psi_idx (ha : 0 < a) (k : ℕ) :
    |(-realDigamma (a + (k : ℝ)) * (k : ℝ))|
      ≤ (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1) ^ 2 := by
  have h := abs_realDigamma_add_nat_le_linear ha k
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hC : 0 ≤ 2 * |realDigamma a| + 1 / a := by positivity
  rw [abs_mul, abs_neg, abs_of_nonneg hk]
  have hstep : |realDigamma (a + (k : ℝ))| * (k : ℝ)
      ≤ (2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1) * (k : ℝ) :=
    mul_le_mul_of_nonneg_right h hk
  nlinarith [hstep, hC]

private theorem bd_ddpsi (ha : 0 < a) (k : ℕ) :
    |realDigamma (a + (k : ℝ)) ^ 2 - trigamma (a + (k : ℝ))|
      ≤ ((2 * |realDigamma a| + 1 / a) ^ 2 + trigamma a) * ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hak : 0 < a + (k : ℝ) := by linarith
  have h := abs_realDigamma_add_nat_le_linear ha k
  have hC : 0 ≤ 2 * |realDigamma a| + 1 / a := by positivity
  have hsq : realDigamma (a + (k : ℝ)) ^ 2
      ≤ (2 * |realDigamma a| + 1 / a) ^ 2 * ((k : ℝ) + 1) ^ 2 := by
    have h2 := pow_le_pow_left₀ (abs_nonneg (realDigamma (a + (k : ℝ)))) h 2
    rw [sq_abs] at h2
    calc realDigamma (a + (k : ℝ)) ^ 2
        ≤ ((2 * |realDigamma a| + 1 / a) * ((k : ℝ) + 1)) ^ 2 := h2
      _ = (2 * |realDigamma a| + 1 / a) ^ 2 * ((k : ℝ) + 1) ^ 2 := by ring
  have htri : trigamma (a + (k : ℝ)) ≤ trigamma a := trigamma_anti ha (by linarith)
  have htri0 : 0 ≤ trigamma (a + (k : ℝ)) := (trigamma_pos hak).le
  have hTa : 0 ≤ trigamma a := (trigamma_pos ha).le
  have hone : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hsq0 : 0 ≤ realDigamma (a + (k : ℝ)) ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

theorem continuousAt_Zfun_lam (ha : 0 < a) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => Zfun a y) lam := by
  have hfun : (fun y : ℝ => Zfun a y) = fun y : ℝ => ∑' k : ℕ, (1 : ℝ) * zterm a y k := by
    funext y; exact Zfun_eq_weighted a y
  rw [hfun]
  exact continuousAt_weightedZ ha (C := 1) 2 (fun k => bd_one k) lam

theorem continuousAt_ZEulerSeries_lam (ha : 0 < a) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => ZEulerSeries a y) lam :=
  continuousAt_weightedZ ha (C := 1) 2 (fun k => bd_idx k) lam

theorem continuousAt_ZEuler2Series_lam (ha : 0 < a) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => ZEuler2Series a y) lam :=
  continuousAt_weightedZ ha (C := 1) 2 (fun k => bd_sq k) lam

theorem continuousAt_ZParamEulerSeries_lam (ha : 0 < a) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => ZParamEulerSeries a y) lam :=
  continuousAt_weightedZ ha (C := 2 * |realDigamma a| + 1 / a) 2 (fun k => bd_psi_idx ha k) lam

theorem continuousAt_Zparam1_lam (ha : 0 < a) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => Zparam1 a y) lam := by
  have hfun : (fun y : ℝ => Zparam1 a y)
      = fun y : ℝ => ∑' k : ℕ, (-realDigamma (a + (k : ℝ))) * zterm a y k := by
    funext y; exact Zparam1_eq ha y
  rw [hfun]
  exact continuousAt_weightedZ ha (C := 2 * |realDigamma a| + 1 / a) 2 (fun k => bd_psi ha k) lam

theorem continuousAt_Zparam2_lam (ha : 0 < a) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => Zparam2 a y) lam := by
  have hfun : (fun y : ℝ => Zparam2 a y)
      = fun y : ℝ =>
        ∑' k : ℕ, (realDigamma (a + (k : ℝ)) ^ 2 - trigamma (a + (k : ℝ))) * zterm a y k := by
    funext y; exact Zparam2_eq ha y
  rw [hfun]
  exact continuousAt_weightedZ ha
    (C := (2 * |realDigamma a| + 1 / a) ^ 2 + trigamma a) 2 (fun k => bd_ddpsi ha k) lam

theorem continuousAt_Afun_lam (ha : 0 < a) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => Afun a y) lam := by
  have hfun : (fun y : ℝ => Afun a y)
      = fun y : ℝ => Zparam1 a y ^ 2 - Zfun a y * Zparam2 a y := rfl
  rw [hfun]
  exact ((continuousAt_Zparam1_lam ha lam).pow 2).sub
    ((continuousAt_Zfun_lam ha lam).mul (continuousAt_Zparam2_lam ha lam))

theorem continuousAt_Bseries_lam (ha : 0 < a) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => Bseries a y) lam := by
  have hfun : (fun y : ℝ => Bseries a y)
      = fun y : ℝ => Zfun a y * Zfun a y + Zfun a y * ZParamEulerSeries a y
          - Zparam1 a y * ZEulerSeries a y := by
    funext y
    rw [Bseries, ZParamSeries_eq_deriv ha y, Zparam1]
  rw [hfun]
  exact (((continuousAt_Zfun_lam ha lam).mul (continuousAt_Zfun_lam ha lam)).add
    ((continuousAt_Zfun_lam ha lam).mul (continuousAt_ZParamEulerSeries_lam ha lam))).sub
    ((continuousAt_Zparam1_lam ha lam).mul (continuousAt_ZEulerSeries_lam ha lam))

theorem continuousAt_Cseries_lam (ha : 0 < a) (g κ τ : ℝ) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => Cseries a g κ τ y) lam := by
  have hZ := continuousAt_Zfun_lam ha lam
  have hE := continuousAt_ZEulerSeries_lam ha lam
  have hE2 := continuousAt_ZEuler2Series_lam ha lam
  have h : ContinuousAt (fun y : ℝ => τ * (Zfun a y * Zfun a y)
      + g * (κ * (Zfun a y * ZEulerSeries a y) - Zfun a y * ZEuler2Series a y
          + ZEulerSeries a y * ZEulerSeries a y)) lam :=
    (continuousAt_const.mul (hZ.mul hZ)).add
      (continuousAt_const.mul (((continuousAt_const.mul (hZ.mul hE)).sub
        (hZ.mul hE2)).add (hE.mul hE)))
  exact h

theorem continuousAt_turanDetKT_lam (ha : 0 < a) (κ τ : ℝ) (lam : ℝ) :
    ContinuousAt (fun y : ℝ => turanDetKT a κ τ y) lam := by
  have h : ContinuousAt (fun y : ℝ =>
      Afun a y * Cseries a (trigamma a) κ τ y - trigamma a * Bseries a y ^ 2) lam :=
    ((continuousAt_Afun_lam ha lam).mul
        (continuousAt_Cseries_lam ha (trigamma a) κ τ lam)).sub
      (continuousAt_const.mul ((continuousAt_Bseries_lam ha lam).pow 2))
  exact h

/-- The same, read in the Bessel argument `x` through `λ = (x/2)²`, at `x = 0`. -/
theorem continuousAt_turanDetKT_arg (ha : 0 < a) (κ τ : ℝ) :
    ContinuousAt (fun y : ℝ => turanDetKT a κ τ ((y / 2) ^ 2)) 0 := by
  have hinner : ContinuousAt (fun y : ℝ => (y / 2) ^ 2) 0 :=
    ((continuous_id.div_const 2).pow 2).continuousAt
  have houter : ContinuousAt (fun y : ℝ => turanDetKT a κ τ y) (((0 : ℝ) / 2) ^ 2) :=
    continuousAt_turanDetKT_lam ha κ τ _
  have h := ContinuousAt.comp (g := fun y : ℝ => turanDetKT a κ τ y)
    (f := fun y : ℝ => (y / 2) ^ 2) (x := (0 : ℝ)) houter hinner
  exact h

/-- A continuous function negative at `0` is negative at some strictly positive
point.  The two converse halves below both take this shape. -/
private theorem exists_pos_of_continuousAt_neg {f : ℝ → ℝ} (hf : ContinuousAt f 0)
    (h0 : f 0 < 0) : ∃ y : ℝ, 0 < y ∧ f y < 0 := by
  have hev : ∀ᶠ y in nhds (0 : ℝ), f y < 0 := hf (Iio_mem_nhds h0)
  have hev' : ∀ᶠ y in nhdsWithin (0 : ℝ) (Ioi 0), f y < 0 ∧ y ∈ Ioi 0 :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨y, hy, hy0⟩ := hev'.exists
  exact ⟨y, hy0, hy⟩

/-! ## `H_ν^{(κ)}` and the two-parameter defect -/

private theorem algebra_HK_ratio (g Z E E2 κ : ℝ) (hg : g ≠ 0) (hZ : Z ≠ 0) :
    4 * (1 * (Z * Z) + g * (κ * (Z * E) - Z * E2 + E * E)) / (g * Z ^ 2) - 4 / g
      = 4 * κ * (E / Z) - 4 * (Z * E2 - E ^ 2) / Z ^ 2 := by
  field

/-- `BesselLaw.besselHkappa` in the `Z_Θ`, `Z_{ΘΘ}` form of `eq:G-L`:
`H_ν^{(κ)} = 4κZ_Θ/Z - 4(ZZ_{ΘΘ} - Z_Θ²)/Z²`.  The `τ`-independent shape the two
statements below both start from. -/
theorem besselHkappa_eq_ratio (hν : -1 < ν) (κ : ℝ) :
    besselHkappa κ ν x
      = 4 * κ * (ZEulerSeries (ν + 1) ((x / 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2))
        - 4 * (Zfun (ν + 1) ((x / 2) ^ 2) * ZEuler2Series (ν + 1) ((x / 2) ^ 2)
            - ZEulerSeries (ν + 1) ((x / 2) ^ 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2 := by
  have ha : 0 < ν + 1 := by linarith
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  rw [besselHkappa, Cseries]
  exact algebra_HK_ratio _ _ _ _ _ (trigamma_pos ha).ne' hZ.ne'

private theorem algebra_HK_C (g τ Z E E2 κ : ℝ) (hg : g ≠ 0) (hZ : Z ≠ 0) :
    4 * (1 * (Z * Z) + g * (κ * (Z * E) - Z * E2 + E * E)) / (g * Z ^ 2) - 4 / g + 4 * τ / g
      = 4 * (τ * (Z * Z) + g * (κ * (Z * E) - Z * E2 + E * E)) / (g * Z ^ 2) := by
  field

/-- The deformed second diagonal entry is `4C_{κ,τ}/(gZ²)`: `besselHkappa` carries
`C_{κ,1}`, and `τ` enters `eq:Ckt-def` only through `τZ²`, so `4τ/g` is exactly what
that term contributes. -/
theorem besselHkappa_add_eq_Cseries (hν : -1 < ν) (κ τ : ℝ) :
    besselHkappa κ ν x + 4 * τ / trigamma (ν + 1)
      = 4 * Cseries (ν + 1) (trigamma (ν + 1)) κ τ ((x / 2) ^ 2)
          / (trigamma (ν + 1) * Zfun (ν + 1) ((x / 2) ^ 2) ^ 2) := by
  have ha : 0 < ν + 1 := by linarith
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  have hg : trigamma (ν + 1) ≠ 0 := (trigamma_pos ha).ne'
  rw [besselHkappa]
  simp only [Cseries]
  exact algebra_HK_C _ _ _ _ _ _ hg hZ.ne'

private theorem algebra_DKT (A B C Z g : ℝ) (hg : g ≠ 0) (hZ : Z ≠ 0) :
    A / Z ^ 2 * (4 * C / (g * Z ^ 2)) - (1 + (2 * B / Z ^ 2 - 1)) ^ 2
      = 4 * (A * C - g * B ^ 2) / (g * Z ^ 4) := by
  field

/-- **`eq:Dkappa-tau-Delta`.**  `D_ν^{(κ,τ)} = 4Δ^{(κ,τ)}(a,λ)/(gZ⁴)` at every
`(κ,τ)` — the same pure algebra in `A, B, C_{κ,τ}, Z, g` that
`BesselDictPH.besselDet_eq_turanDet` runs at the endpoint. -/
theorem besselDefectKT_eq (hν : -1 < ν) (κ τ : ℝ) :
    besselG ν x * (besselHkappa κ ν x + 4 * τ / trigamma (ν + 1)) - (1 + besselP ν x) ^ 2
      = 4 * turanDetKT (ν + 1) κ τ ((x / 2) ^ 2)
          / (trigamma (ν + 1) * Zfun (ν + 1) ((x / 2) ^ 2) ^ 4) := by
  have ha : 0 < ν + 1 := by linarith
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  have hg : trigamma (ν + 1) ≠ 0 := (trigamma_pos ha).ne'
  rw [besselHkappa_add_eq_Cseries hν κ τ]
  change besselGfun ν x * _ - (1 + besselPfun ν x) ^ 2 = _
  rw [besselGfun, besselPfun, turanDetKT]
  exact algebra_DKT _ _ _ _ _ hg hZ.ne'

/-! ## `prop:bessel-sharpness` -/

/-- **`prop:bessel-sharpness`, the sufficient half.**  `D_ν^{(κ,τ)}(z) > 0` for
every `z > 0` on the quadrant `κ ≥ 1`, `τ ≥ 1`.  `eq:Dkappa-tau-Delta` turns the
defect into `4Δ^{(κ,τ)}/(gZ⁴)`, and `TuranDetKT.turanDetKT_pos` supplies the
numerator. -/
theorem bessel_sharpness_pos (hν : -1 < ν) (hκ : 1 ≤ κ) (hτ : 1 ≤ τ) (hx : 0 < x) :
    (1 + besselP ν x) ^ 2
      < besselG ν x * (besselHkappa κ ν x + 4 * τ / trigamma (ν + 1)) := by
  have ha : 0 < ν + 1 := by linarith
  have hlam : 0 < (x / 2) ^ 2 := by positivity
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha hlam.le
  have hpos : 0 < 4 * turanDetKT (ν + 1) κ τ ((x / 2) ^ 2)
      / (trigamma (ν + 1) * Zfun (ν + 1) ((x / 2) ^ 2) ^ 4) :=
    div_pos (by linarith [turanDetKT_pos ha hκ hτ hlam])
      (mul_pos (trigamma_pos ha) (pow_pos hZ 4))
  linarith [besselDefectKT_eq (x := x) hν κ τ, hpos]

/-- **`prop:bessel-sharpness`, positive definiteness.** -/
theorem bessel_schur_matrix_KT_pd (hν : -1 < ν) (hκ : 1 ≤ κ) (hτ : 1 ≤ τ) (hx : 0 < x) :
    SymMat.PD ⟨besselG ν x, 1 + besselP ν x,
      besselHkappa κ ν x + 4 * τ / trigamma (ν + 1)⟩ :=
  ⟨besselG_pos hν hx, bessel_sharpness_pos hν hκ hτ hx⟩

/-- **`prop:bessel-sharpness`, the `τ` half of the converse.**  For `τ < 1` the
degree-zero coefficient `g(τ-1)/Γ(a)⁴` of `Δ^{(κ,τ)}` is negative, so the defect is
negative somewhere on `(0,∞)` — for every `κ`, and with no appeal to the
large-argument behavior.  The paper's sharper statement, that there is then
*exactly one* zero when `τ ≥ τ_cw(a,κ)`, is `ZeroCount`. -/
theorem exists_bessel_defect_neg_of_lt_one (hν : -1 < ν) (κ : ℝ) (hτ : τ < 1) :
    ∃ x : ℝ, 0 < x ∧
      besselG ν x * (besselHkappa κ ν x + 4 * τ / trigamma (ν + 1))
        - (1 + besselP ν x) ^ 2 < 0 := by
  have ha : 0 < ν + 1 := by linarith
  have hG : Real.Gamma (ν + 1) ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hcont : ContinuousAt (fun y : ℝ => turanDetKT (ν + 1) κ τ ((y / 2) ^ 2)) 0 :=
    continuousAt_turanDetKT_arg ha κ τ
  have hf0 : turanDetKT (ν + 1) κ τ (((0 : ℝ) / 2) ^ 2) < 0 := by
    rw [show ((0 : ℝ) / 2) ^ 2 = 0 by norm_num, turanDetKT_lam_zero ha]
    apply div_neg_of_neg_of_pos
    · have := trigamma_pos ha; nlinarith
    · positivity
  obtain ⟨y, hy0, hy⟩ := exists_pos_of_continuousAt_neg hcont hf0
  refine ⟨y, hy0, ?_⟩
  have hlam : 0 < (y / 2) ^ 2 := by positivity
  have hZ : 0 < Zfun (ν + 1) ((y / 2) ^ 2) := Zfun_pos ha hlam.le
  rw [besselDefectKT_eq (x := y) hν κ τ]
  exact div_neg_of_neg_of_pos (by linarith)
    (mul_pos (trigamma_pos ha) (pow_pos hZ 4))

/-! ## The `z ↓ 0` limit: `cor:bessel-matrix` and `rem:schur-correction` -/

/-- Post-composition with `x ↦ (x/2)²` at `x = 0`. -/
private theorem continuousAt_arg_comp {F : ℝ → ℝ}
    (h : ContinuousAt F (((0 : ℝ) / 2) ^ 2)) :
    ContinuousAt (fun y : ℝ => F ((y / 2) ^ 2)) 0 := by
  have hinner : ContinuousAt (fun y : ℝ => (y / 2) ^ 2) 0 :=
    ((continuous_id.div_const 2).pow 2).continuousAt
  exact ContinuousAt.comp (g := F) (f := fun y : ℝ => (y / 2) ^ 2) (x := (0 : ℝ)) h hinner

/-- The Bessel--Schur matrix of `cor:bessel-matrix`, deformed by `(κ,τ)`.  This is
the left-hand side of `eq:bessel-congruence`, so it is `BesselLaw.normalizedTuran`
after the `diag(1,2/√g)` congruence, not that matrix: the off-diagonal carries a
factor `2` and the `(2,2)` entry a factor `4`. -/
noncomputable def schurMatKT (κ τ ν x : ℝ) : SymMat :=
  ⟨besselG ν x, 1 + besselP ν x, besselHkappa κ ν x + 4 * τ / trigamma (ν + 1)⟩

theorem besselG_arg_zero (hν : -1 < ν) : besselG ν 0 = trigamma (ν + 1) := by
  have ha : 0 < ν + 1 := by linarith
  have hG : Real.Gamma (ν + 1) ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  change besselGfun ν 0 = _
  rw [besselGfun, show ((0 : ℝ) / 2) ^ 2 = 0 by norm_num, Afun_lam_zero ha, Zfun_lam_zero]
  field_simp

theorem besselP_arg_zero (hν : -1 < ν) : besselP ν 0 = 1 := by
  have ha : 0 < ν + 1 := by linarith
  have hG : Real.Gamma (ν + 1) ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  change besselPfun ν 0 = _
  rw [besselPfun, show ((0 : ℝ) / 2) ^ 2 = 0 by norm_num, Bseries_lam_zero, Zfun_lam_zero]
  field_simp
  norm_num

theorem besselHkappa_arg_zero (hν : -1 < ν) (κ : ℝ) : besselHkappa κ ν 0 = 0 := by
  rw [besselHkappa_eq_ratio hν, show ((0 : ℝ) / 2) ^ 2 = 0 by norm_num,
    ZEulerSeries_lam_zero, ZEuler2Series_lam_zero]
  simp

/-- **The limit matrix of `cor:bessel-matrix` and `rem:schur-correction`.**  Every
entry is a ratio of series whose value at `λ = 0` is its own degree-zero
coefficient, so the deformed Bessel--Schur matrix extends continuously through
`x = 0` with value `((g,2),(2,4τ/g))` — independent of `κ`. -/
theorem schurMatKT_arg_zero (hν : -1 < ν) (κ τ : ℝ) :
    schurMatKT κ τ ν 0 = ⟨trigamma (ν + 1), 2, 4 * τ / trigamma (ν + 1)⟩ := by
  rw [schurMatKT, besselG_arg_zero hν, besselP_arg_zero hν, besselHkappa_arg_zero hν]
  norm_num

theorem continuousAt_besselG_arg (hν : -1 < ν) :
    ContinuousAt (fun y : ℝ => besselG ν y) 0 := by
  have ha : 0 < ν + 1 := by linarith
  have hZ : 0 < Zfun (ν + 1) (((0 : ℝ) / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  exact (continuousAt_arg_comp (continuousAt_Afun_lam ha _)).div
    ((continuousAt_arg_comp (continuousAt_Zfun_lam ha _)).pow 2) (pow_pos hZ 2).ne'

theorem continuousAt_besselP_arg (hν : -1 < ν) :
    ContinuousAt (fun y : ℝ => besselP ν y) 0 := by
  have ha : 0 < ν + 1 := by linarith
  have hZ : 0 < Zfun (ν + 1) (((0 : ℝ) / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  have h : ContinuousAt (fun y : ℝ =>
      2 * Bseries (ν + 1) ((y / 2) ^ 2) / Zfun (ν + 1) ((y / 2) ^ 2) ^ 2 - 1) 0 :=
    ((continuousAt_const.mul (continuousAt_arg_comp (continuousAt_Bseries_lam ha _))).div
      ((continuousAt_arg_comp (continuousAt_Zfun_lam ha _)).pow 2)
      (pow_pos hZ 2).ne').sub continuousAt_const
  exact h

theorem continuousAt_besselHkappa_arg (hν : -1 < ν) (κ : ℝ) :
    ContinuousAt (fun y : ℝ => besselHkappa κ ν y) 0 := by
  have ha : 0 < ν + 1 := by linarith
  have hZ : 0 < Zfun (ν + 1) (((0 : ℝ) / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  have hZc := continuousAt_arg_comp (continuousAt_Zfun_lam ha (((0 : ℝ) / 2) ^ 2))
  have hEc := continuousAt_arg_comp (continuousAt_ZEulerSeries_lam ha (((0 : ℝ) / 2) ^ 2))
  have hE2c := continuousAt_arg_comp (continuousAt_ZEuler2Series_lam ha (((0 : ℝ) / 2) ^ 2))
  have hfun : (fun y : ℝ => besselHkappa κ ν y) = fun y : ℝ =>
      4 * κ * (ZEulerSeries (ν + 1) ((y / 2) ^ 2) / Zfun (ν + 1) ((y / 2) ^ 2))
        - 4 * (Zfun (ν + 1) ((y / 2) ^ 2) * ZEuler2Series (ν + 1) ((y / 2) ^ 2)
            - ZEulerSeries (ν + 1) ((y / 2) ^ 2) ^ 2) / Zfun (ν + 1) ((y / 2) ^ 2) ^ 2 := by
    funext y; exact besselHkappa_eq_ratio hν κ
  rw [hfun]
  exact (continuousAt_const.mul (hEc.div hZc hZ.ne')).sub
    ((continuousAt_const.mul ((hZc.mul hE2c).sub (hEc.pow 2))).div (hZc.pow 2)
      (pow_pos hZ 2).ne')

/-- **`rem:schur-correction`.**  The determinant of the limit matrix is `4(τ-1)`. -/
theorem schurMatKT_arg_zero_det (hν : -1 < ν) (κ τ : ℝ) :
    (schurMatKT κ τ ν 0).a11 * (schurMatKT κ τ ν 0).a22 - (schurMatKT κ τ ν 0).a12 ^ 2
      = 4 * (τ - 1) := by
  have ha : 0 < ν + 1 := by linarith
  have hg : trigamma (ν + 1) ≠ 0 := (trigamma_pos ha).ne'
  rw [schurMatKT_arg_zero hν κ τ]
  change trigamma (ν + 1) * (4 * τ / trigamma (ν + 1)) - (2 : ℝ) ^ 2 = _
  field

/-- **The limit clause of `cor:bessel-matrix`.**  At `(κ,τ) = (1,1)` the limit
matrix `((g,2),(2,4/g))` is positive semidefinite, nonzero, and singular, i.e.
rank one: the `4/g` correction closes the mixed deficit exactly. -/
theorem schurMat_arg_zero_rank_one (hν : -1 < ν) :
    SymMat.PSD (schurMatKT 1 1 ν 0) ∧ schurMatKT 1 1 ν 0 ≠ 0 ∧
      (schurMatKT 1 1 ν 0).a11 * (schurMatKT 1 1 ν 0).a22
        - (schurMatKT 1 1 ν 0).a12 ^ 2 = 0 := by
  have ha : 0 < ν + 1 := by linarith
  have hg : 0 < trigamma (ν + 1) := trigamma_pos ha
  have hdet := schurMatKT_arg_zero_det hν 1 1
  rw [show (4 : ℝ) * ((1 : ℝ) - 1) = 0 by norm_num] at hdet
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hdet⟩
  · rw [schurMatKT_arg_zero hν]; exact hg.le
  · rw [schurMatKT_arg_zero hν]
    change (0 : ℝ) ≤ 4 * 1 / trigamma (ν + 1)
    positivity
  · linarith [hdet]
  · intro h
    have h11 : (schurMatKT 1 1 ν 0).a11 = 0 := by rw [h]; rfl
    rw [schurMatKT_arg_zero hν] at h11
    exact absurd h11 hg.ne'

/-! ## `eq:H-kappa-global` -/

/-- `Z_Θ(a,λ) = λZ(a+1,λ)`: the Euler weight `k` shifts the parameter.  Reindexing
`k = j+1` cancels the `k` against the `k!`. -/
theorem ZEulerSeries_eq_shift (ha : 0 < a) (lam : ℝ) :
    ZEulerSeries a lam = lam * Zfun (a + 1) lam := by
  have hs : Summable (fun k : ℕ => (k : ℝ) * zterm a lam k) :=
    (summable_norm_idx_zterm ha lam).of_norm
  have hterm : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) * zterm a lam (j + 1) = lam * zterm (a + 1) lam j := by
    intro j
    have hgam : Real.Gamma (a + ((j + 1 : ℕ) : ℝ)) = Real.Gamma (a + 1 + (j : ℝ)) := by
      congr 1; push_cast; ring
    have hfj : ((Nat.factorial j : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos j).ne'
    have hGj : Real.Gamma (a + 1 + (j : ℝ)) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)).ne'
    rw [zterm, zterm, hgam, Nat.factorial_succ]
    push_cast
    field
  rw [ZEulerSeries, hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [tsum_congr hterm, tsum_mul_left, Zfun]

/-- `Z_{ΘΘ}(a,λ) = λ(λZ(a+2,λ) + Z(a+1,λ))`: the same reindexing, twice. -/
theorem ZEuler2Series_eq_shift (ha : 0 < a) (lam : ℝ) :
    ZEuler2Series a lam = lam * (lam * Zfun (a + 2) lam + Zfun (a + 1) lam) := by
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have hs : Summable (fun k : ℕ => ((k : ℝ)) ^ 2 * zterm a lam k) :=
    (summable_norm_sq_zterm ha lam).of_norm
  have hterm : ∀ j : ℕ, (((j + 1 : ℕ) : ℝ)) ^ 2 * zterm a lam (j + 1)
      = lam * ((j : ℝ) * zterm (a + 1) lam j) + lam * zterm (a + 1) lam j := by
    intro j
    have hgam : Real.Gamma (a + ((j + 1 : ℕ) : ℝ)) = Real.Gamma (a + 1 + (j : ℝ)) := by
      congr 1; push_cast; ring
    have hfj : ((Nat.factorial j : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos j).ne'
    have hGj : Real.Gamma (a + 1 + (j : ℝ)) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)).ne'
    rw [zterm, zterm, hgam, Nat.factorial_succ]
    push_cast
    field
  have hsA : Summable (fun j : ℕ => lam * ((j : ℝ) * zterm (a + 1) lam j)) :=
    ((summable_norm_idx_zterm ha1 lam).of_norm).mul_left lam
  have hsB : Summable (fun j : ℕ => lam * zterm (a + 1) lam j) :=
    (summable_zterm ha1 lam).mul_left lam
  rw [ZEuler2Series, hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_mul, zero_add]
  rw [tsum_congr hterm, hsA.tsum_add hsB, tsum_mul_left, tsum_mul_left,
    ← ZEulerSeries, ← Zfun, ZEulerSeries_eq_shift ha1]
  rw [show a + 1 + 1 = a + 2 by ring]
  ring

private theorem algebra_zform (lam Z Z1 Z2 κ : ℝ) (hZ : Z ≠ 0) :
    4 * κ * (lam * Z1 / Z) - 4 * (Z * (lam * (lam * Z2 + Z1)) - (lam * Z1) ^ 2) / Z ^ 2
      = 4 * lam * ((κ - 1) * (Z1 / Z) - lam * (Z * Z2 - Z1 ^ 2) / Z ^ 2) := by
  field

/-- **The shifted-Turánian form of `H_ν^{(κ)}`.**
`H_ν^{(κ)} = 4λ[(κ-1)Z_1/Z - λ(ZZ_2 - Z_1²)/Z²]` with `Z_j = Z(a+j,λ)`,
`a = ν+1`, `λ = (x/2)²`.  **Differs from the paper's route.**  The paper writes
this in the Bessel ratio `r_ν` and reads the `κ = 1` case off the classical
modified-Bessel Turán inequality; here the same content is a Turánian in the
reciprocal-gamma series itself, which `Zfun_turan` proves from the paper's own
`A/Z² > 0`. -/
theorem besselHkappa_eq_zform (hν : -1 < ν) (κ : ℝ) :
    besselHkappa κ ν x
      = 4 * (x / 2) ^ 2 * ((κ - 1) * (Zfun (ν + 1 + 1) ((x / 2) ^ 2)
              / Zfun (ν + 1) ((x / 2) ^ 2))
          - (x / 2) ^ 2 * (Zfun (ν + 1) ((x / 2) ^ 2) * Zfun (ν + 1 + 2) ((x / 2) ^ 2)
              - Zfun (ν + 1 + 1) ((x / 2) ^ 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2) := by
  have ha : 0 < ν + 1 := by linarith
  have hZ : 0 < Zfun (ν + 1) ((x / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  rw [besselHkappa_eq_ratio hν, ZEulerSeries_eq_shift ha, ZEuler2Series_eq_shift ha]
  exact algebra_zform _ _ _ _ _ hZ.ne'

/-- Strict concavity of `a ↦ log Z(a,λ)` on `(0,∞)`: the second derivative is
`-A/Z² < 0`, which is `eq:ABC-log`'s `A/Z² = -L_{aa}` together with `Afun_pos`. -/
theorem strictConcaveOn_log_Zfun (hlam : 0 ≤ lam) :
    StrictConcaveOn ℝ (Ioi (0 : ℝ)) (fun y : ℝ => Real.log (Zfun y lam)) := by
  refine strictConcaveOn_of_deriv2_neg (convex_Ioi 0) ?_ ?_
  · intro y hy
    exact ((hasDerivAt_log_Zfun (mem_Ioi.mp hy) hlam).continuousAt).continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    have hy0 : 0 < y := mem_Ioi.mp hy
    have hev : (deriv fun t : ℝ => Real.log (Zfun t lam))
        =ᶠ[nhds y] fun t : ℝ => Zparam1 t lam / Zfun t lam := by
      filter_upwards [eventually_gt_nhds hy0] with t ht
      exact (hasDerivAt_log_Zfun ht hlam).deriv
    have h2 : deriv (deriv fun t : ℝ => Real.log (Zfun t lam)) y
        = -(Afun y lam) / Zfun y lam ^ 2 := by
      rw [hev.deriv_eq]
      exact (hasDerivAt_logDeriv_Zfun hy0 hlam).deriv
    change deriv (deriv fun t : ℝ => Real.log (Zfun t lam)) y < 0
    rw [h2]
    exact div_neg_of_neg_of_pos (by linarith [Afun_pos hy0 hlam])
      (pow_pos (Zfun_pos hy0 hlam) 2)

/-- **The Turán inequality for the reciprocal-gamma series**,
`Z(a,λ)Z(a+2,λ) < Z(a+1,λ)²`: the midpoint case of `strictConcaveOn_log_Zfun`. -/
theorem Zfun_turan (ha : 0 < a) (hlam : 0 ≤ lam) :
    Zfun a lam * Zfun (a + 2) lam < Zfun (a + 1) lam ^ 2 := by
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have ha2 : (0 : ℝ) < a + 2 := by linarith
  have hZ := Zfun_pos ha hlam
  have hZ1 := Zfun_pos ha1 hlam
  have hZ2 := Zfun_pos ha2 hlam
  have hcc := strictConcaveOn_log_Zfun (lam := lam) hlam
  have hmid := hcc.2 (mem_Ioi.mpr ha) (mem_Ioi.mpr ha2) (by intro h; linarith)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  simp only [smul_eq_mul] at hmid
  rw [show (1 : ℝ) / 2 * a + 1 / 2 * (a + 2) = a + 1 by ring] at hmid
  have hlog : Real.log (Zfun a lam * Zfun (a + 2) lam) < Real.log (Zfun (a + 1) lam ^ 2) := by
    rw [Real.log_mul hZ.ne' hZ2.ne', Real.log_pow]
    push_cast
    linarith
  have := Real.exp_lt_exp.mpr hlog
  rwa [Real.exp_log (by positivity), Real.exp_log (by positivity)] at this

/-- **`eq:H-kappa-global`, the `κ ≥ 1` half — unconditional.**  Both bracket terms
of the shifted form are then nonnegative, the second strictly. -/
theorem besselHkappa_pos_of_one_le (hν : -1 < ν) (hκ : 1 ≤ κ) (hx : 0 < x) :
    0 < besselHkappa κ ν x := by
  have ha : 0 < ν + 1 := by linarith
  have hlam : 0 < (x / 2) ^ 2 := by positivity
  have hZ := Zfun_pos ha hlam.le
  have hZ1 := Zfun_pos (show (0 : ℝ) < ν + 1 + 1 by linarith) hlam.le
  have hturan := Zfun_turan ha hlam.le
  rw [besselHkappa_eq_zform hν κ]
  have h1 : 0 ≤ (κ - 1) * (Zfun (ν + 1 + 1) ((x / 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2)) :=
    mul_nonneg (by linarith) (div_nonneg hZ1.le hZ.le)
  have h2 : 0 < (x / 2) ^ 2 * (Zfun (ν + 1 + 1) ((x / 2) ^ 2) ^ 2
      - Zfun (ν + 1) ((x / 2) ^ 2) * Zfun (ν + 1 + 2) ((x / 2) ^ 2))
        / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2 :=
    div_pos (mul_pos hlam (by linarith)) (pow_pos hZ 2)
  have hkey : 0 < (κ - 1) * (Zfun (ν + 1 + 1) ((x / 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2))
      - (x / 2) ^ 2 * (Zfun (ν + 1) ((x / 2) ^ 2) * Zfun (ν + 1 + 2) ((x / 2) ^ 2)
          - Zfun (ν + 1 + 1) ((x / 2) ^ 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2 := by
    have hneg : (x / 2) ^ 2 * (Zfun (ν + 1) ((x / 2) ^ 2) * Zfun (ν + 1 + 2) ((x / 2) ^ 2)
        - Zfun (ν + 1 + 1) ((x / 2) ^ 2) ^ 2) / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2
        = -((x / 2) ^ 2 * (Zfun (ν + 1 + 1) ((x / 2) ^ 2) ^ 2
            - Zfun (ν + 1) ((x / 2) ^ 2) * Zfun (ν + 1 + 2) ((x / 2) ^ 2))
          / Zfun (ν + 1) ((x / 2) ^ 2) ^ 2) := by
      ring
    rw [hneg]
    linarith
  have : (0 : ℝ) < 4 * (x / 2) ^ 2 := by positivity
  exact mul_pos this hkey

/-- **`prop:scalar-H`'s endpoint positivity, unconditional.**  `H_ν(z) > 0` for
`ν > -1`, `z > 0`, i.e. the shifted modified-Bessel Turán inequality
`eq:H-turan-exact`, proved here from `Zfun_turan` rather than cited. -/
theorem besselHfun_pos (hν : -1 < ν) (hx : 0 < x) : 0 < besselHfun ν x := by
  rw [besselHfun_eq_besselHkappa]
  exact besselHkappa_pos_of_one_le hν le_rfl hx

/-- **`cor:bessel-law`'s underdispersion, unconditional.**  `BesselLaw` proves
`H_ν > 0 ↔ Var Y < E Y`; with `besselHfun_pos` the equivalence becomes a fact about
the discrete Bessel law. -/
theorem besselLaw_underdispersed (hν : -1 < ν) (hx : 0 < x) :
    besselVar (ν + 1) ((x / 2) ^ 2) < besselMean (ν + 1) ((x / 2) ^ 2) :=
  (besselHfun_pos_iff_underdispersed hν).mp (besselHfun_pos hν hx)

/-- **`eq:H-kappa-global`, the `κ < 1` half.**  The bracket of the shifted form is
continuous through `λ = 0` with value `(κ-1)/(ν+1) < 0`, so `H_ν^{(κ)}` is negative
at some `z > 0`. -/
theorem exists_besselHkappa_neg_of_lt_one (hν : -1 < ν) (hκ : κ < 1) :
    ∃ y : ℝ, 0 < y ∧ besselHkappa κ ν y < 0 := by
  have ha : 0 < ν + 1 := by linarith
  have ha1 : (0 : ℝ) < ν + 1 + 1 := by linarith
  have ha2 : (0 : ℝ) < ν + 1 + 2 := by linarith
  have hG : Real.Gamma (ν + 1) ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hZ0 : 0 < Zfun (ν + 1) (((0 : ℝ) / 2) ^ 2) := Zfun_pos ha (sq_nonneg _)
  set bra : ℝ → ℝ := fun y : ℝ =>
    (κ - 1) * (Zfun (ν + 1 + 1) ((y / 2) ^ 2) / Zfun (ν + 1) ((y / 2) ^ 2))
      - (y / 2) ^ 2 * (Zfun (ν + 1) ((y / 2) ^ 2) * Zfun (ν + 1 + 2) ((y / 2) ^ 2)
          - Zfun (ν + 1 + 1) ((y / 2) ^ 2) ^ 2) / Zfun (ν + 1) ((y / 2) ^ 2) ^ 2 with hbra
  have hZc := continuousAt_arg_comp (continuousAt_Zfun_lam ha (((0 : ℝ) / 2) ^ 2))
  have hZ1c := continuousAt_arg_comp (continuousAt_Zfun_lam ha1 (((0 : ℝ) / 2) ^ 2))
  have hZ2c := continuousAt_arg_comp (continuousAt_Zfun_lam ha2 (((0 : ℝ) / 2) ^ 2))
  have hsq : ContinuousAt (fun y : ℝ => (y / 2) ^ 2) 0 :=
    ((continuous_id.div_const 2).pow 2).continuousAt
  have hcont : ContinuousAt bra 0 := by
    rw [hbra]
    exact (continuousAt_const.mul (hZ1c.div hZc hZ0.ne')).sub
      ((hsq.mul ((hZc.mul hZ2c).sub (hZ1c.pow 2))).div (hZc.pow 2) (pow_pos hZ0 2).ne')
  have hval : bra 0 = (κ - 1) / (ν + 1) := by
    have hgam : Real.Gamma (ν + 1 + 1) = (ν + 1) * Real.Gamma (ν + 1) :=
      Real.Gamma_add_one ha.ne'
    rw [hbra]
    simp only [show ((0 : ℝ) / 2) ^ 2 = 0 by norm_num]
    rw [Zfun_lam_zero, Zfun_lam_zero, hgam]
    field
  have hneg : bra 0 < 0 := by
    rw [hval]
    exact div_neg_of_neg_of_pos (by linarith) ha
  obtain ⟨y, hy0, hy⟩ := exists_pos_of_continuousAt_neg hcont hneg
  refine ⟨y, hy0, ?_⟩
  rw [besselHkappa_eq_zform hν κ]
  have h4 : (0 : ℝ) < 4 * (y / 2) ^ 2 := by positivity
  have := mul_neg_of_pos_of_neg h4 (show bra y < 0 from hy)
  simpa [hbra] using this

/-- **`eq:H-kappa-global`.**  `H_ν^{(κ)}(z) > 0` for every `z > 0` exactly when
`κ ≥ 1`. -/
theorem besselHkappa_pos_iff (hν : -1 < ν) :
    (∀ y : ℝ, 0 < y → 0 < besselHkappa κ ν y) ↔ 1 ≤ κ := by
  refine ⟨fun h => ?_, fun hκ y hy => besselHkappa_pos_of_one_le hν hκ hy⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y, hy0, hy⟩ := exists_besselHkappa_neg_of_lt_one hν hlt
  linarith [h y hy0]

end TuranBessel
