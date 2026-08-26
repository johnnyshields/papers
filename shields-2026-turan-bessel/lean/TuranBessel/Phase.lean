/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Gram
import TuranBessel.Degree
import TuranBessel.Threshold

/-!
# The two-parameter family and the coefficientwise phase boundary

Formalizes the algebraic core of `shields-2026-turan-bessel.tex`,
«Reciprocal-gamma formulation and positivity phase diagram» (`sec:main`, `eq:Ckt-def`, `eq:tau-cw`,
`thm:two-parameter-coeff`) and `subsec:coefficient-walls-exposed-degree` «The coefficient walls and
the exposed
degree-one boundary» (`sec:phase`, `lem:boundary-positivity`), in the same square-root-free
normalization used by `Coefficients`:
```
        ⎛ α_m               β_m         ⎞
N_m^{(κ,τ)} = ⎝ β_m     τ/g + c_m^{(κ)}   ⎠ ,      g = ψ₁(a),
```
so `N_m^{(1,1)}` is the `Nmat` of the endpoint theory.

Three things are proved here.

* The deformation is **affine at mixed-determinant level**: the two parameters
  enter only through `δ_m = (τ-1)/g + (κ-1)m/2`, and
  `MD(N_k^{(κ,τ)}, N_l^{(κ,τ)}) = MD(N_k, N_l) + α_k δ_l + α_l δ_k`.
  Summing against the reflection-symmetric weights gives the coefficient form
  `eq:affine-two-param`, with the two directions `pRed` and `qRed` in place of
  the paper's `P` and `Q`.
* `τ_cw(a,κ)` of `eq:tau-cw` is the **exact** value at which the degree-one
  coefficient vanishes, and it satisfies `τ_cw < 1` for every `κ ≥ 1`
  (`thm:two-parameter-coeff`), the separation between the coefficientwise and
  pointwise boundaries.  Both rest on `1 < a²ψ₁(a)`, which is the recurrence
  rather than an estimate.
* The pieces of `lem:boundary-positivity` that are algebraic: `det N̂_1 ≥ 0` for
  `a ≥ 1/2` (`eq:det-N1-boundary`), `s_* + c_2 > 0`, and positivity of the
  degree-two polynomial `P_2` of `eq:boundary-delta2`.

`Trigamma` gains the cubic upper bound `eq:trig-upper-cubic`, which
`lem:boundary-positivity` uses for `a ≥ 1/√2` and which the half-shift bound
cannot supply there (`check_trigamma_cubic_bound.py` measures that).

Sorry-free.
-/

open scoped BigOperators

namespace TuranBessel

variable {a κ τ y : ℝ}

/-! ## The cubic trigamma upper bound -/

/-- `F y = 1/y + 1/(2y²) + 1/(6y³)`, the majorant of `eq:trig-upper-cubic`. -/
noncomputable def cubicMaj (y : ℝ) : ℝ := 1 / y + 1 / (2 * y ^ 2) + 1 / (6 * y ^ 3)

theorem cubicMaj_pos (hy : 0 < y) : 0 < cubicMaj y := by
  unfold cubicMaj; positivity

/-- The telescoping step of `cubicMaj` strictly exceeds the trigamma term, with the
exact surplus `1/(6y³(y+1)³)`.  This is the integrand inequality
`θ/(1-e^{-θ}) < 1 + θ/2 + θ²/12` after the Laplace transform of
`eq:trigamma-integral`, in the form a telescoping argument can use. -/
theorem cubicMaj_step (hy : 0 < y) :
    ((y : ℝ)⁻¹) ^ 2 < cubicMaj y - cubicMaj (y + 1) := by
  have hy1 : (0 : ℝ) < y + 1 := by linarith
  have hinv : ((y : ℝ)⁻¹) ^ 2 = 1 / y ^ 2 := by rw [inv_pow, one_div]
  have key : cubicMaj y - cubicMaj (y + 1) - 1 / y ^ 2
      = 1 / (6 * y ^ 3 * (y + 1) ^ 3) := by
    unfold cubicMaj; field_simp; ring
  have hpos : (0 : ℝ) < 1 / (6 * y ^ 3 * (y + 1) ^ 3) := by positivity
  rw [hinv]; linarith

/-- Every partial sum of the trigamma series is below `cubicMaj y`: the telescoping
sum is `cubicMaj y - cubicMaj (y+N)`, and the subtracted term is positive.  No limit
is taken, so no summability side condition is needed beyond nonnegativity. -/
theorem sum_range_lt_cubicMaj (hy : 0 < y) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((y + (i : ℝ))⁻¹) ^ 2 ≤ cubicMaj y := by
  have hyn : ∀ n : ℕ, (0 : ℝ) < y + (n : ℝ) := by
    intro n; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have htel : ∀ M : ℕ,
      ∑ i ∈ Finset.range M, (cubicMaj (y + (i : ℝ)) - cubicMaj (y + (i : ℝ) + 1))
        = cubicMaj y - cubicMaj (y + (M : ℝ)) := by
    intro M
    induction M with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have : y + ((k : ℝ) + 1) = y + (k : ℝ) + 1 := by ring
        push_cast
        rw [this]
        ring
  have hle : ∑ i ∈ Finset.range N, ((y + (i : ℝ))⁻¹) ^ 2
      ≤ ∑ i ∈ Finset.range N, (cubicMaj (y + (i : ℝ)) - cubicMaj (y + (i : ℝ) + 1)) :=
    Finset.sum_le_sum (fun i _ => (cubicMaj_step (hyn i)).le)
  rw [htel N] at hle
  have := cubicMaj_pos (hyn N)
  linarith

/-- `ψ₁(y) ≤ cubicMaj y`, from the partial sums alone. -/
theorem trigamma_le_cubicMaj (hy : 0 < y) : trigamma y ≤ cubicMaj y := by
  rw [trigamma]
  exact Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_range_lt_cubicMaj hy)

/-- **Cubic upper bound** `ψ₁(y) < 1/y + 1/(2y²) + 1/(6y³)` (`eq:trig-upper-cubic`).
Strictness comes from the recurrence: the `y+1` tail is bounded non-strictly, and
`cubicMaj_step` supplies the strict inequality on the first term. -/
theorem trigamma_lt_cubic (hy : 0 < y) :
    trigamma y < 1 / y + 1 / (2 * y ^ 2) + 1 / (6 * y ^ 3) := by
  have hrec : trigamma y = ((y : ℝ)⁻¹) ^ 2 + trigamma (y + 1) := trigamma_succ hy
  have htail : trigamma (y + 1) ≤ cubicMaj (y + 1) :=
    trigamma_le_cubicMaj (by linarith)
  have hstep := cubicMaj_step hy
  have : trigamma y < cubicMaj y := by rw [hrec]; linarith
  simpa [cubicMaj] using this

/-! ## `1 < a² ψ₁(a)`, from the recurrence rather than from an estimate -/

/-- `a²ψ₁(a) = 1 + a²ψ₁(a+1) > 1`: the denominator of `eq:tau-cw` is positive.
This is the recurrence `eq:trigamma-partial-fraction` read off the first term, not
one of the trigamma estimates. -/
theorem sq_mul_trigamma_gt_one (ha : 0 < a) : 1 < a ^ 2 * trigamma a := by
  have hrec := trigamma_succ' ha
  have hpos : 0 < trigamma (a + 1) := trigamma_pos (by linarith)
  have : a ^ 2 * trigamma a = 1 + a ^ 2 * trigamma (a + 1) := by
    rw [hrec]; field_simp; ring
  nlinarith [pow_pos ha 2]

/-! ## The two-parameter coefficient matrices -/

/-- `c_m^{(κ)}` of `eq:cm-kappa`--`eq:cm-kappa-general`: `0`, `(κ-1)/2`, and
`κm/2 - m(2a+m-2)/(2(2a+2m-3))`.  At `κ = 1` this is `ccoef`. -/
noncomputable def ckappa (a κ : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 0
  else if m = 1 then (κ - 1) / 2
  else κ * (m : ℝ) / 2 - (m : ℝ) * (2 * a + (m : ℝ) - 2) / (2 * (2 * a + 2 * (m : ℝ) - 3))

/-- `N_m^{(κ,τ)}`: the normalized coefficient matrix of `eq:matrix-series-general`. -/
noncomputable def NmatKT (a κ τ : ℝ) (m : ℕ) : SymMat :=
  ⟨αcoef a m, βcoef a m, τ / trigamma a + ckappa a κ m⟩

@[simp] theorem ckappa_zero (a κ : ℝ) : ckappa a κ 0 = 0 := by simp [ckappa]
@[simp] theorem ckappa_one (a κ : ℝ) : ckappa a κ 1 = (κ - 1) / 2 := by
  simp only [ckappa, if_neg (by omega : ¬(1 = 0)), if_true]

@[simp] theorem NmatKT_a11 (a κ τ : ℝ) (m : ℕ) : (NmatKT a κ τ m).a11 = αcoef a m := rfl
@[simp] theorem NmatKT_a12 (a κ τ : ℝ) (m : ℕ) : (NmatKT a κ τ m).a12 = βcoef a m := rfl

/-- The whole two-parameter displacement of the `(2,2)` entry:
`δ_m = (τ-1)/g + (κ-1)m/2`, uniformly in `m` including `m = 0, 1`. -/
noncomputable def ddelta (a κ τ : ℝ) (m : ℕ) : ℝ :=
  (τ - 1) / trigamma a + (κ - 1) * (m : ℝ) / 2

/-- `c_m^{(κ)} - c_m = (κ-1)m/2`, uniformly in `m`: the two terms of the
`m ≥ 2` formula differ by exactly the numerator `2a+2m-3` of their common
denominator, so the deformation is linear in `m` with no exceptional degree. -/
theorem ckappa_sub_ccoef (ha : 0 < a) (κ : ℝ) (m : ℕ) :
    ckappa a κ m - ccoef a m = (κ - 1) * (m : ℝ) / 2 := by
  unfold ckappa
  match m with
  | 0 => simp
  | 1 => simp only [if_neg (by omega : ¬(1 = 0)), if_true, ccoef_one, Nat.cast_one]; ring
  | (k + 2) =>
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      set M : ℝ := (k : ℝ) + 2 with hM
      have hD : (0 : ℝ) < 2 * a + 2 * M - 3 := by rw [hM]; linarith
      have hDne : (2 : ℝ) * (a + M) - 3 ≠ 0 := by
        intro h; rw [hM] at hD h; linarith
      have hcc : ccoef a (k + 2) = M * (M - 1) / (2 * (2 * a + 2 * M - 3)) := by
        unfold ccoef
        rw [if_neg (by omega : ¬(k + 2 ≤ 1))]
        push_cast [hM]; ring_nf
      have hsplit : M * (2 * a + M - 2) / (2 * (2 * a + 2 * M - 3))
          + M * (M - 1) / (2 * (2 * a + 2 * M - 3)) = M / 2 := by
        rw [← add_div,
          show M * (2 * a + M - 2) + M * (M - 1) = M * (2 * a + 2 * M - 3) from by ring]
        field_simp
      rw [if_neg (by omega : ¬(k + 2 = 0)), if_neg (by omega : ¬(k + 2 = 1)), hcc]
      push_cast [hM]
      linarith [hsplit]

theorem NmatKT_a22 (ha : 0 < a) (κ τ : ℝ) (m : ℕ) :
    (NmatKT a κ τ m).a22 = (Nmat a m).a22 + ddelta a κ τ m := by
  have hg : trigamma a ≠ 0 := (trigamma_pos ha).ne'
  have hsub := ckappa_sub_ccoef ha κ m
  change τ / trigamma a + ckappa a κ m
      = (trigamma a)⁻¹ + ccoef a m + ((τ - 1) / trigamma a + (κ - 1) * (m : ℝ) / 2)
  have hτ : τ / trigamma a = (trigamma a)⁻¹ + (τ - 1) / trigamma a := by
    field_simp; ring
  rw [hτ]
  linarith

/-- **Affine at mixed-determinant level.**  The two parameters enter only through
`δ`, so `MD` picks up exactly `α_k δ_l + α_l δ_k` (`eq:affine-two-param`). -/
theorem MD_NmatKT (ha : 0 < a) (κ τ : ℝ) (k l : ℕ) :
    SymMat.MD (NmatKT a κ τ k) (NmatKT a κ τ l)
      = SymMat.MD (Nmat a k) (Nmat a l)
        + αcoef a k * ddelta a κ τ l + αcoef a l * ddelta a κ τ k := by
  simp only [SymMat.MD, NmatKT_a11, NmatKT_a12, NmatKT_a22 ha, Nmat_a11, Nmat_a12]
  ring

/-! ## The exact degree-one boundary `τ_cw` -/

/-- `s_* = τ_*/g = a(2a-1)/(2a²g-1)` of `eq:tau-star-s-star`. -/
noncomputable def sStar (a : ℝ) : ℝ := a * (2 * a - 1) / (2 * a ^ 2 * trigamma a - 1)

/-- `τ_cw(a,κ)` of `eq:tau-cw`. -/
noncomputable def tauCw (a κ : ℝ) : ℝ :=
  (a * trigamma a * (2 * a - 1) - (κ - 1) * a ^ 2 * (trigamma a) ^ 2 / 2)
    / (2 * a ^ 2 * trigamma a - 1)

/-- The denominator `2a²ψ₁(a) - 1` of `eq:tau-cw`, in both the stated and the
normalized shape `field_simp` produces, so every rational rearrangement below can
clear it. -/
theorem tauCw_den_ne (ha : 0 < a) :
    (2 * a ^ 2 * trigamma a - 1) ≠ 0 ∧ (-1 + a ^ 2 * trigamma a * 2) ≠ 0 := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have h1 : 1 < a ^ 2 * trigamma a := sq_mul_trigamma_gt_one ha
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem tauCw_div_trigamma (ha : 0 < a) : tauCw a 1 / trigamma a = sStar a := by
  have hg : trigamma a ≠ 0 := (trigamma_pos ha).ne'
  obtain ⟨hd, hd'⟩ := tauCw_den_ne ha
  obtain ⟨hd2, _⟩ := tauCw_den_ne ha
  unfold tauCw sStar
  rw [div_div, div_eq_div_iff (mul_ne_zero hd2 hg) hd2]
  ring

/-- The boundary is where the degree-one mixed determinant vanishes: this is the
equation `eq:tau-cw` solves, and `τ_cw(a,1)` solves it exactly. -/
theorem MD_boundary_degree_one (ha : 0 < a) :
    SymMat.MD (NmatKT a 1 (tauCw a 1) 0) (NmatKT a 1 (tauCw a 1) 1) = 0 := by
  have hg : 0 < trigamma a := trigamma_pos ha
  obtain ⟨hd, _⟩ := tauCw_den_ne ha
  have hs : tauCw a 1 / trigamma a = sStar a := tauCw_div_trigamma ha
  have ht : trigamma (a + 1) = trigamma a - (a ^ 2)⁻¹ := trigamma_succ' ha
  have hane : (a : ℝ) ≠ 0 := ha.ne'
  -- the defining relation for `s_*`, cleared of its denominator once and for all
  have hlin : sStar a * (2 * a ^ 2 * trigamma a - 1) = a * (2 * a - 1) := by
    unfold sStar; exact div_mul_cancel₀ _ hd
  have hfac : 2 * trigamma a - (a ^ 2)⁻¹ = (2 * a ^ 2 * trigamma a - 1) / a ^ 2 := by
    field_simp
  have hkey : sStar a * (2 * trigamma a - (a ^ 2)⁻¹) = (2 * a - 1) / a := by
    rw [hfac, mul_div_assoc', hlin, div_eq_div_iff (by positivity) hane]
    ring
  have hR : 2 * 1 * ((2 * a - 1) / (2 * a)) = (2 * a - 1) / a := by
    field_simp
  simp only [SymMat.MD, NmatKT, αcoef, βcoef_zero, βcoef_one, ckappa_zero, ckappa_one,
    Nat.cast_zero, Nat.cast_one, add_zero, sub_self, zero_div]
  rw [hs, ht, hR]
  nlinarith [hkey]

/-- **`τ_cw < 1`** for every `κ ≥ 1` (`thm:two-parameter-coeff`): the
coefficientwise boundary lies strictly below the pointwise one.  The exact gap is
`1 - τ_cw = (aψ₁(a) - 1 + (κ-1)a²ψ₁(a)²/2)/(2a²ψ₁(a) - 1)`. -/
theorem tauCw_lt_one (ha : 0 < a) (hκ : 1 ≤ κ) : tauCw a κ < 1 := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have hden : 0 < 2 * a ^ 2 * trigamma a - 1 := by
    have := sq_mul_trigamma_gt_one ha; nlinarith [pow_pos ha 2, hg]
  have hag : 1 < a * trigamma a := a_trigamma_gt_one ha
  obtain ⟨hd, hd'⟩ := tauCw_den_ne ha
  have hgap : 1 - tauCw a κ
      = (a * trigamma a - 1 + (κ - 1) * a ^ 2 * (trigamma a) ^ 2 / 2)
        / (2 * a ^ 2 * trigamma a - 1) := by
    unfold tauCw
    rw [one_sub_div hd, div_eq_div_iff hd hd]
    ring
  have hnum : 0 < a * trigamma a - 1 + (κ - 1) * a ^ 2 * (trigamma a) ^ 2 / 2 := by
    have h2 : 0 ≤ (κ - 1) * a ^ 2 * (trigamma a) ^ 2 / 2 := by
      have : 0 ≤ κ - 1 := by linarith
      positivity
    linarith
  have : 0 < 1 - tauCw a κ := by rw [hgap]; exact div_pos hnum hden
  linarith

/-- The boundary decreases in `κ`, so `τ_cw(a,κ) ≤ τ_cw(a,1)` for `κ ≥ 1`. -/
theorem tauCw_antitone (ha : 0 < a) (hκ : 1 ≤ κ) : tauCw a κ ≤ tauCw a 1 := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have hden : 0 < 2 * a ^ 2 * trigamma a - 1 := by
    have := sq_mul_trigamma_gt_one ha; nlinarith [pow_pos ha 2, hg]
  obtain ⟨hd, hd'⟩ := tauCw_den_ne ha
  have hdiff : tauCw a 1 - tauCw a κ
      = ((κ - 1) * a ^ 2 * (trigamma a) ^ 2 / 2) / (2 * a ^ 2 * trigamma a - 1) := by
    unfold tauCw
    rw [div_sub_div _ _ hd hd, div_eq_div_iff (mul_ne_zero hd hd) hd]
    ring
  have hnn : 0 ≤ ((κ - 1) * a ^ 2 * (trigamma a) ^ 2 / 2) / (2 * a ^ 2 * trigamma a - 1) := by
    have h1 : 0 ≤ (κ - 1) * a ^ 2 * (trigamma a) ^ 2 / 2 := by
      have : 0 ≤ κ - 1 := by linarith
      positivity
    exact div_nonneg h1 hden.le
  linarith [hdiff ▸ hnn]

/-! ## Boundary pieces of `lem:boundary-positivity` -/

/-- `det N̂_1 = (2a-1)(2a²t - 2a + 1)/(4a²(2a²t + 1))` with `t = ψ₁(a+1)`
(`eq:det-N1-boundary`). -/
theorem det_N1_boundary_eq (ha : 0 < a) :
    (NmatKT a 1 (tauCw a 1) 1).a11 * (NmatKT a 1 (tauCw a 1) 1).a22
        - (NmatKT a 1 (tauCw a 1) 1).a12 ^ 2
      = (2 * a - 1) * (2 * a ^ 2 * trigamma (a + 1) - 2 * a + 1)
        / (4 * a ^ 2 * (2 * a ^ 2 * trigamma (a + 1) + 1)) := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have ht : 0 < trigamma (a + 1) := trigamma_pos (by linarith)
  have hane : (a : ℝ) ≠ 0 := ha.ne'
  obtain ⟨hd, _⟩ := tauCw_den_ne ha
  have hs : tauCw a 1 / trigamma a = sStar a := tauCw_div_trigamma ha
  have hga : trigamma a = trigamma (a + 1) + (a ^ 2)⁻¹ := by
    have := trigamma_succ' ha; linarith
  -- `D = 2a²ψ₁(a) - 1` is `2a²ψ₁(a+1) + 1`
  have hDT : 2 * a ^ 2 * trigamma a - 1 = 2 * a ^ 2 * trigamma (a + 1) + 1 := by
    rw [hga]; field_simp; ring
  have hlin : sStar a * (2 * a ^ 2 * trigamma (a + 1) + 1) = a * (2 * a - 1) := by
    rw [← hDT]; unfold sStar; exact div_mul_cancel₀ _ hd
  have hden : (0 : ℝ) < 2 * a ^ 2 * trigamma (a + 1) + 1 := by positivity
  simp only [NmatKT, αcoef, βcoef_one, ckappa_one, Nat.cast_one, sub_self, zero_div, add_zero]
  rw [hs, eq_div_iff (by positivity)]
  have hsS : sStar a = a * (2 * a - 1) / (2 * a ^ 2 * trigamma (a + 1) + 1) :=
    (eq_div_iff hden.ne').mpr hlin
  rw [hsS]
  field

/-- The second factor is positive: `2a²ψ₁(a+1) - 2a + 1 > (a+1)⁻²`, exactly, at the
sharp trigamma lower bound. -/
theorem det_N1_boundary_factor_pos (ha : 0 < a) :
    ((a + 1) ^ 2)⁻¹ < 2 * a ^ 2 * trigamma (a + 1) - 2 * a + 1 := by
  have hb := trigamma_gt_inv_sharp (y := a + 1) (by linarith)
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have hkey : 2 * a ^ 2 * ((a + 1)⁻¹ + (1 / 2) * ((a + 1) ^ 2)⁻¹) - 2 * a + 1
      - ((a + 1) ^ 2)⁻¹ = 0 := by field_simp; ring
  nlinarith [pow_pos ha 2, hb, hkey]

/-- **`det N̂_1 ≥ 0` for `a ≥ 1/2`**, so `N̂_1` is positive semidefinite there
(step 3 of `lem:boundary-positivity`). -/
theorem det_N1_boundary_nonneg (ha : 1 / 2 ≤ a) :
    0 ≤ (NmatKT a 1 (tauCw a 1) 1).a11 * (NmatKT a 1 (tauCw a 1) 1).a22
          - (NmatKT a 1 (tauCw a 1) 1).a12 ^ 2 := by
  have ha0 : 0 < a := by linarith
  have ht : 0 < trigamma (a + 1) := trigamma_pos (by linarith)
  have hfac := det_N1_boundary_factor_pos ha0
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have hpos : (0 : ℝ) < ((a + 1) ^ 2)⁻¹ := by positivity
  rw [det_N1_boundary_eq ha0]
  apply div_nonneg
  · have h1 : 0 ≤ 2 * a - 1 := by linarith
    nlinarith
  · nlinarith [pow_pos ha0 2]

/-- `s_* + c_2 = (4a³ + 2a²g - a - 1)/((2a+1)(2a²g - 1)) > 0`, the step that keeps
the lowered `(2,2)` entries positive for `0 < a < 1/2`. -/
theorem sStar_add_c_two_pos (ha : 0 < a) : 0 < sStar a + ccoef a 2 := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have hden : 0 < 2 * a ^ 2 * trigamma a - 1 := by
    have := sq_mul_trigamma_gt_one ha; nlinarith [pow_pos ha 2, hg]
  have hlow := trigamma_gt_inv_sharp ha
  have heq : sStar a + ccoef a 2
      = (4 * a ^ 3 + 2 * a ^ 2 * trigamma a - a - 1)
        / ((2 * a + 1) * (2 * a ^ 2 * trigamma a - 1)) := by
    obtain ⟨hd, hd'⟩ := tauCw_den_ne ha
    unfold sStar
    have h2a1 : (2 : ℝ) * (2 * a + 1) ≠ 0 := by positivity
    have ha1 : (2 * a + 1 : ℝ) ≠ 0 := by positivity
    rw [ccoef_two, div_add_div _ _ hd h2a1,
      div_eq_div_iff (mul_ne_zero hd h2a1) (mul_ne_zero ha1 hd)]
    ring
  rw [heq]
  apply div_pos
  · have h : 2 * a + 1 < 2 * a ^ 2 * trigamma a := by
      have : 2 * a ^ 2 * (a⁻¹ + (1 / 2) * (a ^ 2)⁻¹) = 2 * a + 1 := by field_simp
      nlinarith [pow_pos ha 2, hlow]
    nlinarith [pow_pos ha 3]
  · nlinarith

/-- `P_2(a,t)` of `eq:boundary-delta2`, the degree-two numerator on the boundary. -/
noncomputable def P2boundary (a t : ℝ) : ℝ :=
  (2 * a ^ 5 + 4 * a ^ 4 + 2 * a ^ 3) * t ^ 2
    + (8 * a ^ 5 + 12 * a ^ 4 + 5 * a ^ 3 + 2 * a ^ 2 + a) * t
    - 8 * a ^ 4 - 6 * a ^ 3 + a ^ 2 + 4 * a + 2

/-- **`P_2 > 0`** (step 4 of `lem:boundary-positivity`).  `P_2` increases in `t`, and
at the sharp trigamma lower bound `t > (a+1)⁻¹ + (a+1)⁻²/2` its value is exactly
`(8a⁵+20a⁴+28a³+30a²+19a+4)/(2(a+1)²)`. -/
theorem P2boundary_pos (ha : 0 < a) : 0 < P2boundary a (trigamma (a + 1)) := by
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  set t0 : ℝ := (a + 1)⁻¹ + (1 / 2) * ((a + 1) ^ 2)⁻¹ with ht0
  have hlow : t0 < trigamma (a + 1) := trigamma_gt_inv_sharp (by linarith)
  have ht0pos : 0 < t0 := by rw [ht0]; positivity
  have hval : P2boundary a t0
      = (8 * a ^ 5 + 20 * a ^ 4 + 28 * a ^ 3 + 30 * a ^ 2 + 19 * a + 4) / (2 * (a + 1) ^ 2) := by
    unfold P2boundary; rw [ht0]; field_simp; ring
  have hvalpos : 0 < P2boundary a t0 := by
    rw [hval]; apply div_pos <;> positivity
  -- strictly increasing in `t` on `t > 0`
  have hmono : P2boundary a t0 < P2boundary a (trigamma (a + 1)) := by
    have hfac : P2boundary a (trigamma (a + 1)) - P2boundary a t0
        = (trigamma (a + 1) - t0)
          * ((2 * a ^ 5 + 4 * a ^ 4 + 2 * a ^ 3) * (trigamma (a + 1) + t0)
             + (8 * a ^ 5 + 12 * a ^ 4 + 5 * a ^ 3 + 2 * a ^ 2 + a)) := by
      unfold P2boundary; ring
    have htp : 0 < trigamma (a + 1) := trigamma_pos (by linarith)
    have hsecond : 0 < (2 * a ^ 5 + 4 * a ^ 4 + 2 * a ^ 3) * (trigamma (a + 1) + t0)
        + (8 * a ^ 5 + 12 * a ^ 4 + 5 * a ^ 3 + 2 * a ^ 2 + a) := by
      have h1 : 0 < (2 * a ^ 5 + 4 * a ^ 4 + 2 * a ^ 3) * (trigamma (a + 1) + t0) := by
        apply mul_pos (by positivity) (by linarith)
      have h2 : 0 < 8 * a ^ 5 + 12 * a ^ 4 + 5 * a ^ 3 + 2 * a ^ 2 + a := by positivity
      linarith
    have := mul_pos (by linarith : (0 : ℝ) < trigamma (a + 1) - t0) hsecond
    linarith [hfac]
  linarith

/-! ## The critical constant `c(a)` -/

/-- `c(a) = 4/ψ₁(a) - 4a + 7/2` of `eq:c-critical`. -/
noncomputable def cCrit (a : ℝ) : ℝ := 4 / trigamma a - 4 * a + 7 / 2

/-- **`c(a) > 3/2`** for every `a > 0` (`lem:large-argument-limit`).  Substituting the
inverse-trigamma bound `1/ψ₁(a) > a - 1/2` gives exactly `3/2`. -/
theorem cCrit_gt (ha : 0 < a) : 3 / 2 < cCrit a := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have hinv : a - 1 / 2 < (trigamma a)⁻¹ := inv_trigamma_gt ha
  have h4 : 4 / trigamma a = 4 * (trigamma a)⁻¹ := by rw [div_eq_mul_inv]
  unfold cCrit
  rw [h4]
  nlinarith [hinv]

/-! ## The coefficient form of the affine identity -/

/-- The degree-`n` coefficient sector of the two-parameter family, in the same
normalization as `Dcoeff` (`eq:Delta-n-MD` with `M_m^{(κ,τ)}` in place of `M_m`). -/
noncomputable def DcoeffKT (a κ τ : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    sred a k * sred a (n - k) * SymMat.MD (NmatKT a κ τ k) (NmatKT a κ τ (n - k))

/-- The `τ`-direction, `[λⁿ] P` of `eq:pq-coefficients` in reduced weights. -/
noncomputable def pRed (a : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), sred a k * sred a (n - k) * αcoef a k

/-- The `κ`-direction, `[λⁿ] Q` of `eq:pq-coefficients` in reduced weights. -/
noncomputable def qRed (a : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), sred a k * sred a (n - k) * αcoef a k * ((n : ℝ) - (k : ℝ))

/-- The reflection `k ↦ n - k` fixes the weights `s_k s_{n-k}`, so the two cross terms
produced by `MD_NmatKT` are equal.  This is the only place `eq:affine-two-param` needs
a symmetry argument. -/
theorem sum_reflect_cross (a κ τ : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        sred a k * sred a (n - k) * (αcoef a (n - k) * ddelta a κ τ k)
      = ∑ k ∈ Finset.range (n + 1),
        sred a k * sred a (n - k) * (αcoef a k * ddelta a κ τ (n - k)) := by
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel]
  rw [show n - (n - k) = k from Nat.sub_sub_self hk']
  ring

/-- **`eq:affine-two-param` at coefficient level.**  Both deformations act affinely on
every coefficient, along the two fixed directions `pRed` and `qRed`. -/
theorem DcoeffKT_affine (ha : 0 < a) (κ τ : ℝ) (n : ℕ) :
    DcoeffKT a κ τ n
      = Dcoeff a n + 2 * ((τ - 1) / trigamma a) * pRed a n + (κ - 1) * qRed a n := by
  have hcast : ∀ k ∈ Finset.range (n + 1), ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact Nat.cast_sub hk'
  have hsplit : DcoeffKT a κ τ n
      = Dcoeff a n
        + (∑ k ∈ Finset.range (n + 1),
            sred a k * sred a (n - k) * (αcoef a k * ddelta a κ τ (n - k)))
        + (∑ k ∈ Finset.range (n + 1),
            sred a k * sred a (n - k) * (αcoef a (n - k) * ddelta a κ τ k)) := by
    unfold DcoeffKT Dcoeff
    rw [Finset.sum_congr rfl (fun k _ =>
      show sred a k * sred a (n - k) * SymMat.MD (NmatKT a κ τ k) (NmatKT a κ τ (n - k))
          = sred a k * sred a (n - k) * SymMat.MD (Nmat a k) (Nmat a (n - k))
            + sred a k * sred a (n - k) * (αcoef a k * ddelta a κ τ (n - k))
            + sred a k * sred a (n - k) * (αcoef a (n - k) * ddelta a κ τ k) from by
        rw [MD_NmatKT ha]; ring)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit, sum_reflect_cross a κ τ n]
  have hcross : (∑ k ∈ Finset.range (n + 1),
        sred a k * sred a (n - k) * (αcoef a k * ddelta a κ τ (n - k)))
      = ((τ - 1) / trigamma a) * pRed a n + ((κ - 1) / 2) * qRed a n := by
    unfold pRed qRed ddelta
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hcast k hk]
    ring
  rw [hcross]
  ring

theorem pRed_pos (ha : 0 < a) (n : ℕ) : 0 < pRed a n := by
  unfold pRed
  refine Finset.sum_pos (fun k _ => ?_) ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
  exact mul_pos (mul_pos (sred_pos ha k) (sred_pos ha (n - k))) (αcoef_pos ha k)

theorem qRed_pos (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) : 0 < qRed a n := by
  unfold qRed
  refine Finset.sum_pos' (fun k hk => ?_) ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), ?_⟩
  · have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : (0 : ℝ) ≤ (n : ℝ) - (k : ℝ) := by
      have : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk'
      linarith
    have hw := mul_pos (mul_pos (sred_pos ha k) (sred_pos ha (n - k))) (αcoef_pos ha k)
    exact mul_nonneg hw.le this
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hw := mul_pos (mul_pos (sred_pos ha 0) (sred_pos ha (n - 0))) (αcoef_pos ha 0)
    simpa using mul_pos hw hn'

/-- **The degree-one coefficient vanishes exactly on `τ = τ_cw(a,κ)`**, for every
`κ`: this is the equation `eq:tau-cw` is the solution of, and the boundary of
`thm:two-parameter-coeff`. -/
theorem DcoeffKT_degree_one_boundary (ha : 0 < a) (κ : ℝ) :
    DcoeffKT a κ (tauCw a κ) 1 = 0 := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have hane : (a : ℝ) ≠ 0 := ha.ne'
  obtain ⟨hd, _⟩ := tauCw_den_ne ha
  have hs1 : sred a 1 = 2 * a / a ^ 2 := sred_one a
  have ht : trigamma (a + 1) = trigamma a - (a ^ 2)⁻¹ := trigamma_succ' ha
  have hMD : SymMat.MD (Nmat a 0) (Nmat a 1)
      = (a * trigamma a - 1) / (a ^ 2 * trigamma a) := by
    have h := MDkappa_eq ha 1
    simpa [N1kappa, Nmat, ccoef_one] using h
  -- the affine identity in degree one, with the three sums evaluated
  have hD : Dcoeff a 1 = 2 * sred a 1 * SymMat.MD (Nmat a 0) (Nmat a 1) := by
    simp only [Dcoeff, Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_self,
      Nat.sub_zero, zero_add, sred_zero]
    rw [SymMat.MD_comm (Nmat a 1) (Nmat a 0)]
    ring
  have hP : pRed a 1 = sred a 1 * (trigamma a + trigamma (a + 1)) := by
    simp only [pRed, Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_self,
      Nat.sub_zero, zero_add, sred_zero, αcoef]
    push_cast
    ring
  have hQ : qRed a 1 = sred a 1 * trigamma a := by
    simp only [qRed, Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_self,
      Nat.sub_zero, zero_add, sred_zero, αcoef]
    push_cast
    ring
  rw [DcoeffKT_affine ha, hD, hP, hQ, hMD, ht]
  have hsp : 0 < sred a 1 := sred_pos ha 1
  unfold tauCw
  field

end TuranBessel
