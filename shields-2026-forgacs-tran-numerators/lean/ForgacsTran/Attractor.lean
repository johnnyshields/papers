/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.AttractorCoeff
import ForgacsTran.AttractorRouche
import ForgacsTran.AttractorVieta
import ForgacsTran.AttractorPole
import ForgacsTran.Reduction
import ForgacsTran.LaurentReduction

/-!
# The isolated exceptional attractor of panel B

`cor:panel-B-attractor` runs on the data `Q(t) = (1-t)(1-t/2)(1-t/4)`, `r = 1`,
`N(t,z) = 1+z+z^2+t(2-z)`.  Assembled here from the three preceding modules:

## Main statements

* `AttractorCoeff` — `deg P_m = m+2` and `[z^{m+2}]P_m = (-1)^m`, the
  corollary's first assertion, from the coefficient recurrence.
* `AttractorRouche` — the Rouché split `64B = 𝒬 + ℋ` on `|t| = 1/2`, the two
  zeros of `B` inside, and their nonreality.
* `AttractorVieta` — `u + v = 7 - t_*`, `uv = 8/t_*`, and the separation
  `‖u‖, ‖v‖ > 3/2`.

## Implementation notes

`panelB_attractor` is everything `cor:panel-B-attractor` establishes about the
point `z_*` before `prop:isolated-dominant-cancellation` is invoked: `t_*` is a
nonreal zero of the reduced numerator of modulus below `1/2`, it is the unique
minimum-modulus zero of `D(·,z_*)` and is simple there, the local spectral ratio
`eq:local-spectral-ratio` is below `1/3`, the numerator vanishes at `(t_*,z_*)`
— the amplitude zero of `rem:cancellation-meaning` — and `z_*` is nonreal and
algebraic, a zero of the sextic the corollary displays.

`prop:isolated-dominant-cancellation` itself is
`AttractorPole.isolated_dominant_cancellation`, proven in the generality the
paper states it in.  What is here is the verification, exact throughout, that the
panel-B data satisfy every hypothesis that proposition asks for, with `ν = 1` and
`σ = 1/3`.

**Scope.**  `z_m = z_* + O(3^{-m})` is read off the general proposition in
`AttractorRate.panel_attractor_rate`, unconditionally and in the `F_M` variable:
the denominators are identified by `panelDen_eq_ftDen` and
`panelDenomCoeff_eq_ftDenom`, and the numerator by the canonical Laurent weight,
so `prop:isolated-dominant-cancellation` is applied at the panel rather than
merely agreeing with it.

The index shift is joined too, in `AttractorIndexShift`:
`QuadraticDefect.denomConv_ftCoeffPoly` says the explicit recursion solves the
defining convolution, `Reduction.initial_data_unique` identifies the panel's own
sequence with it, and `panelPC_eq_ftCoeffPoly` is the resulting
`eq:reduction-coeff` with the sequence named.  `panelP_attractor_rate` therefore
states `cor:panel-B-attractor` in the manuscript's own variable.

The two thresholds do not compose silently and are not left to compose: the
identification holds from `m = 4` and the rate from its own `M₀`, so the joined
statement takes their maximum and carries `4 ≤ m₀` in the statement rather than
letting a reader assume the rate's threshold covered it.

`prop:isolated-dominant-cancellation` takes a *univariate* `B ∈ ℝ[t]`, so
`ftCoeffPoly`'s numerator contribution is `C (B.coeff M)`, of `z`-degree zero,
while the corollary's `N(t,z) = 1 + z + z^2 + t(2 - z)` is bivariate — which
`panelNumCoeff 0 = X^2 + X + 1` records.  The reduction is what closes that gap:
restricting `N` to the denominator fiber `g(t) = -Q(t)/t^r` and clearing the pole
gives the univariate numerator,

`N(t, g(t)) = t^{-2}B(t)`,  `64B = panelB64`,

so `λ_N = -2` and the coefficient sequences satisfy `P_m = F_{m+2}`.

`scripts/check_panel_numerator_branch.py` verifies all of it in exact rational
arithmetic: the restriction identity, the sextic form `panelB64 = 64t^2N(t,g(t))`
the Lean tree would carry, that the sextic's two roots in `|t| < 1/2` are the
amplitude zeros, the shift term by term, and that the shift's threshold is
exactly `m ≥ 2` — the paper states it for sufficiently large `m` and does not
say where that begins.

The numerator side is now formalized through the Laurent reduction:
`panelB64_eq_restriction` is the restriction identity, `panelB64_eq_zero_iff`
identifies the sextic's zeros with the amplitude zeros — which is what makes the
Rouché count and the cancellation statement one statement rather than two proved
against different objects — and `panelLaurent` gives the canonical factorization
`λ_N = -2`, `B_N = panelBrat` off
`LaurentReduction.laurentShift_weight_unique`.

So the panel's univariate numerator is the general framework's own object, and
`panelReductionCoeff` closes the join: `P_m = F_{m+2}`, off
`LaurentReduction.reduction_coeff` instantiated at `λ_N = -2`.  The general
theorem's threshold is `deg_zN\,(deg Q - r) = 4`; the true one is `2`, which
`scripts/check_panel_numerator_branch.py` measures and the paper does not state.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `subsec:isolated-attractors`, `cor:panel-B-attractor`).

## Tags

zero attractor, dominant cancellation, exceptional zero, rational generating function
-/

namespace ForgacsTran

open Complex Metric ComplexConjugate

/-- Paper `cor:panel-B-attractor` — the numerator `N(t,z) = 1+z+z^2+t(2-z)`. -/
def panelNum (t z : ℂ) : ℂ := 1 + z + z ^ 2 + t * (2 - z)

/-- Paper `cor:panel-B-attractor` — the sextic
`z^6 - 12z^5 + 44z^4 - 44z^3 + 96z^2 - 104z + 135` whose zero `z_*` is. -/
def panelResultant (z : ℂ) : ℂ :=
  z ^ 6 - 12 * z ^ 5 + 44 * z ^ 4 - 44 * z ^ 3 + 96 * z ^ 2 - 104 * z + 135

theorem panelNum_two (t : ℂ) : panelNum t 2 = 7 := by
  simp only [panelNum]; ring

/-- Paper `rem:cancellation-meaning` — the canonical Laurent restriction:
`N(t, g(t)) = t^{-2} B(t)` with `g = -Q/t`, i.e. `64 t^2 N(t, g(t)) = 64B(t)`. -/
theorem panelNum_panelZstar {t : ℂ} (ht : t ≠ 0) :
    64 * t ^ 2 * panelNum t (panelZstar t) = panelB64 t := by
  simp only [panelNum, panelZstar, panelB64]
  field_simp
  ring

/-- **Paper `cor:panel-B-attractor` — the resultant identity.**  Solving
`N(t,z) = 0` for `t` and substituting in the denominator clears to the sextic. -/
theorem panelDen_at_numerator_root {z : ℂ} (hz : z ≠ 2) :
    panelDen z ((z ^ 2 + z + 1) / (z - 2)) = -panelResultant z / (8 * (z - 2) ^ 3) := by
  have hz2 : z - 2 ≠ 0 := sub_ne_zero.mpr hz
  simp only [panelDen, panelResultant]
  field_simp
  ring

/-- Paper `cor:panel-B-attractor` — the denominator has real coefficients. -/
theorem panelDen_conj (z t : ℂ) : panelDen (conj z) (conj t) = conj (panelDen z t) := by
  simp only [panelDen]
  simp [map_add, map_sub, map_mul, map_pow, map_ofNat, map_div₀]

/-- **Paper `cor:panel-B-attractor`.**  The panel-B data satisfy every hypothesis
of `prop:isolated-dominant-cancellation` at `z_*`, with `ν = 1` and `σ = 1/3`.

`t` is `t_*`: the unique zero of the reduced numerator `B` in the upper half of
`|t| < 1/2`, its conjugate being the only other zero there.  `z` is
`z_* = -Q(t_*)/t_*`.  The denominator zeros at `z_*` are `t`, `u`, `v`; the
latter two have modulus above `3/2`, so `t` is the unique minimum-modulus zero,
it is simple, and the local spectral ratio `eq:local-spectral-ratio` is below
`1/3`.  The numerator vanishes at `(t_*, z_*)`, which is the cancellation of
`rem:cancellation-meaning`, and `z_*` is nonreal and algebraic. -/
theorem panelB_attractor :
    ∃ t z u v : ℂ,
      0 < t.im ∧ ‖t‖ < 1 / 2 ∧ panelB64 t = 0 ∧
      (∀ w ∈ closedBall (0 : ℂ) (1 / 2), panelB64 w = 0 ↔ (w = t ∨ w = conj t)) ∧
      z = panelZstar t ∧ z.im ≠ 0 ∧ panelNum t z = 0 ∧ panelResultant z = 0 ∧
      (∀ w : ℂ, panelDen z w = 0 ↔ (w = t ∨ w = u ∨ w = v)) ∧
      3 / 2 < ‖u‖ ∧ 3 / 2 < ‖v‖ ∧ ‖t‖ / ‖u‖ < 1 / 3 ∧ ‖t‖ / ‖v‖ < 1 / 3 := by
  obtain ⟨t, htim, htn, htB, htall⟩ := exists_panelRoot
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at htim
    simp at htim
  set z : ℂ := panelZstar t with hz
  have hden : panelDen z t = 0 := panelDen_panelZstar ht0
  have hcub : panelCubic z t = 0 := (panelDen_eq_zero_iff z t).mp hden
  obtain ⟨u, v, hfac, hsum, hprod⟩ := panelCubic_other_roots ht0 hcub
  have hu : 3 / 2 < ‖u‖ := vieta_separation ht0 htn hsum hprod
  have hv : 3 / 2 < ‖v‖ :=
    vieta_separation ht0 htn (by rw [add_comm]; exact hsum) (by rw [mul_comm]; exact hprod)
  have hroots : ∀ w : ℂ, panelDen z w = 0 ↔ (w = t ∨ w = u ∨ w = v) := by
    intro w
    rw [panelDen_eq_zero_iff, hfac w]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact Or.inl (sub_eq_zero.mp h'')
        · exact Or.inr (Or.inl (sub_eq_zero.mp h''))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h'))
    · rintro (rfl | rfl | rfl) <;> ring
  -- `z_*` is nonreal
  have hzim : z.im ≠ 0 := by
    intro h
    have hzc : conj z = z := by
      apply Complex.ext <;> simp [h]
    have hconj : panelDen z (conj t) = 0 := by
      have := panelDen_conj z t
      rw [hzc, hden, map_zero] at this
      exact this
    have hne : conj t ≠ t := by
      intro hcon
      have := congrArg Complex.im hcon
      simp only [Complex.conj_im] at this
      linarith
    have hnorm : ‖conj t‖ < 1 / 2 := by simpa [RCLike.norm_conj] using htn
    rcases (hroots (conj t)).mp hconj with h' | h' | h'
    · exact hne h'
    · rw [h'] at hnorm; linarith
    · rw [h'] at hnorm; linarith
  -- the numerator vanishes at `(t_*, z_*)`
  have hnum : panelNum t z = 0 := by
    have h := panelNum_panelZstar ht0
    rw [← hz] at h
    rw [htB] at h
    have h64 : (64 : ℂ) * t ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 ht0)
    exact (mul_eq_zero.mp h).resolve_left h64
  -- `z_*` is a zero of the sextic
  have hz2 : z ≠ 2 := by
    intro h
    rw [h, panelNum_two] at hnum
    norm_num at hnum
  have hteq : t = (z ^ 2 + z + 1) / (z - 2) := by
    have hz2' : z - 2 ≠ 0 := sub_ne_zero.mpr hz2
    rw [eq_div_iff hz2']
    simp only [panelNum] at hnum
    linear_combination -hnum
  have hres : panelResultant z = 0 := by
    have h := panelDen_at_numerator_root hz2
    rw [← hteq, hden] at h
    have hz2' : (8 : ℂ) * (z - 2) ^ 3 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 3 (sub_ne_zero.mpr hz2))
    have hzero := (div_eq_zero_iff.mp h.symm).resolve_right hz2'
    exact neg_eq_zero.mp hzero
  exact ⟨t, z, u, v, htim, htn, htB, htall, hz, hzim, hnum, hres, hroots, hu, hv,
    spectral_ratio_lt_third htn hu, spectral_ratio_lt_third htn hv⟩

/-! ### Joining the panel to the general proposition

The panel carries its own `panelDen`, so `AttractorPole.isolated_dominant_cancellation`
cannot be applied to it until the two denominators are identified.  That is the
first half of the join named in this module's scope note; the second half is the
index shift `P_m = F_{m+2}` of `lem:laurent-reduction`, which is not done here.

The pencil's numerator polynomial is **not** named `panelQ`: that name is taken,
in `AttractorRouche`, by the dominant part `𝒬 = 548t^2 - 288t + 64` of
the Rouché split — a different object on a different variable.  `panelDenQ` is
the `Q` of `D(t,z) = Q(t) + zt`. -/

/-- Paper `cor:panel-B-attractor` — the pencil's numerator, so that the panel's
denominator is the general `ftDen` at `r = 1`. -/
noncomputable def panelDenQ : Polynomial ℂ :=
  1 - Polynomial.C (7 / 4 : ℂ) * Polynomial.X
    + Polynomial.C (7 / 8 : ℂ) * Polynomial.X ^ 2
    - Polynomial.C (1 / 8 : ℂ) * Polynomial.X ^ 3

/-- **The panel's denominator is the general pencil.**  `panelDen z = ftDen panelDenQ 1 z`,
which is what lets `prop:isolated-dominant-cancellation` be *applied* to the
panel rather than merely agree with it. -/
theorem panelDen_eq_ftDen (z t : ℂ) :
    panelDen z t = (ftDen panelDenQ 1 z).eval t := by
  simp [panelDen, panelDenQ, ftDen]

/-- `Q(0) = 1 ≠ 0`, which is `isolated_dominant_cancellation`'s `hQ0` at the
panel. -/
theorem panelDenQ_eval_zero : panelDenQ.eval 0 = 1 := by
  simp [panelDenQ]

/-- The pencil's numerator over `ℚ`, which is where the panel's
coefficient recurrence lives. -/
noncomputable def panelDenQrat : Polynomial ℚ :=
  1 - Polynomial.C (7 / 4 : ℚ) * Polynomial.X
    + Polynomial.C (7 / 8 : ℚ) * Polynomial.X ^ 2
    - Polynomial.C (1 / 8 : ℚ) * Polynomial.X ^ 3

/-- **The panel's denominator sequence is the general `ftDenom`.**  Term by term:
`d_0 = 1`, `d_1 = X - 7/4` (the resonant index, where the `z` enters),
`d_2 = 7/8`, `d_3 = -1/8`, and nothing above.  This is what identifies the
panel's recurrence with `lem:laurent-reduction`'s, and hence the second half of
the join this module's scope note names — the remaining step being the index
shift `P_m = F_{m+2}` itself. -/
theorem panelDenomCoeff_eq_ftDenom (i : ℕ) :
    panelDenomCoeff i = ftDenom panelDenQrat 1 i := by
  have hc : ∀ k : ℕ, panelDenQrat.coeff k
      = (if k = 0 then (1 : ℚ) else if k = 1 then -(7 / 4)
         else if k = 2 then 7 / 8 else if k = 3 then -(1 / 8) else 0) := by
    intro k
    rcases k with _ | _ | _ | _ | k <;>
      simp [panelDenQrat, Polynomial.coeff_one, Polynomial.coeff_X_pow]
  match i with
  | 0 => rw [panelDenomCoeff, ftDenom, hc]; norm_num
  | 1 => rw [panelDenomCoeff, ftDenom, hc]; norm_num; ring
  | 2 => rw [panelDenomCoeff, ftDenom, hc]; norm_num
  | 3 => rw [panelDenomCoeff, ftDenom, hc]; norm_num
  | (k + 4) =>
      rw [panelDenomCoeff, ftDenom, hc, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp

/-- Above the initial data the panel's denominator sequence is supported on
`j ≤ 3`, so the convolution has four terms. -/
private theorem ftDenom_panelDenQrat_eq_zero {j : ℕ} (hj : 4 ≤ j) :
    ftDenom panelDenQrat 1 j = 0 := by
  rw [← panelDenomCoeff_eq_ftDenom]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
  rfl

/-- **The panel's coefficient polynomials satisfy `lem:laurent-reduction`'s
recurrence.**  `denomConv (ftDenom panelDenQrat 1) panelP` vanishes above the
initial data — which is the recurrence of `lem:laurent-reduction` in the general
framework's own notation, at the panel's data.

This is what the index shift `P_m = F_{m+2}` runs on: two sequences satisfying
the same homogeneous recurrence agree once their initial segments do, and the
shift is which initial segment to compare.  The comparison itself still has to
cross the base change from `ℚ[X]` to `ℂ[X]` and is not done
here. -/
theorem denomConv_panelP (k : ℕ) :
    denomConv (ftDenom panelDenQrat 1) panelP (k + 3) = 0 := by
  have hsub : Finset.range 4 ⊆ Finset.range (k + 3 + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ j ∈ Finset.range (k + 3 + 1), j ∉ Finset.range 4 →
      ftDenom panelDenQrat 1 j * panelP (k + 3 - j) = 0 := by
    intro j _ hj
    rw [Finset.mem_range] at hj
    rw [ftDenom_panelDenQrat_eq_zero (by omega), zero_mul]
  rw [denomConv, ← Finset.sum_subset hsub hzero]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  rw [← panelDenomCoeff_eq_ftDenom, ← panelDenomCoeff_eq_ftDenom,
    ← panelDenomCoeff_eq_ftDenom, ← panelDenomCoeff_eq_ftDenom]
  have h0 : k + 3 - 0 = k + 3 := by omega
  have h1 : k + 3 - 1 = k + 2 := by omega
  have h2 : k + 3 - 2 = k + 1 := by omega
  have h3 : k + 3 - 3 = k := by omega
  rw [h0, h1, h2, h3]
  change (0 : Polynomial ℚ) + 1 * panelP (k + 3)
      + (Polynomial.X - Polynomial.C (7 / 4)) * panelP (k + 2)
      + Polynomial.C (7 / 8) * panelP (k + 1)
      + Polynomial.C (-1 / 8) * panelP k = 0
  rw [show panelP (k + 3)
      = -(Polynomial.X - Polynomial.C (7 / 4)) * panelP (k + 2)
        - Polynomial.C (7 / 8) * panelP (k + 1)
        + Polynomial.C (1 / 8) * panelP k from rfl]
  rw [show Polynomial.C (-1 / 8 : ℚ) = -Polynomial.C (1 / 8 : ℚ) by
    rw [← map_neg]; norm_num]
  ring

/-- **The Laurent restriction of `cor:panel-B-attractor`.**  `N(t,g(t)) = t^{-2}B(t)`
with `64B = panelB64`, in the pole-free form: restricting the bivariate numerator
to the denominator fiber `g(t) = -Q(t)/t` and clearing the double pole gives the
sextic.

This is `lem:laurent-reduction`'s input at the panel, and it is what supplies the
*univariate* numerator that `prop:isolated-dominant-cancellation` asks for —
the proposition takes `B ∈ ℝ[t]`, while the corollary's `N` is bivariate, and
the restriction is what closes that gap.  The Laurent exponent is
`λ_N = -2`, which is the `t^2` here and the `+2` of the shift
`P_m = F_{m+2}`. -/
theorem panelB64_eq_restriction {t : ℂ} (ht : t ≠ 0) :
    panelB64 t = 64 * t ^ 2 * panelNum t (panelZstar t) := by
  rw [panelB64, panelNum, panelZstar]
  field_simp
  ring

/-- **The sextic's zeros are the amplitude zeros.**  Off the origin, `B` vanishes
exactly where the bivariate numerator does on the fiber — so `panelB_attractor`'s
`panelNum t z = 0`, which is `rem:cancellation-meaning`'s amplitude zero, is the
same condition as `panelB64 t = 0`, which is what the Rouché count in
`AttractorRouche` localizes.

The two sides of `cor:panel-B-attractor` were proved against different objects:
the Rouché argument counts zeros of the sextic, and the cancellation statement is
about the numerator on the fiber.  This is the identification that makes them one
statement. -/
theorem panelB64_eq_zero_iff {t : ℂ} (ht : t ≠ 0) :
    panelB64 t = 0 ↔ panelNum t (panelZstar t) = 0 := by
  rw [panelB64_eq_restriction ht]
  have hne : (64 : ℂ) * t ^ 2 ≠ 0 := by
    simp [ht, pow_eq_zero_iff]
  constructor
  · intro h
    exact (mul_eq_zero.1 h).resolve_left hne
  · intro h
    rw [h, mul_zero]

/-! ### The Laurent reduction's input at the panel

`LaurentReduction.laurentShift_weight_unique` identifies `λ_N` and `B_N`
from any exhibited factorization `curveEval Q r N = T^l · B`.  Exhibiting one
at the panel needs the bivariate numerator as an element of `(ℚ[X])[X]`
and the cleared restriction as a polynomial identity.  Both are here; the
Laurent-ring computation that consumes them is not. -/

/-- Paper `cor:panel-B-attractor` — the numerator `N(t,z) = 1 + z + z^2 + t(2-z)`
as a polynomial in `z` over `ℚ[t]`, which is the shape
`LaurentReduction` works in.  Its `z`-coefficients are `1 + 2t`, `1 - t`, `1`. -/
noncomputable def panelNbi : Polynomial (Polynomial ℚ) :=
  Polynomial.C (1 + Polynomial.C (2 : ℚ) * Polynomial.X)
    + Polynomial.C (1 - Polynomial.X) * Polynomial.X
    + Polynomial.X ^ 2

/-- The sextic over `ℚ`, as `LaurentReduction`'s weight would give it. -/
noncomputable def panelB64rat : Polynomial ℚ :=
  Polynomial.X ^ 6 - Polynomial.C (22 : ℚ) * Polynomial.X ^ 5
    + Polynomial.C (141 : ℚ) * Polynomial.X ^ 4
    - Polynomial.C (252 : ℚ) * Polynomial.X ^ 3
    + Polynomial.C (548 : ℚ) * Polynomial.X ^ 2
    - Polynomial.C (288 : ℚ) * Polynomial.X + Polynomial.C (64 : ℚ)

/-- **The cleared restriction, as a polynomial identity over `ℚ`.**
Substituting `z = g(t) = -Q(t)/t` into `N` and multiplying by `t^2` clears the
double pole and leaves

`t^2(1 + 2t) - t(1 - t)Q(t) + Q(t)^2 = B(t)`,  `64B = panelB64`.

Every term is a polynomial, so the identity is exact and needs no `t ≠ 0` —
which is the point of clearing before restricting rather than after.  This is
what `laurentShift_weight_unique` consumes to return `λ_N = -2` and
`B_N = B`. -/
theorem panelClearedRestrict :
    Polynomial.X ^ 2 * (1 + Polynomial.C (2 : ℚ) * Polynomial.X)
        - Polynomial.X * (1 - Polynomial.X) * panelDenQrat + panelDenQrat ^ 2
      = Polynomial.C (1 / 64 : ℚ) * panelB64rat := by
  refine Polynomial.funext fun x => ?_
  simp only [panelDenQrat, panelB64rat, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one]
  ring

section PanelLaurent

open LaurentPolynomial (T)
open scoped LaurentPolynomial

/-- The canonical weight of `cor:panel-B-attractor`, `B` with `64B = panelB64`.
The normalization is not a choice: `laurentShift_weight_unique` pins `B_N` through
the equation `curveEval N = T^l · B`, so the constant `64` is fixed by the
restriction rather than by a convention, and `B.coeff 0 = 1`. -/
noncomputable def panelBrat : Polynomial ℚ := Polynomial.C (1 / 64 : ℚ) * panelB64rat

theorem panelBrat_coeff_zero : panelBrat.coeff 0 = 1 := by
  simp [panelBrat, panelB64rat]

theorem panelNbi_coeff_zero :
    panelNbi.coeff 0 = 1 + Polynomial.C (2 : ℚ) * Polynomial.X := by
  simp [panelNbi]

theorem panelNbi_coeff_one : panelNbi.coeff 1 = 1 - Polynomial.X := by
  simp [panelNbi, Polynomial.coeff_one]

theorem panelNbi_coeff_two : panelNbi.coeff 2 = 1 := by
  simp [panelNbi, Polynomial.coeff_one]

theorem panelNbi_coeff_high {β : ℕ} (hβ : 3 ≤ β) : panelNbi.coeff β = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, β = k + 3 := ⟨β - 3, by omega⟩
  simp [panelNbi, Polynomial.coeff_X_pow, Polynomial.coeff_one,
    Polynomial.coeff_mul_X]

/-- **The cleared restriction, in the general framework's own object.**
`clearedRestrict Q 1 2 N` unfolds to `N_0t^2 - N_1Qt + N_2Q^2`, which is
`panelClearedRestrict`'s left side. -/
theorem clearedRestrict_panel :
    clearedRestrict panelDenQrat 1 2 panelNbi = panelBrat := by
  rw [clearedRestrict]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  rw [panelNbi_coeff_zero, panelNbi_coeff_one, panelNbi_coeff_two, panelBrat]
  simp only [pow_zero, pow_one, one_mul, mul_one, neg_one_sq]
  rw [← panelClearedRestrict]
  norm_num
  ring

theorem panelDenQrat_coeff_zero : panelDenQrat.coeff 0 = 1 := by
  simp [panelDenQrat, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]

theorem panelDenQrat_natDegree : panelDenQrat.natDegree = 3 := by
  have hle : panelDenQrat.natDegree ≤ 3 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
    simp [panelDenQrat, Polynomial.coeff_one]
  have hne : panelDenQrat.coeff 3 ≠ 0 := by
    simp [panelDenQrat, Polynomial.coeff_one, Polynomial.coeff_X_pow]
  exact le_antisymm hle (Polynomial.le_natDegree_of_ne_zero hne)

theorem panelNbi_natDegree_le : panelNbi.natDegree ≤ 2 :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun _ hm => panelNbi_coeff_high (by omega)

theorem panelNbi_ne_zero : panelNbi ≠ 0 := by
  intro h
  have h2 := panelNbi_coeff_two
  rw [h] at h2
  simp at h2

/-- `cor:panel-B-attractor`'s numerator is proper: every `z`-coefficient has
`t`-degree below `max(deg Q, r) = 3`. -/
theorem panelNbi_proper (β : ℕ) :
    (panelNbi.coeff β).degree
      < ((max panelDenQrat.natDegree 1 : ℕ) : WithBot ℕ) := by
  have h3 : ((max panelDenQrat.natDegree 1 : ℕ) : WithBot ℕ) = ((3 : ℕ) : WithBot ℕ) := by
    rw [panelDenQrat_natDegree]
    norm_num
  rw [h3]
  match β with
  | 0 =>
      rw [panelNbi_coeff_zero]
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt Polynomial.degree_one_le (by decide)
      · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
  | 1 =>
      rw [panelNbi_coeff_one]
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt Polynomial.degree_one_le (by decide)
      · exact lt_of_le_of_lt Polynomial.degree_X_le (by decide)
  | 2 =>
      rw [panelNbi_coeff_two]
      exact lt_of_le_of_lt Polynomial.degree_one_le (by decide)
  | (k + 3) =>
      rw [panelNbi_coeff_high (by omega), Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _

/-- **`lem:laurent-reduction` at the panel.**  The canonical factorization
`L_N = t^{λ_N}B_N` with `λ_N = -2` and `64B_N = panelB64`.

`laurentShift_weight_unique` pins both through the equation, so the constant `64`
is fixed by the restriction rather than chosen: `panelBrat.coeff 0 = 1`, and any
other normalization fails the equation rather than giving a second valid answer.

With this, `cor:panel-B-attractor`'s coefficient sequence is the general
framework's, and the univariate numerator `prop:isolated-dominant-cancellation`
asks for is `panelBrat`. -/
theorem panelLaurent :
    laurentShift panelDenQrat 1 panelNbi = (-2 : ℤ)
      ∧ laurentWeight panelDenQrat 1 panelNbi = panelBrat := by
  have hQ0 : panelDenQrat.coeff 0 ≠ 0 := by rw [panelDenQrat_coeff_zero]; norm_num
  have hB0 : panelBrat.coeff 0 ≠ 0 := by rw [panelBrat_coeff_zero]; norm_num
  have hcl := toLaurent_clearedRestrict panelDenQrat 1 2 panelNbi
    (Nat.lt_succ_of_le panelNbi_natDegree_le)
  rw [clearedRestrict_panel] at hcl
  have heq : curveEval panelDenQrat 1 panelNbi = T (-2 : ℤ) * Polynomial.toLaurent panelBrat := by
    have h12 : ((1 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) = (2 : ℤ) := by norm_num
    rw [h12] at hcl
    rw [hcl, ← mul_assoc, mul_comm (T (-2 : ℤ)), mul_assoc, ← LaurentPolynomial.T_add]
    norm_num
  obtain ⟨hl, hw⟩ :=
    laurentShift_weight_unique panelDenQrat (by norm_num) hQ0 panelNbi_ne_zero
      panelNbi_proper hB0 heq
  exact ⟨hl.symm, hw.symm⟩

theorem panelNbi_natDegree : panelNbi.natDegree = 2 := by
  refine le_antisymm panelNbi_natDegree_le (Polynomial.le_natDegree_of_ne_zero ?_)
  rw [panelNbi_coeff_two]
  exact one_ne_zero

/-- **The exchange of indeterminates at the panel.**  `swapVars` reads `N` as a
polynomial in `t` with `z`-polynomial coefficients, and those coefficients are
`panelNumCoeff` — `1 + z + z^2` and `2 - z`.  This is what makes
`panelP_denomConv` an instance of `prop:initial-data`'s recurrence rather than a
statement that merely resembles it. -/
theorem swapVars_panelNbi (m : ℕ) :
    (swapVars panelNbi).coeff m = panelNumCoeff m := by
  have hsw : swapVars panelNbi
      = (1 + Polynomial.C (2 : ℚ) * Polynomial.X).map (Polynomial.C : ℚ →+* Polynomial ℚ)
        + ((1 : Polynomial ℚ) - Polynomial.X).map (Polynomial.C : ℚ →+* Polynomial ℚ)
            * Polynomial.C Polynomial.X
        + Polynomial.C Polynomial.X ^ 2 := by
    simp [panelNbi, swapVars]
  have hcx : (Polynomial.C (Polynomial.X : Polynomial ℚ)) ^ 2
      = Polynomial.C ((Polynomial.X : Polynomial ℚ) ^ 2) := by
    rw [← Polynomial.C_pow]
  rw [hsw, hcx]
  match m with
  | 0 => simp [panelNumCoeff, Polynomial.coeff_one,
      Polynomial.coeff_C, -map_pow]; ring
  | 1 =>
      simp [panelNumCoeff, Polynomial.coeff_one,
        Polynomial.coeff_C, Polynomial.coeff_mul_X, -map_pow]
      ring
  | (k + 2) =>
      simp [panelNumCoeff, Polynomial.coeff_one,
        Polynomial.coeff_mul_X,
        Polynomial.coeff_X, -map_pow]

/-- **`eq:reduction-coeff` at the panel — `P_m = F_{m+2}`.**  The last inference
of the join, and it is `LaurentReduction.reduction_coeff` instantiated: the
denominator recurrence is `panelP_denomConv` through `panelDenomCoeff_eq_ftDenom`
and `swapVars_panelNbi`, and the shift is `λ_N = -2` from `panelLaurent`.

The general theorem's threshold is `deg_zN · (deg Q - r) = 2 · 2 = 4`.
That is not tight here: `scripts/check_panel_numerator_branch.py` shows the
identity already holds at `m = 2` and fails at `m = 0, 1`, so the true threshold
is `2`.  The paper says only "sufficiently large", and neither bound is stated
there. -/
theorem panelReductionCoeff (F : ℕ → Polynomial ℚ)
    (hF : ∀ M, denomConv (ftDenom panelDenQrat 1) F M
      = Polynomial.C (panelBrat.coeff M)) :
    ∀ m : ℕ, 4 ≤ m → panelP m = F (m + 2) := by
  have hQ0 : panelDenQrat.coeff 0 ≠ 0 := by rw [panelDenQrat_coeff_zero]; norm_num
  have hP : ∀ m, denomConv (ftDenom panelDenQrat 1) panelP m
      = (swapVars panelNbi).coeff m := by
    intro m
    rw [swapVars_panelNbi, ← panelP_denomConv, denomConv]
    exact Finset.sum_congr rfl fun j _ => by rw [panelDenomCoeff_eq_ftDenom]
  have hF' : ∀ M, denomConv (ftDenom panelDenQrat 1) F M
      = Polynomial.C ((laurentWeight panelDenQrat 1 panelNbi).coeff M) := by
    intro M; rw [panelLaurent.2]; exact hF M
  have hmain := reduction_coeff panelDenQrat (by norm_num) hQ0 panelNbi_ne_zero
    panelNbi_proper panelP F hP hF'
  intro m hm
  have hdeg : panelNbi.natDegree * (panelDenQrat.natDegree - 1) = 4 := by
    rw [panelNbi_natDegree, panelDenQrat_natDegree]
  have hshift : laurentShift panelDenQrat 1 panelNbi = (-2 : ℤ) := panelLaurent.1
  have h := hmain m (by omega) (by rw [hshift]; omega)
  rw [hshift] at h
  have htn : ((m : ℤ) - (-2 : ℤ)).toNat = m + 2 := by omega
  rw [h, htn]

end PanelLaurent

end ForgacsTran
