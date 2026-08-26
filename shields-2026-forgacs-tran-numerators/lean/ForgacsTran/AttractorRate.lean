/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.Attractor

/-!
# The panel-B attractor rate

`cor:panel-B-attractor` ends by applying `prop:isolated-dominant-cancellation` at
the panel-B data with `ν = 1` and `σ = 1/3`, and reading off the geometric
convergence `z_m = z_* + O(3^{-m})` of the coefficient zeros.  `Attractor`
verifies the hypotheses; the application is made here, so that the rate is a
statement of the tree and not only a remark about one.

## Main statements

* `panelBC` — the canonical Laurent weight `B_N` of `panelLaurent`, carried to
  `ℂ[X]`; `64·panelBC = panelB64`.  This is the univariate numerator
  `prop:isolated-dominant-cancellation` asks for.
* `taylorCoeff_panel` — what the rate is about: `F_M(z)` is the `M`-th Taylor
  coefficient at `t = 0` of the panel's own generating function `B/D(·,z)`.
* `panelB_rootMultiplicity_one` — `ν = 1`.  Rouché counts two zeros of `B` in
  `|t| < 1/2` with multiplicity and they are two *distinct* points, so each
  carries one.
* `eval_derivative_ftDen_panel_factor` — `∂_tD(t_*,z_*) = -(t_*-u)(t_*-v)/8`,
  which is `hsimple` once Vieta separates `u` and `v` from `t_*`.
* `panelB_isolated_cancellation` — `prop:isolated-dominant-cancellation` applied
  at the panel, with `R = 3/2` and `ρ = 1/3`.
* `rootMultiplicity_eq_one_of_factoredOn` — a `FactoredOn` count of one is
  simplicity at the displayed point, not only in total.
* `panel_attractor_rate` — the corollary's headline: for every large `M` the
  coefficient polynomial `F_M` has exactly one zero in a fixed disk about `z_*`,
  that zero is simple, and it is within `K·3^{-M}` of `z_*`.
* `eval_conj_ftCoeffPoly` — `F_M` commutes with conjugation whenever `Q` and `B`
  have conjugation-fixed coefficients, which the panel's do.
* `panel_attractor_rate_conj` — the corollary's "and the conjugate zero
  converges at the same rate": the packet at `conj z_*` is the conjugate of the
  packet at `z_*`.

## Implementation notes

The statement is in the general `F_M` variable, not the panel's own `P_m`.  The
index shift `P_m = F_{m+2}` is `panelReductionCoeff`, which characterizes its
`F` by the denominator convolution rather than by `ftCoeffPoly`; identifying the
two sequences is not done here, so the rate is stated for `F_M`.

`R = 3/2` and `ρ = 1/3` are the paper's own constants, and are what
`vieta_separation` and `spectral_ratio_lt_third` are proved for.  Neither is
tight — the separation needs only *some* radius between `‖t_*‖` and the other
two denominator moduli, and the true local spectral ratio
`eq:local-spectral-ratio` is well below `1/3` — but the paper's constants are
what is used.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `subsec:isolated-attractors`, `cor:panel-B-attractor`,
`prop:isolated-dominant-cancellation`, `eq:local-spectral-ratio`,
`eq:isolated-cancellation-rate`).

## Tags

zero attractor, dominant cancellation, geometric convergence, coefficient zeros
-/

namespace ForgacsTran

open Complex Metric Polynomial Shields ComplexConjugate

/-! ### The reduced numerator as a polynomial

`prop:isolated-dominant-cancellation` takes a `B ∈ ℂ[X]`, while `panelB64` is a
function and `panelBrat` lives over `ℚ`.  `panelBC` is the bridge.
-/

/-- Paper `cor:panel-B-attractor` — the canonical Laurent weight `B_N` of
`panelLaurent`, carried from `ℚ[X]` to `ℂ[X]`.  This is the `B` that
`prop:isolated-dominant-cancellation` consumes at the panel. -/
noncomputable def panelBC : ℂ[X] := panelBrat.map (algebraMap ℚ ℂ)

theorem panelBC_eval (x : ℂ) : panelBC.eval x = (1 / 64 : ℂ) * panelB64 x := by
  rw [panelBC, eval_map, ← aeval_def]
  simp only [panelBrat, panelB64rat, panelB64, map_mul, map_add, map_sub, map_pow,
    aeval_C, aeval_X, eq_ratCast]
  push_cast
  ring

theorem panelBC_ne_zero : panelBC ≠ 0 := by
  intro h
  have h0 := panelBC_eval 0
  rw [h] at h0
  simp only [eval_zero, panelB64] at h0
  norm_num at h0

/-! ### The pencil at the panel -/

theorem panelDenQ_eval (t : ℂ) :
    panelDenQ.eval t = 1 - (7 / 4) * t + (7 / 8) * t ^ 2 - (1 / 8) * t ^ 3 := by
  simp only [panelDenQ, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_one]

/-- The object the rate is about: `F_M(z)` is the `M`-th Taylor coefficient at
`t = 0` of the panel's generating function `B/D(·,z)`, which is
`prop:initial-data`'s `∑_M F_M(z)t^M`. -/
theorem taylorCoeff_panel (z : ℂ) (M : ℕ) :
    taylorCoeff (fun t => panelBC.eval t / panelDen z t) M
      = (ftCoeffPoly panelDenQ panelBC 1 M).eval z := by
  simp only [panelDen_eq_ftDen]
  exact taylorCoeff_div_ftDen panelDenQ panelBC le_rfl
    (by rw [panelDenQ_eval_zero]; norm_num) z M

/-- The `t`-derivative of the panel pencil, `∂_tD(t,z) = Q'(t) + z`. -/
theorem eval_derivative_ftDen_panel (z t : ℂ) :
    (derivative (ftDen panelDenQ 1 z)).eval t
      = -(7 / 4) + (7 / 4) * t - (3 / 8) * t ^ 2 + z := by
  simp only [ftDen, panelDenQ, derivative_add, derivative_sub, derivative_mul, derivative_C,
    derivative_X, derivative_one, derivative_X_pow, pow_one, zero_mul, zero_add,
    mul_one, Nat.cast_ofNat, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_zero]
  ring

/-- **Paper `cor:panel-B-attractor` — the simplicity of the dominant root.**
At `z_* = -Q(t_*)/t_*` the monic cubic `-8D` factors as `(t-t_*)(t-u)(t-v)`, so
its derivative at `t_*` is `(t_*-u)(t_*-v)`.  Vieta's two relations are all that
is needed to see it: `∂_tD(t_*,z_*) = -(t_*-u)(t_*-v)/8`.

**Differs from the paper's route.**  The paper computes no derivative: that
`t_*` is a simple denominator zero is read off the cubic having three distinct
zeros.  `prop:isolated-dominant-cancellation` asks for `∂_tD(t_*,z_*)` itself,
so it is computed here, and the two Vieta relations are substituted into it
rather than the factorization being differentiated — which leaves an identity
between rational functions of `t_*` alone. -/
theorem eval_derivative_ftDen_panel_factor {t u v : ℂ} (ht : t ≠ 0)
    (hsum : u + v = 7 - t) (hprod : u * v = 8 / t) :
    (derivative (ftDen panelDenQ 1 (panelZstar t))).eval t
      = -(1 / 8) * ((t - u) * (t - v)) := by
  have hexp : (t - u) * (t - v) = t ^ 2 - (u + v) * t + u * v := by ring
  rw [eval_derivative_ftDen_panel, hexp, hsum, hprod, panelZstar]
  field_simp
  ring

/-! ### The multiplicity of the cancellation -/

/-- **Paper `cor:panel-B-attractor` — the packet size is `ν = 1`.**  Rouché
counts two zeros of `B` in `|t| < 1/2` *with multiplicity*
(`panelB64_two_zeros`).  A factorization lists exactly its own zeros, so the two
displayed points are `t_*` and `conj t_*` — both are zeros in the disk, by
`panelB64_conj` — and those are distinct because `t_*` is nonreal.  Two distinct
points carrying total multiplicity two carry one apiece, so `t_*` is a simple
zero of `B`. -/
theorem panelB_rootMultiplicity_one {t : ℂ} (htim : 0 < t.im) (htn : ‖t‖ < 1 / 2)
    (htB : panelB64 t = 0) : panelBC.rootMultiplicity t = 1 := by
  obtain ⟨a, G, hfac⟩ := panelB64_two_zeros
  have htmem : t ∈ closedBall (0 : ℂ) (1 / 2) := mem_closedBall_zero_iff.mpr htn.le
  have hcmem : conj t ∈ closedBall (0 : ℂ) (1 / 2) :=
    mem_closedBall_zero_iff.mpr (by rw [RCLike.norm_conj]; exact htn.le)
  have hcB : panelB64 (conj t) = 0 := by rw [panelB64_conj, htB, map_zero]
  have hne : conj t ≠ t := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  -- the two displayed roots are `t` and `conj t`, in one order or the other
  obtain ⟨i, hi, hai⟩ := (hfac.eq_zero_iff htmem).mp htB
  obtain ⟨k, hk, hak⟩ := (hfac.eq_zero_iff hcmem).mp hcB
  have hpair : ∀ w : ℂ, (w - a 0) * (w - a 1) = (w - t) * (w - conj t) := by
    have hik : i ≠ k := by
      intro h
      rw [h, hak] at hai
      exact hne hai
    interval_cases i <;> interval_cases k <;> first
      | exact absurd rfl hik
      | (intro w; rw [hai, hak]; try ring)
  -- the cofactor at `t`
  set g : ℂ → ℂ := fun w => (1 / 64 : ℂ) * ((w - conj t) * G w) with hg
  have hGan : AnalyticAt ℂ G t := hfac.analytic t htmem
  have hgan : AnalyticAt ℂ g t :=
    analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).mul hGan)
  have hgne : g t ≠ 0 := by
    refine mul_ne_zero (by norm_num) (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) ?_)
    exact hfac.ne_zero t htmem
  have hord : analyticOrderAt (fun w => panelBC.eval w) t = ((1 : ℕ) : ℕ∞) := by
    refine (analyticAt_eval panelBC t).analyticOrderAt_eq_natCast.mpr ⟨g, hgan, hgne, ?_⟩
    filter_upwards with w
    rw [pow_one, smul_eq_mul, panelBC_eval, hfac.eq w, hg]
    have h2 : (∏ j ∈ Finset.range 2, (w - a j)) = (w - a 0) * (w - a 1) := by
      simp [Finset.prod_range_succ]
    rw [h2, hpair w]
    ring
  have heq := (analyticOrderAt_eval panelBC_ne_zero t).symm.trans hord
  exact_mod_cast heq

/-- **A one-root factorization is a simple root, at the displayed point.**
`FactoredOn F c ε 1 a G` writes `F = (· - a_0)G` at *every* point of the plane,
not only inside the disk, with `G` nonvanishing on the closed disk.  So `a_0` is
a root and the cofactor does not vanish there: the vanishing order at `a_0` is
exactly one.

This is what separates "one zero in the disk" from "a simple zero": the count is
total multiplicity, and it localizes only because the factorization names the
point. -/
theorem rootMultiplicity_eq_one_of_factoredOn {P : ℂ[X]} {c : ℂ} {ε : ℝ} (hε : 0 < ε)
    {a : ℕ → ℂ} {G : ℂ → ℂ} (hfac : FactoredOn (fun w => P.eval w) c ε 1 a G) :
    P.rootMultiplicity (a 0) = 1 := by
  have hmem : a 0 ∈ closedBall c ε := ball_subset_closedBall (hfac.mem_ball 0 Nat.one_pos)
  have hev : ∀ w : ℂ, P.eval w = (w - a 0) ^ 1 • G w := by
    intro w
    have h := hfac.eq w
    simp only [Finset.prod_range_one] at h
    rw [pow_one, smul_eq_mul]
    exact h
  have hP : P ≠ 0 := by
    intro h
    have hm1 : c + (ε : ℂ) ∈ closedBall c ε := by
      simp [mem_closedBall, abs_of_pos hε]
    have hm2 : c - (ε : ℂ) ∈ closedBall c ε := by
      simp [mem_closedBall, abs_of_pos hε]
    have h1 := hev (c + (ε : ℂ))
    have h2 := hev (c - (ε : ℂ))
    rw [h] at h1 h2
    simp only [eval_zero, pow_one, smul_eq_mul] at h1 h2
    have e1 : c + (ε : ℂ) = a 0 :=
      sub_eq_zero.mp ((mul_eq_zero.mp h1.symm).resolve_right (hfac.ne_zero _ hm1))
    have e2 : c - (ε : ℂ) = a 0 :=
      sub_eq_zero.mp ((mul_eq_zero.mp h2.symm).resolve_right (hfac.ne_zero _ hm2))
    have hz : (2 : ℂ) * (ε : ℂ) = 0 := by linear_combination e1 - e2
    have hz' : (ε : ℂ) = 0 := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    exact hε.ne' (Complex.ofReal_eq_zero.mp hz')
  have hord : analyticOrderAt (fun w => P.eval w) (a 0) = ((1 : ℕ) : ℕ∞) := by
    refine (analyticAt_eval P (a 0)).analyticOrderAt_eq_natCast.mpr
      ⟨G, hfac.analytic _ hmem, hfac.ne_zero _ hmem, ?_⟩
    filter_upwards with w
    exact hev w
  exact_mod_cast (analyticOrderAt_eval hP (a 0)).symm.trans hord

/-! ### The proposition applied -/

/-- **Paper `cor:panel-B-attractor`, the second assertion.**
`prop:isolated-dominant-cancellation` applied at the panel-B data, with `ν = 1`,
`R = 3/2` and `ρ = 1/3`.

`t` is `t_*` and `z` is `z_* = -Q(t_*)/t_*`, nonreal and a zero of the sextic the
corollary displays.  For every sufficiently large `M`, the coefficient
polynomial `F_M` of the general framework — at the panel's own pencil
`panelDenQ` and the panel's canonical Laurent weight `panelBC` — factors on a
fixed disk about `z_*` with exactly one root displayed, and that root obeys
`eq:isolated-cancellation-rate` at `ρ = 1/3`. -/
theorem panelB_isolated_cancellation :
    ∃ t z : ℂ, 0 < t.im ∧ ‖t‖ < 1 / 2 ∧ panelB64 t = 0 ∧ z = panelZstar t ∧
      z.im ≠ 0 ∧ panelResultant z = 0 ∧
      ∃ ε > 0, ∃ K ≥ (0 : ℝ), ∃ M₀ : ℕ, ∀ M ≥ M₀, ∃ (a : ℕ → ℂ) (G : ℂ → ℂ),
        FactoredOn (fun w => (ftCoeffPoly panelDenQ panelBC 1 M).eval w) z ε 1 a G ∧
        ∀ j < 1, ‖a j - z‖ ^ 1 ≤ K * (1 / 3 : ℝ) ^ M := by
  obtain ⟨t, z, -, -, htim, htn, htB, -, hz, hzim, -, hres, -, -, -, -, -⟩ := panelB_attractor
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at htim
    simp at htim
  refine ⟨t, z, htim, htn, htB, hz, hzim, hres, ?_⟩
  -- the other two denominator zeros at `z`, with Vieta and the separation
  have hden : panelDen z t = 0 := by rw [hz]; exact panelDen_panelZstar ht0
  have hcub : panelCubic z t = 0 := (panelDen_eq_zero_iff z t).mp hden
  obtain ⟨u, v, hfac, hsum, hprod⟩ := panelCubic_other_roots ht0 hcub
  have hu : 3 / 2 < ‖u‖ := vieta_separation ht0 htn hsum hprod
  have hv : 3 / 2 < ‖v‖ :=
    vieta_separation ht0 htn (by rw [add_comm]; exact hsum) (by rw [mul_comm]; exact hprod)
  -- `hsimple`
  have htu : t ≠ u := fun h => by rw [h] at htn; linarith
  have htv : t ≠ v := fun h => by rw [h] at htn; linarith
  have hsimple : (derivative (ftDen panelDenQ 1 z)).eval t ≠ 0 := by
    rw [hz, eval_derivative_ftDen_panel_factor ht0 hsum hprod]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero (sub_ne_zero.mpr htu) (sub_ne_zero.mpr htv))
  -- `hsep`, at the separating radius `R = 3/2`
  have hsep : ∀ w : ℂ, ‖w‖ ≤ 3 / 2 → (ftDen panelDenQ 1 z).eval w = 0 → w = t := by
    intro w hw hzero
    rw [← panelDen_eq_ftDen] at hzero
    have := (panelDen_eq_zero_iff z w).mp hzero
    rw [hfac w] at this
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact sub_eq_zero.mp h''
      · exact absurd (sub_eq_zero.mp h'' ▸ hw) (not_le.mpr hu)
    · exact absurd (sub_eq_zero.mp h' ▸ hw) (not_le.mpr hv)
  have hz₀ : z = -panelDenQ.eval t / t ^ 1 := by
    rw [pow_one, panelDenQ_eval, hz, panelZstar]
  have hρ : ‖t‖ / (3 / 2 : ℝ) < 1 / 3 := by
    rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
    linarith
  exact isolated_dominant_cancellation (Q := panelDenQ) (B := panelBC) le_rfl
    (by rw [panelDenQ_eval_zero]; norm_num) panelBC_ne_zero ht0 hz₀
    (panelB_rootMultiplicity_one htim htn htB) hsimple (by linarith) hsep hρ (by norm_num)

/-- **Paper `cor:panel-B-attractor` — the attractor rate.**  There is a nonreal
algebraic `z_*` and a fixed disk about it such that, for every sufficiently
large `M`, the coefficient polynomial `F_M` has exactly one zero `z_M` in that
disk, that zero is **simple**, and `‖z_M - z_*‖ ≤ K·3^{-M}`.  This is the
corollary's "a unique simple zero `z_m` near `z_*` with `z_m = z_* + O(3^{-m})`",
in the general framework's index.

Both halves of "unique simple" are carried: the multiplicity clause is
simplicity at `z_M`, and the `↔` is uniqueness as a point of the disk.  They are
different statements — a double zero at one point is unique as a point — so
neither implies the other and both are stated. -/
theorem panel_attractor_rate :
    ∃ z : ℂ, z.im ≠ 0 ∧ panelResultant z = 0 ∧
      ∃ ε > 0, ∃ K ≥ (0 : ℝ), ∃ M₀ : ℕ, ∀ M ≥ M₀, ∃ zM : ℂ,
        ‖zM - z‖ ≤ K * (1 / 3 : ℝ) ^ M ∧
        (ftCoeffPoly panelDenQ panelBC 1 M).rootMultiplicity zM = 1 ∧
        ∀ w ∈ closedBall z ε,
          (ftCoeffPoly panelDenQ panelBC 1 M).eval w = 0 ↔ w = zM := by
  obtain ⟨t, z, -, -, -, -, hzim, hres, ε, hε, K, hK, M₀, hM⟩ := panelB_isolated_cancellation
  refine ⟨z, hzim, hres, ε, hε, K, hK, M₀, fun M hMM => ?_⟩
  obtain ⟨a, G, hfac, hrate⟩ := hM M hMM
  refine ⟨a 0, by simpa using hrate 0 (by norm_num),
    rootMultiplicity_eq_one_of_factoredOn hε hfac, fun w hw => ?_⟩
  rw [hfac.eq_zero_iff hw]
  constructor
  · rintro ⟨j, hj, rfl⟩
    interval_cases j
    rfl
  · rintro rfl
    exact ⟨0, by norm_num, rfl⟩

/-! ### The conjugate packet

`cor:panel-B-attractor` closes on "and conjugation gives the second zero".  The
panel's pencil and its Laurent weight both have rational coefficients, so every
`F_M` does, and the whole packet reflects.
-/

theorem panelDenQ_eq_map : panelDenQ = panelDenQrat.map (algebraMap ℚ ℂ) := by
  simp only [panelDenQ, panelDenQrat, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_one, eq_ratCast]
  norm_num

/-- The coefficients of a polynomial carried up from `ℚ` are fixed by
conjugation. -/
private theorem conj_coeff_map (p : ℚ[X]) (j : ℕ) :
    conj ((p.map (algebraMap ℚ ℂ)).coeff j) = (p.map (algebraMap ℚ ℂ)).coeff j := by
  rw [Polynomial.coeff_map, eq_ratCast]
  simp

theorem conj_coeff_panelDenQ (j : ℕ) : conj (panelDenQ.coeff j) = panelDenQ.coeff j := by
  rw [panelDenQ_eq_map]; exact conj_coeff_map _ j

theorem conj_coeff_panelBC (j : ℕ) : conj (panelBC.coeff j) = panelBC.coeff j :=
  conj_coeff_map _ j

private theorem eval_conj_ftDenCoeff {Q : ℂ[X]} (hQ : ∀ j, conj (Q.coeff j) = Q.coeff j)
    (r j : ℕ) (z : ℂ) :
    (ftDenCoeff Q r j).eval (conj z) = conj ((ftDenCoeff Q r j).eval z) := by
  by_cases h : j = r <;> simp [ftDenCoeff, h, hQ]

/-- **`F_M` commutes with conjugation.**  The convolution recurrence defining
`ftCoeffPoly` involves only the coefficients of `Q` and of `B`, so if those are
fixed by conjugation then so is the whole sequence, and the zero set of every
`F_M` is closed under reflection in the real axis. -/
theorem eval_conj_ftCoeffPoly {Q B : ℂ[X]} (hQ : ∀ j, conj (Q.coeff j) = Q.coeff j)
    (hB : ∀ j, conj (B.coeff j) = B.coeff j) (r M : ℕ) (z : ℂ) :
    (ftCoeffPoly Q B r M).eval (conj z) = conj ((ftCoeffPoly Q B r M).eval z) := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    have hsum : ∀ i ∈ Finset.range M,
        (ftDenCoeff Q r (M - i) * ftCoeffPoly Q B r i).eval (conj z)
          = conj ((ftDenCoeff Q r (M - i) * ftCoeffPoly Q B r i).eval z) := by
      intro i hi
      rw [eval_mul, eval_mul, map_mul, eval_conj_ftDenCoeff hQ,
        ih i (Finset.mem_range.mp hi)]
    rw [ftCoeffPoly_eq, eval_mul, eval_sub, eval_C, eval_C, eval_finsetSum,
      eval_mul, eval_sub, eval_C, eval_C, eval_finsetSum, map_mul, map_sub, map_sum,
      map_inv₀, hQ 0, hB M, Finset.sum_congr rfl hsum]

/-- Conjugating a polynomial's coefficients reflects its evaluation. -/
private theorem eval_map_conj (P : ℂ[X]) (w : ℂ) :
    (P.map (starRingEnd ℂ)).eval w = conj (P.eval (conj w)) := by
  rw [Polynomial.eval_map]
  have h := Polynomial.hom_eval₂ P (RingHom.id ℂ) (starRingEnd ℂ) (conj w)
  simpa [Polynomial.eval₂_id, starRingEnd_self_apply] using h.symm

/-- **`F_M` is fixed by conjugating its coefficients**, which is the polynomial
form of `eval_conj_ftCoeffPoly`.  It is what carries a root multiplicity from a
point to its reflection. -/
theorem map_conj_ftCoeffPoly {Q B : ℂ[X]} (hQ : ∀ j, conj (Q.coeff j) = Q.coeff j)
    (hB : ∀ j, conj (B.coeff j) = B.coeff j) (r M : ℕ) :
    (ftCoeffPoly Q B r M).map (starRingEnd ℂ) = ftCoeffPoly Q B r M := by
  refine Polynomial.funext fun w => ?_
  rw [eval_map_conj, eval_conj_ftCoeffPoly hQ hB, starRingEnd_self_apply]

/-- **A conjugation-fixed polynomial has the same root multiplicity at a point
and at its reflection.** -/
theorem rootMultiplicity_conj_ftCoeffPoly {Q B : ℂ[X]} (hQ : ∀ j, conj (Q.coeff j) = Q.coeff j)
    (hB : ∀ j, conj (B.coeff j) = B.coeff j) (r M : ℕ) (w : ℂ) :
    (ftCoeffPoly Q B r M).rootMultiplicity (conj w)
      = (ftCoeffPoly Q B r M).rootMultiplicity w := by
  have h := Polynomial.eq_rootMultiplicity_map (p := ftCoeffPoly Q B r M)
    (f := starRingEnd ℂ) (starRingEnd ℂ).injective w
  rw [map_conj_ftCoeffPoly hQ hB] at h
  exact h.symm

/-- **Paper `cor:panel-B-attractor` — the conjugate packet.**  `F_M` has
conjugation-fixed coefficients at the panel, so alongside the zero `z_M`
approaching `z_*` there is the zero `conj z_M` approaching `conj z_*`, at the
same rate and alone in the reflected disk. -/
theorem panel_attractor_rate_conj :
    ∃ z : ℂ, z.im ≠ 0 ∧ panelResultant z = 0 ∧
      ∃ ε > 0, ∃ K ≥ (0 : ℝ), ∃ M₀ : ℕ, ∀ M ≥ M₀, ∃ zM : ℂ,
        ‖zM - z‖ ≤ K * (1 / 3 : ℝ) ^ M ∧
        (ftCoeffPoly panelDenQ panelBC 1 M).rootMultiplicity zM = 1 ∧
        (∀ w ∈ closedBall z ε,
          (ftCoeffPoly panelDenQ panelBC 1 M).eval w = 0 ↔ w = zM) ∧
        ‖conj zM - conj z‖ ≤ K * (1 / 3 : ℝ) ^ M ∧
        (ftCoeffPoly panelDenQ panelBC 1 M).rootMultiplicity (conj zM) = 1 ∧
        (∀ w ∈ closedBall (conj z) ε,
          (ftCoeffPoly panelDenQ panelBC 1 M).eval w = 0 ↔ w = conj zM) := by
  obtain ⟨z, hzim, hres, ε, hε, K, hK, M₀, hM⟩ := panel_attractor_rate
  refine ⟨z, hzim, hres, ε, hε, K, hK, M₀, fun M hMM => ?_⟩
  obtain ⟨zM, hrate, hmult, hzero⟩ := hM M hMM
  refine ⟨zM, hrate, hmult, hzero, ?_, ?_, fun w hw => ?_⟩
  · rw [← map_sub, RCLike.norm_conj]
    exact hrate
  · rw [rootMultiplicity_conj_ftCoeffPoly conj_coeff_panelDenQ conj_coeff_panelBC]
    exact hmult
  · have hzz : z = conj (conj z) := (starRingEnd_self_apply z).symm
    have hwmem : conj w ∈ closedBall z ε := by
      rw [mem_closedBall, Complex.dist_eq, hzz, ← map_sub, RCLike.norm_conj]
      simpa [Complex.dist_eq] using hw
    have hconj := eval_conj_ftCoeffPoly conj_coeff_panelDenQ conj_coeff_panelBC 1 M w
    constructor
    · intro h0
      have : (ftCoeffPoly panelDenQ panelBC 1 M).eval (conj w) = 0 := by
        rw [hconj, h0, map_zero]
      have := (hzero (conj w) hwmem).mp this
      rw [← this, starRingEnd_self_apply]
    · intro h0
      have hcw : conj w = zM := by rw [h0, starRingEnd_self_apply]
      have : (ftCoeffPoly panelDenQ panelBC 1 M).eval (conj w) = 0 :=
        (hzero (conj w) hwmem).mpr hcw
      rw [hconj] at this
      simpa using this

end ForgacsTran
