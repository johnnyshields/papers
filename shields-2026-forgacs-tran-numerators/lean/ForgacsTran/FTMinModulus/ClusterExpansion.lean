/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTMinModulus.Propositions

/-!
# The cluster expansion and the `ρ`-th-root localization

At an endpoint where `Q` has a zero of multiplicity `ρ ≥ 2`, the `ρ` denominator
zeros that emerge form a cluster whose members leave the endpoint along the `ρ`-th
roots of a fixed complex number.  This module produces that expansion and the
localization statement that pins each member to its own root of unity.

## Main statements

* `ftCritical_eval_eq_zero_of_two_le_rootMultiplicity`, `second_deriv_relation` —
  Prop. 3 Case 2 at `ρ = 1`: a repeated denominator zero kills the critical
  polynomial there, and the second derivative relation that replaces it.
* `abs_norm_one_add_sub_le`, `abs_norm_sub_one_add_re_mul_le`,
  `endpoint_expansion_coeff_re` — from a complex endpoint expansion to the
  expansion of its modulus, which is the only part the minimum-modulus argument
  sees.
* `exists_endpoint_linear_gap_of_expansion_on`,
  `exists_endpoint_linear_gap_of_expansion` — the linear gap the expansion opens
  between the principal member and the rest.
* `cluster_two_root_eq`, `clusterAlpha_re`, `clusterAlpha_coeff`,
  `cluster_normalized_expansion` — Prop. 3 Case 2 read off the cluster: the
  normalized expansion of a member in terms of its `ρ`-th root of unity.
* `exists_root_of_unity_close`, `exists_cluster_ratio_close`,
  `norm_cluster_ratio_sub_one_le` — the `ρ`-th-root localization: a point close
  to `1` in the `ρ`-th power is close to one of the `ρ` roots of unity, with the
  quantitative form the cluster needs.
* `principal_expansion_of_tau_rate`, `cluster_member_expansion`,
  `abs_sub_linear_le_of_deriv_bound`, `exists_clusterOmega_eq` — the member
  expansions and the derivative bound that turns a rate into a linear estimate.
* `norm_pow_sub_pow_le_of_norm_le`, `norm_eval_sub_eval_le_of_norm_le`,
  `norm_eval_mem_of_norm_sub_le` — a polynomial's increment on a disk of radius
  `M`, with an explicit Lipschitz constant, and the two-sided modulus bound it
  gives near a point where the polynomial does not vanish.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
  and the principal amplitude» — `sec:geometry`, `lem:amplitude-divisor`.
* `Forgacs2017RationalDenominator`, Proposition 3 Case 2.

## Tags

cluster expansion, root of unity, endpoint, multiplicity, localization
-/

namespace ForgacsTran

open Polynomial

/-! ### `Forgacs2017RationalDenominator` Prop. 3, Case 2 with `ρ = 1`

Our `thm:FT-geometry` takes "the second and third cases" of their Prop. 3.  The
second case splits on the multiplicity `ρ` of the smallest zero of `P`, and its
`ρ = 1` half is finite algebra rather than an asymptotic expansion: the limiting
pencil `P(t) + a t^r` has a zero of multiplicity at least two at `t_a`, and the
derivative conditions that forces are exactly `Geometry.ftCritical` vanishing
there.  **Only that half is here**; the `ρ > 1` half of the second case, and the
third case, are not claimed — see the note below.

Their step "besides the double zero at `t_a`, the moduli of the other zeros are
not `t_a`" is `Geometry.eval_ftDen_ne_zero_of_norm_eq`, which is the strict
minimum-modulus comparison and is already proved; nothing further is needed for
it. -/

/-- **`Forgacs2017RationalDenominator` Prop. 3, Case 2 (`ρ = 1`), first
implication.**  A denominator zero of multiplicity at least two at `t_e ≠ 0`
forces `rP(t_e) - t_e P'(t_e) = 0` — their two displayed equations combined.
That expression is `Geometry.ftCritical` up to sign, so the conclusion is that
`t_e` is one of the critical points `eq:ab-def` reads the endpoints off. -/
theorem ftCritical_eval_eq_zero_of_two_le_rootMultiplicity {P : Polynomial ℂ} {r : ℕ}
    (hr : 1 ≤ r) {a te : ℂ} (hte : te ≠ 0) (hP : ftDen P r a ≠ 0)
    (hmult : 2 ≤ (ftDen P r a).rootMultiplicity te) :
    (ftCritical P r).eval te = 0 := by
  have hk : 1 ≤ (ftDen P r a).rootMultiplicity te := by omega
  have hrm := rootMultiplicity_ftCritical hr hte hP hk
  have hpos : 0 < (ftCritical P r).rootMultiplicity te := by omega
  have hne : ftCritical P r ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  exact (Polynomial.rootMultiplicity_pos hne).1 hpos

/-- **`Forgacs2017RationalDenominator` Prop. 3, Case 2 (`ρ = 1`), second
implication.**  If the collision is of multiplicity at least three, the second
and third derivative conditions combine to `(r-1)P'(t_e) - t_e P''(t_e) = 0`.
Their proof then plays this against the interlacing of the zeros of `P'` and
`P''` to contradict `ρ = 1`; that interlacing step is not here. -/
theorem second_deriv_relation {P : Polynomial ℂ} {r : ℕ} (hr : 2 ≤ r) {a te : ℂ}
    (hte : te ≠ 0)
    (h2 : (derivative P).eval te + (r : ℂ) * a * te ^ (r - 1) = 0)
    (h3 : (derivative (derivative P)).eval te
      + (r : ℂ) * ((r : ℂ) - 1) * a * te ^ (r - 2) = 0) :
    ((r : ℂ) - 1) * (derivative P).eval te
      - te * (derivative (derivative P)).eval te = 0 := by
  have hpow : te ^ (r - 1) = te * te ^ (r - 2) := by
    conv_lhs => rw [show r - 1 = 1 + (r - 2) by omega]
    rw [pow_add, pow_one]
  have e2 : (derivative P).eval te = -((r : ℂ) * a * te ^ (r - 1)) := by linear_combination h2
  have e3 : (derivative (derivative P)).eval te
      = -((r : ℂ) * ((r : ℂ) - 1) * a * te ^ (r - 2)) := by linear_combination h3
  rw [e2, e3, hpow]
  ring


/-! ### From the complex endpoint expansion to its modulus

`Forgacs2017RationalDenominator` Prop. 3 gives the cluster expansion with a
**complex** coefficient, `ζ_j(θ) = 1 + c_jθ + O(θ²)` with
`c_j = (cos(π/ρ) - ω_j)/sin(π/ρ)`.  What `thm:FT-geometry`'s extraction consumes
is its **modulus**, `|ζ_j(θ)| = 1 + (Re c_j)θ + O(θ²)`.  The two are not
interchangeable: `ζ_j - (1 + (Re c_j)θ)` is of exact order `θ` whenever `ω_j` is
nonreal, so only the modulus may have its coefficient replaced by the real part.
This is the transfer between them. -/

/-- `|1 + w| = 1 + Re w + O(|w|²)`, with the error at most `|w|²` for `|w| ≤ 1/2`:
the difference of squares is `(Im w)²` and the denominator is at least one. -/
theorem abs_norm_one_add_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    |‖1 + w‖ - (1 + w.re)| ≤ ‖w‖ ^ 2 := by
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hre' : -(1/2 : ℝ) ≤ w.re := by
    have := neg_abs_le w.re; linarith [hre, hw]
  have h1 : (1 : ℝ) / 2 ≤ 1 + w.re := by linarith
  have h2 : (1 : ℝ) / 2 ≤ ‖1 + w‖ := by
    have h := norm_sub_le ((1 : ℂ) + w) w
    simp only [add_sub_cancel_right, norm_one] at h
    linarith [hw]
  have hsq : ‖1 + w‖ ^ 2 - (1 + w.re) ^ 2 = w.im ^ 2 := by
    have hn : ∀ v : ℂ, ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := fun v => by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hn]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have him : w.im ^ 2 ≤ ‖w‖ ^ 2 := by
    have h := Complex.abs_im_le_norm w
    nlinarith [abs_nonneg w.im, norm_nonneg w, sq_abs w.im]
  rw [abs_le]
  constructor <;> nlinarith [hsq, him, h1, h2, norm_nonneg w]

/-- **The endpoint expansion in modulus.**  From `‖ζ - (1 + cθ)‖ ≤ Cθ²` — their
Prop. 3's display, with the complex coefficient — the modulus satisfies
`|‖ζ‖ - (1 + (Re c)θ)| ≤ (C + ‖c‖²)θ²`, which is the form `eq:endpoint-linear-gap`
is extracted from.  Replacing `c` by `Re c` *inside* the complex statement is not
valid; it is valid only after taking the modulus, which is what this records.

The `‖c‖²θ²` term is exactly what the imaginary part costs, and `hsmall` is not
slack.  Writing `u = 1 + cθ`, the identity `‖u‖² - (1 + (Re c)θ)² = ((Im c)θ)²`
is exact, so

  `‖u‖ - (1 + (Re c)θ) = ((Im c)θ)² / (‖u‖ + 1 + (Re c)θ)`,

and `hsmall` puts `1 + (Re c)θ ≥ 1/2` and `‖u‖ ≥ 1/2`, hence the denominator
above `1`.  So the error is at most `(Im c)²θ² ≤ ‖c‖²θ²`: a real `c` costs
nothing and the whole term is the imaginary part. -/
theorem abs_norm_sub_one_add_re_mul_le {c ζ : ℂ} {θ C : ℝ} (hθ : 0 ≤ θ)
    (hsmall : ‖c‖ * θ ≤ 1 / 2) (h : ‖ζ - (1 + c * (θ : ℂ))‖ ≤ C * θ ^ 2) :
    |‖ζ‖ - (1 + c.re * θ)| ≤ (C + ‖c‖ ^ 2) * θ ^ 2 := by
  have hw : ‖c * (θ : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ]
    exact hsmall
  have hre : (c * (θ : ℂ)).re = c.re * θ := by
    simp [Complex.mul_re]
  have h1 : |‖ζ‖ - ‖1 + c * (θ : ℂ)‖| ≤ C * θ ^ 2 :=
    le_trans (abs_norm_sub_norm_le _ _) h
  have h2 : |‖1 + c * (θ : ℂ)‖ - (1 + c.re * θ)| ≤ ‖c‖ ^ 2 * θ ^ 2 := by
    have := abs_norm_one_add_sub_le hw
    rw [hre] at this
    refine le_trans this ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ, mul_pow]
  calc |‖ζ‖ - (1 + c.re * θ)|
      = |(‖ζ‖ - ‖1 + c * (θ : ℂ)‖) + (‖1 + c * (θ : ℂ)‖ - (1 + c.re * θ))| := by ring_nf
    _ ≤ |‖ζ‖ - ‖1 + c * (θ : ℂ)‖| + |‖1 + c * (θ : ℂ)‖ - (1 + c.re * θ)| := abs_add_le _ _
    _ ≤ C * θ ^ 2 + ‖c‖ ^ 2 * θ ^ 2 := add_le_add h1 h2
    _ = (C + ‖c‖ ^ 2) * θ ^ 2 := by ring

/-- The real part of `Forgacs2017RationalDenominator` Prop. 3's coefficient.  The
denominator `sin(π/ρ)` is real, so the real part passes through the quotient and
lands on `Geometry.endpoint_linear_coeff_pos`'s expression verbatim. -/
theorem endpoint_expansion_coeff_re {ρ : ℕ} {ω : ℂ} :
    ((((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - ω) / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)).re
      = (Real.cos (Real.pi / ρ) - ω.re) / Real.sin (Real.pi / ρ) := by
  rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm, Complex.re_ofReal_mul,
    Complex.sub_re, Complex.ofReal_re]
  ring

/-- **`eq:endpoint-linear-gap`, supplied from the expansion
`Forgacs2017RationalDenominator` Prop. 3 actually gives.**  A finite cluster
whose normalized members expand as `ζ_j(δ) = 1 + c_jδ + O(δ²)` with `c_j`
**complex** and `Re c_j > 0` obeys a single uniform linear modulus gap
`‖ζ_j(δ)‖ ≥ 1 + c_0δ`.

The coefficient has to be complex.  Prop. 3's coefficient is
`c_j = (cos(π/ρ) - ω_j)/sin(π/ρ)` with `ω_j^ρ = -1`, so `Im c_j ≠ 0` at every
nonreal `ω_j`, and then `ζ_j(δ) - (1 + (Re c_j)δ) = i(Im c_j)δ + O(δ²)` is of
exact order `δ`: no `O(δ²)` bound on it can hold, and a hypothesis asserting one
is unsatisfiable rather than merely strong.  It is the *modulus* that obeys the
real-coefficient bound, by `abs_norm_sub_one_add_re_mul_le`, and the gap is
extracted from that.  `Geometry.endpoint_linear_coeff_pos` supplies `Re c_j > 0`.

The conclusion is `Geometry.exists_endpoint_linear_gap`'s verbatim, so this is a
drop-in wherever that one is applied to a genuinely complex expansion. -/
theorem exists_endpoint_linear_gap_of_expansion_on {ι : Type*} {J : Finset ι}
    {ζ : ι → ℝ → ℂ} {c : ι → ℂ} {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hcf : ∀ j ∈ J, 0 < (c j).re)
    (hexp : ∀ j ∈ J, ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      ‖ζ j δ - (1 + c j * (δ : ℂ))‖ ≤ C * δ ^ 2) :
    ∃ c₀ > 0, ∃ δ₀ > 0, ∀ j ∈ J, ∀ δ : ℝ, 0 < δ → δ < δ₀ → 1 + c₀ * δ ≤ ‖ζ j δ‖ := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · exact ⟨1, one_pos, 1, one_pos, by simp⟩
  obtain ⟨j₀, hj₀⟩ := hJ
  have hJ' : J.Nonempty := ⟨j₀, hj₀⟩
  obtain ⟨cmin, hcmin_pos, hcmin⟩ : ∃ x : ℝ, 0 < x ∧ ∀ j ∈ J, x ≤ (c j).re :=
    ⟨J.inf' hJ' (fun j => (c j).re), (Finset.lt_inf'_iff hJ').2 hcf,
      fun j hj => Finset.inf'_le _ hj⟩
  set N : ℝ := J.sup' hJ' (fun j => ‖c j‖) with hNdef
  have hNle : ∀ j ∈ J, ‖c j‖ ≤ N := fun j hj => Finset.le_sup' (fun j => ‖c j‖) hj
  have hN0 : (0 : ℝ) ≤ N := le_trans (norm_nonneg _) (hNle j₀ hj₀)
  have hN1 : (0 : ℝ) < N + 1 := by linarith
  set C' : ℝ := C + N ^ 2 with hC'def
  have hC'0 : (0 : ℝ) ≤ C' := by
    have : (0 : ℝ) ≤ N ^ 2 := sq_nonneg N
    simp only [hC'def]; linarith
  have hC'1 : (0 : ℝ) < C' + 1 := by linarith
  refine ⟨cmin / 2, by positivity,
    min (min ε (1 / (2 * (N + 1)))) (cmin / (2 * (C' + 1))),
    lt_min (lt_min hε (div_pos one_pos (by linarith)))
      (div_pos hcmin_pos (by linarith)), ?_⟩
  intro j hj δ hδ hδ₀
  have hδ1 : δ ≤ ε :=
    le_of_lt (lt_of_lt_of_le hδ₀ (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hδN : δ < 1 / (2 * (N + 1)) :=
    lt_of_lt_of_le hδ₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδC : δ < cmin / (2 * (C' + 1)) := lt_of_lt_of_le hδ₀ (min_le_right _ _)
  have hcj : cmin ≤ (c j).re := hcmin j hj
  have hNj : ‖c j‖ ≤ N := hNle j hj
  have hsmall : ‖c j‖ * δ ≤ 1 / 2 := by
    have h2 : (N + 1) * δ < (N + 1) * (1 / (2 * (N + 1))) :=
      mul_lt_mul_of_pos_left hδN hN1
    have h3 : (N + 1) * (1 / (2 * (N + 1))) = 1 / 2 := by field_simp
    nlinarith [hδ.le, norm_nonneg (c j)]
  have hb := abs_norm_sub_one_add_re_mul_le hδ.le hsmall (hexp j hj δ hδ hδ1)
  have hsq : ‖c j‖ ^ 2 ≤ N ^ 2 := by nlinarith [norm_nonneg (c j)]
  have hb' : |‖ζ j δ‖ - (1 + (c j).re * δ)| ≤ C' * δ ^ 2 := by
    refine le_trans hb ?_
    have : C + ‖c j‖ ^ 2 ≤ C' := by simp only [hC'def]; linarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg δ)
  have hlow : 1 + (c j).re * δ - C' * δ ^ 2 ≤ ‖ζ j δ‖ := by
    have := abs_le.1 hb'
    linarith [this.1]
  have hC'δ : C' * δ ≤ cmin / 2 := by
    have h1 : C' * δ ≤ (C' + 1) * δ := by nlinarith [hδ.le]
    have h2 : (C' + 1) * δ < (C' + 1) * (cmin / (2 * (C' + 1))) :=
      mul_lt_mul_of_pos_left hδC hC'1
    have h3 : (C' + 1) * (cmin / (2 * (C' + 1))) = cmin / 2 := by field_simp
    linarith
  nlinarith [hlow, hC'δ, hδ, hcj]

/-- The `ε = 1` case, which is what `FTGeometryAssembly` applies where the
expansion is genuinely controlled on the whole of `(0,1]`.  Where it is not —
`DominanceFT`'s `hexp₀`, whose family exists only for small `δ` — the windowed
form above is the one a supplier can meet. -/
theorem exists_endpoint_linear_gap_of_expansion {ι : Type*} {J : Finset ι}
    {ζ : ι → ℝ → ℂ} {c : ι → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hcf : ∀ j ∈ J, 0 < (c j).re)
    (hexp : ∀ j ∈ J, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ‖ζ j δ - (1 + c j * (δ : ℂ))‖ ≤ C * δ ^ 2) :
    ∃ c₀ > 0, ∃ δ₀ > 0, ∀ j ∈ J, ∀ δ : ℝ, 0 < δ → δ < δ₀ → 1 + c₀ * δ ≤ ‖ζ j δ‖ :=
  exists_endpoint_linear_gap_of_expansion_on hC one_pos hcf hexp

/-! ### `Forgacs2017RationalDenominator` Prop. 3, Case 2 — from the cluster
expansion to the normalized bound

`hexp₀` asks for the normalized cluster members `ζ_j(δ) = t_j(δ)/τ(δ)` expanded
to first order with an explicit `O(δ²)` remainder.  What is proved here is the
passage from `eq:lower-cluster-expansion` — the members themselves expanded,
`t_j(δ) = x_1 + α_jδ + O(δ²)` — to that normalized statement, pointwise on a
window and with the constant produced rather than assumed.

The coefficient comes out as `(cos(π/ρ) - ω_j)/sin(π/ρ)` **complex**, which is
`Forgacs2017RationalDenominator`'s own display and not its real part: dividing by
`τ = ‖t_p‖` replaces the principal direction by its real part `cos(π/ρ)` and
leaves `ω_j` alone.

**Only Cases 2 and 3 are in scope**, since those are the endpoints
`thm:FT-geometry` consumes; Case 1 of that proposition is not claimed.  The
cluster expansion itself is the remaining input, and `cluster_two_root_eq` is the
`z`-free equation it is read off. -/

/-- **The `z`-free cluster equation.**  Two zeros of one pencil member satisfy a
relation with `z` eliminated, exactly as `Geometry.ftCritical` eliminates it from
`∂_tD`.  Writing `Q = (X - x_1)^ρ q`, the ratio `((t₁-x_1)/(t₂-x_1))^ρ` is
determined by `q` and the `r`-th powers alone, which is what makes the `ρ`
cluster members differ to leading order by the `ρ`-th roots of unity. -/
theorem cluster_two_root_eq {Q q : ℂ[X]} {x₁ : ℂ} {ρ r : ℕ} (hQ : Q = (X - C x₁) ^ ρ * q)
    {z t₁ t₂ : ℂ} (h₁ : (ftDen Q r z).eval t₁ = 0) (h₂ : (ftDen Q r z).eval t₂ = 0) :
    (t₁ - x₁) ^ ρ * q.eval t₁ * t₂ ^ r = (t₂ - x₁) ^ ρ * q.eval t₂ * t₁ ^ r := by
  have e₁ := cluster_root_eq hQ h₁
  have e₂ := cluster_root_eq hQ h₂
  calc (t₁ - x₁) ^ ρ * q.eval t₁ * t₂ ^ r = -(z * t₁ ^ r) * t₂ ^ r := by rw [e₁]
    _ = -(z * t₂ ^ r) * t₁ ^ r := by ring
    _ = (t₂ - x₁) ^ ρ * q.eval t₂ * t₁ ^ r := by rw [e₂]

/-- **The normalization step of `Forgacs2017RationalDenominator` Prop. 3.**  A
point expanded as `g = x + Aδ + O(δ²)` and a positive real `τ` expanded as
`τ = x + (Re B)δ + O(δ²)` give the ratio expanded as
`g/τ = 1 + ((A - Re B)/x)δ + O(δ²)`, with the constant explicit and the bound
pointwise on `(0,1]` rather than asymptotic.

The residual is exact: `(x + Aδ) - (x + (Re B)δ)(1 + Eδ) = -(Re B)Eδ²` when
`xE = A - Re B`, so nothing is discarded and the three error terms are the two
hypotheses plus that residual. -/
theorem norm_div_sub_one_add_mul_le {x τ C D δ : ℝ} {A B g : ℂ}
    (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hτ2 : x / 2 ≤ τ)
    (hg : ‖g - ((x : ℂ) + A * (δ : ℂ))‖ ≤ C * δ ^ 2)
    (hτ : |τ - (x + B.re * δ)| ≤ D * δ ^ 2) :
    ‖g / (τ : ℂ) - (1 + ((A - (B.re : ℂ)) / (x : ℂ)) * (δ : ℂ))‖
      ≤ (2 / x) * (C + D * (1 + ‖(A - (B.re : ℂ)) / (x : ℂ)‖)
        + |B.re| * ‖(A - (B.re : ℂ)) / (x : ℂ)‖) * δ ^ 2 := by
  set E : ℂ := (A - (B.re : ℂ)) / (x : ℂ) with hE
  set K : ℝ := C + D * (1 + ‖E‖) + |B.re| * ‖E‖ with hK
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  have hxE : (x : ℂ) * E = A - (B.re : ℂ) := by rw [hE]; field_simp
  have hτpos : 0 < τ := lt_of_lt_of_le (by linarith) hτ2
  have hτ0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hτpos.ne'
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hC0 : 0 ≤ C := by nlinarith [norm_nonneg (g - ((x : ℂ) + A * (δ : ℂ)))]
  have hD0 : 0 ≤ D := by nlinarith [abs_nonneg (τ - (x + B.re * δ))]
  have hK0 : 0 ≤ K := by
    have h1 := norm_nonneg E
    have h2 := abs_nonneg B.re
    rw [hK]; nlinarith
  -- the exact decomposition: nothing is discarded
  have hkey : g - (τ : ℂ) * (1 + E * (δ : ℂ))
      = (g - ((x : ℂ) + A * (δ : ℂ)))
        - (((τ : ℂ) - ((x : ℂ) + (B.re : ℂ) * (δ : ℂ))) * (1 + E * (δ : ℂ)))
        - (B.re : ℂ) * E * (δ : ℂ) ^ 2 := by
    have h : (x : ℂ) * E * (δ : ℂ) = (A - (B.re : ℂ)) * (δ : ℂ) := by rw [hxE]
    linear_combination -h
  have hEδ : ‖(1 : ℂ) + E * (δ : ℂ)‖ ≤ 1 + ‖E‖ := by
    refine le_trans (norm_add_le _ _) ?_
    have h : ‖E * (δ : ℂ)‖ ≤ ‖E‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
      nlinarith [norm_nonneg E]
    simpa using h
  have hτc : ‖(τ : ℂ) - ((x : ℂ) + (B.re : ℂ) * (δ : ℂ))‖ ≤ D * δ ^ 2 := by
    have hcast : (τ : ℂ) - ((x : ℂ) + (B.re : ℂ) * (δ : ℂ))
        = ((τ - (x + B.re * δ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact hτ
  have hres : ‖(B.re : ℂ) * E * (δ : ℂ) ^ 2‖ = |B.re| * ‖E‖ * δ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have hnum : ‖g - (τ : ℂ) * (1 + E * (δ : ℂ))‖ ≤ K * δ ^ 2 := by
    rw [hkey]
    have h3 := norm_sub_le
      ((g - ((x : ℂ) + A * (δ : ℂ)))
        - (((τ : ℂ) - ((x : ℂ) + (B.re : ℂ) * (δ : ℂ))) * (1 + E * (δ : ℂ))))
      ((B.re : ℂ) * E * (δ : ℂ) ^ 2)
    have h4 := norm_sub_le (g - ((x : ℂ) + A * (δ : ℂ)))
      (((τ : ℂ) - ((x : ℂ) + (B.re : ℂ) * (δ : ℂ))) * (1 + E * (δ : ℂ)))
    have h5 : ‖((τ : ℂ) - ((x : ℂ) + (B.re : ℂ) * (δ : ℂ))) * (1 + E * (δ : ℂ))‖
        ≤ (D * δ ^ 2) * (1 + ‖E‖) := by
      rw [norm_mul]
      exact mul_le_mul hτc hEδ (norm_nonneg _) (by positivity)
    rw [hres] at h3
    rw [hK]; nlinarith [hg, h3, h4, h5]
  have hdiv : g / (τ : ℂ) - (1 + E * (δ : ℂ))
      = (g - (τ : ℂ) * (1 + E * (δ : ℂ))) / (τ : ℂ) := by field_simp
  rw [hdiv, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτpos,
    div_le_iff₀ hτpos]
  have h1 : (1 : ℝ) ≤ 2 / x * τ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hx]
    linarith
  have hgoal : 2 / x * K * δ ^ 2 * τ = (K * δ ^ 2) * (2 / x * τ) := by ring
  rw [hgoal]
  exact le_trans hnum (le_mul_of_one_le_right (mul_nonneg hK0 (sq_nonneg δ)) h1)

/-- The real part of a cluster direction. -/
theorem clusterAlpha_re {x₁ : ℝ} {ρ j : ℕ} :
    (clusterAlpha x₁ ρ j).re = -x₁ * (clusterOmega ρ j).re / Real.sin (Real.pi / ρ) := by
  rw [clusterAlpha, div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm, Complex.re_ofReal_mul,
    neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
  ring

/-- **The coefficient `Forgacs2017RationalDenominator` Prop. 3 arrives at.**
Normalizing the `j`-th cluster direction by the *modulus* of the principal one
replaces `ω_p` by its real part `cos(π/ρ)` and leaves `ω_j` untouched, so the
coefficient of `δ` is `(cos(π/ρ) - ω_j)/sin(π/ρ)`, complex. -/
theorem clusterAlpha_coeff {x₁ : ℝ} (hx : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ) {i jp : ℕ}
    (hp : (clusterOmega ρ jp).re = Real.cos (Real.pi / ρ)) :
    (clusterAlpha x₁ ρ i - (((clusterAlpha x₁ ρ jp).re : ℝ) : ℂ)) / ((x₁ : ℝ) : ℂ)
      = (((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ i)
        / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ) := by
  have hs := sin_pi_div_pos hρ
  have hs0 : ((Real.sin (Real.pi / ρ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hx0 : ((x₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  rw [clusterAlpha_re, hp, clusterAlpha]
  push_cast
  field

/-- **`Forgacs2017RationalDenominator` Prop. 3, Case 2, in the shape the
dominance chain consumes.**  Given `eq:lower-cluster-expansion` pointwise on a
window — the cluster members and the principal branch point each within `Cδ²` of
`x_1 + α_jδ` — the normalized members obey `hexp₀`'s bound with one constant
serving the whole cluster.

The window has to close twice over: `δ ≤ ε ≤ 1` for the linear-in-`δ` estimates,
and `ε ≤ sin(π/ρ)/2` so that `‖α_pδ/x_1‖ ≤ 1/2` and the modulus of the principal
point can be expanded at all.  Both are conditions on `ε`, not on the objects, so
a supplier shrinks its window rather than strengthening its hypotheses.

**Only Cases 2 and 3 of that proposition are in scope**; Case 1 is not claimed,
and the cluster expansion itself is the input, not the output. -/
theorem cluster_normalized_expansion {n₀ : ℕ} {x₁ : ℝ} (hx : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ)
    {idx₀ : Fin n₀ → ℕ} {jp : ℕ} {g₀ : ℝ → Fin n₀ → ℂ} {τ : ℝ → ℝ} {tp : ℝ → ℂ}
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεs : ε ≤ Real.sin (Real.pi / ρ) / 2)
    (hp : (clusterOmega ρ jp).re = Real.cos (Real.pi / ρ))
    (hτeq : ∀ δ : ℝ, 0 < δ → δ ≤ ε → τ δ = ‖tp δ‖)
    (hwin : ∀ δ : ℝ, 0 < δ → δ ≤ ε → x₁ / 2 ≤ τ δ)
    (hgexp : ∀ i : Fin n₀, ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      ‖g₀ δ i - ((x₁ : ℂ) + clusterAlpha x₁ ρ (idx₀ i) * (δ : ℂ))‖ ≤ C * δ ^ 2)
    (hpexp : ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      ‖tp δ - ((x₁ : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ))‖ ≤ C * δ ^ 2) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ i : Fin n₀, ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      ‖g₀ δ i / ((τ δ : ℝ) : ℂ)
        - (1 + ((((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx₀ i))
            / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) * (δ : ℂ))‖ ≤ C₀ * δ ^ 2 := by
  have hs := sin_pi_div_pos hρ
  set s : ℝ := Real.sin (Real.pi / ρ) with hsdef
  set D : ℝ := C + x₁ / s ^ 2 with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set C₀ : ℝ := 2 / x₁ * (C + D * (1 + 2 / s) + x₁ / s * (2 / s)) with hC₀
  refine ⟨C₀, by rw [hC₀]; positivity, fun i δ hδ hδε => ?_⟩
  have hδ1 : δ ≤ 1 := le_trans hδε hε1
  have hB := hpexp δ hδ hδε
  set B : ℂ := clusterAlpha x₁ ρ jp with hBdef
  set A : ℂ := clusterAlpha x₁ ρ (idx₀ i) with hAdef
  have hnB : ‖B‖ = x₁ / s := by rw [hBdef]; exact norm_clusterAlpha hx hρ jp
  -- the principal point's modulus, expanded
  have hsmall : ‖B / (x₁ : ℂ) * (δ : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hδ, hnB]
    have hsimp : x₁ / s / x₁ * δ = δ / s := by field_simp
    rw [hsimp, div_le_div_iff₀ hs (by norm_num : (0:ℝ) < 2)]
    linarith [hδε, hεs]
  have hmod : |‖(x₁ : ℂ) + B * (δ : ℂ)‖ - (x₁ + B.re * δ)| ≤ (x₁ / s ^ 2) * δ ^ 2 := by
    have hfac : (x₁ : ℂ) + B * (δ : ℂ) = ((x₁ : ℝ) : ℂ) * (1 + B / (x₁ : ℂ) * (δ : ℂ)) := by
      have : ((x₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
      field_simp
    have hre : (B / (x₁ : ℂ) * (δ : ℂ)).re = B.re * δ / x₁ := by
      rw [show B / (x₁ : ℂ) * (δ : ℂ) = (((1 / x₁ * δ : ℝ)) : ℂ) * B by
        push_cast; field_simp, Complex.re_ofReal_mul]
      field_simp
    have h1 := abs_norm_one_add_sub_le hsmall
    rw [hre] at h1
    have hnorm : ‖B / (x₁ : ℂ) * (δ : ℂ)‖ = δ / s := by
      rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hδ, hnB]
      field_simp
    rw [hnorm] at h1
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
      show x₁ * ‖1 + B / (x₁ : ℂ) * (δ : ℂ)‖ - (x₁ + B.re * δ)
        = x₁ * (‖1 + B / (x₁ : ℂ) * (δ : ℂ)‖ - (1 + B.re * δ / x₁)) by field_simp,
      abs_mul, abs_of_pos hx]
    calc x₁ * |‖1 + B / (x₁ : ℂ) * (δ : ℂ)‖ - (1 + B.re * δ / x₁)|
        ≤ x₁ * (δ / s) ^ 2 := by
          nlinarith [abs_nonneg (‖1 + B / (x₁ : ℂ) * (δ : ℂ)‖ - (1 + B.re * δ / x₁))]
      _ = x₁ / s ^ 2 * δ ^ 2 := by field_simp
  have hτD : |τ δ - (x₁ + B.re * δ)| ≤ D * δ ^ 2 := by
    rw [hτeq δ hδ hδε]
    have h2 : |‖tp δ‖ - ‖(x₁ : ℂ) + B * (δ : ℂ)‖| ≤ C * δ ^ 2 :=
      le_trans (abs_norm_sub_norm_le _ _) hB
    have := abs_sub_abs_le_abs_sub (‖tp δ‖ - (x₁ + B.re * δ)) 0
    calc |‖tp δ‖ - (x₁ + B.re * δ)|
        ≤ |‖tp δ‖ - ‖(x₁ : ℂ) + B * (δ : ℂ)‖| + |‖(x₁ : ℂ) + B * (δ : ℂ)‖ - (x₁ + B.re * δ)| := by
          have := abs_add_le (‖tp δ‖ - ‖(x₁ : ℂ) + B * (δ : ℂ)‖)
            (‖(x₁ : ℂ) + B * (δ : ℂ)‖ - (x₁ + B.re * δ))
          simpa using this
      _ ≤ C * δ ^ 2 + (x₁ / s ^ 2) * δ ^ 2 := add_le_add h2 hmod
      _ = D * δ ^ 2 := by rw [hD]; ring
  -- the normalization
  have hmain := norm_div_sub_one_add_mul_le (x := x₁) (τ := τ δ) (C := C) (D := D)
    (A := A) (B := B) (g := g₀ δ i) hx hδ hδ1 (hwin δ hδ hδε) (hgexp i δ hδ hδε) hτD
  rw [clusterAlpha_coeff hx hρ hp] at hmain
  refine le_trans hmain ?_
  -- one constant for the whole cluster
  set E : ℂ := (((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx₀ i))
    / ((s : ℝ) : ℂ) with hEdef
  have hEnorm : ‖E‖ ≤ 2 / s := by
    rw [hEdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    refine div_le_div_of_nonneg_right ?_ hs.le
    refine le_trans (norm_sub_le _ _) ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_clusterOmega]
    linarith [Real.abs_cos_le_one (Real.pi / ρ)]
  have hBre : |B.re| ≤ x₁ / s := le_trans (Complex.abs_re_le_norm B) (le_of_eq hnB)
  have hEn0 : 0 ≤ ‖E‖ := norm_nonneg E
  have hs0 : (0 : ℝ) ≤ x₁ / s := by positivity
  have hstep : C + D * (1 + ‖E‖) + |B.re| * ‖E‖
      ≤ C + D * (1 + 2 / s) + x₁ / s * (2 / s) := by
    have hb1 : D * (1 + ‖E‖) ≤ D * (1 + 2 / s) := by nlinarith [hD0, hEnorm]
    have hb2 : |B.re| * ‖E‖ ≤ x₁ / s * (2 / s) :=
      mul_le_mul hBre hEnorm hEn0 hs0
    linarith
  rw [hC₀]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ 2 / x₁)) (sq_nonneg δ)

/-! ### The `ρ`-th-root localization

`Forgacs2017RationalDenominator` Prop. 3 Case 2 reads the cluster directions off
`(t - x_1)^ρ ∝ -z`, and the step that turns that proportionality into an
expansion is: a number whose `ρ`-th power is within `e` of `1` is within `5e` of
a `ρ`-th root of unity — *linearly* in `e`, not at rate `e^{1/ρ}`.

**Differs from the paper's route.**  The paper reads the directions off the
displayed asymptotics.  Here the root of unity is *constructed* from the polar
decomposition, `μ = e^{i(arg u - arg(u^ρ)/ρ)}`, whose `ρ`-th power is `1`
because `e^{iρarg u} = u^ρ/|u^ρ|`; the estimate is then two elementary
inequalities, and no branch of a `ρ`-th root is chosen and no asymptotic taken.
The `e^{1/ρ}` that a product-of-factors argument gives is avoided entirely. -/

private theorem cnorm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simp only [Complex.norm_def, Complex.normSq_apply]
  rw [Real.sq_sqrt (by nlinarith [sq_nonneg z.re, sq_nonneg z.im])]
  ring

private theorem norm_one_sub_exp_sq (θ : ℝ) :
    ‖(1 : ℂ) - Complex.exp ((θ : ℝ) * Complex.I)‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [cnorm_sq, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Dividing an angle by `ρ ≥ 1` moves it toward `0`, so the chord to `1`
shortens.  `|θ| ≤ π` is what makes `cos` monotone across the comparison. -/
private theorem norm_one_sub_exp_div_le {θ : ℝ} (hθ : |θ| ≤ Real.pi) {ρ : ℕ} (hρ : 1 ≤ ρ) :
    ‖(1 : ℂ) - Complex.exp ((-(θ / ρ) : ℝ) * Complex.I)‖
      ≤ ‖(1 : ℂ) - Complex.exp ((θ : ℝ) * Complex.I)‖ := by
  have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast (by omega : 0 < ρ)
  have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have habs : |(-(θ / ρ) : ℝ)| ≤ |θ| := by
    rw [abs_neg, abs_div, abs_of_pos hρ0]
    rw [div_le_iff₀ hρ0]
    nlinarith [abs_nonneg θ]
  have hcos : Real.cos θ ≤ Real.cos (-(θ / ρ)) := by
    rw [← Real.cos_abs θ, ← Real.cos_abs (-(θ / ρ))]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hθ habs
  have h1 := norm_one_sub_exp_sq (-(θ / ρ))
  have h2 := norm_one_sub_exp_sq θ
  nlinarith [norm_nonneg ((1 : ℂ) - Complex.exp ((-(θ / ρ) : ℝ) * Complex.I)),
    norm_nonneg ((1 : ℂ) - Complex.exp ((θ : ℝ) * Complex.I))]

/-- **The localization.**  If `u^ρ` is within `e ≤ 1/2` of `1`, then `u` is within
`5e` of an exact `ρ`-th root of unity.  This is the step
`Forgacs2017RationalDenominator` Prop. 3 Case 2 needs to pass from
`(t_j - x_1)^ρ / (t_p - x_1)^ρ = 1 + O(θ)` to
`t_j - x_1 = ω_j/ω_p · (t_p - x_1) + O(θ^2)`. -/
theorem exists_root_of_unity_close {ρ : ℕ} (hρ : 1 ≤ ρ) {u : ℂ} {e : ℝ}
    (he2 : e ≤ 1 / 2) (h : ‖u ^ ρ - 1‖ ≤ e) :
    ∃ μ : ℂ, μ ^ ρ = 1 ∧ ‖u - μ‖ ≤ 5 * e := by
  have he0 : 0 ≤ e := le_trans (norm_nonneg _) h
  have hrev : ‖(1 : ℂ) - u ^ ρ‖ ≤ e := by rwa [norm_sub_rev]
  have hlo : ‖(1 : ℂ)‖ - ‖u ^ ρ‖ ≤ e := le_trans (norm_sub_norm_le 1 (u ^ ρ)) hrev
  have hhi : ‖u ^ ρ‖ - ‖(1 : ℂ)‖ ≤ e := le_trans (norm_sub_norm_le (u ^ ρ) 1) h
  simp only [norm_one] at hlo hhi
  have hwn2 : (1 : ℝ) / 2 ≤ ‖u ^ ρ‖ := by linarith
  have hwne : ((‖u ^ ρ‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by intro hz; rw [hz] at hwn2; linarith)
  set β : ℝ := ‖u‖ with hβ
  set ψ : ℝ := Complex.arg u with hψ
  set φ : ℝ := Complex.arg (u ^ ρ) with hφ
  have hupolar : ((β : ℝ) : ℂ) * Complex.exp ((ψ : ℝ) * Complex.I) = u :=
    Complex.norm_mul_exp_arg_mul_I u
  have hwpolar : ((‖u ^ ρ‖ : ℝ) : ℂ) * Complex.exp ((φ : ℝ) * Complex.I) = u ^ ρ :=
    Complex.norm_mul_exp_arg_mul_I (u ^ ρ)
  have hβρ : β ^ ρ = ‖u ^ ρ‖ := by rw [hβ, norm_pow]
  have hβ0 : 0 ≤ β := norm_nonneg u
  -- the modulus is within `e` of `1`
  have hβ1 : |β - 1| ≤ e := by
    have hb : -e ≤ β ^ ρ - 1 ∧ β ^ ρ - 1 ≤ e := by
      rw [hβρ]; exact ⟨by linarith, by linarith⟩
    rw [abs_le]
    rcases le_or_gt 1 β with hb1 | hb1
    · have hs : β ≤ β ^ ρ := le_self_pow₀ hb1 (by omega)
      exact ⟨by linarith, by linarith [hb.2]⟩
    · have hs : β ^ ρ ≤ β := pow_le_of_le_one hβ0 hb1.le (by omega)
      exact ⟨by linarith [hb.1], by linarith⟩
  -- `e^{iρψ} = e^{iφ}`, which is what makes the constructed number an exact root
  have hexpψ : Complex.exp ((ψ : ℝ) * Complex.I) ^ ρ
      = Complex.exp ((φ : ℝ) * Complex.I) := by
    refine mul_left_cancel₀ hwne ?_
    have h1 : ((‖u ^ ρ‖ : ℝ) : ℂ) * Complex.exp ((ψ : ℝ) * Complex.I) ^ ρ = u ^ ρ := by
      rw [← hβρ]
      push_cast
      rw [← mul_pow, hupolar]
    rw [h1, hwpolar]
  refine ⟨Complex.exp (((ψ - φ / ρ : ℝ) : ℝ) * Complex.I), ?_, ?_⟩
  · rw [← Complex.exp_nat_mul]
    have hρc : (ρ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcast : (ρ : ℂ) * ((((ψ - φ / ρ : ℝ) : ℝ) : ℂ) * Complex.I)
        = (ρ : ℂ) * (((ψ : ℝ) : ℂ) * Complex.I) - ((φ : ℝ) : ℂ) * Complex.I := by
      push_cast
      field_simp
    rw [hcast, Complex.exp_sub, Complex.exp_nat_mul, hexpψ,
      div_self (Complex.exp_ne_zero _)]
  · have hfac : u - Complex.exp (((ψ - φ / ρ : ℝ) : ℝ) * Complex.I)
        = Complex.exp ((ψ : ℝ) * Complex.I)
          * (((β : ℝ) : ℂ) - Complex.exp ((-(φ / ρ) : ℝ) * Complex.I)) := by
      rw [← hupolar]
      have hsplit : (((ψ - φ / ρ : ℝ) : ℝ) : ℂ) * Complex.I
          = ((ψ : ℝ) : ℂ) * Complex.I + ((-(φ / ρ) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hsplit, Complex.exp_add]
      ring
    have hexp1 : ‖Complex.exp ((ψ : ℝ) * Complex.I)‖ = 1 := by
      simp
    have hchord : ‖(1 : ℂ) - Complex.exp ((φ : ℝ) * Complex.I)‖ ≤ 4 * e := by
      have hrepr : Complex.exp ((φ : ℝ) * Complex.I) = u ^ ρ / ((‖u ^ ρ‖ : ℝ) : ℂ) :=
        (eq_div_iff hwne).2 (by rw [mul_comm]; exact hwpolar)
      rw [hrepr]
      have hstep : (1 : ℂ) - u ^ ρ / ((‖u ^ ρ‖ : ℝ) : ℂ)
          = (((‖u ^ ρ‖ : ℝ) : ℂ) - u ^ ρ) / ((‖u ^ ρ‖ : ℝ) : ℂ) := by field_simp
      rw [hstep, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg (u ^ ρ)), div_le_iff₀ (by linarith : (0:ℝ) < ‖u ^ ρ‖)]
      have hnum : ‖((‖u ^ ρ‖ : ℝ) : ℂ) - u ^ ρ‖ ≤ 2 * e := by
        have hA : ‖((‖u ^ ρ‖ : ℝ) : ℂ) - 1‖ ≤ e := by
          rw [show ((‖u ^ ρ‖ : ℝ) : ℂ) - 1 = ((‖u ^ ρ‖ - 1 : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_le]
          exact ⟨by linarith, by linarith⟩
        have hsum : ((‖u ^ ρ‖ : ℝ) : ℂ) - u ^ ρ
            = (((‖u ^ ρ‖ : ℝ) : ℂ) - 1) + ((1 : ℂ) - u ^ ρ) := by ring
        rw [hsum]
        exact le_trans (norm_add_le _ _) (by linarith)
      nlinarith [hnum, hwn2, he0]
    have hdiv := norm_one_sub_exp_div_le (θ := φ) (Complex.abs_arg_le_pi (u ^ ρ)) hρ
    rw [hfac, norm_mul, hexp1, one_mul]
    have hsum2 : ((β : ℝ) : ℂ) - Complex.exp ((-(φ / ρ) : ℝ) * Complex.I)
        = (((β : ℝ) : ℂ) - 1) + ((1 : ℂ) - Complex.exp ((-(φ / ρ) : ℝ) * Complex.I)) := by
      ring
    have hb : ‖((β : ℝ) : ℂ) - 1‖ ≤ e := by
      rw [show ((β : ℝ) : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact hβ1
    rw [hsum2]
    refine le_trans (norm_add_le _ _) ?_
    linarith [le_trans hdiv hchord]

/-- **The cluster members differ from the principal one by a `ρ`-th root of
unity, up to a controlled error.**  `cluster_two_root_eq` eliminates `z`, so the
ratio `((t - x_1)/(t_p - x_1))^ρ` is a ratio of values of `q` and of `r`-th
powers; when that ratio is within `e` of `1`, `exists_root_of_unity_close` turns
it into an exact root of unity with error `5e` — and multiplying back by
`‖t_p - x_1‖` gives the displacement.

This is `Forgacs2017RationalDenominator` Prop. 3 Case 2's "the `ρ` branches are
separated by the `ρ`-th roots of `-1`", with the separation proved rather than
read off an asymptotic. -/
theorem exists_cluster_ratio_close {Q q : ℂ[X]} {x₁ : ℂ} {ρ r : ℕ} (hρ : 1 ≤ ρ)
    (hQ : Q = (X - C x₁) ^ ρ * q) {z t tp : ℂ}
    (ht : (ftDen Q r z).eval t = 0) (htp : (ftDen Q r z).eval tp = 0)
    (hne : tp ≠ x₁) (hq : q.eval t ≠ 0) (htp0 : tp ≠ 0) {e : ℝ} (he2 : e ≤ 1 / 2)
    (hclose : ‖q.eval tp * t ^ r / (q.eval t * tp ^ r) - 1‖ ≤ e) :
    ∃ μ : ℂ, μ ^ ρ = 1 ∧ ‖t - x₁ - μ * (tp - x₁)‖ ≤ 5 * e * ‖tp - x₁‖ := by
  have hd : tp - x₁ ≠ 0 := sub_ne_zero.2 hne
  have hden : q.eval t * tp ^ r ≠ 0 := mul_ne_zero hq (pow_ne_zero r htp0)
  have hkey := cluster_two_root_eq hQ ht htp
  have hu : ((t - x₁) / (tp - x₁)) ^ ρ = q.eval tp * t ^ r / (q.eval t * tp ^ r) := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero ρ hd) hden]
    linear_combination hkey
  obtain ⟨μ, hμ, hbound⟩ :=
    exists_root_of_unity_close (ρ := ρ) hρ (u := (t - x₁) / (tp - x₁)) he2
      (by rw [hu]; exact hclose)
  refine ⟨μ, hμ, ?_⟩
  have hfac : t - x₁ - μ * (tp - x₁) = ((t - x₁) / (tp - x₁) - μ) * (tp - x₁) := by
    field_simp
  rw [hfac, norm_mul]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

/-- **The ratio `exists_cluster_ratio_close` consumes, decomposed exactly.**  The
`z`-free ratio differs from `1` by two ordinary continuity increments — of `w^r`
and of `q` between the two roots — over the denominator, with no constant
invented and nothing estimated.  Supplying `hclose` is therefore two elementary
moduli bounds, not an asymptotic. -/
theorem norm_cluster_ratio_sub_one_le {q : ℂ[X]} {t tp : ℂ} {r : ℕ}
    (hq : q.eval t ≠ 0) (htp0 : tp ≠ 0) :
    ‖q.eval tp * t ^ r / (q.eval t * tp ^ r) - 1‖
      ≤ (‖q.eval tp‖ * ‖t ^ r - tp ^ r‖ + ‖q.eval tp - q.eval t‖ * ‖tp‖ ^ r)
        / (‖q.eval t‖ * ‖tp‖ ^ r) := by
  have hden : q.eval t * tp ^ r ≠ 0 := mul_ne_zero hq (pow_ne_zero r htp0)
  have hdn : ‖q.eval t * tp ^ r‖ = ‖q.eval t‖ * ‖tp‖ ^ r := by
    rw [norm_mul, norm_pow]
  have hdpos : 0 < ‖q.eval t‖ * ‖tp‖ ^ r := by
    rw [← hdn]; exact norm_pos_iff.2 hden
  have hsplit : q.eval tp * t ^ r / (q.eval t * tp ^ r) - 1
      = (q.eval tp * (t ^ r - tp ^ r) + (q.eval tp - q.eval t) * tp ^ r)
        / (q.eval t * tp ^ r) := by
    field
  rw [hsplit, norm_div, hdn, div_le_div_iff_of_pos_right hdpos]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mul, norm_pow]

/-- **The principal branch's expansion is the `τ`-rate and nothing else.**  The
principal point is `τ(δ)e^{iδ}` exactly, so `eq:lower-cluster-expansion` at the
principal index is equivalent to the *real scalar* statement that
`τ(δ) = x_1 - x_1cos(π/ρ)δ/sin(π/ρ) + O(δ²)`: the rotation contributes the
imaginary part `ix_1δ`, and the two together are `-x_1ω_+δ/sin(π/ρ)` with
`ω_+ = e^{-iπ/ρ}`.

The point is written out as `↑(τ δ) * exp(↑δ * I)` rather than as
`DominanceFT.ftPrincipal τ δ`, which is the same term — that module sits above
this one, so naming it here would invert the import.

The decomposition is exact: the three error terms are the `τ`-rate remainder
carried by the unit rotation, the second-order remainder of `exp`, and the single
cross term `-ix_1cos(π/ρ)δ²/sin(π/ρ)`.  Nothing is estimated twice. -/
theorem principal_expansion_of_tau_rate {x₁ : ℝ} (hx : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ)
    {τ : ℝ → ℝ} {jp : ℕ}
    (hp : clusterOmega ρ jp = Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * Complex.I))
    {C ε : ℝ} (hC : 0 ≤ C) (hε1 : ε ≤ 1)
    (hτ : ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      |τ δ - (x₁ - x₁ * Real.cos (Real.pi / ρ) / Real.sin (Real.pi / ρ) * δ)| ≤ C * δ ^ 2) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      ‖((τ δ : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I)
        - ((x₁ : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ))‖ ≤ C' * δ ^ 2 := by
  have hs := sin_pi_div_pos hρ
  set s : ℝ := Real.sin (Real.pi / ρ) with hsdef
  set c : ℝ := Real.cos (Real.pi / ρ) with hcdef
  set k : ℝ := x₁ * c / s with hk
  have hs0 : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  -- the principal direction, in rectangular form, and the coefficient it gives
  have hω : clusterOmega ρ jp = ((c : ℝ) : ℂ) - ((s : ℝ) : ℂ) * Complex.I := by
    rw [hp]
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re, Complex.sub_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      simp [hcdef, Real.cos_neg]
    · rw [Complex.exp_ofReal_mul_I_im, Complex.sub_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      simp [hsdef, Real.sin_neg]
  have hα : clusterAlpha x₁ ρ jp = -((k : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I := by
    rw [clusterAlpha, hω, div_eq_iff hs0, hk]
    push_cast
    field
  refine ⟨C + (x₁ + |k|) + |k|, by positivity, fun δ hδ hδε => ?_⟩
  have hδ1 : δ ≤ 1 := le_trans hδε hε1
  set L : ℝ := x₁ - k * δ with hL
  have hid : ((τ δ : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I)
      - ((x₁ : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ))
      = ((τ δ - L : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I)
        + ((L : ℝ) : ℂ) * (Complex.exp ((δ : ℂ) * Complex.I) - 1 - (δ : ℂ) * Complex.I)
        - ((k : ℝ) : ℂ) * Complex.I * (δ : ℂ) ^ 2 := by
    rw [hα, hL]
    push_cast
    ring
  have hexp1 : ‖Complex.exp ((δ : ℂ) * Complex.I)‖ = 1 := by
    simp
  have hτL : |τ δ - L| ≤ C * δ ^ 2 := by
    rw [hL]
    exact hτ δ hδ hδε
  have hT1 : ‖((τ δ - L : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I)‖ ≤ C * δ ^ 2 := by
    rw [norm_mul, hexp1, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hτL
  have hsmall : ‖(δ : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ]
    exact hδ1
  have hE : ‖Complex.exp ((δ : ℂ) * Complex.I) - 1 - (δ : ℂ) * Complex.I‖ ≤ δ ^ 2 := by
    refine le_trans (Complex.norm_exp_sub_one_sub_id_le hsmall) (le_of_eq ?_)
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ]
  have hLb : |L| ≤ x₁ + |k| := by
    have h0 : L = x₁ + -(k * δ) := by rw [hL]; ring
    rw [h0]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_of_pos hx, abs_neg, abs_mul, abs_of_pos hδ]
    nlinarith [abs_nonneg k, hδ1, hδ.le]
  have hT2 : ‖((L : ℝ) : ℂ) * (Complex.exp ((δ : ℂ) * Complex.I) - 1 - (δ : ℂ) * Complex.I)‖
      ≤ (x₁ + |k|) * δ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hLb hE (norm_nonneg _) (by positivity)
  have hT3 : ‖((k : ℝ) : ℂ) * Complex.I * (δ : ℂ) ^ 2‖ = |k| * δ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  rw [hid]
  calc ‖((τ δ - L : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I)
        + ((L : ℝ) : ℂ) * (Complex.exp ((δ : ℂ) * Complex.I) - 1 - (δ : ℂ) * Complex.I)
        - ((k : ℝ) : ℂ) * Complex.I * (δ : ℂ) ^ 2‖
      ≤ ‖((τ δ - L : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I)
          + ((L : ℝ) : ℂ) * (Complex.exp ((δ : ℂ) * Complex.I) - 1 - (δ : ℂ) * Complex.I)‖
        + ‖((k : ℝ) : ℂ) * Complex.I * (δ : ℂ) ^ 2‖ := norm_sub_le _ _
    _ ≤ (C * δ ^ 2 + (x₁ + |k|) * δ ^ 2) + |k| * δ ^ 2 := by
        rw [hT3]
        exact add_le_add (le_trans (norm_add_le _ _) (add_le_add hT1 hT2)) (le_refl _)
    _ = (C + (x₁ + |k|) + |k|) * δ ^ 2 := by ring

/-- A root of unity has modulus one. -/
theorem norm_eq_one_of_pow_eq_one {ρ : ℕ} (hρ : 1 ≤ ρ) {μ : ℂ} (hμ : μ ^ ρ = 1) :
    ‖μ‖ = 1 := by
  have h : ‖μ‖ ^ ρ = 1 := by rw [← norm_pow, hμ, norm_one]
  have h0 : 0 ≤ ‖μ‖ := norm_nonneg μ
  rcases lt_trichotomy ‖μ‖ 1 with hlt | heq | hgt
  · exact absurd h (by nlinarith [pow_lt_one₀ h0 hlt (by omega : ρ ≠ 0)])
  · exact heq
  · exact absurd h (by nlinarith [one_lt_pow₀ hgt (by omega : ρ ≠ 0)])

/-- **Every cluster member's expansion, from the principal one.**  Once
`exists_cluster_ratio_close` has produced the exact root of unity `μ` relating a
member to the principal branch, the member's own expansion is the principal one
rotated by `μ`: the displacement splits as
`(t - x_1 - μ(t_p - x_1)) + μ(t_p - x_1 - α_+δ)`, whose two terms are the ratio
error and the principal remainder.

`μ·α_+ = -x_1(μω_+)/sin(π/ρ)` and `(μω_+)^ρ = μ^ρω_+^ρ = -1`, so the rotated
coefficient is again `-x_1ω/sin(π/ρ)` at a `ρ`-th root of `-1` — which is what
makes it `clusterAlpha` at another index. -/
theorem cluster_member_expansion {x₁ : ℝ} (hx : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ) {jp : ℕ}
    {μ t tp : ℂ} {δ e K Cp : ℝ} (hρ1 : 1 ≤ ρ) (hμ : μ ^ ρ = 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K) (hCp : 0 ≤ Cp) (he : e ≤ K * δ)
    (hratio : ‖t - (x₁ : ℂ) - μ * (tp - (x₁ : ℂ))‖ ≤ 5 * e * ‖tp - (x₁ : ℂ)‖)
    (hp : ‖tp - ((x₁ : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ))‖ ≤ Cp * δ ^ 2) :
    ‖t - ((x₁ : ℂ) + μ * clusterAlpha x₁ ρ jp * (δ : ℂ))‖
      ≤ (5 * K * (x₁ / Real.sin (Real.pi / ρ) + Cp) + Cp) * δ ^ 2 := by
  have hs := sin_pi_div_pos hρ
  have hμ1 : ‖μ‖ = 1 := norm_eq_one_of_pow_eq_one hρ1 hμ
  have hnα : ‖clusterAlpha x₁ ρ jp‖ = x₁ / Real.sin (Real.pi / ρ) :=
    norm_clusterAlpha hx hρ jp
  -- the principal displacement is `O(δ)`
  have htpd : ‖tp - (x₁ : ℂ)‖ ≤ (x₁ / Real.sin (Real.pi / ρ) + Cp) * δ := by
    have hsplit : tp - (x₁ : ℂ)
        = (tp - ((x₁ : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ)))
          + clusterAlpha x₁ ρ jp * (δ : ℂ) := by ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, hnα, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    nlinarith [hp, mul_nonneg (mul_nonneg hCp hδ.le) (sub_nonneg.2 hδ1)]
  -- the two error terms
  have hsplit2 : t - ((x₁ : ℂ) + μ * clusterAlpha x₁ ρ jp * (δ : ℂ))
      = (t - (x₁ : ℂ) - μ * (tp - (x₁ : ℂ)))
        + μ * (tp - ((x₁ : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ))) := by ring
  rw [hsplit2]
  refine le_trans (norm_add_le _ _) ?_
  have h2 : ‖μ * (tp - ((x₁ : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ)))‖ ≤ Cp * δ ^ 2 := by
    rw [norm_mul, hμ1, one_mul]; exact hp
  have h1 : ‖t - (x₁ : ℂ) - μ * (tp - (x₁ : ℂ))‖
      ≤ 5 * K * (x₁ / Real.sin (Real.pi / ρ) + Cp) * δ ^ 2 := by
    refine le_trans hratio ?_
    have hb : (0 : ℝ) ≤ x₁ / Real.sin (Real.pi / ρ) + Cp := by positivity
    have hstep : e * ‖tp - (x₁ : ℂ)‖
        ≤ (K * δ) * ((x₁ / Real.sin (Real.pi / ρ) + Cp) * δ) :=
      mul_le_mul he htpd (norm_nonneg _) (mul_nonneg hK hδ.le)
    nlinarith [hstep]
  linarith [h1, h2]

/-- **The `τ`-rate from a first-derivative bound.**  `principal_expansion_of_tau_rate`
reduces Case 2 at the principal index to a second-order statement about `τ`
alone; this reduces *that* to a first-order one, which is what the branch's
explicit `ftTauDeriv` can be measured against: if the derivative is within `Kδ`
of the constant `m` on the window, and `τ` converges to `x_1` at the endpoint,
then `τ` is within `Kδ²` of `x_1 + mδ`.

**Differs from the paper's route.**  `subsec:FT-geometry` states the endpoint
behavior as an asymptotic.  Here the second-order bound is obtained from the
first-order one by the mean value theorem on `[a,δ]` with the constant `Kδ`, and
the left endpoint is then sent to `0` against the limit of `τ` — so the
conclusion is pointwise on the window with an explicit constant, which an
asymptotic does not give and which `Dominance.exp_le_pow_of_one_add_le` needs.

**Superseded for Case 2, retained as a general converter.**  The branch supplies
the second-order rate directly, through the exact identity
`x_1/τ(θ) = cosθ - sinθcotβ(θ)`, which turns a
first-order bound on the *angle* into a second-order bound on `τ` with
`ftTauDeriv` never entering — so `exists_principal_expansion_of_branch` calls
`FTBranchLimitPoint.exists_bound_ftTau_sub_linear` and not this.  Nothing here is
wrong or weaker; the mean-value route it was built for is simply not the one
taken.  It mentions no `ftTau`, so it converts *any* first-order derivative bound
into a second-order rate, and the upper endpoint's expansion is the same species
of problem.  A zero consumer count here records which route won, not whether the
lemma is needed. -/
theorem abs_sub_linear_le_of_deriv_bound {τ τ' : ℝ → ℝ} {x₁ m K ε : ℝ} (hK : 0 ≤ K)
    (hd : ∀ δ ∈ Set.Ioo (0 : ℝ) ε, HasDerivAt τ (τ' δ) δ)
    (hb : ∀ δ ∈ Set.Ioo (0 : ℝ) ε, |τ' δ - m| ≤ K * δ)
    (h0 : Filter.Tendsto τ (nhdsWithin 0 (Set.Ioi 0)) (nhds x₁)) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) ε, |τ δ - (x₁ + m * δ)| ≤ K * δ ^ 2 := by
  intro δ hδ
  set g : ℝ → ℝ := fun x => τ x - (x₁ + m * x) with hg
  -- the mean value bound on `[a, δ]`, uniformly in `a`
  have hmvt : ∀ a ∈ Set.Ioo (0 : ℝ) δ, |g δ - g a| ≤ K * δ ^ 2 := by
    intro a ha
    have hsub : Set.Icc a δ ⊆ Set.Ioo (0 : ℝ) ε := by
      intro x hx
      exact ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hδ.2⟩
    have hderiv : ∀ x ∈ Set.Icc a δ, HasDerivWithinAt g (τ' x - m) (Set.Icc a δ) x := by
      intro x hx
      have hlin : HasDerivAt (fun y : ℝ => x₁ + m * y) m x := by
        simpa using ((hasDerivAt_id x).const_mul m).const_add x₁
      have h1 : HasDerivAt (fun y : ℝ => τ y - (x₁ + m * y)) (τ' x - m) x :=
        HasDerivAt.sub (hd x (hsub hx)) hlin
      exact h1.hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Icc a δ, ‖τ' x - m‖ ≤ K * δ := by
      intro x hx
      have hxm := hsub hx
      have h1 : |τ' x - m| ≤ K * x := hb x hxm
      have h2 : K * x ≤ K * δ := mul_le_mul_of_nonneg_left hx.2 hK
      simpa [Real.norm_eq_abs] using le_trans h1 h2
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc a δ) (Set.left_mem_Icc.2 ha.2.le) (Set.right_mem_Icc.2 ha.2.le)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith [ha.2] : (0:ℝ) ≤ δ - a)]
      at this
    nlinarith [this, mul_nonneg (mul_nonneg hK hδ.1.le) ha.1.le]
  -- send the left endpoint to `0`
  have hlim : Filter.Tendsto (fun a : ℝ => K * δ ^ 2 + |g a|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (K * δ ^ 2)) := by
    have hgt : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Filter.Tendsto (fun a : ℝ => τ a - (x₁ + m * a))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (x₁ - (x₁ + m * 0))) := by
        refine h0.sub ?_
        exact ((continuous_const.add (continuous_const.mul continuous_id)).tendsto
          0).mono_left nhdsWithin_le_nhds
      simpa [hg] using this
    simpa using (tendsto_const_nhds.add (hgt.abs))
  refine ge_of_tendsto hlim ?_
  have hmem : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0), a ∈ Set.Ioo (0 : ℝ) δ := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        ((continuousAt_id (x := (0 : ℝ))).eventually_lt_const hδ.1)] with a h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hmem] with a ha
  have := hmvt a ha
  have h2 : |g δ| ≤ |g δ - g a| + |g a| := by
    have hab := abs_add_le (g δ - g a) (g a)
    rwa [sub_add_cancel] at hab
  simp only [hg] at h2 ⊢
  linarith [this, h2]

/-- **The cluster directions exhaust the `ρ`-th roots of `-1`.**  Every `ω` with
`ω^ρ = -1` is `clusterOmega ρ j` at some index, so the rotated coefficient
`cluster_member_expansion` produces can always be named — which is what lets a
supplier define `idx₀`.  `Cluster.clusterOmega_injOn` is the other half. -/
theorem exists_clusterOmega_eq {ρ : ℕ} (hρ : 1 ≤ ρ) {ω : ℂ} (hω : ω ^ ρ = -1) :
    ∃ j : ℕ, clusterOmega ρ j = ω := by
  have hρ0 : ρ ≠ 0 := by omega
  haveI : NeZero ρ := ⟨hρ0⟩
  have hprim := Complex.isPrimitiveRoot_exp ρ hρ0
  have hone : clusterOmega ρ 1 ≠ 0 := clusterOmega_ne_zero ρ 1
  have h1 : (ω / clusterOmega ρ 1) ^ ρ = 1 := by
    rw [div_pow, hω, clusterOmega_pow hρ, div_self (by norm_num : (-1 : ℂ) ≠ 0)]
  obtain ⟨i, _, hieq⟩ := hprim.eq_pow_of_pow_eq_one h1
  refine ⟨i + 1, ?_⟩
  have hω' : ω = clusterOmega ρ 1 * Complex.exp (2 * Real.pi * Complex.I / ρ) ^ i := by
    rw [hieq]
    field_simp
  rw [hω', clusterOmega, clusterOmega, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have hρc : (ρ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hρ0
  simp only [clusterAngle]
  push_cast
  field

/-- **The `r`-th power increment `norm_cluster_ratio_sub_one_le` consumes.**  On a
disk of radius `M` the map `w ↦ w^r` is `rM^{r-1}`-Lipschitz, by the geometric
factorization `x^r - y^r = (∑_i x^iy^{r-1-i})(x-y)` — so the ratio's first
increment is `O(‖t - t_p‖)`, hence `O(δ)` once both roots are within `O(δ)` of
`x_1`.  No asymptotic is taken. -/
theorem norm_pow_sub_pow_le_of_norm_le {t s : ℂ} {M : ℝ} {r : ℕ}
    (ht : ‖t‖ ≤ M) (hs : ‖s‖ ≤ M) :
    ‖t ^ r - s ^ r‖ ≤ r * M ^ (r - 1) * ‖t - s‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg t) ht
  have hfac : (∑ i ∈ Finset.range r, t ^ i * s ^ (r - 1 - i)) * (t - s) = t ^ r - s ^ r :=
    geom_sum₂_mul t s r
  rw [← hfac, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i ∈ Finset.range r, ‖t ^ i * s ^ (r - 1 - i)‖ ≤ M ^ (r - 1) := by
    intro i hi
    have hir : i ≤ r - 1 := by
      have := Finset.mem_range.1 hi
      omega
    rw [norm_mul, norm_pow, norm_pow]
    have h1 : ‖t‖ ^ i ≤ M ^ i := pow_le_pow_left₀ (norm_nonneg t) ht i
    have h2 : ‖s‖ ^ (r - 1 - i) ≤ M ^ (r - 1 - i) :=
      pow_le_pow_left₀ (norm_nonneg s) hs _
    calc ‖t‖ ^ i * ‖s‖ ^ (r - 1 - i) ≤ M ^ i * M ^ (r - 1 - i) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = M ^ (r - 1) := by rw [← pow_add]; congr 1; omega
  calc ∑ i ∈ Finset.range r, ‖t ^ i * s ^ (r - 1 - i)‖
      ≤ ∑ _i ∈ Finset.range r, M ^ (r - 1) := Finset.sum_le_sum hterm
    _ = r * M ^ (r - 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The polynomial increment, the other half of the ratio supply.**  On a disk
of radius `M` a polynomial is Lipschitz with the explicit constant
`∑_k ‖c_k‖·kM^{k-1}`, by summing `norm_pow_sub_pow_le_of_norm_le` over the
coefficients.  With that lemma this completes what
`norm_cluster_ratio_sub_one_le` needs: both increments are `O(‖t - t_p‖)`, hence
`O(δ)` once the two roots are within `O(δ)` of `x_1`.

The constant is not sharp and is not meant to be — it is explicit and finite,
which is what a pointwise bound on a window requires. -/
theorem norm_eval_sub_eval_le_of_norm_le {q : ℂ[X]} {t s : ℂ} {M : ℝ}
    (ht : ‖t‖ ≤ M) (hs : ‖s‖ ≤ M) :
    ‖q.eval t - q.eval s‖
      ≤ (∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖ * ((k : ℝ) * M ^ (k - 1)))
        * ‖t - s‖ := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  have hfac : q.coeff k * t ^ k - q.coeff k * s ^ k = q.coeff k * (t ^ k - s ^ k) := by ring
  rw [hfac, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact norm_pow_sub_pow_le_of_norm_le ht hs

/-- **A polynomial's modulus is pinned within a factor of two on a small disk.**
Where the Lipschitz bound of `norm_eval_sub_eval_le_of_norm_le` over a step of
size `e` is at most half of `‖q(s)‖`, the modulus at `t` lies in
`[‖q(s)‖/2, 3‖q(s)‖/2]`.

Both halves are used: the lower one keeps `q(t)` off zero and bounds the ratio's
denominator, the upper one bounds its numerator.  This is why the ratio bound's
constant is explicit — it comes from `q`'s own increment on the window rather
than from compactness. -/
theorem norm_eval_mem_of_norm_sub_le {q : ℂ[X]} {t s : ℂ} {M e : ℝ}
    (ht : ‖t‖ ≤ M) (hs : ‖s‖ ≤ M) (hts : ‖t - s‖ ≤ e)
    (hLe : (∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖ * ((k : ℝ) * M ^ (k - 1)))
      * e ≤ ‖q.eval s‖ / 2) :
    ‖q.eval s‖ / 2 ≤ ‖q.eval t‖ ∧ ‖q.eval t‖ ≤ 3 * ‖q.eval s‖ / 2 := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg t) ht
  have hL0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (q.natDegree + 1),
      ‖q.coeff k‖ * ((k : ℝ) * M ^ (k - 1)) :=
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hM0 _))
  have hbd : ‖q.eval t - q.eval s‖
      ≤ (∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖ * ((k : ℝ) * M ^ (k - 1))) * e :=
    le_trans (norm_eval_sub_eval_le_of_norm_le ht hs)
      (mul_le_mul_of_nonneg_left hts hL0)
  have h1 : ‖q.eval s‖ - ‖q.eval t‖ ≤ ‖q.eval t - q.eval s‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  have h2 : ‖q.eval t‖ - ‖q.eval s‖ ≤ ‖q.eval t - q.eval s‖ := norm_sub_norm_le _ _
  exact ⟨by linarith, by linarith⟩

end ForgacsTran
