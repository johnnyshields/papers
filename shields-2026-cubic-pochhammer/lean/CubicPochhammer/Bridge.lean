/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Kernel
import CubicPochhammer.BetaOrder

/-!
# The coefficient convolution and its Schur-concavity

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:reduction` «Exact
reduction to a residue kernel» (`eq:C-def`, `eq:C-beta`) and `sec:cubic-proof`
«Proof of the cubic theorem»
(`cor:C-schur`): the coefficient convolution `C_{m,w}(u,v)`, and the analytic
reduction that turns the proven kernel monotonicity (`Kernel.gmw_monotoneOn`,
`thm:kernel`) into Schur-concavity of `C_{m,w}`.

`C_{m,w}(u,v) = ∑_{k=1}^{m-1} w_k (u)_{3k}(v)_{3(m-k)} /
              ((3k-1)!(3(m-k)-1)!)`   (`eq:C-def`)

is the degree-`m` coefficient of a product of two cubic multiple-Pochhammer
series when the weights are `w_k = f_k f_{m-k}` (`cmf`).  As in `cor:C-schur`,
the weights are carried through as an arbitrary symmetric family increasing
toward the center; nothing in the reduction uses their product form.

`cmw_schur_of_kernel` is `cor:C-schur`'s interior: at fixed parameter sum, and
with both parameters positive, smaller imbalance gives the larger value of
`C_{m,w}`.  The corollary's endpoint is the proven `cmw_right_zero` below, so
the closed range `0 ≤ d ≤ s/2` is covered by the two together.  The interior is
proved in the paper's own two steps:

* `aint_eq` is the beta-binomial representation `eq:C-beta`, with the
  normalizations cleared:
  `aint · (u+v)_{3m} = (3m-2)! · B(u,v) · C_{m,w}(u,v)`, where
  `aint = ∫_0^1 G_{m,w}(p) p^{u-1}(1-p)^{v-1} dp`.  Both `(u+v)_{3m}` and
  `(3m-2)!` depend only on the parameter sum, so at fixed `s` comparing
  `C_{m,w}` is comparing `aint / B(u,v)`, which is `𝔼 G_{m,w}(P)` for
  `P ∼ Beta(u,v)`.
* `beta_order` is the likelihood-ratio order `lem:beta-order`, whose two
  hypotheses on the integrand are met by the proven `Kernel.gmw_symm` and
  `Kernel.gmw_monotoneOn`.

Also proven here: the parameter symmetry `C_{m,w}(u,v) = C_{m,w}(v,u)` that the
specialization to the generalized Turánian consumes, and the endpoint identity
`C_{m,w}(s,0) = 0` that carries the imbalance `d = s/2` at the top of
`cor:C-schur`'s closed range, together with its specialization `cmf_right_zero`
to `w_k = f_k f_{m-k}`.

The strict clause of `prop:kernel-exact` runs the same two steps strictly:
`cmw_strictAntiOn_imbalance` is strict decrease in the imbalance on the closed
`[0,s/2]`, from `beta_order_strict` on the interior and `cmw_pos` against
`cmw_right_zero` at the endpoint.  `weight_center_pos` is what turns the paper's
"the weights are not all zero" into the `0 < w_{⌊m/2⌋}` that
`Kernel.gmw_strictMonoOn` consumes.  `cmf_delta_pos_iff` and
`turan_delta_pos_iff` are `cor:strict`: the degree-`m` coefficient of
`eq:delta-C` is positive exactly on `I+I`, with `MemSumset` and
`memSumset_iff_weights` carrying the elementary half — off `I+I` every weight
`eq:w-from-f` vanishes and so does the convolution — and
`memSumset_iff_of_Icc_support`, `memSumset_iff_of_Ici_support` the corollary's
two explicit descriptions of `I+I`.

`kernel_exact_iff` closes `prop:kernel-exact` as an equivalence.  Its converse
half, `gmw_monotoneOn_of_schur`, replaces the paper's concentration of beta laws
by an algebraic limit: `G_{m,w}` is a polynomial, so
`(3m-2)!\,C_{m,w}(sp, s(1-p))/s^{3m} → G_{m,w}(p)` term by term
(`factorial_mul_cmw`, `tendsto_poch_div_pow`), and no probability law is named.

Sorry-free and axiom-free.

## Main definitions

* `cmw` --- the coefficient convolution `C_{m,w}(u,v)` of `eq:C-def`, carried
  with an arbitrary weight family.
* `cmf` --- `cmw` at the weights `w_k = f_k f_{m-k}` of `eq:w-from-f`.
* `aint` --- the kernel against the unnormalized `Beta(u,v)` weight.
* `MemSumset` --- `m ∈ I + I` for the positive support `I` of `f`, written as
  the existence of the decomposition.

## Main statements

* `aint_eq_sum_bmom` --- the beta moments of the kernel: integrating
  `eq:G-weighted` term by term turns `A_{m,w}` into a weighted sum of beta
  functions at shifted parameters.
* `aint_eq` --- the beta-binomial representation `eq:C-beta` with the
  normalizations cleared.
* `cmw_eq_beta_expectation` --- the same identity solved for `C_{m,w}`, as the
  Beta-expectation of the kernel times `(u+v)_{3m}/(3m-2)!`.  This is the form
  the two monotonicity clauses consume.
* `cmw_schur_of_kernel` --- `cor:C-schur`'s interior: at fixed parameter sum and
  both parameters positive, smaller imbalance gives the larger `C_{m,w}`.
* `cmw_schur_of_kernel_closed` --- the same over the paper's closed quadrant,
  the endpoint supplied by `cmw_right_zero`.
* `cmw_strictAnti_imbalance` --- the strict form, once the central weight is positive.
* `kernel_exact_iff` --- Schur-concavity of `C_{m,w}` for all admissible weights
  is equivalent to monotonicity of the kernel, so the reduction loses nothing.
* `cmf_delta_pos_iff`, `turan_delta_pos_iff` --- the degree-`m` Turánian
  coefficient is strictly positive exactly when `m` lies in `I + I`.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:reduction` «Exact reduction to a
  residue kernel» (`eq:C-def`, `eq:C-beta`) and `sec:cubic-proof` «Proof of the
  cubic theorem» (`cor:C-schur`).
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace CubicPochhammer

/-- The degree-`m` coefficient of a product of two series, carried with an
arbitrary weight family (`eq:C-def`, in the form `cor:C-schur` states it):
`C_{m,w}(u,v) = ∑_{k=1}^{m-1} w_k (u)_{3k}(v)_{3(m-k)} /
              ((3k-1)!(3(m-k)-1)!)`. -/
noncomputable def cmw (w : ℕ → ℝ) (m : ℕ) (u v : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (m - 1),
    w r * (poch u (3 * r) * poch v (3 * (m - r)))
      / ((Nat.factorial (3 * r - 1) : ℝ) * (Nat.factorial (3 * (m - r) - 1) : ℝ))

/-- The degree-`m` coefficient of `F_f(u;x) F_f(v;x)`: the weights of
`eq:w-from-f`, `w_k = f_k f_{m-k}`, inserted into `cmw`. -/
noncomputable def cmf (f : ℕ → ℝ) (m : ℕ) (u v : ℝ) : ℝ :=
  cmw (fun k => f k * f (m - k)) m u v

/-- `C_{m,w} ≥ 0` for nonnegative weights and nonnegative parameters. -/
theorem cmw_nonneg (w : ℕ → ℝ) (m : ℕ) (hwnn : ∀ i, 0 ≤ w i) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ cmw w m u v := by
  refine Finset.sum_nonneg fun r _ => div_nonneg ?_ ?_
  · exact mul_nonneg (hwnn r) (mul_nonneg (poch_nonneg hu _) (poch_nonneg hv _))
  · positivity

/-- **The endpoint identity** `C_{m,w}(u,0) = 0`.  Every summand carries the
factor `(0)_{3(m-k)}` with `3(m-k) ≥ 3`, so the whole convolution vanishes.
This is the top of `cor:C-schur`'s closed range `0 ≤ d ≤ s/2`: `Beta(s,0)` is
not a law, so the endpoint is reached by this identity rather than by the
beta-binomial route that covers the interior. -/
theorem cmw_right_zero (w : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) (u : ℝ) :
    cmw w m u 0 = 0 := by
  refine Finset.sum_eq_zero fun r hr => ?_
  obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
  rw [poch_zero_eq_zero (show 1 ≤ 3 * (m - r) by omega)]
  ring

/-- **Parameter symmetry** `C_{m,w}(u,v) = C_{m,w}(v,u)` for symmetric weights,
by the reindexing `k ↔ m-k`.  The proof of `thm:main` consumes this when it
identifies the fixed-sum difference `eq:schur-def` with the generalized
Turánian `eq:Turan-def`, whose two shifts are not ordered. -/
theorem cmw_symm (w : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r)) (u v : ℝ) :
    cmw w m u v = cmw w m v u := by
  unfold cmw
  refine Finset.sum_nbij' (fun r => m - r) (fun r => m - r) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    simp only [Finset.mem_Icc]
    omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    simp only [Finset.mem_Icc]
    omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only
    omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only
    omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only
    have hback : m - (m - a) = a := by omega
    rw [hback, hsym a h1 h2]
    ring

/-- `C_{m,f}(u,0) = 0` at the paper's own weights `w_k = f_k f_{m-k}`.  This is
the form `thm:main`'s proof needs at the endpoint `d₂ = s/2`, where the
subtracted convolution vanishes. -/
theorem cmf_right_zero (f : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) (u : ℝ) :
    cmf f m u 0 = 0 := cmw_right_zero _ hm u

/-! ### The beta-binomial representation `eq:C-beta` -/

/-- The kernel integrated against the unnormalized `Beta(u,v)` weight,
`∫_0^1 G_{m,w}(p)\,p^{u-1}(1-p)^{v-1}\,dp`.  Divided by `B(u,v)` this is
`𝔼 G_{m,w}(P)` for `P ∼ Beta(u,v)`; `aint_eq` supplies the rest of `eq:C-beta`. -/
noncomputable def aint (m : ℕ) (w : ℕ → ℝ) (u v : ℝ) : ℝ :=
  ∫ p in (0:ℝ)..1, gmw m w p * (p ^ (u - 1) * (1 - p) ^ (v - 1))

/-- `G_{m,w}` is a polynomial, hence continuous — the regularity `lem:beta-order`
needs of its integrand. -/
theorem continuous_gmw (m : ℕ) (w : ℕ → ℝ) : Continuous (gmw m w) := by
  unfold gmw; fun_prop

/-- **The beta moments of the kernel.**  Integrating `eq:G-weighted` term by term
against the unnormalized `Beta(u,v)` weight replaces each summand's
`p^{3k}(1-p)^{3(m-k)}` by a beta function at shifted parameters:

  `A_{m,w}(u,v) = ∑_{k=1}^{m-1} w_k \binom{3m-2}{3k-1} B(u+3k, v+3(m-k))`.

The interchange is `intervalIntegral.integral_finsetSum` over a finite sum of
integrable beta kernels; the endpoint `p = 1` is discarded as a null set, which
is why the termwise identity is only needed on the open interval. -/
theorem aint_eq_sum_bmom (m : ℕ) (w : ℕ → ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    aint m w u v = ∑ r ∈ Finset.Icc 1 (m - 1),
      (w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ))
        * bmom (u + ((3 * r : ℕ) : ℝ)) (v + ((3 * (m - r) : ℕ) : ℝ)) :=
  integral_eq_sum_bmom _ _ (fun r => 3 * r) (fun r => 3 * (m - r)) hu hv fun p hp0 hp1 => by
    unfold gmw
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => by
      rw [mul_assoc (w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ)), mul_assoc,
        monomial_mul_betaKer hp0 hp1 (3 * r) (3 * (m - r))]

/-- **The trinomial split of `eq:C-beta`**: for `1 ≤ k ≤ m-1` and any
multiplicity `r ≥ 1`,

  `\binom{rm-2}{rk-1}\,(rk-1)!\,[r(m-k)-1]! = (rm-2)!`,

which is `Nat.choose_mul_factorial_mul_factorial` once `rm-2-(rk-1)` is
recognized as `r(m-k)-1`.  The `-1` and `-2` shifts are what the `j-1 ≡ r-1
(mod r)` residue class of `eq:G-weighted` costs; the identity is what makes the
binomial coefficient of the kernel cancel against the factorials of `eq:C-def`. -/
theorem choose_mul_factorial_residue {r m k : ℕ} (hr : 1 ≤ r) (hm : 2 ≤ m)
    (hk1 : 1 ≤ k) (hk2 : k ≤ m - 1) :
    Nat.choose (r * m - 2) (r * k - 1) * Nat.factorial (r * k - 1)
      * Nat.factorial (r * (m - k) - 1) = Nat.factorial (r * m - 2) := by
  have hsplit : r * k + r * (m - k) = r * m := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' (by omega : k ≤ m)]
  have hrk : 1 ≤ r * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hrmk : 1 ≤ r * (m - k) := Nat.one_le_iff_ne_zero.mpr (by
    have : 0 < m - k := by omega
    positivity)
  have hle : r * k - 1 ≤ r * m - 2 := by omega
  rw [show r * (m - k) - 1 = r * m - 2 - (r * k - 1) from by omega]
  exact Nat.choose_mul_factorial_mul_factorial hle

/-- **`eq:C-beta`**, with the normalizations cleared:
`aint · (u+v)_{3m} = (3m-2)! · B(u,v) · C_{m,w}(u,v)`.

The beta moments `aint_eq_sum_bmom` are reduced term by term to `B(u,v)` by the
Pochhammer shift `bmom_shift`, and the binomial coefficient is completed to
`(3m-2)!` by `choose_mul_factorial_cubic`. -/
theorem aint_eq (m : ℕ) (hm : 2 ≤ m) (w : ℕ → ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    aint m w u v * poch (u + v) (3 * m)
      = (Nat.factorial (3 * m - 2) : ℝ) * bmom u v * cmw w m u v := by
  rw [aint_eq_sum_bmom m w hu hv]
  exact sum_bmom_mul_poch _ w (fun r => (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ))
    (fun r => 3 * r) (fun r => 3 * (m - r)) _ (3 * m) hu hv
    (fun r hr => by
      obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
      dsimp only
      omega)
    (fun r hr => by
      obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
      dsimp only
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
        (choose_mul_factorial_residue (by norm_num) hm hr1 hr2))

/-! ### Schur-concavity at fixed parameter sum -/

/-- **`eq:C-beta` solved for `C_{m,w}`**: the coefficient convolution is the
`Beta(u,v)`-expectation of the kernel, scaled by `(u+v)_{3m}/(3m-2)!`:

  `C_{m,w}(u,v) = \frac{(u+v)_{3m}}{(3m-2)!}\, 𝔼 G_{m,w}(P)`,  `P ∼ Beta(u,v)`.

This is the form both clauses of `prop:kernel-exact` consume.  At a fixed
parameter sum the prefactor does not move, so `C_{m,w}` inherits whatever order
`lem:beta-order` establishes for `𝔼 G_{m,w}`. -/
theorem cmw_eq_beta_expectation (m : ℕ) (hm : 2 ≤ m) (w : ℕ → ℝ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    cmw w m u v
      = poch (u + v) (3 * m) / (Nat.factorial (3 * m - 2) : ℝ) * (aint m w u v / bmom u v) := by
  have hB : (0:ℝ) < bmom u v := bmom_pos hu hv
  have hF : (0:ℝ) < (Nat.factorial (3 * m - 2) : ℝ) := by positivity
  field_simp
  linear_combination (-1 : ℝ) * aint_eq m hm w hu hv

/-- Any parameter pair rewritten in the fixed-sum coordinates `(s/2 ± d)` of
`eq:fixed-sum`, with `s = u+v` and `d = |u-v|/2`.  Where `v > u` the two
coordinates are exchanged, which is what the parameter symmetry `cmw_symm`
absorbs. -/
theorem cmw_balance (w : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r)) (u v : ℝ) :
    cmw w m u v = cmw w m ((u + v) / 2 + |u - v| / 2) ((u + v) / 2 - |u - v| / 2) := by
  rcases le_or_gt v u with h | h
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u - v),
      show (u + v) / 2 + (u - v) / 2 = u from by ring,
      show (u + v) / 2 - (u - v) / 2 = v from by ring]
  · rw [abs_of_neg (by linarith : u - v < 0),
      show (u + v) / 2 + (-(u - v)) / 2 = v from by ring,
      show (u + v) / 2 - (-(u - v)) / 2 = u from by ring]
    exact cmw_symm w hm hsym u v

/-- **`cor:C-schur` at fixed parameter sum, interior range** (the forward
direction of `prop:kernel-exact`).  For symmetric weights whose kernel is
nondecreasing on `[0,1/2]`, `d ↦ C_{m,w}(s/2+d, s/2-d)` is nonincreasing for
`0 ≤ d < s/2`.

`aint_eq` at both imbalances clears the common factors `(s)_{3m}` and `(3m-2)!`,
leaving the comparison of `aint / B`, which is `lem:beta-order` (`beta_order`)
applied to the kernel. -/
theorem cmw_antitone_imbalance (w : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (hG : MonotoneOn (gmw m w) (Set.Icc 0 (1 / 2)))
    {s d₁ d₂ : ℝ} (hd₁ : 0 ≤ d₁) (hd : d₁ ≤ d₂) (hd₂ : d₂ < s / 2) :
    cmw w m (s / 2 + d₂) (s / 2 - d₂) ≤ cmw w m (s / 2 + d₁) (s / 2 - d₁) := by
  have hs2 : (0:ℝ) < s / 2 := lt_of_le_of_lt (hd₁.trans hd) hd₂
  have hlo₁ : (0:ℝ) < s / 2 + d₁ := by linarith
  have hlo₂ : (0:ℝ) < s / 2 + d₂ := by linarith [hd₁.trans hd]
  have hhi₁ : (0:ℝ) < s / 2 - d₁ := by linarith
  have hhi₂ : (0:ℝ) < s / 2 - d₂ := by linarith
  have hbo := beta_order (H := gmw m w) (gmw_symm m hm w hsym) (continuous_gmw m w) hG hd₁ hd hd₂
  rw [cmw_eq_beta_expectation m hm w hlo₁ hhi₁, cmw_eq_beta_expectation m hm w hlo₂ hhi₂,
    show s / 2 + d₁ + (s / 2 - d₁) = s from by ring,
    show s / 2 + d₂ + (s / 2 - d₂) = s from by ring]
  exact mul_le_mul_of_nonneg_left
    ((div_le_div_iff₀ (bmom_pos hlo₂ hhi₂) (bmom_pos hlo₁ hhi₁)).mpr hbo)
    (div_nonneg (poch_pos (by linarith) _).le (by positivity))

set_option linter.unusedVariables false in
/-- **Schur-concavity of the coefficient convolution** (`cor:C-schur`, via
`eq:C-beta` + `lem:beta-order`).  For symmetric weights whose kernel is
nondecreasing on `[0,1/2]` (`hG`), `C_{m,w}` is Schur-concave: at fixed
parameter sum, a smaller imbalance yields the larger value.

The hypothesis `hG` is `thm:kernel`'s own conclusion, supplied by the proven
`Kernel.gmw_monotoneOn`.  Three binders are surplus to the statement's truth and
are carried anyway, so that the hypotheses are `cor:C-schur`'s own: `hwnn` is the
`0 ≤ w_1` of `eq:w-monotone`, which the proof never uses, and `hu1`, `hv1` are
the positivity of the smaller imbalance's parameters, which follows from that of
the larger. -/
theorem cmw_schur_of_kernel (w : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hwnn : ∀ i, 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (hG : MonotoneOn (gmw m w) (Set.Icc 0 (1 / 2)))
    (u1 v1 u2 v2 : ℝ)
    (hu1 : 0 < u1) (hv1 : 0 < v1) (hu2 : 0 < u2) (hv2 : 0 < v2)
    (hsum : u1 + v1 = u2 + v2) (himb : |u1 - v1| ≤ |u2 - v2|) :
    cmw w m u2 v2 ≤ cmw w m u1 v1 := by
  have hd₂lt : |u2 - v2| / 2 < (u1 + v1) / 2 := by
    rw [hsum]
    rcases le_or_gt v2 u2 with h | h
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u2 - v2)]; linarith
    · rw [abs_of_neg (by linarith : u2 - v2 < 0)]; linarith
  have hb1 := cmw_balance w hm hsym u1 v1
  have hb2 := cmw_balance w hm hsym u2 v2
  rw [← hsum] at hb2
  rw [hb1, hb2]
  exact cmw_antitone_imbalance w m hm hsym hG (by positivity) (by linarith) hd₂lt

/-! ### Strict decrease in the imbalance (`prop:kernel-exact`, strict clause) -/

/-- `C_{m,w} > 0` at positive parameters once the central weight is positive:
`prop:kernel-exact`'s "every interior value is nonnegative and is positive when
the weights are not all zero".  It is what carries strictness to the endpoint
`d = s/2`, where `cmw_right_zero` makes the other value `0`. -/
theorem cmw_pos (w : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) (hwnn : ∀ i, 0 ≤ w i)
    (hwc : 0 < w (m / 2)) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : 0 < cmw w m u v := by
  refine Finset.sum_pos' (fun r _ => div_nonneg ?_ (by positivity)) ⟨m / 2, ?_, ?_⟩
  · exact mul_nonneg (hwnn r) (mul_nonneg (poch_nonneg hu.le _) (poch_nonneg hv.le _))
  · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · exact div_pos (mul_pos hwc (mul_pos (poch_pos hu _) (poch_pos hv _))) (by positivity)

/-- Under `eq:w-monotone` the central weight is the largest of them, so the
paper's "the weights are not all zero" is `0 < w_{⌊m/2⌋}` — the form
`Kernel.gmw_strictMonoOn` and `cmw_pos` consume.  An index past the center is
carried below it by the symmetry `hsym`. -/
theorem weight_center_pos {w : ℕ → ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m - 1) (hwk : 0 < w k) : 0 < w (m / 2) := by
  rcases le_or_gt k (m / 2) with hle | hgt
  · exact lt_of_lt_of_le hwk (hwmono k (m / 2) hk1 hle le_rfl)
  · have hstep := hwmono (m - k) (m / 2) (by omega) (by omega) le_rfl
    rw [hsym k hk1 hk2] at hwk
    linarith

/-- **`prop:kernel-exact`, strict clause, interior range.**  For symmetric weights
whose kernel is strictly increasing on `[0,1/2]`, `d ↦ C_{m,w}(s/2+d, s/2-d)` is
strictly decreasing for `0 ≤ d < s/2`.  The nonstrict route of
`cmw_antitone_imbalance` with `beta_order_strict` in place of `beta_order`. -/
theorem cmw_strictAnti_imbalance (w : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (hG : StrictMonoOn (gmw m w) (Set.Icc 0 (1 / 2)))
    {s d₁ d₂ : ℝ} (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂) (hd₂ : d₂ < s / 2) :
    cmw w m (s / 2 + d₂) (s / 2 - d₂) < cmw w m (s / 2 + d₁) (s / 2 - d₁) := by
  have hs2 : (0:ℝ) < s / 2 := lt_of_le_of_lt (hd₁.trans hd.le) hd₂
  have hlo₁ : (0:ℝ) < s / 2 + d₁ := by linarith
  have hlo₂ : (0:ℝ) < s / 2 + d₂ := by linarith [hd₁.trans hd.le]
  have hhi₁ : (0:ℝ) < s / 2 - d₁ := by linarith
  have hhi₂ : (0:ℝ) < s / 2 - d₂ := by linarith
  have hbo := beta_order_strict (H := gmw m w) (gmw_symm m hm w hsym) (continuous_gmw m w)
    hG.monotoneOn (hG.mono Set.Ioo_subset_Icc_self) hd₁ hd hd₂
  rw [cmw_eq_beta_expectation m hm w hlo₁ hhi₁, cmw_eq_beta_expectation m hm w hlo₂ hhi₂,
    show s / 2 + d₁ + (s / 2 - d₁) = s from by ring,
    show s / 2 + d₂ + (s / 2 - d₂) = s from by ring]
  exact mul_lt_mul_of_pos_left
    ((div_lt_div_iff₀ (bmom_pos hlo₂ hhi₂) (bmom_pos hlo₁ hhi₁)).mpr hbo)
    (div_pos (poch_pos (by linarith) _) (by positivity))

/-- **`prop:kernel-exact`, strict clause** as the paper states it: at each fixed
`s > 0`, `d ↦ C_{m,w}(s/2+d, s/2-d)` is strictly decreasing on the *closed*
`[0,s/2]`.  The interior is `cmw_strictAnti_imbalance`; at the endpoint
`d₂ = s/2` the value is `0` by `cmw_right_zero` while `cmw_pos` makes every
value below it positive. -/
theorem cmw_strictAntiOn_imbalance (w : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hwnn : ∀ i, 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (hwc : 0 < w (m / 2))
    (hG : StrictMonoOn (gmw m w) (Set.Icc 0 (1 / 2)))
    {s : ℝ} (hs : 0 < s) :
    StrictAntiOn (fun d => cmw w m (s / 2 + d) (s / 2 - d)) (Set.Icc 0 (s / 2)) := by
  intro d₁ h₁ d₂ h₂ h12
  change cmw w m (s / 2 + d₂) (s / 2 - d₂) < cmw w m (s / 2 + d₁) (s / 2 - d₁)
  rcases eq_or_lt_of_le h₂.2 with heq | hlt
  · have hzero : s / 2 - d₂ = 0 := by rw [heq]; ring
    rw [hzero, cmw_right_zero w hm]
    exact cmw_pos w hm hwnn hwc (by linarith [h₁.1]) (by rw [heq] at h12; linarith)
  · exact cmw_strictAnti_imbalance w m hm hsym hG h₁.1 h12 hlt

/-! ### Where the coefficient inequalities are strict (`cor:strict`) -/

section Sumset

variable (f : ℕ → ℝ)

/-- `m ∈ I + I` for `I = {n ≥ 1 : f_n > 0}`, written as the existence of the
decomposition rather than as membership in a sumset. -/
def MemSumset (m : ℕ) : Prop :=
  ∃ i j, 1 ≤ i ∧ 1 ≤ j ∧ i + j = m ∧ 0 < f i ∧ 0 < f j

/-- **The first sentence of `cor:strict`'s proof**: `m ∈ I+I` is exactly that the
weights `eq:w-from-f` are not all zero.  Both directions are the same
factorization, read the two ways: a positive product has both factors positive
because `f` is nonnegative. -/
theorem memSumset_iff_weights {m : ℕ} (hm : 2 ≤ m) (hfnn : ∀ r, 0 ≤ f r) :
    MemSumset f m ↔ ∃ k ∈ Finset.Icc 1 (m - 1), 0 < f k * f (m - k) := by
  constructor
  · rintro ⟨i, j, hi, hj, hij, hfi, hfj⟩
    refine ⟨i, Finset.mem_Icc.mpr ⟨hi, by omega⟩, ?_⟩
    rw [show m - i = j from by omega]
    exact mul_pos hfi hfj
  · rintro ⟨k, hk, hpos⟩
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hfk : (0:ℝ) < f k := by
      rcases eq_or_lt_of_le (hfnn k) with h | h
      · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h
    have hfmk : (0:ℝ) < f (m - k) := by
      rcases eq_or_lt_of_le (hfnn (m - k)) with h | h
      · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h
    exact ⟨k, m - k, hk1, by omega, by omega, hfk, hfmk⟩

/-- If `m ∉ I+I` the weights `eq:w-from-f` all vanish, and with them the whole
convolution — so `eq:delta-C` is `0` and not positive.  This is `cor:strict`'s
"if they all vanish, so does `eq:delta-C`", and it needs nothing from the strict
kernel theorem. -/
theorem cmf_eq_zero_of_not_memSumset {m : ℕ} (hm : 2 ≤ m) (hfnn : ∀ r, 0 ≤ f r)
    (h : ¬ MemSumset f m) (u v : ℝ) : cmf f m u v = 0 := by
  have hz : ∀ k ∈ Finset.Icc 1 (m - 1), f k * f (m - k) = 0 := by
    intro k hk
    by_contra hne
    exact h ((memSumset_iff_weights f hm hfnn).mpr ⟨k, hk,
      lt_of_le_of_ne (mul_nonneg (hfnn k) (hfnn (m - k))) (Ne.symm hne)⟩)
  simp only [cmf, cmw]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [hz r hr]
  ring

/-- `I = {a,…,b}` makes `I+I` the interval `{2a,…,2b}` (`cor:strict`).  For
`2a ≤ m ≤ 2b` the witness is `(a, m-a)` below `a+b` and `(m-b, b)` above it. -/
theorem memSumset_iff_of_Icc_support {a b : ℕ} (ha : 1 ≤ a)
    (hI : ∀ n, 0 < f n ↔ (a ≤ n ∧ n ≤ b)) (m : ℕ) :
    MemSumset f m ↔ (2 * a ≤ m ∧ m ≤ 2 * b) := by
  constructor
  · rintro ⟨i, j, hi, hj, hij, hfi, hfj⟩
    obtain ⟨hia, hib⟩ := (hI i).mp hfi
    obtain ⟨hja, hjb⟩ := (hI j).mp hfj
    omega
  · rintro ⟨h1, h2⟩
    rcases le_or_gt m (a + b) with hle | hgt
    · exact ⟨a, m - a, ha, by omega, by omega, (hI a).mpr ⟨le_rfl, by omega⟩,
        (hI (m - a)).mpr ⟨by omega, by omega⟩⟩
    · exact ⟨m - b, b, by omega, by omega, by omega,
        (hI (m - b)).mpr ⟨by omega, by omega⟩, (hI b).mpr ⟨by omega, le_rfl⟩⟩

/-- `I = {a,a+1,…}` makes `I+I` the ray `{m : m ≥ 2a}` (`cor:strict`). -/
theorem memSumset_iff_of_Ici_support {a : ℕ} (ha : 1 ≤ a)
    (hI : ∀ n, 0 < f n ↔ a ≤ n) (m : ℕ) :
    MemSumset f m ↔ 2 * a ≤ m := by
  constructor
  · rintro ⟨i, j, hi, hj, hij, hfi, hfj⟩
    have hi' := (hI i).mp hfi
    have hj' := (hI j).mp hfj
    omega
  · intro h
    exact ⟨a, m - a, ha, by omega, by omega, (hI a).mpr le_rfl, (hI (m - a)).mpr (by omega)⟩

/-- **`cor:strict`, fixed-sum form.**  Under `thm:main`'s degree-`m` hypothesis the
coefficient of `eq:delta-C` is positive exactly on `I+I`, over the whole closed
range `0 ≤ d₁ < d₂ ≤ s/2`.

Off `I+I` the weights all vanish and `cmf_eq_zero_of_not_memSumset` kills both
terms.  On it, `weight_center_pos` makes the central weight positive,
`Kernel.gmw_strictMonoOn` makes the kernel strictly increasing, and
`cmw_strictAntiOn_imbalance` supplies the strict inequality. -/
theorem cmf_delta_pos_iff (m : ℕ) (hm : 2 ≤ m)
    (hfnn : ∀ r, 0 ≤ f r)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → f i * f (m - i) ≤ f j * f (m - j))
    {s d₁ d₂ : ℝ} (hs : 0 < s) (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂) (hd₂ : d₂ ≤ s / 2) :
    0 < cmf f m (s / 2 + d₁) (s / 2 - d₁) - cmf f m (s / 2 + d₂) (s / 2 - d₂)
      ↔ MemSumset f m := by
  set w : ℕ → ℝ := fun k => f k * f (m - k) with hw
  have hwnn : ∀ i, 0 ≤ w i := fun i => mul_nonneg (hfnn i) (hfnn (m - i))
  have hwmono' : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j := hwmono
  have hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r) := by
    intro r hr1 hr2
    have h : m - (m - r) = r := by omega
    simp only [hw, h]
    ring
  have hCmf : ∀ u v : ℝ, cmf f m u v = cmw w m u v := fun _ _ => rfl
  constructor
  · intro hpos
    by_contra hno
    rw [cmf_eq_zero_of_not_memSumset f hm hfnn hno,
      cmf_eq_zero_of_not_memSumset f hm hfnn hno] at hpos
    simp at hpos
  · intro hyes
    obtain ⟨k, hk, hwk⟩ := (memSumset_iff_weights f hm hfnn).mp hyes
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hwc : 0 < w (m / 2) := weight_center_pos (w := w) hm hwmono' hsym hk1 hk2 hwk
    have hG : StrictMonoOn (gmw m w) (Set.Icc 0 (1 / 2)) :=
      gmw_strictMonoOn m hm w hwmono' (fun i _ _ => hwnn i) hsym hwc
    have hkey := cmw_strictAntiOn_imbalance w m hm hwnn hsym hwc hG hs
      (Set.mem_Icc.mpr ⟨hd₁, by linarith⟩) (Set.mem_Icc.mpr ⟨by linarith, hd₂⟩) hd
    rw [hCmf, hCmf]
    linarith

/-- **`cor:strict`, Turánian form**: the same description for `eq:Turan-def`,
which the paper records as holding "whenever `α, β > 0`".  The two parameter
pairs share the sum `s = 2μ+α+β`, with imbalances `|α-β|/2 < (α+β)/2`, and
`|α-β| < α+β` is exactly `α, β > 0` — which is why the strict form needs both
shifts nonzero where `thm:main`'s nonstrict form does not. -/
theorem turan_delta_pos_iff (m : ℕ) (hm : 2 ≤ m)
    (hfnn : ∀ r, 0 ≤ f r)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → f i * f (m - i) ≤ f j * f (m - j))
    {μ α β : ℝ} (hμ : 0 ≤ μ) (hα : 0 < α) (hβ : 0 < β) :
    0 < cmf f m (μ + α) (μ + β) - cmf f m μ (μ + α + β) ↔ MemSumset f m := by
  set w : ℕ → ℝ := fun k => f k * f (m - k) with hw
  have hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r) := by
    intro r hr1 hr2
    have h : m - (m - r) = r := by omega
    simp only [hw, h]
    ring
  have hCmf : ∀ u v : ℝ, cmf f m u v = cmw w m u v := fun _ _ => rfl
  have hsw : ∀ u v : ℝ, cmw w m u v = cmw w m v u := cmw_symm w hm hsym
  have hs : (0:ℝ) < 2 * μ + α + β := by linarith
  set s : ℝ := 2 * μ + α + β with hsdef
  have hhalf : s / 2 = μ + (α + β) / 2 := by rw [hsdef]; ring
  have habs : |α - β| < α + β := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hkey := cmf_delta_pos_iff f m hm hfnn hwmono (s := s) (d₁ := |α - β| / 2)
    (d₂ := (α + β) / 2) hs (by positivity) (by linarith) (by rw [hhalf]; linarith)
  have hlo : cmf f m (s / 2 + (α + β) / 2) (s / 2 - (α + β) / 2) = cmf f m μ (μ + α + β) := by
    rw [show s / 2 + (α + β) / 2 = μ + α + β from by rw [hhalf]; ring,
      show s / 2 - (α + β) / 2 = μ from by rw [hhalf]; ring, hCmf, hCmf, hsw]
  have hhi : cmf f m (s / 2 + |α - β| / 2) (s / 2 - |α - β| / 2) = cmf f m (μ + α) (μ + β) := by
    rcases le_total β α with hle | hle
    · rw [show s / 2 + |α - β| / 2 = μ + α from by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ α - β), hhalf]; ring,
        show s / 2 - |α - β| / 2 = μ + β from by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ α - β), hhalf]; ring]
    · rw [show s / 2 + |α - β| / 2 = μ + β from by
        rw [abs_of_nonpos (by linarith : α - β ≤ 0), hhalf]; ring,
        show s / 2 - |α - β| / 2 = μ + α from by
        rw [abs_of_nonpos (by linarith : α - β ≤ 0), hhalf]; ring, hCmf, hCmf, hsw]
  rw [hlo, hhi] at hkey
  exact hkey

end Sumset

/-! ### The converse of `prop:kernel-exact`

The paper reads the converse off concentration of beta laws: `P_{s,i} → p_i` in
probability as `s → ∞`, so Schur-concavity at every parameter sum forces
`G_{m,w}(p_1) ≥ G_{m,w}(p_2)`.  `G_{m,w}` is a polynomial, so that limit is
algebraic and needs no probability at all.  Clearing the factorial from
`eq:C-def` gives

  `(3m-2)! C_{m,w}(u,v) = ∑_k w_k \binom{3m-2}{3k-1}(u)_{3k}(v)_{3(m-k)}`

(`factorial_mul_cmw`), and at `u = sp`, `v = s(1-p)` each summand divided by
`s^{3m}` is `(sp)_{3k}(s(1-p))_{3(m-k)}/s^{3m}`, which tends to
`p^{3k}(1-p)^{3(m-k)}` because `(sc)_j/s^j = ∏_{i<j}(c + i/s) → c^j`
(`tendsto_poch_div_pow`).  The limit is `G_{m,w}(p)`. -/

/-- `eq:C-def` with the factorial cleared, using
`\binom{3m-2}{3k-1}(3k-1)![3(m-k)-1]! = (3m-2)!`.  This is the same
identity `aint_eq` consumes, taken on its own and with no integral in sight —
which is what makes the large-`s` limit below purely algebraic. -/
theorem factorial_mul_cmw (m : ℕ) (hm : 2 ≤ m) (w : ℕ → ℝ) (u v : ℝ) :
    (Nat.factorial (3 * m - 2) : ℝ) * cmw w m u v
      = ∑ r ∈ Finset.Icc 1 (m - 1), w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ)
          * poch u (3 * r) * poch v (3 * (m - r)) := by
  rw [cmw, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
  have hchoose : Nat.choose (3 * m - 2) (3 * r - 1) * Nat.factorial (3 * r - 1)
      * Nat.factorial (3 * (m - r) - 1) = Nat.factorial (3 * m - 2) := by
    have hle : 3 * r - 1 ≤ 3 * m - 2 := by omega
    have hsub : 3 * m - 2 - (3 * r - 1) = 3 * (m - r) - 1 := by omega
    rw [← hsub]
    exact Nat.choose_mul_factorial_mul_factorial hle
  have hchooseR : (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ) * (Nat.factorial (3 * r - 1) : ℝ)
      * (Nat.factorial (3 * (m - r) - 1) : ℝ) = (Nat.factorial (3 * m - 2) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hchoose
  have hf1 : ((Nat.factorial (3 * r - 1) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : ((Nat.factorial (3 * (m - r) - 1) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  linear_combination (-(w r * poch u (3 * r) * poch v (3 * (m - r)))) * hchooseR

/-- `(sc)_k / s^k = ∏_{i<k}(c + i/s) → c^k` as `s → ∞`, by induction on `k`: the
new factor is `(sc + k)/s = c + k/s`. -/
theorem tendsto_poch_div_pow (c : ℝ) (k : ℕ) :
    Filter.Tendsto (fun s : ℝ => poch (s * c) k / s ^ k) Filter.atTop (nhds (c ^ k)) := by
  induction k with
  | zero =>
      have hconst : (fun s : ℝ => poch (s * c) 0 / s ^ 0) = fun _ : ℝ => (1:ℝ) := by
        funext s; simp [poch]
      rw [hconst, pow_zero]
      exact tendsto_const_nhds
  | succ k ih =>
      have hdiv : Filter.Tendsto (fun s : ℝ => (k : ℝ) / s) Filter.atTop (nhds 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
      have hk : Filter.Tendsto (fun s : ℝ => c + (k : ℝ) / s) Filter.atTop (nhds c) := by
        simpa using tendsto_const_nhds.add hdiv
      have heq : (fun s : ℝ => poch (s * c) k / s ^ k * (c + (k : ℝ) / s))
          =ᶠ[Filter.atTop] fun s : ℝ => poch (s * c) (k + 1) / s ^ (k + 1) := by
        filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with s hs
        have hs0 : s ≠ 0 := ne_of_gt hs
        simp only [poch, Finset.prod_range_succ]
        field
      simpa [pow_succ] using Filter.Tendsto.congr' heq (ih.mul hk)

/-- The beta-average of the kernel at parameters `(sp, s(1-p))`, normalized by
`s^{3m}`, tends to `G_{m,w}(p)`.  This is the paper's `P_{s,i} → p_i` step, run
algebraically on the polynomial `G_{m,w}` instead of through concentration. -/
theorem tendsto_factorial_cmw_div (m : ℕ) (hm : 2 ≤ m) (w : ℕ → ℝ) (p : ℝ) :
    Filter.Tendsto
      (fun s : ℝ => (Nat.factorial (3 * m - 2) : ℝ) * cmw w m (s * p) (s * (1 - p)) / s ^ (3 * m))
      Filter.atTop (nhds (gmw m w p)) := by
  have hterm : ∀ r ∈ Finset.Icc 1 (m - 1),
      Filter.Tendsto (fun s : ℝ =>
          w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ) * (poch (s * p) (3 * r) / s ^ (3 * r))
            * (poch (s * (1 - p)) (3 * (m - r)) / s ^ (3 * (m - r))))
        Filter.atTop
        (nhds (w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ) * p ^ (3 * r)
          * (1 - p) ^ (3 * (m - r)))) := fun r _ =>
    (tendsto_const_nhds.mul (tendsto_poch_div_pow p (3 * r))).mul
      (tendsto_poch_div_pow (1 - p) (3 * (m - r)))
  have hsum := tendsto_finsetSum (Finset.Icc 1 (m - 1)) hterm
  have hlim : (∑ r ∈ Finset.Icc 1 (m - 1), w r * (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ)
      * p ^ (3 * r) * (1 - p) ^ (3 * (m - r))) = gmw m w p := rfl
  rw [hlim] at hsum
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with s hs
  have hs0 : s ≠ 0 := ne_of_gt hs
  rw [factorial_mul_cmw m hm w, Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
  have hpow : s ^ (3 * m) = s ^ (3 * r) * s ^ (3 * (m - r)) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  field_simp

/-- **`prop:kernel-exact`, (2) ⇒ (1)**: Schur-concavity of `C_{m,w}` at every
parameter sum forces the kernel to be nondecreasing on `[0,1/2]`.

At `(u,v) = (sp_1, s(1-p_1))` against `(sp_2, s(1-p_2))` with
`1/2 ≤ p_1 ≤ p_2 < 1` the sums agree and the imbalances are ordered, so
Schur-concavity gives the inequality at every `s > 0`; `tendsto_factorial_cmw_div`
then passes to the limit and gives `G_{m,w}(p_2) ≤ G_{m,w}(p_1)`.  The symmetry
`gmw_symm` turns that into monotonicity on `[0,1/2]`, and the left endpoint
`p = 0` is separate because `1 - 0 = 1` is outside `[1/2,1)`: there
`G_{m,w}(0) = 0` and the kernel is nonnegative. -/
theorem gmw_monotoneOn_of_schur (m : ℕ) (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hwnn : ∀ i, 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (hschur : ∀ u₁ v₁ u₂ v₂ : ℝ, 0 < u₁ → 0 < v₁ → 0 < u₂ → 0 < v₂ →
      u₁ + v₁ = u₂ + v₂ → |u₁ - v₁| ≤ |u₂ - v₂| → cmw w m u₂ v₂ ≤ cmw w m u₁ v₁) :
    MonotoneOn (gmw m w) (Set.Icc 0 (1 / 2)) := by
  have hFa : (0:ℝ) < (Nat.factorial (3 * m - 2) : ℝ) := by positivity
  have hanti : ∀ p₁ p₂ : ℝ, 1 / 2 ≤ p₁ → p₁ ≤ p₂ → p₂ < 1 → gmw m w p₂ ≤ gmw m w p₁ := by
    intro p₁ p₂ h1 h12 h2
    refine le_of_tendsto_of_tendsto (tendsto_factorial_cmw_div m hm w p₂)
      (tendsto_factorial_cmw_div m hm w p₁) ?_
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with s hs
    have hkey := hschur (s * p₁) (s * (1 - p₁)) (s * p₂) (s * (1 - p₂))
      (mul_pos hs (by linarith)) (mul_pos hs (by linarith))
      (mul_pos hs (by linarith)) (mul_pos hs (by linarith)) (by ring) ?_
    · have hpow : (0:ℝ) < s ^ (3 * m) := by positivity
      have hnn : (0:ℝ) ≤ ((Nat.factorial (3 * m - 2) : ℝ) * cmw w m (s * p₁) (s * (1 - p₁))
          - (Nat.factorial (3 * m - 2) : ℝ) * cmw w m (s * p₂) (s * (1 - p₂))) / s ^ (3 * m) :=
        div_nonneg (by nlinarith) hpow.le
      rw [sub_div] at hnn
      linarith
    · rw [abs_of_nonneg (by nlinarith : (0:ℝ) ≤ s * p₁ - s * (1 - p₁)),
        abs_of_nonneg (by nlinarith : (0:ℝ) ≤ s * p₂ - s * (1 - p₂))]
      nlinarith [mul_le_mul_of_nonneg_left h12 hs.le]
  intro p hp q hq hpq
  rcases eq_or_lt_of_le hp.1 with hp0 | hp0
  · have hz : gmw m w 0 = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
      rw [zero_pow (show 3 * r ≠ 0 by omega)]
      ring
    have hnn : 0 ≤ gmw m w q := by
      refine Finset.sum_nonneg fun r _ => ?_
      exact mul_nonneg (mul_nonneg (mul_nonneg (hwnn r) (by positivity)) (pow_nonneg hq.1 _))
        (pow_nonneg (by linarith [hq.2]) _)
    rw [← hp0, hz]
    exact hnn
  · have hrefl := hanti (1 - q) (1 - p) (by linarith [hq.2]) (by linarith) (by linarith)
    rw [gmw_symm m hm w hsym, gmw_symm m hm w hsym] at hrefl
    exact hrefl

/-- `C_{m,w}(0,v) = 0`, the left counterpart of `cmw_right_zero`: every summand
carries `(0)_{3k}` with `3k ≥ 3`. -/
theorem cmw_left_zero (w : ℕ → ℝ) (m : ℕ) (v : ℝ) : cmw w m 0 v = 0 := by
  refine Finset.sum_eq_zero fun r hr => ?_
  obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
  rw [poch_zero_eq_zero (show 1 ≤ 3 * r by omega)]
  ring

/-- **`prop:kernel-exact`, (1) ⇒ (2) on the closed quadrant** `[0,∞)^2`, where the
paper states Schur-concavity.  A boundary point makes `C_{m,w}` vanish
(`cmw_left_zero`, `cmw_right_zero`) while the compared value is nonnegative; and
if the more imbalanced pair is interior so is the less imbalanced one, since
`|u-v| < u+v` is exactly positivity of both coordinates. -/
theorem cmw_schur_of_kernel_closed (w : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hwnn : ∀ i, 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (hG : MonotoneOn (gmw m w) (Set.Icc 0 (1 / 2)))
    (u₁ v₁ u₂ v₂ : ℝ) (hu₁ : 0 ≤ u₁) (hv₁ : 0 ≤ v₁) (hu₂ : 0 ≤ u₂) (hv₂ : 0 ≤ v₂)
    (hsum : u₁ + v₁ = u₂ + v₂) (himb : |u₁ - v₁| ≤ |u₂ - v₂|) :
    cmw w m u₂ v₂ ≤ cmw w m u₁ v₁ := by
  rcases eq_or_lt_of_le hu₂ with h | h
  · rw [← h, cmw_left_zero w m]
    exact cmw_nonneg w m hwnn hu₁ hv₁
  rcases eq_or_lt_of_le hv₂ with h' | h'
  · rw [← h', cmw_right_zero w hm]
    exact cmw_nonneg w m hwnn hu₁ hv₁
  have habs₂ : |u₂ - v₂| < u₂ + v₂ := abs_lt.mpr ⟨by linarith, by linarith⟩
  have habs₁ : |u₁ - v₁| < u₁ + v₁ := by rw [hsum]; linarith
  obtain ⟨ha, hb⟩ := abs_lt.mp habs₁
  exact cmw_schur_of_kernel w m hm hwnn hsym hG u₁ v₁ u₂ v₂ (by linarith) (by linarith) h h'
    hsum himb

/-- **`prop:kernel-exact`**, the equivalence: kernel monotonicity on `[0,1/2]` is
exactly Schur-concavity of `C_{m,w}`.  Forward is `cmw_schur_of_kernel`
(`cmw_schur_of_kernel_closed` for the paper's closed quadrant), backward is
`gmw_monotoneOn_of_schur`.  Stated at positive parameters, which is the weakest
form of (2) the converse consumes and the strongest form of (1) ⇒ (2) it can be
paired with. -/
theorem kernel_exact_iff (w : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hwnn : ∀ i, 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r)) :
    MonotoneOn (gmw m w) (Set.Icc 0 (1 / 2))
      ↔ ∀ u₁ v₁ u₂ v₂ : ℝ, 0 < u₁ → 0 < v₁ → 0 < u₂ → 0 < v₂ →
          u₁ + v₁ = u₂ + v₂ → |u₁ - v₁| ≤ |u₂ - v₂| → cmw w m u₂ v₂ ≤ cmw w m u₁ v₁ :=
  ⟨fun hG u₁ v₁ u₂ v₂ h1 h2 h3 h4 h5 h6 =>
      cmw_schur_of_kernel w m hm hwnn hsym hG u₁ v₁ u₂ v₂ h1 h2 h3 h4 h5 h6,
    gmw_monotoneOn_of_schur m hm w hwnn hsym⟩

end CubicPochhammer
