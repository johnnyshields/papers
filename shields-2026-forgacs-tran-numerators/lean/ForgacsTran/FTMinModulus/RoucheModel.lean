/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTMinModulus.ClusterExpansion

/-!
# The endpoint multiplicity, and the Rouché model for the cluster

Two things the cluster argument needs before Rouché can run: that a denominator
collision at the upper endpoint has multiplicity at most two, and that the pencil
is uniformly close to the model `c₀ + c₁ u^ρ` on a small circle about the
endpoint.  Rouché then puts exactly one pencil zero in each cluster direction.

## Main statements

* `eval_derivative_two_ftRootPolyReal_ne_zero`,
  `eval_derivative_two_ftRootPoly_ne_zero`,
  `rootMultiplicity_ftDen_le_two_of_nonpos` — `Q''` does not vanish at `t ≤ 0`,
  so the collision there has multiplicity at most two.
* `ftRootPoly_eq_map`, `eval_iterate_derivative_ftRootPoly`, `relations_ofReal`,
  `not_three_le_rootMultiplicity_of_gap` — the pencil numerator over `ℝ` and over
  `ℂ` are the same object, which is what lets a real gap bound a complex
  multiplicity.
* `abs_norm_sub_one_add_re_mul_le_of_unimodular`,
  `exists_principal_expansion_of_branch`, `norm_sub_le_of_z_pow_bound`,
  `exists_member_expansion_of_roots`, `clusterAlpha_index_unique` — at the upper
  endpoint a unimodular limit is invisible to the modulus, so the expansion there
  needs its own form.
* `model_root_simple`, `model_roots_distinct`, `norm_pencil_sub_model_le` — the
  model `c₀ + c₁ u^ρ`, its `ρ` simple roots, and how far the pencil is from it;
  `norm_pencil_sub_model_le_of_norm_le` puts an explicit constant on that
  distance over a disk of radius `Dδ`.
* `one_add_pow_le_three_halves`, `norm_pow_sub_one_ge_of_near_one` — the model's
  modulus on a small circle, which is what Rouché compares against.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
  and the principal amplitude» — `sec:geometry`, `lem:amplitude-divisor`.
* `Forgacs2017RationalDenominator`, Proposition 3 Case 2.

## Tags

Rouché, root multiplicity, endpoint, cluster, model polynomial
-/

namespace ForgacsTran

open Polynomial

/-! ### `lem:amplitude-divisor`, the upper endpoint: `Q''` does not vanish at `t ≤ 0`

`Geometry.eval_derivative_two_eq_zero_of_three_le_rootMultiplicity` says a triple
denominator root at `r = 1` forces `Q''(t_e) = 0`;
`Geometry.negShiftProd_deriv_sign` says that cannot happen at `t_e ≤ 0`.  What
is here is the passage between them at the actual `Q`. -/

/-- `Q''` at a nonpositive real point, for the real form of the pencil's
numerator polynomial. -/
theorem eval_derivative_two_ftRootPolyReal_ne_zero {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hn : 2 ≤ n) {t : ℝ} (ht : t ≤ 0) :
    (derivative (derivative (ftRootPolyReal c a))).eval t ≠ 0 := by
  classical
  set xs : Multiset ℝ := Finset.univ.val.map a with hxs
  have hmem : ∀ b ∈ xs, 0 < b := by
    intro b hb
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hb
    exact ha k
  have hcard : 2 ≤ Multiset.card xs := by
    simpa [hxs, Multiset.card_map] using hn
  have hprod : (∏ k, (C (a k) - X) : ℝ[X])
      = (xs.map (fun x : ℝ => C x - X)).prod := by
    rw [hxs, Multiset.map_map]
    rfl
  have hd2 : derivative (derivative (ftRootPolyReal c a))
      = C c * derivative (derivative ((xs.map (fun x : ℝ => C x - X)).prod)) := by
    rw [ftRootPolyReal, hprod, derivative_C_mul, derivative_C_mul]
  obtain ⟨-, -, -, hpos, -⟩ := negShiftProd_deriv_sign
    (fun b hb => lt_of_le_of_lt ht (hmem b hb))
  have hp := hpos hcard
  rw [hd2, eval_mul, eval_C]
  exact mul_ne_zero hc (ne_of_gt hp)

/-- **The connector.**  `Q''(t) ≠ 0` at every nonpositive real `t`, for the
complex pencil numerator itself.  With
`Geometry.eval_derivative_two_eq_zero_of_three_le_rootMultiplicity` this closes
`k ≤ 2` at the finite upper endpoint: a triple root there would force
`Q''(t_b) = 0`, and `t_b ≤ 0` forbids it.  The transport is
`Polynomial.derivative_map` and `Polynomial.eval₂_at_apply`; nothing analytic
crosses. -/
theorem eval_derivative_two_ftRootPoly_ne_zero {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hn : 2 ≤ n) {t : ℝ} (ht : t ≤ 0) :
    (derivative (derivative (ftRootPoly c a))).eval ((t : ℝ) : ℂ) ≠ 0 := by
  have hmapeq : ftRootPoly c a = (ftRootPolyReal c a).map (algebraMap ℝ ℂ) := by
    simp [ftRootPoly, ftRootPolyReal, Polynomial.map_mul, Polynomial.map_prod,
      Polynomial.map_sub]
  have hd : derivative (derivative (ftRootPoly c a))
      = (derivative (derivative (ftRootPolyReal c a))).map (algebraMap ℝ ℂ) := by
    rw [hmapeq, Polynomial.derivative_map, Polynomial.derivative_map]
  rw [hd, Polynomial.eval_map,
    show ((t : ℝ) : ℂ) = algebraMap ℝ ℂ t from rfl,
    Polynomial.eval₂_at_apply]
  simpa using eval_derivative_two_ftRootPolyReal_ne_zero hc ha hn ht

/-- **`lem:amplitude-divisor`, `k = 2` at the finite upper endpoint, closed.**
`Forgacs2017RationalDenominator` Case 3's exclusion, proved: at `r = 1` a triple
denominator root at a nonpositive real point would force `Q''` to vanish there,
and it does not.  With
`Geometry.two_le_rootMultiplicity_ftDen_of_ftCritical` supplying `2 ≤ k`, this
is `k = 2`. -/
theorem rootMultiplicity_ftDen_le_two_of_nonpos {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hn : 2 ≤ n) {t : ℝ} (ht : t ≤ 0) {z : ℂ} :
    (ftDen (ftRootPoly c a) 1 z).rootMultiplicity ((t : ℝ) : ℂ) ≤ 2 := by
  by_contra hcon
  push Not at hcon
  exact eval_derivative_two_ftRootPoly_ne_zero hc ha hn ht
    (eval_derivative_two_eq_zero_of_three_le_rootMultiplicity
      (Q := ftRootPoly c a) (z := z) (te := ((t : ℝ) : ℂ)) (by omega))

/-! ### Connector (3): the pencil numerator over `ℝ` and over `ℂ`

`Geometry`'s log-derivative identities and sign arguments live over `ℝ`;
`ftDen` and `rootMultiplicity` live over `ℂ`.  Everything crosses through
`Polynomial.derivative_map` and `Polynomial.eval₂_at_apply` — no analysis. -/

/-- The complex pencil numerator is the real one mapped. -/
theorem ftRootPoly_eq_map {n : ℕ} (c : ℝ) (a : Fin n → ℝ) :
    ftRootPoly c a = (ftRootPolyReal c a).map (algebraMap ℝ ℂ) := by
  simp [ftRootPoly, ftRootPolyReal, Polynomial.map_mul, Polynomial.map_prod,
    Polynomial.map_sub]

private theorem iterate_derivative_map_ofReal (P : ℝ[X]) (m : ℕ) :
    derivative^[m] (P.map (algebraMap ℝ ℂ)) = (derivative^[m] P).map (algebraMap ℝ ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      Polynomial.derivative_map]

/-- **Connector (3).**  Every iterated derivative of the pencil numerator, at a
real point, is the real one coerced.  `m = 0, 1, 2` are the three the
lower-endpoint argument moves across, and `Complex.ofReal_injective` then carries
any relation between them back to `ℝ`. -/
theorem eval_iterate_derivative_ftRootPoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (m : ℕ) (t : ℝ) :
    (derivative^[m] (ftRootPoly c a)).eval ((t : ℝ) : ℂ)
      = (((derivative^[m] (ftRootPolyReal c a)).eval t : ℝ) : ℂ) := by
  rw [ftRootPoly_eq_map, iterate_derivative_map_ofReal, Polynomial.eval_map,
    show ((t : ℝ) : ℂ) = algebraMap ℝ ℂ t from rfl, Polynomial.eval₂_at_apply]
  rfl

/-- The two relations the lower endpoint produces over `ℂ`, carried to
`ℝ`.  Stated as one lemma because both are the same coercion argument and
a caller needs them together. -/
theorem relations_ofReal {n r : ℕ} {a : Fin n → ℝ} {c t : ℝ}
    (h1 : ((t : ℝ) : ℂ) * (derivative (ftRootPoly c a)).eval ((t : ℝ) : ℂ)
        = (r : ℂ) * (ftRootPoly c a).eval ((t : ℝ) : ℂ))
    (h2 : ((t : ℝ) : ℂ) ^ 2 * (derivative (derivative (ftRootPoly c a))).eval ((t : ℝ) : ℂ)
        = (r : ℂ) * ((r : ℂ) - 1) * (ftRootPoly c a).eval ((t : ℝ) : ℂ)) :
    t * (derivative (ftRootPolyReal c a)).eval t = r * (ftRootPolyReal c a).eval t
      ∧ t ^ 2 * (derivative (derivative (ftRootPolyReal c a))).eval t
        = r * ((r : ℝ) - 1) * (ftRootPolyReal c a).eval t := by
  have e0 := eval_iterate_derivative_ftRootPoly c a 0 t
  have e1 := eval_iterate_derivative_ftRootPoly c a 1 t
  have e2 := eval_iterate_derivative_ftRootPoly c a 2 t
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] at e0 e1 e2
  rw [e0, e1] at h1
  rw [e0, e2] at h2
  constructor
  · exact Complex.ofReal_injective (by push_cast; linear_combination h1)
  · exact Complex.ofReal_injective (by push_cast; linear_combination h2)

/-- **The wrapper — `lem:amplitude-divisor`'s `k ≤ 2` at the lower endpoint,
`ρ = 1`.**  At a real point in the first gap the denominator has no triple
root, with everything produced rather than assumed: `k ≥ 2` gives the first
relation through `Geometry.eval_derivative_ftDen_of_isRoot`,
`eval_derivative_two_relation_of_three_le_rootMultiplicity` gives the second,
`relations_ofReal` carries both to `ℝ`, and
`Geometry.not_relations_in_gap` closes.

`hgt` carries the whole of the case's hypothesis.  It says every root other than
one copy of `x_1` exceeds `t`, which — with `x_1 < t` — forces `x_1` to occur
exactly once: a second copy would sit in the erased multiset and would have to
satisfy `t < x_1`.  So `ρ = 1` is encoded in the statement rather than
side-conditioned, and the multiset is `Finset.univ.val.map a`, which carries the
roots with multiplicity. -/
theorem not_three_le_rootMultiplicity_of_gap {n r : ℕ} {a : Fin n → ℝ} {c t x₁ : ℝ}
    (hc : c ≠ 0) (hr : 1 ≤ r) (ht0 : 0 < t)
    (hx₁ : x₁ ∈ Finset.univ.val.map a) (hx₁t : x₁ < t)
    (hne : (Finset.univ.val.map a).erase x₁ ≠ 0)
    (hgt : ∀ b ∈ (Finset.univ.val.map a).erase x₁, t < b) {z : ℂ} :
    ¬ (3 ≤ (ftDen (ftRootPoly c a) r z).rootMultiplicity ((t : ℝ) : ℂ)) := by
  classical
  intro hk
  have hte : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht0)
  -- the two relations over `ℂ`
  have h0 : (ftDen (ftRootPoly c a) r z).eval ((t : ℝ) : ℂ) = 0 := by
    have := isRoot_iterate_derivative_of_lt_rootMultiplicity
      (p := ftDen (ftRootPoly c a) r z) (t := ((t : ℝ) : ℂ)) (n := 0) (by omega)
    simpa using this
  have hD1 : (derivative (ftDen (ftRootPoly c a) r z)).eval ((t : ℝ) : ℂ) = 0 :=
    isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 1) (by omega)
  have hC1 : ((t : ℝ) : ℂ) * (derivative (ftRootPoly c a)).eval ((t : ℝ) : ℂ)
      = (r : ℂ) * (ftRootPoly c a).eval ((t : ℝ) : ℂ) := by
    have hform := eval_derivative_ftDen_of_isRoot hr hte h0
    rw [hD1] at hform
    field_simp at hform
    linear_combination -hform
  have hC2 := eval_derivative_two_relation_of_three_le_rootMultiplicity hr hte hk
  obtain ⟨hR1, hR2⟩ := relations_ofReal hC1 hC2
  -- transport to the multiset presentation and split off the smallest root
  set xs : Multiset ℝ := Finset.univ.val.map a with hxs
  set ys : Multiset ℝ := xs.erase x₁ with hys
  have hcons : x₁ ::ₘ ys = xs := Multiset.cons_erase hx₁
  have hprod : ftRootPolyReal c a = C c * ((x₁ ::ₘ ys).map (fun x : ℝ => C x - X)).prod := by
    rw [hcons, hxs, ftRootPolyReal, Multiset.map_map]
    rfl
  rw [hprod] at hR1 hR2
  exact not_relations_in_gap hc hr ht0 hne hx₁t hgt hR1 hR2

/-! ### The upper endpoint: a unimodular limit is invisible to the modulus

At the lower endpoint the normalized cluster tends to `1`, and the expansion is
`ζ_j = 1 + c_jδ + O(δ²)` with `c_j` **complex**.  At the upper endpoint for
`r > 1` the small roots go to `0` along the `r`-th roots of `-1`, so
`ζ_j = t_j/τ → ω_j/ω_+` — unimodular, but **not** `1`.  Measured at four pencils,
`‖ζ_j - 1‖` tends to `2.00`, `1.85`, `1.62`, `2.02` at `r = 3,4,5`, so no
statement of the form `ζ_j = 1 + O(δ)` can hold there.

What survives is the **modulus**: `‖ζ_j‖ → 1` cleanly, and its first-order
coefficient is the real `(cos(π/r) - Re ω_j)/sin(π/r)`, measured at `1.734`
against `1.7321` for `r = 3` and `2.0049` against `2` for `r = 4`.  The lemma
below is why the two are compatible: a unimodular factor is invisible to the
modulus, so the whole lower-endpoint modulus chain applies unchanged once the
limit is divided out.

**The two endpoints are not mirror images.**  `hexp₀` had to become complex;
`hexp₁` has to become real.  Mirroring either onto the other is what produced
two of the three defects that binder has carried. -/

/-- **`abs_norm_sub_one_add_re_mul_le` against a unimodular limit.**  If `ζ`
expands about a unimodular `ν` rather than about `1`, its *modulus* obeys the
same real bound: dividing by `ν` changes no norm.  This is what carries the
lower-endpoint modulus machinery to the upper endpoint, where `ζ_j → ω_j/ω_+`
and the complex expansion about `1` is false. -/
theorem abs_norm_sub_one_add_re_mul_le_of_unimodular {ν c ζ : ℂ} {θ C : ℝ} (hθ : 0 ≤ θ)
    (hν : ‖ν‖ = 1) (hsmall : ‖c‖ * θ ≤ 1 / 2)
    (h : ‖ζ - ν * (1 + c * (θ : ℂ))‖ ≤ C * θ ^ 2) :
    |‖ζ‖ - (1 + c.re * θ)| ≤ (C + ‖c‖ ^ 2) * θ ^ 2 := by
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hν
    norm_num at hν
  have hnormζ : ‖ν⁻¹ * ζ‖ = ‖ζ‖ := by
    rw [norm_mul, norm_inv, hν, inv_one, one_mul]
  have hstep : ‖ν⁻¹ * ζ - (1 + c * (θ : ℂ))‖ ≤ C * θ ^ 2 := by
    have hfac : ν⁻¹ * ζ - (1 + c * (θ : ℂ)) = ν⁻¹ * (ζ - ν * (1 + c * (θ : ℂ))) := by
      field_simp
    rw [hfac, norm_mul, norm_inv, hν, inv_one, one_mul]
    exact h
  have := abs_norm_sub_one_add_re_mul_le hθ hsmall hstep
  rwa [hnormζ] at this

/-- **`Forgacs2017RationalDenominator` Prop. 3 Case 2, the principal leg, closed.**
The principal branch point expands as `eq:lower-cluster-expansion` states, with
no hypothesis about `τ` assumed: `FTBranchLimitPoint.exists_bound_ftTau_sub_linear`
supplies the rate and `principal_expansion_of_tau_rate` is its transfer.

The point is written out as `↑(ftTau …) * exp(↑δ * I)` rather than as
`DominanceFT.ftPrincipal`, which is the same term — that module sits above this
one. -/
theorem exists_principal_expansion_of_branch {n r ρ : ℕ} {a : Fin n → ℝ}
    {S : Finset (Fin n)} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) {j : Fin n} (hj : j ∈ S) (hji : j ≠ i)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ k ∉ S, a i * (1 + c) < a k)
    {jp : ℕ} (hp : clusterOmega ρ jp = Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * Complex.I)) :
    ∃ C' ε : ℝ, 0 ≤ C' ∧ 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      ‖((ftTau a r (n - 1) δ : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I)
        - ((a i : ℂ) + clusterAlpha (a i) ρ jp * (δ : ℂ))‖ ≤ C' * δ ^ 2 := by
  obtain ⟨C, ε, hC, hε, hτ⟩ :=
    exists_bound_ftTau_sub_linear hn2 ha hr hS hcard hρ hmin hj hji hc hgap
  obtain ⟨C', hC', hbound⟩ :=
    principal_expansion_of_tau_rate (x₁ := a i) (ha i) hρ hp hC.le
      (min_le_right ε 1)
      (fun δ hδ hδε => hτ δ hδ (le_trans hδε (min_le_left _ _)))
  exact ⟨C', min ε 1, hC', lt_min hε one_pos, hbound⟩

/-- **The crude member bound, from the `z`-rate.**  Every cluster member sits
within `Kδ` of `x_1` once the spectral parameter is `O(δ^ρ)`.

This is the gate on the member leg.  `exists_cluster_ratio_close`'s `e` must be
`O(δ)`, which needs `‖t - t_p‖ = O(δ)`, which is circular against the expansion
unless it comes from outside — and `Cluster.norm_cluster_root` is the way out:
`‖t - x_1‖^ρ‖q(t)‖ = ‖z‖‖t‖^r` turns a `δ^ρ` bound on `z` into a `δ` bound on the
displacement by taking `ρ`-th roots.

**The exponent has to be exact.**  `‖z‖ = O(δ^{ρ-1})` would give only
`‖t - x_1‖ = O(δ^{1-1/ρ})`, too weak to feed a first-order expansion.
`FTBranchZRate.exists_bound_ftBranchZ_pow` supplies `ρ`, and no cluster member
enters its proof, so nothing here is assumed that the conclusion supplies.

The `ρ`-th root is what the identity takes, so an inexact exponent degrades the
conclusion below what the expansion needs — and silently: the gate would still
compile against a weaker hypothesis, and the member leg would simply be
unreachable with nothing indicating why.  A `δ^ρ` hypothesis of this shape is not
interchangeable with any other. -/
theorem norm_sub_le_of_z_pow_bound {Q q : ℂ[X]} {x₁ : ℂ} {ρ r : ℕ} (hρ : 1 ≤ ρ)
    (hQ : Q = (X - C x₁) ^ ρ * q) {z t : ℂ} {Cz M c₀ δ K : ℝ}
    (hroot : (ftDen Q r z).eval t = 0) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hCz : 0 ≤ Cz)
    (hz : ‖z‖ ≤ Cz * δ ^ ρ) (hM : ‖t‖ ≤ M)
    (hc₀ : 0 < c₀) (hq : c₀ ≤ ‖q.eval t‖)
    (hKρ : Cz * M ^ r ≤ K ^ ρ * c₀) :
    ‖t - x₁‖ ≤ K * δ := by
  have hident := norm_cluster_root hQ hroot
  have hqpos : 0 < ‖q.eval t‖ := lt_of_lt_of_le hc₀ hq
  have hδρ : (0 : ℝ) ≤ δ ^ ρ := by positivity
  have htr : ‖t‖ ^ r ≤ M ^ r := pow_le_pow_left₀ (norm_nonneg t) hM r
  have hMr : (0 : ℝ) ≤ M ^ r := le_trans (by positivity) htr
  -- `‖z‖‖t‖^r ≤ (Kδ)^ρ c₀`
  have hstep : ‖z‖ * ‖t‖ ^ r ≤ (K * δ) ^ ρ * c₀ := by
    have h1 : ‖z‖ * ‖t‖ ^ r ≤ (Cz * δ ^ ρ) * M ^ r :=
      mul_le_mul hz htr (by positivity) (by positivity)
    have h2 : (Cz * δ ^ ρ) * M ^ r = (Cz * M ^ r) * δ ^ ρ := by ring
    have h3 : (Cz * M ^ r) * δ ^ ρ ≤ (K ^ ρ * c₀) * δ ^ ρ :=
      mul_le_mul_of_nonneg_right hKρ hδρ
    have h4 : (K ^ ρ * c₀) * δ ^ ρ = (K * δ) ^ ρ * c₀ := by rw [mul_pow]; ring
    linarith [h1, h2 ▸ h1, h3, h4]
  -- cancel `‖q(t)‖`
  have hcancel : ‖t - x₁‖ ^ ρ ≤ (K * δ) ^ ρ := by
    have hkd : (0 : ℝ) ≤ (K * δ) ^ ρ := by positivity
    have hle : ‖t - x₁‖ ^ ρ * ‖q.eval t‖ ≤ (K * δ) ^ ρ * ‖q.eval t‖ := by
      rw [hident]
      exact le_trans hstep (mul_le_mul_of_nonneg_left hq hkd)
    exact le_of_mul_le_mul_right (by linarith [hle]) hqpos
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by omega)).1 hcancel

/-- **The member leg, assembled.**  A cluster member expands as
`eq:lower-cluster-expansion` states, at *its own* index — with the index produced
rather than assumed.

The three steps: `exists_cluster_ratio_close` turns the `z`-free two-root
identity into an exact `ρ`-th root of unity `μ` relating the member to the
principal branch; `cluster_member_expansion` rotates the principal expansion by
`μ`; and `exists_clusterOmega_eq` names the result, since
`(μω_+)^ρ = μ^ρω_+^ρ = -1` makes `μω_+` a cluster direction and
`μ·clusterAlpha x_1 ρ jp = clusterAlpha x_1 ρ ω` for that index.

The `e ≤ Kδ` is what `norm_sub_le_of_z_pow_bound` unlocks: without a crude
`O(δ)` bound on the displacement it is circular, and the `z`-rate is what breaks
the circle. -/
theorem exists_member_expansion_of_roots {x₁ : ℝ} (hx : 0 < x₁) {ρ r : ℕ} (hρ : 2 ≤ ρ)
    {jp : ℕ} {Q q : ℂ[X]} (hQ : Q = (X - C ((x₁ : ℝ) : ℂ)) ^ ρ * q)
    {z t tp : ℂ} {δ e K Cp : ℝ}
    (ht : (ftDen Q r z).eval t = 0) (htp : (ftDen Q r z).eval tp = 0)
    (hne : tp ≠ ((x₁ : ℝ) : ℂ)) (hq : q.eval t ≠ 0) (htp0 : tp ≠ 0)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K) (hCp : 0 ≤ Cp)
    (he2 : e ≤ 1 / 2) (he : e ≤ K * δ)
    (hclose : ‖q.eval tp * t ^ r / (q.eval t * tp ^ r) - 1‖ ≤ e)
    (hp : ‖tp - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ))‖ ≤ Cp * δ ^ 2) :
    ∃ ω : ℕ, ‖t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ ω * (δ : ℂ))‖
      ≤ (5 * K * (x₁ / Real.sin (Real.pi / ρ) + Cp) + Cp) * δ ^ 2 := by
  have hρ1 : 1 ≤ ρ := by omega
  obtain ⟨μ, hμ, hratio⟩ :=
    exists_cluster_ratio_close hρ1 hQ ht htp hne hq htp0 he2 hclose
  have hbound := cluster_member_expansion hx hρ hρ1 hμ hδ hδ1 hK hCp he hratio hp
  -- name the rotated direction
  have hpow : (μ * clusterOmega ρ jp) ^ ρ = -1 := by
    rw [mul_pow, hμ, clusterOmega_pow hρ1, one_mul]
  obtain ⟨ω, hω⟩ := exists_clusterOmega_eq hρ1 hpow
  refine ⟨ω, ?_⟩
  have hs : Real.sin (Real.pi / ρ) ≠ 0 := ne_of_gt (sin_pi_div_pos hρ)
  have halpha : μ * clusterAlpha x₁ ρ jp = clusterAlpha x₁ ρ ω := by
    rw [clusterAlpha, clusterAlpha, hω]
    field_simp
  rwa [halpha] at hbound

/-- **The cluster index is unique once `δ` is small.**  Two distinct directions
sit `‖α_ω - α_{ω'}‖δ` apart while the expansion's error is `Cδ²`, so below
`δ = ‖α_ω - α_{ω'}‖/(2C)` a point cannot satisfy the bound at both.

This is what makes a *labelling* well defined: `exists_member_expansion_of_roots`
produces an index per `(member, δ)` existentially, and uniqueness is what stops
that index depending on `δ` for arbitrary reasons.  It is not by itself
`δ`-independence — see the note there. -/
theorem clusterAlpha_index_unique {x₁ : ℝ} {ρ : ℕ} {ω ω' : ℕ} {t : ℂ} {δ C : ℝ}
    (hδ : 0 < δ)
    (hsep : 2 * (C * δ) < ‖clusterAlpha x₁ ρ ω - clusterAlpha x₁ ρ ω'‖)
    (h1 : ‖t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ ω * (δ : ℂ))‖ ≤ C * δ ^ 2)
    (h2 : ‖t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ ω' * (δ : ℂ))‖ ≤ C * δ ^ 2) :
    False := by
  have hsplit : (clusterAlpha x₁ ρ ω - clusterAlpha x₁ ρ ω') * (δ : ℂ)
      = (t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ ω' * (δ : ℂ)))
        - (t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ ω * (δ : ℂ))) := by ring
  have hle : ‖clusterAlpha x₁ ρ ω - clusterAlpha x₁ ρ ω'‖ * δ ≤ 2 * (C * δ ^ 2) := by
    have hnorm : ‖(clusterAlpha x₁ ρ ω - clusterAlpha x₁ ρ ω') * (δ : ℂ)‖
        = ‖clusterAlpha x₁ ρ ω - clusterAlpha x₁ ρ ω'‖ * δ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    rw [← hnorm, hsplit]
    exact le_trans (norm_sub_le _ _) (by linarith)
  nlinarith [hle, hsep, hδ]

/-! ### The Rouché model for the cluster

Rescaling by `u = (t - x_1)/δ` turns the pencil into
`δ^ρ[u^ρq(x_1 + uδ) + (z/δ^ρ)(x_1 + uδ)^r]`, whose `δ → 0` limit is the model
`F(u) = c_1u^ρ + c_0` with `c_1 = q(x_1)` and `c_0 = z_0x_1^r`.  Its roots are the
cluster directions, and `Shields.Analysis.Complex.Rouche.rouche_of_analytic`
takes a **free centre**, so the disks about `x_1 + α_ωδ` need no translation — the
existence step is a direct application rather than an adaptation of the
origin-centred use in `AttractorPole`.

**`c_0 ≠ 0` is what makes the model nondegenerate**, and it is exactly the
strengthening of the `z`-rate from `‖z‖ = O(δ^ρ)` to `z/δ^ρ → z_0 ≠ 0`.  Without
it `F` collapses to `c_1u^ρ`, a `ρ`-fold root at the origin, and every disk
contains the same point. -/

/-- **The model's roots are simple, exactly when `c_0 ≠ 0`.**  At a root
`c_1u^ρ = -c_0 ≠ 0`, so `u ≠ 0` and `F'(u) = ρc_1u^{ρ-1} ≠ 0`.  This is the
one-root-per-disk nondegeneracy: a `ρ`-fold root would put every cluster
direction at the same point and no separation argument could recover them.

**And `c_0 ≠ 0` is not derivable from any upper bound on `z`, at any constant.**
No statement of the form `‖z‖ ≤ Cδ^ρ` excludes `z/δ^ρ → 0`, however tight `C`
is — so `FTBranchZRate.exists_bound_ftBranchZ_pow` genuinely cannot supply this
and `exists_tendsto_ftBranchZ_div_pow`, which gives `z/δ^ρ → z_0 > 0`, genuinely
must.  The limit version is a precondition for the geometry, not a convenience
strengthening of the bound. -/
theorem model_root_simple {c₀ c₁ u : ℂ} {ρ : ℕ} (hρ : 1 ≤ ρ) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hroot : c₁ * u ^ ρ + c₀ = 0) :
    u ≠ 0 ∧ (ρ : ℂ) * c₁ * u ^ (ρ - 1) ≠ 0 := by
  have hu : u ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : ρ ≠ 0), mul_zero, zero_add] at hroot
    exact hc₀ hroot
  refine ⟨hu, ?_⟩
  have hρc : ((ρ : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero hρc hc₁) (pow_ne_zero _ hu)

/-- The model's roots are `ρ` in number and pairwise distinct, so the cluster
directions they name are separated — the input the disk argument needs, and the
reason `clusterAlpha_index_unique`'s separation is available at all. -/
theorem model_roots_distinct {c₀ c₁ u v : ℂ} {ρ : ℕ} (hρ : 1 ≤ ρ) (hc₀ : c₀ ≠ 0)
    (hc₁ : c₁ ≠ 0) (hu : c₁ * u ^ ρ + c₀ = 0) (hv : c₁ * v ^ ρ + c₀ = 0)
    (hne : u ≠ v) :
    (u / v) ^ ρ = 1 ∧ u / v ≠ 1 := by
  have hv0 : v ≠ 0 := (model_root_simple hρ hc₀ hc₁ hv).1
  have hpow : u ^ ρ = v ^ ρ := by
    have : c₁ * u ^ ρ = c₁ * v ^ ρ := by linear_combination hu - hv
    exact mul_left_cancel₀ hc₁ this
  refine ⟨?_, ?_⟩
  · rw [div_pow, hpow, div_self (pow_ne_zero _ hv0)]
  · intro h
    exact hne (by field_simp at h; exact h)

/-- **The Rouché perturbation, decomposed exactly.**  In `t` coordinates the model
is `M(t) = q(x_1)(t-x_1)^ρ + z_0x_1^rδ^ρ`, which is `δ^ρF((t-x_1)/δ)`, and the
pencil differs from it by exactly two increments:

`D - M = (t-x_1)^ρ(q(t) - q(x_1)) + (zt^r - z_0x_1^rδ^ρ)`.

Nothing is estimated here — this is the identity — and the two increments are
bounded by lemmas already in this module: `norm_eval_sub_eval_le_of_norm_le` for
the first, `norm_pow_sub_pow_le_of_norm_le` for the `t^r` half of the second.
On the circle `‖t - x_1‖ = O(δ)`, so the first term is `O(δ^{ρ+1})`, and the
second is `δ^ρ` times `(z/δ^ρ)t^r - z_0x_1^r`, which is `O(δ)` once the `z`-rate
converges.  Against `‖M‖ ≥ mδ^ρ` on that circle, Rouché applies as soon as the
implied constant times `δ` falls below `m`.

The two increment lemmas were built for the lower-endpoint *ratio* bound; they
serve here unchanged. -/
theorem norm_pencil_sub_model_le {Q q : ℂ[X]} {x₁ : ℂ} {ρ r : ℕ}
    (hQ : Q = (X - C x₁) ^ ρ * q) {z z₀ t : ℂ} {δ : ℝ} :
    ‖(ftDen Q r z).eval t
        - (q.eval x₁ * (t - x₁) ^ ρ + z₀ * x₁ ^ r * (δ : ℂ) ^ ρ)‖
      ≤ ‖t - x₁‖ ^ ρ * ‖q.eval t - q.eval x₁‖
        + ‖z * t ^ r - z₀ * x₁ ^ r * (δ : ℂ) ^ ρ‖ := by
  have hsplit : (ftDen Q r z).eval t
      - (q.eval x₁ * (t - x₁) ^ ρ + z₀ * x₁ ^ r * (δ : ℂ) ^ ρ)
      = (t - x₁) ^ ρ * (q.eval t - q.eval x₁)
        + (z * t ^ r - z₀ * x₁ ^ r * (δ : ℂ) ^ ρ) := by
    rw [ftDen_eval, hQ]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_pow]

/-- **The pencil's increment against its Rouché model, quantitatively.**  With the
pencil written `(t-x_1)^ρq(t) + z(δ)t^r` and the model `(t-x_1)^ρq(x_1) +
z_0x_1^rδ^ρ`, on a disk `‖t - x_1‖ ≤ Dδ` inside `‖t‖ ≤ M` the two differ by at
most `(C_1δ + ‖z(δ)/δ^ρ - z_0‖M^r)δ^ρ`.

Three contributions, and the docstring of `### The domination holds for all
small δ` is exactly the reading of this bound: the `q`-increment and the
`t^r`-increment are both `O(δ^{ρ+1})`, so they are absorbed into `C_1δ·δ^ρ`,
while the rate error contributes `‖z(δ)/δ^ρ - z_0‖M^rδ^ρ` and is made small by
the limit rather than by an estimate.  Every constant is explicit: `L` bounds
`q`'s increment on `‖t‖ ≤ M` and `C_1` collects the two `δ^{ρ+1}` terms. -/
theorem norm_pencil_sub_model_le_of_norm_le {q : ℂ[X]} {xc t z z₀ : ℂ} {M L D C₁ δ : ℝ} {ρ r : ℕ}
    (hδ : 0 < δ) (hD0 : 0 ≤ D)
    (hL : L = ∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖ * ((k : ℝ) * M ^ (k - 1)))
    (hC₁ : C₁ = L * D ^ (ρ + 1) + ‖z₀‖ * (r : ℝ) * M ^ (r - 1) * D)
    (htM : ‖t‖ ≤ M) (hxM : ‖xc‖ ≤ M) (htx : ‖t - xc‖ ≤ D * δ) :
    ‖t - xc‖ ^ ρ * ‖q.eval t - q.eval xc‖
        + ‖z * t ^ r - z₀ * xc ^ r * ((δ : ℝ) : ℂ) ^ ρ‖
      ≤ (C₁ * δ + ‖z / ((δ : ℝ) : ℂ) ^ ρ - z₀‖ * M ^ r) * δ ^ ρ := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg t) htM
  have hMr : (0 : ℝ) ≤ M ^ r := pow_nonneg hM0 r
  have hMr1 : (0 : ℝ) ≤ M ^ (r - 1) := pow_nonneg hM0 _
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hM0 _))
  have hDδ : (0 : ℝ) ≤ D * δ := mul_nonneg hD0 hδ.le
  -- the `q`-increment, weighted by `‖t - x_1‖^ρ`
  have hT1 : ‖t - xc‖ ^ ρ * ‖q.eval t - q.eval xc‖ ≤ L * D ^ (ρ + 1) * δ ^ (ρ + 1) := by
    have hq := norm_eval_sub_eval_le_of_norm_le (q := q) (M := M) htM hxM
    rw [← hL] at hq
    have hp : ‖t - xc‖ ^ ρ ≤ (D * δ) ^ ρ := pow_le_pow_left₀ (norm_nonneg _) htx ρ
    calc ‖t - xc‖ ^ ρ * ‖q.eval t - q.eval xc‖
        ≤ (D * δ) ^ ρ * (L * ‖t - xc‖) :=
          mul_le_mul hp hq (norm_nonneg _) (pow_nonneg hDδ ρ)
      _ ≤ (D * δ) ^ ρ * (L * (D * δ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htx hL0) (pow_nonneg hDδ ρ)
      _ = L * D ^ (ρ + 1) * δ ^ (ρ + 1) := by ring
  -- the `z t^r`-increment, split into the rate error and the `t^r - x_1^r` increment
  have hsplit : z * t ^ r - z₀ * xc ^ r * ((δ : ℝ) : ℂ) ^ ρ
      = (z - z₀ * ((δ : ℝ) : ℂ) ^ ρ) * t ^ r
        + z₀ * ((δ : ℝ) : ℂ) ^ ρ * (t ^ r - xc ^ r) := by ring
  have hznorm : ‖z - z₀ * ((δ : ℝ) : ℂ) ^ ρ‖ = δ ^ ρ * ‖z / ((δ : ℝ) : ℂ) ^ ρ - z₀‖ := by
    have hδC0 : (((δ : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
    have hid : z - z₀ * ((δ : ℝ) : ℂ) ^ ρ
        = ((δ : ℝ) : ℂ) ^ ρ * (z / ((δ : ℝ) : ℂ) ^ ρ - z₀) := by field_simp
    rw [hid, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have hT2a : ‖(z - z₀ * ((δ : ℝ) : ℂ) ^ ρ) * t ^ r‖
      ≤ δ ^ ρ * ‖z / ((δ : ℝ) : ℂ) ^ ρ - z₀‖ * M ^ r := by
    rw [norm_mul, hznorm]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pow_nonneg hδ.le ρ) (norm_nonneg _))
    calc ‖t ^ r‖ = ‖t‖ ^ r := norm_pow t r
      _ ≤ M ^ r := pow_le_pow_left₀ (norm_nonneg t) htM r
  have hT2b : ‖z₀ * ((δ : ℝ) : ℂ) ^ ρ * (t ^ r - xc ^ r)‖
      ≤ ‖z₀‖ * (r : ℝ) * M ^ (r - 1) * D * δ ^ (ρ + 1) := by
    have hpr := norm_pow_sub_pow_le_of_norm_le (M := M) (r := r) htM hxM
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    have hzδ : (0 : ℝ) ≤ ‖z₀‖ * δ ^ ρ := mul_nonneg (norm_nonneg _) (pow_nonneg hδ.le ρ)
    have hrM : (0 : ℝ) ≤ (r : ℝ) * M ^ (r - 1) := mul_nonneg (Nat.cast_nonneg r) hMr1
    calc ‖z₀‖ * δ ^ ρ * ‖t ^ r - xc ^ r‖
        ≤ ‖z₀‖ * δ ^ ρ * ((r : ℝ) * M ^ (r - 1) * ‖t - xc‖) :=
          mul_le_mul_of_nonneg_left hpr hzδ
      _ ≤ ‖z₀‖ * δ ^ ρ * ((r : ℝ) * M ^ (r - 1) * (D * δ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htx hrM) hzδ
      _ = ‖z₀‖ * (r : ℝ) * M ^ (r - 1) * D * δ ^ (ρ + 1) := by ring
  have hsum2 : ‖z * t ^ r - z₀ * xc ^ r * ((δ : ℝ) : ℂ) ^ ρ‖
      ≤ δ ^ ρ * ‖z / ((δ : ℝ) : ℂ) ^ ρ - z₀‖ * M ^ r
        + ‖z₀‖ * (r : ℝ) * M ^ (r - 1) * D * δ ^ (ρ + 1) := by
    rw [hsplit]
    exact le_trans (norm_add_le _ _) (add_le_add hT2a hT2b)
  calc ‖t - xc‖ ^ ρ * ‖q.eval t - q.eval xc‖
        + ‖z * t ^ r - z₀ * xc ^ r * ((δ : ℝ) : ℂ) ^ ρ‖
      ≤ L * D ^ (ρ + 1) * δ ^ (ρ + 1)
        + (δ ^ ρ * ‖z / ((δ : ℝ) : ℂ) ^ ρ - z₀‖ * M ^ r
          + ‖z₀‖ * (r : ℝ) * M ^ (r - 1) * D * δ ^ (ρ + 1)) := add_le_add hT1 hsum2
    _ = (C₁ * δ + ‖z / ((δ : ℝ) : ℂ) ^ ρ - z₀‖ * M ^ r) * δ ^ ρ := by
        rw [hC₁, pow_succ]; ring

/-! ### The model's modulus on a small circle

Rouché needs the model bounded below on the circle it is applied to, and that
circle is centred at one model root `u` with a radius a small multiple of `δ`.
In the normalized coordinate `s = v/u` the model is `c_1u^ρ(s^ρ - 1)`, so the
whole estimate collapses to a statement about `s` near `1`: the geometric sum
`∑_{i<ρ}s^i` stays within `(3/8)ρ` of `ρ`, hence has modulus at least `ρ/2`,
and `s^ρ - 1` is that sum times `s - 1`.

Only the crude bounds are taken — `∑_{i<ρ}i ≤ ρ^2` rather than `ρ(ρ-1)/2`, and
`(1+η)^ρ ≤ 3/2` rather than `e^{1/4}` — because the radius is ours to choose and
a constant of `1/(4ρ)` is as good as any smaller one.
-/

/-- `(1 + η)^ρ ≤ 3/2` once `ρη ≤ 1/4`.  Raise `1 + η ≤ e^η` to the `ρ`, then
`e^{1/4} ≤ 3/2` because `e < (3/2)^4`. -/
theorem one_add_pow_le_three_halves {η : ℝ} {ρ : ℕ} (hη : 0 ≤ η)
    (h : (ρ : ℝ) * η ≤ 1 / 4) : (1 + η) ^ ρ ≤ 3 / 2 := by
  have hexp : Real.exp (1 / 4 : ℝ) ≤ 3 / 2 := by
    have h4 : Real.exp (1 / 4 : ℝ) ^ 4 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    by_contra hcon
    push Not at hcon
    have h5 : ((3 : ℝ) / 2) ^ 4 ≤ Real.exp (1 / 4 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hcon.le 4
    rw [h4] at h5
    have := Real.exp_one_lt_d9
    norm_num at h5
    linarith
  calc (1 + η) ^ ρ ≤ Real.exp η ^ ρ := by
        refine pow_le_pow_left₀ (by linarith) ?_ ρ
        linarith [Real.add_one_le_exp η]
    _ = Real.exp ((ρ : ℝ) * η) := (Real.exp_nat_mul η ρ).symm
    _ ≤ Real.exp (1 / 4 : ℝ) := Real.exp_le_exp.mpr h
    _ ≤ 3 / 2 := hexp

/-- **The geometric sum does not degenerate near `1`.**  For `‖s - 1‖ ≤ 1/(4ρ)`,

`‖s^ρ - 1‖ ≥ (ρ/2)‖s - 1‖`.

This is the normalized form of the whole circle estimate: `s^ρ - 1` factors as
`(∑_{i<ρ}s^i)(s-1)`, and each `s^i` sits within `i(3/2)‖s-1‖` of `1`, so the sum
misses `ρ` by at most `(3/8)ρ`. -/
theorem norm_pow_sub_one_ge_of_near_one {s : ℂ} {ρ : ℕ}
    (h : ‖s - 1‖ * (4 * ρ) ≤ 1) :
    (ρ : ℝ) / 2 * ‖s - 1‖ ≤ ‖s ^ ρ - 1‖ := by
  rcases Nat.eq_zero_or_pos ρ with hρ | hρ
  · subst hρ; simp
  have hη0 : (0 : ℝ) ≤ ‖s - 1‖ := norm_nonneg _
  have hρR : (1 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have hbound : (ρ : ℝ) * ‖s - 1‖ ≤ 1 / 4 := by nlinarith
  have hs : ‖s‖ ≤ 1 + ‖s - 1‖ := by
    have hsplit : s = (s - 1) + 1 := by ring
    calc ‖s‖ = ‖(s - 1) + 1‖ := by rw [← hsplit]
      _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 1 + ‖s - 1‖ := by simp [add_comm]
  have hpow : ∀ j : ℕ, j ≤ ρ → ‖s‖ ^ j ≤ 3 / 2 := by
    intro j hj
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hs j) ?_
    refine one_add_pow_le_three_halves hη0 ?_
    have hjR : (j : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hj
    nlinarith
  have hsi : ∀ i : ℕ, i ≤ ρ → ‖s ^ i - 1‖ ≤ (i : ℝ) * (3 / 2) * ‖s - 1‖ := by
    intro i hi
    have hgeom : (∑ j ∈ Finset.range i, s ^ j) * (s - 1) = s ^ i - 1 := geom_sum_mul s i
    rw [← hgeom, norm_mul]
    have hsum : ‖∑ j ∈ Finset.range i, s ^ j‖ ≤ (i : ℝ) * (3 / 2) := by
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ j ∈ Finset.range i, ‖s ^ j‖ ≤ (3 / 2 : ℝ) := by
        intro j hj
        rw [norm_pow]
        exact hpow j (le_trans (le_of_lt (Finset.mem_range.mp hj)) hi)
      calc ∑ j ∈ Finset.range i, ‖s ^ j‖ ≤ ∑ _j ∈ Finset.range i, (3 / 2 : ℝ) :=
            Finset.sum_le_sum hterm
        _ = (i : ℝ) * (3 / 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    nlinarith
  have hrw : (∑ i ∈ Finset.range ρ, s ^ i) - (ρ : ℂ)
      = ∑ i ∈ Finset.range ρ, (s ^ i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hsplit : ‖(∑ i ∈ Finset.range ρ, s ^ i) - (ρ : ℂ)‖ ≤ 3 / 8 * (ρ : ℝ) := by
    rw [hrw]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range ρ,
        ‖s ^ i - 1‖ ≤ (ρ : ℝ) * (3 / 2) * ‖s - 1‖ := by
      intro i hi
      refine le_trans (hsi i (le_of_lt (Finset.mem_range.mp hi))) ?_
      have hiR : (i : ℝ) ≤ (ρ : ℝ) := by
        exact_mod_cast le_of_lt (Finset.mem_range.mp hi)
      nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    nlinarith
  have hge : (ρ : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range ρ, s ^ i‖ := by
    have hn : ‖((ρ : ℕ) : ℂ)‖ = (ρ : ℝ) := by simp
    have h2 := norm_sub_norm_le ((ρ : ℂ)) (∑ i ∈ Finset.range ρ, s ^ i)
    rw [norm_sub_rev, hn] at h2
    linarith
  calc (ρ : ℝ) / 2 * ‖s - 1‖ ≤ ‖∑ i ∈ Finset.range ρ, s ^ i‖ * ‖s - 1‖ :=
        mul_le_mul_of_nonneg_right hge hη0
    _ = ‖(∑ i ∈ Finset.range ρ, s ^ i) * (s - 1)‖ := (norm_mul _ _).symm
    _ = ‖s ^ ρ - 1‖ := by rw [geom_sum_mul]

/-- The same bound in unnormalized coordinates: on `‖v - u‖ ≤ ‖u‖/(4ρ)`,

`‖v^ρ - u^ρ‖ ≥ (ρ/2)‖v-u‖‖u‖^{ρ-1}`. -/
theorem norm_pow_sub_pow_ge_of_near {u v : ℂ} {ρ : ℕ} (hρ : 1 ≤ ρ) (hu : u ≠ 0)
    (h : ‖v - u‖ * (4 * ρ) ≤ ‖u‖) :
    (ρ : ℝ) / 2 * ‖v - u‖ * ‖u‖ ^ (ρ - 1) ≤ ‖v ^ ρ - u ^ ρ‖ := by
  have hu0 : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hs1 : (v / u) - 1 = (v - u) / u := by field_simp
  have hsn : ‖(v / u) - 1‖ = ‖v - u‖ / ‖u‖ := by rw [hs1, norm_div]
  have hup : (u : ℂ) ^ ρ ≠ 0 := pow_ne_zero ρ hu
  have hsp : (v / u) ^ ρ - 1 = (v ^ ρ - u ^ ρ) / u ^ ρ := by
    rw [div_pow, sub_div, div_self hup]
  have hspn : ‖(v / u) ^ ρ - 1‖ = ‖v ^ ρ - u ^ ρ‖ / ‖u‖ ^ ρ := by
    rw [hsp, norm_div, norm_pow]
  have hhyp : ‖(v / u) - 1‖ * (4 * ρ) ≤ 1 := by
    rw [hsn, div_mul_eq_mul_div, div_le_one hu0]
    exact h
  have hmain := norm_pow_sub_one_ge_of_near_one hhyp
  rw [hsn, hspn] at hmain
  have hpow : ‖u‖ ^ ρ = ‖u‖ ^ (ρ - 1) * ‖u‖ := by
    conv_lhs => rw [show ρ = (ρ - 1) + 1 by omega]
    rw [pow_succ]
  have hpos : (0 : ℝ) < ‖u‖ ^ ρ := pow_pos hu0 ρ
  have hm := mul_le_mul_of_nonneg_right hmain hpos.le
  have e1 : ‖v ^ ρ - u ^ ρ‖ / ‖u‖ ^ ρ * ‖u‖ ^ ρ = ‖v ^ ρ - u ^ ρ‖ := by
    field_simp
  have e2 : (ρ : ℝ) / 2 * (‖v - u‖ / ‖u‖) * ‖u‖ ^ ρ
      = (ρ : ℝ) / 2 * ‖v - u‖ * ‖u‖ ^ (ρ - 1) := by
    rw [hpow]
    field_simp
  rw [e1, e2] at hm
  exact hm

/-- **The model's modulus on the circle Rouché is applied to.**  At a root `u` of
`F(w) = c_1w^ρ + c_0` with `c_0 ≠ 0`, and for `v` within `‖u‖/(4ρ)` of `u`,

`‖F(v)‖ ≥ ‖c_1‖(ρ/2)‖v-u‖‖u‖^{ρ-1}`,

which on the circle `‖v-u‖ = cδ` with `‖u‖ = Aδ` reads
`‖F(v)‖ ≥ ‖c_1‖(ρ/2)cA^{ρ-1}δ^ρ`.  The `δ^ρ` is exact, which is why `c_0 ≠ 0`
is load-bearing: `model_root_simple` supplies `u ≠ 0`, and without it the whole
right-hand side is zero. -/
theorem model_norm_ge_of_near_root {c₀ c₁ u v : ℂ} {ρ : ℕ} (hρ : 1 ≤ ρ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hroot : c₁ * u ^ ρ + c₀ = 0)
    (h : ‖v - u‖ * (4 * ρ) ≤ ‖u‖) :
    ‖c₁‖ * ((ρ : ℝ) / 2 * ‖v - u‖ * ‖u‖ ^ (ρ - 1)) ≤ ‖c₁ * v ^ ρ + c₀‖ := by
  have hu : u ≠ 0 := (model_root_simple hρ hc₀ hc₁ hroot).1
  have hid : c₁ * v ^ ρ + c₀ = c₁ * (v ^ ρ - u ^ ρ) := by linear_combination hroot
  rw [hid, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_sub_pow_ge_of_near hρ hu h) (norm_nonneg _)

/-! ### Rouché, and the pencil root each cluster direction carries

`Shields.rouche_of_analytic` returns a `FactoredOn` for `f` and one for `f + g`
with the *same* count.  Existence of a perturbed root is then a statement about
that count being positive, and the count is read off the model: it is `f`'s own
root inside the circle that forces `n > 0`.  Reading it off the perturbed side
would assume exactly what is being proved.
-/

/-- **Rouché, existence half.**  A root of `f` strictly inside a circle on which
`g` is dominated by `f` forces a root of `f + g` strictly inside it too.

The count is taken from the model: `f w_0 = 0` puts `w_0` among the roots
`FactoredOn f` displays, so that factorization lists at least one, and Rouché
gives the perturbed factorization the same length. -/
theorem exists_root_of_dominated {c : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hlt : ∀ w ∈ Metric.sphere c R, ‖g w‖ < ‖f w‖)
    {w₀ : ℂ} (hw₀ : w₀ ∈ Metric.ball c R) (hfw : f w₀ = 0) :
    ∃ t ∈ Metric.ball c R, f t + g t = 0 := by
  obtain ⟨n, a, a', G, G', h₁, h₂⟩ := Shields.rouche_of_analytic hR hf hg hlt
  obtain ⟨j, hj, -⟩ := (h₁.eq_zero_iff (Metric.ball_subset_closedBall hw₀)).mp hfw
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le j) hj
  refine ⟨a' 0, h₂.mem_ball 0 hn, ?_⟩
  exact (h₂.eq_zero_iff
    (Metric.ball_subset_closedBall (h₂.mem_ball 0 hn))).mpr ⟨0, hn, rfl⟩

/-- **Each cluster direction carries a pencil root.**  Let `u` be a root of the
model `c_1w^ρ + c_0` with `c_1 = q(x_1)` and `c_0 = z_0x_1^rδ^ρ`, and let the
circle of radius `R` about `x_1 + u` be small enough that `R · 4ρ ≤ ‖u‖`.
If on that circle the two increments of `norm_pencil_sub_model_le` stay strictly
below `model_norm_ge_of_near_root`'s lower bound, the pencil has a root inside.

`hdom` is exactly the pair of increments the decomposition names, so the caller
discharges it by bounding `q(t) - q(x_1)` and `zt^r - z_0x_1^rδ^ρ`; both are
`o(δ^ρ)` on the circle once the `z`-rate converges, while the right-hand side is
a fixed multiple of `δ^ρ`.  Nothing here is asymptotic — this is the single
instance, and the `δ`-smallness lives in the caller. -/
theorem exists_ftDen_root_near_model_root {Q q : ℂ[X]} {x₁ : ℂ} {ρ r : ℕ} (hρ : 1 ≤ ρ)
    (hQ : Q = (X - C x₁) ^ ρ * q) (hqx : q.eval x₁ ≠ 0) (hx₁ : x₁ ≠ 0)
    {z z₀ u : ℂ} {δ R : ℝ} (hz₀ : z₀ ≠ 0) (hδ : 0 < δ) (hR : 0 < R)
    (hroot : q.eval x₁ * u ^ ρ + z₀ * x₁ ^ r * (δ : ℂ) ^ ρ = 0)
    (hRu : R * (4 * ρ) ≤ ‖u‖)
    (hdom : ∀ t : ℂ, ‖t - (x₁ + u)‖ = R →
      ‖t - x₁‖ ^ ρ * ‖q.eval t - q.eval x₁‖ + ‖z * t ^ r - z₀ * x₁ ^ r * (δ : ℂ) ^ ρ‖
        < ‖q.eval x₁‖ * ((ρ : ℝ) / 2 * R * ‖u‖ ^ (ρ - 1))) :
    ∃ t : ℂ, ‖t - (x₁ + u)‖ < R ∧ (ftDen Q r z).eval t = 0 := by
  have hδC : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  have hc₀ : z₀ * x₁ ^ r * (δ : ℂ) ^ ρ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hz₀ (pow_ne_zero _ hx₁)) (pow_ne_zero _ hδC)
  set M : ℂ[X] := C (q.eval x₁) * (X - C x₁) ^ ρ + C (z₀ * x₁ ^ r * (δ : ℂ) ^ ρ) with hM
  have hMeval : ∀ t : ℂ,
      M.eval t = q.eval x₁ * (t - x₁) ^ ρ + z₀ * x₁ ^ r * (δ : ℂ) ^ ρ := by
    intro t
    simp [hM]
  have hdomsp : ∀ w ∈ Metric.sphere (x₁ + u) R,
      ‖(ftDen Q r z - M).eval w‖ < ‖M.eval w‖ := by
    intro w hw
    have hws : ‖w - (x₁ + u)‖ = R := by
      rw [← dist_eq_norm]
      exact Metric.mem_sphere.mp hw
    have hvu : ‖w - x₁ - u‖ = R := by
      have hrw : w - x₁ - u = w - (x₁ + u) := by ring
      rw [hrw, hws]
    have hgle : ‖(ftDen Q r z - M).eval w‖
        ≤ ‖w - x₁‖ ^ ρ * ‖q.eval w - q.eval x₁‖
          + ‖z * w ^ r - z₀ * x₁ ^ r * (δ : ℂ) ^ ρ‖ := by
      have hdec := norm_pencil_sub_model_le (Q := Q) (q := q) (x₁ := x₁) (ρ := ρ)
        (r := r) hQ (z := z) (z₀ := z₀) (t := w) (δ := δ)
      rw [eval_sub, hMeval w]
      exact hdec
    have hfge := model_norm_ge_of_near_root (c₀ := z₀ * x₁ ^ r * (δ : ℂ) ^ ρ)
      (c₁ := q.eval x₁) (u := u) (v := w - x₁) hρ hc₀ hqx hroot
      (by rw [hvu]; exact hRu)
    rw [hvu] at hfge
    calc ‖(ftDen Q r z - M).eval w‖
        ≤ ‖w - x₁‖ ^ ρ * ‖q.eval w - q.eval x₁‖
          + ‖z * w ^ r - z₀ * x₁ ^ r * (δ : ℂ) ^ ρ‖ := hgle
      _ < ‖q.eval x₁‖ * ((ρ : ℝ) / 2 * R * ‖u‖ ^ (ρ - 1)) := hdom w hws
      _ ≤ ‖M.eval w‖ := by rw [hMeval w]; exact hfge
  have hw₀ : (x₁ + u) ∈ Metric.ball (x₁ + u) R := Metric.mem_ball_self hR
  have hfw : M.eval (x₁ + u) = 0 := by
    rw [hMeval]
    have hrw : x₁ + u - x₁ = u := by ring
    rw [hrw]
    exact hroot
  obtain ⟨t, htb, ht0⟩ := exists_root_of_dominated hR (analyticOnNhd_eval M _)
    (analyticOnNhd_eval (ftDen Q r z - M) _) hdomsp hw₀ hfw
  refine ⟨t, ?_, ?_⟩
  · rw [← dist_eq_norm]
    exact Metric.mem_ball.mp htb
  · rw [eval_sub] at ht0
    linear_combination ht0

end ForgacsTran
