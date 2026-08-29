/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Uniform bookkeeping for weighted principal-pair dominance

The analytic supply of that theorem — the endpoint root expansions, the residue
comparisons, the contour estimates — is bundled as `FTInputs` in `Bridge`,
because Mathlib carries none of it.  What *is* elementary, and is proven here
without a `sorry`, is the arithmetic the proof runs those inputs through: the
conversion of a linear modulus gap into exponential decay, the resulting bound
on a whole nonprincipal cluster, the two fixed-gap-versus-endpoint-amplitude
estimates, the interior remainder ratio, and the choice of constants that closes
the argument at `|R_M| ≤ |W|/2`.

The cluster estimate is the paper's own `lem:near-cluster-suppression`; the
endpoint, interior and closing steps are the surrounding arithmetic of
`thm:weighted-dominance`.

## Main statements

* `log_le_log_one_add_div` — `x/(1+x) ≤ log (1+x)` for `x ≥ 0`.
* `exp_le_pow_of_one_add_le` — the gap-to-decay conversion:
  `1 + c θ ≤ ζ` and `θ ≤ ε` give `exp (γ * M * θ) ≤ ζ ^ (M+1)` with
  `γ = c / (1 + c * ε)`.  This is the step the proof needs in place of the
  false `(1 + cθ)^(-(M+1)) ⇝ e^(-cMθ)`; the paper's `γ` is `c_0'` at the lower
  endpoint and `c_1'` at the upper.
* `inv_pow_le_exp_neg` — the same statement as the decay bound
  `(ζ ^ (M+1))⁻¹ ≤ exp (-(γ * M * θ))`.
* `cluster_sum_le` — a nonprincipal cluster of `n` members, each of amplitude at
  most `C_W * W` and each with the linear gap, contributes at most
  `C_W * n * exp (-(γ * M * θ)) * W`.
* `exists_gap_threshold` — an `h` exists making `K e^(-γ x)` at most any
  prescribed `δ > 0` on `x ≥ h`.
* `exists_cluster_threshold` — the two composed: one `h`, chosen before `θ` and
  `W`, on which the whole cluster contributes at most `δ * W` throughout
  `θ ≥ h / M`.  This is the `h` of `eq:retained-range`.
* `endpoint_inv_pow_le` / `endpoint_pow_le` — `θ^(-p) ≤ h^(-p) * M^p` for `p ≥ 0`
  and `θ^(|p|) ≤ ε^(|p|)` for `p < 0`: the two branches of the
  `C σ^M / |W| ≤ C_h σ^M M^(p⁺)` estimate, which is where an unexamined `o(1)`
  could otherwise hide an `M`-dependence.
* `interior_ratio_le` — with `c = -log σ / 2`, a remainder `C σ^M` against an
  amplitude `A e^(-cM)` has ratio at most `(C/A) e^(-(-log σ) * M / 2)`.
* `dominance_of_quarters` — `1/4 + 1/4 ≤ 1/2`: the closing accounting, stated so
  that the two endpoint contributions and the retained amplitude are combined
  rather than asserted.

## Implementation notes

Nothing here depends on `FTInputs`; these are facts about real numbers, and the
paper's proof is what supplies their hypotheses.

## References

Formalizes the elementary quantitative steps of
`../shields-2026-forgacs-tran-numerators.tex`, «Weighted principal-pair
dominance» (`subsec:weighted-dominance`, `thm:weighted-dominance`).

## Tags

principal-pair dominance, weight polynomial, uniform bound
-/

namespace ForgacsTran

open Real Finset

/-! ### The gap-to-decay conversion -/

/-- Paper `subsec:weighted-dominance`, inside `lem:near-cluster-suppression`: `log (1+x) ≥
x/(1+x)` for `x ≥ 0`.  This is Mathlib's reciprocal bound
`Real.one_sub_inv_le_log_of_pos` at `1 + x`, since `1 - (1+x)⁻¹ = x/(1+x)`. -/
theorem log_le_log_one_add_div {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have h1 : (0:ℝ) < 1 + x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos h1
  rwa [show 1 - (1 + x)⁻¹ = x / (1 + x) by field] at h

/-- Paper `subsec:weighted-dominance`, `lem:near-cluster-suppression`: the conversion of the
linear endpoint modulus gap `|ζ_j| ≥ 1 + c₀θ` into exponential suppression.
With `γ = c / (1 + c * ε)` and `0 < θ ≤ ε`,
`exp (γ * M * θ) ≤ ζ ^ (M + 1)`.

The naive substitution `(1 + cθ)^(-(M+1)) ⇝ e^(-cMθ)` is false; the factor
`1 / (1 + c * ε)` is what makes it true, and it is available because the
endpoint region has already been restricted to `θ ≤ ε`. -/
theorem exp_le_pow_of_one_add_le
    {c ε θ ζ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (hθε : θ ≤ ε)
    (hζ : 1 + c * θ ≤ ζ) (M : ℕ) :
    Real.exp (c / (1 + c * ε) * M * θ) ≤ ζ ^ (M + 1) := by
  have hε : 0 < ε := lt_of_lt_of_le hθ hθε
  have hcθ : 0 < c * θ := mul_pos hc hθ
  have hcε : 0 < c * ε := mul_pos hc hε
  have h1 : (0:ℝ) < 1 + c * θ := by linarith
  have hζpos : 0 < ζ := lt_of_lt_of_le h1 hζ
  -- `γ * θ ≤ log (1 + c θ) ≤ log ζ`
  have hlog1 : c * θ / (1 + c * θ) ≤ Real.log (1 + c * θ) :=
    log_le_log_one_add_div (le_of_lt hcθ)
  have hmono : c * θ ≤ c * ε := by nlinarith
  have hden : (0:ℝ) < 1 + c * ε := by linarith
  have hstep : c / (1 + c * ε) * θ ≤ c * θ / (1 + c * θ) := by
    have hL : c / (1 + c * ε) * θ = (c * θ) / (1 + c * ε) := by field_simp
    rw [hL, div_le_div_iff₀ hden h1]
    nlinarith [mul_pos hc hθ]
  have hlog2 : Real.log (1 + c * θ) ≤ Real.log ζ := Real.log_le_log h1 hζ
  have hγ : c / (1 + c * ε) * θ ≤ Real.log ζ := le_trans hstep (le_trans hlog1 hlog2)
  -- multiply by `M + 1 ≥ M`
  have hMle : (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
  have hnn : 0 ≤ c / (1 + c * ε) * θ := by positivity
  have hchain : c / (1 + c * ε) * (M : ℝ) * θ ≤ ((M : ℝ) + 1) * Real.log ζ := by
    have : c / (1 + c * ε) * (M : ℝ) * θ = (M : ℝ) * (c / (1 + c * ε) * θ) := by ring
    rw [this]
    calc (M : ℝ) * (c / (1 + c * ε) * θ)
        ≤ ((M : ℝ) + 1) * (c / (1 + c * ε) * θ) := by nlinarith
      _ ≤ ((M : ℝ) + 1) * Real.log ζ := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  calc Real.exp (c / (1 + c * ε) * M * θ)
      ≤ Real.exp (((M : ℝ) + 1) * Real.log ζ) := Real.exp_le_exp.mpr hchain
    _ = ζ ^ (M + 1) := by
        have : ((M : ℝ) + 1) * Real.log ζ = Real.log (ζ ^ (M + 1)) := by
          rw [Real.log_pow]; push_cast; ring
        rw [this, Real.exp_log (pow_pos hζpos _)]

/-- Paper `subsec:weighted-dominance`, `lem:near-cluster-suppression`: the decay form of
`exp_le_pow_of_one_add_le`. -/
theorem inv_pow_le_exp_neg
    {c ε θ ζ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (hθε : θ ≤ ε)
    (hζ : 1 + c * θ ≤ ζ) (M : ℕ) :
    (ζ ^ (M + 1))⁻¹ ≤ Real.exp (-(c / (1 + c * ε) * M * θ)) := by
  have h := exp_le_pow_of_one_add_le hc hθ hθε hζ M
  have hpos : 0 < Real.exp (c / (1 + c * ε) * M * θ) := Real.exp_pos _
  have h1 : (0:ℝ) < 1 + c * θ := by positivity
  have hζpos : 0 < ζ := lt_of_lt_of_le h1 hζ
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (pow_pos hζpos _) hpos).mpr h

/-! ### The nonprincipal endpoint cluster -/

/-- Paper `subsec:weighted-dominance`, `lem:near-cluster-suppression`,
`eq:near-cluster-suppression`.  A finite family of retained nonprincipal roots,
each of amplitude `|A i| ≤ C_W * W` and each carrying the linear modulus gap
`1 + c θ ≤ ζ i`, contributes at most `C_W * n * exp (-(γ M θ)) * W`, with `n` the
number of members.

The paper consumes this at the two endpoints with `C_W = 2`, the value the
residue ratio `A_j/W → 1` supplies through `eq:lower-residue-ratio`, and with
`n = ρ - 2` at the lower endpoint (`eq:lower-cluster-relative-bound`) and
`n = r - 2` at the upper (`eq:upper-cluster-relative-bound`).

Neither `0 ≤ C_W` nor `0 ≤ W` is assumed, because neither is used: on a nonempty
`s` the chain `0 ≤ |A i| ≤ C_W * W` supplies the only sign fact the argument
needs, and on the empty `s` both sides are `0`.  (`exists_cluster_threshold`
below does need `0 ≤ W`, for the reason recorded there.) -/
theorem cluster_sum_le
    {ι : Type*} (s : Finset ι) {A ζ : ι → ℝ} {C_W c ε θ W : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) (hθε : θ ≤ ε)
    (hA : ∀ i ∈ s, |A i| ≤ C_W * W)
    (hgap : ∀ i ∈ s, 1 + c * θ ≤ ζ i) (M : ℕ) :
    ∑ i ∈ s, |A i| * (ζ i ^ (M + 1))⁻¹
      ≤ C_W * s.card * Real.exp (-(c / (1 + c * ε) * M * θ)) * W := by
  have key : ∀ i ∈ s, |A i| * (ζ i ^ (M + 1))⁻¹
      ≤ C_W * W * Real.exp (-(c / (1 + c * ε) * M * θ)) := by
    intro i hi
    have hCWW : (0:ℝ) ≤ C_W * W := le_trans (abs_nonneg _) (hA i hi)
    have hd := inv_pow_le_exp_neg hc hθ hθε (hgap i hi) M
    have hinv_nonneg : 0 ≤ (ζ i ^ (M + 1))⁻¹ := by
      have h1 : (0:ℝ) < 1 + c * θ := by positivity
      have : 0 < ζ i := lt_of_lt_of_le h1 (hgap i hi)
      positivity
    calc |A i| * (ζ i ^ (M + 1))⁻¹
        ≤ (C_W * W) * (ζ i ^ (M + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right (hA i hi) hinv_nonneg
      _ ≤ (C_W * W) * Real.exp (-(c / (1 + c * ε) * M * θ)) :=
          mul_le_mul_of_nonneg_left hd hCWW
  calc ∑ i ∈ s, |A i| * (ζ i ^ (M + 1))⁻¹
      ≤ ∑ _i ∈ s, C_W * W * Real.exp (-(c / (1 + c * ε) * M * θ)) :=
        Finset.sum_le_sum key
    _ = C_W * s.card * Real.exp (-(c / (1 + c * ε) * M * θ)) * W := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Paper `subsec:weighted-dominance`, `lem:near-cluster-suppression` (final
clause): the choice of `h` in `eq:retained-range`.  For any prescribed `δ > 0`
there is an `h > 0` beyond which `K e^(-γ x)` falls below `δ`; taking
`x = M θ ≥ h` is what turns the linear gap into a fixed fraction of the
principal amplitude.  The paper's allocation is `δ = 1/4`.

`K` carries the whole coefficient, so this composes with `cluster_sum_le` at
`K = C_W n W` with nothing left over; `exists_cluster_threshold` is that
composition. -/
theorem exists_gap_threshold {K γ δ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ) (hδ : 0 < δ) :
    ∃ h : ℝ, 0 < h ∧ ∀ x : ℝ, h ≤ x → K * Real.exp (-(γ * x)) ≤ δ := by
  obtain ⟨h₀, hh₀pos, hh₀⟩ : ∃ h₀ : ℝ, 0 < h₀ ∧ K * Real.exp (-(γ * h₀)) ≤ δ := by
    rcases eq_or_lt_of_le hK with hK0 | hK0
    · exact ⟨1, one_pos, by simp [← hK0, hδ.le]⟩
    · refine ⟨max 1 (Real.log (K / δ) / γ), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
      set h₀ := max 1 (Real.log (K / δ) / γ) with hh₀def
      have hlog : Real.log (K / δ) / γ ≤ h₀ := le_max_right _ _
      have : Real.log (K / δ) ≤ γ * h₀ := by
        rw [div_le_iff₀ hγ] at hlog; linarith [hlog]
      have hpos : 0 < K / δ := by positivity
      calc K * Real.exp (-(γ * h₀))
          ≤ K * Real.exp (-Real.log (K / δ)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hK
        _ = δ := by
            rw [← Real.log_inv, Real.exp_log (by positivity)]
            field_simp
  refine ⟨h₀, hh₀pos, fun x hx => ?_⟩
  have hmono : Real.exp (-(γ * x)) ≤ Real.exp (-(γ * h₀)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact le_trans (mul_le_mul_of_nonneg_left hmono hK) hh₀

/-- Paper `subsec:weighted-dominance`, `lem:near-cluster-suppression` (final
clause) at the threshold `h` of `eq:retained-range`: the two preceding lemmas
composed.  Fix the cluster, the amplitude constant `C_W`, the gap constant `c`,
the endpoint window `ε`, and a target fraction `δ > 0`.  Then one `h > 0` serves
the whole retained range — whenever `0 < θ ≤ ε`, the amplitudes obey
`|A i| ≤ C_W * W`, the moduli obey the gap `1 + c θ ≤ ζ i`, and `M θ ≥ h`, the
cluster contributes at most `δ * W`.

The order of the binders is the content: `h` is chosen before `θ`, `W`, `A` and
`ζ`, which is the uniformity `eq:retained-range` asserts and
`thm:weighted-dominance` spends at `δ = 1/4`.  An `h` allowed to depend on `θ`
would say nothing, since the retained range varies with `θ`.

That ordering is also why `0 ≤ W` is a hypothesis here though `cluster_sum_le`
needs none: the conclusion is a bound by `δ * W`, and `h` is fixed before `W` is
seen, so the sign cannot be recovered from the amplitude hypothesis.

This is also `rem:endpoint-sign-free` in its quantitative half: outside the
angular windows of width `h/M`, the linear endpoint modulus gap has become a
suppression fixed by `h` alone rather than one varying with `M`.  The remark's
own point — that the exact sign of the full weighted endpoint cluster is not
needed — is the `|A i| ≤ C_W * W` hypothesis, which bounds the amplitudes in
modulus and says nothing about their signs. -/
theorem exists_cluster_threshold
    {ι : Type*} (s : Finset ι) {C_W c ε δ : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hCW : 0 ≤ C_W) (hδ : 0 < δ) :
    ∃ h : ℝ, 0 < h ∧ ∀ (A ζ : ι → ℝ) (θ W : ℝ), 0 < θ → θ ≤ ε → 0 ≤ W →
      (∀ i ∈ s, |A i| ≤ C_W * W) → (∀ i ∈ s, 1 + c * θ ≤ ζ i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * θ →
          ∑ i ∈ s, |A i| * (ζ i ^ (M + 1))⁻¹ ≤ δ * W := by
  have hden : (0:ℝ) < 1 + c * ε := by positivity
  have hγ : 0 < c / (1 + c * ε) := div_pos hc hden
  obtain ⟨h, hpos, hbd⟩ :=
    exists_gap_threshold (K := C_W * s.card) (mul_nonneg hCW (Nat.cast_nonneg _)) hγ hδ
  refine ⟨h, hpos, fun A ζ θ W hθ hθε hW hA hgap M hM => ?_⟩
  have hstep : C_W * s.card * Real.exp (-(c / (1 + c * ε) * M * θ)) ≤ δ := by
    have hx := hbd ((M : ℝ) * θ) hM
    rwa [← mul_assoc (c / (1 + c * ε))] at hx
  calc ∑ i ∈ s, |A i| * (ζ i ^ (M + 1))⁻¹
      ≤ C_W * s.card * Real.exp (-(c / (1 + c * ε) * M * θ)) * W :=
        cluster_sum_le s hc hθ hθε hA hgap M
    _ ≤ δ * W := mul_le_mul_of_nonneg_right hstep hW

/-! ### Fixed gap against an endpoint amplitude of either sign -/

/-- Paper `sec:dominance`, `thm:weighted-dominance`,
`eq:endpoint-contour-relative-bound` with `p ≥ 0`: on `h/M ≤ θ` the endpoint
amplitude `θ^p` costs at most the polynomial factor `h^(-p) M^p`, so the
fixed-gap remainder `C σ^M / θ^p` is `C_h σ^M M^p` and still `o(1)`. -/
theorem endpoint_inv_pow_le {h θ Mr : ℝ} (hh : 0 < h) (hM : 0 < Mr)
    (hθ : h / Mr ≤ θ) (p : ℕ) :
    (θ ^ p)⁻¹ ≤ (h ^ p)⁻¹ * Mr ^ p := by
  have hθpos : 0 < θ := lt_of_lt_of_le (by positivity) hθ
  have hdivpos : (0:ℝ) < Mr / h := by positivity
  have hinv : θ⁻¹ ≤ Mr / h := by
    rw [show Mr / h = (h / Mr)⁻¹ by rw [inv_div]]
    exact (inv_le_inv₀ hθpos (by positivity)).mpr hθ
  calc (θ ^ p)⁻¹ = (θ⁻¹) ^ p := by rw [inv_pow]
    _ ≤ (Mr / h) ^ p := pow_le_pow_left₀ (by positivity) hinv p
    _ = (h ^ p)⁻¹ * Mr ^ p := by rw [div_pow]; ring

/-- Paper `sec:dominance`, `thm:weighted-dominance`,
`eq:endpoint-contour-relative-bound` with `p < 0`: there the amplitude blows up
at the endpoint, `θ^(-p) ≤ ε^(-p)` is bounded, and no factor of `M` appears —
which is exactly why the exponent in the paper's bound is `p₊ = max p 0`. -/
theorem endpoint_pow_le {θ ε : ℝ} (hθ : 0 ≤ θ) (hθε : θ ≤ ε) (n : ℕ) :
    θ ^ n ≤ ε ^ n :=
  pow_le_pow_left₀ hθ hθε n

/-! ### The compact interior -/

/-- Paper `sec:dominance`, `thm:weighted-dominance`,
`eq:interior-relative-remainder`.  With `α = -log σ > 0` and the deletion
exponent `c = α/2`, a remainder bounded by `C σ^M` against a retained amplitude
`W ≥ A e^(-cM)` has relative size at most `(C/A) e^(-α M/2)`, which is
exponentially small uniformly on the retained interior. -/
theorem interior_ratio_le {σ C A W R : ℝ} (M : ℕ)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hA : 0 < A)
    (hR : |R| ≤ C * σ ^ M)
    (hW : A * Real.exp (-((-Real.log σ) / 2) * M) ≤ W) :
    |R| ≤ C / A * Real.exp (-(-Real.log σ) * M / 2) * W := by
  set α := -Real.log σ with hα
  have hαpos : 0 < α := by
    have : Real.log σ < 0 := Real.log_neg hσ0 hσ1
    simpa [hα] using neg_pos.mpr this
  have hWpos : 0 < W := lt_of_lt_of_le (by positivity) hW
  have hpow : σ ^ M = Real.exp (-(α * M)) := by
    have : -(α * (M : ℝ)) = Real.log (σ ^ M) := by
      rw [Real.log_pow, hα]; ring
    rw [this, Real.exp_log (by positivity)]
  have hC : 0 ≤ C := by
    rcases le_or_gt 0 C with h | h
    · exact h
    · exfalso
      have : C * σ ^ M < 0 := mul_neg_of_neg_of_pos h (by positivity)
      linarith [abs_nonneg R, hR]
  -- `C σ^M = (C/A) e^(-αM/2) * (A e^(-αM/2))`
  have hsplit : C * σ ^ M
      = C / A * Real.exp (-α * M / 2) * (A * Real.exp (-(α / 2) * M)) := by
    have hprod : Real.exp (-α * (M : ℝ) / 2) * Real.exp (-(α / 2) * (M : ℝ))
        = Real.exp (-(α * (M : ℝ))) := by
      rw [← Real.exp_add]; ring_nf
    rw [hpow]
    calc C * Real.exp (-(α * (M : ℝ)))
        = C * (Real.exp (-α * (M : ℝ) / 2) * Real.exp (-(α / 2) * (M : ℝ))) := by rw [hprod]
      _ = C / A * Real.exp (-α * (M : ℝ) / 2) * (A * Real.exp (-(α / 2) * (M : ℝ))) := by
          field_simp
  calc |R| ≤ C * σ ^ M := hR
    _ = C / A * Real.exp (-α * M / 2) * (A * Real.exp (-(α / 2) * M)) := hsplit
    _ ≤ C / A * Real.exp (-α * M / 2) * W := by
        have : (0:ℝ) ≤ C / A * Real.exp (-α * M / 2) := by positivity
        exact mul_le_mul_of_nonneg_left hW this

/-! ### The closing accounting -/

/-- Paper `sec:dominance`, `thm:weighted-dominance`, `eq:dominance-bound`.
The proof allocates `1/4` of the principal amplitude to the nonprincipal
endpoint cluster and `1/4` to the complementary fixed-gap and escaping-root
terms; there is no third contribution, so the two sum to `|R_M| ≤ |W|/2`. -/
theorem dominance_of_quarters {R R₁ R₂ W : ℝ}
    (hsplit : |R| ≤ R₁ + R₂) (h₁ : R₁ ≤ W / 4) (h₂ : R₂ ≤ W / 4) :
    |R| ≤ W / 2 := by linarith

end ForgacsTran
