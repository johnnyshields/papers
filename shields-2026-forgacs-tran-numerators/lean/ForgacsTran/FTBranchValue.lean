/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchExistence

/-!
# The branch value `z(θ)` is real

`Forgacs2017RationalDenominator` Lemma 4(i) and their Eq. (21): on the ray
`arg t = -θ`, at the radius produced by Lemma 2, the pencil branch
`z(t) = -P(t)/t^r` takes a real value, of sign `(-1)^{n-l-1}`.

## Main statements

* `ftArcPoint τ θ` — the point `τ e^{-iθ}`.
* `sub_ftArcPoint_eq` — their Eq. (13), `τ_k - t₀ = -(τ_k sin θ / sin(θ_k - θ)) e^{-iθ_k}`.
* `prod_sub_ftArcPoint` — the product of those chords, the whole `θ`-dependence
  collapsing onto `∑_k θ_k`.
* `ftBranch_ftArcPoint_eq_ofReal` — Lemma 4(i): the branch value is real, and
  `ftBranch_ftArcPoint_sign` gives its sign.
* `exists_ftArcPoint_real` — Lemmas 2 and 4(i) together: every angle in the
  viewing arc carries a denominator zero at a real spectral parameter, which is
  what `thm:FT-geometry` consumes.

## Implementation notes

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

spectral parameter, real value, denominator pencil
-/

namespace ForgacsTran

open Real Set

/-- `t₀ = τ e^{-iθ}`, the point of `Forgacs2017RationalDenominator` Lemma 4. -/
noncomputable def ftArcPoint (τ θ : ℝ) : ℂ := (τ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)

/-- `|τ_k - t₀| = τ_k sin θ / sin (θ_k - θ)`, the chord length of their Fig. 2. -/
noncomputable def ftChord (a θ φ : ℝ) : ℝ := a * Real.sin θ / Real.sin (φ - θ)

theorem exp_neg_ofReal_mul_I (x : ℝ) :
    Complex.exp (-(x : ℂ) * Complex.I) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
  have hx : (-(x : ℂ)) = ((-x : ℝ) : ℂ) := by push_cast; ring
  rw [hx, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast [Real.cos_neg, Real.sin_neg]
  ring

theorem ftChord_pos {a θ φ : ℝ} (ha : 0 < a) (hθ : θ ∈ Ioo 0 π) (hφ : φ ∈ Ioo θ π) :
    0 < ftChord a θ φ := by
  have hs : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hd : 0 < Real.sin (φ - θ) :=
    sin_pos_of_pos_of_lt_pi (by linarith [hφ.1]) (by linarith [hφ.2, hθ.1])
  exact div_pos (mul_pos ha hs) hd

/-- **`Forgacs2017RationalDenominator` Eq. (13).**  Every chord from a zero of `P`
to the branch point has argument `π - θ_k`. -/
theorem sub_ftArcPoint_eq {a τ θ φ : ℝ} (hθ : θ ∈ Ioo 0 π) (hφ : φ ∈ Ioo θ π)
    (h : a * Real.sin φ = τ * Real.sin (φ - θ)) :
    (a : ℂ) - ftArcPoint τ θ
      = -((ftChord a θ φ : ℝ) : ℂ) * Complex.exp (-(φ : ℂ) * Complex.I) := by
  have hd : Real.sin (φ - θ) ≠ 0 :=
    ne_of_gt (sin_pos_of_pos_of_lt_pi (by linarith [hφ.1]) (by linarith [hφ.2, hθ.1]))
  have hsub : Real.sin (φ - θ) = Real.sin φ * Real.cos θ - Real.cos φ * Real.sin θ :=
    Real.sin_sub φ θ
  have him : τ * Real.sin θ = ftChord a θ φ * Real.sin φ := by
    rw [ftChord, div_mul_eq_mul_div, eq_div_iff hd]
    linear_combination (-Real.sin θ) * h
  have hre : a - τ * Real.cos θ = -(ftChord a θ φ) * Real.cos φ := by
    have hrw : -(a * Real.sin θ / Real.sin (φ - θ)) * Real.cos φ
        = -(a * Real.sin θ * Real.cos φ) / Real.sin (φ - θ) := by ring
    rw [hsub] at h
    rw [ftChord, hrw, eq_div_iff hd, hsub]
    linear_combination Real.cos θ * h
  have key : (a : ℂ) - ftArcPoint τ θ
      = ((a - τ * Real.cos θ : ℝ) : ℂ) + ((τ * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    simp only [ftArcPoint, exp_neg_ofReal_mul_I]
    push_cast
    ring
  have key2 : -((ftChord a θ φ : ℝ) : ℂ) * Complex.exp (-(φ : ℂ) * Complex.I)
      = ((-(ftChord a θ φ) * Real.cos φ : ℝ) : ℂ)
        + ((ftChord a θ φ * Real.sin φ : ℝ) : ℂ) * Complex.I := by
    simp only [exp_neg_ofReal_mul_I]
    push_cast
    ring
  rw [key, key2, hre, him]

/-- The chord product: the entire `θ`-dependence of `P(t₀)` collapses onto the
angle sum `∑_k θ_k`. -/
theorem prod_sub_ftArcPoint {n : ℕ} {a φ : Fin n → ℝ} {τ θ : ℝ} (hθ : θ ∈ Ioo 0 π)
    (hφ : ∀ k, φ k ∈ Ioo θ π) (h : ∀ k, a k * Real.sin (φ k) = τ * Real.sin (φ k - θ)) :
    ∏ k, ((a k : ℂ) - ftArcPoint τ θ)
      = ((-1) ^ n * ∏ k, ftChord (a k) θ (φ k) : ℝ)
        * Complex.exp (-((∑ k, φ k : ℝ) : ℂ) * Complex.I) := by
  have hterm : ∀ k, ((a k : ℂ) - ftArcPoint τ θ)
      = (-1 : ℂ) * ((ftChord (a k) θ (φ k) : ℝ) : ℂ) * Complex.exp (-(φ k : ℂ) * Complex.I) := by
    intro k
    rw [sub_ftArcPoint_eq hθ (hφ k) (h k)]; ring
  rw [Finset.prod_congr rfl fun k _ => hterm k]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hexp : ∏ k : Fin n, Complex.exp (-(φ k : ℂ) * Complex.I)
      = Complex.exp (-((∑ k, φ k : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [← Finset.sum_mul]
    simp
  rw [hexp, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

theorem exp_neg_nat_pi_mul_I (l : ℕ) :
    Complex.exp (-((l * π : ℝ) : ℂ) * Complex.I) = (-1 : ℂ) ^ l := by
  have h1 : Complex.exp (-(π : ℂ) * Complex.I) = -1 := by
    rw [show (-(π : ℂ) * Complex.I) = -((π : ℂ) * Complex.I) by ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    norm_num
  have h2 : (-((l * π : ℝ) : ℂ) * Complex.I) = (l : ℂ) * (-(π : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h2, Complex.exp_nat_mul, h1]

/-- **`Forgacs2017RationalDenominator` Lemma 4(i), and their Eq. (21).**  With
`P(t) = c ∏_k (τ_k - t)` and `t₀ = τ e^{-iθ}`, the branch value `-P(t₀)/t₀^r` is
real: the factor `e^{-i ∑_k θ_k}` supplied by the chords cancels `t₀^{-r}`'s
`e^{irθ}` against the angle sum `∑_k θ_k = rθ + lπ`, leaving the sign `(-1)^l`. -/
theorem ftBranch_ftArcPoint_eq {n r l : ℕ} {a φ : Fin n → ℝ} {c τ θ : ℝ}
    (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 π) (hφ : ∀ k, φ k ∈ Ioo θ π)
    (h : ∀ k, a k * Real.sin (φ k) = τ * Real.sin (φ k - θ))
    (hsum : ∑ k, φ k = r * θ + l * π) :
    -((c : ℂ) * ∏ k, ((a k : ℂ) - ftArcPoint τ θ)) / (ftArcPoint τ θ) ^ r
      = (((-1) ^ (n + l + 1) * c * (∏ k, ftChord (a k) θ (φ k)) / τ ^ r : ℝ) : ℂ) := by
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hτ
  have hpow : (ftArcPoint τ θ) ^ r
      = (τ : ℂ) ^ r * Complex.exp (-((r * θ : ℝ) : ℂ) * Complex.I) := by
    rw [ftArcPoint, mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast; ring
  have hsplit : Complex.exp (-((∑ k, φ k : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-((r * θ : ℝ) : ℂ) * Complex.I) * (-1 : ℂ) ^ l := by
    rw [hsum, ← exp_neg_nat_pi_mul_I l, ← Complex.exp_add]
    congr 1
    push_cast; ring
  have hE : Complex.exp (-((r * θ : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  rw [prod_sub_ftArcPoint hθ hφ h, hsplit, hpow]
  push_cast
  field

/-- The sign of the branch value, `Forgacs2017RationalDenominator`'s footnote to
their Eq. (23): it is `(-1)^{n-l-1}`, so the parity of `n - l - 1` is what decides
whether `z` increases or decreases. -/
theorem ftBranch_ftArcPoint_sign {n : ℕ} {a φ : Fin n → ℝ} {c τ θ : ℝ} (r l : ℕ)
    (hc : 0 < c) (hτ : 0 < τ) (ha : ∀ k, 0 < a k) (hθ : θ ∈ Ioo 0 π)
    (hφ : ∀ k, φ k ∈ Ioo θ π) :
    0 < (-1 : ℝ) ^ (n + l + 1)
      * ((-1) ^ (n + l + 1) * c * (∏ k, ftChord (a k) θ (φ k)) / τ ^ r) := by
  have hprod : 0 < ∏ k, ftChord (a k) θ (φ k) :=
    Finset.prod_pos fun k _ => ftChord_pos (ha k) hθ (hφ k)
  have hsq : (-1 : ℝ) ^ (n + l + 1) * (-1) ^ (n + l + 1) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨n + l + 1, by ring⟩
  have : (-1 : ℝ) ^ (n + l + 1)
      * ((-1) ^ (n + l + 1) * c * (∏ k, ftChord (a k) θ (φ k)) / τ ^ r)
      = c * (∏ k, ftChord (a k) θ (φ k)) / τ ^ r := by
    field_simp
    nlinarith [hsq]
  rw [this]
  positivity

/-- **The branch `thm:FT-geometry` imports**, `Forgacs2017RationalDenominator`
Lemmas 2 and 4(i) combined: every angle of the viewing arc carries a radius `τ`
and a *real* spectral parameter `z` for which `τ e^{-iθ}` is a zero of the
denominator pencil `P(t) + z t^r`. -/
theorem exists_ftArcPoint_real {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hl : l < n) {θ : ℝ}
    (hθ0 : 0 < θ) (hθr : θ < π / r) (hrange : (n : ℝ) * θ < r * θ + l * π) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ z : ℝ, 0 < (-1 : ℝ) ^ (n + l + 1) * z ∧
      (c : ℂ) * ∏ k, ((a k : ℂ) - ftArcPoint τ θ) + (z : ℂ) * (ftArcPoint τ θ) ^ r = 0 := by
  obtain ⟨⟨τ, φ⟩, ⟨hτ, hφ, hsum, hratio⟩, -⟩ :=
    exists_unique_ftAngleSystem_pencil hn ha hr hl hθ0 hθr hrange
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hθπ : θ < π := by
    have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have := (lt_div_iff₀ hr0).1 hθr
    nlinarith [hθ0]
  have hθ' : θ ∈ Ioo 0 π := ⟨hθ0, hθπ⟩
  refine ⟨τ, hτ, (-1) ^ (n + l + 1) * c * (∏ k, ftChord (a k) θ (φ k)) / τ ^ r,
    ftBranch_ftArcPoint_sign r l hc hτ ha hθ' hφ, ?_⟩
  have hval := ftBranch_ftArcPoint_eq (c := c) (r := r) (l := l) hτ hθ' hφ hratio hsum
  have hne : (ftArcPoint τ θ) ^ r ≠ 0 := by
    refine pow_ne_zero _ ?_
    simp only [ftArcPoint]
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hτ) (Complex.exp_ne_zero _)
  rw [← hval]
  field

end ForgacsTran
