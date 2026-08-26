/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchRegularity
import ForgacsTran.FTBranchCritical
import ForgacsTran.Geometry

/-!
# The endpoint limit of the branch radius

`Forgacs2017RationalDenominator` Lemma 6 turns on the limit of `τ(θ)` as
`θ → 0` being a zero of `t^{r-1}(rP(t) - tP'(t))` — that is, of `ftCritical`.
This module supplies that fact about the branch; the statement about `z` is the
other lane's.

## Main statements

* `ftPencilIm` — `Im (e^{irθ} P(τ e^{-iθ}))`, which vanishes exactly where the
  branch value is real, and vanishes identically at `θ = 0`.
* `ftPencilImDeriv` — its `θ`-derivative, which at `θ = 0` is
  `-(t Q'(t) - r Q(t))` evaluated at `τ`: the critical polynomial itself.
* `ftPencilIm_eq_zero` — the branch of `FTBranchFunction` satisfies
  `ftPencilIm = 0`.
* `eval_ftCriticalReal_eq_zero_of_tendsto` — the identification: any limit of
  `τ(θ)` as `θ → 0⁺` is a zero of the critical polynomial.
* `ftTau_le_div_cos` — `τ(θ) ≤ (max_k τ_k)/cos θ`, so the branch is bounded near
  `θ = 0`; with the monotonicity of `Forgacs2017RationalDenominator` Lemma 3 this
  is what makes the limit exist.

## Implementation notes

**Differs from the paper's route.**  The paper argues that `τ(θ)e^{±iθ}` are two
zeros of `P + z t^r` which collide as `θ → 0`, so the limit is a multiple zero,
and then reads the critical polynomial off the derivative.  Here the collision is
replaced by Rolle's theorem applied to `θ ↦ Im (e^{irθ}P(τe^{-iθ}))` on `[0, θ]`:
that function vanishes at both ends, its `θ`-derivative at `0` *is* the critical
polynomial, and joint continuity carries the intermediate zero to the limit.  No
limit of polynomial factorizations is taken.

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

endpoint limit, branch radius, Forgacs-Tran branch
-/

namespace ForgacsTran

open Real Set Filter Topology Polynomial

private theorem ftHasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).im) f'.im x :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h

/-- `Im (e^{irθ} P(τ e^{-iθ}))`.  It vanishes exactly where the branch value
`-P(t₀)/t₀^r` is real, and identically at `θ = 0`. -/
noncomputable def ftPencilIm (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) : ℝ :=
  (Complex.exp (((r : ℝ) * θ : ℝ) * Complex.I)
    * (P.map (algebraMap ℝ ℂ)).eval (ftArcPoint τ θ)).im

/-- The `θ`-derivative of `ftPencilIm`, in terms of `Geometry`'s `ftCritical`. -/
noncomputable def ftPencilImDeriv (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) : ℝ :=
  (-Complex.I * Complex.exp (((r : ℝ) * θ : ℝ) * Complex.I)
    * (ftCritical (P.map (algebraMap ℝ ℂ)) r).eval (ftArcPoint τ θ)).im

theorem ftCritical_map (P : Polynomial ℝ) (r : ℕ) :
    ftCritical (P.map (algebraMap ℝ ℂ)) r = (ftCriticalReal P r).map (algebraMap ℝ ℂ) := by
  simp [ftCritical, ftCriticalReal, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.derivative_map]

@[simp] theorem ftArcPoint_zero (τ : ℝ) : ftArcPoint τ 0 = (τ : ℂ) := by
  simp [ftArcPoint]

theorem aeval_ofReal (P : Polynomial ℝ) (t : ℝ) :
    (aeval ((t : ℝ) : ℂ)) P = ((P.eval t : ℝ) : ℂ) := by
  rw [aeval_def, show ((t : ℝ) : ℂ) = algebraMap ℝ ℂ t from rfl]
  exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) t

@[simp] theorem ftPencilIm_zero (P : Polynomial ℝ) (r : ℕ) (τ : ℝ) : ftPencilIm P r τ 0 = 0 := by
  simp [ftPencilIm, aeval_ofReal]

/-- **At `θ = 0` the derivative is the critical polynomial.** -/
theorem ftPencilImDeriv_zero (P : Polynomial ℝ) (r : ℕ) (τ : ℝ) :
    ftPencilImDeriv P r τ 0 = -(ftCriticalReal P r).eval τ := by
  simp [ftPencilImDeriv, ftCritical_map, aeval_ofReal, eval_ftCriticalReal]

theorem hasDerivAt_ftArcPoint_theta (τ θ : ℝ) :
    HasDerivAt (fun s : ℝ => ftArcPoint τ s) (-Complex.I * ftArcPoint τ θ) θ := by
  have h0 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => -((s : ℝ) : ℂ) * Complex.I) (-Complex.I) θ := by
    simpa using h0.neg.mul_const Complex.I
  have h3 : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℝ) : ℂ) * Complex.I))
      (Complex.exp (-(θ : ℂ) * Complex.I) * -Complex.I) θ := h2.cexp
  have h4 := h3.const_mul ((τ : ℝ) : ℂ)
  refine h4.congr_deriv ?_
  simp only [ftArcPoint]
  ring

theorem hasDerivAt_ftPencilIm (P : Polynomial ℝ) (r : ℕ) (τ θ : ℝ) :
    HasDerivAt (fun s => ftPencilIm P r τ s) (ftPencilImDeriv P r τ θ) θ := by
  set Q := P.map (algebraMap ℝ ℂ) with hQ
  have he : HasDerivAt (fun s : ℝ => Complex.exp (((r : ℝ) * s : ℝ) * Complex.I))
      (Complex.exp (((r : ℝ) * θ : ℝ) * Complex.I) * ((r : ℂ) * Complex.I)) θ := by
    have h0 : HasDerivAt (fun s : ℝ => (((r : ℝ) * s : ℝ) : ℂ) * Complex.I)
        ((r : ℂ) * Complex.I) θ := by
      have h1 : HasDerivAt (fun s : ℝ => (((r : ℝ) * s : ℝ) : ℂ)) ((r : ℂ)) θ := by
        have := ((hasDerivAt_id θ).const_mul ((r : ℝ))).ofReal_comp
        simpa using this
      simpa using h1.mul_const Complex.I
    exact h0.cexp
  have hp : HasDerivAt (fun s : ℝ => Q.eval (ftArcPoint τ s))
      ((derivative Q).eval (ftArcPoint τ θ) * (-Complex.I * ftArcPoint τ θ)) θ :=
    (Q.hasDerivAt (ftArcPoint τ θ)).comp θ (hasDerivAt_ftArcPoint_theta τ θ)
  have hmul := he.mul hp
  refine (ftHasDerivAt_im hmul).congr_deriv ?_
  simp only [ftPencilImDeriv, ftCritical, eval_sub, eval_mul, eval_C, eval_X, hQ]
  congr 1
  have hpow : (ftArcPoint τ θ) * Complex.exp (((r : ℝ) * θ : ℝ) * Complex.I)
      = Complex.exp (((r : ℝ) * θ : ℝ) * Complex.I) * ftArcPoint τ θ := by ring
  ring

theorem continuous_ftPencilImDeriv (P : Polynomial ℝ) (r : ℕ) :
    Continuous (fun p : ℝ × ℝ => ftPencilImDeriv P r p.1 p.2) := by
  have harc : Continuous (fun p : ℝ × ℝ => ftArcPoint p.1 p.2) := by
    simp only [ftArcPoint]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp continuous_snd).neg).mul
        continuous_const))
  have hexp : Continuous (fun p : ℝ × ℝ => Complex.exp (((r : ℝ) * p.2 : ℝ) * Complex.I)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_snd)).mul
        continuous_const)
  exact Complex.continuous_im.comp
    ((continuous_const.mul hexp).mul ((ftCritical (P.map (algebraMap ℝ ℂ)) r).continuous_aeval.comp
      harc))

theorem eval_map_ftRootPolyReal {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (t : ℂ) :
    ((ftRootPolyReal c a).map (algebraMap ℝ ℂ)).eval t = (c : ℂ) * ∏ k, ((a k : ℂ) - t) := by
  simp [ftRootPolyReal, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.eval_prod]

theorem ftArcPoint_pow (τ θ : ℝ) (r : ℕ) :
    (ftArcPoint τ θ) ^ r = (τ : ℂ) ^ r * Complex.exp ((-((r : ℝ) * θ) : ℝ) * Complex.I) := by
  rw [ftArcPoint, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **The branch satisfies `ftPencilIm = 0`.**  This is
`Forgacs2017RationalDenominator` Lemma 4(i) in the form the endpoint argument
uses: `e^{irθ}P(t₀)` is real, so its imaginary part vanishes. -/
theorem ftPencilIm_eq_zero {n r l : ℕ} {a : Fin n → ℝ} (c : ℝ) (ha : ∀ k, 0 < a k)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (h : FTBranchAt a r l θ) :
    ftPencilIm (ftRootPolyReal c a) r (ftTau a r l θ) θ = 0 := by
  obtain ⟨hmem, hsum, hratio⟩ := ftBranchAngle_spec ha hθ h
  have hτ : 0 < ftTau a r l θ := ftTau_pos h
  have hval := ftBranch_ftArcPoint_eq (a := a) (φ := fun k => ftBranchAngle a r l k θ)
    (c := c) (r := r) (l := l) hτ hθ hmem hratio hsum
  set X : ℝ := (-1) ^ (n + l + 1) * c
    * (∏ k, ftChord (a k) θ (ftBranchAngle a r l k θ)) / ftTau a r l θ ^ r with hX
  have hne : (ftArcPoint (ftTau a r l θ) θ) ^ r ≠ 0 := by
    refine pow_ne_zero _ ?_
    simp only [ftArcPoint]
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hτ) (Complex.exp_ne_zero _)
  have hQ : (c : ℂ) * ∏ k, ((a k : ℂ) - ftArcPoint (ftTau a r l θ) θ)
      = -((X : ℝ) : ℂ) * (ftArcPoint (ftTau a r l θ) θ) ^ r := by
    field_simp at hval
    linear_combination -hval
  rw [ftPencilIm, eval_map_ftRootPolyReal, hQ, ftArcPoint_pow]
  have hcancel : Complex.exp (((r : ℝ) * θ : ℝ) * Complex.I)
      * (-((X : ℝ) : ℂ) * ((ftTau a r l θ : ℂ) ^ r
        * Complex.exp ((-((r : ℝ) * θ) : ℝ) * Complex.I)))
      = ((-(X * ftTau a r l θ ^ r) : ℝ) : ℂ) := by
    have hE : Complex.exp (((r : ℝ) * θ : ℝ) * Complex.I)
        * Complex.exp ((-((r : ℝ) * θ) : ℝ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      push_cast
      rw [show ((r : ℂ) * (θ : ℂ) * Complex.I + -((r : ℂ) * (θ : ℂ)) * Complex.I) = 0 by ring]
      exact Complex.exp_zero
    push_cast at hE ⊢
    linear_combination (-((X : ℝ) : ℂ) * (ftTau a r l θ : ℂ) ^ r) * hE
  rw [hcancel, Complex.ofReal_im]

/-- **The identification.**  Any limit of the branch radius as `θ → 0⁺` is a zero
of the critical polynomial `E(t) = t P'(t) - r P(t)` — the statement
`Forgacs2017RationalDenominator` Lemma 6 needs about `t_a`. -/
theorem eval_ftCriticalReal_eq_zero_of_tendsto {P : Polynomial ℝ} {r : ℕ} {T : ℝ → ℝ} {L : ℝ}
    {l : Filter ℝ} [l.NeBot] (hl : l ≤ 𝓝[>] (0 : ℝ))
    (hzero : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftPencilIm P r (T θ) θ = 0)
    (hT : Tendsto T l (𝓝 L)) :
    (ftCriticalReal P r).eval L = 0 := by
  have hrolle : ∀ θ : ℝ, ∃ η : ℝ, (0 < θ ∧ ftPencilIm P r (T θ) θ = 0) →
      (η ∈ Ioo 0 θ ∧ ftPencilImDeriv P r (T θ) η = 0) := by
    intro θ
    by_cases hc : 0 < θ ∧ ftPencilIm P r (T θ) θ = 0
    · obtain ⟨w, hw, hw0⟩ := exists_hasDerivAt_eq_zero (f := fun s => ftPencilIm P r (T θ) s)
        (f' := fun s => ftPencilImDeriv P r (T θ) s) hc.1
        (fun s _ => ((hasDerivAt_ftPencilIm P r (T θ) s).continuousAt).continuousWithinAt)
        (by rw [ftPencilIm_zero, hc.2])
        (fun s _ => hasDerivAt_ftPencilIm P r (T θ) s)
      exact ⟨w, fun _ => ⟨hw, hw0⟩⟩
    · exact ⟨0, fun hh => absurd hh hc⟩
  choose η hη using hrolle
  have hgood : ∀ᶠ θ in l, η θ ∈ Ioo 0 θ ∧ ftPencilImDeriv P r (T θ) (η θ) = 0 := by
    filter_upwards [hl hzero, hl self_mem_nhdsWithin] with θ h0 hpos using hη θ ⟨hpos, h0⟩
  have hηtend : Tendsto η l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun _ : ℝ => (0 : ℝ)) (h := fun θ : ℝ => θ) tendsto_const_nhds
      ((tendsto_id.mono_left nhdsWithin_le_nhds).mono_left hl) ?_ ?_
    · filter_upwards [hgood] with θ hθ using hθ.1.1.le
    · filter_upwards [hgood] with θ hθ using hθ.1.2.le
  have hprod : Tendsto (fun θ : ℝ => (T θ, η θ)) l (𝓝 (L, 0)) :=
    hT.prodMk_nhds hηtend
  have hcont : Tendsto ((fun p : ℝ × ℝ => ftPencilImDeriv P r p.1 p.2)
      ∘ (fun θ : ℝ => (T θ, η θ))) l (𝓝 (ftPencilImDeriv P r L 0)) :=
    ((continuous_ftPencilImDeriv P r).tendsto (L, 0)).comp hprod
  simp only [Function.comp_def] at hcont
  have hzero' : Tendsto (fun θ => ftPencilImDeriv P r (T θ) (η θ)) l (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hgood] with θ hθ using hθ.2.symm
  have := tendsto_nhds_unique hcont hzero'
  rw [ftPencilImDeriv_zero] at this
  linarith

/-- **The branch is bounded near `θ = 0`.**  If `τ` exceeded `A / cos θ` every
angle would fall below `π/2`, and their sum could not reach `(n-1)π`.  With the
monotonicity of `Forgacs2017RationalDenominator` Lemma 3 this is what makes the
limit at `0` exist; it is their Remark 5. -/
theorem ftTau_le_div_cos {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n) (_ha : ∀ k, 0 < a k)
    {A θ : ℝ} (hA : ∀ k, a k ≤ A) (hθ0 : 0 < θ) (hθ2 : θ < π / 2)
    (h : FTBranchAt a r (n - 1) θ) :
    ftTau a r (n - 1) θ ≤ A / Real.cos θ := by
  have hπ := pi_pos
  have hθπ : θ ∈ Ioo 0 π := ⟨hθ0, by linarith⟩
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩
  have hsin : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ0 hθπ.2
  have hτ : 0 < ftTau a r (n - 1) θ := ftTau_pos h
  by_contra hcon
  push Not at hcon
  have hgt : A < ftTau a r (n - 1) θ * Real.cos θ := by
    rw [div_lt_iff₀ hcos] at hcon
    linarith
  have hsmall : ∀ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ < π / 2 := by
    intro k
    have hak : a k < ftTau a r (n - 1) θ * Real.cos θ := lt_of_le_of_lt (hA k) hgt
    have hpos : 0 < Real.cos θ / Real.sin θ - a k / (ftTau a r (n - 1) θ * Real.sin θ) := by
      rw [sub_pos, div_lt_div_iff₀ (mul_pos hτ hsin) hsin]
      nlinarith
    have := ftArccot_strictAnti hpos
    rw [show ftArccot 0 = π / 2 by simp [ftArccot]] at this
    exact this
  have hsum : ∑ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ = r * θ + ((n - 1 : ℕ) : ℝ) * π :=
    ftAngleSum_ftTau h
  have hlt : ∑ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ < (n : ℝ) * (π / 2) := by
    have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 (by omega))
    have := Finset.sum_lt_sum_of_nonempty hne fun k (_ : k ∈ Finset.univ) => hsmall k
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hnge : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  rw [hsum, hn1] at hlt
  have hr0 : (0 : ℝ) ≤ r * θ := by positivity
  nlinarith

/-- **The endpoint limit of `Forgacs2017RationalDenominator` Lemma 6.**  In their
`τ(θ)` converges as `θ → 0⁺` to a positive zero of the critical
polynomial — the point their Lemma 6 calls `t_a`.  Monotonicity supplies the
convergence, `ftTau_le_div_cos` the bound, and
`eval_ftCriticalReal_eq_zero_of_tendsto` the identification. -/
theorem exists_tendsto_ftTau_nhdsGT_zero {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hne : ¬(r = 1 ∧ n = 2)) (c : ℝ) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0 := by
  have hn : 0 < n := by omega
  have hπ := pi_pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set δ : ℝ := min (π / (2 * r)) (π / 3) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ3 : δ ≤ π / 3 := min_le_right _ _
  have hδr : δ < π / r :=
    lt_of_le_of_lt (min_le_left _ _) (div_lt_div_of_pos_left hπ hr0 (by linarith))
  have harc : ∀ θ ∈ Ioo (0 : ℝ) δ, θ ∈ Ioo (0 : ℝ) (π / r) :=
    fun θ hθ => ⟨hθ.1, lt_trans hθ.2 hδr⟩
  have hb : ∀ θ ∈ Ioo (0 : ℝ) δ, FTBranchAt a r (n - 1) θ := fun θ hθ =>
    ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) (harc θ hθ)
  set A : ℝ := ∑ k, a k with hAdef
  have hA : ∀ k, a k ≤ A :=
    fun k => Finset.single_le_sum (f := a) (fun i _ => (ha i).le) (Finset.mem_univ k)
  have hApos : 0 < A :=
    Finset.sum_pos (fun k _ => ha k) (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  have hmid : δ / 2 ∈ Ioo (0 : ℝ) δ := ⟨by linarith, by linarith⟩
  have hbdd : BddAbove (ftTau a r (n - 1) '' Ioo (0 : ℝ) δ) := by
    refine ⟨2 * A, ?_⟩
    rintro y ⟨θ, hθ, rfl⟩
    have hθ3 : θ < π / 3 := lt_of_lt_of_le hθ.2 hδ3
    have hcos : (1 : ℝ) / 2 < Real.cos θ := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le (by linarith) hθ3
      rwa [Real.cos_pi_div_three] at this
    have hle := ftTau_le_div_cos hn2 ha hA hθ.1 (by linarith) (hb θ hθ)
    have : A / Real.cos θ ≤ 2 * A := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hanti : AntitoneOn (ftTau a r (n - 1)) (Ioo (0 : ℝ) δ) := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with hEq | hLt
    · rw [hEq]
    · exact le_of_lt (ftTau_strictAnti hn ha hr hne (ftTau_pos (hb x hx))
        (ftTau_pos (hb y hy)) hx.1 hLt (lt_trans hy.2 hδr)
        (ftAngleSum_ftTau (hb x hx)) (ftAngleSum_ftTau (hb y hy)))
  have htend := hanti.tendsto_nhdsWithin_Ioo_right ⟨δ / 2, hmid⟩ hbdd
  refine ⟨_, ?_, htend, ?_⟩
  · exact lt_of_lt_of_le (ftTau_pos (hb _ hmid))
      (le_csSup hbdd (Set.mem_image_of_mem _ hmid))
  · refine eval_ftCriticalReal_eq_zero_of_tendsto le_rfl ?_ htend
    filter_upwards [Ioo_mem_nhdsGT hδpos] with θ hθ
    exact ftPencilIm_eq_zero c ha (ftArc_subset hr (harc θ hθ)) (hb θ hθ)

/-! ### The limit without monotonicity

`exists_tendsto_ftTau_nhdsGT_zero` above buys convergence from
`Forgacs2017RationalDenominator` Lemma 3.  This route buys it without: only the
strict monotonicity in `τ` and the intermediate value theorem are used, so it
does not carry the exclusion `(r, n) ≠ (1, 2)` either.  Monotonicity is only
being used to
force a single cluster point, and that follows instead from the intermediate
value theorem: `E` has finitely many zeros, every cluster point is one of them,
and a continuous function cannot cluster at two values without clustering at
every value between.  Nothing here uses Lemma 3. -/

/-- Every cluster point of the radius is a zero of the critical polynomial. -/
theorem eval_ftCriticalReal_eq_zero_of_mapClusterPt {P : Polynomial ℝ} {r : ℕ} {T : ℝ → ℝ}
    {x : ℝ} (hzero : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftPencilIm P r (T θ) θ = 0)
    (hx : MapClusterPt x (𝓝[>] (0 : ℝ)) T) : (ftCriticalReal P r).eval x = 0 := by
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) ⊓ Filter.comap T (𝓝 x) with hldef
  have hne : l.NeBot := by
    rw [hldef, Filter.inf_neBot_iff]
    intro s hs t ht
    obtain ⟨u, hu, hut⟩ := ht
    obtain ⟨θ, hθs, hθu⟩ := (Filter.frequently_iff.1 (mapClusterPt_iff_frequently.1 hx u hu)) hs
    exact ⟨θ, hθs, hut hθu⟩
  have hle : l ≤ 𝓝[>] (0 : ℝ) := inf_le_left
  have hT : Tendsto T l (𝓝 x) :=
    le_trans (Filter.map_mono inf_le_right) Filter.map_comap_le
  exact eval_ftCriticalReal_eq_zero_of_tendsto (l := l) hle hzero hT

/-- **The intermediate value step.**  A function continuous near `0⁺` that clusters
at two values clusters at every value between them. -/
theorem mapClusterPt_of_mem_Ioo {T : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn T (Ioo 0 δ)) {x₁ x₂ y : ℝ}
    (h1 : MapClusterPt x₁ (𝓝[>] (0 : ℝ)) T) (h2 : MapClusterPt x₂ (𝓝[>] (0 : ℝ)) T)
    (hy : y ∈ Ioo x₁ x₂) : MapClusterPt y (𝓝[>] (0 : ℝ)) T := by
  have hfreq : ∃ᶠ θ in 𝓝[>] (0 : ℝ), T θ = y := by
    rw [Filter.frequently_iff]
    intro s hs
    obtain ⟨δ', hδ'pos, hδ'⟩ : ∃ δ' > 0, Ioo (0 : ℝ) δ' ⊆ s ∩ Ioo 0 δ :=
      mem_nhdsGT_iff_exists_Ioo_subset.1 (Filter.inter_mem hs (Ioo_mem_nhdsGT hδ))
    have hbasis : Ioo (0 : ℝ) δ' ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hδ'pos
    obtain ⟨θ₁, hθ₁mem, hθ₁⟩ :=
      (Filter.frequently_iff.1 (h1.frequently (eventually_lt_nhds hy.1))) hbasis
    obtain ⟨θ₂, hθ₂mem, hθ₂⟩ :=
      (Filter.frequently_iff.1 (h2.frequently (eventually_gt_nhds hy.2))) hbasis
    have hsub : uIcc θ₁ θ₂ ⊆ Ioo 0 δ' :=
      (Set.ordConnected_Ioo).uIcc_subset hθ₁mem hθ₂mem
    have hsub2 : uIcc θ₁ θ₂ ⊆ Ioo 0 δ := fun z hz => (hδ' (hsub hz)).2
    obtain ⟨θ₃, hθ₃mem, hθ₃⟩ := intermediate_value_uIcc (f := T) (hcont.mono hsub2)
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨hθ₁.le, hθ₂.le⟩)
    exact ⟨θ₃, (hδ' (hsub hθ₃mem)).1, hθ₃⟩
  rw [mapClusterPt_iff_frequently]
  intro u hu
  exact hfreq.mono fun θ hθ => hθ ▸ mem_of_mem_nhds hu

/-- **The endpoint limit at every `r ≥ 1`, `n ≥ 2`.**  Unlike
`exists_tendsto_ftTau_nhdsGT_zero` this carries no `(r, n) ≠ (1, 2)`, because it
does not use `Forgacs2017RationalDenominator` Lemma 3 at all. -/
theorem exists_tendsto_ftTau_nhdsGT_zero_of_two_le {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {c : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0 := by
  classical
  have hn : 0 < n := by omega
  have hπ := pi_pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set P : Polynomial ℝ := ftRootPolyReal c a with hPdef
  set δ : ℝ := min (π / (2 * r)) (π / 3) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ3 : δ ≤ π / 3 := min_le_right _ _
  have hδr : δ < π / r :=
    lt_of_le_of_lt (min_le_left _ _) (div_lt_div_of_pos_left hπ hr0 (by linarith))
  have harc : ∀ θ ∈ Ioo (0 : ℝ) δ, θ ∈ Ioo (0 : ℝ) (π / r) :=
    fun θ hθ => ⟨hθ.1, lt_trans hθ.2 hδr⟩
  have hball : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ := fun θ hθ =>
    ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ
  set A : ℝ := ∑ k, a k with hAdef
  have hA : ∀ k, a k ≤ A :=
    fun k => Finset.single_le_sum (f := a) (fun i _ => (ha i).le) (Finset.mem_univ k)
  have hApos : 0 < A :=
    Finset.sum_pos (fun k _ => ha k) (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  -- the radius stays in a compact interval near `0`
  have hmem : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftTau a r (n - 1) θ ∈ Icc 0 (2 * A) := by
    filter_upwards [Ioo_mem_nhdsGT hδpos] with θ hθ
    have hθ3 : θ < π / 3 := lt_of_lt_of_le hθ.2 hδ3
    have hcos : (1 : ℝ) / 2 < Real.cos θ := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le (by linarith) hθ3
      rwa [Real.cos_pi_div_three] at this
    have hle := ftTau_le_div_cos hn2 ha hA hθ.1 (by linarith) (hball θ (harc θ hθ))
    refine ⟨(ftTau_pos (hball θ (harc θ hθ))).le, le_trans hle ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  -- the branch equation, everywhere on the arc
  have hzero : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftPencilIm P r (ftTau a r (n - 1) θ) θ = 0 := by
    filter_upwards [Ioo_mem_nhdsGT hδpos] with θ hθ
    exact ftPencilIm_eq_zero c ha (ftArc_subset hr (harc θ hθ)) (hball θ (harc θ hθ))
  -- `E ≠ 0`, so it has finitely many zeros
  have hE0 : (ftCriticalReal P r).eval 0 ≠ 0 := by
    have hprod : 0 < ∏ k, (a k - (0 : ℝ)) := Finset.prod_pos fun k _ => by simpa using ha k
    have hev : (ftCriticalReal P r).eval 0 = -((r : ℝ) * (c * ∏ k, (a k - (0 : ℝ)))) := by
      rw [eval_ftCriticalReal, hPdef, eval_ftRootPolyReal]
      ring
    rw [hev]
    exact neg_ne_zero.2 (ne_of_gt (mul_pos hr0 (mul_pos hc hprod)))
  have hEne : ftCriticalReal P r ≠ 0 := fun h => hE0 (by rw [h]; simp)
  have hfin : Set.Finite {t : ℝ | (ftCriticalReal P r).IsRoot t} :=
    Polynomial.finite_setOfPred_isRoot hEne
  -- every cluster point is a zero of `E`; two of them would force a third
  have hcluster : ∀ x, MapClusterPt x (𝓝[>] (0 : ℝ)) (ftTau a r (n - 1)) →
      (ftCriticalReal P r).eval x = 0 := fun x hx =>
    eval_ftCriticalReal_eq_zero_of_mapClusterPt hzero hx
  have hcontOn : ContinuousOn (ftTau a r (n - 1)) (Ioo 0 δ) := fun θ hθ =>
    (continuousAt_ftTau hn ha hr (harc θ hθ) hball).continuousWithinAt
  have huniq : ∀ x₁ x₂, MapClusterPt x₁ (𝓝[>] (0 : ℝ)) (ftTau a r (n - 1)) →
      MapClusterPt x₂ (𝓝[>] (0 : ℝ)) (ftTau a r (n - 1)) → x₁ = x₂ := by
    intro x₁ x₂ h1 h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨y, hy, hyroot⟩ : ∃ y ∈ Ioo x₁ x₂, ¬ (ftCriticalReal P r).IsRoot y := by
        by_contra hall
        push Not at hall
        exact (Set.Ioo_infinite hlt) (hfin.subset hall)
      exact hyroot (hcluster y (mapClusterPt_of_mem_Ioo hδpos hcontOn h1 h2 hy))
    · obtain ⟨y, hy, hyroot⟩ : ∃ y ∈ Ioo x₂ x₁, ¬ (ftCriticalReal P r).IsRoot y := by
        by_contra hall
        push Not at hall
        exact (Set.Ioo_infinite hlt) (hfin.subset hall)
      exact hyroot (hcluster y (mapClusterPt_of_mem_Ioo hδpos hcontOn h2 h1 hy))
  -- a cluster point exists, and is unique, so the radius converges
  obtain ⟨L, hLmem, hLcl⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * A)).exists_clusterPt
    (f := Filter.map (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ))) (Filter.le_principal_iff.2 hmem)
  have htend : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * A)).tendsto_nhds_of_unique_mapClusterPt hmem
      fun x _ hxc => huniq x L hxc hLcl
  have hLroot : (ftCriticalReal P r).eval L = 0 := hcluster L hLcl
  refine ⟨L, ?_, htend, hLroot⟩
  rcases lt_or_eq_of_le hLmem.1 with h | h
  · exact h
  · exact absurd (h ▸ hLroot) hE0

/-- **Non-vacuity at `r = 1`.**  `P(t) = (1-t)(2-t)(3-t)`, `r = 1`, so `n = 3 > 2r`
and this instance needs neither `Forgacs2017RationalDenominator` Lemma 3 nor its
exclusion. -/
theorem exists_tendsto_ftTau_r_one_witness :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (ftTau (fun k : Fin 3 => (k : ℝ) + 1) 1 (3 - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      (ftCriticalReal (ftRootPolyReal 1 (fun k : Fin 3 => (k : ℝ) + 1)) 1).eval L = 0 :=
  exists_tendsto_ftTau_nhdsGT_zero_of_two_le (by norm_num) (fun k => by positivity) le_rfl one_pos

end ForgacsTran
