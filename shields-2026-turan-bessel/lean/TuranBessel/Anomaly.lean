/-
# The degree-one inertia transition (`lem:M1-indefinite`)

Formalizes `shields-2026-turan-bessel.tex`, §4 «Gram structure and the exceptional
matrix M₁» (`sec:gram`), Lemma 4.3 (`lem:M1-indefinite`): there is a threshold
`a✱ ∈ (0,1/2)` with `N₁` indefinite for `0 < a < a✱`, singular positive
semidefinite at `a✱`, and positive definite for `a > a✱`.

The sign is carried by
```
f(a) = (4a-1) ψ₁(a) - 4,     4a² ψ₁(a) · det N₁(a) = f(a)      (eq:det-M1),
```
so `det N₁` and `f` share a sign for `a > 0`.  Three facts give the trichotomy:

* `fM1_strictMonoOn` — `f` is strictly increasing on `(0,1/2]`.  Proved termwise
  from the defining series rather than by differentiating it: each summand
  `(4a-1)(a+n)⁻²` is strictly increasing there, and `strict_tsum_lt` lifts that to
  the sum.  This is the series form `f'(a) = 2∑(2r+1-2a)/(a+r)³` of the paper,
  used as a monotonicity statement so that no term-by-term differentiation of a
  `tsum` is needed.
* `fM1_quarter` / `fM1_half_pos` — `f(1/4) = -4 < 0` and `f(1/2) > 0`.  The second
  needs only `trigamma_gt_inv_sharp` (`ψ₁(1/2) > 4`), not the exact value `π²/2`.
* `continuousOn_trigamma` — continuity on `[1/4,1/2]`, for the intermediate value
  theorem.

The paper's decimal `a✱ = 0.3690738484…` is not formalized: it is a numerical
locator, not part of the statement.  What is proved here is existence, uniqueness,
and the inertia on each side.

Sorry-free.
-/
import TuranBessel.Gram

open Set Topology

namespace TuranBessel

variable {a b : ℝ}

/-- `f(a) = (4a-1) ψ₁(a) - 4`, the sign-carrying factor of `det N₁` (eq:det-M1). -/
noncomputable def fM1 (a : ℝ) : ℝ := (4 * a - 1) * trigamma a - 4

/-- `4a² ψ₁(a) · det N₁(a) = f(a)`: the determinant of the degree-one coefficient
matrix and `f` share a sign for `a > 0` (eq:det-M1). -/
theorem fM1_eq_det (ha : 0 < a) :
    fM1 a = 4 * a ^ 2 * trigamma a *
      (αcoef a 1 * ((trigamma a)⁻¹ + ccoef a 1) - (βcoef a 1) ^ 2) := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have hsucc : trigamma (a + 1) = trigamma a - (a⁻¹) ^ 2 := by
    have := trigamma_succ ha; linarith
  have hα : αcoef a 1 = trigamma a - (a⁻¹) ^ 2 := by
    unfold αcoef; push_cast; rw [hsucc]
  have hβ : βcoef a 1 = (2 * a - 1) / (2 * a) := by
    unfold βcoef; norm_num; ring_nf
  have hc : ccoef a 1 = 0 := by unfold ccoef; norm_num
  rw [hα, hβ, hc, fM1]
  have ha' : a ≠ 0 := ne_of_gt ha
  have hg' : trigamma a ≠ 0 := ne_of_gt hg
  field_simp
  ring

/-- Each summand of `f(a)+4 = ∑ (4a-1)(a+n)⁻²` is strictly increasing on `(0,1/2]`. -/
theorem fM1_term_lt (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2) (n : ℕ) :
    (4 * a - 1) * ((a + (n : ℝ))⁻¹ ^ 2) < (4 * b - 1) * ((b + (n : ℝ))⁻¹ ^ 2) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hb0 : 0 < b := lt_trans ha hab
  have hA : 0 < a + (n : ℝ) := by linarith
  have hB : 0 < b + (n : ℝ) := by linarith
  have hA2 : 0 < (a + (n : ℝ)) ^ 2 := by positivity
  have hB2 : 0 < (b + (n : ℝ)) ^ 2 := by positivity
  -- 4ab ≤ 2a, since b ≤ 1/2 and a > 0
  have hab2 : a * b ≤ a * (1 / 2) := mul_le_mul_of_nonneg_left hb ha.le
  -- (4b-1)(a+n)² - (4a-1)(b+n)² = (b-a)(4n² + 2n + a + b - 4ab)
  have key : 0 < 4 * (n : ℝ) ^ 2 + 2 * (n : ℝ) + a + b - 4 * a * b := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [Nat.cast_zero]
      nlinarith [hab2]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
      nlinarith [hab2, hn1]
  have expand : (4 * b - 1) * (a + (n : ℝ)) ^ 2 - (4 * a - 1) * (b + (n : ℝ)) ^ 2
      = (b - a) * (4 * (n : ℝ) ^ 2 + 2 * (n : ℝ) + a + b - 4 * a * b) := by ring
  have key2 : (4 * a - 1) * (b + (n : ℝ)) ^ 2 < (4 * b - 1) * (a + (n : ℝ)) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hab) key]
  have hPQ : (0 : ℝ) < ((a + (n : ℝ)) ^ 2 * (b + (n : ℝ)) ^ 2)⁻¹ := by positivity
  have hA2' : ((a : ℝ) + (n : ℝ)) ^ 2 ≠ 0 := ne_of_gt hA2
  have hB2' : ((b : ℝ) + (n : ℝ)) ^ 2 ≠ 0 := ne_of_gt hB2
  rw [inv_pow, inv_pow]
  calc (4 * a - 1) * ((a + (n : ℝ)) ^ 2)⁻¹
      = ((4 * a - 1) * (b + (n : ℝ)) ^ 2)
          * ((a + (n : ℝ)) ^ 2 * (b + (n : ℝ)) ^ 2)⁻¹ := by field_simp
    _ < ((4 * b - 1) * (a + (n : ℝ)) ^ 2)
          * ((a + (n : ℝ)) ^ 2 * (b + (n : ℝ)) ^ 2)⁻¹ :=
        mul_lt_mul_of_pos_right key2 hPQ
    _ = (4 * b - 1) * ((b + (n : ℝ)) ^ 2)⁻¹ := by field_simp

/-- `f` is strictly increasing on `(0, 1/2]` (the series form of `f' > 0`). -/
theorem fM1_strictMonoOn (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2) :
    fM1 a < fM1 b := by
  have hb0 : 0 < b := lt_trans ha hab
  have hsa : Summable (fun n : ℕ => (a + (n : ℝ))⁻¹ ^ 2) := trigamma_summable ha
  have hsb : Summable (fun n : ℕ => (b + (n : ℝ))⁻¹ ^ 2) := trigamma_summable hb0
  have hlt : ∑' n : ℕ, (4 * a - 1) * ((a + (n : ℝ))⁻¹ ^ 2)
           < ∑' n : ℕ, (4 * b - 1) * ((b + (n : ℝ))⁻¹ ^ 2) :=
    strict_tsum_lt 0
      (fun n => le_of_lt (fM1_term_lt ha hab hb n))
      (fM1_term_lt ha hab hb 0)
      (hsa.mul_left _) (hsb.mul_left _)
  rw [tsum_mul_left, tsum_mul_left] at hlt
  unfold fM1 trigamma
  linarith

/-- `f(1/4) = -4 < 0`. -/
theorem fM1_quarter : fM1 (1 / 4) = -4 := by
  unfold fM1; norm_num

/-- `f(1/2) > 0`, from `ψ₁(1/2) > 4` (`trigamma_gt_inv_sharp`); the exact value
`ψ₁(1/2) = π²/2` is not needed. -/
theorem fM1_half_pos : 0 < fM1 (1 / 2) := by
  have h := trigamma_gt_inv_sharp (y := (1 : ℝ) / 2) (by norm_num)
  have e1 : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
  have e2 : (((1 : ℝ) / 2) ^ 2)⁻¹ = 4 := by norm_num
  rw [e1, e2] at h
  have h4 : (4 : ℝ) < trigamma (1 / 2) := by linarith
  unfold fM1
  have hc : (4 : ℝ) * (1 / 2) - 1 = 1 := by norm_num
  rw [hc, one_mul]
  linarith

/-- For `a > 1/2` the sharp lower bound already forces `f(a) > 0`:
`f(a) > (2a-1)/(2a²) > 0`.  This carries the trichotomy past the range where the
monotonicity argument applies. -/
theorem fM1_pos_of_half_lt (ha : 1 / 2 < a) : 0 < fM1 a := by
  have ha0 : 0 < a := by linarith
  have h := trigamma_gt_inv_sharp ha0
  have h4 : 0 < 4 * a - 1 := by linarith
  have hstep : (4 * a - 1) * (a⁻¹ + (1 / 2) * (a ^ 2)⁻¹) - 4 = (2 * a - 1) / (2 * a ^ 2) := by
    have ha' : a ≠ 0 := ne_of_gt ha0
    field_simp; ring
  have hpos : 0 < (2 * a - 1) / (2 * a ^ 2) := by
    apply div_pos (by linarith) (by positivity)
  have := mul_lt_mul_of_pos_left h h4
  unfold fM1
  linarith [hstep ▸ hpos]

/-- `ψ₁` is continuous on `[1/4, 1/2]`: the defining series is dominated there by the
summable `((1/4)+n)⁻²`, so `continuousOn_tsum` applies. -/
theorem continuousOn_trigamma : ContinuousOn trigamma (Icc (1 / 4 : ℝ) (1 / 2)) := by
  have hu : Summable (fun n : ℕ => ((1 : ℝ) / 4 + (n : ℝ))⁻¹ ^ 2) :=
    trigamma_summable (by norm_num)
  refine continuousOn_tsum (u := fun n : ℕ => ((1 : ℝ) / 4 + (n : ℝ))⁻¹ ^ 2) ?_ hu ?_
  · intro n
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀
    · exact (continuous_id.add continuous_const).continuousOn
    · intro y hy
      have : (1 : ℝ) / 4 ≤ y := hy.1
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      positivity
  · intro n y hy
    have hy1 : (1 : ℝ) / 4 ≤ y := hy.1
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hq : (0 : ℝ) < 1 / 4 + (n : ℝ) := by positivity
    have hy0 : (0 : ℝ) < y + (n : ℝ) := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [inv_pow]
    apply inv_anti₀ (by positivity)
    nlinarith

/-- `f` is continuous on `[1/4, 1/2]`. -/
theorem continuousOn_fM1 : ContinuousOn fM1 (Icc (1 / 4 : ℝ) (1 / 2)) := by
  unfold fM1
  exact (((continuous_const.mul continuous_id).sub continuous_const).continuousOn.mul
    continuousOn_trigamma).sub continuousOn_const

/-- **Lemma 4.3** (`lem:M1-indefinite`), the inertia transition of the degree-one
coefficient matrix.  There is a threshold `c ∈ (1/4, 1/2)` — the paper's
`a✱ = 0.3690738484…`, whose decimal value is a locator and is not formalized — with
`N₁` indefinite below it, singular positive semidefinite at it, and positive definite
above it.  Positive definiteness holds for every `a > c`, including `a ≥ 1/2`, where
`fM1_pos_of_half_lt` supplies it in place of the monotonicity argument. -/
theorem M1_inertia_trichotomy :
    ∃ c : ℝ, 1 / 4 < c ∧ c < 1 / 2 ∧ fM1 c = 0 ∧
      (∀ x : ℝ, 0 < x → x < c → fM1 x < 0) ∧
      (∀ x : ℝ, c < x → 0 < fM1 x) := by
  -- existence, by the intermediate value theorem on [1/4, 1/2]
  have hle : (1 : ℝ) / 4 ≤ 1 / 2 := by norm_num
  have hmem : (0 : ℝ) ∈ Icc (fM1 (1 / 4)) (fM1 (1 / 2)) := by
    rw [fM1_quarter]
    exact ⟨by norm_num, le_of_lt fM1_half_pos⟩
  obtain ⟨c, hcmem, hc0⟩ :=
    intermediate_value_Icc hle continuousOn_fM1 hmem
  have hc1 : (1 : ℝ) / 4 ≤ c := hcmem.1
  have hc2 : c ≤ 1 / 2 := hcmem.2
  -- the endpoints are not roots, so c is interior
  have hc1' : (1 : ℝ) / 4 < c := by
    rcases lt_or_eq_of_le hc1 with h | h
    · exact h
    · exfalso; rw [← h] at hc0; rw [fM1_quarter] at hc0; norm_num at hc0
  have hc2' : c < 1 / 2 := by
    rcases lt_or_eq_of_le hc2 with h | h
    · exact h
    · exfalso; rw [h] at hc0; exact absurd hc0 (ne_of_gt fM1_half_pos)
  refine ⟨c, hc1', hc2', hc0, ?_, ?_⟩
  · intro x hx hxc
    have := fM1_strictMonoOn hx hxc hc2
    linarith
  · intro x hcx
    by_cases hx2 : x ≤ 1 / 2
    · have hc0' : 0 < c := by linarith
      have := fM1_strictMonoOn hc0' hcx hx2
      linarith
    · push_neg at hx2
      exact fM1_pos_of_half_lt hx2

/-- `det N₁ > 0` exactly when `f(a) > 0` (eq:det-M1). -/
theorem detN1_pos_iff (ha : 0 < a) :
    (βcoef a 1) ^ 2 < αcoef a 1 * ((trigamma a)⁻¹ + ccoef a 1) ↔ 0 < fM1 a := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have hscale : 0 < 4 * a ^ 2 * trigamma a := by positivity
  rw [fM1_eq_det ha]
  constructor
  · intro h; exact mul_pos hscale (by linarith)
  · intro h
    rcases mul_pos_iff.mp h with ⟨_, hD⟩ | ⟨hneg, _⟩
    · linarith
    · linarith

/-- Below the threshold `N₁` is not positive semidefinite: its determinant is
negative while its `(1,1)` entry is positive, so it is indefinite. -/
theorem Nmat_one_not_psd (ha : 0 < a) (hf : fM1 a < 0) : ¬ SymMat.PSD (Nmat a 1) := by
  intro hpsd
  have hg : 0 < trigamma a := trigamma_pos ha
  have hscale : 0 < 4 * a ^ 2 * trigamma a := by positivity
  have hdet : (βcoef a 1) ^ 2 ≤ αcoef a 1 * ((trigamma a)⁻¹ + ccoef a 1) := hpsd.2.2
  rw [fM1_eq_det ha] at hf
  have hD : 0 ≤ αcoef a 1 * ((trigamma a)⁻¹ + ccoef a 1) - (βcoef a 1) ^ 2 := by linarith
  nlinarith [mul_nonneg hscale.le hD]

/-- Above the threshold `N₁` is positive definite. -/
theorem Nmat_one_pd_of_fM1_pos (ha : 0 < a) (hf : 0 < fM1 a) : SymMat.PD (Nmat a 1) :=
  ⟨αcoef_pos ha 1, (detN1_pos_iff ha).mpr hf⟩

end TuranBessel
