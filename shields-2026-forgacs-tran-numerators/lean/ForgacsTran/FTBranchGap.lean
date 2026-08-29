/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchLimitPoint
import ForgacsTran.PencilIndex

/-!
# The branch radius stays inside the first gap

The `k = 1` case of `lem:amplitude-divisor` needs the endpoint limit of the branch
radius to sit strictly between the two smallest zeros of the denominator.  The
lower half is a statement about `E`; the upper half, `τ < x₂`, is a statement
about the *branch*, and it is proved here.

## Main statements

* `ftAngle_lt_mid` — the branch angle at `a` sits below the midpoint `(π+θ)/2`
  exactly when `a` is inside the radius.  This is the whole mechanism: the
  midpoint is the angle at which `a = τ`.
* `ftTau_lt_of_lt` — whenever two zeros satisfy `a i < a j`, the radius stays
  below `a j` **everywhere on the arc**, not merely near the endpoint.
* `ftAngle_le_of_div_le_one_sub` — a zero strictly inside the radius closes its
  angle at rate `θ`; the twin of
  `FTBranchLimitPoint.pi_sub_ftAngle_le` for a zero strictly outside.
* `sum_pi_sub_ftAngle_ftTau` — the angle count in complement form, `∑_k (π - θ_k)
  = π - rθ`, which is the budget the individual complements share.
* `exists_tendsto_ftTau_lt_second` — the endpoint limit is then `< a j`, with
  equality excluded by `E(a j) ≠ 0` at a simple `a j`.

## Implementation notes

**Differs from the paper's route.**  `Forgacs2017RationalDenominator` locates the
limit through the critical polynomial `E`, which has zeros in the later gaps too,
so uniqueness in the first gap does not say which zero the limit is.  The bound
here never mentions `E`: it is the angle count `∑ θ_k = rθ + (n-1)π` against the
observation that `a k ≤ τ` forces `θ_k ≤ (π+θ)/2`.  Two zeros at or inside the
radius already push the sum below `rθ + (n-1)π`, so the radius cannot reach the
second zero.  No limit and no derivative enters.

Sorry-free.

## Tags

branch radius, gap, positive zeros
-/

namespace ForgacsTran

open Real Set Filter Topology Polynomial

/-- `1 - cos θ ≤ θ²/2`, from `|sin x| ≤ |x|` at the half angle. -/
theorem one_sub_cos_le_sq_div_two (θ : ℝ) : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  have hd := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hd
  have hp := Real.sin_sq_add_cos_sq (θ / 2)
  have hs : Real.sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := Real.sin_sq_le_sq
  nlinarith

/-- `(π + θ)/2` is the `ftArccot` of `(cos θ - 1)/sin θ`; equivalently
`cot((π+θ)/2) = -tan(θ/2)`. -/
theorem ftArccot_cos_sub_one_div_sin {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ftArccot ((Real.cos θ - 1) / Real.sin θ) = (π + θ) / 2 := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hu1 : 0 < θ / 2 := by linarith [hθ.1]
  have hu2 : θ / 2 < π := by linarith [hθ.2, pi_pos]
  have hsu : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi hu1 hu2
  have h2 : θ = 2 * (θ / 2) := by ring
  have hcos2 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have hd := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hd
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hsin2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have hd := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hd
    linarith
  have hcu : Real.cos (θ / 2) ≠ 0 := by
    intro h; rw [h] at hsin2; simp at hsin2; linarith
  have hmem : (π + θ) / 2 ∈ Ioo 0 π :=
    ⟨by linarith [pi_pos, hθ.1], by linarith [hθ.2, pi_pos]⟩
  refine (ftArccot_eq_of_cos_eq hmem ?_).symm
  have hhalf : (π + θ) / 2 = π / 2 + θ / 2 := by ring
  rw [hhalf, Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
    hcos2, hsin2]
  field

/-- **A zero strictly inside the radius has its angle strictly below the
midpoint.**  The midpoint `(π+θ)/2` is exactly the angle at which `a = τ`. -/
theorem ftAngle_lt_mid {a τ θ : ℝ} (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 π) (h : a < τ) :
    ftAngle a τ θ < (π + θ) / 2 := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  rw [ftAngle, ← ftArccot_cos_sub_one_div_sin hθ]
  refine ftArccot_strictAnti ?_
  have key : Real.cos θ / Real.sin θ - a / (τ * Real.sin θ)
      - (Real.cos θ - 1) / Real.sin θ = (τ - a) / (τ * Real.sin θ) := by
    field
  have hpos : 0 < (τ - a) / (τ * Real.sin θ) := div_pos (by linarith) (by positivity)
  linarith

/-- A zero at or inside the radius has its angle at or below the midpoint. -/
theorem ftAngle_le_mid {a τ θ : ℝ} (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 π) (h : a ≤ τ) :
    ftAngle a τ θ ≤ (π + θ) / 2 := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · rw [ftAngle, ← ftArccot_cos_sub_one_div_sin hθ]
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have : Real.cos θ / Real.sin θ - a / (a * Real.sin θ)
        = (Real.cos θ - 1) / Real.sin θ := by
      field_simp
    rw [this]
  · exact (ftAngle_lt_mid hτ hθ hlt).le

/-- **The radius never reaches a second zero.**  If two zeros satisfy
`a i < a j` then `τ(θ) < a j` throughout the arc.  Nothing here is asymptotic:
the bound holds at every `θ`, and no derivative or limit is used. -/
theorem ftTau_lt_of_lt {n r : ℕ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) {i j : Fin n} (hij : i ≠ j) (hlt : a i < a j) :
    ftTau a r (n - 1) θ < a j := by
  classical
  have hi := i.isLt
  have hj := j.isLt
  have hn2 : 2 ≤ n := by
    by_contra hc
    exact hij (Fin.ext (by omega))
  have hn : 0 < n := by omega
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hb : FTBranchAt a r (n - 1) θ := ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ
  set τ := ftTau a r (n - 1) θ with hτdef
  have hτ : 0 < τ := ftTau_pos hb
  by_contra hcon
  rw [not_lt] at hcon
  -- the two angles at or inside the radius
  have hAi : ftAngle (a i) τ θ < (π + θ) / 2 :=
    ftAngle_lt_mid hτ hθπ (by linarith)
  have hAj : ftAngle (a j) τ θ ≤ (π + θ) / 2 := ftAngle_le_mid hτ hθπ hcon
  have hAk : ∀ k, ftAngle (a k) τ θ < π := fun k => ftAngle_lt_pi _ _ _
  -- split the angle sum off the two distinguished indices
  have hjmem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hsplit : ftAngleSum a τ θ = ftAngle (a i) τ θ + (ftAngle (a j) τ θ
      + ∑ k ∈ (Finset.univ.erase i).erase j, ftAngle (a k) τ θ) := by
    rw [ftAngleSum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ hjmem]
  have hcard : ((Finset.univ.erase i).erase j).card = n - 2 := by
    rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hrest : ∑ k ∈ (Finset.univ.erase i).erase j, ftAngle (a k) τ θ
      ≤ ((n - 2 : ℕ) : ℝ) * π := by
    calc ∑ k ∈ (Finset.univ.erase i).erase j, ftAngle (a k) τ θ
        ≤ ∑ _k ∈ (Finset.univ.erase i).erase j, π :=
          Finset.sum_le_sum fun k _ => (hAk k).le
      _ = ((n - 2 : ℕ) : ℝ) * π := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
  -- and compare with what the branch equation forces
  have hsum : ftAngleSum a τ θ = r * θ + ((n - 1 : ℕ) : ℝ) * π := ftAngleSum_ftTau hb
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := cast_pred_eq_sub_one (by omega)
  have hc2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  rw [hc1] at hsum
  rw [hc2] at hrest
  nlinarith [hθ.1, pi_pos]

/-- The endpoint limit inherits the bound. -/
theorem le_of_tendsto_ftTau {n r : ℕ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    {i j : Fin n} (hij : i ≠ j) (hlt : a i < a j) {L : ℝ}
    (hL : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) : L ≤ a j := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  refine le_of_tendsto hL ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos pi_pos hr0)] with θ hθ
  exact (ftTau_lt_of_lt ha hr hθ hij hlt).le

/-- The derivative of `∏ (C (a k) - X)` at a root of one of its factors: every
term but that one carries the vanishing factor.

**A general fact about polynomials, filed where it was first needed**, and the
companion of `FTBranchCritical.eval_derivative_prod_sub`: that one is the
logarithmic derivative off the roots, this one the value at a root. -/
theorem eval_derivative_prod_sub_at_root {K ι : Type*} [CommRing K] [DecidableEq ι]
    (s : Finset ι) (a : ι → K) {j : ι} (hj : j ∈ s) :
    (derivative (∏ k ∈ s, (C (a k) - X))).eval (a j)
      = -∏ k ∈ s.erase j, (a k - a j) := by
  rw [← Finset.prod_erase_mul _ _ hj, derivative_mul]
  simp [eval_prod]

/-- `E` does not vanish at a **simple** zero of the denominator, so the endpoint
limit cannot be that zero. -/
theorem eval_ftCriticalReal_ne_zero_of_simple {n r : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) {j : Fin n} (hsimple : ∀ k, k ≠ j → a k ≠ a j) :
    (ftCriticalReal (ftRootPolyReal c a) r).eval (a j) ≠ 0 := by
  classical
  have hP : (ftRootPolyReal c a).eval (a j) = 0 := by
    rw [eval_ftRootPolyReal]
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (by ring))
  have hD : (derivative (ftRootPolyReal c a)).eval (a j)
      = c * -∏ k ∈ Finset.univ.erase j, (a k - a j) := by
    rw [ftRootPolyReal, derivative_mul, derivative_C]
    simp [eval_derivative_prod_sub_at_root Finset.univ a (Finset.mem_univ j)]
  rw [eval_ftCriticalReal, hP, hD]
  have hprod : ∏ k ∈ Finset.univ.erase j, (a k - a j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k hk =>
      sub_ne_zero.2 (hsimple k (Finset.mem_erase.1 hk).1)
  have := ha j
  simp only [mul_zero, sub_zero]
  exact mul_ne_zero (ne_of_gt this) (mul_ne_zero hc (neg_ne_zero.2 hprod))

/-- **The endpoint limit lies strictly below the second zero.**  With
`le_of_tendsto_ftTau` this closes the upper half of the first-gap location; the
lower half, `x₁ < t_a`, is a statement about `E` and lives with the divisor
chain.  Strictness is carried by simplicity of `a j` and nothing else. -/
theorem exists_tendsto_ftTau_lt_second {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i j : Fin n} (hij : i ≠ j) (hlt : a i < a j)
    (hsimple : ∀ k, k ≠ j → a k ≠ a j) {c : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ L < a j ∧ Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0 := by
  obtain ⟨L, hL0, hLt, hLe⟩ := exists_tendsto_ftTau_nhdsGT_zero_of_two_le hn2 ha hr hc
  refine ⟨L, hL0, ?_, hLt, hLe⟩
  rcases lt_or_eq_of_le (le_of_tendsto_ftTau ha hr hij hlt hLt) with h | h
  · exact h
  · exact absurd (h ▸ hLe) (eval_ftCriticalReal_ne_zero_of_simple (ne_of_gt hc) ha hsimple)

/-- `t/2 ≤ arctan t` on `[0,1]`: `tan x ≤ 2x` there, because `cos x ≥ 1/2`. -/
theorem half_le_arctan {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t / 2 ≤ Real.arctan t := by
  rcases eq_or_lt_of_le ht0 with rfl | ht
  · simp
  by_contra hcon
  rw [not_le] at hcon
  have hπ3 : (3 : ℝ) < π := pi_gt_three
  have h1 : Real.tan (Real.arctan t) < Real.tan (t / 2) :=
    Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two (Real.arctan_nonneg.2 ht0) (by linarith) hcon
  rw [Real.tan_arctan] at h1
  have hc : (1 : ℝ) / 2 ≤ Real.cos (t / 2) := by
    nlinarith [one_sub_cos_le_sq_div_two (t / 2)]
  have hs : Real.sin (t / 2) ≤ t / 2 := Real.sin_le (by linarith)
  have hsn : 0 ≤ Real.sin (t / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have h2 : Real.tan (t / 2) ≤ t := by
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- A lower bound on `ftArccot` matching `ftArccot_le_inv` from below. -/
theorem inv_two_mul_le_ftArccot {Y : ℝ} (hY : 1 ≤ Y) : 1 / (2 * Y) ≤ ftArccot Y := by
  have hY0 : 0 < Y := by linarith
  have h := Real.arctan_inv_of_pos hY0
  have hinv1 : Y⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; exact Or.inr hY
  have hkey := half_le_arctan (by positivity : (0:ℝ) ≤ Y⁻¹) hinv1
  rw [ftArccot, ← h]
  calc 1 / (2 * Y) = Y⁻¹ / 2 := by field_simp
    _ ≤ Real.arctan Y⁻¹ := hkey

/-- **A zero strictly inside the radius closes its angle at rate `θ`.**  If
`a/τ ≤ 1 - 2c` and `θ² ≤ c`, then `θ_a ≤ θ/c`.

The twin of `FTBranchLimitPoint.pi_sub_ftAngle_le`, which bounds the *complement*
for a zero strictly outside.  Both come from the same two facts: the `ftArccot`
argument is bounded away from `0` on the window — here `cos θ - a/τ ≥ c`, because
`1 - cos θ ≤ θ²/2 ≤ c/2` — and `ftArccot` is at most the reciprocal of its
argument. -/
theorem ftAngle_le_of_div_le_one_sub {a τ θ c : ℝ} (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 π)
    (hc : 0 < c) (hθ2 : θ ^ 2 ≤ c) (hq : a / τ ≤ 1 - 2 * c) :
    ftAngle a τ θ ≤ θ / c := by
  have hθ0 : 0 < θ := hθ.1
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsinle : Real.sin θ ≤ θ := Real.sin_le hθ.1.le
  have hnum : c ≤ Real.cos θ - a / τ := by
    have := one_sub_cos_le_sq_div_two θ
    linarith
  have hXeq : Real.cos θ / Real.sin θ - a / (τ * Real.sin θ)
      = (Real.cos θ - a / τ) / Real.sin θ := by field_simp
  have hXi : c / θ ≤ (Real.cos θ - a / τ) / Real.sin θ := by
    calc c / θ ≤ c / Real.sin θ := by gcongr
      _ ≤ (Real.cos θ - a / τ) / Real.sin θ := by gcongr
  calc ftAngle a τ θ ≤ ftArccot (c / θ) := by
        rw [ftAngle, hXeq]; exact ftArccot_strictAnti.antitone hXi
    _ ≤ (c / θ)⁻¹ := ftArccot_le_inv (by positivity)
    _ = θ / c := by rw [inv_div]

/-- **The angle count in complement form.**  `∑_k (π - θ_k) = π - rθ` on the
branch: each complement is positive, so the total is a budget the individual
complements share, and a bound on one of them bounds every other. -/
theorem sum_pi_sub_ftAngle_ftTau {n r : ℕ} {a : Fin n → ℝ} {θ : ℝ}
    (hb : FTBranchAt a r (n - 1) θ) (hn : 0 < n) :
    ∑ k, (π - ftAngle (a k) (ftTau a r (n - 1) θ) θ) = π - r * θ := by
  have hsumφ : ∑ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ
      = r * θ + ((n - 1 : ℕ) : ℝ) * π := ftAngleSum_ftTau hb
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := cast_pred_eq_sub_one (by omega)
  rw [Finset.sum_sub_distrib, hsumφ, hc1, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The endpoint limit is strictly below the second zero, with NO simplicity
hypothesis on that zero.**  `a i < L` is the lower half of the same location and
is supplied by the caller.

**Differs from the paper's route.**  The critical polynomial `E` cannot give
this: at a repeated `a j` one has `E(a j) = a j·Q'(a j) = 0`, so the
critical-point characterization does not separate `L` from `a j`.  The angle
count does.  With `a i < L` the angle at `a i` closes to `0` at rate `θ`, so the
remaining complements share less than `θ/c` of their total `π - rθ`; the
complement at `a j` is therefore `O(θ)`, which forces its `ftArccot` argument up
like `1/θ`, which forces `τ` a fixed factor below `a j`.  That bound is uniform
in `θ`, which is what upgrades `L ≤ a j` to `L < a j`. -/
theorem lt_of_tendsto_ftTau {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) {i j : Fin n} (hij : i ≠ j) {L : ℝ}
    (hL : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) (hLi : a i < L) :
    L < a j := by
  classical
  have hn : 0 < n := by omega
  have hπ : 0 < π := pi_pos
  have hπ3 : (3 : ℝ) < π := pi_gt_three
  have hai : 0 < a i := ha i
  have haj : 0 < a j := ha j
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le one_pos hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  -- one opaque constant, so nothing below has to see how it was built
  obtain ⟨K, c, hK0, hc0, hKL, hKq⟩ :
      ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ K < L ∧ ∀ t : ℝ, K ≤ t → a i / t ≤ 1 - 2 * c := by
    have hL0 : 0 < L := by linarith
    have hK0 : (0 : ℝ) < (a i + L) / 2 := by linarith
    have hKi : a i < (a i + L) / 2 := by linarith
    have hq1 : a i / ((a i + L) / 2) < 1 := (div_lt_one hK0).2 hKi
    refine ⟨(a i + L) / 2, (1 - a i / ((a i + L) / 2)) / 2, hK0, by linarith,
      by linarith, fun t ht => ?_⟩
    have ht0 : 0 < t := lt_of_lt_of_le hK0 ht
    have h := div_le_div_of_nonneg_left hai.le hK0 ht
    linarith
  have hMlt : a j / (1 + c / (2 * π)) < a j := by
    rw [div_lt_iff₀ (by positivity)]
    have : 0 < a j * (c / (2 * π)) := by positivity
    nlinarith
  refine lt_of_le_of_lt (le_of_tendsto hL ?_) hMlt
  filter_upwards [hL.eventually (eventually_gt_nhds hKL),
    Ioo_mem_nhdsGT (div_pos hπ hr0), Ioo_mem_nhdsGT (zero_lt_one' ℝ),
    Ioo_mem_nhdsGT (div_pos hc0 hπ)] with θ hTK hθarc hθ1 hθc
  obtain ⟨hθ0, hθr⟩ := hθarc
  have hθ1' : θ < 1 := hθ1.2
  have hθc' : θ < c / π := hθc.2
  have hθπc : θ * π < c := by rw [lt_div_iff₀ hπ] at hθc'; linarith
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr ⟨hθ0, hθr⟩
  have hb : FTBranchAt a r (n - 1) θ :=
    ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) ⟨hθ0, hθr⟩
  set τ : ℝ := ftTau a r (n - 1) θ with hτdef
  have hτK : K < τ := hTK
  have hτ0 : 0 < τ := lt_trans hK0 hτK
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ.2
  have hsinge : 2 / π * θ ≤ Real.sin θ := Real.mul_le_sin hθ0.le (by linarith)
  have hdiv : c / π = 2 * (c / (2 * π)) := by field_simp
  have hsq : θ ^ 2 ≤ c / π := by nlinarith
  have hcπ : c / π ≤ c := div_le_self hc0.le (by linarith)
  have hXeq : ∀ x : ℝ, Real.cos θ / Real.sin θ - x / (τ * Real.sin θ)
      = (Real.cos θ - x / τ) / Real.sin θ := by
    intro x; field_simp
  -- the angle at `a i` closes to zero at rate θ
  have hφi : ftAngle (a i) τ θ ≤ θ / c :=
    ftAngle_le_of_div_le_one_sub hτ0 hθπ hc0 (le_trans hsq hcπ) (hKq τ hτK.le)
  -- the complements sum to `π - rθ`, so the one at `a j` is `O(θ)` too
  have hψsum : ∑ k, (π - ftAngle (a k) τ θ) = π - r * θ :=
    sum_pi_sub_ftAngle_ftTau hb hn
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ π - ftAngle (a k) τ θ := fun k _ =>
    (sub_pos.2 (ftAngle_lt_pi _ _ _)).le
  have hpair : ∑ k ∈ ({i, j} : Finset (Fin n)), (π - ftAngle (a k) τ θ)
      ≤ ∑ k, (π - ftAngle (a k) τ θ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k hk _ => hnn k hk
  rw [Finset.sum_pair hij, hψsum] at hpair
  have hψj : π - ftAngle (a j) τ θ ≤ θ / c := by nlinarith
  -- so its `ftArccot` argument grows like `1/θ`
  set Y : ℝ := (a j / τ - Real.cos θ) / Real.sin θ with hY
  have hYeq : π - ftAngle (a j) τ θ = ftArccot Y := by
    rw [ftAngle, hXeq, pi_sub_ftArccot, hY, ← neg_div, neg_sub]
  have hYge1 : 1 ≤ Y := by
    by_contra hlt1
    rw [not_le] at hlt1
    have h1 : ftArccot 1 ≤ ftArccot Y := ftArccot_strictAnti.antitone hlt1.le
    have h4 : ftArccot 1 = π / 4 := by rw [ftArccot, Real.arctan_one]; ring
    rw [← hYeq, h4] at h1
    have h5 : θ / c < π / 4 := by
      rw [div_lt_div_iff₀ hc0 (by norm_num)]
      nlinarith
    linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hYbig : c / (2 * θ) ≤ Y := by
    have h1 : 1 / (2 * Y) ≤ ftArccot Y := inv_two_mul_le_ftArccot hYge1
    rw [← hYeq] at h1
    have h2 : 1 / (2 * Y) ≤ θ / c := le_trans h1 hψj
    rw [div_le_div_iff₀ (by positivity) hc0] at h2
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- which pins `τ` a fixed factor below `a j`
  have h1 : c / (2 * θ) * Real.sin θ ≤ a j / τ - Real.cos θ := by
    rw [hY, le_div_iff₀ hsin] at hYbig; exact hYbig
  have h2 : c / π ≤ c / (2 * θ) * Real.sin θ := by
    have hpos : (0 : ℝ) < c / (2 * θ) := by positivity
    calc c / π = c / (2 * θ) * (2 / π * θ) := by field_simp
      _ ≤ c / (2 * θ) * Real.sin θ := mul_le_mul_of_nonneg_left hsinge hpos.le
  have h3 : 1 - c / (2 * π) ≤ Real.cos θ := by
    have h := one_sub_cos_le_sq_div_two θ
    linarith
  have hkey : 1 + c / (2 * π) ≤ a j / τ := by linarith
  rw [le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ hτ0] at hkey
  linarith

/-- `E < 0` strictly below the smallest zero: there `Q > 0` and `Q' < 0`. -/
theorem eval_ftCriticalReal_neg_of_lt_min {n r : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (hc : 0 < c) (hr : 1 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    {t : ℝ} (ht0 : 0 < t) (hti : t < a i) :
    (ftCriticalReal (ftRootPolyReal c a) r).eval t < 0 := by
  classical
  have hpos : ∀ k, 0 < a k - t := fun k => by linarith [hmin k]
  have hQpos : 0 < (ftRootPolyReal c a).eval t := by
    rw [eval_ftRootPolyReal]
    exact mul_pos hc (Finset.prod_pos fun k _ => hpos k)
  have hD : (derivative (ftRootPolyReal c a)).eval t
      = c * (-(∑ k, 1 / (a k - t)) * ∏ k, (a k - t)) := by
    rw [ftRootPolyReal, derivative_mul, derivative_C]
    simp [eval_derivative_prod_sub Finset.univ a t fun k _ => ne_of_gt (hpos k)]
  have hDneg : (derivative (ftRootPolyReal c a)).eval t < 0 := by
    rw [hD]
    have h1 : 0 < ∑ k, 1 / (a k - t) :=
      Finset.sum_pos (fun k _ => div_pos one_pos (hpos k)) ⟨i, Finset.mem_univ i⟩
    have h2 : 0 < ∏ k, (a k - t) := Finset.prod_pos fun k _ => hpos k
    nlinarith [mul_pos (mul_pos hc h1) h2]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le one_pos hr
  rw [eval_ftCriticalReal]
  nlinarith

/-- A positive zero of `E` lies strictly above a **simple** smallest zero of the
denominator.  This is the lower half of the first-gap location. -/
theorem lt_of_eval_ftCriticalReal_eq_zero {n r : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (hc : 0 < c) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsimple : ∀ k, k ≠ i → a k ≠ a i) {L : ℝ} (hL0 : 0 < L)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0) : a i < L := by
  rcases lt_trichotomy L (a i) with h | h | h
  · exact absurd hLe (ne_of_lt (eval_ftCriticalReal_neg_of_lt_min hc hr hmin hL0 h))
  · exact absurd (h ▸ hLe) (eval_ftCriticalReal_ne_zero_of_simple (ne_of_gt hc) ha hsimple)
  · exact h

/-- **The endpoint limit lies strictly inside the first gap**, `a i < L < a j`.
The only hypothesis on the zeros is that the smallest one is simple — which is
what the `ρ = 1` case *means* — and there is **none at all on `a j`**, so a
repeated second zero is covered. -/
theorem exists_tendsto_ftTau_mem_first_gap {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i j : Fin n} (hij : i ≠ j)
    (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) {c : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, a i < L ∧ L < a j ∧ Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0 := by
  obtain ⟨L, hL0, hLt, hLe⟩ := exists_tendsto_ftTau_nhdsGT_zero_of_two_le hn2 ha hr hc
  have hlow := lt_of_eval_ftCriticalReal_eq_zero hc ha hr hmin hsimple hL0 hLe
  exact ⟨L, hlow, lt_of_tendsto_ftTau hn2 ha hr hij hLt hlow, hLt, hLe⟩

end ForgacsTran
