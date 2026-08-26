/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Multiplicity.CentralSlope
import CubicPochhammer.Multiplicity.OrderTwoSchur

/-!
# The classification: universality holds exactly at `r ≤ 3`

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp
multiplicity threshold»: `prop:multiplicity-threshold` and `cor:multiplicity`.

The two halves meet here.  `UniversalLogConcave r` says every degree-`m`
coefficient of the generalized Turánian of `F_{f,r}` is nonnegative for every
log-concave sequence with no internal zeros; `r = 2` is `turan2_coeff_nonneg`
and `r = 3` is `Main.turan_coeff_nonneg`, while `r ≥ 4` fails on the two-term
sequence in degree three, which `twoTerm_degreeThree_neg_iff` prices exactly.

`gmwr` carries the residue kernel at an arbitrary multiplicity so that the two
proven cases and the failing ones are statements about one object;
`ghat_eq_gmwr` and `ghat_two_eq_gmw2` identify it with the degree-three kernel
of `CentralSlope`, so the central slope computed there is a slope of the object
the monotonicity theorems are about.

## Main definitions

* `gmwr` --- the residue kernel `eq:G-weighted` at an arbitrary multiplicity.
* `UniversalLogConcave` --- universal coefficientwise log-concavity at
  multiplicity `r`.

## Main statements

* `ghat_two_eq_gmw2`, `ghat_eq_gmwr` --- the degree-three kernel of
  `CentralSlope` is the residue kernel at `m = 3` with unit weights.
* `universalLogConcave_two`, `universalLogConcave_three` --- the two cases that
  hold.
* `not_universalLogConcave_of_four_le` --- the failure at `r ≥ 4`, witnessed by
  `twoTerm`.
* `multiplicity_classification` --- `prop:multiplicity-threshold` and
  `cor:multiplicity`: `UniversalLogConcave r ↔ r ≤ 3`.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp multiplicity
  threshold»: `prop:multiplicity-threshold`, `cor:multiplicity`,
  `eq:r-degree-three`, `eq:r-central-slope`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-- The degree-three kernel of `prop:multiplicity-threshold` at `r = 2` is the
`r = 2` residue kernel at `m = 3` with unit weights, so the `+1/2` central slope
of `ghat_central_slope_two` is a slope of the object `gmw2_monotoneOn` proves
monotone. -/
theorem ghat_two_eq_gmw2 (p : ℝ) : ghat 2 (p * (1 - p)) = gmw2 3 (fun _ => 1) p := by
  rw [ghat_eq, gmw2, show Finset.Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) from by decide,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  norm_num [Nat.choose]
  ring

/-! ### The degree-three kernel at every multiplicity -/

/-- The residue kernel `eq:G-weighted` at an arbitrary multiplicity `r`;
`gmwr 3` is `Kernel.gmw` and `gmwr 2` is `gmw2`. -/
noncomputable def gmwr (r m : ℕ) (w : ℕ → ℝ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (m - 1),
    w k * (Nat.choose (r * m - 2) (r * k - 1) : ℝ) * p ^ (r * k) * (1 - p) ^ (r * (m - k))

theorem gmwr_three (m : ℕ) (w : ℕ → ℝ) (p : ℝ) : gmwr 3 m w p = gmw m w p := rfl

theorem gmwr_two (m : ℕ) (w : ℕ → ℝ) (p : ℝ) : gmwr 2 m w p = gmw2 m w p := rfl

/-- **The first display of `prop:multiplicity-threshold`, for every `r ≥ 2`**:
the degree-three constant-weight kernel is
`binom(3r-2,r-1)[p(1-p)]^r(p^r+(1-p)^r)`.

At `m = 3` only the residues `k = 1, 2` occur, their binomials coincide by
`C(3r-2,2r-1) = C(3r-2,r-1)`, and the two monomials share the factor
`[p(1-p)]^r`.  So `ghat` is not a second formula that happens to agree with the
kernel — it is the kernel, at every multiplicity, which is what lets
`eq:r-central-slope` be read off it. -/
theorem ghat_eq_gmwr {r : ℕ} (hr : 2 ≤ r) (p : ℝ) :
    ghat r (p * (1 - p)) = gmwr r 3 (fun _ => 1) p := by
  rw [ghat_eq, gmwr, show Finset.Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) from by decide,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  have hchoose : Nat.choose (r * 3 - 2) (r * 2 - 1) = Nat.choose (r * 3 - 2) (r * 1 - 1) := by
    have hle : r * 2 - 1 ≤ r * 3 - 2 := by omega
    have hsub : r * 3 - 2 - (r * 2 - 1) = r * 1 - 1 := by omega
    rw [← hsub, Nat.choose_symm hle]
  rw [hchoose, show r * 3 - 2 = 3 * r - 2 from by omega, show r * 1 - 1 = r - 1 from by omega,
    show r * 1 = r from by omega, show r * 2 = 2 * r from by omega]
  have hp2 : p ^ (2 * r) = p ^ r * p ^ r := by rw [two_mul, pow_add]
  have hq2 : (1 - p) ^ (2 * r) = (1 - p) ^ r * (1 - p) ^ r := by rw [two_mul, pow_add]
  rw [mul_pow, hp2, hq2]
  ring

/-! ### `cor:multiplicity` -/

/-- Universal coefficientwise log-concavity at multiplicity `r`: every degree-`m`
coefficient of the generalized Turánian of `F_{f,r}` is nonnegative, for every
nonnegative log-concave sequence with no internal zeros. -/
def UniversalLogConcave (r : ℕ) : Prop :=
  ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → LogConcaveSeq f → IntervalSupport f →
    ∀ m : ℕ, 2 ≤ m → ∀ μ α β : ℝ, 0 ≤ μ → 0 ≤ α → 0 ≤ β →
      0 ≤ cmfr r f m (μ + α) (μ + β) - cmfr r f m μ (μ + α + β)

/-- **`r = 2` holds**, proved here rather than cited. -/
theorem universalLogConcave_two : UniversalLogConcave 2 := by
  intro f hfnn hlc hint m hm μ α β hμ hα hβ
  exact turan2_coeff_nonneg f m hm hfnn
    (fun i j hi hij hjm =>
      centralProducts_chain (centralProducts_of_logConcave hfnn hlc hint) m i j hi hij hjm)
    μ α β hμ hα hβ

/-- **`r = 3` holds**, which is `thm:main`. -/
theorem universalLogConcave_three : UniversalLogConcave 3 := by
  intro f hfnn hlc hint m hm μ α β hμ hα hβ
  rw [cmfr_three, cmfr_three]
  exact turan_coeff_nonneg_of_logConcave f m hm hfnn hlc hint μ α β hμ hα hβ

theorem twoTerm_logConcaveSeq : LogConcaveSeq twoTerm := by
  intro j hj
  rw [twoTerm_eq_zero (by omega : 3 ≤ j + 2), mul_zero]
  exact mul_self_nonneg _

theorem twoTerm_intervalSupport : IntervalSupport twoTerm := by
  intro a b c ha hab hbc hpa hpc
  have hA : a = 1 ∨ a = 2 := by
    by_contra h
    rw [twoTerm_eq_zero (by omega : 3 ≤ a)] at hpa
    exact lt_irrefl 0 hpa
  have hC : c = 1 ∨ c = 2 := by
    by_contra h
    rw [twoTerm_eq_zero (by omega : 3 ≤ c)] at hpc
    exact lt_irrefl 0 hpc
  have hB : b = 1 ∨ b = 2 := by omega
  rcases hB with h | h <;> rw [h] <;> norm_num

/-- **`r ≥ 4` fails**, unconditionally: the two-term sequence of
`eq:r-degree-three` satisfies every sequence hypothesis, and its degree-three
coefficient is negative once `μ > 4r/(r-3)`. -/
theorem not_universalLogConcave_of_four_le {r : ℕ} (hr : 4 ≤ r) :
    ¬ UniversalLogConcave r := by
  intro h
  have hr3 : (3 : ℝ) < (r : ℝ) := by
    have : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  set μ : ℝ := 4 * (r : ℝ) / ((r : ℝ) - 3) + 1 with hμdef
  have hthr : 4 * (r : ℝ) / ((r : ℝ) - 3) < μ := by rw [hμdef]; linarith
  have hμ0 : 0 ≤ μ := by
    have : (0 : ℝ) ≤ 4 * (r : ℝ) / ((r : ℝ) - 3) :=
      div_nonneg (by linarith) (by linarith)
    rw [hμdef]; linarith
  have hpos := h twoTerm twoTerm_nonneg twoTerm_logConcaveSeq twoTerm_intervalSupport
    3 (by norm_num) μ 1 1 hμ0 zero_le_one zero_le_one
  rw [show μ + 1 + 1 = μ + 2 from by ring] at hpos
  have hneg := (twoTerm_degreeThree_neg_iff hr hμ0).mpr hthr
  linarith

/-- **`cor:multiplicity`**, the sharp multiplicity classification: for integers
`r ≥ 2`, universal coefficientwise log-concavity of `F_{f,r}` holds exactly for
`r ∈ {2,3}`.

Unconditional.  The `r = 3` case is `thm:main`; the `r ≥ 4` case is the
degree-three counterexample of `prop:multiplicity-threshold`; and the `r = 2`
case, which the paper cites from Karp–Zhang, is `universalLogConcave_two`,
proved here by the `r = 2` kernel route. -/
theorem multiplicity_classification {r : ℕ} (hr : 2 ≤ r) :
    UniversalLogConcave r ↔ (r = 2 ∨ r = 3) := by
  constructor
  · intro h
    by_contra hne
    exact not_universalLogConcave_of_four_le (by omega) h
  · intro h
    rcases h with h | h
    · rw [h]; exact universalLogConcave_two
    · rw [h]; exact universalLogConcave_three

end CubicPochhammer
