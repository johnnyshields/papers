/-
# Main theorem: coefficientwise log-concavity of the cubic Pochhammer series

Assembles `shields-2026-cubic-pochhammer.tex`, `thm:main` (the cubic
multiple-Pochhammer theorem, `KarpZhang2024` Conjecture 1): for every
nonnegative sequence whose symmetric weights increase toward the centre and all
`μ, α, β > 0`, the degree-`m` coefficient of the generalized Turánian

  `Δ_f(μ;α,β;x) = F_f(μ+α;x)F_f(μ+β;x) - F_f(μ;x)F_f(μ+α+β;x)`

is nonnegative:

  `turan_coeff_nonneg : 0 ≤ C_{m,f}(μ+α,μ+β) - C_{m,f}(μ,μ+α+β)`.

The proof feeds the **proven** kernel monotonicity `Kernel.Jmw_nonneg` into the
Schur-concavity bridge `C_schur_of_kernel` (`prop:C-schur`) and reads off the
imbalance comparison `|α-β| ≤ α+β`.

The weight hypothesis `hwmono` is the standard cross-product consequence of
log-concavity with no internal zeros (`eq:w-from-f`, §2): `f_k f_{m-k}` is
nondecreasing as `k` approaches `m/2`.

Sorry-free.  Uses `C_schur_of_kernel` (§2,§3,§5) and, transitively, the §4
bridges `block_certificate` and `Jm_bernstein`.
-/
import CubicPochhammer.Bridge

open scoped BigOperators

namespace CubicPochhammer

/-- **Cubic multiple-Pochhammer theorem** (`thm:main`).  With `f` nonnegative and
its symmetric weights `w_k = f_k f_{m-k}` nondecreasing toward the centre, every
degree-`m` (`m ≥ 2`) coefficient of the generalized Turánian is nonnegative for
`μ, α, β > 0`:

  `C_{m,f}(μ+α, μ+β) ≥ C_{m,f}(μ, μ+α+β)`.

The two parameter pairs share the sum `2μ+α+β`; the imbalance of `(μ+α,μ+β)` is
`|α-β|`, that of `(μ,μ+α+β)` is `α+β`, and `|α-β| ≤ α+β`, so Schur-concavity
(`C_schur_of_kernel`) gives the inequality. -/
theorem turan_coeff_nonneg (f : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hfnn : ∀ r, 0 ≤ f r)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → f i * f (m - i) ≤ f j * f (m - j))
    (μ α β : ℝ) (hμ : 0 < μ) (hα : 0 < α) (hβ : 0 < β) :
    0 ≤ Cmf f m (μ + α) (μ + β) - Cmf f m μ (μ + α + β) := by
  have hker : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ Jmw m (fun r => f r * f (m - r)) t := by
    intro t ht0 ht1
    exact Jmw_nonneg m hm (fun r => f r * f (m - r))
      (fun i j hi hij hj => hwmono i j hi hij hj)
      (fun i _ _ => mul_nonneg (hfnn i) (hfnn (m - i)))
      (fun r _ hr2 => by
        show f r * f (m - r) = f (m - r) * f (m - (m - r))
        have h : m - (m - r) = r := by omega
        rw [h]; ring)
      t ht0 ht1
  have himb : |(μ + α) - (μ + β)| ≤ |μ - (μ + α + β)| := by
    rw [show (μ + α) - (μ + β) = α - β by ring, show μ - (μ + α + β) = -(α + β) by ring,
      abs_neg, abs_of_pos (by linarith : (0 : ℝ) < α + β), abs_le]
    constructor <;> linarith
  have key : Cmf f m μ (μ + α + β) ≤ Cmf f m (μ + α) (μ + β) :=
    C_schur_of_kernel f m hm hfnn hker (μ + α) (μ + β) μ (μ + α + β)
      (by linarith) (by linarith) hμ (by linarith) (by ring) himb
  linarith

end CubicPochhammer
