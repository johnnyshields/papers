/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Bridge
import CubicPochhammer.CentralProducts

/-!
# Main theorem: coefficientwise Schur-concavity of the cubic Pochhammer series

Assembles `shields-2026-cubic-pochhammer.tex`, `thm:main` (cubic coefficientwise
Schur-concavity), and its specialization to Karp–Zhang Conjecture 1.

The theorem is the **fixed-sum** statement: for `s > 0` and
`0 ≤ d₁ ≤ d₂ ≤ s/2`, the degree-`m` coefficient of

  `S(s;d₁,d₂;x) = F_f(s/2+d₁;x)F_f(s/2-d₁;x) - F_f(s/2+d₂;x)F_f(s/2-d₂;x)`

is nonnegative:

  `schur_coeff_nonneg : C_{m,w}(s/2+d₂, s/2-d₂) ≤ C_{m,w}(s/2+d₁, s/2-d₁)`.

It is proved for an arbitrary symmetric weight family increasing toward the
center, as `cor:C-schur` states it; the weights `w_k = f_k f_{m-k}` of
`eq:w-from-f` are one instance.  The generalized Turánian of `eq:Turan-def`
follows by specializing to `s = 2μ+α+β`, `d₁ = |α-β|/2`, `d₂ = (α+β)/2`:

  `turan_coeff_nonneg : 0 ≤ C_{m,f}(μ+α,μ+β) - C_{m,f}(μ,μ+α+β)`,

over the whole closure `μ, α, β ≥ 0`, the boundary cases included.  The
imbalance `d₂ = s/2` occurs exactly at `μ = 0`, and is closed by the proven
endpoint identity `cmw_right_zero`; `α = 0` closes term by term, and `β = 0` by
the proven parameter symmetry `cmw_symm`.

The proof feeds the **proven** kernel monotonicity `Kernel.gmw_monotoneOn`
(`thm:kernel`) into the Schur-concavity of the coefficient convolution,
`Bridge.cmw_schur_of_kernel` (`cor:C-schur`).

The weight hypothesis `hwmono` is the standard cross-product consequence of
log-concavity with no internal zeros (`eq:central-products`, `sec:reduction`, at the weights
`eq:w-from-f` of `sec:cubic-proof`, and the degree-local
form of `rem:local-weight`): `f_k f_{m-k}` is nondecreasing as `k` approaches
`m/2`.  `turan_coeff_nonneg` assumes that chain directly, so it is strictly wider
than `thm:main`; `turan_coeff_nonneg_of_logConcave` is `thm:main` at the paper's
own sequence hypothesis, obtained from it through
`CentralProducts.centralProducts_of_logConcave`.

Sorry-free and axiom-free.

## Main statements

* `schur_coeff_nonneg` --- `thm:main` as the fixed-sum statement: at parameter
  sum `s` and `0 ≤ d₁ ≤ d₂ ≤ s/2`, the degree-`m` coefficient decreases in the
  imbalance.
* `turan_nonneg_of_schur` --- `eq:fixed-sum` read backwards, for an arbitrary
  two-parameter function: symmetry plus fixed-sum monotonicity in the imbalance
  gives the Turánian inequality over the closed quadrant.  Multiplicity-free.
* `turan_coeff_nonneg` --- the generalized Turánian of `eq:Turan-def`, over the
  whole closure `μ, α, β ≥ 0`.
* `turan_coeff_nonneg_of_logConcave` --- the same from the paper's own sequence
  hypothesis, through `CentralProducts`.
* `cmf_delta_pos_iff_of_logConcave`, `turan_delta_pos_iff_of_logConcave` ---
  when the inequality is strict.

## References

* `shields-2026-cubic-pochhammer.tex`, `thm:main` (cubic coefficientwise
  Schur-concavity), `cor:C-schur`, `thm:kernel`, `eq:Turan-def`,
  `eq:w-from-f`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-- **Cubic coefficientwise Schur-concavity** (`thm:main`, fixed-sum form).  For
nonnegative symmetric weights nondecreasing toward the center, every degree-`m`
(`m ≥ 2`) coefficient of the fixed-sum difference `eq:schur-def` is nonnegative
on the closed range `0 ≤ d₁ ≤ d₂ ≤ s/2`:

  `C_{m,w}(s/2+d₂, s/2-d₂) ≤ C_{m,w}(s/2+d₁, s/2-d₁)`.

For `d₂ < s/2` this is Schur-concavity (`cmw_schur_of_kernel`), the two parameter
pairs sharing the sum `s` with imbalances `2d₁ ≤ 2d₂`.  The endpoint `d₂ = s/2`
falls to the proven `cmw_right_zero`: the subtracted term is identically zero
while the other is a sum of nonnegative terms. -/
theorem schur_coeff_nonneg (w : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hwnn : ∀ i, 0 ≤ w i)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (s d₁ d₂ : ℝ) (hs : 0 < s) (hd₁ : 0 ≤ d₁) (hd : d₁ ≤ d₂) (hd₂ : d₂ ≤ s / 2) :
    cmw w m (s / 2 + d₂) (s / 2 - d₂) ≤ cmw w m (s / 2 + d₁) (s / 2 - d₁) := by
  rcases eq_or_lt_of_le hd₂ with heq | hlt
  · -- the endpoint `d₂ = s/2`: the subtracted convolution vanishes
    have hzero : s / 2 - d₂ = 0 := by rw [heq]; ring
    rw [hzero, cmw_right_zero w hm]
    exact cmw_nonneg w m hwnn (by linarith) (by linarith [heq ▸ hd])
  · -- the interior: Schur-concavity at fixed parameter sum
    have hG : MonotoneOn (gmw m w) (Set.Icc 0 (1 / 2)) :=
      gmw_monotoneOn m hm w hwmono (fun i _ _ => hwnn i) hsym
    refine cmw_schur_of_kernel w m hm hwnn hsym hG (s / 2 + d₁) (s / 2 - d₁)
      (s / 2 + d₂) (s / 2 - d₂) (by linarith) (by linarith) (by linarith)
      (by linarith) (by ring) ?_
    rw [show s / 2 + d₁ - (s / 2 - d₁) = 2 * d₁ by ring,
      show s / 2 + d₂ - (s / 2 - d₂) = 2 * d₂ by ring,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * d₁),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * d₂)]
    linarith

/-- **From the fixed-sum form to the Turánian form**, `eq:fixed-sum` read
backwards.  A two-parameter function symmetric in its arguments and, at each
fixed parameter sum, nonincreasing in the imbalance satisfies the generalized
Turánian inequality of `eq:Turan-def` over the whole closed quadrant
`μ, α, β ≥ 0`.

The change of coordinates is `s = 2μ+α+β`, `d = |α-β|/2`, which puts
`(μ+α, μ+β)` at imbalance `d` and `(μ, μ+α+β)` at imbalance `(α+β)/2`; the
absolute value is what covers both orderings of `α` and `β`.  The two boundary
faces are where the parameter pairs coincide: at `α = 0` outright, at `β = 0`
after exchanging them, which is the only use of the symmetry.

Nothing here sees the multiplicity, so it serves `thm:main` at `r = 3` and
`Multiplicity/OrderTwoSchur` at `r = 2`. -/
theorem turan_nonneg_of_schur {C : ℝ → ℝ → ℝ} (hsymm : ∀ u v : ℝ, C u v = C v u)
    (hschur : ∀ s d₁ d₂ : ℝ, 0 < s → 0 ≤ d₁ → d₁ ≤ d₂ → d₂ ≤ s / 2 →
      C (s / 2 + d₂) (s / 2 - d₂) ≤ C (s / 2 + d₁) (s / 2 - d₁))
    {μ α β : ℝ} (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ C (μ + α) (μ + β) - C μ (μ + α + β) := by
  rcases eq_or_lt_of_le hα with hα0 | hα0
  · rw [← hα0, show μ + 0 = μ by ring, sub_self]
  rcases eq_or_lt_of_le hβ with hβ0 | hβ0
  · rw [← hβ0, show μ + 0 = μ by ring, show μ + α + 0 = μ + α by ring,
      hsymm μ (μ + α), sub_self]
  set s : ℝ := 2 * μ + α + β with hsdef
  have hhalf : s / 2 = μ + (α + β) / 2 := by rw [hsdef]; ring
  have hd₂ : C (s / 2 + (α + β) / 2) (s / 2 - (α + β) / 2) = C μ (μ + α + β) := by
    rw [show s / 2 + (α + β) / 2 = μ + α + β by rw [hhalf]; ring,
      show s / 2 - (α + β) / 2 = μ by rw [hhalf]; ring, hsymm]
  have hfixedSum := hschur s (|α - β| / 2) ((α + β) / 2) (by linarith) (by positivity)
    (by
      have : |α - β| ≤ α + β := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      linarith)
    (by rw [hhalf]; linarith)
  rw [hd₂] at hfixedSum
  rcases le_total β α with hle | hle
  · rw [show s / 2 + |α - β| / 2 = μ + α by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ α - β), hhalf]; ring,
      show s / 2 - |α - β| / 2 = μ + β by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ α - β), hhalf]; ring] at hfixedSum
    linarith
  · rw [show s / 2 + |α - β| / 2 = μ + β by
        rw [abs_of_nonpos (by linarith : α - β ≤ 0), hhalf]; ring,
      show s / 2 - |α - β| / 2 = μ + α by
        rw [abs_of_nonpos (by linarith : α - β ≤ 0), hhalf]; ring,
      hsymm (μ + β) (μ + α)] at hfixedSum
    linarith

/-- **Karp–Zhang Conjecture 1**, coefficientwise (`thm:main`, Turánian form).
With `f` nonnegative and its symmetric weights `w_k = f_k f_{m-k}` nondecreasing
toward the center, every degree-`m` (`m ≥ 2`) coefficient of the generalized
Turánian is nonnegative over the whole closure `μ, α, β ≥ 0`:

  `C_{m,f}(μ+α, μ+β) ≥ C_{m,f}(μ, μ+α+β)`.

The two parameter pairs share the sum `s = 2μ+α+β`; the imbalance of
`(μ+α,μ+β)` is `|α-β|`, that of `(μ,μ+α+β)` is `α+β`, and `|α-β| ≤ α+β`, so
`schur_coeff_nonneg` gives the inequality.  Where either shift vanishes the two
products coincide, by the parameter symmetry `cmw_symm`. -/
theorem turan_coeff_nonneg (f : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hfnn : ∀ r, 0 ≤ f r)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → f i * f (m - i) ≤ f j * f (m - j))
    (μ α β : ℝ) (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ cmf f m (μ + α) (μ + β) - cmf f m μ (μ + α + β) := by
  set w : ℕ → ℝ := fun k => f k * f (m - k) with hw
  have hwnn : ∀ i, 0 ≤ w i := fun i => mul_nonneg (hfnn i) (hfnn (m - i))
  have hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r) := by
    intro r hr1 hr2
    have h : m - (m - r) = r := by omega
    simp only [hw, h]
    ring
  exact turan_nonneg_of_schur (C := cmw w m) (cmw_symm w hm hsym)
    (fun s d₁ d₂ hs hd₁ hd hd₂ =>
      schur_coeff_nonneg w m hm hwnn hwmono hsym s d₁ d₂ hs hd₁ hd hd₂) hμ hα hβ

/-- **`thm:main` at the paper's own hypothesis**: `f` nonnegative, log-concave
and with no internal zeros.  `lem:central-products` turns that hypothesis into
the anti-diagonal chain `turan_coeff_nonneg` consumes, so this is the Karp–Zhang
statement as the paper states it, while `turan_coeff_nonneg` remains the wider
theorem at `rem:local-weight`'s degree-local condition. -/
theorem turan_coeff_nonneg_of_logConcave (f : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hfnn : ∀ r, 0 ≤ f r) (hlc : LogConcaveSeq f) (hint : IntervalSupport f)
    (μ α β : ℝ) (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ cmf f m (μ + α) (μ + β) - cmf f m μ (μ + α + β) :=
  turan_coeff_nonneg f m hm hfnn
    (fun i j hi hij hjm =>
      centralProducts_chain (centralProducts_of_logConcave hfnn hlc hint) m i j hi hij hjm)
    μ α β hμ hα hβ

/-! ### `cor:strict` at the paper's own sequence hypothesis -/

/-- **`cor:strict` at `thm:main`'s literal hypothesis.**  `Bridge.cmf_delta_pos_iff`
is stated at the degree-local weight chain of `rem:local-weight`, which is the
wider condition; this composes it with `centralProducts_of_logConcave` so the
exact positive support reads at the sequence hypothesis `thm:main` actually
states -- `f` nonnegative, log-concave, with no internal zeros. -/
theorem cmf_delta_pos_iff_of_logConcave (f : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hfnn : ∀ r, 0 ≤ f r) (hlc : LogConcaveSeq f) (hint : IntervalSupport f)
    {s d₁ d₂ : ℝ} (hs : 0 < s) (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂) (hd₂ : d₂ ≤ s / 2) :
    0 < cmf f m (s / 2 + d₁) (s / 2 - d₁) - cmf f m (s / 2 + d₂) (s / 2 - d₂)
      ↔ MemSumset f m :=
  cmf_delta_pos_iff f m hm hfnn
    (fun i j hi hij hjm =>
      centralProducts_chain (centralProducts_of_logConcave hfnn hlc hint) m i j hi hij hjm)
    hs hd₁ hd hd₂

/-- **`cor:strict`'s Turanian restatement at `thm:main`'s literal hypothesis.**
As `cmf_delta_pos_iff_of_logConcave`, for the shift form of `eq:Turan-def`. -/
theorem turan_delta_pos_iff_of_logConcave (f : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hfnn : ∀ r, 0 ≤ f r) (hlc : LogConcaveSeq f) (hint : IntervalSupport f)
    {μ α β : ℝ} (hμ : 0 ≤ μ) (hα : 0 < α) (hβ : 0 < β) :
    0 < cmf f m (μ + α) (μ + β) - cmf f m μ (μ + α + β) ↔ MemSumset f m :=
  turan_delta_pos_iff f m hm hfnn
    (fun i j hi hij hjm =>
      centralProducts_chain (centralProducts_of_logConcave hfnn hlc hint) m i j hi hij hjm)
    hμ hα hβ

end CubicPochhammer
