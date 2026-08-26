/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchUpper
import ForgacsTran.DominanceFT

/-!
# The upper-endpoint datum cannot be nonzero, at any `r ≥ 2`

`DominanceFT.ftPrincipalAmp_lower_bound` takes the endpoint pair

  `hγ0₁ : ftPrincipal τ (b - 0) = te₁`   and   `hte₁ : te₁ ≠ 0`

at `b = π/r`, together with `hγd₁`, a one-sided derivative of
`δ ↦ ftPrincipal τ (b - δ)` at `0`.  **Those three are jointly contradictory for
every `r ≥ 2`**, and this module proves it once rather than at one pencil at a
time: `hγd₁` supplies continuity from the left, `tendsto_ftTau_nhdsLT_upper`
supplies `τ → 0`, and the two force `te₁ = 0`.

The binder is asking for the negation of the phenomenon it describes.  At
`r ≥ 2` the whole content of the upper endpoint is that the radius collapses, so
requiring the principal point to be nonzero *at* the endpoint cannot be met by
any branch — including by a witness with `n ≥ 2`, which is what
`exists_bound_ftTau_upper` is otherwise waiting for.

**`r = 1` is not covered and is not a gap.**  There the arc ends at `π`, the
collapse fails, and `τ` tends to a finite positive limit, so the pair is
satisfiable; `FTBranchUpper`'s header records that.  The refutation's range is
exactly the collapse's range.

## Main statements

* `tendsto_sub_nhdsGT_zero` — the chart `δ ↦ b - δ` carries `0⁺` to `b⁻`.
* `ftPrincipal_upper_endpoint_eq_zero` — a one-sided derivative at the upper
  endpoint forces the principal point there to be `0`, for every `r ≥ 2`.
* `not_upper_endpoint_datum_ne_zero` — **the refutation**: `hγ0₁`, `hγd₁` and
  `hte₁` cannot hold together at any pencil with `r ≥ 2`.

## Implementation notes

### The escape that is worse than the refutation

`ftTau` itself is **not** continuous at `b`, so instantiating the binder at
`ftTau` appears to satisfy `hte₁`.  It does, and the value is meaningless:

* `FTBranchAt a r (n-1) (π/r)` asks for `∑ θ_k = r(π/r) + (n-1)π = nπ`;
* `ftAngle_lt_pi` bounds every angle by `π` with **no hypotheses at all**, so
  `n` angles sum to strictly less than `nπ` and no `τ > 0` solves it;
* `FTBranchAt` is therefore false at `b`, and `ftTau = dite … else 1` returns
  the placeholder `1`, whence `ftPrincipal ftTau b = exp(b·I) ≠ 0`.

`FTBranchFunction`'s own note — *"off the arc the value is junk; every statement
about it carries `FTBranchAt`"* — is the safeguard this defeats, because `hγ0₁`
and `hte₁` are a pair that does not carry `FTBranchAt`, evaluated exactly where
the arc ends.  A composition closed that way would be green and would rest on a
total function's placeholder.  It is not a repair.

### A pencil where the collapse and the rate are both visible

`Q(t) = (1-t)(2-t)` at `r = 2` is the smallest instance **inside** these
hypotheses -- `n = 2` and `r = 2`, where `Q(t) = 1 - t` has `n = 1` and is
outside them.  Solving the angle sum by bisection, with `δ = π/2 - θ`:

|      `δ` |                     `τ` |   `τ/δ` |
|---------:|------------------------:|--------:|
|    `0.3` |   `0.3940269422151194`  | `1.313` |
|   `0.03` |   `0.0399940002699942`  | `1.3331`|
|  `0.001` |   `0.0013333331111111`  | `1.3333`|
| `0.0003` |   `0.0003999999940000`  | `1.3333`|

`τ → 0`, so `ftPrincipal τ (π/2) = 0` and the datum is refuted here too.  The
ratio settles at `4/3`, which is `tendsto_ftTau_div_nhdsLT_upper`'s constant
`r/(sin(π/r)·∑1/a_k)` at `∑1/a_k = 1 + 1/2 = 3/2`.  **This pencil can see the
`∑1/a_k`**: without it the constant would read `r/sin(π/r) = 2`, and the two
differ by exactly that factor.  A pencil with `∑1/a_k = 1` cannot distinguish
them, which is why one is chosen here that does not.

**Differs from the paper's route.**  The paper states the upper-endpoint
expansion under `r > 1` and does not evaluate the principal point at the
endpoint; nothing here contradicts it.  What is refuted is a Lean binder.

Sorry-free.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair dominance and the
  fixed-numerator theorem» — `thm:weighted-dominance`.

## Tags

upper endpoint, branch radius, refutation, principal point
-/

namespace ForgacsTran

open Real Set Filter Topology

/-- The chart `δ ↦ b - δ` carries `0⁺` to `b⁻`. -/
theorem tendsto_sub_nhdsGT_zero {b : ℝ} :
    Tendsto (fun δ : ℝ => b - δ) (𝓝[>] (0 : ℝ)) (𝓝[<] b) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hc : Tendsto (fun δ : ℝ => b - δ) (𝓝 0) (𝓝 (b - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    rw [sub_zero] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mem_Iio.2 (by linarith [mem_Ioi.1 hδ])

/-- **The endpoint datum is zero, for every `r ≥ 2`.**  A one-sided derivative
of `δ ↦ ftPrincipal τ (b - δ)` at `0` forces continuity from the left, and the
radius collapses there, so the value at `b` is `0` — refuting `hte₁`. -/
theorem ftPrincipal_upper_endpoint_eq_zero {n r : ℕ} {a : Fin n → ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) {τ : ℝ → ℝ}
    (hagree : ∀ θ ∈ Ioo 0 (π / r), τ θ = ftTau a r (n - 1) θ)
    {γe₁ : ℂ}
    (hγd₁ : HasDerivWithinAt (fun δ => ftPrincipal τ (π / r - δ)) γe₁ (Set.Ici 0) 0) :
    ftPrincipal τ (π / r - 0) = 0 := by
  have hπ : 0 < π := pi_pos
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  -- the one-sided derivative gives continuity, hence a limit along `0⁺`
  have hsub : l ≤ 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) :=
    nhdsWithin_mono _ (fun x hx => le_of_lt (mem_Ioi.1 hx))
  have hcont : Tendsto (fun δ => ftPrincipal τ (π / r - δ)) l
      (𝓝 (ftPrincipal τ (π / r - 0))) :=
    (hγd₁.continuousWithinAt.tendsto).mono_left hsub
  -- along the same filter the branch collapses, so the limit is `0`
  have hT : Tendsto (fun δ : ℝ => ftTau a r (n - 1) (π / r - δ)) l (𝓝 0) :=
    (tendsto_ftTau_nhdsLT_upper hn2 ha hr).comp tendsto_sub_nhdsGT_zero
  have hTC : Tendsto (fun δ : ℝ => ((ftTau a r (n - 1) (π / r - δ) : ℝ) : ℂ)) l (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hT
    rw [Function.comp_def] at h
    simpa using h
  have hexp : Tendsto (fun δ : ℝ => Complex.exp (((π / r - δ : ℝ) : ℂ) * Complex.I)) l
      (𝓝 (Complex.exp (((π / r : ℝ) : ℂ) * Complex.I))) := by
    have hc : Continuous fun δ : ℝ =>
        Complex.exp (((π / r - δ : ℝ) : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul
          continuous_const)
    have h0 := hc.tendsto 0
    rw [sub_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun δ => ftPrincipal τ (π / r - δ)) l (𝓝 0) := by
    have hmul := hTC.mul hexp
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (div_pos hπ hr0)] with δ hδ hδ2
    have hδ0 : (0 : ℝ) < δ := hδ
    have hmem : π / r - δ ∈ Ioo 0 (π / r) := ⟨by linarith [hδ2.2], by linarith⟩
    rw [ftPrincipal, hagree _ hmem]
  exact tendsto_nhds_unique hcont hzero

/-- **The refutation.**  `hγ0₁`, `hγd₁` and `hte₁` cannot hold together at any
`r ≥ 2` for a `τ` that is the branch on the arc. -/
theorem not_upper_endpoint_datum_ne_zero {n r : ℕ} {a : Fin n → ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) {τ : ℝ → ℝ}
    (hagree : ∀ θ ∈ Ioo 0 (π / r), τ θ = ftTau a r (n - 1) θ)
    {te₁ γe₁ : ℂ}
    (hγd₁ : HasDerivWithinAt (fun δ => ftPrincipal τ (π / r - δ)) γe₁ (Set.Ici 0) 0)
    (hγ0₁ : ftPrincipal τ (π / r - 0) = te₁) :
    te₁ = 0 := by
  rw [← hγ0₁]
  exact ftPrincipal_upper_endpoint_eq_zero hn2 ha hr hagree hγd₁

end ForgacsTran
