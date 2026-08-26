/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Amplitude

/-!
# A concrete Forgács--Tran branch: the cubic pencil

`weighted_dominance_of_branch` and `main_of_ftBranch_of_geometry` are conditional
on a long binder list and nothing instantiates them, so nothing rules out the
hypotheses being jointly unmeetable.  Three defects this session were binders
unsatisfiable at the real objects, and a per-binder check cannot see a *joint*
failure.  This module builds the data a witness needs, starting from the branch
itself.

The pencil is `Q(t) = (1-t)^3` with `r = 1` — the smallest one whose lower
endpoint cluster has a nonprincipal member, since `rQ - tQ' = (1-t)^2(1+2t)`
gives `t_a = 1` with the smallest zero of `Q` of multiplicity `ρ = 3`, and
`ρ - 2 = 1`.  The quadratic pencil is useless as a witness here: its principal
pair exhausts the denominator zeros, so every cluster binder is empty and the
witness would certify nothing about exactly the binders that were vacuous.

The branch is algebraic.  Writing `t = τe^{iθ}`, the spectral parameter
`z = -Q(t)/t` is real precisely when `2τ³cos θ = 3τ² - 1`, and then
`z = 3 - τ² - 2cos θ/τ`.  Both are polynomial identities, so the branch needs no
implicit function theorem and no root-finder — which is what makes this pencil
usable as a witness at all.

**What the witness discharges, and why that is the point.**  Every binder below
sat in the *cited-result-still-carried* column when `weighted_dominance_of_branch`'s
list was classified — carried because `z` and `τ` were free function variables, so
no theorem could discharge a hypothesis about an arbitrary `τ`.  At concrete data
each becomes a computation:

| binder | here |
|---|---|
| `hQ` | `hasRealCoeffs_cubicQ` |
| `hQ0` | `cubicQ_eval_zero_ne` |
| `hτpos₀` | `cubicTau_pos`, at every angle rather than on a window |
| `hrootplus₀` | `ftDen_cubicQ_eval_cubicTau`, with no hypotheses |
| `hrootev₀` | the same, and **two-sided** — see the note on `cubicTau` |
| `hγ0₀`, `te₀ ≠ 0` | `ftPrincipal_cubicTau_zero`, `t_e = 1 = t_a` |
| `hzmono`-shaped | `cubicTau_strictAntiOn`, their Lemma 3 |
| `hzc₀` | `continuousOn_cubicZ_complex` |

`hrootev₀` is the one to notice.  It asks for the root equation on a *two-sided*
neighborhood of the endpoint, and `ftTau`'s constant off-arc value cannot meet
it — that is the defect this file's `cubicTau` docstring records.  Here it is met.

What remains is `hexp₀`, the endpoint expansion, which is
`Forgacs2017RationalDenominator` Prop. 3 and the only piece needing analysis.

**The branch condition has two positive roots, and only one is the branch.**
Writing `t = τe^{iθ}`, the parameter `z` is real exactly when
`2τ³cos θ = 3τ² − 1`.  At `θ = 0` that is `(τ-1)²(2τ+1)`, a *double* root at
`τ = 1`, and for `θ > 0` the double root splits: one root below `1`, one above.
**Only `τ < 1` is the Forgács--Tran branch.**  There `z > 0` and `τ` really is the
minimum modulus; on the `τ > 1` root `z < 0` and the real zero is *smaller* than
the principal pair, so `thm:FT-geometry`'s minimum-modulus clause fails outright.
Measured at `θ = 0.2`: the roots are `τ = 0.898` with `z = +0.011` and smallest
modulus `0.898 = τ`, against `τ = 1.133` with `z = -0.014` and smallest modulus
`0.779 < τ`.

`existsUnique_cubicTau_Ioc` picks the branch by confining `τ` to `(0,1]`, which
is why the interval in its statement is not cosmetic.  Anyone instantiating this
pencil by solving the cubic directly has to make the same choice, and sampling
`z` instead of following the branch lands on the wrong root while still looking
plausible.

**Two radii appear in this file and they are supposed to differ.**  `Ri = 1` is
the *interior* radius on `[e, b-e]`, where `hinterior` demands **exactly two**
zeros inside — so it must sit below `1/τ²` and exclude the third.  A
*lower-endpoint* radius `R₀` on `(0, e₀]` must instead retain the **whole**
cluster, and the nonprincipal zero runs out past `1.24` across a window of width
`0.2`, so `R₀` has to exceed about `1.3`.  Different binders, different regions,
opposite requirements: `e₀` and `R₀` are not independently choosable, and
unifying the two radii would be an error rather than a tidy-up.

## Implementation notes

Sorry-free.

## References

Formalizes a witness for `../shields-2026-forgacs-tran-numerators.tex`,
`thm:FT-geometry` and `thm:weighted-dominance`, at one explicit pencil.

## Tags

witness, cubic pencil, Forgacs-Tran branch, non-vacuity
-/

namespace ForgacsTran

open Polynomial Complex

/-- The witness pencil `Q(t) = (1-t)^3`. -/
noncomputable def cubicQ : Polynomial ℂ := (1 - X) ^ 3

/-- The spectral parameter along the branch, `z = 3 - τ² - 2cos θ/τ`. -/
noncomputable def cubicZ (τ θ : ℝ) : ℝ := 3 - τ ^ 2 - 2 * Real.cos θ / τ

@[simp] theorem cubicQ_eval (t : ℂ) : cubicQ.eval t = (1 - t) ^ 3 := by
  simp [cubicQ]

theorem hasRealCoeffs_cubicQ : HasRealCoeffs cubicQ := by
  have hmap : cubicQ = ((1 - X : Polynomial ℝ) ^ 3).map (algebraMap ℝ ℂ) := by
    rw [cubicQ, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
  intro k
  rw [hmap, coeff_map]
  simp

theorem cubicQ_eval_zero_ne : cubicQ.eval 0 ≠ 0 := by simp

/-- **The branch identity.**  With `2τ³cos θ = 3τ² - 1`, the point `τe^{iθ}` is a
zero of `Q + z t` at `z = cubicZ τ θ`.  This is `eq:principal-pair` at concrete
data, and it is an algebraic identity: the branch condition is exactly what makes
`-Q(t)/t` real, and the value is then forced. -/
theorem ftDen_cubicQ_eval_principal {τ θ : ℝ} (hτ : 0 < τ)
    (hbr : 2 * Real.cos θ * τ ^ 3 = 3 * τ ^ 2 - 1) :
    (ftDen cubicQ 1 ((cubicZ τ θ : ℝ) : ℂ)).eval
      (((τ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)) = 0 := by
  have hτc : ((τ : ℝ) : ℂ) ≠ 0 := by simpa using hτ.ne'
  set E : ℂ := Complex.exp (((θ : ℝ) : ℂ) * Complex.I) with hEdef
  have hpc : ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have hE : E ^ 2 + 1 = 2 * ((Real.cos θ : ℝ) : ℂ) * E := by
    rw [hEdef, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    linear_combination ((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.I_sq - hpc
  have hbrC : 2 * ((Real.cos θ : ℝ) : ℂ) * ((τ : ℝ) : ℂ) ^ 3
      = 3 * ((τ : ℝ) : ℂ) ^ 2 - 1 := by exact_mod_cast hbr
  have hz : ((cubicZ τ θ : ℝ) : ℂ) * (((τ : ℝ) : ℂ) * E)
      = (3 * ((τ : ℝ) : ℂ) - ((τ : ℝ) : ℂ) ^ 3 - 2 * ((Real.cos θ : ℝ) : ℂ)) * E := by
    rw [cubicZ]
    push_cast
    field_simp
  rw [ftDen_eval, cubicQ_eval, pow_one, hz]
  linear_combination (1 - ((τ : ℝ) : ℂ) ^ 3 * E) * hE - E ^ 2 * hbrC

/-! ### The branch exists and is unique

`ftDen_cubicQ_eval_principal` takes the branch condition as a hypothesis.  For a
witness the condition has to be *met*, at every angle of the arc, by exactly one
`τ` — otherwise there is no branch function to feed the binders.  Both come from
one observation: `f(τ) = 2τ³cos θ - 3τ² + 1` falls strictly from `f(0) = 1` to
`f(1) = 2cos θ - 2 < 0` on `[0,1]`, because its derivative is `6τ(τcos θ - 1)`
and `τcos θ < 1` there. -/

/-- The branch polynomial, whose zero in `(0,1)` is `τ(θ)`. -/
noncomputable def cubicBranchFn (θ τ : ℝ) : ℝ := 2 * Real.cos θ * τ ^ 3 - 3 * τ ^ 2 + 1

theorem hasDerivAt_cubicBranchFn (θ τ : ℝ) :
    HasDerivAt (cubicBranchFn θ) (2 * Real.cos θ * (3 * τ ^ 2) - 3 * (2 * τ)) τ := by
  have h := (((hasDerivAt_pow 3 τ).const_mul (2 * Real.cos θ)).sub
    ((hasDerivAt_pow 2 τ).const_mul 3)).add_const 1
  change HasDerivAt (fun x : ℝ => 2 * Real.cos θ * x ^ 3 - 3 * x ^ 2 + 1) _ τ
  simpa using h

private theorem cos_lt_one_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) : Real.cos θ < 1 := by
  have h := Real.strictAntiOn_cos (Set.left_mem_Icc.2 Real.pi_pos.le)
    ⟨hθ.1.le, hθ.2.le⟩ hθ.1
  simpa using h

theorem strictAntiOn_cubicBranchFn (θ : ℝ) :
    StrictAntiOn (cubicBranchFn θ) (Set.Icc 0 1) := by
  have hcos := Real.cos_le_one θ
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 1)
    (fun x _ => ((hasDerivAt_cubicBranchFn θ x).continuousAt).continuousWithinAt)
    (fun x _ => (hasDerivAt_cubicBranchFn θ x).hasDerivWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  nlinarith [hx.1, hx.2, hcos, Real.neg_one_le_cos θ]

/-- **The branch, at every real angle.**  `f` falls strictly on `[0,1]` from
`f(0) = 1` to `f(1) = 2cos θ - 2 ≤ 0`, so there is exactly one zero in `(0,1]`
whatever `θ` is — at `θ ∈ 2πℤ` it is the endpoint `τ = 1`, which is `t_a`. -/
theorem existsUnique_cubicTau_Ioc (θ : ℝ) :
    ∃! τ : ℝ, τ ∈ Set.Ioc (0 : ℝ) 1 ∧ cubicBranchFn θ τ = 0 := by
  have hcos := Real.cos_le_one θ
  have h0 : cubicBranchFn θ 0 = 1 := by simp [cubicBranchFn]
  have h1 : cubicBranchFn θ 1 = 2 * Real.cos θ - 2 := by simp [cubicBranchFn]; ring
  have hcont : ContinuousOn (cubicBranchFn θ) (Set.Icc 0 1) := fun x _ =>
    ((hasDerivAt_cubicBranchFn θ x).continuousAt).continuousWithinAt
  obtain ⟨τ, hmem, hz⟩ : ∃ τ ∈ Set.Ioc (0 : ℝ) 1, cubicBranchFn θ τ = 0 := by
    rcases eq_or_lt_of_le hcos with heq | hlt
    · exact ⟨1, ⟨one_pos, le_rfl⟩, by rw [h1, heq]; ring⟩
    · have hmem0 : (0 : ℝ) ∈ Set.Ioo (cubicBranchFn θ 1) (cubicBranchFn θ 0) := by
        rw [h0, h1]; exact ⟨by linarith, by norm_num⟩
      obtain ⟨τ, hτmem, hτ0⟩ :=
        intermediate_value_Ioo' (by norm_num : (0:ℝ) ≤ 1) hcont hmem0
      exact ⟨τ, ⟨hτmem.1, hτmem.2.le⟩, hτ0⟩
  refine ⟨τ, ⟨hmem, hz⟩, ?_⟩
  rintro y ⟨hymem, hy0⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := strictAntiOn_cubicBranchFn θ ⟨hymem.1.le, hymem.2⟩ ⟨hmem.1.le, hmem.2⟩ h
    rw [hy0, hz] at this; exact lt_irrefl 0 this
  · have := strictAntiOn_cubicBranchFn θ ⟨hmem.1.le, hmem.2⟩ ⟨hymem.1.le, hymem.2⟩ h
    rw [hy0, hz] at this; exact lt_irrefl 0 this

/-- **The branch as a function, total on `ℝ`.**

**The off-arc value is chosen, not defaulted, and that is the point.**  Mathlib's
`ftTau` is `if h : FTBranchAt … then h.choose else 1`, a constant off the arc.
That constant is what made `weighted_dominance_of_branch`'s `hrootev₀`
unsatisfiable at the Forgács--Tran branch: the binder asks for the root equation
on a *two-sided* neighborhood of the endpoint, and the constant does not satisfy
it on the outward side, so the hypothesis could not be met by the very objects it
was written for.

Here there is no default.  The branch condition `2τ³cos θ = 3τ² - 1` and the
value `z = 3 - τ² - 2cos θ/τ` are **even in `θ`**, so the same `τ` solves it at
`-θ` as at `θ`, and the root at `τ(-θ)e^{-iθ}` is the conjugate of the one at
`τ(θ)e^{iθ}` — a root too, since the pencil is real.  `cubicTau` is therefore
defined by the condition at every real `θ`, and a two-sided binder is satisfiable
at it.

**The rule for the next branch function on a partial domain**: extend by the
symmetry the data already has, and only fall back on a default when there is
none.  A default value is not neutral — it is a claim that the object is
constant there, and any binder quantifying across the boundary will test that
claim. -/
noncomputable def cubicTau (θ : ℝ) : ℝ := (existsUnique_cubicTau_Ioc θ).choose

theorem cubicTau_spec (θ : ℝ) :
    cubicTau θ ∈ Set.Ioc (0 : ℝ) 1 ∧ cubicBranchFn θ (cubicTau θ) = 0 :=
  (existsUnique_cubicTau_Ioc θ).choose_spec.1

theorem cubicTau_pos (θ : ℝ) : 0 < cubicTau θ := (cubicTau_spec θ).1.1

theorem cubicTau_le_one (θ : ℝ) : cubicTau θ ≤ 1 := (cubicTau_spec θ).1.2

theorem cubicTau_branch (θ : ℝ) :
    2 * Real.cos θ * cubicTau θ ^ 3 - 3 * cubicTau θ ^ 2 + 1 = 0 := (cubicTau_spec θ).2

/-- `cubicTau` is even, which is what makes a two-sided binder meetable at it. -/
theorem cubicTau_neg (θ : ℝ) : cubicTau (-θ) = cubicTau θ := by
  refine ((existsUnique_cubicTau_Ioc (-θ)).choose_spec.2 (cubicTau θ)
    ⟨(cubicTau_spec θ).1, ?_⟩).symm
  have h := cubicTau_branch θ
  simpa [cubicBranchFn, Real.cos_neg] using h

/-- **`eq:principal-pair` at the witness pencil, unconditionally.**  The branch
condition is now met by construction, so the root statement no longer carries it. -/
theorem ftDen_cubicQ_eval_cubicTau (θ : ℝ) :
    (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval
      (((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)) = 0 :=
  ftDen_cubicQ_eval_principal (cubicTau_pos θ) (by linarith [cubicTau_branch θ])

/-- **The branch is well defined at every angle of the arc.**  Exactly one
`τ ∈ (0,1)` meets the branch condition, so `ftDen_cubicQ_eval_principal` applies
at every `θ ∈ (0,π)` and the witness has a branch to build on. -/
theorem existsUnique_cubicTau {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ∃! τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) 1 ∧ 2 * Real.cos θ * τ ^ 3 - 3 * τ ^ 2 + 1 = 0 := by
  have hcos := cos_lt_one_of_mem hθ
  have h0 : cubicBranchFn θ 0 = 1 := by simp [cubicBranchFn]
  have h1 : cubicBranchFn θ 1 = 2 * Real.cos θ - 2 := by simp [cubicBranchFn]; ring
  have hcont : ContinuousOn (cubicBranchFn θ) (Set.Icc 0 1) := fun x _ =>
    ((hasDerivAt_cubicBranchFn θ x).continuousAt).continuousWithinAt
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (cubicBranchFn θ 1) (cubicBranchFn θ 0) := by
    rw [h0, h1]
    exact ⟨by linarith, by norm_num⟩
  obtain ⟨τ, hτmem, hτ0⟩ := intermediate_value_Ioo' (by norm_num : (0:ℝ) ≤ 1) hcont hmem0
  refine ⟨τ, ⟨hτmem, hτ0⟩, ?_⟩
  rintro y ⟨hymem, hy0⟩
  by_contra hne
  have hyf : cubicBranchFn θ y = 0 := hy0
  rcases lt_or_gt_of_ne hne with h | h
  · have := strictAntiOn_cubicBranchFn θ ⟨hymem.1.le, hymem.2.le⟩
      ⟨hτmem.1.le, hτmem.2.le⟩ h
    rw [hyf, hτ0] at this
    exact lt_irrefl 0 this
  · have := strictAntiOn_cubicBranchFn θ ⟨hτmem.1.le, hτmem.2.le⟩
      ⟨hymem.1.le, hymem.2.le⟩ h
    rw [hyf, hτ0] at this
    exact lt_irrefl 0 this

/-! ### The lower endpoint

`t_a = 1` and `a = g(t_a) = 0` for this pencil, and both are exact values rather
than limits: the branch condition at `θ = 0` is `(τ-1)²(2τ+1) = 0`, whose only
zero in `(0,1]` is the endpoint itself.  This is `hγ0₀` — `ftPrincipal τ 0 = t_e`
— at the witness, and it pins the `a` of `eq:ab-def`. -/

/-- `τ(0) = 1 = t_a`.  The double zero of the branch polynomial at `θ = 0` is the
endpoint collision `lem:principal-endpoint-regularity` describes. -/
theorem cubicTau_zero : cubicTau 0 = 1 := by
  refine ((existsUnique_cubicTau_Ioc 0).choose_spec.2 1 ⟨⟨one_pos, le_rfl⟩, ?_⟩).symm
  simp [cubicBranchFn]
  norm_num

/-- `z(0) = 0 = a`, the lower endpoint of `I_{Q,1}` for this pencil. -/
theorem cubicZ_zero : cubicZ (cubicTau 0) 0 = 0 := by
  rw [cubicTau_zero, cubicZ]
  norm_num

/-- **`hγ0₀` at the witness.**  The principal branch reaches `t_a = 1` at the
endpoint, so the endpoint datum `te₀` is `1` and is nonzero — the two things
`weighted_dominance_of_branch` asks for before its endpoint factorization. -/
theorem ftPrincipal_cubicTau_zero :
    ((cubicTau 0 : ℝ) : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [cubicTau_zero]
  simp

/-! ### `τ` is strictly decreasing on the arc

`Forgacs2017RationalDenominator` Lemma 3, at the witness pencil, and here it
costs one sign.  The branch polynomial is strictly increasing in `cos θ` at
positive `τ` (its `cos θ`-derivative is `2τ³`) and strictly decreasing in `τ`,
so lowering `cos θ` lowers the root.  On `[0,π]` the cosine falls, so `τ` falls
with it — no derivative of `τ` is formed, which is the same route
`FTBranchMonotone` takes in general. -/

theorem cubicBranchFn_cubicTau (θ : ℝ) : cubicBranchFn θ (cubicTau θ) = 0 :=
  (cubicTau_spec θ).2

/-- **`Forgacs2017RationalDenominator` Lemma 3 at the witness.**  `τ` is strictly
decreasing on the viewing arc. -/
theorem cubicTau_strictAntiOn : StrictAntiOn cubicTau (Set.Icc 0 Real.pi) := by
  intro x hx y hy hxy
  have hcos : Real.cos y < Real.cos x := Real.strictAntiOn_cos hx hy hxy
  have hfx : cubicBranchFn x (cubicTau x) = 0 := cubicBranchFn_cubicTau x
  have hdiff : cubicBranchFn y (cubicTau x) - cubicBranchFn x (cubicTau x)
      = 2 * (Real.cos y - Real.cos x) * cubicTau x ^ 3 := by
    simp only [cubicBranchFn]; ring
  have hneg : cubicBranchFn y (cubicTau x) < 0 := by
    have hp : 0 < cubicTau x ^ 3 := pow_pos (cubicTau_pos x) 3
    nlinarith [cubicTau_pos x]
  by_contra hcon
  push Not at hcon
  have h2 : cubicBranchFn y (cubicTau y) ≤ cubicBranchFn y (cubicTau x) := by
    rcases eq_or_lt_of_le hcon with h | h
    · rw [h]
    · exact (strictAntiOn_cubicBranchFn y ⟨(cubicTau_pos x).le, cubicTau_le_one x⟩
        ⟨(cubicTau_pos y).le, cubicTau_le_one y⟩ h).le
  rw [cubicBranchFn_cubicTau y] at h2
  linarith

/-! ### `τ` and `z` are continuous

`hzc₀` asks for continuity of the spectral parameter across the closed endpoint
window.  It follows from the branch equation alone: for `a ∈ [0,1]` the sign of
`f(θ,a)` decides which side of `a` the root lies on, and `θ ↦ f(θ,a)` is
continuous, so each one-sided bound propagates to nearby angles.

**The endpoint needs the one-sided form, and that is the collision showing
itself.**  At `θ = 0` the branch polynomial is `(τ-1)²(2τ+1)`: a *double* root at
`τ = 1`, so `f(0,·)` does not change sign there and a two-sided argument
degenerates.  What replaces it is `f(θ,1) = 2cos θ - 2 < 0` for `θ ∉ 2πℤ`,
putting the root strictly below `1`, together with `f(0,1-ε) = ε²(3-2ε) > 0`
holding it above `1-ε`.  The degeneracy is the principal pair coalescing, not an
artefact of the parametrization. -/

theorem lt_cubicTau_of_pos {θ a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (h : 0 < cubicBranchFn θ a) : a < cubicTau θ := by
  by_contra hcon
  push Not at hcon
  rcases eq_or_lt_of_le hcon with heq | hlt
  · rw [← heq, cubicBranchFn_cubicTau] at h; exact lt_irrefl 0 h
  · have := strictAntiOn_cubicBranchFn θ ⟨(cubicTau_pos θ).le, cubicTau_le_one θ⟩ ha hlt
    rw [cubicBranchFn_cubicTau] at this
    linarith

theorem cubicTau_lt_of_neg {θ a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (h : cubicBranchFn θ a < 0) : cubicTau θ < a := by
  by_contra hcon
  push Not at hcon
  rcases eq_or_lt_of_le hcon with heq | hlt
  · rw [heq, cubicBranchFn_cubicTau] at h; exact lt_irrefl 0 h
  · have := strictAntiOn_cubicBranchFn θ ha ⟨(cubicTau_pos θ).le, cubicTau_le_one θ⟩ hlt
    rw [cubicBranchFn_cubicTau] at this
    linarith

private theorem continuous_cubicBranchFn_left (a : ℝ) :
    Continuous fun θ : ℝ => cubicBranchFn θ a := by
  unfold cubicBranchFn
  fun_prop

/-- **`τ` is continuous.**  Order-topology form: every strict bound on the root
at one angle propagates to nearby angles through the sign of `f`. -/
theorem continuous_cubicTau : Continuous cubicTau := by
  rw [continuous_iff_continuousAt]
  intro θ₀
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge a 0 with hneg | hpos
    · exact Filter.Eventually.of_forall fun θ => lt_of_lt_of_le hneg (cubicTau_pos θ).le
    · have hamem : a ∈ Set.Icc (0 : ℝ) 1 := ⟨hpos, le_trans ha.le (cubicTau_le_one θ₀)⟩
      have hf0 : 0 < cubicBranchFn θ₀ a := by
        have := strictAntiOn_cubicBranchFn θ₀ hamem
          ⟨(cubicTau_pos θ₀).le, cubicTau_le_one θ₀⟩ ha
        rw [cubicBranchFn_cubicTau] at this
        linarith
      have := Filter.Tendsto.eventually ((continuous_cubicBranchFn_left a).continuousAt (x := θ₀))
        (eventually_gt_nhds hf0)
      filter_upwards [this] with θ hθ
      exact lt_cubicTau_of_pos hamem hθ
  · rcases le_or_gt b 1 with hb1 | hb1
    · have hbmem : b ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans (cubicTau_pos θ₀).le hb.le, hb1⟩
      have hf0 : cubicBranchFn θ₀ b < 0 := by
        have := strictAntiOn_cubicBranchFn θ₀
          ⟨(cubicTau_pos θ₀).le, cubicTau_le_one θ₀⟩ hbmem hb
        rw [cubicBranchFn_cubicTau] at this
        linarith
      have := Filter.Tendsto.eventually ((continuous_cubicBranchFn_left b).continuousAt (x := θ₀))
        (eventually_lt_nhds hf0)
      filter_upwards [this] with θ hθ
      exact cubicTau_lt_of_neg hbmem hθ
    · exact Filter.Eventually.of_forall fun θ => lt_of_le_of_lt (cubicTau_le_one θ) hb1

/-- **`hzc₀` at the witness.**  The spectral parameter is continuous everywhere,
so in particular on every closed endpoint window. -/
theorem continuous_cubicZ_branch : Continuous fun θ : ℝ => cubicZ (cubicTau θ) θ := by
  unfold cubicZ
  exact ((continuous_const.sub (continuous_cubicTau.pow 2)).sub
    ((continuous_const.mul Real.continuous_cos).div continuous_cubicTau
      fun θ => (cubicTau_pos θ).ne'))

theorem continuousOn_cubicZ_complex (a b : ℝ) :
    ContinuousOn (fun θ : ℝ => ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)) (Set.Icc a b) :=
  (Complex.continuous_ofReal.comp continuous_cubicZ_branch).continuousOn

/-! ### On the open arc `τ < 1`

The bound `τ ≤ 1` of `cubicTau_le_one` is strict away from `2πℤ`, since
`f(θ,1) = 2cos θ - 2 < 0` there.  This is what separates the branch from the
endpoint collision, and it is the inequality a minimum-modulus statement for
this pencil rests on: Vieta makes the product of the three denominator zeros
`1`, and the principal pair multiplies to `τ²`, so the third zero is `1/τ²` and
`τ < 1/τ²` is exactly `τ³ < 1`.  The root identity for `1/τ²` is not formalized
here — see the note below. -/

/-- On the open arc `τ < 1`, since `f(θ,1) = 2cos θ - 2 < 0` there. -/
theorem cubicTau_lt_one {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) : cubicTau θ < 1 := by
  refine cubicTau_lt_of_neg ⟨by norm_num, le_rfl⟩ ?_
  have hcos := cos_lt_one_of_mem hθ
  simp only [cubicBranchFn]
  linarith

/-- The non-principal denominator zero, `1/τ²` by Vieta. -/
noncomputable def cubicThird (θ : ℝ) : ℝ := 1 / cubicTau θ ^ 2

/-- **The third root is a root.**  Cleared by hand rather than through
`field_simp`: `1 - 1/τ² = (τ²-1)/τ²`, so the whole expression is a single
fraction over `τ⁶` whose numerator is an identity over the branch condition. -/
theorem ftDen_cubicQ_eval_cubicThird (θ : ℝ) :
    (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval ((cubicThird θ : ℝ) : ℂ) = 0 := by
  have hτ : (0 : ℝ) < cubicTau θ := cubicTau_pos θ
  have hτc : ((cubicTau θ : ℝ) : ℂ) ≠ 0 := by simpa using hτ.ne'
  have hbrC : 2 * ((Real.cos θ : ℝ) : ℂ) * ((cubicTau θ : ℝ) : ℂ) ^ 3
      = 3 * ((cubicTau θ : ℝ) : ℂ) ^ 2 - 1 := by
    have h := cubicTau_branch θ
    exact_mod_cast (by linarith : 2 * Real.cos θ * cubicTau θ ^ 3 = 3 * cubicTau θ ^ 2 - 1)
  have hnum : (((cubicTau θ : ℝ) : ℂ) ^ 2 - 1) ^ 3 + 3 * ((cubicTau θ : ℝ) : ℂ) ^ 4
      - ((cubicTau θ : ℝ) : ℂ) ^ 6
      - 2 * ((Real.cos θ : ℝ) : ℂ) * ((cubicTau θ : ℝ) : ℂ) ^ 3 = 0 := by
    linear_combination -hbrC
  rw [ftDen_eval, cubicQ_eval, pow_one, cubicThird, cubicZ]
  push_cast
  rw [← Complex.ofReal_cos]
  have hsplit : ((1 : ℂ) - 1 / ((cubicTau θ : ℝ) : ℂ) ^ 2) ^ 3
      + (3 - ((cubicTau θ : ℝ) : ℂ) ^ 2
          - 2 * ((Real.cos θ : ℝ) : ℂ) / ((cubicTau θ : ℝ) : ℂ))
        * (1 / ((cubicTau θ : ℝ) : ℂ) ^ 2)
      = ((((cubicTau θ : ℝ) : ℂ) ^ 2 - 1) ^ 3 + 3 * ((cubicTau θ : ℝ) : ℂ) ^ 4
          - ((cubicTau θ : ℝ) : ℂ) ^ 6
          - 2 * ((Real.cos θ : ℝ) : ℂ) * ((cubicTau θ : ℝ) : ℂ) ^ 3)
        / ((cubicTau θ : ℝ) : ℂ) ^ 6 := by
    field_simp
    ring
  rw [hsplit, hnum, zero_div]

/-- **`Forgacs2017RationalDenominator` Props. 1--2 at the witness.**  The
principal pair has strictly the smallest modulus: the only other zero is `1/τ²`,
and `τ < 1/τ²` is `τ³ < 1`. -/
theorem cubicTau_lt_cubicThird {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    cubicTau θ < cubicThird θ := by
  have hτ : (0 : ℝ) < cubicTau θ := cubicTau_pos θ
  have h1 : cubicTau θ < 1 := cubicTau_lt_one hθ
  rw [cubicThird, lt_div_iff₀ (by positivity)]
  nlinarith [hτ, h1]

/-! ### The root set is exactly the three

The pencil has degree three and three distinct zeros are in hand, so there is no
fourth.  That is `huniq₀`; `hsimple₀` and `haR₀` follow with no further analysis,
since distinct roots of a cubic are simple and the moduli are `τ, τ, 1/τ²`. -/

theorem natDegree_ftDen_cubicQ (z : ℂ) : (ftDen cubicQ 1 z).natDegree = 3 := by
  have hQ3 : cubicQ.natDegree = 3 := by
    have he : (1 - X : Polynomial ℂ) = -(X - C 1) := by simp
    have h1 : (1 - X : Polynomial ℂ).natDegree = 1 := by
      rw [he, natDegree_neg, natDegree_X_sub_C]
    rw [cubicQ, natDegree_pow, h1]
  rw [ftDen, natDegree_add_eq_left_of_natDegree_lt, hQ3]
  refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
  rw [hQ3, pow_one, natDegree_X]
  norm_num

/-- **`huniq₀` at the witness.**  Every denominator zero is one of the three. -/
theorem cubicRoot_eq_of_eval_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) {w : ℂ}
    (hw : (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval w = 0) :
    w = ((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
      ∨ w = (starRingEnd ℂ) (((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
      ∨ w = ((cubicThird θ : ℝ) : ℂ) := by
  classical
  set P := ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ) with hP
  set tp : ℂ := ((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I) with htp
  have hdeg : P.natDegree = 3 := natDegree_ftDen_cubicQ _
  have hPne : P ≠ 0 := fun h => by rw [h] at hdeg; simp at hdeg
  have hplus : P.eval tp = 0 := ftDen_cubicQ_eval_cubicTau θ
  have hminus : P.eval ((starRingEnd ℂ) tp) = 0 :=
    ftDen_eval_conj_eq_zero hasRealCoeffs_cubicQ hplus
  have hthird : P.eval ((cubicThird θ : ℝ) : ℂ) = 0 := ftDen_cubicQ_eval_cubicThird θ
  have hgap : cubicTau θ < cubicThird θ := cubicTau_lt_cubicThird hθ
  have hnormp : ‖tp‖ = cubicTau θ := by
    rw [htp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (cubicTau_pos θ)]
  have hnormc : ‖(starRingEnd ℂ) tp‖ = cubicTau θ := by rw [RCLike.norm_conj, hnormp]
  have hnorm3 : ‖((cubicThird θ : ℝ) : ℂ)‖ = cubicThird θ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_trans (cubicTau_pos θ) hgap)]
  have hpc : tp ≠ (starRingEnd ℂ) tp := by
    intro heq
    have him := congrArg Complex.im heq
    rw [Complex.conj_im] at him
    have hval : tp.im = cubicTau θ * Real.sin θ := by
      rw [htp, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_im]
      ring
    rw [hval] at him
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    nlinarith [cubicTau_pos θ]
  have hne3p : tp ≠ ((cubicThird θ : ℝ) : ℂ) := by
    intro h; rw [h, hnorm3] at hnormp; linarith
  have hne3c : (starRingEnd ℂ) tp ≠ ((cubicThird θ : ℝ) : ℂ) := by
    intro h; rw [h, hnorm3] at hnormc; linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hsub : ({tp, (starRingEnd ℂ) tp, ((cubicThird θ : ℝ) : ℂ), w} : Finset ℂ)
      ⊆ P.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Multiset.mem_toFinset, mem_roots hPne, IsRoot]
    rcases hx with rfl | rfl | rfl | rfl
    · exact hplus
    · exact hminus
    · exact hthird
    · exact hw
  have hcard : ({tp, (starRingEnd ℂ) tp, ((cubicThird θ : ℝ) : ℂ), w} : Finset ℂ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hpc, hne3p, Ne.symm h1]),
      Finset.card_insert_of_notMem (by simp [hne3c, Ne.symm h2]),
      Finset.card_insert_of_notMem (by simp [Ne.symm h3]), Finset.card_singleton]
  have h4 : 4 ≤ P.roots.toFinset.card := hcard ▸ Finset.card_le_card hsub
  have hle : P.roots.toFinset.card ≤ 3 :=
    le_trans (Multiset.toFinset_card_le _) (le_trans P.card_roots' (le_of_eq hdeg))
  omega

/-! ### The retained set

`sfun₀` and `hroot₀`/`huniq₀` in one statement: the denominator zeros at a given
angle are exactly the three, so the Finset naming them *is* the root set rather
than a subset asserted to be one. -/

open scoped Classical in
/-- The denominator zeros at angle `θ`: the principal pair and `1/τ²`. -/
noncomputable def cubicRootSet (θ : ℝ) : Finset ℂ :=
  {((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I),
   (starRingEnd ℂ) (((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)),
   ((cubicThird θ : ℝ) : ℂ)}

/-- **`hroot₀` and `huniq₀` at the witness, as one equivalence.**  Membership of
`cubicRootSet` is being a denominator zero — no containment in either direction
is assumed. -/
theorem mem_cubicRootSet_iff {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) {w : ℂ} :
    w ∈ cubicRootSet θ
      ↔ (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval w = 0 := by
  classical
  constructor
  · intro hmem
    simp only [cubicRootSet, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact ftDen_cubicQ_eval_cubicTau θ
    · exact ftDen_eval_conj_eq_zero hasRealCoeffs_cubicQ (ftDen_cubicQ_eval_cubicTau θ)
    · exact ftDen_cubicQ_eval_cubicThird θ
  · intro hw
    simp only [cubicRootSet, Finset.mem_insert, Finset.mem_singleton]
    exact cubicRoot_eq_of_eval_zero hθ hw

/-! ### `hsimple₀`: the three roots are simple

Not by a separability argument but by counting.  The three are distinct and the
degree is three, so `roots` has as many elements as its `toFinset` — it is
`Nodup` — and every multiplicity is `1`.  `Polynomial.one_lt_rootMultiplicity_iff_isRoot`
then says the derivative cannot vanish at any of them.

That lemma is worth naming because four name-shaped searches missed it: it is
filed under `one_lt_rootMultiplicity`, and what is wanted here is its
*contrapositive*, so even a well-aimed search for "simple root implies derivative
nonzero" would not have found it. -/

theorem cubic_pair_ne {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
      ≠ (starRingEnd ℂ) (((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)) := by
  intro heq
  have him := congrArg Complex.im heq
  rw [Complex.conj_im] at him
  have hval : (((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)).im
      = cubicTau θ * Real.sin θ := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im]
    ring
  rw [hval] at him
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  nlinarith [cubicTau_pos θ]

theorem card_cubicRootSet {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    (cubicRootSet θ).card = 3 := by
  classical
  set tp : ℂ := ((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I) with htp
  have hgap : cubicTau θ < cubicThird θ := cubicTau_lt_cubicThird hθ
  have hnormp : ‖tp‖ = cubicTau θ := by
    rw [htp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (cubicTau_pos θ)]
  have hnormc : ‖(starRingEnd ℂ) tp‖ = cubicTau θ := by rw [RCLike.norm_conj, hnormp]
  have hnorm3 : ‖((cubicThird θ : ℝ) : ℂ)‖ = cubicThird θ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_trans (cubicTau_pos θ) hgap)]
  have hpc : tp ≠ (starRingEnd ℂ) tp := cubic_pair_ne hθ
  have hne3p : tp ≠ ((cubicThird θ : ℝ) : ℂ) := by
    intro h; rw [h, hnorm3] at hnormp; linarith
  have hne3c : (starRingEnd ℂ) tp ≠ ((cubicThird θ : ℝ) : ℂ) := by
    intro h; rw [h, hnorm3] at hnormc; linarith
  have h1 : tp ∉ ({(starRingEnd ℂ) tp, ((cubicThird θ : ℝ) : ℂ)} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hpc, hne3p⟩
  have h2 : (starRingEnd ℂ) tp ∉ ({((cubicThird θ : ℝ) : ℂ)} : Finset ℂ) := by
    simp only [Finset.mem_singleton]
    exact hne3c
  rw [cubicRootSet, ← htp, Finset.card_insert_of_notMem h1,
    Finset.card_insert_of_notMem h2, Finset.card_singleton]

/-- **`hsimple₀` at the witness.**  Every denominator zero is simple, so the
derivative does not vanish there. -/
theorem derivative_ftDen_cubicQ_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) {w : ℂ}
    (hw : w ∈ cubicRootSet θ) :
    (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ))).eval w ≠ 0 := by
  classical
  set P := ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ) with hP
  have hdeg : P.natDegree = 3 := natDegree_ftDen_cubicQ _
  have hPne : P ≠ 0 := fun h => by rw [h] at hdeg; simp at hdeg
  have hroot : P.IsRoot w := (mem_cubicRootSet_iff hθ).1 hw
  have hsub : cubicRootSet θ ⊆ P.roots.toFinset := by
    intro x hx
    simp only [Multiset.mem_toFinset, mem_roots hPne]
    exact (mem_cubicRootSet_iff hθ).1 hx
  have h3 : 3 ≤ P.roots.toFinset.card := (card_cubicRootSet hθ) ▸ Finset.card_le_card hsub
  have hle : Multiset.card P.roots ≤ 3 := le_trans P.card_roots' (le_of_eq hdeg)
  have hle2 : P.roots.toFinset.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
  have heq : P.roots.toFinset.card = Multiset.card P.roots := by omega
  have hnodup : P.roots.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.1 heq
  have hmem : w ∈ P.roots := (mem_roots hPne).2 hroot
  have hrm : P.rootMultiplicity w = 1 := by
    rw [← count_roots]
    exact Multiset.count_eq_one_of_mem hnodup hmem
  intro hd
  have hlt := (one_lt_rootMultiplicity_iff_isRoot hPne).2 ⟨hroot, hd⟩
  omega

/-! ### `haR₀`: one separating radius across the window

`R₀` has to be a single constant over the whole endpoint window, not a bound per
angle.  `1/τ²` is the largest of the three moduli and `τ` is antitone, so `1/τ²`
is monotone and its value at the far end of the window bounds it throughout. -/

theorem cubicThird_monotoneOn : MonotoneOn cubicThird (Set.Icc 0 Real.pi) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | h
  · exact le_rfl
  · have hlt : cubicTau y < cubicTau x := cubicTau_strictAntiOn hx hy h
    have hpx : 0 < cubicTau x := cubicTau_pos x
    have hpy : 0 < cubicTau y := cubicTau_pos y
    rw [cubicThird, cubicThird, one_div, one_div,
      inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith

/-- Every denominator zero has modulus at most `1/τ²`, the third root's. -/
theorem norm_le_cubicThird {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) {w : ℂ}
    (hw : w ∈ cubicRootSet θ) : ‖w‖ ≤ cubicThird θ := by
  classical
  have hgap : cubicTau θ < cubicThird θ := cubicTau_lt_cubicThird hθ
  have hnp : ‖((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)‖
      = cubicTau θ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (cubicTau_pos θ)]
  simp only [cubicRootSet, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · rw [hnp]; linarith
  · rw [RCLike.norm_conj, hnp]; linarith
  · rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_trans (cubicTau_pos θ) hgap)]

/-- **`haR₀` at the witness.**  With `R₀ = 1/τ(e)² + 1`, every denominator zero
at every angle of `(0, e]` lies strictly inside the circle of radius `R₀`. -/
theorem norm_lt_cubicRadius {e : ℝ} (he : e < Real.pi) {θ : ℝ}
    (hθ0 : 0 < θ) (hθe : θ ≤ e) {w : ℂ} (hw : w ∈ cubicRootSet θ) :
    ‖w‖ < cubicThird e + 1 := by
  have hθπ : θ ∈ Set.Ioo 0 Real.pi := ⟨hθ0, lt_of_le_of_lt hθe he⟩
  have hmono : cubicThird θ ≤ cubicThird e :=
    cubicThird_monotoneOn ⟨hθ0.le, hθπ.2.le⟩ ⟨le_trans hθ0.le hθe, he.le⟩ hθe
  have := norm_le_cubicThird hθπ hw
  linarith

/-! ### Joint satisfiability of the retained-set block

The binders above are discharged one at a time, which does not say they can be
met *together*: eighteen separate proofs may each have chosen `e₀`, `R₀`,
`τmax₀` differently, and `weighted_dominance_of_branch` needs one assignment
serving all of them.  The statement below asserts the whole lower-endpoint
retained-set block at a single choice — `e₀ = π/2`, `τmax₀ = 1`,
`R₀ = 1/τ(π/2)² + 1`, `sfun₀ = cubicRootSet` — so elaborating it *is* the joint
test.  A window that shrank to nothing under `min` over the group, or a variable
instantiated two ways, would show up here and nowhere else. -/

theorem cubicWitness_retainedSet_block :
    ∃ R₀ τmax₀ e₀ : ℝ, 0 < R₀ ∧ τmax₀ / R₀ < 1 ∧ 0 < e₀ ∧ e₀ < Real.pi ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → 0 < cubicTau δ) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → cubicTau δ ≤ τmax₀) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ cubicRootSet δ,
        (ftDen cubicQ 1 ((cubicZ (cubicTau δ) δ : ℝ) : ℂ)).eval a = 0) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ cubicRootSet δ,
        (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau δ) δ : ℝ) : ℂ))).eval a ≠ 0) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ cubicRootSet δ, ‖a‖ < R₀) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t : ℂ, ‖t‖ ≤ R₀ →
        (ftDen cubicQ 1 ((cubicZ (cubicTau δ) δ : ℝ) : ℂ)).eval t = 0 → t ∈ cubicRootSet δ) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
        (ftDen cubicQ 1 ((cubicZ (cubicTau δ) δ : ℝ) : ℂ)).eval
          (((cubicTau δ : ℝ) : ℂ) * Complex.exp (((δ : ℝ) : ℂ) * Complex.I)) = 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set e : ℝ := Real.pi / 2 with he
  have he0 : 0 < e := by rw [he]; linarith
  have heπ : e < Real.pi := by rw [he]; linarith
  have h3pos : 0 < cubicThird e := lt_trans (cubicTau_pos e) (cubicTau_lt_cubicThird ⟨he0, heπ⟩)
  refine ⟨cubicThird e + 1, 1, e, by linarith, ?_, he0, heπ, fun δ _ _ => cubicTau_pos δ,
    fun δ _ _ => cubicTau_le_one δ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_one (by linarith)]; linarith
  · exact fun δ hδ hδe a ha => (mem_cubicRootSet_iff ⟨hδ, lt_of_le_of_lt hδe heπ⟩).1 ha
  · exact fun δ hδ hδe a ha =>
      derivative_ftDen_cubicQ_ne_zero ⟨hδ, lt_of_le_of_lt hδe heπ⟩ ha
  · exact fun δ hδ hδe a ha => norm_lt_cubicRadius heπ hδ hδe ha
  · exact fun δ hδ hδe t _ ht => (mem_cubicRootSet_iff ⟨hδ, lt_of_le_of_lt hδe heπ⟩).2 ht
  · exact fun δ _ _ => ftDen_cubicQ_eval_cubicTau δ

/-! ### The endpoint collision, exactly

The branch equation rearranges into an identity between the angle and the
distance from `t_a`:

`1 - cos θ = (τ-1)²(2τ+1) / (2τ³)`

with no error term.  The double factor `(τ-1)²` on the right against the double
zero of `1 - cos θ` at `θ = 0` is the collision `lem:principal-endpoint-regularity`
describes, in closed form — and it is what `hγd₀` will have to be built on, since
the implicit function theorem degenerates there: differentiating the branch
equation at `(θ,τ) = (0,1)` gives `6τ' = 6τ'`.

The rate follows by comparing leading terms — `θ²/2` against `3(1-τ)²/2` — giving
`1 - τ = θ/√3 + O(θ²)`, so `τ'(0) = -1/√3` and `γ_e = -1/√3 + i ≠ 0`.  Measured
along the branch: `(1-τ)/θ` runs `0.5408, 0.5585, 0.5678, 0.5725, 0.5749,
0.5761, 0.5767` against `1/√3 = 0.5773503`. -/

theorem cubicTau_endpoint_identity (θ : ℝ) :
    1 - Real.cos θ
      = (cubicTau θ - 1) ^ 2 * (2 * cubicTau θ + 1) / (2 * cubicTau θ ^ 3) := by
  have hτ : 0 < cubicTau θ := cubicTau_pos θ
  have hbr := cubicTau_branch θ
  rw [eq_div_iff (by positivity)]
  linear_combination -hbr

/-! ### The upper endpoint

At `r = 1` the upper endpoint is `θ = π`, where the branch equation becomes
`2τ³ + 3τ² - 1 = 0` with root `τ = 1/2`, so `t_b = -1/2` and the principal pair
coalesces there — exactly the "multiplicity exactly two" collision
`thm:FT-geometry` describes at `θ↑π` with `r = 1`.

**The upper cluster is empty at this pencil, and that bounds what it can
witness.**  The third zero is `1/τ² → 4`, far outside the pair at `1/2`: it obeys
`eq:endpoint-fixed-gap`, not the linear gap, so there are no nonprincipal cluster
members and `n₁ = 0`.  The upper *cluster* binders — `hexp₁`, the `hωne₁` pair,
`hL₁`, `hratio₁` — are therefore vacuous here, and a witness for them needs
`r ≥ 3`, where the cluster has `r - 2` members.  The upper *retained-set* binders
are not vacuous and follow the lower endpoint's route through `θ ↦ π - δ`. -/

theorem cubicTau_pi : cubicTau Real.pi = 1 / 2 := by
  refine ((existsUnique_cubicTau_Ioc Real.pi).choose_spec.2 (1 / 2)
    ⟨⟨by norm_num, by norm_num⟩, ?_⟩).symm
  simp [cubicBranchFn]
  norm_num

/-- `1/τ(π)² = 4`: the largest modulus any denominator zero of this pencil
attains, since `cubicThird` is monotone and `π` is the top of the arc. -/
theorem cubicThird_pi : cubicThird Real.pi = 4 := by
  rw [cubicThird, cubicTau_pi]
  norm_num

/-! ### The upper retained-set block

The upper endpoint's *retained-set* binders are the lower endpoint's read at
`θ = π - δ`, and every lemma above is stated for an arbitrary angle of the open
arc, so they transfer without restatement.  Only the radius is new, and it is
uniform for a reason particular to this pencil: `cubicThird` is monotone, so the
largest modulus anywhere on the arc is `cubicThird π = 4`, and `R₁ = 5` serves
every angle at either endpoint.

The *cluster* binders do not transfer, and must not be attempted here — `n₁ = 0`
at `r = 1`, so they would be vacuous.  See the note at `cubicTau_pi`. -/

theorem cubicWitness_upperRetainedSet_block :
    ∃ R₁ τmax₁ e₁ : ℝ, 0 < R₁ ∧ τmax₁ / R₁ < 1 ∧ 0 < e₁ ∧ e₁ < Real.pi ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ → 0 < cubicTau (Real.pi - δ)) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ → cubicTau (Real.pi - δ) ≤ τmax₁) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ cubicRootSet (Real.pi - δ),
        (ftDen cubicQ 1
          ((cubicZ (cubicTau (Real.pi - δ)) (Real.pi - δ) : ℝ) : ℂ)).eval a = 0) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ cubicRootSet (Real.pi - δ),
        (derivative (ftDen cubicQ 1
          ((cubicZ (cubicTau (Real.pi - δ)) (Real.pi - δ) : ℝ) : ℂ))).eval a ≠ 0) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ cubicRootSet (Real.pi - δ), ‖a‖ < R₁) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t : ℂ, ‖t‖ ≤ R₁ →
        (ftDen cubicQ 1
            ((cubicZ (cubicTau (Real.pi - δ)) (Real.pi - δ) : ℝ) : ℂ)).eval t = 0 →
          t ∈ cubicRootSet (Real.pi - δ)) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
        (ftDen cubicQ 1
            ((cubicZ (cubicTau (Real.pi - δ)) (Real.pi - δ) : ℝ) : ℂ)).eval
          (((cubicTau (Real.pi - δ) : ℝ) : ℂ)
            * Complex.exp (((Real.pi - δ : ℝ) : ℂ) * Complex.I)) = 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set e : ℝ := Real.pi / 2 with he
  have he0 : 0 < e := by rw [he]; linarith
  have heπ : e < Real.pi := by rw [he]; linarith
  have harc : ∀ δ : ℝ, 0 < δ → δ ≤ e → Real.pi - δ ∈ Set.Ioo 0 Real.pi := by
    intro δ hδ hδe
    exact ⟨by linarith [lt_of_le_of_lt hδe heπ], by linarith⟩
  have hbound : ∀ δ : ℝ, 0 < δ → δ ≤ e → cubicThird (Real.pi - δ) ≤ 4 := by
    intro δ hδ hδe
    have := cubicThird_monotoneOn ⟨by linarith [(harc δ hδ hδe).1], (harc δ hδ hδe).2.le⟩
      ⟨hpi.le, le_rfl⟩ (by linarith)
    rwa [cubicThird_pi] at this
  refine ⟨5, 1, e, by norm_num, by norm_num, he0, heπ,
    fun δ _ _ => cubicTau_pos _, fun δ _ _ => cubicTau_le_one _, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun δ hδ hδe a ha => (mem_cubicRootSet_iff (harc δ hδ hδe)).1 ha
  · exact fun δ hδ hδe a ha => derivative_ftDen_cubicQ_ne_zero (harc δ hδ hδe) ha
  · intro δ hδ hδe a ha
    have h1 := norm_le_cubicThird (harc δ hδ hδe) ha
    have h2 := hbound δ hδ hδe
    linarith
  · exact fun δ hδ hδe t _ ht => (mem_cubicRootSet_iff (harc δ hδ hδe)).2 ht
  · exact fun δ _ _ => ftDen_cubicQ_eval_cubicTau _

/-! ### Exact points on the branch

Four angles where `τ` is closed-form.  Each is one appeal to
`existsUnique_cubicTau_Ioc`: exhibit the value, check it lies in `(0,1]` and
kills the branch polynomial, and uniqueness does the rest.  They cost a line
apiece and give this pencil more exact branch data than any other object here. -/

theorem cubicTau_pi_div_two : cubicTau (Real.pi / 2) = 1 / Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ((existsUnique_cubicTau_Ioc (Real.pi / 2)).choose_spec.2 (1 / Real.sqrt 3)
    ⟨⟨by positivity, ?_⟩, ?_⟩).symm
  · rw [div_le_one hp]
    nlinarith [h3, hp]
  · simp only [cubicBranchFn, Real.cos_pi_div_two]
    field_simp
    nlinarith [h3, hp]

theorem cubicTau_pi_div_four : cubicTau (Real.pi / 4) = 1 / Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ((existsUnique_cubicTau_Ioc (Real.pi / 4)).choose_spec.2 (1 / Real.sqrt 2)
    ⟨⟨by positivity, ?_⟩, ?_⟩).symm
  · rw [div_le_one hp]
    nlinarith [h2, hp]
  · simp only [cubicBranchFn, Real.cos_pi_div_four]
    field_simp
    nlinarith [h2, hp]

/-! ### The branch in closed form

The four exact points were not a coincidence.  Writing `v = 1/τ`, the branch
equation `2τ³cos θ = 3τ² - 1` is `3v - v³ = 2cos θ`, and `v = 2cos φ` turns the
left side into `-2cos 3φ` by the triple-angle identity.  So `cos 3φ = cos(π-θ)`
and `φ = (π-θ)/3`:

`τ(θ) = 1 / (2cos((π-θ)/3))`   on `[0,π]`.

Every value used above is a substitution — `θ = 0, π/4, π/2, π` give `2cos` of
`π/3, π/4, π/6, 0`, hence `1, √2, √3, 2`.  Differentiating gives
`τ'(0) = -sin(π/3)/(6cos²(π/3)) = -1/√3`, the rate measured along the branch and
the `γ_e` that `hγd₀` needs.  `cubicTau` itself is the *even* extension of this,
which is why it has a corner at `0` while the closed form is smooth there.

This is Viète's trigonometric root: `2τ³cos θ - 3τ² + 1 = 0` is the
`casus irreducibilis`, three real roots and no real radical expression, and the
branch is the one staying in `(1/2, 1]`.

**What it does not buy.**  It makes the binders at *this* pencil more
computational still, and says nothing whatever about the general branch.
`ftTau` has no closed form — that is why the cited work reaches it through an
angle count and an implicit function theorem, and why `hexp₀` is hard in general
while everything here is elementary.  A reader meeting an explicit `τ` should not
read it as evidence that the general case is explicit.

**Nothing above is retired by it.**  The closed form holds on `[0,π]`, while
`existsUnique_cubicTau_Ioc`, `cubicTau_pos`, `cubicTau_le_one`,
`cubicTau_neg` and `continuous_cubicTau` are *total* on `ℝ` — they are what make
`cubicTau` a function at all, and the two-sided ones are what the evenness
argument needs.  `cubicTau_strictAntiOn` and the endpoint values could now be
re-derived by substitution, and are kept because their consumers
(`cubicThird_monotoneOn`, `cubicThird_pi`, `cubicTau_lt_cubicThird`) take them at
the domains they already have. -/

theorem cubicTau_closed_form {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    cubicTau θ = 1 / (2 * Real.cos ((Real.pi - θ) / 3)) := by
  have hw : (Real.pi - θ) / 3 ∈ Set.Icc 0 (Real.pi / 3) := by
    constructor <;> [linarith [hθ.2]; linarith [hθ.1]]
  have hcos : (1 : ℝ) / 2 ≤ Real.cos ((Real.pi - θ) / 3) := by
    have := Real.cos_le_cos_of_nonneg_of_le_pi hw.1 (by linarith [Real.pi_pos]) hw.2
    rwa [Real.cos_pi_div_three] at this
  have hv : (0 : ℝ) < 2 * Real.cos ((Real.pi - θ) / 3) := by linarith
  refine ((existsUnique_cubicTau_Ioc θ).choose_spec.2 _ ⟨⟨by positivity, ?_⟩, ?_⟩).symm
  · rw [div_le_one hv]; linarith
  · have h3 : Real.cos (3 * ((Real.pi - θ) / 3)) = Real.cos (Real.pi - θ) := by ring_nf
    rw [Real.cos_three_mul, Real.cos_pi_sub] at h3
    simp only [cubicBranchFn]
    field_simp
    nlinarith [h3, hv]

/-! ### `hinterior`, the branch-geometry group

`hinterior`'s first group asks for one `(Ri, τmi, σi)` serving four clauses at
once on a compact interior interval, plus the branch facts there.  The choice is
forced and instructive: the interior asks that **exactly two** denominator zeros
lie inside `‖t‖ ≤ Ri`, and this pencil has three — so `Ri` must separate the
principal pair from `1/τ²`.  On `[e, π-e]` the pair has modulus `τ ≤ τ(e) < 1`
while the third zero has modulus `1/τ² ≥ 1/τ(e)² > 1`, so `Ri = 1` does it, with
`τmi = τ(e)` and `σi = τ(e) < 1`.

That the separating radius exists at all is `cubicTau_lt_one`; that it can be the
*same* radius across the interval is `cubicTau_strictAntiOn`.  Neither is visible
from a per-clause reading — the radius has to be chosen once. -/

theorem cubicWitness_interior_geometry {e : ℝ} (he : 0 < e) (he2 : e < Real.pi / 2) :
    ∃ Ri τmi σi : ℝ, 0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
      (∀ θ ∈ Set.Icc e (Real.pi - e), 0 < cubicTau θ ∧ cubicTau θ ≤ τmi) ∧
      (∀ θ ∈ Set.Icc e (Real.pi - e),
        (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval
          (((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)) = 0) ∧
      (∀ θ ∈ Set.Icc e (Real.pi - e),
        (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ))).eval
          (((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)) ≠ 0) ∧
      (∀ θ ∈ Set.Icc e (Real.pi - e),
        (((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
          ≠ (starRingEnd ℂ) (((cubicTau θ : ℝ) : ℂ)
              * Complex.exp (((θ : ℝ) : ℂ) * Complex.I))) ∧
      (∀ θ ∈ Set.Icc e (Real.pi - e), ∀ t : ℂ, ‖t‖ ≤ Ri →
        (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval t = 0 →
          t = ((cubicTau θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
            ∨ t = (starRingEnd ℂ) (((cubicTau θ : ℝ) : ℂ)
                * Complex.exp (((θ : ℝ) : ℂ) * Complex.I))) := by
  have hpi := Real.pi_pos
  have hearc : e ∈ Set.Ioo 0 Real.pi := ⟨he, by linarith⟩
  have hsub : ∀ θ ∈ Set.Icc e (Real.pi - e), θ ∈ Set.Ioo 0 Real.pi := by
    intro θ hθ; exact ⟨lt_of_lt_of_le he hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩
  have hτe1 : cubicTau e < 1 := cubicTau_lt_one hearc
  have hτe0 : 0 < cubicTau e := cubicTau_pos e
  have hmax : ∀ θ ∈ Set.Icc e (Real.pi - e), cubicTau θ ≤ cubicTau e := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h | h
    · exact le_of_eq (by rw [h])
    · exact (cubicTau_strictAntiOn ⟨he.le, by linarith⟩
        ⟨le_trans he.le hθ.1, (hsub θ hθ).2.le⟩ h).le
  refine ⟨1, cubicTau e, cubicTau e, one_pos, by rw [div_one], hτe0, hτe1,
    fun θ hθ => ⟨cubicTau_pos θ, hmax θ hθ⟩,
    fun θ hθ => ftDen_cubicQ_eval_cubicTau θ, ?_, ?_, ?_⟩
  · intro θ hθ
    refine derivative_ftDen_cubicQ_ne_zero (hsub θ hθ) ?_
    simp [cubicRootSet]
  · intro θ hθ
    exact cubic_pair_ne (hsub θ hθ)
  · intro θ hθ t hnorm hroot
    have hmem := (mem_cubicRootSet_iff (hsub θ hθ)).2 hroot
    simp only [cubicRootSet, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have h3 : cubicThird θ ≤ 1 := by
        rw [h, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (lt_trans (cubicTau_pos θ) (cubicTau_lt_cubicThird (hsub θ hθ)))] at hnorm
        exact hnorm
      have hlt : cubicTau θ < 1 := cubicTau_lt_one (hsub θ hθ)
      have hp : 0 < cubicTau θ := cubicTau_pos θ
      rw [cubicThird, div_le_one (by positivity)] at h3
      nlinarith

end ForgacsTran
