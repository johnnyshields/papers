/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.FTGeometryClosure
import ForgacsTran.FTGeometryCone

/-!
# `thm:FT-geometry` at the boundary values of `n`

`FTGeometryClosure` closes the theorem at `r = 1` with `3 ≤ n`, and
`FTGeometryCone` at `r ≥ 2` with `2 ≤ n`.  `eq:Q-hypotheses` asks only that `Q` be
nonconstant, so three pairs are left over, and they are not alike:

* `(n, r) = (1, 1)` is **out of scope**.  `g(t) = -Q(t)/t` has `g'(t) = Q(0)/t^2 > 0`
  and hence no positive critical point, so the `t_a` of `eq:ab-def` does not exist
  and the theorem has nothing to state.  `PrincipalSimpleBranch.not_ftBranchAt_one_one`
  records the same fact on the branch side.
* `(n, r) = (2, 1)` is `rem:quadratic-case` — a remark *about* the case, not a
  removal of it from the theorem's hypotheses.
* `n = 1` with `r ≥ 2` is in scope and unremarked.

Both remaining cases close here, and the two mechanisms are different.

## Where the degree count suffices

When `\deg(Q + zX^r) ≤ 2` the principal pair **is** the whole denominator, so the
minimum-modulus clause is vacuous rather than proved: there is no third zero to
separate.  That is `eq_or_eq_of_natDegree_le_two`, and it covers `(2,1)` and
`(1,2)` at once.  Only `hmin` is supplied that way; the three clauses themselves
come from `FTBranchEndpointUpper.ft_geometry_at_branch_of_two_le` like every
other case, so `(2,1)` is an instance of the general statement rather than a
parallel assembly beside it.

## Where the cone argument survives the weaker angle bound

At `n = 1` the angle sum is a single angle and `(n-1)π = 0`, so `mul_lt_ftAngle`
degenerates from `θ_1 > rθ` to the equality `θ_1 = rθ`.  `FTGeometryCone`'s near
case then loses its strictness — but only in the one step it can afford to,
because at `r ≥ 3` the closing comparison `\sin(π/(2(r-1))) < \sin(π/r)` is
already strict.  `ftChord_lt_mul_sin_of_le` is that variant, and `r = 2` is
exactly the case where it is not available and the degree count is.

The positive-real exclusion also has to be redone, because `RealCritical`'s route
runs on the first gap between consecutive zeros of `Q` and `n = 1` has none.  It
is shorter rather than harder: `E` is linear, `E(s) = c((r-1)s - ra)`, its only
zero is `t_a = ra/(r-1)`, and `ftTau_le_of_one` puts the branch radius below it
through the closed form `τ(θ) = a\sin(rθ)/\sin((r-1)θ)` and the elementary
`sin_scaled_le`.

**Differs from the paper's route.**  The manuscript's `t_a` is the smallest
positive critical point of `g`, located by the sign analysis of `Σ`.  At `n = 1`
that analysis is not needed: `E` is a linear polynomial and `t_a` is read off it,
and the branch radius is available in closed form rather than as the solution of
an implicit equation.  Neither is a different theorem — it is the same statement
where the general machinery has nothing to do.

## Hypothesis relaxations this needed

Three existing statements carried `2 ≤ n` where their proofs consume only that the
branch exists across the arc, which at `r ≥ 2` holds from `n = 1`.  Each is
relaxed in place and the old form kept as a one-line corollary, so no consumer
moves: `PrincipalGap.ft_minModulus_at_branch_of_or`,
`FTBranchUpper.tendsto_ftTau_nhdsLT_upper_of_pos`, and
`FTBranchEndpointUpper.tendsto_ftBranchZ_atTop_arc_end_of_pos`.

## Containment

`ft_geometry_at_branch_quadratic` and `ft_geometry_unbounded_at_branch_one` relate
`ftBranchZ`, `ftTau`, `ftPrincipal` and the pencil's zero set; their hypotheses are
`∀ k, 0 < a k`, `0 < c`, and a bound on `r`.  None of them mentions any of the
objects the conclusions relate, so none contains a conclusion, and both are
non-vacuous: the admissible class is inhabited at `n = 1` and `n = 2` by any
positive `a` and `c`.

## Main statements

* `eq_or_eq_of_natDegree_le_two`, `natDegree_ftDen_le` — the degree count.
* `ft_minModulus_at_branch_of_deg_le_two` — `hmin` wherever the pencil is at most
  quadratic, with `ft_minModulus_at_branch_quadratic` and
  `ft_minModulus_at_branch_linear_two` its two named instances.
* `ft_geometry_at_branch_quadratic` — **`thm:FT-geometry` at `(n, r) = (2, 1)`**.
* `sin_scaled_le`, `mul_le_ftAngle`, `ftChord_lt_mul_sin_of_le` — the three pieces
  the `n = 1` cone needs beyond `FTGeometryCone`.
* `ftAngle_eq_of_one`, `ftTau_eq_of_one`, `ftTau_le_of_one`,
  `eval_ftCriticalReal_one`, `negDivPow_lt_ftBranchZ_one` — the linear pencil.
* `cone_at_branch_one_of_three_le`, `ft_minModulus_at_branch_one` — `hcone` and
  `hmin` at `n = 1`, every `r ≥ 2`.
* `tendsto_sin_mul_div`, `tendsto_ftTau_one`, `tendsto_ftBranchZ_arc_zero_one` —
  the lower-endpoint limit there.
* `ft_geometry_unbounded_at_branch_one` — **`thm:FT-geometry` at `n = 1`,
  `r ≥ 2`**.

## Implementation notes

Sorry-free.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, «Forgács--Tran geometry and
  endpoint separation» — `sec:geometry`, `subsec:FT-geometry`,
  `thm:FT-geometry`, `eq:ab-def`, `rem:quadratic-case`.
* `Forgacs2017RationalDenominator`, Proposition 1 and Lemmas 2, 3 and 6.

## Tags

quadratic case, linear pencil, degree count, Forgacs-Tran branch
-/

namespace ForgacsTran

open Real Set Polynomial Complex
open scoped Topology

/-- A polynomial of degree at most two has no zero beyond two it is known to have. -/
theorem eq_or_eq_of_natDegree_le_two {P : Polynomial ℂ} (hP0 : P ≠ 0) (hdeg : P.natDegree ≤ 2)
    {u v w : ℂ} (huv : u ≠ v) (hu : P.eval u = 0) (hv : P.eval v = 0) (hw : P.eval w = 0) :
    w = u ∨ w = v := by
  classical
  have hmem : ∀ x : ℂ, P.eval x = 0 → x ∈ P.roots := fun x hx =>
    (Polynomial.mem_roots' (p := P) (a := x)).2 ⟨hP0, hx⟩
  have hsub : ({u, v} : Multiset ℂ) ≤ P.roots := by
    refine Multiset.le_iff_count.2 fun x => ?_
    by_cases hxu : x = u
    · subst hxu
      have h1 : Multiset.count x ({x, v} : Multiset ℂ) = 1 := by
        simp [huv]
      rw [h1]
      exact Multiset.one_le_count_iff_mem.2 (hmem x hu)
    · by_cases hxv : x = v
      · subst hxv
        have h1 : Multiset.count x ({u, x} : Multiset ℂ) = 1 := by
          simp [hxu]
        rw [h1]
        exact Multiset.one_le_count_iff_mem.2 (hmem x hv)
      · have h0 : Multiset.count x ({u, v} : Multiset ℂ) = 0 := by
          simp [hxu, hxv]
        rw [h0]
        exact Nat.zero_le _
  have hcard : Multiset.card P.roots ≤ Multiset.card ({u, v} : Multiset ℂ) := by
    have h1 : Multiset.card P.roots ≤ P.natDegree := P.card_roots'
    have h2 : Multiset.card ({u, v} : Multiset ℂ) = 2 := by simp
    omega
  have heq : P.roots = ({u, v} : Multiset ℂ) := (Multiset.eq_of_le_of_card_le hsub hcard).symm
  have := hmem w hw
  rw [heq] at this
  simpa using this


theorem natDegree_ftDen_le {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hc : c ≠ 0) (r : ℕ) (z : ℂ) :
    (ftDen (ftRootPoly c a) r z).natDegree ≤ max n r := by
  rw [ftDen]
  refine le_trans (natDegree_add_le _ _) (max_le_max (le_of_eq (natDegree_ftRootPoly hc a)) ?_)
  exact le_trans (natDegree_C_mul_le _ _) (le_of_eq (natDegree_X_pow r))

theorem ftDen_ftRootPoly_ne_zero {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 1 ≤ r) (z : ℂ) : ftDen (ftRootPoly c a) r z ≠ 0 := fun h =>
  eval_ftDen_zero_ne_zero ha hc hr z (by rw [h]; simp)

theorem ft_minModulus_at_branch_of_deg_le_two {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hdeg : max n r ≤ 2) :
    ∀ θ ∈ Ioo (0 : ℝ) (π / r), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTau a r (n - 1)) θ →
        w ≠ (starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ) →
        ftTau a r (n - 1) θ < ‖w‖ := by
  intro θ hθ w hw hne hne'
  obtain ⟨hroot, hpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hrp := hroot θ hθ
  have hrm := ftPrincipal_conj_eval_eq_zero (hasRealCoeffs_ftRootPoly c a) hrp
  have hne2 := ftPrincipal_ne_conj_of_pos (hpos θ hθ) hθπ
  have hd : (ftDen (ftRootPoly c a) r
      (((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ))).natDegree ≤ 2 :=
    le_trans (natDegree_ftDen_le hc.ne' r _) hdeg
  rcases eq_or_eq_of_natDegree_le_two (ftDen_ftRootPoly_ne_zero ha hc hr _) hd
    hne2 hrp hrm hw with h | h
  · exact absurd h hne
  · exact absurd h hne'

/-- **`hmin` at `(n, r) = (2, 1)`** — the quadratic case `rem:quadratic-case`
describes, which `thm:FT-geometry` states and the tree's `hn3` excluded.  There is
nothing to separate: the pencil is quadratic, so the principal pair is the whole
denominator. -/
theorem ft_minModulus_at_branch_quadratic {a : Fin 2 → ℝ} {c : ℝ} (ha : ∀ k, 0 < a k)
    (hc : 0 < c) :
    ∀ θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (2 - 1) θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTau a 1 (2 - 1)) θ →
        w ≠ (starRingEnd ℂ) (ftPrincipal (ftTau a 1 (2 - 1)) θ) →
        ftTau a 1 (2 - 1) θ < ‖w‖ :=
  ft_minModulus_at_branch_of_deg_le_two (by omega) ha hc le_rfl (Or.inl (by omega)) (by norm_num)

/-- **`hmin` at `(n, r) = (1, 2)`** — the linear pencil at `r = 2`, the same degree
count in the other regime. -/
theorem ft_minModulus_at_branch_linear_two {a : Fin 1 → ℝ} {c : ℝ} (ha : ∀ k, 0 < a k)
    (hc : 0 < c) :
    ∀ θ ∈ Ioo (0 : ℝ) (π / ((2 : ℕ) : ℝ)), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) 2 ((ftBranchZ a c 2 (1 - 1) θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTau a 2 (1 - 1)) θ →
        w ≠ (starRingEnd ℂ) (ftPrincipal (ftTau a 2 (1 - 1)) θ) →
        ftTau a 2 (1 - 1) θ < ‖w‖ :=
  ft_minModulus_at_branch_of_deg_le_two (by omega) ha hc (by omega) (Or.inr le_rfl) (by norm_num)

theorem ft_geometry_at_branch_quadratic {a : Fin 2 → ℝ} {c : ℝ} (ha : ∀ k, 0 < a k)
    (hc : 0 < c) :
    ∃ za b : ℝ,
      ftBranchZ a c 1 (2 - 1) '' Ioo 0 (π / ((1 : ℕ) : ℝ)) = Ioo za b
        ∧ (∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)),
            (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (2 - 1) θ : ℝ) : ℂ)).eval
                (ftPrincipal (ftTau a 1 (2 - 1)) θ) = 0
              ∧ (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (2 - 1) θ : ℝ) : ℂ)).eval
                  ((starRingEnd ℂ) (ftPrincipal (ftTau a 1 (2 - 1)) θ)) = 0
              ∧ ‖ftPrincipal (ftTau a 1 (2 - 1)) θ‖ = ftTau a 1 (2 - 1) θ
              ∧ ‖(starRingEnd ℂ) (ftPrincipal (ftTau a 1 (2 - 1)) θ)‖
                  = ftTau a 1 (2 - 1) θ)
        ∧ (∀ θ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)), ∀ w : ℂ,
            (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (2 - 1) θ : ℝ) : ℂ)).eval w = 0 →
              ‖w‖ ≤ ftTau a 1 (2 - 1) θ →
                w = ftPrincipal (ftTau a 1 (2 - 1)) θ
                  ∨ w = (starRingEnd ℂ) (ftPrincipal (ftTau a 1 (2 - 1)) θ)) :=
  ft_geometry_at_branch_of_two_le (by omega) ha hc (ft_minModulus_at_branch_quadratic ha hc)

/-! ### The linear pencil `n = 1` -/

/-- `m\sin(kθ) ≤ k\sin(mθ)` for `0 ≤ m ≤ k` and `kθ ≤ π`: the difference vanishes
at `0` and its derivative `km(\cos(mθ) - \cos(kθ))` is nonnegative there. -/
theorem sin_scaled_le {m k : ℝ} (hm : 0 ≤ m) (hmk : m ≤ k) {θ : ℝ} (hθ : 0 ≤ θ)
    (hkθ : k * θ ≤ π) : m * Real.sin (k * θ) ≤ k * Real.sin (m * θ) := by
  have hk : 0 ≤ k := le_trans hm hmk
  set f : ℝ → ℝ := fun u => k * Real.sin (m * u) - m * Real.sin (k * u) with hf
  have hd : ∀ u : ℝ, HasDerivAt f (k * m * (Real.cos (m * u) - Real.cos (k * u))) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => Real.sin (m * v)) (Real.cos (m * u) * m) u := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sin (m * u)).comp u (by simpa using (hasDerivAt_id u).const_mul m)
    have h2 : HasDerivAt (fun v : ℝ => Real.sin (k * v)) (Real.cos (k * u) * k) u := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sin (k * u)).comp u (by simpa using (hasDerivAt_id u).const_mul k)
    have hval : k * (Real.cos (m * u) * m) - m * (Real.cos (k * u) * k)
        = k * m * (Real.cos (m * u) - Real.cos (k * u)) := by ring
    exact hval ▸ ((h1.const_mul k).sub (h2.const_mul m))
  have hmono : MonotoneOn f (Icc 0 θ) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun u _ => (hd u).continuousAt.continuousWithinAt)
      (fun u _ => ((hd u).differentiableAt).differentiableWithinAt) ?_
    intro u hu
    rw [interior_Icc] at hu
    rw [(hd u).deriv]
    have hu0 : 0 ≤ u := le_of_lt hu.1
    have hku : k * u ≤ π := le_trans (by nlinarith [hu.2]) hkθ
    have hcos : Real.cos (k * u) ≤ Real.cos (m * u) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hku (by nlinarith)
    exact mul_nonneg (mul_nonneg hk hm) (sub_nonneg.2 hcos)
  have := hmono (left_mem_Icc.2 hθ) (right_mem_Icc.2 hθ) hθ
  simp only [hf, mul_zero, Real.sin_zero, mul_zero, sub_zero] at this
  linarith

/-- **`θ_k ≥ rθ`, with no lower bound on `n`.**  The nonstrict form of
`mul_lt_ftAngle`, which is what `n = 1` leaves: there the erased sum is empty and
the inequality is an equality. -/
theorem mul_le_ftAngle {n r : ℕ} {a : Fin n → ℝ} {τ θ : ℝ}
    (hsum : ftAngleSum a τ θ = r * θ + ((n - 1 : ℕ) : ℝ) * π) (i : Fin n) :
    (r : ℝ) * θ ≤ ftAngle (a i) τ θ := by
  classical
  rw [ftAngleSum] at hsum
  have hsplit : ftAngle (a i) τ θ + ∑ k ∈ Finset.univ.erase i, ftAngle (a k) τ θ
      = ∑ k, ftAngle (a k) τ θ :=
    Finset.add_sum_erase Finset.univ (fun k => ftAngle (a k) τ θ) (Finset.mem_univ i)
  have hcard : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hle : ∑ k ∈ Finset.univ.erase i, ftAngle (a k) τ θ
      ≤ ∑ _k ∈ Finset.univ.erase i, π :=
    Finset.sum_le_sum fun k _ => (ftAngle_lt_pi _ _ _).le
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hle
  rw [hsum] at hsplit
  linarith

/-- **The near case with the nonstrict angle bound.**  At `r ≥ 3` the last step
`\sin(π/(2(r-1))) < \sin(π/r)` is already strict, so `θ_a ≥ rθ` suffices where
`ftChord_lt_mul_sin` wanted `>`. -/
theorem ftChord_lt_mul_sin_of_le {r : ℕ} (hr : 3 ≤ r) {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hθ : θ ∈ Ioo 0 (π / r)) (hcase : a * Real.cos θ < τ)
    (hang : (r : ℝ) * θ ≤ ftAngle a τ θ) :
    ftChord a θ (ftAngle a τ θ) < a * Real.sin (π / r) := by
  have hπ := Real.pi_pos
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset (by omega) hθ
  set φ : ℝ := ftAngle a τ θ with hφdef
  have hφ : φ ∈ Ioo θ π := ftAngle_mem_Ioo ha hτ hθπ
  have hspec : a * Real.sin φ = τ * Real.sin (φ - θ) := ftAngle_spec (ne_of_gt hτ) hθπ
  have hR : 0 < ftChord a θ φ := ftChord_pos ha hθπ hφ
  have hsub0 : 0 < φ - θ := by linarith [hφ.1]
  have hcossub : ftChord a θ φ * Real.cos (φ - θ) = τ - a * Real.cos θ :=
    ftChord_mul_cos_sub hθπ hφ hspec
  have hacute : φ - θ < π / 2 := by
    by_contra hcon
    push Not at hcon
    have : Real.cos (φ - θ) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by linarith [hφ.2, hθπ.1])
    nlinarith
  have hrm : ((r : ℝ) - 1) * θ ≤ φ - θ := by nlinarith [hθ.1]
  have hm0 : 0 < ((r : ℝ) - 1) * θ := by nlinarith [hθ.1]
  have hsinle : Real.sin (((r : ℝ) - 1) * θ) ≤ Real.sin (φ - θ) :=
    sin_le_sin_of_le_pi_div_two (le_of_lt hm0) hrm (le_of_lt hacute)
  have hsinm : 0 < Real.sin (((r : ℝ) - 1) * θ) :=
    Real.sin_pos_of_pos_of_lt_pi hm0 (by linarith)
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  have hstep : ftChord a θ φ ≤ a * Real.sin θ / Real.sin (((r : ℝ) - 1) * θ) := by
    rw [ftChord]
    exact div_le_div_of_nonneg_left (by positivity) hsinm hsinle
  have hθle : θ ≤ π / (2 * ((r : ℝ) - 1)) := by
    rw [le_div_iff₀ (by nlinarith)]
    nlinarith
  have hratio := sin_div_sin_le (by omega) hθπ.1 hθle
  have hlast : Real.sin (π / (2 * ((r : ℝ) - 1))) < Real.sin (π / r) := by
    refine Real.strictMonoOn_sin ⟨by nlinarith [div_pos hπ (show (0:ℝ) < 2*((r:ℝ)-1) by nlinarith)],
      ?_⟩ ⟨by nlinarith [div_pos hπ hr0], ?_⟩ ?_
    · rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
    · rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith
    · rw [div_lt_div_iff₀ (by nlinarith) hr0]; nlinarith
  have hdiv : a * Real.sin θ / Real.sin (((r : ℝ) - 1) * θ)
      = a * (Real.sin θ / Real.sin (((r : ℝ) - 1) * θ)) := by ring
  rw [hdiv] at hstep
  nlinarith


/-- At `n = 1` the angle sum is a single angle and `(n-1)π = 0`, so the bound of
`mul_le_ftAngle` is an equality. -/
theorem ftAngle_eq_of_one {r : ℕ} {a : Fin 1 → ℝ} {τ θ : ℝ}
    (hsum : ftAngleSum a τ θ = r * θ + ((1 - 1 : ℕ) : ℝ) * π) :
    ftAngle (a 0) τ θ = (r : ℝ) * θ := by
  rw [ftAngleSum, Fin.sum_univ_one] at hsum
  simpa using hsum

/-- **The branch radius at `n = 1`, bounded by the first critical point.**  There
`τ(θ) = a\sin(rθ)/\sin((r-1)θ)` in closed form, and `sin_scaled_le` bounds the
ratio by `r/(r-1)`, which is `t_a/a`. -/
theorem ftTau_le_of_one {r : ℕ} (hr : 2 ≤ r) {a : Fin 1 → ℝ} {τ θ : ℝ} (ha : ∀ k, 0 < a k)
    (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 (π / r))
    (hsum : ftAngleSum a τ θ = r * θ + ((1 - 1 : ℕ) : ℝ) * π) :
    τ ≤ (r : ℝ) * a 0 / ((r : ℝ) - 1) := by
  have hπ := Real.pi_pos
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset (by omega) hθ
  have hφ := ftAngle_eq_of_one (r := r) (a := a) (τ := τ) (θ := θ) hsum
  have hratio := ftAngle_ratio (ha 0) hτ hθπ
  rw [hφ] at hratio
  have hrθπ : (r : ℝ) * θ ≤ π := by
    rw [← le_div_iff₀' hr0]
    exact le_of_lt hθ.2
  have hsubeq : (r : ℝ) * θ - θ = ((r : ℝ) - 1) * θ := by ring
  rw [hsubeq] at hratio
  have hm0 : 0 < ((r : ℝ) - 1) * θ := by nlinarith [hθ.1]
  have hsinm : 0 < Real.sin (((r : ℝ) - 1) * θ) :=
    Real.sin_pos_of_pos_of_lt_pi hm0 (by nlinarith [hθ.1])
  have hkey : ((r : ℝ) - 1) * Real.sin ((r : ℝ) * θ) ≤ (r : ℝ) * Real.sin (((r : ℝ) - 1) * θ) :=
    sin_scaled_le (by linarith) (by linarith) (le_of_lt hθ.1) hrθπ
  rw [← hratio, div_le_div_iff₀ hsinm (by linarith)]
  nlinarith [ha 0]

/-- The critical polynomial of a linear pencil: `E(s) = c((r-1)s - ra)`. -/
theorem eval_ftCriticalReal_one {r : ℕ} {c : ℝ} {a : Fin 1 → ℝ} (s : ℝ) :
    (ftCriticalReal (ftRootPolyReal c a) r).eval s = c * (((r : ℝ) - 1) * s - r * a 0) := by
  have hpoly : ftRootPolyReal c a = C c * (C (a 0) - X) := by
    rw [ftRootPolyReal, Fin.prod_univ_one]
  rw [eval_ftCriticalReal, hpoly]
  simp [derivative_mul]
  ring

/-- **The positive-real exclusion at `n = 1`.**  `E` is linear there, with its only
zero at `t_a = ra/(r-1)`, and `ftTau_le_of_one` puts the branch radius below it. -/
theorem negDivPow_lt_ftBranchZ_one {r : ℕ} (hr : 2 ≤ r) {a : Fin 1 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    {s : ℝ} (hs0 : 0 < s) (hsτ : s ≤ ftTau a r (1 - 1) θ) :
    -(ftRootPolyReal c a).eval s / s ^ r < ftBranchZ a c r (1 - 1) θ := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hb : FTBranchAt a r (1 - 1) θ :=
    ftBranchAt_of_arc_principal (by omega) ha (by omega) (Or.inr hr) hθ
  have hτ : 0 < ftTau a r (1 - 1) θ := ftTau_pos hb
  have hle := ftTau_le_of_one hr ha hτ hθ (ftAngleSum_ftTau hb)
  refine negDivPow_lt_ftBranchZ_of_ftCritical_neg (by omega) ha hc (by omega) (Or.inr hr)
    hθ ?_ hs0 hsτ
  intro u hu
  rw [eval_ftCriticalReal_one]
  have hult : u < (r : ℝ) * a 0 / ((r : ℝ) - 1) := lt_of_lt_of_le hu.2 hle
  rw [lt_div_iff₀ (by linarith)] at hult
  nlinarith [hc]


/-- **`hcone` at `n = 1` and `r ≥ 3`.**  The dichotomy of `FTGeometryCone` runs
unchanged; only the angle bound weakens, from `θ_a > rθ` to the equality `θ_a = rθ`
that a single angle leaves, and at `r ≥ 3` the closing comparison
`\sin(π/(2(r-1))) < \sin(π/r)` is already strict, so nothing is lost. -/
theorem cone_at_branch_one_of_three_le {r : ℕ} (hr : 3 ≤ r) {a : Fin 1 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∀ θ ∈ Ioo (0 : ℝ) (π / r), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (1 - 1) θ : ℝ) : ℂ)).eval w = 0 →
        ‖w‖ ≤ ftTau a r (1 - 1) θ → |Complex.arg w| ∈ Ioo 0 (π / r) := by
  classical
  intro θ hθ w hw hnorm
  have hπ := Real.pi_pos
  have hr1 : 1 ≤ r := by omega
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr1 hθ
  have hb : FTBranchAt a r (1 - 1) θ :=
    ftBranchAt_of_arc_principal (by omega) ha hr1 (Or.inr (by omega)) hθ
  set τ : ℝ := ftTau a r (1 - 1) θ with hτdef
  have hτ : 0 < τ := ftTau_pos hb
  set p : ℂ := ftPrincipal (ftTau a r (1 - 1)) θ with hpdef
  have hproot : (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (1 - 1) θ : ℝ) : ℂ)).eval p = 0 :=
    ftDen_eval_ftPrincipal_ftBranchZ c ha hθπ hb
  have hpnorm : ‖p‖ = τ := norm_ftPrincipal_eq hτ
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpnorm
    linarith
  have hw0 : w ≠ 0 := fun h => eval_ftDen_zero_ne_zero ha hc hr1 _ (h ▸ hw)
  have hargpos : 0 < |Complex.arg w| := by
    refine abs_pos.2 fun h0 => ?_
    obtain ⟨hre, him⟩ := Complex.arg_eq_zero_iff.1 h0
    have hwre : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hs0 : 0 < w.re := lt_of_le_of_ne hre fun h => hw0 (by rw [hwre, ← h]; simp)
    have hsτ : w.re ≤ τ := by
      have hn : ‖w‖ = |w.re| := by rw [hwre]; simp [Complex.norm_real, Real.norm_eq_abs]
      rw [hn, abs_of_pos hs0] at hnorm
      exact hnorm
    have hreal : (ftRootPolyReal c a).eval w.re
        + ftBranchZ a c r (1 - 1) θ * w.re ^ r = 0 := by
      have h := hw
      rw [hwre, eval_ftDen_ofReal] at h
      exact_mod_cast h
    have hval : -(ftRootPolyReal c a).eval w.re / w.re ^ r = ftBranchZ a c r (1 - 1) θ := by
      field_simp
      linarith [hreal]
    exact absurd hval
      (ne_of_lt (negDivPow_lt_ftBranchZ_one (by omega) ha hc hθ hs0 hsτ))
  refine ⟨hargpos, ?_⟩
  have hmin : ∀ k, a 0 ≤ a k := fun k => le_of_eq (congrArg a (Subsingleton.elim 0 k))
  have hC2 : ‖w - ((a 0 : ℝ) : ℂ)‖ ≤ ‖p - ((a 0 : ℝ) : ℂ)‖ :=
    norm_sub_min_le_of_root (by omega) ha (ne_of_gt hc) hw0 hp0
      (by rw [hpnorm]; exact hnorm) hw hproot hmin
  have hpsq : ‖p - ((a 0 : ℝ) : ℂ)‖ ^ 2 = τ ^ 2 - 2 * τ * a 0 * Real.cos θ + a 0 ^ 2 :=
    norm_sub_upperArc_sq τ θ (a 0)
  rcases le_or_gt τ (a 0 * Real.cos θ) with hcase | hcase
  · have hdisk : ‖w - ((a 0 : ℝ) : ℂ)‖ ^ 2 ≤ τ ^ 2 - 2 * τ * a 0 * Real.cos θ + a 0 ^ 2 := by
      rw [← hpsq]
      exact pow_le_pow_left₀ (norm_nonneg _) hC2 2
    exact lt_of_le_of_lt
      (abs_arg_le_of_le_mul_cos (ha 0) hθπ hcase hw0 hnorm hdisk) hθ.2
  · have hang : (r : ℝ) * θ ≤ ftAngle (a 0) τ θ := mul_le_ftAngle (ftAngleSum_ftTau hb) 0
    have hchord := ftChord_lt_mul_sin_of_le hr (ha 0) hτ hθ hcase hang
    have heq : ftChord (a 0) θ (ftAngle (a 0) τ θ)
        = Real.sqrt (a 0 ^ 2 - 2 * a 0 * τ * Real.cos θ + τ ^ 2) :=
      ftChord_eq_sqrt (ha 0) hτ hθπ
    have hpeq : ‖p - ((a 0 : ℝ) : ℂ)‖ = ftChord (a 0) θ (ftAngle (a 0) τ θ) := by
      rw [heq, ← Real.sqrt_sq (norm_nonneg (p - ((a 0 : ℝ) : ℂ))), hpsq]
      congr 1
      ring
    refine abs_arg_lt_of_norm_sub_le (ha 0) ⟨div_pos hπ hr0, ?_⟩ ?_ hC2
    · rw [div_le_div_iff₀ hr0 (by norm_num)]
      nlinarith
    · rw [hpeq]
      exact hchord

/-- **`hmin` at `n = 1`, `r ≥ 3`.** -/
theorem ft_minModulus_at_branch_one_of_three_le {r : ℕ} (hr : 3 ≤ r) {a : Fin 1 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∀ θ ∈ Ioo (0 : ℝ) (π / r), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (1 - 1) θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTau a r (1 - 1)) θ →
        w ≠ (starRingEnd ℂ) (ftPrincipal (ftTau a r (1 - 1)) θ) →
        ftTau a r (1 - 1) θ < ‖w‖ :=
  ft_minModulus_at_branch_of_or (by omega) ha hc (by omega) (Or.inr (by omega))
    (cone_at_branch_one_of_three_le hr ha hc)


/-- `\sin(kθ)/θ → k` at the origin, the slope of `\sin` at `0` rescaled. -/
theorem tendsto_sin_mul_div (k : ℝ) :
    Filter.Tendsto (fun θ : ℝ => Real.sin (k * θ) / θ) (𝓝[≠] (0 : ℝ)) (𝓝 k) := by
  have hd : HasDerivAt (fun θ : ℝ => Real.sin (k * θ)) k 0 := by
    have h := (Real.hasDerivAt_sin (k * 0)).comp 0
      (by simpa using (hasDerivAt_id (0 : ℝ)).const_mul k)
    simpa [Function.comp_def] using h
  refine (hasDerivAt_iff_tendsto_slope.1 hd).congr fun x => ?_
  rw [slope_def_field]
  simp

/-- **The branch radius at `n = 1`, in closed form.**  A single angle makes the
branch equation `θ_1 = rθ`, and `ftAngle_ratio` then solves for `τ`. -/
theorem ftTau_eq_of_one {r : ℕ} (hr : 2 ≤ r) {a : Fin 1 → ℝ} (ha : ∀ k, 0 < a k)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    ftTau a r (1 - 1) θ = a 0 * Real.sin ((r : ℝ) * θ) / Real.sin (((r : ℝ) - 1) * θ) := by
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset (by omega) hθ
  have hb : FTBranchAt a r (1 - 1) θ :=
    ftBranchAt_of_arc_principal (by omega) ha (by omega) (Or.inr hr) hθ
  have hτ : 0 < ftTau a r (1 - 1) θ := ftTau_pos hb
  have hφ := ftAngle_eq_of_one (ftAngleSum_ftTau hb)
  have hratio := ftAngle_ratio (ha 0) hτ hθπ
  rw [hφ, show (r : ℝ) * θ - θ = ((r : ℝ) - 1) * θ from by ring] at hratio
  exact hratio.symm

/-- **The lower-endpoint limit of the radius at `n = 1`**: `τ(θ) → ra/(r-1)`, which
is the first positive critical point of `g` there. -/
theorem tendsto_ftTau_one {r : ℕ} (hr : 2 ≤ r) {a : Fin 1 → ℝ} (ha : ∀ k, 0 < a k) :
    Filter.Tendsto (ftTau a r (1 - 1)) (𝓝[Ioo 0 (π / r)] (0 : ℝ))
      (𝓝 ((r : ℝ) * a 0 / ((r : ℝ) - 1))) := by
  have hπ := Real.pi_pos
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hsub : 𝓝[Ioo 0 (π / r)] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ fun x hx => ne_of_gt hx.1
  have hnum := (tendsto_sin_mul_div (r : ℝ)).mono_left hsub
  have hden := (tendsto_sin_mul_div ((r : ℝ) - 1)).mono_left hsub
  have hmul : Filter.Tendsto
      (fun θ : ℝ => a 0 * (Real.sin ((r : ℝ) * θ) / θ / (Real.sin (((r : ℝ) - 1) * θ) / θ)))
      (𝓝[Ioo 0 (π / r)] (0 : ℝ)) (𝓝 (a 0 * ((r : ℝ) / ((r : ℝ) - 1)))) :=
    (hnum.div hden (by linarith)).const_mul (a 0)
  have hval : a 0 * ((r : ℝ) / ((r : ℝ) - 1)) = (r : ℝ) * a 0 / ((r : ℝ) - 1) := by
    field_simp
  rw [hval] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset (by omega) hθ
  have hm0 : 0 < ((r : ℝ) - 1) * θ := by nlinarith [hθ.1]
  have hsinm : 0 < Real.sin (((r : ℝ) - 1) * θ) :=
    Real.sin_pos_of_pos_of_lt_pi hm0 (by nlinarith [hθ.1, hθ.2, (lt_div_iff₀ hr0).1 hθ.2])
  have hθ0 : θ ≠ 0 := ne_of_gt hθ.1
  have hsm0 : Real.sin (((r : ℝ) - 1) * θ) ≠ 0 := ne_of_gt hsinm
  have hcancel : Real.sin ((r : ℝ) * θ) / θ / (Real.sin (((r : ℝ) - 1) * θ) / θ)
      = Real.sin ((r : ℝ) * θ) / Real.sin (((r : ℝ) - 1) * θ) := by
    field_simp
  rw [ftTau_eq_of_one hr ha hθ, hcancel, mul_div_assoc]

/-- **`hza` at `n = 1`.**  `tendsto_ftBranchZ_lower` transports the radius limit to
the spectral parameter. -/
theorem tendsto_ftBranchZ_arc_zero_one {r : ℕ} (hr : 2 ≤ r) {a : Fin 1 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) :
    Filter.Tendsto (ftBranchZ a c r (1 - 1)) (𝓝[Ioo 0 (π / r)] (0 : ℝ))
      (𝓝 (-(ftRootPolyReal c a).eval ((r : ℝ) * a 0 / ((r : ℝ) - 1))
        / ((r : ℝ) * a 0 / ((r : ℝ) - 1)) ^ r)) := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hL : 0 < (r : ℝ) * a 0 / ((r : ℝ) - 1) := by
    have := ha 0
    apply div_pos (by nlinarith) (by linarith)
  refine tendsto_ftBranchZ_lower ha hL ?_ (tendsto_ftTau_one hr ha)
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  exact ⟨ftArc_subset (by omega) hθ,
    ftBranchAt_of_arc_principal (by omega) ha (by omega) (Or.inr hr) hθ⟩


/-- **`hmin` at `n = 1`, every `r ≥ 2`.**  `r = 2` is the degree count and `r ≥ 3`
is the cone; the two are exhaustive. -/
theorem ft_minModulus_at_branch_linear {r : ℕ} (hr : 2 ≤ r) {a : Fin 1 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∀ θ ∈ Ioo (0 : ℝ) (π / r), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (1 - 1) θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTau a r (1 - 1)) θ →
        w ≠ (starRingEnd ℂ) (ftPrincipal (ftTau a r (1 - 1)) θ) →
        ftTau a r (1 - 1) θ < ‖w‖ := by
  rcases eq_or_lt_of_le hr with h | h
  · exact ft_minModulus_at_branch_of_deg_le_two (by omega) ha hc (by omega) (Or.inr hr) (by omega)
  · exact ft_minModulus_at_branch_one_of_three_le (by omega) ha hc

/-- **`thm:FT-geometry` at `n = 1`, every `r ≥ 2`, with no analytic hypothesis.**
The unbounded convention of `eq:ab-def`, which is the only one `r > 1` reaches. -/
theorem ft_geometry_unbounded_at_branch_one {r : ℕ} (hr : 2 ≤ r) {a : Fin 1 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ za : ℝ,
      ftBranchZ a c r (1 - 1) '' Ioo 0 (π / r) = Ioi za
        ∧ (∀ θ ∈ Ioo 0 (π / r),
            (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (1 - 1) θ : ℝ) : ℂ)).eval
                (ftPrincipal (ftTau a r (1 - 1)) θ) = 0
              ∧ (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (1 - 1) θ : ℝ) : ℂ)).eval
                  ((starRingEnd ℂ) (ftPrincipal (ftTau a r (1 - 1)) θ)) = 0
              ∧ ‖ftPrincipal (ftTau a r (1 - 1)) θ‖ = ftTau a r (1 - 1) θ
              ∧ ‖(starRingEnd ℂ) (ftPrincipal (ftTau a r (1 - 1)) θ)‖
                  = ftTau a r (1 - 1) θ)
        ∧ (∀ θ ∈ Ioo 0 (π / r), ∀ w : ℂ,
            (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (1 - 1) θ : ℝ) : ℂ)).eval w = 0 →
              ‖w‖ ≤ ftTau a r (1 - 1) θ →
                w = ftPrincipal (ftTau a r (1 - 1)) θ
                  ∨ w = (starRingEnd ℂ) (ftPrincipal (ftTau a r (1 - 1)) θ)) := by
  obtain ⟨hroot, hpos, hmono, hcont⟩ :=
    ft_branch_supplies (a := a) (c := c) (by omega) ha hc (by omega) (Or.inr hr)
  exact ⟨_, ft_geometry_unbounded (hasRealCoeffs_ftRootPoly c a) (by omega) hroot hpos hmono
    hcont (tendsto_ftBranchZ_arc_zero_one hr ha)
    (tendsto_ftBranchZ_atTop_arc_end_of_pos (by omega) ha hc hr)
    (ft_minModulus_at_branch_linear hr ha hc)⟩

end ForgacsTran
