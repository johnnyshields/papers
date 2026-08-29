/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchSupplyWitness
import ForgacsTran.PhaseTangency
import ForgacsTran.PencilIndex

/-!
# The root states at the Favard witness

`BranchSupply.RootBranchState` is the one group of
`exists_uniform_ftBranchSupply` with **no producer anywhere in the tree** — outside
`BranchSupply` the name occurs only in hypothesis positions, so every result above it
asserted a class nobody had shown inhabited.  This module inhabits it, at
`BranchSupplyWitness`'s pencil: `Q = 1 - 4t + t²`, `r = 1`, `B = t² + 1`, `τ ≡ 1`, where
the branch is the unit semicircle `γ(θ) = e^{iθ}` and `B`'s roots are `±i` — one on the
arc, at `θ = π/2`, one off it.

**The tangency sets are empty, and computably so.**  A tangency is
`arg(γ') - arg(γ - β) ∈ πℤ`: the chord from `β` parallel to the tangent.  Both roots lie
**on** the unit circle, so the inscribed-angle theorem applies and
`Im(γ'/(γ - β)) = 1/2` identically — the chord turns at exactly half the tangent's rate.
Both branches are therefore affine, and the difference runs

| region | base | difference | multiples of `π` inside |
|---|---|---|---|
| `(0, π)`, at `-i` | `0` | `π/4 + x/2` | none |
| `(0, π/2)`, at `i` | `0` | `3π/4 + x/2` | none |
| `(π/2, π)`, at `i` | `π` | `7π/4 + x/2` | none |

Each range is an open interval of length `π/2` positioned strictly between consecutive
multiples of `π`, touching one only in the limit `x → π/2` — the collision, which every
region excludes.  So nothing here needs the general finiteness of the tangency set:
the sets are empty and the `Finset` is `∅`.

**The nonvanishing has to be asked on CLOSED blocks, degenerate ones included.**
`RootBranchState`'s second disjunct asks every block to sit inside `Ico a m` or `Ioc m b`,
with no `Lb i < Rb i` guard on the `∀ i`.  A block `[π/2, π/2]` sits in neither, and
`not_rootBranchState_I_of_degenerate` proves no `ψ` then exists — so a producer whose
nonvanishing clause is **guarded** by `Lb i < Rb i` lets that block through every condition
that would exclude it, and its `hstates` is false at this pencil rather than merely
unproved.  Asking nonvanishing unguarded excludes it by hypothesis, since the arc meets `i`
there; `fav_rootStates` takes that form, and it is
`PhaseTangency.sum_eVariationOn_of_curvature`'s `hfree` verbatim, so the two lemmas already
agree about what a block has to satisfy.

**The curvature hypothesis is free here**, and `fav_curvature` records it: `wedge γ'' γ'`
is the quantity `τ² + 2τ'² - ττ''`, which is `1` at `τ ≡ 1`.  Nothing below consumes it —
an empty tangency set is stronger than a finite one — but it is what makes the general
route available at this pencil too.

## Main statements

* `fav_tangentRate`, `fav_chordRate_sub_I`, `fav_chordRate_add_I` — the two constant
  rates, `1` and `1/2`.
* `polarAngle_self`, `polarAngle_eq_of_constant_rate` — a branch with constant rate is
  affine, with any base point of the interval.
* `fav_tangentAngle`, `fav_chordAngle_neg_I`, `fav_chordAngle_I_lower`,
  `fav_chordAngle_I_upper` — the four branches in closed form.
* `fav_no_tangency_neg_I`, `fav_no_tangency_I_lower`, `fav_no_tangency_I_upper` — the
  three tangency sets are empty.
* `fav_rootBranchState_neg_I`, `fav_rootBranchState_I`, `fav_rootStates` — the states,
  and the group.
* `fav_curvature` — `hcurv` at this pencil, by arithmetic.
* `not_rootBranchState_I_of_degenerate` — why the group needs the guard.

`../scripts/check_favard_root_states.py` measures the four closed forms and the three
ranges before they are asserted here.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`,
`cor:linear-phase-variation`, `eq:linear-phase-variation`, `eq:viewing-angle-bound`.

## Tags

root state, viewing angle, tangency, non-vacuity, Forgács–Tran
-/
namespace ForgacsTran

open Polynomial Set Real Complex

/-! ### Both integrands are constant, and that is the inscribed-angle theorem -/

/-- The turning rate of the tangent is `1`: `γ'' / γ' = i` identically, because
`γ' = ie^{iθ}` and `γ'' = i²e^{iθ}`. -/
theorem fav_tangentRate (u : ℝ) :
    ((Complex.exp ((u : ℂ) * I) * I * I) / (Complex.exp ((u : ℂ) * I) * I - 0)).im = 1 := by
  have hne : Complex.exp ((u : ℂ) * I) * I ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero
  have hq : Complex.exp ((u : ℂ) * I) * I * I / (Complex.exp ((u : ℂ) * I) * I - 0) = I := by
    rw [sub_zero]
    field_simp
  rw [hq]
  simp

/-- **The chord from a point of the circle turns at half the rate.**  For `β` on the
unit circle, `Im(γ'/(γ - β)) = 1/2` wherever `γ ≠ β` — the inscribed-angle theorem,
and the whole reason the tangency set is computable here rather than merely finite. -/
theorem fav_chordRate_sub_I {u : ℝ} (h : Real.sin u ≠ 1) :
    ((Complex.exp ((u : ℂ) * I) * I) / (Complex.exp ((u : ℂ) * I) - I)).im = 1 / 2 := by
  have hre : (Complex.exp ((u : ℂ) * I)).re = Real.cos u := Complex.exp_ofReal_mul_I_re u
  have him : (Complex.exp ((u : ℂ) * I)).im = Real.sin u := Complex.exp_ofReal_mul_I_im u
  have hpy : Real.cos u ^ 2 + Real.sin u ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq u
  have hN : (Complex.normSq (Complex.exp ((u : ℂ) * I) - I)) = 2 - 2 * Real.sin u := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hre, him]
    nlinarith [hpy]
  have hNpos : (0 : ℝ) < 2 - 2 * Real.sin u := by
    have := Real.neg_one_le_sin u
    have h2 := Real.sin_le_one u
    rcases lt_or_eq_of_le h2 with hlt | heq
    · linarith
    · exact absurd heq h
  have hNne : (2 : ℝ) - 2 * Real.sin u ≠ 0 := ne_of_gt hNpos
  have h1s : (1 : ℝ) - Real.sin u ≠ 0 := by
    intro h0; exact hNne (by linarith)
  rw [Complex.div_im, hN]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.I_re, Complex.I_im, hre, him]
  field_simp
  nlinarith [hpy]

/-- The same at the root the arc misses. -/
theorem fav_chordRate_add_I {u : ℝ} (h : Real.sin u ≠ -1) :
    ((Complex.exp ((u : ℂ) * I) * I) / (Complex.exp ((u : ℂ) * I) - -I)).im = 1 / 2 := by
  have hre : (Complex.exp ((u : ℂ) * I)).re = Real.cos u := Complex.exp_ofReal_mul_I_re u
  have him : (Complex.exp ((u : ℂ) * I)).im = Real.sin u := Complex.exp_ofReal_mul_I_im u
  have hpy : Real.cos u ^ 2 + Real.sin u ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq u
  have hN : (Complex.normSq (Complex.exp ((u : ℂ) * I) - -I)) = 2 + 2 * Real.sin u := by
    simp [Complex.normSq_apply, hre, him]
    nlinarith [hpy]
  have hNpos : (0 : ℝ) < 2 + 2 * Real.sin u := by
    have := Real.neg_one_le_sin u
    rcases lt_or_eq_of_le this with hlt | heq
    · linarith
    · exact absurd heq.symm h
  have hNne : (2 : ℝ) + 2 * Real.sin u ≠ 0 := ne_of_gt hNpos
  have h1s : (1 : ℝ) + Real.sin u ≠ 0 := by
    intro h0; exact hNne (by linarith)
  rw [Complex.div_im, hN]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, hre, him]
  field_simp
  nlinarith [hpy]

/-! ### A polar angle with constant rate is affine -/

/-- At its own base point the branch is the principal argument: the integral is over a
degenerate interval. -/
theorem polarAngle_self (G dG : ℝ → ℂ) (β : ℂ) (a : ℝ) :
    polarAngle G dG β a a = (Complex.log (G a - β)).im := by
  simp [polarAngle, logLift]

/-- **The branch is affine wherever `Im(γ'/(γ-β))` is constant.**  Both branches this
witness needs have constant rate — `1` for the tangent, `1/2` for a chord from a point
of the circle — so each is determined by its value at the base point and nothing has to
be integrated.

The base point is any point of the interval, not necessarily an endpoint: the upper
side of the collision takes its branch based at `π`, the right end. -/
theorem polarAngle_eq_of_constant_rate {G dG : ℝ → ℂ} {β : ℂ} {U : Set ℝ} {p q c base : ℝ}
    (hU : IsOpen U) (hsub : Icc p q ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt G (dG s) s) (hcont : ContinuousOn dG U)
    (hne : ∀ s ∈ Icc p q, G s ≠ β) (hbase : base ∈ Icc p q)
    (hrate : ∀ s ∈ Icc p q, (dG s / (G s - β)).im = c) :
    ∀ x ∈ Icc p q, polarAngle G dG β base x
      = (Complex.log (G base - β)).im + c * (x - base) := by
  intro x hx
  have hderiv : ∀ t ∈ Icc p q,
      HasDerivAt (fun y : ℝ => polarAngle G dG β base y - c * y) 0 t := by
    intro t ht
    have h1 := hasDerivAt_polarAngle_base hU hsub hd hcont hne hbase ht
    rw [hrate t ht] at h1
    have h2 : HasDerivAt (fun y : ℝ => c * y) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    have h3 : HasDerivAt (fun y : ℝ => polarAngle G dG β base y - c * y) (c - c) t :=
      h1.sub h2
    rwa [sub_self] at h3
  have hbd := (convex_Icc p q).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => polarAngle G dG β base y - c * y) (f' := fun _ => (0 : ℝ)) (C := 0)
    (fun t ht => (hderiv t ht).hasDerivWithinAt) (fun t _ => by simp) hbase hx
  have hz : (polarAngle G dG β base x - c * x)
      - (polarAngle G dG β base base - c * base) = 0 :=
    norm_le_zero_iff.1 (by simpa using hbd)
  rw [polarAngle_self] at hz
  linarith

/-! ### The four base angles -/

private theorem one_div_sqrt_two : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp
  linarith [h2]

private theorem arcsin_sqrt_two_div_two : Real.arcsin (Real.sqrt 2 / 2) = π / 4 := by
  rw [← Real.sin_pi_div_four,
    Real.arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]

private theorem norm_one_sub_I : ‖(1 : ℂ) - I‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  norm_num

private theorem norm_one_add_I : ‖(1 : ℂ) + I‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  norm_num

private theorem norm_neg_one_sub_I : ‖(-1 : ℂ) - I‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  norm_num

theorem arg_one_sub_I : Complex.arg ((1 : ℂ) - I) = -(π / 4) := by
  rw [Complex.arg_of_re_nonneg (by norm_num), norm_one_sub_I,
    show ((1 : ℂ) - I).im = -1 by norm_num,
    show (-1 : ℝ) / Real.sqrt 2 = -(1 / Real.sqrt 2) by ring,
    Real.arcsin_neg, one_div_sqrt_two, arcsin_sqrt_two_div_two]

theorem arg_one_add_I : Complex.arg ((1 : ℂ) + I) = π / 4 := by
  rw [Complex.arg_of_re_nonneg (by norm_num), norm_one_add_I,
    show ((1 : ℂ) + I).im = 1 by norm_num, one_div_sqrt_two, arcsin_sqrt_two_div_two]

theorem arg_neg_one_sub_I : Complex.arg ((-1 : ℂ) - I) = -(3 * π / 4) := by
  rw [Complex.arg_of_re_neg_of_im_neg (by norm_num) (by norm_num), norm_neg_one_sub_I,
    show (-((-1 : ℂ) - I)).im = 1 by norm_num, one_div_sqrt_two, arcsin_sqrt_two_div_two]
  ring

/-! ### The branch data, named -/

/-- The tangent field of the Favard branch, `γ' = ie^{iθ}`. -/
noncomputable def favDGamma (s : ℝ) : ℂ := Complex.exp ((s : ℂ) * I) * I

/-- Its derivative, `γ'' = i²e^{iθ}`. -/
noncomputable def favD2Gamma (s : ℝ) : ℂ := Complex.exp ((s : ℂ) * I) * I * I

theorem hasDerivAt_favGamma (s : ℝ) : HasDerivAt (ftPrincipal witTau) (favDGamma s) s :=
  fav_branch_C2.1 s

theorem hasDerivAt_favDGamma (s : ℝ) : HasDerivAt favDGamma (favD2Gamma s) s :=
  fav_branch_C2.2.1 s

theorem favDGamma_ne_zero (s : ℝ) : favDGamma s ≠ 0 := fav_branch_C2.2.2.2 s

theorem continuousOn_favDGamma (S : Set ℝ) : ContinuousOn favDGamma S :=
  fun s _ => (hasDerivAt_favDGamma s).continuousAt.continuousWithinAt

theorem continuousOn_favD2Gamma (S : Set ℝ) : ContinuousOn favD2Gamma S :=
  fun _s _ => fav_branch_C2.2.2.1.continuousAt.continuousWithinAt

/-! ### Where the arc meets the roots of `B` -/

/-- The arc reaches `i` exactly once, at `π/2`.  `SimpleWitness` proves the two halves
separately — the value there and the amplitude's divisor — and this is the statement in
the form the root state's case split needs. -/
theorem favGamma_eq_I_iff {x : ℝ} (hx : x ∈ Icc (0 : ℝ) π) :
    ftPrincipal witTau x = I ↔ x = π / 2 := by
  constructor
  · intro h
    have hre : Real.cos x = 0 := by
      have := congrArg Complex.re h
      rwa [ftPrincipal_witTau, Complex.exp_ofReal_mul_I_re, Complex.I_re] at this
    have hpi := Real.pi_pos
    exact Real.injOn_cos ⟨hx.1, hx.2⟩ ⟨by linarith, by linarith⟩
      (by rw [hre, Real.cos_pi_div_two])
  · rintro rfl
    exact ftPrincipal_witTau_pi_div_two

/-- Off the collision the chord rate's hypothesis holds. -/
theorem fav_sin_ne_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) π) (hne : x ≠ π / 2) :
    Real.sin x ≠ 1 := by
  intro h
  refine hne ?_
  have hpy : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have hc : Real.cos x = 0 := by nlinarith [hpy]
  have hpi := Real.pi_pos
  exact Real.injOn_cos ⟨hx.1, hx.2⟩ ⟨by linarith, by linarith⟩
    (by rw [hc, Real.cos_pi_div_two])

/-- The other root is never reached, because the upper semicircle has `sin ≥ 0`. -/
theorem fav_sin_ne_neg_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) π) : Real.sin x ≠ -1 := by
  have := Real.sin_nonneg_of_mem_Icc ⟨hx.1, hx.2⟩
  intro h
  rw [h] at this
  linarith

/-! ### The three branches, in closed form -/

/-- The tangent's argument advances at rate one: `Θ(x) = π/2 + x`. -/
theorem fav_tangentAngle {x : ℝ} (hx : x ∈ Icc (0 : ℝ) π) :
    polarAngle favDGamma favD2Gamma 0 0 x = π / 2 + x := by
  have hbase : (0 : ℝ) ∈ Icc (0 : ℝ) π := ⟨le_rfl, Real.pi_pos.le⟩
  have h := polarAngle_eq_of_constant_rate (G := favDGamma) (dG := favD2Gamma) (β := 0)
    (U := univ) (p := 0) (q := π) (c := 1) (base := 0) isOpen_univ (subset_univ _)
    (fun s _ => hasDerivAt_favDGamma s) (continuousOn_favD2Gamma _)
    (fun s _ => favDGamma_ne_zero s) hbase (fun s _ => fav_tangentRate s) x hx
  rw [h, show favDGamma 0 - 0 = I by simp [favDGamma], Complex.log_im, Complex.arg_I]
  ring

/-- The chord from the missed root: `Ψ⁻(x) = π/4 + x/2`. -/
theorem fav_chordAngle_neg_I {x : ℝ} (hx : x ∈ Icc (0 : ℝ) π) :
    polarAngle (ftPrincipal witTau) favDGamma (-I) 0 x = π / 4 + x / 2 := by
  have hbase : (0 : ℝ) ∈ Icc (0 : ℝ) π := ⟨le_rfl, Real.pi_pos.le⟩
  have h := polarAngle_eq_of_constant_rate (G := ftPrincipal witTau) (dG := favDGamma)
    (β := -I) (U := univ) (p := 0) (q := π) (c := 1 / 2) (base := 0)
    isOpen_univ (subset_univ _) (fun s _ => hasDerivAt_favGamma s)
    (continuousOn_favDGamma _) (fun s hs => fav_roots_meet.2 s hs) hbase
    (fun s hs => by
      rw [ftPrincipal_witTau]
      exact fav_chordRate_add_I (fav_sin_ne_neg_one hs)) x hx
  rw [h, show ftPrincipal witTau 0 - -I = 1 + I by
      rw [ftPrincipal_witTau]; simp, Complex.log_im, arg_one_add_I]
  ring

theorem favGamma_pi : ftPrincipal witTau π = -1 := by
  rw [ftPrincipal_witTau]
  simp

/-- The chord from the met root, based at `0`, on the lower side of the collision:
`Ψ₀(x) = -π/4 + x/2`.  It reaches only up to a point short of `π/2`, which is all the
lower blocks need. -/
theorem fav_chordAngle_I_lower {y x : ℝ} (hy0 : 0 ≤ y) (hy : y < π / 2)
    (hx : x ∈ Icc (0 : ℝ) y) :
    polarAngle (ftPrincipal witTau) favDGamma I 0 x = -(π / 4) + x / 2 := by
  have hpi := Real.pi_pos
  have hyπ : y ≤ π := by linarith
  have hsub : ∀ s ∈ Icc (0 : ℝ) y, s ∈ Icc (0 : ℝ) π := fun s hs =>
    ⟨hs.1, le_trans hs.2 hyπ⟩
  have hne2 : ∀ s ∈ Icc (0 : ℝ) y, s ≠ π / 2 := fun s hs => by
    have : s ≤ y := hs.2
    intro h; rw [h] at this; linarith
  have hbase : (0 : ℝ) ∈ Icc (0 : ℝ) y := ⟨le_rfl, hy0⟩
  have h := polarAngle_eq_of_constant_rate (G := ftPrincipal witTau) (dG := favDGamma)
    (β := I) (U := univ) (p := 0) (q := y) (c := 1 / 2) (base := 0)
    isOpen_univ (subset_univ _) (fun s _ => hasDerivAt_favGamma s)
    (continuousOn_favDGamma _)
    (fun s hs => fun hcon => hne2 s hs ((favGamma_eq_I_iff (hsub s hs)).1 hcon)) hbase
    (fun s hs => by
      rw [ftPrincipal_witTau]
      exact fav_chordRate_sub_I (fav_sin_ne_one (hsub s hs) (hne2 s hs))) x hx
  rw [h, show ftPrincipal witTau 0 - I = 1 - I by rw [ftPrincipal_witTau]; simp,
    Complex.log_im, arg_one_sub_I]
  ring

/-- The same on the upper side, based at `π`: `Ψ_π(x) = -3π/4 + (x-π)/2`.  The base point
travels with the side because no single one is reachable across the collision. -/
theorem fav_chordAngle_I_upper {y x : ℝ} (hy : π / 2 < y) (hyπ : y ≤ π)
    (hx : x ∈ Icc y π) :
    polarAngle (ftPrincipal witTau) favDGamma I π x = -(3 * π / 4) + (x - π) / 2 := by
  have hpi := Real.pi_pos
  have hsub : ∀ s ∈ Icc y π, s ∈ Icc (0 : ℝ) π := fun s hs =>
    ⟨le_trans (by linarith) hs.1, hs.2⟩
  have hne2 : ∀ s ∈ Icc y π, s ≠ π / 2 := fun s hs => by
    have : y ≤ s := hs.1
    intro h; rw [h] at this; linarith
  have hbase : π ∈ Icc y π := ⟨hyπ, le_rfl⟩
  have h := polarAngle_eq_of_constant_rate (G := ftPrincipal witTau) (dG := favDGamma)
    (β := I) (U := univ) (p := y) (q := π) (c := 1 / 2) (base := π)
    isOpen_univ (subset_univ _) (fun s _ => hasDerivAt_favGamma s)
    (continuousOn_favDGamma _)
    (fun s hs => fun hcon => hne2 s hs ((favGamma_eq_I_iff (hsub s hs)).1 hcon)) hbase
    (fun s hs => by
      rw [ftPrincipal_witTau]
      exact fav_chordRate_sub_I (fav_sin_ne_one (hsub s hs) (hne2 s hs))) x hx
  rw [h, show ftPrincipal witTau π - I = -1 - I by rw [favGamma_pi],
    Complex.log_im, arg_neg_one_sub_I]
  ring

/-! ### The three tangency sets are empty

The condition `Θ(x) - Ψ(x) ∈ πℤ` says the chord from the root is parallel to the
tangent.  Both angles are affine with slopes `1` and `1/2`, so the difference is affine
with slope `1/2` and travels less than `π` over the whole arc; where it starts decides
everything, and in all three regions it starts and ends strictly between consecutive
multiples of `π`.  The one place it does reach a multiple is `x = π/2`, the collision —
which every region excludes. -/

private theorem no_int_mul_pi_of_mem_Ioo {t : ℝ} {n : ℤ} (hlo : (n : ℝ) * π < t)
    (hhi : t < ((n : ℝ) + 1) * π) {j : ℤ} (h : t = (j : ℝ) * π) : False := by
  have hpi := Real.pi_pos
  rw [h] at hlo hhi
  have h1 : (n : ℝ) < (j : ℝ) := by
    by_contra hc
    push Not at hc
    nlinarith
  have h2 : (j : ℝ) < (n : ℝ) + 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have e1 : n < j := by exact_mod_cast h1
  have e2 : j < n + 1 := by exact_mod_cast h2
  omega

/-- No tangency at the missed root: the difference runs inside `(0, π)`. -/
theorem fav_no_tangency_neg_I {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) π) (j : ℤ)
    (h : polarAngle favDGamma favD2Gamma 0 0 x
      - polarAngle (ftPrincipal witTau) favDGamma (-I) 0 x = (j : ℝ) * π) : False := by
  have hpi := Real.pi_pos
  have hmem : x ∈ Icc (0 : ℝ) π := ⟨hx.1.le, hx.2.le⟩
  rw [fav_tangentAngle hmem, fav_chordAngle_neg_I hmem] at h
  refine no_int_mul_pi_of_mem_Ioo (n := 0) (t := π / 2 + x - (π / 4 + x / 2)) ?_ ?_ h
  · push_cast; linarith [hx.1]
  · push_cast; linarith [hx.2]

/-- No tangency below the collision: the difference runs inside `(3π/4, π)`, and the
right-hand end is `π` only in the limit `x → π/2`, which the open block excludes. -/
theorem fav_no_tangency_I_lower {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (π / 2)) (j : ℤ)
    (h : polarAngle favDGamma favD2Gamma 0 0 x
      - polarAngle (ftPrincipal witTau) favDGamma I 0 x = (j : ℝ) * π) : False := by
  have hpi := Real.pi_pos
  have hmem : x ∈ Icc (0 : ℝ) π := ⟨hx.1.le, by linarith [hx.2]⟩
  rw [fav_tangentAngle hmem,
    fav_chordAngle_I_lower (y := x) (x := x) hx.1.le hx.2 ⟨hx.1.le, le_rfl⟩] at h
  refine no_int_mul_pi_of_mem_Ioo (n := 0) (t := π / 2 + x - (-(π / 4) + x / 2)) ?_ ?_ h
  · push_cast; linarith [hx.1]
  · push_cast; linarith [hx.2]

/-- No tangency above it either: the difference runs inside `(2π, 9π/4)`, and the
left-hand end is `2π` only in the limit `x → π/2`. -/
theorem fav_no_tangency_I_upper {x : ℝ} (hx : x ∈ Ioo (π / 2) π) (j : ℤ)
    (h : polarAngle favDGamma favD2Gamma 0 0 x
      - polarAngle (ftPrincipal witTau) favDGamma I π x = (j : ℝ) * π) : False := by
  have hpi := Real.pi_pos
  have hmem : x ∈ Icc (0 : ℝ) π := ⟨by linarith [hx.1], hx.2.le⟩
  rw [fav_tangentAngle hmem,
    fav_chordAngle_I_upper (y := x) (x := x) hx.1 hx.2.le ⟨le_rfl, hx.2.le⟩] at h
  refine no_int_mul_pi_of_mem_Ioo (n := 2)
    (t := π / 2 + x - (-(3 * π / 4) + (x - π) / 2)) ?_ ?_ h
  · push_cast; linarith [hx.1]
  · push_cast; linarith [hx.2]

/-! ### The two root states -/

theorem mem_favB_roots_iff {β : ℂ} : β ∈ favB.roots ↔ β = I ∨ β = -I := by
  rw [Polynomial.mem_roots favB_ne_zero, Polynomial.IsRoot, favB_eval]
  constructor
  · intro h
    have hfac : (β - I) * (β + I) = 0 := by
      have hI : I * I = -1 := Complex.I_mul_I
      linear_combination h - hI
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (by linear_combination h1)
  · rintro (rfl | rfl) <;> simp [Complex.I_sq]

/-- **The state at the root the arc misses.**  One branch based at `0` serves every
block, and the tangency set is **empty** — not merely finite: the chord from `-i` turns
at exactly half the tangent's rate, so the difference runs from `π/4` to `3π/4` over the
whole arc and never reaches a multiple of `π`. -/
theorem fav_rootBranchState_neg_I {k : ℕ} (Lb Rb : Fin k → ℝ) :
    RootBranchState (ftPrincipal witTau) favDGamma favD2Gamma (-I) 0 π Lb Rb
      (fun _ => polarAngle (ftPrincipal witTau) favDGamma (-I) 0) := by
  refine Or.inl ⟨∅, fav_roots_meet.2, by simp, ?_, fun _ => rfl⟩
  intro x hx j hcon
  exact (fav_no_tangency_neg_I hx j hcon).elim

/-- **The state at the root the arc meets.**  The collision is at `m = π/2`, both
tangency sets are empty, and the side each block takes is decided by the amplitude:
`W` vanishes exactly at `π/2`, so a block on which `W` does not vanish cannot contain it.

**`hne` is unguarded, and that is exactly what it has to be.**  `RootBranchState`'s side
clause quantifies over every `i` with no `Lb i < Rb i` guard, so a block `[π/2, π/2]` would
have to sit inside `Ico 0 (π/2)` or `Ioc (π/2) π` and sits in neither
(`not_rootBranchState_I_of_degenerate`).  Asking nonvanishing on **closed** blocks,
degenerate ones included, excludes that block by hypothesis rather than by a side
condition — which is `PhaseTangency.sum_eVariationOn_of_curvature`'s `hfree` verbatim, and
the shape the two lemmas therefore share. -/
theorem fav_rootBranchState_I {k : ℕ} {Lb Rb : Fin k → ℝ}
    (hL : ∀ i, Lb i ∈ Icc (0 : ℝ) π) (hR : ∀ i, Rb i ∈ Icc (0 : ℝ) π)
    (hne : ∀ i, ∀ θ ∈ Icc (Lb i) (Rb i),
      ftAmp witQ favB 1 ((witZ θ : ℝ) : ℂ) (ftPrincipal witTau θ) ≠ 0) :
    ∃ ψ : Fin k → ℝ → ℝ,
      RootBranchState (ftPrincipal witTau) favDGamma favD2Gamma I 0 π Lb Rb ψ := by
  classical
  have hpi := Real.pi_pos
  -- no block contains the collision, because the amplitude vanishes there
  have hsplit : ∀ i, Rb i < π / 2 ∨ π / 2 < Lb i := by
    intro i
    by_contra hc
    push Not at hc
    exact hne i (π / 2) ⟨hc.2, hc.1⟩
      ((ftAmp_favB_eq_zero_iff ⟨by positivity, by linarith⟩).2 rfl)
  refine ⟨fun i => if Rb i < π / 2 then polarAngle (ftPrincipal witTau) favDGamma I 0
      else polarAngle (ftPrincipal witTau) favDGamma I π, Or.inr ?_⟩
  refine ⟨π / 2, by positivity, by linarith, ∅, ∅, ftPrincipal_witTau_pi_div_two,
    fun x hx hxm hcon => hxm ((favGamma_eq_I_iff hx).1 hcon),
    fun x hx j hcon => (fav_no_tangency_I_lower hx j hcon).elim,
    fun x hx j hcon => (fav_no_tangency_I_upper hx j hcon).elim, fun i => ?_⟩
  rcases lt_or_ge (Rb i) (π / 2) with h | h
  · refine Or.inl ⟨fun x hx => ⟨le_trans (hL i).1 hx.1, lt_of_le_of_lt hx.2 h⟩, ?_⟩
    simp [h]
  · have hLb : π / 2 < Lb i := (hsplit i).resolve_left (not_lt.2 h)
    refine Or.inr ⟨fun x hx => ⟨lt_of_lt_of_le hLb hx.1, le_trans hx.2 (hR i).2⟩, ?_⟩
    simp [not_lt.2 h]

/-! ### Why the nondegeneracy hypothesis cannot be dropped -/

/-- **`RootBranchState`'s side clause is unsatisfiable at a block that is the collision
point.**  `Icc (π/2) (π/2)` is `{π/2}`, which lies in neither `Ico 0 (π/2)` nor
`Ioc (π/2) π`, and the first disjunct is refused because the arc does meet `i`.  So no
`ψ` exists.

This is not a defect of the pencil: it is the `∀ i` in the side clause carrying no
`Lb i < Rb i` guard, while every hypothesis that would exclude such a block —
`PhaseSupplyProducer`'s nonvanishing clause included — is guarded by exactly that.
A degenerate block is admissible upstream and impossible here. -/
theorem not_rootBranchState_I_of_degenerate (ψ : Fin 1 → ℝ → ℝ) :
    ¬ RootBranchState (ftPrincipal witTau) favDGamma favD2Gamma I 0 π
        (fun _ => π / 2) (fun _ => π / 2) ψ := by
  have hpi := Real.pi_pos
  have hmem : (π / 2) ∈ Icc (0 : ℝ) π := ⟨by positivity, by linarith⟩
  rintro (⟨S, hmiss, -, -, -⟩ | ⟨m, ham, hmb, S₁, S₂, hm, -, -, -, hside⟩)
  · exact hmiss (π / 2) hmem ftPrincipal_witTau_pi_div_two
  · have hmeq : m = π / 2 := (favGamma_eq_I_iff ⟨ham, hmb⟩).1 hm
    rw [hmeq] at hside
    rcases hside 0 with ⟨hsub, -⟩ | ⟨hsub, -⟩
    · exact absurd (hsub ⟨le_rfl, le_rfl⟩).2 (lt_irrefl _)
    · exact absurd (hsub ⟨le_rfl, le_rfl⟩).1 (lt_irrefl _)

/-! ### The group, in the shape the producer consumes -/

/-- **`exists_uniform_ftBranchSupply`'s `hstates` at the Favard witness**, for every
family of nondegenerate blocks — which is every family the rest of the supply has
anything to say about.

`π / (1 : ℕ)` rather than `π` because that is the arc the producer names at `r = 1`.

**What this settles and what it does not.**  It settles that `RootBranchState` is
inhabited: the group had no producer anywhere in the tree, at any pencil, so until now
every result above it rested on a class nobody had shown nonempty.  It does not settle
`hstates` as currently stated, which quantifies over degenerate blocks too and is
**false** there — see `not_rootBranchState_I_of_degenerate`.  Adding `Lb i < Rb i` to
`RootBranchState`'s side clause, where every neighbouring hypothesis already has it,
makes this theorem exactly `hstates`. -/
theorem fav_rootStates {k : ℕ} {Lb Rb : Fin k → ℝ}
    (hL : ∀ i, Lb i ∈ Icc (0 : ℝ) (π / ((1 : ℕ) : ℝ)))
    (hR : ∀ i, Rb i ∈ Icc (0 : ℝ) (π / ((1 : ℕ) : ℝ)))
    (hne : ∀ i, ∀ θ ∈ Icc (Lb i) (Rb i),
      ftAmp witQ favB 1 ((witZ θ : ℝ) : ℂ) (ftPrincipal witTau θ) ≠ 0) :
    ∀ β ∈ favB.roots, ∃ ψ : Fin k → ℝ → ℝ,
      RootBranchState (ftPrincipal witTau) favDGamma favD2Gamma β 0
        (π / ((1 : ℕ) : ℝ)) Lb Rb ψ := by
  have hcast : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  rw [hcast] at hL hR ⊢
  intro β hβ
  rcases mem_favB_roots_iff.1 hβ with rfl | rfl
  · exact fav_rootBranchState_I hL hR hne
  · exact ⟨_, fav_rootBranchState_neg_I Lb Rb⟩

/-! ### The curvature hypothesis, discharged by computation -/

/-- **`PhaseTangency.sum_eVariationOn_of_curvature`'s `hcurv` at the Favard witness.**
`wedge γ'' γ'` *is* the branch's curvature quantity `τ² + 2τ'² - ττ''`, not a proxy for
it: writing `γ = τe^{iθ}` gives `γ' = (τ' + iτ)e^{iθ}` and
`γ'' = (τ'' + 2iτ' - τ)e^{iθ}`, and the wedge of those two is exactly that expression.
At `τ ≡ 1` it is `1`, so the hypothesis that is hard in general — `PhaseTangency` reduces
it to an inequality on the angle sums — is discharged here by arithmetic.

Nothing in this module consumes it: the tangency sets are exhibited as `∅` outright, which
is stronger than the finiteness `hcurv` buys.  It is stated because it is the one
hypothesis of the general route that this pencil makes free, and because a reader
comparing the two routes will want to know that. -/
theorem fav_curvature (s : ℝ) : wedge (favD2Gamma s) (favDGamma s) = 1 := by
  simp only [wedge, favDGamma, favD2Gamma, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq s]

end ForgacsTran
