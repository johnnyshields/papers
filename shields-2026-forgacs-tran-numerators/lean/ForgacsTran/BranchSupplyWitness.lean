/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.SimpleWitness
import ForgacsTran.BranchSupply

/-!
# How far `hbranch` gets at a concrete pencil

`PhaseSupplyProducer.exists_ftPhaseSupply_of_dominance` leaves `hdom` and
`hbranch`; `hdom` is discharged, and `hbranch` is stated but never yet exhibited,
so every result above it asserts a hypothesis class nobody has shown inhabited.

This module takes `BranchSupply.exists_uniform_ftBranchSupply` — the producer —
to the most favourable pencil in the tree and reports exactly where it stops.
The pencil is `SimpleWitness`'s: `Q = 1 - 4t + t^2`, `r = 1`, `B = t^2 + 1`, where
`τ ≡ 1` so the branch is the unit semicircle `γ(θ) = e^{iθ}` and `B` vanishes
**on** the arc at `θ = π/2`.  Nothing in the tree is better conditioned for this.

## What clears

The branch-geometry group is free here and is proved below: `γ` is `e^{iθ}`, so
it is smooth in the real parameter with `γ' = ie^{iθ}` never zero — `hγd`, `hd2`,
`hc2` and `hreg` hold on **all of `ℝ`**, not merely on a neighbourhood of the
closed arc, which is what the producer asks for and what the general branch does
not supply (`FTGeometryAssembly.hasDerivAt_ftPrincipal_ftTau` is first order and
on the *open* arc only).

## What does not, and it is one group

`hstates` — the `RootBranchState` group — has **no producer anywhere in the
tree**: outside `BranchSupply` the name does not occur.  It is not a question of
this pencil being awkward; nothing constructs one at any pencil.  At this pencil
its two disjuncts are exactly the two cases one wants (`γ` misses `-i` and meets
`i` once, at `π/2`), and both still require the tangency set
`{x : polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = jπ}` to be exhibited as a
`Finset` — the finiteness that `PhaseTangency` is about.

## What this pencil clears DEGENERATELY, which is not coverage

A witness shows a hypothesis class is inhabited.  It does not show the class is
exercised, and this pencil is special in three separate ways.  Each clears a
different hypothesis for free, so a consumer reading the instantiation as broad
coverage would be reading it wrong.

* **`ν = 1` at both ends.**  `E = (X-1)(X+1)`, so the collisions at `γ(0) = 1` and
  `γ(π) = -1` are **simple** — `ftCollisionOrder_witQ_zero` and `..._pi` compute
  both to `1`.  `BranchSupply`'s collar is deliberately proved at *arbitrary*
  multiplicity; this witness exercises only `ν = 1`, the easy case.
* **`τ ≡ 1`.**  Hence `τ' = τ'' = 0` and the curvature quantity
  `K = τ² + 2τ'² - ττ''` is the constant `1` — not merely bounded.  Anything that
  clears here because a derivative of `τ` vanishes says nothing about a pencil
  whose branch radius actually moves.
* **The collar bound is met by a constant.**  `ftCriticalAlong_witQ_factor` splits
  `E∘γ` into a nonvanishing factor and a **real** one, so `Im(logDeriv (E∘γ)) = 1`
  identically and the singular `cot θ` sits entirely in the real part.  This one
  is *not* a speciality of the pencil — it is `lem:amplitude-divisor`'s own
  mechanism, and `im_logDeriv_ofRealSub_zpow` is its general form — but it does
  mean none of the collar's blow-up handling is under test here.

What the pencil *does* exercise nontrivially: a genuine collision at each end
rather than a degenerate arc, `E` nonvanishing on the open arc, a numerator whose
zero lies **on** the arc, and the branch-geometry group above.

## A hypothesis that holds for the wrong reason

`hW0` and `hWL` say the amplitude vanishes at the two endpoints.  At this pencil
they are **true**, and `fav_hW0` proves it — but through `x/0 = 0`, not through
any mathematics: at both endpoints the principal pair collides, so the cofactor
vanishes there and `ftAmp = -(B/0) = 0`, while the amplitude
`W(θ) = i cot(θ)e^{iθ}` in fact blows up.  Since every admissible pencil has the
pair colliding at its endpoints, these two hypotheses are satisfied everywhere
and constrain nothing.  Recorded because a hypothesis that cannot fail is not a
hypothesis, and because the next reader will otherwise take `hW0` for a real
condition on `B`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `cor:linear-phase-variation`,
  `eq:linear-phase-variation`.

## Tags

branch supply, non-vacuity, phase variation, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Complex

/-- **The branch-geometry group of `exists_uniform_ftBranchSupply`, at the Favard
witness, on all of `ℝ`.**  `hγd`, `hd2`, `hc2` and `hreg` in one statement.  The
producer needs them on an open set containing the *closed* arc; here they hold
everywhere, so the endpoint regularity that the general branch lacks is not what
blocks a witness at this pencil. -/
theorem fav_branch_C2 :
    (∀ s : ℝ, HasDerivAt (ftPrincipal witTau) (Complex.exp ((s : ℂ) * I) * I) s)
      ∧ (∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * I) * I)
          (Complex.exp ((s : ℂ) * I) * I * I) s)
      ∧ Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * I) * I * I)
      ∧ (∀ s : ℝ, Complex.exp ((s : ℂ) * I) * I ≠ 0) := by
  have hE : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (((t : ℝ) : ℂ) * I))
      (Complex.exp (((s : ℝ) : ℂ) * I) * I) s := by
    intro s
    have : HasDerivAt (fun w : ℂ => Complex.exp (w * I))
        (Complex.exp (((s : ℝ) : ℂ) * I) * I) (((s : ℝ) : ℂ)) := by
      simpa using ((hasDerivAt_id (((s : ℝ) : ℂ))).mul_const I).cexp
    exact this.comp_ofReal
  have hcont : Continuous (fun t : ℝ => Complex.exp (((t : ℝ) : ℂ) * I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  refine ⟨hasDerivAt_ftPrincipal_witTau, fun s => (hE s).mul_const I,
    (hcont.mul continuous_const).mul continuous_const, fun s => ?_⟩
  exact mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero

/-- **`hW0` at the Favard witness, and it holds by the division convention.**
`D(·, z(0)) = (t-1)^2` and the principal point is `1`, so the cofactor vanishes
there and `ftAmp` is `-(B(1)/0) = 0`.  The amplitude does not vanish at `0` in the
mathematics — `|W| = |cot θ| → ∞` — so this hypothesis is discharged by
`x/0 = 0` and by nothing else. -/
theorem fav_hW0 :
    ftAmp witQ favB 1 ((witZ 0 : ℝ) : ℂ) (ftPrincipal witTau 0) = 0 := by
  have hprin : ftPrincipal witTau 0 = 1 := by
    rw [ftPrincipal_witTau]; simp
  have hroot : (ftDen witQ 1 ((witZ 0 : ℝ) : ℂ)).eval (ftPrincipal witTau 0) = 0 := by
    rw [hprin, ftDen_witQ_lower_sq]; simp
  have hcof : (ftCofactor witQ 1 ((witZ 0 : ℝ) : ℂ) (ftPrincipal witTau 0)).eval
      (ftPrincipal witTau 0) = 0 := by
    rw [← eval_derivative_ftDen hroot, hprin, ftDen_witQ_lower_sq]
    simp [derivative_pow]
  rw [ftAmp, hcof, div_zero, neg_zero]

/-- The same at the upper endpoint, by the same mechanism: `D(·, z(π)) = (t+1)^2`
and the principal point is `-1`. -/
theorem fav_hWL :
    ftAmp witQ favB 1 ((witZ Real.pi : ℝ) : ℂ) (ftPrincipal witTau Real.pi) = 0 := by
  have hprin : ftPrincipal witTau Real.pi = -1 := by
    rw [ftPrincipal_witTau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi, Real.sin_pi]
    simp
  have hroot : (ftDen witQ 1 ((witZ Real.pi : ℝ) : ℂ)).eval
      (ftPrincipal witTau Real.pi) = 0 := by
    rw [hprin, ftDen_witQ_upper_sq]; simp
  have hcof : (ftCofactor witQ 1 ((witZ Real.pi : ℝ) : ℂ)
      (ftPrincipal witTau Real.pi)).eval (ftPrincipal witTau Real.pi) = 0 := by
    rw [← eval_derivative_ftDen hroot, hprin, ftDen_witQ_upper_sq]
    simp [derivative_pow]
  rw [ftAmp, hcof, div_zero, neg_zero]

/-- **The arc meets one root of `B` and misses the other**, which is exactly the
two-disjunct split `RootBranchState` is written around.  Supplied so that a later
producer has the case analysis already settled at this pencil. -/
theorem fav_roots_meet :
    ftPrincipal witTau (π / 2) = I ∧ (∀ θ ∈ Icc (0 : ℝ) π, ftPrincipal witTau θ ≠ -I) := by
  refine ⟨ftPrincipal_witTau_pi_div_two, fun θ hθ hcon => ?_⟩
  have him : (ftPrincipal witTau θ).im = Real.sin θ := by
    rw [ftPrincipal_witTau]
    exact Complex.exp_ofReal_mul_I_im θ
  rw [hcon] at him
  simp only [Complex.neg_im, Complex.I_im] at him
  have : Real.sin θ = -1 := him.symm
  have hnn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, hθ.2⟩
  linarith

/-! ### The critical polynomial along the arc, exposed

`BranchSupply`'s collar hypotheses are stated through `ftCriticalAlong` and
`ftCollisionOrder`, and its own `kappaZero_bundle_witness` runs at `Q = X`,
`z = 0`, `τ = 0`, where the cofactor is the constant `1` — a degenerate arc with
no collision at all.  This pencil has a genuine collision at **each** end, so the
objects are exposed here rather than left inlined. -/

/-- `E = XQ' - rQ` at the Favard witness is `t^2 - 1`: the two collisions are at
`±1`, and nothing else. -/
theorem ftCritical_witQ : ftCritical witQ 1 = X ^ 2 - 1 := by
  refine Polynomial.funext fun t => ?_
  have hd : (derivative witQ).eval t = -4 + 2 * t := by
    have h := derivative_ftDen_witQ_eval 0 t
    rw [ftDen] at h
    simpa using h
  rw [eval_ftCritical, hd, witQ_eval]
  simp
  ring

/-- **`E` along the arc.**  `γ(θ) = e^{iθ}`, so `E(γ(θ)) = e^{2iθ} - 1`. -/
theorem ftCriticalAlong_witQ (θ : ℝ) :
    ftCriticalAlong witQ 1 witTau θ = Complex.exp ((θ : ℂ) * I) ^ 2 - 1 := by
  rw [ftCriticalAlong, ftPrincipal_witTau, ftCritical_witQ]
  simp

/-- **The collision is split off exactly**, into a nonvanishing factor and a
**real** one: `E(γ(θ)) = e^{iθ}·(2i sin θ)`.  This is the shape the collar bound
consumes — `im_logDeriv` of the real factor is `0`, so the blow-up at each end
sits entirely in the real part and drops out. -/
theorem ftCriticalAlong_witQ_factor (θ : ℝ) :
    ftCriticalAlong witQ 1 witTau θ
      = Complex.exp ((θ : ℂ) * I) * (2 * I * (Real.sin θ : ℂ)) := by
  rw [ftCriticalAlong_witQ, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  have hpy : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq]
    norm_num
  linear_combination hpy - ((Real.sin θ : ℂ)) ^ 2 * Complex.I_sq

/-- **`E` does not vanish on the open arc**, so the interior state of the collar
group holds and the two collisions are exactly the endpoints. -/
theorem ftCriticalAlong_witQ_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) :
    ftCriticalAlong witQ 1 witTau θ ≠ 0 := by
  rw [ftCriticalAlong_witQ_factor]
  refine mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (by norm_num) ?_)
  exact Complex.ofReal_ne_zero.2 (Real.sin_pos_of_mem_Ioo hθ).ne'

/-- **The branch never reaches the origin**, the other clause of the arc state. -/
theorem ftPrincipal_witTau_ne_zero (θ : ℝ) : ftPrincipal witTau θ ≠ 0 := by
  rw [ftPrincipal_witTau]; exact Complex.exp_ne_zero _

/-- **The collision order is exactly `1` at each end.**  `E = (t-1)(t+1)` and the
branch reaches `1` at `θ = 0` and `-1` at `θ = π`, each a simple zero — so both
collars are instantiated at a real collision, not at a vacuous one. -/
theorem ftCollisionOrder_witQ_zero : ftCollisionOrder witQ 1 witTau 0 = 1 := by
  have hprin : ftPrincipal witTau 0 = 1 := by rw [ftPrincipal_witTau]; simp
  have hE : ftCritical witQ 1 ≠ 0 := by
    rw [ftCritical_witQ]
    intro h
    have := congrArg (fun p => Polynomial.coeff p 2) h
    simp [coeff_sub, coeff_X_pow, coeff_one] at this
  rw [ftCollisionOrder, hprin, ftCritical_witQ]
  have hfac : (X ^ 2 - 1 : Polynomial ℂ) = (X - C 1) * (X - C (-1)) := by
    simp [map_one, map_neg]; ring
  rw [hfac, Polynomial.rootMultiplicity_mul (by rw [← hfac]; rwa [ftCritical_witQ] at hE),
    Polynomial.rootMultiplicity_X_sub_C_self,
    Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])]

/-- The same at the upper end: the branch reaches `-1` at `θ = π`, also a simple
zero of `E`.  So both of `BranchSupply`'s collars are instantiated at a real
collision of order exactly one. -/
theorem ftCollisionOrder_witQ_pi : ftCollisionOrder witQ 1 witTau π = 1 := by
  have hprin : ftPrincipal witTau π = -1 := by
    rw [ftPrincipal_witTau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi, Real.sin_pi]
    simp
  have hE : (X ^ 2 - 1 : Polynomial ℂ) ≠ 0 := by
    intro h
    have := congrArg (fun p => Polynomial.coeff p 2) h
    simp [coeff_sub, coeff_X_pow, coeff_one] at this
  rw [ftCollisionOrder, hprin, ftCritical_witQ]
  have hfac : (X ^ 2 - 1 : Polynomial ℂ) = (X - C (-1)) * (X - C 1) := by
    simp [map_one, map_neg]; ring
  rw [hfac, Polynomial.rootMultiplicity_mul (by rw [← hfac]; exact hE),
    Polynomial.rootMultiplicity_X_sub_C_self,
    Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot]; norm_num)]

end ForgacsTran
