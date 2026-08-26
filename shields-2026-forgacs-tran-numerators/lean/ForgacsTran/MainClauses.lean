/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.PhaseCount
import ForgacsTran.ZeroCount
import ForgacsTran.AngularBookkeeping
import ForgacsTran.DominanceFT

/-!
# `thm:main` over the dominance supply

`Main.interior_distinct_count` states clause 2(iii) against a bundle that already *contains*
the interior zero set, so the `Finset` it returns is the one it was handed and the theorem
derives nothing.  Here the zero set is a **conclusion**: it is built by the intermediate-value
count of `PhaseCount.exists_interiorZeros_of_dominance` out of `eq:principal-decomposition`
and `eq:dominance-bound`, and `AngularBookkeeping.image_Ioo_eq_Ioo` is what puts it inside
`I_{Q,r}` rather than merely inside some set carried along for the purpose.

All three conclusions then run on **one** supply, rather than on `FTInputs` fields of
differing strength:

## Main statements

* `exists_interiorZeros_ftInterval` — the zero set, produced, inside `ftInterval`.
* `interior_distinct_count_of_dominance` — clause 2(iii): at least `deg P_m - C` distinct
  zeros in `I_{Q,r}`.
* `main_bound_interval_of_dominance` — clause 2(ii): at most `C` zeros outside `I_{Q,r}`.
* `main_bound_of_dominance` — clause 1: at most `C` zeros outside `(0, ∞)`.
* `main_clauses_of_dominance` — the three together, off one hypothesis.
* `chebWitness`, `dominanceSupply_cheb`, `exists_interiorZeros_cheb` — the supply is
  inhabited, and with a nontrivial count: on `[0, π]` the arc `z(θ) = -cos θ` with phase
  `Φ(θ) = kθ` and `P = 2 T_k(-x)` reproduces `2 cos(kθ)` exactly, so `R_M = 0`, and the
  produced set carries at least `k - 2` genuine zeros of a degree-`k` polynomial.

## Implementation notes

`DominanceSupply` is the hypothesis list of `thm:weighted-dominance` written out as a
conjunction: the principal decomposition, `|R_M| ≤ |W|/2`, the strictly increasing phase of
`eq:Phi-def` (which `AngularBookkeeping.strictMonoOn_phase_congr` discharges), and the
strictly increasing reparametrization of `thm:FT-geometry`.  **No zero set appears in it** —
that is the whole difference from a bundle.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair dominance and the
fixed-numerator theorem» (`subsec:proof`, `thm:main` clauses 1 and 2).

## Tags

main theorem, dominance supply, exceptional zero
-/

namespace ForgacsTran

open Set

/-- Paper `thm:weighted-dominance` on one retained subarc, spelled out rather than bundled:
every conjunct is a hypothesis about the objects the manuscript names, and none of them is a
zero set.

**Differs from the paper's route.**  `subsec:proof` obtains the interior zero set inside the
count of `prop:angular-discrepancy` and reads `thm:main`'s clauses off that one narrative;
here the supply of `thm:weighted-dominance` is isolated as a hypothesis and all three clauses
are derived from it.  Factoring it out is what lets clause 2(iii) return a set the count
builds rather than one carried in. -/
def DominanceSupply (P : Polynomial ℝ) (Φ φ ψ z τ Rm : ℝ → ℝ) (W : ℝ → ℂ)
    (a b L aI bI : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn Φ (Icc a b) ∧ StrictMonoOn Φ (Icc a b) ∧
    Real.pi ≤ L ∧ L ≤ Φ b - Φ a ∧
    (∀ θ ∈ Icc a b, Φ θ = φ θ - ψ θ) ∧
    StrictMonoOn z (Icc a b) ∧
    (∀ θ ∈ Icc a b, z θ ∈ Ioo aI bI) ∧
    (∀ θ ∈ Icc a b, 0 < τ θ) ∧
    (∀ θ ∈ Icc a b, W θ ≠ 0) ∧
    (∀ θ ∈ Icc a b, W θ = (‖W θ‖ : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I)) ∧
    (∀ θ ∈ Icc a b, τ θ * P.eval (z θ)
      = 2 * (W θ * Complex.exp (-(φ θ : ℂ) * Complex.I)).re + Rm θ) ∧
    (∀ θ ∈ Icc a b, |Rm θ| ≤ ‖W θ‖ / 2)

/-- **The zero set, produced.**  The intermediate-value count of `prop:angular-discrepancy`
turns the dominance supply into a `Finset` of distinct zeros of `P` lying in `I_{Q,r}`; it is
built here, not handed in. -/
theorem exists_interiorZeros_ftInterval {P : Polynomial ℝ} {Φ φ ψ z τ Rm : ℝ → ℝ}
    {W : ℝ → ℂ} {a b L aI bI : ℝ}
    (hsup : DominanceSupply P Φ φ ψ z τ Rm W a b L aI bI) :
    ∃ Z : Finset ℂ, L / Real.pi - 2 ≤ (Z.card : ℝ) ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ ftInterval aI bI) := by
  obtain ⟨hab, hcont, hmono, hL, hΦ, hΦdef, hzmono, hzS, hτ, hWne, hpolar, hdec, hdom⟩ := hsup
  obtain ⟨n, Z, hn, hnZ, hZr, hZm⟩ :=
    exists_interiorZeros_of_dominance hab hcont hmono hL hΦ hΦdef hzmono
      ordConnected_Ioo hzS hτ hWne hpolar hdec hdom
  refine ⟨Z, le_trans hn ?_, hZr, hZm⟩
  exact_mod_cast hnZ

/-- **Paper `thm:main` clause 2(iii).**  At least `deg P_m - C` **distinct** zeros inside
`I_{Q,r}`.  Unlike `Main.interior_distinct_count`, the zero set is a conclusion: the only
numeric input is that the degree sits below the phase count plus the defect, which is what
`lem:eventual-degree` and `prop:angular-discrepancy` supply. -/
theorem interior_distinct_count_of_dominance {P : Polynomial ℝ} {Φ φ ψ z τ Rm : ℝ → ℝ}
    {W : ℝ → ℂ} {a b L aI bI : ℝ} {C : ℕ}
    (hsup : DominanceSupply P Φ φ ψ z τ Rm W a b L aI bI)
    (hdeg : (((P.map (algebraMap ℝ ℂ)).natDegree : ℕ) : ℝ) ≤ L / Real.pi - 2 + C) :
    ∃ Z : Finset ℂ, (P.map (algebraMap ℝ ℂ)).natDegree - C ≤ Z.card ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ ftInterval aI bI) := by
  obtain ⟨Z, hZc, hZr, hZm⟩ := exists_interiorZeros_ftInterval hsup
  refine ⟨Z, ?_, hZr, hZm⟩
  have hreal : (((P.map (algebraMap ℝ ℂ)).natDegree : ℕ) : ℝ) ≤ (Z.card : ℝ) + (C : ℝ) := by
    linarith
  have : (P.map (algebraMap ℝ ℂ)).natDegree ≤ Z.card + C := by exact_mod_cast hreal
  omega

/-- **Paper `thm:main` clause 2(ii).**  At most `C` zeros outside `I_{Q,r}`, counted with
multiplicity — the counting engine run on the produced zero set. -/
theorem main_bound_interval_of_dominance {P : Polynomial ℝ} {Φ φ ψ z τ Rm : ℝ → ℝ}
    {W : ℝ → ℂ} {a b L aI bI : ℝ} {C : ℕ}
    (hsup : DominanceSupply P Φ φ ψ z τ Rm W a b L aI bI)
    (hdeg : (((P.map (algebraMap ℝ ℂ)).natDegree : ℕ) : ℝ) ≤ L / Real.pi - 2 + C)
    (hPne : P.map (algebraMap ℝ ℂ) ≠ 0) :
    (exceptionalRoots (P.map (algebraMap ℝ ℂ)) (ftInterval aI bI)).card ≤ C := by
  obtain ⟨Z, hZc, hZr, hZm⟩ := interior_distinct_count_of_dominance hsup hdeg
  exact exceptionalRoots_card_le hPne hZr hZm hZc

/-- **Paper `thm:main` clause 1.**  At most `C` zeros outside `(0, ∞)`, over the same supply:
`I_{Q,r} ⊆ (0, ∞)` once its lower endpoint is nonnegative. -/
theorem main_bound_of_dominance {P : Polynomial ℝ} {Φ φ ψ z τ Rm : ℝ → ℝ}
    {W : ℝ → ℂ} {a b L aI bI : ℝ} {C : ℕ}
    (hsup : DominanceSupply P Φ φ ψ z τ Rm W a b L aI bI)
    (hdeg : (((P.map (algebraMap ℝ ℂ)).natDegree : ℕ) : ℝ) ≤ L / Real.pi - 2 + C)
    (hPne : P.map (algebraMap ℝ ℂ) ≠ 0) (haI : 0 ≤ aI) :
    (exceptionalRoots (P.map (algebraMap ℝ ℂ)) posRay).card ≤ C := by
  obtain ⟨Z, hZc, hZr, hZm⟩ := interior_distinct_count_of_dominance hsup hdeg
  exact exceptionalRoots_card_le hPne hZr
    (fun w hw => ftInterval_subset_posRay haI (hZm w hw)) hZc

/-- **Paper `thm:main`, clauses 1 and 2 together, off one supply.**  The interior zero set is
produced once and all three conclusions are read off it. -/
theorem main_clauses_of_dominance {P : Polynomial ℝ} {Φ φ ψ z τ Rm : ℝ → ℝ}
    {W : ℝ → ℂ} {a b L aI bI : ℝ} {C : ℕ}
    (hsup : DominanceSupply P Φ φ ψ z τ Rm W a b L aI bI)
    (hdeg : (((P.map (algebraMap ℝ ℂ)).natDegree : ℕ) : ℝ) ≤ L / Real.pi - 2 + C)
    (hPne : P.map (algebraMap ℝ ℂ) ≠ 0) (haI : 0 ≤ aI) :
    (∃ Z : Finset ℂ, (P.map (algebraMap ℝ ℂ)).natDegree - C ≤ Z.card ∧
        (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
        (∀ w ∈ Z, w ∈ ftInterval aI bI))
      ∧ (exceptionalRoots (P.map (algebraMap ℝ ℂ)) (ftInterval aI bI)).card ≤ C
      ∧ (exceptionalRoots (P.map (algebraMap ℝ ℂ)) posRay).card ≤ C :=
  ⟨interior_distinct_count_of_dominance hsup hdeg,
    main_bound_interval_of_dominance hsup hdeg hPne,
    main_bound_of_dominance hsup hdeg hPne haI⟩

/-! ### The supply is inhabited

`DominanceSupply` is a thirteen-fold conjunction, so a theorem stated against it would be
vacuous if nothing satisfied it.  A Chebyshev arc satisfies it exactly, with no remainder at
all: `z(θ) = -cos θ` is strictly increasing on `[0, π]`, `Φ(θ) = kθ` turns `k` times, and
`P = 2 T_k(-x)` reproduces `2 cos(kθ)` on the nose, so `R_M = 0`.  The count it returns is
`k - 2` genuine zeros of a degree-`k` polynomial, which is not vacuous either. -/

/-- The witness polynomial: `2 T_k(-x)`, which satisfies `P(-cos θ) = 2 cos(kθ)`. -/
noncomputable def chebWitness (k : ℕ) : Polynomial ℝ :=
  2 * (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp (-Polynomial.X)

theorem eval_chebWitness (k : ℕ) (θ : ℝ) :
    (chebWitness k).eval (-Real.cos θ) = 2 * Real.cos ((k : ℝ) * θ) := by
  rw [chebWitness, Polynomial.eval_mul, Polynomial.eval_comp]
  simp only [Polynomial.eval_neg, Polynomial.eval_X, neg_neg, Polynomial.eval_ofNat]
  rw [Polynomial.Chebyshev.T_real_cos]
  push_cast
  ring

/-- `DominanceSupply` is satisfiable, with a nontrivial count: `L / π - 2 = k - 2`. -/
theorem dominanceSupply_cheb {k : ℕ} (hk : 1 ≤ k) :
    DominanceSupply (chebWitness k)
      (fun θ => (k : ℝ) * θ) (fun θ => (k : ℝ) * θ) (fun _ => 0)
      (fun θ => -Real.cos θ) (fun _ => 1) (fun _ => 0) (fun _ => 1)
      0 Real.pi ((k : ℝ) * Real.pi) (-2) 2 := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hπ := Real.pi_pos
  refine ⟨hπ.le, (continuous_const.mul continuous_id).continuousOn, ?_, ?_, ?_,
    fun θ _ => by ring, ?_, ?_, fun _ _ => one_pos, fun _ _ => one_ne_zero, ?_, ?_,
    fun _ _ => by norm_num⟩
  · exact fun x _ y _ hxy => by nlinarith
  · nlinarith
  · simp
  · exact fun x hx y hy hxy => neg_lt_neg (Real.strictAntiOn_cos hx hy hxy)
  · intro θ _
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    exact ⟨by simp; linarith, by simp; linarith⟩
  · intro θ _
    simp
  · intro θ _
    have hre : (Complex.exp (-((((k : ℝ) * θ : ℝ)) : ℂ) * Complex.I)).re
        = Real.cos ((k : ℝ) * θ) := by
      rw [show (-((((k : ℝ) * θ : ℝ)) : ℂ) * Complex.I)
          = (((-((k : ℝ) * θ) : ℝ)) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    rw [eval_chebWitness]
    simp only [one_mul, add_zero]
    rw [hre]

/-- The witness in action.  At the Chebyshev supply the produced set has at least `k - 2`
members, every one a genuine zero of `chebWitness k` inside `I_{-2,2}` — so neither the
hypothesis of `exists_interiorZeros_ftInterval` nor its conclusion is vacuous. -/
theorem exists_interiorZeros_cheb {k : ℕ} (hk : 1 ≤ k) :
    ∃ Z : Finset ℂ, (k : ℝ) - 2 ≤ (Z.card : ℝ) ∧
      (∀ w ∈ Z, ((chebWitness k).map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ ftInterval (-2) 2) := by
  obtain ⟨Z, hZc, hZr, hZm⟩ := exists_interiorZeros_ftInterval (dominanceSupply_cheb hk)
  refine ⟨Z, ?_, hZr, hZm⟩
  have hπ := Real.pi_pos
  have hdiv : (k : ℝ) * Real.pi / Real.pi = (k : ℝ) := by
    field_simp
  rwa [hdiv] at hZc

/-! ### Meeting the dominance instantiation

`DominanceFT.weighted_dominance_ftCoeffPoly` concludes `ftRemainder ≤ ftPrincipalAmp / 2` on
the retained range of `eq:retained-range` off the amplitude windows `Θ M`.  `DominanceSupply`
asks for the same content in the shape the phase count consumes.  The translation moves no
fact: the decomposition is `eq:principal-decomposition` with `t_+^{M+1} = τ^{M+1}e^{i(M+1)θ}`
divided out, and the bound is that conclusion verbatim. -/

/-- Dividing `t_+^{M+1}` out of the principal term leaves `e^{-i(M+1)θ}`, which is why the
phase of `eq:Phi-def` is `(M+1)θ - arg W`. -/
theorem ftPrincipal_pow_ratio {τ : ℝ → ℝ} {θ : ℝ} (hτ : 0 < τ θ) (M : ℕ) :
    ((τ θ : ℝ) : ℂ) ^ (M + 1) / (ftPrincipal τ θ) ^ (M + 1)
      = Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I) := by
  have hne : ((τ θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  rw [ftPrincipal, mul_pow, ← Complex.exp_nat_mul, div_mul_eq_div_div,
    div_self (pow_ne_zero _ hne), one_div, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- **The two halves meet.**  `DominanceSupply` assembled from the conclusion of
`weighted_dominance_ftCoeffPoly` together with the branch data.

What is supplied here beyond that conclusion is exactly the data the phase count needs and
the dominance theorem does not produce: a continuous argument branch `ψ` of the amplitude
(`ViewingAngle.polarAngle` builds one), the strict monotonicity of `Φ_M`
(`AngularBookkeeping.strictMonoOn_phase_congr` discharges it), the strict monotonicity of the
reparametrization `z` (`thm:FT-geometry`), and the turning `L ≤ Φ b - Φ a` on the component. -/
theorem dominanceSupply_of_ftDominance
    {Q B : Polynomial ℂ} {r M : ℕ} {z τ ψ Φ : ℝ → ℝ} {P : Polynomial ℝ}
    {a b aI bI L : ℝ}
    (hP : P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    (hab : a ≤ b)
    (hτ : ∀ θ ∈ Icc a b, 0 < τ θ)
    (hzmono : StrictMonoOn z (Icc a b))
    (hzS : ∀ θ ∈ Icc a b, z θ ∈ Ioo aI bI)
    (hWne : ∀ θ ∈ Icc a b, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0)
    (hpolar : ∀ θ ∈ Icc a b, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I))
    (hΦdef : ∀ θ ∈ Icc a b, Φ θ = ((M : ℝ) + 1) * θ - ψ θ)
    (hΦcont : ContinuousOn Φ (Icc a b)) (hΦmono : StrictMonoOn Φ (Icc a b))
    (hL : Real.pi ≤ L) (hLΦ : L ≤ Φ b - Φ a)
    (hdom : ∀ θ ∈ Icc a b,
      ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2) :
    DominanceSupply P Φ (fun θ => ((M : ℝ) + 1) * θ) ψ z
      (fun θ => (τ θ) ^ (M + 1))
      (fun θ => (τ θ) ^ (M + 1) * P.eval (z θ)
        - 2 * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
            * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I)).re)
      (fun θ => ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ))
      a b L aI bI := by
  -- the remainder of `eq:principal-decomposition` is a real number, and `ftRemainder` is
  -- its absolute value
  have hRm : ∀ θ ∈ Icc a b,
      ftRemainder Q B r z τ M θ
        = |(τ θ) ^ (M + 1) * P.eval (z θ)
            - 2 * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
                * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I)).re| := by
    intro θ hθ
    have hτθ := hτ θ hθ
    have heval : (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)
        = ((P.eval (z θ) : ℝ) : ℂ) := by
      rw [← hP, Polynomial.eval_map,
        show (((z θ : ℝ) : ℂ)) = (algebraMap ℝ ℂ) (z θ) from rfl,
        Polynomial.eval₂_at_apply]
      rfl
    have hratio : ((τ θ : ℝ) : ℂ) ^ (M + 1)
        * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) / (ftPrincipal τ θ) ^ (M + 1))
        = ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
          * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I) := by
      rw [show ((τ θ : ℝ) : ℂ) ^ (M + 1)
          * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) / (ftPrincipal τ θ) ^ (M + 1))
          = (((τ θ : ℝ) : ℂ) ^ (M + 1) / (ftPrincipal τ θ) ^ (M + 1))
            * ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) by ring,
        ftPrincipal_pow_ratio hτθ M]
      ring
    rw [ftRemainder, heval, hratio]
    rw [show (((τ θ : ℝ) : ℂ)) ^ (M + 1) * ((P.eval (z θ) : ℝ) : ℂ)
        = (((τ θ) ^ (M + 1) * P.eval (z θ) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨hab, hΦcont, hΦmono, hL, hLΦ, hΦdef, hzmono, hzS,
    fun θ hθ => pow_pos (hτ θ hθ) _, hWne, hpolar, fun θ _ => by ring, fun θ hθ => ?_⟩
  have h := hdom θ hθ
  rw [hRm θ hθ] at h
  exact h

/-! ### The capstone

`thm:main`, all three clauses, over the Forgács--Tran branch and nothing else.  The analytic
inputs are named and separate: the branch of `thm:FT-geometry` (the reparametrization `z`, the
modulus `τ`, and an argument branch `ψ` of the amplitude) and `thm:weighted-dominance` in the
form `DominanceFT.weighted_dominance_ftCoeffPoly` concludes it.  The phase count, the interior
zero set and both `exceptionalRoots` bounds are derived. -/

/-- The branch data on one retained component of `eq:Omega-M`, at one index: what
`thm:FT-geometry` supplies, together with `eq:dominance-bound` on that component and the
degree--count comparison of `prop:angular-discrepancy`.  No zero set appears in it.

The continuity and strict monotonicity of `Φ_M` are **not** fields: they follow from
`eq:phase-derivative-bound` — a bound `|ψ'| ≤ κ` on the component together with
`κ < M + 1` — through `AngularBookkeeping.continuousOn_phase_congr` and
`strictMonoOn_phase_congr`.  Carrying the derivative bound instead puts the threshold in `M`
where it belongs, in the statement: `κ` is `κ_{Q,r,B}` and may see the numerator, while the
discrepancy constants of `prop:angular-discrepancy` may not.
`Amplitude.exists_phase_derivative_bound`
supplies the `κ`, and `Amplitude.im_logDeriv_eq_phase_deriv` identifies its bound with `|ψ'|`. -/
def FTBranchData (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (P : Polynomial ℝ) (M : ℕ)
    (aI bI : ℝ) (C : ℕ) : Prop :=
  ∃ (a b L : ℝ) (ψ Φ : ℝ → ℝ),
    a ≤ b ∧
    (∀ θ ∈ Icc a b, 0 < τ θ) ∧
    StrictMonoOn z (Icc a b) ∧
    (∀ θ ∈ Icc a b, z θ ∈ Ioo aI bI) ∧
    (∀ θ ∈ Icc a b, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) ∧
    (∀ θ ∈ Icc a b, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I)) ∧
    (∀ θ ∈ Icc a b, Φ θ = ((M : ℝ) + 1) * θ - ψ θ) ∧
    (∃ dψ : ℝ → ℝ, ∃ κ : ℝ, (∀ θ ∈ Icc a b, HasDerivAt ψ (dψ θ) θ) ∧
      (∀ θ ∈ Icc a b, |dψ θ| ≤ κ) ∧ κ < (M : ℝ) + 1) ∧
    Real.pi ≤ L ∧ L ≤ Φ b - Φ a ∧
    (∀ θ ∈ Icc a b, ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2) ∧
    ((P.map (algebraMap ℝ ℂ)).natDegree : ℝ) ≤ L / Real.pi - 2 + C

/-- **Paper `thm:main`, clauses 1 and 2, over the Forgács--Tran branch.**  For every
sufficiently large index: at least `deg P_m - C` distinct zeros inside `I_{Q,r}`, at most `C`
outside it, and at most `C` outside `(0, ∞)` — with the interior zero set built rather than
assumed.

`FTBranchData` is what `thm:FT-geometry` and `thm:weighted-dominance` supply; when the lane
composing `DominanceFT`'s discharging lemmas lands, its conclusion feeds
`dominanceSupply_of_ftDominance` and this closes without a further hypothesis. -/
theorem main_of_ftBranch
    {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {P : ℕ → Polynomial ℝ}
    {aI bI : ℝ} {C m0 : ℕ}
    (hP : ∀ M, (P M).map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    (hne : ∀ M, m0 ≤ M → (P M).map (algebraMap ℝ ℂ) ≠ 0)
    (haI : 0 ≤ aI)
    (hbranch : ∀ M, m0 ≤ M → FTBranchData Q B r z τ (P M) M aI bI C) :
    ∀ M, m0 ≤ M →
      (∃ Z : Finset ℂ, ((P M).map (algebraMap ℝ ℂ)).natDegree - C ≤ Z.card ∧
          (∀ w ∈ Z, ((P M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftInterval aI bI))
        ∧ (exceptionalRoots ((P M).map (algebraMap ℝ ℂ)) (ftInterval aI bI)).card ≤ C
        ∧ (exceptionalRoots ((P M).map (algebraMap ℝ ℂ)) posRay).card ≤ C := by
  intro M hM
  obtain ⟨a, b, L, ψ, Φ, hab, hτ, hzmono, hzS, hWne, hpolar, hΦdef,
    ⟨dψ, κ, hψ, hκ, hMκ⟩, hL, hLΦ, hdom, hdeg⟩ := hbranch M hM
  -- `eq:Phi-def`: both the continuity and the monotonicity come from the derivative bound
  have hΦcont : ContinuousOn Φ (Icc a b) := continuousOn_phase_congr hΦdef hψ
  have hΦmono : StrictMonoOn Φ (Icc a b) := strictMonoOn_phase_congr hΦdef hψ hκ hMκ
  exact main_clauses_of_dominance
    (dominanceSupply_of_ftDominance (hP M) hab hτ hzmono hzS hWne hpolar hΦdef hΦcont
      hΦmono hL hLΦ hdom)
    hdeg (hne M hM) haI

end ForgacsTran
