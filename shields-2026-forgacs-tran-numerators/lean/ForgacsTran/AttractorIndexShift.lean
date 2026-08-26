/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.AttractorRate
import ForgacsTran.QuadraticDefect

/-!
# The index shift, and `cor:panel-B-attractor` in the paper's own variable

`AttractorRate` states the attractor rate for the general coefficient sequence
`F_M`.  `cor:panel-B-attractor` states it for the panel's own `P_m`, and
`lem:laurent-reduction` joins the two by `P_m = F_{m+2}`.  That join is made
here.

`panelReductionCoeff` already identifies `P_m` with `F_{m+2}` for any `F`
satisfying the denominator convolution system, but says nothing about which `F`
that is.  What was missing is the existence half in explicit form: that the
recursively defined `ftCoeffPoly` *is* such an `F`.  It is, and generally —
`denomConv_ftCoeffPoly` assumes nothing about the panel.

## Main statements

* `denomConv_ftCoeffPoly` — for any `Q, B` over a field and any `r ≥ 1` with
  `Q(0) ≠ 0`, the recursion `ftCoeffPoly` solves `prop:initial-data`'s system
  `∑_{j≤M} d_jF_{M-j} = C(B_M)`.  This is the existence counterpart of
  `Reduction.initial_data_unique`, in the explicit form the abstract
  `Reduction.exists_denomConv_eq` does not give.
* `panelPC` — the panel's `P_m` over `ℂ`, where its zeros live.
* `panelPC_eq_ftCoeffPoly` — `eq:reduction-coeff` at the panel with the
  coefficient sequence named: `P_m = F_{m+2}` with
  `F_M = ftCoeffPoly panelDenQ panelBC 1 M`, for `m ≥ 4`.
* `panelP_attractor_rate` — `cor:panel-B-attractor`'s second assertion in the
  paper's own index: `P_m` has a unique **simple** zero `z_m` in a fixed disk
  about `z_*`, and `‖z_m - z_*‖ ≤ K·3^{-m}`.
* `panelP_attractor_rate_conj` — the same for the conjugate packet.

## Implementation notes

`ftDenom` (`Reduction`) and `ftDenCoeff` (`AttractorPole`) are the same
definition under two names; `AttractorPole` does not import `Reduction`, which
is why both exist.  `ftDenCoeff_eq_ftDenom` is the bridge, and it is `rfl`.

**Two thresholds compose, and the composition is explicit.**  `panelP_m` is
identified with `F_{m+2}` only for `m ≥ 4` (`panelReductionCoeff`), while the
rate holds only for `M ≥ M₀` (`panel_attractor_rate`), so the statement below
takes `m₀ = max 4 M₀` and carries `4 ≤ m₀` in the statement rather than leaving
a reader to assume `M₀` already covered it.  Neither threshold is tight:
`scripts/check_panel_numerator_branch.py` measures the true reduction threshold
at `m = 2`.

The rate transports without enlarging the constant, since the `F`-index is two
ahead: `K·(1/3)^{m+2} ≤ K·(1/3)^m`.  The sharper `K/9` is available and is not
claimed, because the paper states `O(3^{-m})`.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Canonical Laurent
reduction and eventual degree» and «Global and local zero laws»
(`sec:reduction`, `prop:initial-data`, `lem:laurent-reduction`,
`eq:reduction-coeff`, `sec:consequences`, `subsec:isolated-attractors`,
`cor:panel-B-attractor`).

## Tags

initial data, coefficient recurrence, index shift, zero attractor
-/

namespace ForgacsTran

open Complex Metric Polynomial Shields ComplexConjugate

/-! ### The existence half of `prop:initial-data`, explicitly -/

/-- `Reduction`'s denominator coefficient and `AttractorPole`'s are the same
object; the modules do not see each other. -/
theorem ftDenCoeff_eq_ftDenom (Q : ℂ[X]) (r i : ℕ) : ftDenCoeff Q r i = ftDenom Q r i := rfl

/-! ### The existence half of `prop:initial-data`

`denomConv_ftCoeffPoly` is in `QuadraticDefect`, proved there for arbitrary `Q`,
`B` and `r ≥ 1`.  It is the evaluable counterpart of
`Reduction.exists_denomConv_eq`, whose solution is built from a power-series
inverse and so cannot be computed with; naming the explicit recursion as *the*
solution is what lets `Reduction.initial_data_unique` identify a second sequence
with it, which is the step `panelPC_eq_ftCoeffPoly` turns on. -/
/-! ### Transport of the system from `ℚ` to `ℂ` -/

private theorem map_denomConv (f : ℚ →+* ℂ) (d P : ℕ → ℚ[X]) (M : ℕ) :
    (denomConv d P M).map f = denomConv (fun j => (d j).map f) (fun m => (P m).map f) M := by
  change Polynomial.mapRingHom f (denomConv d P M) = _
  simp only [denomConv, map_sum, map_mul, Polynomial.coe_mapRingHom]

private theorem map_ftDenom (f : ℚ →+* ℂ) (Q : ℚ[X]) (r i : ℕ) :
    (ftDenom Q r i).map f = ftDenom (Q.map f) r i := by
  by_cases h : i = r <;>
    simp [ftDenom, h, Polynomial.map_add, Polynomial.map_C, Polynomial.coeff_map]

theorem panelDenQ_coeff_zero : panelDenQ.coeff 0 = 1 := by
  rw [panelDenQ_eq_map, Polynomial.coeff_map, panelDenQrat_coeff_zero, map_one]

/-! ### The join -/

/-- Paper `cor:panel-B-attractor` — the panel's coefficient polynomials over
`ℂ`, which is where their zeros live.  `panelP` is defined over `ℚ`. -/
noncomputable def panelPC (m : ℕ) : ℂ[X] := (panelP m).map (algebraMap ℚ ℂ)

/-- **Paper `eq:reduction-coeff` at the panel, with the sequence named.**
`P_m = F_{m+2}` for `m ≥ 4`, where `F_M = ftCoeffPoly panelDenQ panelBC 1 M` is
the coefficient sequence `prop:isolated-dominant-cancellation` runs on.

`panelReductionCoeff` supplies the shift for *some* solution of the convolution
system and `denomConv_ftCoeffPoly` shows `ftCoeffPoly` is one; the two are the
same solution by `Reduction.initial_data_unique`, the diagonal being the unit
`C(Q(0)) = 1`.

The threshold `4` is `panelReductionCoeff`'s, which is
`deg_zN·(deg Q - r) = 2·2`.  It is not tight —
`scripts/check_panel_numerator_branch.py` measures the identity from `m = 2` —
and it is not sharpened here. -/
theorem panelPC_eq_ftCoeffPoly {m : ℕ} (hm : 4 ≤ m) :
    panelPC m = ftCoeffPoly panelDenQ panelBC 1 (m + 2) := by
  have hdQ : IsUnit (ftDenom panelDenQrat 1 0) := by
    rw [ftDenom_zero panelDenQrat le_rfl, panelDenQrat_coeff_zero, map_one]
    exact isUnit_one
  obtain ⟨F, hF⟩ := exists_denomConv_eq hdQ (fun M => Polynomial.C (panelBrat.coeff M))
  -- the mapped sequence solves the pencil system over `ℂ`
  have hFC : ∀ M, denomConv (ftDenom panelDenQ 1) (fun k => (F k).map (algebraMap ℚ ℂ)) M
      = C (panelBC.coeff M) := by
    intro M
    have h := congrArg (fun p : ℚ[X] => p.map (algebraMap ℚ ℂ)) (hF M)
    simp only [map_denomConv, Polynomial.map_C] at h
    rw [show (fun j => (ftDenom panelDenQrat 1 j).map (algebraMap ℚ ℂ))
        = ftDenom panelDenQ 1 from ?_] at h
    · rw [h, panelBC, Polynomial.coeff_map]
    · funext j
      rw [map_ftDenom, ← panelDenQ_eq_map]
  -- so does `ftCoeffPoly`, and the diagonal is a unit, so they coincide
  have hdC : IsUnit (ftDenom panelDenQ 1 0) := by
    rw [ftDenom_zero panelDenQ le_rfl, panelDenQ_coeff_zero, map_one]
    exact isUnit_one
  have huniq := initial_data_unique hdC
    (fun M => (hFC M).trans (denomConv_ftCoeffPoly _ panelBC le_rfl
      (by rw [panelDenQ_coeff_zero]; norm_num) M).symm)
  rw [panelPC, panelReductionCoeff F hF m hm]
  exact congrFun huniq (m + 2)

/-- **Paper `cor:panel-B-attractor` — the attractor rate, in the paper's index.**
There is a nonreal algebraic `z_*` and a fixed disk about it such that, for every
`m` past a threshold, `P_m` has exactly one zero `z_m` in that disk, that zero is
**simple**, and `‖z_m - z_*‖ ≤ K·3^{-m}`.  This is the corollary's "a unique
simple zero `z_m` near `z_*` with `z_m = z_* + O(3^{-m})`" as the corollary
states it.

Simplicity and uniqueness are separate clauses because they are separate claims:
the `↔` says no other point of the disk is a zero, and a double zero at one point
would satisfy it.  What rules that out is the multiplicity clause, which comes
from the `FactoredOn` count of one at the displayed point.

The threshold carries `4 ≤ m₀` because two of them compose: `m ≥ 4` for the
index shift and `m + 2 ≥ M₀` for the rate, and `m₀` is their maximum. -/
theorem panelP_attractor_rate :
    ∃ z : ℂ, z.im ≠ 0 ∧ panelResultant z = 0 ∧
      ∃ ε > 0, ∃ K ≥ (0 : ℝ), ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∀ m ≥ m₀, ∃ zm : ℂ,
        ‖zm - z‖ ≤ K * (1 / 3 : ℝ) ^ m ∧
        (panelPC m).rootMultiplicity zm = 1 ∧
        ∀ w ∈ closedBall z ε, (panelPC m).eval w = 0 ↔ w = zm := by
  obtain ⟨z, hzim, hres, ε, hε, K, hK, M₀, hM⟩ := panel_attractor_rate
  refine ⟨z, hzim, hres, ε, hε, K, hK, max 4 M₀, le_max_left _ _, fun m hmm => ?_⟩
  have hm4 : 4 ≤ m := le_trans (le_max_left _ _) hmm
  have hmM : M₀ ≤ m + 2 := le_trans (le_trans (le_max_right _ _) hmm) (by omega)
  obtain ⟨zm, hrate, hmult, hzero⟩ := hM (m + 2) hmM
  refine ⟨zm, ?_, ?_, ?_⟩
  · refine hrate.trans ?_
    have hpow : (1 / 3 : ℝ) ^ (m + 2) ≤ (1 / 3 : ℝ) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact mul_le_mul_of_nonneg_left hpow hK
  · rw [panelPC_eq_ftCoeffPoly hm4]
    exact hmult
  · intro w hw
    rw [panelPC_eq_ftCoeffPoly hm4]
    exact hzero w hw

/-- **Paper `cor:panel-B-attractor` — the conjugate packet, in the paper's
index.**  `P_m` has rational coefficients, so alongside `z_m` there is
`conj z_m`, simple, alone in the reflected disk, and converging to `conj z_*` at
the same rate. -/
theorem panelP_attractor_rate_conj :
    ∃ z : ℂ, z.im ≠ 0 ∧ panelResultant z = 0 ∧
      ∃ ε > 0, ∃ K ≥ (0 : ℝ), ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∀ m ≥ m₀, ∃ zm : ℂ,
        ‖zm - z‖ ≤ K * (1 / 3 : ℝ) ^ m ∧
        (panelPC m).rootMultiplicity zm = 1 ∧
        (∀ w ∈ closedBall z ε, (panelPC m).eval w = 0 ↔ w = zm) ∧
        ‖conj zm - conj z‖ ≤ K * (1 / 3 : ℝ) ^ m ∧
        (panelPC m).rootMultiplicity (conj zm) = 1 ∧
        (∀ w ∈ closedBall (conj z) ε, (panelPC m).eval w = 0 ↔ w = conj zm) := by
  obtain ⟨z, hzim, hres, ε, hε, K, hK, M₀, hM⟩ := panel_attractor_rate_conj
  refine ⟨z, hzim, hres, ε, hε, K, hK, max 4 M₀, le_max_left _ _, fun m hmm => ?_⟩
  have hm4 : 4 ≤ m := le_trans (le_max_left _ _) hmm
  have hmM : M₀ ≤ m + 2 := le_trans (le_trans (le_max_right _ _) hmm) (by omega)
  obtain ⟨zm, hrate, hmult, hzero, hrate', hmult', hzero'⟩ := hM (m + 2) hmM
  have hpow : K * (1 / 3 : ℝ) ^ (m + 2) ≤ K * (1 / 3 : ℝ) ^ m :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hK
  refine ⟨zm, hrate.trans hpow, ?_, fun w hw => ?_, hrate'.trans hpow, ?_, fun w hw => ?_⟩
  · rw [panelPC_eq_ftCoeffPoly hm4]; exact hmult
  · rw [panelPC_eq_ftCoeffPoly hm4]; exact hzero w hw
  · rw [panelPC_eq_ftCoeffPoly hm4]; exact hmult'
  · rw [panelPC_eq_ftCoeffPoly hm4]; exact hzero' w hw

end ForgacsTran
