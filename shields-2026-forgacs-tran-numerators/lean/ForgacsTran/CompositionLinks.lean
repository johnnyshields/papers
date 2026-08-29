/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.Amplitude
import ForgacsTran.LaurentReduction
import ForgacsTran.EndpointPackage
import ForgacsTran.EndpointUpperPackage
import ForgacsTran.EndpointTauDeriv2
import ForgacsTran.LowerEndpointTangent
import ForgacsTran.FTBranchEndpointUpper
import ForgacsTran.FTMinModulus.UpperEndpoint
import ForgacsTran.BranchInteriorC1

/-!
# Links between the phase supply and the headline bound

`PhaseSupplyGeneral.ft_ftPhaseSupply_general` produces `FTPhaseSupply` at the
admissible pencil for **any** weight satisfying `HasRealCoeffs B` and
`B(0) ≠ 0`; `MainFT.main_bound_of_supply` consumes one at the **specific** weight
`B_N` of `eq:canonical-Laurent-factorization`, alongside conditions on the
spectral parameter.  This module carries the bridging statements, and nothing
about the supply itself.

## Main statements

* `hasRealCoeffs_laurentWeight` — `B_N` has real coefficients whenever `Q` and
  every `t`-coefficient of `N` do.  The route is `clearedRestrict_eq`: the
  cleared restriction `t^{rE}L_N` is a visibly real polynomial and equals
  `X^μ B_N`, so `B_N`'s coefficients are its own, shifted.
* `eval_laurentWeight_zero_ne_zero` — `B_N(0) ≠ 0`, which is
  `curveEval_eq_T_mul_weight` read through `coeff_zero_eq_eval_zero`.  It needs
  no hypothesis beyond the ones that theorem already carries.
* `ftBranchZLower_pos`, `strictMonoOn_ftBranchZLower_Ioo`,
  `continuousOn_ftBranchZLower_Ioo`, `ftTauArc_pos` — the four facts about `z`
  and `τ` on the open viewing arc, at the endpoint-extended spellings the phase
  supply is produced against.
* `tendsto_ftBranchZLower_nhdsGT_zero` and `continuousOn_ftBranchZLower_Ico` —
  at a repeated smallest zero the branch value runs into `0`, which is the value
  `ftBranchZLower` is defined to take there, so it is continuous on `[0,π/r)`.

## Implementation notes

The extension of the previous item to the **closed** arc `[0,π/r]` is false, and
`not_continuousOn_ftBranchZLower_Icc` and `not_strictMonoOn_ftBranchZLower_Icc`
record that: at `r ≥ 2` the branch value diverges at the upper end
(`eq:ab-def`'s `b = +∞`), so no value at `π/r` can make it continuous there and
none can lie above the whole arc.  Both statements a consumer asks for over
`Icc 0 (π/r)` therefore have to be asked for over `Ico 0 (π/r)` instead.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`:
`eq:canonical-Laurent-factorization` and `lem:laurent-reduction` (`sec:reduction`)
for the weight, `thm:FT-geometry` and `eq:ab-def` (`subsec:FT-geometry`) for the
spectral parameter, and `thm:main` for what consumes them.

## Tags

Laurent weight, real coefficients, spectral parameter, viewing arc, endpoint
-/

namespace ForgacsTran

open Polynomial Set Filter Topology Real

/-! ### `HasRealCoeffs`, closed under powers and negation -/

theorem HasRealCoeffs.neg {p : Polynomial ℂ} (hp : HasRealCoeffs p) :
    HasRealCoeffs (-p) := by
  simpa using hasRealCoeffs_zero.sub hp

theorem HasRealCoeffs.pow {p : Polynomial ℂ} (hp : HasRealCoeffs p) (k : ℕ) :
    HasRealCoeffs (p ^ k) := by
  induction k with
  | zero => simpa using hasRealCoeffs_one
  | succ k ih => rw [pow_succ]; exact ih.mul hp

/-! ### The reduced weight has real coefficients -/

/-- The cleared restriction of `sec:reduction` is built from `Q`, the
`t`-coefficients of `N` and powers of `t` alone, so it is real whenever they
are. -/
theorem hasRealCoeffs_clearedRestrict {Q : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    {N : (Polynomial ℂ)[X]} (hN : ∀ β, HasRealCoeffs (N.coeff β)) (r E : ℕ) :
    HasRealCoeffs (clearedRestrict Q r E N) := by
  rw [clearedRestrict]
  refine HasRealCoeffs.sum fun β _ => ?_
  exact (((hasRealCoeffs_one.neg.pow β).mul (hN β)).mul (hQ.pow β)).mul
    (hasRealCoeffs_X.pow _)

/-- **`B_N` has real coefficients.**  `clearedRestrict_eq` writes the cleared
restriction as `t^μ B_N` with `μ` a natural number, so `B_N`'s coefficients are
the cleared restriction's shifted by `μ`, and that polynomial is real. -/
theorem hasRealCoeffs_laurentWeight {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (hQ : HasRealCoeffs Q) {N : (Polynomial ℂ)[X]} (hN : N ≠ 0)
    (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) :
    HasRealCoeffs (laurentWeight Q r N) := by
  obtain ⟨μ, -, hEq⟩ := clearedRestrict_eq Q hr hQ0 hN hproper (E := N.natDegree) le_rfl
  intro k
  have hA := hasRealCoeffs_clearedRestrict hQ hNr r N.natDegree (k + μ)
  rwa [hEq, Polynomial.coeff_X_pow_mul] at hA

/-! ### The reduced weight does not vanish at the origin -/

/-- **`B_N(0) ≠ 0`**, in the `eval` form a consumer of the phase supply asks for.
`eq:canonical-Laurent-factorization` already delivers it as a statement about the
constant coefficient; no further hypothesis enters. -/
theorem eval_laurentWeight_zero_ne_zero {K : Type*} [Field K] (Q : K[X]) {r : ℕ}
    (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) {N : (K[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) :
    (laurentWeight Q r N).eval 0 ≠ 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact (curveEval_eq_T_mul_weight Q hr hQ0 hN hproper).1

/-! ### The spectral parameter on the viewing arc -/

/-- **`z > 0` on the open viewing arc**, at the endpoint-extended parameter.
`ftBranchZLower` agrees with `ftBranchZ` off `0`, so this is
`BranchInteriorC1.ftBranchZ_pos_principal` transported. -/
theorem ftBranchZLower_pos {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) :
    0 < ftBranchZLower a c r (n - 1) θ := by
  rw [ftBranchZLower_agree a c r (n - 1) hθ.1]
  exact ftBranchZ_pos_principal hn ha hc hr hnr hθ

/-- **`z` is strictly increasing on the open viewing arc**, at the
endpoint-extended parameter.  `FTGeometryBranch.ft_branch_supplies` transported
across `ftBranchZLower_agree`. -/
theorem strictMonoOn_ftBranchZLower_Ioo {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    StrictMonoOn (ftBranchZLower a c r (n - 1)) (Ioo 0 (π / r)) := by
  obtain ⟨-, -, hmono, -⟩ := ft_branch_supplies (a := a) (c := c) hn ha hc hr hnr
  intro x hx y hy hxy
  rw [ftBranchZLower_agree a c r (n - 1) hx.1, ftBranchZLower_agree a c r (n - 1) hy.1]
  exact hmono hx hy hxy

/-- **`z` is continuous on the open viewing arc**, at the endpoint-extended
parameter. -/
theorem continuousOn_ftBranchZLower_Ioo {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    ContinuousOn (ftBranchZLower a c r (n - 1)) (Ioo 0 (π / r)) := by
  refine (continuousOn_ftBranchZ (a := a) c hn ha hr hnr).congr fun θ hθ => ?_
  exact ftBranchZLower_agree a c r (n - 1) hθ.1

/-- **The branch radius is positive on the open viewing arc**, at the
endpoint-extended radius `ftTauArc`, which is the `hτ` a consumer of
`FTPhaseSupply` asks for. -/
theorem ftTauArc_pos {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) :
    0 < ftTauArc a r (n - 1) x₁ θ := by
  obtain ⟨-, hpos, -, -⟩ := ft_branch_supplies (a := a) (c := c) hn ha hc hr hnr
  rw [ftTauArc_agree a r (n - 1) x₁ hθ.1 hθ.2]
  exact hpos θ hθ

/-- **The branch value runs into `0` at the lower end**, at a repeated smallest
zero.  The radius runs into `x_1` (`EndpointTauDeriv2.tendsto_ftTau_endpoint`)
and `x_1` is a zero of `Q`, so the fiber value `-Q(x_1)/x_1^r` there is `0` —
which is exactly the value `ftBranchZLower` is defined to take at `0`. -/
theorem tendsto_ftBranchZLower_nhdsGT_zero {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hx₁ : 0 < x₁)
    (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    Tendsto (ftBranchZLower a c r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hn : 0 < n := by omega
  have hT := tendsto_ftTau_endpoint hn ha hr (Or.inl hn2) hx₁ hmin hcard hρ
  have h := tendsto_ftBranchZ_nhdsGT_zero (c := c) hn2 ha hr hx₁ hT
  have hne : (Finset.univ.filter fun k => a k = x₁).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  obtain ⟨i, hi⟩ := hne
  have hix : a i = x₁ := (Finset.mem_filter.1 hi).2
  have hzero : (ftRootPolyReal c a).eval x₁ = 0 := by
    rw [eval_ftRootPolyReal]
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hix]; ring))
  rw [hzero, neg_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  exact (ftBranchZLower_agree a c r (n - 1) hθ).symm

/-- **The spectral parameter is continuous on the half-open arc `[0,π/r)`**, at a
repeated smallest zero.  Off `0` this is
`FTMinModulus.UpperEndpoint.continuousOn_ftBranchZ`; at `0` it is
`tendsto_ftBranchZLower_nhdsGT_zero` against the defined endpoint value.

The closed arc is **not** available; see `not_continuousOn_ftBranchZLower_Icc`. -/
theorem continuousOn_ftBranchZLower_Ico {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hx₁ : 0 < x₁)
    (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ContinuousOn (ftBranchZLower a c r (n - 1)) (Ico 0 (π / r)) := by
  have hn : 0 < n := by omega
  have hr0 : (0 : ℝ) < r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hb : (0 : ℝ) < π / r := div_pos pi_pos hr0
  have hopen := continuousOn_ftBranchZ (a := a) c hn ha hr (Or.inl hn2)
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with hzero | hpos
  · -- the endpoint, where the extension is by the limit
    have hlim : Tendsto (ftBranchZLower a c r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_ftBranchZLower_nhdsGT_zero (c := c) hn2 ha hr hx₁ hmin hcard hρ
    have hIoo : ContinuousWithinAt (ftBranchZLower a c r (n - 1)) (Ioo 0 (π / r)) 0 := by
      have : Tendsto (ftBranchZLower a c r (n - 1)) (𝓝[Ioo 0 (π / r)] (0 : ℝ))
          (𝓝 (ftBranchZLower a c r (n - 1) 0)) := by
        rw [ftBranchZLower_zero]
        exact hlim.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
      exact this
    have hins : ContinuousWithinAt (ftBranchZLower a c r (n - 1))
        (insert 0 (Ioo 0 (π / r))) 0 := continuousWithinAt_insert_self.2 hIoo
    rw [Set.Ioo_insert_left hb] at hins
    exact hzero ▸ hins
  · -- the interior, where the two spellings agree on a neighborhood
    have hmem : θ ∈ Ioo (0 : ℝ) (π / r) := ⟨hpos, hθ.2⟩
    have hat : ContinuousAt (ftBranchZ a c r (n - 1)) θ :=
      (hopen θ hmem).continuousAt (isOpen_Ioo.mem_nhds hmem)
    have heq : ftBranchZ a c r (n - 1) =ᶠ[𝓝 θ] ftBranchZLower a c r (n - 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds hpos] with s hs
      exact (ftBranchZLower_agree a c r (n - 1) hs).symm
    exact ((hat.congr heq).continuousWithinAt)

/-! ### Why the closed arc is not available

`eq:ab-def` puts `b = +∞` at `r ≥ 2`: the spectral parameter diverges at the
upper end of the viewing arc.  So no value at `π/r` — the one `ftBranchZLower`
takes, or any other — extends it continuously there, and none lies above the
whole arc.  A consumer wanting `z` continuous and strictly increasing on a set
containing `π/r` cannot be fed this branch. -/

/-- The spectral parameter is not continuous on the **closed** viewing arc at
`r ≥ 2`, whatever value is assigned at `π/r`. -/
theorem not_continuousOn_ftBranchZLower_Icc {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) :
    ¬ ContinuousOn (ftBranchZLower a c r (n - 1)) (Icc 0 (π / r)) := by
  have hr1 : 1 ≤ r := by omega
  have hr0 : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hb : (0 : ℝ) < π / r := div_pos pi_pos hr0
  have hatop : Tendsto (ftBranchZLower a c r (n - 1))
      (𝓝[Ioo 0 (π / r)] (π / r)) atTop := by
    refine (tendsto_ftBranchZ_atTop_arc_end hn2 ha hc hr).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact (ftBranchZLower_agree a c r (n - 1) hθ.1).symm
  intro hcont
  have hwithin := hcont (π / r) ⟨hb.le, le_rfl⟩
  have hnhds : Tendsto (ftBranchZLower a c r (n - 1)) (𝓝[Ioo 0 (π / r)] (π / r))
      (𝓝 (ftBranchZLower a c r (n - 1) (π / r))) :=
    hwithin.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
  rw [nhdsWithin_Ioo_eq_nhdsLT hb] at hatop hnhds
  exact not_tendsto_nhds_of_tendsto_atTop hatop _ hnhds

/-- The spectral parameter is not strictly increasing on the **closed** viewing
arc at `r ≥ 2`: it exceeds any assigned value at `π/r` somewhere below it. -/
theorem not_strictMonoOn_ftBranchZLower_Icc {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) :
    ¬ StrictMonoOn (ftBranchZLower a c r (n - 1)) (Icc 0 (π / r)) := by
  have hr0 : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hb : (0 : ℝ) < π / r := div_pos pi_pos hr0
  have hatop : Tendsto (ftBranchZLower a c r (n - 1))
      (𝓝[Ioo 0 (π / r)] (π / r)) atTop := by
    refine (tendsto_ftBranchZ_atTop_arc_end hn2 ha hc hr).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact (ftBranchZLower_agree a c r (n - 1) hθ.1).symm
  haveI : (𝓝[Ioo (0 : ℝ) (π / r)] (π / r)).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsLT hb]; infer_instance
  intro hmono
  obtain ⟨θ, hgt, hmem⟩ :=
    ((hatop.eventually (eventually_gt_atTop
      (ftBranchZLower a c r (n - 1) (π / r)))).and self_mem_nhdsWithin).exists
  exact absurd (hmono ⟨hmem.1.le, hmem.2.le⟩ ⟨hb.le, le_rfl⟩ hmem.2) (not_lt.2 hgt.le)

end ForgacsTran
