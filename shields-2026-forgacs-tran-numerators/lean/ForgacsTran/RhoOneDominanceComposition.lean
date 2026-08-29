/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.RhoOneEndpointFactorization
import ForgacsTran.WeightedDominanceBranchOne
import ForgacsTran.LowerSeparationNormalized
import ForgacsTran.WeightedDominanceBranch

/-!
# `thm:weighted-dominance` at the branch, the two `ρ = 1` corners

`subsec:proof` walks a 2×2 grid: `ρ` governs the lower endpoint — the principal
pair collides at the smallest zero when it is repeated, at the critical point `t_a`
when it is simple — and `r` governs the upper, independently.  This module holds
both `ρ = 1` cells: `r = 1` and `2 ≤ r`.  `WeightedDominanceBranch` covers `2 ≤ ρ`
with `2 ≤ r`, `WeightedDominanceBranchOne` covers `2 ≤ ρ` with `r = 1`, and this
module covers `ρ = 1` with `r = 1` — the smallest zero simple at both ends of the
dichotomy `eq:ab-def` draws.

**Both retained clusters are empty here.**  `n₀ = ρ - 2 = 0` and `n₁ = r - 2 = 0`
in `ℕ`, so every binder quantified over either family is met by `Fin.elim0`, and
the five conditioned on `0 < n₀` — `hρ`, `hcB₀`, `hcQ₀`, `hBp₀`, `hEp₀` — are
vacuous.  The `clusterAlpha` degeneracy `Cluster.clusterAlpha_one_eq_zero`
records, and the contradiction `hEp_false_of_rho_one` derives, are both about the
unconditioned forms and cannot be reached from here.

What carries the content is the two principal pairs and their circles: at the
lower end the pair collides at the critical point `t_a`, at the upper end at `-L`,
and each is exactly the pencil's zero set inside its own radius.

**The corner is unconditional.**  The lower endpoint's separation, an antecedent
while it was being proved, is now
`LowerSeparationNormalized.lt_norm_of_root_endpoint_of_first_gap`: at a positive
critical point lying in the first gap — below every zero but the smallest — and
missing every zero, each other root of the endpoint pencil is strictly outside.
Nothing is left for a caller to supply beyond the admissible class.

**The first-gap restriction is load-bearing, and was not there originally.**

**Dropping the first-gap clause makes the hypothesis unmeetable, not merely
weaker.**  With `v_k = t/(a_k - t)` the critical equation is `∑_k v_k = -r`, and
`v_k < 0` exactly when `a_k < t`; the first gap is where exactly one coordinate is
negative.  `Σ` sweeps `-∞` to `+∞` across *every* gap, so an admissible pencil with
`3 ≤ n` always has a critical point in the second gap, where two are negative and
separation fails.  A version quantified over all critical points is therefore false
for every admissible `a`, and the theorem built on it would be vacuous while
compiling green and carrying a clean axiom footprint — nothing in a build, an axiom
guard or a mutation sweep can see that — this statement carried exactly that
defect until it was measured.  `scripts/check_rho_one_hsep_scope.py` measures both
halves, and the clause that repairs it is also what hands the separation theorem
its one-negative configuration.  `LowerSeparationNormalized` reduces it to
a statement with no pencil in it.  Everything else in this corner is proved, and
`exists_separating_radius` is what turns the strict inequality into the radius the
group actually reads — there is no uniform clearance at `ρ = 1`, so no constant
could have played that part.

## Main statements

Five dominance theorems here state the same bound, and their statements are long
enough that the differences do not show on a read.  They differ in exactly three
places — which `r`, whether the interior supply is assumed or produced, and how the
band is quantified:

* `ft_weighted_dominance_rho_one` — `r = 1`; interior supply an antecedent, in data
  form; one produced `ε`.
* `ft_weighted_dominance_rho_one_of_le` — the same, restated so the caller picks any
  `ε ≤ ε₀`, by antitonicity.
* `ft_weighted_dominance_rho_one_unconditional` — `r = 1`; interior supply
  **produced**; the deleted windows written out rather than quantified.
* `ft_weighted_dominance_rho_one_two_le` — `2 ≤ r`; interior supply an antecedent, in
  data form; one produced `ε`.
* `ft_weighted_dominance_rho_one_two_le_unconditional` — `2 ≤ r`; interior supply
  **produced**; the deleted windows written out.

The two `_unconditional` forms are the ones with nothing left to supply, and they are
what a caller wants; the other three exist because the interior supply is where this
corner's remaining work sat while it was being closed, and a form that takes it as an
antecedent is what let the rest be checked against its consumer meanwhile.

The two non-dominance statements are witnesses:
`ft_weighted_dominance_rho_one_hypotheses_nonvacuous` and
`..._two_le_hypotheses_nonvacuous`, the second exercising both sides of the `r = 2`
boundary where `Fin (r - 2)` becomes `Fin 0`.

**The interior supply's clause list is not named here, and should be.**  It is written
out inline at three of the five, which is what makes them hard to tell apart.
`DominanceBandAntitone.ftInteriorData` is that predicate, minted for exactly this
purpose — but it is defined downstream of this module, so it cannot be called from
here.  Its home is `DominanceFT`, beside the `ftRemainder` and `ftPrincipalAmp` it is
about and upstream of every corner that inlines it.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:dominance-bound`, `eq:retained-range`, `eq:ab-def`, `subsec:proof`.

## Tags

weighted dominance, rho = 1, simple smallest zero, principal pair, collision
-/

namespace ForgacsTran

open Real Set Filter Polynomial Complex
open scoped Topology

/-- **`thm:weighted-dominance` at the branch, `ρ = 1` and `r = 1`.**  The fourth
corner.  Both retained clusters are empty — `n₀ = n₁ = 0` — so the content is the
two principal pairs and their circles, and every cluster binder is met by
`Fin.elim0`.

The lower endpoint's separation is supplied by
`LowerSeparationNormalized.lt_norm_of_root_endpoint_of_first_gap`, which bridges
`LowerSeparationQuotient`'s normalized statement into the paper's own variables.
`exists_separating_radius` turns it into the radius the group reads.  There is no
uniform clearance at `ρ = 1`, so no constant could have taken that part. -/
theorem ft_weighted_dominance_rho_one {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta > (0 : ℝ), ∃ L > (0 : ℝ),
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
          (∃ (CI σI AI : ℝ) (Sd : Finset ℝ) (νd : ℝ → ℕ),
            0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ Sd, 1 ≤ νd θj) ∧
            (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ π - ε →
              |ftRemainder (ftRootPoly c a) B 1
                (ftBranchZLowerAt a c 1 (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                (ftTauArc a 1 (n - 1) ta) M θ| ≤ CI * σI ^ M) ∧
            (∀ θ : ℝ, ε ≤ θ → θ ≤ π - ε →
              AI * ∏ θj ∈ Sd, |θ - θj| ^ νd θj
                ≤ ftPrincipalAmp (ftRootPoly c a) B 1
                  (ftBranchZLowerAt a c 1 (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                  (ftTauArc a 1 (n - 1) ta) θ) ∧
            (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ Sd,
              Real.exp (-((-Real.log σI) / (2 * Sd.card) * M / νd θj)) ≤ |θ - θj|)) →
          ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
            1 / M ≤ θ → θ ≤ π - 1 / M → θ ∉ Θ M →
              ftRemainder (ftRootPoly c a) B 1
                  (ftBranchZLowerAt a c 1 (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                  (ftTauArc a 1 (n - 1) ta) M θ
                ≤ ftPrincipalAmp (ftRootPoly c a) B 1
                  (ftBranchZLowerAt a c 1 (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                  (ftTauArc a 1 (n - 1) ta) θ / 2 := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hn : 0 < n := by omega
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  have hQre : HasRealCoeffs (ftRootPoly c a) := hasRealCoeffs_ftRootPoly c a
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hcast : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  -- the lower endpoint
  obtain ⟨ta, hlow, hup, hlim, hE, hγd⟩ :=
    rho_one_hgd (r := 1) hn2 ha hc le_rfl hmin hsimple
  have hta : 0 < ta := lt_trans (ha i) hlow
  have hne : ∀ k, a k - ta ≠ 0 := by
    intro k
    rcases eq_or_ne k i with rfl | hk
    · exact sub_ne_zero.2 (by linarith)
    · exact sub_ne_zero.2 (by linarith [hup k hk])
  have hQta : (ftRootPolyReal c a).eval ta ≠ 0 := by
    rw [eval_ftRootPolyReal]
    exact mul_ne_zero hc.ne' (Finset.prod_ne_zero_iff.2 fun k _ => hne k)
  set aEnd : ℝ := -((ftRootPolyReal c a).eval ta) / ta ^ 1 with haEnd
  have hpne : ftDen (ftRootPoly c a) 1 ((aEnd : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have hev : (ftDen (ftRootPoly c a) 1 ((aEnd : ℝ) : ℂ)).eval 0 = 0 := by
      rw [h0]; simp
    rw [ftDen_eval, zero_pow (by omega : (1 : ℕ) ≠ 0), mul_zero, add_zero] at hev
    exact hQ0 hev
  obtain ⟨R₀, hR, hRsep⟩ := exists_separating_radius hpne
      (lt_norm_of_root_endpoint_of_first_gap (i := i) hn2 le_rfl hc.ne' ta hta hne hup hE)
  have hR0 : (0 : ℝ) < R₀ := lt_trans hta hR
  obtain ⟨e₀, he₀, hlowblk⟩ := window_of_eventually
    (eventually_lower_retained_rho_one hn2 ha hc le_rfl hta hne hE hlim hR hRsep)
  -- the branch parameter runs into the endpoint value
  have hmemarc : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioo 0 π ∧ FTBranchAt a 1 (n - 1) δ := by
    filter_upwards [Ioo_mem_nhdsGT hπ] with δ hδ
    refine ⟨hδ, ftBranchAt_of_arc_principal hn ha le_rfl (Or.inl hn2) ?_⟩
    rw [hcast]; exact hδ
  have hz : Tendsto (ftBranchZ a c 1 (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 aEnd) :=
    tendsto_ftBranchZ_lower (c := c) ha hta hmemarc hlim
  have hzC : Tendsto (fun δ => ((ftBranchZ a c 1 (n - 1) δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((aEnd : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hz
  have hlimsphere : ∀ t : ℂ, ‖t‖ = R₀ →
      (ftDen (ftRootPoly c a) 1 ((aEnd : ℝ) : ℂ)).eval t ≠ 0 := by
    intro t ht hzero
    by_cases hteq : t = ((ta : ℝ) : ℂ)
    · rw [hteq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hta] at ht
      exact absurd ht (by linarith)
    · exact absurd ht (by have := hRsep t hzero hteq; linarith)
  -- the upper endpoint block, at the same radius parameter
  obtain ⟨L, hL, sfun₁, hblk⟩ := exists_upper_endpoint_block_one (x₁ := ta) hn2 ha hc
  refine ⟨ta, hta, L, hL, fun B hB hB0 => ?_⟩
  have hB0' : B ≠ 0 := fun h0 => hB0 (by rw [h0]; simp)
  obtain ⟨C₀, hC₀, ec₀, hec₀, hcbd₀⟩ :=
    exists_contour_bound_of_tendsto (B := B) hzC hR0 hlimsphere
  obtain ⟨C₁, A₁, hC₁, hA₁, e₁, he₁, he₁π, hupblk⟩ := hblk B hB0'
  -- the two spectral parameters agree off the endpoint
  have hZ : ∀ θ : ℝ, 0 < θ →
      ftBranchZLowerAt a c 1 (n - 1) aEnd θ = ftBranchZ a c 1 (n - 1) θ :=
    fun θ hθ => ftBranchZLowerAt_agree a c 1 (n - 1) aEnd hθ
  have hbr : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      ftBranchZLowerAt a c 1 (n - 1) aEnd (π - δ)
        = ftBranchZLower a c 1 (n - 1) (π - δ) := by
    intro δ hδ hδe
    have hpos : (0 : ℝ) < π - δ := by linarith
    rw [hZ (π - δ) hpos, ftBranchZLower_agree a c 1 (n - 1) hpos]
  -- the lower window, and its two remaining binders
  have hE₀ : (0 : ℝ) < min e₀ ec₀ := lt_min he₀ hec₀
  have hE₀a : ∀ δ : ℝ, δ ≤ min e₀ ec₀ → δ ≤ e₀ := fun δ h => le_trans h (min_le_left _ _)
  have hE₀c : ∀ δ : ℝ, δ ≤ min e₀ ec₀ → δ ≤ ec₀ := fun δ h => le_trans h (min_le_right _ _)
  have hbpos : (0 : ℝ) < π / ((1 : ℕ) : ℝ) := by rw [hcast]; exact hπ
  have hγ0₀ : ftPrincipal (ftTauArc a 1 (n - 1) ta) 0 = ((ta : ℝ) : ℂ) := by
    rw [ftPrincipal_ftTauArc_eq_lower a 1 (n - 1) ta hbpos, ftPrincipal_ftTauLower_zero]
  have hγdArc : HasDerivWithinAt (fun δ : ℝ => ftPrincipal (ftTauArc a 1 (n - 1) ta) δ)
      (((ta : ℝ) : ℂ) * I) (Set.Ici 0) 0 := by
    refine hγd.congr_of_eventuallyEq ?_ (ftPrincipal_ftTauArc_eq_lower a 1 (n - 1) ta hbpos)
    have hmem : Set.Iio (π / ((1 : ℕ) : ℝ)) ∈ 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds hbpos)
    filter_upwards [hmem] with θ hθ
    exact ftPrincipal_ftTauArc_eq_lower a 1 (n - 1) ta hθ
  have hk₀ : 1 ≤ (ftDen (ftRootPoly c a) 1
      ((ftBranchZLowerAt a c 1 (n - 1) aEnd 0 : ℝ) : ℂ)).rootMultiplicity
        ((ta : ℝ) : ℂ) := by
    rw [ftBranchZLowerAt_zero, haEnd,
      rootMultiplicity_ftDen_eq_two_at_critical hn ha hc.ne' (le_refl 1) hta.ne' hne hE hQta]
    omega
  have hrootev₀ : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (ftDen (ftRootPoly c a) 1
        ((ftBranchZLowerAt a c 1 (n - 1) aEnd δ : ℝ) : ℂ)).eval
        (ftPrincipal (ftTauArc a 1 (n - 1) ta) δ) = 0 :=
    eventually_of_window hE₀ fun δ hδ hδe => by
      rw [hZ δ hδ]; exact (hlowblk δ hδ (hE₀a δ hδe)).2.2.1
  have hσ₀ : (ta + R₀) / 2 / R₀ ≤ (ta + R₀) / 2 / R₀ := le_rfl
  have hσ₀1 : (ta + R₀) / 2 / R₀ < 1 := by
    rw [div_lt_one hR0]
    linarith
  exact weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data
      (h := 1) (b := π) (z := ftBranchZLowerAt a c 1 (n - 1) aEnd)
      (τ := ftTauArc a 1 (n - 1) ta)
      (sfun₀ := fun δ => {ftPrincipal (ftTauArc a 1 (n - 1) ta) δ,
        ((ftTauArc a 1 (n - 1) ta δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)})
      (sfun₁ := sfun₁) (g₀ := fun _ _ => 0) (g₁ := fun _ _ => 0)
      (n₀ := 0) (n₁ := 0) (idx₀ := fun _ => 0) (jp₀ := 0) (νB₀ := 0)
      (cB₀ := 1) (cQ₀ := 1) (x₁ := ta) (ρ := 2)
      (te₀ := ((ta : ℝ) : ℂ)) (γe₀ := ((ta : ℝ) : ℂ) * I)
      (R₀ := R₀) (τmax₀ := (ta + R₀) / 2) (σ₀ := (ta + R₀) / 2 / R₀)
      (e₀ := min e₀ ec₀) (C₀ := C₀)
      (p₁ := B.rootMultiplicity ((-L : ℝ) : ℂ) - 1) (A₁ := A₁) (L₁ := fun i => i.elim0)
      (R₁ := 2 * L) (τmax₁ := 3 * L / 2) (σ₁ := 3 / 4) (e₁ := e₁) (C₁ := C₁)
      (c₀ := 0) (c₁ := 0)
      hQre hB hB0' (le_refl 1) hQ0 hta (fun h => absurd h (lt_irrefl 0))
      (by exact_mod_cast hta.ne') (by
        simpa using mul_ne_zero (by exact_mod_cast hta.ne' : ((ta : ℝ) : ℂ) ≠ 0)
          Complex.I_ne_zero)
      hγ0₀ hγdArc hk₀ hrootev₀
      (fun h => absurd h (lt_irrefl 0)) (fun h => absurd h (lt_irrefl 0))
      (fun i => i.elim0) (fun h => absurd h (lt_irrefl 0))
      (fun i => i.elim0) (fun h => absurd h (lt_irrefl 0))
      hR0 hσ₀ hσ₀1 hE₀
      (fun δ hδ hδe => (hlowblk δ hδ (hE₀a δ hδe)).1)
      (fun δ hδ hδe => (hlowblk δ hδ (hE₀a δ hδe)).2.1)
      (fun δ hδ hδe t ht => by
        rw [hZ δ hδ]; exact ((hlowblk δ hδ (hE₀a δ hδe)).2.2.2.2.1 t ht).1)
      (fun δ hδ hδe t ht => by
        rw [hZ δ hδ]; exact ((hlowblk δ hδ (hE₀a δ hδe)).2.2.2.2.1 t ht).2.2)
      (fun δ hδ hδe t ht => ((hlowblk δ hδ (hE₀a δ hδe)).2.2.2.2.1 t ht).2.1)
      (fun δ hδ hδe t ht h0 => (hlowblk δ hδ (hE₀a δ hδe)).2.2.2.2.2 t ht
        (by rwa [hZ δ hδ] at h0))
      (fun δ hδ hδe => by rw [hZ δ hδ]; exact (hlowblk δ hδ (hE₀a δ hδe)).2.2.1)
      (fun δ hδ hδe => (hlowblk δ hδ (hE₀a δ hδe)).2.2.2.1)
      (fun δ _ _ => Function.injective_of_subsingleton _)
      (fun δ _ _ i => i.elim0)
      (fun δ hδ hδe => by
        rw [Finset.erase_insert (by simpa using (hlowblk δ hδ (hE₀a δ hδe)).2.2.2.1),
          Finset.erase_singleton, Finset.card_empty])
      hC₀ (fun δ hδ hδe t ht => by
        rw [hZ δ hδ]; exact (hcbd₀ δ hδ (hE₀c δ hδe) t ht).2)
      hA₁ ⟨e₁, he₁, fun η hη hηe => by
        simpa [ftPrincipalAmp, hbr η hη hηe] using
          (hupblk η hη hηe).2.2.2.2.2.2.2.2.2.2⟩
      (fun i => i.elim0) (fun i => i.elim0)
      (by positivity) (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
      (by norm_num) he₁
      (fun δ hδ hδe => (hupblk δ hδ hδe).1)
      (fun δ hδ hδe => (hupblk δ hδ hδe).2.1)
      (fun δ hδ hδe t ht => by
        rw [hbr δ hδ hδe]; exact (hupblk δ hδ hδe).2.2.1 t ht)
      (fun δ hδ hδe t ht => by
        rw [hbr δ hδ hδe]; exact (hupblk δ hδ hδe).2.2.2.1 t ht)
      (fun δ hδ hδe t ht => (hupblk δ hδ hδe).2.2.2.2.1 t ht)
      (fun δ hδ hδe t ht h0 => (hupblk δ hδ hδe).2.2.2.2.2.1 t ht
        (by rwa [hbr δ hδ hδe] at h0))
      (fun δ hδ hδe => by
        rw [hbr δ hδ hδe]; exact (hupblk δ hδ hδe).2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hupblk δ hδ hδe).2.2.2.2.2.2.2.1)
      (fun δ _ _ => Function.injective_of_subsingleton _)
      (fun δ _ _ i => i.elim0)
      (fun δ hδ hδe => (hupblk δ hδ hδe).2.2.2.2.2.2.2.2.1)
      hC₁ (fun δ hδ hδe t ht => by
        rw [hbr δ hδ hδe]; exact (hupblk δ hδ hδe).2.2.2.2.2.2.2.2.2.1 t ht)
      one_pos ⟨1, one_pos, fun δ _ _ i => i.elim0⟩ ⟨1, one_pos, fun δ _ _ i => i.elim0⟩
      ⟨1, one_pos, fun A ζ' θ W _ _ hW _ _ M _ => by simpa using by linarith⟩
      ⟨1, one_pos, fun A ζ' η W _ _ hW _ _ M _ => by simpa using by linarith⟩

/-- **The corner's `ε` is a threshold, not a choice.**  The interior supply is
**antitone** in `ε` — its clauses are hypotheses on `Icc ε (π - ε)`, so a smaller
`ε` is a larger window and a stronger assumption — while the conclusion names no
`ε` at all.  So whatever `ε` `ft_weighted_dominance_rho_one` returns, every smaller
one serves.

**This is not required by the phase supply, and should not be read as load-bearing.**
`exists_ftPhaseSupply_of_dominance` takes `ε` and `hdom` from one existential bundle
per numerator, so an existential here meets an existential there and the shapes
already agree; the uniformity that matters at that seam is `κ₀`, `κ₁`, bound outside
`∀ B`, and it is correctly placed.  What is recorded here is the antitonicity
itself, which costs three lines and is otherwise re-derived by anyone who wonders
whether the two `ε` can be reconciled.

Nothing about `ρ = 1` enters; the same wrapper fits the other three corners. -/
theorem ft_weighted_dominance_rho_one_of_le {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta > (0 : ℝ), ∃ L > (0 : ℝ),
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ ε₀ > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ Θ : ℕ → Set ℝ,
          (∃ (CI σI AI : ℝ) (Sd : Finset ℝ) (νd : ℝ → ℕ),
            0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ Sd, 1 ≤ νd θj) ∧
            (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ π - ε →
              |ftRemainder (ftRootPoly c a) B 1
                (ftBranchZLowerAt a c 1 (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                (ftTauArc a 1 (n - 1) ta) M θ| ≤ CI * σI ^ M) ∧
            (∀ θ : ℝ, ε ≤ θ → θ ≤ π - ε →
              AI * ∏ θj ∈ Sd, |θ - θj| ^ νd θj
                ≤ ftPrincipalAmp (ftRootPoly c a) B 1
                  (ftBranchZLowerAt a c 1 (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                  (ftTauArc a 1 (n - 1) ta) θ) ∧
            (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ Sd,
              Real.exp (-((-Real.log σI) / (2 * Sd.card) * M / νd θj)) ≤ |θ - θj|)) →
          ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
            1 / M ≤ θ → θ ≤ π - 1 / M → θ ∉ Θ M →
              ftRemainder (ftRootPoly c a) B 1
                  (ftBranchZLowerAt a c 1 (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                  (ftTauArc a 1 (n - 1) ta) M θ
                ≤ ftPrincipalAmp (ftRootPoly c a) B 1
                  (ftBranchZLowerAt a c 1 (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                  (ftTauArc a 1 (n - 1) ta) θ / 2 := by
  obtain ⟨ta, hta, L, hL, H⟩ :=
    ft_weighted_dominance_rho_one hn3 ha hc hmin hsimple
  refine ⟨ta, hta, L, hL, fun B hB hB0 => ?_⟩
  obtain ⟨ε₀, hε₀, H₀⟩ := H B hB hB0
  refine ⟨ε₀, hε₀, fun ε hε hle Θ hdata => ?_⟩
  obtain ⟨CI, σI, AI, Sd, νd, hσ0, hσ1, hA, hν, hrem, hfloor, hwin⟩ := hdata
  -- restrict the supply from the larger window to the one this corner named
  exact H₀ Θ ⟨CI, σI, AI, Sd, νd, hσ0, hσ1, hA, hν,
    fun M θ h1 h2 => hrem M θ (le_trans hle h1) (by linarith),
    fun θ h1 h2 => hfloor θ (le_trans hle h1) (by linarith), hwin⟩

/-- **The admissible class is inhabited, and the first-gap antecedent is
reachable.**  At `a = (1,2,3)` with `c = 1` the smallest zero is simple, so the
`ρ = 1` hypotheses hold, and `B = 1` meets `B(0) ≠ 0`.

The corner takes no separation hypothesis any more, so what this rules out is the
admissible class being empty.  It is kept because the class is what a later edit
could quietly break. -/
theorem ft_weighted_dominance_rho_one_hypotheses_nonvacuous :
    ∃ (n : ℕ) (a : Fin n → ℝ) (c : ℝ) (i : Fin n),
      3 ≤ n ∧ (∀ k, 0 < a k) ∧ 0 < c ∧ (∀ k, a i ≤ a k)
        ∧ (∀ k, k ≠ i → a k ≠ a i)
        ∧ HasRealCoeffs (1 : Polynomial ℂ) ∧ (1 : Polynomial ℂ).eval 0 ≠ 0 := by
  classical
  refine ⟨3, ![1, 2, 3], 1, 0, by norm_num, ?_, by norm_num, ?_, ?_,
    hasRealCoeffs_one, by norm_num⟩
  · intro k; fin_cases k <;> norm_num
  · intro k; fin_cases k <;> norm_num
  · intro k hk; fin_cases k <;> simp_all

/-- **The `ρ = 1` corner with nothing assumed.**  The interior supply is produced
from `InteriorBranchSeparation.ft_interior_data_on_arc_one`, whose separation is
unconditional on the admissible class at `3 ≤ n`, so what is left is the
admissible class alone.

**Why this is worth having beyond tidiness.**  An antecedent nobody has shown
meetable is a vacuity risk of exactly the kind that made an earlier version of this
corner empty, and no build-level check can distinguish "holds on a real class" from
"holds because the antecedent cannot be supplied".  Producing the antecedent is
what settles it.

**The deleted family is written out, not existentially quantified.**  An
`∃ Θ : ℕ → Set ℝ` form would be trivially true — `Θ M := univ` makes `θ ∉ Θ M`
unsatisfiable — so the windows appear as `eq:amplitude-deletion`'s own inequality,
and `S` is pinned by `1 ≤ ord_{t_+(θ_j)}(B)`. -/
theorem ft_weighted_dominance_rho_one_unconditional {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta > (0 : ℝ), ∃ L > (0 : ℝ),
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ (S : Finset ℝ) (σ : ℝ), 0 < σ ∧ σ < 1
        ∧ (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) ta) θj))
        ∧ (∀ θj ∈ S, θj ∈ Set.Ioo (0 : ℝ) π)
        ∧ (∃ K > (0 : ℝ), ∃ cdec > (0 : ℝ), ∀ M : ℕ,
            ∑ θj ∈ S, 2 * Real.exp (-((-Real.log σ) / (2 * S.card) * M
                / (B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) ta) θj))))
              ≤ K * Real.exp (-cdec * M))
        ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
          1 / M ≤ θ → θ ≤ π - 1 / M →
          (∀ θj ∈ S, Real.exp (-((-Real.log σ) / (2 * S.card) * M
              / (B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) ta) θj))))
            ≤ |θ - θj|) →
            ftRemainder (ftRootPoly c a) B 1
                (ftBranchZLowerAt a c 1 (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                (ftTauArc a 1 (n - 1) ta) M θ
              ≤ ftPrincipalAmp (ftRootPoly c a) B 1
                (ftBranchZLowerAt a c 1 (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                (ftTauArc a 1 (n - 1) ta) θ / 2 := by
  classical
  have hcast : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  obtain ⟨ta, hta, L, hL, H0⟩ := ft_weighted_dominance_rho_one hn3 ha hc hmin hsimple
  refine ⟨ta, hta, L, hL, fun B hB hB0 => ?_⟩
  have hB0' : B ≠ 0 := fun h0 => hB0 (by rw [h0]; simp)
  obtain ⟨ε, hε, H⟩ := H0 B hB hB0
  -- the two extensions agree off the endpoint, which is all the interior sees
  have hZ : ∀ θ : ℝ, 0 < θ →
      ftBranchZLowerAt a c 1 (n - 1)
        (-((ftRootPolyReal c a).eval ta) / ta ^ 1) θ = ftBranchZLower a c 1 (n - 1) θ := by
    intro θ hθ
    rw [ftBranchZLowerAt_agree a c 1 (n - 1) _ hθ, ftBranchZLower_agree a c 1 (n - 1) hθ]
  obtain ⟨CI, σI, AI, S, hσ0, hσ1, hA, hrem, hfloor, hν, hSband⟩ :
      ∃ (CI σI AI : ℝ) (S : Finset ℝ), 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
        (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ π - ε →
          |ftRemainder (ftRootPoly c a) B 1
            (ftBranchZLowerAt a c 1 (n - 1)
              (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
            (ftTauArc a 1 (n - 1) ta) M θ| ≤ CI * σI ^ M) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ π - ε →
          AI * ∏ θj ∈ S, |θ - θj|
              ^ (B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) ta) θj))
            ≤ ftPrincipalAmp (ftRootPoly c a) B 1
              (ftBranchZLowerAt a c 1 (n - 1)
                (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
              (ftTauArc a 1 (n - 1) ta) θ) ∧
        (∀ θj ∈ S, 1 ≤ B.rootMultiplicity
          (ftPrincipal (ftTauArc a 1 (n - 1) ta) θj)) ∧
        (∀ θj ∈ S, θj ∈ Set.Icc ε (π - ε)) := by
    by_cases hεb : ε ≤ π - ε
    · obtain ⟨CI, σI, AI, S, h1, h2, h3, hrem, hfloor, hν, hSb⟩ :=
        ft_interior_data_on_arc_one (x₁ := ta) (B := B) hn3 ha hc hB hB0' hε
          (by rw [hcast]; exact hεb)
      refine ⟨CI, σI, AI, S, h1, h2, h3, fun M θ hl hr => ?_, fun θ hl hr => ?_, hν,
        by simpa [hcast] using hSb⟩
      · have hθ : 0 < θ := lt_of_lt_of_le hε hl
        rw [ftRemainder, hZ θ hθ]
        exact hrem M θ hl (by rw [hcast]; exact hr)
      · have hθ : 0 < θ := lt_of_lt_of_le hε hl
        rw [ftPrincipalAmp, hZ θ hθ]
        exact hfloor θ hl (by rw [hcast]; exact hr)
    · exact ⟨1, 1 / 2, 1, ∅, by norm_num, by norm_num, by norm_num,
        fun M θ h1 h2 => absurd (le_trans h1 h2) hεb,
        fun θ h1 h2 => absurd (le_trans h1 h2) hεb, by simp, by simp⟩
  obtain ⟨M₀, hM₀⟩ :=
    H (fun M => {θ : ℝ | ∃ θj ∈ S, |θ - θj| < Real.exp (-((-Real.log σI)
        / (2 * S.card) * M
        / (B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) ta) θj))))})
      ⟨CI, σI, AI, S,
        fun θj => B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) ta) θj),
        hσ0, hσ1, hA, hν, hrem, hfloor, fun M θ hθ θj hθj => by
          by_contra hlt
          exact hθ ⟨θj, hθj, not_le.1 hlt⟩⟩
  have hSarc : ∀ θj ∈ S, θj ∈ Set.Ioo (0 : ℝ) π := by
    intro θj hθj
    have hb := hSband θj hθj
    exact ⟨lt_of_lt_of_le hε hb.1, lt_of_le_of_lt hb.2 (by linarith)⟩
  refine ⟨S, σI, hσ0, hσ1, hν, hSarc, exists_exp_decay_of_collars hσ0 hσ1 hν, M₀,
    fun M hM θ h1 h2 hfar => ?_⟩
  refine hM₀ M hM θ h1 h2 fun hmem => ?_
  obtain ⟨θj, hθj, hlt⟩ := hmem
  exact absurd (hfar θj hθj) (not_le.2 hlt)

/-- **`thm:weighted-dominance` at the branch, `ρ = 1` and `2 ≤ r`.**  The fourth
cell of the grid `subsec:proof` walks: `ρ` governs the lower endpoint and `r` the
upper, independently, so a simple smallest zero with a collapsing upper cluster is
its own case and not any of the other three with a hypothesis relaxed.

**Neither half is new.**  The lower endpoint is the `ρ = 1` group of
`RhoOneEndpointFactorization`, which was written `r`-general and is used here at
`2 ≤ r` for the first time; the upper is `EndpointUpperGap.exists_upper_endpoint_block`,
the same one `WeightedDominanceBranch` uses.  What is new is the seam, and that the
two were written against different corners.

**`n₀ = 0` and `n₁ = r - 2`.**  The lower cluster is empty — the principal pair
collides at the critical point `t_a` — while the upper carries `r - 2` members, so
unlike the `r = 1` corner the cluster threshold is real here and `h` comes off the
upper gap coefficient.  At `r = 2` exactly, `Fin (r - 2)` is `Fin 0` and the upper
binders are met by `Fin.elim0`; the content there is the pair and its circle alone,
which is why the witness below is stated at `r = 2` rather than at a typical `r`. -/
theorem ft_weighted_dominance_rho_one_two_le {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ h > (0 : ℝ), ∃ ta > (0 : ℝ),
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
          (∃ (CI σI AI : ℝ) (Sd : Finset ℝ) (νd : ℝ → ℕ),
            0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ Sd, 1 ≤ νd θj) ∧
            (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ π / r - ε →
              |ftRemainder (ftRootPoly c a) B r
                (ftBranchZLowerAt a c r (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ r))
                (ftTauArc a r (n - 1) ta) M θ| ≤ CI * σI ^ M) ∧
            (∀ θ : ℝ, ε ≤ θ → θ ≤ π / r - ε →
              AI * ∏ θj ∈ Sd, |θ - θj| ^ νd θj
                ≤ ftPrincipalAmp (ftRootPoly c a) B r
                  (ftBranchZLowerAt a c r (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ r))
                  (ftTauArc a r (n - 1) ta) θ) ∧
            (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ Sd,
              Real.exp (-((-Real.log σI) / (2 * Sd.card) * M / νd θj)) ≤ |θ - θj|)) →
          ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
            h / M ≤ θ → θ ≤ π / r - h / M → θ ∉ Θ M →
              ftRemainder (ftRootPoly c a) B r
                  (ftBranchZLowerAt a c r (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ r))
                  (ftTauArc a r (n - 1) ta) M θ
                ≤ ftPrincipalAmp (ftRootPoly c a) B r
                  (ftBranchZLowerAt a c r (n - 1)
                    (-((ftRootPolyReal c a).eval ta) / ta ^ r))
                  (ftTauArc a r (n - 1) ta) θ / 2 := by
  classical
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hb : (0 : ℝ) < π / r := div_pos Real.pi_pos hrR
  have hπ2 : (0 : ℝ) < π / r / 2 := by positivity
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  have hQre : HasRealCoeffs (ftRootPoly c a) := hasRealCoeffs_ftRootPoly c a
  -- the lower endpoint, at `ρ = 1`
  obtain ⟨ta, hlow, hup2, hlim, hE, hγd⟩ := rho_one_hgd (r := r) hn2 ha hc hr1 hmin hsimple
  have hta : 0 < ta := lt_trans (ha i) hlow
  have hne : ∀ k, a k - ta ≠ 0 := by
    intro k
    rcases eq_or_ne k i with rfl | hk
    · exact sub_ne_zero.2 (by linarith)
    · exact sub_ne_zero.2 (by linarith [hup2 k hk])
  have hQta : (ftRootPolyReal c a).eval ta ≠ 0 := by
    rw [eval_ftRootPolyReal]
    exact mul_ne_zero hc.ne' (Finset.prod_ne_zero_iff.2 fun k _ => hne k)
  set aEnd : ℝ := -((ftRootPolyReal c a).eval ta) / ta ^ r with haEnd
  have hpne : ftDen (ftRootPoly c a) r ((aEnd : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have hev : (ftDen (ftRootPoly c a) r ((aEnd : ℝ) : ℂ)).eval 0 = 0 := by
      rw [h0]; simp
    rw [ftDen_eval, zero_pow (by omega : r ≠ 0), mul_zero, add_zero] at hev
    exact hQ0 hev
  obtain ⟨R₀, hR, hRsep⟩ := exists_separating_radius hpne
    (lt_norm_of_root_endpoint_of_first_gap (i := i) hn2 hr1 hc.ne' ta hta hne hup2 hE)
  have hR0 : (0 : ℝ) < R₀ := lt_trans hta hR
  obtain ⟨e₀, he₀, hlowblk⟩ := window_of_eventually
    (eventually_lower_retained_rho_one hn2 ha hc hr1 hta hne hE hlim hR hRsep)
  have hmemarc : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioo 0 π ∧ FTBranchAt a r (n - 1) δ := by
    filter_upwards [Ioo_mem_nhdsGT hb] with δ hδ
    refine ⟨⟨hδ.1, lt_of_lt_of_le hδ.2 ?_⟩,
      ftBranchAt_of_arc_principal hn ha hr1 (Or.inl hn2) hδ⟩
    rw [div_le_iff₀ hrR]
    nlinarith [Real.pi_pos, (by exact_mod_cast hr1 : (1 : ℝ) ≤ r)]
  have hz : Tendsto (ftBranchZ a c r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 aEnd) :=
    tendsto_ftBranchZ_lower (c := c) ha hta hmemarc hlim
  have hzC : Tendsto (fun δ => ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((aEnd : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hz
  have hlimsphere : ∀ t : ℂ, ‖t‖ = R₀ →
      (ftDen (ftRootPoly c a) r ((aEnd : ℝ) : ℂ)).eval t ≠ 0 := by
    intro t ht hzero
    by_cases hteq : t = ((ta : ℝ) : ℂ)
    · rw [hteq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hta] at ht
      exact absurd ht (by linarith)
    · exact absurd ht (by have := hRsep t hzero hteq; linarith)
  -- the upper endpoint, the `2 ≤ r` block, at the same radius parameter
  obtain ⟨R₁, hR₁, sfun₁, g₁, c₁, hc₁, hgap₁, ⟨e₁b, he₁b, hupblk⟩, hratioB⟩ :=
    exists_upper_endpoint_block (x₁ := ta) hn2 ha hc hr hta
  obtain ⟨t₁, ht₁, hcl₁raw⟩ := exists_cluster_threshold (ι := Fin (r - 2)) Finset.univ
    (C_W := 2) (δ := 1 / 4) (c := c₁) (ε := 1) hc₁ zero_le_one (by norm_num) (by norm_num)
  refine ⟨t₁, ht₁, ta, hta, fun B hB hB0 => ?_⟩
  have hB0' : B ≠ 0 := fun h0 => hB0 (by rw [h0]; simp)
  obtain ⟨C₀, hC₀, ec₀, hec₀, hcbd₀⟩ :=
    exists_contour_bound_of_tendsto (B := B) hzC hR0 hlimsphere
  obtain ⟨L₁, hL₁, hratioZ⟩ := hratioB B hB0
  obtain ⟨A₁, hA₁, ea₁, hea₁, hampZ⟩ :=
    exists_upper_amplitude_floor (B := B) hn2 ha hc.ne' hr hB0
  obtain ⟨C₁, hC₁, ec₁, hec₁, hcbd₁⟩ :=
    exists_upper_contour_bound (B := B) hn ha hc hr hR₁
  -- the bridges: the extension agrees with the branch parameter off `0`
  have hZ : ∀ θ : ℝ, 0 < θ →
      ftBranchZLowerAt a c r (n - 1) aEnd θ = ftBranchZ a c r (n - 1) θ :=
    fun θ hθ => ftBranchZLowerAt_agree a c r (n - 1) aEnd hθ
  have hzarc : ∀ δ : ℝ, δ < π / r →
      ftBranchZLowerAt a c r (n - 1) aEnd (π / r - δ)
        = ftBranchZ a c r (n - 1) (π / r - δ) :=
    fun δ hδ => hZ (π / r - δ) (by linarith)
  -- the two windows
  have hE₀ : (0 : ℝ) < min e₀ ec₀ := lt_min he₀ hec₀
  have hE₀a : ∀ δ : ℝ, δ ≤ min e₀ ec₀ → δ ≤ e₀ := fun δ h => le_trans h (min_le_left _ _)
  have hE₀c : ∀ δ : ℝ, δ ≤ min e₀ ec₀ → δ ≤ ec₀ := fun δ h => le_trans h (min_le_right _ _)
  have hE₁ : (0 : ℝ) < min (min e₁b ec₁) (π / r / 2) := lt_min (lt_min he₁b hec₁) hπ2
  have hE₁a : ∀ δ : ℝ, δ ≤ min (min e₁b ec₁) (π / r / 2) → δ ≤ e₁b :=
    fun δ h => le_trans h (le_trans (min_le_left _ _) (min_le_left _ _))
  have hE₁c : ∀ δ : ℝ, δ ≤ min (min e₁b ec₁) (π / r / 2) → δ ≤ ec₁ :=
    fun δ h => le_trans h (le_trans (min_le_left _ _) (min_le_right _ _))
  have hE₁lt : ∀ δ : ℝ, δ ≤ min (min e₁b ec₁) (π / r / 2) → δ < π / r :=
    fun δ h => lt_of_le_of_lt (le_trans h (min_le_right _ _)) (by linarith)
  -- the lower factorization group
  have hbpos : (0 : ℝ) < π / r := hb
  have hγ0₀ : ftPrincipal (ftTauArc a r (n - 1) ta) 0 = ((ta : ℝ) : ℂ) := by
    rw [ftPrincipal_ftTauArc_eq_lower a r (n - 1) ta hbpos, ftPrincipal_ftTauLower_zero]
  have hγdArc : HasDerivWithinAt (fun δ : ℝ => ftPrincipal (ftTauArc a r (n - 1) ta) δ)
      (((ta : ℝ) : ℂ) * I) (Set.Ici 0) 0 := by
    refine hγd.congr_of_eventuallyEq ?_ (ftPrincipal_ftTauArc_eq_lower a r (n - 1) ta hbpos)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hbpos)] with θ hθ
    exact ftPrincipal_ftTauArc_eq_lower a r (n - 1) ta hθ
  have hk₀ : 1 ≤ (ftDen (ftRootPoly c a) r
      ((ftBranchZLowerAt a c r (n - 1) aEnd 0 : ℝ) : ℂ)).rootMultiplicity
        ((ta : ℝ) : ℂ) := by
    rw [ftBranchZLowerAt_zero, haEnd,
      rootMultiplicity_ftDen_eq_two_at_critical hn ha hc.ne' hr1 hta.ne' hne hE hQta]
    omega
  have hrootev₀ : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (ftDen (ftRootPoly c a) r
        ((ftBranchZLowerAt a c r (n - 1) aEnd δ : ℝ) : ℂ)).eval
        (ftPrincipal (ftTauArc a r (n - 1) ta) δ) = 0 :=
    eventually_of_window hE₀ fun δ hδ hδe => by
      rw [hZ δ hδ]; exact (hlowblk δ hδ (hE₀a δ hδe)).2.2.1
  have hσ₀1 : (ta + R₀) / 2 / R₀ < 1 := by rw [div_lt_one hR0]; linarith
  -- the upper group's three transferred binders
  have hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ 1 ≤ ftPrincipalAmp (ftRootPoly c a) B r
        (ftBranchZLowerAt a c r (n - 1) aEnd) (ftTauArc a r (n - 1) ta) (π / r - η) := by
    refine ⟨min ea₁ (π / r / 2), lt_min hea₁ hπ2, fun η hη hηe => ?_⟩
    have hlt : η < π / r :=
      lt_of_le_of_lt (le_trans hηe (min_le_right _ _)) (by linarith)
    simpa [ftPrincipalAmp, hzarc η hlt] using hampZ η hη (le_trans hηe (min_le_left _ _))
  have hratio₁ : ∀ j : Fin (r - 2), Filter.Tendsto
      (fun δ : ℝ => ftAmp (ftRootPoly c a) B r
          ((ftBranchZLowerAt a c r (n - 1) aEnd (π / r - δ) : ℝ) : ℂ)
          (g₁ (π / r - δ) j)
        / ftAmp (ftRootPoly c a) B r
          ((ftBranchZLowerAt a c r (n - 1) aEnd (π / r - δ) : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) ta) (π / r - δ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (L₁ j)) := by
    intro j
    refine (hratioZ j).congr' ?_
    filter_upwards [eventually_of_window hπ2
      (fun δ (_ : 0 < δ) (hδe : δ ≤ π / r / 2) => hzarc δ (by linarith))] with δ hd
    rw [hd]
  have hσ₁ : R₁ / 2 / R₁ ≤ 1 / 2 := le_of_eq (by field_simp)
  exact weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data
      (h := t₁) (b := π / r) (z := ftBranchZLowerAt a c r (n - 1) aEnd)
      (τ := ftTauArc a r (n - 1) ta)
      (sfun₀ := fun δ => {ftPrincipal (ftTauArc a r (n - 1) ta) δ,
        ((ftTauArc a r (n - 1) ta δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)})
      (sfun₁ := sfun₁) (g₀ := fun _ _ => 0) (g₁ := g₁)
      (n₀ := 0) (idx₀ := fun _ => 0) (jp₀ := 0) (νB₀ := 0)
      (cB₀ := 1) (cQ₀ := 1) (x₁ := ta) (ρ := 2)
      (te₀ := ((ta : ℝ) : ℂ)) (γe₀ := ((ta : ℝ) : ℂ) * I)
      (R₀ := R₀) (τmax₀ := (ta + R₀) / 2) (σ₀ := (ta + R₀) / 2 / R₀)
      (e₀ := min e₀ ec₀) (C₀ := C₀)
      (p₁ := 1) (A₁ := A₁) (τmax₁ := R₁ / 2) (σ₁ := 1 / 2)
      (e₁ := min (min e₁b ec₁) (π / r / 2)) (C₁ := C₁) (c₀ := 0)
      hQre hB hB0' hr1 hQ0 hta (fun h => absurd h (lt_irrefl 0))
      (by exact_mod_cast hta.ne') (by
        simpa using mul_ne_zero (by exact_mod_cast hta.ne' : ((ta : ℝ) : ℂ) ≠ 0)
          Complex.I_ne_zero)
      hγ0₀ hγdArc hk₀ hrootev₀
      (fun h => absurd h (lt_irrefl 0)) (fun h => absurd h (lt_irrefl 0))
      (fun j => j.elim0) (fun h => absurd h (lt_irrefl 0))
      (fun j => j.elim0) (fun h => absurd h (lt_irrefl 0))
      hR0 le_rfl hσ₀1 hE₀
      (fun δ hδ hδe => (hlowblk δ hδ (hE₀a δ hδe)).1)
      (fun δ hδ hδe => (hlowblk δ hδ (hE₀a δ hδe)).2.1)
      (fun δ hδ hδe t ht => by
        rw [hZ δ hδ]; exact ((hlowblk δ hδ (hE₀a δ hδe)).2.2.2.2.1 t ht).1)
      (fun δ hδ hδe t ht => by
        rw [hZ δ hδ]; exact ((hlowblk δ hδ (hE₀a δ hδe)).2.2.2.2.1 t ht).2.2)
      (fun δ hδ hδe t ht => ((hlowblk δ hδ (hE₀a δ hδe)).2.2.2.2.1 t ht).2.1)
      (fun δ hδ hδe t ht h0 => (hlowblk δ hδ (hE₀a δ hδe)).2.2.2.2.2 t ht
        (by rwa [hZ δ hδ] at h0))
      (fun δ hδ hδe => by rw [hZ δ hδ]; exact (hlowblk δ hδ (hE₀a δ hδe)).2.2.1)
      (fun δ hδ hδe => (hlowblk δ hδ (hE₀a δ hδe)).2.2.2.1)
      (fun δ _ _ => Function.injective_of_subsingleton _)
      (fun δ _ _ j => j.elim0)
      (fun δ hδ hδe => by
        rw [Finset.erase_insert (by simpa using (hlowblk δ hδ (hE₀a δ hδe)).2.2.2.1),
          Finset.erase_singleton, Finset.card_empty])
      hC₀ (fun δ hδ hδe t ht => by
        rw [hZ δ hδ]; exact (hcbd₀ δ hδ (hE₀c δ hδe) t ht).2)
      hA₁ hamp₁ hL₁ hratio₁ hR₁ hσ₁ (by norm_num) hE₁
      (fun δ hδ hδe => (hupblk δ hδ (hE₁a δ hδe)).1)
      (fun δ hδ hδe => (hupblk δ hδ (hE₁a δ hδe)).2.1)
      (fun δ hδ hδe t ht => by
        rw [hzarc δ (hE₁lt δ hδe)]; exact (hupblk δ hδ (hE₁a δ hδe)).2.2.1 t ht)
      (fun δ hδ hδe t ht => by
        rw [hzarc δ (hE₁lt δ hδe)]; exact (hupblk δ hδ (hE₁a δ hδe)).2.2.2.1 t ht)
      (fun δ hδ hδe => (hupblk δ hδ (hE₁a δ hδe)).2.2.2.2.1)
      (fun δ hδ hδe t ht h0 => (hupblk δ hδ (hE₁a δ hδe)).2.2.2.2.2.1 t ht
        (by rwa [hzarc δ (hE₁lt δ hδe)] at h0))
      (fun δ hδ hδe => by
        rw [hzarc δ (hE₁lt δ hδe)]; exact (hupblk δ hδ (hE₁a δ hδe)).2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hupblk δ hδ (hE₁a δ hδe)).2.2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hupblk δ hδ (hE₁a δ hδe)).2.2.2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hupblk δ hδ (hE₁a δ hδe)).2.2.2.2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hupblk δ hδ (hE₁a δ hδe)).2.2.2.2.2.2.2.2.2.2)
      hC₁ (fun δ hδ hδe t ht => by
        rw [hzarc δ (hE₁lt δ hδe)]; exact hcbd₁ δ hδ (hE₁c δ hδe) t ht)
      ht₁ ⟨1, one_pos, fun δ _ _ j => j.elim0⟩ hgap₁
      ⟨1, one_pos, fun A ζ' θ W _ _ hW _ _ M _ => by simpa using by linarith⟩
      ⟨1, one_pos, fun A ζ' η W hη hηe hW hA hg M hM =>
        hcl₁raw A ζ' η W hη hηe hW hA hg M hM⟩


/-- **The `ρ = 1`, `2 ≤ r` class is inhabited on both sides of the `r = 2`
boundary.**  At `a = (1,2,3)` the smallest zero is simple, so `ρ = 1`; the first
component takes `r = 3`, where `n₁ = r - 2 = 1` and the upper cluster's binders
carry content, and the second takes `r = 2`, where `n₁ = 0` and they are met by
`Fin.elim0`.

**Both are needed and the second is the one that is easy to forget.**  At `r = 2`
a statement about the upper cluster is satisfied by having no cluster, so a witness
only at `r = 2` would not exercise the binders and a witness only at `r ≥ 3` would
not exercise the boundary.  `B = 1` meets the numerator condition in either. -/
theorem ft_weighted_dominance_rho_one_two_le_hypotheses_nonvacuous :
    (∃ (n r : ℕ) (a : Fin n → ℝ) (c : ℝ) (i : Fin n),
        2 ≤ n ∧ (∀ k, 0 < a k) ∧ 0 < c ∧ 2 ≤ r ∧ (∀ k, a i ≤ a k)
          ∧ (∀ k, k ≠ i → a k ≠ a i) ∧ 0 < r - 2)
      ∧ (∃ (n r : ℕ) (a : Fin n → ℝ) (c : ℝ) (i : Fin n),
        2 ≤ n ∧ (∀ k, 0 < a k) ∧ 0 < c ∧ 2 ≤ r ∧ (∀ k, a i ≤ a k)
          ∧ (∀ k, k ≠ i → a k ≠ a i) ∧ r - 2 = 0)
      ∧ HasRealCoeffs (1 : Polynomial ℂ) ∧ (1 : Polynomial ℂ).eval 0 ≠ 0 := by
  classical
  refine ⟨⟨3, 3, ![1, 2, 3], 1, 0, by norm_num, ?_, by norm_num, by norm_num, ?_, ?_,
      by norm_num⟩,
    ⟨3, 2, ![1, 2, 3], 1, 0, by norm_num, ?_, by norm_num, by norm_num, ?_, ?_,
      by norm_num⟩,
    hasRealCoeffs_one, by norm_num⟩ <;>
    [skip; skip; skip; skip; skip; skip]
  · intro k; fin_cases k <;> norm_num
  · intro k; fin_cases k <;> norm_num
  · intro k hk; fin_cases k <;> simp_all
  · intro k; fin_cases k <;> norm_num
  · intro k; fin_cases k <;> norm_num
  · intro k hk; fin_cases k <;> simp_all

/-- **The `ρ = 1`, `2 ≤ r` corner with nothing assumed.**  The interior supply is
produced by `InteriorBranchSeparation.ft_interior_data_on_arc_two_le`, which
carries **no `ρ` hypothesis at all** and so applies at a simple smallest zero
exactly as it does at a repeated one.

`x₁` is that theorem's free implicit, and what is passed here is the `ta` this
corner's own lower group produced — not a separately derived point that happens to
agree with it.  Two terms agreeing numerically at one configuration is the failure
that type-checks on both sides.

**The deleted family is written out, not existentially quantified**: an
`∃ Θ : ℕ → Set ℝ` form is trivially true at `Θ M := univ`, so the windows appear as
`eq:amplitude-deletion`'s own inequality and `S` is pinned by
`1 ≤ ord_{t_+(θ_j)}(B)`. -/
theorem ft_weighted_dominance_rho_one_two_le_unconditional {n r : ℕ} {a : Fin n → ℝ}
    {c : ℝ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ h > (0 : ℝ), ∃ ta > (0 : ℝ),
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ (S : Finset ℝ) (σ : ℝ), 0 < σ ∧ σ < 1
        ∧ (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) ta) θj))
        ∧ (∃ K > (0 : ℝ), ∃ cdec > (0 : ℝ), ∀ M : ℕ,
            ∑ θj ∈ S, 2 * Real.exp (-((-Real.log σ) / (2 * S.card) * M
                / (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) ta) θj))))
              ≤ K * Real.exp (-cdec * M))
        ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
          h / M ≤ θ → θ ≤ π / r - h / M →
          (∀ θj ∈ S, Real.exp (-((-Real.log σ) / (2 * S.card) * M
              / (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) ta) θj))))
            ≤ |θ - θj|) →
            ftRemainder (ftRootPoly c a) B r
                (ftBranchZLowerAt a c r (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ r))
                (ftTauArc a r (n - 1) ta) M θ
              ≤ ftPrincipalAmp (ftRootPoly c a) B r
                (ftBranchZLowerAt a c r (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ r))
                (ftTauArc a r (n - 1) ta) θ / 2 := by
  classical
  obtain ⟨h, hh, ta, hta, H0⟩ :=
    ft_weighted_dominance_rho_one_two_le hn2 ha hc hr hmin hsimple
  refine ⟨h, hh, ta, hta, fun B hB hB0 => ?_⟩
  have hB0' : B ≠ 0 := fun h0 => hB0 (by rw [h0]; simp)
  obtain ⟨ε, hε, H⟩ := H0 B hB hB0
  -- the two extensions agree off the endpoint, which is all the interior sees
  have hZ : ∀ θ : ℝ, 0 < θ →
      ftBranchZLowerAt a c r (n - 1)
        (-((ftRootPolyReal c a).eval ta) / ta ^ r) θ
        = ftBranchZLower a c r (n - 1) θ := by
    intro θ hθ
    rw [ftBranchZLowerAt_agree a c r (n - 1) _ hθ, ftBranchZLower_agree a c r (n - 1) hθ]
  obtain ⟨CI, σI, AI, S, hσ0, hσ1, hA, hrem, hfloor, hν⟩ :
      ∃ (CI σI AI : ℝ) (S : Finset ℝ), 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
        (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ π / r - ε →
          |ftRemainder (ftRootPoly c a) B r
            (ftBranchZLowerAt a c r (n - 1)
              (-((ftRootPolyReal c a).eval ta) / ta ^ r))
            (ftTauArc a r (n - 1) ta) M θ| ≤ CI * σI ^ M) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ π / r - ε →
          AI * ∏ θj ∈ S, |θ - θj|
              ^ (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) ta) θj))
            ≤ ftPrincipalAmp (ftRootPoly c a) B r
              (ftBranchZLowerAt a c r (n - 1)
                (-((ftRootPolyReal c a).eval ta) / ta ^ r))
              (ftTauArc a r (n - 1) ta) θ) ∧
        (∀ θj ∈ S, 1 ≤ B.rootMultiplicity
          (ftPrincipal (ftTauArc a r (n - 1) ta) θj)) := by
    by_cases hεb : ε ≤ π / r - ε
    · obtain ⟨CI, σI, AI, S, h1, h2, h3, hrem, hfloor, hν⟩ :=
        ft_interior_data_on_arc_two_le (x₁ := ta) (B := B) hn2 ha hc hr hB hB0' hε hεb
      refine ⟨CI, σI, AI, S, h1, h2, h3, fun M θ hl hrr => ?_, fun θ hl hrr => ?_, hν.1⟩
      · have hθ : 0 < θ := lt_of_lt_of_le hε hl
        rw [ftRemainder, hZ θ hθ]
        exact hrem M θ hl hrr
      · have hθ : 0 < θ := lt_of_lt_of_le hε hl
        rw [ftPrincipalAmp, hZ θ hθ]
        exact hfloor θ hl hrr
    · exact ⟨1, 1 / 2, 1, ∅, by norm_num, by norm_num, by norm_num,
        fun M θ h1 h2 => absurd (le_trans h1 h2) hεb,
        fun θ h1 h2 => absurd (le_trans h1 h2) hεb, by simp⟩
  obtain ⟨M₀, hM₀⟩ :=
    H (fun M => {θ : ℝ | ∃ θj ∈ S, |θ - θj| < Real.exp (-((-Real.log σI)
        / (2 * S.card) * M
        / (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) ta) θj))))})
      ⟨CI, σI, AI, S,
        fun θj => B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) ta) θj),
        hσ0, hσ1, hA, hν, hrem, hfloor, fun M θ hθ θj hθj => by
          by_contra hlt
          exact hθ ⟨θj, hθj, not_le.1 hlt⟩⟩
  refine ⟨S, σI, hσ0, hσ1, hν, exists_exp_decay_of_collars hσ0 hσ1 hν, M₀,
    fun M hM θ h1 h2 hfar => ?_⟩
  refine hM₀ M hM θ h1 h2 fun hmem => ?_
  obtain ⟨θj, hθj, hlt⟩ := hmem
  exact absurd (hfar θj hθj) (not_le.2 hlt)

end ForgacsTran
