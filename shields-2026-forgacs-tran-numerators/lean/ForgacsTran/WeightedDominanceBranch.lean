/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointLowerBlock
import ForgacsTran.EndpointUpperGap

/-!
# `thm:weighted-dominance` at the Forgács–Tran branch

`DominanceFT.weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data`
states the weighted dominance bound against fifty binders describing an abstract branch,
its two endpoint clusters and the two thresholds.  This module discharges every
one of them at the branch itself, so what is left is the admissible class: `Q` a
polynomial with positive zeros, `2 ≤ r`, the smallest zero carried with
multiplicity `ρ ≥ 2`, and a numerator with `B(0) ≠ 0`.

The two endpoints are supplied by `exists_lower_endpoint_block` and
`exists_upper_endpoint_block`, each against one cluster and one window, and the
object bridge is the pair `τ = ftTauArc`, `z = ftBranchZLower` of
`EndpointUpperPackage`: the arc radius, because only it vanishes at the upper
endpoint, and the lower spectral parameter, because only it takes the value `0`
at `θ = 0` that `hk₀`'s multiplicity clause is stated against.

`2 ≤ r` and `2 ≤ ρ` are the sides of `eq:ab-def`'s dichotomy the two endpoint
analyses live on, not restrictions added here.  At `r = 1` the upper cluster's
separating radius does not exist — the conjugate is a second root at the same
modulus — and at `ρ = 1` the smallest zero is simple and
`SimpleWitness` is the route.  Both counts may still be zero: `ρ = 2` gives
`n_0 = 0` and `r = 2` gives `n_1 = 0`, which is the manuscript's "the cluster is
the principal pair alone" at either end.

**The threshold `h` is produced here, and it is quantified ahead of the
numerator.**  The paper states `h = h(Q,r)` before "for every fixed `B`", and the
statement has to say so: `h` comes from `Dominance.exists_cluster_threshold` at
the two gap coefficients and the two cluster sizes `ρ - 2`, `r - 2`, none of
which names `B`.  Both endpoint blocks quantify the numerator inside their own
existential for exactly this reason, so the geometry is fixed before `B` is seen.
`h` also sits ahead of the interior supply, which is the same fact one step
further out.

**The interior supply is taken in its data form, and from `r = 3` that choice is
forced.**  The alternative packaging asks for one separating circle across the
whole compact interior; `thm:FT-geometry` gives a pointwise modulus ratio, and
whether the two agree is decided by `n_1 = r - 2` — the count of non-principal
members of the cluster that collapses into the origin at the upper endpoint.  At
`r = 2` that count is zero and a global circle exists; from `r = 3` a
non-principal member collapses with `τ`, `inf third → 0` at the upper end while
`sup τ` stays `O(1)` at the lower one, and the fixed-circle antecedent is not
merely unproved but false.  The data form is what the dominance proof actually
consumes, it is meetable at every `r`, and its constants reassemble over a finite
cover.

## Main statements

* `ft_weighted_dominance` — `thm:weighted-dominance` at the branch, with the
  interior supply of `subsec:proof`, in data form, as its only remaining
  antecedent.
* `ft_weighted_dominance_fixed_circle` — the same against the fixed-circle block,
  derived from it; usable at `r = 2` and vacuous from `r = 3`.
* `ft_weighted_dominance_hypotheses_nonvacuous` — the hypothesis class inhabited
  with both retained clusters nonempty.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:dominance-bound`, `eq:retained-range`, `subsec:proof`.

## Tags

weighted dominance, principal pair, endpoint cluster, Forgács–Tran branch
-/

namespace ForgacsTran

open Polynomial Complex
open scoped Topology

/-- **`thm:weighted-dominance` at the Forgács–Tran branch.**  Every binder of
`weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data`
discharged at `Q = ftRootPoly c a`, `z = ftBranchZLower`, `τ = ftTauArc` and
`b = π/r`, so the only hypotheses left are the admissible class and `B(0) ≠ 0`.

What stays an antecedent is the interior supply of `subsec:proof`, in the **data**
form: the remainder bound, the amplitude floor over a divisor, and the
deleted-window clause.  That is the form a caller can meet at `2 ≤ r`, because its
constants reassemble over a finite cover
(`InteriorSeparation.exists_finite_separation_cover` and `interior_data_of_pieces`)
and the geometry supplies one separating radius per piece.  The fixed-circle form
does not: see `ft_weighted_dominance_fixed_circle` below and
`check_interior_fixed_radius_higher_r.py`. -/
theorem ft_weighted_dominance {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ h > (0 : ℝ), ∀ (B : Polynomial ℂ), HasRealCoeffs B → B.eval 0 ≠ 0 →
      ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
        (∃ (CI σI AI : ℝ) (Sd : Finset ℝ) (νd : ℝ → ℕ),
          0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ Sd, 1 ≤ νd θj) ∧
          (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ Real.pi / r - ε →
            |ftRemainder (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
              (ftTauArc a r (n - 1) x₁) M θ| ≤ CI * σI ^ M) ∧
          (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε →
            AI * ∏ θj ∈ Sd, |θ - θj| ^ νd θj
              ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
                (ftTauArc a r (n - 1) x₁) θ) ∧
          (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ Sd,
            Real.exp (-((-Real.log σI) / (2 * Sd.card) * M / νd θj)) ≤ |θ - θj|)) →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
          h / M ≤ θ → θ ≤ Real.pi / r - h / M → θ ∉ Θ M →
            ftRemainder (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
                (ftTauArc a r (n - 1) x₁) M θ
              ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
                (ftTauArc a r (n - 1) x₁) θ / 2 := by
  classical
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hb : 0 < Real.pi / r := div_pos Real.pi_pos hrR
  have hπ2 : (0 : ℝ) < Real.pi / r / 2 := by positivity
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  have hQre : HasRealCoeffs (ftRootPoly c a) := hasRealCoeffs_ftRootPoly c a
  have hR₀pos : 0 < ftSepRadius a x₁ := ftSepRadius_pos hx₁ hmin
  -- the endpoint factorization and the two cluster blocks, all of it before the
  -- numerator: the gap coefficients are cluster geometry and name no `B`
  obtain ⟨-, hte₀, hγe₀, -, -, hk₀, -⟩ :=
    endpoint_package_of_two_le_rho (c := c) hn ha hc hr1 hnr hx₁ hmin hcard hρ
  obtain ⟨sfun₀, g₀, idx₀, c₀, hc₀, hgap₀, ⟨e₀b, he₀b, hlow⟩, hresid⟩ :=
    exists_lower_endpoint_block hn2 ha hc hr1 (fun h => by omega) hx₁ hmin hcard hρ
  obtain ⟨R₁, hR₁, sfun₁, g₁, c₁, hc₁, hgap₁, ⟨e₁b, he₁b, hup⟩, hratioB⟩ :=
    exists_upper_endpoint_block hn2 ha hc hr hx₁
  -- `h` is fixed here, from the two gap coefficients and the two cluster sizes
  obtain ⟨t₀, ht₀, hcl₀raw⟩ := exists_cluster_threshold (ι := Fin (ρ - 2)) Finset.univ
    (C_W := 2) (δ := 1 / 4) (c := c₀) (ε := 1) hc₀ zero_le_one (by norm_num) (by norm_num)
  obtain ⟨t₁, ht₁, hcl₁raw⟩ := exists_cluster_threshold (ι := Fin (r - 2)) Finset.univ
    (C_W := 2) (δ := 1 / 4) (c := c₁) (ε := 1) hc₁ zero_le_one (by norm_num) (by norm_num)
  have hthrpos : 0 < max t₀ t₁ := lt_of_lt_of_le ht₀ (le_max_left _ _)
  refine ⟨max t₀ t₁, hthrpos, fun B hB hB0 => ?_⟩
  have hB0' : B ≠ 0 := fun h0 => hB0 (by rw [h0]; simp)
  obtain ⟨cB₀, cQ₀, hcB₀, hcQ₀, hBj₀, hBp₀, hEj₀, hEp₀⟩ := hresid B hB0'
  obtain ⟨L₁, hL₁, hratioZ⟩ := hratioB B hB0
  obtain ⟨C₀, hC₀, ec₀, hec₀, hcbd₀⟩ :=
    exists_endpoint_contour_window_of_two_le_rho hn ha hc hr1 hnr hx₁ hmin hcard hρ B
  obtain ⟨A₁, hA₁, ea₁, hea₁, hampZ⟩ :=
    exists_upper_amplitude_floor (B := B) hn2 ha hc.ne' hr hB0
  obtain ⟨C₁, hC₁, ec₁, hec₁, hcbd₁⟩ := exists_upper_contour_bound (B := B) hn ha hc hr hR₁
  -- the two windows, each the intersection of its block's and its contour bound's
  have hE₀ : (0 : ℝ) < min e₀b ec₀ := lt_min he₀b hec₀
  have hE₀a : ∀ δ : ℝ, δ ≤ min e₀b ec₀ → δ ≤ e₀b := fun δ h => le_trans h (min_le_left _ _)
  have hE₀c : ∀ δ : ℝ, δ ≤ min e₀b ec₀ → δ ≤ ec₀ := fun δ h => le_trans h (min_le_right _ _)
  have hE₁ : (0 : ℝ) < min (min e₁b ec₁) (Real.pi / r / 2) := lt_min (lt_min he₁b hec₁) hπ2
  have hE₁a : ∀ δ : ℝ, δ ≤ min (min e₁b ec₁) (Real.pi / r / 2) → δ ≤ e₁b :=
    fun δ h => le_trans h (le_trans (min_le_left _ _) (min_le_left _ _))
  have hE₁c : ∀ δ : ℝ, δ ≤ min (min e₁b ec₁) (Real.pi / r / 2) → δ ≤ ec₁ :=
    fun δ h => le_trans h (le_trans (min_le_left _ _) (min_le_right _ _))
  have hE₁lt : ∀ δ : ℝ, δ ≤ min (min e₁b ec₁) (Real.pi / r / 2) → δ < Real.pi / r :=
    fun δ h => lt_of_le_of_lt (le_trans h (min_le_right _ _)) (by linarith)
  -- the object bridge: the two spectral parameters agree at the upper endpoint's angles
  have hzarc : ∀ δ : ℝ, δ < Real.pi / r →
      ftBranchZLower a c r (n - 1) (Real.pi / r - δ)
        = ftBranchZ a c r (n - 1) (Real.pi / r - δ) :=
    fun δ hδ => ftBranchZLower_arc_end_agree a c (n - 1) hr1 hδ
  -- the lower endpoint's remaining three binders
  have hγ0₀ : ftPrincipal (ftTauArc a r (n - 1) x₁) 0 = ((x₁ : ℝ) : ℂ) := by
    rw [ftPrincipal_ftTauArc_eq_lower a r (n - 1) x₁ hb, ftPrincipal_ftTauLower_zero]
  have hγd₀ := hasDerivWithinAt_ftPrincipal_ftTauArc_lower hn ha hr1 hnr hx₁ hmin
    hcard hρ
  have hrootev₀ : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval
        (ftPrincipal (ftTauArc a r (n - 1) x₁) δ) = 0 :=
    eventually_of_window hE₀ fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.2.2.2.2.1
  have hσ₀1 : x₁ / ftSepRadius a x₁ < 1 := (div_lt_one hR₀pos).2 (lt_ftSepRadius hmin)
  -- the upper endpoint's binders, transferred to the shared spectral parameter
  have hR₁ne : R₁ ≠ 0 := hR₁.ne'
  have hσ₁ : R₁ / 2 / R₁ ≤ 1 / 2 := le_of_eq (by field_simp)
  have hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ 1 ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
        (ftTauArc a r (n - 1) x₁) (Real.pi / r - η) := by
    refine ⟨min ea₁ (Real.pi / r / 2), lt_min hea₁ hπ2, fun η hη hηe => ?_⟩
    have hlt : η < Real.pi / r :=
      lt_of_le_of_lt (le_trans hηe (min_le_right _ _)) (by linarith)
    simpa [ftPrincipalAmp, hzarc η hlt] using hampZ η hη (le_trans hηe (min_le_left _ _))
  have hratio₁ : ∀ i : Fin (r - 2), Filter.Tendsto
      (fun δ : ℝ => ftAmp (ftRootPoly c a) B r
          ((ftBranchZLower a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ) (g₁ (Real.pi / r - δ) i)
        / ftAmp (ftRootPoly c a) B r
          ((ftBranchZLower a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (L₁ i)) := by
    intro i
    refine (hratioZ i).congr' ?_
    filter_upwards [eventually_of_window hπ2
      (fun δ (_ : 0 < δ) (hδe : δ ≤ Real.pi / r / 2) => hzarc δ (by linarith))] with δ hd
    rw [hd]
  have hroot₁ : ∀ δ : ℝ, 0 < δ → δ ≤ min (min e₁b ec₁) (Real.pi / r / 2) →
      ∀ t ∈ sfun₁ δ, (ftDen (ftRootPoly c a) r
        ((ftBranchZLower a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t = 0 := by
    intro δ hδ hδe t ht
    rw [hzarc δ (hE₁lt δ hδe)]
    exact (hup δ hδ (hE₁a δ hδe)).2.2.1 t ht
  have hsimple₁ : ∀ δ : ℝ, 0 < δ → δ ≤ min (min e₁b ec₁) (Real.pi / r / 2) →
      ∀ t ∈ sfun₁ δ, (derivative (ftDen (ftRootPoly c a) r
        ((ftBranchZLower a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ))).eval t ≠ 0 := by
    intro δ hδ hδe t ht
    rw [hzarc δ (hE₁lt δ hδe)]
    exact (hup δ hδ (hE₁a δ hδe)).2.2.2.1 t ht
  have huniq₁ : ∀ δ : ℝ, 0 < δ → δ ≤ min (min e₁b ec₁) (Real.pi / r / 2) →
      ∀ t : ℂ, ‖t‖ ≤ R₁ → (ftDen (ftRootPoly c a) r
        ((ftBranchZLower a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t = 0 →
        t ∈ sfun₁ δ := by
    intro δ hδ hδe t ht hev
    rw [hzarc δ (hE₁lt δ hδe)] at hev
    exact (hup δ hδ (hE₁a δ hδe)).2.2.2.2.2.1 t ht hev
  have hrootplus₁ : ∀ δ : ℝ, 0 < δ → δ ≤ min (min e₁b ec₁) (Real.pi / r / 2) →
      (ftDen (ftRootPoly c a) r
        ((ftBranchZLower a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval
        (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)) = 0 := by
    intro δ hδ hδe
    rw [hzarc δ (hE₁lt δ hδe)]
    exact (hup δ hδ (hE₁a δ hδe)).2.2.2.2.2.2.1
  have hCbd₁ : ∀ δ : ℝ, 0 < δ → δ ≤ min (min e₁b ec₁) (Real.pi / r / 2) →
      ∀ t ∈ Metric.sphere (0 : ℂ) R₁, ‖B.eval t / (ftDen (ftRootPoly c a) r
        ((ftBranchZLower a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁ := by
    intro δ hδ hδe t ht
    rw [hzarc δ (hE₁lt δ hδe)]
    exact hcbd₁ δ hδ (hE₁c δ hδe) t ht
  have hclu₀ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin (ρ - 2) → ℝ) (θ W : ℝ), 0 < θ → θ ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin (ρ - 2))), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin (ρ - 2))), 1 + c₀ * θ ≤ ζ' i) →
        ∀ M : ℕ, max t₀ t₁ ≤ (M : ℝ) * θ →
          ∑ i ∈ (Finset.univ : Finset (Fin (ρ - 2))), |A i| * (ζ' i ^ (M + 1))⁻¹
            ≤ 1 / 4 * W :=
    ⟨1, one_pos, fun A ζ' θ W hθ hθe hW hA hg M hM =>
      hcl₀raw A ζ' θ W hθ hθe hW hA hg M (le_trans (le_max_left _ _) hM)⟩
  have hclu₁ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin (r - 2) → ℝ) (η W : ℝ), 0 < η → η ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin (r - 2))), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin (r - 2))), 1 + c₁ * η ≤ ζ' i) →
        ∀ M : ℕ, max t₀ t₁ ≤ (M : ℝ) * η →
          ∑ i ∈ (Finset.univ : Finset (Fin (r - 2))), |A i| * (ζ' i ^ (M + 1))⁻¹
            ≤ 1 / 4 * W :=
    ⟨1, one_pos, fun A ζ' η W hη hηe hW hA hg M hM =>
      hcl₁raw A ζ' η W hη hηe hW hA hg M (le_trans (le_max_right _ _) hM)⟩
  exact weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data
      (h := max t₀ t₁)
      (b := Real.pi / r) (z := ftBranchZLower a c r (n - 1))
      (τ := ftTauArc a r (n - 1) x₁) (sfun₀ := sfun₀) (sfun₁ := sfun₁)
      (g₀ := g₀) (g₁ := g₁) (idx₀ := idx₀) (jp₀ := 0)
      (νB₀ := B.rootMultiplicity ((x₁ : ℝ) : ℂ)) (p₁ := 1)
      hQre hB hB0' hr1 hQ0 hx₁ (fun _ => hρ) hte₀ hγe₀ hγ0₀ hγd₀ hk₀ hrootev₀
      (fun _ => hcB₀) (fun _ => hcQ₀) hBj₀ (fun _ => hBp₀) hEj₀ (fun _ => hEp₀)
      hR₀pos (le_refl _) hσ₀1 hE₀
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).1)
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.1)
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.1)
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.2.1)
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.2.2.1)
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.2.2.2.1)
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.2.2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.2.2.2.2.2.2.2.2)
      hC₀ (fun δ hδ hδe => (hcbd₀ δ hδ (hE₀c δ hδe)).1)
      hA₁ hamp₁ hL₁ hratio₁ hR₁ hσ₁ (by norm_num) hE₁
      (fun δ hδ hδe => (hup δ hδ (hE₁a δ hδe)).1)
      (fun δ hδ hδe => (hup δ hδ (hE₁a δ hδe)).2.1)
      hroot₁ hsimple₁
      (fun δ hδ hδe => (hup δ hδ (hE₁a δ hδe)).2.2.2.2.1)
      huniq₁ hrootplus₁
      (fun δ hδ hδe => (hup δ hδ (hE₁a δ hδe)).2.2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hup δ hδ (hE₁a δ hδe)).2.2.2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hup δ hδ (hE₁a δ hδe)).2.2.2.2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hup δ hδ (hE₁a δ hδe)).2.2.2.2.2.2.2.2.2.2)
      hC₁ hCbd₁ hthrpos hgap₀ hgap₁ hclu₀ hclu₁

/-- **The same at the branch, against the fixed-circle interior block.**  Derived
from the data form through `hdata_entry_of_interior`, which is the honest
relationship: the block is *sufficient* for the interior input, never necessary.

**Its antecedent splits on `r`, and the boundary is the theorem's own `n_1`.**
The block needs one separating radius for the whole compact interior,
`sup τ < R_0 < inf(third modulus)`.  At `r = 2`, `n_1 = r - 2 = 0`: the principal
pair is the entire cluster that collapses into the origin at the upper endpoint,
the third modulus stays `O(1)`, and `sup τ` and `inf third` are attained at the
same angle — a global radius exists, and this form is the usable one there, with
no cover needed.  From `r = 3` a non-principal member collapses with `τ`, so
`inf third → 0` at the upper end while `sup τ` sits at the lower one and **the
antecedent is false**, leaving this statement without content at those `r`.

`check_interior_fixed_radius_higher_r.py` asserts that split over pencils with the
smallest zero repeated, at four interior parameters each: `inf third / sup τ`
above `1` in every `r = 2` row and below `1` in every `r ≥ 3` row, while the
pointwise ratio of `thm:FT-geometry` holds in all of them.  For `r ≥ 3` use
`ft_weighted_dominance`. -/
theorem ft_weighted_dominance_fixed_circle {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ h > (0 : ℝ), ∀ (B : Polynomial ℂ), HasRealCoeffs B → B.eval 0 ≠ 0 →
      ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
        (∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
        0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε → 0 < ftTauArc a r (n - 1) x₁ θ) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε → ftTauArc a r (n - 1) x₁ θ ≤ τmi) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε → ftTauArc a r (n - 1) x₁ θ < Ri) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε →
          (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)).eval
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) = 0) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε →
          (derivative (ftDen (ftRootPoly c a) r
            ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ))).eval
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) ≠ 0) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε →
          (derivative (ftDen (ftRootPoly c a) r
            ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ))).eval
            (((ftTauArc a r (n - 1) x₁ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε →
          ftPrincipal (ftTauArc a r (n - 1) x₁) θ
            ≠ ((ftTauArc a r (n - 1) x₁ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε → ∀ t : ℂ, ‖t‖ ≤ Ri →
          (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)).eval t = 0 →
          t = ftPrincipal (ftTauArc a r (n - 1) x₁) θ
            ∨ t = ((ftTauArc a r (n - 1) x₁ θ : ℝ) : ℂ)
              * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (↑S ⊆ Set.Icc ε (Real.pi / r - ε)) ∧
        (∀ θj ∈ S, ftAmp (ftRootPoly c a) B r
          ((ftBranchZLower a c r (n - 1) θj : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) x₁) θj) = 0) ∧
        (∀ θ ∈ Set.Icc ε (Real.pi / r - ε),
          ftAmp (ftRootPoly c a) B r ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) = 0 → θ ∈ S) ∧
        (∀ θ ∈ Set.Icc ε (Real.pi / r - ε), ∃ γ' : ℂ, γ' ≠ 0
          ∧ HasDerivAt (ftPrincipal (ftTauArc a r (n - 1) x₁)) γ' θ) ∧
        (∀ θ ∈ Set.Icc ε (Real.pi / r - ε),
          ContinuousAt (fun θ' => ((ftBranchZLower a c r (n - 1) θ' : ℝ) : ℂ)) θ) ∧
        (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
          Real.exp (-((-Real.log σi) / (2 * S.card) * M
            / (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj)))) ≤ |θ - θj|)) →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
          h / M ≤ θ → θ ≤ Real.pi / r - h / M → θ ∉ Θ M →
            ftRemainder (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
                (ftTauArc a r (n - 1) x₁) M θ
              ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
                (ftTauArc a r (n - 1) x₁) θ / 2 := by
  classical
  have hr1 : 1 ≤ r := by omega
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  have hQre : HasRealCoeffs (ftRootPoly c a) := hasRealCoeffs_ftRootPoly c a
  obtain ⟨h, hh, H0⟩ := ft_weighted_dominance hn2 ha hc hr hx₁ hmin hcard hρ
  refine ⟨h, hh, fun B hB hB0 => ?_⟩
  have hB0' : B ≠ 0 := fun h0 => hB0 (by rw [h0]; simp)
  obtain ⟨ε, hε, H⟩ := H0 B hB hB0
  refine ⟨ε, hε, fun Θ hinterior => ?_⟩
  obtain ⟨Ri, τmi, σi, S, hRi, hσi, hσi0, hσi1, hτposI, hτleI,
    hτRI, hrpI, hspI, hsmI, hneeI, hpairI, hSsubI, hSzeroI, hzerosI, hγdI, hzcI,
    hwinI⟩ := hinterior
  exact H Θ (hdata_entry_of_interior hQre hB hr1 hQ0 hB0' hRi hσi hσi0 hσi1 hτposI
    hτleI hτRI hrpI hspI hsmI hneeI hpairI hSsubI hSzeroI hzerosI hγdI hzcI hwinI)

/-- **The hypothesis set of `ft_weighted_dominance` is inhabited, and not at the
degenerate corner.**  At `Q = (1 - t)^3` with `r = 3` — the joint pencil of
`JointWitness` — the smallest zero carries multiplicity `ρ = 3` and the branch
exponent is `3`, so both retained clusters have one member: `n_0 = ρ - 2 = 1` and
`n_1 = r - 2 = 1`.

Both counts matter.  `ρ = 2` and `r = 2` also satisfy every hypothesis, but there
the two binder families are `Fin 0` and are met by `Fin.elim0` without testing
anything; the last two conjuncts are what say this instance is not that one. -/
theorem ft_weighted_dominance_hypotheses_nonvacuous :
    ∃ (n r ρ : ℕ) (a : Fin n → ℝ) (c x₁ : ℝ) (B : Polynomial ℂ),
      2 ≤ n ∧ (∀ k, 0 < a k) ∧ 0 < c ∧ 2 ≤ r ∧ HasRealCoeffs B ∧ B.eval 0 ≠ 0
        ∧ 0 < x₁ ∧ (∀ k, x₁ ≤ a k)
        ∧ (Finset.univ.filter fun k => a k = x₁).card = ρ ∧ 2 ≤ ρ
        ∧ 0 < ρ - 2 ∧ 0 < r - 2 := by
  classical
  refine ⟨3, 3, 3, ![1, 1, 1], 1, 1, 1, by norm_num, ?_, by norm_num, by norm_num,
    ?_, by simp, by norm_num, ?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · intro k; fin_cases k <;> norm_num
  · intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [Polynomial.coeff_one, hk]
  · intro k; fin_cases k <;> norm_num
  · have hfil : (Finset.univ.filter fun k : Fin 3 => (![1, 1, 1] : Fin 3 → ℝ) k = 1)
        = Finset.univ := by
      ext k; fin_cases k <;> simp
    rw [hfil]
    simp

end ForgacsTran
