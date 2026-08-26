/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.InteriorBranchSeparation
import ForgacsTran.EndpointUpperOneBinders
import ForgacsTran.BranchClockSpacing
import ForgacsTran.WeightedDominanceBranchOneGeneralN

/-!
# `thm:weighted-dominance` at the branch, `r = 1`

`WeightedDominanceBranch.ft_weighted_dominance` discharges every binder of
`DominanceFT.weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data`
at `2 ≤ r` and `2 ≤ ρ`.  This module does the same at `r = 1` and `2 ≤ ρ`, which is
the second of the four corners `subsec:proof` walks.  The lower endpoint is
unchanged — `EndpointLowerBlock.exists_lower_endpoint_block` already covers every
`r ≥ 1` — so what is new is the upper endpoint's block and the composition that
consumes it.

The corner is closed at every admissible `n`.  `3 ≤ n` is `eq:Q-hypotheses`'
own exclusion of `(deg Q, r) = (2,1)`, carried by the lower block and the interior
supply; the upper block holds at `2 ≤ n` and is not what bounds the reach.

**The upper endpoint at `r = 1` is a different object, not the `2 ≤ r` one with a
hypothesis relaxed.**  At `2 ≤ r` the arc radius collapses into the origin, the
retained cluster carries `r - 2` non-principal members, and the amplitude vanishes
to first order, `p_1 = 1`.  At `r = 1` the radius tends to a finite `L > 0`, the
principal pair collides at `-L` where the limiting pencil has a double root, the
retained set is the pair alone — `n_1 = 0` — and the amplitude *diverges*, so the
floor is a constant, `p_1 = 0`.  `EndpointUpperOneBinders` proves those three
facts; this module states them as one block against one `L`, one circle and one
window, and feeds them to the consumer.

**`n_1 = 0` empties five binders and concentrates the content in five others.**
`hL₁`, `hratio₁`, `hgapin₁`, `hginj₁` and `hgmem₁` are met by `Fin.elim0` and test
nothing, and `hcl₁` becomes `0 ≤ W/4`.  What carries the content is `hroot₁`,
`hsimple₁`, `haR₁`, `huniq₁` and `hgcard₁` — the pair is exactly the pencil's zero
set in the disk of radius `2L`, both members simple — and those are supplied from
`WeightedDominanceBranchOneGeneralN`'s count rather than by symmetry with the `2 ≤ r` block.

**`ord_{-L}(B) ≤ 1` is the honest hypothesis on the numerator, and it is where
`p_1 = 0` is true.**  At `ord \ge 2` the amplitude vanishes at the collision and no
constant floor holds; the binder then wants `A_1\eta^{ord-1}`, which is the `2 ≤ r`
shape arriving for an unrelated reason.  `B(0) \ne 0` is still required, by the
consumer, and is a separate condition: `0` and `-L` are different points.

## Main statements

* `exists_upper_endpoint_block_one` — the upper endpoint's whole group at `r = 1`,
  against one `L`, the circle `2L` and one window: the retained pair with its
  count, the contour bound `hCbd₁`, and the amplitude floor `hamp₁` at `p_1 = 0`.
* `ft_weighted_dominance_one` — `thm:weighted-dominance` at `r = 1`, `2 ≤ ρ`, with
  the interior supply of `subsec:proof` in data form as its only antecedent.
* `ft_weighted_dominance_one_unconditional` — the same with the interior supply
  produced, so nothing is assumed on this corner.
* `ft_weighted_dominance_one_hypotheses_nonvacuous` — the hypothesis class
  inhabited with the lower cluster nonempty.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:dominance-bound`, `eq:retained-range`, `eq:ab-def`, `subsec:proof`.

## Tags

weighted dominance, upper endpoint, principal pair, double root, Forgács–Tran branch
-/

namespace ForgacsTran

open Real Set Filter Polynomial Complex
open scoped Topology

/-! ### The upper endpoint's block at `r = 1`

One producer for the upper side of
`weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data`, against
one collision point `L`, one circle `2L` and one window.  The retained set, the
contour bound and the amplitude floor are all built from the same `L`'s limits:
stated as three existentials they need not name the same collision point, and a
consumer pairing one producer's circle with another's floor typechecks and means
nothing.

The `Fin 0` binders are not carried here.  `hL₁`, `hratio₁`, `hgapin₁`, `hginj₁`
and `hgmem₁` are met by `Fin.elim0`, so listing them would add clauses that hold
whatever the geometry does; they are discharged at the composition, where it is
visible that they are the empty ones. -/

/-- **`thm:weighted-dominance`'s upper endpoint at the branch, `r = 1`.**  `n_1 = 0`:
the principal pair is exactly the pencil's zero set in the closed disk of radius
`2L`, and both members are simple.  `τ ≤ 3L/2` against that circle gives `σ_1 = 3/4`.

`hCbd₁` and `hamp₁` are carried too, which the `2 ≤ r` block deliberately leaves
out.  There they are separate analyses off the collapse into the origin; here both
are statements about the limiting pencil at `-L`, so the point they are taken at
has to be the same one, and only a single producer can say so.

The window is punctured and must stay so: `∂_tD(t_+)` vanishes linearly as
`δ → 0`, since the pair collides at the limiting pencil's double root.  The
closed-window form of the simplicity clause is false, and it is the same collision
that makes the amplitude diverge. -/
theorem exists_upper_endpoint_block_one {n : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ ∃ sfun₁ : ℝ → Finset ℂ,
      ∀ B : Polynomial ℂ, B ≠ 0 → B.rootMultiplicity ((-L : ℝ) : ℂ) ≤ 1 →
        ∃ C₁ A₁ : ℝ, 0 ≤ C₁ ∧ 0 < A₁ ∧ ∃ e₁ > (0 : ℝ), e₁ < π ∧
          ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
            0 < ftTauArc a 1 (n - 1) x₁ (π - δ)
            ∧ ftTauArc a 1 (n - 1) x₁ (π - δ) ≤ 3 * L / 2
            ∧ (∀ t ∈ sfun₁ δ, (ftDen (ftRootPoly c a) 1
                ((ftBranchZLower a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t = 0)
            ∧ (∀ t ∈ sfun₁ δ, (derivative (ftDen (ftRootPoly c a) 1
                ((ftBranchZLower a c 1 (n - 1) (π - δ) : ℝ) : ℂ))).eval t ≠ 0)
            ∧ (∀ t ∈ sfun₁ δ, ‖t‖ < 2 * L)
            ∧ (∀ t : ℂ, ‖t‖ ≤ 2 * L → (ftDen (ftRootPoly c a) 1
                ((ftBranchZLower a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₁ δ)
            ∧ (ftDen (ftRootPoly c a) 1
                ((ftBranchZLower a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval
                (ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ)) = 0
            ∧ ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ)
                ≠ ((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ)
                  * Complex.exp (-((π - δ : ℝ) : ℂ) * I)
            ∧ (((sfun₁ δ).erase (ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ))).erase
                (((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ)
                  * Complex.exp (-((π - δ : ℝ) : ℂ) * I))).card = 0
            ∧ (∀ t ∈ Metric.sphere (0 : ℂ) (2 * L),
                ‖B.eval t / (ftDen (ftRootPoly c a) 1
                  ((ftBranchZLower a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁)
            ∧ A₁ * δ ^ 0 ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
                (ftTauArc a 1 (n - 1) x₁) (π - δ) := by
  classical
  obtain ⟨L, hL, hE, hτ, hz⟩ := exists_endpoint_limits_pi (a := a) (c := c) hn2 ha hc
  obtain ⟨eR, heR, hret⟩ := window_of_eventually
    (eventually_upper_retained_one_of_two_le (x₁ := x₁) hn2 ha hc hL hE hτ hz)
  refine ⟨L, hL, fun δ => {ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ),
    ((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ) * Complex.exp (-((π - δ : ℝ) : ℂ) * I)},
    fun B hB0 hm => ?_⟩
  obtain ⟨C₁, hC₁, eC, heC, hC⟩ :=
    exists_upper_contour_bound_one_of_zero_free (B := B) (L := L) hz
      (by positivity)
      (eval_ne_zero_on_sphere_two_mul_endpoint_pi_of_two_le hn2 ha hc hL hE)
  obtain ⟨A₁, hA₁, eA, heA, hA⟩ :=
    ftPrincipalAmp_floor_of_endpoint_pi_of_multiplicity (x₁ := x₁) (B := B)
      hn2 ha hc hL hE hτ hz hB0 hm
  refine ⟨C₁, A₁, hC₁, hA₁, min (min eR eC) (min eA (π / 2)),
    lt_min (lt_min heR heC) (lt_min heA (by positivity)), ?_, fun δ hδ hδe => ?_⟩
  · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _))
      (by linarith [pi_pos])
  have hδhalf : δ ≤ π / 2 := le_trans hδe (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδπ : (0 : ℝ) < π - δ := by linarith [pi_pos]
  have hzarc : ftBranchZLower a c 1 (n - 1) (π - δ) = ftBranchZ a c 1 (n - 1) (π - δ) :=
    ftBranchZLower_agree a c 1 (n - 1) hδπ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    hret δ hδ (le_trans hδe (le_trans (min_le_left _ _) (min_le_left _ _)))
  refine ⟨h1, h2, fun t ht => by rw [hzarc]; exact (h5 t ht).1,
    fun t ht => by rw [hzarc]; exact (h5 t ht).2.2,
    fun t ht => (h5 t ht).2.1, fun t ht h0 => h6 t ht (by rwa [hzarc] at h0),
    by rw [hzarc]; exact h3, h4, ?_, fun t ht => ?_, ?_⟩
  · rw [Finset.erase_insert (by simpa using h4), Finset.erase_singleton, Finset.card_empty]
  · rw [hzarc]
    exact (hC δ hδ (le_trans hδe (le_trans (min_le_left _ _) (min_le_right _ _))) t ht).2
  · simpa [ftPrincipalAmp, hzarc] using
      hA δ hδ (le_trans hδe (le_trans (min_le_right _ _) (min_le_left _ _)))

/-- **`thm:weighted-dominance` at the Forgács–Tran branch, `r = 1`.**  Every binder
of `weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data`
discharged at `Q = ftRootPoly c a` with `r = 1`, `z = ftBranchZLower`,
`τ = ftTauArc` and `b = π`, so the only hypotheses left are the admissible class,
`B(0) ≠ 0`, and `ord_{-L}(B) ≤ 1` at the collision point.

**`L` is quantified with `h`, ahead of the numerator, and it has to be.**  `L` is
the limit of the arc radius at the upper endpoint — a function of `Q` alone — so
the numerator condition `ord_{-L}(B) ≤ 1` cannot even be stated until it is fixed.
The same ordering carries `h = h(Q,r)`: it is built from the lower cluster's gap
coefficient and its size `ρ - 2`, and the upper cluster is empty, so no threshold
comes from that end.

**`3 ≤ n` is Forgács–Tran's own exclusion, not a limit of the formalization.**
`eq:Q-hypotheses` rules out `(deg Q, r) = (2,1)`, which is exactly `n = 2` here,
and both the lower endpoint block and the interior supply carry that exclusion as
a hypothesis.  The upper endpoint asks less — `exists_upper_endpoint_block_one`
holds at every `n ≥ 2` — so nothing on this side is what bounds the reach.

What stays an antecedent is the interior supply of `subsec:proof` in **data**
form, exactly as at `2 ≤ r`.  `ft_weighted_dominance_one_unconditional` discharges
it. -/
theorem ft_weighted_dominance_one {n ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ h > (0 : ℝ), ∃ L > (0 : ℝ), ∀ (B : Polynomial ℂ), HasRealCoeffs B →
      B.eval 0 ≠ 0 → B.rootMultiplicity ((-L : ℝ) : ℂ) ≤ 1 →
      ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
        (∃ (CI σI AI : ℝ) (Sd : Finset ℝ) (νd : ℝ → ℕ),
          0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ Sd, 1 ≤ νd θj) ∧
          (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ π - ε →
            |ftRemainder (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
              (ftTauArc a 1 (n - 1) x₁) M θ| ≤ CI * σI ^ M) ∧
          (∀ θ : ℝ, ε ≤ θ → θ ≤ π - ε →
            AI * ∏ θj ∈ Sd, |θ - θj| ^ νd θj
              ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
                (ftTauArc a 1 (n - 1) x₁) θ) ∧
          (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ Sd,
            Real.exp (-((-Real.log σI) / (2 * Sd.card) * M / νd θj)) ≤ |θ - θj|)) →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
          h / M ≤ θ → θ ≤ π - h / M → θ ∉ Θ M →
            ftRemainder (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
                (ftTauArc a 1 (n - 1) x₁) M θ
              ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
                (ftTauArc a 1 (n - 1) x₁) θ / 2 := by
  classical
  have hb : (0 : ℝ) < π / ((1 : ℕ) : ℝ) := by simpa using pi_pos
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  have hQre : HasRealCoeffs (ftRootPoly c a) := hasRealCoeffs_ftRootPoly c a
  have hR₀pos : 0 < ftSepRadius a x₁ := ftSepRadius_pos hx₁ hmin
  -- the endpoint factorization and the lower block, both before the numerator
  obtain ⟨-, hte₀, hγe₀, -, -, hk₀, -⟩ :=
    endpoint_package_of_two_le_rho (c := c) (r := 1) (by omega) ha hc le_rfl
      (Or.inl (by omega)) hx₁ hmin hcard hρ
  obtain ⟨sfun₀, g₀, idx₀, c₀, hc₀, hgap₀, ⟨e₀b, he₀b, hlow⟩, hresid⟩ :=
    exists_lower_endpoint_block (r := 1) (by omega) ha hc le_rfl
      (by rintro ⟨-, h2⟩; omega) hx₁ hmin hcard hρ
  obtain ⟨L, hL, sfun₁, hblk⟩ :=
    exists_upper_endpoint_block_one (x₁ := x₁) (by omega) ha hc
  -- `h` from the lower cluster alone: the upper cluster is empty at `r = 1`, so it
  -- contributes no threshold
  obtain ⟨t₀, ht₀, hcl₀raw⟩ := exists_cluster_threshold (ι := Fin (ρ - 2)) Finset.univ
    (C_W := 2) (δ := 1 / 4) (c := c₀) (ε := 1) hc₀ zero_le_one (by norm_num) (by norm_num)
  refine ⟨t₀, ht₀, L, hL, fun B hB hB0 hm => ?_⟩
  have hB0' : B ≠ 0 := fun h0 => hB0 (by rw [h0]; simp)
  obtain ⟨cB₀, cQ₀, hcB₀, hcQ₀, hBj₀, hBp₀, hEj₀, hEp₀⟩ := hresid B hB0'
  obtain ⟨C₀, hC₀, ec₀, hec₀, hcbd₀⟩ :=
    exists_endpoint_contour_window_of_two_le_rho (r := 1) (by omega) ha hc le_rfl
      (Or.inl (by omega)) hx₁ hmin hcard hρ B
  obtain ⟨C₁, A₁, hC₁, hA₁, e₁b, he₁b, -, hup⟩ := hblk B hB0' hm
  have hE₀ : (0 : ℝ) < min e₀b ec₀ := lt_min he₀b hec₀
  have hE₀a : ∀ δ : ℝ, δ ≤ min e₀b ec₀ → δ ≤ e₀b := fun δ h => le_trans h (min_le_left _ _)
  have hE₀c : ∀ δ : ℝ, δ ≤ min e₀b ec₀ → δ ≤ ec₀ := fun δ h => le_trans h (min_le_right _ _)
  -- the lower endpoint's remaining three binders
  have hγ0₀ : ftPrincipal (ftTauArc a 1 (n - 1) x₁) 0 = ((x₁ : ℝ) : ℂ) := by
    rw [ftPrincipal_ftTauArc_eq_lower a 1 (n - 1) x₁ hb, ftPrincipal_ftTauLower_zero]
  have hγd₀ := hasDerivWithinAt_ftPrincipal_ftTauArc_lower (r := 1) (by omega) ha
    le_rfl (Or.inl (by omega)) hx₁ hmin hcard hρ
  have hrootev₀ : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (ftDen (ftRootPoly c a) 1 ((ftBranchZLower a c 1 (n - 1) δ : ℝ) : ℂ)).eval
        (ftPrincipal (ftTauArc a 1 (n - 1) x₁) δ) = 0 :=
    eventually_of_window hE₀ fun δ hδ hδe => (hlow δ hδ (hE₀a δ hδe)).2.2.2.2.2.2.1
  have hσ₀1 : x₁ / ftSepRadius a x₁ < 1 := (div_lt_one hR₀pos).2 (lt_ftSepRadius hmin)
  exact weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data
      (h := t₀) (b := π) (z := ftBranchZLower a c 1 (n - 1)) (τ := ftTauArc a 1 (n - 1) x₁)
      (sfun₀ := sfun₀) (sfun₁ := sfun₁) (g₀ := g₀) (g₁ := fun _ _ => 0)
      (idx₀ := idx₀) (jp₀ := 0) (νB₀ := B.rootMultiplicity ((x₁ : ℝ) : ℂ))
      (n₁ := 0) (p₁ := 0) (τmax₁ := 3 * L / 2) (σ₁ := 3 / 4) (R₁ := 2 * L)
      (L₁ := fun i => i.elim0) (c₁ := 0)
      hQre hB hB0' le_rfl hQ0 hx₁ (fun _ => hρ) hte₀ hγe₀ hγ0₀ hγd₀ hk₀ hrootev₀
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
      hA₁ ⟨e₁b, he₁b, fun η hη hηe => (hup η hη hηe).2.2.2.2.2.2.2.2.2.2⟩
      (fun i => i.elim0) (fun i => i.elim0)
      (by positivity) (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
      (by norm_num) he₁b
      (fun δ hδ hδe => (hup δ hδ hδe).1)
      (fun δ hδ hδe => (hup δ hδ hδe).2.1)
      (fun δ hδ hδe => (hup δ hδ hδe).2.2.1)
      (fun δ hδ hδe => (hup δ hδ hδe).2.2.2.1)
      (fun δ hδ hδe => (hup δ hδ hδe).2.2.2.2.1)
      (fun δ hδ hδe => (hup δ hδ hδe).2.2.2.2.2.1)
      (fun δ hδ hδe => (hup δ hδ hδe).2.2.2.2.2.2.1)
      (fun δ hδ hδe => (hup δ hδ hδe).2.2.2.2.2.2.2.1)
      (fun δ _ _ => Function.injective_of_subsingleton _)
      (fun δ _ _ i => i.elim0)
      (fun δ hδ hδe => (hup δ hδ hδe).2.2.2.2.2.2.2.2.1)
      hC₁ (fun δ hδ hδe => (hup δ hδ hδe).2.2.2.2.2.2.2.2.2.1)
      ht₀ hgap₀ ⟨1, one_pos, fun δ _ _ i => i.elim0⟩
      ⟨1, one_pos, fun A ζ' θ W hθ hθe hW hA hg M hM =>
        hcl₀raw A ζ' θ W hθ hθe hW hA hg M hM⟩
      ⟨1, one_pos, fun A ζ' η W _ _ hW _ _ M _ => by simpa using by linarith⟩

/-- **`eq:amplitude-deletion`'s collars have exponentially small total length.**
Each divisor point contributes a window of length `2exp(-κM/ν_j)`; the largest
multiplicity gives the slowest decay, and there are `|S|` of them.

Nothing here sees the branch, the numerator or `r`: the statement is about a finite
set of positive multiplicities and a `σ ∈ (0,1)`, which is why it is proved once
and instantiated at each corner. -/
theorem exists_exp_decay_of_collars {S : Finset ℝ} {mult : ℝ → ℕ} {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hν : ∀ θj ∈ S, 1 ≤ mult θj) :
    ∃ K > (0 : ℝ), ∃ cdec > (0 : ℝ), ∀ M : ℕ,
      ∑ θj ∈ S, 2 * Real.exp (-((-Real.log σ) / (2 * S.card) * M / (mult θj)))
        ≤ K * Real.exp (-cdec * M) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · refine ⟨1, one_pos, 1, one_pos, fun M => ?_⟩
    rw [Finset.sum_empty]
    positivity
  have hcard0 : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hSne
  have hlog : 0 < -Real.log σ := by have := Real.log_neg hσ0 hσ1; linarith
  set κ : ℝ := (-Real.log σ) / (2 * S.card) with hκ
  have hκ0 : 0 < κ := div_pos hlog (by linarith)
  set N : ℕ := S.sup mult with hN
  obtain ⟨θ0, hθ0⟩ := hSne
  have hN1 : 1 ≤ N := le_trans (hν θ0 hθ0) (Finset.le_sup (f := mult) hθ0)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  refine ⟨2 * S.card, by linarith, κ / N, div_pos hκ0 hNR, fun M => ?_⟩
  have hterm : ∀ θj ∈ S,
      2 * Real.exp (-(κ * M / (mult θj))) ≤ 2 * Real.exp (-(κ / N * M)) := by
    intro θj hθj
    have hνj : 0 < (mult θj : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hν θj hθj)
    have hle : (mult θj : ℝ) ≤ N := by exact_mod_cast Finset.le_sup (f := mult) hθj
    have hMnn : (0 : ℝ) ≤ κ * M := by positivity
    have hdiv : κ * M / N ≤ κ * M / (mult θj) := div_le_div_of_nonneg_left hMnn hνj hle
    have hexp := Real.exp_le_exp.2 (neg_le_neg hdiv)
    calc 2 * Real.exp (-(κ * M / (mult θj)))
        ≤ 2 * Real.exp (-(κ * M / N)) := by linarith [hexp]
      _ = 2 * Real.exp (-(κ / N * M)) := by ring_nf
  calc ∑ θj ∈ S, 2 * Real.exp (-(κ * M / (mult θj)))
      ≤ ∑ _θj ∈ S, 2 * Real.exp (-(κ / N * M)) := Finset.sum_le_sum hterm
    _ = 2 * S.card * Real.exp (-(κ / N * M)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ = 2 * S.card * Real.exp (-(κ / N) * M) := by ring_nf

/-- **`thm:weighted-dominance` at the branch, `r = 1`, with nothing assumed on this
corner.**  The interior supply is produced by
`InteriorBranchSeparation.ft_interior_data_on_arc_one`, whose separation is
unconditional on the admissible class at `3 ≤ n` and puts no restriction on any
multiplicity, so what is left is the admissible class, `B(0) ≠ 0` and
`ord_{-L}(B) ≤ 1`.

**The deleted family is written out, not existentially quantified.**  An
`∃ Θ : ℕ → Set ℝ` form would be trivially true — `Θ M := univ` makes `θ ∉ Θ M`
unsatisfiable — so the windows appear as `eq:amplitude-deletion`'s own inequality,
and `S` is pinned by `1 ≤ ord_{t_+(θ_j)}(B)`: every divisor point is an angle where
`B` vanishes at the principal point, and `B` has finitely many zeros. -/
theorem ft_weighted_dominance_one_unconditional {n ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ h > (0 : ℝ), ∃ L > (0 : ℝ), ∀ (B : Polynomial ℂ), HasRealCoeffs B →
      B.eval 0 ≠ 0 → B.rootMultiplicity ((-L : ℝ) : ℂ) ≤ 1 →
      ∃ (S : Finset ℝ) (σ : ℝ), 0 < σ ∧ σ < 1
      ∧ (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θj))
      ∧ (∀ θj ∈ S, θj ∈ Set.Ioo (0 : ℝ) π)
      ∧ (∃ K > (0 : ℝ), ∃ cdec > (0 : ℝ), ∀ M : ℕ,
          ∑ θj ∈ S, 2 * Real.exp (-((-Real.log σ) / (2 * S.card) * M
              / (B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θj))))
            ≤ K * Real.exp (-cdec * M))
      ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ π - h / M →
        (∀ θj ∈ S, Real.exp (-((-Real.log σ) / (2 * S.card) * M
            / (B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θj)))) ≤ |θ - θj|) →
          ftRemainder (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
              (ftTauArc a 1 (n - 1) x₁) M θ
            ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
              (ftTauArc a 1 (n - 1) x₁) θ / 2 := by
  classical
  have hcast : π / ((1 : ℕ) : ℝ) = π := by norm_num
  obtain ⟨h, hh, L, hL, H0⟩ := ft_weighted_dominance_one hn3 ha hc hx₁ hmin hcard hρ
  refine ⟨h, hh, L, hL, fun B hB hB0 hm => ?_⟩
  have hB0' : B ≠ 0 := fun h0 => hB0 (by rw [h0]; simp)
  obtain ⟨ε, hε, H⟩ := H0 B hB hB0 hm
  obtain ⟨CI, σI, AI, S, hσ0, hσ1, hA, hrem, hfloor, hν, hSband⟩ :
      ∃ (CI σI AI : ℝ) (S : Finset ℝ), 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
        (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ π - ε →
          |ftRemainder (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
            (ftTauArc a 1 (n - 1) x₁) M θ| ≤ CI * σI ^ M) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ π - ε →
          AI * ∏ θj ∈ S, |θ - θj|
              ^ (B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θj))
            ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
              (ftTauArc a 1 (n - 1) x₁) θ) ∧
        (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θj)) ∧
        (∀ θj ∈ S, θj ∈ Set.Icc ε (π - ε)) := by
    by_cases hεb : ε ≤ π - ε
    · have := ft_interior_data_on_arc_one (x₁ := x₁) (B := B) (by omega) ha hc hB hB0'
        hε (by rw [hcast]; exact hεb)
      rwa [hcast] at this
    · exact ⟨1, 1 / 2, 1, ∅, by norm_num, by norm_num, by norm_num,
        fun M θ h1 h2 => absurd (le_trans h1 h2) hεb,
        fun θ h1 h2 => absurd (le_trans h1 h2) hεb, by simp, by simp⟩
  obtain ⟨M₀, hM₀⟩ :=
    H (fun M => {θ : ℝ | ∃ θj ∈ S, |θ - θj| < Real.exp (-((-Real.log σI)
        / (2 * S.card) * M / (B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θj))))})
      ⟨CI, σI, AI, S, fun θj => B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θj),
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

/-- **The hypothesis set of `ft_weighted_dominance_one` is inhabited, and not at the
degenerate corner.**  At `Q = (1 - t)^3` with `r = 1` the smallest zero carries
multiplicity `ρ = 3`, so the lower retained cluster has one member, `n_0 = ρ - 2 = 1`.

`n_1 = 0` is not a degeneracy to be avoided here — it is the `r = 1` geometry: the
principal pair is the whole upper cluster.  What the last conjunct rules out is the
other degeneracy, `ρ = 2`, where the lower family is `Fin 0` and is met by
`Fin.elim0` without testing anything.

The numerator condition is stated at every `L`, because `L` is produced by the
theorem rather than chosen: `B = 1` meets `B(0) ≠ 0` and `ord_{-L}(B) ≤ 1` whatever
collision point the upper endpoint hands back. -/
theorem ft_weighted_dominance_one_hypotheses_nonvacuous :
    ∃ (n ρ : ℕ) (a : Fin n → ℝ) (c x₁ : ℝ),
      3 ≤ n ∧ (∀ k, 0 < a k) ∧ 0 < c ∧ 0 < x₁ ∧ (∀ k, x₁ ≤ a k)
        ∧ (Finset.univ.filter fun k => a k = x₁).card = ρ ∧ 2 ≤ ρ ∧ 0 < ρ - 2
        ∧ HasRealCoeffs (1 : Polynomial ℂ) ∧ (1 : Polynomial ℂ).eval 0 ≠ 0
        ∧ ∀ L : ℝ, (1 : Polynomial ℂ).rootMultiplicity ((-L : ℝ) : ℂ) ≤ 1 := by
  classical
  refine ⟨3, 3, ![1, 1, 1], 1, 1, by norm_num, ?_, by norm_num, by norm_num, ?_, ?_,
    by norm_num, by norm_num, hasRealCoeffs_one, by norm_num, fun L => ?_⟩
  · intro k; fin_cases k <;> norm_num
  · intro k; fin_cases k <;> norm_num
  · have hfil : (Finset.univ.filter fun k : Fin 3 => (![1, 1, 1] : Fin 3 → ℝ) k = 1)
        = Finset.univ := by
      ext k; fin_cases k <;> simp
    rw [hfil]
    simp
  · rw [Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])]
    exact Nat.zero_le 1

end ForgacsTran
