/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointLowerChart
import ForgacsTran.EndpointUpperBinders

/-!
# The lower endpoint block

`EndpointUpperGap.exists_upper_endpoint_block` assembles the upper endpoint's
binders of `thm:weighted-dominance` against **one** separating radius, one
enumeration and one window.  This is its lower counterpart, and the reason it is
one theorem rather than nine is the same: the retained set, the enumeration, the
residue asymptotics and the modulus gap are all statements about *one* cluster,
and a caller that obtains them from four separate existentials can pair one
producer's cardinality with another's values and still build.

The eleven of those clauses that describe the cluster itself are
`EndpointUpperBinders.RetainedCluster`, which the upper block returns too — the
two endpoints differ only in the angle, the radius and which spectral parameter
is substituted, and naming the shape is what makes that visible.

So everything here is stated at the single `ψ` of
`exists_principal_pair_cluster_indices_of_two_le_rho`, the single chart of
`exists_lower_chart`, and the single window their two windows intersect.  The
radius is `ftSepRadius a x₁` and the spectral parameter is `ftBranchZLower`, which
is the pair the two-endpoint composition uses.

The count is `n_0 = ρ - 2`: the retained cluster is the `ρ` members of the
smallest zero's fiber with the principal pair removed.

`2 ≤ ρ` is a real restriction and `1 ≤ r` is not.  The lower endpoint's geometry
is the fiber of the smallest zero, which the branch exponent does not see, so this
block holds at every `r ≥ 1` — only `¬(r = 1 ∧ n = 2)` is needed, and that is the
degenerate pencil where the retained cluster and the principal pair exhaust the
denominator.  At `ρ = 1` the block does not apply and cannot be repaired by
relaxing a hypothesis: `Cluster.clusterAlpha_one_eq_zero` says the endpoint
slope datum degenerates to `0` there, so `hγe₀ ≠ 0` fails, and
`SimpleEndpoint.hEp_false_of_rho_one` shows `hEp₀` is outright false.  A simple
smallest zero needs its own endpoint regularity, not this one weakened.

**The numerator is quantified inside**, after the cluster and its modulus gap.
`B` enters this block in one place only — the leading behavior of `B` along each
branch — while the cluster, the enumeration, the window and the gap coefficient
`c_0` are properties of the denominator's fiber alone.  Stating it as
`∀ B, …` rather than taking `B` as a binder is what lets a caller fix the
threshold `h` of `thm:weighted-dominance` before the numerator, which is what the
paper's `h = h(Q,r)` asserts.

## Main statements

* `exists_lower_endpoint_block` — the residue asymptotics, the linear modulus gap
  and the eleven window fields, at one cluster.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:lower-cluster-expansion`, `eq:lower-residue-ratio`,
  `eq:endpoint-linear-gap`.

## Tags

lower endpoint, retained cluster, residue asymptotics, weighted dominance
-/

namespace ForgacsTran

open Polynomial
open scoped Topology

/-- **The lower endpoint's binder block of `thm:weighted-dominance`.**  At the
branch `z = ftBranchZLower`, the arc radius `τ = ftTauArc` and the separating
radius `R_0 = ftSepRadius a x₁`: the residue asymptotics of
`eq:lower-residue-ratio` at one pair of constants, the modulus gap of
`eq:endpoint-linear-gap` with its coefficient positive, and the eleven window
fields — all against one cluster, one enumeration and one window.

The principal point's own cluster label is `0`, because the shift
`(j + ρ - j_p) \bmod ρ` sends `j_p` there; that is what lets `jp₀ := 0` in the
consumer and is why the principal asymptotics come out of the same application
that produces the members'. -/
theorem exists_lower_endpoint_block {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hne1 : ¬(r = 1 ∧ n = 2))
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ (sfun₀ : ℝ → Finset ℂ) (g₀ : ℝ → Fin (ρ - 2) → ℂ) (idx₀ : Fin (ρ - 2) → ℕ)
      (c₀ : ℝ), 0 < c₀
      ∧ (∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i : Fin (ρ - 2),
          1 + c₀ * δ ≤ ‖g₀ δ i‖ / ftTauArc a r (n - 1) x₁ δ)
      ∧ (∃ e₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
        RetainedCluster (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
          (ftTauArc a r (n - 1) x₁) δ (ftSepRadius a x₁) x₁ (sfun₀ δ) (g₀ δ))
      ∧ ∀ (B : Polynomial ℂ), B ≠ 0 → ∃ cB₀ cQ₀ : ℂ, cB₀ ≠ 0 ∧ cQ₀ ≠ 0 ∧
          (∀ i : Fin (ρ - 2), Filter.Tendsto
            (fun δ : ℝ => B.eval (g₀ δ i)
              / ((δ : ℝ) : ℂ) ^ ((B.rootMultiplicity ((x₁ : ℝ) : ℂ) : ℕ) : ℤ))
            (𝓝[>] (0 : ℝ))
            (𝓝 (cB₀ * clusterAlpha x₁ ρ (idx₀ i)
              ^ B.rootMultiplicity ((x₁ : ℝ) : ℂ))))
        ∧ Filter.Tendsto
            (fun δ : ℝ => B.eval (ftPrincipal (ftTauArc a r (n - 1) x₁) δ)
              / ((δ : ℝ) : ℂ) ^ ((B.rootMultiplicity ((x₁ : ℝ) : ℂ) : ℕ) : ℤ))
            (𝓝[>] (0 : ℝ))
            (𝓝 (cB₀ * clusterAlpha x₁ ρ 0 ^ B.rootMultiplicity ((x₁ : ℝ) : ℂ)))
        ∧ (∀ i : Fin (ρ - 2), Filter.Tendsto
            (fun δ : ℝ => (derivative (ftDen (ftRootPoly c a) r
                ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ))).eval (g₀ δ i)
              / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
            (𝓝[>] (0 : ℝ)) (𝓝 (cQ₀ * clusterAlpha x₁ ρ (idx₀ i) ^ (ρ - 1))))
        ∧ Filter.Tendsto
            (fun δ : ℝ => (derivative (ftDen (ftRootPoly c a) r
                ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ))).eval
                (ftPrincipal (ftTauArc a r (n - 1) x₁) δ)
              / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
            (𝓝[>] (0 : ℝ)) (𝓝 (cQ₀ * clusterAlpha x₁ ρ 0 ^ (ρ - 1))) := by
  classical
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := hr
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hb : 0 < Real.pi / r := div_pos Real.pi_pos hrR
  obtain ⟨ψ, jp, jc, hjp, hjc, hjcshift, hshift, epp, hepp, hall⟩ :=
    exists_principal_pair_cluster_indices_of_two_le_rho hn2 ha hc hr1 hne1 hx₁ hmin hcard hρ
  obtain ⟨chart, hchartinj, hchartlt, hnejp, hnejc, hchart01⟩ :=
    exists_lower_chart hρ hjp hjc hjcshift
  have hjpc : jp ≠ jc := by
    rw [hjcshift]
    rcases lt_or_ge (1 + jp) ρ with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [show 1 + jp = ρ by omega, Nat.mod_self]; omega
  -- the window: the cluster's own, kept strictly inside the arc
  have hE0 : 0 < min epp (Real.pi / r / 2) := lt_min hepp (by positivity)
  have hEb : min epp (Real.pi / r / 2) < Real.pi / r :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hElt : ∀ δ : ℝ, 0 < δ → δ ≤ min epp (Real.pi / r / 2) → δ < Real.pi / r :=
    fun δ _ h => lt_of_le_of_lt h hEb
  obtain ⟨hτpos, hτle, hrootplus, hnepair⟩ :=
    endpoint_retained_partial_of_two_le_rho (c := c) hn2 ha hr1 hne1 hmin hcard hρ hEb
  -- the arc radius agrees with the lower one across that window
  have harc : ∀ δ : ℝ, 0 < δ → δ ≤ min epp (Real.pi / r / 2) →
      ftTauArc a r (n - 1) x₁ δ = ftTauLower a r (n - 1) x₁ δ :=
    fun δ hδ hδe => ftTauArc_eq_lower a r (n - 1) x₁ (hElt δ hδ hδe)
  have hparc : ∀ δ : ℝ, 0 < δ → δ ≤ min epp (Real.pi / r / 2) →
      ftPrincipal (ftTauArc a r (n - 1) x₁) δ
        = ftPrincipal (ftTauLower a r (n - 1) x₁) δ :=
    fun δ hδ hδe => ftPrincipal_ftTauArc_eq_lower a r (n - 1) x₁ (hElt δ hδ hδe)
  -- the principal pair, in the chart lemma's spelling
  have hpA : ∀ δ : ℝ, 0 < δ → δ ≤ min epp (Real.pi / r / 2) →
      ftPrincipal (ftTauArc a r (n - 1) x₁) δ
        = ψ (clusterDir ρ jp * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) := by
    intro δ hδ hδe
    rw [hparc δ hδ hδe]
    exact (hall δ hδ (le_trans hδe (min_le_left _ _))).1
  have hqA : ∀ δ : ℝ, 0 < δ → δ ≤ min epp (Real.pi / r / 2) →
      ((ftTauArc a r (n - 1) x₁ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I)
        = ψ (clusterDir ρ jc * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) := by
    intro δ hδ hδe
    have h2 := (hall δ hδ (le_trans hδe (min_le_left _ _))).2.1
    rw [conj_ftPrincipal'] at h2
    rw [harc δ hδ hδe]
    exact h2
  have hτposA : ∀ δ : ℝ, 0 < δ → δ ≤ min epp (Real.pi / r / 2) →
      0 < ftTauArc a r (n - 1) x₁ δ := by
    intro δ hδ hδe
    rw [harc δ hδ hδe]
    exact hτpos δ hδ hδe
  -- the residue asymptotics, the principal point carried in the same family
  obtain ⟨chartExt, hExtCast, hExtLast⟩ :
      ∃ f : Fin ((ρ - 2) + 1) → ℕ,
        (∀ i : Fin (ρ - 2), f (Fin.castSucc i) = chart i) ∧ f (Fin.last (ρ - 2)) = jp :=
    ⟨fun i => if h : (i : ℕ) < ρ - 2 then chart ⟨(i : ℕ), h⟩ else jp,
      fun i => by simp [Fin.val_castSucc, i.isLt], by simp⟩
  have hjp0 : (jp + ρ - jp) % ρ = 0 := by rw [Nat.add_sub_cancel_left, Nat.mod_self]
  have hPev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ftPrincipal (ftTauArc a r (n - 1) x₁) δ
        = ψ (clusterDir ρ jp * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) :=
    eventually_of_window hE0 hpA
  -- the modulus gap
  have hτev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ‖ftPrincipal (ftTauArc a r (n - 1) x₁) δ‖ = ftTauArc a r (n - 1) x₁ δ
        ∧ ftPrincipal (ftTauArc a r (n - 1) x₁) δ ≠ 0 :=
    eventually_of_window hE0 fun δ hδ hδe =>
      ⟨norm_ftPrincipal_eq (hτposA δ hδ hδe), ftPrincipal_ne_zero_of_pos (hτposA δ hδ hδe)⟩
  have hPs : Filter.Tendsto
      (fun δ : ℝ => (ftPrincipal (ftTauArc a r (n - 1) x₁) δ - ((x₁ : ℝ) : ℂ))
        / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (clusterAlpha x₁ ρ 0)) := by
    refine (tendsto_ftPrincipal_slope_of_two_le_rho hn ha hr1 hnr hx₁ hmin hcard
      hρ).congr' ?_
    filter_upwards [eventually_of_window hE0 hparc] with δ hd
    rw [hd]
  obtain ⟨c₀, hc₀, eg, heg, hgap⟩ :=
    exists_linear_gap_of_slopes (ρ := ρ) (x₁ := x₁) hx₁ hρ (m := ρ - 2)
      (g := fun i δ => ψ (clusterDir ρ (chart i)
        * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)))
      (P := fun δ => ftPrincipal (ftTauArc a r (n - 1) x₁) δ)
      (τ := ftTauArc a r (n - 1) x₁)
      (idx := fun i => (chart i + ρ - jp) % ρ)
      (fun i => Nat.mod_lt _ (by omega)) hchart01 hτev (fun i => hshift (chart i)) hPs
  refine ⟨fun δ => ftClusterSet a c r (n - 1) ρ ψ δ,
    fun δ i => ψ (clusterDir ρ (chart i) * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)),
    fun i => (chart i + ρ - jp) % ρ, c₀, hc₀, ⟨eg, heg, hgap⟩,
    ⟨min epp (Real.pi / r / 2), hE0, fun δ hδ hδe => ?_⟩, fun B hB0 => ?_⟩
  · obtain ⟨hcardS, hroots, hnorms, hsimple, hcomplete⟩ :=
      (hall δ hδ (le_trans hδe (min_le_left _ _))).2.2
    obtain ⟨hginj, hgmem, hgcard⟩ :=
      lower_cluster_enumeration_of_chart (a := a) (c := c) (r := r) (x₁ := x₁)
        hjp hjc hjpc hchartinj hchartlt hnejp hnejc hcardS (hpA δ hδ hδe) (hqA δ hδ hδe)
    refine ⟨hτposA δ hδ hδe, ?_, hroots, hsimple, hnorms, hcomplete, ?_, ?_,
      hginj, hgmem, hgcard⟩
    · rw [harc δ hδ hδe]; exact hτle δ hδ hδe
    · rw [hparc δ hδ hδe]
      exact hrootplus δ hδ hδe
    · rw [hparc δ hδ hδe, harc δ hδ hδe]
      exact hnepair δ hδ hδe
  obtain ⟨cB, cQ, hcB, hcQ, hBt, hEt⟩ :=
    exists_residue_asymptotics_of_slopes (m := (ρ - 2) + 1)
      (t := fun i δ => ψ (clusterDir ρ (chartExt i)
        * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)))
      (idx := fun i => (chartExt i + ρ - jp) % ρ)
      hn2 ha hc hr1 hx₁ hmin hcard hρ hB0 (fun i => hshift (chartExt i))
  refine ⟨cB, cQ, hcB, hcQ, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := hBt (Fin.castSucc i)
    simp only [hExtCast] at h
    simpa [zpow_natCast] using h
  · have h := hBt (Fin.last (ρ - 2))
    simp only [hExtLast, hjp0] at h
    simp only [zpow_natCast]
    refine h.congr' ?_
    filter_upwards [hPev] with δ hd
    rw [hd]
  · intro i
    have h := hEt (Fin.castSucc i)
    simp only [hExtCast] at h
    simpa [zpow_natCast] using h
  · have h := hEt (Fin.last (ρ - 2))
    simp only [hExtLast, hjp0] at h
    simp only [zpow_natCast]
    refine h.congr' ?_
    filter_upwards [hPev] with δ hd
    rw [hd]

end ForgacsTran
