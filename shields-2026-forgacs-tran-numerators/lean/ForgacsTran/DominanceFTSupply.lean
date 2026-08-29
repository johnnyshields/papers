/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.DominanceAssembly
import ForgacsTran.Amplitude
import ForgacsTran.FTMinModulus

/-!
# The paper's named objects, and the supplies `thm:weighted-dominance` consumes

`DominanceAssembly.weighted_dominance` proves the theorem over abstract
`Rrem`/`Wamp`.  This module names the paper's own objects and discharges the
supplies that assembly consumes; `DominanceFTBranch` then states the theorem on
the Forgács--Tran branch out of them.

## Main statements

* `amplitude_lower_bound_of_endpoint_form` — `hamp₀`/`hamp₁`, from
  `Amplitude.amplitude_endpoint_form`.  `δ^{k-1}W = δ^ν V` with `V`
  continuous and `V(0)≠0` becomes `Aδ^p ≤ |W|` on a one-sided window,
  `p = ν - (k-1)` truncated at zero — the paper's `p_+`, and the truncation is
  why one statement covers both signs of `p`.
* `cluster_amplitude_window` — `hCW₀`/`hCW₁`, from
  `Cluster.eventually_cluster_amplitude_le`.  The `C_W = 2` stays derived from
  `eq:lower-residue-ratio`, never assumed.
* `weighted_dominance_of_windows` — the six endpoint supplies are each proved on a
  window of their own; this reconciles them onto one `ε`, taking the
  interior supply as a function of the window because the interior region *grows*
  as `ε` shrinks.  That is the paper's own order: fix `ε`
  first, then establish the interior estimates on the resulting compact set.
* `ftPrincipal`, `ftPrincipalAmp`, `ftRemainder` — `eq:principal-pair`,
  `eq:W-def` and `eq:principal-decomposition` as named objects.
* `ftRemainder_split` — `EndpointDominance.endpoint_remainder_split_indexed` in
  those names, which is what feeds `hsplit₀`/`hsplit₁` through
  `EndpointDominance.hsplit_of_indexed_uniform`.
* `weighted_dominance_ftCoeffPoly_at` — `eq:dominance-bound` with the interior
  parameter `e` a **parameter**, so a caller fixes it before producing the
  interior data, which is `subsec:proof`'s order.
* `weighted_dominance_ftCoeffPoly` — **`eq:dominance-bound` on
  `eq:retained-range` for `F_M`**: `ftRemainder ≤ \tfrac12 ftPrincipalAmp`,
  stated in `ftCoeffPoly Q B r` and `ftAmp Q B r`.
* `ftPrincipalAmp_lower_bound`, `ftPrincipalAmp_ne_zero_of_lower_bound`,
  `ftCluster_amplitude_le_two`, `ftSplit_of_branch` — the three endpoint supplies
  discharged from the branch, all four stated through a **chart** `w` so one
  statement serves both endpoints: `w = id` below, `w = fun η => b - η`
  above.
* `interior_remainder_uniform` — `eq:interior-remainder`, and
  `eq:interior-relative-remainder`'s remainder
  half, uniform over the compact interior: there the retained cluster is the
  principal pair alone, so `R_M` *is* the contour error.
* `amplitude_floor_off_windows` — `eq:amplitude-deletion`'s arithmetic: off the
  windows each factor of the amplitude's zero divisor is at least `e^{-cM}`, so a
  lower bound by the divisor becomes `A_Ie^{-cJM}`.  The paper's exponent
  `c = \tfrac1{2J}log(1/σ_I)` is forced by matching it to
  `A_Ie^{-(α/2)M}`.
* `hint_of_interior_data` — the interior supply built from those two plus the
  amplitude's lower bound by its own zero divisor.
* `exists_interior_amplitude_data` — **`lem:amplitude-divisor` on the compact
  interior, as a conclusion.**  The amplitude's zero set `S`, its orders `ν`
  and the local cofactors `U`, from the branch alone: `S` is finite because the
  branch is injective and carries each amplitude zero to a zero of `B`, which is
  `eq:amplitude-zero-count`'s mechanism; `ν` is `B`'s root multiplicity along
  the branch; `U` comes from `Amplitude.exists_amplitude_factor_on`.
* `exists_interior_amplitude_factors` — the same with `S` supplied rather than
  built, which is what a caller needs when the windows `Θ` are *defined*
  from `S` and its multiplicities.  It still derives `ν`, `U`, the
  factorization and the amplitude's continuity.
* `interior_data_of_geometry`, `hdata_entry_of_interior` — one entry of the
  interior supply from primitives: the remainder bound from
  `interior_remainder_uniform`, the cofactors from
  `exists_interior_amplitude_factors`, and the floor from
  `Amplitude.exists_amplitude_divisor_lower_bound`.
* `dominance_shrinking_of_fixed_window` — `eq:retained-range` with the amplitude
  windows shrinking, from the fixed one.

## Implementation notes

The uniform contour constant comes from
`EndpointDominance.exists_uniform_ftDiv_bound` — `B/D` is continuous on the
compact `[0,e] × \{|t| = R_0\}` and so bounded there.
**Differs from the paper's route.**  The manuscript gets that uniformity by
decreasing `ε` until `eq:contour-remainder-bound`'s hypotheses hold on
each region; here it is compactness, and the bound is stated on `B/D` over a
*fixed* circle rather than on the retained-set data.  The two are not
interchangeable: a bound on `poleRem/poleCofactor` does not exist at the
parameter values where two retained zeros collide, and `B/D` on a zero-free
circle does not see the collision.  The interior amplitude bound is
`Amplitude.exists_amplitude_divisor_lower_bound` — the collar decomposition over
the whole zero set, not just one zero — composed with the deleted-window
inequality in `hint_of_interior_data`, where `amplitude_floor_off_windows` turns
the product `∏_j|θ-θ_j|^{ν_j}` into the floor `e^{-cM}`; the
`1/ν_j` in the window width is what makes every factor contribute equally.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`,
`subsec:weighted-dominance`, `thm:weighted-dominance`, `eq:dominance-bound`,
`eq:retained-range`, `lem:amplitude-divisor`, `eq:lower-residue-ratio`).

## Tags

weighted dominance, endpoint supply, principal amplitude
-/

namespace ForgacsTran

open Polynomial Complex

/-! ### The endpoint amplitude lower bound -/

/-- **Paper `lem:amplitude-divisor`, in the form `thm:weighted-dominance` uses
it.**  `Amplitude.amplitude_endpoint_form` gives `δ^{k-1}W(δ) =
δ^ν V(δ)` with `V` continuous and `V(0)≠0`; this turns it into the
lower bound `Aδ^p ≤ |W(δ)|` on a one-sided window, with
`p = ν - (k-1)` truncated at zero.

The truncation is the paper's `p_+ = max\{p,0\}`, and it is why one statement
covers both signs of `p`: where `ν < k-1` the amplitude blows up at the
endpoint and the bound holds with `p = 0`.  This is `hamp₀` (and, in the
reflected variable, `hamp₁`) of `weighted_dominance`. -/
theorem amplitude_lower_bound_of_endpoint_form {Q B : Polynomial ℂ} (hB : B ≠ 0) {r : ℕ}
    (hr : 1 ≤ r) {γ zf : ℝ → ℂ} {te γe : ℂ} (hte : te ≠ 0) (hγe : γe ≠ 0) (hγ0 : γ 0 = te)
    (hγ : HasDerivWithinAt γ γe (Set.Ici 0) 0) (hP : ftDen Q r (zf 0) ≠ 0)
    (hk : 1 ≤ (ftDen Q r (zf 0)).rootMultiplicity te)
    (hroot : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), (ftDen Q r (zf δ)).eval (γ δ) = 0) :
    ∃ A > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      A * δ ^ (B.rootMultiplicity te - ((ftDen Q r (zf 0)).rootMultiplicity te - 1))
        ≤ ‖ftAmp Q B r (zf δ) (γ δ)‖ := by
  classical
  obtain ⟨V, hVc, hV0, hVeq⟩ :=
    amplitude_endpoint_form (Q := Q) (B := B) hB hr hte hγe hγ0 hγ hP hk hroot
  set k := (ftDen Q r (zf 0)).rootMultiplicity te with hkdef
  set ν := B.rootMultiplicity te with hνdef
  set p := ν - (k - 1) with hpdef
  set A : ℝ := ‖V 0‖ / 2 with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hVbd : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)), A < ‖V δ‖ := by
    refine (hVc.norm).eventually_const_lt ?_
    rw [hAdef]
    have : 0 < ‖V 0‖ := norm_pos_iff.mpr hV0
    linarith
  have hmono : nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
      ≤ nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ)) :=
    nhdsWithin_mono _ Set.Ioi_subset_Ici_self
  have hev : ∀ᶠ (δ : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (((δ : ℝ) : ℂ) ^ (k - 1) * ftAmp Q B r (zf δ) (γ δ) = ((δ : ℝ) : ℂ) ^ ν * V δ)
        ∧ A < ‖V δ‖ :=
    hVeq.and (hmono hVbd)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨A, hApos, min (ε₀ / 2) 1, lt_min (by linarith) one_pos, ?_⟩
  intro δ hδ hδε
  have hδ1 : δ ≤ 1 := le_trans hδε (min_le_right _ _)
  have hδ0 : dist δ (0 : ℝ) < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    calc δ ≤ min (ε₀ / 2) 1 := hδε
      _ ≤ ε₀ / 2 := min_le_left _ _
      _ < ε₀ := by linarith
  obtain ⟨hid, hVδ⟩ := hball hδ0 hδ
  -- take norms of the endpoint identity
  have hnorm : δ ^ (k - 1) * ‖ftAmp Q B r (zf δ) (γ δ)‖ = δ ^ ν * ‖V δ‖ := by
    have := congrArg norm hid
    rwa [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ] at this
  have hple : ν ≤ p + (k - 1) := by omega
  have hpow : δ ^ (p + (k - 1)) ≤ δ ^ ν := pow_le_pow_of_le_one hδ.le hδ1 hple
  have hk1 : (0 : ℝ) < δ ^ (k - 1) := by positivity
  have hchain : A * δ ^ p * δ ^ (k - 1) ≤ δ ^ (k - 1) * ‖ftAmp Q B r (zf δ) (γ δ)‖ := by
    rw [hnorm]
    calc A * δ ^ p * δ ^ (k - 1) = A * δ ^ (p + (k - 1)) := by rw [pow_add]; ring
      _ ≤ A * δ ^ ν := mul_le_mul_of_nonneg_left hpow hApos.le
      _ ≤ δ ^ ν * ‖V δ‖ := by nlinarith [pow_nonneg hδ.le ν, hVδ]
  nlinarith [hchain, hk1]

/-! ### The cluster amplitude comparison on a window -/

/-- **Paper `eq:lower-residue-ratio`'s `C_W = 2`, on a one-sided window.**
`Cluster.eventually_cluster_amplitude_le` gives `|W_j| ≤ 2|W|` eventually along
`θ ↓ 0`; this is that statement read as a window `(0,ε]`,
which is the `hCW₀` hypothesis of `weighted_dominance`.  The constant is derived
from the residue ratio, never assumed. -/
theorem cluster_amplitude_window {κ : Type*} {s : Finset κ} {W : ℝ → ℂ} {Wf : κ → ℝ → ℂ}
    {L : κ → ℂ}
    (hW : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), W θ ≠ 0)
    (h : ∀ i ∈ s, Filter.Tendsto (fun θ => Wf i θ / W θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (L i)))
    (hL : ∀ i ∈ s, ‖L i‖ = 1) :
    ∃ ε > (0 : ℝ), ∀ θ : ℝ, 0 < θ → θ ≤ ε → ∀ i ∈ s, ‖Wf i θ‖ ≤ 2 * ‖W θ‖ := by
  have hev := eventually_cluster_amplitude_le hW h hL
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε₀ / 2, by linarith, ?_⟩
  intro θ hθ hθε i hi
  have hd : dist θ (0 : ℝ) < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hθ]; linarith
  exact hball hd hθ i hi

/-! ### One window for all six supplies -/

/-- **`weighted_dominance` with each supply carrying its own window.**  The six
endpoint supplies are each established on a window of their own — the amplitude
bound on one, the residue comparison on another, the modulus gap on a third, the
split on a fourth — and `weighted_dominance` needs them on a common `ε`.
Shrinking is free for all of them; the interior is not, because its region grows
as `ε` shrinks, so the interior supply is taken as a *function* of the
window, which is what the paper does too ("decrease to some
`0 < ε ≤ ε_*`", then establish the interior estimates on the
resulting compact set). -/
theorem weighted_dominance_of_windows {n₀ n₁ p₀ p₁ : ℕ} {b : ℝ} {Θ : ℕ → Set ℝ}
    {Rrem : ℕ → ℝ → ℝ} {Wamp : ℝ → ℝ}
    {A₀ c₀ C₀ σ₀ : ℝ} {Wf₀ ζ₀ : ℝ → Fin n₀ → ℝ}
    {A₁ c₁ C₁ σ₁ : ℝ} {Wf₁ ζ₁ : ℝ → Fin n₁ → ℝ}
    (hc₀ : 0 < c₀) (hA₀ : 0 < A₀) (hC₀ : 0 ≤ C₀) (hσ₀0 : 0 ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (hc₁ : 0 < c₁) (hA₁ : 0 < A₁) (hC₁ : 0 ≤ C₁) (hσ₁0 : 0 ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (hamp₀ : ∃ e > (0 : ℝ), ∀ θ : ℝ, 0 < θ → θ ≤ e → A₀ * θ ^ p₀ ≤ Wamp θ)
    (hCW₀ : ∃ e > (0 : ℝ), ∀ θ : ℝ, 0 < θ → θ ≤ e → ∀ i, |Wf₀ θ i| ≤ 2 * Wamp θ)
    (hgap₀ : ∃ e > (0 : ℝ), ∀ θ : ℝ, 0 < θ → θ ≤ e → ∀ i, 1 + c₀ * θ ≤ ζ₀ θ i)
    (hsplit₀ : ∃ e > (0 : ℝ), ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ e →
      |Rrem M θ| ≤ (∑ i, |Wf₀ θ i| * (ζ₀ θ i ^ (M + 1))⁻¹) + C₀ * σ₀ ^ M)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e → A₁ * η ^ p₁ ≤ Wamp (b - η))
    (hCW₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e → ∀ i, |Wf₁ (b - η) i| ≤ 2 * Wamp (b - η))
    (hgap₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e → ∀ i, 1 + c₁ * η ≤ ζ₁ (b - η) i)
    (hsplit₁ : ∃ e > (0 : ℝ), ∀ (M : ℕ) (η : ℝ), 0 < η → η ≤ e →
      |Rrem M (b - η)| ≤ (∑ i, |Wf₁ (b - η) i| * (ζ₁ (b - η) i ^ (M + 1))⁻¹) + C₁ * σ₁ ^ M)
    (hint : ∀ e : ℝ, 0 < e → ∃ AI CI σI : ℝ, 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M → |Rrem M θ| ≤ CI * σI ^ M) ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        AI * Real.exp (-((-Real.log σI) / 2) * M) ≤ Wamp θ)) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M → |Rrem M θ| ≤ Wamp θ / 2 := by
  obtain ⟨e₁, he₁, hamp₀⟩ := hamp₀
  obtain ⟨e₂, he₂, hCW₀⟩ := hCW₀
  obtain ⟨e₃, he₃, hgap₀⟩ := hgap₀
  obtain ⟨e₄, he₄, hsplit₀⟩ := hsplit₀
  obtain ⟨e₅, he₅, hamp₁⟩ := hamp₁
  obtain ⟨e₆, he₆, hCW₁⟩ := hCW₁
  obtain ⟨e₇, he₇, hgap₁⟩ := hgap₁
  obtain ⟨e₈, he₈, hsplit₁⟩ := hsplit₁
  set ε : ℝ := min (min (min e₁ e₂) (min e₃ e₄)) (min (min e₅ e₆) (min e₇ e₈)) with hε
  have hεpos : 0 < ε := by
    rw [hε]; repeat' apply lt_min
    all_goals assumption
  have h1 : ε ≤ e₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have h2 : ε ≤ e₂ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have h3 : ε ≤ e₃ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h4 : ε ≤ e₄ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have h5 : ε ≤ e₅ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have h6 : ε ≤ e₆ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have h7 : ε ≤ e₇ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h8 : ε ≤ e₈ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨AI, CI, σI, hσI0, hσI1, hAI, hbdI, hampI⟩ := hint ε hεpos
  exact weighted_dominance hεpos hc₀ hA₀ hC₀ hσ₀0 hσ₀1
    (fun θ hθ hθε => hamp₀ θ hθ (le_trans hθε h1))
    (fun θ hθ hθε => hCW₀ θ hθ (le_trans hθε h2))
    (fun θ hθ hθε => hgap₀ θ hθ (le_trans hθε h3))
    (fun M θ hθ hθε => hsplit₀ M θ hθ (le_trans hθε h4))
    hc₁ hA₁ hC₁ hσ₁0 hσ₁1
    (fun η hη hηε => hamp₁ η hη (le_trans hηε h5))
    (fun η hη hηε => hCW₁ η hη (le_trans hηε h6))
    (fun η hη hηε => hgap₁ η hη (le_trans hηε h7))
    (fun M η hη hηε => hsplit₁ M η hη (le_trans hηε h8))
    hσI0 hσI1 hAI hbdI hampI

/-! ### `thm:weighted-dominance` for `F_M` -/

/-- Paper `eq:principal-pair` — the principal branch `t_+(θ) = τ(θ)e^{iθ}`. -/
noncomputable def ftPrincipal (τ : ℝ → ℝ) (θ : ℝ) : ℂ :=
  ((τ θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)

/-- `eq:principal-pair` — the second member `t_-(θ) = τ(θ)e^{-iθ}` is the conjugate
of the first, so it has the same modulus.  `τ` is explicit: the cubic witnesses
apply this at a named radius rather than rewriting with it. -/
theorem conj_ftPrincipal (τ : ℝ → ℝ) (θ : ℝ) :
    (starRingEnd ℂ) (ftPrincipal τ θ)
      = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I) := by
  rw [ftPrincipal, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp

/-- Paper `eq:W-def` — the modulus `|W(θ)|` of the principal amplitude. -/
noncomputable def ftPrincipalAmp (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ‖ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)‖

/-- Paper `eq:principal-decomposition` — `|R_M(θ)|`, the normalized
coefficient with the principal pair's contribution removed. -/
noncomputable def ftRemainder (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (M : ℕ) (θ : ℝ) : ℝ :=
  ‖(((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)
    - ((2 * ((((τ θ : ℝ) : ℂ)) ^ (M + 1)
        * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
            / (ftPrincipal τ θ) ^ (M + 1))).re : ℝ) : ℂ)‖

/-- **`endpoint_remainder_split_indexed` in the paper's named objects.**  Feeds
`weighted_dominance_ftCoeffPoly`'s `hsplit₀` (and, in the reflected variable, its
`hsplit₁`) with `W_j = ‖𝒲(g_j)‖` and `ζ_j = ‖g_j‖/τ`. -/
theorem ftRemainder_split {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0) {z τ : ℝ → ℝ} {θ : ℝ} (hτ : 0 < τ θ)
    {s : Finset ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀) (hτR : τ θ ≤ R₀)
    (hroot : ∀ a ∈ s, (ftDen Q r ((z θ : ℝ) : ℂ)).eval a = 0)
    (hsimple : ∀ a ∈ s, (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (haR : ∀ a ∈ s, ‖a‖ < R₀)
    (huniq : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 → t ∈ s)
    (hrootplus : (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hne : ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I))
    {n : ℕ} (g : Fin n → ℂ) (hginj : Function.Injective g)
    (hgmem : ∀ i, g i ∈ (s.erase (ftPrincipal τ θ)).erase
      (((τ θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I)))
    (hgcard : ((s.erase (ftPrincipal τ θ)).erase
      (((τ θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I))).card = n) :
    ∃ C ≥ (0 : ℝ), ∀ M : ℕ,
      |ftRemainder Q B r z τ M θ|
        ≤ (∑ i : Fin n, |‖ftAmp Q B r ((z θ : ℝ) : ℂ) (g i)‖|
              * ((‖g i‖ / τ θ) ^ (M + 1))⁻¹)
          + τ θ * C * (τ θ / R₀) ^ M :=
  endpoint_remainder_split_indexed hQ hB hr hQ0 hτ hR₀ hτR hroot hsimple ha0 haR huniq
    hrootplus hne g hginj hgmem hgcard

/-! ### The interior remainder as an identity, in the paper's named objects

`interior_remainder_bound_of_bound` bounds `R_M` on the compact interior; what
`eq:C1-interior-remainder` needs is the **identity** behind that bound, because
the quantity it differentiates,
`(τ^{M+1}F_M(z(θ))).re/(2|W|) - cos Φ_M`, has two halves that are each `O(M)`
while only their difference is exponentially small.  Differentiating the halves
separately therefore proves nothing, and no bound on the difference survives
differentiation either.  Read as one analytic function of the spectral parameter
— `PoleExpansion.ftContourRem`, whose `w`-derivative carries the same `R^{-M}` as
its value — it differentiates in one step through
`PoleExpansion.hasDerivAt_ftContourRem_comp`. -/

/-- **`eq:contour-separated-expansion` on the compact interior, as an identity, in
the paper's named objects.**  `ftRemainder` *is* `τ^{M+1}` times the contour
remainder's modulus, not merely bounded by it. -/
theorem ftRemainder_eq_contour {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0) {z τ : ℝ → ℝ}
    {θ : ℝ} (hτ : 0 < τ θ) {R₀ : ℝ} (hR₀ : 0 < R₀) (hτR : τ θ < R₀)
    (hrootplus : (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsp : (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0)
    (hsm : (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
      (((τ θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I)) ≠ 0)
    (hne : ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (hpairdisk : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
      t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (M : ℕ) :
    ftRemainder Q B r z τ M θ
      = τ θ ^ (M + 1) * ‖ftContourRem Q B r R₀ M ((z θ : ℝ) : ℂ)‖ := by
  have hprin : ftPrincipal τ θ = ((τ θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) := rfl
  rw [hprin] at hrootplus hsp hne hpairdisk
  rw [ftRemainder, hprin,
    interior_remainder_eq_contour hQ hB hr hQ0 hτ hR₀ hτR hrootplus hsp hsm hne hpairdisk M,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]

/-- The real-part form, which is the one `eq:C1-interior-remainder` differentiates:
the numerator of `(τ^{M+1}F_M(z(θ))).re/(2|W|) - cos Φ_M` is the real part of a
single analytic function of the spectral parameter. -/
theorem ftCoeff_re_sub_principal_eq_contour_re {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0) {z τ : ℝ → ℝ}
    {θ : ℝ} (hτ : 0 < τ θ) {R₀ : ℝ} (hR₀ : 0 < R₀) (hτR : τ θ < R₀)
    (hrootplus : (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsp : (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0)
    (hsm : (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
      (((τ θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I)) ≠ 0)
    (hne : ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (hpairdisk : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
      t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (M : ℕ) :
    ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
        - 2 * ((((τ θ : ℝ) : ℂ)) ^ (M + 1)
            * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
                / (ftPrincipal τ θ) ^ (M + 1))).re
      = ((((τ θ : ℝ) : ℂ)) ^ (M + 1)
          * ftContourRem Q B r R₀ M ((z θ : ℝ) : ℂ)).re := by
  have hprin : ftPrincipal τ θ = ((τ θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) := rfl
  rw [hprin] at hrootplus hsp hne hpairdisk
  rw [hprin]
  exact interior_remainder_re_eq_contour hQ hB hr hQ0 hτ hR₀ hτR hrootplus hsp hsm hne
    hpairdisk M

/-- **`eq:dominance-bound` at a caller-named interior parameter.**  Every window
is `e`, and `e` is a parameter rather than an existential inside each supply, so
a caller fixes it **first** and only then has to produce the interior data — which
is `subsec:proof`'s own order: choose `ε` with every amplitude zero inside
`(ε, π/r - ε)`, then quantify `M`.

That order is what BANK-37's residue asks for.  `hint` here is at one `e`, not at
every `e`, so a caller building `Θ` out of `σ(e)` is no longer building it before
`σ` exists; the circularity that forces an admissible `Θ` to be `M`-independent is
in the `∀ e` form and not in this one.

`weighted_dominance_ftCoeffPoly` is this theorem with the eight endpoint windows
reconciled by a `min`, and its signature is unchanged.  Nothing is lost by taking
`e` as a parameter: each endpoint supply is `∀ δ ≤ e, P δ`, so all eight are
downward closed in `e` and hold at any `e` below the `min` the wrapper forms. -/
theorem weighted_dominance_ftCoeffPoly_at {Q B : Polynomial ℂ} {r : ℕ}
    {n₀ n₁ p₀ p₁ : ℕ} {b e : ℝ} {z τ : ℝ → ℝ} {Θ : ℕ → Set ℝ}
    {Wf₀ ζ₀ : ℝ → Fin n₀ → ℝ} {Wf₁ ζ₁ : ℝ → Fin n₁ → ℝ}
    {A₀ c₀ C₀ σ₀ A₁ c₁ C₁ σ₁ : ℝ} (he : 0 < e)
    (hc₀ : 0 < c₀) (hA₀ : 0 < A₀) (hC₀ : 0 ≤ C₀) (hσ₀0 : 0 ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (hc₁ : 0 < c₁) (hA₁ : 0 < A₁) (hC₁ : 0 ≤ C₁) (hσ₁0 : 0 ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (hamp₀ : ∀ θ : ℝ, 0 < θ → θ ≤ e → A₀ * θ ^ p₀ ≤ ftPrincipalAmp Q B r z τ θ)
    (hCW₀ : ∀ θ : ℝ, 0 < θ → θ ≤ e → ∀ i,
      |Wf₀ θ i| ≤ 2 * ftPrincipalAmp Q B r z τ θ)
    (hgap₀ : ∀ θ : ℝ, 0 < θ → θ ≤ e → ∀ i, 1 + c₀ * θ ≤ ζ₀ θ i)
    (hsplit₀ : ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ e →
      |ftRemainder Q B r z τ M θ|
        ≤ (∑ i, |Wf₀ θ i| * (ζ₀ θ i ^ (M + 1))⁻¹) + C₀ * σ₀ ^ M)
    (hamp₁ : ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    (hCW₁ : ∀ η : ℝ, 0 < η → η ≤ e → ∀ i,
      |Wf₁ (b - η) i| ≤ 2 * ftPrincipalAmp Q B r z τ (b - η))
    (hgap₁ : ∀ η : ℝ, 0 < η → η ≤ e → ∀ i, 1 + c₁ * η ≤ ζ₁ (b - η) i)
    (hsplit₁ : ∀ (M : ℕ) (η : ℝ), 0 < η → η ≤ e →
      |ftRemainder Q B r z τ M (b - η)|
        ≤ (∑ i, |Wf₁ (b - η) i| * (ζ₁ (b - η) i ^ (M + 1))⁻¹) + C₁ * σ₁ ^ M)
    (hint : ∃ AI CI σI : ℝ, 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        AI * Real.exp (-((-Real.log σI) / 2) * M) ≤ ftPrincipalAmp Q B r z τ θ)) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
        ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  obtain ⟨AI, CI, σI, hσI0, hσI1, hAI, hbdI, hampI⟩ := hint
  obtain ⟨h, hhpos, M₀, hM₀⟩ :=
    weighted_dominance (Rrem := ftRemainder Q B r z τ)
      (Wamp := ftPrincipalAmp Q B r z τ) (Θ := Θ) (b := b) (ε := e)
      he hc₀ hA₀ hC₀ hσ₀0 hσ₀1 hamp₀ hCW₀ hgap₀ hsplit₀
      hc₁ hA₁ hC₁ hσ₁0 hσ₁1 hamp₁ hCW₁ hgap₁ hsplit₁
      hσI0 hσI1 hAI hbdI hampI
  refine ⟨h, hhpos, M₀, fun M hM θ h1 h2 h3 => ?_⟩
  have hnn : (0 : ℝ) ≤ ftRemainder Q B r z τ M θ := norm_nonneg _
  have hb := hM₀ M hM θ h1 h2 h3
  rwa [abs_of_nonneg hnn] at hb

/-- **`weighted_dominance_ftCoeffPoly_at` with the threshold `h` an input.**  The
paper's `h` is a function of the denominator alone, so it is a parameter here,
constrained only by `hcl₀` and `hcl₁` — `Dominance.exists_cluster_threshold`'s
conclusion at the two endpoint gap rates, whose statements mention neither `B` nor
the amplitude.  A caller wanting one threshold for every numerator supplies it once
from that lemma and instantiates this at each `B`.

`weighted_dominance_ftCoeffPoly_at` is this with `h` produced inside, and its
signature is unchanged. -/
theorem weighted_dominance_ftCoeffPoly_at_of_threshold {Q B : Polynomial ℂ} {r : ℕ}
    {n₀ n₁ p₀ p₁ : ℕ} {b e : ℝ} {z τ : ℝ → ℝ} {Θ : ℕ → Set ℝ}
    {Wf₀ ζ₀ : ℝ → Fin n₀ → ℝ} {Wf₁ ζ₁ : ℝ → Fin n₁ → ℝ}
    {A₀ c₀ C₀ σ₀ A₁ c₁ C₁ σ₁ h : ℝ} (he : 0 < e) (hhpos : 0 < h)
    (hA₀ : 0 < A₀) (hC₀ : 0 ≤ C₀) (hσ₀0 : 0 ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (hA₁ : 0 < A₁) (hC₁ : 0 ≤ C₁) (hσ₁0 : 0 ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (hamp₀ : ∀ θ : ℝ, 0 < θ → θ ≤ e → A₀ * θ ^ p₀ ≤ ftPrincipalAmp Q B r z τ θ)
    (hCW₀ : ∀ θ : ℝ, 0 < θ → θ ≤ e → ∀ i,
      |Wf₀ θ i| ≤ 2 * ftPrincipalAmp Q B r z τ θ)
    (hgap₀ : ∀ θ : ℝ, 0 < θ → θ ≤ e → ∀ i, 1 + c₀ * θ ≤ ζ₀ θ i)
    (hcl₀ : ∀ (A ζ' : Fin n₀ → ℝ) (θ W : ℝ), 0 < θ → θ ≤ e → 0 ≤ W →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), 1 + c₀ * θ ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * θ →
          ∑ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    (hsplit₀ : ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ e →
      |ftRemainder Q B r z τ M θ|
        ≤ (∑ i, |Wf₀ θ i| * (ζ₀ θ i ^ (M + 1))⁻¹) + C₀ * σ₀ ^ M)
    (hamp₁ : ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    (hCW₁ : ∀ η : ℝ, 0 < η → η ≤ e → ∀ i,
      |Wf₁ (b - η) i| ≤ 2 * ftPrincipalAmp Q B r z τ (b - η))
    (hgap₁ : ∀ η : ℝ, 0 < η → η ≤ e → ∀ i, 1 + c₁ * η ≤ ζ₁ (b - η) i)
    (hcl₁ : ∀ (A ζ' : Fin n₁ → ℝ) (η W : ℝ), 0 < η → η ≤ e → 0 ≤ W →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), 1 + c₁ * η ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * η →
          ∑ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    (hsplit₁ : ∀ (M : ℕ) (η : ℝ), 0 < η → η ≤ e →
      |ftRemainder Q B r z τ M (b - η)|
        ≤ (∑ i, |Wf₁ (b - η) i| * (ζ₁ (b - η) i ^ (M + 1))⁻¹) + C₁ * σ₁ ^ M)
    (hint : ∃ AI CI σI : ℝ, 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        AI * Real.exp (-((-Real.log σI) / 2) * M) ≤ ftPrincipalAmp Q B r z τ θ)) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
        ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  obtain ⟨AI, CI, σI, hσI0, hσI1, hAI, hbdI, hampI⟩ := hint
  obtain ⟨M₀, hM₀⟩ :=
    weighted_dominance_of_threshold (Rrem := ftRemainder Q B r z τ)
      (Wamp := ftPrincipalAmp Q B r z τ) (Θ := Θ) (b := b) (ε := e) (h := h)
      he hhpos hcl₀ hA₀ hC₀ hσ₀0 hσ₀1 hamp₀ hCW₀ hgap₀ hsplit₀
      hcl₁ hA₁ hC₁ hσ₁0 hσ₁1 hamp₁ hCW₁ hgap₁ hsplit₁
      hσI0 hσI1 hAI hbdI hampI
  refine ⟨M₀, fun M hM θ h1 h2 h3 => ?_⟩
  have hnn : (0 : ℝ) ≤ ftRemainder Q B r z τ M θ := norm_nonneg _
  have hb := hM₀ M hM θ h1 h2 h3
  rwa [abs_of_nonneg hnn] at hb

/-- **Paper `thm:weighted-dominance`, for `F_M`.**  `eq:dominance-bound` on
`eq:retained-range`, stated at the paper's own objects: the coefficient
polynomials `ftCoeffPoly Q B r` of `eq:F-M-def`, the residue amplitude `ftAmp` of
`eq:residue-amplitude`, and the principal branch `t_+(θ) = τ(θ)e^{iθ}`.

Each supply carries its own window, `weighted_dominance_of_windows` reconciling
them.  `hamp₀`/`hamp₁` are discharged by
`amplitude_lower_bound_of_endpoint_form`, `hCW₀`/`hCW₁` by
`cluster_amplitude_window` (so the `C_W = 2` stays derived from
`eq:lower-residue-ratio`, never assumed), and `hsplit₀`/`hsplit₁` by
`ftRemainder_split` composed with `hsplit_of_indexed_uniform`.  What is left
carried is the branch data of `thm:FT-geometry` and the interior supply. -/
theorem weighted_dominance_ftCoeffPoly {Q B : Polynomial ℂ} {r : ℕ}
    -- `Θ` is bound HERE, before `hinterior`'s `∀ e`, while `σi` is produced inside
    -- it — so every admissible `Θ` is forced `M`-independent and `subsec:proof`'s
    -- shrinking windows cannot be expressed.  The mismatch is internal, not merely
    -- a gap against the manuscript: the conclusion's own window `h/M ≤ θ ≤ b - h/M`
    -- ALREADY shrinks with `M`, so the theorem knows about shrinking windows in its
    -- interval and not in its exceptional set.  `Θ` is the one `M`-indexed object in
    -- the statement required to be independent of the `M`-dependent data, which is
    -- why `CubicWitnessInterior.cubicWitness_window_forced` can force it `M`-independent
    -- while the rest of the statement is not.
    --
    -- Three restatements are ruled out, and the third is the one that looks right.
    -- Putting `Θ` inside `hinterior`'s existential leaves it out of scope at the
    -- conclusion, which then asserts only that SOME exceptional set exists — green,
    -- and unusable, since a caller cannot check `θ ∉ Θ M` for any concrete `θ`.
    -- Leaving `Θ` where it is while `hinterior` takes it as an input changes
    -- nothing, because it is still fixed before `σi`.  And `Θ : ℝ → ℕ → Set ℝ` with
    -- the conclusion pinned at `e = h/M` — the shape that reads as the fix — still
    -- forces a fixed width: at a pencil where `σ(e) ≥ τ(e)^ρ` with `τ(e) = 1 - ce
    -- + O(e²)`, `-log σ(h/M) ≲ ρc·h/M`, so `c(e)·M` tends to a constant and the
    -- half-width `e^{-cM/ν}` tends to a positive constant again.
    --
    -- What works is to separate the window from the geometry rather than reorder
    -- them: `interior_data_of_geometry` is this hypothesis with no `Θ` in it, and
    -- `dominance_shrinking_of_fixed_window` upgrades a fixed window to `h/M` from
    -- it.  The residue — that `hinterior` demands the window at every `e` and uses
    -- it at one — is removed by `weighted_dominance_ftCoeffPoly_at`, which takes
    -- `e` as a parameter and `hint` at that one `e`.  Making the radii produced
    -- internally from `Tendsto` statements explicit is *not* needed: the eight
    -- endpoint supplies are each `∀ δ ≤ e, P δ`, hence downward closed in `e`, so
    -- a caller may name any `e` below the `min` this theorem forms.  That is the
    -- manuscript's order, and this theorem is now the `min`-reconciling wrapper
    -- over it.
    {n₀ n₁ p₀ p₁ : ℕ} {b : ℝ} {z τ : ℝ → ℝ} {Θ : ℕ → Set ℝ}
    {Wf₀ ζ₀ : ℝ → Fin n₀ → ℝ} {Wf₁ ζ₁ : ℝ → Fin n₁ → ℝ}
    {A₀ c₀ C₀ σ₀ A₁ c₁ C₁ σ₁ : ℝ}
    (hc₀ : 0 < c₀) (hA₀ : 0 < A₀) (hC₀ : 0 ≤ C₀) (hσ₀0 : 0 ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (hc₁ : 0 < c₁) (hA₁ : 0 < A₁) (hC₁ : 0 ≤ C₁) (hσ₁0 : 0 ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (hamp₀ : ∃ e > (0 : ℝ), ∀ θ : ℝ, 0 < θ → θ ≤ e →
      A₀ * θ ^ p₀ ≤ ftPrincipalAmp Q B r z τ θ)
    (hCW₀ : ∃ e > (0 : ℝ), ∀ θ : ℝ, 0 < θ → θ ≤ e → ∀ i,
      |Wf₀ θ i| ≤ 2 * ftPrincipalAmp Q B r z τ θ)
    (hgap₀ : ∃ e > (0 : ℝ), ∀ θ : ℝ, 0 < θ → θ ≤ e → ∀ i, 1 + c₀ * θ ≤ ζ₀ θ i)
    (hsplit₀ : ∃ e > (0 : ℝ), ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ e →
      |ftRemainder Q B r z τ M θ|
        ≤ (∑ i, |Wf₀ θ i| * (ζ₀ θ i ^ (M + 1))⁻¹) + C₀ * σ₀ ^ M)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    (hCW₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e → ∀ i,
      |Wf₁ (b - η) i| ≤ 2 * ftPrincipalAmp Q B r z τ (b - η))
    (hgap₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e → ∀ i, 1 + c₁ * η ≤ ζ₁ (b - η) i)
    (hsplit₁ : ∃ e > (0 : ℝ), ∀ (M : ℕ) (η : ℝ), 0 < η → η ≤ e →
      |ftRemainder Q B r z τ M (b - η)|
        ≤ (∑ i, |Wf₁ (b - η) i| * (ζ₁ (b - η) i ^ (M + 1))⁻¹) + C₁ * σ₁ ^ M)
    (hint : ∀ e : ℝ, 0 < e → ∃ AI CI σI : ℝ, 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        AI * Real.exp (-((-Real.log σI) / 2) * M) ≤ ftPrincipalAmp Q B r z τ θ)) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
        ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  -- the eight endpoint windows reconciled by a `min`, then the theorem with `e`
  -- named.  Each supply is `∀ δ ≤ e, P δ`, hence downward closed in `e`, so all
  -- eight survive the shrink.
  obtain ⟨e₁, he₁, hamp₀⟩ := hamp₀
  obtain ⟨e₂, he₂, hCW₀⟩ := hCW₀
  obtain ⟨e₃, he₃, hgap₀⟩ := hgap₀
  obtain ⟨e₄, he₄, hsplit₀⟩ := hsplit₀
  obtain ⟨e₅, he₅, hamp₁⟩ := hamp₁
  obtain ⟨e₆, he₆, hCW₁⟩ := hCW₁
  obtain ⟨e₇, he₇, hgap₁⟩ := hgap₁
  obtain ⟨e₈, he₈, hsplit₁⟩ := hsplit₁
  set ε : ℝ := min (min (min e₁ e₂) (min e₃ e₄)) (min (min e₅ e₆) (min e₇ e₈)) with hε
  have hεpos : 0 < ε := by
    rw [hε]; repeat' apply lt_min
    all_goals assumption
  have h1 : ε ≤ e₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have h2 : ε ≤ e₂ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have h3 : ε ≤ e₃ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h4 : ε ≤ e₄ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have h5 : ε ≤ e₅ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have h6 : ε ≤ e₆ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have h7 : ε ≤ e₇ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h8 : ε ≤ e₈ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  exact weighted_dominance_ftCoeffPoly_at (e := ε) hεpos hc₀ hA₀ hC₀ hσ₀0 hσ₀1
    hc₁ hA₁ hC₁ hσ₁0 hσ₁1
    (fun θ hθ hθε => hamp₀ θ hθ (le_trans hθε h1))
    (fun θ hθ hθε => hCW₀ θ hθ (le_trans hθε h2))
    (fun θ hθ hθε => hgap₀ θ hθ (le_trans hθε h3))
    (fun M θ hθ hθε => hsplit₀ M θ hθ (le_trans hθε h4))
    (fun η hη hηε => hamp₁ η hη (le_trans hηε h5))
    (fun η hη hηε => hCW₁ η hη (le_trans hηε h6))
    (fun η hη hηε => hgap₁ η hη (le_trans hηε h7))
    (fun M η hη hηε => hsplit₁ M η hη (le_trans hηε h8))
    (hint ε hεpos)


/-- **`weighted_dominance_ftCoeffPoly` with the threshold `h` an input.**  The
ten endpoint windows are reconciled by a `min` as in the bundled form; the two
extra ones are the cluster hypotheses' own, and they carry the only constraint on
`h`.  Neither mentions `B`, the amplitude, or the remainder, so a caller may fix
one `h` and instantiate at every numerator.

`weighted_dominance_ftCoeffPoly` is this with `h` produced inside. -/
theorem weighted_dominance_ftCoeffPoly_of_threshold {Q B : Polynomial ℂ} {r : ℕ}
    {n₀ n₁ p₀ p₁ : ℕ} {b : ℝ} {z τ : ℝ → ℝ} {Θ : ℕ → Set ℝ}
    {Wf₀ ζ₀ : ℝ → Fin n₀ → ℝ} {Wf₁ ζ₁ : ℝ → Fin n₁ → ℝ}
    {A₀ c₀ C₀ σ₀ A₁ c₁ C₁ σ₁ h : ℝ} (hhpos : 0 < h)
    (hA₀ : 0 < A₀) (hC₀ : 0 ≤ C₀) (hσ₀0 : 0 ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (hA₁ : 0 < A₁) (hC₁ : 0 ≤ C₁) (hσ₁0 : 0 ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (hcl₀ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₀ → ℝ) (θ W : ℝ), 0 < θ → θ ≤ e → 0 ≤ W →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), 1 + c₀ * θ ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * θ →
          ∑ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    (hcl₁ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₁ → ℝ) (η W : ℝ), 0 < η → η ≤ e → 0 ≤ W →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), 1 + c₁ * η ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * η →
          ∑ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    (hamp₀ : ∃ e > (0 : ℝ), ∀ θ : ℝ, 0 < θ → θ ≤ e →
      A₀ * θ ^ p₀ ≤ ftPrincipalAmp Q B r z τ θ)
    (hCW₀ : ∃ e > (0 : ℝ), ∀ θ : ℝ, 0 < θ → θ ≤ e → ∀ i,
      |Wf₀ θ i| ≤ 2 * ftPrincipalAmp Q B r z τ θ)
    (hgap₀ : ∃ e > (0 : ℝ), ∀ θ : ℝ, 0 < θ → θ ≤ e → ∀ i, 1 + c₀ * θ ≤ ζ₀ θ i)
    (hsplit₀ : ∃ e > (0 : ℝ), ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ e →
      |ftRemainder Q B r z τ M θ|
        ≤ (∑ i, |Wf₀ θ i| * (ζ₀ θ i ^ (M + 1))⁻¹) + C₀ * σ₀ ^ M)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    (hCW₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e → ∀ i,
      |Wf₁ (b - η) i| ≤ 2 * ftPrincipalAmp Q B r z τ (b - η))
    (hgap₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e → ∀ i, 1 + c₁ * η ≤ ζ₁ (b - η) i)
    (hsplit₁ : ∃ e > (0 : ℝ), ∀ (M : ℕ) (η : ℝ), 0 < η → η ≤ e →
      |ftRemainder Q B r z τ M (b - η)|
        ≤ (∑ i, |Wf₁ (b - η) i| * (ζ₁ (b - η) i ^ (M + 1))⁻¹) + C₁ * σ₁ ^ M)
    (hint : ∀ e : ℝ, 0 < e → ∃ AI CI σI : ℝ, 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        AI * Real.exp (-((-Real.log σI) / 2) * M) ≤ ftPrincipalAmp Q B r z τ θ)) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
        ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  obtain ⟨e₁, he₁, hamp₀⟩ := hamp₀
  obtain ⟨e₂, he₂, hCW₀⟩ := hCW₀
  obtain ⟨e₃, he₃, hgap₀⟩ := hgap₀
  obtain ⟨e₄, he₄, hsplit₀⟩ := hsplit₀
  obtain ⟨e₅, he₅, hamp₁⟩ := hamp₁
  obtain ⟨e₆, he₆, hCW₁⟩ := hCW₁
  obtain ⟨e₇, he₇, hgap₁⟩ := hgap₁
  obtain ⟨e₈, he₈, hsplit₁⟩ := hsplit₁
  obtain ⟨e₉, he₉, hcl₀⟩ := hcl₀
  obtain ⟨e₁₀, he₁₀, hcl₁⟩ := hcl₁
  set ε : ℝ :=
    min (min (min (min e₁ e₂) (min e₃ e₄)) (min (min e₅ e₆) (min e₇ e₈))) (min e₉ e₁₀) with hε
  have hεpos : 0 < ε := by
    rw [hε]; repeat' apply lt_min
    all_goals assumption
  have hP : ε ≤ min (min (min e₁ e₂) (min e₃ e₄)) (min (min e₅ e₆) (min e₇ e₈)) :=
    min_le_left _ _
  have h1 : ε ≤ e₁ :=
    le_trans hP (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have h2 : ε ≤ e₂ :=
    le_trans hP (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have h3 : ε ≤ e₃ :=
    le_trans hP (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h4 : ε ≤ e₄ :=
    le_trans hP (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have h5 : ε ≤ e₅ :=
    le_trans hP (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have h6 : ε ≤ e₆ :=
    le_trans hP (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have h7 : ε ≤ e₇ :=
    le_trans hP (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h8 : ε ≤ e₈ :=
    le_trans hP (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have h9 : ε ≤ e₉ := le_trans (min_le_right _ _) (min_le_left _ _)
  have h10 : ε ≤ e₁₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  exact weighted_dominance_ftCoeffPoly_at_of_threshold (e := ε) (h := h) hεpos hhpos
    hA₀ hC₀ hσ₀0 hσ₀1 hA₁ hC₁ hσ₁0 hσ₁1
    (fun θ hθ hθε => hamp₀ θ hθ (le_trans hθε h1))
    (fun θ hθ hθε => hCW₀ θ hθ (le_trans hθε h2))
    (fun θ hθ hθε => hgap₀ θ hθ (le_trans hθε h3))
    (fun A ζ' θ W hθ hθε => hcl₀ A ζ' θ W hθ (le_trans hθε h9))
    (fun M θ hθ hθε => hsplit₀ M θ hθ (le_trans hθε h4))
    (fun η hη hηε => hamp₁ η hη (le_trans hηε h5))
    (fun η hη hηε => hCW₁ η hη (le_trans hηε h6))
    (fun η hη hηε => hgap₁ η hη (le_trans hηε h7))
    (fun A ζ' η W hη hηε => hcl₁ A ζ' η W hη (le_trans hηε h10))
    (fun M η hη hηε => hsplit₁ M η hη (le_trans hηε h8))
    (hint ε hεpos)


/-! ### Discharging the endpoint supplies from the branch

**Differs from the paper's route.**  The paper writes the two endpoints as
separate passages, `θ↓0` and `θ↑π/r`, each with its
own constants.  Here both are covered at once by a **chart** `w : ℝ → ℝ` mapping
the window coordinate to the angle: `w = id` at the lower endpoint, `w = fun η => π/r - η`
at the upper, which is the reflection `eq:retained-range` uses.  Only the objects
indexed by the angle — `z`, `τ`, `ftPrincipalAmp`, `ftRemainder` — are composed
with it; the retained cluster and its enumeration are indexed by the window
coordinate directly. -/

/-- **`hamp` discharged.**  `amplitude_lower_bound_of_endpoint_form` in the named
objects: the branch's endpoint factorization gives the amplitude floor
`Aδ^p ≤ |W|`. -/
theorem ftPrincipalAmp_lower_bound {Q B : Polynomial ℂ} (hB0 : B ≠ 0) {r : ℕ} (hr : 1 ≤ r)
    {z τ w : ℝ → ℝ} {te γe : ℂ} (hte : te ≠ 0) (hγe : γe ≠ 0)
    (hγ0 : ftPrincipal τ (w 0) = te)
    (hγd : HasDerivWithinAt (fun δ => ftPrincipal τ (w δ)) γe (Set.Ici 0) 0)
    (hP : ftDen Q r ((z (w 0) : ℝ) : ℂ) ≠ 0)
    (hk : 1 ≤ (ftDen Q r ((z (w 0) : ℝ) : ℂ)).rootMultiplicity te)
    (hrootev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (ftDen Q r ((z (w δ) : ℝ) : ℂ)).eval (ftPrincipal τ (w δ)) = 0) :
    ∃ A > (0 : ℝ), ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
      A * δ ^ (B.rootMultiplicity te
          - ((ftDen Q r ((z (w 0) : ℝ) : ℂ)).rootMultiplicity te - 1))
        ≤ ftPrincipalAmp Q B r z τ (w δ) :=
  amplitude_lower_bound_of_endpoint_form (γ := fun δ => ftPrincipal τ (w δ))
    (zf := fun δ => ((z (w δ) : ℝ) : ℂ)) hB0 hr hte hγe hγ0 hγd hP hk hrootev

/-- The amplitude floor forces the principal amplitude nonzero on the window,
which is the nonvanishing `cluster_amplitude_window` asks for.  So that input is
derived from the same branch datum, not assumed separately. -/
theorem ftPrincipalAmp_ne_zero_of_lower_bound {Q B : Polynomial ℂ} {r : ℕ} {z τ w : ℝ → ℝ}
    {A e : ℝ} {p : ℕ} (hA : 0 < A) (he : 0 < e)
    (h : ∀ δ : ℝ, 0 < δ → δ ≤ e → A * δ ^ p ≤ ftPrincipalAmp Q B r z τ (w δ)) :
    ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ftAmp Q B r ((z (w δ) : ℝ) : ℂ) (ftPrincipal τ (w δ)) ≠ 0 := by
  have hmem : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ ≤ e := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    exact (continuousAt_id (x := (0 : ℝ))).eventually_le_const he
  have hpos : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ := eventually_mem_nhdsWithin
  filter_upwards [hmem, hpos] with δ hδe hδ
  have hb := h δ hδ hδe
  have : 0 < ftPrincipalAmp Q B r z τ (w δ) := lt_of_lt_of_le (by positivity) hb
  exact norm_pos_iff.mp this

/-- **`hCW` discharged.**  The residue ratios of `eq:lower-residue-ratio` are
unimodular in the limit — `Cluster.norm_clusterAlpha_zpow_ratio`, because all the
cluster directions share one modulus — so `Cluster.eventually_cluster_amplitude_le`
gives `|W_j| ≤ 2|W|` on a window.  The `2` is derived here, never assumed. -/
theorem ftCluster_amplitude_le_two {Q B : Polynomial ℂ} {r : ℕ} {z τ w : ℝ → ℝ}
    {n : ℕ} {g : ℝ → Fin n → ℂ} {L : Fin n → ℂ}
    (hLnorm : ∀ i, ‖L i‖ = 1)
    (hratio : ∀ i, Filter.Tendsto
      (fun δ => ftAmp Q B r ((z (w δ) : ℝ) : ℂ) (g δ i)
        / ftAmp Q B r ((z (w δ) : ℝ) : ℂ) (ftPrincipal τ (w δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L i)))
    (hW : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ftAmp Q B r ((z (w δ) : ℝ) : ℂ) (ftPrincipal τ (w δ)) ≠ 0) :
    ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      ‖ftAmp Q B r ((z (w δ) : ℝ) : ℂ) (g δ i)‖ ≤ 2 * ftPrincipalAmp Q B r z τ (w δ) := by
  have hL : ∀ i ∈ (Finset.univ : Finset (Fin n)), ‖L i‖ = 1 := fun i _ => hLnorm i
  obtain ⟨e, he, hbd⟩ :=
    cluster_amplitude_window (s := (Finset.univ : Finset (Fin n)))
      (W := fun δ => ftAmp Q B r ((z (w δ) : ℝ) : ℂ) (ftPrincipal τ (w δ)))
      (Wf := fun i δ => ftAmp Q B r ((z (w δ) : ℝ) : ℂ) (g δ i)) hW
      (fun i _ => hratio i) hL
  exact ⟨e, he, fun δ hδ hδe i => hbd δ hδ hδe i (Finset.mem_univ i)⟩

/-- **`hsplit` discharged.**  The endpoint split at every parameter of the window,
with one contour constant, in the shape `weighted_dominance_ftCoeffPoly` takes.

Every hypothesis is about the denominator geometry along the branch — the
retained cluster `sfun`, its position strictly inside the circle, its simplicity
and minimality in `|t| ≤ R_0`, the principal pair, and the enumeration of the
`n` nonprincipal members — together with `hCbd`, the paper's contour supremum
`C_Γ = sup_Γ|B/D|`, which `exists_uniform_ftDiv_bound` produces from
continuity and a zero-free circle.  None mentions `F_M` against `W`. -/
theorem ftSplit_of_branch {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0) {z τ w : ℝ → ℝ}
    {n : ℕ} {g : ℝ → Fin n → ℂ} {sfun : ℝ → Finset ℂ}
    {R₀ τmax C σ e : ℝ} (hR₀ : 0 < R₀) (hσ : τmax / R₀ ≤ σ) (hCnn : 0 ≤ C)
    (hτpos : ∀ δ : ℝ, 0 < δ → δ ≤ e → 0 < τ (w δ))
    (hτle : ∀ δ : ℝ, 0 < δ → δ ≤ e → τ (w δ) ≤ τmax)
    (hτR : ∀ δ : ℝ, 0 < δ → δ ≤ e → τ (w δ) ≤ R₀)
    (hroot : ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ a ∈ sfun δ,
      (ftDen Q r ((z (w δ) : ℝ) : ℂ)).eval a = 0)
    (hsimple : ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ a ∈ sfun δ,
      (derivative (ftDen Q r ((z (w δ) : ℝ) : ℂ))).eval a ≠ 0)
    (ha0 : ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ a ∈ sfun δ, a ≠ 0)
    (haR : ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ a ∈ sfun δ, ‖a‖ < R₀)
    (huniq : ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z (w δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun δ)
    (hrootplus : ∀ δ : ℝ, 0 < δ → δ ≤ e →
      (ftDen Q r ((z (w δ) : ℝ) : ℂ)).eval (ftPrincipal τ (w δ)) = 0)
    (hne : ∀ δ : ℝ, 0 < δ → δ ≤ e →
      ftPrincipal τ (w δ) ≠ ((τ (w δ) : ℝ) : ℂ) * Complex.exp (-((w δ : ℝ) : ℂ) * I))
    (hginj : ∀ δ : ℝ, 0 < δ → δ ≤ e → Function.Injective (g δ))
    (hgmem : ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i, g δ i ∈
      ((sfun δ).erase (ftPrincipal τ (w δ))).erase
        (((τ (w δ) : ℝ) : ℂ) * Complex.exp (-((w δ : ℝ) : ℂ) * I)))
    (hgcard : ∀ δ : ℝ, 0 < δ → δ ≤ e →
      (((sfun δ).erase (ftPrincipal τ (w δ))).erase
        (((τ (w δ) : ℝ) : ℂ) * Complex.exp (-((w δ : ℝ) : ℂ) * I))).card = n)
    (hCbd : ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z (w δ) : ℝ) : ℂ)).eval t‖ ≤ C) :
    ∀ (M : ℕ) (δ : ℝ), 0 < δ → δ ≤ e →
      |ftRemainder Q B r z τ M (w δ)|
        ≤ (∑ i, |‖ftAmp Q B r ((z (w δ) : ℝ) : ℂ) (g δ i)‖|
              * ((‖g δ i‖ / τ (w δ)) ^ (M + 1))⁻¹)
          + τmax * C * σ ^ M := by
  refine hsplit_of_indexed_uniform (τ := fun δ => τ (w δ)) (Cθ := fun _ => C) (R₀ := R₀)
    (ε := e) (Rrem := fun M δ => ftRemainder Q B r z τ M (w δ))
    (Wf := fun δ i => ‖ftAmp Q B r ((z (w δ) : ℝ) : ℂ) (g δ i)‖)
    (ζ := fun δ i => ‖g δ i‖ / τ (w δ))
    hR₀ hσ hCnn hτpos hτle (fun _ _ _ => hCnn) (fun _ _ _ => le_rfl) ?_
  intro M δ hδ hδe
  exact endpoint_remainder_split_indexed_of_bound hQ hB hr hQ0 (hτpos δ hδ hδe) hR₀
    (hτR δ hδ hδe) (hroot δ hδ hδe) (hsimple δ hδ hδe) (ha0 δ hδ hδe) (haR δ hδ hδe)
    (huniq δ hδ hδe)
    (hrootplus δ hδ hδe) (hne δ hδ hδe) (g δ) (hginj δ hδ hδe) (hgmem δ hδ hδe)
    (hgcard δ hδ hδe) (hCbd δ hδ hδe) M

/-! ### The compact interior -/

/-- **`eq:interior-remainder`**, and `eq:interior-relative-remainder`'s remainder
half, uniformly.  On the compact interior the retained cluster is the principal
pair alone, so `EndpointDominance.interior_remainder_bound_of_bound` gives `R_M`
directly as the contour error; `tau_geom_le` makes the constant and the ratio
uniform over the region.  The conclusion is `|R_M(θ)| ≤ C_I σ_I^M` with
`C_I = τ_max C` and `σ_I = σ` on `[lo, hi]`, which is the display
`eq:interior-remainder` at `[ε, π/r - ε]`.  This is `hint`'s first component,
derived. -/
theorem interior_remainder_uniform {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0) {z τ : ℝ → ℝ}
    {R₀ τmax C σ lo hi : ℝ} (hR₀ : 0 < R₀) (hσ : τmax / R₀ ≤ σ) (hCnn : 0 ≤ C)
    (hτpos : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi → 0 < τ θ)
    (hτle : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi → τ θ ≤ τmax)
    (hτR : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi → τ θ < R₀)
    (hrootplus : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsp : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0)
    (hsm : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
        (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0)
    (hne : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I))
    (hpair : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
      t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I))
    (hCbd : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z θ : ℝ) : ℂ)).eval t‖ ≤ C) :
    ∀ (M : ℕ) (θ : ℝ), lo ≤ θ → θ ≤ hi →
      |ftRemainder Q B r z τ M θ| ≤ τmax * C * σ ^ M := by
  intro M θ h1 h2
  have hper := interior_remainder_bound_of_bound hQ hB hr hQ0 (hτpos θ h1 h2) hR₀
    (hτR θ h1 h2) (hrootplus θ h1 h2) (hsp θ h1 h2) (hsm θ h1 h2) (hne θ h1 h2)
    (hpair θ h1 h2) (hCbd θ h1 h2) M
  have hg := tau_geom_le hR₀ hσ (hτpos θ h1 h2) (hτle θ h1 h2) hCnn M
  have hnn : (0 : ℝ) ≤ ftRemainder Q B r z τ M θ := norm_nonneg _
  rw [abs_of_nonneg hnn]
  exact le_trans hper hg

/-! ### The amplitude floor off the deleted windows -/

/-- **Paper `eq:amplitude-deletion`, the arithmetic.**  Off the windows
`|θ - θ_j| ≥ e^{-cM/ν_j}`, each factor of the amplitude's zero
divisor is at least `e^{-cM}`, so a lower bound by the divisor becomes the
exponential floor `Ae^{-cJM}`, `J = \#S`.  With `c = \tfrac{1}{2J}log(1/σ)`
this is exactly the `A_Ie^{-(α/2)M}` that `eq:interior-relative-remainder`
consumes — which is *why* the windows are removed, and why their width carries
the `1/ν_j`. -/
theorem amplitude_floor_off_windows {S : Finset ℝ} {ν : ℝ → ℕ} {A c : ℝ} (hA : 0 < A)
    (hν : ∀ θj ∈ S, 1 ≤ ν θj) {W : ℝ → ℝ} {θ : ℝ} (M : ℕ)
    (hprod : A * ∏ θj ∈ S, |θ - θj| ^ ν θj ≤ W θ)
    (hoff : ∀ θj ∈ S, Real.exp (-(c * M / ν θj)) ≤ |θ - θj|) :
    A * Real.exp (-(c * S.card * M)) ≤ W θ := by
  have hterm : ∀ θj ∈ S, Real.exp (-(c * M)) ≤ |θ - θj| ^ ν θj := by
    intro θj hj
    have hνr : (0 : ℝ) < (ν θj : ℝ) := by exact_mod_cast hν θj hj
    have hpow : (Real.exp (-(c * M / ν θj))) ^ ν θj = Real.exp (-(c * M)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    calc Real.exp (-(c * M)) = (Real.exp (-(c * M / ν θj))) ^ ν θj := hpow.symm
      _ ≤ |θ - θj| ^ ν θj := pow_le_pow_left₀ (Real.exp_pos _).le (hoff θj hj) _
  have hprodlb : Real.exp (-(c * S.card * M)) ≤ ∏ θj ∈ S, |θ - θj| ^ ν θj := by
    have hconst : ∏ _θj ∈ S, Real.exp (-(c * M)) = Real.exp (-(c * S.card * M)) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
      congr 1
      ring
    calc Real.exp (-(c * S.card * M)) = ∏ _θj ∈ S, Real.exp (-(c * M)) := hconst.symm
      _ ≤ ∏ θj ∈ S, |θ - θj| ^ ν θj :=
          Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) hterm
  exact le_trans (mul_le_mul_of_nonneg_left hprodlb hA.le) hprod

/-- **`hint` built from its three primitive components.**  The interior supply
that `weighted_dominance_of_windows` consumes: the remainder bound (derived by
`interior_remainder_uniform`), the amplitude's lower bound by its own zero
divisor (derived by `Amplitude.exists_amplitude_divisor_lower_bound`), and the
definition of the deleted windows `eq:amplitude-deletion` at the paper's exponent
`c = \tfrac1{2J}log(1/σ_I)`.

The exponent is forced: `amplitude_floor_off_windows` turns the divisor bound
into `A_Ie^{-cJM}`, and `eq:interior-relative-remainder` wants
`A_Ie^{-(α/2)M}` with `α = log(1/σ_I)`, so `cJ = α/2`.  With
no amplitude zero on the arc the divisor is empty and the floor is the constant
`A_I` itself. -/
theorem hint_of_interior_data_at {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {b e : ℝ}
    {Θ : ℕ → Set ℝ}
    (hdata : ∃ (CI σI AI : ℝ) (S : Finset ℝ) (ν : ℝ → ℕ),
      0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ S, 1 ≤ ν θj) ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e →
        |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
        AI * ∏ θj ∈ S, |θ - θj| ^ ν θj ≤ ftPrincipalAmp Q B r z τ θ) ∧
      (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
        Real.exp (-((-Real.log σI) / (2 * S.card) * M / ν θj)) ≤ |θ - θj|)) :
    ∃ AI CI σI : ℝ, 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        AI * Real.exp (-((-Real.log σI) / 2) * M) ≤ ftPrincipalAmp Q B r z τ θ) := by
  obtain ⟨CI, σI, AI, S, ν, hσ0, hσ1, hA, hν, hrem, hfloor, hwin⟩ := hdata
  have hlogpos : 0 < -Real.log σI := by
    have : Real.log σI < 0 := Real.log_neg hσ0 hσ1
    linarith
  refine ⟨AI, CI, σI, hσ0, hσ1, hA, fun M θ h1 h2 _ => hrem M θ h1 h2,
    fun M θ h1 h2 h3 => ?_⟩
  have hfl := amplitude_floor_off_windows (c := (-Real.log σI) / (2 * S.card)) hA hν M
    (hfloor θ h1 h2) (hwin M θ h3)
  rcases Nat.eq_zero_or_pos S.card with hcard | hcard
  · -- no amplitude zero on the arc: the divisor is empty and the floor is `A_I`
    rw [hcard] at hfl
    have hAI : AI ≤ ftPrincipalAmp Q B r z τ θ := by simpa using hfl
    have hexp : Real.exp (-((-Real.log σI) / 2) * M) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      nlinarith
    nlinarith [hA, hAI, hexp]
  · have hJr : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcard
    have heq : (-Real.log σI) / (2 * (S.card : ℝ)) * (S.card : ℝ) * (M : ℝ)
        = (-Real.log σI) / 2 * (M : ℝ) := by field_simp
    rw [heq] at hfl
    have hsign : -(-Real.log σI / 2 * (M : ℝ)) = -(-Real.log σI / 2) * (M : ℝ) := by ring
    rwa [hsign] at hfl

/-- `hint_of_interior_data_at` at every interior parameter, which is the shape
`weighted_dominance_ftCoeffPoly` consumes. -/
theorem hint_of_interior_data {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {b : ℝ}
    {Θ : ℕ → Set ℝ}
    (hdata : ∀ e : ℝ, 0 < e → ∃ (CI σI AI : ℝ) (S : Finset ℝ) (ν : ℝ → ℕ),
      0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ S, 1 ≤ ν θj) ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e →
        |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
        AI * ∏ θj ∈ S, |θ - θj| ^ ν θj ≤ ftPrincipalAmp Q B r z τ θ) ∧
      (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
        Real.exp (-((-Real.log σI) / (2 * S.card) * M / ν θj)) ≤ |θ - θj|)) :
    ∀ e : ℝ, 0 < e → ∃ AI CI σI : ℝ, 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → θ ∉ Θ M →
        AI * Real.exp (-((-Real.log σI) / 2) * M) ≤ ftPrincipalAmp Q B r z τ θ) :=
  fun e he => hint_of_interior_data_at (hdata e he)

/-- **`lem:amplitude-divisor` on the compact interior, as a conclusion.**
Produces the amplitude's zero set `S`, its orders `ν`, and the local cofactors
`U` — the data `Amplitude.exists_amplitude_divisor_lower_bound` consumes — from
the branch alone.

`S` is finite because `γ` is injective on the arc and carries each amplitude
zero to a zero of `B`, of which there are finitely many; that is
`eq:amplitude-zero-count`'s mechanism, and `Amplitude.amplitude_zero_count` is
the count it supports.  `ν` is `B`'s root multiplicity at the branch point,
positive exactly because the zero is a zero.  `U` comes from
`Amplitude.exists_amplitude_factor_on`, one cofactor per zero, chosen with a junk
value off `S` so the family is an honest `ℝ → ℝ → ℂ`.

The branch inputs are `thm:FT-geometry`'s: injectivity, a nonvanishing derivative
(`γ'(θ) = e^{iθ}(τ' + iτ) ≠ 0`), continuity of `z`, and the
principal root being a simple denominator zero throughout the arc. -/
theorem exists_interior_amplitude_data {Q B : Polynomial ℂ} (hB0 : B ≠ 0) {r : ℕ}
    {z τ : ℝ → ℝ} {e hi : ℝ}
    (hγinj : Set.InjOn (ftPrincipal τ) (Set.Icc e hi))
    (hγd : ∀ θ ∈ Set.Icc e hi, ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ)
    (hzc : ∀ θ ∈ Set.Icc e hi, ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ)
    (hroot : ∀ θ ∈ Set.Icc e hi, (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsimple : ∀ θ ∈ Set.Icc e hi,
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) :
    ∃ (S : Finset ℝ) (ν : ℝ → ℕ) (U : ℝ → ℝ → ℂ),
      (∀ θj ∈ S, 1 ≤ ν θj) ∧ (↑S ⊆ Set.Icc e hi) ∧
      (∀ θ ∈ Set.Icc e hi,
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S) ∧
      (∀ θj ∈ S, ContinuousWithinAt (U θj) (Set.Icc e hi) θj) ∧
      (∀ θj ∈ S, U θj θj ≠ 0) ∧
      (∀ θj ∈ S, ∀ θ ∈ Set.Icc e hi,
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
          = (((θ - θj : ℝ)) : ℂ) ^ ν θj * U θj θ) := by
  classical
  set Z : Set ℝ :=
    {θ | θ ∈ Set.Icc e hi ∧ ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0} with hZdef
  -- the amplitude vanishes exactly where `B` does along the branch
  have hBzero : ∀ θ ∈ Z, B.eval (ftPrincipal τ θ) = 0 := by
    intro θ hθ
    exact (ftAmp_eq_zero_iff (hroot θ hθ.1) (hsimple θ hθ.1)).mp hθ.2
  -- `Z` injects into the zeros of `B`, hence is finite
  have hfinimg : ((fun θ => ftPrincipal τ θ) '' Z).Finite := by
    refine Set.Finite.subset (B.roots.toFinset.finite_toSet) ?_
    rintro w ⟨θ, hθ, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hB0).mpr (hBzero θ hθ)
  have hZfin : Z.Finite :=
    Set.Finite.of_finite_image hfinimg (hγinj.mono fun θ hθ => hθ.1)
  set S : Finset ℝ := hZfin.toFinset with hSdef
  have hmemS : ∀ θ : ℝ, θ ∈ S ↔ θ ∈ Z := by
    intro θ; rw [hSdef, Set.Finite.mem_toFinset]
  set ν : ℝ → ℕ := fun θj => B.rootMultiplicity (ftPrincipal τ θj) with hνdef
  -- one cofactor per zero, junk off `S`
  have hex : ∀ θj : ℝ, ∃ u : ℝ → ℂ, θj ∈ S →
      (ContinuousWithinAt u (Set.Icc e hi) θj ∧ u θj ≠ 0 ∧
        ∀ θ ∈ Set.Icc e hi, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
          = (((θ - θj : ℝ)) : ℂ) ^ ν θj * u θ) := by
    intro θj
    by_cases hj : θj ∈ S
    · have hjZ := (hmemS θj).mp hj
      obtain ⟨γ', hγ'0, hγ'⟩ := hγd θj hjZ.1
      obtain ⟨u, hu1, hu2, hu3⟩ :=
        exists_amplitude_factor_on (Q := Q) (B := B) (r := r)
          (zf := fun θ' => ((z θ' : ℝ) : ℂ)) hB0 hγ' hγ'0 (hzc θj hjZ.1) hroot hsimple hjZ.1
      exact ⟨u, fun _ => ⟨hu1, hu2, hu3⟩⟩
    · exact ⟨fun _ => 0, fun hc => absurd hc hj⟩
  choose U hU using hex
  refine ⟨S, ν, U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θj hj
    have hjZ := (hmemS θj).mp hj
    exact (Polynomial.rootMultiplicity_pos hB0).mpr (hBzero θj hjZ)
  · intro θ hθ
    exact ((hmemS θ).mp hθ).1
  · intro θ hθ h0
    exact (hmemS θ).mpr ⟨hθ, h0⟩
  · exact fun θj hj => (hU θj hj).1
  · exact fun θj hj => (hU θj hj).2.1
  · exact fun θj hj => (hU θj hj).2.2

/-- **The cofactors alone, for a zero set the caller has already named.**  Same
content as `exists_interior_amplitude_data`, but with `S` supplied rather than
built — which is what a caller needs when the deleted windows `Θ` are
*defined* from `S` and its multiplicities, as `eq:amplitude-deletion` defines
them, so `S` has to exist before `Θ` does.  `ν` is still not a parameter:
it is `B`'s root multiplicity along the branch. -/
theorem exists_interior_amplitude_factors {Q B : Polynomial ℂ} (hB0 : B ≠ 0) {r : ℕ}
    {z τ : ℝ → ℝ} {e hi : ℝ} {S : Finset ℝ}
    (hSsub : ↑S ⊆ Set.Icc e hi)
    (hSzero : ∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0)
    (hγd : ∀ θ ∈ Set.Icc e hi, ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ)
    (hzc : ∀ θ ∈ Set.Icc e hi, ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ)
    (hroot : ∀ θ ∈ Set.Icc e hi, (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsimple : ∀ θ ∈ Set.Icc e hi,
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) :
    ∃ U : ℝ → ℝ → ℂ,
      (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal τ θj)) ∧
      (∀ θj ∈ S, ContinuousWithinAt (U θj) (Set.Icc e hi) θj) ∧
      (∀ θj ∈ S, U θj θj ≠ 0) ∧
      (∀ θj ∈ S, ∀ θ ∈ Set.Icc e hi,
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
          = (((θ - θj : ℝ)) : ℂ) ^ B.rootMultiplicity (ftPrincipal τ θj) * U θj θ) ∧
      ContinuousOn (fun θ => ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ))
        (Set.Icc e hi) := by
  classical
  have hBzero : ∀ θj ∈ S, B.eval (ftPrincipal τ θj) = 0 := by
    intro θj hj
    exact (ftAmp_eq_zero_iff (hroot θj (hSsub hj)) (hsimple θj (hSsub hj))).mp (hSzero θj hj)
  have hex : ∀ θj : ℝ, ∃ u : ℝ → ℂ, θj ∈ S →
      (ContinuousWithinAt u (Set.Icc e hi) θj ∧ u θj ≠ 0 ∧
        ∀ θ ∈ Set.Icc e hi, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
          = (((θ - θj : ℝ)) : ℂ) ^ B.rootMultiplicity (ftPrincipal τ θj) * u θ) := by
    intro θj
    by_cases hj : θj ∈ S
    · obtain ⟨γ', hγ'0, hγ'⟩ := hγd θj (hSsub hj)
      obtain ⟨u, hu1, hu2, hu3⟩ :=
        exists_amplitude_factor_on (Q := Q) (B := B) (r := r)
          (zf := fun θ' => ((z θ' : ℝ) : ℂ)) hB0 hγ' hγ'0 (hzc θj (hSsub hj)) hroot hsimple
          (hSsub hj)
      exact ⟨u, fun _ => ⟨hu1, hu2, hu3⟩⟩
    · exact ⟨fun _ => 0, fun hc => absurd hc hj⟩
  choose U hU using hex
  have hWc : ContinuousOn (fun θ => ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ))
      (Set.Icc e hi) := by
    intro θ hθ
    obtain ⟨γ', -, hγ'⟩ := hγd θ hθ
    have hγc : ContinuousAt (ftPrincipal τ) θ := hγ'.continuousAt
    have hden : ContinuousAt
        (fun θ' => (derivative (ftDen Q r ((z θ' : ℝ) : ℂ))).eval (ftPrincipal τ θ')) θ :=
      continuousAt_eval_derivative_ftDen hγc (hzc θ hθ)
    have hnum : ContinuousAt (fun θ' => -B.eval (ftPrincipal τ θ')) θ :=
      (((Polynomial.continuous B).continuousAt).comp hγc).neg
    have heq : Set.EqOn (fun θ' => ftAmp Q B r ((z θ' : ℝ) : ℂ) (ftPrincipal τ θ'))
        (fun θ' => -B.eval (ftPrincipal τ θ')
          / (derivative (ftDen Q r ((z θ' : ℝ) : ℂ))).eval (ftPrincipal τ θ'))
        (Set.Icc e hi) :=
      fun θ' hθ' => ftAmp_eq_neg_div_derivative (hroot θ' hθ')
    exact ContinuousWithinAt.congr ((hnum.div hden (hsimple θ hθ)).continuousWithinAt)
      heq (heq hθ)
  exact ⟨U, fun θj hj => (Polynomial.rootMultiplicity_pos hB0).mpr (hBzero θj hj),
    fun θj hj => (hU θj hj).1, fun θj hj => (hU θj hj).2.1,
    fun θj hj => (hU θj hj).2.2, hWc⟩

/-- **The interior supply, before any window is imposed.**  The two facts
`prop:angular-discrepancy` actually consumes on the compact interior: the
remainder decays geometrically, and the amplitude is bounded below by its own
divisor (`lem:amplitude-divisor`).  Neither mentions `Θ`.

Separating them from the window is what lets the deleted family be chosen after
the interior parameter rather than before it: the constants here are those of the
*given* `e`, so a caller that fixes `e` first gets a fixed `σ`, and the window
`eq:amplitude-deletion` builds from it shrinks with `M` instead of being pinned
to the worst `e`. -/
theorem interior_data_of_geometry {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0) {z τ : ℝ → ℝ}
    {b e : ℝ}
    {R₀ τmax σ : ℝ} {S : Finset ℝ} (hB0 : B ≠ 0)
    (hR₀ : 0 < R₀) (hσ : τmax / R₀ ≤ σ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    -- the interior remainder inputs
    (hτpos : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e → 0 < τ θ)
    (hτle : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e → τ θ ≤ τmax)
    (hτR : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e → τ θ < R₀)
    (hrootplus : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsp : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0)
    (hsm : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
        (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0)
    (hne : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
      ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I))
    (hpair : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
      t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I))
    -- the amplitude's zero set, which `eq:amplitude-deletion` defines `Θ` from
    (hSsub : ↑S ⊆ Set.Icc e (b - e))
    (hSzero : ∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0)
    (hzeros : ∀ θ ∈ Set.Icc e (b - e),
      ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S)
    -- the branch inputs `lem:amplitude-divisor` runs on
    (hγd : ∀ θ ∈ Set.Icc e (b - e), ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ)
    (hzc : ∀ θ ∈ Set.Icc e (b - e), ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ)
    :
    ∃ (CI σI AI : ℝ), 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e →
        |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
        AI * ∏ θj ∈ S, |θ - θj| ^ (B.rootMultiplicity (ftPrincipal τ θj))
          ≤ ftPrincipalAmp Q B r z τ θ) ∧
      (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal τ θj)) ∧ σI = σ := by
  -- the contour constant, produced on the compact interior rather than assumed
  have hzcOn : ContinuousOn (fun θ : ℝ => ((z θ : ℝ) : ℂ)) (Set.Icc e (b - e)) :=
    fun θ hθ => (hzc θ hθ).continuousWithinAt
  have hDne : ∀ θ ∈ Set.Icc e (b - e), ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval t ≠ 0 := by
    intro θ hθ t ht hzero
    have hnt : ‖t‖ = R₀ := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 ht
    have hτθ : 0 < τ θ := hτpos θ hθ.1 hθ.2
    have hnp : ‖ftPrincipal τ θ‖ = τ θ := by
      rw [ftPrincipal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτθ,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hnm : ‖((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)‖ = τ θ := by
      rw [← conj_polar (τ θ) θ, RCLike.norm_conj, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hτθ, Complex.norm_exp_ofReal_mul_I, mul_one]
    rcases hpair θ hθ.1 hθ.2 t hnt.le hzero with rfl | rfl
    · rw [hnp] at hnt; exact absurd hnt (hτR θ hθ.1 hθ.2).ne
    · rw [hnm] at hnt; exact absurd hnt (hτR θ hθ.1 hθ.2).ne
  obtain ⟨C, hCnn, hCbd'⟩ :=
    exists_uniform_ftDiv_bound (Q := Q) (B := B) (r := r) (R₀ := R₀) (z := z)
      (a := e) (b := b - e) hzcOn hDne
  have hCbd : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z θ : ℝ) : ℂ)).eval t‖ ≤ C :=
    fun θ h1 h2 t ht => hCbd' θ ⟨h1, h2⟩ t ht
  have hrootI : ∀ θ ∈ Set.Icc e (b - e),
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0 :=
    fun θ hθ => hrootplus θ hθ.1 hθ.2
  have hsimpleI : ∀ θ ∈ Set.Icc e (b - e),
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0 :=
    fun θ hθ => hsp θ hθ.1 hθ.2
  obtain ⟨U, hν, hUc, hU0, hUeq, hWc⟩ :=
    exists_interior_amplitude_factors hB0 hSsub hSzero hγd hzc hrootI hsimpleI
  obtain ⟨A, hA, hfloor⟩ :=
    exists_amplitude_divisor_lower_bound (a := e) (b := b - e)
      (W := fun θ => ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)) (S := S)
      (ν := fun θj => B.rootMultiplicity (ftPrincipal τ θj)) (U := U)
      hWc hSsub hzeros hUc hU0 hUeq
  refine ⟨τmax * C, σ, A, hσ0, hσ1, hA, ?_, ?_, hν, rfl⟩
  · exact interior_remainder_uniform hQ hB hr hQ0 hR₀ hσ hCnn hτpos hτle hτR hrootplus hsp
      hsm hne hpair hCbd
  · intro θ h1 h2
    exact hfloor θ ⟨h1, h2⟩


/-- **One entry of `hint`'s input, built from the primitives.**  At a fixed
window `[ε, b-ε]`: the remainder bound comes from
`interior_remainder_uniform` (the retained cluster there is the principal pair
alone), and the amplitude's lower bound by its own zero divisor from
`Amplitude.exists_amplitude_divisor_lower_bound`.  Only the definition of the
deleted windows is carried.

`σ_I` is the interior contour ratio and `C_I = τ_{max}C_Γ`; both
constants are produced here rather than assumed — `C_Γ` by
`exists_uniform_ftDiv_bound` on the compact interior, where `τ(θ) < R_0`
keeps the principal pair off the circle, and `A_I` by the collar decomposition of
`Amplitude.exists_amplitude_divisor_lower_bound`.

The window clause `eq:amplitude-deletion` is the only thing this adds to
`interior_data_of_geometry`, which carries the two facts that do not mention
`Θ`. -/
theorem hdata_entry_of_interior {Q B : Polynomial ℂ} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0) {z τ : ℝ → ℝ}
    {b e : ℝ} {Θ : ℕ → Set ℝ}
    {R₀ τmax σ : ℝ} {S : Finset ℝ} (hB0 : B ≠ 0)
    (hR₀ : 0 < R₀) (hσ : τmax / R₀ ≤ σ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    -- the interior remainder inputs
    (hτpos : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e → 0 < τ θ)
    (hτle : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e → τ θ ≤ τmax)
    (hτR : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e → τ θ < R₀)
    (hrootplus : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsp : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0)
    (hsm : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
        (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0)
    (hne : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
      ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I))
    (hpair : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
      t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I))
    -- the amplitude's zero set, which `eq:amplitude-deletion` defines `Θ` from
    (hSsub : ↑S ⊆ Set.Icc e (b - e))
    (hSzero : ∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0)
    (hzeros : ∀ θ ∈ Set.Icc e (b - e),
      ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S)
    -- the branch inputs `lem:amplitude-divisor` runs on
    (hγd : ∀ θ ∈ Set.Icc e (b - e), ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ)
    (hzc : ∀ θ ∈ Set.Icc e (b - e), ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ)
    -- the deleted windows
    (hwin : ∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
      Real.exp (-((-Real.log σ) / (2 * S.card) * M
        / (B.rootMultiplicity (ftPrincipal τ θj)))) ≤ |θ - θj|) :
    ∃ (CI σI AI : ℝ) (S' : Finset ℝ) (ν' : ℝ → ℕ),
      0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ S', 1 ≤ ν' θj) ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e →
        |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
        AI * ∏ θj ∈ S', |θ - θj| ^ ν' θj ≤ ftPrincipalAmp Q B r z τ θ) ∧
      (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S',
        Real.exp (-((-Real.log σI) / (2 * S'.card) * M / ν' θj)) ≤ |θ - θj|) := by
  obtain ⟨CI, σI, AI, hσ0', hσ1', hA', hrem, hfloor, hν, hσeq⟩ :=
    interior_data_of_geometry hQ hB hr hQ0 hB0 hR₀ hσ hσ0 hσ1 hτpos hτle hτR hrootplus
      hsp hsm hne hpair hSsub hSzero hzeros hγd hzc
  refine ⟨CI, σI, AI, S, fun θj => B.rootMultiplicity (ftPrincipal τ θj),
    hσ0', hσ1', hA', hν, hrem, hfloor, ?_⟩
  rw [hσeq]
  exact hwin

/-! ### From a fixed deleted window to `eq:amplitude-deletion`'s shrinking one

`weighted_dominance_of_branch` asks for its window inequality inside
`hinterior`'s `∀ e`, while using it at a single `e`.  A witness must therefore
meet it at arbitrarily small `e`, where the interior contraction ratio `σ(e)`
tends to `1`; the constant `c = (-log σ(e))/(2|S|)` of `eq:amplitude-deletion`
tends to `0` with it, and the half-width `e^{-cM/ν_j}` it forces tends to a fixed
positive number rather than shrinking.  That is why an admissible `Θ` can be
forced `M`-independent.

The repair is not to make `Θ` depend on `e`.  Pinning the conclusion at
`e = h/M` -- the shape the mismatch note in `weighted_dominance_ftCoeffPoly`
proposes -- does not help: `-log σ(h/M)` is then itself of order `1/M`, so
`c·M` tends to a constant and the half-width again does not shrink.  What
removes it is fixing the interior parameter **first**, which is what
`subsec:proof` does: it chooses `ε` with every amplitude zero inside
`(ε, π/r - ε)` before `M` is quantified, so `σ(ε)` is one constant and
`eq:amplitude-deletion` is exponentially small in `M`.

This theorem is that step, stated once and pencil-independently.  It takes a
dominance bound off any **fixed** window and the interior supply of
`interior_data_of_geometry` at one fixed `e`, and returns dominance off a window
of half-width `h/M`.  The conclusion of the fixed-window theorem is not
weakened -- it is consumed. -/

/-- **`eq:retained-range` with the amplitude windows shrinking.**  Given
`eq:dominance-bound` off a fixed window about the amplitude zeros, plus the
interior remainder bound and the divisor floor of `lem:amplitude-divisor` on one
fixed subinterval containing them, the deleted windows may be taken of half-width
`h/M`.

The content of the upgrade is that an exponential beats a polynomial: on the
band, the floor is `A(h/M)^{∑ν}` and the remainder is `Cσ^M`. -/
theorem dominance_shrinking_of_fixed_window
    {Rrem : ℕ → ℝ → ℝ} {Wamp : ℝ → ℝ} {Θ : ℕ → Set ℝ} {S : Finset ℝ} {ν : ℝ → ℕ}
    {b e CI σI AI : ℝ}
    (hσI0 : 0 < σI) (hσI1 : σI < 1) (hAI : 0 < AI) (_hCI : 0 ≤ CI)
    (_hnn : ∀ (M : ℕ) (θ : ℝ), 0 ≤ Rrem M θ)
    (hfixed : ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M → Rrem M θ ≤ Wamp θ / 2)
    (hcover : ∀ (M : ℕ) (θ : ℝ), (∀ θj ∈ S, 1 ≤ |θ - θj|) → θ ∉ Θ M)
    (hnear : ∀ θ : ℝ, ∀ θj ∈ S, |θ - θj| < 1 → e ≤ θ ∧ θ ≤ b - e)
    (hrem : ∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ b - e → Rrem M θ ≤ CI * σI ^ M)
    (hfloor : ∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
      AI * ∏ θj ∈ S, |θ - θj| ^ ν θj ≤ Wamp θ) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → (∀ θj ∈ S, h / M ≤ |θ - θj|) →
        Rrem M θ ≤ Wamp θ / 2 := by
  classical
  obtain ⟨hd, hhd, Md, hdomFixed⟩ := hfixed
  set N : ℕ := ∑ θj ∈ S, ν θj with hN
  have hlim : Filter.Tendsto (fun M : ℕ => CI * ((M : ℝ) ^ N * σI ^ M))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one N hσI0.le hσI1).const_mul CI
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.1
    (hlim.eventually_le_const (show (0 : ℝ) < AI / 2 by positivity))
  refine ⟨max hd 1, lt_of_lt_of_le one_pos (le_max_right _ _), max (max Md M₁) 1,
    fun M hM θ h1 h2 h3 => ?_⟩
  have hMd : Md ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMone' : M₁ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMone : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMone
  have hhle : hd ≤ max hd 1 := le_max_left _ _
  have h1le : (1 : ℝ) ≤ max hd 1 := le_max_right _ _
  have hMNpos : (0 : ℝ) < (M : ℝ) ^ N := by positivity
  by_cases hband : ∀ θj ∈ S, (1 : ℝ) ≤ |θ - θj|
  · -- outside the fixed window: the hypothesis, verbatim
    have hmono := div_le_div_of_nonneg_right hhle hMpos.le
    exact hdomFixed M hMd θ (le_trans hmono h1) (by linarith [h2]) (hcover M θ hband)
  · -- the band: the floor is polynomial in `1/M` and the remainder is not
    push Not at hband
    obtain ⟨θj, hθj, hlt⟩ := hband
    obtain ⟨hθ1, hθ2⟩ := hnear θ θj hθj hlt
    -- the divisor floor, evaluated on the band
    have hprod : (max hd 1 / (M : ℝ)) ^ N ≤ ∏ θk ∈ S, |θ - θk| ^ ν θk := by
      rw [hN, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun i _ => by positivity) (fun i hi => ?_)
      exact pow_le_pow_left₀ (by positivity) (h3 i hi) _
    have hlow : AI * (max hd 1) ^ N / (M : ℝ) ^ N
        ≤ AI * ∏ θk ∈ S, |θ - θk| ^ ν θk := by
      rw [mul_div_assoc, ← div_pow]
      exact mul_le_mul_of_nonneg_left hprod hAI.le
    have hkey : CI * σI ^ M * (2 * (M : ℝ) ^ N) ≤ AI * (max hd 1) ^ N := by
      have hMn := hM₁ M hMone'
      have hHpow : (1 : ℝ) ≤ (max hd 1) ^ N := one_le_pow₀ h1le
      nlinarith [hMn, hHpow, hAI.le, hMNpos]
    have hdiv : CI * σI ^ M ≤ AI * (max hd 1) ^ N / (2 * (M : ℝ) ^ N) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hkey]
    have heq : AI * (max hd 1) ^ N / (2 * (M : ℝ) ^ N)
        = (AI * (max hd 1) ^ N / (M : ℝ) ^ N) / 2 := by
      field_simp
    rw [heq] at hdiv
    linarith [hfloor θ hθ1 hθ2, hlow, hdiv, hrem M θ hθ1 hθ2]

end ForgacsTran
