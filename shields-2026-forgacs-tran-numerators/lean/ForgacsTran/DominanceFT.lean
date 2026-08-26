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
# The endpoint supplies derived, and `thm:weighted-dominance` for `F_M`

`DominanceAssembly.weighted_dominance` proves the theorem over abstract
`Rrem`/`Wamp`.  This module discharges the supplies the tree can prove and states
the theorem at the paper's own objects.

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
* `hdata_entry_of_interior` — one entry of the interior supply from primitives:
  the remainder bound from `interior_remainder_uniform`, the cofactors from
  `exists_interior_amplitude_factors`, and the floor from
  `Amplitude.exists_amplitude_divisor_lower_bound`.
* `weighted_dominance_of_branch` — **the corollary with the composition
  performed.**  `hamp`, `hCW`, `hsplit` and `hint` are gone from the binder list:
  they are applied, not assumed, and so are `eq:endpoint-linear-gap` and
  `eq:lower-residue-ratio` — both are our paper's extractions from Prop. 3, not
  Prop. 3 itself, so what is assumed in their place is the endpoint *expansion*
  `ζ_j(δ) = 1 + c_jδ + O(δ²)` and the leading behavior of `B` and `∂_tD` along
  each branch.  What survives is the Forgács--Tran branch data, the uniform
  contour bounds, and the definition of the deleted windows.

## Implementation notes

**What each surviving hypothesis is.**  `eq:endpoint-linear-gap` and
`eq:lower-residue-ratio` are **not** among them.  The manuscript's proof of
`thm:FT-geometry` says Prop. 3 of `Forgacs2017RationalDenominator` supplies the
endpoint *expansion* and that "we extract the uniform separation asserted above",
so the gap is our step, not the cited one; and Forgács--Tran state nothing about
residue ratios at all.  Both are therefore derived here — the gap from the
expansion through `Geometry.endpoint_linear_coeff_pos` and
`Geometry.exists_endpoint_linear_gap`, the ratio from the leading behavior of `B`
and `∂_tD` through `Cluster.tendsto_residue_ratio_cluster`.

The two steps that were ours and undischarged are now discharged too.  The
uniform contour constant comes from `EndpointDominance.exists_uniform_ftDiv_bound`
— `B/D` is continuous on the compact `[0,e] × \{|t| = R_0\}` and so bounded there.
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

**Containment.**  The conclusion relates `ftRemainder` to `ftPrincipalAmp`.  No
explicit binder mentions either, and none mentions `ftCoeffPoly`, which is the
whole of `ftRemainder`'s coefficient side — so no hypothesis can be the
conclusion in disguise.  Exactly one binder, `hinterior`, mentions `ftAmp`, and
only to say which `θ` its zero set contains and that the deleted windows
avoid them; it relates the amplitude to nothing.  **The endpoint binders are one-sided, and the two
halves take different
domains.**  `hγ`/`hγd`/`hγd₀`/`hγd₁` are `HasDerivWithinAt … (Set.Ici 0) 0`;
`hroot`/`hrootev`/`hrootev₀`/`hrootev₁` are `∀ᶠ δ in 𝓝[>] 0`.  Not uniform, and
deliberately so: the derivative needs the endpoint *in* its domain, because
`Amplitude.amplitude_endpoint_form` returns `V`'s value and continuity **at** the
endpoint; the eventual conditions must exclude it, because every conclusion
downstream already does and including it would smuggle in a condition `hk`
supplies separately.

They were two-sided until measured.  `τ` sees `θ` only through `cos`, hence is
even, so the one-sided difference quotients at the endpoint are exact negatives —
both `∓1/√3`, differing by `1.135`, a corner rather than a derivative
(`scripts/check_endpoint_derivative_onesided.py`).  The manuscript agrees:
`lem:principal-endpoint-regularity` extends the branch to a regular arc on the
**closed** `[0, π/r]` with `δ` the angular *distance* to the endpoint, so `δ ≥ 0`
throughout and no two-sided statement is ever claimed.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`,
`subsec:weighted-dominance`, `thm:weighted-dominance`, `eq:dominance-bound`,
`eq:retained-range`, `lem:amplitude-divisor`, `eq:lower-residue-ratio`).

## Tags

weighted dominance, endpoint supply, Forgacs-Tran branch
-/

set_option linter.style.longFile 2900

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
constrained only by `hcl₀` and `hcl₁` — `WeightedDominance.exists_cluster_threshold`'s
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
    -- why `CubicWitness.cubicWitness_window_forced` can force it `M`-independent
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

/-! ### `thm:weighted-dominance` on the branch alone -/

/-- **`thm:weighted-dominance` against the interior *data* rather than the geometry
that would produce it.**  Every endpoint binder is unchanged; what moves is the
interior antecedent, which is now `hdata_entry_of_interior`'s conclusion — the
remainder bound, the amplitude floor over a divisor, and the deleted-window
clause — in place of the fixed-circle block that theorem consumes.

The distinction is not presentational, and from `3 ≤ r` it is the difference
between a satisfiable antecedent and an unsatisfiable one.  The block asks for
**one** separating radius across the whole compact interior,
`sup τ < R_0 < inf(third modulus)`, while `thm:FT-geometry` gives only the
pointwise ratio `third(θ) ≥ (1+c)τ(θ)`, at one angle at a time.

Whether the two agree is decided by `n_1 = r - 2`, the count of **non-principal**
members of the cluster that collapses into the origin at the upper endpoint.  At
`r = 2` that count is zero: the principal pair is the whole collapsing set,
nothing non-principal runs into the origin with `τ`, the third modulus stays
`O(1)`, and `sup τ` and `inf third` are attained at the *same* angle — so the
fixed form reduces to the pointwise ratio and asks nothing extra.  From `r = 3` a
non-principal member collapses too, `inf third → 0` at the upper end while
`sup τ` sits at the lower one, and no radius separates them.

`check_interior_fixed_radius_higher_r.py` asserts that split rather than
describing it, over pencils with the smallest zero repeated: above `1` in every
row at `r = 2`, below `1` in every row at `r ≥ 3`, with the pointwise ratio
holding throughout.

So the data form is the one a caller can meet at every `r`.  Its constants
reassemble over a finite cover through
`InteriorSeparation.interior_data_of_pieces`, and one radius per piece is what the
geometry does supply. -/
theorem weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data {Q B : Polynomial ℂ}
    (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {b : ℝ} {z τ : ℝ → ℝ}
    {n₀ n₁ : ℕ} {g₀ : ℝ → Fin n₀ → ℂ} {g₁ : ℝ → Fin n₁ → ℂ}
    {sfun₀ sfun₁ : ℝ → Finset ℂ}
    {x₁ : ℝ} (hx₁ : 0 < x₁) {ρ : ℕ} (hρ : 0 < n₀ → 2 ≤ ρ)
    -- lower endpoint: the endpoint factorization
    {te₀ γe₀ : ℂ} (hte₀ : te₀ ≠ 0) (hγe₀ : γe₀ ≠ 0)
    (hγ0₀ : ftPrincipal τ 0 = te₀)
    (hγd₀ : HasDerivWithinAt (fun δ => ftPrincipal τ δ) γe₀ (Set.Ici 0) 0)
    (hk₀ : 1 ≤ (ftDen Q r ((z 0 : ℝ) : ℂ)).rootMultiplicity te₀)
    (hrootev₀ : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    -- lower endpoint: the residue ratio
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    {idx₀ : Fin n₀ → ℕ} {jp₀ : ℕ} {νB₀ : ℕ} {cB₀ cQ₀ : ℂ}
    (hcB₀ : 0 < n₀ → cB₀ ≠ 0) (hcQ₀ : 0 < n₀ → cQ₀ ≠ 0)
    (hBj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => B.eval (g₀ δ i) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ (idx₀ i) ^ νB₀)))
    (hBp₀ : 0 < n₀ → Filter.Tendsto
      (fun δ : ℝ => B.eval (ftPrincipal τ δ) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ jp₀ ^ νB₀)))
    (hEj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (g₀ δ i)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ (idx₀ i) ^ (ρ - 1))))
    (hEp₀ : 0 < n₀ → Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (ftPrincipal τ δ)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ jp₀ ^ (ρ - 1))))
    -- lower endpoint: the retained cluster and the contour bound
    {R₀ τmax₀ σ₀ e₀ : ℝ} (hR₀ : 0 < R₀) (hσ₀ : τmax₀ / R₀ ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (he₀ : 0 < e₀)
    (hτpos₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → 0 < τ δ)
    (hτle₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → τ δ ≤ τmax₀)
    (hroot₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval a = 0)
    (hsimple₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval a ≠ 0)
    (haR₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ, ‖a‖ < R₀)
    (huniq₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₀ δ)
    (hrootplus₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    (hne₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ftPrincipal τ δ ≠ ((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))
    (hginj₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → Function.Injective (g₀ δ))
    (hgmem₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ i, g₀ δ i ∈
      ((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)))
    (hgcard₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))).card = n₀)
    -- the separating circle, zero-free across the closed window, and the branch
    -- parameter continuous on it: `eq:contour-remainder-bound`'s constant is
    -- produced from these two by compactness, not assumed uniform
    -- the contour bound enters as the punctured statement the proof uses, not as
    -- the closed-window data one route happens to derive it from.  Taken here at
    -- the lower endpoint too, where the closed form IS meetable: a theorem whose
    -- two endpoints take different kinds of input is what lets an upper binder be
    -- built by symmetry with a lower one and come out false.
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hCbd₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z δ : ℝ) : ℂ)).eval t‖ ≤ C₀)
    -- upper endpoint: the same, through the chart `η ↦ b - η`
    -- the upper endpoint enters as the amplitude bound itself, not as a route to
    -- it: `weighted_dominance_ftCoeffPoly` already takes `p₁` abstractly, and the
    -- endpoint group's only use here was to obtain this.  Which route proves it
    -- depends on `r` — the finite one at `r = 1`, where `γ(0) ≠ 0`, and the origin
    -- one at `r ≥ 2`, where `FTBranchUpperRefutation` proves `γ(0) = 0`.
    {p₁ : ℕ} {A₁ : ℝ} (hA₁ : 0 < A₁)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    -- `eq:upper-residue-ratio`.  At the upper endpoint the amplitude ratio is a
    -- ratio of NORMALIZED ROOTS, `W_j/W = ζ_j/ζ_+(1+O(τ))`, and its limit has
    -- modulus one because the `ζ` tend to the `r`th roots of `-1`.  This is NOT
    -- the lower endpoint's cluster ratio: `B(0) ≠ 0`, so `B` does not vanish on
    -- this cluster, and no `clusterAlpha`, no `ν_B` and no `ρ-1` enters.  The
    -- cluster is empty unless `r ≥ 2`, which the supplied gap carries.
    {L₁ : Fin n₁ → ℂ}
    (hL₁ : ∀ i : Fin n₁, ‖L₁ i‖ = 1)
    (hratio₁ : ∀ i : Fin n₁, Filter.Tendsto
      (fun δ : ℝ => ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (g₁ (b - δ) i)
        / ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (ftPrincipal τ (b - δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L₁ i)))
    {R₁ τmax₁ σ₁ e₁ : ℝ} (hR₁ : 0 < R₁) (hσ₁ : τmax₁ / R₁ ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (he₁ : 0 < e₁)
    (hτpos₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → 0 < τ (b - δ))
    (hτle₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → τ (b - δ) ≤ τmax₁)
    (hroot₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval a = 0)
    (hsimple₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (derivative (ftDen Q r ((z (b - δ) : ℝ) : ℂ))).eval a ≠ 0)
    (haR₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ, ‖a‖ < R₁)
    (huniq₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t : ℂ, ‖t‖ ≤ R₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₁ δ)
    (hrootplus₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval (ftPrincipal τ (b - δ)) = 0)
    (hne₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      ftPrincipal τ (b - δ) ≠ ((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))
    (hginj₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → Function.Injective (g₁ (b - δ)))
    (hgmem₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ i, g₁ (b - δ) i ∈
      ((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I)))
    (hgcard₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))).card = n₁)
    -- the contour bound enters as the punctured statement the proof uses.  The
    -- closed-window form is not merely stronger than needed here: at `r ≥ 2` it is
    -- unmeetable, because `z` is unbounded as `δ → 0` and a continuous function on
    -- a compact set is bounded; and at the one pencil where it IS discharged, it
    -- passes without probing the endpoint at all — at `δ = 0` the junk value of `z`
    -- leaves `Q` alone, whose zero misses the sphere, so it holds by Lean's
    -- division-by-zero convention rather than by the geometry.  A binder that holds
    -- for a reason unrelated to what it was written to test is not evidence, and
    -- looks exactly like evidence.
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hCbd₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
      ‖B.eval t / (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁)
    -- `eq:endpoint-linear-gap` at both endpoints, and the threshold it feeds.
    -- The bundled form extracts the two gap rates from the expansion of
    -- `[Prop.~3]` and then produces `h` from them; here all three are inputs.
    -- None of the four hypotheses names `B`, the amplitude, or the remainder, so
    -- one threshold serves every numerator over a fixed denominator.
    {c₀ c₁ h : ℝ} (hhpos : 0 < h)
    (hgapin₀ : ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₀ * δ ≤ ‖g₀ δ i‖ / τ δ)
    (hgapin₁ : ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₁ * δ ≤ ‖g₁ (b - δ) i‖ / τ (b - δ))
    (hcl₀ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₀ → ℝ) (θ W : ℝ), 0 < θ → θ ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), 1 + c₀ * θ ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * θ →
          ∑ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    (hcl₁ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₁ → ℝ) (η W : ℝ), 0 < η → η ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), 1 + c₁ * η ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * η →
          ∑ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W) :
    ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
      (∃ (CI σI AI : ℝ) (Sd : Finset ℝ) (νd : ℝ → ℕ),
        0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ Sd, 1 ≤ νd θj) ∧
        (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ b - ε →
          |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
          AI * ∏ θj ∈ Sd, |θ - θj| ^ νd θj ≤ ftPrincipalAmp Q B r z τ θ) ∧
        (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ Sd,
          Real.exp (-((-Real.log σI) / (2 * Sd.card) * M / νd θj)) ≤ |θ - θj|)) →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
          ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  -- Four binders the others already force, constructed rather than carried.
  -- `0` is not a denominator zero, because `D(0,z) = Q(0) ≠ 0` once `r ≥ 1`;
  -- and `τ` stays inside the separating circle because `τmax/R ≤ σ < 1`.
  have hzero_not_root : ∀ zz : ℝ, (ftDen Q r ((zz : ℝ) : ℂ)).eval 0 ≠ 0 := by
    intro zz hev
    rw [ftDen_eval, zero_pow (by omega : r ≠ 0), mul_zero, add_zero] at hev
    exact hQ0 hev
  have hP₀ : ftDen Q r ((z 0 : ℝ) : ℂ) ≠ 0 := by
    intro h
    exact hzero_not_root (z 0) (by rw [h]; simp)
  have hP₁ : ftDen Q r ((z (b - 0) : ℝ) : ℂ) ≠ 0 := by
    intro h
    exact hzero_not_root (z (b - 0)) (by rw [h]; simp)
  have ha0₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ, a ≠ 0 := by
    intro δ hδ hδe a haS h0
    exact hzero_not_root (z δ) (h0 ▸ hroot₀ δ hδ hδe a haS)
  have ha0₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ, a ≠ 0 := by
    intro δ hδ hδe a haS h0
    exact hzero_not_root (z (b - δ)) (h0 ▸ hroot₁ δ hδ hδe a haS)
  have hτmR₀ : τmax₀ ≤ R₀ := by
    have h1 : τmax₀ / R₀ < 1 := lt_of_le_of_lt hσ₀ hσ₀1
    rw [div_lt_one hR₀] at h1
    linarith
  have hτmR₁ : τmax₁ ≤ R₁ := by
    have h1 : τmax₁ / R₁ < 1 := lt_of_le_of_lt hσ₁ hσ₁1
    rw [div_lt_one hR₁] at h1
    linarith
  have hτR₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → τ δ ≤ R₀ :=
    fun δ hδ hδe => le_trans (hτle₀ δ hδ hδe) hτmR₀
  have hτR₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → τ (b - δ) ≤ R₁ :=
    fun δ hδ hδe => le_trans (hτle₁ δ hδ hδe) hτmR₁
  -- the amplitude floors
  obtain ⟨A₀, hA₀, ea₀, hea₀, hamp₀⟩ :=
    ftPrincipalAmp_lower_bound (w := id) hB0 hr hte₀ hγe₀ hγ0₀ hγd₀ hP₀ hk₀ hrootev₀
  obtain ⟨ea₁, hea₁, hamp₁⟩ := hamp₁
  -- six sign conditions the other binders already force
  have hτmax₀ : 0 ≤ τmax₀ :=
    le_trans (hτpos₀ e₀ he₀ le_rfl).le (hτle₀ e₀ he₀ le_rfl)
  have hτmax₁ : 0 ≤ τmax₁ :=
    le_trans (hτpos₁ e₁ he₁ le_rfl).le (hτle₁ e₁ he₁ le_rfl)
  have hσ₀0 : 0 ≤ σ₀ := le_trans (by positivity) hσ₀
  have hσ₁0 : 0 ≤ σ₁ := le_trans (by positivity) hσ₁
  -- `eq:contour-remainder-bound`'s constant, produced on each closed endpoint
  -- window rather than assumed uniform there
  -- `eq:lower-residue-ratio`, from `Cluster.tendsto_residue_ratio_cluster`
  have hδne : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((δ : ℝ) : ℂ) ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin] with δ hδ
    exact_mod_cast ne_of_gt hδ
  have hamp_eq : ∀ (zz : ℝ) (t : ℂ), (ftDen Q r ((zz : ℝ) : ℂ)).eval t = 0 →
      ftAmp Q B r ((zz : ℝ) : ℂ) t
        = -B.eval t / (derivative (ftDen Q r ((zz : ℝ) : ℂ))).eval t := by
    intro zz t ht
    rw [ftAmp_eq_derivative ht, neg_div]
  have hratio₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ => ftAmp Q B r ((z δ : ℝ) : ℂ) (g₀ δ i)
        / ftAmp Q B r ((z δ : ℝ) : ℂ) (ftPrincipal τ δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((clusterAlpha x₁ ρ (idx₀ i) / clusterAlpha x₁ ρ jp₀)
        ^ ((νB₀ : ℤ) - ((ρ - 1 : ℕ) : ℤ)))) := by
    intro i
    have hn₀ : 0 < n₀ := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hρi : 2 ≤ ρ := hρ hn₀
    have hcore := tendsto_residue_ratio_cluster (ν := νB₀) (k := ρ - 1)
      (aj := clusterAlpha x₁ ρ (idx₀ i)) (ap := clusterAlpha x₁ ρ jp₀)
      (hcB₀ hn₀) (hcQ₀ hn₀) (clusterAlpha_ne_zero hx₁ hρi _)
      (clusterAlpha_ne_zero hx₁ hρi _) hδne (hBj₀ i) (hBp₀ hn₀) (hEj₀ i) (hEp₀ hn₀)
    refine hcore.congr' ?_
    have hmem : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ ∧ δ ≤ e₀ := by
      have h1 : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ ≤ e₀ :=
        eventually_nhdsWithin_of_eventually_nhds
          ((continuousAt_id (x := (0 : ℝ))).eventually_le_const he₀)
      filter_upwards [eventually_mem_nhdsWithin, h1] with δ h2 h3
      exact ⟨h2, h3⟩
    filter_upwards [hmem] with δ hδ
    have hgm := hgmem₀ δ hδ.1 hδ.2 i
    have hgs : g₀ δ i ∈ sfun₀ δ :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hgm)
    rw [hamp_eq (z δ) (g₀ δ i) (hroot₀ δ hδ.1 hδ.2 _ hgs),
      hamp_eq (z δ) (ftPrincipal τ δ) (hrootplus₀ δ hδ.1 hδ.2)]
  -- the residue comparisons
  obtain ⟨ec₀, hec₀, hCW₀⟩ :=
    ftCluster_amplitude_le_two (w := id) (g := g₀)
      (L := fun i => (clusterAlpha x₁ ρ (idx₀ i) / clusterAlpha x₁ ρ jp₀)
        ^ ((νB₀ : ℤ) - ((ρ - 1 : ℕ) : ℤ)))
      (fun i => norm_clusterAlpha_zpow_ratio hx₁
        (hρ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)) (idx₀ i) jp₀ _) hratio₀
      (ftPrincipalAmp_ne_zero_of_lower_bound (w := id) hA₀ hea₀ hamp₀)
  obtain ⟨ec₁, hec₁, hCW₁⟩ :=
    ftCluster_amplitude_le_two (w := fun δ => b - δ) (g := fun δ => g₁ (b - δ))
      (L := L₁) hL₁ hratio₁
      (ftPrincipalAmp_ne_zero_of_lower_bound (w := fun δ => b - δ) hA₁ hea₁ hamp₁)
  -- `eq:endpoint-linear-gap`, supplied rather than extracted, and the cluster
  -- threshold at those two rates
  obtain ⟨eg₀, heg₀, hgap₀'⟩ := hgapin₀
  obtain ⟨eg₁, heg₁, hgap₁'⟩ := hgapin₁
  obtain ⟨ecl₀, hecl₀, hcl₀'⟩ := hcl₀
  obtain ⟨ecl₁, hecl₁, hcl₁'⟩ := hcl₁
  -- the endpoint splits
  have hsp₀ := ftSplit_of_branch (w := id) (g := g₀) (sfun := sfun₀) hQ hB hr hQ0 hR₀ hσ₀
    hC₀ hτpos₀ hτle₀ hτR₀ hroot₀ hsimple₀ ha0₀ haR₀ huniq₀ hrootplus₀ hne₀ hginj₀ hgmem₀
    hgcard₀ hCbd₀
  have hsp₁ := ftSplit_of_branch (w := fun δ => b - δ) (g := fun δ => g₁ (b - δ))
    (sfun := sfun₁) hQ hB hr
    hQ0 hR₁ hσ₁ hC₁ hτpos₁ hτle₁ hτR₁ hroot₁ hsimple₁ ha0₁ haR₁ huniq₁ hrootplus₁ hne₁ hginj₁
    hgmem₁ hgcard₁ hCbd₁
  -- the eight endpoint windows, reconciled once; `ε` is what the theorem hands
  -- back, so a caller learns the interior parameter BEFORE choosing `Θ`.
  set εA : ℝ :=
    min (min (min (min ea₀ ec₀) (min eg₀ e₀)) (min (min ea₁ ec₁) (min eg₁ e₁)))
      (min ecl₀ ecl₁) with hεA
  have hεApos : 0 < εA := by
    rw [hεA]; repeat' apply lt_min
    all_goals assumption
  have kP : εA ≤ min (min (min ea₀ ec₀) (min eg₀ e₀)) (min (min ea₁ ec₁) (min eg₁ e₁)) :=
    min_le_left _ _
  have k1 : εA ≤ ea₀ :=
    le_trans kP (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have k2 : εA ≤ ec₀ :=
    le_trans kP (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have k3 : εA ≤ eg₀ :=
    le_trans kP (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have k4 : εA ≤ e₀ :=
    le_trans kP (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have k5 : εA ≤ ea₁ :=
    le_trans kP (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have k6 : εA ≤ ec₁ :=
    le_trans kP (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have k7 : εA ≤ eg₁ :=
    le_trans kP (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have k8 : εA ≤ e₁ :=
    le_trans kP (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have k9 : εA ≤ ecl₀ := le_trans (min_le_right _ _) (min_le_left _ _)
  have k10 : εA ≤ ecl₁ := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨εA, hεApos, fun Θ hdata => ?_⟩
  exact weighted_dominance_ftCoeffPoly_at_of_threshold (e := εA) (h := h) hεApos hhpos
    (Wf₀ := fun δ i => ‖ftAmp Q B r ((z δ : ℝ) : ℂ) (g₀ δ i)‖)
    (ζ₀ := fun δ i => ‖g₀ δ i‖ / τ δ)
    (Wf₁ := fun θ i => ‖ftAmp Q B r ((z θ : ℝ) : ℂ) (g₁ θ i)‖)
    (ζ₁ := fun θ i => ‖g₁ θ i‖ / τ θ)
    hA₀ (mul_nonneg hτmax₀ hC₀) hσ₀0 hσ₀1
    hA₁ (mul_nonneg hτmax₁ hC₁) hσ₁0 hσ₁1
    (fun θ hθ hθe => hamp₀ θ hθ (le_trans hθe k1))
    (fun θ hθ hθe i => by
      have := hCW₀ θ hθ (le_trans hθe k2) i
      rwa [abs_of_nonneg (norm_nonneg _)])
    (fun θ hθ hθe => hgap₀' θ hθ (le_trans hθe k3))
    (fun A ζ' θ W hθ hθe => hcl₀' A ζ' θ W hθ (le_trans hθe k9))
    (fun M θ hθ hθe => hsp₀ M θ hθ (le_trans hθe k4))
    (fun η hη hηe => hamp₁ η hη (le_trans hηe k5))
    (fun η hη hηe i => by
      have := hCW₁ η hη (le_trans hηe k6) i
      rwa [abs_of_nonneg (norm_nonneg _)])
    (fun η hη hηe => hgap₁' η hη (le_trans hηe k7))
    (fun A ζ' η W hη hηe => hcl₁' A ζ' η W hη (le_trans hηe k10))
    (fun M η hη hηe => hsp₁ M η hη (le_trans hηe k8))
    (hint_of_interior_data_at hdata)

/-- **`weighted_dominance_of_branch_any_multiplicity_at` with the threshold an
input.**  The gap rates of `eq:endpoint-linear-gap` and the threshold `h` they
feed are parameters here, not constants manufactured inside.  That is the
paper's own order: `h` is a function of the denominator and `r` alone, and the
numerator enters only at `M_0`.  With `h` produced under the numerator's binder
the statement cannot say so, and a caller reading a numerator-uniform constant
off it is reading something the type does not carry.

Four hypotheses replace the two expansion groups the bundled form carries: the
two linear gaps, which `exists_endpoint_linear_gap_of_expansion_on` and
`exists_endpoint_linear_gap_of_norm_on` supply from those same expansions, and
the two cluster bounds, which are
`WeightedDominance.exists_cluster_threshold`'s conclusion at those rates.  None
of the four names `B`, `ftAmp`, `ftPrincipalAmp` or `ftRemainder`.

**Containment.**  As in the bundled form, no binder names `ftRemainder`, so no
binder relates the two sides of the conclusion.  The four new ones name only the

This is now the data form above, composed with `hdata_entry_of_interior`.  The
statement is unchanged, so every consumer of it is unchanged; what the derivation
records is that the fixed-circle block is *sufficient* for the interior input and
not necessary — and at `2 ≤ r` it is not available, which is why the data form is
the one the branch composition uses.
cluster moduli `‖g₀ δ i‖ / τ δ` and abstract amplitude-gap data. -/
theorem weighted_dominance_of_branch_any_multiplicity_at_of_threshold {Q B : Polynomial ℂ}
    (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {b : ℝ} {z τ : ℝ → ℝ}
    {n₀ n₁ : ℕ} {g₀ : ℝ → Fin n₀ → ℂ} {g₁ : ℝ → Fin n₁ → ℂ}
    {sfun₀ sfun₁ : ℝ → Finset ℂ}
    {x₁ : ℝ} (hx₁ : 0 < x₁) {ρ : ℕ} (hρ : 0 < n₀ → 2 ≤ ρ)
    -- lower endpoint: the endpoint factorization
    {te₀ γe₀ : ℂ} (hte₀ : te₀ ≠ 0) (hγe₀ : γe₀ ≠ 0)
    (hγ0₀ : ftPrincipal τ 0 = te₀)
    (hγd₀ : HasDerivWithinAt (fun δ => ftPrincipal τ δ) γe₀ (Set.Ici 0) 0)
    (hk₀ : 1 ≤ (ftDen Q r ((z 0 : ℝ) : ℂ)).rootMultiplicity te₀)
    (hrootev₀ : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    -- lower endpoint: the residue ratio
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    {idx₀ : Fin n₀ → ℕ} {jp₀ : ℕ} {νB₀ : ℕ} {cB₀ cQ₀ : ℂ}
    (hcB₀ : 0 < n₀ → cB₀ ≠ 0) (hcQ₀ : 0 < n₀ → cQ₀ ≠ 0)
    (hBj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => B.eval (g₀ δ i) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ (idx₀ i) ^ νB₀)))
    (hBp₀ : 0 < n₀ → Filter.Tendsto
      (fun δ : ℝ => B.eval (ftPrincipal τ δ) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ jp₀ ^ νB₀)))
    (hEj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (g₀ δ i)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ (idx₀ i) ^ (ρ - 1))))
    (hEp₀ : 0 < n₀ → Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (ftPrincipal τ δ)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ jp₀ ^ (ρ - 1))))
    -- lower endpoint: the retained cluster and the contour bound
    {R₀ τmax₀ σ₀ e₀ : ℝ} (hR₀ : 0 < R₀) (hσ₀ : τmax₀ / R₀ ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (he₀ : 0 < e₀)
    (hτpos₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → 0 < τ δ)
    (hτle₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → τ δ ≤ τmax₀)
    (hroot₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval a = 0)
    (hsimple₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval a ≠ 0)
    (haR₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ, ‖a‖ < R₀)
    (huniq₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₀ δ)
    (hrootplus₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    (hne₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ftPrincipal τ δ ≠ ((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))
    (hginj₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → Function.Injective (g₀ δ))
    (hgmem₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ i, g₀ δ i ∈
      ((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)))
    (hgcard₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))).card = n₀)
    -- the separating circle, zero-free across the closed window, and the branch
    -- parameter continuous on it: `eq:contour-remainder-bound`'s constant is
    -- produced from these two by compactness, not assumed uniform
    -- the contour bound enters as the punctured statement the proof uses, not as
    -- the closed-window data one route happens to derive it from.  Taken here at
    -- the lower endpoint too, where the closed form IS meetable: a theorem whose
    -- two endpoints take different kinds of input is what lets an upper binder be
    -- built by symmetry with a lower one and come out false.
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hCbd₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z δ : ℝ) : ℂ)).eval t‖ ≤ C₀)
    -- upper endpoint: the same, through the chart `η ↦ b - η`
    -- the upper endpoint enters as the amplitude bound itself, not as a route to
    -- it: `weighted_dominance_ftCoeffPoly` already takes `p₁` abstractly, and the
    -- endpoint group's only use here was to obtain this.  Which route proves it
    -- depends on `r` — the finite one at `r = 1`, where `γ(0) ≠ 0`, and the origin
    -- one at `r ≥ 2`, where `FTBranchUpperRefutation` proves `γ(0) = 0`.
    {p₁ : ℕ} {A₁ : ℝ} (hA₁ : 0 < A₁)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    -- `eq:upper-residue-ratio`.  At the upper endpoint the amplitude ratio is a
    -- ratio of NORMALIZED ROOTS, `W_j/W = ζ_j/ζ_+(1+O(τ))`, and its limit has
    -- modulus one because the `ζ` tend to the `r`th roots of `-1`.  This is NOT
    -- the lower endpoint's cluster ratio: `B(0) ≠ 0`, so `B` does not vanish on
    -- this cluster, and no `clusterAlpha`, no `ν_B` and no `ρ-1` enters.  The
    -- cluster is empty unless `r ≥ 2`, which the supplied gap carries.
    {L₁ : Fin n₁ → ℂ}
    (hL₁ : ∀ i : Fin n₁, ‖L₁ i‖ = 1)
    (hratio₁ : ∀ i : Fin n₁, Filter.Tendsto
      (fun δ : ℝ => ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (g₁ (b - δ) i)
        / ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (ftPrincipal τ (b - δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L₁ i)))
    {R₁ τmax₁ σ₁ e₁ : ℝ} (hR₁ : 0 < R₁) (hσ₁ : τmax₁ / R₁ ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (he₁ : 0 < e₁)
    (hτpos₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → 0 < τ (b - δ))
    (hτle₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → τ (b - δ) ≤ τmax₁)
    (hroot₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval a = 0)
    (hsimple₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (derivative (ftDen Q r ((z (b - δ) : ℝ) : ℂ))).eval a ≠ 0)
    (haR₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ, ‖a‖ < R₁)
    (huniq₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t : ℂ, ‖t‖ ≤ R₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₁ δ)
    (hrootplus₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval (ftPrincipal τ (b - δ)) = 0)
    (hne₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      ftPrincipal τ (b - δ) ≠ ((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))
    (hginj₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → Function.Injective (g₁ (b - δ)))
    (hgmem₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ i, g₁ (b - δ) i ∈
      ((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I)))
    (hgcard₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))).card = n₁)
    -- the contour bound enters as the punctured statement the proof uses.  The
    -- closed-window form is not merely stronger than needed here: at `r ≥ 2` it is
    -- unmeetable, because `z` is unbounded as `δ → 0` and a continuous function on
    -- a compact set is bounded; and at the one pencil where it IS discharged, it
    -- passes without probing the endpoint at all — at `δ = 0` the junk value of `z`
    -- leaves `Q` alone, whose zero misses the sphere, so it holds by Lean's
    -- division-by-zero convention rather than by the geometry.  A binder that holds
    -- for a reason unrelated to what it was written to test is not evidence, and
    -- looks exactly like evidence.
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hCbd₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
      ‖B.eval t / (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁)
    -- `eq:endpoint-linear-gap` at both endpoints, and the threshold it feeds.
    -- The bundled form extracts the two gap rates from the expansion of
    -- `[Prop.~3]` and then produces `h` from them; here all three are inputs.
    -- None of the four hypotheses names `B`, the amplitude, or the remainder, so
    -- one threshold serves every numerator over a fixed denominator.
    {c₀ c₁ h : ℝ} (hhpos : 0 < h)
    (hgapin₀ : ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₀ * δ ≤ ‖g₀ δ i‖ / τ δ)
    (hgapin₁ : ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₁ * δ ≤ ‖g₁ (b - δ) i‖ / τ (b - δ))
    (hcl₀ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₀ → ℝ) (θ W : ℝ), 0 < θ → θ ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), 1 + c₀ * θ ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * θ →
          ∑ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    (hcl₁ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₁ → ℝ) (η W : ℝ), 0 < η → η ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), 1 + c₁ * η ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * η →
          ∑ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W) :
    ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
      (∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
      0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → 0 < τ θ) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → τ θ ≤ τmi) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → τ θ < Ri) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
          (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → ∀ t : ℂ, ‖t‖ ≤ Ri →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
        t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
      (↑S ⊆ Set.Icc ε (b - ε)) ∧
      (∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0) ∧
      (∀ θ ∈ Set.Icc ε (b - ε),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S) ∧
      (∀ θ ∈ Set.Icc ε (b - ε), ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ) ∧
      (∀ θ ∈ Set.Icc ε (b - ε), ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ) ∧
      (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
        Real.exp (-((-Real.log σi) / (2 * S.card) * M
          / (B.rootMultiplicity (ftPrincipal τ θj)))) ≤ |θ - θj|)) →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
          ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  obtain ⟨ε, hε, H⟩ :=
    weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data (h := h)
      hQ hB hB0 hr hQ0 hx₁ hρ hte₀ hγe₀ hγ0₀ hγd₀ hk₀ hrootev₀ hcB₀ hcQ₀ hBj₀ hBp₀ hEj₀ hEp₀ hR₀
      hσ₀ hσ₀1 he₀ hτpos₀ hτle₀ hroot₀ hsimple₀ haR₀ huniq₀ hrootplus₀ hne₀ hginj₀ hgmem₀ hgcard₀
      hC₀ hCbd₀ hA₁ hamp₁ hL₁ hratio₁ hR₁ hσ₁ hσ₁1 he₁ hτpos₁ hτle₁ hroot₁ hsimple₁ haR₁ huniq₁
      hrootplus₁ hne₁ hginj₁ hgmem₁ hgcard₁ hC₁ hCbd₁ hhpos hgapin₀ hgapin₁ hcl₀ hcl₁
  refine ⟨ε, hε, fun Θ hinterior => ?_⟩
  obtain ⟨Ri, τmi, σi, S, hRi, hσi, hσi0, hσi1, hτposI, hτleI,
    hτRI, hrpI, hspI, hsmI, hneeI, hpairI, hSsubI, hSzeroI, hzerosI, hγdI, hzcI,
    hwinI⟩ := hinterior
  exact H Θ (hdata_entry_of_interior hQ hB hr hQ0 hB0 hRi hσi hσi0 hσi1 hτposI
    hτleI hτRI hrpI hspI hsmI hneeI hpairI hSsubI hSzeroI hzerosI hγdI hzcI hwinI)

/-- **`thm:weighted-dominance` with the interior parameter handed back.**  The
theorem produces the `ε` it will use — the reconciliation of the eight endpoint
windows — and only then asks for the interior data, at that one `ε`, for a
deleted family `Θ` chosen afterwards.

That order is `subsec:proof`'s and it is what BANK-37's residue asks for.  In
`weighted_dominance_of_branch_any_multiplicity` the deleted family is bound
*before* `hinterior`'s `∀ e`, so one `Θ` has to serve every interior parameter,
and at a pencil whose branch radius climbs to `1` that forces it
`M`-independent.  Here `Θ` is quantified inside, after `ε` is known, so it has to
serve one interior parameter and the caller may build it out of that `ε`'s own
`σ`.  Nothing in the endpoint group mentions `Θ`, which is why `ε` can be
produced before it.

`weighted_dominance_of_branch_any_multiplicity` is this theorem applied at the
`ε` it returns, and its signature is unchanged. -/
theorem weighted_dominance_of_branch_any_multiplicity_at {Q B : Polynomial ℂ}
    (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {b : ℝ} {z τ : ℝ → ℝ}
    {n₀ n₁ : ℕ} {g₀ : ℝ → Fin n₀ → ℂ} {g₁ : ℝ → Fin n₁ → ℂ}
    {sfun₀ sfun₁ : ℝ → Finset ℂ}
    {x₁ : ℝ} (hx₁ : 0 < x₁) {ρ : ℕ} (hρ : 0 < n₀ → 2 ≤ ρ)
    -- lower endpoint: the endpoint factorization
    {te₀ γe₀ : ℂ} (hte₀ : te₀ ≠ 0) (hγe₀ : γe₀ ≠ 0)
    (hγ0₀ : ftPrincipal τ 0 = te₀)
    (hγd₀ : HasDerivWithinAt (fun δ => ftPrincipal τ δ) γe₀ (Set.Ici 0) 0)
    (hk₀ : 1 ≤ (ftDen Q r ((z 0 : ℝ) : ℂ)).rootMultiplicity te₀)
    (hrootev₀ : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    -- lower endpoint: the residue ratio
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    {idx₀ : Fin n₀ → ℕ} {jp₀ : ℕ} {νB₀ : ℕ} {cB₀ cQ₀ : ℂ}
    (hcB₀ : 0 < n₀ → cB₀ ≠ 0) (hcQ₀ : 0 < n₀ → cQ₀ ≠ 0)
    (hBj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => B.eval (g₀ δ i) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ (idx₀ i) ^ νB₀)))
    (hBp₀ : 0 < n₀ → Filter.Tendsto
      (fun δ : ℝ => B.eval (ftPrincipal τ δ) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ jp₀ ^ νB₀)))
    (hEj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (g₀ δ i)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ (idx₀ i) ^ (ρ - 1))))
    (hEp₀ : 0 < n₀ → Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (ftPrincipal τ δ)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ jp₀ ^ (ρ - 1))))
    -- lower endpoint: the retained cluster and the contour bound
    {R₀ τmax₀ σ₀ e₀ : ℝ} (hR₀ : 0 < R₀) (hσ₀ : τmax₀ / R₀ ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (he₀ : 0 < e₀)
    (hτpos₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → 0 < τ δ)
    (hτle₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → τ δ ≤ τmax₀)
    (hroot₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval a = 0)
    (hsimple₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval a ≠ 0)
    (haR₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ, ‖a‖ < R₀)
    (huniq₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₀ δ)
    (hrootplus₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    (hne₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ftPrincipal τ δ ≠ ((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))
    (hginj₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → Function.Injective (g₀ δ))
    (hgmem₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ i, g₀ δ i ∈
      ((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)))
    (hgcard₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))).card = n₀)
    -- the separating circle, zero-free across the closed window, and the branch
    -- parameter continuous on it: `eq:contour-remainder-bound`'s constant is
    -- produced from these two by compactness, not assumed uniform
    -- the contour bound enters as the punctured statement the proof uses, not as
    -- the closed-window data one route happens to derive it from.  Taken here at
    -- the lower endpoint too, where the closed form IS meetable: a theorem whose
    -- two endpoints take different kinds of input is what lets an upper binder be
    -- built by symmetry with a lower one and come out false.
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hCbd₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z δ : ℝ) : ℂ)).eval t‖ ≤ C₀)
    -- `eq:endpoint-linear-gap` is *not* assumed: Prop. 3 supplies the expansion
    -- `ζ_j(δ) = 1 + c_jδ + O(δ²)`, and the uniform gap is our extraction from it
    {Cexp₀ : ℝ} (hCexp₀ : 0 ≤ Cexp₀)
    (hωne₀ : ∀ i : Fin n₀, clusterOmega ρ (idx₀ i)
      ≠ Complex.exp (((Real.pi / ρ : ℝ) : ℂ) * I))
    (hωne'₀ : ∀ i : Fin n₀, clusterOmega ρ (idx₀ i)
      ≠ Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * I))
    (hexp₀ : ∀ i : Fin n₀, ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ‖g₀ δ i / ((τ δ : ℝ) : ℂ)
        - (1 + ((((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx₀ i))
            / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) * (δ : ℂ))‖ ≤ Cexp₀ * δ ^ 2)
    -- upper endpoint: the same, through the chart `η ↦ b - η`
    -- the upper endpoint enters as the amplitude bound itself, not as a route to
    -- it: `weighted_dominance_ftCoeffPoly` already takes `p₁` abstractly, and the
    -- endpoint group's only use here was to obtain this.  Which route proves it
    -- depends on `r` — the finite one at `r = 1`, where `γ(0) ≠ 0`, and the origin
    -- one at `r ≥ 2`, where `FTBranchUpperRefutation` proves `γ(0) = 0`.
    {p₁ : ℕ} {A₁ : ℝ} (hA₁ : 0 < A₁)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    -- `eq:upper-residue-ratio`.  At the upper endpoint the amplitude ratio is a
    -- ratio of NORMALIZED ROOTS, `W_j/W = ζ_j/ζ_+(1+O(τ))`, and its limit has
    -- modulus one because the `ζ` tend to the `r`th roots of `-1`.  This is NOT
    -- the lower endpoint's cluster ratio: `B(0) ≠ 0`, so `B` does not vanish on
    -- this cluster, and no `clusterAlpha`, no `ν_B` and no `ρ-1` enters.  The
    -- cluster is empty unless `r ≥ 2`, which is `hn₁r`.
    {idx₁ : Fin n₁ → ℕ} {L₁ : Fin n₁ → ℂ}
    (hn₁r : 0 < n₁ → 2 ≤ r)
    (hL₁ : ∀ i : Fin n₁, ‖L₁ i‖ = 1)
    (hratio₁ : ∀ i : Fin n₁, Filter.Tendsto
      (fun δ : ℝ => ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (g₁ (b - δ) i)
        / ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (ftPrincipal τ (b - δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L₁ i)))
    {R₁ τmax₁ σ₁ e₁ : ℝ} (hR₁ : 0 < R₁) (hσ₁ : τmax₁ / R₁ ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (he₁ : 0 < e₁)
    (hτpos₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → 0 < τ (b - δ))
    (hτle₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → τ (b - δ) ≤ τmax₁)
    (hroot₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval a = 0)
    (hsimple₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (derivative (ftDen Q r ((z (b - δ) : ℝ) : ℂ))).eval a ≠ 0)
    (haR₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ, ‖a‖ < R₁)
    (huniq₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t : ℂ, ‖t‖ ≤ R₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₁ δ)
    (hrootplus₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval (ftPrincipal τ (b - δ)) = 0)
    (hne₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      ftPrincipal τ (b - δ) ≠ ((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))
    (hginj₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → Function.Injective (g₁ (b - δ)))
    (hgmem₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ i, g₁ (b - δ) i ∈
      ((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I)))
    (hgcard₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))).card = n₁)
    -- the contour bound enters as the punctured statement the proof uses.  The
    -- closed-window form is not merely stronger than needed here: at `r ≥ 2` it is
    -- unmeetable, because `z` is unbounded as `δ → 0` and a continuous function on
    -- a compact set is bounded; and at the one pencil where it IS discharged, it
    -- passes without probing the endpoint at all — at `δ = 0` the junk value of `z`
    -- leaves `Q` alone, whose zero misses the sphere, so it holds by Lean's
    -- division-by-zero convention rather than by the geometry.  A binder that holds
    -- for a reason unrelated to what it was written to test is not evidence, and
    -- looks exactly like evidence.
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hCbd₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
      ‖B.eval t / (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁)
    -- `eq:endpoint-linear-gap` is *not* assumed: Prop. 3 supplies the expansion
    -- `ζ_j(δ) = 1 + c_jδ + O(δ²)`, and the uniform gap is our extraction from it
    {Cexp₁ : ℝ} (hCexp₁ : 0 ≤ Cexp₁)
    (hωne₁ : ∀ i : Fin n₁, clusterOmega r (idx₁ i)
      ≠ Complex.exp (((Real.pi / r : ℝ) : ℂ) * I))
    (hωne'₁ : ∀ i : Fin n₁, clusterOmega r (idx₁ i)
      ≠ Complex.exp (((-(Real.pi / r) : ℝ) : ℂ) * I))
    -- the MODULUS form: at the upper endpoint `ζ_j → ω_j`, an `r`th root of `-1`,
    -- not to `1`, so only `‖ζ_j‖` expands about `1`.  `eq:endpoint-linear-gap`'s
    -- upper display is a modulus in the manuscript and the two endpoints do not
    -- share expansion shape any more than they share residue geometry.
    (hexp₁ : ∀ i : Fin n₁, ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      |‖g₁ (b - δ) i / ((τ (b - δ) : ℝ) : ℂ)‖
        - (1 + ((Real.cos (Real.pi / r) - (clusterOmega r (idx₁ i)).re)
            / Real.sin (Real.pi / r)) * δ)| ≤ Cexp₁ * δ ^ 2) :
    ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
      (∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
      0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → 0 < τ θ) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → τ θ ≤ τmi) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → τ θ < Ri) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
          (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → ∀ t : ℂ, ‖t‖ ≤ Ri →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
        t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
      (↑S ⊆ Set.Icc ε (b - ε)) ∧
      (∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0) ∧
      (∀ θ ∈ Set.Icc ε (b - ε),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S) ∧
      (∀ θ ∈ Set.Icc ε (b - ε), ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ) ∧
      (∀ θ ∈ Set.Icc ε (b - ε), ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ) ∧
      (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
        Real.exp (-((-Real.log σi) / (2 * S.card) * M
          / (B.rootMultiplicity (ftPrincipal τ θj)))) ≤ |θ - θj|)) →
      ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
          ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  -- `eq:endpoint-linear-gap`, extracted from the expansion of `[Prop.~3]`
  obtain ⟨c₀, hc₀, δg₀, hδg₀, hgapraw₀⟩ :=
    exists_endpoint_linear_gap_of_expansion_on (J := (Finset.univ : Finset (Fin n₀)))
      (ζ := fun i δ => g₀ δ i / ((τ δ : ℝ) : ℂ))
      (c := fun i => (((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx₀ i))
        / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ))
      hCexp₀ he₀ (fun i _ => by
        have hρi : 2 ≤ ρ := hρ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)
        rw [endpoint_expansion_coeff_re]
        exact endpoint_linear_coeff_pos hρi (clusterOmega_pow (by omega : 1 ≤ ρ) _)
          (hωne₀ i) (hωne'₀ i)) (fun i _ => hexp₀ i)
  obtain ⟨c₁, hc₁, δg₁, hδg₁, hgapraw₁⟩ :=
    exists_endpoint_linear_gap_of_norm_on (J := (Finset.univ : Finset (Fin n₁)))
      (ζ := fun i δ => g₁ (b - δ) i / ((τ (b - δ) : ℝ) : ℂ))
      (cf := fun i => (Real.cos (Real.pi / r) - (clusterOmega r (idx₁ i)).re)
        / Real.sin (Real.pi / r))
      hCexp₁ he₁ (fun i _ =>
        endpoint_linear_coeff_pos (hn₁r (lt_of_le_of_lt (Nat.zero_le _) i.isLt))
          (clusterOmega_pow hr _) (hωne₁ i) (hωne'₁ i)) (fun i _ => hexp₁ i)
  have hgap₀ : ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₀ * δ ≤ ‖g₀ δ i‖ / τ δ := by
    refine ⟨min (δg₀ / 2) e₀, lt_min (by linarith) he₀, fun δ hδ hδe i => ?_⟩
    have hτδ : 0 < τ δ := hτpos₀ δ hδ (le_trans hδe (min_le_right _ _))
    have hx := hgapraw₀ i (Finset.mem_univ i) δ hδ
      (lt_of_le_of_lt (le_trans hδe (min_le_left _ _)) (by linarith))
    rwa [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτδ] at hx
  have hgap₁ : ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₁ * δ ≤ ‖g₁ (b - δ) i‖ / τ (b - δ) := by
    refine ⟨min (δg₁ / 2) e₁, lt_min (by linarith) he₁, fun δ hδ hδe i => ?_⟩
    have hτδ : 0 < τ (b - δ) := hτpos₁ δ hδ (le_trans hδe (min_le_right _ _))
    have hx := hgapraw₁ i (Finset.mem_univ i) δ hδ
      (lt_of_le_of_lt (le_trans hδe (min_le_left _ _)) (by linarith))
    rwa [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτδ] at hx
  -- one threshold for both endpoints: the larger of the two the cluster bound
  -- allows, since `h ≤ Mθ` only gets harder as `h` grows
  obtain ⟨t₀, ht₀, hcl₀⟩ := exists_cluster_threshold (ι := Fin n₀) Finset.univ
    (C_W := 2) (δ := 1 / 4) (c := c₀) (ε := 1) hc₀ zero_le_one (by norm_num) (by norm_num)
  obtain ⟨t₁, ht₁, hcl₁⟩ := exists_cluster_threshold (ι := Fin n₁) Finset.univ
    (C_W := 2) (δ := 1 / 4) (c := c₁) (ε := 1) hc₁ zero_le_one (by norm_num) (by norm_num)
  have hthrpos : 0 < max t₀ t₁ := lt_of_lt_of_le ht₀ (le_max_left _ _)
  have hclu₀ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₀ → ℝ) (θ W : ℝ), 0 < θ → θ ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), 1 + c₀ * θ ≤ ζ' i) →
        ∀ M : ℕ, max t₀ t₁ ≤ (M : ℝ) * θ →
          ∑ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W :=
    ⟨1, one_pos, fun A ζ' θ W hθ hθe hW hA hg M hM =>
      hcl₀ A ζ' θ W hθ hθe hW hA hg M (le_trans (le_max_left _ _) hM)⟩
  have hclu₁ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₁ → ℝ) (η W : ℝ), 0 < η → η ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), 1 + c₁ * η ≤ ζ' i) →
        ∀ M : ℕ, max t₀ t₁ ≤ (M : ℝ) * η →
          ∑ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W :=
    ⟨1, one_pos, fun A ζ' η W hη hηe hW hA hg M hM =>
      hcl₁ A ζ' η W hη hηe hW hA hg M (le_trans (le_max_right _ _) hM)⟩
  obtain ⟨ε, hε, H⟩ :=
    weighted_dominance_of_branch_any_multiplicity_at_of_threshold (h := max t₀ t₁)
    hQ hB hB0 hr hQ0 hx₁ hρ hte₀ hγe₀ hγ0₀ hγd₀ hk₀ hrootev₀ hcB₀ hcQ₀ hBj₀ hBp₀ hEj₀ hEp₀
    hR₀ hσ₀ hσ₀1 he₀ hτpos₀ hτle₀ hroot₀ hsimple₀ haR₀ huniq₀ hrootplus₀ hne₀ hginj₀ hgmem₀
    hgcard₀ hC₀ hCbd₀ hA₁ hamp₁ hL₁ hratio₁ hR₁ hσ₁ hσ₁1 he₁ hτpos₁ hτle₁ hroot₁ hsimple₁
    haR₁ huniq₁ hrootplus₁ hne₁ hginj₁ hgmem₁ hgcard₁ hC₁ hCbd₁ hthrpos hgap₀ hgap₁ hclu₀
    hclu₁
  exact ⟨ε, hε, fun Θ hinterior => ⟨max t₀ t₁, hthrpos, H Θ hinterior⟩⟩

/-- **Paper `thm:weighted-dominance`, on the cited branch and its modulus gap.**
`eq:dominance-bound` on `eq:retained-range` for `F_M`, with the amplitude floor,
the residue comparison and the endpoint split all *applied* rather than assumed:
`hamp` comes from `ftPrincipalAmp_lower_bound`, `hCW` from
`ftCluster_amplitude_le_two` (so `C_W = 2` stays derived from
`eq:lower-residue-ratio`), and `hsplit` from `ftSplit_of_branch`.

What survives in the binder list is the Forgács–Tran branch — the endpoint
factorization data `te`, `γe`, the retained cluster and its enumeration — the
endpoint expansion `ζ_j(δ) = 1 + c_jδ + O(δ^2)` of `[Prop.~3]`
and the leading behavior of `B` and `∂_tD` along each branch, the
separating circle (zero-free, with the retained cluster strictly inside it) and
continuity of the spectral parameter across each closed window, and the interior
supply.  `eq:endpoint-linear-gap`, `eq:lower-residue-ratio` and the uniform
contour constant of `eq:contour-remainder-bound` are **not** binders: the first
two are the manuscript's own extractions from that expansion, the third its own
uniformity sentence, and all three are derived here.  No binder names `poleRem`
or `poleCofactor`, and **none names `ftRemainder`**, so no binder relates the two
sides of the conclusion and none of them can contain it.  Exactly one binder
names `ftPrincipalAmp` -- `hamp₁`, the upper-endpoint amplitude floor -- and it
names only that side.  Its lower counterpart `hamp₀` is not a binder at all:
`ftPrincipalAmp_lower_bound` produces it from the endpoint factorization.  The
asymmetry is the upper endpoint's, not the statement's.  The two endpoints
share one statement through the chart `w`: `id` below, `fun η => b - η` above.

**The two endpoints do not share their residue data, and must not.**  Below,
`eq:lower-residue-ratio` compares amplitudes through `clusterAlpha x_1 ρ`, the
direction into the smallest zero of `Q`, with the orders `ν_B` and `ρ-1`.
Above, `eq:upper-residue-ratio` gives `W_j/W = ζ_j/ζ_+(1+O(τ))`, a ratio
of *normalized roots* whose limit has modulus one — no `clusterAlpha`, no
`ν_B`, no `ρ-1`, because `B(0) ≠ 0` means `B` does not vanish on the upper
cluster at all.  Stating the upper endpoint as a second copy of the lower one is
not merely inexact: `∂_tD ≍ 1/τ` diverges there for `r > 1`, so a
binder dividing it by `δ^{ρ-1}` cannot be satisfied and the theorem goes
vacuous over most of its range.  `hratio₁` and `hL₁` are the upper endpoint in
its own terms; `hexp₁` and the `hωne₁` pair carry `r`, since the upper
cluster tends to the `r`th roots of `-1` with principal pair `e^{± iπ/r}`,
not to the `ρ`th roots.

At `r = 2` those two roots are `e^{± iπ/2}`, both principal, so `n_1 = 0` and
the upper cluster binders are empty.  That is the manuscript's own "the cluster
is the principal pair alone", and the conclusion does not lean on them there:
the upper remainder is then the contour error, bounded by `hσ₁` and the
contour constant. -/
theorem weighted_dominance_of_branch_any_multiplicity {Q B : Polynomial ℂ}
    (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {b : ℝ} {z τ : ℝ → ℝ} {Θ : ℕ → Set ℝ}
    {n₀ n₁ : ℕ} {g₀ : ℝ → Fin n₀ → ℂ} {g₁ : ℝ → Fin n₁ → ℂ}
    {sfun₀ sfun₁ : ℝ → Finset ℂ}
    {x₁ : ℝ} (hx₁ : 0 < x₁) {ρ : ℕ} (hρ : 0 < n₀ → 2 ≤ ρ)
    -- lower endpoint: the endpoint factorization
    {te₀ γe₀ : ℂ} (hte₀ : te₀ ≠ 0) (hγe₀ : γe₀ ≠ 0)
    (hγ0₀ : ftPrincipal τ 0 = te₀)
    (hγd₀ : HasDerivWithinAt (fun δ => ftPrincipal τ δ) γe₀ (Set.Ici 0) 0)
    (hk₀ : 1 ≤ (ftDen Q r ((z 0 : ℝ) : ℂ)).rootMultiplicity te₀)
    (hrootev₀ : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    -- lower endpoint: the residue ratio
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    {idx₀ : Fin n₀ → ℕ} {jp₀ : ℕ} {νB₀ : ℕ} {cB₀ cQ₀ : ℂ}
    (hcB₀ : 0 < n₀ → cB₀ ≠ 0) (hcQ₀ : 0 < n₀ → cQ₀ ≠ 0)
    (hBj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => B.eval (g₀ δ i) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ (idx₀ i) ^ νB₀)))
    (hBp₀ : 0 < n₀ → Filter.Tendsto
      (fun δ : ℝ => B.eval (ftPrincipal τ δ) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ jp₀ ^ νB₀)))
    (hEj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (g₀ δ i)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ (idx₀ i) ^ (ρ - 1))))
    (hEp₀ : 0 < n₀ → Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (ftPrincipal τ δ)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ jp₀ ^ (ρ - 1))))
    -- lower endpoint: the retained cluster and the contour bound
    {R₀ τmax₀ σ₀ e₀ : ℝ} (hR₀ : 0 < R₀) (hσ₀ : τmax₀ / R₀ ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (he₀ : 0 < e₀)
    (hτpos₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → 0 < τ δ)
    (hτle₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → τ δ ≤ τmax₀)
    (hroot₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval a = 0)
    (hsimple₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval a ≠ 0)
    (haR₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ, ‖a‖ < R₀)
    (huniq₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₀ δ)
    (hrootplus₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    (hne₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ftPrincipal τ δ ≠ ((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))
    (hginj₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → Function.Injective (g₀ δ))
    (hgmem₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ i, g₀ δ i ∈
      ((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)))
    (hgcard₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))).card = n₀)
    -- the separating circle, zero-free across the closed window, and the branch
    -- parameter continuous on it: `eq:contour-remainder-bound`'s constant is
    -- produced from these two by compactness, not assumed uniform
    -- the contour bound enters as the punctured statement the proof uses, not as
    -- the closed-window data one route happens to derive it from.  Taken here at
    -- the lower endpoint too, where the closed form IS meetable: a theorem whose
    -- two endpoints take different kinds of input is what lets an upper binder be
    -- built by symmetry with a lower one and come out false.
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hCbd₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z δ : ℝ) : ℂ)).eval t‖ ≤ C₀)
    -- `eq:endpoint-linear-gap` is *not* assumed: Prop. 3 supplies the expansion
    -- `ζ_j(δ) = 1 + c_jδ + O(δ²)`, and the uniform gap is our extraction from it
    {Cexp₀ : ℝ} (hCexp₀ : 0 ≤ Cexp₀)
    (hωne₀ : ∀ i : Fin n₀, clusterOmega ρ (idx₀ i)
      ≠ Complex.exp (((Real.pi / ρ : ℝ) : ℂ) * I))
    (hωne'₀ : ∀ i : Fin n₀, clusterOmega ρ (idx₀ i)
      ≠ Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * I))
    (hexp₀ : ∀ i : Fin n₀, ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ‖g₀ δ i / ((τ δ : ℝ) : ℂ)
        - (1 + ((((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx₀ i))
            / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) * (δ : ℂ))‖ ≤ Cexp₀ * δ ^ 2)
    -- upper endpoint: the same, through the chart `η ↦ b - η`
    -- the upper endpoint enters as the amplitude bound itself, not as a route to
    -- it: `weighted_dominance_ftCoeffPoly` already takes `p₁` abstractly, and the
    -- endpoint group's only use here was to obtain this.  Which route proves it
    -- depends on `r` — the finite one at `r = 1`, where `γ(0) ≠ 0`, and the origin
    -- one at `r ≥ 2`, where `FTBranchUpperRefutation` proves `γ(0) = 0`.
    {p₁ : ℕ} {A₁ : ℝ} (hA₁ : 0 < A₁)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    -- `eq:upper-residue-ratio`.  At the upper endpoint the amplitude ratio is a
    -- ratio of NORMALIZED ROOTS, `W_j/W = ζ_j/ζ_+(1+O(τ))`, and its limit has
    -- modulus one because the `ζ` tend to the `r`th roots of `-1`.  This is NOT
    -- the lower endpoint's cluster ratio: `B(0) ≠ 0`, so `B` does not vanish on
    -- this cluster, and no `clusterAlpha`, no `ν_B` and no `ρ-1` enters.  The
    -- cluster is empty unless `r ≥ 2`, which is `hn₁r`.
    {idx₁ : Fin n₁ → ℕ} {L₁ : Fin n₁ → ℂ}
    (hn₁r : 0 < n₁ → 2 ≤ r)
    (hL₁ : ∀ i : Fin n₁, ‖L₁ i‖ = 1)
    (hratio₁ : ∀ i : Fin n₁, Filter.Tendsto
      (fun δ : ℝ => ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (g₁ (b - δ) i)
        / ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (ftPrincipal τ (b - δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L₁ i)))
    {R₁ τmax₁ σ₁ e₁ : ℝ} (hR₁ : 0 < R₁) (hσ₁ : τmax₁ / R₁ ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (he₁ : 0 < e₁)
    (hτpos₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → 0 < τ (b - δ))
    (hτle₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → τ (b - δ) ≤ τmax₁)
    (hroot₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval a = 0)
    (hsimple₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (derivative (ftDen Q r ((z (b - δ) : ℝ) : ℂ))).eval a ≠ 0)
    (haR₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ, ‖a‖ < R₁)
    (huniq₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t : ℂ, ‖t‖ ≤ R₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₁ δ)
    (hrootplus₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval (ftPrincipal τ (b - δ)) = 0)
    (hne₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      ftPrincipal τ (b - δ) ≠ ((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))
    (hginj₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → Function.Injective (g₁ (b - δ)))
    (hgmem₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ i, g₁ (b - δ) i ∈
      ((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I)))
    (hgcard₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))).card = n₁)
    -- the contour bound enters as the punctured statement the proof uses.  The
    -- closed-window form is not merely stronger than needed here: at `r ≥ 2` it is
    -- unmeetable, because `z` is unbounded as `δ → 0` and a continuous function on
    -- a compact set is bounded; and at the one pencil where it IS discharged, it
    -- passes without probing the endpoint at all — at `δ = 0` the junk value of `z`
    -- leaves `Q` alone, whose zero misses the sphere, so it holds by Lean's
    -- division-by-zero convention rather than by the geometry.  A binder that holds
    -- for a reason unrelated to what it was written to test is not evidence, and
    -- looks exactly like evidence.
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hCbd₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
      ‖B.eval t / (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁)
    -- `eq:endpoint-linear-gap` is *not* assumed: Prop. 3 supplies the expansion
    -- `ζ_j(δ) = 1 + c_jδ + O(δ²)`, and the uniform gap is our extraction from it
    {Cexp₁ : ℝ} (hCexp₁ : 0 ≤ Cexp₁)
    (hωne₁ : ∀ i : Fin n₁, clusterOmega r (idx₁ i)
      ≠ Complex.exp (((Real.pi / r : ℝ) : ℂ) * I))
    (hωne'₁ : ∀ i : Fin n₁, clusterOmega r (idx₁ i)
      ≠ Complex.exp (((-(Real.pi / r) : ℝ) : ℂ) * I))
    -- the MODULUS form: at the upper endpoint `ζ_j → ω_j`, an `r`th root of `-1`,
    -- not to `1`, so only `‖ζ_j‖` expands about `1`.  `eq:endpoint-linear-gap`'s
    -- upper display is a modulus in the manuscript and the two endpoints do not
    -- share expansion shape any more than they share residue geometry.
    (hexp₁ : ∀ i : Fin n₁, ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      |‖g₁ (b - δ) i / ((τ (b - δ) : ℝ) : ℂ)‖
        - (1 + ((Real.cos (Real.pi / r) - (clusterOmega r (idx₁ i)).re)
            / Real.sin (Real.pi / r)) * δ)| ≤ Cexp₁ * δ ^ 2)
    -- the compact interior: the remainder bound derived, the amplitude's lower
    -- bound by its own zero divisor, and the definition of the deleted windows
    (hinterior : ∀ e : ℝ, 0 < e →
      ∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
        0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → 0 < τ θ) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → τ θ ≤ τmi) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → τ θ < Ri) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
            (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → ∀ t : ℂ, ‖t‖ ≤ Ri →
          (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
          t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (↑S ⊆ Set.Icc e (b - e)) ∧
        (∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0) ∧
        (∀ θ ∈ Set.Icc e (b - e),
          ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S) ∧
        (∀ θ ∈ Set.Icc e (b - e), ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ) ∧
        (∀ θ ∈ Set.Icc e (b - e), ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ) ∧
        (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
          Real.exp (-((-Real.log σi) / (2 * S.card) * M
            / (B.rootMultiplicity (ftPrincipal τ θj)))) ≤ |θ - θj|)) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
        ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  obtain ⟨ε, hε, H⟩ :=
    weighted_dominance_of_branch_any_multiplicity_at hQ hB hB0 hr hQ0 hx₁ hρ
      hte₀ hγe₀ hγ0₀ hγd₀ hk₀ hrootev₀ hcB₀ hcQ₀ hBj₀ hBp₀ hEj₀ hEp₀
      hR₀ hσ₀ hσ₀1 he₀ hτpos₀ hτle₀ hroot₀ hsimple₀ haR₀ huniq₀ hrootplus₀ hne₀
      hginj₀ hgmem₀ hgcard₀ hC₀ hCbd₀ hCexp₀ hωne₀ hωne'₀ hexp₀
      hA₁ hamp₁ hn₁r hL₁ hratio₁
      hR₁ hσ₁ hσ₁1 he₁ hτpos₁ hτle₁ hroot₁ hsimple₁ haR₁ huniq₁ hrootplus₁ hne₁
      hginj₁ hgmem₁ hgcard₁ hC₁ hCbd₁ hCexp₁ hωne₁ hωne'₁ hexp₁
  exact H Θ (hinterior ε hε)










/-- **`thm:weighted-dominance` with the smallest zero assumed multiple.**  The
`ρ ≥ 2` specialization of `weighted_dominance_of_branch_any_multiplicity`, kept
because the composition layer supplies `hρ` in this form. -/
theorem weighted_dominance_of_branch {Q B : Polynomial ℂ}
    (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {b : ℝ} {z τ : ℝ → ℝ} {Θ : ℕ → Set ℝ}
    {n₀ n₁ : ℕ} {g₀ : ℝ → Fin n₀ → ℂ} {g₁ : ℝ → Fin n₁ → ℂ}
    {sfun₀ sfun₁ : ℝ → Finset ℂ}
    {x₁ : ℝ} (hx₁ : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ)
    -- lower endpoint: the endpoint factorization
    {te₀ γe₀ : ℂ} (hte₀ : te₀ ≠ 0) (hγe₀ : γe₀ ≠ 0)
    (hγ0₀ : ftPrincipal τ 0 = te₀)
    (hγd₀ : HasDerivWithinAt (fun δ => ftPrincipal τ δ) γe₀ (Set.Ici 0) 0)
    (hk₀ : 1 ≤ (ftDen Q r ((z 0 : ℝ) : ℂ)).rootMultiplicity te₀)
    (hrootev₀ : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    -- lower endpoint: the residue ratio
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    {idx₀ : Fin n₀ → ℕ} {jp₀ : ℕ} {νB₀ : ℕ} {cB₀ cQ₀ : ℂ}
    (hcB₀ : cB₀ ≠ 0) (hcQ₀ : cQ₀ ≠ 0)
    (hBj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => B.eval (g₀ δ i) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ (idx₀ i) ^ νB₀)))
    (hBp₀ : Filter.Tendsto
      (fun δ : ℝ => B.eval (ftPrincipal τ δ) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ jp₀ ^ νB₀)))
    (hEj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (g₀ δ i)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ (idx₀ i) ^ (ρ - 1))))
    (hEp₀ : Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (ftPrincipal τ δ)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ jp₀ ^ (ρ - 1))))
    -- lower endpoint: the retained cluster and the contour bound
    {R₀ τmax₀ σ₀ e₀ : ℝ} (hR₀ : 0 < R₀) (hσ₀ : τmax₀ / R₀ ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (he₀ : 0 < e₀)
    (hτpos₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → 0 < τ δ)
    (hτle₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → τ δ ≤ τmax₀)
    (hroot₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval a = 0)
    (hsimple₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval a ≠ 0)
    (haR₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ, ‖a‖ < R₀)
    (huniq₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₀ δ)
    (hrootplus₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    (hne₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ftPrincipal τ δ ≠ ((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))
    (hginj₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → Function.Injective (g₀ δ))
    (hgmem₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ i, g₀ δ i ∈
      ((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)))
    (hgcard₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))).card = n₀)
    -- the separating circle, zero-free across the closed window, and the branch
    -- parameter continuous on it: `eq:contour-remainder-bound`'s constant is
    -- produced from these two by compactness, not assumed uniform
    -- the contour bound enters as the punctured statement the proof uses, not as
    -- the closed-window data one route happens to derive it from.  Taken here at
    -- the lower endpoint too, where the closed form IS meetable: a theorem whose
    -- two endpoints take different kinds of input is what lets an upper binder be
    -- built by symmetry with a lower one and come out false.
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hCbd₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z δ : ℝ) : ℂ)).eval t‖ ≤ C₀)
    -- `eq:endpoint-linear-gap` is *not* assumed: Prop. 3 supplies the expansion
    -- `ζ_j(δ) = 1 + c_jδ + O(δ²)`, and the uniform gap is our extraction from it
    {Cexp₀ : ℝ} (hCexp₀ : 0 ≤ Cexp₀)
    (hωne₀ : ∀ i : Fin n₀, clusterOmega ρ (idx₀ i)
      ≠ Complex.exp (((Real.pi / ρ : ℝ) : ℂ) * I))
    (hωne'₀ : ∀ i : Fin n₀, clusterOmega ρ (idx₀ i)
      ≠ Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * I))
    (hexp₀ : ∀ i : Fin n₀, ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ‖g₀ δ i / ((τ δ : ℝ) : ℂ)
        - (1 + ((((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx₀ i))
            / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) * (δ : ℂ))‖ ≤ Cexp₀ * δ ^ 2)
    -- upper endpoint: the same, through the chart `η ↦ b - η`
    -- the upper endpoint enters as the amplitude bound itself, not as a route to
    -- it: `weighted_dominance_ftCoeffPoly` already takes `p₁` abstractly, and the
    -- endpoint group's only use here was to obtain this.  Which route proves it
    -- depends on `r` — the finite one at `r = 1`, where `γ(0) ≠ 0`, and the origin
    -- one at `r ≥ 2`, where `FTBranchUpperRefutation` proves `γ(0) = 0`.
    {p₁ : ℕ} {A₁ : ℝ} (hA₁ : 0 < A₁)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    -- `eq:upper-residue-ratio`.  At the upper endpoint the amplitude ratio is a
    -- ratio of NORMALIZED ROOTS, `W_j/W = ζ_j/ζ_+(1+O(τ))`, and its limit has
    -- modulus one because the `ζ` tend to the `r`th roots of `-1`.  This is NOT
    -- the lower endpoint's cluster ratio: `B(0) ≠ 0`, so `B` does not vanish on
    -- this cluster, and no `clusterAlpha`, no `ν_B` and no `ρ-1` enters.  The
    -- cluster is empty unless `r ≥ 2`, which is `hn₁r`.
    {idx₁ : Fin n₁ → ℕ} {L₁ : Fin n₁ → ℂ}
    (hn₁r : 0 < n₁ → 2 ≤ r)
    (hL₁ : ∀ i : Fin n₁, ‖L₁ i‖ = 1)
    (hratio₁ : ∀ i : Fin n₁, Filter.Tendsto
      (fun δ : ℝ => ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (g₁ (b - δ) i)
        / ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (ftPrincipal τ (b - δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L₁ i)))
    {R₁ τmax₁ σ₁ e₁ : ℝ} (hR₁ : 0 < R₁) (hσ₁ : τmax₁ / R₁ ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (he₁ : 0 < e₁)
    (hτpos₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → 0 < τ (b - δ))
    (hτle₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → τ (b - δ) ≤ τmax₁)
    (hroot₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval a = 0)
    (hsimple₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (derivative (ftDen Q r ((z (b - δ) : ℝ) : ℂ))).eval a ≠ 0)
    (haR₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ, ‖a‖ < R₁)
    (huniq₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t : ℂ, ‖t‖ ≤ R₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₁ δ)
    (hrootplus₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval (ftPrincipal τ (b - δ)) = 0)
    (hne₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      ftPrincipal τ (b - δ) ≠ ((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))
    (hginj₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → Function.Injective (g₁ (b - δ)))
    (hgmem₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ i, g₁ (b - δ) i ∈
      ((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I)))
    (hgcard₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))).card = n₁)
    -- the contour bound enters as the punctured statement the proof uses.  The
    -- closed-window form is not merely stronger than needed here: at `r ≥ 2` it is
    -- unmeetable, because `z` is unbounded as `δ → 0` and a continuous function on
    -- a compact set is bounded; and at the one pencil where it IS discharged, it
    -- passes without probing the endpoint at all — at `δ = 0` the junk value of `z`
    -- leaves `Q` alone, whose zero misses the sphere, so it holds by Lean's
    -- division-by-zero convention rather than by the geometry.  A binder that holds
    -- for a reason unrelated to what it was written to test is not evidence, and
    -- looks exactly like evidence.
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hCbd₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
      ‖B.eval t / (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁)
    -- `eq:endpoint-linear-gap` is *not* assumed: Prop. 3 supplies the expansion
    -- `ζ_j(δ) = 1 + c_jδ + O(δ²)`, and the uniform gap is our extraction from it
    {Cexp₁ : ℝ} (hCexp₁ : 0 ≤ Cexp₁)
    (hωne₁ : ∀ i : Fin n₁, clusterOmega r (idx₁ i)
      ≠ Complex.exp (((Real.pi / r : ℝ) : ℂ) * I))
    (hωne'₁ : ∀ i : Fin n₁, clusterOmega r (idx₁ i)
      ≠ Complex.exp (((-(Real.pi / r) : ℝ) : ℂ) * I))
    -- the MODULUS form: at the upper endpoint `ζ_j → ω_j`, an `r`th root of `-1`,
    -- not to `1`, so only `‖ζ_j‖` expands about `1`.  `eq:endpoint-linear-gap`'s
    -- upper display is a modulus in the manuscript and the two endpoints do not
    -- share expansion shape any more than they share residue geometry.
    (hexp₁ : ∀ i : Fin n₁, ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      |‖g₁ (b - δ) i / ((τ (b - δ) : ℝ) : ℂ)‖
        - (1 + ((Real.cos (Real.pi / r) - (clusterOmega r (idx₁ i)).re)
            / Real.sin (Real.pi / r)) * δ)| ≤ Cexp₁ * δ ^ 2)
    -- the compact interior: the remainder bound derived, the amplitude's lower
    -- bound by its own zero divisor, and the definition of the deleted windows
    (hinterior : ∀ e : ℝ, 0 < e →
      ∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
        0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → 0 < τ θ) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → τ θ ≤ τmi) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → τ θ < Ri) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
            (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → ∀ t : ℂ, ‖t‖ ≤ Ri →
          (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
          t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (↑S ⊆ Set.Icc e (b - e)) ∧
        (∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0) ∧
        (∀ θ ∈ Set.Icc e (b - e),
          ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S) ∧
        (∀ θ ∈ Set.Icc e (b - e), ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ) ∧
        (∀ θ ∈ Set.Icc e (b - e), ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ) ∧
        (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
          Real.exp (-((-Real.log σi) / (2 * S.card) * M
            / (B.rootMultiplicity (ftPrincipal τ θj)))) ≤ |θ - θj|)) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
        ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 :=
  weighted_dominance_of_branch_any_multiplicity (hρ := fun _ => hρ)
      (hcB₀ := fun _ => hcB₀) (hcQ₀ := fun _ => hcQ₀) (hBp₀ := fun _ => hBp₀)
      (hEp₀ := fun _ => hEp₀) (hQ := hQ) (hB := hB)
      (hB0 := hB0) (hr := hr) (hQ0 := hQ0) (n₀ := n₀) (n₁ := n₁) (g₀ := g₀) (g₁ := g₁)
      (sfun₀ := sfun₀) (sfun₁ := sfun₁) (x₁ := x₁) (hx₁ := hx₁) (ρ := ρ) (te₀ := te₀)
      (γe₀ := γe₀) (hte₀ := hte₀) (hγe₀ := hγe₀) (hγ0₀ := hγ0₀) (hγd₀ := hγd₀) (hk₀ := hk₀)
      (hrootev₀ := hrootev₀) (idx₀ := idx₀) (jp₀ := jp₀) (νB₀ := νB₀) (cB₀ := cB₀) (cQ₀ := cQ₀)
      (hBj₀ := hBj₀) (hEj₀ := hEj₀)
      (R₀ := R₀) (τmax₀ := τmax₀) (σ₀ := σ₀) (e₀ := e₀) (hR₀ := hR₀) (hσ₀ := hσ₀) (hσ₀1 := hσ₀1)
      (he₀ := he₀) (hτpos₀ := hτpos₀) (hτle₀ := hτle₀) (hroot₀ := hroot₀) (hsimple₀ := hsimple₀)
      (haR₀ := haR₀) (huniq₀ := huniq₀) (hrootplus₀ := hrootplus₀) (hne₀ := hne₀)
      (hginj₀ := hginj₀) (hgmem₀ := hgmem₀) (hgcard₀ := hgcard₀) (C₀ := C₀) (hC₀ := hC₀)
      (hCbd₀ := hCbd₀) (Cexp₀ := Cexp₀) (hCexp₀ := hCexp₀) (hωne₀ := hωne₀) (hωne'₀ := hωne'₀)
      (hexp₀ := hexp₀) (p₁ := p₁) (A₁ := A₁) (hA₁ := hA₁) (hamp₁ := hamp₁) (idx₁ := idx₁)
      (L₁ := L₁) (hn₁r := hn₁r) (hL₁ := hL₁) (hratio₁ := hratio₁) (R₁ := R₁) (τmax₁ := τmax₁)
      (σ₁ := σ₁) (e₁ := e₁) (hR₁ := hR₁) (hσ₁ := hσ₁) (hσ₁1 := hσ₁1) (he₁ := he₁)
      (hτpos₁ := hτpos₁) (hτle₁ := hτle₁) (hroot₁ := hroot₁) (hsimple₁ := hsimple₁)
      (haR₁ := haR₁) (huniq₁ := huniq₁) (hrootplus₁ := hrootplus₁) (hne₁ := hne₁)
      (hginj₁ := hginj₁) (hgmem₁ := hgmem₁) (hgcard₁ := hgcard₁) (C₁ := C₁) (hC₁ := hC₁)
      (hCbd₁ := hCbd₁) (Cexp₁ := Cexp₁) (hCexp₁ := hCexp₁) (hωne₁ := hωne₁) (hωne'₁ := hωne'₁)
      (hexp₁ := hexp₁) (hinterior := hinterior)


/-- **`thm:weighted-dominance` with the smallest zero assumed multiple, and the
interior parameter handed back.**  The `ρ ≥ 2` specialization of
`weighted_dominance_of_branch_any_multiplicity_at`, in the shape the composition
layer supplies `hρ`.

`ε` is produced before `Θ` is chosen, so the deleted family may be built from
that `ε`'s own `σ` — which `weighted_dominance_of_branch` cannot offer, because
there `Θ` is fixed first and the interior data is demanded at every `e`. -/
theorem weighted_dominance_of_branch_at {Q B : Polynomial ℂ}
    (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {b : ℝ} {z τ : ℝ → ℝ}
    {n₀ n₁ : ℕ} {g₀ : ℝ → Fin n₀ → ℂ} {g₁ : ℝ → Fin n₁ → ℂ}
    {sfun₀ sfun₁ : ℝ → Finset ℂ}
    {x₁ : ℝ} (hx₁ : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ)
    -- lower endpoint: the endpoint factorization
    {te₀ γe₀ : ℂ} (hte₀ : te₀ ≠ 0) (hγe₀ : γe₀ ≠ 0)
    (hγ0₀ : ftPrincipal τ 0 = te₀)
    (hγd₀ : HasDerivWithinAt (fun δ => ftPrincipal τ δ) γe₀ (Set.Ici 0) 0)
    (hk₀ : 1 ≤ (ftDen Q r ((z 0 : ℝ) : ℂ)).rootMultiplicity te₀)
    (hrootev₀ : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    -- lower endpoint: the residue ratio
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    {idx₀ : Fin n₀ → ℕ} {jp₀ : ℕ} {νB₀ : ℕ} {cB₀ cQ₀ : ℂ}
    (hcB₀ : cB₀ ≠ 0) (hcQ₀ : cQ₀ ≠ 0)
    (hBj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => B.eval (g₀ δ i) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ (idx₀ i) ^ νB₀)))
    (hBp₀ : Filter.Tendsto
      (fun δ : ℝ => B.eval (ftPrincipal τ δ) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ jp₀ ^ νB₀)))
    (hEj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (g₀ δ i)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ (idx₀ i) ^ (ρ - 1))))
    (hEp₀ : Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (ftPrincipal τ δ)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ jp₀ ^ (ρ - 1))))
    -- lower endpoint: the retained cluster and the contour bound
    {R₀ τmax₀ σ₀ e₀ : ℝ} (hR₀ : 0 < R₀) (hσ₀ : τmax₀ / R₀ ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (he₀ : 0 < e₀)
    (hτpos₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → 0 < τ δ)
    (hτle₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → τ δ ≤ τmax₀)
    (hroot₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval a = 0)
    (hsimple₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval a ≠ 0)
    (haR₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ, ‖a‖ < R₀)
    (huniq₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₀ δ)
    (hrootplus₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    (hne₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ftPrincipal τ δ ≠ ((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))
    (hginj₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → Function.Injective (g₀ δ))
    (hgmem₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ i, g₀ δ i ∈
      ((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)))
    (hgcard₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))).card = n₀)
    -- the separating circle, zero-free across the closed window, and the branch
    -- parameter continuous on it: `eq:contour-remainder-bound`'s constant is
    -- produced from these two by compactness, not assumed uniform
    -- the contour bound enters as the punctured statement the proof uses, not as
    -- the closed-window data one route happens to derive it from.  Taken here at
    -- the lower endpoint too, where the closed form IS meetable: a theorem whose
    -- two endpoints take different kinds of input is what lets an upper binder be
    -- built by symmetry with a lower one and come out false.
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hCbd₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z δ : ℝ) : ℂ)).eval t‖ ≤ C₀)
    -- `eq:endpoint-linear-gap` is *not* assumed: Prop. 3 supplies the expansion
    -- `ζ_j(δ) = 1 + c_jδ + O(δ²)`, and the uniform gap is our extraction from it
    {Cexp₀ : ℝ} (hCexp₀ : 0 ≤ Cexp₀)
    (hωne₀ : ∀ i : Fin n₀, clusterOmega ρ (idx₀ i)
      ≠ Complex.exp (((Real.pi / ρ : ℝ) : ℂ) * I))
    (hωne'₀ : ∀ i : Fin n₀, clusterOmega ρ (idx₀ i)
      ≠ Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * I))
    (hexp₀ : ∀ i : Fin n₀, ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ‖g₀ δ i / ((τ δ : ℝ) : ℂ)
        - (1 + ((((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx₀ i))
            / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) * (δ : ℂ))‖ ≤ Cexp₀ * δ ^ 2)
    -- upper endpoint: the same, through the chart `η ↦ b - η`
    -- the upper endpoint enters as the amplitude bound itself, not as a route to
    -- it: `weighted_dominance_ftCoeffPoly` already takes `p₁` abstractly, and the
    -- endpoint group's only use here was to obtain this.  Which route proves it
    -- depends on `r` — the finite one at `r = 1`, where `γ(0) ≠ 0`, and the origin
    -- one at `r ≥ 2`, where `FTBranchUpperRefutation` proves `γ(0) = 0`.
    {p₁ : ℕ} {A₁ : ℝ} (hA₁ : 0 < A₁)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    -- `eq:upper-residue-ratio`.  At the upper endpoint the amplitude ratio is a
    -- ratio of NORMALIZED ROOTS, `W_j/W = ζ_j/ζ_+(1+O(τ))`, and its limit has
    -- modulus one because the `ζ` tend to the `r`th roots of `-1`.  This is NOT
    -- the lower endpoint's cluster ratio: `B(0) ≠ 0`, so `B` does not vanish on
    -- this cluster, and no `clusterAlpha`, no `ν_B` and no `ρ-1` enters.  The
    -- cluster is empty unless `r ≥ 2`, which is `hn₁r`.
    {idx₁ : Fin n₁ → ℕ} {L₁ : Fin n₁ → ℂ}
    (hn₁r : 0 < n₁ → 2 ≤ r)
    (hL₁ : ∀ i : Fin n₁, ‖L₁ i‖ = 1)
    (hratio₁ : ∀ i : Fin n₁, Filter.Tendsto
      (fun δ : ℝ => ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (g₁ (b - δ) i)
        / ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (ftPrincipal τ (b - δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L₁ i)))
    {R₁ τmax₁ σ₁ e₁ : ℝ} (hR₁ : 0 < R₁) (hσ₁ : τmax₁ / R₁ ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (he₁ : 0 < e₁)
    (hτpos₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → 0 < τ (b - δ))
    (hτle₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → τ (b - δ) ≤ τmax₁)
    (hroot₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval a = 0)
    (hsimple₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (derivative (ftDen Q r ((z (b - δ) : ℝ) : ℂ))).eval a ≠ 0)
    (haR₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ, ‖a‖ < R₁)
    (huniq₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t : ℂ, ‖t‖ ≤ R₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₁ δ)
    (hrootplus₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval (ftPrincipal τ (b - δ)) = 0)
    (hne₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      ftPrincipal τ (b - δ) ≠ ((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))
    (hginj₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → Function.Injective (g₁ (b - δ)))
    (hgmem₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ i, g₁ (b - δ) i ∈
      ((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I)))
    (hgcard₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))).card = n₁)
    -- the contour bound enters as the punctured statement the proof uses.  The
    -- closed-window form is not merely stronger than needed here: at `r ≥ 2` it is
    -- unmeetable, because `z` is unbounded as `δ → 0` and a continuous function on
    -- a compact set is bounded; and at the one pencil where it IS discharged, it
    -- passes without probing the endpoint at all — at `δ = 0` the junk value of `z`
    -- leaves `Q` alone, whose zero misses the sphere, so it holds by Lean's
    -- division-by-zero convention rather than by the geometry.  A binder that holds
    -- for a reason unrelated to what it was written to test is not evidence, and
    -- looks exactly like evidence.
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hCbd₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
      ‖B.eval t / (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁)
    -- `eq:endpoint-linear-gap` is *not* assumed: Prop. 3 supplies the expansion
    -- `ζ_j(δ) = 1 + c_jδ + O(δ²)`, and the uniform gap is our extraction from it
    {Cexp₁ : ℝ} (hCexp₁ : 0 ≤ Cexp₁)
    (hωne₁ : ∀ i : Fin n₁, clusterOmega r (idx₁ i)
      ≠ Complex.exp (((Real.pi / r : ℝ) : ℂ) * I))
    (hωne'₁ : ∀ i : Fin n₁, clusterOmega r (idx₁ i)
      ≠ Complex.exp (((-(Real.pi / r) : ℝ) : ℂ) * I))
    -- the MODULUS form: at the upper endpoint `ζ_j → ω_j`, an `r`th root of `-1`,
    -- not to `1`, so only `‖ζ_j‖` expands about `1`.  `eq:endpoint-linear-gap`'s
    -- upper display is a modulus in the manuscript and the two endpoints do not
    -- share expansion shape any more than they share residue geometry.
    (hexp₁ : ∀ i : Fin n₁, ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      |‖g₁ (b - δ) i / ((τ (b - δ) : ℝ) : ℂ)‖
        - (1 + ((Real.cos (Real.pi / r) - (clusterOmega r (idx₁ i)).re)
            / Real.sin (Real.pi / r)) * δ)| ≤ Cexp₁ * δ ^ 2)
    :
    ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
      (∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
      0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → 0 < τ θ) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → τ θ ≤ τmi) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → τ θ < Ri) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
          (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → ∀ t : ℂ, ‖t‖ ≤ Ri →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
        t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
      (↑S ⊆ Set.Icc ε (b - ε)) ∧
      (∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0) ∧
      (∀ θ ∈ Set.Icc ε (b - ε),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S) ∧
      (∀ θ ∈ Set.Icc ε (b - ε), ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ) ∧
      (∀ θ ∈ Set.Icc ε (b - ε), ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ) ∧
      (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
        Real.exp (-((-Real.log σi) / (2 * S.card) * M
          / (B.rootMultiplicity (ftPrincipal τ θj)))) ≤ |θ - θj|)) →
      ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
          ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 :=
  weighted_dominance_of_branch_any_multiplicity_at (hρ := fun _ => hρ)
      (hcB₀ := fun _ => hcB₀) (hcQ₀ := fun _ => hcQ₀) (hBp₀ := fun _ => hBp₀)
      (hEp₀ := fun _ => hEp₀) (hQ := hQ) (hB := hB)
      (hB0 := hB0) (hr := hr) (hQ0 := hQ0) (n₀ := n₀) (n₁ := n₁) (g₀ := g₀) (g₁ := g₁)
      (sfun₀ := sfun₀) (sfun₁ := sfun₁) (x₁ := x₁) (hx₁ := hx₁) (ρ := ρ) (te₀ := te₀)
      (γe₀ := γe₀) (hte₀ := hte₀) (hγe₀ := hγe₀) (hγ0₀ := hγ0₀) (hγd₀ := hγd₀) (hk₀ := hk₀)
      (hrootev₀ := hrootev₀) (idx₀ := idx₀) (jp₀ := jp₀) (νB₀ := νB₀) (cB₀ := cB₀) (cQ₀ := cQ₀)
      (hBj₀ := hBj₀) (hEj₀ := hEj₀)
      (R₀ := R₀) (τmax₀ := τmax₀) (σ₀ := σ₀) (e₀ := e₀) (hR₀ := hR₀) (hσ₀ := hσ₀) (hσ₀1 := hσ₀1)
      (he₀ := he₀) (hτpos₀ := hτpos₀) (hτle₀ := hτle₀) (hroot₀ := hroot₀) (hsimple₀ := hsimple₀)
      (haR₀ := haR₀) (huniq₀ := huniq₀) (hrootplus₀ := hrootplus₀) (hne₀ := hne₀)
      (hginj₀ := hginj₀) (hgmem₀ := hgmem₀) (hgcard₀ := hgcard₀) (C₀ := C₀) (hC₀ := hC₀)
      (hCbd₀ := hCbd₀) (Cexp₀ := Cexp₀) (hCexp₀ := hCexp₀) (hωne₀ := hωne₀) (hωne'₀ := hωne'₀)
      (hexp₀ := hexp₀) (p₁ := p₁) (A₁ := A₁) (hA₁ := hA₁) (hamp₁ := hamp₁) (idx₁ := idx₁)
      (L₁ := L₁) (hn₁r := hn₁r) (hL₁ := hL₁) (hratio₁ := hratio₁) (R₁ := R₁) (τmax₁ := τmax₁)
      (σ₁ := σ₁) (e₁ := e₁) (hR₁ := hR₁) (hσ₁ := hσ₁) (hσ₁1 := hσ₁1) (he₁ := he₁)
      (hτpos₁ := hτpos₁) (hτle₁ := hτle₁) (hroot₁ := hroot₁) (hsimple₁ := hsimple₁)
      (haR₁ := haR₁) (huniq₁ := huniq₁) (hrootplus₁ := hrootplus₁) (hne₁ := hne₁)
      (hginj₁ := hginj₁) (hgmem₁ := hgmem₁) (hgcard₁ := hgcard₁) (C₁ := C₁) (hC₁ := hC₁)
      (hCbd₁ := hCbd₁) (Cexp₁ := Cexp₁) (hCexp₁ := hCexp₁) (hωne₁ := hωne₁) (hωne'₁ := hωne'₁)
      (hexp₁ := hexp₁)

end ForgacsTran
