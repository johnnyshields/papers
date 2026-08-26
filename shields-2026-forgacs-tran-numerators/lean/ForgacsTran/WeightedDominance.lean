/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Dominance
import ForgacsTran.Cluster

/-!
# Weighted principal-pair dominance, assembled

`Dominance` proves the arithmetic the theorem's proof runs its inputs through —
the gap-to-decay conversion, the cluster sum, the two endpoint-amplitude
estimates, the interior ratio, and the closing `1/4 + 1/4 ≤ 1/2`.  What was
missing was the step that turns those into a *theorem with named constants*: the
choice of `h`, then of `M₀`, and the check that the three regions cover
`eq:retained-range`.  That is what this module does.

## Main statements

* `tendsto_pow_mul_geometric_nhds_zero`, `exists_pow_mul_geometric_le`,
  `exists_succ_pow_mul_geometric_le` — `M^pσ^M → 0`.  Without it the
  endpoint contour remainder is only `o(1)` in the paper's sense and no `M₀` can
  be named.
* `endpoint_contour_relative_le` — `eq:endpoint-contour-relative-bound`: the
  contour remainder against `Aθ^p` on `h/M ≤ θ` is
  `(C/A)h^{-p}M^pσ^M` times the amplitude, the `M`-dependence exactly
  `M^{p_+}`.
* `exists_endpoint_dominance` — one endpoint region of `thm:weighted-dominance`.
  One `h`, then one `M₀`, give `|R_M| ≤ |W|/2` throughout, the cluster taking
  `1/4` and the contour remainder `1/4`.  The amplitude hypothesis is the
  `C_W = 2` that `Cluster.eventually_cluster_amplitude_le` derives from
  `eq:lower-residue-ratio`, rather than a constant assumed.
* `exists_interior_dominance` — `eq:interior-relative-remainder` on the retained
  interior.
* `exists_dominance_threshold` — `eq:dominance-bound` on the whole of
  `eq:retained-range`, from the three regional estimates, with `h` the larger
  endpoint threshold and `M₀` large enough that `h/M ≤ ε`, which is
  what makes the regions cover the range.
* `exists_window_threshold` — `eq:amplitude-window-negligible`: `(M+1)` times the
  total deleted length falls below `1`.

## Implementation notes

**Scope.**  Two inputs of each regional estimate are carried as explicit named
hypotheses on given data rather than derived, because the manuscript imports them
from `Forgacs2017RationalDenominator` through `thm:FT-geometry` and from
`lem:contour-separation`: the linear modulus gap `1 + cθ ≤ |ζ_j|`
(`eq:endpoint-linear-gap`), and the contour remainder bound `|E| ≤ Cσ^M`.
The amplitude lower bound `Aθ^p ≤ |W|` is `lem:amplitude-divisor`.  No
hypothesis structure is introduced: each is an ordinary binder in the theorem's
type, and no regional hypothesis is used outside its own region.  Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`,
`subsec:weighted-dominance`, `thm:weighted-dominance`, `eq:dominance-bound`,
`eq:retained-range`, `eq:endpoint-contour-relative-bound`,
`eq:interior-relative-remainder`, `eq:amplitude-deletion`,
`eq:amplitude-window-negligible`).

## Tags

weighted dominance, principal pair, assembly
-/

namespace ForgacsTran

open Filter Topology

/-! ### Polynomial-times-geometric decay -/

/-- `M^p σ^M → 0` for `0 ≤ σ < 1`: the step
`eq:endpoint-contour-relative-bound` needs after `endpoint_inv_pow_le` has
turned `θ^{-p}` into `h^{-p}M^p`.  Without it the endpoint contour remainder is
only `o(1)` in the paper's sense and no threshold `M₀` can be named. -/
theorem tendsto_pow_mul_geometric_nhds_zero {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (p : ℕ) :
    Tendsto (fun M : ℕ => (M : ℝ) ^ p * σ ^ M) atTop (𝓝 0) := by
  have hnorm : ‖σ‖ < (1 : ℝ) := by rwa [Real.norm_eq_abs, abs_of_nonneg hσ0]
  have h := isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (R := ℝ) p hnorm
  have h1 : (fun M : ℕ => (M : ℝ) ^ p * σ ^ M) =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    refine h.congr' EventuallyEq.rfl ?_
    filter_upwards with M
    simp
  exact (Asymptotics.isLittleO_one_iff (F := ℝ)).mp h1

/-- The threshold form: beyond some `M₀`, `K M^p σ^M` is below any prescribed
`δ > 0`.  This is what fixes `M₀` in `thm:weighted-dominance`. -/
theorem exists_pow_mul_geometric_le {σ K δ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hδ : 0 < δ)
    (p : ℕ) : ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → K * ((M : ℝ) ^ p * σ ^ M) ≤ δ := by
  have h := (tendsto_pow_mul_geometric_nhds_zero hσ0 hσ1 p).const_mul K
  rw [mul_zero] at h
  exact eventually_atTop.mp (h.eventually_le_const hδ)

/-- The same with `(M+1)^p`, which is the shape `eq:amplitude-window-negligible`
takes. -/
theorem exists_succ_pow_mul_geometric_le {σ K δ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hK : 0 ≤ K) (hδ : 0 < δ) (p : ℕ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → K * (((M : ℝ) + 1) ^ p * σ ^ M) ≤ δ := by
  obtain ⟨M₁, hM₁⟩ := exists_pow_mul_geometric_le (K := K * 2 ^ p) hσ0 hσ1 hδ p
  refine ⟨max 1 M₁, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_left _ _) hM
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hstep : ((M : ℝ) + 1) ^ p ≤ 2 ^ p * (M : ℝ) ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) p
  have hσp : (0 : ℝ) ≤ σ ^ M := by positivity
  calc K * (((M : ℝ) + 1) ^ p * σ ^ M)
      ≤ K * ((2 ^ p * (M : ℝ) ^ p) * σ ^ M) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact mul_le_mul_of_nonneg_right hstep hσp
    _ = K * 2 ^ p * ((M : ℝ) ^ p * σ ^ M) := by ring
    _ ≤ δ := hM₁ M (le_trans (le_max_right _ _) hM)

/-! ### The endpoint contour remainder -/

/-- **Paper `eq:endpoint-contour-relative-bound`.**  A contour remainder bounded
by `Cσ^M`, against a principal amplitude bounded below by `Aθ^p` on
`h/M ≤ θ`, is at most `(C/A)h^{-p}M^pσ^M` times that amplitude.  The
`M^p` is exactly the paper's `M^{p_+}` and no worse. -/
theorem endpoint_contour_relative_le {h θ Amin C σ W E : ℝ} {p M : ℕ}
    (hh : 0 < h) (hM : 0 < (M : ℝ)) (hθ : h / M ≤ θ) (hA : 0 < Amin) (hC : 0 ≤ C)
    (hσ0 : 0 ≤ σ) (hW : Amin * θ ^ p ≤ W) (hE : |E| ≤ C * σ ^ M) :
    |E| ≤ C / Amin * (h ^ p)⁻¹ * ((M : ℝ) ^ p * σ ^ M) * W := by
  have hθpos : 0 < θ := lt_of_lt_of_le (by positivity) hθ
  have hinv := endpoint_inv_pow_le hh hM hθ p
  have hθp : (0 : ℝ) < θ ^ p := by positivity
  have hone : (1 : ℝ) ≤ (h ^ p)⁻¹ * (M : ℝ) ^ p * θ ^ p := by
    have hmul := mul_le_mul_of_nonneg_right hinv hθp.le
    rw [inv_mul_cancel₀ (ne_of_gt hθp)] at hmul
    linarith
  have hσM : (0 : ℝ) ≤ σ ^ M := by positivity
  calc |E| ≤ C * σ ^ M := hE
    _ = C * σ ^ M * 1 := by ring
    _ ≤ C * σ ^ M * ((h ^ p)⁻¹ * (M : ℝ) ^ p * θ ^ p) :=
        mul_le_mul_of_nonneg_left hone (by positivity)
    _ = C / Amin * (h ^ p)⁻¹ * ((M : ℝ) ^ p * σ ^ M) * (Amin * θ ^ p) := by
        field_simp
    _ ≤ C / Amin * (h ^ p)⁻¹ * ((M : ℝ) ^ p * σ ^ M) * W :=
        mul_le_mul_of_nonneg_left hW (by positivity)

/-! ### One endpoint region -/

/-- **Paper `thm:weighted-dominance`, one endpoint region.**  Fix the endpoint
data — the linear gap constant `c` of `eq:endpoint-linear-gap`, the window `ε`,
the amplitude exponent `p` and constant `A` of `lem:amplitude-divisor`, and the
contour rate `Cσ^M` of `lem:contour-separation`.  Then one `h > 0` and one
`M₀` serve the whole region: on `h/M ≤ θ ≤ ε` the nonprincipal
cluster contributes at most `|W|/4` and the contour remainder at most `|W|/4`,
so `eq:dominance-bound` holds.

`h` is chosen before `θ`, `W`, the amplitudes and the moduli, and `M₀` after `h`
— which is the paper's order and the whole content of its closing paragraph.
The amplitude hypothesis is `|W_j| ≤ 2|W|`, the `C_W = 2` that
`Cluster.eventually_cluster_amplitude_le` derives from
`eq:lower-residue-ratio`. -/
theorem exists_endpoint_dominance_of_threshold {ι : Type*} (s : Finset ι)
    {c ε Amin C σ h : ℝ} {p : ℕ}
    (hA : 0 < Amin) (hC : 0 ≤ C) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hhpos : 0 < h)
    (hcl : ∀ (A ζ : ι → ℝ) (θ W : ℝ), 0 < θ → θ ≤ ε → 0 ≤ W →
      (∀ i ∈ s, |A i| ≤ 2 * W) → (∀ i ∈ s, 1 + c * θ ≤ ζ i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * θ →
          ∑ i ∈ s, |A i| * (ζ i ^ (M + 1))⁻¹ ≤ 1 / 4 * W) :
    ∃ M₀ : ℕ, ∀ (Wf ζ : ι → ℝ) (W E R θ : ℝ) (M : ℕ), M₀ ≤ M →
      0 < θ → θ ≤ ε → h ≤ (M : ℝ) * θ →
      Amin * θ ^ p ≤ W →
      (∀ i ∈ s, |Wf i| ≤ 2 * W) →
      (∀ i ∈ s, 1 + c * θ ≤ ζ i) →
      |E| ≤ C * σ ^ M →
      |R| ≤ (∑ i ∈ s, |Wf i| * (ζ i ^ (M + 1))⁻¹) + |E| →
      |R| ≤ W / 2 := by
  obtain ⟨M₁, hM₁⟩ := exists_pow_mul_geometric_le
    (K := C / Amin * (h ^ p)⁻¹) (δ := 1 / 4) hσ0 hσ1 (by norm_num) p
  refine ⟨max 1 M₁, ?_⟩
  intro Wf ζ W E R θ M hM hθ hθε hhM hWlow hWf hgap hE hR
  have hM1 : 1 ≤ M := le_trans (le_max_left _ _) hM
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hWpos : 0 < W := lt_of_lt_of_le (by positivity) hWlow
  have hθM : h / M ≤ θ := by rw [div_le_iff₀ hMr]; linarith
  -- the nonprincipal cluster
  have hclu : ∑ i ∈ s, |Wf i| * (ζ i ^ (M + 1))⁻¹ ≤ W / 4 := by
    have := hcl Wf ζ θ W hθ hθε hWpos.le hWf hgap M hhM
    linarith [this]
  -- the contour remainder
  have hcon : |E| ≤ W / 4 := by
    have h1 := endpoint_contour_relative_le hhpos hMr hθM hA hC hσ0 hWlow hE
    have h2 := hM₁ M (le_trans (le_max_right _ _) hM)
    have h3 : C / Amin * (h ^ p)⁻¹ * ((M : ℝ) ^ p * σ ^ M) * W ≤ (1 / 4) * W :=
      mul_le_mul_of_nonneg_right h2 hWpos.le
    linarith [h1, h3]
  linarith [hR, hclu, hcon, abs_nonneg R]

/-- **`thm:weighted-dominance`'s endpoint region, with `h` produced.**  This is
`exists_endpoint_dominance_of_threshold` composed with `exists_cluster_threshold`,
and it is the form written before the paper's constant order was read off the
statement: it bundles `h` with `M₀` in one existential, so a caller fixing the
numerator first can only obtain an `h` that has already seen it.  Kept because
consumers are written against it; new callers wanting the paper's
`h = h(Q,r)` should take the threshold form and supply `h` from
`exists_cluster_threshold`, whose statement mentions no numerator data at all. -/
theorem exists_endpoint_dominance {ι : Type*} (s : Finset ι)
    {c ε Amin C σ : ℝ} {p : ℕ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hA : 0 < Amin) (hC : 0 ≤ C)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ (Wf ζ : ι → ℝ) (W E R θ : ℝ) (M : ℕ), M₀ ≤ M →
      0 < θ → θ ≤ ε → h ≤ (M : ℝ) * θ →
      Amin * θ ^ p ≤ W →
      (∀ i ∈ s, |Wf i| ≤ 2 * W) →
      (∀ i ∈ s, 1 + c * θ ≤ ζ i) →
      |E| ≤ C * σ ^ M →
      |R| ≤ (∑ i ∈ s, |Wf i| * (ζ i ^ (M + 1))⁻¹) + |E| →
      |R| ≤ W / 2 := by
  obtain ⟨h, hhpos, hcl⟩ :=
    exists_cluster_threshold s (C_W := 2) (δ := 1 / 4) hc hε (by norm_num) (by norm_num)
  obtain ⟨M₀, hM₀⟩ :=
    exists_endpoint_dominance_of_threshold (p := p) s hA hC hσ0 hσ1 hhpos hcl
  exact ⟨h, hhpos, M₀, hM₀⟩

/-! ### The compact interior -/

/-- **Paper `eq:interior-relative-remainder`.**  On the retained interior, where
the amplitude windows `eq:amplitude-deletion` have been removed and the amplitude
is therefore at least `A e^{-cM}` with `c = \tfrac12log(1/σ)`, the interior
contour remainder is below half the amplitude for all large `M`. -/
theorem exists_interior_dominance {σ C Amin : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hA : 0 < Amin) :
    ∃ M₀ : ℕ, ∀ (W R : ℝ) (M : ℕ), M₀ ≤ M →
      |R| ≤ C * σ ^ M →
      Amin * Real.exp (-((-Real.log σ) / 2) * M) ≤ W →
      |R| ≤ W / 2 := by
  set α : ℝ := -Real.log σ with hα
  have hαpos : 0 < α := by
    have : Real.log σ < 0 := Real.log_neg hσ0 hσ1
    simpa [hα] using neg_pos.mpr this
  set σ' : ℝ := Real.exp (-(α / 2)) with hσ'
  have hσ'0 : 0 ≤ σ' := (Real.exp_pos _).le
  have hσ'1 : σ' < 1 := by
    rw [hσ', Real.exp_lt_one_iff]
    linarith
  obtain ⟨M₁, hM₁⟩ := exists_pow_mul_geometric_le
    (K := C / Amin) (δ := 1 / 2) hσ'0 hσ'1 (by norm_num) 0
  refine ⟨M₁, ?_⟩
  intro W R M hM hR hW
  have hWpos : 0 < W := lt_of_lt_of_le (by positivity) hW
  have h1 := interior_ratio_le M hσ0 hσ1 hA hR hW
  have hexp : Real.exp (-α * (M : ℝ) / 2) = σ' ^ M := by
    rw [hσ', ← Real.exp_nat_mul]
    congr 1
    ring
  have h2 := hM₁ M hM
  rw [pow_zero, one_mul] at h2
  rw [hexp] at h1
  have h3 : C / Amin * σ' ^ M * W ≤ (1 / 2) * W :=
    mul_le_mul_of_nonneg_right h2 hWpos.le
  linarith [h1, h3]

/-! ### The retained range -/

/-- **Paper `thm:weighted-dominance`, `eq:dominance-bound` on
`eq:retained-range`.**  The three regional estimates combine into one `h` and one
`M₀` covering the whole retained range `h/M ≤ θ ≤ π/r - h/M` off the
amplitude windows.

The content is the order of the constants and the closing of the gap between
them: `h` is the larger of the two endpoint thresholds, and `M₀` is large enough
that `h/M ≤ ε`, which is what makes the three regions actually cover
the range — the paper's "choose `M₀` sufficiently large that `h/M₀ < ε`".
No region hypothesis is used outside its own region. -/
theorem exists_dominance_threshold_of_threshold {b ε h : ℝ} {Θ : ℕ → Set ℝ}
    {R : ℕ → ℝ → ℝ} {W : ℝ → ℝ} (hε : 0 < ε) (hhpos : 0 < h)
    (hlow : ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M → ∀ θ : ℝ,
      0 < θ → θ ≤ ε → h ≤ (M : ℝ) * θ → |R M θ| ≤ W θ / 2)
    (hup : ∃ M₂ : ℕ, ∀ M : ℕ, M₂ ≤ M → ∀ θ : ℝ,
      θ < b → b - ε ≤ θ → h ≤ (M : ℝ) * (b - θ) → |R M θ| ≤ W θ / 2)
    (hmid : ∃ M₃ : ℕ, ∀ M : ℕ, M₃ ≤ M → ∀ θ : ℝ,
      ε ≤ θ → θ ≤ b - ε → θ ∉ Θ M → |R M θ| ≤ W θ / 2) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M → |R M θ| ≤ W θ / 2 := by
  obtain ⟨M₁, hlow⟩ := hlow
  obtain ⟨M₂, hup⟩ := hup
  obtain ⟨M₃, hmid⟩ := hmid
  obtain ⟨N, hN⟩ := exists_nat_ge (h / ε)
  refine ⟨max (max M₁ M₂) (max M₃ (max 1 N)), ?_⟩
  intro M hM θ hθlo hθhi hΘ
  have hM1 : 1 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) hM)
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hMN : (N : ℝ) ≤ (M : ℝ) := by
    have : N ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) hM)
    exact_mod_cast this
  have hsmall : h / M ≤ ε := by
    rw [div_le_iff₀ hMr]
    rw [div_le_iff₀ hε] at hN
    nlinarith [hN, hMN, hε, hhpos]
  have hθpos : 0 < θ := lt_of_lt_of_le (by positivity) hθlo
  have hhMθ : h ≤ (M : ℝ) * θ := by rw [div_le_iff₀ hMr] at hθlo; linarith
  rcases le_or_gt θ ε with hcase | hcase
  · exact hlow M (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM) θ hθpos hcase
      hhMθ
  · rcases le_or_gt (b - ε) θ with hcase2 | hcase2
    · have hbθ : h ≤ (M : ℝ) * (b - θ) := by
        have : h / M ≤ b - θ := by linarith
        rw [div_le_iff₀ hMr] at this; linarith
      have hθb : θ < b := by
        have : (0 : ℝ) < h / M := by positivity
        linarith
      exact hup M (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM) θ hθb hcase2
        hbθ
    · refine hmid M (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM) θ
        hcase.le (by linarith) hΘ

/-- `exists_dominance_threshold_of_threshold` with `h` produced as `max` of the two
endpoint thresholds.  Kept for consumers written against the bundled form. -/
theorem exists_dominance_threshold {b ε : ℝ} {Θ : ℕ → Set ℝ} {R : ℕ → ℝ → ℝ} {W : ℝ → ℝ}
    (hε : 0 < ε)
    (hlow : ∃ hL > (0 : ℝ), ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M → ∀ θ : ℝ,
      0 < θ → θ ≤ ε → hL ≤ (M : ℝ) * θ → |R M θ| ≤ W θ / 2)
    (hup : ∃ hU > (0 : ℝ), ∃ M₂ : ℕ, ∀ M : ℕ, M₂ ≤ M → ∀ θ : ℝ,
      θ < b → b - ε ≤ θ → hU ≤ (M : ℝ) * (b - θ) → |R M θ| ≤ W θ / 2)
    (hmid : ∃ M₃ : ℕ, ∀ M : ℕ, M₃ ≤ M → ∀ θ : ℝ,
      ε ≤ θ → θ ≤ b - ε → θ ∉ Θ M → |R M θ| ≤ W θ / 2) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M → |R M θ| ≤ W θ / 2 := by
  obtain ⟨hL, hLpos, M₁, hlow⟩ := hlow
  obtain ⟨hU, hUpos, M₂, hup⟩ := hup
  have hhpos : 0 < max hL hU := lt_of_lt_of_le hLpos (le_max_left _ _)
  obtain ⟨M₀, hM₀⟩ := exists_dominance_threshold_of_threshold (h := max hL hU) hε hhpos
    ⟨M₁, fun M hM θ hθ hθε hhM => hlow M hM θ hθ hθε (le_trans (le_max_left _ _) hhM)⟩
    ⟨M₂, fun M hM θ hθb hθε hhM => hup M hM θ hθb hθε (le_trans (le_max_right _ _) hhM)⟩
    hmid
  exact ⟨max hL hU, hhpos, M₀, hM₀⟩

/-! ### The deleted amplitude windows -/

/-- **Paper `thm:weighted-dominance`, final clause, and
`eq:amplitude-window-negligible`.**  The windows `eq:amplitude-deletion` have
total length `∑_j 2e^{-cM/ν_j}`, and `(M+1)` times that falls below `1` for
all large `M`: the number `J` of amplitude zeros and their multiplicities are
fixed, so the whole deleted set is negligible against the `M+1` phase points
`prop:angular-discrepancy` counts. -/
theorem exists_window_threshold {J n : ℕ} {c : ℝ} (hc : 0 < c) (hn : 1 ≤ n)
    (ν : Fin J → ℕ) (hν1 : ∀ j, 1 ≤ ν j) (hνn : ∀ j, ν j ≤ n) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ((M : ℝ) + 1) * ∑ j, 2 * Real.exp (-(c * M / ν j)) ≤ 1 := by
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set σ : ℝ := Real.exp (-(c / n)) with hσ
  have hσ0 : (0 : ℝ) ≤ σ := (Real.exp_pos _).le
  have hσ1 : σ < 1 := by
    rw [hσ, Real.exp_lt_one_iff]
    have : 0 < c / (n : ℝ) := by positivity
    linarith
  obtain ⟨M₀, hM₀⟩ := exists_succ_pow_mul_geometric_le
    (K := 2 * J) (δ := 1) hσ0 hσ1 (by positivity) (by norm_num) 1
  refine ⟨M₀, fun M hM => ?_⟩
  have hterm : ∀ j : Fin J, 2 * Real.exp (-(c * M / ν j)) ≤ 2 * σ ^ M := by
    intro j
    have hνr : (0 : ℝ) < (ν j : ℝ) := by exact_mod_cast hν1 j
    have hle : (ν j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hνn j
    have hpow : σ ^ M = Real.exp (-(c * M / n)) := by
      rw [hσ, ← Real.exp_nat_mul]
      congr 1
      field_simp
    rw [hpow]
    have : -(c * M / ν j) ≤ -(c * M / n) := by
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      have : c * M / n ≤ c * M / (ν j : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity) hνr hle
      linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) (by norm_num)
  have hsum : ∑ j, 2 * Real.exp (-(c * M / ν j)) ≤ 2 * J * σ ^ M := by
    calc ∑ j, 2 * Real.exp (-(c * M / ν j)) ≤ ∑ _j : Fin J, 2 * σ ^ M :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = 2 * J * σ ^ M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hMpos : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  calc ((M : ℝ) + 1) * ∑ j, 2 * Real.exp (-(c * M / ν j))
      ≤ ((M : ℝ) + 1) * (2 * J * σ ^ M) := mul_le_mul_of_nonneg_left hsum hMpos
    _ = 2 * J * (((M : ℝ) + 1) ^ 1 * σ ^ M) := by rw [pow_one]; ring
    _ ≤ 1 := hM₀ M hM


end ForgacsTran
