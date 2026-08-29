/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.PoleExpansion
import ForgacsTran.Amplitude
import ForgacsTran.WeightedDominance

/-!
# The endpoint region of weighted dominance, at the paper's own objects

`WeightedDominance` proves the endpoint scheme over abstract reals.  This module
instantiates it at `ftCoeffPoly` and `ftAmp`.

## Main statements

* `norm_residue_term` — `‖W_aζ_a^{-M-1}‖ = ‖W_a‖(‖a‖/τ)^{-M-1}`.
* `endpoint_remainder_split` — **the paper's `R_M` bounded at the paper's own
  objects.**  With `s` the set of denominator zeros in `|t| ≤ R_0`, all simple
  and nonzero, and the principal pair `t_± = τ e^{± iθ}` among them,
  `τ^{M+1}F_M(z) - 2Re(W e^{-i(M+1)θ})` is bounded by the nonprincipal
  cluster residues plus one contour error `τ C(τ/R_0)^M`.  Assembled from
  `PoleExpansion.exists_cluster_expansion` and
  `Amplitude.principal_pair_contribution`; nothing is assumed beyond the
  denominator geometry `s` and the principal pair being a root.
* `exists_endpoint_dominance_of_split` — the endpoint region packaged in exactly
  the `hlow` shape `WeightedDominance.exists_dominance_threshold` consumes.
* `exists_upper_endpoint_of_reflected`, `exists_upper_endpoint_dominance_of_split`
  — the same for `hup`, in the reflected variable `η = π/r - θ`.
* `interior_remainder_eq_contour`, `interior_remainder_re_eq_contour` —
  `eq:contour-separated-expansion` on the compact interior as an **identity**:
  the retained cluster is the principal pair alone, so
  `τ^{M+1}F_M(z) - 2Re(W e^{-i(M+1)θ})` *equals* `τ^{M+1}` times
  `PoleExpansion.ftContourRem`, and the second states its real part.  The identity
  is what `eq:C1-interior-remainder` needs: the quantity it differentiates has two
  halves that are each `O(M)` while only their difference is exponentially small,
  so no bound on the difference survives differentiation.
* `norm_smul_ftContourRem_le` — the contour remainder's own bound, in the
  `ftContourRem` name.
* `interior_remainder_bound_of_bound`, `interior_remainder_bound` —
  `eq:interior-relative-remainder`'s remainder, the first being the identity with
  `norm_smul_ftContourRem_le` applied to its right-hand side and the second
  producing the contour constant by compactness.
* `sum_reindex_of_card`, `endpoint_remainder_split_indexed` — the split with the
  nonprincipal cluster enumerated as `j = 1,…,n`, which is the indexed shape
  `exists_endpoint_dominance_of_split` consumes.
* `hsplit_of_indexed_uniform` — the passage from a per-`θ` constant to one
  constant for the window, with what that costs isolated into two binders.

## Implementation notes

**Scope.**  `endpoint_remainder_split` is unconditional for one `θ`: its `C`
is `C_Γ = sup_Γ|B/D|`, produced by `exists_ftDiv_bound` from
compactness of the separating circle.  Passing to one constant for the whole
window is `exists_uniform_ftDiv_bound`, which is the manuscript's sentence "after
decreasing `ε`, the hypotheses of `eq:contour-remainder-bound` are
therefore uniform on each of these regions" — *derived*, from continuity of the
spectral parameter and a zero-free circle, on the closed window.  What it needs
is that `B/D` be read on a fixed circle rather than the retained-set data: the
retained `Finset` loses a member wherever two zeros collide, so `poleRem` and
`poleCofactor` jump there and no bound on them survives the endpoint, while
`B/D` does not move at all.  The one binder `hsplit_of_indexed_uniform` still
isolates is `τ(θ) ≤ τ_{max} ≤ R_0`, which is
`thm:FT-geometry`'s bound on the principal modulus near the endpoint; it does not
mention `F_M`.  Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`,
`subsec:weighted-dominance`, `thm:weighted-dominance`,
`eq:principal-decomposition`, `eq:retained-range`).

## Tags

endpoint region, weighted dominance, denominator pencil
-/

namespace ForgacsTran

open Polynomial Metric Complex

/-- The residue contribution of a single retained pole, in modulus:
`‖W_a ζ_a^{-M-1}‖ = ‖W_a‖ (‖a‖/τ)^{-M-1}`. -/
theorem norm_residue_term {Q B : ℂ[X]} {r : ℕ} {z a : ℂ} {τ : ℝ} (hτ : 0 < τ) (M : ℕ) :
    ‖ftAmp Q B r z a * ((a / (τ : ℂ)) ^ (M + 1))⁻¹‖
      = ‖ftAmp Q B r z a‖ * ((‖a‖ / τ) ^ (M + 1))⁻¹ := by
  rw [norm_mul, norm_inv, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hτ]

/-! ### The contour constant `C_Γ = sup_Γ|B/D|` -/

/-- **The paper's contour constant, produced.**  Where every retained zero lies
strictly inside the circle, the circle carries no zero of the denominator at all,
so `B/D` is continuous on it and bounded by compactness.  This is the constant
`eq:contour-remainder-bound` is stated with — attached to the circle and the
pencil, not to the retained set. -/
theorem exists_ftDiv_bound {Q B : ℂ[X]} {r : ℕ} {zr : ℝ} {s : Finset ℂ} {R₀ : ℝ}
    (haR : ∀ a ∈ s, ‖a‖ < R₀)
    (huniq : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r (zr : ℂ)).eval t = 0 → t ∈ s) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r (zr : ℂ)).eval t‖ ≤ C := by
  have hDne : ∀ t ∈ sphere (0 : ℂ) R₀, (ftDen Q r (zr : ℂ)).eval t ≠ 0 := by
    intro t ht h
    have hnt : ‖t‖ = R₀ := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 ht
    have := haR t (huniq t hnt.le h)
    rw [hnt] at this
    exact lt_irrefl _ this
  have hcont : ContinuousOn (fun t => ‖B.eval t / (ftDen Q r (zr : ℂ)).eval t‖)
      (sphere (0 : ℂ) R₀) :=
    (((continuous_eval B).continuousOn).div ((continuous_eval _).continuousOn) hDne).norm
  obtain ⟨C, hC⟩ :=
    IsCompact.exists_bound_of_continuousOn (isCompact_sphere (0 : ℂ) R₀) hcont
  refine ⟨max C 0, le_max_right _ _, fun t ht => le_trans ?_ (le_max_left _ _)⟩
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC t ht

/-- **The contour constant is uniform on a compact parameter interval.**  This is
the passage the manuscript makes when it says that after decreasing
`ε` the hypotheses of `eq:contour-remainder-bound` are uniform on each
region.  It is a statement about `B/D` on a *fixed* circle, so it survives the
parameter values at which two retained zeros collide — which is precisely where a
bound on the retained-set data does not exist.  Continuity of the spectral
parameter and a zero-free circle are all it needs. -/
theorem exists_uniform_ftDiv_bound {Q B : ℂ[X]} {r : ℕ} {R₀ : ℝ} {z : ℝ → ℝ} {a b : ℝ}
    (hzc : ContinuousOn (fun θ : ℝ => ((z θ : ℝ) : ℂ)) (Set.Icc a b))
    (hDne : ∀ θ ∈ Set.Icc a b, ∀ t ∈ sphere (0 : ℂ) R₀,
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval t ≠ 0) :
    ∃ C ≥ (0 : ℝ), ∀ θ ∈ Set.Icc a b, ∀ t ∈ sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z θ : ℝ) : ℂ)).eval t‖ ≤ C := by
  set K : Set (ℝ × ℂ) := Set.Icc a b ×ˢ sphere (0 : ℂ) R₀ with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_sphere (0 : ℂ) R₀)
  have hnum : ContinuousOn (fun p : ℝ × ℂ => B.eval p.2) K :=
    ((continuous_eval B).comp continuous_snd).continuousOn
  have hzK : ContinuousOn (fun p : ℝ × ℂ => ((z p.1 : ℝ) : ℂ)) K :=
    hzc.comp continuousOn_fst fun p hp => hp.1
  have hden : ContinuousOn (fun p : ℝ × ℂ => (ftDen Q r ((z p.1 : ℝ) : ℂ)).eval p.2) K := by
    simp only [ftDen_eval]
    exact (((continuous_eval Q).comp continuous_snd).continuousOn).add
      (hzK.mul ((continuous_snd.pow r).continuousOn))
  have hcont : ContinuousOn
      (fun p : ℝ × ℂ => ‖B.eval p.2 / (ftDen Q r ((z p.1 : ℝ) : ℂ)).eval p.2‖) K :=
    (hnum.div hden fun p hp => hDne p.1 hp.1 p.2 hp.2).norm
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun θ hθ t ht => le_trans ?_ (le_max_left _ _)⟩
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC (θ, t) ⟨hθ, ht⟩

/-- **Paper `eq:principal-decomposition` at the endpoint, with the retained
cluster displayed.**  With `s` the set of denominator zeros in `|t| ≤ R_0`, all
simple and nonzero, and the principal pair `t_± = τ e^{± iθ}` among
them, the normalized coefficient minus the principal term `2Re(W e^{-i(M+1)θ})`
is bounded by the nonprincipal cluster residues plus a single contour error
`τ C(τ/R_0)^M`.

This is exactly the hypothesis `WeightedDominance.exists_endpoint_dominance`
consumes, at the paper's `ftCoeffPoly` and `ftAmp` rather than at abstract reals.
Nothing is assumed here beyond the denominator geometry `s` and the principal
pair: the decomposition is `PoleExpansion.exists_cluster_expansion` and the
grouping is `Amplitude.principal_pair_contribution`. -/
theorem endpoint_remainder_split_of_bound {Q B : ℂ[X]} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {zr τ θ : ℝ} (hτ : 0 < τ) {s : Finset ℂ} {R₀ C : ℝ} (hR₀ : 0 < R₀) (hτR : τ ≤ R₀)
    (hroot : ∀ a ∈ s, (ftDen Q r (zr : ℂ)).eval a = 0)
    (hsimple : ∀ a ∈ s, (derivative (ftDen Q r (zr : ℂ))).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (haR : ∀ a ∈ s, ‖a‖ < R₀)
    (huniq : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r (zr : ℂ)).eval t = 0 → t ∈ s)
    (hrootplus : (ftDen Q r (zr : ℂ)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) = 0)
    (hne : (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ (τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (hCbd : ∀ t ∈ sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r (zr : ℂ)).eval t‖ ≤ C) :
    ∀ M : ℕ,
      ‖((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
          - ((2 * (((τ : ℂ)) ^ (M + 1)
              * (ftAmp Q B r (zr : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
                  / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1))).re : ℝ) : ℂ)‖
        ≤ (∑ a ∈ (s.erase ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))).erase
              ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)),
             ‖ftAmp Q B r (zr : ℂ) a‖ * ((‖a‖ / τ) ^ (M + 1))⁻¹)
          + τ * C * (τ / R₀) ^ M := by
  classical
  set tp : ℂ := (τ : ℂ) * Complex.exp ((θ : ℂ) * I) with htp
  set tm : ℂ := (τ : ℂ) * Complex.exp (-(θ : ℂ) * I) with htm
  have hτ0 : ((τ : ℂ)) ≠ 0 := by exact_mod_cast hτ.ne'
  have hconj : (starRingEnd ℂ) tp = tm := conj_polar τ θ
  have hrootminus : (ftDen Q r (zr : ℂ)).eval tm = 0 := by
    rw [← hconj]; exact ftDen_eval_conj_eq_zero hQ hrootplus
  have hnormtp : ‖tp‖ = τ := by
    rw [htp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hnormtm : ‖tm‖ = τ := by
    rw [← hconj, RCLike.norm_conj, hnormtp]
  have hplus : tp ∈ s := huniq tp (by rw [hnormtp]; exact hτR) hrootplus
  have hminus : tm ∈ s := huniq tm (by rw [hnormtm]; exact hτR) hrootminus
  have hbd :=
    cluster_expansion_of_div_bound (B := B) hr hQ0 hR₀ hτ hroot hsimple ha0 haR huniq hCbd
  intro M
  set f : ℂ → ℂ := fun a => ftAmp Q B r (zr : ℂ) a * ((a / (τ : ℂ)) ^ (M + 1))⁻¹ with hf
  have hmemtm : tm ∈ s.erase tp := Finset.mem_erase.mpr ⟨fun h => hne h.symm, hminus⟩
  have hsum : ∑ a ∈ s, f a
      = (f tp + f tm) + ∑ a ∈ (s.erase tp).erase tm, f a := by
    rw [← Finset.add_sum_erase s f hplus, ← Finset.add_sum_erase (s.erase tp) f hmemtm]
    ring
  have hpair : f tp + f tm
      = ((2 * (((τ : ℂ)) ^ (M + 1)
          * (ftAmp Q B r (zr : ℂ) tp / tp ^ (M + 1))).re : ℝ) : ℂ) := by
    have hrw : ∀ a : ℂ, a ≠ 0 →
        f a = ((τ : ℂ)) ^ (M + 1) * (ftAmp Q B r (zr : ℂ) a / a ^ (M + 1)) := by
      intro a ha
      change ftAmp Q B r (zr : ℂ) a * ((a / (τ : ℂ)) ^ (M + 1))⁻¹
        = ((τ : ℂ)) ^ (M + 1) * (ftAmp Q B r (zr : ℂ) a / a ^ (M + 1))
      rw [div_pow]
      field_simp
    rw [hrw tp (ha0 tp hplus), hrw tm (ha0 tm hminus), ← hconj]
    exact principal_pair_contribution hQ hB hrootplus
  have hmain := hbd M
  rw [hsum, hpair] at hmain
  have htri : ‖((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
        - ((2 * (((τ : ℂ)) ^ (M + 1) * (ftAmp Q B r (zr : ℂ) tp / tp ^ (M + 1))).re : ℝ) : ℂ)‖
      ≤ ‖∑ a ∈ (s.erase tp).erase tm, f a‖ + τ * C * (τ / R₀) ^ M := by
    have hsplit : ((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
        - ((2 * (((τ : ℂ)) ^ (M + 1) * (ftAmp Q B r (zr : ℂ) tp / tp ^ (M + 1))).re : ℝ) : ℂ)
        = (((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
            - (((2 * (((τ : ℂ)) ^ (M + 1) * (ftAmp Q B r (zr : ℂ) tp / tp ^ (M + 1))).re : ℝ) : ℂ)
              + ∑ a ∈ (s.erase tp).erase tm, f a))
          + ∑ a ∈ (s.erase tp).erase tm, f a := by ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have := hmain
    linarith [norm_add_le
      (((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
        - (((2 * (((τ : ℂ)) ^ (M + 1) * (ftAmp Q B r (zr : ℂ) tp / tp ^ (M + 1))).re : ℝ) : ℂ)
          + ∑ a ∈ (s.erase tp).erase tm, f a))
      (∑ a ∈ (s.erase tp).erase tm, f a)]
  refine le_trans htri ?_
  have hnormsum : ‖∑ a ∈ (s.erase tp).erase tm, f a‖
      ≤ ∑ a ∈ (s.erase tp).erase tm, ‖ftAmp Q B r (zr : ℂ) a‖ * ((‖a‖ / τ) ^ (M + 1))⁻¹ := by
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun a _ => ?_
    rw [hf, norm_residue_term hτ]
  linarith [hnormsum]

/-- **Paper `eq:principal-decomposition` at the endpoint**, with the contour
constant produced by compactness rather than supplied. -/
theorem endpoint_remainder_split {Q B : ℂ[X]} (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {zr τ θ : ℝ} (hτ : 0 < τ) {s : Finset ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀) (hτR : τ ≤ R₀)
    (hroot : ∀ a ∈ s, (ftDen Q r (zr : ℂ)).eval a = 0)
    (hsimple : ∀ a ∈ s, (derivative (ftDen Q r (zr : ℂ))).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (haR : ∀ a ∈ s, ‖a‖ < R₀)
    (huniq : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r (zr : ℂ)).eval t = 0 → t ∈ s)
    (hrootplus : (ftDen Q r (zr : ℂ)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) = 0)
    (hne : (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ (τ : ℂ) * Complex.exp (-(θ : ℂ) * I)) :
    ∃ C ≥ (0 : ℝ), ∀ M : ℕ,
      ‖((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
          - ((2 * (((τ : ℂ)) ^ (M + 1)
              * (ftAmp Q B r (zr : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
                  / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1))).re : ℝ) : ℂ)‖
        ≤ (∑ a ∈ (s.erase ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))).erase
              ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)),
             ‖ftAmp Q B r (zr : ℂ) a‖ * ((‖a‖ / τ) ^ (M + 1))⁻¹)
          + τ * C * (τ / R₀) ^ M := by
  obtain ⟨C, hC0, hCbd⟩ := exists_ftDiv_bound (B := B) haR huniq
  exact ⟨C, hC0, endpoint_remainder_split_of_bound hQ hB hr hQ0 hτ hR₀ hτR hroot hsimple
    ha0 haR huniq hrootplus hne hCbd⟩


/-! ### The endpoint region, in the shape `exists_dominance_threshold` consumes -/

/-- **Paper `thm:weighted-dominance`, one endpoint region, packaged.**  Given the
endpoint supply — the amplitude lower bound `Aθ^p ≤ |W|` of
`lem:amplitude-divisor`, the amplitude comparison `|W_j| ≤ 2|W|` that
`Cluster.eventually_cluster_amplitude_le` derives from `eq:lower-residue-ratio`,
the linear modulus gap `1 + cθ ≤ |ζ_j|` of `eq:endpoint-linear-gap`,
and the split of `eq:principal-decomposition` that `endpoint_remainder_split`
supplies — one `h` and one `M₀` give `|R_M(θ)| ≤ |W(θ)|/2` throughout
the endpoint window.

The conclusion is exactly the `hlow` (equivalently `hup`, after reflecting the
angle) hypothesis of `WeightedDominance.exists_dominance_threshold`. -/
theorem exists_endpoint_dominance_of_split_of_threshold {n : ℕ}
    {ε Amin c Ccont σ h : ℝ} {p : ℕ}
    (hAmin : 0 < Amin) (hC : 0 ≤ Ccont) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hhpos : 0 < h)
    (hcl : ∀ (A ζ' : Fin n → ℝ) (θ W : ℝ), 0 < θ → θ ≤ ε → 0 ≤ W →
      (∀ i ∈ (Finset.univ : Finset (Fin n)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n)), 1 + c * θ ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * θ →
          ∑ i ∈ (Finset.univ : Finset (Fin n)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    {Wamp : ℝ → ℝ} {Wf ζ : ℝ → Fin n → ℝ} {Rrem : ℕ → ℝ → ℝ}
    (hamp : ∀ θ : ℝ, 0 < θ → θ ≤ ε → Amin * θ ^ p ≤ Wamp θ)
    (hCW : ∀ θ : ℝ, 0 < θ → θ ≤ ε → ∀ i, |Wf θ i| ≤ 2 * Wamp θ)
    (hgap : ∀ θ : ℝ, 0 < θ → θ ≤ ε → ∀ i, 1 + c * θ ≤ ζ θ i)
    (hsplit : ∀ M : ℕ, ∀ θ : ℝ, 0 < θ → θ ≤ ε →
      |Rrem M θ| ≤ (∑ i, |Wf θ i| * (ζ θ i ^ (M + 1))⁻¹) + Ccont * σ ^ M) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      0 < θ → θ ≤ ε → h ≤ (M : ℝ) * θ → |Rrem M θ| ≤ Wamp θ / 2 := by
  have hend := exists_endpoint_dominance_of_threshold (ι := Fin n) Finset.univ
    (c := c) (ε := ε) (Amin := Amin) (C := Ccont) (σ := σ) (p := p)
    hAmin hC hσ0 hσ1 hhpos hcl
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      0 < θ → θ ≤ ε → h ≤ (M : ℝ) * θ → |Rrem M θ| ≤ Wamp θ / 2 := by
    obtain ⟨M₀, hM₀⟩ := hend
    refine ⟨M₀, fun M hM θ hθ hθε hhM => ?_⟩
    refine hM₀ (Wf θ) (ζ θ) (Wamp θ) (Ccont * σ ^ M) (Rrem M θ) θ M hM hθ hθε hhM
      (hamp θ hθ hθε) (fun i _ => hCW θ hθ hθε i) (fun i _ => hgap θ hθ hθε i) ?_ ?_
    · rw [abs_of_nonneg (by positivity)]
    · exact le_trans (hsplit M θ hθ hθε) (by
        rw [abs_of_nonneg (show (0:ℝ) ≤ Ccont * σ ^ M by positivity)])
  exact ⟨M₀, hM₀⟩

/-- `exists_endpoint_dominance_of_split_of_threshold` with `h` produced from
`Dominance.exists_cluster_threshold`.  Kept for consumers written against
the bundled form; new callers wanting the paper's `h = h(Q,r)` should take the
threshold form, whose supplying lemma mentions no numerator data. -/
theorem exists_endpoint_dominance_of_split {n : ℕ} {ε Amin c Ccont σ : ℝ} {p : ℕ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hAmin : 0 < Amin) (hC : 0 ≤ Ccont)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {Wamp : ℝ → ℝ} {Wf ζ : ℝ → Fin n → ℝ} {Rrem : ℕ → ℝ → ℝ}
    (hamp : ∀ θ : ℝ, 0 < θ → θ ≤ ε → Amin * θ ^ p ≤ Wamp θ)
    (hCW : ∀ θ : ℝ, 0 < θ → θ ≤ ε → ∀ i, |Wf θ i| ≤ 2 * Wamp θ)
    (hgap : ∀ θ : ℝ, 0 < θ → θ ≤ ε → ∀ i, 1 + c * θ ≤ ζ θ i)
    (hsplit : ∀ M : ℕ, ∀ θ : ℝ, 0 < θ → θ ≤ ε →
      |Rrem M θ| ≤ (∑ i, |Wf θ i| * (ζ θ i ^ (M + 1))⁻¹) + Ccont * σ ^ M) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      0 < θ → θ ≤ ε → h ≤ (M : ℝ) * θ → |Rrem M θ| ≤ Wamp θ / 2 := by
  obtain ⟨h, hhpos, hcl⟩ :=
    exists_cluster_threshold (ι := Fin n) Finset.univ (C_W := 2) (δ := 1 / 4)
      (c := c) (ε := ε) hc hε (by norm_num) (by norm_num)
  obtain ⟨M₀, hM₀⟩ := exists_endpoint_dominance_of_split_of_threshold (p := p)
    hAmin hC hσ0 hσ1 hhpos hcl hamp hCW hgap hsplit
  exact ⟨h, hhpos, M₀, hM₀⟩

/-- The upper endpoint of `eq:retained-range` is the lower one in the reflected
variable `η = π/r - θ`.  This converts the shape
`exists_endpoint_dominance_of_split` produces into the `hup` shape
`WeightedDominance.exists_dominance_threshold` consumes. -/
theorem exists_upper_endpoint_of_reflected {b ε : ℝ} {R : ℕ → ℝ → ℝ} {W : ℝ → ℝ}
    (h : ∃ hU > (0 : ℝ), ∃ M₂ : ℕ, ∀ M : ℕ, M₂ ≤ M → ∀ η : ℝ,
      0 < η → η ≤ ε → hU ≤ (M : ℝ) * η → |R M (b - η)| ≤ W (b - η) / 2) :
    ∃ hU > (0 : ℝ), ∃ M₂ : ℕ, ∀ M : ℕ, M₂ ≤ M → ∀ θ : ℝ,
      θ < b → b - ε ≤ θ → hU ≤ (M : ℝ) * (b - θ) → |R M θ| ≤ W θ / 2 := by
  obtain ⟨hU, hUpos, M₂, hM₂⟩ := h
  refine ⟨hU, hUpos, M₂, fun M hM θ hθb hθε hhU => ?_⟩
  have hη : 0 < b - θ := by linarith
  have hηε : b - θ ≤ ε := by linarith
  have hrw : b - (b - θ) = θ := by ring
  have := hM₂ M hM (b - θ) hη hηε hhU
  rwa [hrw] at this

/-- `exists_upper_endpoint_of_reflected` with the threshold `hU` an input rather
than a bundled existential. -/
theorem exists_upper_endpoint_of_reflected_of_threshold {b ε hU : ℝ}
    {R : ℕ → ℝ → ℝ} {W : ℝ → ℝ}
    (h : ∃ M₂ : ℕ, ∀ M : ℕ, M₂ ≤ M → ∀ η : ℝ,
      0 < η → η ≤ ε → hU ≤ (M : ℝ) * η → |R M (b - η)| ≤ W (b - η) / 2) :
    ∃ M₂ : ℕ, ∀ M : ℕ, M₂ ≤ M → ∀ θ : ℝ,
      θ < b → b - ε ≤ θ → hU ≤ (M : ℝ) * (b - θ) → |R M θ| ≤ W θ / 2 := by
  obtain ⟨M₂, hM₂⟩ := h
  refine ⟨M₂, fun M hM θ hθb hθε hhU => ?_⟩
  have hη : 0 < b - θ := by linarith
  have hηε : b - θ ≤ ε := by linarith
  have hrw : b - (b - θ) = θ := by ring
  have := hM₂ M hM (b - θ) hη hηε hhU
  rwa [hrw] at this

/-! ### The upper endpoint, in the reflected variable -/

/-- **Paper `thm:weighted-dominance`, the upper endpoint region, at a given
threshold.**  The same supply as `exists_endpoint_dominance_of_split_of_threshold`,
read in `η = π/r - θ`, delivered in the `hup` shape
`WeightedDominance.exists_dominance_threshold_of_threshold` consumes.

The threshold `h` is the *same* constant at both endpoints, which is what lets the
composed statement carry one `h` depending on the denominator alone. -/
theorem exists_upper_endpoint_dominance_of_split_of_threshold {n : ℕ}
    {ε b Amin c Ccont σ h : ℝ} {p : ℕ}
    (hAmin : 0 < Amin) (hC : 0 ≤ Ccont) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hhpos : 0 < h)
    (hcl : ∀ (A ζ' : Fin n → ℝ) (η W : ℝ), 0 < η → η ≤ ε → 0 ≤ W →
      (∀ i ∈ (Finset.univ : Finset (Fin n)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n)), 1 + c * η ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * η →
          ∑ i ∈ (Finset.univ : Finset (Fin n)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    {Wamp : ℝ → ℝ} {Wf ζ : ℝ → Fin n → ℝ} {Rrem : ℕ → ℝ → ℝ}
    (hamp : ∀ η : ℝ, 0 < η → η ≤ ε → Amin * η ^ p ≤ Wamp (b - η))
    (hCW : ∀ η : ℝ, 0 < η → η ≤ ε → ∀ i, |Wf (b - η) i| ≤ 2 * Wamp (b - η))
    (hgap : ∀ η : ℝ, 0 < η → η ≤ ε → ∀ i, 1 + c * η ≤ ζ (b - η) i)
    (hsplit : ∀ M : ℕ, ∀ η : ℝ, 0 < η → η ≤ ε →
      |Rrem M (b - η)| ≤ (∑ i, |Wf (b - η) i| * (ζ (b - η) i ^ (M + 1))⁻¹) + Ccont * σ ^ M) :
    ∃ M₂ : ℕ, ∀ M : ℕ, M₂ ≤ M → ∀ θ : ℝ,
      θ < b → b - ε ≤ θ → h ≤ (M : ℝ) * (b - θ) → |Rrem M θ| ≤ Wamp θ / 2 :=
  exists_upper_endpoint_of_reflected_of_threshold
    (exists_endpoint_dominance_of_split_of_threshold (n := n) (Amin := Amin) (p := p)
      (Wamp := fun η => Wamp (b - η)) (Wf := fun η => Wf (b - η)) (ζ := fun η => ζ (b - η))
      (Rrem := fun M η => Rrem M (b - η)) hAmin hC hσ0 hσ1 hhpos hcl hamp hCW hgap hsplit)

/-- `exists_upper_endpoint_dominance_of_split_of_threshold` with `h` produced from
`Dominance.exists_cluster_threshold`.  Kept for consumers written against
the bundled form. -/
theorem exists_upper_endpoint_dominance_of_split {n : ℕ} {ε b Amin c Ccont σ : ℝ} {p : ℕ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hAmin : 0 < Amin) (hC : 0 ≤ Ccont)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {Wamp : ℝ → ℝ} {Wf ζ : ℝ → Fin n → ℝ} {Rrem : ℕ → ℝ → ℝ}
    (hamp : ∀ η : ℝ, 0 < η → η ≤ ε → Amin * η ^ p ≤ Wamp (b - η))
    (hCW : ∀ η : ℝ, 0 < η → η ≤ ε → ∀ i, |Wf (b - η) i| ≤ 2 * Wamp (b - η))
    (hgap : ∀ η : ℝ, 0 < η → η ≤ ε → ∀ i, 1 + c * η ≤ ζ (b - η) i)
    (hsplit : ∀ M : ℕ, ∀ η : ℝ, 0 < η → η ≤ ε →
      |Rrem M (b - η)| ≤ (∑ i, |Wf (b - η) i| * (ζ (b - η) i ^ (M + 1))⁻¹) + Ccont * σ ^ M) :
    ∃ hU > (0 : ℝ), ∃ M₂ : ℕ, ∀ M : ℕ, M₂ ≤ M → ∀ θ : ℝ,
      θ < b → b - ε ≤ θ → hU ≤ (M : ℝ) * (b - θ) → |Rrem M θ| ≤ Wamp θ / 2 := by
  obtain ⟨hU, hUpos, hcl⟩ :=
    exists_cluster_threshold (ι := Fin n) Finset.univ (C_W := 2) (δ := 1 / 4)
      (c := c) (ε := ε) hc hε (by norm_num) (by norm_num)
  obtain ⟨M₂, hM₂⟩ := exists_upper_endpoint_dominance_of_split_of_threshold (p := p) (b := b)
    hAmin hC hσ0 hσ1 hUpos hcl hamp hCW hgap hsplit
  exact ⟨hU, hUpos, M₂, hM₂⟩

/-! ### The compact interior: the principal pair alone -/

/-- **`eq:contour-separated-expansion` at the principal pair, as an identity.**
On the compact interior the retained cluster is the principal pair alone, so the
normalized coefficient minus its principal contribution *equals*
`τ^{M+1}` times the contour remainder — it is not merely bounded by it.

The identity is what a derivative needs.  `eq:C1-interior-remainder` differentiates
`(τ^{M+1}F_M(z(θ))).re/(2|W|) - cos Φ_M` in `θ`, and its two halves are each
`O(M)` while only the difference is exponentially small, so no bound on the
difference survives differentiation.  Reading the difference as one analytic
object — `ftContourRem`, whose `w`-derivative carries the same `R^{-M}` as its
value because differentiating in `w` never touches `t^{-M-1}` — is the only route,
and `PoleExpansion.hasDerivAt_ftContourRem_comp` is what consumes it.

`interior_remainder_bound_of_bound` is this identity with
`PoleExpansion.norm_smul_taylorCoeff_poleRem_le_of_div` applied to the right-hand
side.  Nothing is proved twice.

**Containment.**  No hypothesis mentions `ftContourRem` or `ftCoeffPoly`: what is
asked is the pole structure at the parameter — the pair are simple zeros, they are
distinct, and nothing else lies in the disk. -/
theorem interior_remainder_eq_contour {Q B : ℂ[X]} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {zr τ θ : ℝ} (hτ : 0 < τ) {R₀ : ℝ} (hR₀ : 0 < R₀) (hτR : τ < R₀)
    (hrootplus : (ftDen Q r (zr : ℂ)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) = 0)
    (hsp : (derivative (ftDen Q r (zr : ℂ))).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ≠ 0)
    (hsm : (derivative (ftDen Q r (zr : ℂ))).eval ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)) ≠ 0)
    (hne : (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ (τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (hpairdisk : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r (zr : ℂ)).eval t = 0 →
      t = (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ∨ t = (τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (M : ℕ) :
    ((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
        - ((2 * (((τ : ℂ)) ^ (M + 1)
            * (ftAmp Q B r (zr : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
                / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1))).re : ℝ) : ℂ)
      = ((τ : ℂ)) ^ (M + 1) * ftContourRem Q B r R₀ M (zr : ℂ) := by
  classical
  set D : ℂ[X] := ftDen Q r (zr : ℂ) with hD
  set tp : ℂ := (τ : ℂ) * Complex.exp ((θ : ℂ) * I) with htp
  set tm : ℂ := (τ : ℂ) * Complex.exp (-(θ : ℂ) * I) with htm
  have hτ0 : ((τ : ℂ)) ≠ 0 := by exact_mod_cast hτ.ne'
  have htp0 : tp ≠ 0 := mul_ne_zero hτ0 (Complex.exp_ne_zero _)
  have htm0 : tm ≠ 0 := mul_ne_zero hτ0 (Complex.exp_ne_zero _)
  have hconj : (starRingEnd ℂ) tp = tm := conj_polar τ θ
  have hrootminus : D.eval tm = 0 := by
    rw [← hconj]; exact ftDen_eval_conj_eq_zero hQ hrootplus
  set s : Finset ℂ := {tp, tm} with hs
  have hmemiff : ∀ a : ℂ, a ∈ s ↔ (a = tp ∨ a = tm) := by intro a; simp [hs]
  have hroot : ∀ a ∈ s, D.eval a = 0 := by
    intro a ha; rcases (hmemiff a).mp ha with rfl | rfl
    · exact hrootplus
    · exact hrootminus
  have hsimple : ∀ a ∈ s, (derivative D).eval a ≠ 0 := by
    intro a ha; rcases (hmemiff a).mp ha with rfl | rfl
    · exact hsp
    · exact hsm
  have ha0 : ∀ a ∈ s, a ≠ 0 := by
    intro a ha; rcases (hmemiff a).mp ha with rfl | rfl
    · exact htp0
    · exact htm0
  have hnormtp : ‖tp‖ = τ := by
    rw [htp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hnormtm : ‖tm‖ = τ := by rw [← hconj, RCLike.norm_conj, hnormtp]
  have haR : ∀ a ∈ s, ‖a‖ < R₀ := by
    intro a ha; rcases (hmemiff a).mp ha with rfl | rfl
    · rw [hnormtp]; exact hτR
    · rw [hnormtm]; exact hτR
  have huniq : ∀ t : ℂ, ‖t‖ ≤ R₀ → D.eval t = 0 → t ∈ s :=
    fun t htR ht => (hmemiff t).mpr (hpairdisk t htR ht)
  have hS := poleCofactor_ne_zero (D := D) (s := s) hroot hsimple huniq
  have hS0 := hS 0 (by simp [hR₀.le])
  -- the pole expansion at the pair, with the remainder read as a contour integral
  have hcoeff := taylorCoeff_div_poleExpansion (B := B) (D := D) hroot hsimple ha0 hS0 M
  rw [taylorCoeff_div_ftDen Q B hr hQ0 (zr : ℂ) M] at hcoeff
  have hterm : ∀ a ∈ s,
      ((τ : ℂ)) ^ (M + 1) * (-(poleRes B D a) * (a ^ (M + 1))⁻¹)
        = ftAmp Q B r (zr : ℂ) a * ((a / (τ : ℂ)) ^ (M + 1))⁻¹ := by
    intro a ha
    have hane : (a : ℂ) ≠ 0 := ha0 a ha
    rw [ftAmp_eq_derivative (hroot a ha), poleRes, div_pow]
    field_simp
    rw [hD]
  have hsplit : ((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
        - ∑ a ∈ s, ftAmp Q B r (zr : ℂ) a * ((a / (τ : ℂ)) ^ (M + 1))⁻¹
      = ((τ : ℂ)) ^ (M + 1)
        * Shields.taylorCoeff
            (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) M := by
    rw [hcoeff, mul_add, Finset.mul_sum, Finset.sum_congr rfl hterm]
    ring
  -- the pair sum is the principal contribution of `eq:principal-decomposition`
  have hrw : ∀ a : ℂ, a ≠ 0 →
      ftAmp Q B r (zr : ℂ) a * ((a / (τ : ℂ)) ^ (M + 1))⁻¹
        = ((τ : ℂ)) ^ (M + 1) * (ftAmp Q B r (zr : ℂ) a / a ^ (M + 1)) := by
    intro a ha
    rw [div_pow]
    field_simp
  have hsumpair : ∑ a ∈ s, ftAmp Q B r (zr : ℂ) a * ((a / (τ : ℂ)) ^ (M + 1))⁻¹
      = ((2 * (((τ : ℂ)) ^ (M + 1)
          * (ftAmp Q B r (zr : ℂ) tp / tp ^ (M + 1))).re : ℝ) : ℂ) := by
    rw [hs, Finset.sum_pair hne, hrw tp htp0, hrw tm htm0, ← hconj]
    exact principal_pair_contribution hQ hB hrootplus
  rw [← hsumpair, hsplit,
    taylorCoeff_poleRem_eq_ftContourRem (Q := Q) (B := B) (r := r) (w := (zr : ℂ))
      (s := s) hR₀ hroot hsimple ha0 haR hS]

/-- The real part of `interior_remainder_eq_contour`, which is the form
`eq:C1-interior-remainder` differentiates: the numerator of
`(τ^{M+1}F_M(z)).re/(2|W|) - cos Φ_M` is the real part of one analytic function of
the spectral parameter, not the difference of two `O(M)` halves. -/
theorem interior_remainder_re_eq_contour {Q B : ℂ[X]} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {zr τ θ : ℝ} (hτ : 0 < τ) {R₀ : ℝ} (hR₀ : 0 < R₀) (hτR : τ < R₀)
    (hrootplus : (ftDen Q r (zr : ℂ)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) = 0)
    (hsp : (derivative (ftDen Q r (zr : ℂ))).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ≠ 0)
    (hsm : (derivative (ftDen Q r (zr : ℂ))).eval ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)) ≠ 0)
    (hne : (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ (τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (hpairdisk : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r (zr : ℂ)).eval t = 0 →
      t = (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ∨ t = (τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (M : ℕ) :
    (((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)).re
        - 2 * (((τ : ℂ)) ^ (M + 1)
            * (ftAmp Q B r (zr : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
                / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1))).re
      = (((τ : ℂ)) ^ (M + 1) * ftContourRem Q B r R₀ M (zr : ℂ)).re := by
  have h := congrArg Complex.re
    (interior_remainder_eq_contour hQ hB hr hQ0 hτ hR₀ hτR hrootplus hsp hsm hne hpairdisk M)
  rwa [Complex.sub_re, Complex.ofReal_re] at h

/-- The contour remainder's own bound, in the `ftContourRem` name: this is
`PoleExpansion.norm_smul_taylorCoeff_poleRem_le_of_div` with
`taylorCoeff_poleRem_eq_ftContourRem` applied to its left-hand side. -/
theorem norm_smul_ftContourRem_le {Q B : ℂ[X]} {r : ℕ} {w : ℂ} {s : Finset ℂ}
    {R C τ : ℝ} (hR : 0 < R) (hτ : 0 ≤ τ)
    (hroot : ∀ a ∈ s, (ftDen Q r w).eval a = 0)
    (hsimple : ∀ a ∈ s, (derivative (ftDen Q r w)).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (haR : ∀ a ∈ s, ‖a‖ < R)
    (hS : ∀ t ∈ closedBall (0 : ℂ) R, (poleCofactor (ftDen Q r w) s).eval t ≠ 0)
    (hC : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t / (ftDen Q r w).eval t‖ ≤ C) (M : ℕ) :
    ‖((τ : ℂ)) ^ (M + 1) * ftContourRem Q B r R M w‖ ≤ τ * C * (τ / R) ^ M := by
  rw [← taylorCoeff_poleRem_eq_ftContourRem hR hroot hsimple ha0 haR hS]
  exact norm_smul_taylorCoeff_poleRem_le_of_div hR hτ hroot hsimple ha0 haR hS hC M

/-- **Paper `eq:interior-relative-remainder`, the remainder.**  On the compact
interior the retained cluster is the principal pair alone, so `R_M` *is* the
contour error: `endpoint_remainder_split` at `s = \{t_+, t_-\}` has an empty
nonprincipal sum, leaving `|R_M| ≤ τ C(τ/R_0)^M` with no cluster term.

The hypothesis `hpair` is `thm:FT-geometry`'s minimum-modulus clause — the
principal pair are the only denominator zeros in `|t| ≤ τ`, extended to the
separating radius `R_0` by the compact-interior gap.  It is a statement about the
denominator's zeros, not about the coefficient.

**Differs from the paper's route.**  The paper gives the compact interior its own
passage.  Here it is the endpoint split at `s = \{t_+, t_-\}`: the nonprincipal
sum is then empty, so one theorem covers both regions and the interior needs no
separate contour argument. -/
theorem interior_remainder_bound_of_bound {Q B : ℂ[X]} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {zr τ θ : ℝ} (hτ : 0 < τ) {R₀ C : ℝ} (hR₀ : 0 < R₀) (hτR : τ < R₀)
    (hrootplus : (ftDen Q r (zr : ℂ)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) = 0)
    (hsp : (derivative (ftDen Q r (zr : ℂ))).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ≠ 0)
    (hsm : (derivative (ftDen Q r (zr : ℂ))).eval ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)) ≠ 0)
    (hne : (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ (τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (hpair : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r (zr : ℂ)).eval t = 0 →
      t = (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ∨ t = (τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (hCbd : ∀ t ∈ sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r (zr : ℂ)).eval t‖ ≤ C) :
    ∀ M : ℕ,
      ‖((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
          - ((2 * (((τ : ℂ)) ^ (M + 1)
              * (ftAmp Q B r (zr : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
                  / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1))).re : ℝ) : ℂ)‖
        ≤ τ * C * (τ / R₀) ^ M := by
  classical
  set D : ℂ[X] := ftDen Q r (zr : ℂ) with hD
  set tp : ℂ := (τ : ℂ) * Complex.exp ((θ : ℂ) * I) with htp
  set tm : ℂ := (τ : ℂ) * Complex.exp (-(θ : ℂ) * I) with htm
  have hτ0 : ((τ : ℂ)) ≠ 0 := by exact_mod_cast hτ.ne'
  have htp0 : tp ≠ 0 := mul_ne_zero hτ0 (Complex.exp_ne_zero _)
  have htm0 : tm ≠ 0 := mul_ne_zero hτ0 (Complex.exp_ne_zero _)
  have hconj : (starRingEnd ℂ) tp = tm := conj_polar τ θ
  have hrootminus : D.eval tm = 0 := by
    rw [← hconj]; exact ftDen_eval_conj_eq_zero hQ hrootplus
  set s : Finset ℂ := {tp, tm} with hs
  have hmemiff : ∀ a : ℂ, a ∈ s ↔ (a = tp ∨ a = tm) := by intro a; simp [hs]
  have hroot : ∀ a ∈ s, D.eval a = 0 := by
    intro a ha; rcases (hmemiff a).mp ha with rfl | rfl
    · exact hrootplus
    · exact hrootminus
  have hsimple : ∀ a ∈ s, (derivative D).eval a ≠ 0 := by
    intro a ha; rcases (hmemiff a).mp ha with rfl | rfl
    · exact hsp
    · exact hsm
  have ha0 : ∀ a ∈ s, a ≠ 0 := by
    intro a ha; rcases (hmemiff a).mp ha with rfl | rfl
    · exact htp0
    · exact htm0
  have hnormtp : ‖tp‖ = τ := by
    rw [htp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hnormtm : ‖tm‖ = τ := by rw [← hconj, RCLike.norm_conj, hnormtp]
  have haR : ∀ a ∈ s, ‖a‖ < R₀ := by
    intro a ha; rcases (hmemiff a).mp ha with rfl | rfl
    · rw [hnormtp]; exact hτR
    · rw [hnormtm]; exact hτR
  have huniq : ∀ t : ℂ, ‖t‖ ≤ R₀ → D.eval t = 0 → t ∈ s :=
    fun t htR ht => (hmemiff t).mpr (hpair t htR ht)
  have hS := poleCofactor_ne_zero (D := D) (s := s) hroot hsimple huniq
  intro M
  rw [interior_remainder_eq_contour hQ hB hr hQ0 hτ hR₀ hτR hrootplus hsp hsm hne hpair M]
  exact norm_smul_ftContourRem_le (s := s) hR₀ hτ.le hroot hsimple ha0 haR hS hCbd M

/-- **Paper `eq:interior-relative-remainder`, the remainder**, with the contour
constant produced by compactness. -/
theorem interior_remainder_bound {Q B : ℂ[X]} (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {zr τ θ : ℝ} (hτ : 0 < τ) {R₀ : ℝ} (hR₀ : 0 < R₀) (hτR : τ < R₀)
    (hrootplus : (ftDen Q r (zr : ℂ)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) = 0)
    (hsp : (derivative (ftDen Q r (zr : ℂ))).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ≠ 0)
    (hsm : (derivative (ftDen Q r (zr : ℂ))).eval ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)) ≠ 0)
    (hne : (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ (τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
    (hpair : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r (zr : ℂ)).eval t = 0 →
      t = (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ∨ t = (τ : ℂ) * Complex.exp (-(θ : ℂ) * I)) :
    ∃ C ≥ (0 : ℝ), ∀ M : ℕ,
      ‖((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
          - ((2 * (((τ : ℂ)) ^ (M + 1)
              * (ftAmp Q B r (zr : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
                  / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1))).re : ℝ) : ℂ)‖
        ≤ τ * C * (τ / R₀) ^ M := by
  classical
  set tp : ℂ := (τ : ℂ) * Complex.exp ((θ : ℂ) * I) with htp
  set tm : ℂ := (τ : ℂ) * Complex.exp (-(θ : ℂ) * I) with htm
  have hτ0 : ((τ : ℂ)) ≠ 0 := by exact_mod_cast hτ.ne'
  have hconj : (starRingEnd ℂ) tp = tm := conj_polar τ θ
  have hrootminus : (ftDen Q r (zr : ℂ)).eval tm = 0 := by
    rw [← hconj]; exact ftDen_eval_conj_eq_zero hQ hrootplus
  have hmemiff : ∀ a : ℂ, a ∈ ({tp, tm} : Finset ℂ) ↔ (a = tp ∨ a = tm) := by
    intro a; simp
  have hroot : ∀ a ∈ ({tp, tm} : Finset ℂ), (ftDen Q r (zr : ℂ)).eval a = 0 := by
    intro a ha
    rcases (hmemiff a).mp ha with rfl | rfl
    · exact hrootplus
    · exact hrootminus
  have hsimple : ∀ a ∈ ({tp, tm} : Finset ℂ),
      (derivative (ftDen Q r (zr : ℂ))).eval a ≠ 0 := by
    intro a ha
    rcases (hmemiff a).mp ha with rfl | rfl
    · exact hsp
    · exact hsm
  have hnormtp : ‖tp‖ = τ := by
    rw [htp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hnormtm : ‖tm‖ = τ := by rw [← hconj, RCLike.norm_conj, hnormtp]
  have haR : ∀ a ∈ ({tp, tm} : Finset ℂ), ‖a‖ < R₀ := by
    intro a ha
    rcases (hmemiff a).mp ha with rfl | rfl
    · rw [hnormtp]; exact hτR
    · rw [hnormtm]; exact hτR
  obtain ⟨C, hC0, hCbd⟩ :=
    exists_ftDiv_bound (B := B) (s := ({tp, tm} : Finset ℂ)) haR
      (fun t htR ht => (hmemiff t).mpr (hpair t htR ht))
  exact ⟨C, hC0, interior_remainder_bound_of_bound hQ hB hr hQ0 hτ hR₀ hτR hrootplus hsp hsm
    hne hpair hCbd⟩

/-- The geometric step shared by the endpoint and interior uniformity passes:
a per-parameter bound `τ(θ)C(τ(θ)/R_0)^M` sits under the uniform
`τ_{max}Cσ^M` once `τ ≤ τ_{max}` and `τ_{max}/R_0 ≤ σ`. -/
theorem tau_geom_le {τθ τmax C σ R₀ : ℝ} (hR₀ : 0 < R₀) (hσ : τmax / R₀ ≤ σ)
    (hτ : 0 < τθ) (hτm : τθ ≤ τmax) (hC : 0 ≤ C) (M : ℕ) :
    τθ * C * (τθ / R₀) ^ M ≤ τmax * C * σ ^ M := by
  have hτmax0 : 0 ≤ τmax := le_trans hτ.le hτm
  have hratio : τθ / R₀ ≤ σ := le_trans (by gcongr) hσ
  have hrpow : (τθ / R₀) ^ M ≤ σ ^ M := pow_le_pow_left₀ (by positivity) hratio M
  calc τθ * C * (τθ / R₀) ^ M ≤ τmax * C * (τθ / R₀) ^ M := by
        have hmul : τθ * C ≤ τmax * C := by nlinarith
        exact mul_le_mul_of_nonneg_right hmul (by positivity)
    _ ≤ τmax * C * σ ^ M := mul_le_mul_of_nonneg_left hrpow (by positivity)


/-! ### Indexing the nonprincipal cluster -/

/-- Re-index a sum over a finite set by an injective enumeration of the right
size.  The paper indexes the nonprincipal endpoint cluster by `j = 1,…,ρ-2`
(or `r-2`); `WeightedDominance.exists_endpoint_dominance` wants that indexed
form, while `endpoint_remainder_split` produces the set form. -/
theorem sum_reindex_of_card {α : Type*} {s : Finset α} {n : ℕ}
    (g : Fin n → α) (hg : Function.Injective g) (hmem : ∀ i, g i ∈ s)
    (hcard : s.card = n) (f : α → ℝ) :
    ∑ a ∈ s, f a = ∑ i : Fin n, f (g i) := by
  classical
  have himg : Finset.image g Finset.univ = s := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      exact hmem i
    · rw [hcard, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  rw [← himg]
  exact Finset.sum_image hg.injOn

/-- **`endpoint_remainder_split` in the indexed shape.**  With the `n`
nonprincipal retained members enumerated as `g_1,…,g_n`, the split reads
exactly as `exists_endpoint_dominance_of_split`'s `hsplit` hypothesis, at
`R_M = ‖τ^{M+1}F_M - 2Re(W e^{-i(M+1)θ})‖`,
`W_j = ‖𝒲(g_j)‖` and `ζ_j = ‖g_j‖/τ`. -/
theorem endpoint_remainder_split_indexed_of_bound {Q B : ℂ[X]} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {zr τ θ : ℝ} (hτ : 0 < τ) {s : Finset ℂ} {R₀ C : ℝ} (hR₀ : 0 < R₀) (hτR : τ ≤ R₀)
    (hroot : ∀ a ∈ s, (ftDen Q r (zr : ℂ)).eval a = 0)
    (hsimple : ∀ a ∈ s, (derivative (ftDen Q r (zr : ℂ))).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (haR : ∀ a ∈ s, ‖a‖ < R₀)
    (huniq : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r (zr : ℂ)).eval t = 0 → t ∈ s)
    (hrootplus : (ftDen Q r (zr : ℂ)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) = 0)
    (hne : (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ (τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
    {n : ℕ} (g : Fin n → ℂ) (hginj : Function.Injective g)
    (hgmem : ∀ i, g i ∈ (s.erase ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))).erase
      ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)))
    (hgcard : ((s.erase ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))).erase
      ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I))).card = n)
    (hCbd : ∀ t ∈ sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r (zr : ℂ)).eval t‖ ≤ C) :
    ∀ M : ℕ,
      |‖((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
          - ((2 * (((τ : ℂ)) ^ (M + 1)
              * (ftAmp Q B r (zr : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
                  / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1))).re : ℝ) : ℂ)‖|
        ≤ (∑ i : Fin n, |‖ftAmp Q B r (zr : ℂ) (g i)‖| * ((‖g i‖ / τ) ^ (M + 1))⁻¹)
          + τ * C * (τ / R₀) ^ M := by
  classical
  have hbd := endpoint_remainder_split_of_bound hQ hB hr hQ0 hτ hR₀ hτR hroot hsimple ha0
    haR huniq hrootplus hne hCbd
  intro M
  have hre := sum_reindex_of_card g hginj hgmem hgcard
    (fun a => ‖ftAmp Q B r (zr : ℂ) a‖ * ((‖a‖ / τ) ^ (M + 1))⁻¹)
  rw [abs_of_nonneg (norm_nonneg _)]
  simp only [abs_norm]
  rw [← hre]
  exact hbd M

/-- The indexed split with the contour constant produced by compactness. -/
theorem endpoint_remainder_split_indexed {Q B : ℂ[X]} (hQ : HasRealCoeffs Q)
    (hB : HasRealCoeffs B) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {zr τ θ : ℝ} (hτ : 0 < τ) {s : Finset ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀) (hτR : τ ≤ R₀)
    (hroot : ∀ a ∈ s, (ftDen Q r (zr : ℂ)).eval a = 0)
    (hsimple : ∀ a ∈ s, (derivative (ftDen Q r (zr : ℂ))).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (haR : ∀ a ∈ s, ‖a‖ < R₀)
    (huniq : ∀ t : ℂ, ‖t‖ ≤ R₀ → (ftDen Q r (zr : ℂ)).eval t = 0 → t ∈ s)
    (hrootplus : (ftDen Q r (zr : ℂ)).eval ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) = 0)
    (hne : (τ : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ (τ : ℂ) * Complex.exp (-(θ : ℂ) * I))
    {n : ℕ} (g : Fin n → ℂ) (hginj : Function.Injective g)
    (hgmem : ∀ i, g i ∈ (s.erase ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))).erase
      ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I)))
    (hgcard : ((s.erase ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))).erase
      ((τ : ℂ) * Complex.exp (-(θ : ℂ) * I))).card = n) :
    ∃ C ≥ (0 : ℝ), ∀ M : ℕ,
      |‖((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval (zr : ℂ)
          - ((2 * (((τ : ℂ)) ^ (M + 1)
              * (ftAmp Q B r (zr : ℂ) ((τ : ℂ) * Complex.exp ((θ : ℂ) * I))
                  / ((τ : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ (M + 1))).re : ℝ) : ℂ)‖|
        ≤ (∑ i : Fin n, |‖ftAmp Q B r (zr : ℂ) (g i)‖| * ((‖g i‖ / τ) ^ (M + 1))⁻¹)
          + τ * C * (τ / R₀) ^ M := by
  obtain ⟨C, hC0, hCbd⟩ := exists_ftDiv_bound (B := B) haR huniq
  exact ⟨C, hC0, endpoint_remainder_split_indexed_of_bound hQ hB hr hQ0 hτ hR₀ hτR hroot
    hsimple ha0 haR huniq hrootplus hne g hginj hgmem hgcard hCbd⟩


/-- **The last step to `weighted_dominance`'s `hsplit`, with the uniformity
isolated.**  `endpoint_remainder_split_indexed` gives, for each `θ`, a bound
whose constant `τ(θ)C(θ)` and ratio `τ(θ)/R_0` both move with
`θ`.  `exists_endpoint_dominance_of_split` needs one constant and one ratio
for the whole window.  This converts the first into the second, against
`τ(θ) ≤ τ_{max} ≤ R_0` — `thm:FT-geometry`'s bound on the
principal modulus near the endpoint — and a uniform bound on the contour
constant, which `exists_uniform_ftDiv_bound` supplies at `C_θ ≡ C`.
Neither mentions `F_M`. -/
theorem hsplit_of_indexed_uniform {C σ τmax R₀ ε : ℝ} {τ Cθ : ℝ → ℝ}
    (hR₀ : 0 < R₀) (hσ : τmax / R₀ ≤ σ) (hCnn : 0 ≤ C)
    (hτpos : ∀ θ : ℝ, 0 < θ → θ ≤ ε → 0 < τ θ)
    (hτle : ∀ θ : ℝ, 0 < θ → θ ≤ ε → τ θ ≤ τmax)
    (hC0 : ∀ θ : ℝ, 0 < θ → θ ≤ ε → 0 ≤ Cθ θ)
    (hCunif : ∀ θ : ℝ, 0 < θ → θ ≤ ε → Cθ θ ≤ C)
    {Rrem : ℕ → ℝ → ℝ} {n : ℕ} {Wf ζ : ℝ → Fin n → ℝ}
    (hper : ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ ε →
      |Rrem M θ| ≤ (∑ i, |Wf θ i| * (ζ θ i ^ (M + 1))⁻¹) + τ θ * Cθ θ * (τ θ / R₀) ^ M) :
    ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ ε →
      |Rrem M θ| ≤ (∑ i, |Wf θ i| * (ζ θ i ^ (M + 1))⁻¹) + τmax * C * σ ^ M := by
  intro M θ hθ hθε
  have hτ := hτpos θ hθ hθε
  have hτm := hτle θ hθ hθε
  have hCθ := hC0 θ hθ hθε
  have hCu := hCunif θ hθ hθε
  have hτmax0 : 0 ≤ τmax := le_trans hτ.le hτm
  have hratio : τ θ / R₀ ≤ σ := le_trans (by gcongr) hσ
  have hrpow : (τ θ / R₀) ^ M ≤ σ ^ M := pow_le_pow_left₀ (by positivity) hratio M
  have hkey : τ θ * Cθ θ * (τ θ / R₀) ^ M ≤ τmax * C * σ ^ M := by
    calc τ θ * Cθ θ * (τ θ / R₀) ^ M ≤ τmax * C * (τ θ / R₀) ^ M := by
          have hmul : τ θ * Cθ θ ≤ τmax * C := by nlinarith
          exact mul_le_mul_of_nonneg_right hmul (by positivity)
      _ ≤ τmax * C * σ ^ M := mul_le_mul_of_nonneg_left hrpow (by positivity)
  linarith [hper M θ hθ hθε, hkey]


end ForgacsTran
