/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.TauArcAt
import ForgacsTran.BranchSupplyCubicWitness
import ForgacsTran.CubicRootStates
import ForgacsTran.PencilIndex

/-!
# The composition re-aimed at the corrected arc radius

`CubicPhaseSupplyComposition` was written before `ftTauArcAt` existed and asks for
`hbranch` at `ftTauArc ![1,1,1] 1 2 1`, whose value past `π/r` is `0` — the
convention that is right only when the branch runs into the origin.  The branch
supply is built at `cubicArcTau = ftTauArcAt ![1,1,1] 1 2 1 (1/2)`.

The two agree **strictly below `π`** and differ at `π` itself, so the seam is
crossed by congruence on the sets each hypothesis actually quantifies over — every
one of which excludes `π`, because a band is `[ε, π/r - ε]` and a retained range is
`[h/M, π/r - h/M]`.

Three bridges are needed and all three are proved here or already existed:
`ftRootPoly_one_eq_cubicQ` for the pencil, `ftTauArc_eq_cubicArcTau_of_lt` for the
radius, and `cubicArcZ_eq_ftBranchZLower` for the spectral parameter — the last by
the only route available, since `ftBranchZ` is defined through chords and
`cubicZ` through the closed form: both make the pencil vanish at the same nonzero
point, and a degree-one pencil has only one such value.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `subsec:proof`.

## Tags

phase supply, composition, endpoint convention, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real

/-- **The radii agree strictly below `π/r`**, where both reduce to `ftTauLower`.
No lower bound on `θ` is needed: the two definitions differ only in the `else`
branch. -/
theorem ftTauArc_eq_ftTauArcAt_of_lt {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ aEnd : ℝ)
    {θ : ℝ} (hθ : θ < Real.pi / r) :
    ftTauArc a r l x₁ θ = ftTauArcAt a r l x₁ aEnd θ := by
  rw [ftTauArc_eq_lower a r l x₁ hθ, ftTauArcAt_eq_lower a r l x₁ aEnd hθ]

theorem ftTauArc_eq_cubicArcTau_of_lt {θ : ℝ} (hθ : θ < π) :
    ftTauArc ![1, 1, 1] 1 2 1 θ = cubicArcTau θ := by
  have h1 : θ < π / ((1 : ℕ) : ℝ) := by rw [pi_div_natCast_one]; exact hθ
  rw [cubicArcTau]
  exact ftTauArc_eq_ftTauArcAt_of_lt _ _ _ _ _ h1

/-- **The spectral parameters agree on the open arc.**  `ftBranchZ` is built from
chords and `cubicZ` from the closed form, so they are not equal by unfolding.  Both
make the degree-one pencil vanish at the same nonzero branch point, and there is
only one such value: `Q(w) + z w = 0` determines `z` once `w ≠ 0`. -/
theorem cubicArcZ_eq_ftBranchZLower {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) :
    cubicArcZ θ = ftBranchZLower ![1, 1, 1] 1 1 2 θ := by
  have hτ : cubicArcTau θ = cubicTau θ := cubicArcTau_eq ⟨hθ.1.le, hθ.2.le⟩
  have hbr : FTBranchAt ![1, 1, 1] 1 2 θ := by
    refine ftBranchAt_of_arc_principal (by omega) (fun k => by fin_cases k <;> norm_num)
      le_rfl (Or.inl (by omega)) ?_
    rw [pi_div_natCast_one]; exact hθ
  -- the two roots are the same point
  have hpt : ftPrincipal cubicTau θ = ftPrincipal (ftTau ![1, 1, 1] 1 2) θ :=
    ftPrincipal_congr (cubicTau_eq_ftTau hθ)
  have hw0 : ftPrincipal cubicTau θ ≠ 0 := ftPrincipal_cubicTau_ne_zero θ
  -- each spectral value annihilates the pencil there
  have h1 : (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).eval
      (ftPrincipal cubicTau θ) = 0 := ftDen_cubicQ_eval_cubicTau θ
  have h2 : (ftDen cubicQ 1 ((ftBranchZ ![1, 1, 1] 1 1 2 θ : ℝ) : ℂ)).eval
      (ftPrincipal cubicTau θ) = 0 := by
    rw [hpt, ← ftRootPoly_one_eq_cubicQ]
    exact ftDen_eval_ftPrincipal_ftBranchZ 1 (fun k => by fin_cases k <;> norm_num) hθ hbr
  -- subtract: `(z₁ - z₂) * w = 0`
  rw [ftDen] at h1 h2
  simp only [eval_add, eval_mul, eval_C, eval_X, pow_one] at h1 h2
  have hz : ((cubicZ (cubicTau θ) θ : ℝ) : ℂ) = ((ftBranchZ ![1, 1, 1] 1 1 2 θ : ℝ) : ℂ) := by
    have hsub : (((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
        - ((ftBranchZ ![1, 1, 1] 1 1 2 θ : ℝ) : ℂ)) * ftPrincipal cubicTau θ = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.1 hsub with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hw0
  rw [cubicArcZ, hτ, ftBranchZLower_agree ![1, 1, 1] 1 1 2 hθ.1]
  exact_mod_cast hz

/-- **The amplitude divisor is congruent in `z` and `τ` on its own interval.** -/
theorem ftAmplitudeDivisor_congr {Q B : Polynomial ℂ} {r : ℕ} {z z' τ τ' : ℝ → ℝ}
    {lo hi : ℝ} (hz : ∀ θ ∈ Icc lo hi, z θ = z' θ)
    (hτ : ∀ θ ∈ Icc lo hi, τ θ = τ' θ) :
    ftAmplitudeDivisor Q B r z τ lo hi = ftAmplitudeDivisor Q B r z' τ' lo hi := by
  classical
  rw [ftAmplitudeDivisor, ftAmplitudeDivisor]
  refine Finset.filter_congr fun θ _ => ?_
  constructor
  · rintro ⟨hmem, h0⟩
    refine ⟨hmem, ?_⟩
    rwa [← hz θ hmem, ← ftPrincipal_congr (hτ θ hmem)]
  · rintro ⟨hmem, h0⟩
    refine ⟨hmem, ?_⟩
    rwa [hz θ hmem, ftPrincipal_congr (hτ θ hmem)]

/-! ### The composition, re-aimed -/

/-- **`FTPhaseSupply` at the corrected arc radius**, with `hbranch` stated at the
same `(cubicQ, cubicArcZ, cubicArcTau)` the branch supply is built at.

Every set the transported hypotheses quantify over excludes `π` — a band is
`[ε, π - ε]` with `ε > 0`, and the retained range is `[h/M, π - h/M]` with `M ≥ 1`
— which is why the two radii may be exchanged throughout even though they differ
at `π` itself. -/
theorem cubic_ftPhaseSupply_at_arcTau {κ₀ κ₁ : ℝ}
    (hbranch : ∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc 0 (π / ((1 : ℕ) : ℝ))) →
      (∀ i, Rb i ∈ Icc 0 (π / ((1 : ℕ) : ℝ))) →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ))) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
        ftAmp cubicQ witB 1 ((cubicArcZ θ : ℝ) : ℂ)
          (ftPrincipal cubicArcTau θ) ≠ 0) →
      ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          ftAmp cubicQ witB 1 ((cubicArcZ θ : ℝ) : ℂ) (ftPrincipal cubicArcTau θ)
            = ((ftPrincipalAmp cubicQ witB 1 cubicArcZ cubicArcTau θ : ℝ) : ℂ)
              * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
        (∀ i, 0 ≤ varψ i) ∧
        (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
        ∑ i, varψ i ≤ κ₀ + κ₁ * witB.natDegree) :
    ∃ hcol : ℝ, 0 < hcol ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply cubicQ witB 1 cubicArcZ cubicArcTau hcol κ₀ κ₁ M := by
  have hpi : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  have hpipos := pi_pos
  obtain ⟨hcol, hhcol, Hb⟩ :=
    exists_dominance_bundle_at_branch_one (n := 3) (a := ![1, 1, 1]) (c := 1) (x₁ := 1)
      (by omega) cubicPencil_ha one_pos one_pos cubicPencil_hmin cubicPencil_hcard
      (by omega)
  obtain ⟨ε, σ, hε, hσ0, hσ1, hεband, hτ, hroot, hsimple, hband, hdom⟩ :=
    Hb witB hasRealCoeffs_witB (by rw [witB_eval]; norm_num)
  -- the two spellings may be exchanged on any set that avoids `π`
  have hbandsub : ∀ θ ∈ Icc ε (π / ((1 : ℕ) : ℝ) - ε), θ ∈ Ioo (0 : ℝ) π := by
    intro θ hθ
    rw [hpi] at hθ
    exact ⟨lt_of_lt_of_le hε hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩
  have hzeq : ∀ θ ∈ Icc ε (π / ((1 : ℕ) : ℝ) - ε),
      ftBranchZLower ![1, 1, 1] 1 1 2 θ = cubicArcZ θ :=
    fun θ hθ => (cubicArcZ_eq_ftBranchZLower (hbandsub θ hθ)).symm
  have hteq : ∀ θ ∈ Icc ε (π / ((1 : ℕ) : ℝ) - ε),
      ftTauArc ![1, 1, 1] 1 2 1 θ = cubicArcTau θ :=
    fun θ hθ => ftTauArc_eq_cubicArcTau_of_lt (hbandsub θ hθ).2
  have hQ : ftRootPoly 1 ![1, 1, 1] = cubicQ := ftRootPoly_one_eq_cubicQ
  refine ⟨hcol, hhcol, exists_ftPhaseSupply_of_dominance (Q := cubicQ) (B := witB)
    (r := 1) (z := cubicArcZ) (τ := cubicArcTau) (ε := ε) (σ := σ)
    (hQ ▸ hasRealCoeffs_ftRootPoly 1 ![1, 1, 1]) hasRealCoeffs_witB le_rfl
    (hQ ▸ ftRootPoly_coeff_zero_ne_zero one_ne_zero cubicPencil_ha)
    (hQ ▸ ftRootPoly_coeff_one_ne_zero (by omega) one_ne_zero cubicPencil_ha)
    witB_ne_zero (by rw [witB_eval]; norm_num) hσ0 hσ1 hhcol hεband
    (fun θ hθ => by rw [← hteq θ hθ]; exact hτ θ hθ)
    (fun θ hθ => by
      rw [← hQ, ← hzeq θ hθ, ← ftPrincipal_congr (hteq θ hθ)]; exact hroot θ hθ)
    (fun θ hθ => by
      rw [← hQ, ← hzeq θ hθ, ← ftPrincipal_congr (hteq θ hθ)]; exact hsimple θ hθ)
    ?_ ?_ hbranch⟩
  · -- `hband`, on the open arc
    intro θ hθ hz0
    have hlt : θ < π := by rw [hpi] at hθ; exact hθ.2
    have h0 : θ ∈ Ioo (0 : ℝ) π := ⟨hθ.1, hlt⟩
    refine hband θ hθ ?_
    rw [← hQ, cubicArcZ_eq_ftBranchZLower h0,
      ← ftPrincipal_congr (ftTauArc_eq_cubicArcTau_of_lt hlt)] at hz0
    exact hz0
  · -- `hdom`, transported; `M ≥ 1` keeps the retained range off both endpoints
    obtain ⟨Md, hMd⟩ := hdom
    refine ⟨max Md 1, fun M hM θ h1 h2 hgap => ?_⟩
    have hM1 : 1 ≤ M := le_trans (le_max_right Md 1) hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
    have hcolM : 0 < hcol / M := by positivity
    rw [hpi] at h2
    have h0 : θ ∈ Ioo (0 : ℝ) π := ⟨lt_of_lt_of_le hcolM h1, by linarith⟩
    have hzθ : ftBranchZLower ![1, 1, 1] 1 1 2 θ = cubicArcZ θ :=
      (cubicArcZ_eq_ftBranchZLower h0).symm
    have htθ : ftTauArc ![1, 1, 1] 1 2 1 θ = cubicArcTau θ :=
      ftTauArc_eq_cubicArcTau_of_lt h0.2
    have hdiv : ftAmplitudeDivisor (ftRootPoly 1 ![1, 1, 1]) witB 1
        (ftBranchZLower ![1, 1, 1] 1 1 2) (ftTauArc ![1, 1, 1] 1 2 1) ε
          (π / ((1 : ℕ) : ℝ) - ε)
        = ftAmplitudeDivisor cubicQ witB 1 cubicArcZ cubicArcTau ε
          (π / ((1 : ℕ) : ℝ) - ε) := by
      rw [hQ]; exact ftAmplitudeDivisor_congr hzeq hteq
    have hwin : ftWindowRadius (ftRootPoly 1 ![1, 1, 1]) witB 1
        (ftBranchZLower ![1, 1, 1] 1 1 2) (ftTauArc ![1, 1, 1] 1 2 1) ε σ M
        = ftWindowRadius cubicQ witB 1 cubicArcZ cubicArcTau ε σ M := by
      rw [ftWindowRadius, ftWindowRadius, hdiv]
    have hres := hMd M (le_trans (le_max_left _ _) hM) θ h1 (by rw [hpi]; linarith)
      (fun θj hθj => by rw [hwin]; exact hgap θj (hdiv ▸ hθj))
    simp only [show (3 : ℕ) - 1 = 2 from rfl] at hres
    rw [ftRemainder, ftPrincipalAmp, ftAmp, hQ, hzθ, ftPrincipal_congr htθ, htθ] at hres
    rw [ftRemainder, ftPrincipalAmp, ftAmp]
    exact hres

/-- **`FTPhaseSupply` at a named pencil, with no hypotheses at all.**

`Q = (1-t)^3`, `r = 1`, `B = 3t^2 + 1`, at the corrected arc radius.  The
dominance half is this file's chain through the `ρ ≥ 2, r = 1` cell; the branch
half is `CubicRootStates.cubic_branchSupply`.  Nothing is assumed. -/
theorem cubic_ftPhaseSupply :
    ∃ κ₀ κ₁ hcol : ℝ, 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧ 0 < hcol ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply cubicQ witB 1 cubicArcZ cubicArcTau hcol κ₀ κ₁ M := by
  have hpi : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  obtain ⟨κ₀, κ₁, hκ₀, hκ₁, Mb, Hb⟩ := cubic_branchSupply
  -- the witness predates the containment binder and concludes from FEWER
  -- hypotheses, so it supplies the weaker form by discarding the extra argument
  obtain ⟨hcol, hhcol, hs⟩ :=
    cubic_ftPhaseSupply_at_arcTau (κ₀ := κ₀) (κ₁ := κ₁)
      ⟨Mb, by
        rw [hpi]
        exact fun M hM k Lb Rb hL hR hord _ hne => by
          simpa [cubicArcAmp] using Hb M hM k Lb Rb hL hR hord hne⟩
  exact ⟨κ₀, κ₁, hcol, hκ₀, hκ₁, hhcol, hs⟩

end ForgacsTran
