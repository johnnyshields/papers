/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperPackage
import ForgacsTran.PrincipalSimpleBranch
import ForgacsTran.AmplitudeBand
import ForgacsTran.InteriorSupply

/-!
# `thm:FT-geometry`'s branch data in the two-endpoint composition's spelling

`exists_ftPhaseSupply_of_dominance` asks for three facts about the principal
branch — the radius is positive, the principal point is a zero of the pencil, and
that zero is simple.  `FTGeometryAssembly.ft_branch_root_and_pos` and
`PrincipalSimpleBranch.ft_principal_simple_at_branch` prove all three
unconditionally, and they state them at `ftBranchZ` and `ftTau`, while the
two-endpoint composition runs at `ftBranchZLower` and `ftTauArc`.

The two spellings **do not** name the same functions.  `ftBranchZLower` is `0`
at `θ ≤ 0` and `ftTauArc` is `0` at `θ ≥ π/r`, where `ftBranchZ` and `ftTau` are
whatever the construction leaves there; each pair agrees only on the *open* arc,
under `ftBranchZLower_agree` and `ftTauArc_agree`.  A statement carried across
without that restriction type-checks on both sides and is false at an endpoint,
so the conversion is stated on `Ioo 0 (π/r)` and nowhere else.

`InteriorBranchSeparation.ft_interior_data_of_minModulus` does the same
conversion for the remainder bound and the amplitude floor; this module does it
for the geometry, which is the other half of what the phase supply consumes.

## Main statements

* `ft_branch_geometry_arc` — the three facts on the open arc, at `ftBranchZLower`
  and `ftTauArc`.
* `ft_branch_geometry_band` — the same restricted to a band `[ε, π/r - ε]`, which
  is the binder shape of `exists_ftPhaseSupply_of_dominance`.
* `exists_band_at_branch` — `hband` at the branch, with nothing assumed.
* `ftAmp_eq_zero_at_branch_of_one_le_mult` — a zero of `B` on the branch is a zero
  of the amplitude.
* `mem_ftAmplitudeDivisor_at_branch` — hence a member of the amplitude divisor of
  the band, which is where `hdom`'s antecedent applies.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:FT-geometry`,
  `lem:amplitude-divisor`, `subsec:proof`.

## Tags

principal branch, simple zero, amplitude divisor, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real

/-- **The three branch facts of `exists_ftPhaseSupply_of_dominance`, at the
composition's own spectral parameter and radius.**

Positivity, the root property and simplicity, all on the open viewing arc, with
no hypothesis beyond the admissible class.  `ftBranchZLower` and `ftTauArc` agree
with `ftBranchZ` and `ftTau` exactly there, so the arc is not a convenience: it is
the largest set on which the statement is about the branch at all. -/
theorem ft_branch_geometry_arc {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ} {z : ℝ → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ) :
    (∀ θ ∈ Ioo (0 : ℝ) (π / r), 0 < ftTauArc a r (n - 1) x₁ θ)
      ∧ (∀ θ ∈ Ioo (0 : ℝ) (π / r),
          (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ)).eval
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) = 0)
      ∧ (∀ θ ∈ Ioo (0 : ℝ) (π / r),
          (derivative (ftDen (ftRootPoly c a) r
              ((z θ : ℝ) : ℂ))).eval
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) ≠ 0) := by
  have hτ : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      ftTauArc a r (n - 1) x₁ θ = ftTau a r (n - 1) θ :=
    fun θ hθ => ftTauArc_agree a r (n - 1) x₁ hθ.1 hθ.2
  obtain ⟨hroot, hpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_, fun θ hθ => ?_⟩
  · rw [hτ θ hθ]
    exact hpos θ hθ
  · rw [hz θ hθ, ftPrincipal_congr (hτ θ hθ)]
    exact hroot θ hθ
  · rw [hz θ hθ, ftPrincipal_congr (hτ θ hθ)]
    exact (ft_principal_simple_at_branch hn ha hc.ne' hr hnr hθ).1

/-- **The conjugate member is simple too**, in the same spelling.  Not consumed by
the phase supply, which asks about the principal point alone; it is here because
`ft_principal_simple_at_branch` proves both and the second half would otherwise be
re-derived at its next use. -/
theorem ft_branch_conj_simple_arc {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ} {z : ℝ → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / r)) :
    (derivative (ftDen (ftRootPoly c a) r
        ((z θ : ℝ) : ℂ))).eval
      ((starRingEnd ℂ) (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)) ≠ 0 := by
  have hτ : ftTauArc a r (n - 1) x₁ θ = ftTau a r (n - 1) θ :=
    ftTauArc_agree a r (n - 1) x₁ hθ.1 hθ.2
  rw [hz θ hθ, ftPrincipal_congr hτ]
  exact (ft_principal_simple_at_branch hn ha hc.ne' hr hnr hθ).2

/-- **The same three on a band `[ε, π/r - ε]`**, which is the binder shape
`exists_ftPhaseSupply_of_dominance` takes them in.  The band sits inside the open
arc for every `ε > 0`, so this is a restriction and carries no further content. -/
theorem ft_branch_geometry_band {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ} {z : ℝ → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ θ ∈ Icc ε (π / r - ε), 0 < ftTauArc a r (n - 1) x₁ θ)
      ∧ (∀ θ ∈ Icc ε (π / r - ε),
          (ftDen (ftRootPoly c a) r ((z θ : ℝ) : ℂ)).eval
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) = 0)
      ∧ (∀ θ ∈ Icc ε (π / r - ε),
          (derivative (ftDen (ftRootPoly c a) r
              ((z θ : ℝ) : ℂ))).eval
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) ≠ 0) := by
  have hsub : Icc ε (π / r - ε) ⊆ Ioo (0 : ℝ) (π / r) := by
    intro θ hθ
    exact ⟨lt_of_lt_of_le hε hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩
  obtain ⟨hτ, hroot, hsimple⟩ :=
    ft_branch_geometry_arc (x₁ := x₁) hn ha hc hr hnr hz
  exact ⟨fun θ hθ => hτ θ (hsub hθ), fun θ hθ => hroot θ (hsub hθ),
    fun θ hθ => hsimple θ (hsub hθ)⟩

/-- **`exists_ftPhaseSupply_of_dominance`'s `hband` at the branch, unconditional.**

`AmplitudeBand.exists_band_of_amplitude_zeros` needs exactly the three facts
above, so once they are stated in the composition's spelling the band comes with
no hypothesis beyond the admissible class and `B ≠ 0`. -/
theorem exists_band_at_branch {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ} {z : ℝ → ℝ}
    {B : Polynomial ℂ} (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ) (hB0 : B ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < π / r - ε ∧
      ∀ θ ∈ Ioo (0 : ℝ) (π / r),
        ftAmp (ftRootPoly c a) B r ((z θ : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) = 0 →
          θ ∈ Icc ε (π / r - ε) := by
  obtain ⟨hτ, hroot, hsimple⟩ :=
    ft_branch_geometry_arc (x₁ := x₁) hn ha hc hr hnr hz
  exact exists_band_of_amplitude_zeros hr hB0 hτ hroot hsimple

/-- **A zero of `B` on the branch is a zero of the amplitude**, in the
composition's spelling.  This is `lem:amplitude-divisor`'s first sentence read in
the direction the seam uses it: a corner of `thm:weighted-dominance` hands over a
retained set whose members carry `1 ≤ ν_j`, and what the divisor of the band is
defined by is the vanishing of `W`. -/
theorem ftAmp_eq_zero_at_branch_of_one_le_mult {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {z : ℝ → ℝ} {B : Polynomial ℂ} (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ)
    (hB0 : B ≠ 0) {θj : ℝ} (hθj : θj ∈ Ioo (0 : ℝ) (π / r))
    (hmult : 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj)) :
    ftAmp (ftRootPoly c a) B r ((z θj : ℝ) : ℂ)
      (ftPrincipal (ftTauArc a r (n - 1) x₁) θj) = 0 := by
  obtain ⟨-, hroot, hsimple⟩ :=
    ft_branch_geometry_arc (x₁ := x₁) hn ha hc hr hnr hz
  have hBz : B.eval (ftPrincipal (ftTauArc a r (n - 1) x₁) θj) = 0 :=
    (Polynomial.rootMultiplicity_pos hB0).1 (by omega)
  exact (ftAmp_eq_zero_iff (hroot θj hθj) (hsimple θj hθj)).2 hBz

/-- **The seam's inclusion.**  A retained parameter of a corner of
`thm:weighted-dominance` — one carrying `1 ≤ ν_j` and located on the open arc —
is a member of the amplitude divisor of the band, which is the set `hdom`'s
antecedent quantifies over.

Both hypotheses are used and neither implies the other: `hmult` is what makes the
amplitude vanish, and `hband` is what puts the parameter inside `[ε, π/r - ε]`
rather than merely inside the arc. -/
theorem mem_ftAmplitudeDivisor_at_branch {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {z : ℝ → ℝ} {B : Polynomial ℂ} (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ)
    (hB0 : B ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hband : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      ftAmp (ftRootPoly c a) B r ((z θ : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) = 0 →
        θ ∈ Icc ε (π / r - ε))
    {θj : ℝ} (hθj : θj ∈ Ioo (0 : ℝ) (π / r))
    (hmult : 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj)) :
    θj ∈ ftAmplitudeDivisor (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) ε (π / r - ε) := by
  have hzero :=
    ftAmp_eq_zero_at_branch_of_one_le_mult hn ha hc hr hnr hz hB0 hθj hmult
  obtain ⟨hτ, hroot, hsimple⟩ :=
    ft_branch_geometry_band (x₁ := x₁) hn ha hc hr hnr hz hε
  exact ftAmplitudeDivisor_complete hB0 (band_subset_Ioo_pi hr hε) hτ hroot hsimple
    (hband θj hθj hzero) hzero

/-- **The three conclusions are assertions, not vacuities.**  At `Q = (1-t)^2`,
`r = 2` the admissible class holds and the viewing arc is inhabited, so each of
the three `∀ θ ∈ Ioo 0 (π/r)` clauses is being claimed of an actual angle — and
the third, a `≠ 0`, is the one a vacuous arc would satisfy for free. -/
theorem ft_branch_geometry_arc_nonvacuous :
    ∃ θ : ℝ, θ ∈ Ioo (0 : ℝ) (π / ((2 : ℕ) : ℝ)) ∧
      0 < ftTauArc (fun _ : Fin 2 => (1 : ℝ)) 2 1 1 θ ∧
      (ftDen (ftRootPoly 1 (fun _ : Fin 2 => (1 : ℝ))) 2
          ((ftBranchZLower (fun _ : Fin 2 => (1 : ℝ)) 1 2 1 θ : ℝ) : ℂ)).eval
        (ftPrincipal (ftTauArc (fun _ : Fin 2 => (1 : ℝ)) 2 1 1) θ) = 0 ∧
      (derivative (ftDen (ftRootPoly 1 (fun _ : Fin 2 => (1 : ℝ))) 2
          ((ftBranchZLower (fun _ : Fin 2 => (1 : ℝ)) 1 2 1 θ : ℝ) : ℂ))).eval
        (ftPrincipal (ftTauArc (fun _ : Fin 2 => (1 : ℝ)) 2 1 1) θ) ≠ 0 := by
  have hmem : (π / 4 : ℝ) ∈ Ioo (0 : ℝ) (π / ((2 : ℕ) : ℝ)) := by
    have := pi_pos
    constructor <;> [linarith; (push_cast; linarith)]
  obtain ⟨hτ, hroot, hsimple⟩ :=
    ft_branch_geometry_arc (a := fun _ : Fin 2 => (1 : ℝ)) (c := 1) (r := 2) (x₁ := 1)
      (z := ftBranchZLower (fun _ : Fin 2 => (1 : ℝ)) 1 2 1)
      (by omega) (fun _ => one_pos) one_pos (by omega) (Or.inl (by omega))
      (fun θ hθ => ftBranchZLower_agree _ _ _ _ hθ.1)
  exact ⟨π / 4, hmem, hτ _ hmem, hroot _ hmem, hsimple _ hmem⟩

end ForgacsTran
