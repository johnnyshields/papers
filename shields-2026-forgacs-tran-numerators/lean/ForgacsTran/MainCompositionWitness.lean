/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.MainComposition
import ForgacsTran.QuadraticWitness

/-!
# A witness for the retained component

`MainComposition.FTRetainedComponent` is what `main_of_ftDominance` and
`main_of_ftBranch_of_geometry` are conditional on, and nothing else in the tree concludes it.
A conditional theorem whose hypothesis nothing satisfies proves nothing while looking
finished, and this is the shape where that is hardest to see: eleven of the twelve clauses are
shared with `MainClauses.FTBranchData`, which is inhabited by
`QuadraticWitness.witness_ftBranchData`, so the surface reading is that the two stand or fall
together.  They do not.  The twelfth clause — the component sits inside the retained range
`h/M ≤ θ ≤ b - h/M` of `eq:retained-range` — is what ties the window width `h` to the defect
constant `C`, and it is absent from `FTBranchData` exactly because `FTBranchData` carries
`eq:dominance-bound` instead.

The Favard pencil `Q = 1 - 4t + t²`, `r = 1`, `B = 1` of `rem:quadratic-case` satisfies it, at
every window width `h > 0` and every index past `4h/π`, on the retained range itself.  There
are no deleted windows: `B = 1` has no zeros, so the principal amplitude does not vanish on
the arc and `eq:Omega-M` is the whole range.

**The defect constant grows with the window width.**  The component loses `h/M` from each end
of `(0,π)`, so the phase turns by `(M+1)(π - 2h/M)` rather than `(M+1)π` and the guaranteed
interior count drops by about `2h/π`.  The witness therefore carries `C = ⌈4h/π⌉₊ + 1`,
against the `C = 2` of `witness_ftBranchData`, and `C` is bound *after* `h` here.

## Main statements

* `witness_ftRetainedComponent` — the retained component, at every window width `h > 0`.
* `witness_ftDominance` — `eq:dominance-bound` on the retained range, the other hypothesis of
  `main_of_ftDominance`; the remainder vanishes identically for a quadratic pencil.
* `witness_main_of_ftDominance` — the two composed, so `thm:main` clauses 1 and 2 hold for the
  Favard pencil with neither a dominance nor a component hypothesis left, and with the
  interior count `M - C` growing with the degree.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `rem:quadratic-case` and
`eq:retained-range` in the service of `thm:main`.

## Tags

witness, retained component, retained range
-/

namespace ForgacsTran

open Polynomial Set

/-- The witness deletes no windows.  `B = 1` has no zeros, so the principal amplitude is
nonvanishing on the whole arc and `eq:Omega-M` is the retained range itself. -/
def witWindow : ℕ → Set ℝ := fun _ => (∅ : Set ℝ)

@[simp] theorem not_mem_witWindow (M : ℕ) (θ : ℝ) : θ ∉ witWindow M := by
  simp [witWindow]

/-- **The retained component.**  `FTRetainedComponent` holds for the Favard pencil
`Q = 1 - 4t + t²`, `r = 1`, `B = 1` at every window width `h > 0` and every index with
`4h ≤ πM`, on the retained range `[h/M, π - h/M]` of `eq:retained-range`, with defect
constant `C = ⌈4h/π⌉₊ + 1`. -/
theorem witness_ftRetainedComponent {hh : ℝ} (hhpos : 0 < hh) {M : ℕ} (hM : 1 ≤ M)
    (hMh : 4 * hh ≤ Real.pi * (M : ℝ)) :
    FTRetainedComponent witQ 1 1 witZ witTau (witP M) M 1 7
      (⌈4 * hh / Real.pi⌉₊ + 1) hh Real.pi witWindow := by
  have hπ : (3 : ℝ) < Real.pi := by have := Real.pi_gt_three; linarith
  have hπ0 : (0 : ℝ) < Real.pi := by linarith
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMR0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hapos : 0 < hh / (M : ℝ) := by positivity
  have ha4 : 4 * (hh / (M : ℝ)) ≤ Real.pi := by
    rw [show 4 * (hh / (M : ℝ)) = 4 * hh / (M : ℝ) by ring, div_le_iff₀ hMR0]
    linarith
  have hab : hh / (M : ℝ) ≤ Real.pi - hh / (M : ℝ) := by linarith
  have hbπ : Real.pi - hh / (M : ℝ) < Real.pi := by linarith
  have hsub : Icc (hh / (M : ℝ)) (Real.pi - hh / (M : ℝ)) ⊆ Icc 0 Real.pi :=
    Icc_subset_Icc hapos.le hbπ.le
  have hsin : ∀ θ ∈ Icc (hh / (M : ℝ)) (Real.pi - hh / (M : ℝ)), 0 < Real.sin θ := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hapos hθ.1)
      (lt_of_le_of_lt hθ.2 hbπ)
  refine ⟨hh / (M : ℝ), Real.pi - hh / (M : ℝ),
    ((M : ℝ) + 1) * (Real.pi - 2 * (hh / (M : ℝ))),
    fun _ => Real.pi / 2, fun θ => ((M : ℝ) + 1) * θ - Real.pi / 2, hab,
    fun θ hθ => ⟨hθ.1, hθ.2, not_mem_witWindow M θ⟩, ?_, ?_, ?_, ?_, ?_, fun θ _ => rfl,
    ⟨fun _ => 0, 0, fun θ _ => hasDerivAt_const θ (Real.pi / 2), fun θ _ => by simp,
      by linarith⟩, ?_, ?_, ?_⟩
  · exact fun θ _ => by rw [witTau_eq]; simp only [quadMod_one]; norm_num
  · exact (quadratic_z_strictMonoOn (by norm_num) (by norm_num) (-4)).mono hsub
  · intro θ _
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    rw [witZ_eq]
    exact ⟨by linarith, by linarith⟩
  · intro θ hθ
    rw [witQ_eq, witZfun_eq, witTau_eq,
      quad_ftAmp (by norm_num) (by norm_num) (-4) (hsin θ hθ).ne']
    refine div_ne_zero Complex.I_ne_zero ?_
    have : (0 : ℝ) < 2 * quadHalf 1 1 * Real.sin θ := by
      rw [quadHalf_one]; have := hsin θ hθ; positivity
    exact_mod_cast this.ne'
  · intro θ hθ
    rw [witQ_eq, witZfun_eq, witTau_eq]
    exact quad_polar (by norm_num) (by norm_num) (-4) (hsin θ hθ)
  · -- `π ≤ L`: the component keeps at least half the arc, and `M + 1 ≥ 2`
    have h1 : Real.pi / 2 ≤ Real.pi - 2 * (hh / (M : ℝ)) := by linarith
    have h2 : (2 : ℝ) * (Real.pi / 2)
        ≤ ((M : ℝ) + 1) * (Real.pi - 2 * (hh / (M : ℝ))) :=
      mul_le_mul (by linarith) h1 (by linarith) (by linarith)
    linarith
  · -- `L ≤ Φ b' - Φ a`, with equality
    change ((M : ℝ) + 1) * (Real.pi - 2 * (hh / (M : ℝ)))
      ≤ (((M : ℝ) + 1) * (Real.pi - hh / (M : ℝ)) - Real.pi / 2)
        - (((M : ℝ) + 1) * (hh / (M : ℝ)) - Real.pi / 2)
    exact le_of_eq (by ring)
  · -- the degree--count comparison: `deg P_M = M` against the turning
    rw [witP_natDegree]
    have hCr : 4 * hh / Real.pi ≤ (⌈4 * hh / Real.pi⌉₊ : ℝ) := Nat.le_ceil _
    have hCπ : 4 * hh ≤ (⌈4 * hh / Real.pi⌉₊ : ℝ) * Real.pi := (div_le_iff₀ hπ0).1 hCr
    have haMr : hh / (M : ℝ) * (M : ℝ) = hh := by field_simp
    have hale : hh / (M : ℝ) ≤ hh := by
      rw [div_le_iff₀ hMR0]; nlinarith
    have key : 2 * (hh / (M : ℝ)) * ((M : ℝ) + 1)
        ≤ (⌈4 * hh / Real.pi⌉₊ : ℝ) * Real.pi := by
      have hexp : 2 * (hh / (M : ℝ)) * ((M : ℝ) + 1)
          = 2 * (hh / (M : ℝ) * (M : ℝ)) + 2 * (hh / (M : ℝ)) := by ring
      rw [hexp, haMr]
      linarith
    have hexpand : ((M : ℝ) + 1) * (Real.pi - 2 * (hh / (M : ℝ))) / Real.pi
        = ((M : ℝ) + 1) - 2 * (hh / (M : ℝ)) * ((M : ℝ) + 1) / Real.pi := by
      field_simp
    have hlast : 2 * (hh / (M : ℝ)) * ((M : ℝ) + 1) / Real.pi
        ≤ (⌈4 * hh / Real.pi⌉₊ : ℝ) := by
      rw [div_le_iff₀ hπ0]; linarith
    rw [hexpand]
    push_cast
    linarith

/-- **`eq:dominance-bound` on the retained range, for the Favard pencil.**  The pencil is
quadratic in `t`, so the principal pair exhausts the denominator and the remainder of
`eq:principal-decomposition` vanishes identically wherever `sin θ ≠ 0`.  The retained range
is interior to `(0,π)` at every `h > 0`, which is all the clause needs. -/
theorem witness_ftDominance {hh : ℝ} (hhpos : 0 < hh) :
    ∀ M : ℕ, 1 ≤ M → ∀ θ : ℝ, hh / (M : ℝ) ≤ θ → θ ≤ Real.pi - hh / (M : ℝ) →
      θ ∉ witWindow M →
      ftRemainder witQ 1 1 witZ witTau M θ ≤ ftPrincipalAmp witQ 1 1 witZ witTau θ / 2 := by
  intro M hM θ hθ1 hθ2 _
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMR0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hapos : 0 < hh / (M : ℝ) := by positivity
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hapos hθ1) (by linarith)
  rw [witQ_eq, witZfun_eq, witTau_eq,
    quad_ftRemainder_eq_zero (by norm_num) (by norm_num) (-4) M hsin]
  have : (0 : ℝ) ≤ ftPrincipalAmp (quadPoly 1 (-4) 1) 1 1 (quadZ 1 (-4) 1)
      (fun _ => quadMod 1 1) θ := norm_nonneg _
  linarith

/-- **`main_of_ftDominance` instantiated.**  Both of its analytic hypotheses hold for the
Favard pencil at every window width `h > 0`, so `thm:main` clauses 1 and 2 come out with no
hypothesis left: at every index past `max(1, ⌈4h/π⌉)` there are at least `M - C` distinct
zeros in `I_{Q,1} = (1,7)`, at most `C` outside it, and at most `C` off `(0,∞)`, with
`C = ⌈4h/π⌉₊ + 1`.

The interior count grows with the degree, so the conclusion is not merely inhabited but
nontrivial — the half `Bridge.ftInputsWitness` does not have.  `C` is bound after `h`, which
is the order the mathematics fixes: a wider deleted window costs interior zeros. -/
theorem witness_main_of_ftDominance {hh : ℝ} (hhpos : 0 < hh) :
    ∀ M : ℕ, max 1 ⌈4 * hh / Real.pi⌉₊ ≤ M →
      (∃ Z : Finset ℂ, M - (⌈4 * hh / Real.pi⌉₊ + 1) ≤ Z.card ∧
          (∀ w ∈ Z, ((witP M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftInterval 1 7))
        ∧ (exceptionalRoots ((witP M).map (algebraMap ℝ ℂ)) (ftInterval 1 7)).card
            ≤ ⌈4 * hh / Real.pi⌉₊ + 1
        ∧ (exceptionalRoots ((witP M).map (algebraMap ℝ ℂ)) posRay).card
            ≤ ⌈4 * hh / Real.pi⌉₊ + 1 := by
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hgeM : ∀ M : ℕ, max 1 ⌈4 * hh / Real.pi⌉₊ ≤ M → 4 * hh ≤ Real.pi * (M : ℝ) := by
    intro M hM
    have h1 : (⌈4 * hh / Real.pi⌉₊ : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hM
    have h2 : 4 * hh / Real.pi ≤ (M : ℝ) := le_trans (Nat.le_ceil _) h1
    rw [div_le_iff₀ hπ0] at h2
    linarith
  have hne : ∀ M : ℕ, max 1 ⌈4 * hh / Real.pi⌉₊ ≤ M →
      (witP M).map (algebraMap ℝ ℂ) ≠ 0 := by
    intro M hM h
    have hd := witP_natDegree M
    rw [h, Polynomial.natDegree_zero] at hd
    have : 1 ≤ M := le_trans (le_max_left _ _) hM
    omega
  have h := main_of_ftDominance (Q := witQ) (B := 1) (r := 1) (z := witZ) (τ := witTau)
    (P := witP) (aI := 1) (bI := 7) (C := ⌈4 * hh / Real.pi⌉₊ + 1)
    (m0 := max 1 ⌈4 * hh / Real.pi⌉₊) (M₀ := max 1 ⌈4 * hh / Real.pi⌉₊)
    (Θ := witWindow) (bb := Real.pi) (h := hh)
    (fun M => witP_map M) hne (by norm_num) le_rfl
    (fun M hM => witness_ftDominance hhpos M (le_trans (le_max_left _ _) hM))
    (fun M hM => witness_ftRetainedComponent hhpos (le_trans (le_max_left _ _) hM)
      (hgeM M hM))
  intro M hM
  have := h M hM
  rwa [witP_natDegree] at this

end ForgacsTran
