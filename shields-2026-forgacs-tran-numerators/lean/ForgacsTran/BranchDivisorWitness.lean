/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchArcGeometry
import ForgacsTran.CubicBranchBridge
import ForgacsTran.PencilIndex

/-!
# The amplitude divisor is nonempty at the branch

`BranchArcGeometry.mem_ftAmplitudeDivisor_at_branch` carries a retained parameter
into `ftAmplitudeDivisor`, and its own non-vacuity witness does not reach the
multiplicity hypothesis: nothing there exhibits a `B` and a `θ_j` with
`1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc …) θ_j)`, so the divisor was never
shown to be inhabited at the branch's own spelling.  Since the seam exists to
move a *nonempty* retained set across, that lemma was true but unwitnessed.

Two witnesses here, and they cover different things.

**The general one** builds `B` from a branch point rather than hoping a zero of
some fixed `B` lands on the curve: at any admissible pencil and any angle of the
open arc, `branchWitnessB` is the real quadratic whose zeros are that branch point
and its conjugate.  The multiplicity hypothesis then holds by construction, at
every `(n, r)` of the admissible class and every angle.
`scripts/check_band_epsilon_stabilizes.py` runs the same construction numerically.

**The concrete one** is a transfer, not a second pencil.  `CubicWitnessInterior`
already proves `witB.rootMultiplicity (ftPrincipal cubicTau (π/2)) = 1` at
`Q = (1-t)^3`, `B = 3t^2 + 1`, and `CubicBranchBridge.cubicTau_eq_ftTau` identifies
`cubicTau` with `ftTau ![1,1,1] 1 2`; one more step through `ftTauArc_agree` puts it
in this spelling.  Everything is named — the pencil, the numerator, the angle — and
the multiplicity is exactly `1` rather than at least `1`.

**The `z` bridge is absent and is not needed.**  The tree carries no identity
between `cubicZ (cubicTau θ) θ` and `ftBranchZ ![1,1,1] 1 1 2 θ`, which is what
blocks transferring `cubicWitness_hinterior` as a whole.  It does not block this,
because `mem_ftAmplitudeDivisor_at_branch`'s multiplicity hypothesis mentions no
spectral parameter at all — only `ftPrincipal (ftTauArc …) θ_j` — so the radius
bridge alone carries it.

## Main statements

* `exists_nonempty_ftAmplitudeDivisor_at_branch` — at every admissible pencil and
  every angle of the arc, a real `B` with `B(0) ≠ 0` whose divisor contains that
  angle.
* `cubic_mem_ftAmplitudeDivisor` — the same at named data, `r = 1`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `lem:amplitude-divisor`,
  `subsec:proof`.

## Tags

amplitude divisor, non-vacuity, witness, Forgács–Tran branch
-/

namespace ForgacsTran

open Polynomial Set Real

/-! ### The general witness: `B` built from a branch point -/

/-- **The real quadratic vanishing at a prescribed branch point.**  Its zeros are
`t_+(θ)` and its conjugate, so `lem:amplitude-divisor`'s hypothesis holds by
construction rather than by a root of some fixed `B` happening to land on the
curve.  Built as the image of a real polynomial, which is what makes
`HasRealCoeffs` immediate. -/
noncomputable def branchWitnessB {n : ℕ} (a : Fin n → ℝ) (r : ℕ) (x₁ θ : ℝ) :
    Polynomial ℂ :=
  ((X ^ 2 - C (2 * (ftPrincipal (ftTauArc a r (n - 1) x₁) θ).re) * X
      + C (Complex.normSq (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)) :
    Polynomial ℝ)).map (algebraMap ℝ ℂ)

theorem hasRealCoeffs_branchWitnessB {n : ℕ} (a : Fin n → ℝ) (r : ℕ) (x₁ θ : ℝ) :
    HasRealCoeffs (branchWitnessB a r x₁ θ) := by
  intro k
  rw [branchWitnessB, coeff_map]
  simp

theorem branchWitnessB_eval {n : ℕ} (a : Fin n → ℝ) (r : ℕ) (x₁ θ : ℝ) (t : ℂ) :
    (branchWitnessB a r x₁ θ).eval t
      = t ^ 2 - 2 * ((ftPrincipal (ftTauArc a r (n - 1) x₁) θ).re : ℂ) * t
        + ((Complex.normSq (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) : ℝ) : ℂ) := by
  rw [branchWitnessB]
  simp

/-- The witness vanishes at the branch point it was built from.  The identity is
`w^2 - (w + conj w)w + w conj w = 0`, with `2 Re w = w + conj w` and
`normSq w = w conj w`. -/
theorem branchWitnessB_eval_branch {n : ℕ} (a : Fin n → ℝ) (r : ℕ) (x₁ θ : ℝ) :
    (branchWitnessB a r x₁ θ).eval (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) = 0 := by
  set w : ℂ := ftPrincipal (ftTauArc a r (n - 1) x₁) θ with hw
  rw [branchWitnessB_eval, ← Complex.mul_conj]
  have h2 : (2 : ℂ) * ((w.re : ℝ) : ℂ) = w + (starRingEnd ℂ) w := by
    rw [Complex.add_conj]; push_cast; ring
  rw [h2]
  ring

theorem branchWitnessB_ne_zero {n : ℕ} (a : Fin n → ℝ) (r : ℕ) (x₁ θ : ℝ) :
    branchWitnessB a r x₁ θ ≠ 0 := by
  intro h
  have h2 : (branchWitnessB a r x₁ θ).coeff 2 = 1 := by
    rw [branchWitnessB, coeff_map]
    simp
  rw [h] at h2
  simp at h2

/-- `B(0) = |t_+(θ)|^2`, nonzero exactly because the branch radius is. -/
theorem branchWitnessB_eval_zero_ne_zero {n : ℕ} (a : Fin n → ℝ) (r : ℕ) (x₁ θ : ℝ)
    (hτ : 0 < ftTauArc a r (n - 1) x₁ θ) :
    (branchWitnessB a r x₁ θ).eval 0 ≠ 0 := by
  have hne : ftPrincipal (ftTauArc a r (n - 1) x₁) θ ≠ 0 := by
    rw [ftPrincipal]
    exact mul_ne_zero (by exact_mod_cast hτ.ne') (Complex.exp_ne_zero _)
  have hns : Complex.normSq (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) ≠ 0 :=
    fun h => hne (Complex.normSq_eq_zero.1 h)
  rw [branchWitnessB_eval]
  have hz : (0 : ℂ) ^ 2
      - 2 * (((ftPrincipal (ftTauArc a r (n - 1) x₁) θ).re : ℝ) : ℂ) * 0
      + ((Complex.normSq (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) : ℝ) : ℂ)
      = ((Complex.normSq (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) : ℝ) : ℂ) := by ring
  rw [hz]
  exact Complex.ofReal_ne_zero.2 hns

theorem one_le_rootMultiplicity_branchWitnessB {n : ℕ} (a : Fin n → ℝ) (r : ℕ)
    (x₁ θ : ℝ) :
    1 ≤ (branchWitnessB a r x₁ θ).rootMultiplicity
      (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) := by
  have := (Polynomial.rootMultiplicity_pos (branchWitnessB_ne_zero a r x₁ θ)).2
    (branchWitnessB_eval_branch a r x₁ θ)
  omega

/-- **The amplitude divisor is inhabited at the branch, at every admissible pencil
and every angle of the open arc.**  This is what
`mem_ftAmplitudeDivisor_at_branch` was missing: a `B` for which its multiplicity
hypothesis actually holds.  `B` is real with `B(0) ≠ 0`, so it is a numerator the
paper's setting admits and not merely a polynomial of the right shape. -/
theorem exists_nonempty_ftAmplitudeDivisor_at_branch {n r : ℕ} {a : Fin n → ℝ}
    {c x₁ : ℝ} {z : ℝ → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ)
    {θj : ℝ} (hθj : θj ∈ Ioo (0 : ℝ) (π / r)) :
    ∃ (B : Polynomial ℂ) (ε : ℝ), HasRealCoeffs B ∧ B ≠ 0 ∧ B.eval 0 ≠ 0
      ∧ 0 < ε ∧ ε < π / r - ε
      ∧ θj ∈ ftAmplitudeDivisor (ftRootPoly c a) B r z
          (ftTauArc a r (n - 1) x₁) ε (π / r - ε)
      ∧ (ftAmplitudeDivisor (ftRootPoly c a) B r z
          (ftTauArc a r (n - 1) x₁) ε (π / r - ε)).Nonempty := by
  obtain ⟨hτ, -, -⟩ := ft_branch_geometry_arc (x₁ := x₁) (c := c) hn ha hc hr hnr hz
  set B : Polynomial ℂ := branchWitnessB a r x₁ θj with hB
  have hB0 : B ≠ 0 := branchWitnessB_ne_zero a r x₁ θj
  obtain ⟨ε, hε, hεlt, hband⟩ :=
    exists_band_at_branch (x₁ := x₁) (B := B) hn ha hc hr hnr hz hB0
  have hmem := mem_ftAmplitudeDivisor_at_branch (x₁ := x₁) (B := B) hn ha hc hr hnr
    hz hB0 hε hband hθj (one_le_rootMultiplicity_branchWitnessB a r x₁ θj)
  exact ⟨B, ε, hasRealCoeffs_branchWitnessB a r x₁ θj, hB0,
    branchWitnessB_eval_zero_ne_zero a r x₁ θj (hτ θj hθj), hε, hεlt, hmem, ⟨θj, hmem⟩⟩

/-! ### The concrete witness: the cubic pencil, transferred -/

theorem cubicArc_mem : (π / 2 : ℝ) ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) := by
  have := pi_pos
  rw [pi_div_natCast_one]
  constructor <;> linarith

/-- The two radii at `π/2` are the same number: `ftTauArc` is `ftTauLower` below
`π/r`, `ftTauLower` is `ftTau` above `0`, and `cubicTau_eq_ftTau` identifies that
with the witness pencil's own branch. -/
theorem ftTauArc_eq_cubicTau :
    ftTauArc ![1, 1, 1] 1 2 1 (π / 2) = cubicTau (π / 2) := by
  have hpi := pi_pos
  rw [ftTauArc_agree ![1, 1, 1] 1 2 1 cubicArc_mem.1 cubicArc_mem.2]
  exact (cubicTau_eq_ftTau ⟨by linarith, by linarith⟩).symm

theorem ftPrincipal_ftTauArc_eq_cubic :
    ftPrincipal (ftTauArc ![1, 1, 1] 1 2 1) (π / 2) = ftPrincipal cubicTau (π / 2) :=
  ftPrincipal_congr ftTauArc_eq_cubicTau

/-- **The amplitude divisor is inhabited at named data.**  The pencil is
`Q = (1-t)^3` as `ftRootPoly 1 ![1,1,1]`, the numerator is `B = 3t^2 + 1`, the
angle is `π/2`, and `r = 1`.  Nothing is existential except the band's `ε`, and
the multiplicity there is exactly `1` — `witB_rootMultiplicity_pi_div_two` —
rather than merely at least `1`. -/
theorem cubic_mem_ftAmplitudeDivisor :
    ∃ ε : ℝ, 0 < ε ∧ ε < π / ((1 : ℕ) : ℝ) - ε
      ∧ (π / 2 : ℝ) ∈ ftAmplitudeDivisor (ftRootPoly 1 ![1, 1, 1]) witB 1
          (ftBranchZLower ![1, 1, 1] 1 1 2) (ftTauArc ![1, 1, 1] 1 2 1)
          ε (π / ((1 : ℕ) : ℝ) - ε) := by
  have ha : ∀ k, 0 < (![1, 1, 1] : Fin 3 → ℝ) k := by
    intro k; fin_cases k <;> norm_num
  have hmult : 1 ≤ witB.rootMultiplicity
      (ftPrincipal (ftTauArc ![1, 1, 1] 1 2 1) (π / 2)) := by
    rw [ftPrincipal_ftTauArc_eq_cubic, witB_rootMultiplicity_pi_div_two]
  obtain ⟨ε, hε, hεlt, hband⟩ :=
    exists_band_at_branch (n := 3) (r := 1) (a := ![1, 1, 1]) (c := 1) (x₁ := 1)
      (z := ftBranchZLower ![1, 1, 1] 1 1 2) (B := witB) (by omega) ha one_pos
      (le_refl 1) (Or.inl (by omega))
      (fun θ hθ => ftBranchZLower_agree _ _ _ _ hθ.1) witB_ne_zero
  exact ⟨ε, hε, hεlt, mem_ftAmplitudeDivisor_at_branch (n := 3) (r := 1)
    (a := ![1, 1, 1]) (c := 1) (x₁ := 1) (z := ftBranchZLower ![1, 1, 1] 1 1 2)
    (B := witB) (by omega) ha one_pos (le_refl 1) (Or.inl (by omega))
    (fun θ hθ => ftBranchZLower_agree _ _ _ _ hθ.1) witB_ne_zero hε hband
    cubicArc_mem hmult⟩

end ForgacsTran
