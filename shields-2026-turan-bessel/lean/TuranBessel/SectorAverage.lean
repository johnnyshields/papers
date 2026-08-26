/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.FourCopy
import TuranBessel.Sharpness

/-!
# The canonical sector average at general `(κ,τ)`

Formalizes `shields-2026-turan-bessel.tex`, «Four-copy determinant sectors»
(`subsec:four-copy`, `prop:four-copy`, `eq:sector-density`,
`eq:D-canonical-average`) at general `(κ,τ)`.

`FourCopy` defines the microcanonical sector densities `d_n^{(κ,τ)}` and proves
`eq:D-canonical-average` at the endpoint, where `Bridge.hasSum_turanDetCoeff`
identifies `∑ Δ_n λⁿ` with the determinant.  `TuranDetKT.hasSum_turanDetKT`
supplies that identification for every `(κ,τ)`, and `Sharpness.besselDefectKT_eq`
carries it across `eq:D-Delta`, so the same two statements hold on the whole
two-parameter family.  Nothing new is needed beyond joining them: the sector
density is already defined at general `(κ,τ)`, and `4Δ^{(κ,τ)}/(gZ⁴)` is already
its generating value.

Sorry-free.
-/

namespace TuranBessel

variable {a lam κ τ ν x : ℝ}

/-- **`eq:D-canonical-average` at general `(κ,τ)`.**  `4Δ^{(κ,τ)}/(gZ⁴)` is the
canonical average of the microcanonical sector densities `d_n^{(κ,τ)}`.
`FourCopy.hasSum_sectorDensity` is the endpoint case, recovered through
`FourCopy.sectorDensityKT_one_one` and `TuranDetKT.turanDetKT_endpoint`. -/
theorem hasSum_sectorDensityKT (ha : 0 < a) (hlam : 0 ≤ lam) (κ τ : ℝ) :
    HasSum (fun n : ℕ => sectorDensityKT a κ τ n * fourPMF a lam n)
      (4 * turanDetKT a κ τ lam / (trigamma a * Zfun a lam ^ 4)) := by
  have hZ := Zfun_pos ha hlam
  have hg := trigamma_pos ha
  have h := (hasSum_turanDetKT ha κ τ lam).div_const (trigamma a * Zfun a lam ^ 4 / 4)
  have hval : turanDetKT a κ τ lam / (trigamma a * Zfun a lam ^ 4 / 4)
      = 4 * turanDetKT a κ τ lam / (trigamma a * Zfun a lam ^ 4) := by
    field_simp
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  have hT : tweight a n ≠ 0 := (tweight_pos ha n).ne'
  rw [sectorDensityKT, turanCoeffFactor, fourPMF]
  field_simp

/-- **`eq:D-canonical-average` as `prop:four-copy` states it, at general `(κ,τ)`.**
With `a = ν+1` and `λ = (x/2)²`, the Bessel--Schur defect `D_ν^{(κ,τ)}(x)` is the
canonical average `E_λ d_N^{(κ,τ)}` of the sector densities.  `κ` and `τ` enter
only through the sectors, which is `rem:ensemble-positivity`'s reading: the
correction wall is already visible in `d_0^{(κ,τ)} = 4(τ-1)`
(`FourCopy.sectorDensityKT_zero`). -/
theorem besselDefectKT_eq_sectorAverage (hν : -1 < ν) (κ τ : ℝ) :
    HasSum (fun n : ℕ => sectorDensityKT (ν + 1) κ τ n * fourPMF (ν + 1) ((x / 2) ^ 2) n)
      (besselG ν x * (besselHkappa κ ν x + 4 * τ / trigamma (ν + 1))
        - (1 + besselP ν x) ^ 2) := by
  have ha : 0 < ν + 1 := by linarith
  rw [besselDefectKT_eq hν κ τ]
  exact hasSum_sectorDensityKT ha (sq_nonneg _) κ τ

end TuranBessel
