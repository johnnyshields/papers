/-
# Analytic bridge and Bessel consequences

The proven core (`coefficientwise_positivity`) concerns `Dcoeff a n`, the
combinatorial mixed-determinant sum built from the closed-form coefficient
matrices `N_m`.  Two ingredients of `shields-2026-turan-bessel.tex` sit outside
current Mathlib and are isolated here as **named axioms**, each documenting the
missing dependency:

1. **The coefficient formulas** — §4 «Reciprocal-gamma convolution and coefficient
   formulas» (`sec:coefficients`, `thm:coefficients`, `lem:convolution`).  That the
   Maclaurin coefficient of `det 𝒯` really is `S_m M_m`-structured rests on an
   asymmetric reciprocal-gamma convolution — the Gauss ₂F₁ (Chu–Vandermonde)
   theorem for real parameters, which Mathlib does not have.

2. **The Bessel dictionary** — §3 «Exact reduction from ₀F₁ to the Bessel
   inequality» (`sec:bessel-reduction`, `eq:I-Z`, `eq:D-Delta`).  The identity
   `I_{a-1}(2√λ) = λ^{(a-1)/2} Z(a,λ)` and the log-derivative dictionary need the
   modified Bessel functions `I_ν, K_ν`, absent from Mathlib.

Everything below the axioms is proven and *consumes* `coefficientwise_positivity`:
the paper's coefficientwise statements for the true Turán determinant and for the
Bessel–Schur determinant follow unconditionally *given* the two bridge axioms.

The §2 «Main results» pointwise inequality `thm:bessel` and matrix corollary
`cor:bessel-matrix` are recorded as statements with a single documented `sorry`
naming the residual analytic step (assembling the positive Maclaurin series into
the pointwise value, which needs the Bessel machinery of ingredient 2).
-/
import TuranBessel.Main

namespace TuranBessel

/-! ### Bridge 1 — the true Turán-determinant coefficients -/

/-- The positive normalization `ψ₁(a) Γ(a)^{-4}/2 = Δ_n / Dcoeff`, via `Real.Gamma`. -/
noncomputable def turanCoeffFactor (a : ℝ) : ℝ := trigamma a / (2 * Real.Gamma a ^ 4)

theorem turanCoeffFactor_pos (a : ℝ) (ha : 0 < a) : 0 < turanCoeffFactor a :=
  div_pos (trigamma_pos ha)
    (mul_pos (by norm_num) (pow_pos (Real.Gamma_pos_of_pos ha) 4))

/-- `Δ_n(a) = [λⁿ] det 𝒯(a,λ)`, the genuine Maclaurin coefficient. -/
axiom turanDetCoeff : ℝ → ℕ → ℝ

/-- **eq:Delta-n-MD (bridge).**  The reciprocal-gamma convolution identifies the
determinant coefficient with the mixed-determinant sum.  Requires the real-
parameter Gauss ₂F₁ theorem (`lem:convolution`), not in Mathlib. -/
axiom turanDetCoeff_eq (a : ℝ) (n : ℕ) :
    turanDetCoeff a n = turanCoeffFactor a * Dcoeff a n

/-- **`thm:coefficientwise` for the true determinant.**  Every positive-degree
Maclaurin coefficient of `det 𝒯(a,·)` is strictly positive for `a > 0` — proven
from `coefficientwise_positivity` and the bridge. -/
theorem turanDetCoeff_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    0 < turanDetCoeff a n := by
  rw [turanDetCoeff_eq]
  exact mul_pos (turanCoeffFactor_pos a ha) (coefficientwise_positivity ha hn)

/-! ### Bridge 2 — the Bessel–Schur determinant -/

/-- The curvature functionals `G_ν, P_ν, H_ν` of eq:Gnu–eq:Hnu.  Opaque: Mathlib
has no modified Bessel functions to define them from. -/
axiom besselG : ℝ → ℝ → ℝ
axiom besselP : ℝ → ℝ → ℝ
axiom besselH : ℝ → ℝ → ℝ

/-- `[λⁿ] D_{a-1}(2√λ)`, the Maclaurin coefficient of the Bessel–Schur
determinant defect. -/
axiom besselSchurCoeff : ℝ → ℕ → ℝ

/-- **eq:D-Delta (bridge).**  `D_{a-1}(2√λ) = 4 Δ(a,λ)/(ψ₁(a) Z⁴)`, so its
coefficients are a positive multiple of the determinant coefficients.  Requires
the dictionary eq:I-Z (modified Bessel functions), not in Mathlib. -/
axiom besselSchurCoeff_eq (a : ℝ) (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ besselSchurCoeff a n = c * turanDetCoeff a n

/-- **Coefficientwise Bessel–Schur positivity.**  For `a > 0` (`ν = a-1 > -1`),
every positive-degree small-argument coefficient of the Bessel–Schur defect is
strictly positive — proven from `turanDetCoeff_pos`. -/
theorem besselSchurCoeff_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    0 < besselSchurCoeff a n := by
  obtain ⟨c, hc, heq⟩ := besselSchurCoeff_eq a n
  rw [heq]
  exact mul_pos hc (turanDetCoeff_pos ha hn)

/-! ### Pointwise Bessel inequality and interpretations (residual analytic steps) -/

/-- **Sharp mixed Bessel–Schur inequality** (`thm:bessel`, eq:bessel-main): for
`ν > -1`, `z > 0`,
`G_ν(z)(H_ν(z) + 4/ψ₁(ν+1)) > (1 + P_ν(z))²`.

Reduction (machine-checked at the coefficient level above): the defect is a
positive multiple of `Δ(a,λ) = Σ_{n≥1} Δ_n(a) λⁿ` with each `Δ_n > 0`
(`besselSchurCoeff_pos`).  The residual `sorry` is the routine assembly of the
strictly-positive Maclaurin series into the pointwise value for `λ > 0`, which
needs the modified Bessel functions absent from Mathlib. -/
theorem bessel_schur_ineq {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) :
    (1 + besselP ν z) ^ 2 < besselG ν z * (besselH ν z + 4 / trigamma (ν + 1)) := by
  sorry

/-- `G_ν(z) = -∂²_ν log I_ν(z) > 0` for `ν>-1`, `z>0` (order log-convexity of
`I_ν`).  Opaque with `besselG`; a consequence of the strict total positivity of
the kernel `I_ν(z)`. -/
axiom besselG_pos {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) : 0 < besselG ν z

/-- **Positive Bessel–Schur matrix** (`cor:bessel-matrix`): the `2×2` matrix is
positive definite for `ν>-1`, `z>0` — the leading entry from `besselG_pos`, the
determinant from `bessel_schur_ineq`. -/
theorem bessel_schur_matrix_pd {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) :
    SymMat.PD ⟨besselG ν z, 1 + besselP ν z, besselH ν z + 4 / trigamma (ν + 1)⟩ :=
  ⟨besselG_pos hν hz, bessel_schur_ineq hν hz⟩

end TuranBessel
