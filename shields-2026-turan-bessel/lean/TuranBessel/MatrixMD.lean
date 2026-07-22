/-
# Real symmetric 2×2 matrices and the mixed determinant

Formalizes the elementary matrix algebra behind
`shields-2026-turan-bessel.tex`, §5 «Mixed determinants and coefficientwise
positivity» (`sec:determinant`), `lem:MD-positive`:

* `SymMat`               — a real symmetric `2×2` matrix `⟨a11, a12, a22⟩`.
* `SymMat.MD`            — the mixed determinant `x₁₁y₂₂ + x₂₂y₁₁ - 2x₁₂y₁₂`,
                           the polarization of `det`.
* `MD_nonneg`            — `lem:MD-positive`, non-strict half:
                           `X, Y ⪰ 0 ⟹ MD(X,Y) ≥ 0`.
* `MD_pos_of_psd_pd`     — `lem:MD-positive`, strict half:
                           `X ⪰ 0`, `X ≠ 0`, `Y ≻ 0 ⟹ MD(X,Y) > 0`.

Everything here is sorry-free (pure `ring`/`nlinarith`).
-/
import Mathlib.Tactic

namespace TuranBessel

/-- A real symmetric `2×2` matrix, stored by its three distinct entries
`⟨a11, a12, a22⟩`. -/
structure SymMat where
  a11 : ℝ
  a12 : ℝ
  a22 : ℝ

namespace SymMat

@[ext] theorem ext {X Y : SymMat}
    (h11 : X.a11 = Y.a11) (h12 : X.a12 = Y.a12) (h22 : X.a22 = Y.a22) : X = Y := by
  cases X; cases Y; simp_all

/-- Mixed determinant `x₁₁y₂₂ + x₂₂y₁₁ - 2 x₁₂ y₁₂`; the polarization of
`det X = a11 a22 - a12²` (`det (X+Y) = det X + det Y + MD X Y`, in `stale/`). -/
def MD (X Y : SymMat) : ℝ := X.a11 * Y.a22 + X.a22 * Y.a11 - 2 * X.a12 * Y.a12

/-- Positive semidefinite: nonnegative diagonal and nonnegative determinant. -/
def PSD (M : SymMat) : Prop := 0 ≤ M.a11 ∧ 0 ≤ M.a22 ∧ M.a12 ^ 2 ≤ M.a11 * M.a22

/-- Positive definite: `a11 > 0` and `det > 0`. -/
def PD (M : SymMat) : Prop := 0 < M.a11 ∧ M.a12 ^ 2 < M.a11 * M.a22

instance : Zero SymMat := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem zero_a11 : (0 : SymMat).a11 = 0 := rfl
@[simp] theorem zero_a12 : (0 : SymMat).a12 = 0 := rfl
@[simp] theorem zero_a22 : (0 : SymMat).a22 = 0 := rfl

theorem MD_comm (X Y : SymMat) : MD X Y = MD Y X := by
  simp only [MD]; ring

/-- Positive definite matrices are positive semidefinite. -/
theorem PD.psd {M : SymMat} (h : PD M) : PSD M := by
  obtain ⟨h11, hdet⟩ := h
  refine ⟨h11.le, ?_, hdet.le⟩
  nlinarith [sq_nonneg M.a12]

/-- A nonzero PSD matrix has a strictly positive diagonal entry. -/
theorem PSD.pos_diag_of_ne {M : SymMat} (hM : PSD M) (hne : M ≠ 0) :
    0 < M.a11 ∨ 0 < M.a22 := by
  obtain ⟨h11, h22, hdet⟩ := hM
  by_contra h
  rw [not_or, not_lt, not_lt] at h
  obtain ⟨h1, h2⟩ := h
  have e11 : M.a11 = 0 := le_antisymm h1 h11
  have e22 : M.a22 = 0 := le_antisymm h2 h22
  have e12 : M.a12 = 0 := by nlinarith [sq_nonneg M.a12]
  exact hne (SymMat.ext (by simp [e11]) (by simp [e12]) (by simp [e22]))

/-- `lem:MD-positive`, non-strict half.  If `X, Y ⪰ 0` then `MD(X,Y) ≥ 0`. -/
theorem MD_nonneg {X Y : SymMat} (hX : PSD X) (hY : PSD Y) : 0 ≤ MD X Y := by
  obtain ⟨hx11, hx22, hxdet⟩ := hX
  obtain ⟨hy11, hy22, hydet⟩ := hY
  -- `(x₁₂y₁₂)² ≤ (x₁₁x₂₂)(y₁₁y₂₂)`, together with `S² ≥ 4(x₁₁x₂₂)(y₁₁y₂₂)`.
  have hprod : X.a12 ^ 2 * Y.a12 ^ 2 ≤ (X.a11 * X.a22) * (Y.a11 * Y.a22) :=
    mul_le_mul hxdet hydet (sq_nonneg _) (mul_nonneg hx11 hx22)
  simp only [MD]
  nlinarith [sq_nonneg (X.a11 * Y.a22 - X.a22 * Y.a11), hprod,
    mul_nonneg hx11 hy22, mul_nonneg hx22 hy11]

/-- `lem:MD-positive`, strict half.  If `X ⪰ 0`, `X ≠ 0`, and `Y ≻ 0`, then
`MD(X,Y) > 0`. -/
theorem MD_pos_of_psd_pd {X Y : SymMat} (hX : PSD X) (hXne : X ≠ 0) (hY : PD Y) :
    0 < MD X Y := by
  obtain ⟨hx11, hx22, hxdet⟩ := hX
  obtain ⟨hy11, hydet⟩ := hY
  have hy22 : 0 < Y.a22 := by nlinarith [sq_nonneg Y.a12]
  have hdiag : 0 < X.a11 ∨ 0 < X.a22 := PSD.pos_diag_of_ne ⟨hx11, hx22, hxdet⟩ hXne
  have hSnonneg : 0 ≤ X.a11 * Y.a22 + X.a22 * Y.a11 :=
    add_nonneg (mul_nonneg hx11 hy22.le) (mul_nonneg hx22 hy11.le)
  simp only [MD]
  by_cases hsign : X.a12 * Y.a12 ≤ 0
  · -- `c ≤ 0`: then `S > 0 ≥ 2c`.
    rcases hdiag with h | h
    · nlinarith [mul_pos h hy22, mul_nonneg hx22 hy11.le]
    · nlinarith [mul_pos h hy11, mul_nonneg hx11 hy22.le]
  · -- `c > 0`: then `x₁₂ ≠ 0`, so `x₁₂² > 0`, giving a strict Cauchy–Schwarz.
    rw [not_le] at hsign
    have hx12ne : X.a12 ≠ 0 := by
      rintro h0; rw [h0, zero_mul] at hsign; exact lt_irrefl _ hsign
    have hx12 : 0 < X.a12 ^ 2 := by positivity
    have step1 : X.a12 ^ 2 * Y.a12 ^ 2 < X.a12 ^ 2 * (Y.a11 * Y.a22) :=
      mul_lt_mul_of_pos_left hydet hx12
    have step2 : X.a12 ^ 2 * (Y.a11 * Y.a22) ≤ (X.a11 * X.a22) * (Y.a11 * Y.a22) :=
      mul_le_mul_of_nonneg_right hxdet (mul_nonneg hy11.le hy22.le)
    have key : (X.a12 * Y.a12) ^ 2 < (X.a11 * X.a22) * (Y.a11 * Y.a22) := by
      nlinarith [step1, step2]
    -- `(2c)² < S²`; with `S ≥ 0` this gives `2c < S`, i.e. `MD X Y > 0`.
    have hS2 : (2 * (X.a12 * Y.a12)) ^ 2 < (X.a11 * Y.a22 + X.a22 * Y.a11) ^ 2 := by
      nlinarith [sq_nonneg (X.a11 * Y.a22 - X.a22 * Y.a11), key]
    have hlt : 2 * (X.a12 * Y.a12) < X.a11 * Y.a22 + X.a22 * Y.a11 :=
      lt_of_pow_lt_pow_left₀ 2 hSnonneg hS2
    linarith

end SymMat
end TuranBessel
