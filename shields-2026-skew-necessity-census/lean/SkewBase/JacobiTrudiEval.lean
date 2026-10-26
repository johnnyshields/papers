import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import SkewBase.Copied.SchurFunction

/-!
# Evaluation commutes with the Jacobi–Trudi determinant

Formalizes `shields-2026-skew-base-computational.tex`, «Profiles and Schur invariants»
(`lem:profiles`, `eq:jt`) and the evaluation step of the proof of `thm:census`: for a point
`η = (η₁, η₂, …)` of `S^ℕ`, the evaluation `h_k ↦ η_k` is a ring homomorphism, and the image of
the skew Schur function `s_F = det (h_{x_i - y_j})` is the determinant of the evaluated entries.

The ring `Λ = ℤ[h₁, h₂, …]` of the paper is `LambdaZ`.  `SkewGluing.Lambda` carries rational
coefficients; `schurZ` has the same determinant over `ℤ` and `map_schurZ` identifies it with
`Profile.schur` after the base change `ℤ → ℚ`, which is injective (`schurZ_eq_iff`), so equality
of skew Schur functions is the same statement in both rings.  The profile's beta lists
`ξ = x`, `ζ = y` are those of `eq:jt`: `ζ_last = 0`, `ζ_i = ξ_{i+1} - g_i`, `ξ_i = ζ_i + r_i`.

Sorry-free.
-/

namespace SkewBase

open SkewGluing MvPolynomial

/-- The ring `Λ = ℤ[h₁, h₂, …]`, as the polynomial ring on the variables `h_j`, `j ≥ 1`. -/
abbrev LambdaZ : Type := MvPolynomial ℕ+ ℤ

/-- The Jacobi–Trudi entry `h_j` over `ℤ`, with `h₀ = 1` and `h_j = 0` for `j < 0`. -/
noncomputable def hhZ (j : ℤ) : LambdaZ :=
  if h₁ : j < 0 then 0 else if h₂ : j = 0 then 1 else X ⟨j.toNat, by omega⟩

/-- The skew Schur function of the connected diagram with profile `P`, over `ℤ`:
`det (h_{ξ_i - ζ_j})`. -/
noncomputable def schurZ {n : ℕ} (P : Profile n) : LambdaZ :=
  (Matrix.of fun i j : Fin (n + 1) => hhZ (P.xi i - P.zeta j)).det

theorem map_hhZ (j : ℤ) : MvPolynomial.map (Int.castRingHom ℚ) (hhZ j) = hh j := by
  unfold hhZ hh
  by_cases h1 : j < 0
  · simp [h1]
  · by_cases h2 : j = 0
    · subst h2
      simp
    · have h3 : 0 < j.toNat := by omega
      simp only [h1, h2, hPos, h3, dite_false, dite_true, ite_false]
      exact MvPolynomial.map_X _ _

/-- The base change `ℤ → ℚ` takes `schurZ P` to `Profile.schur P`. -/
theorem map_schurZ {n : ℕ} (P : Profile n) :
    MvPolynomial.map (Int.castRingHom ℚ) (schurZ P) = P.schur := by
  unfold schurZ Profile.schur
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [map_hhZ]

theorem map_injective_lambda :
    Function.Injective (MvPolynomial.map (σ := ℕ+) (Int.castRingHom ℚ)) :=
  MvPolynomial.map_injective _ (RingHom.injective_int _)

/-- Equality of skew Schur functions over `ℤ` is equality over `ℚ`. -/
theorem schurZ_eq_iff {m n : ℕ} (P : Profile m) (Q : Profile n) :
    schurZ P = schurZ Q ↔ P.schur = Q.schur := by
  constructor
  · intro h
    rw [← map_schurZ, ← map_schurZ, h]
  · intro h
    apply map_injective_lambda
    rw [map_schurZ, map_schurZ]
    exact h

/-- Rotation does not change the skew Schur function over `ℤ`. -/
theorem schurZ_rotate {n : ℕ} (P : Profile n) : schurZ P.rotate = schurZ P := by
  rw [schurZ_eq_iff]
  exact P.schur_rotate

section Evaluation

variable {S : Type*} [CommRing S]

/-- The evaluation at the point `η`: the ring homomorphism `ℤ[h₁, h₂, …] → S` with `h_k ↦ η_k`. -/
noncomputable def evalAt (η : ℕ → S) : LambdaZ →+* S :=
  MvPolynomial.eval₂Hom (Int.castRingHom S) fun k : ℕ+ => η k

/-- The evaluated Jacobi–Trudi entry: `0` for `j < 0`, `1` for `j = 0`, `η_j` for `j > 0`. -/
def jtEntry (η : ℕ → S) (j : ℤ) : S := if j < 0 then 0 else if j = 0 then 1 else η j.toNat

theorem evalAt_hhZ (η : ℕ → S) (j : ℤ) : evalAt η (hhZ j) = jtEntry η j := by
  unfold hhZ jtEntry evalAt
  by_cases h1 : j < 0
  · simp [h1]
  · by_cases h2 : j = 0
    · subst h2
      simp
    · simp only [h1, h2, dite_false, ite_false]
      exact MvPolynomial.eval₂_X _ _ _

/-- **Evaluation commutes with the determinant `eq:jt`.**  The image of `s_F` at the point `η` is
the determinant of the matrix `(η_{x_i - y_j})`, with `η_0 = 1` and `η_k = 0` for `k < 0`. -/
theorem evalAt_schurZ (η : ℕ → S) {n : ℕ} (P : Profile n) :
    evalAt η (schurZ P) =
      (Matrix.of fun i j : Fin (n + 1) => jtEntry η (P.xi i - P.zeta j)).det := by
  unfold schurZ
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [evalAt_hhZ]

end Evaluation

end SkewBase
