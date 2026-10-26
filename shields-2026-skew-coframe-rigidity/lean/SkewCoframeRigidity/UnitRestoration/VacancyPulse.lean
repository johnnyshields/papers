/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Defs

/-!
# The vacancy pulse of a zero-free core

Formalizes the second half of `sc:unit-expansion` in `shields-2026-skew-coframe-rigidity.tex`
(«The complete unit expansion and finite injectivity», `sc:vacancy-pulse`).  Over a field `F`
with a letter sequence `U` (zero at negative indices), proper rows `I`, native columns `S` and
the invertible proper matrix `T = (U_{I i - S s})`, a restoration at a vacancy `b` outside `S`
has the first coframe increment
`δ^{(b)} = -P_b (z^b - ∑_s (T⁻¹ v_b)_s z^{S s})`, `v_b = (U_{I i - b})`.  Any rational
combination `δ = ∑_b ρ_b δ^{(b)}` has `δ₀ = 0`, `[Uδ]_{I i} = 0` and `δ_b = -ρ_b P_b` at each
vacancy.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open Polynomial Matrix SkewCoframeRigidity.Coframe

variable {F : Type*} [Field F] {n m : ℕ}

/-- The proper matrix `(U_{I i - S s})` of rows `I` and native columns `S`. -/
def properMat (U : ℕ → F) (I S : Fin n → ℕ) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i s => letterOf U ((I i : ℤ) - S s)

/-- The right-hand side `v_b = (U_{I i - b})`. -/
def vacancyVec (U : ℕ → F) (I : Fin n → ℕ) (b : ℕ) : Fin n → F :=
  fun i => letterOf U ((I i : ℤ) - b)

/-- The complete first coframe increment `δ^{(b)}` of a restoration at `b` with numerator
coefficient `p = P⁺_b`. -/
noncomputable def pulse (U : ℕ → F) (I S : Fin n → ℕ) (p : F) (b : ℕ) : F[X] :=
  Polynomial.C (-p) * (Polynomial.X ^ b -
    ∑ s, Polynomial.C (((properMat U I S)⁻¹ *ᵥ vacancyVec U I b) s) * Polynomial.X ^ S s)

/-- The weighted combination `∑_v ρ_v δ^{(b_v)}`. -/
noncomputable def pulseSum (U : ℕ → F) (I S : Fin n → ℕ) (bpos : Fin m → ℕ) (P ρ : Fin m → F) :
    F[X] :=
  ∑ v, Polynomial.C (ρ v) * pulse U I S (P v) (bpos v)

theorem coeff_series_mul_monomial (U : ℕ → F) (e k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk U * ((Polynomial.X ^ e : F[X]) : PowerSeries F)) =
      letterOf U ((k : ℤ) - e) := by
  rw [Polynomial.coe_pow, Polynomial.coe_X, PowerSeries.coeff_mul_X_pow']
  by_cases h : e ≤ k
  · rw [if_pos h, PowerSeries.coeff_mk, letterOf, if_neg (by omega)]
    congr 1; omega
  · rw [if_neg h, letterOf, if_pos (by omega)]

theorem coeff_series_mul_C_monomial (U : ℕ → F) (c : F) (e k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk U *
      ((Polynomial.C c * Polynomial.X ^ e : F[X]) : PowerSeries F)) =
      c * letterOf U ((k : ℤ) - e) := by
  rw [Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm, PowerSeries.coeff_C_mul,
    coeff_series_mul_monomial]

theorem coeff_series_mul_pulse (U : ℕ → F) (I S : Fin n → ℕ) (p : F) (b k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk U * (pulse U I S p b : PowerSeries F)) =
      -p * (letterOf U ((k : ℤ) - b) -
        ∑ s, ((properMat U I S)⁻¹ *ᵥ vacancyVec U I b) s * letterOf U ((k : ℤ) - S s)) := by
  unfold pulse
  rw [Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm, PowerSeries.coeff_C_mul]
  congr 1
  rw [Polynomial.coe_sub, mul_sub, map_sub, coeff_series_mul_monomial]
  congr 1
  rw [show ((∑ s, Polynomial.C (((properMat U I S)⁻¹ *ᵥ vacancyVec U I b) s) *
      Polynomial.X ^ S s : F[X]) : PowerSeries F) = ∑ s, ((Polynomial.C
      (((properMat U I S)⁻¹ *ᵥ vacancyVec U I b) s) * Polynomial.X ^ S s : F[X]) : PowerSeries F)
    from map_sum (Polynomial.coeToPowerSeries.ringHom (R := F)) _ _, Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => coeff_series_mul_C_monomial _ _ _ _

/-- The equation `[Uδ^{(b)}]_{I i} = 0` at an original proper row. -/
theorem coeff_row_pulse (U : ℕ → F) (I S : Fin n → ℕ) (hT : (properMat U I S).det ≠ 0)
    (p : F) (b : ℕ) (i : Fin n) :
    PowerSeries.coeff (I i) (PowerSeries.mk U * (pulse U I S p b : PowerSeries F)) = 0 := by
  rw [coeff_series_mul_pulse]
  have hinv : properMat U I S *ᵥ ((properMat U I S)⁻¹ *ᵥ vacancyVec U I b) = vacancyVec U I b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hT),
      Matrix.one_mulVec]
  generalize (properMat U I S)⁻¹ *ᵥ vacancyVec U I b = t at hinv ⊢
  have := congrFun hinv i
  have e : (properMat U I S *ᵥ t) i = ∑ s, letterOf U ((I i : ℤ) - S s) * t s := rfl
  rw [e] at this
  rw [show (∑ s, t s * letterOf U ((I i : ℤ) - S s)) = ∑ s, letterOf U ((I i : ℤ) - S s) * t s
    from Finset.sum_congr rfl fun _ _ => mul_comm _ _, this]
  simp [vacancyVec]

theorem coeff_pulse (U : ℕ → F) (I S : Fin n → ℕ) (p : F) (b k : ℕ) :
    (pulse U I S p b).coeff k = -p * ((if k = b then 1 else 0) -
      ∑ s, ((properMat U I S)⁻¹ *ᵥ vacancyVec U I b) s * (if k = S s then 1 else 0)) := by
  unfold pulse
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    Polynomial.finsetSum_coeff]
  congr 2
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

/-- **The vacancy pulse** (`sc:unit-expansion`): for positive vacancies `bpos`, distinct from
the native columns `S`, and any weights `ρ`, the combination `δ` has `δ₀ = 0`,
`[Uδ]_{I i} = 0`, and `δ_{b_v} = -ρ_v P_v`. -/
theorem pulseSum_spec (U : ℕ → F) (I S : Fin n → ℕ) (hT : (properMat U I S).det ≠ 0)
    (bpos : Fin m → ℕ) (P ρ : Fin m → F) (hSpos : ∀ s, 0 < S s) (hbpos : ∀ v, 0 < bpos v)
    (hbinj : Function.Injective bpos) (hbS : ∀ v s, bpos v ≠ S s) :
    (pulseSum U I S bpos P ρ).coeff 0 = 0 ∧
    (∀ i, PowerSeries.coeff (I i) (PowerSeries.mk U * (pulseSum U I S bpos P ρ : PowerSeries F))
      = 0) ∧
    ∀ v, (pulseSum U I S bpos P ρ).coeff (bpos v) = -(ρ v * P v) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold pulseSum
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [Polynomial.coeff_C_mul, coeff_pulse]
    simp [(hbpos v).ne, fun s => (hSpos s).ne]
  · intro i
    unfold pulseSum
    rw [show ((∑ v, Polynomial.C (ρ v) * pulse U I S (P v) (bpos v) : F[X]) : PowerSeries F) =
      ∑ v, ((Polynomial.C (ρ v) * pulse U I S (P v) (bpos v) : F[X]) : PowerSeries F) from
        map_sum (Polynomial.coeToPowerSeries.ringHom (R := F)) _ _, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm, PowerSeries.coeff_C_mul,
      coeff_row_pulse U I S hT, mul_zero]
  · intro v
    unfold pulseSum
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single v]
    · rw [Polynomial.coeff_C_mul, coeff_pulse]
      simp [fun s => (hbS v s)]
    · intro w _ hw
      rw [Polynomial.coeff_C_mul, coeff_pulse]
      have : bpos v ≠ bpos w := fun h => hw (hbinj h).symm
      simp [fun s => (hbS v s), this]
    · simp

/-- A nonzero weight at a vacancy with `P_v ≠ 0` gives a nonzero tangent. -/
theorem pulseSum_ne_zero (U : ℕ → F) (I S : Fin n → ℕ) (hT : (properMat U I S).det ≠ 0)
    (bpos : Fin m → ℕ) (P ρ : Fin m → F) (hSpos : ∀ s, 0 < S s) (hbpos : ∀ v, 0 < bpos v)
    (hbinj : Function.Injective bpos) (hbS : ∀ v s, bpos v ≠ S s) (v : Fin m) (hρ : ρ v ≠ 0)
    (hP : P v ≠ 0) : pulseSum U I S bpos P ρ ≠ 0 := by
  intro h
  have := (pulseSum_spec U I S hT bpos P ρ hSpos hbpos hbinj hbS).2.2 v
  rw [h, Polynomial.coeff_zero] at this
  exact mul_ne_zero hρ hP (by linear_combination this)

end SkewCoframeRigidity.UnitRestoration
