/-
# Coefficient data of the Turán matrix

Formalizes the closed-form coefficient matrices of
`shields-2026-turan-bessel.tex`, §4 «Reciprocal-gamma convolution and coefficient
formulas» (`sec:coefficients`, `thm:coefficients`) and §5 «Probabilistic
interpretation: the finite conditional law» (`sec:conditional`, `eq:Nm`),
in the square-root-free normalization `N_m = diag(1,g^{-1/2}) M_m diag(1,g^{-1/2})`:
```
        ⎛ α_m        β_m      ⎞
N_m  =  ⎝ β_m    g^{-1}+c_m   ⎠ ,     g = ψ₁(a),
```
with `α_m = ψ₁(a+m)`, `β_0 = 1`, `β_m = (2a+m-2)/(2(a+m-1))` (`m ≥ 1`),
`c_0 = c_1 = 0`, `c_m = m(m-1)/(2(2a+2m-3))` (`m ≥ 2`).

The reduced weight `sred a m = (2a+m-1)_m / (m! ((a)_m)²)` is `S_m Γ(a)²`; the
common factor `Γ(a)^{-4}` is positive and drops out of every sign in
`Δ_n = ½ Σ S_k S_{n-k} MD(M_k,M_{n-k})`, so the paper's `S_m` are replaced by
`sred` throughout.

Only sign facts live here; positive-definiteness of `N_m` is proved in `Gram`.
-/
import TuranBessel.MatrixMD
import TuranBessel.Trigamma

open scoped BigOperators

namespace TuranBessel

variable {a : ℝ}

/-- Ascending product `(x)_m = ∏_{i<m} (x+i)`. -/
noncomputable def poch (x : ℝ) (m : ℕ) : ℝ := ∏ i ∈ Finset.range m, (x + (i : ℝ))

@[simp] theorem poch_zero (x : ℝ) : poch x 0 = 1 := by simp [poch]

theorem poch_one (x : ℝ) : poch x 1 = x := by simp [poch]

theorem poch_two (x : ℝ) : poch x 2 = x * (x + 1) := by
  simp [poch, Finset.prod_range_succ]

/-- `(x)_m > 0` whenever every factor is positive. -/
theorem poch_pos {x : ℝ} {m : ℕ} (hx : ∀ i : ℕ, i < m → 0 < x + (i : ℝ)) :
    0 < poch x m :=
  Finset.prod_pos (fun i hi => hx i (Finset.mem_range.mp hi))

/-- Reduced weight `sred a m = S_m Γ(a)²`, a rational function of `a`. -/
noncomputable def sred (a : ℝ) (m : ℕ) : ℝ :=
  poch (2 * a + (m : ℝ) - 1) m / ((Nat.factorial m : ℝ) * (poch a m) ^ 2)

/-- `sred` is strictly positive for `a > 0`. -/
theorem sred_pos (ha : 0 < a) (m : ℕ) : 0 < sred a m := by
  have hnum : 0 < poch (2 * a + (m : ℝ) - 1) m :=
    poch_pos (fun i hi => by
      have hle : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
      nlinarith [ha, hle, Nat.cast_nonneg (α := ℝ) i])
  have hp : 0 < poch a m := poch_pos (fun i _ => by
    have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hf : 0 < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  exact div_pos hnum (by positivity)

@[simp] theorem sred_zero (a : ℝ) : sred a 0 = 1 := by simp [sred]

theorem sred_one (a : ℝ) : sred a 1 = 2 * a / a ^ 2 := by
  rw [sred, poch_one, poch_one]; norm_num

theorem sred_two (a : ℝ) : sred a 2 = (2 * a + 1) * (2 * a + 2) / (2 * (a * (a + 1)) ^ 2) := by
  rw [sred, poch_two, poch_two]
  have h2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [h2]; push_cast; ring

/-- `α_m = ψ₁(a+m)`. -/
noncomputable def αcoef (a : ℝ) (m : ℕ) : ℝ := trigamma (a + (m : ℝ))

/-- `β_0 = 1`,  `β_m = (2a+m-2)/(2(a+m-1))` for `m ≥ 1`. -/
noncomputable def βcoef (a : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 1 else (2 * a + (m : ℝ) - 2) / (2 * (a + (m : ℝ) - 1))

/-- `c_0 = c_1 = 0`,  `c_m = m(m-1)/(2(2a+2m-3))` for `m ≥ 2`. -/
noncomputable def ccoef (a : ℝ) (m : ℕ) : ℝ :=
  if m ≤ 1 then 0 else (m : ℝ) * ((m : ℝ) - 1) / (2 * (2 * a + 2 * (m : ℝ) - 3))

/-- The square-root-free coefficient matrix `N_m` (eq:Nm). -/
noncomputable def Nmat (a : ℝ) (m : ℕ) : SymMat :=
  ⟨αcoef a m, βcoef a m, (trigamma a)⁻¹ + ccoef a m⟩

@[simp] theorem Nmat_a11 (a : ℝ) (m : ℕ) : (Nmat a m).a11 = αcoef a m := rfl
@[simp] theorem Nmat_a12 (a : ℝ) (m : ℕ) : (Nmat a m).a12 = βcoef a m := rfl
@[simp] theorem Nmat_a22 (a : ℝ) (m : ℕ) : (Nmat a m).a22 = (trigamma a)⁻¹ + ccoef a m := rfl

theorem αcoef_pos (ha : 0 < a) (m : ℕ) : 0 < αcoef a m := by
  apply trigamma_pos; positivity

@[simp] theorem βcoef_zero (a : ℝ) : βcoef a 0 = 1 := by simp [βcoef]

@[simp] theorem ccoef_zero (a : ℝ) : ccoef a 0 = 0 := by simp [ccoef]
@[simp] theorem ccoef_one (a : ℝ) : ccoef a 1 = 0 := by simp [ccoef]

theorem ccoef_two (a : ℝ) : ccoef a 2 = 2 / (2 * (2 * a + 1)) := by
  unfold ccoef; rw [if_neg (by omega)]; push_cast; ring

theorem ccoef_nonneg (ha : 0 < a) (m : ℕ) : 0 ≤ ccoef a m := by
  unfold ccoef
  split_ifs with h
  · exact le_refl 0
  · have hm : (2 : ℝ) ≤ (m : ℝ) := by
      have : 2 ≤ m := by omega
      exact_mod_cast this
    have hnum : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by nlinarith
    have hden : 0 < 2 * (2 * a + 2 * (m : ℝ) - 3) := by nlinarith
    exact div_nonneg hnum hden.le

/-- `β_m > 0` for `m ≥ 2`. -/
theorem βcoef_pos_of_two (ha : 0 < a) {m : ℕ} (hm : 2 ≤ m) : 0 < βcoef a m := by
  unfold βcoef
  rw [if_neg (by omega)]
  have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  apply div_pos <;> nlinarith

/-- `β_1 = (2a-1)/(2a)`; in particular it is negative for `0 < a < 1/2`. -/
theorem βcoef_one (a : ℝ) : βcoef a 1 = (2 * a - 1) / (2 * a) := by
  unfold βcoef; rw [if_neg (by omega)]; push_cast; ring

/-- `N_0 = ⟨g, 1, g⁻¹⟩` is rank-one PSD and nonzero. -/
theorem Nmat_zero_psd (ha : 0 < a) : SymMat.PSD (Nmat a 0) := by
  have hg : 0 < trigamma a := trigamma_pos ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [Nmat_a11, αcoef, Nat.cast_zero, add_zero]; exact hg.le
  · simp only [Nmat_a22, ccoef_zero, add_zero]; exact (inv_pos.mpr hg).le
  · have hprod : (Nmat a 0).a11 * (Nmat a 0).a22 = 1 := by
      simp only [Nmat_a11, Nmat_a22, αcoef, ccoef_zero, Nat.cast_zero, add_zero]
      exact mul_inv_cancel₀ hg.ne'
    rw [hprod]
    simp only [Nmat_a12, βcoef_zero]
    norm_num

theorem Nmat_zero_ne (ha : 0 < a) : Nmat a 0 ≠ 0 := by
  intro h
  have h11 : (Nmat a 0).a11 = 0 := by rw [h]; rfl
  simp only [Nmat_a11, αcoef, Nat.cast_zero, add_zero] at h11
  exact (trigamma_pos ha).ne' h11

end TuranBessel
