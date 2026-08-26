/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Gram
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The Gram representation of the coefficient fiber at a free shift

Formalizes `shields-2026-turan-bessel.tex`, «Gram structure and the exceptional
matrix M₁» (`subsec:gram`, `thm:gram`, `eq:Nm-gram`, `eq:Mm-gram`, `eq:rho-m`) at
the free shift `s` the paper states it at, rather than only at the endpoint
`s = 1/g` that `Gram` needs.

In `ℓ²(ℕ₀) ⊕ ℝ` put
```
  ξ_m      = (u^{(m)}, 0),          u_r^{(m)} = (x+r)⁻¹,
  η_m(s)   = (v^{(m)}, √ρ_m(s)),    v_r^{(m)} = q(x-1+r)⁻¹,
```
with `x = a+m`, `q = a+m/2-1` and `ρ_m(s) = s + c_m - q²ψ₁(x-1)` (`eq:rho-m`).
Then `N_m(s) = Gram(ξ_m, η_m(s))` (`eq:Nm-gram`): the three inner products are
`ψ₁(x) = α_m` (`eq:u-norm`), `q/(x-1) = β_m` (`eq:uv-cross`) and
`q²ψ₁(x-1) + ρ_m(s) = s + c_m` (`eq:v-norm`).  The final coordinate contributes
exactly the slack, which is what makes the `(2,2)` entry free.

Positive definiteness follows for every `s` with `ρ_m(s) > 0`.

**Differs from the paper's route.**  The paper argues `N_m(s) ≻ 0` from linear
independence of `ξ_m` and `η_m(s)`, which needs the strict Cauchy--Schwarz
equality case.  Here the same conclusion comes from the non-strict inequality
`Gram.βcoef_sq_le_gram` plus the strictly positive slack `ρ_m(s)`, which is
already available and needs no equality analysis.

`Gram.rho`, `Coefficients.Nmat` and `Gram.Nmat_det_pos` are the case
`s = (ψ₁ a)⁻¹` of `rhoS`, `NmatS` and `NmatS_det_pos` here.

Sorry-free.
-/

open scoped BigOperators InnerProductSpace

namespace TuranBessel

variable {a s : ℝ}

/-! ### The shift-parametrized slack and fiber -/

/-- `ρ_m(s) = s + c_m - q²ψ₁(x-1)` (`eq:rho-m`), at a free shift `s`.
`Gram.rho` is `rhoS` at `s = g⁻¹`. -/
noncomputable def rhoS (a s : ℝ) (m : ℕ) : ℝ :=
  s + ccoef a m - (gramP a m) ^ 2 * trigamma (a + (m : ℝ) - 1)

theorem rhoS_inv_trigamma (a : ℝ) (m : ℕ) : rhoS a (trigamma a)⁻¹ m = rho a m := rfl

/-- `N_m(s)`, the symmetric matrix with entries `α_m`, `β_m` and `s + c_m`
(`subsec:gram`).  `Coefficients.Nmat` is `NmatS` at `s = g⁻¹`. -/
noncomputable def NmatS (a s : ℝ) (m : ℕ) : SymMat :=
  ⟨αcoef a m, βcoef a m, s + ccoef a m⟩

@[simp] theorem NmatS_a11 (a s : ℝ) (m : ℕ) : (NmatS a s m).a11 = αcoef a m := rfl
@[simp] theorem NmatS_a12 (a s : ℝ) (m : ℕ) : (NmatS a s m).a12 = βcoef a m := rfl
@[simp] theorem NmatS_a22 (a s : ℝ) (m : ℕ) : (NmatS a s m).a22 = s + ccoef a m := rfl

theorem NmatS_inv_trigamma (a : ℝ) (m : ℕ) : NmatS a (trigamma a)⁻¹ m = Nmat a m := rfl

/-! ### The two `ℓ²` sequences -/

/-- `u_r^{(m)} = (a+m+r)⁻¹`. -/
noncomputable def uSeq (a : ℝ) (m : ℕ) : ℕ → ℝ := fun r => (a + (m : ℝ) + (r : ℝ))⁻¹

/-- `v_r^{(m)} = q (a+m-1+r)⁻¹`, `q = a+m/2-1`. -/
noncomputable def vSeq (a : ℝ) (m : ℕ) : ℕ → ℝ :=
  fun r => gramP a m * (a + (m : ℝ) - 1 + (r : ℝ))⁻¹

theorem memℓp_uSeq (ha : 0 < a) (m : ℕ) : Memℓp (uSeq a m) 2 := by
  have hx : 0 < a + (m : ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  refine memℓp_gen ?_
  refine (trigamma_summable hx).congr fun r => ?_
  have hr : 0 < a + (m : ℝ) + (r : ℝ) := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  rw [ENNReal.toReal_ofNat, Real.rpow_two, uSeq, Real.norm_eq_abs, sq_abs]

theorem memℓp_vSeq (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) : Memℓp (vSeq a m) 2 := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : 0 < a + (m : ℝ) - 1 := by linarith
  refine memℓp_gen ?_
  refine ((trigamma_summable hx).mul_left ((gramP a m) ^ 2)).congr fun r => ?_
  rw [ENNReal.toReal_ofNat, Real.rpow_two, vSeq, Real.norm_eq_abs, sq_abs, mul_pow]

/-! ### The Hilbert space `ℓ²(ℕ₀) ⊕ ℝ` and the two vectors -/

/-- `ℓ²(ℕ₀) ⊕ ℝ`, the space `thm:gram` states `eq:Nm-gram` in. -/
abbrev GramSpace : Type := WithLp 2 (lp (fun _ : ℕ => ℝ) 2 × ℝ)

/-- The inner product of `ℓ²(ℕ₀) ⊕ ℝ` on the two components. -/
theorem gram_inner (f g : lp (fun _ : ℕ => ℝ) 2) (c d : ℝ) :
    ⟪WithLp.toLp 2 (f, c), WithLp.toLp 2 (g, d)⟫_ℝ = (∑' r : ℕ, f r * g r) + c * d := by
  rw [WithLp.prod_inner_apply, lp.inner_eq_tsum]
  simp only [RCLike.inner_apply, conj_trivial]
  exact congrArg₂ (· + ·) (tsum_congr fun r => mul_comm _ _) (mul_comm _ _)

/-- `u^{(m)}` as an element of `ℓ²(ℕ₀)`. -/
noncomputable def uVec (ha : 0 < a) (m : ℕ) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨uSeq a m, memℓp_uSeq ha m⟩

/-- `v^{(m)}` as an element of `ℓ²(ℕ₀)`. -/
noncomputable def vVec (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨vSeq a m, memℓp_vSeq ha hm⟩

@[simp] theorem uVec_apply (ha : 0 < a) (m r : ℕ) : (uVec ha m) r = uSeq a m r := rfl

@[simp] theorem vVec_apply (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    (vVec ha hm) r = vSeq a m r := rfl

/-- `Gram(ξ,η)`, the symmetric `2×2` matrix of inner products
`⟨ξ,ξ⟩`, `⟨ξ,η⟩`, `⟨η,η⟩` (`subsec:gram`). -/
noncomputable def gramMat (ξ η : GramSpace) : SymMat :=
  ⟨⟪ξ, ξ⟫_ℝ, ⟪ξ, η⟫_ℝ, ⟪η, η⟫_ℝ⟩

@[simp] theorem gramMat_a11 (ξ η : GramSpace) : (gramMat ξ η).a11 = ⟪ξ, ξ⟫_ℝ := rfl
@[simp] theorem gramMat_a12 (ξ η : GramSpace) : (gramMat ξ η).a12 = ⟪ξ, η⟫_ℝ := rfl
@[simp] theorem gramMat_a22 (ξ η : GramSpace) : (gramMat ξ η).a22 = ⟪η, η⟫_ℝ := rfl

/-- `ξ_m = (u^{(m)}, 0)`. -/
noncomputable def gramXi (ha : 0 < a) (m : ℕ) : GramSpace :=
  WithLp.toLp 2 (uVec ha m, 0)

/-- `η_m(s) = (v^{(m)}, √(ρ_m(s)))`. -/
noncomputable def gramEta (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) (s : ℝ) : GramSpace :=
  WithLp.toLp 2 (vVec ha hm, Real.sqrt (rhoS a s m))

/-! ### The three inner products -/

/-- **`eq:u-norm`.**  `‖ξ_m‖² = ψ₁(a+m) = α_m`. -/
theorem inner_xi_xi (ha : 0 < a) (m : ℕ) :
    ⟪gramXi ha m, gramXi ha m⟫_ℝ = αcoef a m := by
  rw [gramXi, gram_inner, mul_zero, add_zero, αcoef, trigamma]
  exact tsum_congr fun r => by simp only [uVec_apply, uSeq]; rw [sq]

/-- **`eq:uv-cross`.**  `⟨ξ_m, η_m(s)⟩ = q/(x-1) = β_m`, independently of `s`:
the last coordinate of `ξ_m` is zero. -/
theorem inner_xi_eta (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) (s : ℝ) :
    ⟪gramXi ha m, gramEta ha hm s⟫_ℝ = βcoef a m := by
  rw [gramXi, gramEta, gram_inner, zero_mul, add_zero, βcoef_eq_gram ha hm, ← cross_sum ha hm,
    ← tsum_mul_left]
  exact tsum_congr fun r => by simp only [uVec_apply, vVec_apply, uSeq, vSeq]; ring

/-- **`eq:v-norm` plus `eq:rho-m`.**  `‖η_m(s)‖² = q²ψ₁(x-1) + ρ_m(s) = s + c_m`. -/
theorem inner_eta_eta (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) (hs : 0 ≤ rhoS a s m) :
    ⟪gramEta ha hm s, gramEta ha hm s⟫_ℝ = s + ccoef a m := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hv : ∑' r : ℕ, (vVec ha hm) r * (vVec ha hm) r
      = (gramP a m) ^ 2 * trigamma (a + (m : ℝ) - 1) := by
    rw [trigamma, ← tsum_mul_left]
    exact tsum_congr fun r => by simp only [vVec_apply, vSeq]; rw [sq, sq]; ring
  rw [gramEta, gram_inner, hv, ← sq, Real.sq_sqrt hs, rhoS]
  ring

/-! ### `eq:Nm-gram` -/

/-- **`eq:Nm-gram`.**  `N_m(s) = Gram(ξ_m, η_m(s))` in `ℓ²(ℕ₀) ⊕ ℝ`, for every
`m ≥ 1` and every shift `s` with `ρ_m(s) ≥ 0`.  The final coordinate contributes
`ρ_m(s)`, so the `(2,2)` entry is `q²ψ₁(x-1) + ρ_m(s) = s + c_m`. -/
theorem NmatS_eq_gram (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) (hs : 0 ≤ rhoS a s m) :
    NmatS a s m = gramMat (gramXi ha m) (gramEta ha hm s) :=
  SymMat.ext (inner_xi_xi ha m).symm (inner_xi_eta ha hm s).symm
    (inner_eta_eta ha hm hs).symm

/-- **`eq:Mm-gram`.**  The unnormalized fiber
`M_m(s) = diag(1,√g) N_m(s) diag(1,√g)` is the Gram matrix of `ξ_m` and
`√g η_m(s)`, which is what `thm:gram` states at `s = 1/g`.  Written on the
entries, since `SymMat` carries no congruence operation. -/
theorem Mmat_eq_gram_smul (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) (hs : 0 ≤ rhoS a s m)
    {g : ℝ} (hg : 0 ≤ g) :
    (⟨αcoef a m, Real.sqrt g * βcoef a m, g * (s + ccoef a m)⟩ : SymMat)
      = gramMat (gramXi ha m) (Real.sqrt g • gramEta ha hm s) := by
  refine SymMat.ext (inner_xi_xi ha m).symm ?_ ?_
  · rw [gramMat_a12, real_inner_smul_right, inner_xi_eta ha hm s]
  · rw [gramMat_a22, real_inner_smul_left, real_inner_smul_right, inner_eta_eta ha hm hs,
      ← mul_assoc, Real.mul_self_sqrt hg]

/-! ### Positive definiteness at a free shift -/

/-- `det N_m(s) > 0` for `m ≥ 1` whenever `ρ_m(s) > 0`: the non-strict
Cauchy--Schwarz `Gram.βcoef_sq_le_gram` plus the strictly positive slack.
`Gram.Nmat_det_pos` is the case `s = g⁻¹`. -/
theorem NmatS_det_pos (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) (hρ : 0 < rhoS a s m) :
    (βcoef a m) ^ 2 < αcoef a m * (s + ccoef a m) := by
  have hcs := βcoef_sq_le_gram ha hm
  have hpm : αcoef a m * ((gramP a m) ^ 2 * trigamma (a + (m : ℝ) - 1))
      = αcoef a m * (s + ccoef a m) - αcoef a m * rhoS a s m := by
    rw [rhoS]; ring
  have hαpos : 0 < αcoef a m := αcoef_pos ha m
  linarith [hcs, hpm, mul_pos hαpos hρ]

/-- **`thm:gram` at a free shift.**  `N_m(s) ≻ 0` for every `m ≥ 1` and every `s`
with `ρ_m(s) > 0`.  `Gram.Nmat_pd_two` and `Gram.Nmat_pd_one` are the two ranges
in which `ρ_m(1/g) > 0` is then verified. -/
theorem NmatS_pd (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) (hρ : 0 < rhoS a s m) :
    SymMat.PD (NmatS a s m) :=
  ⟨αcoef_pos ha m, NmatS_det_pos ha hm hρ⟩

end TuranBessel
