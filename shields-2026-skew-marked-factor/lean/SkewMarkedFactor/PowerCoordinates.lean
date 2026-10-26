/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MurnaghanNakayama.PowerSumSpan
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Involution
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Kernel.Main
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Power coordinates

The coordinate seam in «Marked composition and the power-sum action» (`eq:delta`):
the source copy of `Lambda` has formal power-sum variables, while the target copy
has the complete-homogeneous variables used by Jacobi–Trudi.  The inverse is the
Newton recursion, not a choice of a spanning expression.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

/-- The complete homogeneous function expressed in formal power-sum variables. -/
def completeInPower : ℕ → Lambda
  | 0 => 1
  | n + 1 => C ((n + 1 : ℚ)⁻¹) *
      (X (⟨n + 1, by omega⟩ : ℕ+) +
        ∑ i : Fin n, X (⟨i + 1, by omega⟩ : ℕ+) * completeInPower (n - i))
termination_by n => n
decreasing_by have := i.isLt; omega

/-- Substitution of the actual Newton power sums. -/
def powerSumMap : Lambda →ₐ[ℚ] Lambda := aeval fun k : ℕ+ => pPoly k

/-- Substitution of the complete homogeneous functions in power coordinates. -/
def completePowerMap : Lambda →ₐ[ℚ] Lambda := aeval fun k : ℕ+ => completeInPower k

@[simp] theorem powerSumMap_X (k : ℕ+) : powerSumMap (X k) = pPoly k := by
  simp [powerSumMap]

@[simp] theorem completePowerMap_X (k : ℕ+) :
    completePowerMap (X k) = completeInPower k := by simp [completePowerMap]

-- Newton's recursive equations expose the subtype representation of `PNat`.
-- Full definitional reduction is confined to the coordinate seam.
set_option backward.isDefEq.respectTransparency false in
theorem powerSumMap_completeInPower (n : ℕ) :
    powerSumMap (completeInPower n) = hPos n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [completeInPower, hPos]
    | succ n =>
      rw [completeInPower]
      change powerSumMap ((C ((n + 1 : ℚ)⁻¹) : Lambda) *
        ((X (⟨n + 1, by omega⟩ : ℕ+) : Lambda) +
          ∑ i : Fin n, (X (⟨i + 1, by omega⟩ : ℕ+) : Lambda) *
            completeInPower (n - i))) = hPos (n + 1)
      rw [map_mul, map_add, map_sum, powerSumMap_X]
      simp only [map_mul, powerSumMap_X]
      have hi : ∀ i : Fin n, powerSumMap (completeInPower (n - i)) = hPos (n - i) :=
        fun i => ih _ (by have := i.isLt; omega)
      simp only [hi]
      rw [Gluing.Plan.MN.hPos_succ_eq]
      simp [Algebra.smul_def]

set_option backward.isDefEq.respectTransparency false in
theorem completePowerMap_hPos (n : ℕ) :
    completePowerMap (hPos n) = completeInPower n := by
  cases n with
  | zero => simp [hPos, completeInPower]
  | succ n =>
    have hh := hPos_pnat (⟨n + 1, by omega⟩ : ℕ+)
    change hPos (n + 1) = X (⟨n + 1, by omega⟩ : ℕ+) at hh
    rw [hh, completePowerMap_X]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem completePowerMap_pPoly (n : ℕ) :
    completePowerMap (pPoly n) = if hn : 0 < n then X (⟨n, hn⟩ : ℕ+) else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [pPoly, map_zero]
      change (0 : Lambda) = (0 : Lambda)
      rfl
    | succ n =>
      rw [pPoly, map_sub, map_mul, map_sum, completePowerMap_hPos]
      simp only [map_mul, completePowerMap_hPos]
      have hi : ∀ i : Fin n, completePowerMap (pPoly (i + 1)) =
          X (⟨i + 1, by omega⟩ : ℕ+) := by
        intro i
        simpa using ih (i + 1) (by have := i.isLt; omega)
      simp only [hi, Nat.succ_pos, ↓reduceDIte]
      rw [completeInPower]
      simp only [map_natCast]
      change ((n + 1 : ℕ) : Lambda) *
        ((C ((n + 1 : ℚ)⁻¹) : Lambda) *
          ((X (⟨n + 1, by omega⟩ : ℕ+) : Lambda) +
            ∑ i : Fin n, (X (⟨i + 1, by omega⟩ : ℕ+) : Lambda) *
              completeInPower (n - i))) -
        (∑ i : Fin n, (X (⟨i + 1, by omega⟩ : ℕ+) : Lambda) *
          completeInPower (n - i)) = X (⟨n + 1, by omega⟩ : ℕ+)
      have hn : (n + 1 : ℚ) ≠ 0 := by positivity
      have hc : ((n + 1 : ℕ) : Lambda) * C ((n + 1 : ℚ)⁻¹) = 1 := by
        rw [show ((n + 1 : ℕ) : Lambda) = C (n + 1 : ℚ) by simp,
          ← C_mul, mul_inv_cancel₀ hn, C_1]
      rw [← mul_assoc, hc, one_mul]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- The power-sum coordinate isomorphism.  Its domain variables are `p_k`;
its codomain variables are `h_k`, although both polynomial rings have the alias `Lambda`. -/
def powerSumEquiv : Lambda ≃ₐ[ℚ] Lambda :=
  AlgEquiv.ofAlgHom powerSumMap completePowerMap
    (by
      apply MvPolynomial.algHom_ext
      intro k
      simp only [AlgHom.comp_apply, AlgHom.id_apply, completePowerMap_X]
      simpa [hPos_pnat] using powerSumMap_completeInPower k)
    (by
      apply MvPolynomial.algHom_ext
      intro k
      simp only [AlgHom.comp_apply, AlgHom.id_apply, powerSumMap_X]
      have he : (⟨(k : ℕ), k.pos⟩ : ℕ+) = k := Subtype.ext rfl
      simpa only [k.pos, dite_true, he] using completePowerMap_pPoly k)

@[simp] theorem powerSumEquiv_X (k : ℕ+) : powerSumEquiv (X k) = pPoly k :=
  powerSumMap_X k

@[simp] theorem powerSumEquiv_symm_X (k : ℕ+) :
    powerSumEquiv.symm (X k) = completeInPower k := completePowerMap_X k

@[simp] theorem powerSumEquiv_symm_pPoly (k : ℕ+) :
    powerSumEquiv.symm (pPoly k) = X k := by
  apply powerSumEquiv.injective
  rw [powerSumEquiv.apply_symm_apply, powerSumEquiv_X]

/-- Newton power sums collected into a series, including the genuine zero boundary. -/
def newtonSeries : PowerSeries Lambda := PowerSeries.mk pPoly

set_option backward.isDefEq.respectTransparency false in
theorem newtonSeries_mul_hSeries :
    newtonSeries * hSeries = PowerSeries.X * PowerSeries.derivative hSeries := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [newtonSeries, hSeries, pPoly, PowerSeries.coeff_mul]
  | succ n =>
    have shift : PowerSeries.coeff (n + 1)
        (PowerSeries.X * PowerSeries.derivative hSeries) =
        PowerSeries.coeff n (PowerSeries.derivative hSeries) := by
      simp only [PowerSeries.coeff_succ_X_mul]
    rw [shift, PowerSeries.coeff_derivative]
    rw [PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun ij => PowerSeries.coeff ij.1 newtonSeries *
        PowerSeries.coeff ij.2 hSeries) (n + 1)]
    simp only [newtonSeries, hSeries, PowerSeries.coeff_mk]
    rw [Finset.sum_range_succ]
    have hzero : ∑ i ∈ Finset.range (n + 1), pPoly i * hPos (n + 1 - i) =
        ∑ i : Fin n, pPoly (i + 1) * hPos (n - i) := by
      rw [Finset.sum_range_succ']
      simp only [show pPoly 0 = 0 by rw [pPoly], zero_mul, add_zero]
      rw [← Fin.sum_univ_eq_sum_range]
      congr 1
      funext i
      congr 2
      omega
    rw [hzero, Nat.sub_self, show hPos 0 = 1 by simp [hPos], mul_one, pPoly]
    push_cast
    ring

theorem coeffDeriv_add (D : Derivation ℚ Lambda Lambda) (f g : PowerSeries Lambda) :
    coeffDeriv D (f + g) = coeffDeriv D f + coeffDeriv D g := by
  ext n; simp [coeff_coeffDeriv, map_add]

theorem coeffDeriv_X (D : Derivation ℚ Lambda Lambda) :
    coeffDeriv D PowerSeries.X = 0 := by
  ext n
  rw [coeff_coeffDeriv, PowerSeries.coeff_X]
  split_ifs <;> simp

theorem coeffDeriv_X_pow (D : Derivation ℚ Lambda Lambda) (m : ℕ) :
    coeffDeriv D (PowerSeries.X ^ m) = 0 := by
  ext n
  rw [coeff_coeffDeriv, PowerSeries.coeff_X_pow]
  split_ifs <;> simp

theorem coeffDeriv_derivative (D : Derivation ℚ Lambda Lambda) (f : PowerSeries Lambda) :
    coeffDeriv D (PowerSeries.derivative f) =
      PowerSeries.derivative (coeffDeriv D f) := by
  ext n
  rw [coeff_coeffDeriv, PowerSeries.coeff_derivative, Derivation.leibniz,
    PowerSeries.coeff_derivative, coeff_coeffDeriv]
  simp [smul_eq_mul, mul_comm]

/-- The diagonal action on the actual Newton power sums.  The index of the
derivation must be positive; the power-sum index may be zero. -/
theorem pDeriv_pPoly {m : ℕ} (hm : 0 < m) (n : ℕ) :
    pDeriv m (pPoly n) = if m = n then (m : Lambda) else 0 := by
  have h := congrArg (coeffDeriv (pDeriv m)) newtonSeries_mul_hSeries
  rw [coeffDeriv_mul, coeffDeriv_mul, coeffDeriv_X, mul_zero, add_zero,
    coeffDeriv_derivative, coeffDeriv_hSeries hm,
    Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_X] at h
  have he := eSeries_mul_hSeries
  have hs : coeffDeriv (pDeriv m) newtonSeries =
      (m : PowerSeries Lambda) * PowerSeries.X ^ m := by
    have hh : hSeries * (coeffDeriv (pDeriv m) newtonSeries -
        (m : PowerSeries Lambda) * PowerSeries.X ^ m) = 0 := by
      have hp : PowerSeries.X * PowerSeries.X ^ (m - 1) =
          (PowerSeries.X : PowerSeries Lambda) ^ m := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        simp [pow_succ, mul_comm]
      simp only [smul_eq_mul, nsmul_eq_mul, mul_one] at h
      linear_combination h - PowerSeries.X ^ m * newtonSeries_mul_hSeries +
        (m : PowerSeries Lambda) * hSeries * hp
    have hh' := congrArg (fun x => eSeries * x) hh
    rw [← mul_assoc, he, one_mul, mul_zero, sub_eq_zero] at hh'
    exact hh'
  have hn := congrArg (PowerSeries.coeff n) hs
  rw [coeff_coeffDeriv] at hn
  simp only [newtonSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_natCast_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero] at hn
  simpa [eq_comm] using hn

/-- Transport of the Hall derivation across the coordinate seam (`eq:delta`). -/
theorem pDeriv_powerSumEquiv (k : ℕ+) (f : Lambda) :
    pDeriv k (powerSumEquiv f) = powerSumEquiv (C (k : ℚ) * pderiv k f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    have hc : powerSumEquiv (C a) = C a := powerSumEquiv.commutes a
    rw [hc, MvPolynomial.derivation_C, pderiv_C, mul_zero, map_zero]
  | add f g hf hg => simp [hf, hg, map_add, mul_add]
  | mul_X f j hf =>
    rw [map_mul, Derivation.leibniz, powerSumEquiv_X, pDeriv_pPoly k.pos,
      pderiv_mul, mul_add, map_add, map_mul, map_mul, hf]
    simp only [smul_eq_mul, map_mul, powerSumEquiv_X, pderiv_X, Pi.single_apply]
    by_cases h : k = j
    · subst j; simp; ring
    · have h' : (k : ℕ) ≠ (j : ℕ) := fun hc => h (PNat.coe_injective hc)
      simp only [h', Ne.symm h, ite_false, mul_zero, add_zero, map_zero]
      ring

theorem pDeriv_commute {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (f : Lambda) :
    pDeriv m (pDeriv n f) = pDeriv n (pDeriv m f) :=
  Gluing.Plan.KernelAux.pDeriv_comm hm hn f

theorem derivation_weighted_sum_apply (s : Finset ℕ+) (b : ℕ+ → Lambda) (f : Lambda) :
    (∑ j ∈ s, b j • (pderiv j : Derivation ℚ Lambda Lambda)) f =
      ∑ j ∈ s, b j * pderiv j f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj, Derivation.add_apply, Derivation.smul_apply,
      smul_eq_mul, ih]

/-- The complete-homogeneous-coordinate expression in `eq:delta`.  The sum is
finite because it runs only over variables actually occurring in `f`. -/
theorem pDeriv_h_coordinate_sum (m : ℕ) (f : Lambda) :
    pDeriv m f = ∑ j ∈ f.vars, hh ((j : ℤ) - m) * pderiv j f := by
  classical
  let D : Derivation ℚ Lambda Lambda :=
    ∑ j ∈ f.vars, hh ((j : ℤ) - m) • pderiv j
  have hD : pDeriv m f = D f := by
    apply MvPolynomial.derivation_eq_of_forall_mem_vars
    intro k hk
    rw [pDeriv_X]
    change hh ((k : ℤ) - m) =
      (∑ j ∈ f.vars, hh ((j : ℤ) - m) • pderiv j) (X k)
    rw [derivation_weighted_sum_apply]
    simp [pderiv_X, Pi.single_apply, hk]
  rw [hD]
  exact derivation_weighted_sum_apply _ _ _

/-- Terms strictly below the Hall index disappear; the zero-index `h_0` at
the equality boundary is retained. -/
theorem pDeriv_h_coordinate_sum_positive (m : ℕ) (f : Lambda) :
    pDeriv m f = ∑ j ∈ f.vars.filter (fun j : ℕ+ => m ≤ (j : ℕ)),
      hPos ((j : ℕ) - m) * pderiv j f := by
  classical
  rw [pDeriv_h_coordinate_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : m ≤ (j : ℕ)
  · rw [ite_eq_left hj]
    have hcast : (j : ℤ) - m = (((j : ℕ) - m : ℕ) : ℤ) := by omega
    rw [hcast, hh_natCast]
  · rw [ite_eq_right hj, hh_of_neg (by omega : (j : ℤ) - m < 0), zero_mul]

/-- Substitution of homogeneous polynomials preserves the specified weights. -/
theorem homogeneous_aeval {g : ℕ+ → Lambda} (hg : ∀ k,
    IsWeightedHomogeneous degWeight (g k) k) {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) :
    IsWeightedHomogeneous degWeight (aeval g f) a := by
  classical
  rw [MvPolynomial.as_sum f, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial]
  have hm := IsWeightedHomogeneous.prod d.support
    (fun k => g k ^ d k) (fun k => d k * (k : ℕ))
    (fun k _ => by simpa [nsmul_eq_mul] using (hg k).pow (d k))
  have he : ∑ k ∈ d.support, d k * (k : ℕ) = a := by
    simpa [Finsupp.weight_apply, Finsupp.sum, degWeight, nsmul_eq_mul] using
      hf (MvPolynomial.mem_support_iff.mp hd)
  simpa [Finsupp.prod, he] using hm.C_mul (f.coeff d)

set_option backward.isDefEq.respectTransparency false in
theorem homogeneous_completeInPower (n : ℕ) :
    IsWeightedHomogeneous degWeight (completeInPower n) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simpa [completeInPower] using isWeightedHomogeneous_one ℚ degWeight
    | succ n =>
      rw [completeInPower]
      apply IsWeightedHomogeneous.C_mul
      apply IsWeightedHomogeneous.add
      · exact isWeightedHomogeneous_X ℚ degWeight _
      · apply IsWeightedHomogeneous.sum
        intro i _
        have hi := i.isLt
        have hh := (isWeightedHomogeneous_X ℚ degWeight
          (⟨i + 1, by omega⟩ : ℕ+)).mul (ih (n - i) (by omega))
        simpa [degWeight, show (i : ℕ) + 1 + (n - i) = n + 1 by omega] using hh

theorem homogeneous_powerSumEquiv {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) :
    IsWeightedHomogeneous degWeight (powerSumEquiv f) a :=
  homogeneous_aeval (fun k => Gluing.Plan.KernelAux.isWeightedHomogeneous_pPoly k) hf

theorem homogeneous_powerSumEquiv_symm {f : Lambda} {a : ℕ}
    (hf : IsWeightedHomogeneous degWeight f a) :
    IsWeightedHomogeneous degWeight (powerSumEquiv.symm f) a :=
  homogeneous_aeval (fun k => homogeneous_completeInPower k) hf

end SkewMarkedFactor
