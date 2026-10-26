/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic.Linarith
import SkewMarkedFactor.MixedTerminal
import SkewMarkedFactor.RibbonDeletion

/-!
# Nonvanishing of ribbon Schur functions at a fractional alphabet size

«Recovering mixed ribbon factors» (`sec:mixed-extraction`) of
`shields-2026-skew-marked-factor.tex`.  For a ribbon `D` and rational `0 < x < 1`, the
specialization `p_j ↦ x` of `s_D` is nonzero.  The proof passes to the antitranspose, where the
Jacobi--Trudi determinant of a one-cell-per-diagonal profile is an upper Hessenberg determinant
in the coefficients of `∑ (-1)^k e_k(1^x) t^k`; these satisfy `(k+1) a_{k+1} = (k - x) a_k`, hence
are negative for `k ≥ 1`, and the Hessenberg determinant has a definite sign.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan

/-- Upper Hessenberg shape with unit subdiagonal and strictly negative entries on and above the
diagonal. -/
def HessNeg {N : ℕ} (M : Matrix (Fin N) (Fin N) ℚ) : Prop :=
  (∀ i j : Fin N, j.val + 1 < i.val → M i j = 0) ∧
  (∀ i j : Fin N, i.val = j.val + 1 → M i j = 1) ∧
  (∀ i j : Fin N, i.val ≤ j.val → M i j < 0)

theorem HessNeg.det_sign : ∀ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℚ), HessNeg M →
    0 < (-1 : ℚ) ^ N * M.det := by
  intro N
  induction N with
  | zero => intro M _; simp
  | succ n ih =>
    intro M hM
    obtain ⟨h0, h1, h2⟩ := hM
    have hM' : HessNeg (M.submatrix Fin.castSucc Fin.castSucc) := by
      refine ⟨fun i j h => h0 _ _ (by simpa using h), fun i j h => h1 _ _ (by simpa using h),
        fun i j h => h2 _ _ (by simpa using h)⟩
    have hlast := ih _ hM'
    have hMll : M (Fin.last n) (Fin.last n) < 0 := h2 _ _ (by simp)
    have hdet := Matrix.det_succ_row M (Fin.last n)
    rw [Fin.sum_univ_castSucc] at hdet
    cases n with
    | zero =>
      simp only [Fin.sum_univ_zero, zero_add] at hdet
      simp at hlast ⊢
      simpa using hMll
    | succ m =>
      have hsum : ∑ j : Fin (m + 1), (-1 : ℚ) ^ ((Fin.last (m + 1)).val + (Fin.castSucc j).val) *
          M (Fin.last (m + 1)) (Fin.castSucc j) *
          (M.submatrix (Fin.last (m + 1)).succAbove (Fin.castSucc j).succAbove).det =
          (-1 : ℚ) ^ ((Fin.last (m + 1)).val + (Fin.castSucc (Fin.last m)).val) *
          M (Fin.last (m + 1)) (Fin.castSucc (Fin.last m)) *
          (M.submatrix (Fin.last (m + 1)).succAbove
            (Fin.castSucc (Fin.last m)).succAbove).det := by
        refine Finset.sum_eq_single (Fin.last m) (fun j _ hj => ?_) (by simp)
        have : j.val < m := by
          have := j.isLt
          have : j.val ≠ m := fun h => hj (Fin.ext (by simpa using h))
          omega
        rw [h0 _ _ (by simp; omega)]
        simp
      rw [hsum] at hdet
      have hc : ∀ j : Fin (m + 1), ((Fin.castSucc (Fin.last m)).succAbove j).val =
          if j.val < m then j.val else j.val + 1 := by
        intro j
        rw [Fin.succAbove]
        by_cases hj : j.val < m
        · have : Fin.castSucc j < Fin.castSucc (Fin.last m) := by
            rw [Fin.castSucc_lt_castSucc_iff, Fin.lt_def]; simpa using hj
          simp [this, hj]
        · have : ¬ Fin.castSucc j < Fin.castSucc (Fin.last m) := by
            rw [Fin.castSucc_lt_castSucc_iff, Fin.lt_def]; simpa using hj
          simp [this, hj]
      have hM'' : HessNeg (M.submatrix (Fin.last (m + 1)).succAbove
          (Fin.castSucc (Fin.last m)).succAbove) := by
        refine ⟨fun i j h => h0 _ _ ?_, fun i j h => h1 _ _ ?_, fun i j h => h2 _ _ ?_⟩
        · have hi := i.isLt
          rw [Fin.succAbove_last] at *
          simp only [Fin.val_castSucc, hc] at *
          split_ifs <;> omega
        · have hi := i.isLt
          rw [Fin.succAbove_last] at *
          simp only [Fin.val_castSucc, hc] at *
          split_ifs <;> omega
        · have hi := i.isLt
          rw [Fin.succAbove_last] at *
          simp only [Fin.val_castSucc, hc] at *
          split_ifs <;> omega
      have hlast2 := ih _ hM''
      rw [hdet]
      simp only [Fin.succAbove_last, Fin.val_last, Fin.val_castSucc] at *
      have e1 : M (Fin.last (m + 1)) (Fin.castSucc (Fin.last m)) = 1 :=
        h1 _ _ (by simp)
      rw [e1]
      generalize (M.submatrix Fin.castSucc (Fin.last m).castSucc.succAbove).det = d2 at *
      generalize (M.submatrix Fin.castSucc Fin.castSucc).det = d1 at *
      generalize M (Fin.last (m + 1)) (Fin.last (m + 1)) = a at *
      rcases neg_one_pow_eq_or ℚ m with h | h <;>
        simp only [pow_succ, pow_add, h] at hlast hlast2 ⊢ <;> nlinarith

/-! ### The alphabet `1^x` and the elementary functions -/

/-- The specialization `p_j ↦ x` as an algebra homomorphism. -/
def specAlg (x : ℚ) : Lambda →ₐ[ℚ] ℚ :=
  (MvPolynomial.aeval fun _ : ℕ+ => x).comp powerSumEquiv.symm.toAlgHom

theorem specAlg_apply (x : ℚ) (Q : Lambda) : specAlg x Q = powerSumSpecialize x Q := rfl

theorem specAlg_pPoly (x : ℚ) {k : ℕ} (hk : 0 < k) : specAlg x (pPoly k) = x := by
  have h : powerSumEquiv.symm (pPoly k) = MvPolynomial.X (⟨k, hk⟩ : ℕ+) :=
    powerSumEquiv_symm_pPoly (⟨k, hk⟩ : ℕ+)
  change MvPolynomial.aeval (fun _ : ℕ+ => x) (powerSumEquiv.symm (pPoly k)) = x
  rw [h]
  exact MvPolynomial.aeval_X _ _

/-- The ring homomorphism `ev x`. -/
abbrev specHom (x : ℚ) : Lambda →+* ℚ := (specAlg x : Lambda →+* ℚ)

/-- The series `Σ (-1)^k e_k(1^x) t^k`. -/
def eSpec (x : ℚ) : PowerSeries ℚ := PowerSeries.map (specHom x) eSeries

/-- The series `Σ h_k(1^x) t^k`. -/
def hSpec (x : ℚ) : PowerSeries ℚ := PowerSeries.map (specHom x) hSeries

theorem eSpec_mul_hSpec (x : ℚ) : eSpec x * hSpec x = 1 := by
  rw [eSpec, hSpec, ← map_mul, eSeries_mul_hSeries, map_one]

theorem map_derivative_spec (x : ℚ) (F : PowerSeries Lambda) :
    PowerSeries.map (specHom x) (PowerSeries.derivative F) =
      PowerSeries.derivative (PowerSeries.map (specHom x) F) := by
  ext n
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]

theorem coeff_newtonSpec (x : ℚ) (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.map (specHom x) newtonSeries) =
      if m = 0 then 0 else x := by
  rw [PowerSeries.coeff_map]
  rcases m with _ | m
  · simp [newtonSeries, pPoly]
  · simp only [newtonSeries, PowerSeries.coeff_mk]
    change specAlg x (pPoly (m + 1)) = _
    rw [specAlg_pPoly x (Nat.succ_pos m)]
    simp

theorem hSpec_ode (x : ℚ) :
    (1 - PowerSeries.X) * PowerSeries.derivative (hSpec x) = PowerSeries.C x * hSpec x := by
  have hN := congrArg (PowerSeries.map (specHom x)) newtonSeries_mul_hSeries
  rw [map_mul, map_mul, PowerSeries.map_X, map_derivative_spec] at hN
  have hnew : (1 - PowerSeries.X) * PowerSeries.map (specHom x) newtonSeries =
      PowerSeries.C x * PowerSeries.X := by
    ext n
    rw [sub_mul, one_mul, map_sub]
    rcases n with _ | n
    · rw [PowerSeries.coeff_zero_X_mul, mul_comm, PowerSeries.coeff_zero_X_mul, coeff_newtonSpec]
      simp
    · rw [PowerSeries.coeff_succ_X_mul, coeff_newtonSpec, coeff_newtonSpec,
        mul_comm (PowerSeries.C x), PowerSeries.coeff_succ_X_mul]
      rcases n with _ | n
      · simp
      · simp
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℚ))
  have : PowerSeries.X * ((1 - PowerSeries.X) * PowerSeries.derivative (hSpec x)) =
      (1 - PowerSeries.X) * (PowerSeries.map (specHom x) newtonSeries * hSpec x) := by
    have hN' : PowerSeries.map (specHom x) newtonSeries * hSpec x =
        PowerSeries.X * PowerSeries.derivative (hSpec x) := hN
    rw [mul_left_comm, hN']
  rw [this, ← mul_assoc, hnew]; ring

theorem eSpec_ode (x : ℚ) :
    (1 - PowerSeries.X) * PowerSeries.derivative (eSpec x) = - (PowerSeries.C x * eSpec x) := by
  have h1 := eSpec_mul_hSpec x
  have h2 : PowerSeries.derivative (eSpec x) * hSpec x +
      eSpec x * PowerSeries.derivative (hSpec x) = 0 := by
    have := congrArg PowerSeries.derivative h1
    rw [Derivation.leibniz] at this
    simpa [smul_eq_mul, mul_comm, add_comm] using this
  have h3 := hSpec_ode x
  linear_combination (-(1 - PowerSeries.X) * PowerSeries.derivative (eSpec x)
      - PowerSeries.C x * eSpec x) * h1 + (eSpec x * (1 - PowerSeries.X)) * h2
      - eSpec x ^ 2 * h3

/-! ### Signs of the coefficients of `eSpec` -/

theorem eSpec_coeff_zero (x : ℚ) : PowerSeries.coeff 0 (eSpec x) = 1 := by
  simp [eSpec, eSeries, PowerSeries.coeff_map, elem]

theorem eSpec_rec (x : ℚ) (n : ℕ) :
    ((n : ℚ) + 1) * PowerSeries.coeff (n + 1) (eSpec x) =
      ((n : ℚ) - x) * PowerSeries.coeff n (eSpec x) := by
  have h := congrArg (PowerSeries.coeff n) (eSpec_ode x)
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_derivative, map_neg,
    show PowerSeries.C x * eSpec x = x • eSpec x by simp [PowerSeries.smul_eq_C_mul],
    map_smul] at h
  rcases n with _ | n
  · simp at h ⊢
    linarith
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative] at h
    push_cast at h ⊢
    simp only [smul_eq_mul] at h
    linarith

theorem eSpec_coeff_neg {x : ℚ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ n : ℕ, PowerSeries.coeff (n + 1) (eSpec x) < 0 := by
  intro n
  induction n with
  | zero =>
    have h := eSpec_rec x 0
    rw [eSpec_coeff_zero] at h
    simp at h
    linarith
  | succ n ih =>
    have h := eSpec_rec x (n + 1)
    have hn : (1 : ℚ) ≤ ((n + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos n
    push_cast at h hn
    nlinarith

/-- The coefficient of `eSpec x` at an integer index, zero for negative indices. -/
def aVal (x : ℚ) (k : ℤ) : ℚ := if k < 0 then 0 else PowerSeries.coeff k.toNat (eSpec x)

theorem spec_elem (x : ℚ) (n : ℕ) :
    specAlg x (elem n) = (-1) ^ n * PowerSeries.coeff n (eSpec x) := by
  have : PowerSeries.coeff n (eSpec x) = (-1) ^ n * specAlg x (elem n) := by
    simp [eSpec, eSeries, PowerSeries.coeff_map]
  rw [this, ← mul_assoc, ← mul_pow]
  simp

theorem spec_iota_hh (x : ℚ) (k : ℤ) :
    specAlg x (schurInvolution (hh k)) = if k < 0 then 0 else (-1) ^ k.toNat * aVal x k := by
  by_cases hk : k < 0
  · simp [hk]
  · have : hh k = hPos k.toNat := by
      rw [← hh_natCast]; congr 1; omega
    simp [hk, this, schurInvolution_hPos, spec_elem, aVal]

/-! ### Profiles with vanishing overlaps -/

theorem neg_one_pow_sq (n : ℕ) : ((-1 : ℚ) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow]; simp

theorem spec_iota_profile_ne_zero {x : ℚ} (hx0 : 0 < x) (hx1 : x < 1) {n : ℕ} (P : Profile n)
    (hg : ∀ j, P.g j = 0) : specAlg x (schurInvolution P.schur) ≠ 0 := by
  set φ : Lambda →+* ℚ := ((specAlg x).toRingHom.comp schurInvolution.toRingHom) with hφ
  have hφapp : ∀ f, φ f = specAlg x (schurInvolution f) := fun f => rfl
  have hdet : specAlg x (schurInvolution P.schur) =
      (Matrix.of fun i j : Fin (n + 1) => φ (hh (P.xi i - P.zeta j))).det := by
    rw [← hφapp, Profile.schur, RingHom.map_det]
    rfl
  set c : Fin (n + 1) → ℚ := fun i => (-1) ^ (P.xi i).toNat
  set d : Fin (n + 1) → ℚ := fun j => (-1) ^ (P.zeta j).toNat
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
    Matrix.of fun i j => aVal x (P.xi i - P.zeta j)
  have hentry : (Matrix.of fun i j : Fin (n + 1) => φ (hh (P.xi i - P.zeta j))) =
      Matrix.of fun i j => c i * (d j * A i j) := by
    ext i j
    simp only [Matrix.of_apply, hφapp, spec_iota_hh, A]
    by_cases hk : P.xi i - P.zeta j < 0
    · simp [hk, aVal]
    · simp only [hk, ite_false]
      have hz := P.zeta_nonneg j
      have hx := P.xi_pos i
      have e1 : (P.xi i).toNat = (P.xi i - P.zeta j).toNat + (P.zeta j).toNat := by omega
      have e2 : (-1 : ℚ) ^ (P.xi i - P.zeta j).toNat =
          c i * d j := by
        have := neg_one_pow_sq (P.zeta j).toNat
        simp only [c, d]
        rw [e1, pow_add]
        calc (-1 : ℚ) ^ (P.xi i - P.zeta j).toNat
            = (-1) ^ (P.xi i - P.zeta j).toNat *
                ((-1) ^ (P.zeta j).toNat * (-1) ^ (P.zeta j).toNat) := by
              rw [this, mul_one]
          _ = _ := by ring
      rw [e2]; ring
  have hsucc : ∀ j : Fin n, P.xi j.succ = P.zeta j.castSucc := by
    intro j
    have := P.xi_succ_sub_zeta_castSucc j
    rw [hg j] at this
    omega
  have hA : HessNeg A := by
    refine ⟨fun i j h => ?_, fun i j h => ?_, fun i j h => ?_⟩
    · have hjn : j.val < n := by have := i.isLt; omega
      have hlt : P.xi i < P.xi (⟨j.val, hjn⟩ : Fin n).succ := by
        apply P.xi_strictAnti
        rw [Fin.lt_def]; simp; omega
      rw [hsucc] at hlt
      have hj : (⟨j.val, hjn⟩ : Fin n).castSucc = j := Fin.ext rfl
      rw [hj] at hlt
      have hneg : P.xi i - P.zeta j < 0 := by omega
      simp only [A, aVal, Matrix.of_apply, hneg, ite_true]
    · have hjn : j.val < n := by have := i.isLt; omega
      have hi : i = (⟨j.val, hjn⟩ : Fin n).succ := Fin.ext (by simp [h])
      have hj : (⟨j.val, hjn⟩ : Fin n).castSucc = j := Fin.ext rfl
      have h3 := hsucc ⟨j.val, hjn⟩
      rw [hj] at h3
      have hxi : P.xi i = P.zeta j := by rw [hi]; exact h3
      simp [A, aVal, hxi, eSpec_coeff_zero]
    · have hle : P.xi j ≤ P.xi i := P.xi_strictAnti.antitone (Fin.le_def.mpr h)
      have hr := P.r_pos j
      have hx := P.xi_sub_zeta j
      have hk : 1 ≤ (P.xi i - P.zeta j).toNat := by omega
      obtain ⟨m, hm⟩ : ∃ m, (P.xi i - P.zeta j).toNat = m + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hk).symm⟩
      simp only [A, aVal, Matrix.of_apply]
      simp only [show ¬ (P.xi i - P.zeta j < 0) by omega, ite_false, hm]
      exact eSpec_coeff_neg hx0 hx1 m
  have hdA := HessNeg.det_sign (n + 1) A hA
  have e1 := Matrix.det_mul_column c (Matrix.of fun i j => d j * A i j)
  have e2 := Matrix.det_mul_row d A
  rw [hdet, hentry]
  simp only [Matrix.of_apply] at e1 e2
  rw [e1, e2]
  have hc : ∏ i, c i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (by norm_num)
  have hd : ∏ i, d i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (by norm_num)
  have hA0 : A.det ≠ 0 := by
    intro h0; rw [h0] at hdA; simp at hdA
  exact mul_ne_zero hc (mul_ne_zero hd hA0)

/-! ### Ribbons -/

theorem profile_g_zero_of {n : ℕ} (P : Profile n) (h : ((∑ i, P.r i : ℕ) : ℤ) = P.xi 0) :
    ∀ j, P.g j = 0 := by
  have hzeta : P.zeta 0 = ∑ k : Fin n, ((P.r k.succ : ℤ) - P.g k) := by
    unfold Profile.zeta; simp
  have hx0 : P.xi 0 = P.zeta 0 + P.r 0 := rfl
  rw [Fin.sum_univ_succ] at h
  rw [hx0, hzeta, Finset.sum_sub_distrib] at h
  push_cast at h
  have hg : ∑ k : Fin n, (P.g k : ℤ) = 0 := by linarith
  have hg' : ∑ k : Fin n, P.g k = 0 := by exact_mod_cast hg
  intro j
  exact (Finset.sum_eq_zero_iff.mp hg') j (Finset.mem_univ j)

theorem ribbon_profile_g_zero {D : Diagram} (hD : IsRibbon D) :
    ∀ j, (cellProfile D).2.g j = 0 := by
  obtain ⟨v, hv⟩ := hD.1.exists_translate_cells
  have h2 := hD.2
  generalize cellProfile D = G at hv ⊢
  obtain ⟨n, P⟩ := G
  have hcard : D.card = ∑ i, P.r i := by
    rw [hv, Gluing.translate, Finset.card_image_of_injective _ (add_left_injective _),
      Profile.card_cells]
  have hspan : (span D : ℤ) = P.xi 0 := by
    rw [hv, span_translate, Profile.span_cells]
  rw [hcard] at h2
  exact profile_g_zero_of P (by rw [h2, hspan])

/-- **Nonvanishing of ribbon Schur functions at a fractional alphabet size.**  For a ribbon `D`
and `0 < x < 1`, the specialization `s_D(1^x)` is nonzero. -/
theorem ribbon_powerSumSpecialize_ne_zero {D : Diagram} (hD : IsRibbon D) {x : ℚ}
    (hx0 : 0 < x) (hx1 : x < 1) : powerSumSpecialize x (cellSchur D) ≠ 0 := by
  have hD' : IsRibbon (antitranspose D) := is_ribbon_antitranspose hD
  have h1 : cellSchur D = schurInvolution (cellSchur (antitranspose D)) := by
    rw [cellSchur_antitranspose, schurInvolution_involutive (cellSchur D)]
  rw [h1, ← specAlg_apply, cellSchur_of_isConnectedSkew hD'.1]
  exact spec_iota_profile_ne_zero hx0 hx1 _ (ribbon_profile_g_zero hD')

end SkewMarkedFactor
