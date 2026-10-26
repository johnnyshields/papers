/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/MurnaghanNakayama/Shift.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MurnaghanNakayama.Determinant
import SkewMarkedFactor.Gluing.DualEvaluation

/-!
# Multiplication by a power sum on a Jacobi–Trudi determinant, in `N` variables

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.1.3 (`OlsonHarris2024HopfApplications`), the
multiplication form of the Murnaghan–Nakayama rule.

In `N` variables `x_0, …, x_{N-1}` the determinant `det (h_{a_i + j})_{i,j < N}` satisfies
`p_m · det (h_{a_i + j}) = Σ_k det (h_{a_i + m δ_{ik} + j})` (`psum_mul_det_eq_sum`), for
`a_i ≥ -(N-1)`.  The proof multiplies the matrix `H = (h_{a_i + j})` by the matrix
`C_{jl} = Σ_u (-1)^u e_u x_l^{N-1-j-u}` and gets `H C = (x_l^{a_i + N - 1})`
(`hMatrix_mul_C`); a matrix `C` with `det C ≠ 0` and the trace formula
`Σ_k det (A with row k replaced by (A_k B)) = det A · tr B` finish.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace MN

open MvPolynomial

/-! ### The trace formula for row replacement -/

section Trace

variable {n : ℕ} {R : Type*} [CommRing R]

theorem det_updateRow_eq_sum (A : Matrix (Fin n) (Fin n) R) (k : Fin n) (r : Fin n → R) :
    (A.updateRow k r).det = ∑ j, A.adjugate j k * r j := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- `Σ_k det (A with row k replaced by A_k B) = det A · tr B`. -/
theorem sum_det_updateRow_vecMul (A B : Matrix (Fin n) (Fin n) R) :
    ∑ k, (A.updateRow k (Matrix.vecMul (A k) B)).det = A.det * B.trace := by
  simp only [det_updateRow_eq_sum]
  have h1 : ∑ k, ∑ j, A.adjugate j k * Matrix.vecMul (A k) B j = (A.adjugate * (A * B)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
  rw [h1, ← Matrix.mul_assoc, Matrix.adjugate_mul]
  simp [Matrix.trace_smul]

end Trace

/-! ### The identity `x_l^t = Σ_r D_{l,r} h_{t-r}` -/

section NVar

variable (N : ℕ)

/-- `h_k` of the `N` variables, `0` for negative `k`. -/
noncomputable def hs (k : ℤ) : MvPolynomial (Fin N) ℚ :=
  if k < 0 then 0 else hsymm (Fin N) ℚ k.toNat

/-- `e_r` of the `N` variables. -/
noncomputable def es (r : ℕ) : MvPolynomial (Fin N) ℚ := esymm (Fin N) ℚ r

/-- `D_{l,r} = Σ_{u ≤ r} (-1)^u e_u x_l^{r-u}`, which is `(-1)^r` times the `r`-th elementary
symmetric polynomial of the variables other than `x_l`. -/
noncomputable def Dc (l : Fin N) (r : ℕ) : MvPolynomial (Fin N) ℚ :=
  ∑ u ∈ Finset.range (r + 1), (-1) ^ u * es N u * X l ^ (r - u)

theorem hs_neg {k : ℤ} (hk : k < 0) : hs N k = 0 := by simp [hs, hk]

theorem hs_nat (k : ℕ) : hs N (k : ℤ) = hsymm (Fin N) ℚ k := by simp [hs]

theorem hs_zero : hs N 0 = 1 := by
  have := hs_nat N 0
  simpa [hsymm_zero] using this

theorem evalComplete_hh_eq (k : ℤ) :
    evalComplete N (varAlphabet N) (hh k) = hs N k := by
  rw [evalComplete_hh]
  unfold hs
  split_ifs
  · rfl
  · exact completeHom_varAlphabet N _

theorem es_eq_zero {r : ℕ} (hr : N < r) : es N r = 0 := by
  unfold es esymm
  rw [Finset.powersetCard_eq_empty.mpr (by simpa using hr)]
  simp

open AlgebraicCombinatorics.SymmetricPolynomials in
/-- Newton's identity `Σ_r (-1)^r e_r h_{t-r} = 0` for `t ≥ 1`, summed over `r ≤ N`. -/
theorem newton_eh_range (t : ℕ) (ht : 1 ≤ t) :
    ∑ r ∈ Finset.range (N + 1), (-1) ^ r * es N r * hs N ((t : ℤ) - r) = 0 := by
  have hNG := newtonGirard_eh (K := ℚ) (N := N) t (by omega)
  have e1 : ∑ r ∈ Finset.range (t + 1), (-1 : MvPolynomial (Fin N) ℚ) ^ r * es N r *
      hs N ((t : ℤ) - r) = 0 := by
    rw [← hNG]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r ≤ t := by simpa [Nat.lt_succ_iff] using hr
    have : ((t : ℤ) - r) = ((t - r : ℕ) : ℤ) := by omega
    rw [this, hs_nat]
    rfl
  have e2 : ∀ r, N < r → (-1 : MvPolynomial (Fin N) ℚ) ^ r * es N r * hs N ((t : ℤ) - r) = 0 :=
    fun r hr => by rw [es_eq_zero N hr]; simp
  have e3 : ∀ r, t < r → (-1 : MvPolynomial (Fin N) ℚ) ^ r * es N r * hs N ((t : ℤ) - r) = 0 :=
    fun r hr => by rw [hs_neg N (by omega)]; simp
  have e4 : ∑ r ∈ Finset.range (N + 1), (-1 : MvPolynomial (Fin N) ℚ) ^ r * es N r *
        hs N ((t : ℤ) - r) =
      ∑ r ∈ Finset.range (max N t + 1), (-1 : MvPolynomial (Fin N) ℚ) ^ r * es N r *
        hs N ((t : ℤ) - r) := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun r hr hr' => ?_
    exact e2 r (by simp at hr hr'; omega)
  have e5 : ∑ r ∈ Finset.range (t + 1), (-1 : MvPolynomial (Fin N) ℚ) ^ r * es N r *
        hs N ((t : ℤ) - r) =
      ∑ r ∈ Finset.range (max N t + 1), (-1 : MvPolynomial (Fin N) ℚ) ^ r * es N r *
        hs N ((t : ℤ) - r) := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun r hr hr' => ?_
    exact e3 r (by simp at hr hr'; omega)
  rw [e4, ← e5, e1]

/-- Vieta at `x_l`: `Σ_{u ≤ N} (-1)^u e_u x_l^{N-u} = ∏_i (x_l - x_i) = 0`. -/
theorem Dc_N (l : Fin N) : Dc N l N = 0 := by
  set s : Multiset (MvPolynomial (Fin N) ℚ) :=
    (Finset.univ : Finset (Fin N)).val.map (X : Fin N → MvPolynomial (Fin N) ℚ) with hs_def
  have hV := Multiset.prod_X_sub_X_eq_sum_esymm s
  have hcard : Multiset.card s = N := by simp [hs_def]
  rw [hcard] at hV
  have hev := congrArg (Polynomial.eval (X l : MvPolynomial (Fin N) ℚ)) hV
  have hL : Polynomial.eval (X l : MvPolynomial (Fin N) ℚ)
      ((s.map fun t => Polynomial.X - Polynomial.C t).prod) = 0 := by
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨X l, ?_, by simp⟩
    rw [hs_def, Multiset.mem_map]
    exact ⟨l, Finset.mem_univ l, rfl⟩
  rw [hL] at hev
  have hes : ∀ j, s.esymm j = es N j := fun j => by
    have := congrFun (esymm_eq_multiset_esymm (Fin N) ℚ) j
    simpa [es, hs_def] using this.symm
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X, hes] at hev
  unfold Dc
  rw [hev]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

theorem hs_shift (s r : ℕ) : hs N (((s + 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ)) = hs N ((s : ℤ) - r) := by
  congr 1
  push_cast
  ring

theorem Dc_zero (l : Fin N) : Dc N l 0 = 1 := by
  simp [Dc, es, esymm_zero]

theorem Dc_succ (l : Fin N) (r : ℕ) :
    Dc N l (r + 1) = X l * Dc N l r + (-1) ^ (r + 1) * es N (r + 1) := by
  unfold Dc
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have : ∀ u ∈ Finset.range (r + 1), (-1 : MvPolynomial (Fin N) ℚ) ^ u * es N u *
      X l ^ (r + 1 - u) = X l * ((-1) ^ u * es N u * X l ^ (r - u)) := by
    intro u hu
    have hu' : u ≤ r := by simpa [Nat.lt_succ_iff] using hu
    rw [show r + 1 - u = (r - u) + 1 by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl this]
  simp

/-- **The key identity.**  `x_l^t = Σ_{r < N} D_{l,r} h_{t-r}`. -/
theorem sum_Dc_hs (l : Fin N) (t : ℕ) :
    ∑ r ∈ Finset.range N, Dc N l r * hs N ((t : ℤ) - r) = X l ^ t := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by have := l.pos; omega⟩
  induction t with
  | zero =>
    rw [Finset.sum_range_succ', Dc_zero]
    have : ∀ r ∈ Finset.range N', Dc (N' + 1) l (r + 1) * hs (N' + 1) (((0 : ℕ) : ℤ) -
        ((r + 1 : ℕ) : ℤ)) = 0 := fun r _ => by
      rw [hs_neg _ (by push_cast; omega), mul_zero]
    rw [Finset.sum_eq_zero this]
    simp [hs_zero]
  | succ s ih =>
    have hNG := newton_eh_range (N' + 1) (s + 1) (by omega)
    rw [Finset.sum_range_succ', Finset.sum_range_succ] at hNG
    simp only [hs_shift, es, esymm_zero, pow_zero, mul_one, Nat.cast_zero, sub_zero] at hNG
    have hD := Dc_N (N' + 1) l
    rw [Dc_succ] at hD
    rw [Finset.sum_range_succ', Finset.sum_congr rfl (fun r _ => by
      rw [Dc_succ, hs_shift])]
    rw [pow_succ, ← ih, Finset.sum_range_succ]
    simp only [add_mul, Finset.sum_add_distrib, Dc_zero, one_mul, Nat.cast_zero, sub_zero]
    have hx : ∑ r ∈ Finset.range N', X l * Dc (N' + 1) l r * hs (N' + 1) ((s : ℤ) - r) =
        (∑ r ∈ Finset.range N', Dc (N' + 1) l r * hs (N' + 1) ((s : ℤ) - r)) * X l := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by ring
    have hes : ∀ x, es (N' + 1) x = esymm (Fin (N' + 1)) ℚ x := fun _ => rfl
    simp only [hes] at hD hNG ⊢
    simp only [Nat.cast_add, Nat.cast_one] at hNG ⊢
    linear_combination hNG - hs (N' + 1) ((s : ℤ) - N') * hD + hx

/-- The matrix `C_{jl} = D_{l, N-1-j}`. -/
noncomputable def Cmat : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) ℚ) :=
  Matrix.of fun j l => Dc N l (N - 1 - j)

/-- The matrix `H_{ij} = h_{a_i + j}`. -/
noncomputable def hMat (a : Fin N → ℤ) : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) ℚ) :=
  Matrix.of fun i j => hs N (a i + j)

/-- The matrix `X_{il} = x_l^{a_i + N - 1}`. -/
noncomputable def xMat (a : Fin N → ℤ) : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) ℚ) :=
  Matrix.of fun i l => X l ^ (a i + N - 1).toNat

theorem hMat_mul_Cmat (a : Fin N → ℤ) (ha : ∀ i, 0 ≤ a i + N - 1) :
    hMat N a * Cmat N = xMat N a := by
  refine Matrix.ext fun i l => ?_
  simp only [Matrix.mul_apply, hMat, Cmat, Matrix.of_apply, xMat]
  set G : ℕ → MvPolynomial (Fin N) ℚ := fun j => hs N (a i + (j : ℤ)) * Dc N l (N - 1 - j)
    with hG
  have hG' : ∑ j : Fin N, hs N (a i + ((j : ℕ) : ℤ)) * Dc N l (N - 1 - j) =
      ∑ r ∈ Finset.range N, G r := Fin.sum_univ_eq_sum_range G N
  rw [hG', ← Finset.sum_range_reflect G N]
  rw [← sum_Dc_hs N l (a i + N - 1).toNat]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r < N := Finset.mem_range.mp hr
  have e1 : N - 1 - (N - 1 - r) = r := by omega
  have e2 : a i + ((N - 1 - r : ℕ) : ℤ) = (((a i + N - 1).toNat : ℕ) : ℤ) - r := by
    have := ha i
    rw [Int.toNat_of_nonneg this]
    omega
  simp only [hG]
  rw [e1, e2, mul_comm]

theorem det_Cmat_ne_zero : (Cmat N).det ≠ 0 := by
  have h0 := hMat_mul_Cmat N (fun i => (i : ℤ) - (N - 1)) (fun i => by omega)
  have hV : xMat N (fun i => (i : ℤ) - (N - 1)) = (Matrix.vandermonde (X : Fin N →
      MvPolynomial (Fin N) ℚ)).transpose := by
    refine Matrix.ext fun i l => ?_
    simp only [xMat, Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
    have : ((i : ℕ) : ℤ) - ((N : ℤ) - 1) + N - 1 = ((i : ℕ) : ℤ) := by ring
    rw [this, Int.toNat_natCast]
  have hdet : (xMat N (fun i => (i : ℤ) - (N - 1))).det ≠ 0 := by
    rw [hV, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr (MvPolynomial.X_injective)
  intro hC
  apply hdet
  rw [← h0, Matrix.det_mul, hC, mul_zero]

/-- **Multiplication by `p_m` on the determinant `det (h_{a_i + j})`.** -/
theorem psum_mul_det_eq_sum (a : Fin N → ℤ) (ha : ∀ i, 0 ≤ a i + N - 1) (m : ℕ) :
    psum (Fin N) ℚ m * (hMat N a).det =
      ∑ k : Fin N, (hMat N (Function.update a k (a k + m))).det := by
  have hCne := det_Cmat_ne_zero N
  apply mul_right_cancel₀ hCne
  have hk : ∀ k : Fin N, (hMat N (Function.update a k (a k + m))).det * (Cmat N).det =
      ((xMat N a).updateRow k (Matrix.vecMul (xMat N a k)
        (Matrix.diagonal fun l => X l ^ m))).det := by
    intro k
    have ha' : ∀ i, 0 ≤ Function.update a k (a k + m) i + N - 1 := by
      intro i
      by_cases hik : i = k
      · subst hik; have := ha i; simp only [Function.update_self]; omega
      · rw [Function.update_of_ne hik]; exact ha i
    rw [← Matrix.det_mul, hMat_mul_Cmat N _ ha']
    congr 1
    refine Matrix.ext fun i l => ?_
    by_cases hik : i = k
    · subst hik
      simp only [xMat, Matrix.of_apply, Function.update_self, Matrix.updateRow_self,
        Matrix.vecMul_diagonal]
      rw [← pow_add]
      have := ha i
      have e : (a i + (m : ℤ) + N - 1).toNat = (a i + N - 1).toNat + m := by omega
      rw [e]
    · simp only [xMat, Matrix.of_apply, Function.update_of_ne hik, Matrix.updateRow_ne hik]
  rw [Finset.sum_mul, Finset.sum_congr rfl fun k _ => hk k, sum_det_updateRow_vecMul,
    Matrix.trace_diagonal]
  have h1 : (xMat N a).det = (hMat N a).det * (Cmat N).det := by
    rw [← hMat_mul_Cmat N a ha, Matrix.det_mul]
  rw [h1]
  simp only [psum]
  ring

end NVar

/-! ### Evaluation of `Λ` -/

theorem evalComplete_hPos_eq (N k : ℕ) :
    evalComplete N (varAlphabet N) (hPos k) = hsymm (Fin N) ℚ k := by
  rw [evalComplete_hPos, completeHom_varAlphabet]

open AlgebraicCombinatorics.SymmetricPolynomials in
/-- The power sum `p_m ∈ Λ` evaluates to the power sum polynomial in `N` variables. -/
theorem evalComplete_pPoly (N : ℕ) :
    ∀ m, 0 < m → evalComplete N (varAlphabet N) (pPoly m) = psum (Fin N) ℚ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hNG := newtonGirard_hp (K := ℚ) (N := N) (n + 1) (by omega)
    rw [Finset.sum_range_succ] at hNG
    simp only [Nat.add_sub_cancel, Nat.sub_self, h_zero, one_mul] at hNG
    rw [pPoly, map_sub, map_mul, map_sum, evalComplete_hPos_eq, map_natCast,
      Fin.sum_univ_eq_sum_range (fun i => evalComplete N (varAlphabet N)
        (pPoly (i + 1) * hPos (n - i))) n]
    have : ∀ i ∈ Finset.range n, evalComplete N (varAlphabet N) (pPoly (i + 1) * hPos (n - i)) =
        hsymm (Fin N) ℚ (n - i) * psum (Fin N) ℚ (i + 1) := by
      intro i hi
      rw [map_mul, ih (i + 1) (by have := Finset.mem_range.mp hi; omega) (by omega),
        evalComplete_hPos_eq, mul_comm]
    rw [Finset.sum_congr rfl this]
    have e : ∀ j ∈ Finset.range n, h (K := ℚ) (N := N) (n - j) * p (j + 1) =
        hsymm (Fin N) ℚ (n - j) * psum (Fin N) ℚ (j + 1) := fun _ _ => rfl
    rw [Finset.sum_congr rfl e] at hNG
    change _ = psum (Fin N) ℚ (n + 1)
    have : psum (Fin N) ℚ (n + 1) = p (K := ℚ) (N := N) (n + 1) := rfl
    rw [this]
    linear_combination -hNG

theorem evalComplete_jtDet (N : ℕ) (a : Fin N → ℤ) :
    evalComplete N (varAlphabet N) (jtDet a fun j : Fin N => -(j : ℤ)) = (hMat N a).det := by
  unfold jtDet
  rw [evalComplete, AlgHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hMat]
  have := evalComplete_hh_eq N (a i - -(j : ℤ))
  unfold evalComplete at this
  rw [this]
  congr 1
  ring

end MN

end Plan

end SkewMarkedFactor.Gluing
