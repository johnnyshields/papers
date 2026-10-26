/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The bordered determinant over a commutative ring

The determinant of a matrix bordered by one row and one column is
`det [[M, a], [b, c]] = c det M - b ⬝ adj(M) a` over any commutative ring.  This is the algebra
behind `sc:restoration-polynomial` and `sc:bordered-grade` in
`shields-2026-skew-coframe-rigidity.tex`.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open Matrix Polynomial

variable {R : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]

/-- `M` bordered by the column `a`, the row `b` and the corner `c`. -/
def bordered (M : Matrix m m R) (a b : m → R) (c : R) : Matrix (m ⊕ Unit) (m ⊕ Unit) R :=
  Matrix.fromBlocks M (Matrix.replicateCol Unit a) (Matrix.replicateRow Unit b)
    (Matrix.of fun _ _ => c)

/-- The bordered determinant over a domain-free ring, once `det M` is a nonzerodivisor. -/
theorem det_bordered_of_regular (M : Matrix m m R) (a b : m → R) (c : R)
    (hreg : IsRegular M.det) :
    (bordered M a b c).det = c * M.det - b ⬝ᵥ (M.adjugate *ᵥ a) := by
  by_cases hm : IsEmpty m
  · have h1 : M.det = 1 := by simp [Matrix.det_isEmpty]
    have h2 : (bordered M a b c).det = c := by
      have : bordered M a b c = Matrix.fromBlocks M (Matrix.replicateCol Unit a) 0
          (Matrix.of fun _ _ => c) := by
        ext i j
        rcases i with i | i
        · rcases j with j | j <;> simp [bordered]
        · rcases j with j | j
          · exact (hm.false j).elim
          · simp [bordered]
      rw [this, Matrix.det_fromBlocks_zero₂₁, h1, Matrix.det_unique]
      simp
    simp [h1, h2]
  · rw [not_isEmpty_iff] at hm
    have hcard : 0 < Fintype.card m := Fintype.card_pos
    let L : Matrix (m ⊕ Unit) (m ⊕ Unit) R :=
      Matrix.fromBlocks M.adjugate 0 (-(Matrix.replicateRow Unit (b ᵥ* M.adjugate)))
        (Matrix.of fun _ _ => M.det)
    have hvec : (b ᵥ* M.adjugate) ᵥ* M = M.det • b := by
      rw [Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
    have hLN : L * bordered M a b c = Matrix.fromBlocks (M.det • (1 : Matrix m m R))
        (Matrix.replicateCol Unit (M.adjugate *ᵥ a)) 0
        (Matrix.of fun _ _ => c * M.det - b ⬝ᵥ (M.adjugate *ᵥ a)) := by
      simp only [L, bordered, Matrix.fromBlocks_multiply]
      congr 1
      · simp [Matrix.adjugate_mul]
      · ext i j
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      · ext i j
        have := congrFun hvec j
        simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.neg_apply, Matrix.replicateRow_apply,
          Matrix.zero_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
        simp only [Matrix.vecMul, dotProduct] at this ⊢
        simp only [Finset.sum_neg_distrib, neg_mul, Finset.univ_unique, Finset.sum_singleton] at this ⊢
        linear_combination (-1 : R) * this
      · ext i j
        have hs : ∑ j, (∑ x, b x * M.adjugate x j) * a j =
            ∑ x, b x * ∑ j, M.adjugate x j * a j := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          simp [mul_assoc]
        simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.mulVec, hs]
        ring
    have hdetL : L.det = M.det ^ Fintype.card m := by
      simp only [L]
      rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_adjugate]
      simp
      rw [← pow_succ]
      congr 1; omega
    have hdetR : (Matrix.fromBlocks (M.det • (1 : Matrix m m R))
        (Matrix.replicateCol Unit (M.adjugate *ᵥ a)) 0
        (Matrix.of fun _ _ => c * M.det - b ⬝ᵥ (M.adjugate *ᵥ a))).det =
        M.det ^ Fintype.card m * (c * M.det - b ⬝ᵥ (M.adjugate *ᵥ a)) := by
      rw [Matrix.det_fromBlocks_zero₂₁]
      simp
    have key := congrArg Matrix.det hLN
    rw [Matrix.det_mul, hdetL, hdetR] at key
    exact (hreg.pow (n := Fintype.card m)).left key

/-- **The bordered determinant** over any commutative ring. -/
theorem det_bordered (M : Matrix m m R) (a b : m → R) (c : R) :
    (bordered M a b c).det = c * M.det - b ⬝ᵥ (M.adjugate *ᵥ a) := by
  let M' : Matrix m m R[X] := Matrix.charmatrix (-M)
  have hreg : IsRegular M'.det := by
    have : M'.det = (-M).charpoly := rfl
    rw [this]
    exact (Matrix.charpoly_monic _).isRegular
  have h := det_bordered_of_regular M' (fun i => Polynomial.C (a i)) (fun i => Polynomial.C (b i))
    (Polynomial.C c) hreg
  have h0 := congrArg (Polynomial.evalRingHom (0 : R)) h
  have hM' : (Polynomial.evalRingHom (0 : R)).mapMatrix M' = M := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [M', Matrix.charmatrix_apply]
    · simp [M', Matrix.charmatrix_apply, hij]
  have hb : (Polynomial.evalRingHom (0 : R)).mapMatrix
      (bordered M' (fun i => Polynomial.C (a i)) (fun i => Polynomial.C (b i)) (Polynomial.C c)) =
      bordered M a b c := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simpa [bordered] using congrFun (congrFun hM' i) j
    all_goals simp [bordered]
  have hl := RingHom.map_det (Polynomial.evalRingHom (0 : R)) (bordered M'
    (fun i => Polynomial.C (a i)) (fun i => Polynomial.C (b i)) (Polynomial.C c))
  rw [hb] at hl
  have hd := RingHom.map_det (Polynomial.evalRingHom (0 : R)) M'
  rw [hM'] at hd
  have hadj : ∀ i j, Polynomial.evalRingHom (0 : R) (M'.adjugate i j) = M.adjugate i j := by
    intro i j
    have := congrFun (congrFun (RingHom.map_adjugate (Polynomial.evalRingHom (0 : R)) M') i) j
    simpa [hM'] using this
  rw [← hl, h, map_sub, map_mul, hd]
  have hadj' : ∀ i j, Polynomial.eval (0 : R) (M'.adjugate i j) = M.adjugate i j := hadj
  simp [dotProduct, Matrix.mulVec, Polynomial.eval_finset_sum, hadj']

/-- **The bordered grade** (`sc:bordered-grade`): scaling the positive letters by `ε = X` and the
new unit by `ν` gives `ν ε^r det N - ε^{r+1} (b ⬝ adj N a)`, `r` the order of `N`. -/
theorem det_bordered_scaled (N : Matrix m m R) (a b : m → R) (ν : R) :
    (bordered ((Polynomial.X : R[X]) • N.map Polynomial.C) ((Polynomial.X : R[X]) • fun i => (Polynomial.C (a i) : R[X]))
      ((Polynomial.X : R[X]) • fun i => (Polynomial.C (b i) : R[X])) ((Polynomial.C ν : R[X]))).det =
      (Polynomial.C ν : R[X]) * Polynomial.X ^ Fintype.card m * Polynomial.C N.det -
        Polynomial.X ^ (Fintype.card m + 1) * Polynomial.C (b ⬝ᵥ (N.adjugate *ᵥ a)) := by
  rw [det_bordered, Matrix.det_smul]
  have hdet : (N.map Polynomial.C).det = Polynomial.C N.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [hdet]
  by_cases hm : IsEmpty m
  · have h0 : b ⬝ᵥ (N.adjugate *ᵥ a) = 0 := by simp [dotProduct]
    simp [h0, dotProduct]
  · rw [not_isEmpty_iff] at hm
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card m = k + 1 := ⟨Fintype.card m - 1, by
      have := Fintype.card_pos (α := m); omega⟩
    have hadj : (((Polynomial.X : R[X]) • N.map Polynomial.C)).adjugate =
        (Polynomial.X : R[X]) ^ k • (N.adjugate).map Polynomial.C := by
      rw [Matrix.adjugate_smul, hk, Nat.add_sub_cancel]
      congr 1
      exact (RingHom.map_adjugate (Polynomial.C : R →+* R[X]) N).symm
    have hdot : (fun i => (Polynomial.C (b i) : R[X])) ⬝ᵥ
        ((N.adjugate).map Polynomial.C *ᵥ fun i => (Polynomial.C (a i) : R[X])) =
        Polynomial.C (b ⬝ᵥ (N.adjugate *ᵥ a)) := by
      simp [dotProduct, Matrix.mulVec, map_sum]
    rw [hadj]
    simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hdot, hk]
    ring

end SkewCoframeRigidity.UnitRestoration
