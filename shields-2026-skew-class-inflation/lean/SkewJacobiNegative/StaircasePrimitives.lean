/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/StaircasePrimitives.lean

import SkewJacobiNegative.HessenbergExpansion
import SkewJacobiNegative.CornerAlgebra
import SkewJacobiNegative.PrivateEntries
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Primitive factors of staircase restrictions

The private largest generator and primitive affine factor in
`lem:staircase-content` of `shields-2026-skew-jacobi-negative.tex`.
The restriction is the erasure of the actual full Jacobi--Trudi determinant.
-/

namespace SkewJacobiNegative.Staircase

open Gluing
open scoped BigOperators
/-- A fixed classical normalization is shared by all actual gcd computations.
The subsequent monic-content construction removes its numerical unit. -/
noncomputable instance completeStrongNormalizationMonoid :
    StrongNormalizationMonoid CompleteRing :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

noncomputable instance completeStrongNormalizedGCDMonoid :
    StrongNormalizedGCDMonoid CompleteRing :=
  UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid CompleteRing


/-- Interior rows exceed the sum of both incident gaps.  Endpoint inequalities
are already part of `Profile`. -/
def Thick {n : ℕ} (P : Profile n) : Prop :=
  ∀ j k : Fin n, j.succ = k.castSucc → P.g j + P.g k < P.r j.succ

/-- The gap incident to the bottom row, with value zero for a singleton. -/
def lastGap {n : ℕ} (P : Profile n) : ℕ :=
  ∑ j : Fin n, if j.val + 1 = n then P.g j else 0

/-- The ordinary arithmetic domain of an oriented component after all q-seams
have been cut.  No polynomial conclusion is a field of this predicate. -/
structure QComponent {n : ℕ} (q : ℕ+) (P : Profile n) : Prop where
  thick : Thick P
  gap_pos : ∀ j, 0 < P.g j
  gap_ne : ∀ j, P.g j ≠ q.val
  bottom : q.val + lastGap P < P.r (Fin.last n)

/-- The actual restriction, not an independently presented interval polynomial. -/
noncomputable def restriction {n : ℕ} (q : ℕ+) (P : Profile n) : CompleteRing :=
  eraseGenerator q P.toBetaDiagram.schur

/-- The complete full-interval index, in the actual beta coordinates. -/
def fullIndex {n : ℕ} (P : Profile n) : ℤ := P.toBetaDiagram.largestLabel

/-- Its positive generator label. -/
def fullGenerator {n : ℕ} (P : Profile n) : ℕ+ :=
  ⟨(fullIndex P).toNat, by
    have hp : 0 < fullIndex P := P.toBetaDiagram.largestLabel_pos
    omega⟩

/-- The product of all internal gap generators, with repetitions retained. -/
noncomputable def gapMonomial {n : ℕ} (P : Profile n) : CompleteRing :=
  ∏ j : Fin n, complete (P.g j)

/-- The actual largest-corner residual after erasing the cut generator. -/
noncomputable def residual {n : ℕ} (q : ℕ+) (P : Profile n) : CompleteRing :=
  eraseGenerator q P.toBetaDiagram.cornerResidual

/-- Intrinsic thickness forces the genuine lower entries to be negative. -/
theorem Thick.hessenberg {n : ℕ} {P : Profile n} (hP : Thick P) : P.Hessenberg := by
  intro i j hij
  let a : Fin n := ⟨j.val, by omega⟩
  let b : Fin n := ⟨j.val + 1, by omega⟩
  have hab : a.succ = b.castSucc := by ext; rfl
  have hja : j = a.castSucc := by ext; rfl
  have hrow := hP a b hab
  have hz := P.zeta_castSucc a
  have hg := P.xi_succ_sub_zeta_castSucc b
  have hx := P.xi_sub_zeta a.succ
  have hbi : b.succ ≤ i := by
    change j.val + 1 + 1 ≤ i.val
    omega
  have hm : P.xi i ≤ P.xi b.succ := P.xi_strictAnti.antitone hbi
  rw [hja]
  rw [← hab] at hg
  have hcast : (P.g a : ℤ) + P.g b < P.r a.succ := by exact_mod_cast hrow
  omega

/-- The full index is strictly larger than every other actual entry label. -/
theorem index_lt_full {n : ℕ} (P : Profile n) (i j : Fin (n + 1))
    (h : i ≠ 0 ∨ j ≠ Fin.last n) :
    P.xi i - P.zeta j < fullIndex P :=
  P.toBetaDiagram.index_lt_largestLabel i j h

/-- The retained endpoint adjoining a cut makes the private index exceed q. -/
theorem fullIndex_gt_q {n : ℕ} {q : ℕ+} {P : Profile n} (hP : QComponent q P) :
    (q.val : ℤ) < fullIndex P := by
  have hb : q.val < P.r (Fin.last n) := by have := hP.bottom; omega
  have hm : P.xi (Fin.last n) ≤ P.xi 0 :=
    P.xi_strictAnti.antitone (Fin.zero_le _)
  have hz := P.zeta_last
  have hx := P.xi_sub_zeta (Fin.last n)
  have hc : (q.val : ℤ) < P.r (Fin.last n) := by exact_mod_cast hb
  change (q.val : ℤ) < P.xi 0 - P.zeta (Fin.last n)
  omega

/-- The full-corner minor is upper triangular, with actual gaps on its diagonal. -/
theorem cornerPolynomial_eq_gapMonomial {n : ℕ} {P : Profile n} (hP : Thick P) :
    P.toBetaDiagram.cornerPolynomial = gapMonomial P := by
  classical
  unfold BetaDiagram.cornerPolynomial
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_congr rfl
    intro i _
    change complete (P.xi i.succ - P.zeta i.castSucc) = complete (P.g i)
    rw [P.xi_succ_sub_zeta_castSucc]
  · intro i j hij
    change complete (P.xi i.succ - P.zeta j.castSucc) = 0
    apply complete_of_neg
    apply hP.hessenberg
    change j.val + 1 < i.val + 1
    exact Nat.add_lt_add_right hij 1

/-- Erasing q leaves every internal gap factor unchanged. -/
theorem erase_gapMonomial {n : ℕ} {q : ℕ+} {P : Profile n} (hP : QComponent q P) :
    eraseGenerator q (gapMonomial P) = gapMonomial P := by
  classical
  simp only [gapMonomial, map_prod, eraseGenerator_complete]
  apply Finset.prod_congr rfl
  intro j _
  rw [if_neg]
  exact_mod_cast hP.gap_ne j

/-- Gap positivity makes the actual largest-generator coefficient nonzero. -/
theorem gapMonomial_ne_zero {n : ℕ} (P : Profile n) : gapMonomial P ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact (complete_ne_zero_iff _).mpr (by positivity)

/-- Exact full-interval affine decomposition of the actual restricted determinant. -/
theorem restriction_affine {n : ℕ} {q : ℕ+} {P : Profile n} (hP : QComponent q P) :
    restriction q P = (-1 : CompleteRing) ^ n * gapMonomial P *
      MvPolynomial.X (fullGenerator P) + residual q P := by
  have hne : fullGenerator P ≠ q := by
    intro he
    have hv := congrArg Subtype.val he
    have hf : (q.val : ℤ) < P.toBetaDiagram.largestLabel := fullIndex_gt_q hP
    have hp := P.toBetaDiagram.largestLabel_pos
    have hvZ := congrArg (fun k : ℕ => (k : ℤ)) hv
    change ((P.toBetaDiagram.largestLabel.toNat : ℕ) : ℤ) = (q.val : ℤ) at hvZ
    rw [Int.toNat_of_nonneg hp.le] at hvZ
    exact (ne_of_gt hf) hvZ
  have hg : eraseGenerator q (MvPolynomial.X (fullGenerator P)) =
      MvPolynomial.X (fullGenerator P) := by
    simp only [eraseGenerator, MvPolynomial.eval₂Hom_X', if_neg hne]
  unfold restriction
  rw [P.toBetaDiagram.schur_corner_split]
  change eraseGenerator q
    ((-1 : CompleteRing) ^ n * P.toBetaDiagram.cornerPolynomial *
      MvPolynomial.X (fullGenerator P) + P.toBetaDiagram.cornerResidual) = _
  rw [cornerPolynomial_eq_gapMonomial hP.thick]
  simp only [map_add, map_mul, map_pow, map_neg, map_one, erase_gapMonomial hP, hg]
  rfl

/-- Dividing a nonzero polynomial cannot introduce a previously absent variable. -/
theorem not_mem_vars_of_dvd {a b : CompleteRing} (hb : b ≠ 0) (hab : a ∣ b)
    (v : ℕ+) (hv : v ∉ b.vars) : v ∉ a.vars := by
  classical
  obtain ⟨c, hc⟩ := hab
  have ha : a ≠ 0 := by intro h; simp [h] at hc; exact hb hc
  have hcn : c ≠ 0 := by intro h; simp [h] at hc; exact hb hc
  have hz : b.degreeOf v = 0 := by
    simpa only [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, not_not] using hv
  have hd := MvPolynomial.degreeOf_mul_eq (n := v) ha hcn
  rw [← hc, hz] at hd
  rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
  omega

/-- Erasure cannot introduce a variable absent from the original polynomial. -/
theorem not_mem_vars_erase (q v : ℕ+) (p : CompleteRing) (hv : v ∉ p.vars) :
    v ∉ (eraseGenerator q p).vars := by
  classical
  intro hm
  change v ∈ (MvPolynomial.bind₁
    (fun j : ℕ+ => if j = q then 0 else MvPolynomial.X j) p).vars at hm
  obtain ⟨j, hj, hjv⟩ := MvPolynomial.mem_vars_bind₁ _ _ hm
  by_cases hjq : j = q
  · simp [hjq] at hjv
  · simp only [if_neg hjq, MvPolynomial.vars_X, Finset.mem_singleton] at hjv
    exact hv (hjv ▸ hj)

/-- The actual residual omits the private full-interval generator. -/
theorem full_not_mem_residual {n : ℕ} (q : ℕ+) (P : Profile n) :
    fullGenerator P ∉ (residual q P).vars :=
  not_mem_vars_erase q _ _ P.toBetaDiagram.largest_not_mem_residual

/-- The unsigned coefficient omits the private full-interval generator. -/
theorem full_not_mem_gapMonomial {n : ℕ} {P : Profile n} (hP : Thick P) :
    fullGenerator P ∉ (gapMonomial P).vars := by
  rw [← cornerPolynomial_eq_gapMonomial hP]
  exact P.toBetaDiagram.largest_not_mem_corner

/-- The actual gap content is the normalized gcd, not a supplied factorization. -/
noncomputable def content {n : ℕ} (q : ℕ+) (P : Profile n) : CompleteRing :=
  gcd (gapMonomial P) (residual q P)

/-- A chosen exact quotient is used only when divisibility has been proved. -/
noncomputable def exactQuotient (a b : CompleteRing) (h : a ∣ b) : CompleteRing :=
  Classical.choose h

theorem exactQuotient_spec (a b : CompleteRing) (h : a ∣ b) :
    b = a * exactQuotient a b h := Classical.choose_spec h

/-- The monomial part of the primitive coefficient. -/
noncomputable def primitiveCoefficient {n : ℕ} (q : ℕ+) (P : Profile n) : CompleteRing :=
  exactQuotient (content q P) (gapMonomial P) (gcd_dvd_left _ _)

/-- The constant part of the primitive factor. -/
noncomputable def primitiveConstant {n : ℕ} (q : ℕ+) (P : Profile n) : CompleteRing :=
  exactQuotient (content q P) (residual q P) (gcd_dvd_right _ _)

/-- The primitive factor with the determinant's own sign convention. -/
noncomputable def primitive {n : ℕ} (q : ℕ+) (P : Profile n) : CompleteRing :=
  (-1 : CompleteRing) ^ n * primitiveCoefficient q P *
    MvPolynomial.X (fullGenerator P) + primitiveConstant q P

/-- Sign normalization makes the highest coefficient an unsigned monomial. -/
noncomputable def normalizedPrimitive {n : ℕ} (q : ℕ+) (P : Profile n) : CompleteRing :=
  (-1 : CompleteRing) ^ n * primitive q P

theorem gap_content_mul_coefficient {n : ℕ} (q : ℕ+) (P : Profile n) :
    gapMonomial P = content q P * primitiveCoefficient q P :=
  exactQuotient_spec _ _ _

theorem residual_content_mul_constant {n : ℕ} (q : ℕ+) (P : Profile n) :
    residual q P = content q P * primitiveConstant q P :=
  exactQuotient_spec _ _ _

/-- The exact actual-polydeterminant factorization. -/
theorem restriction_eq_content_mul_primitive {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : restriction q P = content q P * primitive q P := by
  rw [restriction_affine hP, gap_content_mul_coefficient q P,
    residual_content_mul_constant q P]
  unfold primitive
  ring

theorem content_ne_zero {n : ℕ} (q : ℕ+) (P : Profile n) : content q P ≠ 0 := by
  intro hz
  have hd := gap_content_mul_coefficient q P
  exact gapMonomial_ne_zero P (by simpa [hz] using hd)

theorem primitiveCoefficient_ne_zero {n : ℕ} (q : ℕ+) (P : Profile n) :
    primitiveCoefficient q P ≠ 0 := by
  intro hz
  have hd := gap_content_mul_coefficient q P
  exact gapMonomial_ne_zero P (by simpa [hz] using hd)

/-- Gcd extraction proves, rather than assumes, primitivity of the affine pair. -/
theorem primitive_pair_relPrime {n : ℕ} (q : ℕ+) (P : Profile n) :
    IsRelPrime (primitiveCoefficient q P) (primitiveConstant q P) := by
  apply gcd_isUnit_iff_isRelPrime.mp
  exact isUnit_gcd_of_eq_mul_gcd (gap_content_mul_coefficient q P)
    (residual_content_mul_constant q P) (content_ne_zero q P)

/-- The affine primitive is irreducible over the actual free complete-generator ring. -/
theorem primitive_irreducible {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : Irreducible (primitive q P) := by
  classical
  have ha := primitiveCoefficient_ne_zero q P
  have hs : (-1 : CompleteRing) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hvc : fullGenerator P ∉ (primitiveCoefficient q P).vars :=
    not_mem_vars_of_dvd (gapMonomial_ne_zero P)
      ⟨content q P, by rw [gap_content_mul_coefficient q P]; ring⟩ _
      (full_not_mem_gapMonomial hP.thick)
  have hvb : fullGenerator P ∉ (primitiveConstant q P).vars := by
    by_cases hb : residual q P = 0
    · have hc := residual_content_mul_constant q P
      have hz : primitiveConstant q P = 0 :=
        (mul_eq_zero.mp (hc.symm.trans hb)).resolve_left (content_ne_zero q P)
      simp [hz]
    · exact not_mem_vars_of_dvd hb
        ⟨content q P, by rw [residual_content_mul_constant q P]; ring⟩ _
        (full_not_mem_residual q P)
  have hvcSigned : fullGenerator P ∉
      ((-1 : CompleteRing) ^ n * primitiveCoefficient q P).vars := by
    intro hv
    have hu := MvPolynomial.vars_mul ((-1 : CompleteRing) ^ n)
      (primitiveCoefficient q P) hv
    have hvars : (((-1 : CompleteRing) ^ n)).vars = ∅ := by
      have he : (-1 : CompleteRing) ^ n = MvPolynomial.C ((-1 : ℚ) ^ n) := by simp
      rw [he, MvPolynomial.vars_C]
    simpa [hvars, hvc] using hu
  have hcopSigned : IsRelPrime ((-1 : CompleteRing) ^ n * primitiveCoefficient q P)
      (primitiveConstant q P) := by
    intro d hd hb
    have hda : d ∣ primitiveCoefficient q P := by
      have hu : IsUnit ((-1 : CompleteRing) ^ n) := isUnit_neg_one.pow n
      exact (hu.dvd_mul_left).mp hd
    exact primitive_pair_relPrime q P hda hb
  exact MvPolynomial.irreducible_mul_X_add _ _ _ (mul_ne_zero hs ha)
    hvcSigned hvb hcopSigned

/-- Every actual component restriction in the arithmetic domain is nonzero. -/
theorem restriction_ne_zero {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : restriction q P ≠ 0 := by
  rw [restriction_eq_content_mul_primitive hP]
  exact mul_ne_zero (content_ne_zero q P) (primitive_irreducible hP).ne_zero

/-- An additional seam specialization preserves a component whenever its
internal gaps and full interval avoid the additional erased index. -/
theorem erase_restriction_ne_zero {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (v : ℕ+)
    (hgap : ∀ j, P.g j ≠ v.val) (hfull : fullGenerator P ≠ v) :
    eraseGenerator v (restriction q P) ≠ 0 := by
  classical
  have hfix : eraseGenerator v (gapMonomial P) = gapMonomial P := by
    simp only [gapMonomial, map_prod, eraseGenerator_complete]
    apply Finset.prod_congr rfl
    intro j _
    rw [if_neg]
    exact_mod_cast hgap j
  have haff : eraseGenerator v (restriction q P) =
      (-1 : CompleteRing) ^ n * gapMonomial P * MvPolynomial.X (fullGenerator P) +
        eraseGenerator v (residual q P) := by
    have hvX : eraseGenerator v (MvPolynomial.X (fullGenerator P)) =
        MvPolynomial.X (fullGenerator P) := by
      simp only [eraseGenerator, MvPolynomial.eval₂Hom_X', if_neg hfull]
    rw [restriction_affine hP]
    simp only [map_add, map_mul, map_pow, map_neg, map_one, hfix, hvX]
  have hc : MvPolynomial.pderiv (fullGenerator P) (gapMonomial P) = 0 :=
    MvPolynomial.pderiv_eq_zero_of_notMem_vars (full_not_mem_gapMonomial hP.thick)
  have hb : MvPolynomial.pderiv (fullGenerator P)
      (eraseGenerator v (residual q P)) = 0 :=
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (not_mem_vars_erase v _ _ (full_not_mem_residual q P))
  have hs : (-1 : CompleteRing) ^ n = MvPolynomial.C ((-1 : ℚ) ^ n) := by simp
  have hsDeriv : MvPolynomial.pderiv (fullGenerator P) ((-1 : CompleteRing) ^ n) = 0 := by
    rw [hs]
    exact MvPolynomial.pderiv_C
  have hd : MvPolynomial.pderiv (fullGenerator P)
      (eraseGenerator v (restriction q P)) = (-1 : CompleteRing) ^ n * gapMonomial P := by
    rw [haff]
    simp only [map_add, MvPolynomial.pderiv_mul, hsDeriv, hc, hb,
      MvPolynomial.pderiv_X_self, zero_mul, mul_zero, zero_add, add_zero, mul_one]
  intro hz
  rw [hz, map_zero] at hd
  exact (mul_ne_zero (pow_ne_zero n (by norm_num)) (gapMonomial_ne_zero P)) hd.symm

/-- Exact division also preserves omission of the largest variable in the
zero-residual case. -/
theorem full_not_mem_primitiveConstant {n : ℕ} (q : ℕ+) (P : Profile n) :
    fullGenerator P ∉ (primitiveConstant q P).vars := by
  by_cases hb : residual q P = 0
  · have hc := residual_content_mul_constant q P
    have hz : primitiveConstant q P = 0 :=
      (mul_eq_zero.mp (hc.symm.trans hb)).resolve_left (content_ne_zero q P)
    simp [hz]
  · exact not_mem_vars_of_dvd hb
      ⟨content q P, by rw [residual_content_mul_constant q P]; ring⟩ _
      (full_not_mem_residual q P)

/-- No variable of the actual full determinant lies above its full interval. -/
theorem not_mem_schur_above_full {n : ℕ} (P : Profile n) (v : ℕ+)
    (hv : fullIndex P < (v.val : ℤ)) : v ∉ P.toBetaDiagram.schur.vars := by
  apply not_mem_vars_det
  intro i j
  change v ∉ (complete (P.xi i - P.zeta j)).vars
  rw [mem_vars_complete_iff]
  have hr : P.xi i ≤ P.xi 0 := P.xi_strictAnti.antitone (Fin.zero_le i)
  have hc : P.zeta (Fin.last n) ≤ P.zeta j :=
    P.zeta_strictAnti.antitone (Fin.le_last j)
  change P.xi 0 - P.zeta (Fin.last n) < (v.val : ℤ) at hv
  omega

/-- No variable above the full interval is introduced by restriction. -/
theorem not_mem_restriction_above_full {n : ℕ} (q : ℕ+) (P : Profile n) (v : ℕ+)
    (hv : fullIndex P < (v.val : ℤ)) : v ∉ (restriction q P).vars :=
  not_mem_vars_erase q v _ (not_mem_schur_above_full P v hv)

end SkewJacobiNegative.Staircase
