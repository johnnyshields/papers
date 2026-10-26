/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.PlanePolynomial
import SkewCornerDescent.TriangularDivisors

/-!
# Plane numerators in the unchanged polynomial generators

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). The closure variable is an original
polynomial generator, and the lower corrections and cap product retain their full
polynomial dependence.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

variable {σ k : Type*} [LinearOrder σ] [Field k]

/-- Substitute the actual closure generator into the denominator-cleared numerator. -/
noncomputable def triangularPlanePolynomial (K : σ) (p : Polynomial k)
    (A F : MvPolynomial σ k) : MvPolynomial σ k :=
  (clearedPlanePolynomial p A F).eval (X K)

/-- The numerator uses no index above the actual closure top. -/
theorem triangularPlanePolynomial_vars {K : σ} (p : Polynomial k)
    {A F : MvPolynomial σ k} (hA : ∀ i ∈ A.vars, i < K) (hF : ∀ i ∈ F.vars, i < K) :
    ∀ i ∈ (triangularPlanePolynomial K p A F).vars, i ≤ K := by
  classical
  rw [triangularPlanePolynomial, clearedPlanePolynomial, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.scaleRoots, Polynomial.eval_finsetSum]
  intro i hi
  have hsum := vars_sum_subset
    (t := (p.map C).support)
    (φ := fun j => Polynomial.eval (X K + A)
      (Polynomial.monomial j ((p.map C).coeff j * F ^ ((p.map C).natDegree - j)))) hi
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hsum
  simp only [Polynomial.eval_monomial, Polynomial.coeff_map] at hij
  rcases Finset.mem_union.mp (vars_mul _ _ hij) with h | h
  · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
    · simp only [vars_C, Finset.notMem_empty] at h
    · exact (hF i (vars_pow _ _ h)).le
  · rcases Finset.mem_union.mp (vars_add_subset _ _ (vars_pow _ _ h)) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      exact h.le
    · exact (hA i h).le

omit [LinearOrder σ] in
/-- The canonical original-generator split identifies the whole plane numerator,
including its cap denominator powers and complete lower correction. -/
theorem triangularPlanePolynomial_split {R : Type*} [CommRing R] [IsDomain R] [Algebra k R]
    (e : MvPolynomial σ k ≃ₐ[k] Polynomial R) (K : σ) (p : Polynomial k)
    (A F : MvPolynomial σ k) (a f : R)
    (hX : e (X K) = Polynomial.X) (hA : e A = Polynomial.C a)
    (hF : e F = Polynomial.C f) :
    e (triangularPlanePolynomial K p A F) = clearedPlanePolynomial p a f := by
  classical
  have heC (c : k) : e (algebraMap k (MvPolynomial σ k) c) =
      Polynomial.C (algebraMap k R c) := e.commutes c
  rw [triangularPlanePolynomial, clearedPlanePolynomial, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.scaleRoots, Polynomial.eval_finsetSum, map_sum]
  rw [Polynomial.support_map_of_injective p (RingHom.injective _)]
  rw [clearedPlanePolynomial, Polynomial.comp, Polynomial.scaleRoots,
    Polynomial.eval₂_finsetSum]
  rw [Polynomial.support_map_of_injective p (RingHom.injective _)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.eval_monomial, Polynomial.coeff_map,
    Polynomial.natDegree_map, map_mul, map_pow, map_add, hX, hA, hF, heC,
    Polynomial.eval₂_monomial]

/-- Splitting at a protected top turns a strictly lower correction into a constant. -/
theorem triangularCorrection_split_constant {K : σ} {r : MvPolynomial σ k}
    (hr : ∀ i ∈ r.vars, i < K) :
    let e := (renameEquiv k (Equiv.optionSubtypeNe K).symm).trans (optionEquivLeft k _)
    e r = Polynomial.C ((e r).coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  change (optionEquivLeft k {i // i ≠ K}
    (rename (Equiv.optionSubtypeNe K).symm r)).natDegree = 0
  rw [← degreeOf_eq_natDegree]
  exact not_not.mp (mt mem_vars_iff_degreeOf_ne_zero.mpr
    (triangular_correction_notMem hr))

/-- Monicity in the actual closure generator is produced from the rational plane polynomial. -/
theorem triangularPlanePolynomial_split_monic {K : σ} {p : Polynomial k} (hp : p.Monic)
    {A F : MvPolynomial σ k} (hA : ∀ i ∈ A.vars, i < K) (hF : ∀ i ∈ F.vars, i < K) :
    (optionEquivLeft k {i // i ≠ K}
      (rename (Equiv.optionSubtypeNe K).symm (triangularPlanePolynomial K p A F))).Monic := by
  classical
  let e : MvPolynomial σ k ≃ₐ[k] Polynomial (MvPolynomial {i // i ≠ K} k) :=
    (renameEquiv k (Equiv.optionSubtypeNe K).symm).trans (optionEquivLeft k _)
  have hconst (r : MvPolynomial σ k) (hr : ∀ i ∈ r.vars, i < K) :
      e r = Polynomial.C ((e r).coeff 0) := triangularCorrection_split_constant hr
  change (e (triangularPlanePolynomial K p A F)).Monic
  rw [triangularPlanePolynomial_split e K p A F ((e A).coeff 0) ((e F).coeff 0)
    (by simp [e, optionEquivLeft_apply]) (hconst A hA) (hconst F hF)]
  exact clearedPlanePolynomial_monic hp _ _

/-- The numerator retains precisely the degree of the rational plane factor in the closure top. -/
theorem triangularPlanePolynomial_degreeOf {K : σ} {p : Polynomial k} (hp : p.Monic)
    {A F : MvPolynomial σ k} (hA : ∀ i ∈ A.vars, i < K)
    (hF : ∀ i ∈ F.vars, i < K) :
    (triangularPlanePolynomial K p A F).degreeOf K = p.natDegree := by
  classical
  let e : MvPolynomial σ k ≃ₐ[k] Polynomial (MvPolynomial {i // i ≠ K} k) :=
    (renameEquiv k (Equiv.optionSubtypeNe K).symm).trans (optionEquivLeft k _)
  rw [degreeOf_eq_natDegree]
  change (e (triangularPlanePolynomial K p A F)).natDegree = _
  rw [triangularPlanePolynomial_split e K p A F ((e A).coeff 0) ((e F).coeff 0)
    (by simp [e, optionEquivLeft_apply]) (triangularCorrection_split_constant hA)
    (triangularCorrection_split_constant hF)]
  exact clearedPlanePolynomial_natDegree hp _ _

/-- A positive-degree plane factor gives a nonzero nonunit cleared polynomial. -/
theorem triangularPlanePolynomial_nonunit {K : σ} {p : Polynomial k} (hp : p.Monic)
    (hdeg : 0 < p.natDegree) {A F : MvPolynomial σ k}
    (hA : ∀ i ∈ A.vars, i < K) (hF : ∀ i ∈ F.vars, i < K) :
    triangularPlanePolynomial K p A F ≠ 0 ∧
      ¬IsUnit (triangularPlanePolynomial K p A F) := by
  have he := triangularPlanePolynomial_degreeOf hp hA hF
  constructor
  · intro hz
    rw [hz, degreeOf_zero] at he
    omega
  · intro hu
    obtain ⟨c, _, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
    rw [hc, degreeOf_C] at he
    omega

/-- A monic triangular response dividing a genuine cleared plane numerator has the closure top.
Neither protected-top equality nor monicity of the numerator is assumed. -/
theorem triangularPlanePolynomial_divisor_top {K J : σ} {p : Polynomial k} (hp : p.Monic)
    {A F B : MvPolynomial σ k} (hA : ∀ i ∈ A.vars, i < K)
    (hF : ∀ i ∈ F.vars, i < K) (hB : ∀ i ∈ B.vars, i < J)
    (hd : X J + B ∣ triangularPlanePolynomial K p A F) : J = K :=
  monicTriangularPolynomial_dvd_top_eq hB (triangularPlanePolynomial_vars p hA hF)
    (triangularPlanePolynomial_split_monic hp hA hF) hd

omit [LinearOrder σ] in
/-- Evaluation transports the entire cleared numerator, not just its leading term. -/
theorem triangularPlanePolynomial_eval {E : Type*} [Field E] [Algebra k E]
    (g : MvPolynomial σ k →ₐ[k] E) (K : σ) {p : Polynomial k} (hp : p.Monic)
    (A F : MvPolynomial σ k) :
    g (triangularPlanePolynomial K p A F) =
      (clearedPlanePolynomial p (g A) (g F)).eval (g (X K)) := by
  change g.toRingHom ((clearedPlanePolynomial p A F).eval (X K)) = _
  rw [← Polynomial.eval₂_at_apply g.toRingHom,
    Polynomial.eval₂_eq_eval_map, clearedPlanePolynomial_map g hp]
  rfl

/-- A genuine triangular polynomial divisor produces a root after substituting its zero.
The substitution fixes every strictly lower correction. -/
theorem triangularPlanePolynomial_divisor_root {E : Type*} [Field E] [Algebra k E]
    (e : MvPolynomial σ k →ₐ[k] E) {K : σ} {p : Polynomial k} (hp : p.Monic)
    {A F B : MvPolynomial σ k} (hA : ∀ i ∈ A.vars, i < K)
    (hF : ∀ i ∈ F.vars, i < K) (hB : ∀ i ∈ B.vars, i < K)
    (hd : X K + B ∣ triangularPlanePolynomial K p A F) :
    (clearedPlanePolynomial p (e A) (e F)).eval (-e B) = 0 := by
  classical
  let g : MvPolynomial σ k →ₐ[k] E :=
    aeval (fun i => if i = K then -e B else e (X i))
  have hfix (r : MvPolynomial σ k) (hr : ∀ i ∈ r.vars, i < K) : g r = e r := by
    apply hom_congr_vars (f₁ := g.toRingHom) (f₂ := e.toRingHom) _ _ rfl
    · ext c
      exact (g.commutes c).trans (e.commutes c).symm
    · intro i hi _
      change (aeval (fun i => if i = K then -e B else e (X i))) (X i) = e (X i)
      simp only [aeval_X, ite_eq_right (ne_of_lt (hr i hi))]
  have hzero : g (X K + B) = 0 := by
    rw [map_add, hfix B hB]
    simp only [g, aeval_X, ite_true, neg_add_cancel]
  have h := map_dvd g.toRingHom hd
  change g (X K + B) ∣ g (triangularPlanePolynomial K p A F) at h
  rw [hzero, zero_dvd_iff] at h
  rw [triangularPlanePolynomial_eval g K hp A F, hfix A hA, hfix F hF] at h
  simpa only [g, aeval_X, ite_true] using h

end SkewCornerDescent
