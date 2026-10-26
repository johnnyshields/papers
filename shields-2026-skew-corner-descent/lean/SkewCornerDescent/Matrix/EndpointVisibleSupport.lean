/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.EndpointProfiles

/-!
# Recovering the visible literal support of an endpoint profile

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Positive
distinct original endpoint distances with nonzero full contraction coefficients
are recovered from the coefficients in any specified visibility window. The unit
at degree zero is kept separate, and no natural subtraction is truncated.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- The literal coefficient of the complete endpoint profile. -/
theorem endpointProfile_coeff {ι K : Type*} [Fintype ι] [CommRing K]
    (distance : ι → ℤ) (v : ι → K) (z : ℤ) :
    (endpointProfile distance v).coeff z =
      (if (0 : ℤ) = z then 1 else 0) - ∑ i, if distance i = z then v i else 0 := by
  classical
  simp only [endpointProfile, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- At one positive distinct original distance the coefficient is the negative
of its complete inverse contraction coefficient. -/
theorem endpointProfile_coeff_at_index {ι K : Type*} [Fintype ι] [CommRing K]
    (distance : ι → ℤ) (hindex : Function.Injective distance) (v : ι → K)
    (i : ι) (hi : 0 < distance i) : (endpointProfile distance v).coeff (distance i) = -v i := by
  classical
  rw [endpointProfile_coeff, ite_eq_right (by omega : (0 : ℤ) ≠ distance i)]
  have hsum : (∑ j, if distance j = distance i then v j else 0) = v i := by
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl]
    · intro j _ hji
      rw [ite_eq_right (fun h => hji (hindex h))]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [hsum, zero_sub]

/-- A positive absent original distance has zero coefficient, not the constant unit. -/
theorem endpointProfile_coeff_absent {ι K : Type*} [Fintype ι] [CommRing K]
    (distance : ι → ℤ) (v : ι → K) (z : ℤ) (hz : 0 < z)
    (habsent : ∀ i, distance i ≠ z) : (endpointProfile distance v).coeff z = 0 := by
  classical
  rw [endpointProfile_coeff, ite_eq_right (by omega : (0 : ℤ) ≠ z)]
  have hsum : (∑ i, if distance i = z then v i else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => ite_eq_right (habsent i)
  rw [hsum, sub_self]

/-- Equality of all visible coefficients recovers every visible original
endpoint distance. Coefficients may be dependent functions in any commutative
coefficient ring; only their genuine nonvanishing is used. -/
theorem endpointProfile_visible_support_eq {ι κ K : Type*}
    [Fintype ι] [Fintype κ] [CommRing K]
    (left : ι → ℤ) (right : κ → ℤ) (hleft : Function.Injective left)
    (hright : Function.Injective right) (a : ι → K) (b : κ → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (hleftpos : ∀ i, 0 < left i) (hrightpos : ∀ j, 0 < right j)
    (visible : ℤ → Prop) [DecidablePred visible]
    (hcoeff : ∀ z, 0 ≤ z → visible z →
      (endpointProfile left a).coeff z = (endpointProfile right b).coeff z) :
    (Finset.univ.filter fun i => visible (left i)).image left =
      (Finset.univ.filter fun j => visible (right j)).image right := by
  classical
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hv := (Finset.mem_filter.mp hi).2
    by_contra hnot
    have habsent : ∀ j, right j ≠ left i := by
      intro j he
      apply hnot
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm ▸ hv⟩, he⟩
    have heq := hcoeff (left i) (hleftpos i).le hv
    rw [endpointProfile_coeff_at_index left hleft a i (hleftpos i),
      endpointProfile_coeff_absent right b (left i) (hleftpos i) habsent] at heq
    exact ha i (neg_eq_zero.mp heq)
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have hv := (Finset.mem_filter.mp hj).2
    by_contra hnot
    have habsent : ∀ i, left i ≠ right j := by
      intro i he
      apply hnot
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm ▸ hv⟩, he⟩
    have heq := (hcoeff (right j) (hrightpos j).le hv).symm
    rw [endpointProfile_coeff_at_index right hright b j (hrightpos j),
      endpointProfile_coeff_absent left a (right j) (hrightpos j) habsent] at heq
    exact hb j (neg_eq_zero.mp heq)

end SkewCornerDescent.Matrix
