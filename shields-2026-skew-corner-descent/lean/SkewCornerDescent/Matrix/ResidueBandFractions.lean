/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResiduePolynomialBand

/-!
# Lower-denominator representatives of the actual residue band

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Elements of the actual lower residue field are fractions of supported polynomials in the
surviving original generators. Polynomial-band elements retain strictly lower denominators.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance (N : ℕ+) : Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- Polynomial adjoin membership supplies a supported original polynomial, not a formal symbol. -/
theorem residue_adjoin_polynomial (N K : ℕ+) {x : OtherField N}
    (hx : x ∈ Algebra.adjoin ℚ
      (residueGenerator N '' {j : {j : ℕ+ // j ≠ N} | j.val < K})) :
    ∃ p ∈ supported ℚ {j : {j : ℕ+ // j ≠ N} | j.val < K},
      algebraMap (OtherPolynomial N) (OtherField N) p = x := by
  let S := supported ℚ {j : {j : ℕ+ // j ≠ N} | j.val < K}
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨X j, (X_mem_supported (R := ℚ)).mpr hj, rfl⟩
  | algebraMap q =>
    refine ⟨C q, S.algebraMap_mem q, ?_⟩
    exact IsScalarTower.algebraMap_apply ℚ (OtherPolynomial N) (OtherField N) q
  | add x y _ _ hx hy =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    exact ⟨p + q, S.add_mem hp hq, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    exact ⟨p * q, S.mul_mem hp hq, map_mul _ _ _⟩

/-- Every actual lower-field element has a nonzero denominator in lower surviving variables. -/
theorem residueLowerField_fraction (N K : ℕ+) {x : OtherField N}
    (hx : x ∈ residueLowerField N K) :
    ∃ p ∈ supported ℚ {j : {j : ℕ+ // j ≠ N} | j.val < K},
    ∃ q ∈ supported ℚ {j : {j : ℕ+ // j ≠ N} | j.val < K},
      q ≠ 0 ∧ x = algebraMap (OtherPolynomial N) (OtherField N) p /
        algebraMap (OtherPolynomial N) (OtherField N) q := by
  change x ∈ IntermediateField.adjoin ℚ
    (residueGenerator N '' {j : {j : ℕ+ // j ≠ N} | j.val < K}) at hx
  obtain ⟨a, ha, b, hb, he⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
  obtain ⟨p, hp, rfl⟩ := residue_adjoin_polynomial N K ha
  obtain ⟨q, hq, rfl⟩ := residue_adjoin_polynomial N K hb
  by_cases hq0 : q = 0
  · subst q
    refine ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, one_ne_zero, ?_⟩
    simpa only [map_zero, map_one, div_zero, zero_div] using he
  · exact ⟨p, hp, q, hq, hq0, he⟩

/-- Clearing a polynomial-band element never introduces higher-coordinate denominators. -/
theorem residuePolynomialBand_fraction (N K : ℕ+) (hNK : N ≤ K) {x : OtherField N}
    (hx : x ∈ residuePolynomialBand N K) :
    ∃ p ∈ supported ℚ {j : {j : ℕ+ // j ≠ N} | j.val < K},
    ∃ q ∈ supported ℚ {j : {j : ℕ+ // j ≠ N} | j.val < N},
      q ≠ 0 ∧ x = algebraMap (OtherPolynomial N) (OtherField N) p /
        algebraMap (OtherPolynomial N) (OtherField N) q := by
  let S := supported ℚ {j : {j : ℕ+ // j ≠ N} | j.val < K}
  let T := supported ℚ {j : {j : ℕ+ // j ≠ N} | j.val < N}
  have hTS : T ≤ S := supported_mono (fun j hj => lt_of_lt_of_le hj hNK)
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hlow | hhigh
    · obtain ⟨p, hp, q, hq, hq0, he⟩ := residueLowerField_fraction N N hlow
      exact ⟨p, hTS hp, q, hq, hq0, he⟩
    · obtain ⟨j, _, hjK, rfl⟩ := hhigh
      exact ⟨X j, (X_mem_supported (R := ℚ)).mpr hjK, 1, T.one_mem, one_ne_zero,
        by rw [map_one, div_one]; rfl⟩
  | algebraMap q =>
    refine ⟨C q, S.algebraMap_mem q, 1, T.one_mem, one_ne_zero, ?_⟩
    rw [map_one, div_one]
    exact (IsScalarTower.algebraMap_apply ℚ (OtherPolynomial N) (OtherField N) q).symm
  | add x y _ _ hx hy =>
    obtain ⟨p, hp, q, hq, hq0, rfl⟩ := hx
    obtain ⟨r, hr, s, hs, hs0, rfl⟩ := hy
    refine ⟨p * s + r * q, S.add_mem (S.mul_mem hp (hTS hs)) (S.mul_mem hr (hTS hq)),
      q * s, T.mul_mem hq hs, mul_ne_zero hq0 hs0, ?_⟩
    rw [map_add, map_mul, map_mul, map_mul]
    have hq' := (map_ne_zero_iff (algebraMap (OtherPolynomial N) (OtherField N))
      (IsFractionRing.injective _ _)).mpr hq0
    have hs' := (map_ne_zero_iff (algebraMap (OtherPolynomial N) (OtherField N))
      (IsFractionRing.injective _ _)).mpr hs0
    field_simp [hq', hs']
  | mul x y _ _ hx hy =>
    obtain ⟨p, hp, q, hq, hq0, rfl⟩ := hx
    obtain ⟨r, hr, s, hs, hs0, rfl⟩ := hy
    exact ⟨p * r, S.mul_mem hp hr, q * s, T.mul_mem hq hs, mul_ne_zero hq0 hs0,
      by rw [map_mul, map_mul, div_mul_div_comm]⟩

end SkewCornerDescent.Matrix
