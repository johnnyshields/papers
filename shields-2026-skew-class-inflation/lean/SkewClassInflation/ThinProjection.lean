/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinPowerBetas

/-!
# A section on the actual thin-power generators

The specialization used for the faithful substitution in
`eq:thin-substitution` of `shields-2026-skew-class-inflation.tex`.
The inner gap generator maps to one, positive multiples of the block
span retain independent signed generators, and all other generators
map to zero.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- An explicit complete-generator specialization, with the gap unit retained. -/
noncomputable def projection : CompleteRing →ₐ[ℚ] CompleteRing :=
  MvPolynomial.aeval fun j : ℕ+ =>
    if j.val = B.c then 1 else
    if h : B.boundary.q ∣ j.val then
      (-1 : CompleteRing) ^ (j.val / B.boundary.q) *
        MvPolynomial.X ⟨j.val / B.boundary.q,
          Nat.div_pos (Nat.le_of_dvd j.pos h)
            (by have := B.boundary.p_pos; have := B.boundary.ap_lt_q; omega)⟩
    else 0

/-- Residue classes strictly between zero and the block span vanish, except the gap itself. -/
theorem projection_residue (r : ℕ) (hr : 0 < r) (hrq : r < B.boundary.q) (z : ℤ) :
    B.projection (complete ((r : ℤ) + z * B.boundary.q)) =
      if r = B.c ∧ z = 0 then 1 else 0 := by
  have hq : 0 < B.boundary.q := by have := B.boundary.ap_lt_q; omega
  have hcm : B.c < B.boundary.q := by
    have := B.boundary_q_eq
    have := B.c_lt_a
    have := B.a_lt_b
    omega
  have hkmod : ((r : ℤ) + z * B.boundary.q) % B.boundary.q = r := by
    rw [mul_comm z, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by omega)]
  by_cases hk : 0 < (r : ℤ) + z * B.boundary.q
  · let j : ℕ+ := ⟨((r : ℤ) + z * B.boundary.q).toNat, by omega⟩
    have hj : (j.val : ℤ) = (r : ℤ) + z * B.boundary.q := by dsimp [j]; omega
    have hnot : ¬ B.boundary.q ∣ j.val := by
      intro hd
      have hd' : (B.boundary.q : ℤ) ∣ (j.val : ℤ) := by exact_mod_cast hd
      have hh := Int.emod_eq_zero_of_dvd hd'
      rw [hj, hkmod] at hh
      omega
    have hiff : j.val = B.c ↔ r = B.c ∧ z = 0 := by
      constructor
      · intro he
        have he' : (r : ℤ) + z * B.boundary.q = B.c := by omega
        have hh := congrArg (fun x : ℤ => x % B.boundary.q) he'
        rw [hkmod, Int.emod_eq_of_lt (by omega) (by omega)] at hh
        have heq : r = B.c := by omega
        refine ⟨heq, ?_⟩
        have hz : z * B.boundary.q = 0 := by omega
        exact (mul_eq_zero.mp hz).resolve_right (by omega)
      · rintro ⟨rfl, rfl⟩
        omega
    have he : complete ((r : ℤ) + z * B.boundary.q) = MvPolynomial.X j :=
      complete_of_pos hk
    rw [he, projection, MvPolynomial.aeval_X]
    simp only [dite_eq_right hnot, hiff]
  · have hne : (r : ℤ) + z * B.boundary.q ≠ 0 := by
      intro he
      rw [he, Int.zero_emod] at hkmod
      omega
    rw [complete_of_neg (by omega), map_zero]
    have hn : ¬ (r = B.c ∧ z = 0) := by rintro ⟨_, rfl⟩; omega
    rw [ite_eq_right hn]

/-- Every positive block-span multiple retains its own independent signed generator. -/
theorem projection_multiple (m : ℕ) (hm : 0 < m) :
    B.projection (complete ((m : ℤ) * B.boundary.q)) =
      (-1 : CompleteRing) ^ m * MvPolynomial.X (⟨m, hm⟩ : ℕ+) := by
  have hq : 0 < B.boundary.q := by
    have := B.boundary.p_pos
    have := B.boundary.ap_lt_q
    omega
  have hcm : B.c < B.boundary.q := by
    have := B.boundary_q_eq
    have := B.c_lt_a
    have := B.a_lt_b
    omega
  have hk : 0 < (m : ℤ) * B.boundary.q := mul_pos (by omega) (by omega)
  let j : ℕ+ := ⟨m * B.boundary.q, Nat.mul_pos hm hq⟩
  have he : complete ((m : ℤ) * B.boundary.q) = MvPolynomial.X j := by
    have hj : ((m : ℤ) * B.boundary.q).toNat = m * B.boundary.q := by
      rw [← Nat.cast_mul, Int.toNat_natCast]
    simpa only [hj] using (complete_of_pos hk)
  have hjc : j.val ≠ B.c := by
    have hle : B.boundary.q ≤ m * B.boundary.q :=
      le_mul_of_one_le_left (by omega) (by omega)
    dsimp [j]
    omega
  rw [he, projection, MvPolynomial.aeval_X, ite_eq_right hjc,
    dite_eq_left (show B.boundary.q ∣ j.val from ⟨m, Nat.mul_comm _ _⟩)]
  simp only [j, Nat.mul_div_cancel _ hq, PNat.mk_coe]
  rfl

end SkewClassInflation.ThinParameters
