-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/CSign/Parity.lean
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Basic
import GluingCore.Tactics

/-!
# The parity bookkeeping of the lifted heights

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`): the congruences between the height of a lifted strip and the
heights and northbound counts of the outer in thesis Lemma 5.5.11
(`OlsonHarris2024HopfApplications`), as statements about the first rows `L` and last rows `H` of
the diagonals of a connected skew outer with contents `[μ, M]`, whose end diagonals are
singletons.  Here `S_x = H_{x-1} - L_x + 1` for `μ < x ≤ M` and `S_x = 1` otherwise is the
quantity `profS`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace CSign

/-- The sign `(-1)^a` as a product of signs, when the exponents agree modulo two. -/
theorem neg_one_pow_eq_parity (a b c m : ℕ) (rs : ℤ)
    (h : ((a : ℤ) - m * rs - b - c) % 2 = 0) :
    (-1 : ℤ) ^ a = ((-1 : ℤ) ^ rs.natAbs) ^ m * (-1) ^ b * (-1) ^ c := by
  rw [← pow_mul, ← pow_add, ← pow_add, neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two (R := ℤ) (n := rs.natAbs * m + b + c)]
  congr 1
  have h2 : (m : ℤ) * rs = (m : ℤ) * (rs.natAbs : ℤ) ∨
      (m : ℤ) * rs = -((m : ℤ) * (rs.natAbs : ℤ)) := by
    rcases Int.natAbs_eq rs with h' | h'
    · left; rw [← h']
    · right; rw [← mul_neg, ← h']
  have e : ((rs.natAbs * m : ℕ) : ℤ) = (m : ℤ) * (rs.natAbs : ℤ) := by push_cast; ring
  omega

theorem sigma_cases (rs : ℤ) : ((-1 : ℤ) ^ rs.natAbs = 1) ∨ ((-1 : ℤ) ^ rs.natAbs = -1) := by
  rcases neg_one_pow_eq_or ℤ rs.natAbs with h | h <;> simp [h]

/-- Parity for a ribbon removable on the right: the window is `[u, v - 1]` with `v = u + m`. -/
theorem right_parity (H L : ℤ → ℤ) (μ M u v m rs Sj Sv : ℤ) (hv : v = u + m) (hm : 1 ≤ m)
    (hμu : μ ≤ u) (hvM : v ≤ M + 1) (hends : L μ = H μ ∧ L M = H M)
    (hB0 : u = μ ∨ H (u - 1) = H u) (hBm : v = M + 1 ∨ H (v - 1) - H v = 1)
    (hSj : Sj = if μ + 1 ≤ u ∧ u ≤ M then H (u - 1) - L u + 1 else 1)
    (hSv : Sv = if μ + 1 ≤ v ∧ v ≤ M then H (v - 1) - L v + 1 else 1) :
    ((-(m * rs) + Sj - Sv) - m * rs - (H u - H (v - 1)) - (L u - L (min v M))) % 2 = 0 := by
  obtain ⟨he1, he2⟩ := hends
  have hu : u = μ ∨ μ + 1 ≤ u := by omega
  have hv' : v = M + 1 ∨ v ≤ M := by omega
  rcases hu with rfl | hu <;> rcases hv' with hv' | hv'
  · have e : v - 1 = M := by omega
    have e2 : min v M = M := by omega
    rw [e, e2]
    split_ifs at hSj hSv <;> omega
  · have e2 : min v M = v := by omega
    rw [e2]
    split_ifs at hSj hSv <;> omega
  · have e : v - 1 = M := by omega
    have e2 : min v M = M := by omega
    rw [e, e2]
    split_ifs at hSj hSv <;> omega
  · have e2 : min v M = v := by omega
    rw [e2]
    split_ifs at hSj hSv <;> omega

/-- Parity for a ribbon removable on the left: the window is `[u, v - 1]` with `v = u + m`. -/
theorem left_parity (H L : ℤ → ℤ) (μ M u v m rs Sj Sv : ℤ) (hv : v = u + m) (hm : 1 ≤ m)
    (hμu : μ ≤ u) (hvM : v ≤ M + 1) (hends : L μ = H μ ∧ L M = H M)
    (hA0 : u = μ ∨ L (u - 1) - L u = 1) (hAm : v = M + 1 ∨ L (v - 1) = L v)
    (hSj : Sj = if μ + 1 ≤ u ∧ u ≤ M then H (u - 1) - L u + 1 else 1)
    (hSv : Sv = if μ + 1 ≤ v ∧ v ≤ M then H (v - 1) - L v + 1 else 1) :
    ((-(m * rs) + Sj - Sv - 1) - 1 - m * rs - (L u - L (v - 1)) -
      (H (max (u - 1) μ) - H (v - 1))) % 2 = 0 := by
  obtain ⟨he1, he2⟩ := hends
  have hu : u = μ ∨ μ + 1 ≤ u := by omega
  have hv' : v = M + 1 ∨ v ≤ M := by omega
  rcases hu with rfl | hu <;> rcases hv' with hv' | hv'
  · have e : v - 1 = M := by omega
    have e3 : max (u - 1) u = u := by omega
    rw [e, e3]
    rw [e] at hAm
    split_ifs at hSj hSv <;> omega
  · have e3 : max (u - 1) u = u := by omega
    rw [e3]
    split_ifs at hSj hSv <;> omega
  · have e : v - 1 = M := by omega
    have e3 : max (u - 1) μ = u - 1 := by omega
    rw [e, e3]
    rw [e] at hAm
    split_ifs at hSj hSv <;> omega
  · have e3 : max (u - 1) μ = u - 1 := by omega
    rw [e3]
    split_ifs at hSj hSv <;> omega

end CSign

end Corner

end Plan

end GluingCore
