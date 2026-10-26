import SkewGluing.Aligned.CaseD.Rot1

/-!
# Aligned marks, case (d): the profile of a rotated diagram

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, case (c) "by rotation").

Rotating a connected diagram `D` reverses its profile:
`profM (rotate D) K = profM D (-K)`, `profS (rotate D) K = profS D (1 - K)`, and
`profIL (rotate D) k = profIL D (2 - k)`.  The term
`alD_CT` of the nested count is compatible: `CT_{rotate C}(-e, 1 - J) = CT_C(e, J)`
(`alD_CT_rotate`).

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {D : Diagram}

theorem alD_profM_rotate (hD : IsConnectedSkew D) (K : ℤ) :
    profM (SkewGluing.rotate D) K = profM D (-K) := by
  have hne := hD.2.1
  have h1 := minContent_rotate hne
  have h2 := maxContent_rotate hne
  by_cases h : minContent D ≤ -K ∧ -K ≤ maxContent D
  · have h' : minContent (SkewGluing.rotate D) ≤ K ∧
        K ≤ maxContent (SkewGluing.rotate D) := by omega
    rw [aligned_profM_eq h', aligned_profM_eq h, diagHi_rotate]
    have := diagLo_rotate (D := D) (-K)
    rw [neg_neg] at this
    rw [this]
    ring
  · have h' : ¬ (minContent (SkewGluing.rotate D) ≤ K ∧
        K ≤ maxContent (SkewGluing.rotate D)) := by omega
    rw [aligned_profM_eq_zero h', aligned_profM_eq_zero h]

theorem alD_profS_rotate (hD : IsConnectedSkew D) (K : ℤ) :
    profS (SkewGluing.rotate D) K = profS D (1 - K) := by
  have hne := hD.2.1
  have h1 := minContent_rotate hne
  have h2 := maxContent_rotate hne
  by_cases h : minContent D + 1 ≤ 1 - K ∧ 1 - K ≤ maxContent D
  · have h' : minContent (SkewGluing.rotate D) + 1 ≤ K ∧
        K ≤ maxContent (SkewGluing.rotate D) := by omega
    rw [aligned_profS_eq h', aligned_profS_eq h, diagHi_rotate]
    have e1 := diagLo_rotate (D := D) (-K)
    rw [neg_neg] at e1
    have e2 := diagLo_rotate (D := D) (-(K - 1))
    have i1 : 1 - K - 1 = -K := by ring
    rw [i1, e1]
    have e3 : -(K - 1) = 1 - K := by ring
    rw [e3]
    ring
  · have h' : ¬ (minContent (SkewGluing.rotate D) + 1 ≤ K ∧
        K ≤ maxContent (SkewGluing.rotate D)) := by omega
    rw [aligned_profS_eq_one h', aligned_profS_eq_one h]

theorem alD_profIL_rotate (hD : IsConnectedSkew D) (k : ℤ) :
    profIL (SkewGluing.rotate D) k = profIL D (2 - k) := by
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    have e : 2 - 2 * n = 2 * (1 - n) := by ring
    rw [e, profIL_even, profIL_even, alD_profS_rotate hD]
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    have e : 2 - (2 * n + 1) = 2 * (-n) + 1 := by ring
    rw [e, profIL_odd, profIL_odd, alD_profM_rotate hD]

theorem alD_CT_rotate (hC : IsConnectedSkew D) {e : ℤ} (he : -1 ≤ e ∧ e ≤ 1) (J : ℤ) :
    alD_CT (SkewGluing.rotate D) (-e) (1 - J) = alD_CT D e J := by
  unfold alD_CT
  obtain rfl | rfl | rfl : e = -1 ∨ e = 0 ∨ e = 1 := by omega
  · simp only [neg_neg, show ¬ ((1 : ℤ) = -1) by omega, show ¬ ((1 : ℤ) = 0) by omega,
      ite_false, ite_true]
    rw [alD_profM_rotate hC]
    congr 1
    ring
  · simp only [neg_zero, ite_true, show ¬ ((0 : ℤ) = -1) by omega]
    rw [alD_profS_rotate hC]
    simp
  · simp only [ite_true, show ¬ ((1 : ℤ) = -1) by omega,
      show ¬ ((1 : ℤ) = 0) by omega, ite_false]
    rw [alD_profM_rotate hC]
    congr 1
    ring

end MarkedInner

end SkewGluing
