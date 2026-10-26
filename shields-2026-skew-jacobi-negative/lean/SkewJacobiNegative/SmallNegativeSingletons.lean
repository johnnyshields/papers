/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.LowNegativePatterns

/-!
# Singleton parents with at most two core negatives

The complete arbitrary-order assertion of `cor:singleton-two-negatives`,
including the dense and one-negative instances of `lem:singleton-rigidity`.
-/

namespace SkewJacobiNegative.BetaDiagram

/-- `cor:singleton-two-negatives`: every fixed-leader input is supplied from
connectedness, zero-freeness, and the actual core count. -/
theorem singletonContext_rotationRigid_of_two_negative {n : ℕ}
    (Q : BetaDiagram (n + 2)) (hQ : Q.Connected) (hZ : Q.ZeroFree)
    (hCount : negativeCount Q ≤ 2)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).RotationRigid := by
  apply Q.singletonContext_rotationRigid hQ hZ (Q.two_negative_rigidity hQ hCount)
    ?_ s u v g hs hu hv hg
  intro hS
  cases n with
  | zero => exact Q.endpointLeader_two hS
  | succ n =>
    cases n with
    | zero =>
      have h0 := Q.connected_negativeRowCount_le hQ (0 : Fin 3)
      have h1 := Q.connected_negativeRowCount_le hQ (1 : Fin 3)
      have h2 := Q.connected_negativeRowCount_le hQ (2 : Fin 3)
      have hSum : negativeCount Q = negativeRowCount Q 0 +
          negativeRowCount Q 1 + negativeRowCount Q 2 := by
        simp [negativeCount_eq_sum, Fin.sum_univ_succ, add_assoc]
      have hBound : negativeCount Q ≤ 1 := by norm_num at h0 h1 h2; omega
      by_cases hz : negativeCount Q = 0
      · have hDense : Q.Dense := by
          intro i j
          have hn : ¬ Q.row i < Q.col j := by
            intro h
            have hm : (i,j) ∈ negativeSites Q := by simp [negativeSites, h]
            have hp := Finset.card_pos.mpr ⟨(i,j),hm⟩
            change 0 < negativeCount Q at hp
            omega
          exact lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hZ i j))
        exact Q.endpointLeader_dense hDense hS
      · exact Q.endpointLeader_one_negative_three hQ hZ (by omega) hS
    | succ n => exact Q.endpointLeader_two_negative_ge_four hQ hZ hCount hS

/-- `lem:singleton-rigidity` for the one-negative cores; the same argument
also covers every larger core with exactly one negative. -/
theorem singletonContext_rotationRigid_of_one_negative {n : ℕ}
    (Q : BetaDiagram (n + 2)) (hQ : Q.Connected) (hZ : Q.ZeroFree)
    (hCount : negativeCount Q = 1)
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).RotationRigid :=
  Q.singletonContext_rotationRigid_of_two_negative hQ hZ (by omega)
    s u v g hs hu hv hg

end SkewJacobiNegative.BetaDiagram
