/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroCutReassembly
import SkewClassInflation.ZeroPrefixContraction
import SkewClassInflation.UnitCutCoefficients

/-!
# The first zero seam and its zero-free prefix

The positional peeling step for `thm:two-row-thin-class` in
`shields-2026-skew-class-inflation.tex`.  The first cut is selected from
the actual gap positions.  Its prefix has no zero gaps, and profiles
with no zero gaps are unchanged by total zero contraction.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Gluing
open SkewJacobiNegative.GeneralHessenberg

/-- Without a zero gap, the recursive total contraction is literally the identity. -/
theorem contractAllZeros_self {n : ℕ} (P : Profile n) (hg : ∀ j, 0 < P.g j) :
    contractAllZeros P = ⟨n, P⟩ := by
  cases n with
  | zero => rfl
  | succ n =>
    have hn : ¬ ∃ c : Fin (n + 1), (P.lift rowShiftTwoOne).g c = (1 : ℕ+).val := by
      rintro ⟨c, hc⟩
      have hp := hg c
      change 2 * P.g c + 1 = 1 at hc
      omega
    simp only [contractAllZeros, dite_eq_right hn]

/-- A nonempty zero-gap set has an actual first position, with every earlier gap positive. -/
theorem exists_first_zero {n : ℕ} (P : Profile n) (hz : ∃ j, P.g j = 0) :
    ∃ c : Fin n, P.g c = 0 ∧ ∀ j : Fin n, j < c → 0 < P.g j := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => P.g j = 0)
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hz
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  refine ⟨S.min' hS, (Finset.mem_filter.mp (S.min'_mem hS)).2, ?_⟩
  intro j hj
  by_contra hn
  have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  exact (not_le_of_gt hj) (S.min'_le j hjS)

/-- The prefix before the first zero seam is thick and has no unit entries. -/
theorem first_zero_prefix_zeroFree {n : ℕ} (P : Profile (n + 1))
    (hP : Staircase.Thick P) (c : Fin (n + 1))
    (hc : ∀ j : Fin (n + 1), j < c → 0 < P.g j) :
    (leftOfSeam P c).toBetaDiagram.ZeroFree := by
  apply thick_positive_gaps_zeroFree _ (slice_thick hP 0 c.val (by omega))
  intro j
  change 0 < P.g ⟨0 + j.val, by have := j.isLt; omega⟩
  apply hc
  change 0 + j.val < c.val
  have := j.isLt
  omega

end SkewClassInflation
