/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.DistinguishedCutReassembly
import SkewClassInflation.DistinguishedPrefixContraction
import SkewClassInflation.ZeroJoinRecurrence

/-!
# Peeling the first actual distinguished seam

The finite first-seam and constant-coefficient producers for
`lem:total-contraction-inverse` of `shields-2026-skew-class-inflation.tex`.
The prefix has no distinguished generator because every possible occurrence
would be one of its excluded actual seams.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Staircase SkewJacobiNegative.GeneralHessenberg

/-- A profile with no distinguished seam is unchanged by the actual total contraction. -/
theorem contractAllMinimum_self {n : ℕ} (P : Profile n) (v : ℕ+) (hg : ∀ j, P.g j ≠ v.val) :
    contractAllMinimum P v = ⟨n, P⟩ := by
  cases n with
  | zero => rfl
  | succ n =>
    have hn : ¬ ∃ c : Fin (n + 1), P.g c = v.val := by
      rintro ⟨c, hc⟩
      exact hg c hc
    simp only [contractAllMinimum, dite_eq_right hn]

/-- A nonempty set of distinguished seams has an actual first index. -/
theorem exists_first_distinguished {n : ℕ} (P : Profile n) (v : ℕ+)
    (hv : ∃ j, P.g j = v.val) :
    ∃ c : Fin n, P.g c = v.val ∧ ∀ j : Fin n, j < c → P.g j ≠ v.val := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => P.g j = v.val)
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hv
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  refine ⟨S.min' hS, (Finset.mem_filter.mp (S.min'_mem hS)).2, ?_⟩
  intro j hj he
  have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  exact (not_le_of_gt hj) (S.min'_le j hjS)

/-- No distinguished generator occurs when the strict row bounds and actual gap exclusions hold. -/
theorem distinguished_not_mem_of_gap_ne {n : ℕ} (P : Profile n) (v : ℕ+) (hP : Thick P)
    (hr : ∀ i, v.val < P.r i) (hg : ∀ j, P.g j ≠ v.val) :
    v ∉ P.toBetaDiagram.schur.vars := by
  apply not_mem_vars_det
  intro i j
  change v ∉ (complete (P.xi i - P.zeta j)).vars
  rw [mem_vars_complete_iff]
  intro he
  obtain ⟨s, _, _, hs⟩ := (distinguished_index_iff_seam P hP v hr i j).mp he.symm
  exact hg s hs

/-- Erasing the actual joining generator cuts off an unchanged nondistinguished prefix. -/
theorem distinguished_join_constant {n m : ℕ} (L : Profile n) (R : Profile m) (v : ℕ+)
    (hL : Thick L) (hrL : ∀ i, v.val < L.r i) (hrR : ∀ i, v.val < R.r i)
    (hgL : ∀ j, L.g j ≠ v.val)
    (hJ : Thick (Profile.join L R v.val (hrL _) (hrR _))) :
    eraseGenerator v (Profile.join L R v.val (hrL _) (hrR _)).toBetaDiagram.schur =
      L.toBetaDiagram.schur * eraseGenerator v R.toBetaDiagram.schur := by
  have hd : eraseGenerator v (complete v.val) = 0 := by
    rw [eraseGenerator_complete]
    rw [ite_eq_left rfl]
  rw [Profile.join_schur L R v.val (hrL _) (hrR _) hJ, map_sub, map_mul, map_mul, hd,
    zero_mul, sub_zero, eraseGenerator_eq_self _ _
      (distinguished_not_mem_of_gap_ne L v hL hrL hgL)]

end SkewClassInflation
