/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.NonVMark

/-!
# Connected skew witnesses for both ordinary-mark deletions

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:non-v-family`). Both complete deletions have explicit actual
profile presentations for every `k ≥ 3`. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing
open scoped BigOperators

/-- Deleting the southwest marked column retains row lengths `(2,k-1,1)`. -/
def nonVLowerRemovalProfile (k : ℕ) (hk : 3 ≤ k) : Profile 2 where
  r := ![2, k - 1, 1]
  g := ![1, 0]
  r_pos := by intro i; fin_cases i <;> simp; all_goals omega
  g_lt_castSucc := by intro i; fin_cases i <;> simp; all_goals omega
  g_lt_succ := by intro i; fin_cases i <;> simp; all_goals omega

/-- Deleting the northeast marked column retains row lengths `(1,k-1,2)`. -/
def nonVUpperRemovalProfile (k : ℕ) (hk : 3 ≤ k) : Profile 2 where
  r := ![1, k - 1, 2]
  g := ![0, 1]
  r_pos := by intro i; fin_cases i <;> simp; all_goals omega
  g_lt_castSucc := by intro i; fin_cases i <;> simp; all_goals omega
  g_lt_succ := by intro i; fin_cases i <;> simp; all_goals omega

/-- The actual lower-deletion beta lists. -/
theorem nonVLowerRemoval_beta (k : ℕ) (hk : 3 ≤ k) :
    (nonVLowerRemovalProfile k hk).zeta = ![(k : ℤ) - 1, 1, 0] ∧
      (nonVLowerRemovalProfile k hk).xi = ![(k : ℤ) + 1, (k : ℤ), 1] := by
  constructor
  · funext i
    fin_cases i <;> simp [Profile.zeta, nonVLowerRemovalProfile, Fin.sum_univ_succ,
      Nat.cast_sub (by omega : 1 ≤ k)]
  · funext i
    fin_cases i <;> simp [Profile.xi, Profile.zeta, nonVLowerRemovalProfile,
      Fin.sum_univ_succ, Nat.cast_sub (by omega : 1 ≤ k)]
    all_goals ring

/-- The actual upper-deletion beta lists. -/
theorem nonVUpperRemoval_beta (k : ℕ) (hk : 3 ≤ k) :
    (nonVUpperRemovalProfile k hk).zeta = ![(k : ℤ), 1, 0] ∧
      (nonVUpperRemovalProfile k hk).xi = ![(k : ℤ) + 1, (k : ℤ), 2] := by
  constructor
  · funext i
    fin_cases i <;> simp [Profile.zeta, nonVUpperRemovalProfile, Fin.sum_univ_succ,
      Nat.cast_sub (by omega : 1 ≤ k)]
    all_goals ring
  · funext i
    fin_cases i <;> simp [Profile.xi, Profile.zeta, nonVUpperRemovalProfile,
      Fin.sum_univ_succ, Nat.cast_sub (by omega : 1 ≤ k)]
    all_goals ring

/-- The complete southwest deletion equals its literal translated profile. -/
theorem nonVMark_lowerRemoval (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).E \ (nonVMark k).W =
      translate (-2, -1) (nonVLowerRemovalProfile k hk).cells := by
  ext p
  obtain ⟨a, b⟩ := p
  change (a, b) ∈ nonVDiagram k \ {(-1, 0), (0, 0)} ↔ _
  rw [Finset.mem_sdiff, mem_translate]
  change _ ↔ (a + 2, b + 1) ∈ (nonVLowerRemovalProfile k hk).cells
  simp only [mem_nonVDiagram, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rw [Profile.mem_cells, (nonVLowerRemoval_beta k hk).1, (nonVLowerRemoval_beta k hk).2]
  constructor
  · intro h
    have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
    rcases h.1 with h0 | h1 | h2
    · refine ⟨2, ?_, ?_, ?_⟩ <;> simp <;> omega
    · refine ⟨1, ?_, ?_, ?_⟩ <;> simp <;> omega
    · refine ⟨0, ?_, ?_, ?_⟩ <;> simp <;> omega
  · rintro ⟨i, hi, hlo, hhi⟩
    fin_cases i <;> norm_num at hi hlo hhi <;> omega

/-- The complete northeast deletion equals its literal translated profile. -/
theorem nonVMark_upperRemoval (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).E \ (nonVMark k).upper =
      translate (-2, -2) (nonVUpperRemovalProfile k hk).cells := by
  rw [nonVMark_upper]
  ext p
  obtain ⟨a, b⟩ := p
  change (a, b) ∈ nonVDiagram k \
    {(-2, (k : ℤ) - 1), (-1, (k : ℤ) - 1)} ↔ _
  rw [Finset.mem_sdiff, mem_translate]
  change _ ↔ (a + 2, b + 2) ∈ (nonVUpperRemovalProfile k hk).cells
  simp only [mem_nonVDiagram, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rw [Profile.mem_cells, (nonVUpperRemoval_beta k hk).1, (nonVUpperRemoval_beta k hk).2]
  constructor
  · intro h
    have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
    rcases h.1 with h0 | h1 | h2
    · refine ⟨2, ?_, ?_, ?_⟩ <;> simp <;> omega
    · refine ⟨1, ?_, ?_, ?_⟩ <;> simp <;> omega
    · refine ⟨0, ?_, ?_, ?_⟩ <;> simp <;> omega
  · rintro ⟨i, hi, hlo, hhi⟩
    fin_cases i <;> norm_num at hi hlo hhi <;> omega

/-- Both genuine deletions are connected skew; neither is taken as a legality hypothesis. -/
theorem nonVMark_removalsConnected (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).RemovalsConnected := by
  unfold MarkedInner.RemovalsConnected
  rw [nonVMark_lowerRemoval k hk, nonVMark_upperRemoval k hk]
  exact ⟨isConnectedSkew_translate _ (nonVLowerRemovalProfile k hk).isConnectedSkew_cells,
    isConnectedSkew_translate _ (nonVUpperRemovalProfile k hk).isConnectedSkew_cells⟩

end SkewCornerDescent
