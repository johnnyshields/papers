/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundedEvenDiscrepancy

/-!
# Positive windows for actual initial even discrepancies

The cyclic-to-linear coordinate step in factor-reversal necessity for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
A wrapped discrepancy is read backwards using the reflected actual
undetermined cut.  No change of source weight or inventory is used.
Sorry-free.
-/

namespace SkewClassInflation

/-- Any actual initial discrepancy has a genuine nonwrapped positive two-endpoint window. -/
theorem undetermined_even_discrepancy_window {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty)
    (hD : (evenCutDisagreements α (undeterminedGcd α k) (undeterminedCuts α k)).Nonempty) :
    ∃ m ∈ undeterminedCuts α k, ∃ x : ℕ, 0 < x ∧ m + x < N ∧
      ¬ undeterminedGcd α k ∣ x ∧ compositionCutType α x ≠ 1 ∧
      compositionCutType α (m + x) ≠ 1 ∧
      compositionCutType α x ≠ compositionCutType α (m + x) := by
  classical
  obtain ⟨x, hx⟩ := hD
  obtain ⟨hx0, hxN, hnot⟩ := evenCutDisagreements_bounds α _ _ x hx
  obtain ⟨_, m, hm, heven, heven', hdiff⟩ := (Finset.mem_filter.mp hx).2
  have hmb := Finset.mem_Ioo.mp (Finset.mem_filter.mp hm).1
  have hdN := undeterminedGcd_dvd_weight α k hne
  have hdm := undeterminedGcd_dvd α k m hm
  have hneq : x + m ≠ N := by
    intro he
    apply hnot
    exact (Nat.dvd_add_iff_left hdm).mpr (he ▸ hdN)
  by_cases hlt : x + m < N
  · rw [Nat.mod_eq_of_lt hlt, Nat.add_comm x m] at heven' hdiff
    exact ⟨m, hm, x, hx0, by omega, hnot, heven, heven', hdiff⟩
  · have hr : (x + m) % N = x + m - N := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    let y := x + m - N
    have hy0 : 0 < y := by dsimp only [y]; omega
    have hsum : (N - m) + y = x := by dsimp only [y]; omega
    have hynot : ¬ undeterminedGcd α k ∣ y := by
      intro hh
      have hdm' := undeterminedGcd_dvd α k (N - m) (undeterminedCuts_reflect α k m hm)
      exact hnot (hsum ▸ dvd_add hdm' hh)
    refine ⟨N - m, undeterminedCuts_reflect α k m hm, y, hy0, by omega,
      hynot, ?_, ?_, ?_⟩
    · simpa only [hr] using heven'
    · rwa [hsum]
    · rw [hsum]
      intro he
      apply hdiff
      rw [hr]
      exact he.symm

end SkewClassInflation
