/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.DeterminationPeriods

/-!
# Finite closure of actual even-cut discrepancies

The finite period-refinement mechanism for the ribbon factor-reversal classification cited
after `thm:sharp-inflation` in `shields-2026-skew-class-inflation.tex`.
Every nonempty next discrepancy set strictly decreases the positive
candidate period.  The construction therefore reaches an actual empty
next set; no termination or stable-period datum is assumed.  Sorry-free.
-/

namespace SkewClassInflation

/-- Actual even-type disagreements reached by the current frontier, away from its period. -/
noncomputable def evenCutDisagreements {N : ℕ} (α : Composition N)
    (p : ℕ) (T : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioo 0 N).filter (fun x => ¬ p ∣ x ∧ ∃ t ∈ T,
    compositionCutType α x ≠ 1 ∧ compositionCutType α ((x + t) % N) ≠ 1 ∧
      compositionCutType α x ≠ compositionCutType α ((x + t) % N))

/-- A new discrepancy both lies at a true proper coordinate and fails old-period divisibility. -/
theorem evenCutDisagreements_bounds {N : ℕ} (α : Composition N) (p : ℕ) (T : Finset ℕ)
    (x : ℕ) (hx : x ∈ evenCutDisagreements α p T) :
    0 < x ∧ x < N ∧ ¬ p ∣ x := by
  have hh := Finset.mem_filter.mp hx
  exact ⟨(Finset.mem_Ioo.mp hh.1).1, (Finset.mem_Ioo.mp hh.1).2, hh.2.1⟩

/-- One actual closure step refines the period by every new discrepancy and updates its frontier. -/
noncomputable def evenCutClosureStep {N : ℕ} (α : Composition N)
    (S : ℕ × Finset ℕ) : ℕ × Finset ℕ :=
  let D := evenCutDisagreements α S.1 S.2
  (S.1.gcd (D.gcd id), D)

/-- A positive period remains positive after every actual refinement. -/
theorem evenCutClosureStep_pos {N : ℕ} (α : Composition N) (S : ℕ × Finset ℕ)
    (hp : 0 < S.1) : 0 < (evenCutClosureStep α S).1 :=
  Nat.gcd_pos_of_pos_left _ hp

/-- Every refined candidate period divides its predecessor. -/
theorem evenCutClosureStep_dvd {N : ℕ} (α : Composition N) (S : ℕ × Finset ℕ) :
    (evenCutClosureStep α S).1 ∣ S.1 := Nat.gcd_dvd_left _ _

/-- A nonempty discrepancy set strictly decreases the actual positive candidate period. -/
theorem evenCutClosureStep_lt {N : ℕ} (α : Composition N) (S : ℕ × Finset ℕ)
    (hp : 0 < S.1) (hne : (evenCutDisagreements α S.1 S.2).Nonempty) :
    (evenCutClosureStep α S).1 < S.1 := by
  have hle := Nat.le_of_dvd hp (evenCutClosureStep_dvd α S)
  have hneq : (evenCutClosureStep α S).1 ≠ S.1 := by
    intro he
    obtain ⟨x, hx⟩ := hne
    have hg : (evenCutClosureStep α S).1 ∣ (evenCutDisagreements α S.1 S.2).gcd id :=
      Nat.gcd_dvd_right _ _
    have hd := hg.trans (Finset.gcd_dvd hx)
    rw [he] at hd
    exact (evenCutDisagreements_bounds α S.1 S.2 x hx).2.2 hd
  omega

/-- Positive periods persist throughout the actual iterated construction. -/
theorem evenCutClosure_iterate_pos {N : ℕ} (α : Composition N) (S : ℕ × Finset ℕ)
    (hp : 0 < S.1) (i : ℕ) : 0 < ((evenCutClosureStep α)^[i] S).1 := by
  induction i with
  | zero => exact hp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact evenCutClosureStep_pos α _ ih

/-- The actual refinement process reaches an empty next set before its initial positive period. -/
theorem evenCutClosure_terminates {N : ℕ} (α : Composition N) (S : ℕ × Finset ℕ)
    (hp : 0 < S.1) :
    ∃ i < S.1, evenCutDisagreements α ((evenCutClosureStep α)^[i] S).1
      ((evenCutClosureStep α)^[i] S).2 = ∅ := by
  classical
  generalize he : S.1 = p at hp ⊢
  induction p using Nat.strong_induction_on generalizing S with
  | h p ih =>
    by_cases hD : evenCutDisagreements α S.1 S.2 = ∅
    · exact ⟨0, hp, hD⟩
    · have hlt := evenCutClosureStep_lt α S (by omega) (Finset.nonempty_iff_ne_empty.mpr hD)
      have hpos := evenCutClosureStep_pos α S (by omega)
      obtain ⟨i, hi, hstop⟩ := ih (evenCutClosureStep α S).1 (by omega)
        (evenCutClosureStep α S) rfl hpos
      refine ⟨i + 1, by omega, ?_⟩
      rwa [Function.iterate_succ_apply]

/-- The actual initial period and undetermined frontier, without supplied refinement data. -/
noncomputable def evenCutClosureInitial {N : ℕ} (α : Composition N) (k : ℕ) :
    ℕ × Finset ℕ := (undeterminedGcd α k, undeterminedCuts α k)

/-- Every actual nonempty undetermined frontier has a terminating even-discrepancy refinement. -/
theorem undetermined_evenCutClosure_terminates {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) :
    ∃ i < undeterminedGcd α k,
      evenCutDisagreements α ((evenCutClosureStep α)^[i] (evenCutClosureInitial α k)).1
        ((evenCutClosureStep α)^[i] (evenCutClosureInitial α k)).2 = ∅ :=
  evenCutClosure_terminates α (evenCutClosureInitial α k) (undeterminedGcd_pos α k hne)

end SkewClassInflation
