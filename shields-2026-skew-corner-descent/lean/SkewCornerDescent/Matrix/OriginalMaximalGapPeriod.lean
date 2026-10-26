/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicMaximalWindows
import SkewCornerDescent.Matrix.OriginalMaximalBinReciprocal

/-!
# The exact average branch of the actual maximal gap bin

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). The true
completed gap inventory gives the exact mean. An upper bound equal to that mean
produces the selected-multiplicity period by the standing coprime outer counts.
No gap periodicity is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual maximal window bound dominates the exact mean; equality supplies
the missing completed-gap period rather than taking it as a hypothesis. -/
theorem originalCompletedGap_maximum_mean_period {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (b a r : ℕ) (hab : a ≤ b) (hcoprime : b.Coprime a)
    (hcount : originalSelectedCount (hD := hD) P = b * r)
    (Δ M : ℤ) (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ)
    (hbound : ∀ s : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
        1 ((b - a) * r) s ≤ M) :
    ((b - a : ℕ) : ℤ) * Δ ≤ M ∧
      (M = ((b - a : ℕ) : ℤ) * Δ → Function.Periodic
        (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
        (r : ZMod (originalSelectedCount (hD := hD) P))) := by
  let f := fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)
  have he := (ZMod.finEquiv (originalSelectedCount (hD := hD) P)).toEquiv.sum_comp f
  change (∑ i, c.originalCompletedGap P
    ((ZMod.finEquiv _).symm ((ZMod.finEquiv _) i))) = ∑ z, f z at he
  simp only [RingEquiv.symm_apply_apply] at he
  have hsum : ∑ z, f z = (b : ℤ) * Δ := by
    rw [← he, ← hspan]
    exact c.originalCompletedGap_sum P hB
  have hmean : (((b - a) * r : ℕ) : ℤ) * ∑ z, f z =
      (originalSelectedCount (hD := hD) P : ℤ) * (((b - a : ℕ) : ℤ) * Δ) := by
    rw [hsum, hcount]
    push_cast
    ring
  have hmax := integer_inventory_le_of_window_bound f 1 ((b - a) * r) M hbound
  have hmax' : (((b - a) * r : ℕ) : ℤ) * ∑ z, f z ≤
      (originalSelectedCount (hD := hD) P : ℤ) * M := by simpa using hmax
  rw [hmean] at hmax'
  have hB' : 0 < (originalSelectedCount (hD := hD) P : ℤ) := by exact_mod_cast hB
  refine ⟨le_of_mul_le_mul_left hmax' hB', ?_⟩
  intro hM
  have hp := integer_zmod_period_of_maximum_eq_average f ((b - a) * r) M hbound (by
    rw [hM]
    exact hmean)
  have hgcd : Nat.gcd ((b - a) * r) (originalSelectedCount (hD := hD) P) = r := by
    rw [hcount, Nat.gcd_mul_right]
    have hc : (b - a).Coprime b := (Nat.coprime_self_sub_left hab).mpr hcoprime.symm
    rw [hc.gcd_eq_one, one_mul]
  rwa [hgcd] at hp

/-- The actual maximum and one attaining start are constructed from the complete
finite cycle. Its equality branch then supplies the selected-multiplicity period. -/
theorem originalCompletedGap_maximum_alternative {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (b a r : ℕ) (hab : a ≤ b) (hcoprime : b.Coprime a)
    (hcount : originalSelectedCount (hD := hD) P = b * r)
    (Δ : ℤ) (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ) :
    ∃ M : ℤ,
      (∀ s : ZMod (originalSelectedCount (hD := hD) P),
        windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
          1 ((b - a) * r) s ≤ M) ∧
      (∃ s : ZMod (originalSelectedCount (hD := hD) P),
        windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
          1 ((b - a) * r) s = M) ∧
      ((b - a : ℕ) : ℤ) * Δ ≤ M ∧
      (M = ((b - a : ℕ) : ℤ) * Δ → Function.Periodic
        (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
        (r : ZMod (originalSelectedCount (hD := hD) P))) := by
  classical
  let f := fun s : ZMod (originalSelectedCount (hD := hD) P) =>
    windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      1 ((b - a) * r) s
  have hne : (Finset.univ : Finset (ZMod (originalSelectedCount (hD := hD) P))).Nonempty :=
    ⟨0, Finset.mem_univ _⟩
  let M := Finset.univ.sup' hne f
  have hbnd : ∀ s, f s ≤ M := fun s => Finset.le_sup' f (Finset.mem_univ s)
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup' hne f
  have hmean := c.originalCompletedGap_maximum_mean_period P hB b a r hab hcoprime
    hcount Δ M hspan hbnd
  exact ⟨M, hbnd, ⟨s, hs.symm⟩, hmean.1, hmean.2⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
