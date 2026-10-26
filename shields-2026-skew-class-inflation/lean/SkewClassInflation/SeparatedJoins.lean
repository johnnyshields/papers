/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileJoins

/-!
# Hessenberg joins with separated positive seams

The endpoint hypotheses in `eq:cut-merge` and the source construction
`eq:repeated-blocks` of `shields-2026-skew-class-inflation.tex`.
The incident interior gaps are retained explicitly; connectedness alone
is not substituted for the required separation.  Sorry-free.
-/

namespace SkewClassInflation.Profile

open SkewJacobiNegative

/-- Exact incident endpoint bounds preserve Hessenberg form at a positive joining seam. -/
theorem join_thick {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
    (hp : d < P.r (Fin.last n)) (hq : d < Q.r 0)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q)
    (hleft : ∀ j : Fin n, j.val + 1 = n → P.g j + d < P.r (Fin.last n))
    (hright : ∀ j : Fin m, j.val = 0 → d + Q.g j < Q.r 0) :
    Staircase.Thick (join P Q d hp hq) := by
  intro j k hjk
  have hv : j.val + 1 = k.val := congrArg Fin.val hjk
  have hj := j.isLt
  have hk := k.isLt
  change joinGaps P Q d j + joinGaps P Q d k < joinRows P Q j.succ
  rcases lt_trichotomy k.val n with hkn | hkn | hnk
  · have hjn : j.val < n := by omega
    have h := hP ⟨j.val, hjn⟩ ⟨k.val, hkn⟩ (Fin.ext hv)
    change P.g ⟨j.val, hjn⟩ + P.g ⟨k.val, hkn⟩ <
      P.r ⟨j.val + 1, by omega⟩ at h
    simpa only [joinGaps, dite_eq_left hjn, dite_eq_left hkn, joinRows,
      Fin.val_succ, dite_eq_left (show j.val + 1 < n + 1 by omega)] using h
  · have hjn : j.val < n := by omega
    have h := hleft ⟨j.val, hjn⟩ (by change j.val + 1 = n; omega)
    have he : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = Fin.last n :=
      Fin.ext (by change j.val + 1 = n; omega)
    simpa only [joinGaps, dite_eq_left hjn, dite_eq_right (show ¬ k.val < n by omega),
      dite_eq_left hkn, joinRows, Fin.val_succ,
      dite_eq_left (show j.val + 1 < n + 1 by omega), he] using h
  · by_cases hjn : j.val = n
    · have hm : 0 < m := by omega
      have h := hright (⟨0, hm⟩ : Fin m) rfl
      have hkg : (⟨k.val - (n + 1), by omega⟩ : Fin m) = ⟨0, hm⟩ :=
        Fin.ext (by change k.val - (n + 1) = 0; omega)
      have hjr : (⟨j.val + 1 - (n + 1), by omega⟩ : Fin (m + 1)) = 0 :=
        Fin.ext (by simp only [Fin.val_zero]; omega)
      simpa only [joinGaps, dite_eq_right (show ¬ j.val < n by omega), dite_eq_left hjn,
        dite_eq_right (show ¬ k.val < n by omega), dite_eq_right (show k.val ≠ n by omega),
        joinRows, Fin.val_succ, dite_eq_right (show ¬ j.val + 1 < n + 1 by omega),
        hkg, hjr] using h
    · have hjn' : n < j.val := by omega
      let a : Fin m := ⟨j.val - (n + 1), by omega⟩
      let b : Fin m := ⟨k.val - (n + 1), by omega⟩
      have hab : a.succ = b.castSucc := Fin.ext (by dsimp [a, b]; omega)
      have h := hQ a b hab
      have hr : (⟨j.val + 1 - (n + 1), by omega⟩ : Fin (m + 1)) = a.succ := by
        apply Fin.ext
        dsimp [a]
        omega
      simpa only [joinGaps, dite_eq_right (show ¬ j.val < n by omega), dite_eq_right hjn,
        dite_eq_right (show ¬ k.val < n by omega), dite_eq_right (show k.val ≠ n by omega),
        joinRows, Fin.val_succ, dite_eq_right (show ¬ j.val + 1 < n + 1 by omega),
        hr] using h

end SkewClassInflation.Profile
