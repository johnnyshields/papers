/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileMergeReadings
import SkewClassInflation.ThinPowers

/-!
# Positional recovery of the remaining thin power

The literal splitting calculation used by `thm:two-row-thin-class` in
`shields-2026-skew-class-inflation.tex`.  A fixed first block and the full
merged row word recover every row and gap of the remaining block.  No
Schur-equality hypothesis is substituted for the literal merger equation.
Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- The right factor of a literal merged thin power is the full remaining literal power. -/
theorem right_power_of_merge {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (R : Profile k)
    (he : Profile.merge (B.innerPower m hm) R 0 ((B.innerPower m hm).r_pos _) (R.r_pos _) =
      B.innerPower (m + k) (by omega)) : R = B.innerPower k hk := by
  have hlast : (B.innerPower m hm).r (Fin.last m) = B.b := by
    simp [innerPower, powerRows, Nat.ne_of_gt hm]
  have hmiddle : (B.innerPower (m + k) (by omega)).r (⟨m, by omega⟩ : Fin (m + k + 1)) =
      B.a + B.b := by
    change B.powerRows (m + k) ⟨m, by omega⟩ = B.a + B.b
    simp [powerRows, Nat.ne_of_gt hm, Nat.ne_of_gt hk]
  have hmid := Profile.merge_joined_row (B.innerPower m hm) R 0
    ((B.innerPower m hm).r_pos _) (R.r_pos _)
  rw [he, hmiddle, hlast] at hmid
  have hfirst : R.r 0 = B.a := by omega
  apply Gluing.Profile.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hfirst
    · have hr := Profile.merge_r_right (B.innerPower m hm) R 0
        ((B.innerPower m hm).r_pos _) (R.r_pos _) j
      rw [he] at hr
      change R.r j.succ = B.powerRows k j.succ
      rw [← hr]
      change B.powerRows (m + k) ⟨m + 1 + j.val, by have := j.isLt; omega⟩ =
        B.powerRows k j.succ
      unfold powerRows
      split_ifs <;> simp only [Fin.val_succ] at * <;> omega
  · funext j
    have hg := Profile.merge_g_right (B.innerPower m hm) R 0
      ((B.innerPower m hm).r_pos _) (R.r_pos _) j
    rw [he] at hg
    change B.c = R.g j at hg
    exact hg.symm

end SkewClassInflation.ThinParameters
