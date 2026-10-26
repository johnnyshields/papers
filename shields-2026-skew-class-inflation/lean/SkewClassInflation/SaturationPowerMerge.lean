/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationPowers
import SkewClassInflation.ProfileMergeReadings

/-!
# Literal merger of arbitrary repeated-inner powers

The source contraction in `eq:total-contraction` of
`shields-2026-skew-class-inflation.tex`.  Merger retains every ordered
interior row, including values coinciding with the merger length.
Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- Merging two positive repeated-inner powers gives the literal power of their total order. -/
theorem merge_powers (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (⟨a * A.k + b * A.k, Profile.merge (A.power a ha) (A.power b hb) A.d
      (A.power_rows_above_seam a ha _) (A.power_rows_above_seam b hb _)⟩ : ConnectedProfile) =
      ⟨(a + b) * A.k, A.power (a + b) (by omega)⟩ := by
  let P := A.power a ha
  let Q := A.power b hb
  have hp : A.d < P.r (Fin.last (a * A.k)) := A.power_rows_above_seam a ha _
  have hq : A.d < Q.r 0 := A.power_rows_above_seam b hb _
  have hak : 0 < a * A.k := Nat.mul_pos ha A.k_pos
  have hbk : 0 < b * A.k := Nat.mul_pos hb A.k_pos
  have hsize : a * A.k + b * A.k = (a + b) * A.k := by ring
  apply profileSigma_eq_of_words
  · apply List.ext_getElem
    · simp only [List.length_ofFn]
      omega
    · intro i hi hj
      simp only [List.length_ofFn] at hi hj
      simp only [List.getElem_ofFn]
      change (Profile.merge P Q A.d hp hq).r ⟨i, hi⟩ =
        A.powerRows (a + b) ⟨i, hj⟩
      rcases lt_trichotomy i (a * A.k) with hl | he | hr
      · have hleft := Profile.merge_r_left P Q A.d hp hq ⟨i, hl⟩
        change (Profile.merge P Q A.d hp hq).r ⟨i, hi⟩ = P.r ⟨i, by omega⟩ at hleft
        rw [hleft]
        change A.powerRows a ⟨i, by omega⟩ = A.powerRows (a + b) ⟨i, hj⟩
        unfold powerRows
        dsimp only
        split_ifs <;> first | rfl | omega
      · subst i
        have hm := Profile.merge_joined_row P Q A.d hp hq
        rw [A.power_last, A.power_first] at hm
        have hmerger : (A.merger : ℤ) = (A.r 0 : ℤ) + A.r (Fin.last A.k) - A.d := by
          have := A.first_bound
          dsimp [merger]
          omega
        have hrow : (Profile.merge P Q A.d hp hq).r ⟨a * A.k, hi⟩ = A.merger := by
          have hm' : ((Profile.merge P Q A.d hp hq).r ⟨a * A.k, hi⟩ : ℤ) =
              (A.merger : ℤ) := by linarith only [hm, hmerger]
          exact_mod_cast hm'
        rw [hrow]
        unfold powerRows
        dsimp only
        rw [ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left (Nat.mul_mod_left a A.k)]
      · let j : Fin (b * A.k) := ⟨i - (a * A.k + 1), by omega⟩
        have hjv : j.val + 1 = i - a * A.k := by dsimp [j]; omega
        have heq : (⟨a * A.k + 1 + j.val, by have := j.isLt; omega⟩ :
            Fin (a * A.k + b * A.k + 1)) = ⟨i, hi⟩ := Fin.ext (by dsimp [j]; omega)
        have hright := Profile.merge_r_right P Q A.d hp hq j
        rw [heq] at hright
        rw [hright]
        change A.powerRows b j.succ = A.powerRows (a + b) ⟨i, hj⟩
        have hmod : (j.val + 1) % A.k = i % A.k := by
          have hi' : i = a * A.k + (j.val + 1) := by omega
          simp only [hi', Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
        have hzero : j.val + 1 ≠ 0 := by omega
        have hizero : i ≠ 0 := by omega
        have hlast : j.val + 1 = b * A.k ↔ i = (a + b) * A.k := by omega
        simp only [powerRows, Fin.val_succ, ite_eq_right hzero,
          ite_eq_right hizero, hlast, hmod]
  · apply List.ext_getElem
    · simp only [List.length_ofFn]
      exact hsize
    · intro i hi hj
      simp only [List.length_ofFn] at hi hj
      simp only [List.getElem_ofFn]
      change (Profile.merge P Q A.d hp hq).g ⟨i, hi⟩ = A.c
      by_cases hl : i < a * A.k
      · exact Profile.merge_g_left P Q A.d hp hq ⟨i, hl⟩
      · let j : Fin (b * A.k) := ⟨i - a * A.k, by omega⟩
        have heq : (⟨a * A.k + j.val, by have := j.isLt; omega⟩ :
            Fin (a * A.k + b * A.k)) = ⟨i, hi⟩ := Fin.ext (by dsimp [j]; omega)
        have hg := Profile.merge_g_right P Q A.d hp hq j
        rw [heq] at hg
        exact hg

end SkewClassInflation.SaturationInner
