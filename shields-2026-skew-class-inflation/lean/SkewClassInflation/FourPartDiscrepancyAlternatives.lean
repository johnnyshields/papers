/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FourPartActualPatterns

/-!
# Actual four-part alternatives at an undetermined even discrepancy

The four-part counting step in even-discrepancy reconstruction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
A genuine same-inventory mate flips the undetermined cut and preserves
the other actual subset cuts.  The exact labeled inventory count then
forces the two full-code alternatives, including repeated part values.
Sorry-free.
-/

namespace SkewClassInflation

/-- Equal actual reflected cut pairs identify the full code. -/
theorem compositionCutCodeNat_eq_of_cut_bools {N : ℕ} (α : Composition N) (x y : ℕ)
    (hl : actualCutBool α x = actualCutBool α y)
    (hr : actualCutBool α (N - x) = actualCutBool α (N - y)) :
    compositionCutCodeNat α x = compositionCutCodeNat α y := by
  classical
  by_cases hx : x ∈ properCuts α <;> by_cases hxr : N - x ∈ properCuts α <;>
    by_cases hy : y ∈ properCuts α <;> by_cases hyr : N - y ∈ properCuts α <;>
      simp_all [actualCutBool, compositionCutCodeNat, compositionCutType, compositionCutSign]

/-- Equal signed values identify the actual pair or put both pairs on the even channel. -/
theorem equal_cutSign_bool_pairs {N : ℕ} (α : Composition N) (x y : ℕ)
    (he : compositionCutSign α x = compositionCutSign α y) :
    (actualCutBool α x = actualCutBool α y ∧
      actualCutBool α (N - x) = actualCutBool α (N - y)) ∨
    (actualCutBool α x = actualCutBool α (N - x) ∧
      actualCutBool α y = actualCutBool α (N - y)) := by
  classical
  by_cases hx : x ∈ properCuts α <;> by_cases hxr : N - x ∈ properCuts α <;>
    by_cases hy : y ∈ properCuts α <;> by_cases hyr : N - y ∈ properCuts α <;>
      simp_all [actualCutBool, compositionCutSign]

/-- The actual inventory and reflected subset data force the two full-code alternatives. -/
theorem fourPart_even_discrepancy_alternatives {N : ℕ} (α β : Composition N)
    (hInv : coarseningInventory β = coarseningInventory α) (m x z p : ℕ+)
    (hsum : m.val + x.val + z.val + p.val = N)
    (hm : compositionCutType α m.val = 1) (hx : compositionCutType α x.val ≠ 1)
    (hmxt : compositionCutType α (m.val + x.val) ≠ 1)
    (hz : compositionCutType α z.val = 1)
    (hmzt : compositionCutType α (m.val + z.val) = 1)
    (hmx : actualCutBool α (m.val + x.val) = !actualCutBool α x.val)
    (hmz : actualCutBool α (m.val + z.val) = actualCutBool α z.val)
    (hmflip : actualCutBool β m.val = !actualCutBool α m.val)
    (hother : ∀ y ∈ ({x.val, z.val, m.val + x.val, m.val + z.val,
        x.val + z.val, m.val + x.val + z.val} : Finset ℕ),
      actualCutBool β y = actualCutBool α y ∧
        actualCutBool β (N - y) = actualCutBool α (N - y))
    (hsign : compositionCutSign α (x.val + z.val) =
      compositionCutSign α (m.val + x.val + z.val)) :
    (compositionCutCodeNat α (x.val + z.val) = compositionCutCodeNat α z.val ∧
      compositionCutCodeNat α (m.val + x.val + z.val) = compositionCutCodeNat α z.val) ∨
    (compositionCutCodeNat α (x.val + z.val) = compositionCutCodeNat α x.val ∧
      compositionCutCodeNat α (m.val + x.val + z.val) =
        compositionCutCodeNat α (m.val + x.val)) := by
  classical
  have htypes (y : ℕ) := coarseningInventory_cut_type β α hInv y
  have hxm := (hother x.val (by simp)).1
  have hzm := (hother z.val (by simp)).1
  have hmxm := (hother (m.val + x.val) (by simp)).1
  have hmzm := (hother (m.val + z.val) (by simp)).1
  have hxmz := hother (x.val + z.val) (by simp)
  have hmxmz := hother (m.val + x.val + z.val) (by simp)
  have hβm : compositionCutType β m.val = 1 := (htypes m.val).trans hm
  have hβx : compositionCutType β x.val ≠ 1 := by rwa [htypes x.val]
  have hβmx : compositionCutType β (m.val + x.val) ≠ 1 := by rwa [htypes (m.val + x.val)]
  have hβz : compositionCutType β z.val = 1 := (htypes z.val).trans hz
  have hβmz : compositionCutType β (m.val + z.val) = 1 := (htypes _).trans hmzt
  have hβmxcut : actualCutBool β (m.val + x.val) = !actualCutBool β x.val := by
    rw [hmxm, hxm]
    exact hmx
  have hβmzcut : actualCutBool β (m.val + z.val) = actualCutBool β z.val := by
    rw [hmzm, hzm]
    exact hmz
  have hcount := fourPart_mask_count_invariant α β hInv.symm m x z p hsum
  rw [fourPart_actual_discrepancy_count α m.val x.val z.val hm hx hmxt hz hmzt hmx hmz,
    fourPart_actual_discrepancy_count β m.val x.val z.val
      hβm hβx hβmx hβz hβmz hβmxcut hβmzcut,
    hmflip, hxm, hzm, hxmz.1, hxmz.2, hmxmz.1, hmxmz.2] at hcount
  have hoptions := fourPartDiscrepancy_alternatives
    (actualCutBool α m.val) (actualCutBool α x.val) (actualCutBool α z.val)
    (actualCutBool α (x.val + z.val)) (actualCutBool α (N - (x.val + z.val)))
    (actualCutBool α (m.val + x.val + z.val))
    (actualCutBool α (N - (m.val + x.val + z.val)))
    (equal_cutSign_bool_pairs α _ _ hsign) hcount
  rcases hoptions with ⟨h6, hr6, h7, hr7⟩ | ⟨h6, hr6, h7, hr7⟩
  · left
    have hzr := actualCutBool_reflect_one α z.val hz
    exact ⟨compositionCutCodeNat_eq_of_cut_bools α _ _ h6 (hr6.trans hzr.symm),
      compositionCutCodeNat_eq_of_cut_bools α _ _ h7 (hr7.trans hzr.symm)⟩
  · right
    have hxr := actualCutBool_reflect_even α x.val hx
    have hmxr := actualCutBool_reflect_even α (m.val + x.val) hmxt
    exact ⟨compositionCutCodeNat_eq_of_cut_bools α _ _ h6 (hr6.trans hxr.symm),
      compositionCutCodeNat_eq_of_cut_bools α _ _ (h7.trans hmx.symm)
        (hr7.trans (hmxr.trans hmx).symm)⟩

end SkewClassInflation
