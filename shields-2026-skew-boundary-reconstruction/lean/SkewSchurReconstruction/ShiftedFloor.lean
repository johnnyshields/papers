/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.LaplaceFloor

/-!
# The normalized and shifted floors

In `rem:which-floor`, the normalized action and the base-shifted action have
adjacent minimizing pairs {1,2} and {0,1}, respectively, at positive base.
At base zero both actions agree and their minimizing pair is {1,2}.
-/

namespace SkewSchurReconstruction
namespace Diagram

variable {n m : ℕ}

/-- The two floor conventions are related on the actual ratio locus, not identified. -/
theorem ratio_shifted_floor_same_count (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hinner : X.inner = Y.inner)
    (hG : gridDefect X Y ≠ 0) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) (w : ConvexWeight) :
    (∀ j : Fin (n + 1), j ∈ defectMinimizers w X Y 0 ↔ j.val = 1 ∨ j.val = 2) ∧
      (∀ j : Fin (n + 1), j ∈ defectMinimizers w X Y (-(r : ℤ)) ↔
        if r = 0 then j.val = 1 ∨ j.val = 2 else j.val = 0 ∨ j.val = 1) := by
  obtain ⟨v, hv, _, _, _, hall⟩ :=
    ratio_rigidity_same_count X Y hX hY hinner hG r a ha h
  obtain ⟨hvirtual, _, hchain, _⟩ := hall w
  have hrow := hchain ⟨0, hv⟩
  have hz : X.rowParam ⟨0, by have := v.isLt; omega⟩ = 0 := by
    simp [rowParam, top, hX.1]
  have hplain : ∀ j : Fin (n + 1),
      j ∈ defectMinimizers w X Y 0 ↔ j.val = 1 ∨ j.val = 2 := by
    simpa only [hz, Fin.val_mk, zero_add] using hrow
  refine ⟨hplain, ?_⟩
  by_cases hr : r = 0
  · subst r
    simpa using hplain
  · have hgamma : ratioVirtualShift r a = r := by simp [ratioVirtualShift, hr]
    simpa only [hgamma, ite_eq_right hr] using hvirtual

/-- `rem:which-floor`, with row count supplied by the actual ratio identity. -/
theorem ratio_shifted_floor (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected)
    (hinner : ∀ (i : Fin n) (j : Fin m), i.val = j.val → X.inner i = Y.inner j)
    (hG : gridDefect X Y ≠ 0) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    ∃ hn : n = m, let Z : Diagram n := hn.symm ▸ Y;
      ∀ w : ConvexWeight,
        (∀ j : Fin (n + 1), j ∈ defectMinimizers w X Z 0 ↔ j.val = 1 ∨ j.val = 2) ∧
          (∀ j : Fin (n + 1), j ∈ defectMinimizers w X Z (-(r : ℤ)) ↔
            if r = 0 then j.val = 1 ∨ j.val = 2 else j.val = 0 ∨ j.val = 1) := by
  have hn := rowCount_eq_of_ratioIdentity X Y hX hY r a ha h
  subst m
  refine ⟨rfl, ?_⟩
  dsimp only
  intro w
  exact ratio_shifted_floor_same_count X Y hX hY (funext fun i => hinner i i rfl)
    hG r a ha h w

end Diagram
end SkewSchurReconstruction
