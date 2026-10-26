/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.Local.EmptyMark
import SkewGluing.RowConnected
import SkewGluing.EmptyRowErosion

/-!
# Row geometry for every legal mark

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`).  Empty marks use the proved singleton-endpoint composition
construction.  Nonempty marks use the proved private-cut gluing construction.

Sorry-free.
-/

namespace SkewGluing

/-- A nonempty normalized horizontal row is a connected skew diagram. -/
theorem isConnectedSkew_horizontalRow {m : ℕ} (hm : 1 ≤ m) :
    IsConnectedSkew (horizontalRow m) := by
  have hc : ClassRows (horizontalRow m) 0 1 0 0 ((m : ℤ) - 1)
      (fun _ _ => 0) (fun _ _ => 0) := by
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · intro j a r ha0 ha1
      have ha : a = 0 := by omega
      subst a
      simp only [mem_horizontalRow, zero_add, mul_one, add_zero, ValidClass]
      constructor
      · rintro ⟨hr, hj0, hj1⟩
        exact ⟨Or.inl ⟨by omega, by omega⟩, by omega, by omega⟩
      · rintro ⟨⟨hj0, hj1⟩ | ⟨_, hbad⟩, hr0, hr1⟩
        · exact ⟨by omega, by omega, by omega⟩
        · omega
    · intro _ _ _ _ _
      exact le_refl _
    · intro _ _ _ _ _
      exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · intro _ _ _
      exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · intro hh
      omega
    · intro _
      rfl
  exact hc.isConnectedSkew

namespace MarkedInner
variable {ω : MarkedInner}

/-- The actual row composition is connected skew, including the empty mark. -/
theorem IsLegal.isConnectedSkew_compose_horizontalRow_all (h : ω.IsLegal)
    {m : ℕ} (hm : 1 ≤ m) : IsConnectedSkew (ω.compose (horizontalRow m)) := by
  by_cases hW : ω.W.Nonempty
  · exact h.isConnectedSkew_compose_horizontalRow hW hm
  · exact IsLegalEmpty.isConnectedSkew_compose
      ⟨h, Finset.not_nonempty_iff_eq_empty.mp hW⟩ (isConnectedSkew_horizontalRow hm)

/-- The actual row union is connected skew, with no extra nonempty-mark assumption. -/
theorem IsLegal.isConnectedSkew_rowCopies_all (h : ω.IsLegal)
    {m : ℕ} (hm : 1 ≤ m) : IsConnectedSkew (ω.rowCopies m) := by
  simpa only [ω.compose_horizontalRow hm] using h.isConnectedSkew_compose_horizontalRow_all hm

end MarkedInner
end SkewGluing
