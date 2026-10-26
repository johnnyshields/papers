/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CellProfiles

/-!
# Hatted marks throughout the actual bi-infinite amalgamation

The translation step for Hypothesis IV in `subsec:marked-geometry`
of `shields-2026-skew-class-inflation.tex`.  Empty hatted marks at one
specified placement give empty hatted marks at every translated copy
in the actual periodic cell union.  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing

/-- Translating by a whole period preserves membership in the actual infinite amalgamation. -/
theorem periodicUnion_sub_smul (ω : MarkedInner) (x : ℤ × ℤ) (k : ℤ) :
    x - k • ω.v ∈ ω.periodicUnion ↔ x ∈ ω.periodicUnion := by
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have he : (x - k • ω.v) - l • ω.v = x - (k + l) • ω.v := by
      rw [add_smul]
      abel
    rw [← he]
    exact hl
  · rintro ⟨l, hl⟩
    refine ⟨l - k, ?_⟩
    have he : (x - k • ω.v) - (l - k) • ω.v = x - l • ω.v := by
      rw [sub_smul]
      abel
    rw [he]
    exact hl

/-- A hatted mark at any translated copy moves back into the actual base hatted mark. -/
theorem hatMark_sub_smul (ω : MarkedInner) (x : ℤ × ℤ) (k : ℤ)
    (hx : x ∈ ω.hatMark (translate (k • ω.v) ω.W)) :
    x - k • ω.v ∈ ω.hatMark ω.W := by
  have he : x + eCell - k • ω.v = (x - k • ω.v) + eCell := by abel
  rcases hx with hx | hx
  · left
    refine ⟨(periodicUnion_sub_smul ω x k).mpr hx.1, ?_⟩
    have hw := hx.2
    rw [mem_translate, he] at hw
    exact hw
  · right
    have hw := hx.1
    rw [mem_translate] at hw
    refine ⟨hw, ?_⟩
    have hp := (periodicUnion_sub_smul ω (x + eCell) k).mpr hx.2
    rw [he] at hp
    exact hp

/-- A literally empty base hatted mark proves Hypothesis IV for all copies. -/
theorem noHatAdjacency_of_hatMark_empty (ω : MarkedInner) (h : ω.hatMark ω.W = ∅) :
    ω.NoHatAdjacency := by
  intro k m x _ y hy
  have hh := hatMark_sub_smul ω y m hy
  rw [h] at hh
  exact hh.elim

end SkewClassInflation
