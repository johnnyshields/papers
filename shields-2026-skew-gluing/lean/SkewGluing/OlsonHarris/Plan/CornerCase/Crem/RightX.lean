import SkewGluing.OlsonHarris.Plan.CornerCase.Crem.Compose

/-!
# The outer after removing a ribbon removable on the right

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the outer `D \ A` of thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`) for a ribbon `A` of size `m` removable on the right from a
connected skew `D`.

A ribbon removable on the right is the border strip `A = windowRibbon D j₀ m` of the last cells
of the diagonals `j₀ ≤ j < j₀ + m` (`RightWindow`); then `D \ A` has the diagonals of `D` except
those of the window with a single cell, the same first rows, and the last rows lowered by one on
the window (`contents_X`, `diagLo_X`, `diagHi_X`).

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

/-- The data of a ribbon `windowRibbon D j₀ m` of size `m` removable on the right from `D`. -/
structure RightWindow (D : Diagram) (j0 : ℤ) (m : ℕ) : Prop where
  conn : IsConnectedSkew D
  pos : 0 < m
  start : j0 ∈ contents D
  stop : j0 + m - 1 ∈ contents D
  startEnd : j0 - 1 ∉ contents D ∨ diagHi D (j0 - 1) = diagHi D j0
  stopEnd : j0 + m ∉ contents D ∨ diagHi D (j0 + m - 1) - diagHi D (j0 + m) = 1

theorem RightWindow.of_mem {D A : Diagram} (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m)
    (hA : A ∈ rightRibbons D m) :
    ∃ j0 : ℤ, A = windowRibbon D j0 m ∧ RightWindow D j0 m := by
  obtain ⟨n0, h1, h2, h3, h4, hY⟩ := rightRibbon_endpoints hD hm hA
  exact ⟨n0, hY, ⟨hD, hm, h1, h2, h3, h4⟩⟩

variable {D : Diagram} {j0 : ℤ} {m : ℕ}

theorem mem_sdiff_window {i j : ℤ} :
    (i, i + j) ∈ D \ windowRibbon D j0 m ↔
      (i, i + j) ∈ D ∧ ¬ (j0 ≤ j ∧ j < j0 + m ∧ i = diagHi D j) := by
  rw [Finset.mem_sdiff, mem_windowRibbon]
  simp only [content]
  have e : i + j - i = j := by ring
  rw [e]

theorem contents_X (hw : RightWindow D j0 m) {j : ℤ} :
    j ∈ contents (D \ windowRibbon D j0 m) ↔
      j ∈ contents D ∧ ¬ (j0 ≤ j ∧ j < j0 + m ∧ diagLo D j = diagHi D j) := by
  have hs := (isConnectedSkew_iff_diagonal.mp hw.conn)
  rw [mem_contents_iff]
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_sdiff_window] at hi
    refine ⟨mem_contents_iff.mpr ⟨i, hi.1⟩, fun ⟨h1, h2, h3⟩ => hi.2 ⟨h1, h2, ?_⟩⟩
    have := diagLo_le hi.1 (by ring : i + j - i = j)
    have := le_diagHi hi.1 (by ring : i + j - i = j)
    omega
  · rintro ⟨hj, hn⟩
    refine ⟨diagLo D j, ?_⟩
    rw [mem_sdiff_window]
    refine ⟨diagLo_mem hj, fun ⟨h1, h2, h3⟩ => hn ⟨h1, h2, h3⟩⟩

theorem diagLo_X (hw : RightWindow D j0 m) {j : ℤ}
    (hj : j ∈ contents (D \ windowRibbon D j0 m)) :
    diagLo (D \ windowRibbon D j0 m) j = diagLo D j := by
  have hj' := (contents_X hw).mp hj
  refine diagLo_eq_of (l := diagLo D j) ?_ ?_
  · rw [mem_sdiff_window]
    exact ⟨diagLo_mem hj'.1, fun ⟨h1, h2, h3⟩ => hj'.2 ⟨h1, h2, h3.symm ▸ (by
      have := diagLo_le_diagHi hj'.1; omega)⟩⟩
  · intro i hi
    rw [mem_sdiff_window] at hi
    exact diagLo_le hi.1 (by ring)

theorem diagHi_X (hw : RightWindow D j0 m) {j : ℤ}
    (hj : j ∈ contents (D \ windowRibbon D j0 m)) :
    diagHi (D \ windowRibbon D j0 m) j =
      diagHi D j - (if j0 ≤ j ∧ j < j0 + m then 1 else 0) := by
  have hs := hw.conn.1
  have hj' := (contents_X hw).mp hj
  have hle := diagLo_le_diagHi hj'.1
  by_cases hwin : j0 ≤ j ∧ j < j0 + m
  · have hlt : diagLo D j < diagHi D j := by
      by_contra hc
      exact hj'.2 ⟨hwin.1, hwin.2, by omega⟩
    simp only [hwin, and_self, ↓reduceIte]
    refine diagHi_eq_of (l := diagHi D j - 1) ?_ ?_
    · rw [mem_sdiff_window]
      refine ⟨(mem_skew_iff hs).mpr ⟨hj'.1, by omega, by omega⟩, fun ⟨_, _, h3⟩ => by omega⟩
    · intro i hi
      rw [mem_sdiff_window] at hi
      have := le_diagHi hi.1 (by ring : i + j - i = j)
      by_contra hc
      exact hi.2 ⟨hwin.1, hwin.2, by omega⟩
  · simp only [hwin, ↓reduceIte, sub_zero]
    refine diagHi_eq_of (l := diagHi D j) ?_ ?_
    · rw [mem_sdiff_window]
      exact ⟨diagHi_mem hj'.1, fun ⟨h1, h2, _⟩ => hwin ⟨h1, h2⟩⟩
    · intro i hi
      rw [mem_sdiff_window] at hi
      exact le_diagHi hi.1 (by ring)

end Rem

end Corner

end Plan

end SkewGluing
