/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.ExteriorGaps

/-!
# Ordered beta profiles

The row-length and adjacent-overlap reading of `eq:profile` in
`shields-2026-skew-cofactor-independence.tex`.  The profile determines the
actual decreasing beta lists up to a common translation, including diagrams
with gaps.  Half-turn reverses the profile.
-/

namespace SkewCofactorIndependence.BetaDiagram
variable {n : ℕ}

/-- Ordered row lengths and signed overlaps reconstruct both beta lists. -/
theorem translationEquivalent_of_profile (D E : BetaDiagram n)
    (hr : ∀ i, D.rowLength i = E.rowLength i)
    (ho : ∀ (i : Fin n) (hi : i.val + 1 < n), D.overlap i hi = E.overlap i hi) :
    D.TranslationEquivalent E := by
  by_cases hn : 0 < n
  · let c := D.row ⟨0, hn⟩ - E.row ⟨0, hn⟩
    have hrows : ∀ k : ℕ, ∀ i : Fin n, i.val = k → D.row i = E.row i + c := by
      intro k
      induction k with
      | zero =>
        intro i hi
        have he : i = ⟨0, hn⟩ := Fin.ext hi
        subst i
        dsimp [c]
        omega
      | succ k ih =>
        intro i hi
        let j : Fin n := ⟨k, by omega⟩
        have hj := ih j rfl
        have hlen := hr j
        have hnext : j.val + 1 < n := by dsimp [j]; omega
        have h : (⟨j.val + 1, hnext⟩ : Fin n) = i := Fin.ext (by dsimp [j]; omega)
        have hov := ho j hnext
        dsimp [rowLength, overlap] at hlen hov
        rw [h] at hov
        omega
    refine ⟨c, fun i => hrows i.val i rfl, ?_⟩
    intro i
    have h := hrows i.val i rfl
    have hlen := hr i
    dsimp [rowLength] at hlen
    omega
  · refine ⟨0, ?_, ?_⟩ <;> intro i <;> have := i.isLt <;> omega

/-- Translation preserves every ordered row length. -/
theorem TranslationEquivalent.rowLength_eq {D E : BetaDiagram n}
    (h : D.TranslationEquivalent E) (i : Fin n) : D.rowLength i = E.rowLength i := by
  obtain ⟨c, hr, hc⟩ := h
  simp only [rowLength, hr, hc]
  ring

/-- Translation preserves each signed adjacent overlap. -/
theorem TranslationEquivalent.overlap_eq {D E : BetaDiagram n}
    (h : D.TranslationEquivalent E) (i : Fin n) (hi : i.val + 1 < n) :
    D.overlap i hi = E.overlap i hi := by
  obtain ⟨c, hr, hc⟩ := h
  simp only [overlap, hr, hc]
  ring

/-- Half-turn reverses ordered row lengths. -/
theorem rotate_rowLength (D : BetaDiagram n) (i : Fin n) :
    D.rotate.rowLength i = D.rowLength i.rev := by
  simp only [rowLength, rotate]
  ring

/-- Half-turn reverses adjacent overlaps, with the actual reversed successor index. -/
theorem rotate_overlap (D : BetaDiagram n) (i : Fin n) (hi : i.val + 1 < n) :
    let j := (⟨i.val + 1, hi⟩ : Fin n).rev
    ∃ hj : j.val + 1 < n, D.rotate.overlap i hi = D.overlap j hj := by
  let j := (⟨i.val + 1, hi⟩ : Fin n).rev
  have hj : j.val + 1 < n := by simp only [j, Fin.val_rev]; omega
  refine ⟨hj, ?_⟩
  have he : (⟨j.val + 1, hj⟩ : Fin n) = i.rev := by
    apply Fin.ext
    simp only [j, Fin.val_rev]
    omega
  change -D.col (⟨i.val + 1, hi⟩ : Fin n).rev - -D.row i.rev =
    D.row ⟨j.val + 1, hj⟩ - D.col j
  rw [he]
  dsimp [j]
  ring

/-- The complete ordered profile characterizes common translation. -/
theorem translationEquivalent_iff_profile (D E : BetaDiagram n) :
    D.TranslationEquivalent E ↔
      (∀ i, D.rowLength i = E.rowLength i) ∧
      (∀ (i : Fin n) (hi : i.val + 1 < n), D.overlap i hi = E.overlap i hi) := by
  constructor
  · intro h
    exact ⟨h.rowLength_eq, h.overlap_eq⟩
  · rintro ⟨hr, ho⟩
    exact D.translationEquivalent_of_profile E hr ho

end SkewCofactorIndependence.BetaDiagram
