/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileJoinBetas
import SkewJacobiNegative.RestorationGeometry

/-!
# Literal beta supports under joins

Formalizes the full-list union operations used in `eq:thin-beta-lists`
of `shields-2026-skew-class-inflation.tex`.  The union formulas describe
the actual strict beta lists, not a canceled realization.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Image of an ordered concatenation, with an arbitrary transformation of its first word. -/
theorem image_joined_word {n m : ℕ} (f : Fin (n + 1) → ℤ) (g : Fin (m + 1) → ℤ)
    (φ : ℤ → ℤ) :
    Finset.univ.image (fun i : Fin (n + m + 2) =>
      if h : i.val < n + 1 then φ (f ⟨i.val, h⟩)
      else g ⟨i.val - (n + 1), by have := i.isLt; omega⟩) =
        (Finset.univ.image f).image φ ∪ Finset.univ.image g := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : i.val < n + 1
    · left
      refine ⟨f ⟨i.val, h⟩, ⟨⟨i.val, h⟩, rfl⟩, ?_⟩
      simpa only [dite_eq_left h] using hi
    · right
      exact ⟨⟨i.val - (n + 1), by have := i.isLt; omega⟩,
        by simpa only [dite_eq_right h] using hi⟩
  · rintro (⟨y, ⟨i, hi⟩, hφ⟩ | ⟨i, hi⟩)
    · refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_⟩
      simp only [dite_eq_left i.isLt]
      exact (congrArg φ hi).trans hφ
    · refine ⟨⟨n + 1 + i.val, by have := i.isLt; omega⟩, ?_⟩
      rw [dite_eq_right (by change ¬ n + 1 + i.val < n + 1; omega)]
      have he : (⟨n + 1 + i.val - (n + 1), by have := i.isLt; omega⟩ : Fin (m + 1)) = i :=
        Fin.ext (by simp)
      rw [he]
      exact hi

namespace Profile

variable {n m : ℕ}

/-- Joining translates the first full upper beta set and takes the literal union with the second. -/
theorem join_rowSet (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    (join P Q d hP hQ).toBetaDiagram.rowSet =
      P.toBetaDiagram.rowSet.image (fun x => x + Q.xi 0 - d) ∪ Q.toBetaDiagram.rowSet := by
  change Finset.univ.image (join P Q d hP hQ).xi = _
  rw [(join_beta P Q d hP hQ).1]
  exact image_joined_word P.xi Q.xi (fun x => x + Q.xi 0 - d)

/-- The same whole-block translation acts on the full lower beta set. -/
theorem join_colSet (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    (join P Q d hP hQ).toBetaDiagram.colSet =
      P.toBetaDiagram.colSet.image (fun x => x + Q.xi 0 - d) ∪ Q.toBetaDiagram.colSet := by
  change Finset.univ.image (join P Q d hP hQ).zeta = _
  rw [(join_beta P Q d hP hQ).2]
  exact image_joined_word P.zeta Q.zeta (fun x => x + Q.xi 0 - d)

/-- The span of a literal join is the sum of the spans minus its one joining gap. -/
theorem join_span (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    (join P Q d hP hQ).xi 0 = P.xi 0 + Q.xi 0 - d := by
  rw [congrFun (join_beta P Q d hP hQ).1 0]
  simp [joinUpper]

end Profile
end SkewClassInflation
