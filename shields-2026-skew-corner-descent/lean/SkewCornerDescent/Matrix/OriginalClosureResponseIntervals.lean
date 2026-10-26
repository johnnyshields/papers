/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureIntervalCuts

/-!
# Complete original response intervals in literal closure copies

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The equivalence
retains all original removed positions between the actual selected cuts, including proper
minors at both boundaries and every unselected block. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A full remaining copy never identifies two original source positions. -/
theorem originalClosureRemainingCopy_injective {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) :
    Function.Injective (originalClosureRemainingCopy (hD := hD) P Q v hQ upper) := by
  intro i j hij
  cases upper
  · exact Sum.inr.inj ((originalClosureRemainingEquiv P Q v hQ).injective hij)
  · exact Sum.inl.inj ((originalClosureRemainingEquiv P Q v hQ).injective hij)

/-- Literal placement of every complete source response-interval position. -/
noncomputable def originalClosureResponseIntervalCopy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (i : OriginalResponseInterval (hD := hD) P (some b) (some d)) :
    OriginalResponseInterval (hD := hD) Q
      (some (originalHorizontalClosureSelectedCopy P Q v hQ upper b))
      (some (originalHorizontalClosureSelectedCopy P Q v hQ upper d)) := by
  have hi := (originalHorizontalClosure_interval_same_copy P Q v hQ upper b d i.1.1).mpr
    ⟨i.2, i.1.2⟩
  exact ⟨⟨originalClosureRemainingCopy P Q v hQ upper i.1.1, hi.2⟩, hi.1⟩

/-- No actual response-interval position is omitted by the literal source placement. -/
theorem originalClosureResponseIntervalCopy_surjective {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    Function.Surjective (originalClosureResponseIntervalCopy P Q v hQ upper b d) := by
  intro k
  obtain ⟨j, hj⟩ := (originalClosureRemainingEquiv P Q v hQ).surjective k.1.1
  have hk := And.intro k.2 k.1.2
  cases upper
  · rcases j with j | j
    · rw [originalClosureRemainingEquiv_upper] at hj
      rw [← hj] at hk
      exact False.elim (originalHorizontalClosure_interval_other_copy P Q v hQ false b d j hk)
    · rw [originalClosureRemainingEquiv_lower] at hj
      rw [← hj] at hk
      have hi := (originalHorizontalClosure_interval_same_copy P Q v hQ false b d j).mp hk
      refine ⟨⟨⟨j, hi.2⟩, hi.1⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hj)
  · rcases j with j | j
    · rw [originalClosureRemainingEquiv_upper] at hj
      rw [← hj] at hk
      have hi := (originalHorizontalClosure_interval_same_copy P Q v hQ true b d j).mp hk
      refine ⟨⟨⟨j, hi.2⟩, hi.1⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hj)
    · rw [originalClosureRemainingEquiv_lower] at hj
      rw [← hj] at hk
      exact False.elim (originalHorizontalClosure_interval_other_copy P Q v hQ true b d j hk)

/-- The complete retained original interval is exactly one complete source copy. -/
noncomputable def originalClosureResponseIntervalEquiv {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    OriginalResponseInterval (hD := hD) P (some b) (some d) ≃
      OriginalResponseInterval (hD := hD) Q
        (some (originalHorizontalClosureSelectedCopy P Q v hQ upper b))
        (some (originalHorizontalClosureSelectedCopy P Q v hQ upper d)) :=
  Equiv.ofBijective (originalClosureResponseIntervalCopy P Q v hQ upper b d)
    ⟨fun _ _ hij => Subtype.ext (Subtype.ext (originalClosureRemainingCopy_injective
      P Q v hQ upper (congrArg (fun i => i.1.1) hij))),
      originalClosureResponseIntervalCopy_surjective P Q v hQ upper b d⟩

/-- Reindexing the complete interval preserves both full endpoint lists by one common shift. -/
theorem originalHorizontalClosure_response_interval_endpoints {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (i : OriginalResponseInterval (hD := hD) P (some b) (some d)) :
    let e := originalClosureResponseIntervalEquiv P Q v hQ upper b d
    let w := originalClosureBlockDisplacement P upper
    originalResponseRows Q (e i).1.1 = originalResponseRows P i.1.1 + w.2 - w.1 ∧
    originalResponseCols Q (e i).1.1 = originalResponseCols P i.1.1 + w.2 - w.1 :=
  originalHorizontalClosure_remaining_endpoints P Q v hQ upper i.1.1

end SkewCornerDescent.Matrix.SelectedCoordinate
