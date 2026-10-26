/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureCapCuts

/-!
# Full remaining-index equivalence for both literal exterior caps

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Actual cap intervals
include every unselected block and the selected boundary's proper minor. The opposite
copy has no retained position inside either cap. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Literal placement of every complete source exterior-cap position. -/
noncomputable def originalClosureCapIntervalCopy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (i : OriginalResponseInterval (hD := hD) P
      (originalClosureCapLeft upper b) (originalClosureCapRight upper b)) :
    OriginalResponseInterval (hD := hD) Q
      (originalClosureCapLeft upper (originalHorizontalClosureSelectedCopy P Q v hQ upper b))
      (originalClosureCapRight upper (originalHorizontalClosureSelectedCopy P Q v hQ upper b)) := by
  have hi := (originalHorizontalClosure_cap_same_copy P Q v hQ upper b i.1.1).mpr
    ⟨i.2, i.1.2⟩
  exact ⟨⟨originalClosureRemainingCopy P Q v hQ upper i.1.1, hi.2⟩, hi.1⟩

/-- Every actual exterior-cap position comes from its complete source cap. -/
theorem originalClosureCapIntervalCopy_surjective {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    Function.Surjective (originalClosureCapIntervalCopy P Q v hQ upper b) := by
  intro k
  obtain ⟨j, hj⟩ := (originalClosureRemainingEquiv P Q v hQ).surjective k.1.1
  have hk := And.intro k.2 k.1.2
  cases upper
  · rcases j with j | j
    · rw [originalClosureRemainingEquiv_upper] at hj
      rw [← hj] at hk
      exact False.elim (originalHorizontalClosure_cap_other_copy P Q v hQ false b j hk)
    · rw [originalClosureRemainingEquiv_lower] at hj
      rw [← hj] at hk
      have hi := (originalHorizontalClosure_cap_same_copy P Q v hQ false b j).mp hk
      refine ⟨⟨⟨j, hi.2⟩, hi.1⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hj)
  · rcases j with j | j
    · rw [originalClosureRemainingEquiv_upper] at hj
      rw [← hj] at hk
      have hi := (originalHorizontalClosure_cap_same_copy P Q v hQ true b j).mp hk
      refine ⟨⟨⟨j, hi.2⟩, hi.1⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hj)
    · rw [originalClosureRemainingEquiv_lower] at hj
      rw [← hj] at hk
      exact False.elim (originalHorizontalClosure_cap_other_copy P Q v hQ true b j hk)

/-- Each complete literal exterior cap is exactly its complete source cap. -/
noncomputable def originalClosureCapIntervalEquiv {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    OriginalResponseInterval (hD := hD) P
      (originalClosureCapLeft upper b) (originalClosureCapRight upper b) ≃
      OriginalResponseInterval (hD := hD) Q
        (originalClosureCapLeft upper (originalHorizontalClosureSelectedCopy P Q v hQ upper b))
        (originalClosureCapRight upper (originalHorizontalClosureSelectedCopy P Q v hQ upper b)) :=
  Equiv.ofBijective (originalClosureCapIntervalCopy P Q v hQ upper b)
    ⟨fun _ _ hij => Subtype.ext (Subtype.ext (originalClosureRemainingCopy_injective
      P Q v hQ upper (congrArg (fun i => i.1.1) hij))),
      originalClosureCapIntervalCopy_surjective P Q v hQ upper b⟩

/-- Complete exterior-cap endpoint lists have the actual common affine copy shift. -/
theorem originalHorizontalClosure_cap_interval_endpoints {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (i : OriginalResponseInterval (hD := hD) P
      (originalClosureCapLeft upper b) (originalClosureCapRight upper b)) :
    let e := originalClosureCapIntervalEquiv P Q v hQ upper b
    let w := originalClosureBlockDisplacement P upper
    originalResponseRows Q (e i).1.1 = originalResponseRows P i.1.1 + w.2 - w.1 ∧
    originalResponseCols Q (e i).1.1 = originalResponseCols P i.1.1 + w.2 - w.1 :=
  originalHorizontalClosure_remaining_endpoints P Q v hQ upper i.1.1

end SkewCornerDescent.Matrix.SelectedCoordinate
