/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalAmalgamationWord
import SkewCornerDescent.Matrix.OriginalTranslatedGaps

/-!
# The actual amalgamation's completed geometric gap word

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:original-transfer`).
Complete literal end windows preserve both true exterior caps and every internal gap.
The union selected inventory determines the word offset. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

include c

omit c in
/-- The normalized literal amalgamation preserves the original exterior cap distances. -/
theorem originalAmalgamation_cap_distances (c : SelectedCoordinate D hD) {n m : ℕ}
    (P : Profile n) (A : Profile m) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    originalHessenbergDistance (hD := hD) A 0 0 =
        originalHessenbergDistance (hD := hD) P 0 0 ∧
      originalHessenbergDistance (hD := hD) A (Fin.last _) (Fin.last _) =
        originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) := by
  classical
  have hcuts := originalAmalgamation_private_end_cuts P A q v u hq hv hwindow hA hcutq hcutLq
  obtain ⟨hleft, hright⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  have hupper : P.cells = translate (u - v)
      (A.cells.filter fun x => q ≤ content x ∧ content x < A.xi 0) := by
    apply translate_injective v
    rw [translate_translate]
    have he : v + (u - v) = u := by abel
    rw [he]
    exact hright.symm
  have hc := originalLiteralWindow_selected_count_le (hD := hD) A P q (A.xi 0)
    (u - v) hupper (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.2)
  have hBA : 0 < originalSelectedCount (hD := hD) A := by omega
  obtain ⟨hu, hwidth⟩ := originalAmalgamation_profile_extrema P A q v u hq hv hA
  constructor
  · obtain ⟨a, ha, _, he⟩ := originalWindow_restriction_selected_rank A P q (u - v)
      hupper (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.2) ⟨0, hB⟩
    have ha0 : a = ⟨0, hBA⟩ := Fin.ext ha
    rw [ha0] at he
    have hz := originalSelected_minContent_of_translated_cells A P
      (originalSelectedEnumeration A ⟨0, hBA⟩)
      (originalSelectedEnumeration P ⟨0, hB⟩) (u - v) 0
      (by simpa only [SkewGluing.translate_zero] using he.symm)
    rw [originalHessenbergDistance_first A hBA, originalHessenbergDistance_first P hB]
    unfold originalFirstCapDistance
    have huv : content (u - v) = -q := by
      simp only [content, Prod.fst_sub, Prod.snd_sub] at hu hv ⊢
      omega
    rw [huv] at hz
    simp only [content, Prod.fst_zero, Prod.snd_zero, sub_self, add_zero] at hz
    omega
  · let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    obtain ⟨a, ha, _, he⟩ := originalWindow_lower_restriction_selected_rank A P q u
      hleft.symm (fun x hx => (hcuts x hx).1) (fun x hx => (hcuts x hx).2.2.1) last
    have halast : a = ⟨originalSelectedCount (hD := hD) A - 1, by omega⟩ := by
      apply Fin.ext
      change a.val = originalSelectedCount (hD := hD) A - 1
      dsimp only [last] at ha
      omega
    rw [halast] at he
    have hz := originalSelected_minContent_of_translated_cells A P
      (originalSelectedEnumeration A ⟨originalSelectedCount (hD := hD) A - 1, by omega⟩)
      (originalSelectedEnumeration P last) u 0
      (by simpa only [SkewGluing.translate_zero] using he.symm)
    have hpa := c.originalSelected_endpoint_distance P (originalSelectedEnumeration P last)
    have haa := c.originalSelected_endpoint_distance A
      (originalSelectedEnumeration A ⟨originalSelectedCount (hD := hD) A - 1, by omega⟩)
    rw [originalHessenbergDistance_last A hBA, originalHessenbergDistance_last P hB]
    unfold originalLastCapDistance
    rw [P.zeta_last, A.zeta_last]
    rw [hu] at hz
    simp only [content, Prod.fst_zero, Prod.snd_zero, sub_self, add_zero] at hz
    dsimp only [last] at hpa hz
    omega

/-- The completed union gap word is the source prefix followed by the complete source
cycle. Its final entry retains both actual exterior caps. -/
theorem originalAmalgamation_completed_gap_word {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W) :
    ∃ hcount : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hinventory : originalSelectedCount (hD := hD) A +
      originalSelectedCount (hD := hD) W = 2 * originalSelectedCount (hD := hD) P,
      ∀ i : Fin (originalSelectedCount (hD := hD) A),
        c.originalCompletedGap A i =
          if hi : i.val < originalSelectedCount (hD := hD) P -
              originalSelectedCount (hD := hD) W then
            c.originalCompletedGap P ⟨i.val, by omega⟩
          else c.originalCompletedGap P
            ⟨i.val - (originalSelectedCount (hD := hD) P -
              originalSelectedCount (hD := hD) W), by have := i.isLt; omega⟩ := by
  classical
  obtain ⟨hc, hinv, _⟩ := c.originalAmalgamation_internal_word P W A q v u z
    hq hv hwindow hW hA hcutq hcutLq hC
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  have hBA : 0 < originalSelectedCount (hD := hD) A := by omega
  have hshift : originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P =
      originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W := by omega
  have hcuts := originalAmalgamation_private_end_cuts P A q v u hq hv hwindow hA hcutq hcutLq
  obtain ⟨hleft, hright⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  have hupper : P.cells = translate (u - v)
      (A.cells.filter fun x => q ≤ content x ∧ content x < A.xi 0) := by
    apply translate_injective v
    rw [translate_translate]
    have he : v + (u - v) = u := by abel
    rw [he]
    exact hright.symm
  refine ⟨hc, hinv, fun i => ?_⟩
  split_ifs with hi
  · have hiP : i.val + 1 < originalSelectedCount (hD := hD) P := by omega
    let j : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨i.val, by omega⟩
    obtain ⟨a, ha, he⟩ := c.originalWindow_upper_internal_distance A P q (u - v)
      hupper (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.2) j
    have hai : a = i := Fin.ext ha
    rw [hai] at he
    simp only [originalCompletedGap, show i.val + 1 ≠
      originalSelectedCount (hD := hD) A by omega, ite_false,
      show i.val + 1 ≠ originalSelectedCount (hD := hD) P by omega]
    exact congrArg (fun t : ℤ => t - (c.top : ℤ)) he.symm
  · let p : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨i.val - (originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W), by have := i.isLt; omega⟩
    by_cases hlast : i.val + 1 = originalSelectedCount (hD := hD) A
    · have hp : p.val + 1 = originalSelectedCount (hD := hD) P := by
        dsimp only [p]
        omega
      have hcap := c.originalAmalgamation_cap_distances P A q v u
        hq hv hwindow hA hcutq hcutLq hB
      change c.originalCompletedGap A i = c.originalCompletedGap P p
      simp only [originalCompletedGap, hlast, hp, ite_true, hcap.1, hcap.2]
    · have hp : p.val + 1 < originalSelectedCount (hD := hD) P := by
        dsimp only [p]
        have := i.isLt
        omega
      let j : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨p.val, by omega⟩
      obtain ⟨a, ha, he⟩ := c.originalWindow_lower_internal_distance A P q u hleft.symm
        (fun x hx => (hcuts x hx).1) (fun x hx => (hcuts x hx).2.2.1) j
      have hai : a = i := by
        apply Fin.ext
        dsimp only [j, p] at ha
        omega
      rw [hai] at he
      change c.originalCompletedGap A i = c.originalCompletedGap P p
      simp only [originalCompletedGap, hlast, ite_false,
        show p.val + 1 ≠ originalSelectedCount (hD := hD) P by omega]
      exact congrArg (fun t : ℤ => t - (c.top : ℤ)) he.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
