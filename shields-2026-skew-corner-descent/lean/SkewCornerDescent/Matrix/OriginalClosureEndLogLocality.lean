/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalEndLogLocality
import SkewCornerDescent.Matrix.OriginalClosureOrderedResponses
import SkewCornerDescent.Matrix.OriginalClosureCentralResponse

/-!
# Complete original closure endpoint logarithms

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal closure placements preserve complete original cap neighborhoods.
Endpoint condensation then transports all cap logarithmic jets below the source
selected count, including entries containing the chosen higher generator. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual closure retains every complete source entry in a left cap neighborhood
strictly shorter than the selected count. No neighborhood matching premise is supplied. -/
theorem originalHorizontalClosure_normal_left_neighborhood {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) P)
    (i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) :
    c.originalNormalExtension Q i j = c.originalNormalExtension P i j := by
  have hcount := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  let ip : Fin (originalSelectedCount (hD := hD) P + 1) := ⟨i, by omega⟩
  let jp : Fin (originalSelectedCount (hD := hD) P + 1) := ⟨j, by omega⟩
  let iq : Fin (originalSelectedCount (hD := hD) Q + 1) := ⟨i, by omega⟩
  let jq : Fin (originalSelectedCount (hD := hD) Q + 1) := ⟨j, by omega⟩
  have heq : c.originalHessenbergResponse Q iq jq = c.originalHessenbergResponse P ip jp := by
    let t : Fin (originalSelectedCount (hD := hD) P) := ⟨j, by omega⟩
    have htp : t.castSucc = jp := by apply Fin.ext; rfl
    have htq : (originalClosureSelectedIndex P Q v hQ true t).castSucc = jq := by
      apply Fin.ext
      simp only [originalClosureSelectedIndex, ite_true, zero_add, Fin.val_castSucc]
      rfl
    by_cases hz : i = 0
    · have hip : ip = 0 := Fin.ext hz
      have hiq : iq = 0 := Fin.ext hz
      rw [hip, hiq, ← htp, ← htq]
      exact originalHorizontalClosure_ordered_left_response c P Q v hQ t
    · let s : Fin (originalSelectedCount (hD := hD) P) := ⟨i - 1, by omega⟩
      have hsp : s.succ = ip := by apply Fin.ext; change i - 1 + 1 = i; omega
      have hsq : (originalClosureSelectedIndex P Q v hQ true s).succ = iq := by
        apply Fin.ext
        simp only [originalClosureSelectedIndex, ite_true, zero_add, Fin.val_succ]
        change i - 1 + 1 = i
        omega
      rw [← hsp, ← hsq, ← htp, ← htq]
      exact originalHorizontalClosure_ordered_response c P Q v hQ true s t
  have hip := c.originalNormalExtension_inside P ip jp
  have hiq := c.originalNormalExtension_inside Q iq jq
  change c.originalNormalExtension P i j = _ at hip
  change c.originalNormalExtension Q i j = _ at hiq
  rw [hip, hiq, heq]

/-- The complete actual horizontal closure and source have identical left-cap logarithmic
coefficients below the source selected count. All diagonal units and exact normal
subdiagonals are produced; every higher-generator boundary jet remains. -/
theorem originalHorizontalClosure_left_log_coeff {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) P) :
    PowerSeries.coeff k (leftCap (c.originalNormalExtension Q)
      (originalSelectedCount (hD := hD) Q)) =
    PowerSeries.coeff k (leftCap (c.originalNormalExtension P)
      (originalSelectedCount (hD := hD) P)) := by
  have hcount := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBP : 0 < originalSelectedCount (hD := hD) P := by omega
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  have hmaxQ := c.originalHorizontalClosure_profile_component_span P Q v hQ hmax
  rw [c.original_left_log_prefix_locality Q hBQ hmaxQ k (by omega),
    c.original_left_log_prefix_locality P hBP hmax k hk.le]
  rw [leftCap_congr (c.originalNormalExtension Q) (c.originalNormalExtension P) k
    (fun i j hi hj => c.originalHorizontalClosure_normal_left_neighborhood P Q v hQ k hk i j hi hj)]

/-- The actual lower closure copy retains every full source entry in a right cap window.
The original beta-rank translation supplies the shifted indices, including the global end. -/
theorem originalHorizontalClosure_normal_right_neighborhood {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) P)
    (i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) :
    let B := originalSelectedCount (hD := hD) P
    c.originalNormalExtension Q (B + (B - k + i)) (B + (B - k + j)) =
      c.originalNormalExtension P (B - k + i) (B - k + j) := by
  dsimp only
  let B := originalSelectedCount (hD := hD) P
  have hcount := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  let ip : Fin (B + 1) := ⟨B - k + i, by dsimp only [B] at *; omega⟩
  let jp : Fin (B + 1) := ⟨B - k + j, by dsimp only [B] at *; omega⟩
  let iq : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨B + (B - k + i), by dsimp only [B] at *; omega⟩
  let jq : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨B + (B - k + j), by dsimp only [B] at *; omega⟩
  have heq : c.originalHessenbergResponse Q iq jq = c.originalHessenbergResponse P ip jp := by
    let s : Fin B := ⟨B - k + i - 1, by dsimp only [B] at *; omega⟩
    have hsp : s.succ = ip := by
      apply Fin.ext
      change B - k + i - 1 + 1 = B - k + i
      dsimp only [B] at *
      omega
    have hsq : (originalClosureSelectedIndex P Q v hQ false s).succ = iq := by
      apply Fin.ext
      simp only [originalClosureSelectedIndex, Bool.false_eq_true, ite_false, Fin.val_succ]
      change B + (B - k + i - 1) + 1 = B + (B - k + i)
      dsimp only [B] at *
      omega
    by_cases hz : B - k + j = B
    · have hjp : jp = Fin.last B := Fin.ext hz
      have hjq : jq = Fin.last (originalSelectedCount (hD := hD) Q) := by
        apply Fin.ext
        change B + (B - k + j) = originalSelectedCount (hD := hD) Q
        dsimp only [B] at *
        omega
      rw [hjp, hjq, ← hsp, ← hsq]
      exact originalHorizontalClosure_ordered_right_response c P Q v hQ s
    · let t : Fin B := ⟨B - k + j, by dsimp only [B] at *; omega⟩
      have htp : t.castSucc = jp := by apply Fin.ext; rfl
      have htq : (originalClosureSelectedIndex P Q v hQ false t).castSucc = jq := by
        apply Fin.ext
        simp only [originalClosureSelectedIndex, Bool.false_eq_true, ite_false, Fin.val_castSucc]
        rfl
      rw [← hsp, ← hsq, ← htp, ← htq]
      exact originalHorizontalClosure_ordered_response c P Q v hQ false s t
  have hip := c.originalNormalExtension_inside P ip jp
  have hiq := c.originalNormalExtension_inside Q iq jq
  change c.originalNormalExtension P (B - k + i) (B - k + j) = _ at hip
  change c.originalNormalExtension Q (B + (B - k + i)) (B + (B - k + j)) = _ at hiq
  rw [hiq, hip, heq]

/-- Both full right-cap logarithmic coefficients agree below the source selected count.
Actual closure geometry supplies the complete shifted cap neighborhood and every unit. -/
theorem originalHorizontalClosure_right_log_coeff {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) P) :
    PowerSeries.coeff k (rightCap (c.originalNormalExtension Q) 0
      (originalSelectedCount (hD := hD) Q)) =
    PowerSeries.coeff k (rightCap (c.originalNormalExtension P) 0
      (originalSelectedCount (hD := hD) P)) := by
  let B := originalSelectedCount (hD := hD) P
  have hcount := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBP : 0 < originalSelectedCount (hD := hD) P := by omega
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  have hmaxQ := c.originalHorizontalClosure_profile_component_span P Q v hQ hmax
  rw [c.original_right_log_suffix_locality Q hBQ hmaxQ k
      (B + (B - k)) (by dsimp only [B] at *; omega),
    c.original_right_log_suffix_locality P hBP hmax k (B - k) (by dsimp only [B] at *; omega)]
  have he := rightCap_offsets_congr (c.originalNormalExtension Q) (c.originalNormalExtension P)
    (B + (B - k)) (B - k) k (fun i j hi hj => by
      have h := c.originalHorizontalClosure_normal_right_neighborhood P Q v hQ k hk i j hi hj
      simpa only [Nat.add_assoc] using h)
  rw [he]

end SkewCornerDescent.Matrix.SelectedCoordinate
