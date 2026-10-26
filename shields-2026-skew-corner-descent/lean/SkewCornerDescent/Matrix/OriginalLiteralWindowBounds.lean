/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowRows

/-!
# Actual target boundaries of a complete literal window profile

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Complete parent
cells place the whole target inside the translated content band. Private source cuts keep
both translated boundaries out of its actual interior. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- A complete literal window supplies the target band and both actual private boundaries. -/
theorem originalLiteralWindow_profile_bounds {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo hi : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi) :
    (∀ x ∈ Q.cells, lo + content v ≤ content x ∧ content x < hi + content v) ∧
      (∀ x ∈ diagramInterior Q.cells, content x ≠ lo + content v) ∧
      (∀ x ∈ diagramInterior Q.cells, content x ≠ hi + content v) := by
  have hc (x : ℤ × ℤ) : content (x - v) = content x - content v := by
    simp only [content, Prod.fst_sub, Prod.snd_sub]
    ring
  have hmem (x : ℤ × ℤ) (hx : x ∈ diagramInterior Q.cells) :
      x - v ∈ diagramInterior P.cells := by
    rw [hwindow, interior_translate, mem_translate,
      interior_content_filter P.cells (fun k => lo ≤ k ∧ k < hi), Finset.mem_filter] at hx
    exact hx.1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hwindow, mem_translate, Finset.mem_filter] at hx
    rw [hc] at hx
    omega
  · intro x hx he
    have h := hlo (x - v) (hmem x hx)
    rw [hc, he] at h
    omega
  · intro x hx he
    have h := hhi (x - v) (hmem x hx)
    rw [hc, he] at h
    omega

end SkewCornerDescent.Matrix
