/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CofactorSchur
import SkewSchurReconstruction.TableauBridge

/-!
# Standard Young shapes for the finite boundary presentation

Formalizes the shape conventions of «Capped cofactors and admissible convex weights»
(`sec:coordinates`) in `shields-2026-skew-boundary-reconstruction.tex`.
The signed-index free determinant and the shared tableau Jacobi--Trudi theorem
are identified under the same boundaries.  Sorry-free.
-/

namespace SkewSchurReconstruction

/-- A finite antitone boundary interpreted as Mathlib's standard Young diagram. -/
def boundaryShape {n : ℕ} (f : Fin n → ℕ) (hf : Antitone f) : YoungDiagram :=
  YoungDiagram.ofRowLens (List.ofFn f) hf.sortedGE_ofFn

theorem boundaryShape_rowLen {n : ℕ} (f : Fin n → ℕ) (hf : Antitone f) (i : Fin n) :
    (boundaryShape f hf).rowLen i.val = f i := by
  have h := YoungDiagram.rowLen_ofRowLens
    (w := List.ofFn f) (hw := hf.sortedGE_ofFn) ⟨i.val, by simp⟩
  simpa [boundaryShape] using h

theorem boundaryShape_rowLen_outside {n : ℕ} (f : Fin n → ℕ) (hf : Antitone f)
    (i : ℕ) (hi : n ≤ i) : (boundaryShape f hf).rowLen i = 0 := by
  by_contra hne
  have hc : (i, 0) ∈ boundaryShape f hf :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
  obtain ⟨hil, _⟩ := YoungDiagram.mem_ofRowLens.mp hc
  simp only [List.length_ofFn] at hil
  omega

/-- Signed differences agree with the shared complete-index convention in the free ring. -/
theorem complete_sub_eq_jtCoeff (p q : ℕ) :
    complete ((p : ℤ) - q) = Shields.jtCoeff (fun k => complete (k : ℤ)) p q := by
  by_cases h : q ≤ p
  · have he : (p : ℤ) - q = ((p - q : ℕ) : ℤ) := by omega
    rw [he, Shields.jtCoeff, ite_eq_left h]
  · rw [complete_of_neg (by omega), Shields.jtCoeff, ite_eq_right h]

namespace Diagram

variable {n : ℕ}

/-- The standard outer Young shape. -/
def outerShape (X : Diagram n) : YoungDiagram := boundaryShape X.outer X.outer_antitone

/-- The standard inner Young shape, retaining the prescribed zero padding. -/
def innerShape (X : Diagram n) : YoungDiagram := boundaryShape X.inner X.inner_antitone

@[simp]
theorem outerShape_rowLen (X : Diagram n) (i : Fin n) :
    X.outerShape.rowLen i.val = X.outer i := boundaryShape_rowLen _ _ i

@[simp]
theorem innerShape_rowLen (X : Diagram n) (i : Fin n) :
    X.innerShape.rowLen i.val = X.inner i := boundaryShape_rowLen _ _ i

theorem innerShape_le_outerShape (X : Diagram n) : X.innerShape ≤ X.outerShape := by
  intro c hc
  obtain ⟨hi, hj⟩ := (YoungDiagram.mem_ofRowLens (w := List.ofFn X.inner)
    (hw := X.inner_antitone.sortedGE_ofFn) (c := c)).mp hc
  have hi' : c.1 < n := by simpa only [List.length_ofFn] using hi
  apply (YoungDiagram.mem_ofRowLens (w := List.ofFn X.outer)
    (hw := X.outer_antitone.sortedGE_ofFn)).mpr
  refine ⟨(by simpa only [List.length_ofFn] using hi'), ?_⟩
  have hj' : c.2 < X.inner ⟨c.1, hi'⟩ := by
    simpa only [List.getElem_ofFn] using hj
  have hout := hj'.trans (X.row_nonempty ⟨c.1, hi'⟩)
  simpa only [List.getElem_ofFn] using hout

/-- The actual diagram determinant is the shared free-generator Jacobi--Trudi determinant. -/
theorem schurFunction_eq_shared_jacobiTrudiDet (X : Diagram n) :
    X.schurFunction = Shields.jacobiTrudiDet (fun k => complete (k : ℤ))
      X.outerShape X.innerShape n := by
  rw [schurFunction_eq_jacobiTrudiDet, Shields.jacobiTrudiDet]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [jacobiTrudiMatrix, Matrix.of_apply, outerShape_rowLen, innerShape_rowLen]
  rw [← complete_sub_eq_jtCoeff]
  congr 1
  push_cast
  ring

/-- Every finite-alphabet specialization is the actual bounded skew-tableau generating function. -/
theorem tableauSpecialization_schurFunction {R : Type*} [CommRing R]
    (X : Diagram n) (b : ℕ) (β : ℕ → R) :
    tableauSpecialization b β X.schurFunction =
      Shields.skewSchur X.outerShape X.innerShape b β := by
  rw [schurFunction_eq_shared_jacobiTrudiDet]
  apply tableauSpecialization_jacobiTrudiDet
  · exact X.innerShape_le_outerShape
  · intro i hi
    exact boundaryShape_rowLen_outside _ _ i hi

end Diagram
end SkewSchurReconstruction
