/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.LiteralWindowBands

/-!
# Literal tiling from equal complete boundary windows

Supports `shields-2026-skew-corner-descent.tex`, «The full-window boundary»
(`lem:boundary-full-window`).

Equality of the complete lower and upper cell windows propagates actual cells through
all content bands. The reconstruction retains rows and columns, not merely Schur functions.
Skewness, connectedness, and the ordinary joining edge are separate geometric obligations.

Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- The first literal content band of a southwest-normalized diagram. -/
def firstContentBand (D : Diagram) (δ : ℤ) : Diagram :=
  D.filter fun x => 0 ≤ content x ∧ content x < δ

/-- The lower complete window, with the last content band removed. -/
def lowerFullWindow (D : Diagram) (b : ℕ) (δ : ℤ) : Diagram :=
  D.filter fun x => 0 ≤ content x ∧ content x < ((b : ℤ) - 1) * δ

/-- The upper complete window, with the first content band removed. -/
def upperFullWindow (D : Diagram) (b : ℕ) (δ : ℤ) : Diagram :=
  D.filter fun x => δ ≤ content x ∧ content x < (b : ℤ) * δ

/-- Equal complete windows identify membership across each eligible literal translation. -/
theorem fullWindow_step {D : Diagram} {b : ℕ} {δ : ℤ} {v x : ℤ × ℤ}
    (hv : content v = δ)
    (hwindow : upperFullWindow D b δ = translate v (lowerFullWindow D b δ))
    (hx : 0 ≤ content x ∧ content x < ((b : ℤ) - 1) * δ) :
    x + v ∈ D ↔ x ∈ D := by
  apply literalWindow_step (L := (b : ℤ) * δ) hv
  · simpa only [upperFullWindow, lowerFullWindow, sub_mul, one_mul] using hwindow
  · constructor <;> nlinarith [hx.1, hx.2]

/-- Every band is the literal translate of the first one, with the same displacement. -/
theorem fullWindow_iterate {D : Diagram} {b : ℕ} {δ : ℤ} {v : ℤ × ℤ}
    (hδ : 0 < δ) (hv : content v = δ)
    (hwindow : upperFullWindow D b δ = translate v (lowerFullWindow D b δ))
    (x : ℤ × ℤ) (hx : 0 ≤ content x ∧ content x < δ)
    (j : ℕ) (hj : j < b) :
    x + (j : ℤ) • v ∈ D ↔ x ∈ D := by
  apply literalWindow_iterate (L := (b : ℤ) * δ) hδ hv
  · simpa only [upperFullWindow, lowerFullWindow, sub_mul, one_mul] using hwindow
  · exact hx.1
  · have hjcast : (j : ℤ) + 1 ≤ (b : ℤ) := by exact_mod_cast hj
    nlinarith [hx.2]

/-- Complete equal boundary windows reconstruct every actual cell from the first band. -/
theorem fullWindow_cells_eq_copies {D : Diagram} {b : ℕ} {δ : ℤ} {v : ℤ × ℤ}
    (hb : 0 < b) (hδ : 0 < δ) (hv : content v = δ)
    (hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < (b : ℤ) * δ)
    (hwindow : upperFullWindow D b δ = translate v (lowerFullWindow D b δ)) :
    D = (Finset.range b).biUnion
      (fun j => translate ((j : ℤ) • v) (firstContentBand D δ)) := by
  have hbs : b - 1 + 1 = b := by omega
  have hcast : ((b - 1 : ℕ) : ℤ) + 1 = (b : ℤ) := by exact_mod_cast hbs
  have he := literalWindow_cells_eq_prefix_copies (k := b - 1)
    hδ hv hδ (le_refl δ)
    (by nlinarith : (b : ℤ) * δ = ((b - 1 : ℕ) : ℤ) * δ + δ)
    hbound (by
      simpa only [upperFullWindow, lowerFullWindow, sub_mul, one_mul] using hwindow)
  rw [← hbs, Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
  simpa only [firstContentBand, literalPrefix] using he

end SkewCornerDescent
