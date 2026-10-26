/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.NonVNormalization
import SkewGluing.CornerTransport

/-!
# The non-V rectangle child

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:non-v-child`).

The literal two-by-three rectangle has the literal two-cell row as its interior.
Corner transport gives its actual composed child and both stated spans.

Sorry-free.
-/

namespace SkewCornerDescent
open SkewGluing SkewGluing.MarkedInner

/-- The outer rectangle `(3,3)`, with its southwest cell at the origin. -/
def nonVRectangle : Diagram := {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)}

/-- The literal rectangle is connected and skew. -/
theorem nonVRectangle_connected : IsConnectedSkew nonVRectangle := by decide

/-- Its actual southeast interior is the canonical two-cell row. -/
theorem nonVRectangle_interior : diagramInterior nonVRectangle = horizontalRow 2 := by
  decide

/-- The rectangle has four occupied content diagonals. -/
theorem nonVRectangle_span : span nonVRectangle = 4 := by decide

/-- The canonical child row has two occupied content diagonals. -/
theorem nonVRow_span : span (horizontalRow 2) = 2 := by decide

/-- All non-cap transport powers vanish for this rectangle. -/
theorem nonVRectangle_scalar (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).transportScalar (nonVMark_isLegal k hk) nonVRectangle = hh 1 ^ 2 := by
  have hr : (nonVRectangle.image Prod.fst).card = 2 := by decide
  have hc : (nonVRectangle.image Prod.snd).card = 3 := by decide
  have hir : ((diagramInterior nonVRectangle).image Prod.fst).card = 1 := by decide
  have hic : ((diagramInterior nonVRectangle).image Prod.snd).card = 2 := by decide
  simp [transportScalar, hr, hc, hir, hic, nonVMark_normalC k hk,
    nonVMark_normalTheta k hk]

/-- The actual connected interior produces exactly one actual composed child. -/
theorem nonVRectangle_childProduct (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).childProduct (nonVMark_isLegal k hk) nonVRectangle
      nonVRectangle_connected.1 =
    cellSchur ((nonVMark k).compose (horizontalRow 2))
      ((nonVMark_isLegal k hk).connected_compose (by decide)).1 := by
  have hic : IsConnectedSkew (diagramInterior nonVRectangle) := by decide
  have hi := hic.2
  have he := edgeComponents_eq_singleton hi
  have hm : diagramInterior nonVRectangle ∈ edgeComponents (diagramInterior nonVRectangle) := by
    rw [he]; simp
  have ha : (edgeComponents (diagramInterior nonVRectangle)).attach =
      {⟨diagramInterior nonVRectangle, hm⟩} := by
    ext C
    simp only [Finset.mem_attach, Finset.mem_singleton, Subtype.ext_iff, true_iff]
    simpa only [he, Finset.mem_singleton] using C.2
  unfold childProduct
  rw [ha, Finset.prod_singleton]
  exact cellSchur_congr (congrArg (nonVMark k).compose nonVRectangle_interior) _ _

/-- The actual rectangle composition has the displayed nontrivial child cofactor. -/
theorem nonVMark_rectangle_cofactor (k : ℕ) (hk : 3 ≤ k) :
    cellSchur (diagramInterior ((nonVMark k).compose nonVRectangle))
      ((nonVMark_isLegal k hk).connected_compose nonVRectangle_connected).1.interior =
    hh 1 ^ 2 * cellSchur ((nonVMark k).compose (horizontalRow 2))
      ((nonVMark_isLegal k hk).connected_compose (by decide)).1 := by
  rw [(nonVMark_isLegal k hk).corner_transport nonVRectangle_connected (by decide),
    nonVRectangle_scalar k hk, nonVRectangle_childProduct k hk]

/-- The spans are those of the actual parent and child diagrams, not supplied polynomials. -/
theorem nonVMark_rectangle_spans (k : ℕ) (hk : 3 ≤ k) :
    (span ((nonVMark k).compose nonVRectangle) : ℤ) = 4 * k + 2 ∧
    (span ((nonVMark k).compose (horizontalRow 2)) : ℤ) = 2 * k + 2 := by
  constructor
  · rw [span_compose nonVRectangle_connected (nonVMark_isLegal k hk),
      nonVRectangle_span, nonVMark_period, nonVMark_width]
    norm_num
  · rw [span_compose (by decide : IsConnectedSkew (horizontalRow 2))
      (nonVMark_isLegal k hk), nonVRow_span, nonVMark_period, nonVMark_width]
    norm_num

end SkewCornerDescent
