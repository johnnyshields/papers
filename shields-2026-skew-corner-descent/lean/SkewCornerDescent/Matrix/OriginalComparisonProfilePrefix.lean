/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationEndpointProfiles
import SkewCornerDescent.Matrix.OriginalClosureEndpointProfiles
import SkewCornerDescent.Matrix.OriginalInternalSelfJet

/-!
# The actual amalgamation and ordinary closure share the whole source prefix

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The full literal source copy identifies each complete incoming and outgoing
endpoint polynomial in both comparison diagrams. Every original source
internal position is included, even when it is the last shared position.
No comparison of just response values is substituted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete original endpoint-profile prefixes agree in the actual union
and either actual ordinary closure, with both count bounds produced. -/
theorem originalComparison_shared_profile_prefix {n m s : ℕ}
    (P : Profile n) (A : Profile m) (O : Profile s)
    (q : ℤ) (v u zO : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hO : originalHorizontalClosure P = translate zO O.cells ∨
      originalVerticalClosure P = translate zO O.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q)) :
    ∃ hc : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hCO : originalSelectedCount (hD := hD) O = 2 * originalSelectedCount (hD := hD) P,
    ∀ i : Fin (originalSelectedCount (hD := hD) P - 1),
      c.originalInternalEndpointProfiles A ⟨i.val, by have := i.isLt; omega⟩ =
        c.originalInternalEndpointProfiles O ⟨i.val, by have := i.isLt; omega⟩ := by
  obtain ⟨hc, ha⟩ := c.originalAmalgamation_endpoint_polynomials P A q v u hq hv hwindow hA
    (fun x hx => privateDiagonal_avoids_interior hcutq hx)
    (fun x hx => privateDiagonal_avoids_interior hcutLq hx)
  obtain ⟨hCO, ho⟩ := c.originalClosure_endpoint_polynomials P O zO hO
  refine ⟨hc, hCO, ?_⟩
  intro i
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  have hap := ha true a b
  have hop := ho true a b
  simp only [ite_true, zero_add] at hap hop
  exact Prod.ext (hap.1.trans hop.1.symm) (hap.2.trans hop.2.symm)

end SkewCornerDescent.Matrix.SelectedCoordinate
