/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrimitiveClosureHeights
import SkewCornerDescent.Matrix.OriginalSelectedCoreMultiplePhase

/-!
# Complete actual proper-core profiles in a constant primitive chart

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The original active-class supplier produces the complete constant gap word.
Literal equal windows and the actual constant response then produce every
proper-core phase jet. The strict core degree bounds identify the complete
incoming and outgoing core polynomials at every selected occurrence.
No proper-core equality or gap period is an input. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
noncomputable local instance primitiveCoreProfilesRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Exact rational matching and a constant primitive source word produce
both complete proper-core profiles, including the final selected occurrence. -/
theorem originalPrimitive_constant_core_profiles {n m an hn : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile an) (H : Profile hn)
    (q : ℤ) (v u z h : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate h H.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : Nat.Coprime b a)
    (hcountP : originalSelectedCount (hD := hD) P = b)
    (hcountW : originalSelectedCount (hD := hD) W = a)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det = Λ^b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ) (fun j => W.zeta j.castSucc)).det = Λ^a)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (i₀ : Fin (originalSelectedCount (hD := hD) P - 1))
    (hconstant : ∀ i, c.originalInternalResidue P i = c.originalInternalResidue P i₀) :
    ∀ i : Fin (originalSelectedCount (hD := hD) P),
      c.originalSelectedCoreLeft P i = c.originalSelectedCoreLeft P 0 ∧
        c.originalSelectedCoreRight P i = c.originalSelectedCoreRight P 0 := by
  obtain ⟨_, hgap, _⟩ := c.originalPrimitive_closure_heights P W A H q v u z h hv hwindow hW
    hA hH hcutq hcutLq hmax Λ a b ha hab hcop hcountP hcountW hKU hKW p₀ p₁ hpq hdep
  have hC : 0 < originalSelectedCount (hD := hD) W := by rw [hcountW]; exact ha
  have hjets := c.originalSelectedCore_multiple_phase_jets P W q z v hv hW.symm hwindow
    hcutq hcutLq hC 1 (b-a) (by omega) (by omega)
    (by rw [hcountP, hcountW]; omega)
    (fun i j _ => (hconstant i).trans (hconstant j).symm)
    (fun i j _ _ => (hgap i).trans (hgap j).symm)
  intro i
  have hi (k : ℕ) (hk : k < (c.top : ℕ)) :=
    hjets i.val 0 i (by simp only [Fin.val_zero, zero_add, Nat.mul_one]) k hk
  constructor
  · ext k
    by_cases hk : k < (c.top : ℕ)
    · exact (hi k hk).1
    · exact (c.selected_core_left_coeff_of_top_le _ _ k (by omega)).trans
        (c.selected_core_left_coeff_of_top_le _ _ k (by omega)).symm
  · ext k
    by_cases hk : k < (c.top : ℕ)
    · exact (hi k hk).2
    · exact (c.selected_core_right_coeff_of_top_le _ _ k (by omega)).trans
        (c.selected_core_right_coeff_of_top_le _ _ k (by omega)).symm

end SkewCornerDescent.Matrix.SelectedCoordinate
