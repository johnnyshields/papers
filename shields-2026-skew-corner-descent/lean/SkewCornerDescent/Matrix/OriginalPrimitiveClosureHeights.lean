/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrimitiveClasses
import SkewCornerDescent.Matrix.OriginalWindowActiveClasses
import SkewCornerDescent.Matrix.OriginalClosureCapSum
import SkewCornerDescent.Matrix.OriginalInternalCyclicProfiles
import SkewCornerDescent.Matrix.OriginalAmalgamationSpan

/-!
# Actual primitive interval heights include the omitted closure gap

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
At selected multiplicity one every actual internal class is active.
The original rational residue classifier therefore identifies every
internal height with the genuine closure height. The actual closure cap
sum then includes the omitted gap, giving its full constant cyclic period.
No gap period or omitted-height equality is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
noncomputable local instance primitiveClosureHeightsRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Exact rational matching in a primitive chart gives the same full height
at every internal position and at the omitted actual closure position. -/
theorem originalPrimitive_closure_heights {n m an hn : ℕ}
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
    [NeZero (originalSelectedCount (hD := hD) P)] :
    let K := originalHessenbergDistance (hD := hD) P 0 0 +
      originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _)
    (∀ i : Fin (originalSelectedCount (hD := hD) P - 1),
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) = K) ∧
      (∀ i, c.originalCompletedGap P i = K - (c.top : ℤ)) ∧
      Function.Periodic (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
        (1 : ZMod (originalSelectedCount (hD := hD) P)) := by
  classical
  let K := originalHessenbergDistance (hD := hD) P 0 0 +
    originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _)
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hC : 0 < originalSelectedCount (hD := hD) W := by rw [hcountW]; exact ha
  have hmaxW := originalWindow_component_span P W A q v u z hv hwindow hW hA
    (c.top : ℕ) hmax
  obtain ⟨label, hlabels⟩ := (c.originalWindow_active_classes P W H q v z h hwindow hW hH
    (fun x hx => privateDiagonal_avoids_interior hcutq hx)
    (fun x hx => privateDiagonal_avoids_interior hcutLq hx) hC hmax hmaxW Λ b a (b-a)
    (by omega) hKU hKW p₀ p₁ hpq hdep).1
  have hcentral := c.originalHorizontalClosure_central_cap_sum P H h hH hB
  dsimp only at hcentral
  have hheight (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) = K := by
    have hactive := c.originalPrimitive_internal_active P W a b hcop hcountP i
    have hneq : a * (Finset.univ.filter fun j =>
        c.originalInternalResidue P i = c.originalInternalResidue P j).card ≠
      b * (Finset.univ.filter fun j =>
        c.originalInternalResidue P i = c.originalInternalResidue W j).card := by
      intro he
      apply hactive
      change (a : ℤ)*(Finset.univ.filter fun j =>
          c.originalInternalResidue P j = c.originalInternalResidue P i).card -
        (b : ℤ)*(Finset.univ.filter fun j =>
          c.originalInternalResidue W j = c.originalInternalResidue P i).card = 0
      have hp : (Finset.univ.filter fun j =>
          c.originalInternalResidue P j = c.originalInternalResidue P i) =
        (Finset.univ.filter fun j =>
          c.originalInternalResidue P i = c.originalInternalResidue P j) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact eq_comm
      have hw : (Finset.univ.filter fun j =>
          c.originalInternalResidue W j = c.originalInternalResidue P i) =
        (Finset.univ.filter fun j =>
          c.originalInternalResidue P i = c.originalInternalResidue W j) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact eq_comm
      rw [hp, hw, sub_eq_zero]
      exact_mod_cast he
    have he := (hlabels (originalInternalStateIndex P i) hneq).1
    exact he.trans hcentral
  have hgap (i : Fin (originalSelectedCount (hD := hD) P)) :
      c.originalCompletedGap P i = K - (c.top : ℤ) := by
    by_cases hi : i.val+1 = originalSelectedCount (hD := hD) P
    · rw [originalCompletedGap, ite_eq_left hi]
    · let j : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨i.val, by omega⟩
      rw [originalCompletedGap, ite_eq_right hi]
      exact congrArg (fun x : ℤ => x-(c.top : ℤ)) (hheight j)
  exact ⟨hheight, hgap, fun x => (hgap _).trans (hgap _).symm⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
