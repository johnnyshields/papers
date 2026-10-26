/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.PolynomialLaurentSubfield
import SkewCornerDescent.Matrix.OriginalInternalProfileSupport
import SkewCornerDescent.Matrix.OriginalCrossPrefixCharge

/-!
# Protected-generator support of complete directed profile charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual short-period spans bound every full inverse coupling, both profile
families, the genuine shifted cross charge, and the full self charge. Integer
resolving offsets include the negative regime. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual internal response omits every generator above its whole period. -/
theorem originalInternal_residue_mem_lower {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (H : ℕ+) (hNH : c.top < H)
    (hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ))
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    c.originalInternalResidue P i ∈ residueLowerField c.top H := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  have hspan : P.xi (originalRowSplitEquiv P (.inl (some (E a)))) -
      P.zeta (originalColSplitEquiv P (.inl (some (E b)))) < (H : ℤ) := by
    have h := (c.originalInternalDistance_short_period P r d hp i i le_rfl (by omega)).trans hheight
    change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P a.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P b.castSucc))) < _ at h
    rwa [originalHessenbergRows_succ, originalHessenbergCols_castSucc] at h
  have h := (c.originalLocalResponse_profiles_mem_lower P (some (E a)) (some (E b)) H hNH hspan).1
  have he := c.originalInternalResponseMatrix_selected_entry P i i
  change c.originalInternalResponseMatrix P i i =
    c.originalLocalResponse P (some (E a)) (some (E b)) at he
  rw [← he] at h
  exact h

/-- Every full directed cross-profile charge stays below the protected generator,
with all genuine shifted endpoints and residue inverses retained. -/
theorem originalCrossPrefixCharge_mem_lower {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (H : ℕ+) (hNH : c.top < H)
    (hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ))
    (m : ℕ) (J : ℕ+) (T : ℕ)
    (hT : T ≤ originalSelectedCount (hD := hD) P - 1 - m) :
    c.originalCrossPrefixCharge P m J T hT ∈ residueLowerField c.top H := by
  classical
  unfold originalCrossPrefixCharge
  apply Subfield.sum_mem
  intro s _
  dsimp only
  apply Subfield.mul_mem
  · apply polynomial_laurent_coeff_mem_subfield
    apply polynomial_product_coeff_mem_subfield
    · intro k
      exact (c.originalInternal_profiles_mem_lower P r d hn hp H hNH hheight _ k).1
    · intro k
      exact (c.originalInternal_profiles_mem_lower P r d hn hp H hNH hheight _ k).2
  · apply Subfield.inv_mem
    exact c.originalInternal_residue_mem_lower P r d hn hp H hNH hheight _

/-- The full self charge has the same strict support bound. -/
theorem originalSelfPrefixCharge_mem_lower {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (H : ℕ+) (hNH : c.top < H)
    (hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ))
    (J : ℕ+) (T : ℕ) (hT : T ≤ originalSelectedCount (hD := hD) P - 1) :
    c.originalSelfPrefixCharge P J T hT ∈ residueLowerField c.top H := by
  have h := c.originalCrossPrefixCharge_mem_lower P r d hn hp H hNH hheight 0 J T
    (by omega)
  simpa only [originalCrossPrefixCharge, originalSelfPrefixCharge, Nat.add_zero] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
