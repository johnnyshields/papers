/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalRowHessian
import SkewCornerDescent.Matrix.OriginalResponseClasses

/-!
# Protected actual row classes have integer mixed jets

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
A class whose actual representative top exceeds both true-cap tops is an
actual internal response. The source supplies its full interval and integer
mixed-jet bound; no arbitrary affine row family is substituted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A protected actual row class inherits the full internal integer mixed
spectrum. The two cap exclusions locate its source representative, rather
than assuming an internal representative is available. -/
theorem originalResponseClass_row_hessian_bound {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1)
    (X : c.OriginalResponseClass P) (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    (hsum : (p : ℤ) + (q : ℤ) = (c.originalResponseClassTop P hB X : ℤ))
    (hleft : originalHessenbergDistance (hD := hD) P 0 0 < (p : ℤ) + (q : ℤ))
    (hright : originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) <
      (p : ℤ) + (q : ℤ)) :
    ∃ k : ℕ, k ≤ (if p = q then 1 else 2) ∧
      residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
        (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩ X.val) =
        -(if p = q then 2 else 1 : OtherField c.top) * (k : OtherField c.top) := by
  let j := c.originalResponseClassIndex P X
  have htop := c.originalHessenbergTop_coe P hB j j le_rfl
  change (c.originalResponseClassTop P hB X : ℤ) =
    originalHessenbergDistance (hD := hD) P j j at htop
  have hj0 : 0 < j.val := by
    by_contra hn
    have he : j = 0 := by
      apply Fin.ext
      change j.val = 0
      omega
    rw [he] at htop
    omega
  have hjB : j.val < originalSelectedCount (hD := hD) P := by
    by_contra hn
    have he : j = Fin.last _ := by
      apply Fin.ext
      change j.val = originalSelectedCount (hD := hD) P
      have hj : j.val < originalSelectedCount (hD := hD) P + 1 := j.isLt
      omega
    rw [he] at htop
    omega
  let i : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨j.val - 1, by omega⟩
  have hi : (⟨i.val + 1, by omega⟩ : Fin (originalSelectedCount (hD := hD) P + 1)) = j := by
    apply Fin.ext
    dsimp only [i]
    omega
  have hs : (p : ℤ) + (q : ℤ) = originalHessenbergDistance (hD := hD) P
      ⟨i.val + 1, by omega⟩ ⟨i.val + 1, by omega⟩ := by
    rw [hi]
    exact hsum.trans htop
  have hv : c.originalInternalResidue P i = X.val := by
    unfold originalInternalResidue
    rw [hi]
    exact c.originalResponseClassIndex_spec P X
  obtain ⟨k, hk, hjet⟩ := c.originalInternal_row_hessian_bound P hmax hrows i p q hp hq hs
  rw [hv] at hjet
  exact ⟨k, hk, hjet⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
