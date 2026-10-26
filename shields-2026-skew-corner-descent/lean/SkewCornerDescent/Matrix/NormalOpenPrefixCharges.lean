/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalOpenWindowCharges

/-!
# Complete finite prefix charges for the normal overlap expression

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The prefix retains the same five complete local matrix functionals as the
open charge, including both distinct exterior pair terms. It is a finite
window expression, not a definition of a logarithmic coefficient.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The full five-window normal charge restricted to the first genuine starts. -/
noncomputable def normalOpenOverlapPrefixCharge {N : ℕ} {F : Type*} [Field F]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F))
    (δ : PowerSeries F → PowerSeries F) (b γ : F) (d T : ℕ)
    (hT : T ≤ N - (d + 1)) : F :=
    let w := fun p : PowerSeries F => (PowerSeries.constantCoeff p)⁻¹
    let ν := fun p : PowerSeries F => PowerSeries.coeff 1 p * w p
    let longF := fun V : Matrix (Fin (d + 2)) (Fin (d + 2)) (PowerSeries F) =>
      PowerSeries.constantCoeff (δ (V 0 (Fin.last (d + 1)))) * ∏ k, w (V k k)
    let vertexF := fun V : Matrix (Fin (d + 1)) (Fin (d + 1)) (PowerSeries F) =>
      (∏ k, w (V k k)) * ∑ k, ν (V k k)
    let innerF := fun V : Matrix (Fin (d + 1)) (Fin (d + 1)) (PowerSeries F) =>
      (∏ k, w (V k k)) * ∑ t : Fin d,
        PowerSeries.constantCoeff (V t.castSucc t.succ) * w (V t.castSucc t.castSucc) *
          w (V t.succ t.succ)
    let leftF := fun V : Matrix (Fin (d + 2)) (Fin (d + 2)) (PowerSeries F) =>
      (∏ k : Fin (d + 1), w (V k.succ k.succ)) *
        (PowerSeries.constantCoeff (V 0 1) * w (V 0 0) * w (V 1 1))
    let rightF := fun V : Matrix (Fin (d + 2)) (Fin (d + 2)) (PowerSeries F) =>
      (∏ k : Fin (d + 1), w (V k.castSucc k.castSucc)) *
        (PowerSeries.constantCoeff (V (Fin.last d).castSucc (Fin.last (d + 1))) *
          w (V (Fin.last d).castSucc (Fin.last d).castSucc) *
          w (V (Fin.last (d + 1)) (Fin.last (d + 1))))
    (-1 : F) ^ (d + 1) * b ^ (d + 1) *
      (∑ s : Fin T, longF (contiguousMatrixWindow M (d + 2)
        ⟨s.val, by have := s.isLt; omega⟩)) -
    (-1 : F) ^ d * b ^ d * γ *
      (∑ s : Fin T, vertexF (contiguousMatrixWindow M (d + 1)
        ⟨s.val, by have := s.isLt; omega⟩)) -
    (-1 : F) ^ (d + 1) * b ^ (d + 1) * γ *
      ((∑ s : Fin T, innerF (contiguousMatrixWindow M (d + 1)
          ⟨s.val, by have := s.isLt; omega⟩)) +
        (∑ s : Fin T, leftF (contiguousMatrixWindow M (d + 2)
          ⟨s.val, by have := s.isLt; omega⟩)) +
        (∑ s : Fin T, rightF (contiguousMatrixWindow M (d + 2)
          ⟨s.val, by have := s.isLt; omega⟩)))

end SkewCornerDescent.Matrix
