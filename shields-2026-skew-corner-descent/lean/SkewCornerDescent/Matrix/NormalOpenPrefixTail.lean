/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalOpenPrefixCharges

/-!
# Complete copied-tail cancellation of the normal open charge

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Each of the five full local window sums splits at its actual copied tail.
No scalar response or frozen inverse is substituted for the matrix copy.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- A complete copied matrix tail cancels from the open normal charge, leaving
precisely its genuine prefix charge. The full inverse and onsite jets are unchanged. -/
theorem normalOpenOverlapCharge_copy_tail {N B T d : ℕ} {F : Type*} [Field F]
    (hd : 0 < d) (hdim : N = T + B) (hsize : d + 1 ≤ B)
    (M : Matrix (Fin N) (Fin N) (PowerSeries F))
    (P : Matrix (Fin B) (Fin B) (PowerSeries F))
    (hcopy : ∀ i j : Fin B,
      M ⟨T + i.val, by have := i.isLt; omega⟩ ⟨T + j.val, by have := j.isLt; omega⟩ = P i j)
    (δ : PowerSeries F → PowerSeries F) (b γ : F) :
    normalOpenOverlapCharge M δ b γ (d + 1) =
      normalOpenOverlapCharge P δ b γ (d + 1) +
        normalOpenOverlapPrefixCharge M δ b γ d T (by omega) := by
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
  have hsum (k : ℕ) (hk : k ≤ d + 1)
      (G : Matrix (Fin (k + 1)) (Fin (k + 1)) (PowerSeries F) → F) :
      (∑ s : Fin (N - k),
        G (contiguousMatrixWindow M (k + 1) ⟨s.val, by have := s.isLt; omega⟩)) =
      (∑ s : Fin (B - k),
        G (contiguousMatrixWindow P (k + 1) ⟨s.val, by have := s.isLt; omega⟩)) +
      (∑ s : Fin T,
        G (contiguousMatrixWindow M (k + 1) ⟨s.val, by have := s.isLt; omega⟩)) := by
    rw [contiguousMatrixWindow_sum_starts, contiguousMatrixWindow_sum_starts]
    exact contiguousMatrixWindow_sum_copy_tail (by omega) hdim M P hcopy G
  have hl := hsum (d + 1) (by omega) longF
  have hv := hsum d (by omega) vertexF
  have hi := hsum d (by omega) innerF
  have hle := hsum (d + 1) (by omega) leftF
  have hre := hsum (d + 1) (by omega) rightF
  rw [normalOpenOverlapCharge_windows hd M, normalOpenOverlapCharge_windows hd P]
  dsimp only [normalOpenOverlapPrefixCharge]
  dsimp only [longF, vertexF, innerF, leftF, rightF, w, ν] at hl hv hi hle hre
  linear_combination
    (-1 : F) ^ (d + 1) * b ^ (d + 1) * hl -
      (-1 : F) ^ d * b ^ d * γ * hv -
      (-1 : F) ^ (d + 1) * b ^ (d + 1) * γ * (hi + hle + hre)

end SkewCornerDescent.Matrix
