/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedCoreWords
import SkewCornerDescent.TruncatedLinearCorePhase

/-!
# Proper-core phase rigidity on the original open source chain

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Actual internal response and gap periodicity produce mixed jets through the
raw source derivative. Complete literal windows supply the phase anchor, so
proper cores repeat without any assumption at the actual closure edge.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Source-selected proper-core jets repeat under an internal response and gap
period. Complete windows supply the anchor and the actual raw gradients supply
the mixed products; no cyclic closure-product identity is assumed.

**Differs from the paper's route.** The open chain uses its literal matched
window to give finite-order unit torsion, rather than closing the chain with
an as-yet unidentified omitted phase. -/
theorem originalSelectedCore_phase_jets {n m : ℕ} (P : Profile n) (W : Profile m)
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hdiff : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = r * d)
    (hresponse : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
      j.val = i.val + r → c.originalInternalResidue P i = c.originalInternalResidue P j)
    (hgap : ∀ i j : Fin (originalSelectedCount (hD := hD) P),
      j.val = i.val + r → j.val + 1 < originalSelectedCount (hD := hD) P →
        c.originalCompletedGap P i = c.originalCompletedGap P j) :
    ∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val + r →
      ∀ k, k < (c.top : ℕ) →
        (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
        (c.originalSelectedCoreRight P j).coeff k = (c.originalSelectedCoreRight P i).coeff k := by
  classical
  let L := originalSelectedCount (hD := hD) P
  have hrd : 0 < r * d := Nat.mul_pos hr hd
  have hwindowSize : r * d < L := by dsimp only [L]; omega
  let A : ℕ → PowerSeries (OtherField c.top) := fun i =>
    if hi : i < L then (c.originalSelectedCoreLeft P ⟨i, hi⟩ : PowerSeries (OtherField c.top))
    else 1
  let B : ℕ → PowerSeries (OtherField c.top) := fun i =>
    if hi : i < L then (c.originalSelectedCoreRight P ⟨i, hi⟩ : PowerSeries (OtherField c.top))
    else 1
  have hA (i) : PowerSeries.constantCoeff (A i) = 1 := by
    dsimp only [A]
    split_ifs with hi
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe]
      exact (c.originalSelectedCore_constants P ⟨i, hi⟩).1
    · exact map_one _
  have hB (i) : PowerSeries.constantCoeff (B i) = 1 := by
    dsimp only [B]
    split_ifs with hi
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe]
      exact (c.originalSelectedCore_constants P ⟨i, hi⟩).2
    · exact map_one _
  have hself (i) (hi : i < L) (k) (hk : k < (c.top : ℕ)) :
      PowerSeries.coeff k (A i * B i) = PowerSeries.coeff k (A 0 * B 0) := by
    simp only [A, B, dite_eq_left hi, dite_eq_left (show 0 < L by omega),
      ← Polynomial.coe_mul, Polynomial.coeff_coe]
    exact c.originalSelectedCore_self_products P ⟨i, hi⟩ ⟨0, by omega⟩ k hk
  have hedge (i) (hi : i + r + 1 < L) (k) (hk : k < (c.top : ℕ)) :
      PowerSeries.coeff k (A i * B (i + 1)) =
        PowerSeries.coeff k (A (i + r) * B (i + r + 1)) := by
    let a : Fin (L - 1) := ⟨i, by omega⟩
    let b : Fin (L - 1) := ⟨i + r, by omega⟩
    have hg := hgap ⟨i, by omega⟩ ⟨i + r, by omega⟩ rfl hi
    have hs : originalHessenbergDistance (hD := hD) P
        ⟨i + 1, by omega⟩ ⟨i + 1, by omega⟩ =
      originalHessenbergDistance (hD := hD) P
        ⟨i + r + 1, by omega⟩ ⟨i + r + 1, by omega⟩ := by
      simp only [originalCompletedGap,
        ite_eq_right (show i + 1 ≠ originalSelectedCount (hD := hD) P by omega),
        ite_eq_right (show i + r + 1 ≠ originalSelectedCount (hD := hD) P by omega)] at hg
      exact sub_left_injective hg
    have hp := c.originalSelectedCore_internal_products P a b hs (hresponse a b rfl) k hk
    simpa only [A, B, dite_eq_left (show i < L by omega),
      dite_eq_left (show i + 1 < L by omega), dite_eq_left (show i + r < L by omega),
      dite_eq_left hi,
      ← Polynomial.coe_mul, Polynomial.coeff_coe] using hp
  have hw (k) (_hk : k < (c.top : ℕ)) :
      PowerSeries.coeff k (A (r * d)) = PowerSeries.coeff k (A 0) := by
    have hp := (c.originalWindow_selected_core_words P W q u v hv hW hwindow hq hLq
      ⟨0, by omega⟩ ⟨r * d, hwindowSize⟩ (by simp only [hdiff, zero_add])).1
    simp only [A, dite_eq_left hwindowSize, dite_eq_left (show 0 < L by omega),
      Polynomial.coeff_coe]
    exact congrArg (fun p : Polynomial (OtherField c.top) => p.coeff k) hp
  have hp := SkewCornerDescent.truncated_linear_core_phase_periodic r d L (c.top : ℕ)
    hd hwindowSize A B hA hB hself hedge hw
  intro i j hji k hk
  have he := hp i.val (by rw [← hji]; exact j.isLt) k hk
  have hiL : i.val < L := i.isLt
  have hjL : j.val < L := j.isLt
  simpa only [A, B, hji.symm, dite_eq_left hiL, dite_eq_left hjL,
    Polynomial.coeff_coe] using he

end SkewCornerDescent.Matrix.SelectedCoordinate
