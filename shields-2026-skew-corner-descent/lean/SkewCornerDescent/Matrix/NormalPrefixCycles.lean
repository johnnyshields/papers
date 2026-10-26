/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalFirstPrefixCharge
import SkewCornerDescent.FinitePeriodicWords

/-!
# Canonical full-normal cyclic prefix charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete diagonal and adjacent-entry words use the existing finite-cycle
convention. The crossing pair is its actual matrix entry; only its diagonal
endpoint is identified by the proved overlap period. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open scoped BigOperators

/-- The actual diagonal entries in the first complete overlap period. -/
def normalDiagonalCycle {N T : ℕ} {F : Type*} [NeZero T]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F)) (hT : T ≤ N) :
    ZMod T → PowerSeries F := finiteWordCycle (fun i => M i i) hT

/-- The adjacent-entry word keeps the genuine crossing edge at the last
period position; its second endpoint is not replaced by column zero. -/
def normalAdjacentCycle {N T : ℕ} {F : Type*} [NeZero T]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F)) (hT : T ≤ N - 1) :
    ZMod T → PowerSeries F := finiteWordCycle
      (fun i : Fin (N - 1) => M ⟨i.val, by have := i.isLt; omega⟩
        ⟨i.val + 1, by have := i.isLt; omega⟩) hT

/-- An overlap period identifies every full normal diagonal germ with its
canonical cyclic letter, without a smaller residue-period assumption. -/
theorem normalDiagonalCycle_eq {N T : ℕ} {F : Type*} [NeZero T]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F)) (hT : T ≤ N)
    (hp : ∀ i j : Fin N, j.val = i.val + T → M i i = M j j) (i : Fin N) :
    M i i = normalDiagonalCycle M hT (i.val : ZMod T) :=
  finiteWordCycle_eq _ hT hp i

/-- The same overlap transport holds for actual adjacent entries, including
their full inverse jets. -/
theorem normalAdjacentCycle_eq {N T : ℕ} {F : Type*} [NeZero T]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F)) (hT : T ≤ N - 1)
    (hp : ∀ i j : Fin (N - 1), j.val = i.val + T →
      M ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val + 1, by have := i.isLt; omega⟩ =
      M ⟨j.val, by have := j.isLt; omega⟩ ⟨j.val + 1, by have := j.isLt; omega⟩)
    (i : Fin (N - 1)) :
    M ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val + 1, by have := i.isLt; omega⟩ =
      normalAdjacentCycle M hT (i.val : ZMod T) :=
  finiteWordCycle_eq _ hT hp i

/-- The complete cyclic onsite-minus-adjacent-pair first-normal charge. -/
noncomputable def normalCyclicFirstCharge {T : ℕ} {F : Type*} [Field F] [NeZero T]
    (f q : ZMod T → PowerSeries F) (b : F) : F :=
  (∑ s : ZMod T, PowerSeries.coeff 1 (f s) * (PowerSeries.constantCoeff (f s))⁻¹) -
    b * ∑ s : ZMod T, PowerSeries.constantCoeff (q s) *
      (PowerSeries.constantCoeff (f s))⁻¹ *
      (PowerSeries.constantCoeff (f (s + 1)))⁻¹

/-- The entire first prefix is the cyclic onsite-minus-pair charge of its
actual normal words. Every directed position is retained once. -/
theorem normalFirstPrefixCharge_cyclic {N T : ℕ} {F : Type*} [Field F] [NeZero T]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F)) (b : F) (hT : T ≤ N - 1)
    (hp : ∀ i j : Fin N, j.val = i.val + T → M i i = M j j) :
    let f := normalDiagonalCycle M (show T ≤ N by omega)
    let q := normalAdjacentCycle M hT
    normalFirstPrefixCharge M b T hT =
      normalCyclicFirstCharge f q b := by
  dsimp only [normalCyclicFirstCharge]
  unfold normalFirstPrefixCharge
  dsimp only
  have hcast (s : Fin T) : ZMod.finEquiv T s = (s.val : ZMod T) := by
    cases T with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ T =>
      apply Fin.ext
      change s.val = s.val % (T + 1)
      exact (Nat.mod_eq_of_lt s.isLt).symm
  have hdiag (s : Fin T) :
      normalDiagonalCycle M (show T ≤ N by omega) (ZMod.finEquiv T s) =
        M ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val, by have := s.isLt; omega⟩ := by
    simp [hcast, normalDiagonalCycle, finiteWordCycle, Nat.mod_eq_of_lt s.isLt]
  have hpair (s : Fin T) :
      normalAdjacentCycle M hT (ZMod.finEquiv T s) =
        M ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val + 1, by have := s.isLt; omega⟩ := by
    simp [hcast, normalAdjacentCycle, finiteWordCycle, Nat.mod_eq_of_lt s.isLt]
  have hnext (s : Fin T) :
      normalDiagonalCycle M (show T ≤ N by omega) (ZMod.finEquiv T s + 1) =
        M ⟨s.val + 1, by have := s.isLt; omega⟩
          ⟨s.val + 1, by have := s.isLt; omega⟩ := by
    have he := normalDiagonalCycle_eq M (show T ≤ N by omega) hp
      ⟨s.val + 1, by have := s.isLt; omega⟩
    simpa [hcast] using he.symm
  congr 1
  · apply Fintype.sum_equiv (ZMod.finEquiv T).toEquiv
    intro s
    simp [contiguousMatrixWindow, Matrix.submatrix_apply, hdiag]
  · congr 1
    apply Fintype.sum_equiv (ZMod.finEquiv T).toEquiv
    intro s
    change _ = PowerSeries.constantCoeff (normalAdjacentCycle M hT (ZMod.finEquiv T s)) *
      (PowerSeries.constantCoeff (normalDiagonalCycle M (show T ≤ N by omega)
        (ZMod.finEquiv T s)))⁻¹ *
      (PowerSeries.constantCoeff (normalDiagonalCycle M (show T ≤ N by omega)
        (ZMod.finEquiv T s + 1)))⁻¹
    rw [hpair, hdiag, hnext]
    simp only [Fin.isValue, Fin.reduceLast, Finset.prod_inv_distrib,
      Fin.prod_univ_two, mul_inv_rev]
    let i : Fin N := ⟨s.val, by have := s.isLt; omega⟩
    let j : Fin N := ⟨s.val + 1, by have := s.isLt; omega⟩
    change PowerSeries.constantCoeff (M i j) *
      ((PowerSeries.constantCoeff (M j j))⁻¹ * (PowerSeries.constantCoeff (M i i))⁻¹) =
      PowerSeries.constantCoeff (M i j) * (PowerSeries.constantCoeff (M i i))⁻¹ *
        (PowerSeries.constantCoeff (M j j))⁻¹
    ring

end SkewCornerDescent.Matrix
