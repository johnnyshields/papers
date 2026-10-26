/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalOnePositiveInventories
import SkewCornerDescent.Matrix.OriginalShortCoefficient

/-!
# The original short bound for one-positive signed support

Formalizes `shields-2026-skew-corner-descent.tex` (`cor:one-positive-short`,
`lem:two-support`). The actual signed inventory produces a nonzero short detector;
the original coefficient producer supplies its complete rational-defect coefficient.
The positive remainder and eligible short length are derived internally, including
the length-one exclusion. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

noncomputable local instance onePositiveShortRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Exactly one positive actual class and at least one negative class detect the
whole supplied original rational defect at the positive-remainder short order.
Arbitrarily many negative classes and dependent response functions are retained.
**Differs from the paper's route.** For `lem:two-support`, the general signed
logarithmic Jensen inequality replaces the two-point centered Taylor expansion.
The proof follows the paper's one-positive-support route. -/
theorem originalOnePositive_short {n m ℓ t : ℕ}
    (P : Profile n) (W : Profile ℓ) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin ℓ => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁)
    (p : c.OriginalResponseClass P)
    (hpositive : 0 < c.originalResponseClassExponent P W a b p)
    (hothers : ∀ X, X ≠ p → c.originalResponseClassExponent P W a b X ≤ 0)
    (hnegative : ∃ X, c.originalResponseClassExponent P W a b X < 0) :
    ∃ k s : ℕ, 0 < k ∧ 0 < s ∧ s < b - a ∧ b = k * (b - a) + s ∧
      2 ≤ r * s ∧ PowerSeries.coeff (r * s - 1)
        (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0 := by
  have hd : 0 < b - a := by omega
  obtain ⟨k, s, hk, hs, hsd, hbshape, _⟩ := positive_remainder_exists hd (by omega : b - a < b)
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  let : NeZero (r * (b - a)) := ⟨Nat.ne_of_gt (Nat.mul_pos hrpos hd)⟩
  let : NeZero (r * b) := ⟨Nat.ne_of_gt (Nat.mul_pos hrpos (by omega))⟩
  have hdiff : originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W =
      r * (b - a) := by rw [hcountP, hcountW, Nat.mul_sub_left_distrib]
  let : NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W) :=
    ⟨by rw [hdiff]; exact NeZero.ne _⟩
  obtain ⟨hperiod, hshort, _⟩ := c.originalOnePositive_inventories P W q z v hv hW.symm
    hwindow hcutq hcutLq hmax Λ b a r k s ha (by omega) hrpos hk hs hsd hbshape
    hr hKU hKW p hpositive hothers hnegative
  obtain ⟨hperiod', hdetect⟩ := c.originalShort_coefficient P W A Q q v u z w hq hv hwindow
    hW hA hQ hcutq hcutLq hmax Λ b a r k s ha hab hrpos hk hs hsd hbshape
    hr hKU hKW hp p₀ p₁ hpq hdep
  obtain ⟨hsize, hcoefficient⟩ := hdetect hshort
  have hstrict : s < b - a := by
    by_contra hnot
    have hsfull : s = b - a := by omega
    have hC : 0 < originalSelectedCount (hD := hD) W := by
      rw [hcountW]; exact Nat.mul_pos hrpos ha
    obtain ⟨hperiod'', hcounts, _⟩ := c.originalWindow_responseClass_defects P W q z v hv
      hW.symm hwindow hcutq hcutLq hC r (b - a) s k b a hrpos hs hk hbshape
      (by omega) hcountP hcountW
    let word := c.originalResponseClassWord P (r * (b - a)) hperiod''
    have heq (Y : c.OriginalResponseClass P) :
        c.originalResponseClassExponent P W a b Y =
          classDefect word 1 (b - a) s (r * s - 1) 0 Y := hcounts Y
    rw [hsfull] at heq
    obtain ⟨X, hX⟩ := hnegative
    have hXp : X ≠ p := by intro he; rw [he] at hX; omega
    have he := full_remainder_active_unique hrpos hd word
      (a := p) (b := X) (by rw [← heq p]; exact hpositive.ne')
      (by rw [← heq X]; exact hX.ne)
    exact hXp he.symm
  exact ⟨k, s, hk, hs, hstrict, hbshape, hsize, hcoefficient⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
