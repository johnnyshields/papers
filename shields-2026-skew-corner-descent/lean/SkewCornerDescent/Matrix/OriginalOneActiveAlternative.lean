/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowPositiveNullPeriod
import SkewCornerDescent.Matrix.OriginalManyActiveGeneral

/-!
# Actual one-active detection or periodic response and gaps

Supports `shields-2026-skew-corner-descent.tex` (`lem:positive-support`).
The original maximal-bin producer supplies the gap alternative. The original
coefficient producer converts failure to detect into full-period inventory
nullity, and complete literal counts force the actual completed response period.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

noncomputable local instance oneActiveAlternativeRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A single active actual class either detects the complete original defect
by the full-period order, or both complete response and gap words have the
selected multiplicity as period. No period or cyclic-count premise is assumed. -/
theorem originalOneActive_alternative {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
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
    (hcoprime : b.Coprime a) (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)] [NeZero (r * b)]
    [NeZero (r * (b - a))]
    (Δ : ℤ) (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ)
    (hqspan : q = ((b - a : ℕ) : ℤ) * Δ)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁)
    (active : c.OriginalResponseClass P)
    (hunique : ∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0) :
    PowerSeries.coeff (r * (b - a) - 1)
        (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0 ∨
      (Function.Periodic (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
        (r : ZMod (originalSelectedCount (hD := hD) P)) ∧
      ∃ hperiod : r * (b - a) ≤ originalSelectedCount (hD := hD) P - 1,
        Function.Periodic (closureWord (finiteWordCycle (n := r * (b - a))
          (c.originalInternalResidue P) hperiod) active.val (r * b)) (r : ZMod (r * b))) := by
  classical
  by_cases hdetect : PowerSeries.coeff (r * (b - a) - 1)
      (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0
  · exact Or.inl hdetect
  have hvanish := not_not.mp hdetect
  obtain ⟨M, K, hK, _, _, _, hmean, hstrict, hperiod⟩ :=
    c.originalMaximalBin_alternative P W A Q q v u z w hq hv hwindow hW hA hQ hcutq
      hcutLq hmax Λ b a r ha hab hrpos hcoprime hr hKU hKW Δ hspan hqspan p₀ p₁ hpq hdep
  have hM : M = q := by
    by_contra hne
    have hd := hstrict (by omega)
    rw [Nat.mul_comm (b - a) r, hvanish, map_zero] at hd
    exact hd rfl
  have hp := hperiod hM
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hrpos ha
  have hdiff : originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W =
      r * (b - a) := by rw [hcountP, hcountW, Nat.mul_sub_left_distrib]
  let : NeZero (originalSelectedCount (hD := hD) P -
    originalSelectedCount (hD := hD) W) := ⟨by rw [hdiff]; exact NeZero.ne _⟩
  have hn : 2 ≤ r * (b - a) := by
    simpa only [one_mul] using
      Nat.mul_le_mul (show 1 ≤ r by omega) (show 2 ≤ b - a by omega)
  have hnB : r * (b - a) ≤ originalSelectedCount (hD := hD) P := by
    rw [hcountP]
    exact Nat.mul_le_mul_left r (Nat.sub_le b a)
  obtain ⟨_, _, _, _, _, htransfer⟩ := c.originalActual_coefficient P W A Q q v u z w
    hq hv hwindow hW hA hQ hcutq hcutLq hC hmax Λ b a r (by omega) hrpos hr hKU hKW
    hp (r * (b - a)) hn hnB (dvd_mul_right r _) p₀ p₁ hpq hdep
  have hzero (capacity : r * (b - a) ≤ originalSelectedCount (hD := hD) P - 1) :
      windowDefect (finiteWordCycle (n := r * (b - a))
        (c.originalInternalResidue P) capacity) Subtype.val
        (c.originalResponseClassExponent P W a b) b (r * b) (r * (b - a)) = 0 := by
    rw [finiteWord_windowDefect_congr (c.originalInternalResidue P) Subtype.val
      (c.originalResponseClassExponent P W a b) b (r * (b - a))
      hdiff hcountP _ capacity] at htransfer
    by_contra hne
    exact (htransfer hne) hvanish
  exact Or.inr ⟨hp, c.originalWindow_one_active_null_primitive P W q z v hv hW.symm
    hwindow hcutq hcutLq hmax Λ b a r ha hab hrpos hcoprime.symm hr hKU hKW
    active hunique hzero⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
