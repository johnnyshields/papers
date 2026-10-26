/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalManyActive
import SkewCornerDescent.Matrix.OriginalMaximalBin

/-!
# Original many-active detection without an assumed gap period

Formalizes `shields-2026-skew-corner-descent.tex` (`cor:many-active`). The
constructed maximal gap bin either detects directly or supplies the actual gap
period consumed by the dual-inventory coefficient assembly. No period or class
nonvanishing conclusion is carried as an additional hypothesis. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

noncomputable local instance manyActiveGeneralRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Two actual unbalanced response classes force a nonzero coefficient of the
complete original rational defect by order `r*(b-a)-1`, for arbitrary actual gaps. -/
theorem originalManyActive_general {n m s t : ℕ}
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
    (Δ : ℤ) (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ)
    (hqspan : q = ((b - a : ℕ) : ℤ) * Δ)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁)
    (htwo : ∃ X Y : c.OriginalResponseClass P, X ≠ Y ∧
      c.originalResponseClassExponent P W a b X ≠ 0 ∧
      c.originalResponseClassExponent P W a b Y ≠ 0) :
    ∃ h : ℕ, 0 < h ∧ h ≤ r * (b - a) - 1 ∧
      PowerSeries.coeff h (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0 := by
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hnsize : 2 ≤ r * (b - a) := by
    simpa only [one_mul] using
      Nat.mul_le_mul (show 1 ≤ r by omega) (show 2 ≤ b - a by omega)
  let : NeZero (r * (b - a)) := ⟨by omega⟩
  let : NeZero (r * b) := ⟨Nat.ne_of_gt (Nat.mul_pos hrpos (by omega))⟩
  let : NeZero (originalSelectedCount (hD := hD) P) := ⟨by rw [hcountP]; exact NeZero.ne _⟩
  have hdiff : originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W =
      r * (b - a) := by rw [hcountP, hcountW, Nat.mul_sub_left_distrib]
  let : NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W) :=
    ⟨by rw [hdiff]; exact NeZero.ne _⟩
  obtain ⟨M, K, hK, _, _, _, hmean, hstrict, hperiod⟩ :=
    c.originalMaximalBin_alternative P W A Q q v u z w hq hv hwindow hW hA hQ hcutq
      hcutLq hmax Λ b a r ha hab hrpos hcoprime hr hKU hKW Δ hspan hqspan p₀ p₁ hpq hdep
  by_cases hM : q < M
  · have hderiv := hstrict hM
    have hcoeff : PowerSeries.coeff ((b - a) * r - 1)
        (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0 := by
      intro hz
      exact hderiv (by rw [hz, map_zero])
    rw [Nat.mul_comm (b - a) r] at hcoeff
    exact ⟨r * (b - a) - 1, by omega, le_rfl, hcoeff⟩
  · have hp := hperiod (by omega)
    obtain ⟨j, hj, hjn, _, hcoeff⟩ := c.originalManyActive_periodic P W A Q q v u z w
      hq hv hwindow hW hA hQ hcutq hcutLq hmax Λ b a r ha hab hrpos hr hKU hKW
      hp p₀ p₁ hpq hdep htwo
    exact ⟨j - 1, by omega, by omega, hcoeff⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
