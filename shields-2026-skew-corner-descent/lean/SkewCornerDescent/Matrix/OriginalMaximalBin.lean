/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalStrictRationalDefect
import SkewCornerDescent.Matrix.OriginalTransfer
import SkewCornerDescent.Matrix.OriginalMaximalSchurFrontier

/-!
# The actual maximal-bin detection or gap-period alternative

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Original
corner powers supply both selected counts. The cyclic maximum and protected
generator are constructed. A strict maximum detects the full supplied rational
defect; equality derives the selected-multiplicity gap period. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

noncomputable local instance maximalBinRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- On the paper's actual coprime outer-count domain, the constructed maximal bin
either detects the full supplied rational defect or produces the completed-gap
period. No class inventory, protected index, or gap period is an input. -/
theorem originalMaximalBin_alternative {n m s t : ℕ}
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
    [NeZero (originalSelectedCount (hD := hD) P)]
    (Δ : ℤ) (hspan : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ)
    (hqspan : q = ((b - a : ℕ) : ℤ) * Δ)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    ∃ M : ℤ, ∃ K : ℕ+, ∃ hK : c.top < K,
      (K : ℤ) = (c.top : ℤ) + M ∧
      (∀ x : ZMod (originalSelectedCount (hD := hD) P),
        windowSum (fun a => c.originalCompletedGap P ((ZMod.finEquiv _).symm a))
          1 ((b - a) * r) x ≤ M) ∧
      (∃ x : ZMod (originalSelectedCount (hD := hD) P),
        windowSum (fun a => c.originalCompletedGap P ((ZMod.finEquiv _).symm a))
          1 ((b - a) * r) x = M) ∧
      q ≤ M ∧
      (q < M → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff ((b - a) * r - 1)
          (c.originalDeterminantDefect P A Q a b p₀ p₁)) ≠ 0) ∧
      (M = q → Function.Periodic
        (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
        (r : ZMod (originalSelectedCount (hD := hD) P))) := by
  classical
  have hcountP : originalSelectedCount (hD := hD) P = b * r := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hcountW : originalSelectedCount (hD := hD) W = a * r := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos ha hrpos
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [hcountP]
    exact Nat.mul_pos (by omega) hrpos
  have hj : 2 ≤ (b - a) * r := by
    have hd : 2 ≤ b - a := by omega
    have hm := Nat.mul_le_mul_left (b - a) hrpos
    omega
  have hjlen : (b - a) * r = originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W := by
    rw [hcountP, hcountW, Nat.sub_mul]
  have hjB : (b - a) * r ≤ originalSelectedCount (hD := hD) P := by omega
  obtain ⟨M, K, hK, hKeq, hbound, hretain, _, _, _⟩ :=
    c.originalSchur_maximal_gap_frontier P hB hmax ((b - a) * r) hj hjB
  have hmean := c.originalCompletedGap_maximum_mean_period P hB b a r (by omega)
    hcoprime hcountP Δ M hspan hbound
  have hmeanq : q ≤ M := by rw [hqspan]; exact hmean.1
  obtain ⟨ε, δ, classes, e, _, hε, _, hdegree, _, _, hfactor, hρ, _⟩ :=
    c.originalRationalClasses_representation P W A Q q v u z w hv hwindow hW hA hQ
      hcutq hcutLq hC hmax Λ b a (by omega) hKU hKW p₀ p₁ hpq hdep
  refine ⟨M, K, hK, hKeq, hbound, hretain, hmeanq, ?_, ?_⟩
  · intro hstrict
    have ht := c.originalRationalDefect_strict_bin_ne_zero P W A Q q v u z w hq hv
      hwindow hW hA hQ hcutq hcutLq hC hmax ((b - a) * r) hj hjlen M hstrict
      hbound hretain K hK hKeq classes e ε hε b a (by omega) hdegree hfactor
    dsimp only at ht
    simpa only [originalDeterminantDefect, hρ] using ht.2.1
  · intro hM
    apply hmean.2
    rw [hM, hqspan]

end SkewCornerDescent.Matrix.SelectedCoordinate
