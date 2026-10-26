/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalManyActive

/-!
# Prescribed short-inventory transfer on the actual chart

Formalizes the sharper conditional clause of `shields-2026-skew-corner-descent.tex`
(`cor:many-active`). A nonzero actual short inventory forces its length at least
two from the complete class counts. It then detects the full original defect at
precisely that eligible coefficient, not merely at some shorter period coefficient.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory

noncomputable local instance shortCoefficientRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- On the actual periodic-gap domain, a prescribed nonzero short inventory
detects the original coefficient of order `r*s-1`. The length-one boundary is
excluded internally, and neither an active-class hypothesis nor positive weights
are required for the transfer implication. -/
theorem originalShort_coefficient {n m ℓ t : ℕ}
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
    (Λ : Lambda) (b a r k s : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hrpos : 0 < r)
    (hk : 0 < k) (hs : 0 < s) (hsd : s ≤ b - a) (hbshape : b = k * (b - a) + s)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin ℓ => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)]
    [NeZero (r * (b - a))] [NeZero (r * b)]
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    ∃ hperiod : r * (b - a) ≤ originalSelectedCount (hD := hD) P - 1,
      windowDefect (finiteWordCycle (n := r * (b - a)) (c.originalInternalResidue P) hperiod)
        Subtype.val (c.originalResponseClassExponent P W a b) b (r * b) (r * s) ≠ 0 →
      (2 ≤ r * s ∧ PowerSeries.coeff (r * s - 1)
        (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0) := by
  classical
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]; exact Nat.mul_pos hrpos ha
  obtain ⟨hperiod, hcounts, _⟩ := c.originalWindow_responseClass_defects
    P W q z v hv hW.symm hwindow hcutq hcutLq hC r (b - a) s k b a
      hrpos hs hk hbshape (by omega) hcountP hcountW
  let word := c.originalResponseClassWord P (r * (b - a)) hperiod
  have heq : c.originalResponseClassExponent P W a b =
      classDefect word 1 (b - a) s (r * s - 1) 0 := funext fun X => hcounts X
  have hcycle := c.originalResponseClassWord_val P (r * (b - a)) hperiod
  have hlen : k * (r * (b - a)) + r * s = r * b := by
    calc
      _ = r * (k * (b - a) + s) := by ring
      _ = r * b := congrArg (r * ·) hbshape.symm
  let : NeZero (k * (r * (b - a)) + r * s) := ⟨by rw [hlen]; exact NeZero.ne _⟩
  refine ⟨hperiod, ?_⟩
  intro hshort
  have hshort' : windowDefect (Subtype.val ∘ word) Subtype.val
      (classDefect word 1 (b - a) s (r * s - 1) 0) (k * (b - a) + s)
      (k * (r * (b - a)) + r * s) (r * s) ≠ 0 := by
    rw [heq] at hshort
    have hc : (Subtype.val ∘ word) =
        finiteWordCycle (n := r * (b - a)) (c.originalInternalResidue P) hperiod := hcycle
    rw [hc, finiteWord_windowDefect_congr (c.originalInternalResidue P) Subtype.val
      (classDefect word 1 (b - a) s (r * s - 1) 0) (k * (b - a) + s) (r * s)
      rfl hlen hperiod hperiod, ← hbshape]
    exact hshort
  have hj := short_window_nonvanishing_length_ge_two hrpos hs hsd hk word Subtype.val hshort'
  have hjB : r * s ≤ originalSelectedCount (hD := hD) P := by
    rw [hcountP]
    exact Nat.mul_le_mul_left r (hsd.trans (Nat.sub_le b a))
  obtain ⟨K, hK, _, _, _, hdetect⟩ := c.originalActual_coefficient P W A Q q v u z w
    hq hv hwindow hW hA hQ hcutq hcutLq hC hmax Λ b a r (by omega) hrpos hr hKU hKW
    hp (r * s) hj hjB (dvd_mul_right r s) p₀ p₁ hpq hdep
  have hdiff : originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W =
      r * (b - a) := by rw [hcountP, hcountW, Nat.mul_sub_left_distrib]
  refine ⟨hj, hdetect ?_⟩
  rw [finiteWord_windowDefect_congr (c.originalInternalResidue P) Subtype.val
    (c.originalResponseClassExponent P W a b) b (r * s) hdiff hcountP _ hperiod]
  exact hshort

end SkewCornerDescent.Matrix.SelectedCoordinate
