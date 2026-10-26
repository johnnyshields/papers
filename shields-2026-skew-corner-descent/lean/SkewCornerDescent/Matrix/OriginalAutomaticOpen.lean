/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalManyActive

/-!
# The automatic identity locus on the actual original chart

Formalizes `shields-2026-skew-corner-descent.tex` (`cor:automatic-open`). At
primitive multiplicity and positive remainder one, the actual last inventory
vanishes identically. Actual dual nonvanishing therefore selects the full-period
inventory, and original coefficient transfer detects at its eligible order.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

noncomputable local instance automaticOpenRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The automatic last-detector identity, nonzero full-period detector, and
original coefficient are assembled on one complete actual chart. No last-detector
nonvanishing or independently assigned response family is assumed. -/
theorem originalAutomatic_open {n m ℓ t : ℕ}
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
    (Λ : Lambda) (b a r k : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b)
    (hrone : r = 1) (hk : 0 < k) (hshape : b = k * (b - a) + 1)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin ℓ => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (r * (b - a))] [NeZero (r * b)]
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁)
    (htwo : ∃ X Y : c.OriginalResponseClass P, X ≠ Y ∧
      c.originalResponseClassExponent P W a b X ≠ 0 ∧
      c.originalResponseClassExponent P W a b Y ≠ 0) :
    ∃ hperiod : r * (b - a) ≤ originalSelectedCount (hD := hD) P - 1,
      let f := finiteWordCycle (n := r * (b - a)) (c.originalInternalResidue P) hperiod
      let e := c.originalResponseClassExponent P W a b
      lastWindowDefect f Subtype.val e b (r * b) = 0 ∧
        windowDefect f Subtype.val e b (r * b) (r * (b - a)) ≠ 0 ∧
        PowerSeries.coeff (b - a - 1) (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0 := by
  classical
  subst r
  have hd : 2 ≤ b - a := by omega
  have hcountP : originalSelectedCount (hD := hD) P = 1 * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, mul_one, one_mul]
  have hcountW : originalSelectedCount (hD := hD) W = 1 * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, mul_one, one_mul]
  have hC : 0 < originalSelectedCount (hD := hD) W := by rw [hcountW, one_mul]; exact ha
  obtain ⟨l, s, hl, hs, hsd, hbshape, hperiod, _, heligible⟩ :=
    c.originalWindow_inventory_dual_nonvanishing P W A Q q v u z w hv hwindow hW hA hQ
      hcutq hcutLq hmax Λ b a 1 ha hab (by omega) hr hKU hKW p₀ p₁ hpq hdep htwo
  have hsone := (positive_remainder_one_unique hd (hshape.symm.trans hbshape) hsd).1
  have hn : windowDefect (finiteWordCycle (n := 1 * (b - a)) (c.originalInternalResidue P) hperiod)
      Subtype.val (c.originalResponseClassExponent P W a b) b (1 * b) (1 * (b - a)) ≠ 0 := by
    rcases heligible with hn | ⟨hsize, _⟩
    · exact hn
    · rw [hsone, Nat.mul_one] at hsize
      omega
  obtain ⟨hperiod', hcounts, _⟩ := c.originalWindow_responseClass_defects P W q z v hv
    hW.symm hwindow hcutq hcutLq hC 1 (b - a) 1 k b a (by omega) (by omega) hk
    hshape (by omega) hcountP hcountW
  let word := c.originalResponseClassWord P (1 * (b - a)) hperiod
  have heq : c.originalResponseClassExponent P W a b = classDefect word 1 (b - a) 1 0 0 := by
    funext X
    have h := hcounts X
    simpa only [word, originalResponseClassExponent, originalResponseValueExponent,
      Nat.mul_one, Nat.sub_self] using h
  have hdim : classDefect word 1 (1 * (b - a)) 1 0 0 =
      classDefect word 1 (b - a) 1 0 0 := by
    funext X
    simp only [classDefect, windowSum, Finset.range_zero, Finset.sum_empty,
      Nat.cast_zero, mul_zero]
  let : NeZero (k * (1 * (b - a)) + 1) := ⟨by
    have hb : k * (1 * (b - a)) + 1 = b := by simpa only [one_mul] using hshape.symm
    rw [hb]; omega⟩
  have hzero := one_position_windowDefect_full_zero (by omega) hk word Subtype.val
  rw [windowDefect_eq_last, hdim, ← heq] at hzero
  have hbword : k * (1 * (b - a)) + 1 = b := by simpa only [one_mul] using hshape.symm
  rw [hbword] at hzero
  have hcycle : (Subtype.val ∘ word) =
      finiteWordCycle (n := 1 * (b - a)) (c.originalInternalResidue P) hperiod :=
    c.originalResponseClassWord_val P (1 * (b - a)) hperiod
  rw [hcycle] at hzero
  have hzero' : lastWindowDefect (finiteWordCycle (c.originalInternalResidue P) hperiod)
      Subtype.val (c.originalResponseClassExponent P W a b) b (1 * b) = 0 := by
    unfold lastWindowDefect at hzero ⊢
    simpa only [one_mul] using hzero
  have hdiff : originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W =
      1 * (b - a) := by rw [hcountP, hcountW, Nat.mul_sub_left_distrib]
  let : NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W) :=
    ⟨by rw [hdiff]; exact NeZero.ne _⟩
  obtain ⟨K, hK, _, _, _, hdetect⟩ := c.originalActual_coefficient P W A Q q v u z w
    hq hv hwindow hW hA hQ hcutq hcutLq hC hmax Λ b a 1 (by omega) (by omega) hr hKU hKW
    hp (1 * (b - a)) (by omega) (by rw [hcountP]; omega) (one_dvd _) p₀ p₁ hpq hdep
  have hcoefficient := hdetect (by
    rw [finiteWord_windowDefect_congr (c.originalInternalResidue P) Subtype.val
      (c.originalResponseClassExponent P W a b) b (1 * (b - a)) hdiff hcountP _ hperiod]
    exact hn)
  refine ⟨hperiod, hzero', hn, ?_⟩
  simpa only [one_mul] using hcoefficient

end SkewCornerDescent.Matrix.SelectedCoordinate
