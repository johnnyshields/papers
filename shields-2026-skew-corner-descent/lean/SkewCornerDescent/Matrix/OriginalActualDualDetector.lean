/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassModel
import SkewCornerDescent.Matrix.ConstantActiveLabelDualNonvanishing

/-!
# Closed dual detection on the actual matched response chart

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`, `cor:many-active`).
The actual matched chart supplies every model and exposure premise of the dual
detector. Its two nonvanishing alternatives are identities in the unchanged
original coefficient field, with the literal original period word and signed
source/window occurrence counts. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory
open scoped BigOperators

noncomputable local instance actualDualDetectorRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Two actual unbalanced response classes force one reduced original dual
detector to be nonzero. Triangularity, both chambers, cap signs, source units,
active labels, and all inactive exposures are supplied by declarations in the tree. -/
theorem originalWindow_actual_dual_nonvanishing {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hv : content v = q)
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
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (r * (b - a))]
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁)
    (htwo : ∃ X Y : c.OriginalResponseClass P, X ≠ Y ∧
      c.originalResponseClassExponent P W a b X ≠ 0 ∧
      c.originalResponseClassExponent P W a b Y ≠ 0) :
    let d := b - a
    ∃ k s : ℕ, 0 < k ∧ 0 < s ∧ s ≤ d ∧ b = k * d + s ∧
    ∃ hperiod : r * d ≤ originalSelectedCount (hD := hD) P - 1,
      let cycle := finiteWordCycle (n := r * d) (c.originalInternalResidue P) hperiod
      let e := c.originalResponseClassExponent P W a b
      ((s : OtherField c.top) * (∑ i, (windowProduct cycle 1 (r * s) i)⁻¹) -
        ((r * s : ℕ) : OtherField c.top) * (windowProduct cycle 1 (r * s - 1) 0)⁻¹ *
          (∑ X : c.OriginalResponseClass P, (e X : OtherField c.top) * X.val⁻¹) ≠ 0) ∨
      ((((r * d * d : ℕ) : OtherField c.top) *
          (windowProduct cycle 1 (r * d) 0) ^ (k - 1) *
          windowProduct cycle 1 (r * s - 1) 0) -
        (∑ X : c.OriginalResponseClass P, (e X : OtherField c.top) * X.val⁻¹) *
          (∑ i, windowProduct cycle 1 ((k - 1) * (r * d) + r * s) i) ≠ 0) := by
  classical
  let d := b - a
  have hd : 0 < d := by dsimp only [d]; omega
  have had : a + d = b := by dsimp only [d]; omega
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]; exact Nat.mul_pos hrpos ha
  obtain ⟨hB, K, hNK, k, s, hk, hs, hsd, hbshape, hperiod, p, den, label,
      base, cap, scaleDen, xnegative, xpositive, hp, hq, hq0, hrep, hactiveTop,
      hlabels, haffine, hxnegative, hxpositive, hscaleNegative, hscalePositive,
      hcapnegative, hcappositive⟩ :=
    c.originalWindow_responseClass_model P W A Q q v u z w hv hwindow hW hA hQ hcutq
      hcutLq hmax Λ b a r ha hab hrpos hr hKU hKW p₀ p₁ hpq hdep
  obtain ⟨hperiod', hcounts, _⟩ := c.originalWindow_responseClass_defects P W q z v hv
    hW.symm hwindow hcutq hcutLq hC r d s k b a hrpos hs hk hbshape had hcountP hcountW
  have heq : ∀ X : c.OriginalResponseClass P,
      c.originalResponseClassExponent P W a b X =
        classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s (r * s - 1) 0 X := by
    intro X
    exact hcounts X
  have htwo' : ∃ X Y : c.OriginalResponseClass P, X ≠ Y ∧
      classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s (r * s - 1) 0 X ≠ 0 ∧
      classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s (r * s - 1) 0 Y ≠ 0 := by
    obtain ⟨X, Y, hXY, hX, hY⟩ := htwo
    exact ⟨X, Y, hXY, by rw [← heq X]; exact hX, by rw [← heq Y]; exact hY⟩
  have hdual := constantActiveLabels_original_dual_nonvanishing hrpos hd hs c.top K hNK.le
    (c.originalResponseClassTop P hB) p den
    (fun X => ne_of_gt (c.originalResponseClassTop_gt P hB X))
    (fun X => (c.originalResponseClassTop_gt P hB X).le) hp hq hq0
    (c.originalResponseClassWord P (r * d) hperiod) k label base cap scaleDen
    hactiveTop hlabels haffine xnegative xpositive hxnegative hxpositive
    hscaleNegative hscalePositive hcapnegative hcappositive htwo'
  dsimp only at hdual
  simp_rw [← hrep, ← heq] at hdual
  have hcycle : (Subtype.val ∘ c.originalResponseClassWord P (r * d) hperiod) =
      finiteWordCycle (n := r * d) (c.originalInternalResidue P) hperiod :=
    c.originalResponseClassWord_val P (r * d) hperiod
  rw [hcycle] at hdual
  dsimp only
  exact ⟨k, s, hk, hs, hsd, hbshape, hperiod, hdual⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
