/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseCycleProjection
import SkewCornerDescent.Matrix.OriginalResponseClassDefects
import SkewCornerDescent.CyclicPeriodDetector
import SkewCornerDescent.CyclicLastInventory

/-!
# Dual identities on the unchanged original response field

Formalizes `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`,
`eq:dual-first`, `eq:dual-short`, `eq:dual-last`). Complete literal windows
supply the cyclic projection and exact signed class balance. The original corner
powers supply both selected counts. Every closure-cycle start is retained.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The three normalized inventory identities use actual response values and
actual source/window multiplicities. The final clause identifies every actual
completed source cycle with the literal periodic closure word. -/
theorem originalWindow_dual_identities {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r d s k : ℕ) (ha : 0 < a) (hrpos : 0 < r)
    (hs : 0 < s) (hsd : s ≤ d) (hk : 0 < k)
    (hb : b = k * d + s) (had : a + d = b)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (r * d)] [NeZero (r * s)] [NeZero (k * (r * d) + r * s)]
    [NeZero (r * d + r * a)] [NeZero (originalSelectedCount (hD := hD) P)] :
    ∃ hperiod : r * d ≤ originalSelectedCount (hD := hD) P - 1,
      let f := finiteWordCycle (n := r * d) (c.originalInternalResidue P) hperiod
      let e := c.originalResponseClassExponent P W a b
      let S : c.OriginalResponseClass P → OtherField c.top := Subtype.val
      windowDefect f S e b (r * d + r * a) (r * d) =
        (r * d : ℕ) * (d : OtherField c.top) * (∏ i, f i)⁻¹ -
          (∑ i, windowProduct f 1 (r * a) i) *
            (∏ i ∈ Finset.range (r * d + r * a - 1), f (i : ZMod (r * d)))⁻¹ *
              closureLabelSum e S ∧
      windowDefect f S e b (k * (r * d) + r * s) (r * s) =
        (s : OtherField c.top) * inverseWindowSum f (r * s) -
          (r * s : ℕ) * (∏ i ∈ Finset.range (r * s - 1), f (i : ZMod (r * d)))⁻¹ *
            closureLabelSum e S ∧
      lastWindowDefect f S e b (k * (r * d) + r * s) =
        ((b : OtherField c.top) / (s : OtherField c.top)) * (∏ i, f i)⁻¹ ^ k *
          windowDefect f S e b (k * (r * d) + r * s) (r * s) ∧
      (∀ x : OtherField c.top, completeResponseCycle (c.originalInternalResidue P) x =
        closureWord f x (originalSelectedCount (hD := hD) P)) := by
  classical
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [hcountP]; exact Nat.mul_pos hrpos (by omega)
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]; exact Nat.mul_pos hrpos ha
  obtain ⟨hperiod, hcounts, hsum⟩ := c.originalWindow_responseClass_defects
    P W q u v hv hW hwindow hcutq hcutLq hC r d s k b a hrpos hs hk hb had hcountP hcountW
  let f := finiteWordCycle (n := r * d) (c.originalInternalResidue P) hperiod
  let e := c.originalResponseClassExponent P W a b
  have he : ∑ X, e X = (d : ℤ) := by
    change ∑ X, c.originalResponseClassExponent P W a b X = (d : ℤ)
    simp_rw [originalResponseClassExponent, originalResponseValueExponent, hcounts]
    exact hsum
  have hS := c.originalResponseClass_ne_zero P hB hmax
  have hf : ∀ i, f i ≠ 0 := by
    intro i
    have heq := congrFun (c.originalResponseClassWord_val P (r * d) hperiod) i
    change finiteWordCycle (c.originalInternalResidue P) hperiod i ≠ 0
    rw [← heq]
    exact hS _
  have hbn : b * (r * d) = d * (r * d + r * a) := by rw [← had]; ring
  have hperiodId := windowDefect_period f Subtype.val e hf hS he hbn
  have hshort := windowDefect_short f Subtype.val e
    (Nat.mul_le_mul_left r hsd) hk hb he
  have hfull := windowDefect_full_eq_short f Subtype.val e
    (Nat.mul_le_mul_left r hsd) hk hb rfl rfl (by exact_mod_cast (Nat.ne_of_gt hs)) he
  rw [windowDefect_eq_last] at hfull
  obtain ⟨hperiod', hproj⟩ := c.originalWindow_complete_cycle_projection P W q u v hv hW
    hwindow hcutq hcutLq hC (r * d) (by
      rw [hcountP, hcountW, ← Nat.mul_sub_left_distrib]; congr 1; omega)
  exact ⟨hperiod, hperiodId, hshort, hfull, hproj⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
