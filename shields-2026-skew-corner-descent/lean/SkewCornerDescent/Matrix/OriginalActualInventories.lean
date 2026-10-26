/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalActualDualDetector
import SkewCornerDescent.CyclicWindowNonvanishing
import SkewCornerDescent.CyclicEligibleNonvanishing

/-!
# Literal nonvanishing inventories of the actual matched chart

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`, `cor:many-active`).
The closed actual dual detector returns to the complete literal period and last
inventories. The closure length is identified with the original outer count by a
proved length bridge, not by transporting an implicit finite-group instance.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory
open scoped BigOperators

noncomputable local instance actualInventoriesRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

private theorem windowDefect_length_congr {F ι : Type*} [Field F] [Fintype ι]
    {n B C : ℕ} [NeZero n] [NeZero B] [NeZero C] (h : B = C)
    (f : ZMod n → F) (S : ι → F) (e : ι → ℤ) (b j : ℕ) :
    windowDefect f S e b B j = windowDefect f S e b C j := by
  subst C
  rfl

private theorem lastWindowDefect_length_congr {F ι : Type*} [Field F] [Fintype ι]
    {n B C : ℕ} [NeZero n] [NeZero B] [NeZero C] (h : B = C)
    (f : ZMod n → F) (S : ι → F) (e : ι → ℤ) (b : ℕ) :
    lastWindowDefect f S e b B = lastWindowDefect f S e b C := by
  subst C
  rfl

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Two actual unbalanced classes force nonvanishing of the complete literal
period or last inventory in the unchanged original field. Every detector model
premise and source unit is produced internally. -/
theorem originalWindow_inventory_dual_nonvanishing {n m s t : ℕ}
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
    [NeZero (r * b)]
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
      (windowDefect cycle Subtype.val e b (r * b) (r * d) ≠ 0 ∨
        lastWindowDefect cycle Subtype.val e b (r * b) ≠ 0) ∧
      (windowDefect cycle Subtype.val e b (r * b) (r * d) ≠ 0 ∨
        (2 ≤ r * s ∧ windowDefect cycle Subtype.val e b (r * b) (r * s) ≠ 0)) := by
  classical
  let d := b - a
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
  obtain ⟨k, s, hk, hs, hsd, hbshape, hperiod, hcore⟩ :=
    c.originalWindow_actual_dual_nonvanishing P W A Q q v u z w hv hwindow hW hA hQ
      hcutq hcutLq hmax Λ b a r ha hab hrpos hr hKU hKW p₀ p₁ hpq hdep htwo
  let word := c.originalResponseClassWord P (r * d) hperiod
  let cycle := finiteWordCycle (n := r * d) (c.originalInternalResidue P) hperiod
  have hcycle : Subtype.val ∘ word = cycle := c.originalResponseClassWord_val P (r * d) hperiod
  obtain ⟨hperiod', hcounts, _⟩ := c.originalWindow_responseClass_defects P W q z v hv
    hW.symm hwindow hcutq hcutLq hC r d s k b a hrpos hs hk hbshape (by dsimp only [d]; omega)
    hcountP hcountW
  have heq : c.originalResponseClassExponent P W a b =
      classDefect word 1 d s (r * s - 1) 0 := by
    funext X
    exact hcounts X
  dsimp only at hcore
  simp_rw [heq] at hcore
  dsimp only [cycle] at hcycle
  rw [← hcycle] at hcore
  have hlen : k * (r * d) + r * s = r * b := by rw [hbshape]; ring
  let : NeZero (k * (r * d) + r * s) := ⟨by rw [hlen]; exact NeZero.ne _⟩
  have hreg : ∀ X : c.OriginalResponseClass P, X.val ≠ 0 :=
    c.originalResponseClass_ne_zero P hB hmax
  have hresult := cleared_dual_implies_window_nonvanishing hrpos hs hsd hk word
    Subtype.val hreg hcore
  have heligible := window_dual_eligible_nonvanishing hrpos hs hsd hk word Subtype.val hresult
  rw [hcycle, ← hbshape] at hresult heligible
  dsimp only
  refine ⟨k, s, hk, hs, hsd, hbshape, hperiod, ?_, ?_⟩
  · rw [heq]
    rcases hresult with hn | hlast
    · left
      rw [← windowDefect_length_congr hlen cycle Subtype.val _ b (r * d)]
      exact hn
    · right
      rw [← lastWindowDefect_length_congr hlen cycle Subtype.val _ b]
      exact hlast
  · rw [heq]
    rcases heligible with hn | ⟨hsize, hshort⟩
    · left
      rw [← windowDefect_length_congr hlen cycle Subtype.val _ b (r * d)]
      exact hn
    · right
      refine ⟨hsize, ?_⟩
      rw [← windowDefect_length_congr hlen cycle Subtype.val _ b (r * s)]
      exact hshort

end SkewCornerDescent.Matrix.SelectedCoordinate
