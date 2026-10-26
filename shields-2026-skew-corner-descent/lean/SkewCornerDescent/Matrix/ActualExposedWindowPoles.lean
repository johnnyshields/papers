/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualExposureExtremes
import SkewCornerDescent.ExposedWindowPoles

/-!
# Maximal poles produced by actual original response chambers

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original coefficients»
(`sec:dual`, `lem:peeling`, `thm:dual-period`). The exposed-root producer and exact word counts
compose on faithful original-matrix response representatives. Square denominators retain the
original rational functions and give one sign to every maximal term, in both chambers.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- Positive square denominator of a real specialization of a faithful response representative. -/
noncomputable def exposedResponseDenominator (N : ℕ+) {ι : Type*}
    (q : ι → OtherPolynomial N) (i : ι) : MvPolynomial ℕ ℝ :=
  realResiduePolynomial N (q i) ^ 2

/-- The literal numerator defining the exposed response divisor, before sign normalization. -/
noncomputable def exposedResponseLinearNumerator (N : ℕ+) {ι : Type*} (top : ι → ℕ+)
    (p q : ι → OtherPolynomial N) (i : ι) : MvPolynomial ℕ ℝ :=
  X (top i : ℕ) * realResiduePolynomial N (q i) + realResiduePolynomial N (p i)

/-- The original numerator multiplied by its regular denominator. Shared variables are retained. -/
noncomputable def exposedResponseNumerator (N : ℕ+) {ι : Type*} (top : ι → ℕ+)
    (p q : ι → OtherPolynomial N) (i : ι) : MvPolynomial ℕ ℝ :=
  (X (top i : ℕ) * realResiduePolynomial N (q i) + realResiduePolynomial N (p i)) *
    realResiduePolynomial N (q i)

/-- Square-denominator sign normalization is exactly the same actual triangular response
where its original denominator is regular. -/
theorem exposedResponse_fraction (N : ℕ+) {ι : Type*} (top : ι → ℕ+)
    (p q : ι → OtherPolynomial N) (x : ℕ → ℝ) (i : ι)
    (hq : MvPolynomial.eval x (realResiduePolynomial N (q i)) ≠ 0) :
    MvPolynomial.eval x (exposedResponseNumerator N top p q i) /
      MvPolynomial.eval x (exposedResponseDenominator N q i) =
      rationalTriangularResponse (top i : ℕ) (realResiduePolynomial N (p i))
        (realResiduePolynomial N (q i)) x := by
  simp only [exposedResponseNumerator, exposedResponseDenominator,
    rationalTriangularResponse, map_mul, map_add, map_pow, eval_X]
  field_simp [hq]

/-- At every regular assignment the produced cleared cyclic numerator represents the
original triangular-response reciprocal sum, including all starts and repeated wraps. -/
theorem exposedCyclicWindow_fraction {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] [Fintype G] (N : ℕ+) (top : ι → ℕ+)
    (p q : ι → OtherPolynomial N) (x : ℕ → ℝ)
    (hq : ∀ i, MvPolynomial.eval x (realResiduePolynomial N (q i)) ≠ 0)
    (hn : ∀ i, MvPolynomial.eval x (exposedResponseNumerator N top p q i) ≠ 0)
    (word : G → ι) (step : G) (j : ℕ) (a : ι) :
    let num := exposedResponseNumerator N top p q
    let den := exposedResponseDenominator N q
    let count := fun Y i => windowSum (classMask word Y) step j i
    let bound := maximalClassWindowCount word step j
    MvPolynomial.eval x (clearedPoleSum Finset.univ (num a) (bound a) (count a)
      (fun i => den a ^ count a i * ∏ Y ∈ Finset.univ.erase a,
        num Y ^ (bound Y - count Y i) * den Y ^ count Y i)) /
      (MvPolynomial.eval x (num a) ^ bound a *
        ∏ Y ∈ Finset.univ.erase a, MvPolynomial.eval x (num Y) ^ bound Y) =
      ∑ i, (windowProduct ((fun Y =>
        rationalTriangularResponse (top Y : ℕ) (realResiduePolynomial N (p Y))
          (realResiduePolynomial N (q Y)) x) ∘ word) step j i)⁻¹ := by
  classical
  dsimp only
  rw [cyclic_inverse_window_numerator_fraction word step j a
    (exposedResponseNumerator N top p q) (exposedResponseDenominator N q)
    (MvPolynomial.eval x) hn]
  simp_rw [exposedResponse_fraction N top p q x _ (hq _)]

/-- A simultaneous actual chamber exposes one class and proves that the complete reciprocal
word inventory has a nonzero leading cleared numerator at its actual maximal window count. -/
theorem simultaneousActualChamber_cyclic_pole {ι G : Type*} [Fintype ι]
    [DecidableEq ι] [AddCommGroup G] [Fintype G]
    (N K : ℕ+) (hNK : N ≤ K) (top : ι → ℕ+) (p q : ι → OtherPolynomial N)
    (hp : ∀ i k, k ∈ (realResiduePolynomial N (p i)).vars → k < (top i : ℕ))
    (hq : ∀ i k, k ∈ (realResiduePolynomial N (q i)).vars → k < (N : ℕ))
    (hanchor : ∃ i, top i = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive)
    (word : G → ι) (step : G) (j : ℕ) :
    ∃ a : {i : ι // top i = K},
      let num := exposedResponseNumerator N top p q
      let den := exposedResponseDenominator N q
      let count := fun Y i => windowSum (classMask word Y) step j i
      let bound := maximalClassWindowCount word step j
      ¬ exposedResponseLinearNumerator N top p q a.val ∣
        clearedPoleSum Finset.univ (num a.val) (bound a.val) (count a.val)
        (fun i => den a.val ^ count a.val i * ∏ Y ∈ Finset.univ.erase a.val,
          num Y ^ (bound Y - count Y i) * den Y ^ count Y i) := by
  classical
  obtain ⟨a, hzero, hreg, hsign⟩ := simultaneousActualChamber_exposed_extreme
    N K hNK top p q hp hq hanchor positive x hx
  let y := anchorAssignment (K : ℕ)
    (rationalAnchorRoot (fun a : {i : ι // top i = K} => realResiduePolynomial N (p a.val))
      (fun a => realResiduePolynomial N (q a.val))) a x
  let P := fun i => X (top i : ℕ) * realResiduePolynomial N (q i) +
    realResiduePolynomial N (p i)
  let Q := fun i => realResiduePolynomial N (q i)
  let sign : ℝ := if positive then 1 else -1
  have he (i : ι) : MvPolynomial.eval y (P i) / MvPolynomial.eval y (Q i) =
      rationalTriangularResponse (top i : ℕ) (realResiduePolynomial N (p i))
        (realResiduePolynomial N (q i)) y := by
    dsimp only [P, Q, rationalTriangularResponse]
    rw [map_add, map_mul, eval_X]
    have hQi : MvPolynomial.eval y (realResiduePolynomial N (q i)) ≠ 0 := hreg i
    field_simp [hQi]
  have hden : ∀ i, 0 < MvPolynomial.eval y (exposedResponseDenominator N q i) := by
    intro i
    rw [exposedResponseDenominator, map_pow]
    exact sq_pos_of_ne_zero (hreg i)
  have hz : MvPolynomial.eval y (P a.val) / MvPolynomial.eval y (Q a.val) = 0 := by
    rw [he, a.property]
    exact hzero
  have hz' : MvPolynomial.eval y (P a.val) = 0 :=
    (div_eq_zero_iff.mp hz).resolve_right (hreg a.val)
  have hn : MvPolynomial.eval y (exposedResponseNumerator N top p q a.val) = 0 := by
    change MvPolynomial.eval y (P a.val * Q a.val) = 0
    rw [map_mul, hz', zero_mul]
  refine ⟨a, ?_⟩
  have hnums : ∀ i, i ≠ a.val →
      0 < sign * MvPolynomial.eval y (exposedResponseNumerator N top p q i) := by
    intro i hi
    apply normalizedResponseNumerator_pos (P i) (Q i) (MvPolynomial.eval y) sign (hreg i)
    rw [he]
    have hs := hsign i hi
    cases positive <;> simpa only [sign, Bool.false_eq_true, ite_false, ite_true, responseSign,
      neg_one_mul, one_mul, neg_pos] using hs
  have hpos := cyclic_inverse_window_numerator_eval_pos word step j a.val
    (exposedResponseNumerator N top p q) (exposedResponseDenominator N q)
    (MvPolynomial.eval y) sign hn hden hnums
  dsimp only at hpos ⊢
  rintro ⟨z, hz⟩
  rw [hz, map_mul, show MvPolynomial.eval y
    (exposedResponseLinearNumerator N top p q a.val) = 0 from hz', zero_mul, mul_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- Complete original matrices supply their own exposed chambers and noncancelling maximal
reciprocal poles. No chamber, sign certificate, or window bound is left as a premise. -/
theorem originalResponses_cyclic_poles {D : Diagram} {hD : IsConnectedSkew D}
    (c : SelectedCoordinate D hD) {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] [Fintype G]
    (n : ι → ℕ) (P : ∀ i, Profile (n i))
    (b d : ∀ i, Option (OriginalSelectedBlocks (hD := hD) (P i)))
    (top : ι → ℕ+) (htop : ∀ i, c.top < top i)
    (hindices : ∀ i, (P i).xi (originalRowSplitEquiv (hD := hD) (P i) (.inl (b i))) -
      (P i).zeta (originalColSplitEquiv (hD := hD) (P i) (.inl (d i))) = (top i : ℤ))
    (hmax : ∀ i C, C ∈ edgeComponents (diagramInterior (P i).cells) →
      span C ≤ (c.top : ℕ))
    (K : ℕ+) (hanchor : ∃ i, top i = K)
    (hdistinct : ∀ i l, top i = K → top l = K → i ≠ l →
      c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) ≠
        c.regularResidue (c.originalLocalResponse (P l) (b l) (d l)))
    (word : G → ι) (step : G) (j : ℕ) :
    ∃ p q : ι → OtherPolynomial c.top,
      (∀ i, c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) =
        residueGenerator c.top ⟨top i, ne_of_gt (htop i)⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (p i) /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) (q i)) ∧
      ∀ positive : Bool, ∃ a : {i : ι // top i = K},
        ∃ x ∈ simultaneousActualChamber c.top K top p q positive,
        let num := exposedResponseNumerator c.top top p q
        let den := exposedResponseDenominator c.top q
        let count := fun Y i => windowSum (classMask word Y) step j i
        let bound := maximalClassWindowCount word step j
        ¬ exposedResponseLinearNumerator c.top top p q a.val ∣
          clearedPoleSum Finset.univ (num a.val) (bound a.val) (count a.val)
          (fun i => den a.val ^ count a.val i * ∏ Y ∈ Finset.univ.erase a.val,
            num Y ^ (bound Y - count Y i) * den Y ^ count Y i) := by
  classical
  obtain ⟨p, q, hp, hq, he, hchamber⟩ :=
    c.originalResponses_simultaneous_chambers n P b d top htop hindices hmax
      K hanchor hdistinct
  have hNK : c.top ≤ K := by
    obtain ⟨i, hi⟩ := hanchor
    exact (htop i).le.trans_eq hi
  refine ⟨p, q, he, ?_⟩
  intro positive
  obtain ⟨x, hx⟩ := (hchamber positive).2
  obtain ⟨a, ha⟩ := simultaneousActualChamber_cyclic_pole c.top K hNK top p q
    hp hq hanchor positive x hx word step j
  exact ⟨a, x, hx, ha⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
