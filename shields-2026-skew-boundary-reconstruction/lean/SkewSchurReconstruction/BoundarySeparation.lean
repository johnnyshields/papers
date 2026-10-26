/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CapFixedRigidity
import SkewSchurReconstruction.CapGridVectors
import SkewSchurReconstruction.EqualPairRigidity

/-!
# Boundary separation

Formalizes “Every positive cap separates an equal pair” (`subsec:cap-separation`):
`cor:boundary-separation`, `eq:cap-leading-monomial`, and
`eq:ratio-leading-monomial`.  Responses are those of the actual signed cofactor
vectors on their cap grids.  The scope is the legitimate cap-fixed hypotheses of
`thm:cap-fixed-rigidity`, with the additional equal-parent condition that the
zeroth cofactor defect vanishes.  The positive floor and first-coordinate support
are produced by `CapFixedRigidity`; neither a minimizing coordinate nor an initial
form is assumed.  Zero coordinates keep infinite valuation.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

/-- The positive-cap finite difference strictly increases on nonnegative integer shifts. -/
theorem ConvexWeight.cap_difference_strict (w : ConvexWeight) {a d e : ℤ}
    (ha : 0 < a) (hd : 0 ≤ d) (hde : d < e) :
    w.weight (a + d).toNat - w.weight d.toNat <
      w.weight (a + e).toNat - w.weight e.toNat := by
  have hn : 0 < a.toNat := by omega
  have h := w.strictMono_difference hn (show d.toNat < e.toNat by omega)
  have h₁ : d.toNat + a.toNat = (a + d).toNat := by omega
  have h₂ : e.toNat + a.toNat = (a + e).toNat := by omega
  simpa only [h₁, h₂] using h

/-- Strict superadditivity determines the actual two-term ratio kernel, including its sign. -/
theorem boundary_ratio_kernel (w : ConvexWeight) (r a d : ℤ)
    (hr : 0 < r) (ha : 0 < a) (hd : 0 ≤ d) :
    complete (r + a + d) - complete a * complete (r + d) ≠ 0 ∧
    initialForm w.generatorWeight
        (complete (r + a + d) - complete a * complete (r + d)) =
      -(complete a * complete (r + d)) ∧
    monomialValuation w.generatorWeight
        (complete (r + a + d) - complete a * complete (r + d)) =
      (w.weight a.toNat + w.weight (r + d).toNat : WithTop ℝ) := by
  let p : CompleteRing := -(complete a * complete (r + d))
  let q : CompleteRing := complete (r + a + d)
  have hrd : 0 ≤ r + d := by omega
  have hp : p ≠ 0 := neg_ne_zero.mpr (mul_ne_zero
    (complete_ne_zero_of_nonneg a ha.le) (complete_ne_zero_of_nonneg (r + d) hrd))
  have hhom : MvPolynomial.IsWeightedHomogeneous w.generatorWeight p
      (w.weight a.toNat + w.weight (r + d).toNat) :=
    ((complete_convex_homogeneous w a ha.le).mul
      (complete_convex_homogeneous w (r + d) hrd)).neg
  have hsuper := w.strict_superadditive (show 0 < a.toNat by omega)
    (show 0 < (r + d).toNat by omega)
  have he : a.toNat + (r + d).toNat = (r + a + d).toNat := by omega
  rw [he] at hsuper
  have hlt : monomialValuation w.generatorWeight p <
      monomialValuation w.generatorWeight q := by
    rw [monomialValuation_eq_of_homogeneous hp hhom,
      complete_monomialValuation w (r + a + d) (by omega)]
    exact WithTop.coe_lt_coe.mpr hsuper
  have hb := strict_lowerBound_of_valuation_lt hp hlt
  have hi : initialForm w.generatorWeight (p + q) = p := by
    rw [initialForm_add_eq_left hp hb, initialForm_eq_of_homogeneous hp hhom]
  have hsum : p + q ≠ 0 := by
    intro hz
    rw [hz, initialForm_zero] at hi
    exact hp hi.symm
  have hval : monomialValuation w.generatorWeight (p + q) =
      (w.weight a.toNat + w.weight (r + d).toNat : WithTop ℝ) := by
    rw [monomialValuation_add_eq_left hlt,
      monomialValuation_eq_of_homogeneous hp hhom, WithTop.coe_add]
  have hrewrite : complete (r + a + d) - complete a * complete (r + d) = p + q := by
    dsimp [p, q]
    ring
  rw [hrewrite]
  exact ⟨hsum, hi, hval⟩

namespace Diagram

variable {n : ℕ}

/-- On an actual common grid, the grid response is the sum of the indexed cofactor defects. -/
theorem gridDefect_response_eq_sum (X Y : Diagram n)
    (hgrid : ∀ j, X.capShift j = Y.capShift j) (a : ℤ) :
    gridResponse (gridDefect X Y) a =
      ∑ j, cofactorDefect X Y j * complete (a + X.capShift j) := by
  rw [gridDefect_response, capPolynomial, capPolynomial, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hgrid j]
  exact (sub_mul _ _ _).symm

/-- The ratio difference is the actual sum of the two-term kernels, not a relation binder. -/
theorem gridDefect_ratio_response_eq_sum (X Y : Diagram n)
    (hgrid : ∀ j, X.capShift j = Y.capShift j) (r a : ℤ) :
    gridResponse (gridDefect X Y) (r + a) -
        complete a * gridResponse (gridDefect X Y) r =
      ∑ j, cofactorDefect X Y j *
        (complete (r + a + X.capShift j) - complete a * complete (r + X.capShift j)) := by
  rw [gridDefect_response_eq_sum X Y hgrid, gridDefect_response_eq_sum X Y hgrid,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem shifted_summand_unique (w : ConvexWeight) (X Y : Diagram n)
    (c : Fin (n + 1)) (hc : c.val = 1) (hGc : cofactorDefect X Y c ≠ 0)
    (hfloor : positiveFloor w X Y = defectAction w X Y c)
    (hzero : cofactorDefect X Y 0 = 0) (a : ℤ) (ha : 0 < a)
    (j : Fin (n + 1)) (hj : j ≠ c) :
    monomialValuation w.generatorWeight
        (cofactorDefect X Y c * complete (a + X.capShift c)) <
      monomialValuation w.generatorWeight
        (cofactorDefect X Y j * complete (a + X.capShift j)) := by
  classical
  have hdc := X.capShift_nonneg c
  have hdj := X.capShift_nonneg j
  have hcomplete : complete (a + X.capShift c) ≠ 0 :=
    complete_ne_zero_of_nonneg _ (by omega)
  have hterm : cofactorDefect X Y c * complete (a + X.capShift c) ≠ 0 :=
    mul_ne_zero hGc hcomplete
  by_cases hGj : cofactorDefect X Y j = 0
  · rw [hGj, zero_mul, monomialValuation_zero, monomialValuation_eq_coe hterm]
    exact WithTop.coe_lt_top _
  have hjpos : 0 < j.val := by
    by_contra h
    have hj0 : j = 0 := Fin.ext (by simpa using (show j.val = 0 by omega))
    exact hGj (by simpa only [hj0] using hzero)
  have hcj : c < j := by
    change c.val < j.val
    have hvne : j.val ≠ c.val := fun h => hj (Fin.ext h)
    omega
  have hfloorj : defectAction w X Y c ≤ defectAction w X Y j := by
    rw [← hfloor]
    apply Finset.inf_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hjpos
  have hα : leastWeight w.generatorWeight (cofactorDefect X Y c) +
      w.weight (X.capShift c).toNat ≤
      leastWeight w.generatorWeight (cofactorDefect X Y j) +
        w.weight (X.capShift j).toNat := by
    unfold defectAction at hfloorj
    rw [monomialValuation_eq_coe hGc, monomialValuation_eq_coe hGj] at hfloorj
    simpa only [← WithTop.coe_add, WithTop.coe_le_coe] using hfloorj
  have hdiff := w.cap_difference_strict ha hdc (X.capShift_strictMono hcj)
  rw [monomialValuation_mul, monomialValuation_mul,
    monomialValuation_eq_coe hGc, monomialValuation_eq_coe hGj,
    complete_monomialValuation w (a + X.capShift c) (by omega),
    complete_monomialValuation w (a + X.capShift j) (by omega)]
  simp only [← WithTop.coe_add, WithTop.coe_lt_coe]
  linarith

section CapFixed

variable (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0)
    (hzero : cofactorDefect X Y 0 = 0)

include hX hY hgrid hv hprefix hchanged hfloor hzero

/-- Column one is the unique lowest actual positive-cap summand; column zero is included. -/
theorem cap_fixed_boundary_summand_unique (a : ℤ) (ha : 0 < a)
    (j : Fin (n + 1)) (hj : j ≠ ⟨1, by have := v.isLt; omega⟩) :
    monomialValuation w.generatorWeight
        (cofactorDefect X Y ⟨1, by have := v.isLt; omega⟩ *
          complete (a + X.capShift ⟨1, by have := v.isLt; omega⟩)) <
      monomialValuation w.generatorWeight
        (cofactorDefect X Y j * complete (a + X.capShift j)) := by
  let c : Fin (n + 1) := ⟨1, by have := v.isLt; omega⟩
  have hGc := cap_fixed_prefix_support w X Y hX hY hgrid v hv hprefix hchanged hfloor
    c (by simp [c]) (by simp [c])
  have hfloorc := (cap_fixed_floor w X Y hX hY hgrid v hv hprefix hchanged hfloor).2.1
  exact shifted_summand_unique w X Y c rfl hGc hfloorc hzero a ha j hj

/-- The actual cap response is nonzero with precisely the column-one initial polynomial. -/
theorem cap_fixed_boundary_response (a : ℤ) (ha : 0 < a) :
    gridResponse (gridDefect X Y) a ≠ 0 ∧
    initialForm w.generatorWeight (gridResponse (gridDefect X Y) a) =
      complete (a + X.capShift ⟨1, by have := v.isLt; omega⟩) *
        initialForm w.generatorWeight (cofactorDefect X Y ⟨1, by have := v.isLt; omega⟩) ∧
    leastWeight w.generatorWeight (gridResponse (gridDefect X Y) a) =
      leastWeight w.generatorWeight (cofactorDefect X Y ⟨1, by have := v.isLt; omega⟩) +
        w.weight (a + X.capShift ⟨1, by have := v.isLt; omega⟩).toNat := by
  classical
  let c : Fin (n + 1) := ⟨1, by have := v.isLt; omega⟩
  let f : Fin (n + 1) → CompleteRing :=
    fun j => cofactorDefect X Y j * complete (a + X.capShift j)
  have hGc := cap_fixed_prefix_support w X Y hX hY hgrid v hv hprefix hchanged hfloor
    c (by simp [c]) (by simp [c])
  have hdc := X.capShift_nonneg c
  have hp : complete (a + X.capShift c) ≠ 0 := complete_ne_zero_of_nonneg _ (by omega)
  have hfc : f c ≠ 0 := mul_ne_zero hGc hp
  have hmin : ∀ j ∈ Finset.univ, j ≠ c →
      monomialValuation w.generatorWeight (f c) < monomialValuation w.generatorWeight (f j) := by
    intro j _ hj
    exact cap_fixed_boundary_summand_unique w X Y hX hY hgrid v hv hprefix hchanged
      hfloor hzero a ha j hj
  have hi := initialForm_sum_unique Finset.univ f (Finset.mem_univ c) hfc hmin
  rw [gridDefect_response_eq_sum X Y hgrid]
  refine ⟨sum_ne_zero_of_unique_min Finset.univ f (Finset.mem_univ c) hfc hmin, ?_, ?_⟩
  · rw [hi.1, initialForm_mul hGc hp, complete_initialForm w _ (by omega), mul_comm]
  · rw [hi.2, leastWeight_mul hGc hp, complete_leastWeight w _ (by omega)]

/-- The strict-superadditive ratio kernels again have column one as their unique minimum. -/
theorem cap_fixed_ratio_summand_unique (r a : ℤ) (hr : 0 < r) (ha : 0 < a)
    (j : Fin (n + 1)) (hj : j ≠ ⟨1, by have := v.isLt; omega⟩) :
    monomialValuation w.generatorWeight
        (cofactorDefect X Y ⟨1, by have := v.isLt; omega⟩ *
          (complete (r + a + X.capShift ⟨1, by have := v.isLt; omega⟩) -
            complete a * complete (r + X.capShift ⟨1, by have := v.isLt; omega⟩))) <
      monomialValuation w.generatorWeight
        (cofactorDefect X Y j *
          (complete (r + a + X.capShift j) - complete a * complete (r + X.capShift j))) := by
  let c : Fin (n + 1) := ⟨1, by have := v.isLt; omega⟩
  have hval (k : Fin (n + 1)) :
      monomialValuation w.generatorWeight
          (cofactorDefect X Y k *
            (complete (r + a + X.capShift k) - complete a * complete (r + X.capShift k))) =
        monomialValuation w.generatorWeight
          (cofactorDefect X Y k * complete (r + X.capShift k)) +
            (w.weight a.toNat : WithTop ℝ) := by
    have hd := X.capShift_nonneg k
    rw [monomialValuation_mul,
      (boundary_ratio_kernel w r a (X.capShift k) hr ha hd).2.2,
      monomialValuation_mul, complete_monomialValuation w _ (by omega)]
    ac_rfl
  rw [hval c, hval j]
  exact WithTop.add_lt_add_right WithTop.coe_ne_top
    (cap_fixed_boundary_summand_unique w X Y hX hY hgrid v hv hprefix hchanged
      hfloor hzero r hr j hj)

/-- Exact initial polynomial and nonvanishing of the actual positive-base ratio difference. -/
theorem cap_fixed_ratio_response (r a : ℤ) (hr : 0 < r) (ha : 0 < a) :
    gridResponse (gridDefect X Y) (r + a) -
        complete a * gridResponse (gridDefect X Y) r ≠ 0 ∧
    initialForm w.generatorWeight
        (gridResponse (gridDefect X Y) (r + a) -
          complete a * gridResponse (gridDefect X Y) r) =
      -(complete a * complete (r + X.capShift ⟨1, by have := v.isLt; omega⟩) *
        initialForm w.generatorWeight (cofactorDefect X Y ⟨1, by have := v.isLt; omega⟩)) := by
  classical
  let c : Fin (n + 1) := ⟨1, by have := v.isLt; omega⟩
  let f : Fin (n + 1) → CompleteRing := fun j => cofactorDefect X Y j *
    (complete (r + a + X.capShift j) - complete a * complete (r + X.capShift j))
  have hGc := cap_fixed_prefix_support w X Y hX hY hgrid v hv hprefix hchanged hfloor
    c (by simp [c]) (by simp [c])
  have hk := boundary_ratio_kernel w r a (X.capShift c) hr ha (X.capShift_nonneg c)
  have hfc : f c ≠ 0 := mul_ne_zero hGc hk.1
  have hmin : ∀ j ∈ Finset.univ, j ≠ c →
      monomialValuation w.generatorWeight (f c) < monomialValuation w.generatorWeight (f j) := by
    intro j _ hj
    exact cap_fixed_ratio_summand_unique w X Y hX hY hgrid v hv hprefix hchanged
      hfloor hzero r a hr ha j hj
  have hi := (initialForm_sum_unique Finset.univ f (Finset.mem_univ c) hfc hmin).1
  rw [gridDefect_ratio_response_eq_sum X Y hgrid]
  refine ⟨sum_ne_zero_of_unique_min Finset.univ f (Finset.mem_univ c) hfc hmin, ?_⟩
  rw [hi, initialForm_mul hGc hk.1, hk.2.1]
  ring

/-- No actual ratio identity occurs at any nonnegative base and positive cap. -/
theorem cap_fixed_ratio_exclusion (r a : ℤ) (hr : 0 ≤ r) (ha : 0 < a) :
    gridResponse (gridDefect X Y) (r + a) ≠
      complete a * gridResponse (gridDefect X Y) r := by
  by_cases hz : r = 0
  · subst r
    have hn : 0 < n := by have := v.isLt; omega
    simpa only [zero_add, gridDefect_response_zero X Y hn hn, mul_zero] using
      (cap_fixed_boundary_response w X Y hX hY hgrid v hv hprefix hchanged hfloor hzero a ha).1
  · exact sub_ne_zero.mp
      (cap_fixed_ratio_response w X Y hX hY hgrid v hv hprefix hchanged hfloor hzero
        r a (by omega) ha).1

end CapFixed

/-- Actual equal pairs cannot obey any positive-cap ratio identity.  Common grid,
first split, and strict floor are produced from Schur equality in the proof. -/
theorem equal_pair_ratio_exclusion (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hinner : X.inner = Y.inner)
    (hne : X ≠ Y) (heq : X.schurFunction = Y.schurFunction)
    (r a : ℤ) (hr : 0 ≤ r) (ha : 0 < a) :
    gridResponse (gridDefect X Y) (r + a) ≠
      complete a * gridResponse (gridDefect X Y) r := by
  have hn := equality_normalizes_cap X Y hX hY heq
    (by
      intro i j hij
      have : i = j := Fin.ext hij
      subst j
      exact congrFun hinner i)
  have hgrid : ∀ j, X.capShift j = Y.capShift j := fun j => hn.2.2 j j rfl
  obtain ⟨v, hv, hprefix, hchanged⟩ :=
    exists_first_changed_row X Y hX.1 hn.2.1 hinner hne
  have hrows : X.rowLengthMultiset = Y.rowLengthMultiset := by
    rw [rowLengthMultiset_eq_list X, rowLengthMultiset_eq_list Y]
    exact rowLength_multiset_eq_of_schurFunction_eq X Y hX hY heq
  have hfloor := equal_pair_strict_floor squareWeight X Y hX hY hgrid hrows heq
    v hprefix hchanged
  exact cap_fixed_ratio_exclusion squareWeight X Y hX hY hgrid v hv hprefix hchanged
    hfloor (cofactorDefect_zero_of_schur_eq X Y heq) r a hr ha

end Diagram
end SkewSchurReconstruction
