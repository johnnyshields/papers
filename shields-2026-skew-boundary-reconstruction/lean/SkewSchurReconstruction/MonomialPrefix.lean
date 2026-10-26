/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CapFixedRigidity
import SkewSchurReconstruction.EqualPairRigidity

/-!
# Weight-independent monomial prefixes

Formalizes `prop:monomial-prefix` and `eq:monomial-prefix-exchange` in
“First-split localization and cap-fixed rigidity” (`sec:localization`).
The first-split determinant supplies the initial unit monomial.  The actual
common-row defect relation and the cap-fixed minimizing pairs supply the
successive exchanges.  Polynomial coefficient injectivity then supplies
monomiality, rather than assuming it.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

private theorem prefix_initialForm_neg {w : ℕ+ → ℝ} {p : CompleteRing}
    (hp : p ≠ 0) : initialForm w (-p) = -initialForm w p := by
  have hm : (-1 : CompleteRing) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hh : MvPolynomial.IsWeightedHomogeneous w (-1 : CompleteRing) 0 := by
    simpa using MvPolynomial.isWeightedHomogeneous_C w (-1 : ℤ)
  rw [← neg_one_mul p, initialForm_mul hm hp,
    initialForm_eq_of_homogeneous hm hh, neg_one_mul]

/-- Multiplication by a unit-coefficient monomial cannot conceal extra terms. -/
private theorem monomial_of_monomial_mul {p : CompleteRing} (hp : p ≠ 0)
    (a b : ℕ+ →₀ ℕ) (c : ℤ)
    (he : MvPolynomial.monomial a 1 * p = MvPolynomial.monomial b c) :
    ∃ d, p = MvPolynomial.monomial d c := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hp
  have hcoeff (e : ℕ+ →₀ ℕ) :
      p.coeff e = if b = a + e then c else 0 := by
    have h := congrArg (fun q : CompleteRing => q.coeff (a + e)) he
    simpa only [MvPolynomial.coeff_monomial_mul, one_mul,
      MvPolynomial.coeff_monomial] using h
  have hb : b = a + d := by
    by_contra hn
    exact hd (by simp only [hcoeff d, ite_eq_right hn])
  have hdc : p.coeff d = c := by rw [hcoeff, ite_eq_left hb]
  refine ⟨d, ?_⟩
  rw [← hdc]
  apply MvPolynomial.eq_monomial_of_support_subset_singleton
  intro e he'
  have hne := MvPolynomial.mem_support_iff.mp he'
  have hbe : b = a + e := by
    by_contra hn
    exact hne (by simp only [hcoeff e, ite_eq_right hn])
  exact add_left_cancel (hbe.symm.trans hb)

namespace Diagram

variable {n : ℕ}

/-- The unit sign is fixed by the changed row, not by the convex weight. -/
noncomputable def prefixSign (X Y : Diagram n) (v : Fin n) (j : Fin (n + 1)) : ℤ :=
  (if X.rowParam v < Y.rowParam v then 1 else -1) * (-1) ^ j.val

/-- Consecutive prefix signs alternate. -/
theorem prefixSign_adjacent (X Y : Diagram n) (v : Fin n)
    (a b : Fin (n + 1)) (hab : b.val = a.val + 1) :
    prefixSign X Y v a = -prefixSign X Y v b := by
  unfold prefixSign
  rw [hab, pow_succ]
  ring

/-- Every prefix coefficient is a unit of the integral coefficient ring. -/
theorem prefixSign_eq_one_or_neg_one (X Y : Diagram n) (v : Fin n)
    (j : Fin (n + 1)) : prefixSign X Y v j = 1 ∨ prefixSign X Y v j = -1 := by
  have hp : (-1 : ℤ) ^ j.val = 1 ∨ (-1 : ℤ) ^ j.val = -1 := by
    induction j.val with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rcases ih with h | h
      · right; simp [pow_succ, h]
      · left; simp [pow_succ, h]
  unfold prefixSign
  split_ifs <;> rcases hp with h | h <;> simp [h]

private theorem cofactor_initial_monomial (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (j : Fin (n + 1)) :
    ∃ d, initialForm w.generatorWeight (X.cofactor j) =
      MvPolynomial.monomial d ((-1 : ℤ) ^ j.val) := by
  classical
  let l := Finset.univ.toList.map (fun i : Fin n => (X.peelIndex j i).toNat)
  have hp : (∏ i, complete (X.peelIndex j i)) =
      MvPolynomial.monomial (exponentVector l) (1 : ℤ) := by
    have ht : ∀ i, ((X.peelIndex j i).toNat : ℤ) = X.peelIndex j i := by
      intro i
      have := X.peelIndex_nonneg hX j i
      omega
    have he := prod_complete_eq_monomial l
    simp only [l, List.map_map, Function.comp_def] at he
    simp_rw [ht] at he
    simpa using he
  refine ⟨exponentVector l, ?_⟩
  rw [cofactor_initialForm w X hX j, hp]
  have hs : (-1 : CompleteRing) ^ j.val =
      MvPolynomial.C ((-1 : ℤ) ^ j.val) := by simp
  rw [hs, MvPolynomial.C_mul_monomial, mul_one]

/-- The lower actual parent alone supplies the first-split initial form, with
its direction fixed by the changed row for every convex weight. -/
theorem first_split_initialForm (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    initialForm w.generatorWeight (cofactorDefect X Y v.succ) =
      if X.rowParam v < Y.rowParam v then
        (-1 : CompleteRing) ^ v.succ.val * ∏ i, complete (X.peelIndex v.succ i)
      else -((-1 : CompleteRing) ^ v.succ.val * ∏ i, complete (Y.peelIndex v.succ i)) := by
  have hx := X.cofactor_ne_zero w hX v.succ
  have hy := Y.cofactor_ne_zero w hY v.succ
  by_cases hlt : X.rowParam v < Y.rowParam v
  · rw [ite_eq_left hlt]
    have ha := parentAction_first_split_lt w X Y hX hY hgrid hrows v hprefix hlt
    have hl : leastWeight w.generatorWeight (X.cofactor v.succ) <
        leastWeight w.generatorWeight (Y.cofactor v.succ) := by
      unfold parentAction at ha
      rw [← hgrid v.succ] at ha
      linarith
    have hv : monomialValuation w.generatorWeight (X.cofactor v.succ) <
        monomialValuation w.generatorWeight (-Y.cofactor v.succ) := by
      rw [monomialValuation_neg, monomialValuation_eq_coe hx,
        monomialValuation_eq_coe hy]
      exact WithTop.coe_lt_coe.mpr hl
    have hi := initialForm_add_eq_left hx (strict_lowerBound_of_valuation_lt hx hv)
    rw [cofactorDefect, sub_eq_add_neg, hi, cofactor_initialForm w X hX]
  · rw [ite_eq_right hlt]
    have hgt : Y.rowParam v < X.rowParam v := by omega
    have ha := parentAction_first_split_lt w Y X hY hX (fun j => (hgrid j).symm)
      hrows.symm v (fun i hi => (hprefix i hi).symm) hgt
    have hl : leastWeight w.generatorWeight (Y.cofactor v.succ) <
        leastWeight w.generatorWeight (X.cofactor v.succ) := by
      unfold parentAction at ha
      rw [← hgrid v.succ] at ha
      linarith
    have hn := neg_ne_zero.mpr hy
    have hv : monomialValuation w.generatorWeight (-Y.cofactor v.succ) <
        monomialValuation w.generatorWeight (X.cofactor v.succ) := by
      rw [monomialValuation_neg, monomialValuation_eq_coe hx,
        monomialValuation_eq_coe hy]
      exact WithTop.coe_lt_coe.mpr hl
    have hi := initialForm_add_eq_left hn (strict_lowerBound_of_valuation_lt hn hv)
    rw [cofactorDefect, show X.cofactor v.succ - Y.cofactor v.succ =
      -Y.cofactor v.succ + X.cofactor v.succ by ring, hi,
      prefix_initialForm_neg hy, cofactor_initialForm w Y hY]

private theorem first_split_unit_monomial (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset) (v : Fin n)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    ∃ d, initialForm w.generatorWeight (cofactorDefect X Y v.succ) =
      MvPolynomial.monomial d (prefixSign X Y v v.succ) := by
  have he := first_split_initialForm w X Y hX hY hgrid hrows v hprefix hchanged
  by_cases hlt : X.rowParam v < Y.rowParam v
  · obtain ⟨d, hd⟩ := cofactor_initial_monomial w X hX v.succ
    refine ⟨d, ?_⟩
    rw [ite_eq_left hlt, ← cofactor_initialForm w X hX v.succ, hd] at he
    simpa [prefixSign, hlt] using he
  · obtain ⟨d, hd⟩ := cofactor_initial_monomial w Y hY v.succ
    refine ⟨d, ?_⟩
    rw [ite_eq_right hlt, ← cofactor_initialForm w Y hY v.succ, hd] at he
    simpa [prefixSign, hlt, map_neg] using he

/-- The initial two-column relation is produced from the exact common-row
relation by projecting at its actual least weight. -/
theorem cap_fixed_initial_pair_relation (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0) (i : Fin v.val) :
    let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
    let a : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩
    let b : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩
    complete (X.capShift a - X.rowParam r) *
        initialForm w.generatorWeight (cofactorDefect X Y a) +
      complete (X.capShift b - X.rowParam r) *
        initialForm w.generatorWeight (cofactorDefect X Y b) = 0 := by
  classical
  dsimp only
  let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
  let a : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩
  let b : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩
  let f := fun j => complete (X.capShift j - X.rowParam r) * cofactorDefect X Y j
  have hpair (j : Fin (n + 1)) :
      j ∈ defectMinimizers w X Y (X.rowParam r) ↔ j = a ∨ j = b := by
    have h := cap_fixed_minimizer_mem_iff w X Y hX hY hgrid v hv hprefix hchanged hfloor i j
    simpa only [r, a, b, Fin.ext_iff, Fin.val_mk] using h
  obtain ⟨haf, hamin⟩ := (mem_defectMinimizers w X Y _ a).mp
    ((hpair a).mpr (Or.inl rfl))
  obtain ⟨hbf, hbmin⟩ := (mem_defectMinimizers w X Y _ b).mp
    ((hpair b).mpr (Or.inr rfl))
  obtain ⟨hafeas, hag⟩ := (defectTiltedCost_finite_iff w X Y _ a).mp haf
  obtain ⟨hbfeas, hbg⟩ := (defectTiltedCost_finite_iff w X Y _ b).mp hbf
  have hca := (complete_ne_zero_iff _).mpr (sub_nonneg.mpr hafeas)
  have hcb := (complete_ne_zero_iff _).mpr (sub_nonneg.mpr hbfeas)
  have hfa : f a ≠ 0 := mul_ne_zero hca hag
  have hfb : f b ≠ 0 := mul_ne_zero hcb hbg
  have hvab : monomialValuation w.generatorWeight (f a) =
      monomialValuation w.generatorWeight (f b) := by
    simpa only [f, common_summand_valuation] using le_antisymm (hamin b) (hbmin a)
  have hlab : leastWeight w.generatorWeight (f a) =
      leastWeight w.generatorWeight (f b) := by
    rw [monomialValuation_eq_coe hfa, monomialValuation_eq_coe hfb] at hvab
    exact WithTop.coe_injective hvab
  let C : CompleteRing →ₗ[ℤ] CompleteRing :=
    MvPolynomial.weightedHomogeneousComponent w.generatorWeight
    (leastWeight w.generatorWeight (f a))
  have hother (j : Fin (n + 1)) (hja : j ≠ a) (hjb : j ≠ b) : C (f j) = 0 := by
    have hl : monomialValuation w.generatorWeight (f a) <
        monomialValuation w.generatorWeight (f j) := by
      apply lt_of_le_of_ne
      · simpa only [f, common_summand_valuation] using hamin j
      · intro he
        have hc : defectTiltedCost w X Y (X.rowParam r) j =
            defectTiltedCost w X Y (X.rowParam r) a := by
          simpa only [f, common_summand_valuation] using he.symm
        have hj : j ∈ defectMinimizers w X Y (X.rowParam r) := by
          apply (mem_defectMinimizers w X Y _ j).mpr
          rw [hc]
          exact ⟨haf, hamin⟩
        exact ((hpair j).mp hj).elim hja hjb
    exact component_eq_zero_of_strict_lowerBound
      (strict_lowerBound_of_valuation_lt hfa hl)
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
  have hs : (∑ j, C (f j)) = C (f a) + C (f b) := by
    calc
      (∑ j, C (f j)) = ∑ j ∈ ({a, b} : Finset (Fin (n + 1))), C (f j) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        have hn : j ≠ a ∧ j ≠ b := by simpa using hj
        exact hother j hn.1 hn.2
      _ = C (f a) + C (f b) := Finset.sum_pair hab
  have hrel : ∑ j, f j = 0 :=
    common_row_defect_relation X Y (funext hgrid) r
      (hprefix r (by dsimp [r]; exact i.isLt))
  have hinit : C (f a) + C (f b) = 0 := by
    have h := congrArg (fun p => C p) hrel
    rw [map_sum, map_zero, hs] at h
    exact h
  change initialForm w.generatorWeight (f a) + C (f b) = 0 at hinit
  change initialForm w.generatorWeight (f a) +
    MvPolynomial.weightedHomogeneousComponent w.generatorWeight
      (leastWeight w.generatorWeight (f a)) (f b) = 0 at hinit
  rw [hlab] at hinit
  change initialForm w.generatorWeight (f a) + initialForm w.generatorWeight (f b) = 0 at hinit
  rw [show f a = complete (X.capShift a - X.rowParam r) * cofactorDefect X Y a from rfl,
    show f b = complete (X.capShift b - X.rowParam r) * cofactorDefect X Y b from rfl,
    initialForm_mul hca hag, initialForm_mul hcb hbg,
    complete_initialForm w _ (sub_nonneg.mpr hafeas),
    complete_initialForm w _ (sub_nonneg.mpr hbfeas)] at hinit
  exact hinit

/-- Every supported cap-fixed prefix initial form is one monomial with the
explicit alternating unit coefficient. -/
theorem cap_fixed_prefix_unit_monomial (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0)
    (j : Fin (n + 1)) (hjpos : 0 < j.val) (hjupper : j.val ≤ v.val + 1) :
    ∃ d, initialForm w.generatorWeight (cofactorDefect X Y j) =
      MvPolynomial.monomial d (prefixSign X Y v j) := by
  classical
  have hrows := rowLengths_eq_of_floor w X Y hX hY hgrid hfloor
  have hbase := first_split_unit_monomial w X Y hX hY hgrid hrows v hprefix hchanged
  have hdesc : ∀ t (k : Fin (n + 1)), k.val + t = v.val + 1 → 0 < k.val →
      ∃ d, initialForm w.generatorWeight (cofactorDefect X Y k) =
        MvPolynomial.monomial d (prefixSign X Y v k) := by
    intro t
    induction t with
    | zero =>
      intro k hk _
      have he : k = v.succ := Fin.ext (by simpa using hk)
      simpa only [he] using hbase
    | succ t ih =>
      intro k hk hkpos
      let b : Fin (n + 1) := ⟨k.val + 1, by have := v.isLt; omega⟩
      let i : Fin v.val := ⟨k.val - 1, by omega⟩
      let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
      have ha : (⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩ : Fin (n + 1)) = k := by
        apply Fin.ext; dsimp [i]; omega
      have hb : (⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩ : Fin (n + 1)) = b := by
        apply Fin.ext; dsimp [i, b]; omega
      obtain ⟨d, hd⟩ := ih b (by dsimp [b]; omega) (by dsimp [b]; omega)
      have hrel := cap_fixed_initial_pair_relation w X Y hX hY hgrid v hv hprefix hchanged hfloor i
      dsimp only at hrel
      rw [ha, hb, hd] at hrel
      change complete (X.capShift k - X.rowParam r) *
          initialForm w.generatorWeight (cofactorDefect X Y k) +
        complete (X.capShift b - X.rowParam r) *
          MvPolynomial.monomial d (prefixSign X Y v b) = 0 at hrel
      have hmin := (cap_fixed_minimizer_mem_iff w X Y hX hY hgrid
        v hv hprefix hchanged hfloor i k).mpr
        (Or.inl (by dsimp [i]; omega))
      have hminb := (cap_fixed_minimizer_mem_iff w X Y hX hY hgrid
        v hv hprefix hchanged hfloor i b).mpr
        (Or.inr (by dsimp [i, b]; omega))
      have hf := ((defectTiltedCost_finite_iff w X Y _ k).mp
        ((mem_defectMinimizers w X Y _ k).mp hmin).1).1
      have hfb := ((defectTiltedCost_finite_iff w X Y _ b).mp
        ((mem_defectMinimizers w X Y _ b).mp hminb).1).1
      have hz : 0 ≤ X.capShift k - X.rowParam r := sub_nonneg.mpr hf
      have hzb : 0 ≤ X.capShift b - X.rowParam r := sub_nonneg.mpr hfb
      have hnat : (((X.capShift k - X.rowParam r).toNat : ℕ) : ℤ) =
          X.capShift k - X.rowParam r := by omega
      have hnatb : (((X.capShift b - X.rowParam r).toNat : ℕ) : ℤ) =
          X.capShift b - X.rowParam r := by omega
      have hc := complete_eq_monomial_index (X.capShift k - X.rowParam r).toNat
      have hcb := complete_eq_monomial_index (X.capShift b - X.rowParam r).toNat
      rw [hnat] at hc
      rw [hnatb] at hcb
      rw [hc, hcb, MvPolynomial.monomial_mul_monomial, one_mul] at hrel
      have he : MvPolynomial.monomial
          (completeIndexExponent (X.capShift k - X.rowParam r).toNat) 1 *
          initialForm w.generatorWeight (cofactorDefect X Y k) =
        MvPolynomial.monomial
          (completeIndexExponent (X.capShift b - X.rowParam r).toNat + d)
          (-prefixSign X Y v b) := by
        simpa only [map_neg] using (eq_neg_of_add_eq_zero_left hrel)
      have hg := cap_fixed_prefix_support w X Y hX hY hgrid v hv hprefix hchanged hfloor k
        hkpos (by omega)
      obtain ⟨e, he'⟩ := monomial_of_monomial_mul (initialForm_ne_zero hg) _ _ _ he
      refine ⟨e, ?_⟩
      rw [← prefixSign_adjacent X Y v k b rfl] at he'
      exact he'
  exact hdesc (v.val + 1 - j.val) j (by omega) hjpos

/-- Cancelling the same complete multiplier down the actual minimizing chain
makes the entire prefix independent of any two weights satisfying the floor. -/
theorem cap_fixed_prefix_initialForm_eq (w u : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloorw : positiveFloor w X Y < defectAction w X Y 0)
    (hflooru : positiveFloor u X Y < defectAction u X Y 0)
    (j : Fin (n + 1)) (hjpos : 0 < j.val) (hjupper : j.val ≤ v.val + 1) :
    initialForm w.generatorWeight (cofactorDefect X Y j) =
      initialForm u.generatorWeight (cofactorDefect X Y j) := by
  have hrows := rowLengths_eq_of_floor w X Y hX hY hgrid hfloorw
  have hbase : initialForm w.generatorWeight (cofactorDefect X Y v.succ) =
      initialForm u.generatorWeight (cofactorDefect X Y v.succ) := by
    rw [first_split_initialForm w X Y hX hY hgrid hrows v hprefix hchanged,
      first_split_initialForm u X Y hX hY hgrid hrows v hprefix hchanged]
  have hdesc : ∀ t (k : Fin (n + 1)), k.val + t = v.val + 1 → 0 < k.val →
      initialForm w.generatorWeight (cofactorDefect X Y k) =
        initialForm u.generatorWeight (cofactorDefect X Y k) := by
    intro t
    induction t with
    | zero =>
      intro k hk _
      have he : k = v.succ := Fin.ext (by simpa using hk)
      simpa only [he] using hbase
    | succ t ih =>
      intro k hk hkpos
      let b : Fin (n + 1) := ⟨k.val + 1, by have := v.isLt; omega⟩
      let i : Fin v.val := ⟨k.val - 1, by omega⟩
      let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
      have ha : (⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩ : Fin (n + 1)) = k := by
        apply Fin.ext; dsimp [i]; omega
      have hb : (⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩ : Fin (n + 1)) = b := by
        apply Fin.ext; dsimp [i, b]; omega
      have he := ih b (by dsimp [b]; omega) (by dsimp [b]; omega)
      have hw := cap_fixed_initial_pair_relation w X Y hX hY hgrid v hv hprefix hchanged hfloorw i
      have hu := cap_fixed_initial_pair_relation u X Y hX hY hgrid v hv hprefix hchanged hflooru i
      dsimp only at hw hu
      rw [ha, hb, he] at hw
      rw [ha, hb] at hu
      have hm : complete (X.capShift k - X.rowParam r) ≠ 0 := by
        apply (complete_ne_zero_iff _).mpr
        have hmin := (cap_fixed_minimizer_mem_iff w X Y hX hY hgrid
          v hv hprefix hchanged hfloorw i k).mpr
          (Or.inl (by dsimp [i]; omega))
        exact sub_nonneg.mpr (((defectTiltedCost_finite_iff w X Y _ k).mp
          ((mem_defectMinimizers w X Y _ k).mp hmin).1).1)
      apply mul_left_cancel₀ hm
      exact (eq_neg_of_add_eq_zero_left hw).trans (eq_neg_of_add_eq_zero_left hu).symm
  exact hdesc (v.val + 1 - j.val) j (by omega) hjpos

/-- The unsigned monomials obey the exact exchange identity once their
alternating integral unit coefficients are cancelled. -/
private theorem cap_fixed_prefix_monomial_exchange (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0) (i : Fin v.val)
    (d e : ℕ+ →₀ ℕ)
    (hd : initialForm w.generatorWeight
      (cofactorDefect X Y ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩) =
        MvPolynomial.monomial d
          (prefixSign X Y v ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩))
    (he : initialForm w.generatorWeight
      (cofactorDefect X Y ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩) =
        MvPolynomial.monomial e
          (prefixSign X Y v ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩)) :
    let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
    let a : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩
    let b : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩
    complete (X.capShift a - X.rowParam r) * MvPolynomial.monomial d (1 : ℤ) =
      complete (X.capShift b - X.rowParam r) * MvPolynomial.monomial e (1 : ℤ) := by
  dsimp only
  let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
  let a : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩
  let b : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩
  have hs := prefixSign_adjacent X Y v a b rfl
  have hrel := cap_fixed_initial_pair_relation w X Y hX hY hgrid v hv hprefix hchanged hfloor i
  dsimp only at hrel
  rw [hd, he] at hrel
  change complete (X.capShift a - X.rowParam r) * MvPolynomial.monomial d (prefixSign X Y v a) +
    complete (X.capShift b - X.rowParam r) *
      MvPolynomial.monomial e (prefixSign X Y v b) = 0 at hrel
  have hsm (f : ℕ+ →₀ ℕ) (c : ℤ) : MvPolynomial.monomial f c =
      MvPolynomial.C c * MvPolynomial.monomial f (1 : ℤ) := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  have hsb : prefixSign X Y v b = -prefixSign X Y v a := by omega
  rw [hsm d, hsm e, hsb, map_neg] at hrel
  have hz : MvPolynomial.C (prefixSign X Y v a) ≠ (0 : CompleteRing) := by
    rcases prefixSign_eq_one_or_neg_one X Y v a with h | h <;> simp [h]
  apply mul_left_cancel₀ hz
  have hf : MvPolynomial.C (prefixSign X Y v a) *
      (complete (X.capShift a - X.rowParam r) * MvPolynomial.monomial d (1 : ℤ)) =
    MvPolynomial.C (prefixSign X Y v a) *
      (complete (X.capShift b - X.rowParam r) * MvPolynomial.monomial e (1 : ℤ)) := by
    linear_combination hrel
  exact hf

/-- The cap-fixed certificate uses the square weight only to select its
exponents.  Its unit coefficients and exchanges hold for every weight under
the stated floor hypotheses. -/
theorem cap_fixed_monomial_prefix (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : ∀ w : ConvexWeight, positiveFloor w X Y < defectAction w X Y 0) :
    ∃ d : Fin (n + 1) → ℕ+ →₀ ℕ,
      (∀ j : Fin (n + 1), 0 < j.val → j.val ≤ v.val + 1 →
        (prefixSign X Y v j = 1 ∨ prefixSign X Y v j = -1) ∧
        ∀ w : ConvexWeight, initialForm w.generatorWeight (cofactorDefect X Y j) =
          MvPolynomial.monomial (d j) (prefixSign X Y v j)) ∧
      ∀ i : Fin v.val,
        let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
        let a : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩
        let b : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩
        prefixSign X Y v a = -prefixSign X Y v b ∧
        complete (X.capShift a - X.rowParam r) * MvPolynomial.monomial (d a) (1 : ℤ) =
          complete (X.capShift b - X.rowParam r) * MvPolynomial.monomial (d b) (1 : ℤ) := by
  classical
  have hex : ∀ j : Fin (n + 1), ∃ e : ℕ+ →₀ ℕ,
      0 < j.val → j.val ≤ v.val + 1 →
        initialForm squareWeight.generatorWeight (cofactorDefect X Y j) =
          MvPolynomial.monomial e (prefixSign X Y v j) := by
    intro j
    by_cases hj : 0 < j.val ∧ j.val ≤ v.val + 1
    · obtain ⟨e, he⟩ := cap_fixed_prefix_unit_monomial squareWeight X Y hX hY hgrid
        v hv hprefix hchanged (hfloor squareWeight) j hj.1 hj.2
      exact ⟨e, fun _ _ => he⟩
    · exact ⟨0, fun hp hu => False.elim (hj ⟨hp, hu⟩)⟩
  choose d hd using hex
  refine ⟨d, ?_, ?_⟩
  · intro j hjpos hjupper
    refine ⟨prefixSign_eq_one_or_neg_one X Y v j, ?_⟩
    intro w
    exact (cap_fixed_prefix_initialForm_eq w squareWeight X Y hX hY hgrid
      v hv hprefix hchanged (hfloor w) (hfloor squareWeight) j hjpos hjupper).trans
      (hd j hjpos hjupper)
  · intro i
    dsimp only
    let a : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩
    let b : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩
    refine ⟨prefixSign_adjacent X Y v a b rfl, ?_⟩
    apply cap_fixed_prefix_monomial_exchange squareWeight X Y hX hY hgrid
      v hv hprefix hchanged (hfloor squareWeight) i (d a) (d b)
    · exact hd a (by dsimp [a]; omega) (by dsimp [a]; have := i.isLt; omega)
    · exact hd b (by dsimp [b]; omega) (by dsimp [b]; have := i.isLt; omega)

/-- `prop:monomial-prefix` for actual distinct connected diagrams with the same
inner boundary and the same Schur function.  First-change data, every floor,
the monomials, and their alternating signs are all produced from these inputs. -/
theorem equal_pair_monomial_prefix (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hinner : X.inner = Y.inner) (hne : X ≠ Y)
    (heq : X.schurFunction = Y.schurFunction) :
    ∃ v : Fin n, 0 < v.val ∧
      (∀ j, X.capShift j = Y.capShift j) ∧
      (∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i) ∧
      X.rowParam v ≠ Y.rowParam v ∧
      ∃ d : Fin (n + 1) → ℕ+ →₀ ℕ,
        (∀ j : Fin (n + 1), 0 < j.val → j.val ≤ v.val + 1 →
          (prefixSign X Y v j = 1 ∨ prefixSign X Y v j = -1) ∧
          ∀ w : ConvexWeight, initialForm w.generatorWeight (cofactorDefect X Y j) =
            MvPolynomial.monomial (d j) (prefixSign X Y v j)) ∧
        ∀ i : Fin v.val,
          let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
          let a : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩
          let b : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩
          prefixSign X Y v a = -prefixSign X Y v b ∧
          complete (X.capShift a - X.rowParam r) * MvPolynomial.monomial (d a) (1 : ℤ) =
            complete (X.capShift b - X.rowParam r) * MvPolynomial.monomial (d b) (1 : ℤ) := by
  obtain ⟨v, hv, hgrid, hprefix, hchanged, hchain⟩ :=
    equal_pair_rigidity X Y hX hY hinner hne heq
  have hanchor := (hchain squareWeight).2.2 v.succ
    (by simp only [Fin.val_succ]; omega) (by change v.val + 1 ≤ v.val + 1; exact le_rfl)
  have hfloor : positiveFloor squareWeight X Y < defectAction squareWeight X Y 0 := by
    have hle : positiveFloor squareWeight X Y ≤ defectAction squareWeight X Y v.succ := by
      apply Finset.inf_le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ]
      omega
    have hfinite : defectAction squareWeight X Y v.succ ≠ ⊤ :=
      fun ht => hanchor ((defectAction_eq_top_iff squareWeight X Y v.succ).mp ht)
    have hzero := cofactorDefect_zero_of_schur_eq X Y heq
    rw [(defectAction_eq_top_iff squareWeight X Y 0).mpr hzero]
    exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfinite)
  have hrows := rowLengths_eq_of_floor squareWeight X Y hX hY hgrid hfloor
  have hfloors (w : ConvexWeight) : positiveFloor w X Y < defectAction w X Y 0 :=
    equal_pair_strict_floor w X Y hX hY hgrid hrows heq v hprefix hchanged
  exact ⟨v, hv, hgrid, hprefix, hchanged,
    cap_fixed_monomial_prefix X Y hX hY hgrid v hv hprefix hchanged hfloors⟩

end Diagram
end SkewSchurReconstruction
