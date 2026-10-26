/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.FirstSplit
import SkewSchurReconstruction.MinimizerChains
import SkewSchurReconstruction.GeneratorMonomials

/-!
# Actual cap-fixed minimizing chains

Producer closure for “Adjacent-edge rigidity at a fixed cap”
(`thm:cap-fixed-rigidity`) in “First-split localization and cap-fixed rigidity”
(`sec:localization`).  The floor supplies equal initial energies and the
row-length multiset.  Actual common-row determinant relations then supply
balancing, and strict Monge supplies interlacing.  Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

variable {n : ℕ}

/-- The positive normalized defect floor excludes column zero. -/
noncomputable def positiveFloor (w : ConvexWeight) (X Y : Diagram n) : WithTop ℝ :=
  (Finset.univ.filter (fun j : Fin (n + 1) => 0 < j.val)).inf (defectAction w X Y)

/-- Finite global minimizers of the actual tilted defect costs. -/
noncomputable def defectMinimizers (w : ConvexWeight) (X Y : Diagram n)
    (A : ℤ) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun j => defectTiltedCost w X Y A j ≠ ⊤ ∧
    ∀ k, defectTiltedCost w X Y A j ≤ defectTiltedCost w X Y A k)

@[simp] theorem mem_defectMinimizers (w : ConvexWeight) (X Y : Diagram n)
    (A : ℤ) (j : Fin (n + 1)) :
    j ∈ defectMinimizers w X Y A ↔ defectTiltedCost w X Y A j ≠ ⊤ ∧
      ∀ k, defectTiltedCost w X Y A j ≤ defectTiltedCost w X Y A k := by
  classical
  simp [defectMinimizers]

/-- Convexity and nonnegative row parameters make actual parent actions nondecreasing. -/
theorem parentAction_step_nonneg (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (k : Fin n) :
    parentAction w X k.castSucc ≤ parentAction w X k.succ := by
  have hr := parentAction_recurrence w X hX k
  have ha := X.rowParam_nonneg k
  by_cases hz : X.rowParam k = 0
  · simp only [hz, sub_zero] at hr
    linarith
  · have hm := w.strict_monge_int (show 0 < X.rowParam k by omega)
      (X.capShift_strictMono
        (show k.castSucc < k.succ by change k.val < k.val + 1; omega))
      (X.diagonal_feasible hX k)
    simp only [sub_zero] at hm
    linarith

theorem parentAction_zero_le (w : ConvexWeight) (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) : parentAction w X 0 ≤ parentAction w X j := by
  have h : ∀ k (hk : k < n + 1), parentAction w X 0 ≤ parentAction w X ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact le_rfl
    | succ k ih =>
      intro hk
      let r : Fin n := ⟨k, by omega⟩
      exact (ih (by omega)).trans (parentAction_step_nonneg w X hX r)
  exact h j.val j.isLt

private theorem defectAction_ge_parent_min (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j) (j : Fin (n + 1)) :
    (min (parentAction w X j) (parentAction w Y j) : WithTop ℝ) ≤ defectAction w X Y j := by
  have hv := monomialValuation_sub_ge w.generatorWeight (X.cofactor j) (Y.cofactor j)
  rw [monomialValuation_eq_coe (X.cofactor_ne_zero w hX j),
    monomialValuation_eq_coe (Y.cofactor_ne_zero w hY j)] at hv
  have hc := add_le_add_right hv (w.weight (X.capShift j).toNat : WithTop ℝ)
  unfold parentAction defectAction cofactorDefect
  rw [← hgrid j]
  simpa only [WithTop.coe_min, WithTop.coe_add, min_add_add_right, add_comm] using hc

theorem positiveFloor_ge_initial_min (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j) :
    (min (parentAction w X 0) (parentAction w Y 0) : WithTop ℝ) ≤ positiveFloor w X Y := by
  apply Finset.le_inf
  intro j _
  apply le_trans _ (defectAction_ge_parent_min w X Y hX hY hgrid j)
  exact WithTop.coe_le_coe.mpr
    (min_le_min (parentAction_zero_le w X hX j) (parentAction_zero_le w Y hY j))

private theorem zero_valuation_eq_action (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) :
    monomialValuation w.generatorWeight (X.cofactor 0) = (parentAction w X 0 : WithTop ℝ) := by
  rw [monomialValuation_eq_coe (X.cofactor_ne_zero w hX 0)]
  simp [parentAction, w.zero]

/-- The strict floor forces equal initial parent energies rather than assuming them. -/
theorem initial_actions_eq_of_floor (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0) :
    parentAction w X 0 = parentAction w Y 0 := by
  have hl := lt_of_le_of_lt (positiveFloor_ge_initial_min w X Y hX hY hgrid) hfloor
  have hv0 : defectAction w X Y 0 =
      monomialValuation w.generatorWeight (X.cofactor 0 - Y.cofactor 0) := by
    simp [defectAction, cofactorDefect, w.zero]
  rw [hv0] at hl
  by_contra hn
  have hvne : monomialValuation w.generatorWeight (X.cofactor 0) ≠
      monomialValuation w.generatorWeight (Y.cofactor 0) := by
    rw [zero_valuation_eq_action w X hX, zero_valuation_eq_action w Y hY]
    exact fun h => hn (WithTop.coe_injective h)
  rw [monomialValuation_sub_eq_min hvne, zero_valuation_eq_action w X hX,
    zero_valuation_eq_action w Y hY, ← WithTop.coe_min] at hl
  exact lt_irrefl _ hl

private theorem cofactor_zero_initial_product (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) :
    initialForm w.generatorWeight (X.cofactor 0) = ∏ i, complete (X.rowLength i : ℤ) := by
  rw [cofactor_initialForm w X hX 0]
  simp only [Fin.val_zero, pow_zero, one_mul]
  apply Finset.prod_congr rfl
  intro i _
  have he : X.peelIndex 0 i = (X.rowLength i : ℤ) := by
    simpa [peelIndex] using (X.rowLength_eq_coordinates i).symm
  rw [he]

/-- The floor cancels the entire initial parent monomial at column zero. -/
theorem initial_forms_eq_of_floor (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0) :
    initialForm w.generatorWeight (X.cofactor 0) =
      initialForm w.generatorWeight (Y.cofactor 0) := by
  have he := initial_actions_eq_of_floor w X Y hX hY hgrid hfloor
  have hl := lt_of_le_of_lt (positiveFloor_ge_initial_min w X Y hX hY hgrid) hfloor
  rw [he, min_self] at hl
  have hv0 : defectAction w X Y 0 =
      monomialValuation w.generatorWeight (X.cofactor 0 - Y.cofactor 0) := by
    simp [defectAction, cofactorDefect, w.zero]
  rw [hv0, ← zero_valuation_eq_action w Y hY] at hl
  have hstrict := strict_lowerBound_of_valuation_lt (Y.cofactor_ne_zero w hY 0) hl
  have hc := component_eq_zero_of_strict_lowerBound hstrict
  have hleast : leastWeight w.generatorWeight (X.cofactor 0) =
      leastWeight w.generatorWeight (Y.cofactor 0) := by
    simpa [parentAction, w.zero] using he
  unfold initialForm
  rw [hleast]
  rw [map_sub, sub_eq_zero] at hc
  exact hc

/-- Positive complete generators recover every row length from the cancelled monomial. -/
theorem rowLengths_eq_of_floor (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0) :
    X.rowLengthMultiset = Y.rowLengthMultiset := by
  classical
  have he := initial_forms_eq_of_floor w X Y hX hY hgrid hfloor
  rw [cofactor_zero_initial_product w X hX, cofactor_zero_initial_product w Y hY] at he
  let l := Finset.univ.toList.map X.rowLength
  let m := Finset.univ.toList.map Y.rowLength
  have hl : ∀ k ∈ l, 0 < k := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
    exact Nat.sub_pos_of_lt (X.row_nonempty i)
  have hm : ∀ k ∈ m, 0 < k := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
    exact Nat.sub_pos_of_lt (Y.row_nonempty i)
  have hp : (l.map (fun k : ℕ => complete (k : ℤ))).prod =
      (m.map (fun k : ℕ => complete (k : ℤ))).prod := by
    simpa [l, m, List.map_map, Function.comp_def] using he
  have hr := (prod_complete_eq_iff_of_pos l m hl hm).mp hp
  simpa only [l, m, rowLengthMultiset, ← Multiset.map_coe, Finset.coe_toList] using hr

theorem defectTiltedCost_finite_iff (w : ConvexWeight) (X Y : Diagram n)
    (A : ℤ) (j : Fin (n + 1)) :
    defectTiltedCost w X Y A j ≠ ⊤ ↔
      A ≤ X.capShift j ∧ cofactorDefect X Y j ≠ 0 := by
  by_cases hj : A ≤ X.capShift j
  · simp [defectTiltedCost, hj, monomialValuation_eq_top_iff]
  · simp [defectTiltedCost, hj]

/-- A tilted cost is exactly the valuation of the corresponding actual kernel summand. -/
theorem common_summand_valuation (w : ConvexWeight) (X Y : Diagram n)
    (A : ℤ) (j : Fin (n + 1)) :
    monomialValuation w.generatorWeight
      (complete (X.capShift j - A) * cofactorDefect X Y j) =
      defectTiltedCost w X Y A j := by
  by_cases hj : A ≤ X.capShift j
  · rw [monomialValuation_mul,
      complete_monomialValuation w _ (sub_nonneg.mpr hj)]
    simp only [defectTiltedCost, ite_eq_left hj]
    exact add_comm _ _
  · rw [complete_of_neg (by omega), zero_mul, monomialValuation_zero]
    simp [defectTiltedCost, hj]

theorem defectMinimizers_nonempty (w : ConvexWeight) (X Y : Diagram n)
    (A : ℤ) (q : Fin (n + 1)) (hq : defectTiltedCost w X Y A q ≠ ⊤) :
    (defectMinimizers w X Y A).Nonempty := by
  classical
  obtain ⟨j, _, hmin⟩ := Set.exists_min_image (Set.univ : Set (Fin (n + 1)))
    (defectTiltedCost w X Y A) (Set.toFinite _) (Set.univ_nonempty)
  have hj : defectTiltedCost w X Y A j ≠ ⊤ := by
    intro ht
    have hle := hmin q (Set.mem_univ q)
    rw [ht] at hle
    exact hq (top_le_iff.mp hle)
  exact ⟨j, (mem_defectMinimizers w X Y A j).mpr
    ⟨hj, fun k => hmin k (Set.mem_univ k)⟩⟩

/-- Tropical balancing is produced by the exact common-row determinant relation. -/
theorem defectMinimizers_card_ge_two (w : ConvexWeight) (X Y : Diagram n)
    (hgrid : ∀ j, X.capShift j = Y.capShift j) (i : Fin n)
    (hrow : X.rowParam i = Y.rowParam i)
    (q : Fin (n + 1)) (hq : defectTiltedCost w X Y (X.rowParam i) q ≠ ⊤) :
    2 ≤ (defectMinimizers w X Y (X.rowParam i)).card := by
  classical
  obtain ⟨j, hj⟩ := defectMinimizers_nonempty w X Y (X.rowParam i) q hq
  obtain ⟨hjfin, hjmin⟩ := (mem_defectMinimizers w X Y _ j).mp hj
  let f := fun k => complete (X.capShift k - X.rowParam i) * cofactorDefect X Y k
  have hfj : f j ≠ 0 := by
    intro hz
    apply hjfin
    rw [← common_summand_valuation]
    simp only [f] at hz
    rw [hz, monomialValuation_zero]
  have hrel : ∑ k, f k = 0 := by
    exact common_row_defect_relation X Y (funext hgrid) i hrow
  have hmin : ∀ k ∈ Finset.univ,
      monomialValuation w.generatorWeight (f j) ≤ monomialValuation w.generatorWeight (f k) := by
    intro k _
    simpa only [f, common_summand_valuation] using hjmin k
  obtain ⟨k, _, hkj, hval⟩ :=
    exists_second_minimizer_of_sum_zero Finset.univ f (Finset.mem_univ j) hfj hrel hmin
  have hcost : defectTiltedCost w X Y (X.rowParam i) k =
      defectTiltedCost w X Y (X.rowParam i) j := by
    simpa only [f, common_summand_valuation] using hval
  have hk : k ∈ defectMinimizers w X Y (X.rowParam i) := by
    apply (mem_defectMinimizers w X Y _ k).mpr
    rw [hcost]
    exact ⟨hjfin, hjmin⟩
  have hc := Finset.one_lt_card.mpr ⟨j, hj, k, hk, hkj.symm⟩
  omega

/-- Strict Monge interlaces actual defect minima, including their column valuation offsets. -/
theorem defectMinimizers_interlace (w : ConvexWeight) (X Y : Diagram n)
    {A A' : ℤ} (hA : A < A') {x y : Fin (n + 1)}
    (hx : x ∈ defectMinimizers w X Y A) (hy : y ∈ defectMinimizers w X Y A') :
    x ≤ y := by
  obtain ⟨hxfin, hxmin⟩ := (mem_defectMinimizers w X Y A x).mp hx
  obtain ⟨hyfin, hymin⟩ := (mem_defectMinimizers w X Y A' y).mp hy
  obtain ⟨hxf, hxg⟩ := (defectTiltedCost_finite_iff w X Y A x).mp hxfin
  obtain ⟨hyf, hyg⟩ := (defectTiltedCost_finite_iff w X Y A' y).mp hyfin
  by_contra hn
  have hyx : y < x := lt_of_not_ge hn
  have hd := X.capShift_strictMono hyx
  have hyf' : A ≤ X.capShift y := hA.le.trans hyf
  have hxf' : A' ≤ X.capShift x := hyf.trans hd.le
  have h₁ := hxmin y
  have h₂ := hymin x
  simp only [defectTiltedCost, ite_eq_left hxf, ite_eq_left hyf, ite_eq_left hyf',
    ite_eq_left hxf', monomialValuation_eq_coe hxg, monomialValuation_eq_coe hyg,
    ← WithTop.coe_add, WithTop.coe_le_coe] at h₁ h₂
  have hm := w.strict_monge_int hA hd hyf
  linarith

private theorem tilted_zero_row_eq_action (w : ConvexWeight) (X Y : Diagram n)
    (j : Fin (n + 1)) : defectTiltedCost w X Y 0 j = defectAction w X Y j := by
  simp only [defectTiltedCost, defectAction, ite_eq_left (X.capShift_nonneg j), sub_zero]

/-- The strict floor excludes column zero from the zeroth-row minimum. -/
theorem zero_not_defectMinimizers_of_floor (w : ConvexWeight) (X Y : Diagram n)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0) :
    0 ∉ defectMinimizers w X Y 0 := by
  intro hz
  have hmin := ((mem_defectMinimizers w X Y 0 0).mp hz).2
  have hle : defectAction w X Y 0 ≤ positiveFloor w X Y := by
    apply Finset.le_inf
    intro j _
    simpa only [tilted_zero_row_eq_action] using hmin j
  exact (not_lt_of_ge hle) hfloor

/-- No-backflow bounds every actual common-prefix minimizer by the first-split column. -/
theorem defectMinimizers_le_split (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset) (v : Fin n)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (i : Fin n) (hiv : i < v) {j : Fin (n + 1)}
    (hj : j ∈ defectMinimizers w X Y (X.rowParam i)) : j ≤ v.succ := by
  by_contra hn
  have hback := defect_no_backflow w X Y hX hY hgrid hrows v hprefix hchanged
    i hiv j (lt_of_not_ge hn)
  have hmin := ((mem_defectMinimizers w X Y _ j).mp hj).2 v.succ
  exact (not_lt_of_ge hmin) hback

/-- Exact actual minimizer pairs: the floor itself supplies all synchronization inputs. -/
theorem cap_fixed_minimizers (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0) :
    ∀ i : Fin v.val,
      (defectMinimizers w X Y (X.rowParam ⟨i.val, by omega⟩)).image Fin.val =
        {i.val + 1, i.val + 2} := by
  classical
  have hrows := rowLengths_eq_of_floor w X Y hX hY hgrid hfloor
  let row : Fin v.val → Fin n := fun i => ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
  let M : Fin v.val → Finset ℕ := fun i =>
    (defectMinimizers w X Y (X.rowParam (row i))).image Fin.val
  have hrowlt : ∀ i, row i < v := by intro i; exact i.isLt
  have hanchor := (first_split_anchor w X Y hX hY hgrid hrows v hprefix hchanged).1
  have hqfin : ∀ i, defectTiltedCost w X Y (X.rowParam (row i)) v.succ ≠ ⊤ := by
    intro i
    apply (defectTiltedCost_finite_iff w X Y _ _).mpr
    refine ⟨?_, hanchor⟩
    have hri := X.rowParam_strictMono (hrowlt i)
    have hd := X.diagonal_feasible hX v
    have hc := X.capShift_strictMono
      (show v.castSucc < v.succ by change v.val < v.val + 1; omega)
    omega
  have hcard : ∀ i, 2 ≤ (M i).card := by
    intro i
    dsimp only [M]
    rw [Finset.card_image_of_injective _ Fin.val_injective]
    exact defectMinimizers_card_ge_two w X Y hgrid (row i)
      (hprefix _ (hrowlt i)) v.succ (hqfin i)
  have hupper : ∀ i, ∀ x ∈ M i, x ≤ v.val + 1 := by
    intro i x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact defectMinimizers_le_split w X Y hX hY hgrid hrows v hprefix hchanged
      (row i) (hrowlt i) hj
  have hzero : 0 ∉ M ⟨0, hv⟩ := by
    intro hz
    obtain ⟨j, hj, hjzero⟩ := Finset.mem_image.mp hz
    have hj0 : j = 0 := Fin.ext hjzero
    have hr0 : X.rowParam (row ⟨0, hv⟩) = 0 := by
      exact X.rowParam_zero hX.1
    rw [hj0, hr0] at hj
    exact zero_not_defectMinimizers_of_floor w X Y hfloor hj
  have hinter : ∀ i j : Fin v.val, i.val + 1 = j.val →
      ∀ x ∈ M i, ∀ y ∈ M j, x ≤ y := by
    intro i j hij x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    apply defectMinimizers_interlace w X Y _ ha hb
    apply X.rowParam_strictMono
    change i.val < j.val
    omega
  exact cap_fixed_interlacing_chain hv M hcard hupper hzero hinter

/-- The exact pair statement with column indices, not merely the image of a set. -/
theorem cap_fixed_minimizer_mem_iff (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0)
    (i : Fin v.val) (j : Fin (n + 1)) :
    j ∈ defectMinimizers w X Y (X.rowParam ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩) ↔
      j.val = i.val + 1 ∨ j.val = i.val + 2 := by
  classical
  have he := cap_fixed_minimizers w X Y hX hY hgrid v hv hprefix hchanged hfloor i
  constructor
  · intro hj
    have him : j.val ∈
        (defectMinimizers w X Y
          (X.rowParam ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩)).image Fin.val :=
      Finset.mem_image.mpr ⟨j, hj, rfl⟩
    rw [he] at him
    simpa only [Finset.mem_insert, Finset.mem_singleton] using him
  · intro hj
    have him : j.val ∈ ({i.val + 1, i.val + 2} : Finset ℕ) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
    rw [← he] at him
    obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp him
    have : k = j := Fin.ext hkj
    simpa only [this] using hk

/-- Every column of the solid prefix is a supported actual defect coordinate. -/
theorem cap_fixed_prefix_support (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0)
    (j : Fin (n + 1)) (hjpos : 0 < j.val) (hjupper : j.val ≤ v.val + 1) :
    cofactorDefect X Y j ≠ 0 := by
  let i : Fin v.val := ⟨min (j.val - 1) (v.val - 1), by omega⟩
  have hjpair : j.val = i.val + 1 ∨ j.val = i.val + 2 := by
    dsimp [i]
    omega
  have hj :=
    (cap_fixed_minimizer_mem_iff w X Y hX hY hgrid v hv hprefix hchanged hfloor i j).mpr
      hjpair
  have hfin := ((mem_defectMinimizers w X Y _ j).mp hj).1
  exact ((defectTiltedCost_finite_iff w X Y _ j).mp hfin).2

/-- Adjacent tied costs give the exact normalized action difference. -/
theorem cap_fixed_action_recurrence (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0)
    (i : Fin v.val) :
    let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
    let a : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩
    let b : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩
    defectAction w X Y b = defectAction w X Y a +
      ((w.weight (X.capShift a - X.rowParam r).toNat -
        w.weight (X.capShift b - X.rowParam r).toNat +
        w.weight (X.capShift b).toNat - w.weight (X.capShift a).toNat : ℝ) :
          WithTop ℝ) := by
  dsimp only
  let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
  let a : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩
  let b : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩
  have ha := (cap_fixed_minimizer_mem_iff w X Y hX hY hgrid v hv hprefix hchanged hfloor i a).mpr
    (Or.inl rfl)
  have hb := (cap_fixed_minimizer_mem_iff w X Y hX hY hgrid v hv hprefix hchanged hfloor i b).mpr
    (Or.inr rfl)
  obtain ⟨haf, hamin⟩ := (mem_defectMinimizers w X Y _ a).mp ha
  obtain ⟨hbf, hbmin⟩ := (mem_defectMinimizers w X Y _ b).mp hb
  obtain ⟨hafeas, hag⟩ := (defectTiltedCost_finite_iff w X Y _ a).mp haf
  obtain ⟨hbfeas, hbg⟩ := (defectTiltedCost_finite_iff w X Y _ b).mp hbf
  have ht := le_antisymm (hamin b) (hbmin a)
  simp only [defectTiltedCost, ite_eq_left hafeas, ite_eq_left hbfeas,
    monomialValuation_eq_coe hag, monomialValuation_eq_coe hbg, ← WithTop.coe_add,
    WithTop.coe_inj] at ht
  change defectAction w X Y b = defectAction w X Y a + _
  unfold defectAction
  rw [monomialValuation_eq_coe hag, monomialValuation_eq_coe hbg]
  simp only [← WithTop.coe_add, WithTop.coe_inj]
  linarith

/-- The two first positive columns are exactly the floor columns, represented on the cap grid. -/
theorem cap_fixed_floor (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0) :
    (Finset.univ.filter (fun j : Fin (n + 1) =>
      0 < j.val ∧ defectAction w X Y j = positiveFloor w X Y)).image X.capShift =
      {X.capShift ⟨1, by have := v.isLt; omega⟩,
        X.capShift ⟨2, by have := v.isLt; omega⟩} ∧
    positiveFloor w X Y = defectAction w X Y ⟨1, by have := v.isLt; omega⟩ ∧
    defectAction w X Y ⟨1, by have := v.isLt; omega⟩ =
      defectAction w X Y ⟨2, by have := v.isLt; omega⟩ := by
  classical
  let a : Fin (n + 1) := ⟨1, by have := v.isLt; omega⟩
  let b : Fin (n + 1) := ⟨2, by have := v.isLt; omega⟩
  let i : Fin v.val := ⟨0, hv⟩
  have hr0 : X.rowParam (⟨0, by have := v.isLt; omega⟩ : Fin n) = 0 :=
    X.rowParam_zero hX.1
  have hp : ∀ j : Fin (n + 1), j ∈ defectMinimizers w X Y 0 ↔ j.val = 1 ∨ j.val = 2 := by
    intro j
    have hh := cap_fixed_minimizer_mem_iff w X Y hX hY hgrid v hv hprefix hchanged hfloor i j
    simpa only [i, Fin.val_mk, hr0, Nat.zero_add] using hh
  have ha := (hp a).mpr (Or.inl rfl)
  have hb := (hp b).mpr (Or.inr rfl)
  have hamin := ((mem_defectMinimizers w X Y 0 a).mp ha).2
  have hbmin := ((mem_defectMinimizers w X Y 0 b).mp hb).2
  have hab : defectAction w X Y a = defectAction w X Y b := by
    simpa only [tilted_zero_row_eq_action] using le_antisymm (hamin b) (hbmin a)
  have hfa : positiveFloor w X Y = defectAction w X Y a := by
    apply le_antisymm
    · apply Finset.inf_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, by change 0 < 1; omega⟩
    · apply Finset.le_inf
      intro j _
      simpa only [tilted_zero_row_eq_action] using hamin j
  have hcol : ∀ j : Fin (n + 1), 0 < j.val ∧ defectAction w X Y j = positiveFloor w X Y ↔
      j = a ∨ j = b := by
    intro j
    constructor
    · rintro ⟨_, hj⟩
      have hjmin : j ∈ defectMinimizers w X Y 0 := by
        apply (mem_defectMinimizers w X Y 0 j).mpr
        rw [tilted_zero_row_eq_action, hj, hfa]
        exact ⟨by simpa only [tilted_zero_row_eq_action] using
          ((mem_defectMinimizers w X Y 0 a).mp ha).1,
          by intro k; simpa only [tilted_zero_row_eq_action] using hamin k⟩
      rcases (hp j).mp hjmin with hj | hj
      · exact Or.inl (Fin.ext hj)
      · exact Or.inr (Fin.ext hj)
    · rintro (rfl | rfl)
      · exact ⟨by simp [a], hfa.symm⟩
      · exact ⟨by simp [b], hab.symm.trans hfa.symm⟩
  have hs : Finset.univ.filter (fun j : Fin (n + 1) =>
      0 < j.val ∧ defectAction w X Y j = positiveFloor w X Y) = {a, b} := by
    ext j
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] using hcol j
  refine ⟨?_, hfa, hab⟩
  rw [hs]
  simp only [Finset.image_insert, Finset.image_singleton]
  rfl

/-- The later actual normalized actions lie strictly above the split anchor. -/
theorem cap_fixed_tail_above_anchor (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0)
    (j : Fin (n + 1)) (hj : v.succ < j) :
    defectAction w X Y v.succ < defectAction w X Y j := by
  have hrows := rowLengths_eq_of_floor w X Y hX hY hgrid hfloor
  let i : Fin n := ⟨0, hX.1⟩
  have hr0 : X.rowParam i = 0 := X.rowParam_zero hX.1
  have hb := defect_no_backflow w X Y hX hY hgrid hrows v hprefix hchanged i hv j hj
  rw [hr0] at hb
  simpa only [tilted_zero_row_eq_action] using hb

/-- Every adjacent normalized action after the first tie strictly increases. -/
theorem cap_fixed_action_strict (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (hfloor : positiveFloor w X Y < defectAction w X Y 0)
    (i : Fin v.val) (hi : 0 < i.val) :
    defectAction w X Y ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩ <
      defectAction w X Y ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩ := by
  let r : Fin n := ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩
  let a : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; have := v.isLt; omega⟩
  let b : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; have := v.isLt; omega⟩
  have hA : 0 < X.rowParam r := by
    have hr := X.rowParam_strictMono
      (show (⟨0, hX.1⟩ : Fin n) < r from hi)
    rw [X.rowParam_zero hX.1] at hr
    exact hr
  have hfeas : X.rowParam r ≤ X.capShift a := by
    have hd := X.diagonal_feasible hX r
    have hc := X.capShift_strictMono
      (show r.castSucc < a by change i.val < i.val + 1; omega)
    omega
  have hm := w.strict_monge_int hA
    (X.capShift_strictMono (show a < b by change i.val + 1 < i.val + 2; omega)) hfeas
  simp only [sub_zero] at hm
  have hr := cap_fixed_action_recurrence w X Y hX hY hgrid v hv hprefix hchanged hfloor i
  change defectAction w X Y b = defectAction w X Y a + _ at hr
  have hag := cap_fixed_prefix_support w X Y hX hY hgrid v hv hprefix hchanged hfloor a
    (by change 0 < i.val + 1; omega)
    (by change i.val + 1 ≤ v.val + 1; have := i.isLt; omega)
  change defectAction w X Y a < defectAction w X Y b
  rw [hr]
  simp only [defectAction, monomialValuation_eq_coe hag, ← WithTop.coe_add,
    WithTop.coe_lt_coe]
  linarith

end Diagram
end SkewSchurReconstruction
