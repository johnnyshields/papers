/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CapFixedRigidity
import SkewSchurReconstruction.EqualityNormalization

/-!
# Rigidity of actual equal pairs

Formalizes “Application to actual skew Schur equality” (`subsec:actual-equality`,
`thm:equal-pair-rigidity`).  The first changed row, common cap grid, row-length
multiset, and strict floor are constructed from the actual diagrams and their
Schur equality.  No first-split data or balancing assumptions occur in the
public equal-pair theorem.  Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

variable {n : ℕ}

theorem rowLengthMultiset_eq_list (X : Diagram n) :
    X.rowLengthMultiset = (X.rowLengthList : Multiset ℕ) := by
  classical
  let s : Finset (Fin n) := ⟨(List.ofFn (id : Fin n → Fin n) : Multiset (Fin n)),
    List.nodup_ofFn_ofInjective Function.injective_id⟩
  have hs : s = Finset.univ := by
    ext i
    change i ∈ (List.ofFn (id : Fin n → Fin n) : Multiset (Fin n)) ↔ i ∈ Finset.univ
    simp only [Multiset.mem_coe, List.mem_ofFn, Finset.mem_univ, iff_true]
    exact ⟨i, rfl⟩
  have hvals : (List.ofFn (id : Fin n → Fin n) : Multiset (Fin n)) = Finset.univ.val :=
    congrArg Finset.val hs
  unfold rowLengthMultiset
  rw [← hvals, Multiset.map_coe, List.map_ofFn]
  rfl

/-- A nonidentical pair with a common top and inner boundary has a first changed
row parameter, which cannot be the zeroth parameter. -/
theorem exists_first_changed_row (X Y : Diagram n) (hn : 0 < n)
    (htop : X.top = Y.top) (hinner : X.inner = Y.inner) (hne : X ≠ Y) :
    ∃ v : Fin n, 0 < v.val ∧
      (∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i) ∧
      X.rowParam v ≠ Y.rowParam v := by
  classical
  have hex : ∃ i, X.rowParam i ≠ Y.rowParam i := by
    by_contra hh
    push Not at hh
    have hout : X.outer = Y.outer := by
      funext i
      have hi := hh i
      unfold rowParam at hi
      rw [htop] at hi
      omega
    apply hne
    cases X
    cases Y
    cases hout
    cases hinner
    rfl
  let s : Finset (Fin n) := Finset.univ.filter (fun i => X.rowParam i ≠ Y.rowParam i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let v := s.min' hs
  have hchanged : X.rowParam v ≠ Y.rowParam v :=
    (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hv : 0 < v.val := by
    by_contra hh
    have hz : v.val = 0 := by omega
    have he : v = (⟨0, hn⟩ : Fin n) := Fin.ext hz
    rw [he, X.rowParam_zero hn, Y.rowParam_zero hn] at hchanged
    exact hchanged rfl
  refine ⟨v, hv, ?_, hchanged⟩
  intro i hi
  by_contra hni
  have him : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hni⟩
  have hle : v ≤ i := Finset.min'_le s i him
  change v.val ≤ i.val at hle
  omega

/-- Equal Schur functions force the actual zeroth cofactor defect to vanish. -/
theorem cofactorDefect_zero_of_schur_eq (X Y : Diagram n)
    (heq : X.schurFunction = Y.schurFunction) : cofactorDefect X Y 0 = 0 := by
  exact sub_eq_zero.mpr heq

/-- A supported first split makes the positive floor finite, while Schur equality
makes the zeroth normalized action infinite. -/
theorem equal_pair_strict_floor (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (heq : X.schurFunction = Y.schurFunction) (v : Fin n)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    positiveFloor w X Y < defectAction w X Y 0 := by
  have hanchor := (first_split_anchor w X Y hX hY hgrid hrows v hprefix hchanged).1
  have hfinite : defectAction w X Y v.succ ≠ ⊤ := by
    exact fun ht => hanchor ((defectAction_eq_top_iff w X Y v.succ).mp ht)
  have hle : positiveFloor w X Y ≤ defectAction w X Y v.succ := by
    apply Finset.inf_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ]
    omega
  have htop : defectAction w X Y 0 = ⊤ :=
    (defectAction_eq_top_iff w X Y 0).mpr (cofactorDefect_zero_of_schur_eq X Y heq)
  rw [htop]
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfinite)

/-- Actual equal-pair rigidity, with the first changed row and the common grid
constructed from the input diagrams.  Every admissible weight has the same
adjacent chain, floor columns, and solid supported prefix. -/
theorem equal_pair_rigidity (X Y : Diagram n) (hX : X.Connected) (hY : Y.Connected)
    (hinner : X.inner = Y.inner) (hne : X ≠ Y)
    (heq : X.schurFunction = Y.schurFunction) :
    ∃ (v : Fin n) (hv : 0 < v.val),
      (∀ j, X.capShift j = Y.capShift j) ∧
      (∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i) ∧
      X.rowParam v ≠ Y.rowParam v ∧
      ∀ w : ConvexWeight,
        (∀ i : Fin v.val,
          (defectMinimizers w X Y
            (X.rowParam ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩)).image Fin.val =
            {i.val + 1, i.val + 2}) ∧
        (Finset.univ.filter (fun j : Fin (n + 1) =>
          0 < j.val ∧ defectAction w X Y j = positiveFloor w X Y)).image X.capShift =
          {X.capShift ⟨1, by have := v.isLt; omega⟩,
            X.capShift ⟨2, by have := v.isLt; have := hv; omega⟩} ∧
        (∀ j : Fin (n + 1), 0 < j.val → j.val ≤ v.val + 1 → cofactorDefect X Y j ≠ 0) := by
  have hnormal := equality_normalizes_cap X Y hX hY heq
    (by intro i j hij; have hij' : i = j := Fin.ext hij; subst j; exact congrFun hinner i)
  have hgrid : ∀ j, X.capShift j = Y.capShift j := fun j => hnormal.2.2 j j rfl
  obtain ⟨v, hv, hprefix, hchanged⟩ := exists_first_changed_row X Y hX.1 hnormal.2.1 hinner hne
  have hrows : X.rowLengthMultiset = Y.rowLengthMultiset := by
    rw [rowLengthMultiset_eq_list X, rowLengthMultiset_eq_list Y]
    exact rowLength_multiset_eq_of_schurFunction_eq X Y hX hY heq
  refine ⟨v, hv, hgrid, hprefix, hchanged, ?_⟩
  intro w
  have hfloor := equal_pair_strict_floor w X Y hX hY hgrid hrows heq v hprefix hchanged
  refine ⟨cap_fixed_minimizers w X Y hX hY hgrid v hv hprefix hchanged hfloor,
    (cap_fixed_floor w X Y hX hY hgrid v hv hprefix hchanged hfloor).1, ?_⟩
  intro j hjpos hjupper
  exact cap_fixed_prefix_support w X Y hX hY hgrid v hv hprefix hchanged hfloor j hjpos hjupper

end Diagram
end SkewSchurReconstruction
