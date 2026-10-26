/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CapGridVectors

/-!
# Ratio-identity normalization on actual union grids

Formalizes "Ratio identities and full adjacent-edge rigidity" (`sec:full-rigidity`):
`lem:ratio-row-lengths`, `thm:terminal-gap`, `prop:top-terminal`, and `cor:cap-fixing`.
Responses use actual heterogeneous grid defects.  The zero-response relation,
coefficient bounds, and terminal nonvanishing are produced by diagram determinants.
Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

/-- The actual finite-grid ratio identity `eq:ratio-identity`. -/
def RatioIdentity (G : ℤ →₀ CompleteRing) (r a : ℕ) : Prop :=
  gridResponse G ((r : ℤ) + a) = complete a * gridResponse G r

namespace Diagram

variable {n m : ℕ}

theorem rowLengthList_extendNortheast (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).rowLengthList = k :: X.rowLengthList := by
  unfold rowLengthList
  rw [List.ofFn_succ, extendNortheast_rowLength_zero]
  congr 1

/-- A union-grid ratio identity equates the actual cap remainders of both parents. -/
theorem ratio_remainders_eq (X : Diagram n) (Y : Diagram m) (r a : ℕ)
    (h : RatioIdentity (gridDefect X Y) r a) :
    complete a * X.capPolynomial r - X.capPolynomial ((r : ℤ) + a) =
      complete a * Y.capPolynomial r - Y.capPolynomial ((r : ℤ) + a) := by
  unfold RatioIdentity at h
  rw [gridDefect_response, gridDefect_response] at h
  linear_combination -h

/-- A ratio identity produces row-length multiset equality before any common cap is assumed. -/
theorem rowLength_multiset_eq_of_ratioIdentity (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    (X.rowLengthList : Multiset ℕ) = (Y.rowLengthList : Multiset ℕ) := by
  by_cases hr : 0 < r
  · have he : ((X.extendNortheast r hr).extendNortheast a ha).schurFunction =
        ((Y.extendNortheast r hr).extendNortheast a ha).schurFunction := by
      rw [schurFunction_extendNortheast, capPolynomial_extendNortheast,
        schurFunction_extendNortheast, capPolynomial_extendNortheast]
      have hh := ratio_remainders_eq X Y r a h
      simpa [add_comm] using hh
    have hm := rowLength_multiset_eq_of_schurFunction_eq _ _
      ((X.extendNortheast r hr).extendNortheast_connected a ha
        (X.extendNortheast_connected r hr hX))
      ((Y.extendNortheast r hr).extendNortheast_connected a ha
        (Y.extendNortheast_connected r hr hY)) he
    rw [rowLengthList_extendNortheast, rowLengthList_extendNortheast,
      rowLengthList_extendNortheast, rowLengthList_extendNortheast] at hm
    change ({a} : Multiset ℕ) + ({r} + (X.rowLengthList : Multiset ℕ)) =
      {a} + ({r} + (Y.rowLengthList : Multiset ℕ)) at hm
    exact add_left_cancel (add_left_cancel hm)
  · have hr0 : r = 0 := by omega
    subst r
    have he : (X.extendNortheast a ha).schurFunction =
        (Y.extendNortheast a ha).schurFunction := by
      have hh := ratio_remainders_eq X Y 0 a h
      simp only [Nat.cast_zero, zero_add, X.capPolynomial_zero hX.1,
        Y.capPolynomial_zero hY.1, mul_zero, zero_sub] at hh
      rw [schurFunction_extendNortheast, schurFunction_extendNortheast]
      simpa using neg_injective (by simpa using hh)
    have hm := rowLength_multiset_eq_of_schurFunction_eq _ _
      (X.extendNortheast_connected a ha hX) (Y.extendNortheast_connected a ha hY) he
    rw [rowLengthList_extendNortheast, rowLengthList_extendNortheast] at hm
    change ({a} : Multiset ℕ) + (X.rowLengthList : Multiset ℕ) =
      {a} + (Y.rowLengthList : Multiset ℕ) at hm
    exact add_left_cancel hm

/-- Row count is supplied by the actual ratio identity, not by a shared-grid assumption. -/
theorem rowCount_eq_of_ratioIdentity (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) : n = m := by
  have hm := rowLength_multiset_eq_of_ratioIdentity X Y hX hY r a ha h
  simpa [rowLengthList] using congrArg Multiset.card hm

end Diagram

/-- Largest supported shift of a nonzero actual union-grid defect. -/
noncomputable def lastDefectShift {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hG : gridDefect X Y ≠ 0) : ℤ :=
  (gridDefect X Y).support.max' (Finsupp.support_nonempty_iff.mpr hG)

theorem lastDefectShift_mem {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hG : gridDefect X Y ≠ 0) : lastDefectShift X Y hG ∈ (gridDefect X Y).support :=
  Finset.max'_mem _ _

theorem le_lastDefectShift {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hG : gridDefect X Y ≠ 0) (d : ℤ) (hd : d ∈ (gridDefect X Y).support) :
    d ≤ lastDefectShift X Y hG := Finset.le_max' _ _ hd

/-- Own zero response excludes a nonzero defect supported only at shift zero. -/
theorem lastDefectShift_pos {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (hG : gridDefect X Y ≠ 0) :
    0 < lastDefectShift X Y hG := by
  classical
  let G := gridDefect X Y
  let e := lastDefectShift X Y hG
  have he := lastDefectShift_mem X Y hG
  have hen : G e ≠ 0 := Finsupp.mem_support_iff.mp he
  have h0 := (gridDefect_shift_bounds X Y e hen).1
  by_contra h
  have he0 : e = 0 := by omega
  have hs : G = Finsupp.single 0 (G 0) := by
    ext d
    by_cases hd : d = 0
    · subst d
      simp
    · have hg : G d = 0 := by
        by_contra hg
        have hdn := (gridDefect_shift_bounds X Y d hg).1
        have hde := le_lastDefectShift X Y hG d (Finsupp.mem_support_iff.mpr hg)
        change d ≤ e at hde
        omega
      simp [hd, hg]
  have hz := gridDefect_response_zero X Y hX.1 hY.1
  change gridResponse G 0 = 0 at hz
  rw [hs, gridResponse_single] at hz
  simp only [zero_add, complete_zero, mul_one] at hz
  rw [he0] at hen
  exact hen hz

private theorem pderiv_complete_below (a : ℤ) (k : ℕ+) (ha : a < (k.val : ℤ)) :
    MvPolynomial.pderiv k (complete a) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hk
  have h := complete_vars_bound a a le_rfl k hk
  omega

/-- The terminal-gap bound on the actual union grid, without a common inner boundary. -/
theorem terminal_gap {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (hG : gridDefect X Y ≠ 0)
    (r a : ℕ) (ha : 0 < a) (h : RatioIdentity (gridDefect X Y) r a) :
    lastDefectShift X Y hG + r + a ≤ terminalBound X Y := by
  classical
  let G := gridDefect X Y
  let e := lastDefectShift X Y hG
  let H : ℤ := e + r + a
  have he := lastDefectShift_mem X Y hG
  have hen : G e ≠ 0 := Finsupp.mem_support_iff.mp he
  have hep : 0 < e := lastDefectShift_pos X Y hX hY hG
  by_contra hb
  have hHD : terminalBound X Y < H := by dsimp [H, e]; omega
  have hHp : 0 < H := by dsimp [H]; omega
  let k : ℕ+ := ⟨H.toNat, by omega⟩
  have hk : (k.val : ℤ) = H := by dsimp [k]; omega
  have hc : ∀ d, MvPolynomial.pderiv k (G d) = 0 := by
    intro d
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hv
    have hbound := gridDefect_coefficient_vars_bound X Y d k hv
    rw [hk] at hbound
    omega
  have hleft : MvPolynomial.pderiv k (gridResponse G ((r : ℤ) + a)) = G e := by
    change MvPolynomial.pderiv k
      (∑ d ∈ G.support, G d * complete ((r : ℤ) + a + d)) = G e
    rw [map_sum]
    have ht : ∀ d ∈ G.support,
        MvPolynomial.pderiv k (G d * complete ((r : ℤ) + a + d)) =
          if d = e then G e else 0 := by
      intro d hd
      have hde := le_lastDefectShift X Y hG d hd
      change d ≤ e at hde
      by_cases hdeq : d = e
      · subst d
        have heq : (r : ℤ) + a + e = H := by dsimp [H]; ring
        rw [heq]
        have hx : complete H = MvPolynomial.X k := complete_of_pos hHp
        simp [Derivation.leibniz, smul_eq_mul, hc, hx]
      · have hlt : (r : ℤ) + a + d < (k.val : ℤ) := by rw [hk]; dsimp [H]; omega
        simp [Derivation.leibniz, smul_eq_mul, hc, pderiv_complete_below _ k hlt, hdeq]
    apply (Finset.sum_congr rfl ht).trans
    rw [Finset.sum_eq_single e]
    · simp
    · intro d _ hde
      simp [hde]
    · intro h
      exact (h (show e ∈ G.support from he)).elim
  have hright : MvPolynomial.pderiv k (gridResponse G r) = 0 := by
    change MvPolynomial.pderiv k (∑ d ∈ G.support, G d * complete ((r : ℤ) + d)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    have hde := le_lastDefectShift X Y hG d hd
    change d ≤ e at hde
    have hlt : (r : ℤ) + d < (k.val : ℤ) := by rw [hk]; dsimp [H]; omega
    simp [Derivation.leibniz, smul_eq_mul, hc, pderiv_complete_below _ k hlt]
  have ham : MvPolynomial.pderiv k (complete a) = 0 := by
    apply pderiv_complete_below
    rw [hk]
    dsimp [H]
    omega
  have hh := congrArg (MvPolynomial.pderiv k) h
  change MvPolynomial.pderiv k (gridResponse G ((r : ℤ) + a)) =
    MvPolynomial.pderiv k (complete a * gridResponse G r) at hh
  rw [hleft] at hh
  simp only [Derivation.leibniz, smul_eq_mul, hright, ham, mul_zero, add_zero] at hh
  exact hen hh

namespace Diagram

/-- With common inner boundary, increasing the top increases the terminal cap shift. -/
theorem terminalShift_lt_of_top_lt {n : ℕ} (X Y : Diagram n) (hn : 0 < n)
    (hinner : X.inner = Y.inner) (ht : X.top < Y.top) :
    X.capShift (Fin.last n) < Y.capShift (Fin.last n) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [terminalShift_eq, terminalShift_eq, hinner]
    omega

/-- The larger-top parent supplies a unique terminal supported cofactor on the union grid. -/
theorem gridDefect_terminal_of_top_lt {n : ℕ} (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hinner : X.inner = Y.inner) (ht : X.top < Y.top) :
    gridDefect X Y (Y.capShift (Fin.last n)) = -Y.cofactor (Fin.last n) ∧
      gridDefect X Y (Y.capShift (Fin.last n)) ≠ 0 := by
  have hs := terminalShift_lt_of_top_lt X Y hX.1 hinner ht
  have hx : X.cofactorGridVector (Y.capShift (Fin.last n)) = 0 := by
    by_contra h
    have hb := (X.cofactorGridVector_shift_bounds _ h).2
    omega
  have he : gridDefect X Y (Y.capShift (Fin.last n)) = -Y.cofactor (Fin.last n) := by
    simp [gridDefect, hx, Y.cofactorGridVector_apply_capShift]
  exact ⟨he, by rw [he]; exact neg_ne_zero.mpr (Y.cofactor_ne_zero squareWeight hY _)⟩

/-- Different tops force the largest supported defect shift to reach the terminal bound. -/
theorem lastDefectShift_eq_terminalBound_of_top_ne {n : ℕ} (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hG : gridDefect X Y ≠ 0)
    (hinner : X.inner = Y.inner) (ht : X.top ≠ Y.top) :
    lastDefectShift X Y hG = terminalBound X Y := by
  have hem := lastDefectShift_mem X Y hG
  have heD := (gridDefect_shift_bounds X Y _ (Finsupp.mem_support_iff.mp hem)).2
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hs := terminalShift_lt_of_top_lt X Y hX.1 hinner ht
    have hn := (gridDefect_terminal_of_top_lt X Y hX hY hinner ht).2
    have he := le_lastDefectShift X Y hG _ (Finsupp.mem_support_iff.mpr hn)
    unfold terminalBound at *
    rw [max_eq_right hs.le] at heD ⊢
    omega
  · have hs := terminalShift_lt_of_top_lt Y X hY.1 hinner.symm ht
    have hn := (gridDefect_terminal_of_top_lt Y X hY hX hinner.symm ht).2
    have hn' : gridDefect X Y (X.capShift (Fin.last n)) ≠ 0 := by
      intro hz
      have he : gridDefect Y X (X.capShift (Fin.last n)) =
          -gridDefect X Y (X.capShift (Fin.last n)) := by simp [gridDefect]
      rw [he, hz, neg_zero] at hn
      exact hn rfl
    have he := le_lastDefectShift X Y hG _ (Finsupp.mem_support_iff.mpr hn')
    unfold terminalBound at *
    rw [max_eq_left hs.le] at heD ⊢
    omega

/-- An actual ratio identity fixes the cap origin and full grid under a common inner boundary. -/
theorem ratioIdentity_fixes_cap {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) (hG : gridDefect X Y ≠ 0)
    (r a : ℕ) (ha : 0 < a) (h : RatioIdentity (gridDefect X Y) r a)
    (hinner : ∀ (i : Fin n) (j : Fin m), i.val = j.val → X.inner i = Y.inner j) :
    n = m ∧ X.top = Y.top ∧
      ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), i.val = j.val → X.capShift i = Y.capShift j := by
  have hn := rowCount_eq_of_ratioIdentity X Y hX hY r a ha h
  subst m
  have hin : X.inner = Y.inner := funext fun i => hinner i i rfl
  have ht : X.top = Y.top := by
    by_contra ht
    have he := lastDefectShift_eq_terminalBound_of_top_ne X Y hX hY hG hin ht
    have hg := terminal_gap X Y hX hY hG r a ha h
    rw [he] at hg
    omega
  refine ⟨rfl, ht, ?_⟩
  intro i j hij
  have he : i = j := Fin.ext hij
  subst j
  unfold capShift
  split_ifs <;> simp [ht, hin]

end Diagram
end SkewSchurReconstruction
