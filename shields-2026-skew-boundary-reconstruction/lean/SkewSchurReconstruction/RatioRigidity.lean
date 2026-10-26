/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.EqualPairRigidity
import SkewSchurReconstruction.RatioNormalization

/-!
# Ratio identities through actual extended equal pairs

Formalizes "Ratio identities and full adjacent-edge rigidity" (`sec:full-rigidity`,
`thm:ratio-rigidity`).  Extensions and minimizers are the actual diagram objects.

**Differs from the paper's route.** The manuscript uses direct virtual-row balancing.
The proofs here transport the already proved equality chain of actual extended diagrams
back to the original virtual and genuine rows. Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

variable {n : ℕ}

/-- The positive virtual displacement selected by a ratio identity. -/
def ratioVirtualShift (r a : ℕ) : ℕ := if r = 0 then a else r

theorem ratioVirtualShift_pos (r a : ℕ) (ha : 0 < a) : 0 < ratioVirtualShift r a := by
  unfold ratioVirtualShift
  split_ifs <;> omega

/-- At base zero, the ratio identity is equality of the actual positive extensions. -/
theorem ratioIdentity_extension_schur_eq_zero (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) 0 a) :
    (X.extendNortheast a ha).schurFunction = (Y.extendNortheast a ha).schurFunction := by
  unfold RatioIdentity at h
  simp only [Nat.cast_zero, zero_add] at h
  rw [gridDefect_response_zero X Y hX.1 hY.1, mul_zero, gridDefect_response] at h
  rw [schurFunction_extendNortheast, schurFunction_extendNortheast]
  exact sub_eq_zero.mp h

/-- At positive base, the ratio identity is equality of actual iterated extensions. -/
theorem ratioIdentity_iterated_extension_schur_eq (X Y : Diagram n)
    (r a : ℕ) (hr : 0 < r) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    ((X.extendNortheast r hr).extendNortheast a ha).schurFunction =
      ((Y.extendNortheast r hr).extendNortheast a ha).schurFunction := by
  unfold RatioIdentity at h
  rw [gridDefect_response, gridDefect_response] at h
  rw [schurFunction_extendNortheast, capPolynomial_extendNortheast,
    schurFunction_extendNortheast, capPolynomial_extendNortheast]
  have he : (a : ℤ) + r = (r : ℤ) + a := by omega
  rw [he]
  linear_combination -h

/-- The old columns of a single extension have the negated actual defect. -/
theorem cofactorDefect_extend_succ (X Y : Diagram n) (k : ℕ) (hk : 0 < k)
    (j : Fin (n + 1)) :
    cofactorDefect (X.extendNortheast k hk) (Y.extendNortheast k hk) j.succ =
      -cofactorDefect X Y j := by
  simp only [cofactorDefect, cofactor_extendNortheast_succ]
  ring

/-- The old columns of a double extension have the unchanged actual defect. -/
theorem cofactorDefect_iterated_extend_succ_succ (X Y : Diagram n)
    (r a : ℕ) (hr : 0 < r) (ha : 0 < a) (j : Fin (n + 1)) :
    cofactorDefect ((X.extendNortheast r hr).extendNortheast a ha)
      ((Y.extendNortheast r hr).extendNortheast a ha) j.succ.succ =
      cofactorDefect X Y j := by
  rw [cofactorDefect_extend_succ, cofactorDefect_extend_succ, neg_neg]

/-- An actual equality extension has no zeroth defect coordinate. -/
theorem cofactorDefect_extend_zero_of_eq (X Y : Diagram n) (k : ℕ) (hk : 0 < k)
    (he : (X.extendNortheast k hk).schurFunction = (Y.extendNortheast k hk).schurFunction) :
    cofactorDefect (X.extendNortheast k hk) (Y.extendNortheast k hk) 0 = 0 :=
  cofactorDefect_zero_of_schur_eq _ _ he

/-- Common inner boundaries extend identically when their cap origins have been normalized. -/
theorem extend_inner_eq (X Y : Diagram n) (k : ℕ) (hk : 0 < k)
    (htop : X.top = Y.top) (hinner : X.inner = Y.inner) :
    (X.extendNortheast k hk).inner = (Y.extendNortheast k hk).inner := by
  funext i
  cases i using Fin.cases with
  | zero => simp only [extendNortheast_inner_zero, htop]
  | succ i => simp only [extendNortheast_inner_succ, hinner]

theorem extend_cap_grid_eq (X Y : Diagram n) (k : ℕ) (hk : 0 < k)
    (hgrid : ∀ j, X.capShift j = Y.capShift j) :
    ∀ j, (X.extendNortheast k hk).capShift j = (Y.extendNortheast k hk).capShift j := by
  intro j
  cases j using Fin.cases with
  | zero => simp only [extendNortheast_capShift_zero]
  | succ j => simp only [extendNortheast_capShift_succ, hgrid j]

/-- All old tilted costs of a single extension agree exactly with the displaced original costs. -/
theorem defectTiltedCost_extend_succ (w : ConvexWeight) (X Y : Diagram n)
    (k : ℕ) (hk : 0 < k) (row : ℤ) (j : Fin (n + 1)) :
    defectTiltedCost w (X.extendNortheast k hk) (Y.extendNortheast k hk)
        ((k : ℤ) + row) j.succ = defectTiltedCost w X Y row j := by
  have hd : ((k : ℤ) + X.capShift j) - ((k : ℤ) + row) = X.capShift j - row := by ring
  have hf : (k : ℤ) + row ≤ (k : ℤ) + X.capShift j ↔ row ≤ X.capShift j := by omega
  simp only [defectTiltedCost, extendNortheast_capShift_succ,
    cofactorDefect_extend_succ, monomialValuation_neg, hf, hd]

/-- Old tilted costs of the iterated extension agree with the corresponding original row. -/
theorem defectTiltedCost_iterated_extend_succ_succ (w : ConvexWeight) (X Y : Diagram n)
    (r a : ℕ) (hr : 0 < r) (ha : 0 < a) (row : ℤ) (j : Fin (n + 1)) :
    defectTiltedCost w ((X.extendNortheast r hr).extendNortheast a ha)
        ((Y.extendNortheast r hr).extendNortheast a ha)
        ((a : ℤ) + r + row) j.succ.succ = defectTiltedCost w X Y row j := by
  rw [show (a : ℤ) + r + row = a + ((r : ℤ) + row) by ring,
    defectTiltedCost_extend_succ, defectTiltedCost_extend_succ]

/-- A minimum transported through old columns is still a minimum in the original board. -/
theorem defectMinimizer_restrict {p : ℕ} (w : ConvexWeight)
    (X Y : Diagram n) (U V : Diagram p) (row oldRow : ℤ)
    (f : Fin (n + 1) → Fin (p + 1))
    (hcost : ∀ j, defectTiltedCost w U V row (f j) = defectTiltedCost w X Y oldRow j)
    (q : Fin (n + 1)) (hq : f q ∈ defectMinimizers w U V row) (j : Fin (n + 1)) :
    j ∈ defectMinimizers w X Y oldRow ↔ f j ∈ defectMinimizers w U V row := by
  obtain ⟨hqfin, hqmin⟩ := (mem_defectMinimizers w U V row (f q)).mp hq
  constructor
  · intro hj
    obtain ⟨hjfin, hjmin⟩ := (mem_defectMinimizers w X Y oldRow j).mp hj
    have hjq : defectTiltedCost w U V row (f j) = defectTiltedCost w U V row (f q) := by
      apply le_antisymm
      · simpa only [hcost] using hjmin q
      · exact hqmin (f j)
    apply (mem_defectMinimizers w U V row (f j)).mpr
    rw [hjq]
    exact ⟨hqfin, hqmin⟩
  · intro hj
    obtain ⟨hjfin, hjmin⟩ := (mem_defectMinimizers w U V row (f j)).mp hj
    apply (mem_defectMinimizers w X Y oldRow j).mpr
    rw [← hcost j]
    exact ⟨hjfin, fun k => by simpa only [hcost] using hjmin (f k)⟩

theorem extension_shared_row_prefix (X Y : Diagram n) (k : ℕ) (hk : 0 < k)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i) :
    ∀ i : Fin (n + 1), i.val < v.succ.val →
      (X.extendNortheast k hk).rowParam i = (Y.extendNortheast k hk).rowParam i := by
  intro i hi
  cases i using Fin.cases with
  | zero => simp only [extendNortheast_rowParam_zero]
  | succ i =>
      rw [extendNortheast_rowParam_succ, extendNortheast_rowParam_succ]
      congr 1
      apply hprefix
      simp only [Fin.val_succ] at hi
      omega

theorem extension_changed_row (X Y : Diagram n) (k : ℕ) (hk : 0 < k)
    (v : Fin n) (hchanged : X.rowParam v ≠ Y.rowParam v) :
    (X.extendNortheast k hk).rowParam v.succ ≠
      (Y.extendNortheast k hk).rowParam v.succ := by
  rw [extendNortheast_rowParam_succ, extendNortheast_rowParam_succ]
  exact fun h => hchanged (add_left_cancel h)

private theorem actual_equal_chain_mem (w : ConvexWeight) {p : ℕ} (U V : Diagram p)
    (hU : U.Connected) (hV : V.Connected) (hgrid : ∀ j, U.capShift j = V.capShift j)
    (heq : U.schurFunction = V.schurFunction) (s : Fin p) (hs : 0 < s.val)
    (hprefix : ∀ i : Fin p, i.val < s.val → U.rowParam i = V.rowParam i)
    (hchanged : U.rowParam s ≠ V.rowParam s) :
    ∀ i : Fin s.val, ∀ j : Fin (p + 1),
      j ∈ defectMinimizers w U V
          (U.rowParam ⟨i.val, by have := i.isLt; have := s.isLt; omega⟩) ↔
        j.val = i.val + 1 ∨ j.val = i.val + 2 := by
  have hrows : U.rowLengthMultiset = V.rowLengthMultiset := by
    rw [rowLengthMultiset_eq_list U, rowLengthMultiset_eq_list V]
    exact rowLength_multiset_eq_of_schurFunction_eq U V hU hV heq
  have hfloor := equal_pair_strict_floor w U V hU hV hgrid hrows heq s hprefix hchanged
  exact cap_fixed_minimizer_mem_iff w U V hU hV hgrid s hs hprefix hchanged hfloor

theorem ratio_zero_extended_chain (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (a : ℕ) (ha : 0 < a) (h : RatioIdentity (gridDefect X Y) 0 a)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    ∀ i : Fin v.succ.val, ∀ j : Fin (n + 1 + 1),
      j ∈ defectMinimizers w (X.extendNortheast a ha) (Y.extendNortheast a ha)
          ((X.extendNortheast a ha).rowParam
            ⟨i.val, by have := i.isLt; have := v.isLt; simp only [Fin.val_succ] at *; omega⟩) ↔
        j.val = i.val + 1 ∨ j.val = i.val + 2 := by
  apply actual_equal_chain_mem w _ _
    (X.extendNortheast_connected a ha hX) (Y.extendNortheast_connected a ha hY)
    (extend_cap_grid_eq X Y a ha hgrid)
    (ratioIdentity_extension_schur_eq_zero X Y hX hY a ha h) v.succ
    (by simp)
    (extension_shared_row_prefix X Y a ha v hprefix)
    (extension_changed_row X Y a ha v hchanged)

theorem ratio_positive_extended_chain (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (r a : ℕ) (hr : 0 < r) (ha : 0 < a) (h : RatioIdentity (gridDefect X Y) r a)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    ∀ i : Fin v.succ.succ.val, ∀ j : Fin (n + 1 + 1 + 1),
      j ∈ defectMinimizers w ((X.extendNortheast r hr).extendNortheast a ha)
          ((Y.extendNortheast r hr).extendNortheast a ha)
          (((X.extendNortheast r hr).extendNortheast a ha).rowParam
            ⟨i.val, by have := i.isLt; have := v.isLt; simp only [Fin.val_succ] at *; omega⟩) ↔
        j.val = i.val + 1 ∨ j.val = i.val + 2 := by
  apply actual_equal_chain_mem w _ _
    ((X.extendNortheast r hr).extendNortheast_connected a ha
      (X.extendNortheast_connected r hr hX))
    ((Y.extendNortheast r hr).extendNortheast_connected a ha
      (Y.extendNortheast_connected r hr hY))
    (extend_cap_grid_eq _ _ a ha (extend_cap_grid_eq X Y r hr hgrid))
    (ratioIdentity_iterated_extension_schur_eq X Y r a hr ha h) v.succ.succ
    (by simp)
    (extension_shared_row_prefix _ _ a ha v.succ
      (extension_shared_row_prefix X Y r hr v hprefix))
    (extension_changed_row _ _ a ha v.succ (extension_changed_row X Y r hr v hchanged))

private theorem virtual_pair_restrict_one (w : ConvexWeight) (X Y : Diagram n)
    (a : ℕ) (ha : 0 < a)
    (hpair : ∀ j : Fin (n + 1 + 1),
      j ∈ defectMinimizers w (X.extendNortheast a ha) (Y.extendNortheast a ha) 0 ↔
        j.val = 1 ∨ j.val = 2) :
    ∀ j : Fin (n + 1), j ∈ defectMinimizers w X Y (-(a : ℤ)) ↔
      j.val = 0 ∨ j.val = 1 := by
  have hcost : ∀ j : Fin (n + 1),
      defectTiltedCost w (X.extendNortheast a ha) (Y.extendNortheast a ha) 0 j.succ =
        defectTiltedCost w X Y (-(a : ℤ)) j := by
    intro j
    have hh := defectTiltedCost_extend_succ w X Y a ha (-(a : ℤ)) j
    simpa only [add_neg_cancel] using hh
  have hq := (hpair (0 : Fin (n + 1)).succ).mpr (Or.inl (by simp))
  intro j
  have hh := defectMinimizer_restrict w X Y (X.extendNortheast a ha)
    (Y.extendNortheast a ha) 0 (-(a : ℤ)) Fin.succ hcost 0 hq j
  rw [hpair j.succ] at hh
  simp only [Fin.val_succ] at hh
  exact hh.trans (by omega)

private theorem virtual_pair_restrict_two (w : ConvexWeight) (X Y : Diagram n)
    (r a : ℕ) (hr : 0 < r) (ha : 0 < a)
    (hpair : ∀ j : Fin (n + 1 + 1 + 1),
      j ∈ defectMinimizers w ((X.extendNortheast r hr).extendNortheast a ha)
          ((Y.extendNortheast r hr).extendNortheast a ha) a ↔
        j.val = 2 ∨ j.val = 3) :
    ∀ j : Fin (n + 1), j ∈ defectMinimizers w X Y (-(r : ℤ)) ↔
      j.val = 0 ∨ j.val = 1 := by
  have hcost : ∀ j : Fin (n + 1),
      defectTiltedCost w ((X.extendNortheast r hr).extendNortheast a ha)
          ((Y.extendNortheast r hr).extendNortheast a ha) a j.succ.succ =
        defectTiltedCost w X Y (-(r : ℤ)) j := by
    intro j
    have hh := defectTiltedCost_iterated_extend_succ_succ w X Y r a hr ha (-(r : ℤ)) j
    have he : (a : ℤ) + r + -(r : ℤ) = a := by ring
    simpa only [he] using hh
  have hq := (hpair (0 : Fin (n + 1)).succ.succ).mpr (Or.inl (by simp))
  intro j
  have hh := defectMinimizer_restrict w X Y ((X.extendNortheast r hr).extendNortheast a ha)
    ((Y.extendNortheast r hr).extendNortheast a ha) a (-(r : ℤ))
    (fun j => j.succ.succ) hcost 0 hq j
  rw [hpair j.succ.succ] at hh
  simp only [Fin.val_succ] at hh
  exact hh.trans (by omega)

/-- The actual ratio identity supplies the virtual adjacent pair for every convex weight.
**Differs from the paper's route.** Restricts the equality chain of actual single or
double extensions instead of balancing the virtual row directly. -/
theorem ratio_virtual_minimizers_normalized (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (r a : ℕ) (ha : 0 < a) (h : RatioIdentity (gridDefect X Y) r a)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    ∀ j : Fin (n + 1), j ∈ defectMinimizers w X Y (-(ratioVirtualShift r a : ℤ)) ↔
      j.val = 0 ∨ j.val = 1 := by
  by_cases hr0 : r = 0
  · subst r
    simp only [ratioVirtualShift]
    apply virtual_pair_restrict_one w X Y a ha
    intro j
    let i : Fin v.succ.val := ⟨0, by simp⟩
    have hh := ratio_zero_extended_chain w X Y hX hY hgrid a ha h v hprefix hchanged i j
    change j ∈ defectMinimizers w (X.extendNortheast a ha) (Y.extendNortheast a ha)
      ((X.extendNortheast a ha).rowParam ⟨0, Nat.zero_lt_succ n⟩) ↔
        j.val = 1 ∨ j.val = 2 at hh
    rw [rowParam_zero] at hh
    exact hh
  · have hr : 0 < r := by omega
    simp only [ratioVirtualShift, ite_eq_right hr0]
    apply virtual_pair_restrict_two w X Y r a hr ha
    intro j
    let i : Fin v.succ.succ.val := ⟨1, by simp⟩
    have hh := ratio_positive_extended_chain w X Y hX hY hgrid r a hr ha h v hprefix
      hchanged i j
    have heRow : (((X.extendNortheast r hr).extendNortheast a ha).rowParam
        (⟨1, by omega⟩ : Fin (n + 1 + 1))) = (a : ℤ) := by
      have he : (⟨1, by omega⟩ : Fin (n + 1 + 1)) =
          (0 : Fin (n + 1)).succ := Fin.ext rfl
      rw [he, extendNortheast_rowParam_succ, extendNortheast_rowParam_zero, add_zero]
    change j ∈ defectMinimizers w ((X.extendNortheast r hr).extendNortheast a ha)
      ((Y.extendNortheast r hr).extendNortheast a ha)
      ((((X.extendNortheast r hr).extendNortheast a ha).rowParam
        (⟨1, by omega⟩ : Fin (n + 1 + 1)))) ↔ j.val = 2 ∨ j.val = 3 at hh
    rw [heRow] at hh
    exact hh

/-- The virtual adjacent tie determines the exact general-weight defect gap. -/
theorem ratio_virtual_gap_normalized (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (r a : ℕ) (ha : 0 < a) (h : RatioIdentity (gridDefect X Y) r a)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    cofactorDefect X Y 0 ≠ 0 ∧ cofactorDefect X Y 1 ≠ 0 ∧
      leastWeight w.generatorWeight (cofactorDefect X Y 0) -
          (leastWeight w.generatorWeight (cofactorDefect X Y 1) +
            w.weight (X.capShift 1).toNat) =
        w.weight (ratioVirtualShift r a + (X.capShift 1).toNat) -
          w.weight (ratioVirtualShift r a) - w.weight (X.capShift 1).toNat := by
  have hn : 0 < n := hX.1
  have hv1 : (1 : Fin (n + 1)).val = 1 := by
    change 1 % (n + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  let gamma := ratioVirtualShift r a
  have hg : 0 < gamma := ratioVirtualShift_pos r a ha
  have hp := ratio_virtual_minimizers_normalized w X Y hX hY hgrid r a ha h v hprefix hchanged
  have hm0 := (hp 0).mpr (Or.inl rfl)
  have hm1 := (hp 1).mpr (Or.inr hv1)
  obtain ⟨hf0, hmin0⟩ := (mem_defectMinimizers w X Y _ 0).mp hm0
  obtain ⟨hf1, hmin1⟩ := (mem_defectMinimizers w X Y _ 1).mp hm1
  have hG0 := ((defectTiltedCost_finite_iff w X Y _ 0).mp hf0).2
  have hG1 := ((defectTiltedCost_finite_iff w X Y _ 1).mp hf1).2
  have he := le_antisymm (hmin0 1) (hmin1 0)
  have hd0 : 0 ≤ X.capShift 1 := X.capShift_nonneg 1
  have hfe0 : -(gamma : ℤ) ≤ 0 := by omega
  have hfe1 : -(gamma : ℤ) ≤ X.capShift 1 := by omega
  have hdto : (X.capShift 1 - -(gamma : ℤ)).toNat = gamma + (X.capShift 1).toNat := by omega
  change defectTiltedCost w X Y (-(gamma : ℤ)) 0 =
    defectTiltedCost w X Y (-(gamma : ℤ)) 1 at he
  simp only [defectTiltedCost, X.capShift_zero, ite_eq_left hfe0, ite_eq_left hfe1,
    monomialValuation_eq_coe hG0, monomialValuation_eq_coe hG1,
    zero_sub, neg_neg, Int.toNat_natCast, hdto, ← WithTop.coe_add,
    WithTop.coe_inj] at he
  refine ⟨hG0, hG1, ?_⟩
  change leastWeight w.generatorWeight (cofactorDefect X Y 0) -
      (leastWeight w.generatorWeight (cofactorDefect X Y 1) + w.weight (X.capShift 1).toNat) =
    w.weight (gamma + (X.capShift 1).toNat) - w.weight gamma - w.weight (X.capShift 1).toNat
  linarith

/-- The virtual gap is strictly positive and therefore supplies the floor premise. -/
theorem ratio_strict_floor_normalized (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (r a : ℕ) (ha : 0 < a) (h : RatioIdentity (gridDefect X Y) r a)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    positiveFloor w X Y < defectAction w X Y 0 := by
  obtain ⟨hG0, hG1, hgap⟩ := ratio_virtual_gap_normalized w X Y hX hY hgrid r a ha h
    v hprefix hchanged
  have hn : 0 < n := hX.1
  let z : Fin n := ⟨0, hn⟩
  have hz : z.succ = (1 : Fin (n + 1)) := by
    apply Fin.ext
    change 1 = 1 % (n + 1)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have hdp : 0 < X.capShift 1 := by
    rw [← hz]
    exact X.capShift_succ_pos z
  have hdpn : 0 < (X.capShift 1).toNat := by omega
  have hgamma := ratioVirtualShift_pos r a ha
  have hs := w.strict_superadditive hgamma hdpn
  have hstrict : leastWeight w.generatorWeight (cofactorDefect X Y 1) +
      w.weight (X.capShift 1).toNat <
      leastWeight w.generatorWeight (cofactorDefect X Y 0) := by linarith
  have halpha : defectAction w X Y 1 < defectAction w X Y 0 := by
    simp only [defectAction, monomialValuation_eq_coe hG0, monomialValuation_eq_coe hG1,
      X.capShift_zero, Int.toNat_zero, w.zero, WithTop.coe_zero, add_zero,
      ← WithTop.coe_add, WithTop.coe_lt_coe]
    exact hstrict
  apply lt_of_le_of_lt _ halpha
  apply Finset.inf_le
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change 0 < 1 % (n + 1)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem ratio_square_gap_normalized (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (r a : ℕ) (ha : 0 < a) (h : RatioIdentity (gridDefect X Y) r a)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    leastWeight squareWeight.generatorWeight (cofactorDefect X Y 0) -
        (leastWeight squareWeight.generatorWeight (cofactorDefect X Y 1) +
          squareWeight.weight (X.capShift 1).toNat) =
      2 * (ratioVirtualShift r a : ℝ) * ((X.capShift 1).toNat : ℝ) := by
  rw [(ratio_virtual_gap_normalized squareWeight X Y hX hY hgrid r a ha h
    v hprefix hchanged).2.2]
  simp only [squareWeight, Nat.cast_add]
  ring

/-- Same-count ratio rigidity; every normalization and first-split datum is produced internally. -/
theorem ratio_rigidity_same_count (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hinner : X.inner = Y.inner)
    (hG : gridDefect X Y ≠ 0) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    ∃ (v : Fin n) (hv : 0 < v.val),
      (∀ j, X.capShift j = Y.capShift j) ∧
      (∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i) ∧
      X.rowParam v ≠ Y.rowParam v ∧
      ∀ w : ConvexWeight,
        (∀ j : Fin (n + 1), j ∈ defectMinimizers w X Y (-(ratioVirtualShift r a : ℤ)) ↔
          j.val = 0 ∨ j.val = 1) ∧
        positiveFloor w X Y < defectAction w X Y 0 ∧
        (∀ i : Fin v.val, ∀ j : Fin (n + 1),
          j ∈ defectMinimizers w X Y
              (X.rowParam ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩) ↔
            j.val = i.val + 1 ∨ j.val = i.val + 2) ∧
        (Finset.univ.filter (fun j : Fin (n + 1) =>
          0 < j.val ∧ defectAction w X Y j = positiveFloor w X Y)).image X.capShift =
          {X.capShift ⟨1, by have := v.isLt; have := hv; omega⟩,
            X.capShift ⟨2, by have := v.isLt; have := hv; omega⟩} ∧
        positiveFloor w X Y = defectAction w X Y ⟨1, by have := v.isLt; have := hv; omega⟩ ∧
        defectAction w X Y ⟨1, by have := v.isLt; have := hv; omega⟩ =
          defectAction w X Y ⟨2, by have := v.isLt; have := hv; omega⟩ ∧
        (leastWeight w.generatorWeight (cofactorDefect X Y 0) -
            (leastWeight w.generatorWeight (cofactorDefect X Y 1) +
              w.weight (X.capShift 1).toNat) =
          w.weight (ratioVirtualShift r a + (X.capShift 1).toNat) -
            w.weight (ratioVirtualShift r a) - w.weight (X.capShift 1).toNat) ∧
        (∀ j : Fin (n + 1), j.val ≤ v.val + 1 → cofactorDefect X Y j ≠ 0) := by
  have hnormal := ratioIdentity_fixes_cap X Y hX hY hG r a ha h
    (fun i j hij => by have he : i = j := Fin.ext hij; rw [he]; exact congrFun hinner j)
  have hgrid : ∀ j, X.capShift j = Y.capShift j := fun j => hnormal.2.2 j j rfl
  have hne : X ≠ Y := by
    intro he
    subst Y
    exact hG (by simp [gridDefect])
  obtain ⟨v, hv, hprefix, hchanged⟩ :=
    exists_first_changed_row X Y hX.1 hnormal.2.1 hinner hne
  refine ⟨v, hv, hgrid, hprefix, hchanged, ?_⟩
  intro w
  have hfloor := ratio_strict_floor_normalized w X Y hX hY hgrid r a ha h v hprefix hchanged
  have hcapfloor := cap_fixed_floor w X Y hX hY hgrid v hv hprefix hchanged hfloor
  have hgap := ratio_virtual_gap_normalized w X Y hX hY hgrid r a ha h v hprefix hchanged
  refine ⟨ratio_virtual_minimizers_normalized w X Y hX hY hgrid r a ha h v hprefix hchanged,
    hfloor, cap_fixed_minimizer_mem_iff w X Y hX hY hgrid v hv hprefix hchanged hfloor,
    hcapfloor.1, hcapfloor.2.1, hcapfloor.2.2, hgap.2.2, ?_⟩
  intro j hj
  by_cases hj0 : j.val = 0
  · have he : j = 0 := Fin.ext hj0
    rw [he]
    exact hgap.1
  · exact cap_fixed_prefix_support w X Y hX hY hgrid v hv hprefix hchanged hfloor j
      (by omega) hj

/-- `thm:ratio-rigidity` on the actual heterogeneous grid-defect ratio locus. -/
theorem ratio_rigidity {m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected)
    (hinner : ∀ (i : Fin n) (j : Fin m), i.val = j.val → X.inner i = Y.inner j)
    (hG : gridDefect X Y ≠ 0) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    ∃ hn : n = m, let Z : Diagram n := hn.symm ▸ Y;
      ∃ (v : Fin n) (hv : 0 < v.val),
        (∀ j, X.capShift j = Z.capShift j) ∧
        (∀ i : Fin n, i.val < v.val → X.rowParam i = Z.rowParam i) ∧
        X.rowParam v ≠ Z.rowParam v ∧
        ∀ w : ConvexWeight,
          (∀ j : Fin (n + 1), j ∈ defectMinimizers w X Z (-(ratioVirtualShift r a : ℤ)) ↔
            j.val = 0 ∨ j.val = 1) ∧
          positiveFloor w X Z < defectAction w X Z 0 ∧
          (∀ i : Fin v.val, ∀ j : Fin (n + 1),
            j ∈ defectMinimizers w X Z
                (X.rowParam ⟨i.val, by have := i.isLt; have := v.isLt; omega⟩) ↔
              j.val = i.val + 1 ∨ j.val = i.val + 2) ∧
          (Finset.univ.filter (fun j : Fin (n + 1) =>
            0 < j.val ∧ defectAction w X Z j = positiveFloor w X Z)).image X.capShift =
            {X.capShift ⟨1, by have := v.isLt; have := hv; omega⟩,
              X.capShift ⟨2, by have := v.isLt; have := hv; omega⟩} ∧
          positiveFloor w X Z = defectAction w X Z ⟨1, by have := v.isLt; have := hv; omega⟩ ∧
          defectAction w X Z ⟨1, by have := v.isLt; have := hv; omega⟩ =
            defectAction w X Z ⟨2, by have := v.isLt; have := hv; omega⟩ ∧
          (leastWeight w.generatorWeight (cofactorDefect X Z 0) -
              (leastWeight w.generatorWeight (cofactorDefect X Z 1) +
                w.weight (X.capShift 1).toNat) =
            w.weight (ratioVirtualShift r a + (X.capShift 1).toNat) -
              w.weight (ratioVirtualShift r a) - w.weight (X.capShift 1).toNat) ∧
          (∀ j : Fin (n + 1), j.val ≤ v.val + 1 → cofactorDefect X Z j ≠ 0) := by
  have hn := rowCount_eq_of_ratioIdentity X Y hX hY r a ha h
  subst m
  refine ⟨rfl, ?_⟩
  exact ratio_rigidity_same_count X Y hX hY
    (funext fun i => hinner i i rfl) hG r a ha h

/-- The exact square-weight gap on the actual heterogeneous ratio locus. -/
theorem ratio_square_gap {m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected)
    (hinner : ∀ (i : Fin n) (j : Fin m), i.val = j.val → X.inner i = Y.inner j)
    (hG : gridDefect X Y ≠ 0) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    ∃ hn : n = m, let Z : Diagram n := hn.symm ▸ Y;
      cofactorDefect X Z 0 ≠ 0 ∧ cofactorDefect X Z 1 ≠ 0 ∧
        leastWeight squareWeight.generatorWeight (cofactorDefect X Z 0) -
          (leastWeight squareWeight.generatorWeight (cofactorDefect X Z 1) +
            squareWeight.weight (X.capShift 1).toNat) =
          2 * (ratioVirtualShift r a : ℝ) * ((X.capShift 1).toNat : ℝ) := by
  have hn := rowCount_eq_of_ratioIdentity X Y hX hY r a ha h
  subst m
  obtain ⟨v, hv, hgrid, hprefix, hchanged, _⟩ := ratio_rigidity_same_count X Y hX hY
    (funext fun i => hinner i i rfl) hG r a ha h
  obtain ⟨hG0, hG1, _⟩ := ratio_virtual_gap_normalized squareWeight X Y hX hY hgrid
    r a ha h v hprefix hchanged
  exact ⟨rfl, hG0, hG1,
    ratio_square_gap_normalized X Y hX hY hgrid r a ha h v hprefix hchanged⟩

end Diagram
end SkewSchurReconstruction
