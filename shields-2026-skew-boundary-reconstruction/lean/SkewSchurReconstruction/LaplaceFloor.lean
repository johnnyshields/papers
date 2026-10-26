/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.RatioRigidity
import SkewSchurReconstruction.PolynomialValuation

/-!
# The positive Laplace floor component

Formalizes "Cancellative Leftmost as a square-weight specialization" (`subsec:floor`),
`lem:laplace-equivalence`, `eq:J0`, `eq:J0-equivalence`, and `thm:floor`.
The positive floor component follows from the actual zeroth-row cofactor relation. Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

variable {n : ℕ}

/-- The positive columns attaining the actual normalized defect floor. -/
noncomputable def positiveFloorFace (w : ConvexWeight) (X Y : Diagram n) :
    Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun j => 0 < j.val ∧ defectAction w X Y j = positiveFloor w X Y)

/-- The actual positive Laplace floor polynomial `eq:J0`. -/
noncomputable def laplaceFloorSum (w : ConvexWeight) (X Y : Diagram n) : CompleteRing :=
  ∑ j ∈ positiveFloorFace w X Y,
    complete (X.capShift j) * initialForm w.generatorWeight (cofactorDefect X Y j)

/-- Common-grid identification of the actual heterogeneous defect. -/
theorem gridDefect_apply_of_common_grid (X Y : Diagram n)
    (hgrid : ∀ j, X.capShift j = Y.capShift j) (j : Fin (n + 1)) :
    gridDefect X Y (X.capShift j) = cofactorDefect X Y j := by
  rw [gridDefect, Finsupp.sub_apply, X.cofactorGridVector_apply_capShift,
    hgrid j, Y.cofactorGridVector_apply_capShift]
  rfl

/-- Nonzero actual grid defects have a nonzero positive coordinate. -/
theorem exists_positive_defect_coordinate (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hG : gridDefect X Y ≠ 0) :
    ∃ j : Fin (n + 1), 0 < j.val ∧ cofactorDefect X Y j ≠ 0 := by
  let e := lastDefectShift X Y hG
  have he : gridDefect X Y e ≠ 0 := Finsupp.mem_support_iff.mp (lastDefectShift_mem X Y hG)
  have hep : 0 < e := lastDefectShift_pos X Y hX hY hG
  have hxe : X.cofactorGridVector e ≠ 0 := by
    intro hx
    have hye : Y.cofactorGridVector e ≠ 0 := by
      intro hy
      exact he (by simp [gridDefect, hx, hy])
    obtain ⟨j, hj⟩ := Y.exists_capShift_of_gridVector_ne_zero e hye
    have hxj : X.capShift j = e := (hgrid j).trans hj
    rw [← hxj, X.cofactorGridVector_apply_capShift] at hx
    exact X.cofactor_ne_zero squareWeight hX j hx
  obtain ⟨j, hj⟩ := X.exists_capShift_of_gridVector_ne_zero e hxe
  refine ⟨j, ?_, ?_⟩
  · by_contra hn
    have hz : j = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    rw [hz, X.capShift_zero] at hj
    omega
  · rw [← hj, gridDefect_apply_of_common_grid X Y hgrid j] at he
    exact he

/-- The positive normalized floor is finite, derived from an actual nonzero defect. -/
theorem positiveFloor_ne_top (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hG : gridDefect X Y ≠ 0) : positiveFloor w X Y ≠ ⊤ := by
  obtain ⟨j, hj, hg⟩ := exists_positive_defect_coordinate X Y hX hY hgrid hG
  have hle : positiveFloor w X Y ≤ defectAction w X Y j := by
    apply Finset.inf_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  intro ht
  rw [ht] at hle
  exact hg ((defectAction_eq_top_iff w X Y j).mp (top_le_iff.mp hle))

/-- The positive part of the actual zeroth-row relation is minus its zeroth coordinate. -/
theorem positive_laplace_sum_eq_neg_zero (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => 0 < j.val),
      complete (X.capShift j) * cofactorDefect X Y j) = -cofactorDefect X Y 0 := by
  classical
  let i : Fin n := ⟨0, hX.1⟩
  have hr := X.common_row_defect_relation Y (funext hgrid) i
    (by rw [X.rowParam_zero hX.1, Y.rowParam_zero hY.1])
  rw [X.rowParam_zero hX.1] at hr
  simp only [sub_zero] at hr
  change (∑ j, complete (X.capShift j) * cofactorDefect X Y j) = 0 at hr
  have hs : Finset.univ.filter (fun j : Fin (n + 1) => 0 < j.val) =
      Finset.univ.erase 0 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hj
      exact ⟨fun h => by rw [h] at hj; exact Nat.lt_irrefl 0 hj, True.intro⟩
    · intro hj
      by_contra hn
      apply hj.1
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
  rw [hs]
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => complete (X.capShift j) * cofactorDefect X Y j) (Finset.mem_univ 0)] at hr
  simp only [X.capShift_zero, complete_zero, one_mul] at hr
  exact eq_neg_of_add_eq_zero_right hr

theorem laplace_summand_valuation (w : ConvexWeight) (X Y : Diagram n)
    (j : Fin (n + 1)) :
    monomialValuation w.generatorWeight (complete (X.capShift j) * cofactorDefect X Y j) =
      defectAction w X Y j := by
  rw [monomialValuation_mul, complete_monomialValuation w _ (X.capShift_nonneg j)]
  exact add_comm _ _

/-- Own row zero proves the lower bound `alpha_0 >= m_+`. -/
theorem zero_action_ge_positiveFloor (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j) :
    positiveFloor w X Y ≤ defectAction w X Y 0 := by
  have hv := (polynomialAddValuation w.generatorWeight).map_le_sum
    (s := Finset.univ.filter (fun j : Fin (n + 1) => 0 < j.val))
    (f := fun j => complete (X.capShift j) * cofactorDefect X Y j)
    (g := positiveFloor w X Y) (by
      intro j hj
      rw [polynomialAddValuation_apply, laplace_summand_valuation]
      exact Finset.inf_le hj)
  rw [positive_laplace_sum_eq_neg_zero X Y hX hY hgrid,
    polynomialAddValuation_apply, monomialValuation_neg] at hv
  simpa only [defectAction, X.capShift_zero, Int.toNat_zero, w.zero,
    WithTop.coe_zero, add_zero] using hv

private theorem component_zero_iff_of_lower_bound {w : ℕ+ → ℝ} (p : CompleteRing) (a : ℝ)
    (hbound : (a : WithTop ℝ) ≤ monomialValuation w p) :
    MvPolynomial.weightedHomogeneousComponent w a p = 0 ↔
      (a : WithTop ℝ) < monomialValuation w p := by
  by_cases hp : p = 0
  · subst p
    simp only [map_zero, monomialValuation_zero, WithTop.coe_lt_top]
  · have hv := monomialValuation_eq_coe (w := w) hp
    rw [hv] at hbound ⊢
    have hab : a ≤ leastWeight w p := WithTop.coe_le_coe.mp hbound
    constructor
    · intro hc
      apply WithTop.coe_lt_coe.mpr
      by_contra hn
      have he : a = leastWeight w p := le_antisymm hab (le_of_not_gt hn)
      rw [he] at hc
      exact initialForm_ne_zero hp hc
    · intro hlt
      have hreal := WithTop.coe_lt_coe.mp hlt
      apply component_eq_zero_of_strict_lowerBound
      intro d hd
      exact hreal.trans_le (leastWeight_lowerBound w p d hd)

private theorem positiveFloor_eq_coe (w : ConvexWeight) (X Y : Diagram n)
    (hf : positiveFloor w X Y ≠ ⊤) :
    positiveFloor w X Y =
      ((WithTop.untopD (0 : ℝ) (positiveFloor w X Y) : ℝ) : WithTop ℝ) := by
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hf
  rw [← hc, WithTop.untopD_coe]

/-- The component at the positive floor is exactly the positive Laplace floor polynomial. -/
theorem positive_sum_floor_component (w : ConvexWeight) (X Y : Diagram n)
    (hf : positiveFloor w X Y ≠ ⊤) :
    MvPolynomial.weightedHomogeneousComponent w.generatorWeight
        (WithTop.untopD (0 : ℝ) (positiveFloor w X Y))
        (∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => 0 < j.val),
          complete (X.capShift j) * cofactorDefect X Y j) =
      laplaceFloorSum w X Y := by
  classical
  let m : ℝ := WithTop.untopD (0 : ℝ) (positiveFloor w X Y)
  have hm : positiveFloor w X Y = (m : WithTop ℝ) := positiveFloor_eq_coe w X Y hf
  have hface : positiveFloorFace w X Y =
      (Finset.univ.filter (fun j : Fin (n + 1) => 0 < j.val)).filter
        (fun j => defectAction w X Y j = positiveFloor w X Y) := by
    ext j
    simp [positiveFloorFace]
  rw [map_sum, laplaceFloorSum, hface]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  have hb : positiveFloor w X Y ≤ defectAction w X Y j := Finset.inf_le hj
  have hv := laplace_summand_valuation w X Y j
  by_cases he : defectAction w X Y j = positiveFloor w X Y
  · rw [ite_eq_left he]
    have hp : complete (X.capShift j) * cofactorDefect X Y j ≠ 0 := by
      intro hz
      rw [hz, monomialValuation_zero, he] at hv
      exact hf hv.symm
    have hl := monomialValuation_eq_coe (w := w.generatorWeight) hp
    rw [hv, he, hm] at hl
    have hweight : leastWeight w.generatorWeight
        (complete (X.capShift j) * cofactorDefect X Y j) = m :=
      (WithTop.coe_injective hl).symm
    have hcomponent : MvPolynomial.weightedHomogeneousComponent w.generatorWeight m
        (complete (X.capShift j) * cofactorDefect X Y j) =
        initialForm w.generatorWeight (complete (X.capShift j) * cofactorDefect X Y j) := by
      unfold initialForm
      rw [hweight]
    have hcomplete := complete_ne_zero_of_nonneg (X.capShift j) (X.capShift_nonneg j)
    have hdefect := (mul_ne_zero_iff.mp hp).2
    change MvPolynomial.weightedHomogeneousComponent w.generatorWeight m
      (complete (X.capShift j) * cofactorDefect X Y j) = _
    rw [hcomponent, initialForm_mul hcomplete hdefect,
      complete_initialForm w _ (X.capShift_nonneg j)]
  · rw [ite_eq_right he]
    have hlt : (m : WithTop ℝ) <
        monomialValuation w.generatorWeight (complete (X.capShift j) * cofactorDefect X Y j) := by
      rw [hv, ← hm]
      exact lt_of_le_of_ne hb (fun h => he h.symm)
    exact (component_zero_iff_of_lower_bound _ m hlt.le).mpr hlt

/-- Own row zero identifies `J0` with minus the floor component of the zeroth defect. -/
theorem laplaceFloorSum_eq_neg_zero_component (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hG : gridDefect X Y ≠ 0) :
    laplaceFloorSum w X Y =
      -MvPolynomial.weightedHomogeneousComponent w.generatorWeight
        (WithTop.untopD (0 : ℝ) (positiveFloor w X Y)) (cofactorDefect X Y 0) := by
  have hc := congrArg
    (MvPolynomial.weightedHomogeneousComponent w.generatorWeight
      (WithTop.untopD (0 : ℝ) (positiveFloor w X Y)))
    (positive_laplace_sum_eq_neg_zero X Y hX hY hgrid)
  rw [positive_sum_floor_component w X Y (positiveFloor_ne_top w X Y hX hY hgrid hG),
    map_neg] at hc
  exact hc

/-- The actual positive Laplace floor vanishes exactly on the strict-floor branch. -/
theorem laplaceFloorSum_eq_zero_iff (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hG : gridDefect X Y ≠ 0) :
    laplaceFloorSum w X Y = 0 ↔ positiveFloor w X Y < defectAction w X Y 0 := by
  let m : ℝ := WithTop.untopD (0 : ℝ) (positiveFloor w X Y)
  have hm : positiveFloor w X Y = (m : WithTop ℝ) :=
    positiveFloor_eq_coe w X Y (positiveFloor_ne_top w X Y hX hY hgrid hG)
  have hz : defectAction w X Y 0 = monomialValuation w.generatorWeight (cofactorDefect X Y 0) := by
    simp only [defectAction, X.capShift_zero, Int.toNat_zero, w.zero,
      WithTop.coe_zero, add_zero]
  have hb := zero_action_ge_positiveFloor w X Y hX hY hgrid
  rw [hm, hz] at hb
  rw [laplaceFloorSum_eq_neg_zero_component w X Y hX hY hgrid hG, neg_eq_zero, hm, hz]
  exact component_zero_iff_of_lower_bound _ m hb

private theorem positive_defect_shift_support_nonempty (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hG : gridDefect X Y ≠ 0) :
    ((gridDefect X Y).support.filter (fun d => 0 < d)).Nonempty := by
  classical
  refine ⟨lastDefectShift X Y hG, Finset.mem_filter.mpr ⟨lastDefectShift_mem X Y hG, ?_⟩⟩
  exact lastDefectShift_pos X Y hX hY hG

/-- The actual leftmost positive supported union-grid shift. -/
noncomputable def firstPositiveDefectShift (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hG : gridDefect X Y ≠ 0) : ℤ :=
  ((gridDefect X Y).support.filter (fun d => 0 < d)).min'
    (positive_defect_shift_support_nonempty X Y hX hY hG)

theorem firstPositiveDefectShift_eq_one (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hG : gridDefect X Y ≠ 0) (hG1 : cofactorDefect X Y 1 ≠ 0) :
    firstPositiveDefectShift X Y hX hY hG = X.capShift 1 := by
  classical
  have hn : 0 < n := hX.1
  have hv1 : (1 : Fin (n + 1)).val = 1 := by
    change 1 % (n + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  let z : Fin n := ⟨0, hn⟩
  have hz : z.succ = (1 : Fin (n + 1)) := by
    apply Fin.ext
    change 1 = (1 : Fin (n + 1)).val
    exact hv1.symm
  have hd1 : 0 < X.capShift 1 := by rw [← hz]; exact X.capShift_succ_pos z
  have hm1 : X.capShift 1 ∈ (gridDefect X Y).support.filter (fun d => 0 < d) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finsupp.mem_support_iff.mpr
      (by rwa [gridDefect_apply_of_common_grid X Y hgrid 1]), hd1⟩
  let t := firstPositiveDefectShift X Y hX hY hG
  have htmem : t ∈ (gridDefect X Y).support.filter (fun d => 0 < d) :=
    Finset.min'_mem _ _
  obtain ⟨htsupport, htpos⟩ := Finset.mem_filter.mp htmem
  have htnz := Finsupp.mem_support_iff.mp htsupport
  have hex : ∃ j : Fin (n + 1), X.capShift j = t := by
    by_cases hx : X.cofactorGridVector t = 0
    · have hy : Y.cofactorGridVector t ≠ 0 := by
        intro hy
        exact htnz (by simp [gridDefect, hx, hy])
      obtain ⟨j, hj⟩ := Y.exists_capShift_of_gridVector_ne_zero t hy
      exact ⟨j, (hgrid j).trans hj⟩
    · exact X.exists_capShift_of_gridVector_ne_zero t hx
  obtain ⟨j, hj⟩ := hex
  have hjpos : 0 < j.val := by
    by_contra hh
    have hj0 : j = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    rw [hj0, X.capShift_zero] at hj
    omega
  have hlower : X.capShift 1 ≤ t := by
    rw [← hj]
    apply X.capShift_strictMono.monotone
    change (1 : Fin (n + 1)).val ≤ j.val
    rw [hv1]
    omega
  have hupper : t ≤ X.capShift 1 := Finset.min'_le _ _ hm1
  exact le_antisymm hupper hlower

theorem ratio_global_square_bound_normalized (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (r a : ℕ) (ha : 0 < a) (h : RatioIdentity (gridDefect X Y) r a)
    (v : Fin n) (hv : 0 < v.val)
    (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    cofactorDefect X Y 0 ≠ 0 ∧
      ∀ j : Fin (n + 1), cofactorDefect X Y j ≠ 0 →
        leastWeight squareWeight.generatorWeight (cofactorDefect X Y 0) -
          (leastWeight squareWeight.generatorWeight (cofactorDefect X Y j) +
            squareWeight.weight (X.capShift j).toNat) ≤
          2 * (ratioVirtualShift r a : ℝ) * ((X.capShift j).toNat : ℝ) := by
  obtain ⟨hG0, hG1, _⟩ := ratio_virtual_gap_normalized squareWeight X Y hX hY hgrid
    r a ha h v hprefix hchanged
  have hfloor := ratio_strict_floor_normalized squareWeight X Y hX hY hgrid r a ha h
    v hprefix hchanged
  have hcapfloor := cap_fixed_floor squareWeight X Y hX hY hgrid v hv hprefix hchanged hfloor
  have hgap := ratio_square_gap_normalized X Y hX hY hgrid r a ha h v hprefix hchanged
  refine ⟨hG0, ?_⟩
  intro j hj
  by_cases hj0 : j.val = 0
  · have hj' : j = 0 := Fin.ext hj0
    rw [hj']
    simp only [X.capShift_zero, Int.toNat_zero, squareWeight.zero, Nat.cast_zero,
      add_zero, sub_self, mul_zero, le_refl]
  · have hjpos : 0 < j.val := by omega
    have hle : defectAction squareWeight X Y 1 ≤ defectAction squareWeight X Y j := by
      have hv1 : (⟨1, by have := v.isLt; omega⟩ : Fin (n + 1)) = 1 := by
        apply Fin.ext
        change 1 = 1 % (n + 1)
        exact (Nat.mod_eq_of_lt (by have := v.isLt; have := hv; omega)).symm
      rw [← hv1, ← hcapfloor.2.1]
      apply Finset.inf_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjpos⟩
    simp only [defectAction, monomialValuation_eq_coe hG1, monomialValuation_eq_coe hj,
      ← WithTop.coe_add, WithTop.coe_le_coe] at hle
    have hd : (X.capShift 1).toNat ≤ (X.capShift j).toNat := by
      have hval1 : (1 : Fin (n + 1)).val = 1 := by
        change 1 % (n + 1) = 1
        exact Nat.mod_eq_of_lt (by have := v.isLt; have := hv; omega)
      have hdc := X.capShift_strictMono.monotone (show (1 : Fin (n + 1)) ≤ j by
        change (1 : Fin (n + 1)).val ≤ j.val; rw [hval1]; omega)
      omega
    have hdR : ((X.capShift 1).toNat : ℝ) ≤ ((X.capShift j).toNat : ℝ) := by exact_mod_cast hd
    have hgamma : 0 < (ratioVirtualShift r a : ℝ) := by
      exact_mod_cast ratioVirtualShift_pos r a ha
    nlinarith

/-- The Cancellative Leftmost conclusion and supplied global floor bound on actual ratio pairs. -/
theorem ratio_floor_same_count (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hinner : X.inner = Y.inner)
    (hG : gridDefect X Y ≠ 0) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    ∃ (v : Fin n) (hv : 0 < v.val),
      laplaceFloorSum squareWeight X Y = 0 ∧
      positiveFloor squareWeight X Y < defectAction squareWeight X Y 0 ∧
      (positiveFloorFace squareWeight X Y).image X.capShift =
        {X.capShift ⟨1, by have := v.isLt; have := hv; omega⟩,
          X.capShift ⟨2, by have := v.isLt; have := hv; omega⟩} ∧
      firstPositiveDefectShift X Y hX hY hG = X.capShift 1 ∧
      cofactorDefect X Y 0 ≠ 0 ∧
      (∀ j : Fin (n + 1), cofactorDefect X Y j ≠ 0 →
        leastWeight squareWeight.generatorWeight (cofactorDefect X Y 0) -
          (leastWeight squareWeight.generatorWeight (cofactorDefect X Y j) +
            squareWeight.weight (X.capShift j).toNat) ≤
          2 * (ratioVirtualShift r a : ℝ) * ((X.capShift j).toNat : ℝ)) ∧
      (∀ j : Fin (n + 1), j.val ≤ v.val + 1 → cofactorDefect X Y j ≠ 0) := by
  obtain ⟨v, hv, hgrid, hprefix, hchanged, hall⟩ :=
    ratio_rigidity_same_count X Y hX hY hinner hG r a ha h
  obtain ⟨_, hfloor, _, hface, _, _, _, hsolid⟩ := hall squareWeight
  obtain ⟨hG0, hbound⟩ := ratio_global_square_bound_normalized X Y hX hY hgrid r a ha h
    v hv hprefix hchanged
  have hval1 : (1 : Fin (n + 1)).val = 1 := by
    change 1 % (n + 1) = 1
    exact Nat.mod_eq_of_lt (by have := v.isLt; have := hv; omega)
  have hG1 : cofactorDefect X Y 1 ≠ 0 := hsolid 1 (by rw [hval1]; omega)
  refine ⟨v, hv, (laplaceFloorSum_eq_zero_iff squareWeight X Y hX hY hgrid hG).mpr hfloor,
    hfloor, hface, firstPositiveDefectShift_eq_one X Y hX hY hgrid hG hG1,
    hG0, hbound, hsolid⟩

theorem ratio_cancellative_leftmost_same_count (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected) (hinner : X.inner = Y.inner)
    (hG : gridDefect X Y ≠ 0) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    laplaceFloorSum squareWeight X Y = 0 ∧
      firstPositiveDefectShift X Y hX hY hG ∈
        (positiveFloorFace squareWeight X Y).image X.capShift := by
  obtain ⟨v, hv, hJ, _, hface, hfirst, _, _, _⟩ :=
    ratio_floor_same_count X Y hX hY hinner hG r a ha h
  refine ⟨hJ, ?_⟩
  rw [hfirst, hface]
  have hindex : (⟨1, by have := v.isLt; have := hv; omega⟩ : Fin (n + 1)) = 1 := by
    apply Fin.ext
    change 1 = 1 % (n + 1)
    exact (Nat.mod_eq_of_lt (by have := v.isLt; have := hv; omega)).symm
  rw [hindex]
  exact Finset.mem_insert_self _ _

/-- The floor, supplied global bound, and solid prefix on heterogeneous actual ratio pairs. -/
theorem ratio_floor {m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected)
    (hinner : ∀ (i : Fin n) (j : Fin m), i.val = j.val → X.inner i = Y.inner j)
    (hG : gridDefect X Y ≠ 0) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    ∃ hn : n = m, let Z : Diagram n := hn.symm ▸ Y;
      let hZ : Z.Connected := (by cases hn; exact hY);
      let hGZ : gridDefect X Z ≠ 0 := (by cases hn; exact hG);
      ∃ (v : Fin n) (hv : 0 < v.val),
        laplaceFloorSum squareWeight X Z = 0 ∧
        positiveFloor squareWeight X Z < defectAction squareWeight X Z 0 ∧
        (positiveFloorFace squareWeight X Z).image X.capShift =
          {X.capShift ⟨1, by have := v.isLt; have := hv; omega⟩,
            X.capShift ⟨2, by have := v.isLt; have := hv; omega⟩} ∧
        firstPositiveDefectShift X Z hX hZ hGZ = X.capShift 1 ∧
        cofactorDefect X Z 0 ≠ 0 ∧
        (∀ j : Fin (n + 1), cofactorDefect X Z j ≠ 0 →
          leastWeight squareWeight.generatorWeight (cofactorDefect X Z 0) -
            (leastWeight squareWeight.generatorWeight (cofactorDefect X Z j) +
              squareWeight.weight (X.capShift j).toNat) ≤
            2 * (ratioVirtualShift r a : ℝ) * ((X.capShift j).toNat : ℝ)) ∧
        (∀ j : Fin (n + 1), j.val ≤ v.val + 1 → cofactorDefect X Z j ≠ 0) := by
  have hn := rowCount_eq_of_ratioIdentity X Y hX hY r a ha h
  subst m
  refine ⟨rfl, ?_⟩
  exact ratio_floor_same_count X Y hX hY (funext fun i => hinner i i rfl) hG r a ha h

/-- The leftmost positive supported shift belongs to the floor, and `J0=0` is automatic. -/
theorem ratio_cancellative_leftmost {m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected)
    (hinner : ∀ (i : Fin n) (j : Fin m), i.val = j.val → X.inner i = Y.inner j)
    (hG : gridDefect X Y ≠ 0) (r a : ℕ) (ha : 0 < a)
    (h : RatioIdentity (gridDefect X Y) r a) :
    ∃ hn : n = m, let Z : Diagram n := hn.symm ▸ Y;
      let hZ : Z.Connected := (by cases hn; exact hY);
      let hGZ : gridDefect X Z ≠ 0 := (by cases hn; exact hG);
      laplaceFloorSum squareWeight X Z = 0 ∧
        firstPositiveDefectShift X Z hX hZ hGZ ∈
          (positiveFloorFace squareWeight X Z).image X.capShift := by
  have hn := rowCount_eq_of_ratioIdentity X Y hX hY r a ha h
  subst m
  refine ⟨rfl, ?_⟩
  exact ratio_cancellative_leftmost_same_count X Y hX hY
    (funext fun i => hinner i i rfl) hG r a ha h

end Diagram
end SkewSchurReconstruction
