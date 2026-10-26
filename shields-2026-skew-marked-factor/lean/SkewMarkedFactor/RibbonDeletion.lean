/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.MarkedCharts
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Kernel.Main

/-!
# Ribbon deletion

The geometric statements of «Marked composition and the power-sum action»,
«Ribbon deletion» (`sec:action`, `subsec:ribbon-action`, `lem:ribbon-deletion`).
Heights below are integer equalities, not merely equalities of ribbon signs.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan

/-- The algebraic empty-outer convention, independently of geometric composition. -/
noncomputable def compositionValue (η : MarkedInner) (D : Diagram) : Lambda :=
  cellSchur (Plan.MarkedInner.copies η D)

@[simp] theorem composition_value_empty (η : MarkedInner) : compositionValue η ∅ = 1 := by
  simp [compositionValue, Plan.MarkedInner.copies_empty, cellSchur_empty]

theorem composition_value_nonempty {η : MarkedInner} (ho : η.IsOrdinary)
    {D : Diagram} (hD : D.Nonempty) :
    compositionValue η D = cellSchur (η.compose D) := by
  rw [compositionValue, Plan.MarkedInner.compose_eq_copies ho hD]

/-- A span obstruction excludes southeast as well as northwest removable ribbons. -/
theorem right_ribbons_empty_of_span_lt {X : Diagram} {n : ℕ} (h : span X < n) :
    rightRibbons X n = ∅ := by
  ext Y
  rw [mem_rightRibbons]
  simp only [Finset.notMem_empty, iff_false]
  rintro ⟨hYX, hcard, hrib, _⟩
  have hs : span Y ≤ span X := Finset.card_le_card (Finset.image_subset_image hYX)
  have := hrib.2
  omega

/-- None of the three actual normalization diagrams has a positive-multiple ribbon. -/
theorem normalizer_no_ribbons {η : MarkedInner} (hη : η.IsLegal) {m : ℕ} (hm : 0 < m) :
    leftRibbons η.W (m * η.period.toNat) = ∅ ∧
    rightRibbons η.W (m * η.period.toNat) = ∅ ∧
    leftRibbons (hatMarkFin η) (m * η.period.toNat) = ∅ ∧
    rightRibbons (hatMarkFin η) (m * η.period.toNat) = ∅ ∧
    leftRibbons (hatMiddleFin η) (m * η.period.toNat) = ∅ ∧
    rightRibbons (hatMiddleFin η) (m * η.period.toNat) = ∅ := by
  have hp := hη.period_pos
  have hw := hη.2.2.1.2
  have hmul : η.period.toNat ≤ m * η.period.toNat := Nat.le_mul_of_pos_left _ hm
  have hW : span η.W < m * η.period.toNat := by change η.width < _; omega
  have hhat := Gluing.MarkedInner.span_hatMarkFin_le η
  have hB : span (hatMarkFin η) < m * η.period.toNat := by omega
  have hmid := hη.span_hatMiddleFin_lt
  have hC : span (hatMiddleFin η) < m * η.period.toNat := by omega
  exact ⟨leftRibbons_eq_empty_of_span_lt hW, right_ribbons_empty_of_span_lt hW,
    leftRibbons_eq_empty_of_span_lt hB, right_ribbons_empty_of_span_lt hB,
    leftRibbons_eq_empty_of_span_lt hC, right_ribbons_empty_of_span_lt hC⟩

/-- Exact height of a lifted northwest ribbon, before rotation to the southeast. -/
theorem lift_height_exact {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {D R : Diagram} (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m)
    (hR : R ∈ leftRibbons D m) :
    (ribbonHeight (liftRibbon η D R) : ℤ) =
      (ribbonHeight R : ℤ) - (m : ℤ) * η.v.1 := by
  obtain ⟨t, fLo, fHi, hM, hkey⟩ := EdgeRibbon.exists_model hη hc hD
  obtain ⟨j, hj1, hj2, hstart, hend, rfl⟩ :=
    (mem_leftRibbons_iff_segment hD hm).mp hR
  rw [EdgeRibbon.liftRibbon_segment hc hM hkey hj1 hj2]
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have hp := hη.period_pos
  have hpn : ((η.period.toNat : ℕ) : ℤ) = η.period := Int.toNat_of_nonneg hp.le
  have hmn : ((m * η.period.toNat : ℕ) : ℤ) = (m : ℤ) * η.period := by
    push_cast; rw [hpn]
  have hpos : 0 < m * η.period.toNat := Nat.mul_pos hm (by omega)
  obtain ⟨hlo, hhi, _, _⟩ := (hM.removable_iff hmz).mpr
    ⟨j, hj1, hj2, hstart, hend, rfl⟩
  have hF := isConnectedSkew_iff_diagonal.mp (hη.isConnectedSkew_compose hD)
  have houter := ribbonHeight_segment (isConnectedSkew_iff_diagonal.mp hD) hm hj1 hj2
  have hinner := ribbonHeight_segment hF hpos hlo (by rw [hmn]; exact hhi)
  have hheight := hM.diagLo_start_end (j₀ := j) (n := m) hj1 hmz hj2
  rw [hmn] at hinner
  rw [hinner, houter]
  exact hheight

/-- Antitransposition exchanges rows and columns. -/
theorem num_rows_antitranspose (D : Diagram) : numRows (antitranspose D) = numCols D := by
  unfold numRows rowSet antitranspose
  rw [numCols_eq_card_image_snd, Finset.image_image]
  have he : (Prod.fst : ℤ × ℤ → ℤ) ∘ (fun x : ℤ × ℤ => (-x.2, -x.1)) =
      (fun i : ℤ => -i) ∘ Prod.snd := rfl
  rw [he, ← Finset.image_image, Finset.card_image_of_injective _ neg_injective]

/-- The height complement of a ribbon is an integer identity. -/
theorem ribbon_height_antitranspose {R : Diagram} (hR : IsRibbon R) :
    (ribbonHeight (antitranspose R) : ℤ) + ribbonHeight R = (R.card : ℤ) - 1 := by
  have hspan := span_add_one_eq_numRows_add_numCols hR.1
  have hr : 0 < numRows R := by
    unfold numRows rowSet
    exact Finset.card_pos.mpr (hR.1.2.1.image _)
  have hc : 0 < numCols R := by
    rw [numCols_eq_card_image_snd]
    exact Finset.card_pos.mpr (hR.1.2.1.image _)
  unfold ribbonHeight
  rw [num_rows_antitranspose]
  rw [← hR.2] at hspan
  omega

theorem is_ribbon_antitranspose {R : Diagram} (hR : IsRibbon R) :
    IsRibbon (antitranspose R) :=
  ⟨isConnectedSkew_antitranspose hR.1, by
    rw [card_antitranspose, span, contents_antitranspose]; exact hR.2⟩

theorem downset_antitranspose_iff (X R : Diagram) :
    IsDownsetIn (antitranspose X) (antitranspose R) ↔ IsUpsetIn X R := by
  constructor
  · rintro ⟨hsub, hdown⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have := hsub (show atVec x ∈ antitranspose R by
        rw [mem_antitranspose']; simpa only [atVec_atVec] using hx)
      rw [mem_antitranspose'] at this
      simpa only [atVec_atVec] using this
    · intro x hx y hy h1 h2
      have := hdown (atVec x) (by rw [mem_antitranspose']; simpa only [atVec_atVec] using hx)
        (atVec y) (by rw [mem_antitranspose']; simpa only [atVec_atVec] using hy)
        (by simp only [atVec]; omega) (by simp only [atVec]; omega)
      rw [mem_antitranspose'] at this
      simpa only [atVec_atVec] using this
  · rintro ⟨hsub, hup⟩
    refine ⟨antitranspose_subset hsub, ?_⟩
    intro x hx y hy h1 h2
    rw [mem_antitranspose'] at hx hy ⊢
    apply hup (atVec x) hx (atVec y) hy <;> simp only [atVec] <;> omega

theorem left_ribbons_antitranspose (D : Diagram) (m : ℕ) :
    leftRibbons (antitranspose D) m = (rightRibbons D m).image antitranspose := by
  ext R
  rw [Finset.mem_image]
  constructor
  · intro hR
    have h := mem_leftRibbons.mp hR
    refine ⟨antitranspose R, ?_, antitranspose_antitranspose⟩
    rw [mem_rightRibbons]
    refine ⟨by simpa only [antitranspose_antitranspose] using antitranspose_subset h.1,
      by rw [card_antitranspose]; exact h.2.1,
      is_ribbon_antitranspose h.2.2.1, ?_⟩
    have hh : IsDownsetIn (antitranspose D) (antitranspose (antitranspose R)) := by
      rw [antitranspose_antitranspose]; exact h.2.2.2
    exact (downset_antitranspose_iff D (antitranspose R)).mp hh
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨hsub, hcard, hrib, hup⟩ := mem_rightRibbons.mp hA
    rw [mem_leftRibbons]
    exact ⟨antitranspose_subset hsub, by rw [card_antitranspose]; exact hcard,
      is_ribbon_antitranspose hrib, (downset_antitranspose_iff D A).mpr hup⟩

theorem ribbon_sign_antitranspose {R : Diagram} (hR : IsRibbon R) :
    ribbonSign (antitranspose R) = (-1 : ℤ) ^ (R.card - 1) * ribbonSign R := by
  have hH := ribbon_height_antitranspose hR
  have hr : 0 < R.card := Finset.card_pos.mpr hR.1.2.1
  unfold ribbonSign
  rw [← pow_add, neg_one_pow_eq_pow_mod_two (n := ribbonHeight _),
    neg_one_pow_eq_pow_mod_two (n := _ + ribbonHeight R)]
  congr 1
  omega

/-- The actual outer involution, including its ribbon sign. -/
theorem ribbon_sum_antitranspose (F : Diagram → Lambda) (D : Diagram) (m : ℕ) :
    ribbonSumLeft F (antitranspose D) m = (-1 : Lambda) ^ (m - 1) *
      ribbonSumRight (fun X => F (antitranspose X)) D m := by
  unfold ribbonSumLeft ribbonSumRight
  rw [left_ribbons_antitranspose, Finset.sum_image
    (fun A _ B _ h => antitranspose_injective h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_
  obtain ⟨_, hcard, hrib, _⟩ := mem_rightRibbons.mp hR
  rw [ribbon_sign_antitranspose hrib, hcard, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, ← antitranspose_sdiff]
  ring

/-- Height of one actual key ribbon. -/
def keyHeight (η : MarkedInner) : ℕ := ribbonHeight (keyRibbon η)

theorem key_height_eq {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a) :
    (keyHeight η : ℤ) = -η.v.1 := by
  have hs : ({((0 : ℤ), (0 : ℤ))} : Diagram) ∈
      leftRibbons {((0 : ℤ), (0 : ℤ))} 1 := by
    rw [mem_leftRibbons]
    refine ⟨subset_rfl, by simp, ⟨isConnectedSkew_singleton (0, 0), ?_⟩,
      ⟨subset_rfl, fun x hx _ _ _ _ => hx⟩⟩
    simp [span, contents]
  have h := lift_height_exact hη hc (isConnectedSkew_singleton (0, 0)) (by omega) hs
  simp only [liftRibbon, Finset.singleton_biUnion, ribbonHeight, MN.numRows_translate] at h
  have hsingle : numRows ({((0 : ℤ), (0 : ℤ))} : Diagram) = 1 := by
    simp [numRows, rowSet]
  simpa only [keyHeight, ribbonHeight, hsingle, Nat.sub_self, Nat.cast_zero,
    Nat.cast_one, one_mul, zero_sub] using h

/-- The bottom key ribbon is the rotated top key ribbon of the rotated mark. -/
def bottomKeyRibbon (η : MarkedInner) : Diagram := rotate (keyRibbon η.rotate)

/-- Actual southeast key copies indexed by the removed cells of the outer diagram. -/
def bottomLift (η : MarkedInner) (D R : Diagram) : Diagram :=
  rotate (liftRibbon η.rotate (rotate D) (rotate R))

theorem copies_rotate {η : MarkedInner} (ho : η.IsOrdinary) (D : Diagram) :
    Plan.MarkedInner.copies η.rotate (rotate D) = rotate (Plan.MarkedInner.copies η D) := by
  by_cases hD : D = ∅
  · subst D; simp [rotate, Plan.MarkedInner.copies_empty]
  · have hn := Finset.nonempty_iff_ne_empty.mpr hD
    have hr : (rotate D).Nonempty := hn.image _
    have hoR : η.rotate.IsOrdinary := by
      unfold MarkedInner.IsOrdinary AttachCase.IsMixed at ho ⊢
      cases h : η.case <;> simp_all [Gluing.MarkedInner.rotate, AttachCase.rotate]
    rw [← Plan.MarkedInner.compose_eq_copies hoR hr,
      ← Plan.MarkedInner.compose_eq_copies ho hn]
    exact Gluing.MarkedInner.rotate_compose hn η

/-- The southeast correspondence on a connected component, with an injective geometric lift. -/
theorem southeast_ribbon_bijection_connected {η : MarkedInner} (hη : η.IsLegal)
    (hc : η.case = .a) {D : Diagram} (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) :
    rightRibbons (Plan.MarkedInner.copies η D) (m * η.period.toNat) =
      (rightRibbons D m).image (bottomLift η D) ∧
      Set.InjOn (bottomLift η D) (rightRibbons D m : Set Diagram) := by
  have ho : η.IsOrdinary := by simp [MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  have hηR := Gluing.MarkedInner.isLegal_rotate hη
  have hcR : η.rotate.case = .a := by
    simp [Gluing.MarkedInner.rotate, AttachCase.rotate, hc]
  obtain ⟨hleft, hinj, _⟩ := leftRibbons_copies hηR hcR (isConnectedSkew_rotate hD) hm
  rw [Gluing.MarkedInner.period_rotate, copies_rotate ho D,
    Plan.leftRibbons_rotate, Plan.leftRibbons_rotate] at hleft
  have himage := congrArg (fun S : Finset Diagram => S.image rotate) hleft
  refine ⟨?_, ?_⟩
  · simp only [Finset.image_image, Function.comp_def, rotate_rotate,
      Finset.image_id'] at himage
    apply Finset.ext
    intro R
    simpa only [Finset.mem_image, bottomLift] using
      Iff.of_eq (congrArg (fun S : Finset Diagram => R ∈ S) himage)
  · intro R hR S hS heq
    have hr : rotate R ∈ leftRibbons (rotate D) m := by
      rw [Plan.leftRibbons_rotate]
      exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
    have hs : rotate S ∈ leftRibbons (rotate D) m := by
      rw [Plan.leftRibbons_rotate]
      exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
    exact rotate_injective (hinj hr hs (rotate_injective heq))

/-- The exact integer height, not merely the parity needed for Murnaghan–Nakayama. -/
theorem southeast_height_exact_connected {η : MarkedInner} (hη : η.IsLegal)
    (hc : η.case = .a) {D R : Diagram} (hD : IsConnectedSkew D)
    {m : ℕ} (hm : 0 < m) (hR : R ∈ rightRibbons D m) :
    (ribbonHeight (bottomLift η D R) : ℤ) =
      (m : ℤ) * keyHeight η + ribbonHeight R := by
  have hcR : η.rotate.case = .a := by
    simp [Gluing.MarkedInner.rotate, AttachCase.rotate, hc]
  have hr : rotate R ∈ leftRibbons (rotate D) m := by
    rw [Plan.leftRibbons_rotate]
    exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
  have h := lift_height_exact (Gluing.MarkedInner.isLegal_rotate hη) hcR
    (isConnectedSkew_rotate hD) hm hr
  have hk := key_height_eq hη hc
  unfold bottomLift ribbonHeight at h ⊢
  simp only [Plan.MarkedInner.numRows_rotate] at h ⊢
  change _ = _ - (m : ℤ) * η.v.1 at h
  rw [hk]
  linarith

private theorem exposed_losses_downset {D R : Diagram} (hD : IsSkew D)
    (hR : IsDownsetIn D R) :
    (R.filter fun x => x + (0, 1) ∉ D).card = numRows D - numRows (D \ R) ∧
    (R.filter fun x => x + (1, 0) ∉ D).card = numCols D - numCols (D \ R) ∧
    (R.filter fun x => x + eCell ∉ D).card = span D - span (D \ R) := by
  have hrem := isSkew_sdiff_downset hD hR
  have hcard := Finset.card_sdiff_add_card_eq_card hR.1
  have h1 := card_filter_split hR (0, 1) (by simp)
  have h2 := card_filter_split hR (1, 0) (by simp)
  have h3 := card_filter_split hR eCell (by simp [eCell])
  have hr1 := card_eq_numRows_add_countE hD
  have hr2 := card_eq_numRows_add_countE hrem
  have hc1 := card_eq_numCols_add_countS hD
  have hc2 := card_eq_numCols_add_countS hrem
  have hd1 := card_eq_span_add_countSE hD
  have hd2 := card_eq_span_add_countSE hrem
  have he := Finset.card_filter_add_card_filter_not (s := R) (fun x => x + (0, 1) ∈ D)
  have hs := Finset.card_filter_add_card_filter_not (s := R) (fun x => x + (1, 0) ∈ D)
  have hse := Finset.card_filter_add_card_filter_not (s := R) (fun x => x + eCell ∈ D)
  unfold countE at hr1 hr2
  unfold countS at hc1 hc2
  unfold countSE at hd1 hd2
  exact ⟨by omega, by omega, by omega⟩

/-- Remainder product on arbitrary skew outers, with the algebraic empty value. -/
theorem northwest_ribbon_remainder {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {D R : Diagram} (hD : IsSkew D) (hR : IsDownsetIn D R) :
    cellSchur (Plan.MarkedInner.copies η D \ liftRibbon η D R) =
      cellSchur η.W ^ (numRows D - numRows (D \ R)) *
      cellSchur (hatMarkFin η) ^ (numCols D - numCols (D \ R)) *
      cellSchur (hatMiddleFin η) ^ (span D - span (D \ R)) *
      compositionValue η (D \ R) := by
  have h := cellSchur_copies_sdiff_liftRibbon hη hc hD hR
  obtain ⟨he, hs, hse⟩ := exposed_losses_downset hD hR
  rw [he, hs, hse] at h
  simpa only [compositionValue, mul_comm, mul_left_comm, mul_assoc] using h

/-- Southeast deletion leaves exactly the row, column, and diagonal loss factors. -/
theorem southeast_ribbon_remainder {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {D R : Diagram} (hD : IsSkew D) (hR : IsUpsetIn D R) :
    cellSchur (Plan.MarkedInner.copies η D \ bottomLift η D R) =
      cellSchur η.W ^ (numRows D - numRows (D \ R)) *
      cellSchur (hatMarkFin η) ^ (numCols D - numCols (D \ R)) *
      cellSchur (hatMiddleFin η) ^ (span D - span (D \ R)) *
      compositionValue η (D \ R) := by
  have ho : η.IsOrdinary := by simp [MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  have hcR : η.rotate.case = .a := by
    simp [Gluing.MarkedInner.rotate, AttachCase.rotate, hc]
  have hr := Plan.isUpsetIn_iff_rotate.mp hR
  have h := northwest_ribbon_remainder (Gluing.MarkedInner.isLegal_rotate hη) hcR
    (isSkew_rotate hD) hr
  have hF : rotate (Plan.MarkedInner.copies η D \ bottomLift η D R) =
      Plan.MarkedInner.copies η.rotate (rotate D) \
        liftRibbon η.rotate (rotate D) (rotate R) := by
    rw [Gluing.rotate_sdiff, ← copies_rotate ho D]
    simp only [bottomLift, rotate_rotate]
  have hrest : compositionValue η.rotate (rotate D \ rotate R) =
      compositionValue η (D \ R) := by
    rw [← Gluing.rotate_sdiff]
    unfold compositionValue
    rw [copies_rotate ho, cellSchur_rotate]
  rw [hrest, ← Gluing.rotate_sdiff,
    Plan.MarkedInner.cellSchur_W_rotate,
    Plan.MarkedInner.cellSchur_hatMarkFin_rotate hη.1 hη.2.2.1,
    Plan.MarkedInner.cellSchur_hatMiddleFin_rotate, Plan.MarkedInner.numRows_rotate,
    Plan.MarkedInner.numRows_rotate, Plan.MarkedInner.numCols_rotate,
    Plan.MarkedInner.numCols_rotate, span_rotate, span_rotate] at h
  rw [← cellSchur_rotate, hF]
  exact h

/-- The end caps give coordinate separation between distinct outer components. -/
theorem inner_coordinate_bounds_a {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a) :
    η.v.1 ≤ 0 ∧ 1 ≤ η.v.2 ∧
    ∀ x ∈ η.E, ∀ y ∈ η.E,
      x.1 - y.1 ≤ -2 * η.v.1 ∧ x.2 - y.2 ≤ 2 * η.v.2 - 2 := by
  obtain ⟨t, fLo, fHi, hM, _⟩ :=
    EdgeRibbon.exists_model hη hc (isConnectedSkew_singleton (0, 0))
  have hEs := isConnectedSkew_iff_diagonal.mp hη.1.1
  have hp := hη.period_pos
  have hw0 : 0 ≤ η.widthZ := by unfold Gluing.MarkedInner.widthZ; positivity
  have hwq := hη.2.2.1.2
  have hwz : η.widthZ = (η.width : ℤ) := rfl
  have hspan := span_eq_of_isConnectedSkew hη.1.1
  have hspan2 := hη.1.span_eq
  have hend : maxContent η.E = minContent η.E + η.period + η.widthZ - 1 := by
    unfold Gluing.MarkedInner.widthZ
    omega
  have hmem : ∀ a : ℤ, 0 ≤ a → a ≤ η.period + η.widthZ - 1 →
      minContent η.E + a ∈ contents η.E := by
    intro a ha hb
    exact hEs.mem_contents_iff.mpr ⟨by omega, by omega⟩
  have hstep : ∀ a b : ℤ, 0 ≤ a → a ≤ b → b ≤ η.period + η.widthZ - 1 →
      η.lo b ≤ η.lo a ∧ η.lo a ≤ η.lo b + (b - a) := by
    intro a b ha hab hb
    have h := hEs.diagLo_anti (hmem a ha (by omega)) (hmem b (by omega) hb) (by omega)
    simpa [Gluing.MarkedInner.lo] using h
  have hcap := hM.capU
  have hkey := key_height_eq hη hc
  have hv1 : η.v.1 ≤ 0 := by
    have hnonneg : (0 : ℤ) ≤ keyHeight η := by positivity
    omega
  have hdrop := hstep 0 (η.period - 1) le_rfl (by omega) (by omega)
  have hv2 : 1 ≤ η.v.2 := by
    have he : η.period = η.v.2 - η.v.1 := rfl
    have hp1 : η.rowShift = η.v.1 := rfl
    rw [hp1] at hcap
    omega
  have hends :
      η.lo 0 - η.lo (η.period + η.widthZ - 1) ≤ -2 * η.v.1 ∧
      η.lo (η.period + η.widthZ - 1) - η.lo 0 +
        (η.period + η.widthZ - 1) ≤ 2 * η.v.2 - 2 := by
    have hp1 : η.rowShift = η.v.1 := rfl
    rw [hp1] at hcap
    by_cases hw : η.widthZ = 0
    · rw [hw]
      simp only [add_zero]
      rw [hcap]
      have he : η.period = η.v.2 - η.v.1 := rfl
      constructor <;> omega
    · have hw : 0 < η.widthZ := by omega
      have ht : t < η.widthZ := by rcases hM.tw with ht | ⟨he, _⟩ <;> omega
      have hlast := hM.ge (a := η.widthZ - 1) (by omega) (by omega)
      have hflat := hM.capL hw
      have hmiddle := hstep η.widthZ (η.period - 1) (by omega) (by omega) (by omega)
      have he : η.period = η.v.2 - η.v.1 := rfl
      have hp1 : η.rowShift = η.v.1 := rfl
      rw [hp1] at hlast
      have e : η.widthZ - 1 + η.period = η.period + η.widthZ - 1 := by ring
      rw [e, hflat] at hlast
      constructor <;> omega
  have hmin := minContent_mem hEs.1
  have hmax := maxContent_mem hEs.1
  have hminEq : diagHi η.E (minContent η.E) = diagLo η.E (minContent η.E) := by
    symm
    exact hEs.2.2.2.2 _ hmin (Or.inl (fun h => by have := minContent_le h; omega))
  have hmaxEq : diagHi η.E (maxContent η.E) = diagLo η.E (maxContent η.E) := by
    symm
    exact hEs.2.2.2.2 _ hmax (Or.inr (fun h => by have := le_maxContent h; omega))
  have hb : ∀ x ∈ η.E,
      η.lo (η.period + η.widthZ - 1) ≤ x.1 ∧ x.1 ≤ η.lo 0 ∧
      η.lo 0 + minContent η.E ≤ x.2 ∧
      x.2 ≤ η.lo (η.period + η.widthZ - 1) + maxContent η.E := by
    intro x hx
    have hxC := content_mem_contents hx
    have hxlo : diagLo η.E (content x) ≤ x.1 := diagLo_le hx rfl
    have hxhi : x.1 ≤ diagHi η.E (content x) := le_diagHi hx rfl
    have hl := hEs.diagLo_anti hxC hmax (le_maxContent hxC)
    have hu := hEs.diagHi_anti hmin hxC (minContent_le hxC)
    have hll := hEs.diagLo_anti hmin hxC (minContent_le hxC)
    have huu := hEs.diagHi_anti hxC hmax (le_maxContent hxC)
    rw [hminEq] at hu
    rw [hmaxEq] at huu
    have hEnd : η.lo (η.period + η.widthZ - 1) = diagLo η.E (maxContent η.E) := by
      unfold Gluing.MarkedInner.lo
      congr 1
      omega
    have hStart : η.lo 0 = diagLo η.E (minContent η.E) := by
      simp only [Gluing.MarkedInner.lo, add_zero]
    simp only [hEnd, hStart]
    have he : content x = x.2 - x.1 := rfl
    exact ⟨by omega, by omega, by omega, by omega⟩
  refine ⟨hv1, hv2, ?_⟩
  intro x hx y hy
  have hxB := hb x hx
  have hyB := hb y hy
  exact ⟨by omega, by rw [hend] at hxB; omega⟩

/-- Distinct components remain separated in both coordinates after taking actual copies. -/
theorem copies_components_incomparable {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {D C : Diagram} (hD : IsSkew D) (hC : C ∈ edgeComponents D)
    {x y : ℤ × ℤ} (hx : x ∈ Plan.MarkedInner.copies η C)
    (hy : y ∈ Plan.MarkedInner.copies η (D \ C)) :
    (x.1 < y.1 ∧ y.2 < x.2) ∨ (y.1 < x.1 ∧ x.2 < y.2) := by
  obtain ⟨d, hd, hx⟩ := Plan.MarkedInner.mem_copies.mp hx
  obtain ⟨d', hd', hy⟩ := Plan.MarkedInner.mem_copies.mp hy
  have hdD := component_subset hC hd
  have hd'D := (Finset.mem_sdiff.mp hd').1
  have hsep := Plan.MarkedInner.two_le_content_sdiff hD hC hd hd'
  obtain ⟨hv1, hv2, hrect⟩ := inner_coordinate_bounds_a hη hc
  have hxE := mem_translate.mp hx
  have hyE := mem_translate.mp hy
  have hxy := hrect _ hxE _ hyE
  have hyx := hrect _ hyE _ hxE
  have horg : ∀ X d, η.origin X d = content d • η.v + d.1 • eCell := by
    intro X d
    simp [Gluing.MarkedInner.origin, hc]
  simp only [horg] at hxE hyE hxy hyx
  simp only [eCell, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, Int.zsmul_eq_mul, mul_one] at hxy hyx
  rcases hsep with hsep | hsep
  · have hdr : d'.1 < d.1 := by
      by_contra hn
      have hrr : d.1 ≤ d'.1 := by omega
      have hcc : d.2 ≤ d'.2 := by unfold content at hsep; omega
      exact comparable_not_mem_component hD hC hd hd' hrr hcc
    have hdc : d.2 < d'.2 := by
      by_contra hn
      have hcc : d'.2 ≤ d.2 := by omega
      have hrr : d'.1 ≤ d.1 := by unfold content at hsep; omega
      exact comparable_not_mem_component' hD hC hd' hd hrr hcc
    have hp : content d' - content d ≥ 2 := by omega
    have hm1 := mul_le_mul_of_nonpos_right hp hv1
    have hm2 := mul_le_mul_of_nonneg_right hp (by omega : 0 ≤ η.v.2 - 1)
    right
    constructor <;> unfold content at hxy hyx hsep hp hm1 hm2 <;> nlinarith
  · have hdr : d.1 < d'.1 := by
      by_contra hn
      have hrr : d'.1 ≤ d.1 := by omega
      have hcc : d'.2 ≤ d.2 := by unfold content at hsep; omega
      exact comparable_not_mem_component' hD hC hd' hd hrr hcc
    have hdc : d'.2 < d.2 := by
      by_contra hn
      have hcc : d.2 ≤ d'.2 := by omega
      have hrr : d.1 ≤ d'.1 := by unfold content at hsep; omega
      exact comparable_not_mem_component hD hC hd hd' hrr hcc
    have hp : content d - content d' ≥ 2 := by omega
    have hm1 := mul_le_mul_of_nonpos_right hp hv1
    have hm2 := mul_le_mul_of_nonneg_right hp (by omega : 0 ≤ η.v.2 - 1)
    left
    constructor <;> unfold content at hxy hyx hsep hp hm1 hm2 <;> nlinarith

private theorem skew_union_of_incomparable {A B : Diagram} (hA : IsSkew A) (hB : IsSkew B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B,
      (x.1 < y.1 ∧ y.2 < x.2) ∨ (y.1 < x.1 ∧ x.2 < y.2)) :
    IsSkew (A ∪ B) := by
  intro x hx y hy h1 h2 i hi j hj
  rcases Finset.mem_union.mp hx with hx | hx <;>
    rcases Finset.mem_union.mp hy with hy | hy
  · exact Finset.mem_union_left _ (hA x hx y hy h1 h2 i hi j hj)
  · rcases hsep x hx y hy with h | h <;> omega
  · rcases hsep y hy x hx with h | h <;> omega
  · exact Finset.mem_union_right _ (hB x hx y hy h1 h2 i hi j hj)

/-- Arbitrary skew outers, including disconnected and empty outers, produce skew copies. -/
theorem copies_skew_a {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {D : Diagram} (hD : IsSkew D) : IsSkew (Plan.MarkedInner.copies η D) := by
  classical
  have ho : η.IsOrdinary := by simp [MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  suffices h : ∀ n : ℕ, ∀ X : Diagram, X.card = n → IsSkew X →
      IsSkew (Plan.MarkedInner.copies η X) from h D.card D rfl hD
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hn hD
    by_cases he : D = ∅
    · subst D
      rw [Plan.MarkedInner.copies_empty]
      intro x hx; simp at hx
    · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr he
      let C := D.filter fun y => DiagReach D d y
      have hC : C ∈ edgeComponents D := mem_edgeComponents.mpr ⟨d, hd, rfl⟩
      have hconn := isConnectedSkew_component hD hC
      have hrest := isSkew_sdiff_component hD hC
      have hsmall : (D \ C).card < n := by
        have hcard := Finset.card_sdiff_add_card_eq_card (component_subset hC)
        have hpos := Finset.card_pos.mpr (component_nonempty hC)
        omega
      have hB := ih (D \ C).card hsmall (D \ C) rfl hrest
      have hA : IsSkew (Plan.MarkedInner.copies η C) := by
        rw [← Plan.MarkedInner.compose_eq_copies ho hconn.2.1]
        exact (hη.isConnectedSkew_compose hconn).1
      rw [← union_component_sdiff hC, Plan.MarkedInner.copies_union ho]
      exact skew_union_of_incomparable hA hB
        (fun x hx y hy => copies_components_incomparable hη hc hD hC hx hy)

/-- Ordinary origins do not depend on the ambient outer diagram. -/
theorem lift_outer_independent {η : MarkedInner} (ho : η.IsOrdinary) (D D' R : Diagram) :
    liftRibbon η D R = liftRibbon η D' R := by
  unfold liftRibbon
  refine Finset.biUnion_congr rfl fun d _ => ?_
  rw [Plan.MarkedInner.origin_ordinary ho D D']

private theorem copies_component_a {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {D C : Diagram} (hD : IsSkew D) (hC : C ∈ edgeComponents D) :
    Plan.MarkedInner.copies η C ∈ edgeComponents (Plan.MarkedInner.copies η D) ∧
    Plan.MarkedInner.copies η D \ Plan.MarkedInner.copies η C =
      Plan.MarkedInner.copies η (D \ C) := by
  classical
  have ho : η.IsOrdinary := by simp [MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  have hconn := isConnectedSkew_component hD hC
  have hcconn : IsConnectedSkew (Plan.MarkedInner.copies η C) := by
    rw [← Plan.MarkedInner.compose_eq_copies ho hconn.2.1]
    exact hη.isConnectedSkew_compose hconn
  have hsep := Plan.MarkedInner.copies_separated hη
    (fun x hx y hy => Plan.MarkedInner.two_le_content_sdiff hD hC hx hy)
  have hunion : Plan.MarkedInner.copies η D =
      Plan.MarkedInner.copies η C ∪ Plan.MarkedInner.copies η (D \ C) := by
    calc
      Plan.MarkedInner.copies η D =
          Plan.MarkedInner.copies η (C ∪ (D \ C)) :=
        congrArg (Plan.MarkedInner.copies η) (union_component_sdiff hC).symm
      _ = _ := Plan.MarkedInner.copies_union ho C (D \ C)
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hcconn.2.1
    rw [hunion, mem_edgeComponents]
    refine ⟨x, Finset.mem_union_left _ hx, ?_⟩
    rw [filter_reach_union_left hsep.nonAdjacent hx]
    ext y
    rw [Finset.mem_filter]
    exact ⟨fun hy => ⟨hy, hcconn.2.2 x hx y hy⟩, fun hy => hy.1⟩
  · rw [hunion]
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hmem, hn⟩
      rcases hmem with ha | hb
      · exact False.elim (hn ha)
      · exact hb
    · intro hb
      exact ⟨Or.inr hb, fun ha => Finset.disjoint_left.mp hsep.disjoint ha hb⟩

/-- Northwest ribbon correspondence and exact height on every skew outer. -/
theorem northwest_ribbon_bijection {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {D : Diagram} (hD : IsSkew D) {m : ℕ} (hm : 0 < m) :
    leftRibbons (Plan.MarkedInner.copies η D) (m * η.period.toNat) =
      (leftRibbons D m).image (liftRibbon η D) ∧
    Set.InjOn (liftRibbon η D) (leftRibbons D m : Set Diagram) ∧
    ∀ R ∈ leftRibbons D m, (ribbonHeight (liftRibbon η D R) : ℤ) =
      (ribbonHeight R : ℤ) - (m : ℤ) * η.v.1 := by
  classical
  have ho : η.IsOrdinary := by simp [MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  have hp := hη.period_pos
  have hN : 0 < m * η.period.toNat := Nat.mul_pos hm (by omega)
  suffices h : ∀ n : ℕ, ∀ X : Diagram, X.card = n → IsSkew X →
      leftRibbons (Plan.MarkedInner.copies η X) (m * η.period.toNat) =
        (leftRibbons X m).image (liftRibbon η X) ∧
      Set.InjOn (liftRibbon η X) (leftRibbons X m : Set Diagram) ∧
      ∀ R ∈ leftRibbons X m, (ribbonHeight (liftRibbon η X R) : ℤ) =
        (ribbonHeight R : ℤ) - (m : ℤ) * η.v.1 from h D.card D rfl hD
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hn hX
    by_cases he : X = ∅
    · subst X
      have he1 : leftRibbons (∅ : Diagram) m = ∅ :=
        leftRibbons_eq_empty_of_span_lt (by simpa [span, contents] using hm)
      have he2 : leftRibbons (∅ : Diagram) (m * η.period.toNat) = ∅ :=
        leftRibbons_eq_empty_of_span_lt (by simpa [span, contents] using hN)
      simp [Plan.MarkedInner.copies_empty, he1, he2, Set.InjOn]
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
      let C := X.filter fun y => DiagReach X x y
      have hC : C ∈ edgeComponents X := mem_edgeComponents.mpr ⟨x, hx, rfl⟩
      have hconn := isConnectedSkew_component hX hC
      have hrest := isSkew_sdiff_component hX hC
      have hsmall : (X \ C).card < n := by
        have hcard := Finset.card_sdiff_add_card_eq_card (component_subset hC)
        have hpos := Finset.card_pos.mpr (component_nonempty hC)
        omega
      obtain ⟨hAimg, hAinj, _⟩ := leftRibbons_copies hη hc hconn hm
      obtain ⟨hBimg, hBinj, hBheight⟩ := ih (X \ C).card hsmall (X \ C) rfl hrest
      have hAC : liftRibbon η C = liftRibbon η X :=
        funext (lift_outer_independent ho C X)
      have hBC : liftRibbon η (X \ C) = liftRibbon η X :=
        funext (lift_outer_independent ho (X \ C) X)
      rw [hAC] at hAimg hAinj
      rw [hBC] at hBimg hBinj hBheight
      obtain ⟨hcopC, hcopRest⟩ := copies_component_a hη hc hX hC
      have hsplit := leftRibbons_eq_union hX hC (m := m)
      have hcopSplit := leftRibbons_eq_union (copies_skew_a hη hc hX) hcopC
        (m := m * η.period.toNat)
      rw [hcopRest, hAimg, hBimg] at hcopSplit
      refine ⟨?_, ?_, ?_⟩
      · rw [hsplit, Finset.image_union]
        exact hcopSplit
      · intro R hR S hS heq
        change R ∈ leftRibbons X m at hR
        change S ∈ leftRibbons X m at hS
        rw [hsplit, Finset.mem_union] at hR hS
        have hcross : ∀ A ∈ leftRibbons C m, ∀ B ∈ leftRibbons (X \ C) m,
            liftRibbon η X A ≠ liftRibbon η X B := by
          intro A hA B hB hab
          have hLA : liftRibbon η X A ∈
              leftRibbons (Plan.MarkedInner.copies η C) (m * η.period.toNat) := by
            rw [hAimg]; exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
          have hLB : liftRibbon η X B ∈
              leftRibbons (Plan.MarkedInner.copies η (X \ C)) (m * η.period.toNat) := by
            rw [hBimg]; exact Finset.mem_image.mpr ⟨B, hB, rfl⟩
          rw [← hcopRest] at hLB
          exact Finset.disjoint_left.mp
            (disjoint_leftRibbons_component (X := Plan.MarkedInner.copies η X)
              (C := Plan.MarkedInner.copies η C) hN) hLA (hab.symm ▸ hLB)
        rcases hR with hR | hR <;> rcases hS with hS | hS
        · exact hAinj hR hS heq
        · exact False.elim (hcross R hR S hS heq)
        · exact False.elim (hcross S hS R hR heq.symm)
        · exact hBinj hR hS heq
      · intro R hR
        rw [hsplit, Finset.mem_union] at hR
        rcases hR with hR | hR
        · rw [← hAC]
          exact lift_height_exact hη hc hconn hm hR
        · exact hBheight R hR

/-- Southeast-removable ribbons on arbitrary skew outers, with the exact integer height. -/
theorem southeast_ribbon_bijection {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {D : Diagram} (hD : IsSkew D) {m : ℕ} (hm : 0 < m) :
    rightRibbons (Plan.MarkedInner.copies η D) (m * η.period.toNat) =
      (rightRibbons D m).image (bottomLift η D) ∧
    Set.InjOn (bottomLift η D) (rightRibbons D m : Set Diagram) ∧
    ∀ R ∈ rightRibbons D m, (ribbonHeight (bottomLift η D R) : ℤ) =
      (m : ℤ) * keyHeight η + ribbonHeight R := by
  have ho : η.IsOrdinary := by simp [MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  have hcR : η.rotate.case = .a := by
    simp [Gluing.MarkedInner.rotate, AttachCase.rotate, hc]
  obtain ⟨hleft, hinj, hheight⟩ := northwest_ribbon_bijection
    (Gluing.MarkedInner.isLegal_rotate hη) hcR (isSkew_rotate hD) hm
  rw [Gluing.MarkedInner.period_rotate, copies_rotate ho D,
    Plan.leftRibbons_rotate, Plan.leftRibbons_rotate] at hleft
  have himage := congrArg (fun S : Finset Diagram => S.image rotate) hleft
  refine ⟨?_, ?_, ?_⟩
  · simp only [Finset.image_image, Function.comp_def, rotate_rotate,
      Finset.image_id'] at himage
    apply Finset.ext
    intro R
    simpa only [Finset.mem_image, bottomLift] using
      Iff.of_eq (congrArg (fun S : Finset Diagram => R ∈ S) himage)
  · intro R hR S hS heq
    have hr : rotate R ∈ leftRibbons (rotate D) m := by
      rw [Plan.leftRibbons_rotate]
      exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
    have hs : rotate S ∈ leftRibbons (rotate D) m := by
      rw [Plan.leftRibbons_rotate]
      exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
    exact rotate_injective (hinj hr hs (rotate_injective heq))
  · intro R hR
    have hr : rotate R ∈ leftRibbons (rotate D) m := by
      rw [Plan.leftRibbons_rotate]
      exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
    have hh := hheight (rotate R) hr
    have hk := key_height_eq hη hc
    unfold bottomLift ribbonHeight at hh ⊢
    simp only [Plan.MarkedInner.numRows_rotate] at hh ⊢
    change _ = _ - (m : ℤ) * η.v.1 at hh
    rw [hk]
    linarith

theorem bottom_key_height {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a) :
    ribbonHeight (bottomKeyRibbon η) = keyHeight η := by
  have hcR : η.rotate.case = .a := by
    simp [Gluing.MarkedInner.rotate, AttachCase.rotate, hc]
  have hR := key_height_eq (Gluing.MarkedInner.isLegal_rotate hη) hcR
  have h := key_height_eq hη hc
  unfold bottomKeyRibbon ribbonHeight
  rw [Plan.MarkedInner.numRows_rotate]
  change keyHeight η.rotate = keyHeight η
  have hv : η.rotate.v = η.v := rfl
  rw [hv] at hR
  omega

/-- The geometric empty convention is harmless for positive-multiple ribbon sets. -/
theorem southeast_ribbon_bijection_composite {η : MarkedInner} (hη : η.IsLegal)
    (hc : η.case = .a) {D : Diagram} (hD : IsSkew D) {m : ℕ} (hm : 0 < m) :
    rightRibbons (η.compose D) (m * η.period.toNat) =
      (rightRibbons D m).image (bottomLift η D) ∧
    Set.InjOn (bottomLift η D) (rightRibbons D m : Set Diagram) ∧
    ∀ R ∈ rightRibbons D m, (ribbonHeight (bottomLift η D R) : ℤ) =
      (m : ℤ) * ribbonHeight (bottomKeyRibbon η) + ribbonHeight R := by
  have ho : η.IsOrdinary := by simp [MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  obtain ⟨himg, hinj, hheight⟩ := southeast_ribbon_bijection hη hc hD hm
  rw [← bottom_key_height hη hc] at hheight
  by_cases he : D = ∅
  · subst D
    have hr := (normalizer_no_ribbons hη hm).2.1
    have heR : rightRibbons (∅ : Diagram) m = ∅ :=
      right_ribbons_empty_of_span_lt (by simpa [span, contents] using hm)
    simp [Gluing.MarkedInner.compose, hr, heR, Set.InjOn]
  · rw [Plan.MarkedInner.compose_eq_copies ho (Finset.nonempty_iff_ne_empty.mpr he)]
    exact ⟨himg, hinj, hheight⟩

theorem southeast_ribbon_remainder_composite {η : MarkedInner} (hη : η.IsLegal)
    (hc : η.case = .a) {D R : Diagram} (hD : IsSkew D) {m : ℕ}
    (hm : 0 < m) (hR : R ∈ rightRibbons D m) :
    cellSchur (η.compose D \ bottomLift η D R) =
      cellSchur η.W ^ (numRows D - numRows (D \ R)) *
      cellSchur (hatMarkFin η) ^ (numCols D - numCols (D \ R)) *
      cellSchur (hatMiddleFin η) ^ (span D - span (D \ R)) *
      compositionValue η (D \ R) := by
  obtain ⟨hsub, hcard, _, hup⟩ := mem_rightRibbons.mp hR
  have hnR : R.Nonempty := Finset.card_pos.mp (by omega)
  have hnD : D.Nonempty := hnR.mono hsub
  have ho : η.IsOrdinary := by simp [MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  rw [Plan.MarkedInner.compose_eq_copies ho hnD]
  exact southeast_ribbon_remainder hη hc hD hup

/-- All three clauses of `lem:ribbon-deletion`, for arbitrary skew outers. -/
theorem ribbon_deletion {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {D : Diagram} (hD : IsSkew D) {m : ℕ} (hm : 0 < m) :
    (rightRibbons η.W (m * η.period.toNat) = ∅ ∧
      rightRibbons (hatMarkFin η) (m * η.period.toNat) = ∅ ∧
      rightRibbons (hatMiddleFin η) (m * η.period.toNat) = ∅) ∧
    (rightRibbons (η.compose D) (m * η.period.toNat) =
      (rightRibbons D m).image (bottomLift η D) ∧
      Set.InjOn (bottomLift η D) (rightRibbons D m : Set Diagram) ∧
      ∀ R ∈ rightRibbons D m, (ribbonHeight (bottomLift η D R) : ℤ) =
        (m : ℤ) * ribbonHeight (bottomKeyRibbon η) + ribbonHeight R) ∧
    (∀ R ∈ rightRibbons D m,
      cellSchur (η.compose D \ bottomLift η D R) =
        cellSchur η.W ^ (numRows D - numRows (D \ R)) *
        cellSchur (hatMarkFin η) ^ (numCols D - numCols (D \ R)) *
        cellSchur (hatMiddleFin η) ^ (span D - span (D \ R)) *
        compositionValue η (D \ R)) := by
  obtain ⟨_, hW, _, hB, _, hC⟩ := normalizer_no_ribbons hη hm
  exact ⟨⟨hW, hB, hC⟩, southeast_ribbon_bijection_composite hη hc hD hm,
    fun R hR => southeast_ribbon_remainder_composite hη hc hD hm hR⟩

end SkewMarkedFactor
