/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.RibbonDeletion
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Involution
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MarkFacts

/-!
# Ordinary power-sum action

«Marked composition and the power-sum action», «Ribbon deletion» (`sec:action`,
`lem:action`, `eq:modified`).  The map is defined on the actual free shape space;
translation invariance is a theorem about its values, not an identification of basis vectors.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan Gluing.Plan.KernelAux Gluing.Plan.MarkFacts MvPolynomial

/-- The Schur function of the southwest mark, used for row normalization. -/
noncomputable def normalizerRow (η : MarkedInner) : Lambda := cellSchur η.W
/-- The Schur function of the reduced mark, used for column normalization. -/
noncomputable def normalizerColumn (η : MarkedInner) : Lambda := cellSchur (hatMarkFin η)
/-- The Schur function of the reduced middle, used for diagonal normalization. -/
noncomputable def normalizerDiagonal (η : MarkedInner) : Lambda := cellSchur (hatMiddleFin η)
private theorem normalizer_row_of_empty {η : MarkedInner} (hW : η.W = ∅) :
    normalizerRow η = 1 := by
  rw [normalizerRow, hW, cellSchur_empty]

private theorem normalizer_column_of_empty {η : MarkedInner} (hW : η.W = ∅) :
    normalizerColumn η = 1 := by
  rw [normalizerColumn, EsDiff.hatMarkFin_empty hW, cellSchur_empty]

private theorem normalizers_empty_edges (E : Diagram) :
    normalizerRow (emptyMarkV E) = normalizerRow (emptyMarkH E) ∧
    normalizerColumn (emptyMarkV E) = normalizerColumn (emptyMarkH E) ∧
    normalizerDiagonal (emptyMarkV E) = normalizerDiagonal (emptyMarkH E) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [normalizer_row_of_empty rfl, normalizer_row_of_empty rfl]
  · rw [normalizer_column_of_empty rfl, normalizer_column_of_empty rfl]
  · unfold normalizerDiagonal hatMiddleFin
    rw [EsDiff.middle_empty (ω := emptyMarkV E) rfl,
      EsDiff.middle_empty (ω := emptyMarkH E) rfl]
    rfl


open Classical in
/-- The full ordinary domain includes the vertical empty-edge reading. -/
noncomputable def modifiedValue (η : MarkedInner) (D : Diagram) : Lambda :=
  if η.W = ∅ ∧ η.case = .b then modComp (emptyMarkH η.E) (antitranspose D)
  else modComp η D
private theorem modified_vertical_empty (E D : Diagram) :
    modifiedValue (emptyMarkV E) D = modComp (emptyMarkH E) (antitranspose D) := by
  classical
  exact ite_eq_left (show (emptyMarkV E).W = ∅ ∧ (emptyMarkV E).case = .b from ⟨rfl, rfl⟩)


/-- The linear extension of modified composition to literal finite cell sets. -/
noncomputable def modifiedMap (η : MarkedInner) : ShapeSpace →ₗ[ℚ] Lambda :=
  Finsupp.linearCombination ℚ (modifiedValue η)

/-- The factor is the actual power-sum derivative, not an assumed multiplier. -/
noncomputable def xi (η : MarkedInner) : Lambda := pDeriv η.period.toNat (cellSchur η.E)

/-- The extra outer sign for vertical attachment. -/
noncomputable def ordinarySign (η : MarkedInner) (m : ℕ) : Lambda :=
  if η.case = .b then (-1) ^ (m - 1) else 1

@[simp] theorem modified_map_shape (η : MarkedInner) (D : Diagram) :
    modifiedMap η (shape D) = modifiedValue η D := by
  simp [modifiedMap, shape, Finsupp.linearCombination_single]

@[simp] theorem modified_empty (η : MarkedInner) : modifiedValue η ∅ = 1 := by
  classical
  unfold modifiedValue
  split_ifs <;> simp [modComp_empty, antitranspose]

/-- The modified linear map sends the empty shape to the unit. -/
theorem modified_map_empty (η : MarkedInner) : modifiedMap η (shape ∅) = 1 := by
  rw [modified_map_shape, modified_empty]

theorem modified_translate (η : MarkedInner) (t : ℤ × ℤ) (D : Diagram) :
    modifiedValue η (translate t D) = modifiedValue η D := by
  classical
  unfold modifiedValue
  split_ifs
  · rw [antitranspose_translate, modComp_translate]
  · exact modComp_translate η t D

private theorem mod_comp_singleton {η : MarkedInner} (ho : η.IsOrdinary) (x : ℤ × ℤ) :
    modComp η {x} = cellSchur η.E := by
  classical
  rw [modComp_connected_eq_tFun ho (isConnectedSkew_singleton x)]
  have hE : countE ({x} : Diagram) = 0 := by
    simp [countE, Finset.filter_singleton, Prod.ext_iff]
  have hS : countS ({x} : Diagram) = 0 := by
    simp [countS, Finset.filter_singleton, Prod.ext_iff]
  have hSE : countSE ({x} : Diagram) = 0 := by
    simp [countSE, Finset.filter_singleton, Prod.ext_iff, eCell]
  simp [tFun, hE, hS, hSE, Plan.MarkedInner.copies, cellSchur_translate]

/-- Every singleton has the inner Schur value after applying the map. -/
theorem modified_singleton {η : MarkedInner} (ho : η.IsOrdinary) (x : ℤ × ℤ) :
    modifiedValue η {x} = cellSchur η.E := by
  classical
  unfold modifiedValue
  split_ifs
  · have hh : (emptyMarkH η.E).IsOrdinary := by simp [MarkedInner.IsOrdinary, emptyMarkH,
      AttachCase.IsMixed]
    simpa only [antitranspose, Finset.image_singleton, atVec, emptyMarkH] using
      mod_comp_singleton hh (atVec x)
  · exact mod_comp_singleton ho x

theorem modified_map_singleton {η : MarkedInner} (ho : η.IsOrdinary) (x : ℤ × ℤ) :
    modifiedMap η (shape {x}) = cellSchur η.E := by
  rw [modified_map_shape, modified_singleton ho]

private theorem legal_not_vertical_empty {η : MarkedInner} (hη : η.IsLegal) :
    ¬ (η.W = ∅ ∧ η.case = .b) := by
  rintro ⟨hw, hc⟩
  exact (Gluing.MarkedInner.W_nonempty_of_case_b hη hc).ne_empty hw

theorem modified_eq_mod_comp {η : MarkedInner} (hη : η.IsLegal) (D : Diagram) :
    modifiedValue η D = modComp η D := by
  classical
  simp only [modifiedValue, ite_eq_right (legal_not_vertical_empty hη)]

@[simp] theorem empty_period_eq (E : Diagram) :
    (emptyMarkV E).period = (emptyMarkH E).period := by
  simp only [emptyMarkV, emptyMarkH, MarkedInner.period, vH, vV, content,
    Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

@[simp] theorem xi_empty_edges (E : Diagram) : xi (emptyMarkV E) = xi (emptyMarkH E) := by
  unfold xi
  rw [empty_period_eq]
  rfl

/-- The normalization is a product of actual diagram Schur functions. -/
noncomputable def normalizationFactor (η : MarkedInner) (D : Diagram) : Lambda :=
  normalizerRow η ^ (D.card - numRows D) *
    normalizerColumn η ^ (D.card - numCols D) *
    normalizerDiagonal η ^ (D.card - span D)

/-- The empty-edge gauge acts on the outer diagram, not on the inner function. -/
theorem empty_vertical_copies_gauge (E D : Diagram) :
    Plan.MarkedInner.copies (emptyMarkV E) D =
      Plan.MarkedInner.copies (emptyMarkH E) (antitranspose D) := by
  by_cases hD : D = ∅
  · subst D
    simp [Plan.MarkedInner.copies_empty, antitranspose]
  · have hn := Finset.nonempty_iff_ne_empty.mpr hD
    have hat := antitranspose_nonempty_iff.mpr hn
    have h := compose_emptyMarks_antitranspose hat E
    rw [antitranspose_antitranspose] at h
    have hoH : (emptyMarkH E).IsOrdinary := by
      simp [MarkedInner.IsOrdinary, emptyMarkH, AttachCase.IsMixed]
    have hoV : (emptyMarkV E).IsOrdinary := by
      simp [MarkedInner.IsOrdinary, emptyMarkV, AttachCase.IsMixed]
    rw [Plan.MarkedInner.compose_eq_copies hoH hat,
      Plan.MarkedInner.compose_eq_copies hoV hn] at h
    exact h.symm

/-- The modified map has the paper's normalization on every skew outer, including empty. -/
theorem modified_normalization {η : MarkedInner} (hη : η.IsReadoutLegal)
    (ho : η.IsOrdinary) {D : Diagram} (hD : IsSkew D) :
    modifiedValue η D = normalizationFactor η D * compositionValue η D := by
  rcases hη with hη | ⟨hE, he⟩
  · rw [modified_eq_mod_comp hη,
      modComp_eq_tFun hη ho D.card D rfl hD]
    have hr := card_eq_numRows_add_countE hD
    have hc := card_eq_numCols_add_countS hD
    have hd := card_eq_span_add_countSE hD
    have er : D.card - numRows D = countE D := by omega
    have ec : D.card - numCols D = countS D := by omega
    have ed : D.card - span D = countSE D := by omega
    simp only [normalizationFactor, normalizerRow, normalizerColumn, normalizerDiagonal,
      er, ec, ed, compositionValue, tFun]
  · have hH := emptyMarkH_isLegal hE
    have hoH : (emptyMarkH η.E).IsOrdinary := by
      simp [MarkedInner.IsOrdinary, emptyMarkH, AttachCase.IsMixed]
    have hAT := isSkew_antitranspose hD
    have hd := card_eq_span_add_countSE hAT
    have hs : span (antitranspose D) = span D := by
      unfold span; rw [contents_antitranspose]
    have ed : countSE (antitranspose D) = D.card - span D := by
      rw [card_antitranspose, hs] at hd
      omega
    have hcop := empty_vertical_copies_gauge η.E D
    rw [he]
    rw [modified_vertical_empty]
    rw [modComp_eq_tFun hH hoH (antitranspose D).card (antitranspose D) rfl hAT]
    change normalizerRow (emptyMarkH η.E) ^ countE (antitranspose D) *
      normalizerColumn (emptyMarkH η.E) ^ countS (antitranspose D) *
      normalizerDiagonal (emptyMarkH η.E) ^ countSE (antitranspose D) *
      compositionValue (emptyMarkH η.E) (antitranspose D) =
      normalizerRow (emptyMarkV η.E) ^ (D.card - numRows D) *
      normalizerColumn (emptyMarkV η.E) ^ (D.card - numCols D) *
      normalizerDiagonal (emptyMarkV η.E) ^ (D.card - span D) *
      compositionValue (emptyMarkV η.E) D
    rw [normalizer_row_of_empty (η := emptyMarkH η.E) rfl,
      normalizer_row_of_empty (η := emptyMarkV η.E) rfl,
      normalizer_column_of_empty (η := emptyMarkH η.E) rfl,
      normalizer_column_of_empty (η := emptyMarkV η.E) rfl,
      (normalizers_empty_edges η.E).2.2, ed]
    simp only [one_pow, one_mul, compositionValue, hcop]

theorem modified_normalization_nonempty {η : MarkedInner} (hη : η.IsReadoutLegal)
    (ho : η.IsOrdinary) {D : Diagram} (hD : IsSkew D) (hn : D.Nonempty) :
    modifiedValue η D = normalizationFactor η D * cellSchur (η.compose D) := by
  rw [modified_normalization hη ho hD, composition_value_nonempty ho hn]

private theorem ribbon_sum_singleton (F : Diagram → Lambda) (x : ℤ × ℤ) :
    ribbonSumRight F {x} 1 = F ∅ := by
  have hr : rightRibbons ({x} : Diagram) 1 = {{x}} := by
    ext R
    rw [Finset.mem_singleton, mem_rightRibbons]
    constructor
    · rintro ⟨hsub, hcard, _, _⟩
      exact Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
    · rintro rfl
      refine ⟨subset_rfl, by simp, ⟨isConnectedSkew_singleton x, ?_⟩, ?_⟩
      · simp [span, contents]
      · exact ⟨subset_rfl, fun y hy _ _ _ _ => hy⟩
  rw [ribbonSumRight, hr, Finset.sum_singleton]
  simp [ribbonSign, ribbonHeight, numRows, rowSet]

private theorem cases_ordinary {η : MarkedInner} (ho : η.IsOrdinary) :
    η.case = .a ∨ η.case = .b := by
  unfold MarkedInner.IsOrdinary AttachCase.IsMixed at ho
  cases h : η.case <;> simp_all

private theorem edge_compat_ordinary {η : MarkedInner} (hη : η.IsLegal) (ho : η.IsOrdinary) :
    EdgeCompat η := by
  rcases cases_ordinary ho with ha | hb
  · exact edgeCompat_a hη ha
  · exact edgeCompat_b hη hb

/-- The one-cell calculation identifies the actual derivative with the geometric product. -/
theorem xi_factor_legal {η : MarkedInner} (hη : η.IsLegal) (ho : η.IsOrdinary) :
    xi η = (edgeSign η 1 : Lambda) * hatFactor η := by
  have h := (edge_compat_ordinary hη ho {((0 : ℤ), (0 : ℤ))}
    (isConnectedSkew_singleton (0, 0)).1 1 (by omega)).2
  rw [mod_comp_singleton ho, ribbon_sum_singleton, modComp_empty] at h
  simpa only [one_mul, pow_one, mul_one, xi] using h

/-- The two empty-edge readings have the same one-cell sign. -/
theorem edge_sign_empty_edges (E : Diagram) :
    edgeSign (emptyMarkV E) 1 = edgeSign (emptyMarkH E) 1 := by
  have hv : (vH E).1 = (vV E).1 + 1 := by
    have h := congrArg Prod.fst (vH_eq_vV_add_eCell E)
    simpa [eCell] using h
  have hpar : ((vH E).1.natAbs + (vV E).1.natAbs) % 2 = 1 := by omega
  have hprod : (-1 : ℤ) ^ (vH E).1.natAbs * (-1) ^ (vV E).1.natAbs = -1 := by
    rw [← pow_add, neg_one_pow_eq_pow_mod_two, hpar]
    simp
  have hsq : (-1 : ℤ) ^ (vV E).1.natAbs * (-1) ^ (vV E).1.natAbs = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  simp only [edgeSign, emptyMarkH, emptyMarkV, one_mul]
  linear_combination -((-1 : ℤ) ^ (vV E).1.natAbs) * hprod +
    ((-1 : ℤ) ^ (vH E).1.natAbs) * hsq

theorem hat_factor_empty_edges (E : Diagram) :
    hatFactor (emptyMarkV E) = hatFactor (emptyMarkH E) := by
  change normalizerRow (emptyMarkV E) * normalizerColumn (emptyMarkV E) *
      normalizerDiagonal (emptyMarkV E) =
    normalizerRow (emptyMarkH E) * normalizerColumn (emptyMarkH E) *
      normalizerDiagonal (emptyMarkH E)
  rw [(normalizers_empty_edges E).1, (normalizers_empty_edges E).2.1,
    (normalizers_empty_edges E).2.2]

/-- The actual one-cell derivative is the signed normalizer product on the full domain. -/
theorem xi_factor {η : MarkedInner} (hη : η.IsReadoutLegal) (ho : η.IsOrdinary) :
    xi η = (edgeSign η 1 : Lambda) * hatFactor η := by
  rcases hη with hη | ⟨hE, he⟩
  · exact xi_factor_legal hη ho
  · have hH := emptyMarkH_isLegal hE
    have hoH : (emptyMarkH η.E).IsOrdinary := by
      simp [MarkedInner.IsOrdinary, emptyMarkH, AttachCase.IsMixed]
    have h := xi_factor_legal hH hoH
    rw [he, xi_empty_edges, edge_sign_empty_edges, hat_factor_empty_edges]
    exact h

theorem xi_factor_normalizers {η : MarkedInner} (hη : η.IsReadoutLegal)
    (ho : η.IsOrdinary) :
    xi η = (edgeSign η 1 : Lambda) * normalizerRow η *
      normalizerColumn η * normalizerDiagonal η := by
  rw [xi_factor hη ho]
  simp only [hatFactor, normalizerRow, normalizerColumn, normalizerDiagonal, mul_assoc]

private theorem edge_sign_factor {η : MarkedInner} (ho : η.IsOrdinary) {m : ℕ} (hm : 0 < m) :
    (edgeSign η m : Lambda) = ordinarySign η m * (edgeSign η 1 : Lambda) ^ m := by
  rcases cases_ordinary ho with ha | hb
  · simp [edgeSign, ordinarySign, ha, ← pow_mul, Nat.mul_comm]
  · have he : -( (-1 : ℤ) ^ (m * η.v.1.natAbs)) =
        (-1 : ℤ) ^ (m - 1) * (-((-1 : ℤ) ^ η.v.1.natAbs)) ^ m := by
      have hs : (-1 : ℤ) ^ (m - 1 + m) = -1 := by
        rw [neg_one_pow_eq_pow_mod_two]
        have : (m - 1 + m) % 2 = 1 := by omega
        simp [this]
      have hneg : (-((-1 : ℤ) ^ η.v.1.natAbs)) ^ m =
          (-1 : ℤ) ^ m * ((-1 : ℤ) ^ η.v.1.natAbs) ^ m := by
        conv_lhs => rw [neg_eq_neg_one_mul, mul_pow]
      rw [hneg, ← pow_mul, Nat.mul_comm η.v.1.natAbs m,
        ← mul_assoc, ← pow_add, hs]
      ring
    simp only [edgeSign, hb, ordinarySign, ↓reduceIte, one_mul]
    exact_mod_cast he

/-- No compatibility certificate occurs in the ordinary chart action. -/
theorem ordinary_action_legal {η : MarkedInner} (hη : η.IsLegal) (ho : η.IsOrdinary)
    {D : Diagram} (hD : IsSkew D) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * η.period.toNat) (modifiedValue η D) =
      ordinarySign η m * xi η ^ m * ribbonSumRight (modifiedValue η) D m := by
  have hf : modifiedValue η = modComp η := funext (modified_eq_mod_comp hη)
  rw [hf]
  have h := (edge_compat_ordinary hη ho D hD m hm).2
  rw [edge_sign_factor ho hm] at h
  rw [xi_factor_legal hη ho, mul_pow]
  simpa only [mul_assoc] using h

private theorem empty_vertical_action {E D : Diagram} (hE : IsConnectedSkew E)
    (hD : IsSkew D) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * (emptyMarkV E).period.toNat) (modifiedValue (emptyMarkV E) D) =
      ordinarySign (emptyMarkV E) m * xi (emptyMarkV E) ^ m *
        ribbonSumRight (modifiedValue (emptyMarkV E)) D m := by
  have hh := emptyMarkH_isLegal hE
  have ho : (emptyMarkH E).IsOrdinary := by
    simp [MarkedInner.IsOrdinary, emptyMarkH, AttachCase.IsMixed]
  have h := (edgeCompat_a hh rfl (antitranspose D) (isSkew_antitranspose hD) m hm).1
  rw [ribbon_sum_antitranspose (modComp (emptyMarkH E)) D m] at h
  have hxi := xi_factor_legal hh ho
  have hs := edge_sign_factor ho hm
  rw [hs] at h
  have hsign : ordinarySign (emptyMarkH E) m = 1 := by
    simp only [ordinarySign]
    exact ite_eq_right (by simp [emptyMarkH])
  rw [hsign] at h
  simp only [one_mul] at h
  rw [← mul_pow, ← hxi] at h
  have hf : modifiedValue (emptyMarkV E) =
      fun X => modComp (emptyMarkH E) (antitranspose X) :=
    funext (modified_vertical_empty E)
  rw [empty_period_eq, xi_empty_edges, hf]
  have hvsign : ordinarySign (emptyMarkV E) m = (-1 : Lambda) ^ (m - 1) := by
    simp only [ordinarySign]
    exact ite_eq_left rfl
  rw [hvsign]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem ordinary_action {η : MarkedInner} (hη : η.IsReadoutLegal) (ho : η.IsOrdinary)
    {D : Diagram} (hD : IsSkew D) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * η.period.toNat) (modifiedValue η D) =
      ordinarySign η m * xi η ^ m * ribbonSumRight (modifiedValue η) D m := by
  rcases hη with hη | ⟨hE, he⟩
  · exact ordinary_action_legal hη ho hD hm
  · have h := empty_vertical_action hE hD hm
    simpa only [← he] using h

/-- Nonvanishing is discharged from the actual hatted diagrams. -/
theorem xi_ne_zero {η : MarkedInner} (hη : η.IsReadoutLegal) (ho : η.IsOrdinary) : xi η ≠ 0 := by
  rcases hη with hη | ⟨hE, he⟩
  · rw [xi_factor_legal hη ho]
    apply mul_ne_zero _ (hatFactor_ne_zero hη)
    rcases cases_ordinary ho with hcase | hcase <;> simp [edgeSign, hcase]
  · have hH := emptyMarkH_isLegal hE
    have hoH : (emptyMarkH η.E).IsOrdinary := by
      simp [MarkedInner.IsOrdinary, emptyMarkH, AttachCase.IsMixed]
    have h : xi (emptyMarkH η.E) ≠ 0 := by
      rw [xi_factor_legal hH hoH]
      exact mul_ne_zero (by simp [edgeSign, emptyMarkH]) (hatFactor_ne_zero hH)
    have hp : η.period = (emptyMarkH η.E).period := by rw [he, empty_period_eq]; rfl
    unfold xi at h ⊢
    rw [hp]
    exact h

/-- All period-multiple directions annihilate the three normalization factors. -/
theorem normalizers_killed {η : MarkedInner} (hη : η.IsReadoutLegal) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * η.period.toNat) (normalizerRow η) = 0 ∧
    pDeriv (m * η.period.toNat) (normalizerColumn η) = 0 ∧
    pDeriv (m * η.period.toNat) (normalizerDiagonal η) = 0 := by
  rcases hη with hη | ⟨hE, he⟩
  · exact pDeriv_cellSchur_hat_aux hη hm
  · have h := pDeriv_cellSchur_hat_aux (emptyMarkH_isLegal hE) hm
    rw [he, empty_period_eq]
    change pDeriv (m * (emptyMarkH η.E).period.toNat) (normalizerRow (emptyMarkH η.E)) = 0 ∧
      pDeriv (m * (emptyMarkH η.E).period.toNat) (normalizerColumn (emptyMarkH η.E)) = 0 ∧
      pDeriv (m * (emptyMarkH η.E).period.toNat) (normalizerDiagonal (emptyMarkH η.E)) = 0 at h
    rw [(normalizers_empty_edges η.E).1, (normalizers_empty_edges η.E).2.1,
      (normalizers_empty_edges η.E).2.2]
    exact h

theorem xi_killed {η : MarkedInner} (hη : η.IsReadoutLegal) (ho : η.IsOrdinary)
    {m : ℕ} (hm : 0 < m) : pDeriv (m * η.period.toNat) (xi η) = 0 := by
  rcases hη with hη | ⟨hE, he⟩
  · rw [xi_factor_legal hη ho]
    rcases cases_ordinary ho with hcase | hcase <;>
      simp [edgeSign, hcase, Derivation.leibniz,
        pDeriv_hatFactor hη (cases_ordinary ho) hm]
  · have hh := emptyMarkH_isLegal hE
    have hoH : (emptyMarkH η.E).IsOrdinary := by
      simp [MarkedInner.IsOrdinary, emptyMarkH, AttachCase.IsMixed]
    have h : pDeriv (m * (emptyMarkH η.E).period.toNat) (xi (emptyMarkH η.E)) = 0 := by
      rw [xi_factor_legal hh hoH]
      apply derivation_eq_zero_mul
      · simp [edgeSign, emptyMarkH]
      · exact pDeriv_hatFactor hh (Or.inl rfl) hm
    have hp : η.period = (emptyMarkH η.E).period := by rw [he, empty_period_eq]; rfl
    unfold xi at h ⊢
    simpa only [hp, emptyMarkH] using h

/-- Homogeneity of the actual derivative follows term by term from ribbon deletion. -/
theorem xi_homogeneous {η : MarkedInner} (hη : η.IsReadoutLegal) :
    IsWeightedHomogeneous degWeight (xi η) (η.E.card - η.period.toNat) := by
  have hE : IsConnectedSkew η.E := by
    rcases hη with h | ⟨h, _⟩
    · exact h.1.1
    · exact h
  have hp : 0 < η.period.toNat := by
    rcases hη with h | ⟨h, he⟩
    · have := h.period_pos; omega
    · rw [he, empty_period_eq]
      have hh := (emptyMarkH_isLegal h).period_pos
      omega
  rw [xi, pDeriv_cellSchur_right hE.1 hp, ribbonSumRight]
  refine IsWeightedHomogeneous.sum _ _ _ fun R hR => ?_
  obtain ⟨hsub, hcard, _, _⟩ := mem_rightRibbons.mp hR
  have hweight := isWeightedHomogeneous_cellSchur (isSkew_sdiff_of_mem_rightRibbons hE.1 hR)
  rw [Finset.card_sdiff_of_subset hsub, hcard] at hweight
  have hscalar := isWeightedHomogeneous_C degWeight (ribbonSign R : ℚ)
  simpa using hscalar.mul hweight

theorem normalization_killed {η : MarkedInner} (hη : η.IsReadoutLegal)
    (D : Diagram) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * η.period.toNat) (normalizationFactor η D) = 0 := by
  obtain ⟨hr, hc, hd⟩ := normalizers_killed hη hm
  unfold normalizationFactor
  exact derivation_eq_zero_mul
    (derivation_eq_zero_mul (derivation_eq_zero_pow hr _) (derivation_eq_zero_pow hc _))
    (derivation_eq_zero_pow hd _)

/-- Each actual normalization function is nonzero throughout the full readout domain. -/
theorem normalizers_ne_zero {η : MarkedInner} (hη : η.IsReadoutLegal) :
    normalizerRow η ≠ 0 ∧ normalizerColumn η ≠ 0 ∧ normalizerDiagonal η ≠ 0 := by
  rcases hη with hη | ⟨hE, he⟩
  · exact ⟨cellSchur_ne_zero hη.isSkew_W,
      cellSchur_ne_zero hη.isSkew_hatMarkFin, cellSchur_ne_zero hη.isSkew_hatMiddleFin⟩
  · have hh := emptyMarkH_isLegal hE
    have h : normalizerRow (emptyMarkH η.E) ≠ 0 ∧
        normalizerColumn (emptyMarkH η.E) ≠ 0 ∧
        normalizerDiagonal (emptyMarkH η.E) ≠ 0 :=
      ⟨cellSchur_ne_zero hh.isSkew_W,
      cellSchur_ne_zero hh.isSkew_hatMarkFin, cellSchur_ne_zero hh.isSkew_hatMiddleFin⟩
    rw [he, (normalizers_empty_edges η.E).1, (normalizers_empty_edges η.E).2.1,
      (normalizers_empty_edges η.E).2.2]
    exact h

theorem normalization_ne_zero {η : MarkedInner} (hη : η.IsReadoutLegal) (D : Diagram) :
    normalizationFactor η D ≠ 0 := by
  have hn := normalizers_ne_zero hη
  unfold normalizationFactor
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn.1) (pow_ne_zero _ hn.2.1))
    (pow_ne_zero _ hn.2.2)


/-- The action on arbitrary skew-supported formal combinations. -/
theorem ordinary_shape_action {η : MarkedInner} (hη : η.IsReadoutLegal) (ho : η.IsOrdinary)
    {h : ShapeSpace} (hh : h ∈ skewSupportedSpace) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * η.period.toNat) (modifiedMap η h) =
      ordinarySign η m * xi η ^ m * modifiedMap η (rightOp m h) := by
  refine skewSupportedSpace_induction (P := fun h =>
    pDeriv (m * η.period.toNat) (modifiedMap η h) =
      ordinarySign η m * xi η ^ m * modifiedMap η (rightOp m h))
    (by simp) (fun a b ha hb => by simp only [map_add, ha, hb]; ring)
    (fun q a ha => by
      simp only [map_smul, Derivation.map_smul]
      change q • pDeriv (m * η.period.toNat) (modifiedMap η a) =
        ordinarySign η m * xi η ^ m * (q • modifiedMap η (rightOp m a))
      rw [ha]
      simp only [Algebra.smul_def]
      ring) ?_ hh
  intro D hD
  rw [modified_map_shape, ordinary_action hη ho hD hm, rightOp_shape, map_sum]
  congr 1
  unfold ribbonSumRight
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [map_smul, modified_map_shape, smul_int_eq]

/-- Southeast deletion, with the head of the word acting first. -/
noncomputable def removalWord : List ℕ → ShapeSpace →ₗ[ℚ] ShapeSpace
  | [] => LinearMap.id
  | m :: ν => (removalWord ν).comp (rightOp m)

private theorem removal_word_supported (ν : List ℕ) {h : ShapeSpace}
    (hh : h ∈ skewSupportedSpace) : removalWord ν h ∈ skewSupportedSpace := by
  induction ν generalizing h with
  | nil => exact hh
  | cons m ν ih => exact ih (rightOp_mem_skewSupportedSpace hh m)

private theorem p_deriv_word_mul {ν : List ℕ} {a : Lambda}
    (ha : ∀ n ∈ ν, pDeriv n a = 0) (b : Lambda) :
    pDerivWord ν (a * b) = a * pDerivWord ν b := by
  induction ν generalizing b with
  | nil => rfl
  | cons n ν ih =>
    change pDerivWord ν (pDeriv n (a * b)) = a * pDerivWord ν (pDeriv n b)
    rw [Derivation.leibniz, ha n (List.mem_cons_self)]
    simp only [mul_zero, add_zero, smul_eq_mul]
    exact ih (fun k hk => ha k (List.mem_cons_of_mem n hk)) _

/-- Positive parts give the nonnegative vertical word exponent, including the empty word. -/
theorem word_length_le_sum {ν : List ℕ} (hν : ∀ m ∈ ν, 0 < m) : ν.length ≤ ν.sum := by
  induction ν with
  | nil => simp
  | cons m ν ih =>
    have hm := hν m (List.mem_cons_self)
    have htail := ih (fun n hn => hν n (List.mem_cons_of_mem m hn))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Iterated action on the genuine modified shape map. -/
theorem ordinary_word_action {η : MarkedInner} (hη : η.IsReadoutLegal) (ho : η.IsOrdinary)
    {ν : List ℕ} (hν : ∀ m ∈ ν, 0 < m) {h : ShapeSpace}
    (hh : h ∈ skewSupportedSpace) :
    pDerivWord (ν.map (fun m => m * η.period.toNat)) (modifiedMap η h) =
      (if η.case = .b then (-1 : Lambda) ^ (ν.sum - ν.length) else 1) *
        xi η ^ ν.sum * modifiedMap η (removalWord ν h) := by
  induction ν generalizing h with
  | nil => simp [pDerivWord, removalWord]
  | cons m ν ih =>
    have hm := hν m (List.mem_cons_self)
    have htail : ∀ n ∈ ν, 0 < n := fun n hn => hν n (List.mem_cons_of_mem m hn)
    have hlen := word_length_le_sum htail
    have hconst : ∀ n ∈ ν.map (fun n => n * η.period.toNat),
        pDeriv n (ordinarySign η m * xi η ^ m) = 0 := by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
      have hkill := xi_killed hη ho (htail k hk)
      have hsign : pDeriv (k * η.period.toNat) (ordinarySign η m) = 0 := by
        unfold ordinarySign
        split_ifs <;> simp
      exact derivation_eq_zero_mul hsign (derivation_eq_zero_pow hkill m)
    simp only [List.map_cons, pDerivWord, LinearMap.comp_apply]
    change pDerivWord (ν.map (fun n => n * η.period.toNat))
      (pDeriv (m * η.period.toNat) (modifiedMap η h)) = _
    rw [ordinary_shape_action hη ho hh hm,
      p_deriv_word_mul hconst, ih htail (rightOp_mem_skewSupportedSpace hh m)]
    simp only [List.sum_cons, List.length_cons, removalWord, LinearMap.comp_apply]
    unfold ordinarySign
    by_cases hb : η.case = .b
    · simp only [hb, ↓reduceIte]
      have he : m - 1 + (ν.sum - ν.length) = m + ν.sum - (ν.length + 1) := by omega
      rw [← he, pow_add, pow_add]
      ring
    · simp only [hb, ↓reduceIte, one_mul]
      rw [pow_add]
      ring

/-- The horizontal version has exactly the multiplier `xi^m`. -/
theorem horizontal_action {η : MarkedInner} (hη : η.IsReadoutLegal) (hc : η.case = .a)
    {D : Diagram} (hD : IsSkew D) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * η.period.toNat) (modifiedValue η D) =
      xi η ^ m * ribbonSumRight (modifiedValue η) D m := by
  have ho : η.IsOrdinary := by simp [MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  simpa [ordinarySign, hc] using ordinary_action hη ho hD hm

/-- The vertical version retains the outer sign, including the empty vertical edge. -/
theorem vertical_action {η : MarkedInner} (hη : η.IsReadoutLegal) (hc : η.case = .b)
    {D : Diagram} (hD : IsSkew D) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * η.period.toNat) (modifiedValue η D) =
      (-1 : Lambda) ^ (m - 1) * xi η ^ m * ribbonSumRight (modifiedValue η) D m := by
  have ho : η.IsOrdinary := by simp [MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  simpa [ordinarySign, hc] using ordinary_action hη ho hD hm

theorem ordinary_chart_action {χ : Chart} (hχ : χ.IsProperOrdinary) {m : ℕ} (hm : 0 < m) :
    pDeriv (m * χ.ω.period.toNat) (modifiedValue χ.ω χ.D) =
      ordinarySign χ.ω m * xi χ.ω ^ m * ribbonSumRight (modifiedValue χ.ω) χ.D m :=
  ordinary_action hχ.1.2.2.2 hχ.2 hχ.1.1.1 hm

/-- Public word action directly on an actual skew diagram. -/
theorem ordinary_diagram_word_action {η : MarkedInner} (hη : η.IsReadoutLegal)
    (ho : η.IsOrdinary) {D : Diagram} (hD : IsSkew D) {ν : List ℕ}
    (hν : ∀ m ∈ ν, 0 < m) :
    pDerivWord (ν.map (fun m => m * η.period.toNat)) (modifiedValue η D) =
      (if η.case = .b then (-1 : Lambda) ^ (ν.sum - ν.length) else 1) *
        xi η ^ ν.sum * modifiedMap η (removalWord ν (shape D)) := by
  simpa only [modified_map_shape] using
    ordinary_word_action hη ho hν (shape_mem_skewSupportedSpace hD)

end SkewMarkedFactor
