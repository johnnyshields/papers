/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.PeriodTests
import SkewCornerDescent.Matrix.PrimeOrder
import SkewGluing.ComponentOrders
import SkewGluing.ProfileDiscrete

/-!
# Equal-inner discrete residuals

Formalizes `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `lem:alpha-row-candidate`).
The arguments use equal parent cofactors and inner functions; source-minimality
and parent-function equality are not hypotheses.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
variable {ω η : MarkedInner}
open SkewCornerDescent.Matrix

/-- A discrete interior has one component per interior cell. -/
theorem interior_card_eq_component_card {D : Diagram} (hd : HasDiscreteInterior D) :
    (diagramInterior D).card = (edgeComponents (diagramInterior D)).card := by
  rw [GluingCore.card_eq_sum_edgeComponents]
  calc
    _ = ∑ _C ∈ edgeComponents (diagramInterior D), 1 :=
      Finset.sum_congr rfl fun C hC => hd C hC
    _ = _ := by simp

/-- In the discrete case, every high-span connected factor is the inner function. -/
theorem IsLegal.highSpan_factor_eq_inner_of_discrete (h : ω.IsLegal) {D G : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) (hd : HasDiscreteInterior D)
    (hG : IsConnectedSkew G) (hsp : ω.period ≤ (span G : ℤ))
    (hf : cellSchur G hG.1 ∣
      cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior) :
    cellSchur G hG.1 = cellSchur ω.E h.1.1.1 := by
  have hir : Irreducible (cellSchur G hG.1) := by
    simpa only [map_integralCellSchur] using irreducible_integralCellSchur (K := ℚ) hG
  obtain ⟨C, he⟩ := h.highSpan_factor_is_child hD hcard hir
    (by rw [polynomialSpan_cellSchur hG]; exact hsp) hf
  have hc := isConnectedSkew_component hD.1.interior C.2
  have hs := cellSchur_eq_of_associated hG.1 (h.connected_compose hc).1 he
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hd C.1 C.2)
  have hh : cellSchur (ω.compose C.1) (h.connected_compose hc).1 =
      cellSchur ω.E h.1.1.1 := by
    have hxC : IsConnectedSkew ({x} : Diagram) := hx ▸ hc
    have heq := h.cellSchur_compose_singleton x hxC
    rw [cellSchur_eq_gluing] at heq ⊢
    rw [hx]
    exact heq
  exact hs.trans hh

/-- Equal inners and cofactors force the other residual interior to be discrete. -/
theorem IsLegal.other_discrete_of_equal_inner {D R : Diagram}
    (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D) (hR : IsConnectedSkew R)
    (hDcard : 2 ≤ D.card) (hRcard : 2 ≤ R.card)
    (hd : HasDiscreteInterior D)
    (hk : cellSchur (diagramInterior (ω.compose D)) (hω.connected_compose hD).1.interior =
      cellSchur (diagramInterior (η.compose R)) (hη.connected_compose hR).1.interior)
    (hi : cellSchur ω.E hω.1.1.1 = cellSchur η.E hη.1.1.1) :
    HasDiscreteInterior R := by
  classical
  intro T hT
  by_contra hn
  have hc := isConnectedSkew_component hR.1.interior hT
  have htcard : 2 ≤ T.card := by
    have hh := Finset.card_pos.mpr hc.2.1
    omega
  have htspan := two_le_span_of_two_le_card hc htcard
  have hG := hη.connected_compose hc
  have hs := span_compose hc hη
  have hinner := congrArg SkewCornerDescent.Matrix.polynomialSpan hi
  rw [polynomialSpan_cellSchur hω.1.1, polynomialSpan_cellSchur hη.1.1] at hinner
  have hωsp := hω.1.span_eq
  have hηsp := hη.1.span_eq
  have hq : 0 < η.period := by have := hη.2.2.1.2; omega
  have hw0 : (0 : ℤ) ≤ ω.width := Int.natCast_nonneg _
  have hh : (span ω.E : ℤ) < span (η.compose T) := by
    have htspan' : (2 : ℤ) ≤ span T := by exact_mod_cast htspan
    nlinarith
  have hdiv := hη.child_dvd_cofactor hR hRcard hT
  rw [← hk] at hdiv
  have he := hω.highSpan_factor_eq_inner_of_discrete hD hDcard hd hG
    (by omega) hdiv
  have hEq := congrArg SkewCornerDescent.Matrix.polynomialSpan he
  rw [polynomialSpan_cellSchur hG, polynomialSpan_cellSchur hω.1.1] at hEq
  omega

/-- Every discrete child has exactly the supplied inner function. -/
theorem IsLegal.discrete_child_function (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hd : HasDiscreteInterior D)
    (C : {C // C ∈ edgeComponents (diagramInterior D)}) :
    ω.childFunction h hD C = cellSchur ω.E h.1.1.1 := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hd C.1 C.2)
  have hc := isConnectedSkew_component hD.1.interior C.2
  have hxC : IsConnectedSkew ({x} : Diagram) := hx ▸ hc
  have heq := h.cellSchur_compose_singleton x hxC
  unfold childFunction
  rw [cellSchur_eq_gluing] at heq ⊢
  rw [hx]
  exact heq

/-- The inner's exact cofactor multiplicity is the number of isolated interior cells. -/
theorem IsLegal.inner_multiplicity_discrete (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) (hd : HasDiscreteInterior D) :
    emultiplicity (cellSchur ω.E h.1.1.1)
      (cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior) =
        ((diagramInterior D).card : ℕ∞) := by
  classical
  have hf : Irreducible (cellSchur ω.E h.1.1.1) := by
    simpa only [map_integralCellSchur] using irreducible_integralCellSchur (K := ℚ) h.1.1
  have hs : ω.period ≤
      (SkewCornerDescent.Matrix.polynomialSpan (cellSchur ω.E h.1.1.1) : ℤ) := by
    rw [polynomialSpan_cellSchur h.1.1, h.1.span_eq]
    omega
  have he := h.highSpan_multiplicity_count hD hcard hf hs
  have he' : emultiplicity (cellSchur ω.E h.1.1.1)
      (cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior) =
      ∑ C ∈ (edgeComponents (diagramInterior D)).attach,
        if Associated (cellSchur ω.E h.1.1.1) (ω.childFunction h hD C)
          then (1 : ℕ∞) else 0 := he
  rw [he']
  simp only [h.discrete_child_function hD hd, ite_eq_left (Associated.refl _),
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_attach,
    interior_card_eq_component_card hd]

/-- Equal cofactors and equal inners preserve the number of isolated residual cells. -/
theorem IsLegal.other_interior_card_of_equal_inner {D R : Diagram}
    (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D) (hR : IsConnectedSkew R)
    (hDcard : 2 ≤ D.card) (hRcard : 2 ≤ R.card) (hd : HasDiscreteInterior D)
    (hk : cellSchur (diagramInterior (ω.compose D)) (hω.connected_compose hD).1.interior =
      cellSchur (diagramInterior (η.compose R)) (hη.connected_compose hR).1.interior)
    (hi : cellSchur ω.E hω.1.1.1 = cellSchur η.E hη.1.1.1) :
    (diagramInterior D).card = (diagramInterior R).card := by
  have hr := hω.other_discrete_of_equal_inner hη hD hR hDcard hRcard hd hk hi
  have h1 := hω.inner_multiplicity_discrete hD hDcard hd
  have h2 := hη.inner_multiplicity_discrete hR hRcard hr
  rw [hk, hi, h2] at h1
  exact_mod_cast h1.symm

/-- Equal parent and inner spans with different periods strictly order widths and outer spans. -/
theorem IsLegal.equal_span_statistics {D R : Diagram}
    (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D) (hR : IsConnectedSkew R)
    (hDcard : 2 ≤ D.card) (hRcard : 2 ≤ R.card) (hp : η.period < ω.period)
    (hparent : span (ω.compose D) = span (η.compose R))
    (hi : cellSchur ω.E hω.1.1.1 = cellSchur η.E hη.1.1.1) :
    span D < span R ∧ ω.width < η.width ∧
      ω.period * ((span D : ℤ) - 1) = η.period * ((span R : ℤ) - 1) := by
  have hinner := congrArg SkewCornerDescent.Matrix.polynomialSpan hi
  rw [polynomialSpan_cellSchur hω.1.1, polynomialSpan_cellSchur hη.1.1] at hinner
  have hw := hω.1.span_eq
  have hu := hη.1.span_eq
  have hpar : (span (ω.compose D) : ℤ) = span (η.compose R) := by exact_mod_cast hparent
  rw [span_compose hD hω, span_compose hR hη] at hpar
  have hq : 0 < η.period := by have := hη.2.2.1.2; omega
  have hm : (2 : ℤ) ≤ span D := by exact_mod_cast two_le_span_of_two_le_card hD hDcard
  have hm' : (2 : ℤ) ≤ span R := by exact_mod_cast two_le_span_of_two_le_card hR hRcard
  have he : ω.period * ((span D : ℤ) - 1) = η.period * ((span R : ℤ) - 1) := by
    nlinarith
  refine ⟨?_, by omega, he⟩
  by_contra hn
  have horder : (span R : ℤ) ≤ span D := by exact_mod_cast Nat.le_of_not_gt hn
  nlinarith

/-- In the discrete case the actual child product is a power of the inner. -/
theorem IsLegal.discrete_child_product (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hd : HasDiscreteInterior D) :
    ω.childProduct h D hD.1 = (cellSchur ω.E h.1.1.1) ^ (diagramInterior D).card := by
  unfold childProduct
  change (∏ C ∈ (edgeComponents (diagramInterior D)).attach,
    ω.childFunction h hD C) = _
  simp only [h.discrete_child_function hD hd, Finset.prod_const, Finset.card_attach,
    interior_card_eq_component_card hd]

/-- Equal cofactors with the same isolated children give exact equality of the scalar products. -/
theorem IsLegal.transportScalar_eq_of_equal_inner {D R : Diagram}
    (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D) (hR : IsConnectedSkew R)
    (hDcard : 2 ≤ D.card) (hRcard : 2 ≤ R.card) (hd : HasDiscreteInterior D)
    (hk : cellSchur (diagramInterior (ω.compose D)) (hω.connected_compose hD).1.interior =
      cellSchur (diagramInterior (η.compose R)) (hη.connected_compose hR).1.interior)
    (hi : cellSchur ω.E hω.1.1.1 = cellSchur η.E hη.1.1.1) :
    ω.transportScalar hω D = η.transportScalar hη R := by
  have hr := hω.other_discrete_of_equal_inner hη hD hR hDcard hRcard hd hk hi
  have hc := hω.other_interior_card_of_equal_inner hη hD hR hDcard hRcard hd hk hi
  rw [hω.corner_transport hD hDcard, hη.corner_transport hR hRcard,
    hω.discrete_child_product hD hd, hη.discrete_child_product hR hr, hi, hc] at hk
  exact mul_right_cancel₀ (pow_ne_zero _ (cellSchur_ne_zero η.E hη.1.1.1)) hk

/-- The order of the normal scalar is its explicit linear combination of factor orders. -/
theorem IsLegal.transportScalar_order (h : ω.IsLegal) (D : Diagram) {f : Lambda}
    (hf : Prime f) :
    primeOrder f (ω.transportScalar h D) =
      primeOrder f (ω.normalTheta h) +
      ((D.image Prod.fst).card - 1 - ((diagramInterior D).image Prod.fst).card) *
        primeOrder f (ω.normalA h) +
      ((D.image Prod.snd).card - 1 - ((diagramInterior D).image Prod.snd).card) *
        primeOrder f (ω.normalB h) +
      (span D - span (diagramInterior D)) * primeOrder f (ω.normalC h) := by
  obtain ⟨ha, hb, hc, ht⟩ := h.normal_factors_ne_zero
  unfold transportScalar
  rw [primeOrder_mul hf
      (mul_ne_zero (mul_ne_zero ht (pow_ne_zero _ ha)) (pow_ne_zero _ hb))
      (pow_ne_zero _ hc),
    primeOrder_mul hf (mul_ne_zero ht (pow_ne_zero _ ha)) (pow_ne_zero _ hb),
    primeOrder_mul hf ht (pow_ne_zero _ ha),
    primeOrder_pow hf, primeOrder_pow hf, primeOrder_pow hf]

/-- A factor above a normalization bound has zero order in that normalization. -/
theorem order_zero_of_span_bound {f g : Lambda} (hg : g ≠ 0) {n : ℤ}
    (hb : (polynomialSpan g : ℤ) < n) (hf : n ≤ (polynomialSpan f : ℤ)) :
    primeOrder f g = 0 := by
  apply primeOrder_eq_zero_of_not_dvd
  intro hd
  have hs : (polynomialSpan f : ℤ) ≤ polynomialSpan g := by
    exact_mod_cast polynomialSpan_le_of_dvd hg hd
  omega

/-- All three interior statistics count the isolated cells in the discrete case. -/
theorem discrete_interior_statistics {D : Diagram} (hD : IsSkew D)
    (hd : HasDiscreteInterior D) :
    ((diagramInterior D).image Prod.fst).card = (diagramInterior D).card ∧
      ((diagramInterior D).image Prod.snd).card = (diagramInterior D).card ∧
      span (diagramInterior D) = (diagramInterior D).card := by
  classical
  have he {α : Type} [DecidableEq α] (f : ℤ × ℤ → α) :
      (∑ C ∈ edgeComponents (diagramInterior D), (C.image f).card) =
        (diagramInterior D).card := by
    rw [interior_card_eq_component_card hd]
    calc
      _ = ∑ _C ∈ edgeComponents (diagramInterior D), 1 := by
        apply Finset.sum_congr rfl
        intro C hC
        obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (hd C hC)
        simp
      _ = _ := by simp
  exact ⟨(sum_component_rows hD.interior).symm.trans (he Prod.fst),
    (sum_component_cols hD.interior).symm.trans (he Prod.snd),
    (sum_component_spans hD.interior).symm.trans (he content)⟩

/-- Above the larger mark width, cancellation leaves only nonnegative target orders. -/
theorem IsLegal.alpha_order_identity {D R : Diagram}
    (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D) (hR : IsConnectedSkew R)
    (hDcard : 2 ≤ D.card) (hRcard : 2 ≤ R.card) (hd : HasDiscreteInterior D)
    (hk : cellSchur (diagramInterior (ω.compose D)) (hω.connected_compose hD).1.interior =
      cellSchur (diagramInterior (η.compose R)) (hη.connected_compose hR).1.interior)
    (hi : cellSchur ω.E hω.1.1.1 = cellSchur η.E hη.1.1.1)
    (hwidth : ω.width < η.width) {f : Lambda} (hf : Prime f)
    (hsp : (η.width : ℤ) ≤ polynomialSpan f) :
    (span D - (diagramInterior D).card) *
        primeOrder f (cellSchur (diagramInterior η.E) hη.1.1.1.interior) =
      ((R.image Prod.fst).card - 1 - (diagramInterior D).card) * primeOrder f (η.normalA hη) +
      ((R.image Prod.snd).card - 1 - (diagramInterior D).card) * primeOrder f (η.normalB hη) +
      (span R - (diagramInterior D).card) *
        primeOrder f (cellSchur (diagramInterior η.E) hη.1.1.1.interior) := by
  have hr := hω.other_discrete_of_equal_inner hη hD hR hDcard hRcard hd hk hi
  have hc := hω.other_interior_card_of_equal_inner hη hD hR hDcard hRcard hd hk hi
  have hs := hω.transportScalar_eq_of_equal_inner hη hD hR hDcard hRcard hd hk hi
  have he := congrArg (primeOrder f) hs
  rw [hω.transportScalar_order D hf, hη.transportScalar_order R hf] at he
  have hA0 : primeOrder f (ω.normalA hω) = 0 :=
    order_zero_of_span_bound hω.normal_factors_ne_zero.1
      (hω.normal_mark_spans.1.trans_lt (by exact_mod_cast hwidth)) hsp
  have hB0 : primeOrder f (ω.normalB hω) = 0 :=
    order_zero_of_span_bound hω.normal_factors_ne_zero.2.1
      (hω.normal_mark_spans.2.trans_lt (by exact_mod_cast hwidth)) hsp
  have hT0 : primeOrder f (ω.normalTheta hω) = 0 := by
    apply order_zero_of_span_bound hω.normal_factors_ne_zero.2.2.2 _ hsp
    have ht := hω.normalTheta_span_le
    omega
  have hT1 : primeOrder f (η.normalTheta hη) = 0 := by
    apply order_zero_of_span_bound hη.normal_factors_ne_zero.2.2.2 _ hsp
    have ht := hη.normalTheta_span_le
    omega
  have hκ := interiorSchur_eq_of_cellSchur_eq hω.1.1 hη.1.1 hi
  have h0 := hω.interiorSchur_single_normalization
  have h1 := hη.interiorSchur_single_normalization
  have hC0 := congrArg (primeOrder f) h0
  have hC1 := congrArg (primeOrder f) h1
  rw [primeOrder_mul hf hω.normal_factors_ne_zero.2.2.2
    hω.normal_factors_ne_zero.2.2.1, hT0, zero_add, hκ] at hC0
  rw [primeOrder_mul hf hη.normal_factors_ne_zero.2.2.2
    hη.normal_factors_ne_zero.2.2.1, hT1, zero_add] at hC1
  rw [hA0, hB0, hT0, hT1, ← hC0, ← hC1] at he
  simp only [zero_add, mul_zero, add_zero] at he
  rw [(discrete_interior_statistics hD.1 hd).2.2,
    (discrete_interior_statistics hR.1 hr).1,
    (discrete_interior_statistics hR.1 hr).2.1,
    (discrete_interior_statistics hR.1 hr).2.2, ← hc] at he
  exact he

/-- Every high-span order in the alpha residual vanishes in the inner corner. -/
theorem IsLegal.alpha_vanishing_orders {D R : Diagram}
    (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D) (hR : IsConnectedSkew R)
    (hDcard : 2 ≤ D.card) (hRcard : 2 ≤ R.card) (hp : η.period < ω.period)
    (hd : HasDiscreteInterior D) (hparent : span (ω.compose D) = span (η.compose R))
    (hk : cellSchur (diagramInterior (ω.compose D)) (hω.connected_compose hD).1.interior =
      cellSchur (diagramInterior (η.compose R)) (hη.connected_compose hR).1.interior)
    (hi : cellSchur ω.E hω.1.1.1 = cellSchur η.E hη.1.1.1)
    {f : Lambda} (hf : Prime f) (hsp : (η.width : ℤ) ≤ polynomialSpan f) :
    ((R.image Prod.fst).card - 1 - (diagramInterior D).card) * primeOrder f (η.normalA hη) = 0 ∧
      ((R.image Prod.snd).card - 1 - (diagramInterior D).card) *
        primeOrder f (η.normalB hη) = 0 ∧
      primeOrder f (cellSchur (diagramInterior η.E) hη.1.1.1.interior) = 0 := by
  have hstat := hω.equal_span_statistics hη hD hR hDcard hRcard hp hparent hi
  have he := hω.alpha_order_identity hη hD hR hDcard hRcard hd hk hi hstat.2.1 hf hsp
  have hb := IsLegal.corner_transport_exponents hD hDcard
  rw [(discrete_interior_statistics hD.1 hd).2.2] at hb
  have hlt : span D - (diagramInterior D).card <
      span R - (diagramInterior D).card := by omega
  have hzero : primeOrder f (cellSchur (diagramInterior η.E) hη.1.1.1.interior) = 0 := by
    nlinarith
  rw [hzero, mul_zero, mul_zero, add_zero] at he
  exact ⟨by omega, by omega, hzero⟩

/-- A positive-width mark normalization is a connected prime of exactly that width. -/
theorem IsLegal.normalA_irreducible_span (h : η.IsLegal) (hw : 0 < η.width) :
    Irreducible (η.normalA h) ∧ polynomialSpan (η.normalA h) = η.width := by
  have hW : η.W.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [width, span, contents, he, Finset.image_empty, Finset.card_empty] at hw
    omega
  have hc : IsConnectedSkew η.W := by
    rcases h.1.2 with he | he
    · exact False.elim (hW.ne_empty he.1)
    · exact he.2.1
  simp only [normalA, dite_eq_left hW, markA]
  exact ⟨by simpa only [map_integralCellSchur] using
    irreducible_integralCellSchur (K := ℚ) hc, polynomialSpan_cellSchur hc⟩

/-- The target outer has exactly one more row than its isolated interior cell count. -/
theorem IsLegal.alpha_row_count {D R : Diagram}
    (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D) (hR : IsConnectedSkew R)
    (hDcard : 2 ≤ D.card) (hRcard : 2 ≤ R.card) (hp : η.period < ω.period)
    (hd : HasDiscreteInterior D) (hparent : span (ω.compose D) = span (η.compose R))
    (hk : cellSchur (diagramInterior (ω.compose D)) (hω.connected_compose hD).1.interior =
      cellSchur (diagramInterior (η.compose R)) (hη.connected_compose hR).1.interior)
    (hi : cellSchur ω.E hω.1.1.1 = cellSchur η.E hη.1.1.1) :
    (R.image Prod.fst).card = (diagramInterior D).card + 1 := by
  have hs := hω.equal_span_statistics hη hD hR hDcard hRcard hp hparent hi
  have hu : 0 < η.width := by omega
  obtain ⟨hir, hspan⟩ := hη.normalA_irreducible_span hu
  have ho := hω.alpha_vanishing_orders hη hD hR hDcard hRcard hp hd hparent hk hi
    hir.prime (by rw [hspan])
  rw [primeOrder_self hir.prime, mul_one] at ho
  have hr := hω.other_discrete_of_equal_inner hη hD hR hDcard hRcard hd hk hi
  have hc := hω.other_interior_card_of_equal_inner hη hD hR hDcard hRcard hd hk hi
  have hb := IsLegal.corner_transport_exponents hR hRcard
  rw [(discrete_interior_statistics hR.1 hr).1, ← hc] at hb
  omega

/-- Both candidate normalizers lie strictly below the larger width. -/
theorem IsLegal.alpha_span_bounds {D R : Diagram}
    (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D) (hR : IsConnectedSkew R)
    (hDcard : 2 ≤ D.card) (hRcard : 2 ≤ R.card) (hp : η.period < ω.period)
    (hd : HasDiscreteInterior D) (hparent : span (ω.compose D) = span (η.compose R))
    (hk : cellSchur (diagramInterior (ω.compose D)) (hω.connected_compose hD).1.interior =
      cellSchur (diagramInterior (η.compose R)) (hη.connected_compose hR).1.interior)
    (hi : cellSchur ω.E hω.1.1.1 = cellSchur η.E hη.1.1.1) :
    polynomialSpan (cellSchur (diagramInterior η.E) hη.1.1.1.interior) < η.width ∧
      polynomialSpan (η.normalB hη) < η.width := by
  have hs := hω.equal_span_statistics hη hD hR hDcard hRcard hp hparent hi
  have hu : 0 < η.width := by omega
  have hκ : polynomialSpan (cellSchur (diagramInterior η.E) hη.1.1.1.interior) < η.width := by
    apply polynomialSpan_cellSchur_lt_of_orders hη.1.1.1.interior hu
    intro f hf hsp
    exact (hω.alpha_vanishing_orders hη hD hR hDcard hRcard hp hd hparent hk hi hf
      (by exact_mod_cast hsp)).2.2
  have hrow := hω.alpha_row_count hη hD hR hDcard hRcard hp hd hparent hk hi
  have hcntD := GluingCore.span_add_one_eq_numRows_add_numCols
    (show GluingCore.IsConnectedSkew D from hD)
  have hcntR := GluingCore.span_add_one_eq_numRows_add_numCols
    (show GluingCore.IsConnectedSkew R from hR)
  rw [GluingCore.numCols_eq_card_image_snd] at hcntD hcntR
  change (span D : ℤ) + 1 = ((D.image Prod.fst).card : ℤ) + (D.image Prod.snd).card at hcntD
  change (span R : ℤ) + 1 = ((R.image Prod.fst).card : ℤ) + (R.image Prod.snd).card at hcntR
  have hb := IsLegal.corner_transport_exponents hD hDcard
  rw [(discrete_interior_statistics hD.1 hd).1,
    (discrete_interior_statistics hD.1 hd).2.1] at hb
  have hcol : 0 < (R.image Prod.snd).card - 1 - (diagramInterior D).card := by omega
  have hW : η.W.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [width, span, contents, he, Finset.image_empty, Finset.card_empty] at hu
    omega
  have hB : η.normalB hη = cellSchur η.hatMarkWindow (hη.isSkew_hatMarkWindow hW) := by
    simp only [normalB, dite_eq_left hW, hatMarkB]
  refine ⟨hκ, ?_⟩
  rw [hB]
  apply polynomialSpan_cellSchur_lt_of_orders (hη.isSkew_hatMarkWindow hW) hu
  intro f hf hsp
  have he := (hω.alpha_vanishing_orders hη hD hR hDcard hRcard hp hd hparent hk hi hf
    (by exact_mod_cast hsp)).2.1
  have hz := (Nat.mul_eq_zero.mp he).resolve_left (ne_of_gt hcol)
  rwa [hB] at hz

/-- The full alpha row-candidate conclusion under the paper's cofactor-level hypotheses. -/
theorem IsLegal.alpha_row_candidate {D R : Diagram}
    (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D) (hR : IsConnectedSkew R)
    (hDcard : 2 ≤ D.card) (hRcard : 2 ≤ R.card) (hp : η.period < ω.period)
    (hd : HasDiscreteInterior D) (hparent : span (ω.compose D) = span (η.compose R))
    (hk : cellSchur (diagramInterior (ω.compose D)) (hω.connected_compose hD).1.interior =
      cellSchur (diagramInterior (η.compose R)) (hη.connected_compose hR).1.interior)
    (hi : cellSchur ω.E hω.1.1.1 = cellSchur η.E hη.1.1.1) :
    HasDiscreteInterior R ∧
      (diagramInterior R).card = (diagramInterior D).card ∧
      (∀ (n : ℕ) (P : Profile n) (v : ℤ × ℤ), R = translate v P.cells →
        ∀ i, P.g i = 1) ∧
      polynomialSpan (cellSchur (diagramInterior η.E) hη.1.1.1.interior) < η.width ∧
      polynomialSpan (η.normalB hη) < η.width := by
  have hr := hω.other_discrete_of_equal_inner hη hD hR hDcard hRcard hd hk hi
  have hc := hω.other_interior_card_of_equal_inner hη hD hR hDcard hRcard hd hk hi
  have hrow := hω.alpha_row_count hη hD hR hDcard hRcard hp hd hparent hk hi
  have hbounds := hω.alpha_span_bounds hη hD hR hDcard hRcard hp hd hparent hk hi
  refine ⟨hr, hc.symm, ?_, hbounds⟩
  intro n P v he
  apply P.gaps_eq_one_of_discrete_row_count v he hr
  rw [← hc]
  exact hrow

end SkewGluing.MarkedInner
