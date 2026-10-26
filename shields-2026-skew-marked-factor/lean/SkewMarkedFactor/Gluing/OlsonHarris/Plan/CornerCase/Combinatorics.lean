/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Combinatorics.lean
import SkewMarkedFactor.Gluing.Local
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MarkFacts.HatMark
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Bookkeeping
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Lift
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.CSign
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Crem

/-!
# The combinatorial inputs of the corner case

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis §5.5
(`OlsonHarris2024HopfApplications`), Lemmas 5.5.2–5.5.11, for a legal mark `ω` of case (c)
(`W → O ↑ W`) and a connected outer `D`, in the form consumed by the Leibniz and Murnaghan–
Nakayama computation of thesis Lemma 5.5.12 (`SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Connected`).

* `span_hatMarkFin_le`, `IsLegal.isSkew_middle`, `IsLegal.isSkew_hatMiddleFin` (module
  `MarkFacts.HatMark`, proved): the hatted mark occupies only diagonals of `W₋`, and `O` and
  `\overline O` are skew.
* `isSkew_hatMarkFin` (module `HatMark`, proved): `\overline W` is skew (thesis Remark 5.3.7).
* `corner_span_hatMiddle_lt`: `dia(\overline O) < q` (thesis Lemma 5.5.9, from
  `lem:gluing-local` (2)).
* `corner_no_leftRibbons` (module `NoRightRibbons`, proved): no ribbon of size `m q` is
  removable on the left from `D ∘_ω E` (thesis Lemmas 5.5.2, 5.5.7 (iii), 5.5.11 (iii)).
* `corner_ribbon_bijection` (module `Lift`, from the boundary words of the composite): the
  ribbons of size `m q` removable on the right from `D ∘_ω E` are the border-strip lifts of the
  ribbons of size `m` removable on the right or on the left from `D`;
* `corner_lift_height_sign`: the heights of the lifts (thesis Lemmas 5.5.10, 5.5.11), proved in
  `CSign`;
* `corner_lift_remainder`: the remainders `s_{F \ Ã}` (thesis Lemma 5.5.8), proved in `Crem`;
* `corner_ribbon_core`: the three together;
* `corner_ribbon_lift`: the same in the form of thesis Lemma 5.5.12, proved from
  `corner_ribbon_core` (exponent and sign bookkeeping, `Bookkeeping`).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

open MarkedInner

/-- The sign-and-power factor `(-1)^{ξ(D)} s_W^{|D| - row D} s_{\overline W}^{|D| - col D}
s_{\overline O}^{|D| - dia D}` of the corner modified composition of a connected `D`, so that
`modCompC ω D = cornerPrefactor ω D * s_{D ∘_ω E}`. -/
noncomputable def cornerPrefactor (ω : MarkedInner) (D : Diagram) : Lambda :=
  (-1 : Lambda) ^ northbound ω D * cellSchur ω.W ^ (D.card - numRows D) *
    cellSchur (hatMarkFin ω) ^ (D.card - numCols D) *
      cellSchur (hatMiddleFin ω) ^ (D.card - span D)

theorem componentTc_eq (ω : MarkedInner) (D : Diagram) :
    componentTc ω D = cornerPrefactor ω D * cellSchur (ω.compose D) := by
  unfold componentTc componentT cornerPrefactor
  ring

/-- A legal mark of case (c) is a nonempty mark. -/
theorem isNonemptyMark_of_case_c {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    ω.IsNonemptyMark := by
  rcases hω.1.2 with h | h
  · have := h.2.2
    rw [hc] at this
    cases this
  · exact h

theorem period_toNat_pos {ω : MarkedInner} (hω : ω.IsLegal) : 0 < ω.period.toNat := by
  have := hω.period_pos
  omega

/-- **Thesis Lemma 5.5.9.**  For a legal mark of case (c), `dia(\overline O) < q = k(E)`: the
hatted middle has fewer diagonals than the period (already the middle `O` has `q + t - s < q`
diagonals, `lem:gluing-local` (2) for mixed marks). -/
theorem corner_span_hatMiddle_lt {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    (span (hatMiddleFin ω) : ℤ) < ω.period := by
  have hW : ω.W.Nonempty := (isNonemptyMark_of_case_c hω hc).1
  obtain ⟨s, t, -, -, -, -, hcont, -, hmix, -, -⟩ := hω.gluing_local_two hW
  obtain ⟨hts, -⟩ := hmix (by simp [AttachCase.IsMixed, hc])
  have hq := hω.period_pos
  have hsub : contents (hatMiddleFin ω) ⊆ contents ω.middle :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have h1 : span (hatMiddleFin ω) ≤ span ω.middle := Finset.card_le_card hsub
  have h2 : span ω.middle = (Finset.Icc (minContent ω.E + s)
      (minContent ω.E + ω.period + t - 1)).card := by
    unfold span; rw [hcont]
  rw [Int.card_Icc] at h2
  omega

/-- **Thesis Lemmas 5.5.10 and 5.5.11: the heights of the lifts.**  There is a sign
`σ = (-1)^{h(E)}`, depending only on `ω` (`h(E) = ht K_W + ht K_O + 1`), such that for a ribbon `A`
of size `m` removable from the connected outer `D`, the lift `Ã = cornerLift ω D m s A` (on the
right, offset `s`) or `cornerLift ω D m t A` (on the left, offset `t`) has height sign
`(-1)^{ht Ã} = ± σ^m (-1)^{ht A} (-1)^{ξ(D) + ξ(D \ A)}`, with `+` for `A` removable on the right
and `-` on the left (thesis: `ht Ã = m h(E) + ht A - ξ(D) + ξ(D \ A)`, respectively
`m h(E) - ht A + ξ(D) - ξ(D \ A) - 1`).  The proof is in
`SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.CSign`. -/
theorem corner_lift_height_sign {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ D : Diagram, IsConnectedSkew D → ∀ m : ℕ, 0 < m →
      ∀ s t : ℤ, ω.IsPhases s t →
        (∀ A ∈ rightRibbons D m,
          ribbonSign (cornerLift ω D m s A) =
            σ ^ m * ribbonSign A * (-1) ^ (northboundSum ω D + northboundSum ω (D \ A))) ∧
        (∀ A ∈ leftRibbons D m,
          ribbonSign (cornerLift ω D m t A) =
            -(σ ^ m * ribbonSign A * (-1) ^ (northboundSum ω D + northboundSum ω (D \ A)))) :=
  corner_lift_height_sign_proof hω hc

/-- **Thesis Lemma 5.5.8: the remainder after removing a lifted key ribbon.**  For a ribbon `A`
of size `m` removable on the right (offset `s`) or on the left (offset `t`) from the connected
outer `D`, `F \ Ã` is the edge-disjoint union of `(D \ A) ∘_ω E`, a copy of `\overline O`, and
copies of `\overline W` and `W`, so
`s_{F \ Ã} = s_W^{row D - row (D \ A)} s_{\overline W}^{col D - col (D \ A)}
s_{\overline O}^{dia D - dia (D \ A)} ∏_C s_{C ∘_ω E}`, the product over the edge components `C`
of `D \ A`.  The proof is in
`SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Crem`. -/
theorem corner_lift_remainder {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    ∀ D : Diagram, IsConnectedSkew D → ∀ m : ℕ, 0 < m → ∀ s t : ℤ, ω.IsPhases s t →
      (∀ A ∈ rightRibbons D m,
        cellSchur (ω.compose D \ cornerLift ω D m s A) =
          cellSchur ω.W ^ (numRows D - numRows (D \ A)) *
            cellSchur (hatMarkFin ω) ^ (numCols D - numCols (D \ A)) *
              cellSchur (hatMiddleFin ω) ^ (span D - span (D \ A)) * compSchur ω (D \ A)) ∧
      (∀ A ∈ leftRibbons D m,
        cellSchur (ω.compose D \ cornerLift ω D m t A) =
          cellSchur ω.W ^ (numRows D - numRows (D \ A)) *
            cellSchur (hatMarkFin ω) ^ (numCols D - numCols (D \ A)) *
              cellSchur (hatMiddleFin ω) ^ (span D - span (D \ A)) * compSchur ω (D \ A)) :=
  corner_lift_remainder_proof hω hc

/-- **The ribbons of size `m q` removable on the right from a corner composite** (thesis
Lemmas 5.5.5, 5.5.7 (i)–(ii), 5.5.8, 5.5.10 and 5.5.11 (i)–(ii)): the bijection with the ribbons
of the outer (`corner_ribbon_bijection`, proved from the boundary words of the composite),
together with `corner_lift_height_sign` and `corner_lift_remainder`. -/
theorem corner_ribbon_core {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ D : Diagram, IsConnectedSkew D → ∀ m : ℕ, 0 < m →
      ∃ liftR liftL : Diagram → Diagram,
        rightRibbons (ω.compose D) (m * ω.period.toNat) =
          (rightRibbons D m).image liftR ∪ (leftRibbons D m).image liftL ∧
        Set.InjOn liftR (rightRibbons D m) ∧ Set.InjOn liftL (leftRibbons D m) ∧
        Disjoint ((rightRibbons D m).image liftR) ((leftRibbons D m).image liftL) ∧
        (∀ A ∈ rightRibbons D m,
          ribbonSign (liftR A) =
              σ ^ m * ribbonSign A * (-1) ^ (northboundSum ω D + northboundSum ω (D \ A)) ∧
            cellSchur (ω.compose D \ liftR A) =
              cellSchur ω.W ^ (numRows D - numRows (D \ A)) *
                cellSchur (hatMarkFin ω) ^ (numCols D - numCols (D \ A)) *
                  cellSchur (hatMiddleFin ω) ^ (span D - span (D \ A)) *
                    compSchur ω (D \ A)) ∧
        (∀ A ∈ leftRibbons D m,
          ribbonSign (liftL A) =
              -(σ ^ m * ribbonSign A * (-1) ^ (northboundSum ω D + northboundSum ω (D \ A))) ∧
            cellSchur (ω.compose D \ liftL A) =
              cellSchur ω.W ^ (numRows D - numRows (D \ A)) *
                cellSchur (hatMarkFin ω) ^ (numCols D - numCols (D \ A)) *
                  cellSchur (hatMiddleFin ω) ^ (span D - span (D \ A)) *
                    compSchur ω (D \ A)) := by
  have hW : ω.W.Nonempty := (isNonemptyMark_of_case_c hω hc).1
  have hl : ω.IsLegalNonempty := ⟨hω, hW⟩
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  obtain ⟨σ, hσ, hsign⟩ := corner_lift_height_sign hω hc
  refine ⟨σ, hσ, fun D hD m hm => ?_⟩
  obtain ⟨hset, injR, injL, hdisj⟩ := corner_ribbon_bijection hl hD hc hph hm
  obtain ⟨hsR, hsL⟩ := hsign D hD m hm s t hph
  obtain ⟨hrR, hrL⟩ := corner_lift_remainder hω hc D hD m hm s t hph
  exact ⟨cornerLift ω D m s, cornerLift ω D m t, hset, injR, injL, hdisj,
    fun A hA => ⟨hsR A hA, hrR A hA⟩, fun A hA => ⟨hsL A hA, hrL A hA⟩⟩

/-- The prefactor identity behind the two cases of `corner_ribbon_lift`: for a subset `A` of size
`m` of a connected skew diagram `D` with `D \ A` skew, the corner prefactor of `D`, the height
sign of `corner_ribbon_core` and the remainder of `corner_ribbon_core` multiply to
`σ^m (s_W s_{\overline W} s_{\overline O})^m r s^c_{D \ A}` (the exponents of `s_W`,
`s_{\overline W}`, `s_{\overline O}` add up because `|D| = |D \ A| + m`). -/
theorem cornerPrefactor_mul_remainder (ω : MarkedInner) {D A : Diagram} (hD : IsConnectedSkew D)
    {m : ℕ} (hAD : A ⊆ D) (hcard : A.card = m) (hX : IsSkew (D \ A)) (σ r : ℤ) :
    cornerPrefactor ω D * (((σ ^ m * r * (-1) ^ (northboundSum ω D +
          northboundSum ω (D \ A)) : ℤ)) : Lambda) *
      (cellSchur ω.W ^ (numRows D - numRows (D \ A)) *
        cellSchur (hatMarkFin ω) ^ (numCols D - numCols (D \ A)) *
          cellSchur (hatMiddleFin ω) ^ (span D - span (D \ A)) * compSchur ω (D \ A)) =
      (σ : Lambda) ^ m * hatFactor ω ^ m * (r : Lambda) * modCompC ω (D \ A) := by
  have hXc : (D \ A).card + m = D.card := by
    rw [Finset.card_sdiff_of_subset hAD, hcard]
    have := Finset.card_le_card hAD
    omega
  have hXsub : D \ A ⊆ D := Finset.sdiff_subset
  have r1 := numRows_mono hXsub
  have r2 := numCols_mono hXsub
  have r3 := span_mono hXsub
  have c1 := numRows_le_card D
  have c2 := numCols_le_card D
  have c3 := span_le_card D
  have d1 := numRows_le_card (D \ A)
  have d2 := numCols_le_card (D \ A)
  have d3 := span_le_card (D \ A)
  have hξ : northboundSum ω D = northbound ω D := by
    unfold northboundSum
    rw [edgeComponents_eq_singleton hD.2, Finset.sum_singleton]
  rw [modCompC_eq ω hX, hξ]
  unfold cornerPrefactor hatFactor
  set sW := cellSchur ω.W
  set sH := cellSchur (hatMarkFin ω)
  set sO := cellSchur (hatMiddleFin ω)
  have e1 : sW ^ (D.card - numRows D) * sW ^ (numRows D - numRows (D \ A)) =
      sW ^ ((D \ A).card - numRows (D \ A)) * sW ^ m := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have e2 : sH ^ (D.card - numCols D) * sH ^ (numCols D - numCols (D \ A)) =
      sH ^ ((D \ A).card - numCols (D \ A)) * sH ^ m := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have e3 : sO ^ (D.card - span D) * sO ^ (span D - span (D \ A)) =
      sO ^ ((D \ A).card - span (D \ A)) * sO ^ m := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hsign : ((-1 : Lambda) ^ northbound ω D) * (((-1 : ℤ) ^ (northbound ω D +
      northboundSum ω (D \ A)) : ℤ) : Lambda) = (-1 : Lambda) ^ northboundSum ω (D \ A) := by
    push_cast
    rw [pow_add, ← mul_assoc, ← mul_pow]
    simp
  have hcast : (((σ ^ m * r * (-1) ^ (northbound ω D + northboundSum ω (D \ A)) : ℤ)) :
      Lambda) = (σ : Lambda) ^ m * (r : Lambda) *
        (((-1 : ℤ) ^ (northbound ω D + northboundSum ω (D \ A)) : ℤ) : Lambda) := by
    push_cast; ring
  rw [hcast]
  calc _ = ((-1 : Lambda) ^ northbound ω D * (((-1 : ℤ) ^ (northbound ω D +
        northboundSum ω (D \ A)) : ℤ) : Lambda)) *
      ((sW ^ (D.card - numRows D) * sW ^ (numRows D - numRows (D \ A))) *
        (sH ^ (D.card - numCols D) * sH ^ (numCols D - numCols (D \ A))) *
        (sO ^ (D.card - span D) * sO ^ (span D - span (D \ A)))) *
        ((σ : Lambda) ^ m * (r : Lambda)) * compSchur ω (D \ A) := by ring
    _ = _ := by rw [hsign, e1, e2, e3, mul_pow, mul_pow]; ring

/-- **The ribbons of size `m q` removable on the right from a corner composite, in the form of
the corner equation** (thesis Lemma 5.5.12): the lifts of `corner_ribbon_core` with the
prefactor of the corner modified composition and the signs of Murnaghan–Nakayama. -/
theorem corner_ribbon_lift {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ D : Diagram, IsConnectedSkew D → ∀ m : ℕ, 0 < m →
      ∃ liftR liftL : Diagram → Diagram,
        rightRibbons (ω.compose D) (m * ω.period.toNat) =
          (rightRibbons D m).image liftR ∪ (leftRibbons D m).image liftL ∧
        Set.InjOn liftR (rightRibbons D m) ∧ Set.InjOn liftL (leftRibbons D m) ∧
        Disjoint ((rightRibbons D m).image liftR) ((leftRibbons D m).image liftL) ∧
        (∀ A ∈ rightRibbons D m,
          cornerPrefactor ω D * ((ribbonSign (liftR A) : ℤ) : Lambda) *
              cellSchur (ω.compose D \ liftR A) =
            (σ : Lambda) ^ m * hatFactor ω ^ m * (ribbonSign A : Lambda) *
              modCompC ω (D \ A)) ∧
        (∀ A ∈ leftRibbons D m,
          cornerPrefactor ω D * ((ribbonSign (liftL A) : ℤ) : Lambda) *
              cellSchur (ω.compose D \ liftL A) =
            -((σ : Lambda) ^ m * hatFactor ω ^ m * (ribbonSign A : Lambda) *
              modCompC ω (D \ A))) := by
  obtain ⟨σ, hσ, H⟩ := corner_ribbon_core hω hc
  refine ⟨σ, hσ, fun D hD m hm => ?_⟩
  obtain ⟨liftR, liftL, hset, injR, injL, hdisj, hR, hL⟩ := H D hD m hm
  refine ⟨liftR, liftL, hset, injR, injL, hdisj, fun A hA => ?_, fun A hA => ?_⟩
  · obtain ⟨hsg, hrem⟩ := hR A hA
    obtain ⟨hAD, hcard, -, hup⟩ := mem_rightRibbons.mp hA
    rw [hsg, hrem]
    exact cornerPrefactor_mul_remainder ω hD hAD hcard (isSkew_sdiff_of_isUpsetIn hD.1 hup) σ _
  · obtain ⟨hsg, hrem⟩ := hL A hA
    obtain ⟨hAD, hcard, -, hdown⟩ := mem_leftRibbons.mp hA
    rw [hsg, hrem, Int.cast_neg]
    have := cornerPrefactor_mul_remainder ω hD hAD hcard (isSkew_sdiff_of_isDownsetIn hD.1 hdown)
      σ (ribbonSign A)
    linear_combination (-1 : Lambda) * this

/-! ### Checked examples -/

section Examples

/-- The rotation of the hook mark is a legal mark of case (c). -/
example : hookInner.rotate.IsLegal ∧ hookInner.rotate.case = .c := ⟨by decide +kernel, rfl⟩

/-- Its hatted mark is skew (here empty). -/
example : IsSkew (hatMarkFin hookInner.rotate) := by decide +kernel

/-- No ribbon of size `q = 2` is removable on the left from `(2, 2) ∘_ω E`
(`corner_no_leftRibbons`, `m = 1`). -/
example : leftRibbons (hookInner.rotate.compose (skewOf [2, 2] [])) 2 = ∅ := by decide +kernel

/-- The ribbons of size `q = 2` removable on the right from `(2, 2) ∘_ω E` are in bijection with
the ribbons of size `1` removable from `(2, 2)` on the right or on the left
(`corner_ribbon_lift`, `m = 1`): there are `1 + 1`. -/
example : (rightRibbons (hookInner.rotate.compose (skewOf [2, 2] [])) 2).card =
    (rightRibbons (skewOf [2, 2] []) 1).card + (leftRibbons (skewOf [2, 2] []) 1).card := by
  decide +kernel

end Examples

end Corner

end Plan

end SkewMarkedFactor.Gluing
