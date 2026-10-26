/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.Mark

/-!
# Composition and charts

Formalizes the cell-coordinate composition used in `shields-2026-skew-corner-descent.tex`,
«Marked inners and finite end caps» (`sec:marks`, `eq:placements`, `eq:composition-span`).

The composition `D ∘_ω E` is defined as the union of translated inner copies, together with the
supplemental copies in the mixed cases. The target-paper result here is the span formula for a
nonempty connected outer and legal marked inner. The remaining chart and gauge declarations are
copied supporting material from the sibling project.

TODO-COPIED: copied from skew-factor-gluing.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

/-- The copy origin `L_ω(d)` of `eq:placements` for the cell `d = (i, i + j)` of `D`:
`j v + i e`, `j v - i e`, `j v + (i - ℓ_j) e`, `j v - (h_j - i) e` in cases (a)–(d). -/
def origin (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) : ℤ × ℤ :=
  match ω.case with
  | .a => content d • ω.v + d.1 • eCell
  | .b => content d • ω.v - d.1 • eCell
  | .c => content d • ω.v + (d.1 - diagLo D (content d)) • eCell
  | .d => content d • ω.v - (diagHi D (content d) - d.1) • eCell

/-- In the mixed cases, the cell `d` and the cell `(i - 1, j)` directly north of it lie on the
same northwest (case (c)), respectively southeast (case (d)), boundary ribbon: their ribbon
ranks `i - ℓ_j + 1`, respectively `h_j - i + 1`, agree.  In the ordinary cases this never
holds. -/
def SameRibbon (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) : Prop :=
  (d.1 - 1, d.2) ∈ D ∧
    match ω.case with
    | .a => False
    | .b => False
    | .c => d.1 - diagLo D (content d) = (d.1 - 1) - diagLo D (content d + 1)
    | .d => diagHi D (content d) - d.1 = diagHi D (content d + 1) - (d.1 - 1)

instance (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) : Decidable (ω.SameRibbon D d) := by
  unfold SameRibbon
  cases ω.case <;> infer_instance

/-- The shift `±e` of the supplemental copies: `+e` in case (c), `-e` in case (d). -/
def supplementalShift (ω : MarkedInner) : ℤ × ℤ :=
  match ω.case with
  | .c => eCell
  | _ => -eCell

/-- The composition `D ∘_ω E`, by the cell form of `eq:placements`: the translated copies
`E + L_ω(d)` for `d ∈ D`, plus, for a vertical pair on the same boundary ribbon with lower cell
`d`, the supplemental copy `W₊ + L_ω(d) ± e`. The empty-outer convention is
`∅ ∘_ω E = W`. -/
def compose (D : Diagram) (ω : MarkedInner) : Diagram :=
  if D = ∅ then ω.W else
    D.biUnion (fun d => translate (ω.origin D d) ω.E) ∪
      (D.filter (ω.SameRibbon D)).biUnion
        (fun d => translate (ω.origin D d + ω.supplementalShift) ω.upper)

theorem mem_compose {D : Diagram} (hD : D.Nonempty) {ω : MarkedInner} {x : ℤ × ℤ} :
    x ∈ ω.compose D ↔ (∃ d ∈ D, x ∈ translate (ω.origin D d) ω.E) ∨
      ∃ d ∈ D, ω.SameRibbon D d ∧
        x ∈ translate (ω.origin D d + ω.supplementalShift) ω.upper := by
  have hne : D ≠ ∅ := hD.ne_empty
  unfold compose
  simp only [hne, ↓reduceIte]
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro (⟨d, hd, hx⟩ | ⟨d, ⟨hd, hr⟩, hx⟩)
    · exact Or.inl ⟨d, hd, hx⟩
    · exact Or.inr ⟨d, hd, hr, hx⟩
  · rintro (⟨d, hd, hx⟩ | ⟨d, hd, hr, hx⟩)
    · exact Or.inl ⟨d, hd, hx⟩
    · exact Or.inr ⟨d, ⟨hd, hr⟩, hx⟩

theorem content_origin (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) :
    content (ω.origin D d) = content d * ω.period := by
  unfold origin period
  have : ∀ n : ℤ, content (n • eCell) = 0 := by
    intro n; simp [content, eCell]
  cases ω.case <;> simp only [content_add, content_sub, content_smul, this] <;> ring

theorem content_supplementalShift (ω : MarkedInner) : content ω.supplementalShift = 0 := by
  unfold supplementalShift
  cases ω.case <;> simp [content, eCell]

/-- The width of a well-formed mark: `N_E = q + w`. -/
theorem IsWellFormed.span_eq {ω : MarkedInner} (h : ω.IsWellFormed) :
    (span ω.E : ℤ) = ω.period + ω.width := by
  obtain ⟨hE, hm⟩ := h
  have hEne : ω.E.Nonempty := hE.2.1
  have hsp := span_eq_of_isConnectedSkew hE
  rcases hm with hemp | hnon
  · obtain ⟨h1, h2, -⟩ := hemp
    have hw : ω.width = 0 := by simp [width, h1, span, contents]
    have hq : ω.period = maxContent ω.E - minContent ω.E + 1 := by
      unfold period
      rw [h2]
      unfold vH
      rw [content_add, content_sub, content_ne hEne, content_sw hEne]
      simp [content]
    omega
  · have hmax := hnon.maxContent_eq hE
    obtain ⟨hne, hW, hWE, hUE, hsw, hneU, -⟩ := hnon
    have hspW := span_eq_of_isConnectedSkew hW
    have hmin : minContent ω.W = minContent ω.E := by
      have hsub : contents ω.W ⊆ contents ω.E := Finset.image_subset_image hWE
      apply le_antisymm
      · have : content (sw ω.E) ∈ contents ω.W := content_mem_contents hsw
        rw [content_sw hEne] at this
        exact minContent_le this
      · exact minContent_le (hsub (minContent_mem hne))
    unfold width period
    omega

theorem IsWellFormed.contents_eq {ω : MarkedInner} (h : ω.IsWellFormed) :
    contents ω.E = Finset.Icc (minContent ω.E) (minContent ω.E + ω.period + ω.width - 1) := by
  have hE := h.1
  have h' := isConnectedSkew_iff_diagonal.mp hE
  rw [h'.contents_eq]
  have := span_eq_of_isConnectedSkew hE
  have := h.span_eq
  congr 1
  omega

/-- **The composition-span formula** in `eq:composition-span`. For a legal mark of width `w` and
period `q` and a connected outer `D` with `r = N_D`, the composite has span `N_F = r q + w`. -/
theorem span_compose {D : Diagram} (hD : IsConnectedSkew D) {ω : MarkedInner}
    (hω : ω.IsLegal) :
    (span (ω.compose D) : ℤ) = (span D : ℤ) * ω.period + ω.width := by
  have hDne : D.Nonempty := hD.2.1
  have hwf := hω.1
  have hq : 0 < ω.period := by
    have := hω.2.2.1
    unfold IsNarrow at this
    omega
  have hcE := hwf.contents_eq
  have hspE := hwf.span_eq
  set c0 := minContent ω.E with hc0
  set q := ω.period with hqdef
  set w : ℤ := (ω.width : ℤ) with hwdef
  have hw0 : 0 ≤ w := by positivity
  have hwq : w < q := hω.2.2.1.2
  have hD' := isConnectedSkew_iff_diagonal.mp hD
  set m := minContent D with hm
  set M := maxContent D with hM
  have hspD := span_eq_of_isConnectedSkew hD
  have hcD : ∀ j, j ∈ contents D ↔ m ≤ j ∧ j ≤ M := fun j => hD'.mem_contents_iff
  have hmem : ∀ x : ℤ × ℤ, x ∈ ω.compose D → ∃ d ∈ D,
      c0 + content d * q ≤ content x ∧ content x ≤ c0 + content d * q + q + w - 1 := by
    intro x hx
    have key : ∀ d ∈ D, ∀ T : Diagram, T ⊆ ω.E → ∀ t : ℤ × ℤ, content t = content d * q →
        x ∈ translate t T → ∃ d ∈ D, c0 + content d * q ≤ content x ∧
          content x ≤ c0 + content d * q + q + w - 1 := by
      intro d hd T hT t ht hxT
      refine ⟨d, hd, ?_⟩
      have h1 := mem_translate.mp hxT
      have h2 := hT h1
      have h3 : content (x - t) ∈ contents ω.E := content_mem_contents h2
      rw [hcE, Finset.mem_Icc] at h3
      rw [content_sub, ht] at h3
      constructor <;> omega
    rcases (mem_compose hDne).mp hx with ⟨d, hd, hxd⟩ | ⟨d, hd, -, hxd⟩
    · exact key d hd ω.E subset_rfl _ (content_origin ω D d) hxd
    · refine key d hd ω.upper ?_ _ ?_ hxd
      · exact (hwf.2.elim (fun h => by
          obtain ⟨h1, -⟩ := h
          intro y hy; simp [upper, h1, translate] at hy) (fun h => h.2.2.2.1))
      · rw [content_add, content_origin, content_supplementalShift]; ring
  have hsurj : ∀ k : ℤ, (∃ j : ℤ, m ≤ j ∧ j ≤ M ∧ c0 ≤ k - j * q ∧ k - j * q ≤ c0 + q + w - 1) →
      k ∈ contents (ω.compose D) := by
    rintro k ⟨j, hj1, hj2, hk1, hk2⟩
    have hjD : j ∈ contents D := (hcD j).mpr ⟨hj1, hj2⟩
    obtain ⟨i0, hi0⟩ := mem_contents_iff.mp hjD
    have hkE : k - j * q ∈ contents ω.E := by
      rw [hcE, Finset.mem_Icc]; constructor <;> omega
    obtain ⟨i1, hi1⟩ := mem_contents_iff.mp hkE
    rw [mem_contents_iff]
    refine ⟨i1 + (ω.origin D (i0, i0 + j)).1, ?_⟩
    rw [mem_compose hDne]
    left
    refine ⟨(i0, i0 + j), hi0, ?_⟩
    rw [mem_translate]
    have e : (i1 + (ω.origin D (i0, i0 + j)).1, i1 + (ω.origin D (i0, i0 + j)).1 + k) -
        ω.origin D (i0, i0 + j) = (i1, i1 + (k - j * q)) := by
      have hc := content_origin ω D (i0, i0 + j)
      simp only [content] at hc
      ext
      · simp
      · simp only [Prod.snd_sub]
        have : (i0 + j - i0) * q = j * q := by ring
        rw [← hqdef] at hc
        omega
    rw [e]; exact hi1
  have hfin : contents (ω.compose D) = Finset.Icc (c0 + m * q) (c0 + M * q + q + w - 1) := by
    ext k
    rw [Finset.mem_Icc]
    constructor
    · intro hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨d, hd, h1, h2⟩ := hmem x hx
      have hd' := (hcD (content d)).mp (content_mem_contents hd)
      have e1 : m * q ≤ content d * q := mul_le_mul_of_nonneg_right hd'.1 hq.le
      have e2 : content d * q ≤ M * q := mul_le_mul_of_nonneg_right hd'.2 hq.le
      constructor <;> omega
    · rintro ⟨h1, h2⟩
      apply hsurj
      by_cases hc : k < c0 + M * q
      · refine ⟨(k - c0) / q, ?_, ?_, ?_, ?_⟩
        · have : m * q ≤ k - c0 := by omega
          exact (Int.le_ediv_iff_mul_le hq).mpr this
        · have : (k - c0) / q < M := by
            apply (Int.ediv_lt_iff_lt_mul hq).mpr; omega
          omega
        · have := Int.mul_ediv_add_emod (k - c0) q
          have := Int.emod_nonneg (k - c0) hq.ne'
          have := Int.emod_lt_of_pos (k - c0) hq
          nlinarith
        · have := Int.mul_ediv_add_emod (k - c0) q
          have := Int.emod_nonneg (k - c0) hq.ne'
          have := Int.emod_lt_of_pos (k - c0) hq
          nlinarith
      · refine ⟨M, ?_, le_refl _, by omega, by omega⟩
        have := minContent_le (maxContent_mem hDne |> fun h => by
          exact h)
        omega
  have hspF : span (ω.compose D) = (contents (ω.compose D)).card := rfl
  rw [hspF, hfin, Int.card_Icc]
  have : 0 ≤ c0 + M * q + q + w - 1 + 1 - (c0 + m * q) := by nlinarith
  rw [Int.toNat_of_nonneg this]
  have h5 : (M - m + 1) = (span D : ℤ) := by omega
  rw [← h5]
  ring

theorem sameRibbon_of_ordinary {ω : MarkedInner} (h : ¬ ω.case.IsMixed) (D : Diagram)
    (d : ℤ × ℤ) : ¬ ω.SameRibbon D d := by
  unfold SameRibbon
  unfold AttachCase.IsMixed at h
  rintro ⟨-, h2⟩
  revert h2
  cases hc : ω.case <;> simp_all

theorem compose_of_ordinary {D : Diagram} (hD : D.Nonempty) {ω : MarkedInner}
    (h : ¬ ω.case.IsMixed) {x : ℤ × ℤ} :
    x ∈ ω.compose D ↔ ∃ d ∈ D, x ∈ translate (ω.origin D d) ω.E := by
  rw [mem_compose hD]
  constructor
  · rintro (h1 | ⟨d, _, hr, _⟩)
    · exact h1
    · exact absurd hr (sameRibbon_of_ordinary h D d)
  · exact Or.inl

/-- A cell-coordinate gauge identity for the two ordinary attachment conventions. This is
supporting material from the sibling project and is not used to prove `eq:composition-span`. -/
theorem compose_antitranspose_gauge {D : Diagram} (hD : D.Nonempty) {ωa ωb : MarkedInner}
    (hE : ωa.E = ωb.E) (ha : ωa.case = .a) (hb : ωb.case = .b) (hv : ωa.v = ωb.v + eCell) :
    ωa.compose D = ωb.compose (antitranspose D) := by
  have hDa : (antitranspose D).Nonempty := hD.image _
  have hna : ¬ ωa.case.IsMixed := by simp [AttachCase.IsMixed, ha]
  have hnb : ¬ ωb.case.IsMixed := by simp [AttachCase.IsMixed, hb]
  ext x
  rw [compose_of_ordinary hD hna, compose_of_ordinary hDa hnb]
  constructor
  · rintro ⟨d, hd, hx⟩
    refine ⟨(-d.2, -d.1), mem_antitranspose.mpr (by simpa using hd), ?_⟩
    have e : ωb.origin (antitranspose D) (-d.2, -d.1) = ωa.origin D d := by
      unfold origin
      rw [ha, hb]
      simp only [hv]
      ext
      · simp [content, eCell]; ring
      · simp [content, eCell]; ring
    rw [e, ← hE]; exact hx
  · rintro ⟨d', hd', hx⟩
    have hd'' := mem_antitranspose.mp hd'
    refine ⟨(-d'.2, -d'.1), hd'', ?_⟩
    have e : ωb.origin (antitranspose D) d' = ωa.origin D (-d'.2, -d'.1) := by
      unfold origin
      rw [ha, hb]
      simp only [hv]
      ext
      · simp [content, eCell]; ring
      · simp [content, eCell]; ring
    rw [e] at hx; rw [hE]; exact hx

end MarkedInner

/-! ## Charts and the common final factor -/

/-- The marked inner `ω` translated by `t`: `E` and `W₋` move, the displacement is unchanged
(so `W₊` moves too). -/
def MarkedInner.translateBy (t : ℤ × ℤ) (ω : MarkedInner) : MarkedInner where
  E := translate t ω.E
  W := translate t ω.W
  v := ω.v
  case := ω.case

/-- Two marked inners are equal up to translation. -/
def MarkedInner.EquivTranslate (ω₁ ω₂ : MarkedInner) : Prop := ∃ t, ω₂ = ω₁.translateBy t

/-- A chart: an outer diagram `D` and a marked inner `ω`, presenting `D ∘_ω E`. -/
structure Chart where
  /-- The outer diagram. -/
  D : Diagram
  /-- The marked inner. -/
  ω : MarkedInner

namespace Chart

/-- The diagram presented by the chart. -/
def parent (χ : Chart) : Diagram := χ.ω.compose χ.D

/-- The period `q = c(v)` of a chart. -/
def period (χ : Chart) : ℤ := χ.ω.period

/-- The chart is *legal* (the mark satisfies I–IV, with `D` nonempty and connected skew) and
*proper* (both factors connected, with at least two cells). -/
def IsProperLegal (χ : Chart) : Prop :=
  IsConnectedSkew χ.D ∧ 2 ≤ χ.D.card ∧ 2 ≤ χ.ω.E.card ∧ χ.ω.IsLegal

/-- `F` has the chart `χ`: `F` is the parent of `χ` up to translation. -/
def IsChartOf (χ : Chart) (F : Diagram) : Prop := ∃ t, F = translate t χ.parent

end Chart

/-- A common-final-factor relation on diagrams. This is supporting material from the sibling
project and is not asserted by the target paper's composition-span result. -/
def HasCommonFinalFactor {R : Type*} (s : Diagram → R) (F₁ F₂ : Diagram) : Prop :=
  (¬ ∃ t, F₂ = translate t F₁) ∧
  ∃ χ₁ χ₂ : Chart, χ₁.IsProperLegal ∧ χ₂.IsProperLegal ∧ χ₁.IsChartOf F₁ ∧
    χ₂.IsChartOf F₂ ∧
    (χ₁.ω.EquivTranslate χ₂.ω ∨ χ₁.ω.rotate.EquivTranslate χ₂.ω) ∧ s χ₁.D = s χ₂.D

/-- The fiber `𝓕(ω, Q)` of a marked inner `ω` with `|E| ≥ 2` over an outer value `Q`,
parametrized by an outer function `s`: the diagrams `A ∘_ω E` and `A ∘_{ω*} E*` for
connected `A` with `|A| ≥ 2` and `s A = Q`, as cell sets (the representatives of the
composition formula; the paper reads them up to translation). -/
def fiber {R : Type*} (s : Diagram → R) (ω : MarkedInner) (Q : R) : Set Diagram :=
  {F | ∃ A : Diagram, IsConnectedSkew A ∧ 2 ≤ A.card ∧ s A = Q ∧
    (F = ω.compose A ∨ F = ω.rotate.compose A)}

/-! ## Checked examples -/

section Examples

open MarkedInner

/-- The outer domino of the chart figure. -/
def domino : Diagram := {(0, 0), (0, 1)}

/-- A nontrivial composite example for the copied marked-inner definitions. -/
example : compose domino chartFigureInner =
    {(-3, 3), (-3, 4), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (0, 0)} := by
  decide +kernel

/-- The span law for the figure: `N_F = r q + w = 2 * 3 + 2 = 8`. -/
example : span (compose domino chartFigureInner) = 8 := by decide +kernel

/-- `(7) = (3) ∘_{(1)} (3) = (2) ∘_{(1)} (4)`. -/
example : compose (skewOf [3] []) rowInnerThree = skewOf [7] [] := by decide +kernel
example : compose (skewOf [2] []) rowInnerFour = skewOf [7] [] := by decide +kernel

/-- The gauge example `(2) ∘_{ω_a} E = (1, 1) ∘_{ω_b} E`, after normalization. -/
example : normalize (compose (skewOf [2] []) gaugeInnerA) =
    normalize (compose (skewOf [1, 1] []) gaugeInnerB) := by decide +kernel

/-- The hook `(2, 1)` with its singleton case-(d) mark: `(3) ∘_ω (2, 1)` has seven cells. -/
example : (compose (skewOf [3] []) hookInner).card = 7 := by decide +kernel

example : normalize (compose (skewOf [3] []) hookInner) =
    normalize {(-3, 2), (-3, 3), (-2, 1), (-2, 2), (-1, 0), (-1, 1), (0, 0)} := by
  decide +kernel

example : normalize (compose (skewOf [2, 2] []) hookInner) =
    normalize {(-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-1, 0), (-1, 1),
      (0, 0)} := by
  decide +kernel

/-- A worked instance of the copied cell-coordinate gauge identity. -/
example : compose (skewOf [2] []) gaugeInnerA =
    compose (antitranspose (skewOf [2] [])) gaugeInnerB :=
  compose_antitranspose_gauge (by decide) rfl rfl rfl (by decide)

end Examples

end SkewGluing
