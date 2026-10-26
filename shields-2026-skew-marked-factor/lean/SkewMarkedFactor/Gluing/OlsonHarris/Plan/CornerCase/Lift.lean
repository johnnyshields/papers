/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Lift.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.OuterWindows

/-!
# The lifts of the ribbons of the outer

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.5.7 (i)–(ii) and the
bijection of Lemma 5.5.11 (`OlsonHarris2024HopfApplications`), for a legal mark of case (c).

The ribbons of size `m q` removable on the right from `D ∘_ω E` are the border strips
`liftR A`, `A` a ribbon of size `m` removable on the right from `D`, and `liftL A`, `A` removable
on the left, the strip starting `q (c(A) - c(D)) + s` (respectively `+ t`) diagonals above the
least content of the composite; the lifts are injective with disjoint images
(`corner_ribbon_bijection`).  The proof reads the windows of the southeast word of the composite
(`window_classification`, `corner_word_facts`) and of the extended words of the outer
(`right_window_D`, `left_window_D_mem`).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

open MarkedInner

/-- The border-strip conditions of a window read on the southeast word. -/
theorem window_conds_iff_word {X : Diagram} (hX : IsConnectedSkew X) {N : ℕ} (hN : 0 < N)
    (k0 : ℤ) :
    (minContent X + k0 ∈ contents X ∧ minContent X + k0 + N - 1 ∈ contents X ∧
      (minContent X + k0 - 1 ∉ contents X ∨
        diagHi X (minContent X + k0 - 1) = diagHi X (minContent X + k0)) ∧
      (minContent X + k0 + N ∉ contents X ∨
        diagHi X (minContent X + k0 + N - 1) - diagHi X (minContent X + k0 + N) = 1)) ↔
    (0 ≤ k0 ∧ k0 + N ≤ span X ∧ (k0 = 0 ∨ wordB X k0 = 0) ∧
      (k0 + N = span X ∨ wordB X (k0 + N) = 1)) := by
  simp only [contents_iff hX]
  have e1 : minContent X + k0 + N - 1 = minContent X + (k0 + N) - 1 := by ring
  have e2 : minContent X + k0 + N = minContent X + (k0 + N) := by ring
  rw [e1, e2]
  unfold wordB bitB
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by omega, by omega, ?_, ?_⟩
    · by_cases hk : k0 = 0
      · left; exact hk
      · right
        rcases h3 with h3 | h3
        · exfalso; omega
        · omega
    · by_cases hk : k0 + N = span X
      · left; exact hk
      · right
        rcases h4 with h4 | h4
        · exfalso; omega
        · omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rcases h3 with h3 | h3
      · left; omega
      · right; omega
    · rcases h4 with h4 | h4
      · left; omega
      · right; omega

/-- The border strip of the composite `F = D ∘_ω E` of size `m q` that starts
`q (c(A) - c(D)) + off` diagonals above the least content of `F`, lifting the ribbon `A` of the
outer (`c` is the least content). -/
def cornerLift (ω : MarkedInner) (D : Diagram) (m : ℕ) (off : ℤ) (A : Diagram) : Diagram :=
  windowRibbon (ω.compose D) (minContent ω.E + minContent A * ω.period + off) (m * ω.period.toNat)

variable {ω : MarkedInner} {D : Diagram}

theorem cornerLift_inj {off : ℤ} {m : ℕ} (hm : 0 < m) (hq : 0 < ω.period) {A A' : Diagram}
    (h : cornerLift ω D m off A = cornerLift ω D m off A') : minContent A = minContent A' := by
  have hN : 0 < m * ω.period.toNat := Nat.mul_pos hm (by omega)
  have := windowRibbon_inj hN h
  have h2 : minContent A * ω.period = minContent A' * ω.period := by omega
  exact mul_right_cancel₀ hq.ne' h2

/-- **The ribbons of size `m q` removable on the right from the corner composite are the lifts of
the ribbons of size `m` removable from the outer** (thesis Lemma 5.5.7 (i)–(ii), Lemma 5.5.11):
those removable on the right lift at the offset `s`, those removable on the left at the offset
`t`; the lifts are injective with disjoint images. -/
theorem corner_ribbon_bijection (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) {m : ℕ} (hm : 0 < m) :
    rightRibbons (ω.compose D) (m * ω.period.toNat) =
        (rightRibbons D m).image (cornerLift ω D m s) ∪
          (leftRibbons D m).image (cornerLift ω D m t) ∧
      Set.InjOn (cornerLift ω D m s) (rightRibbons D m) ∧
      Set.InjOn (cornerLift ω D m t) (leftRibbons D m) ∧
      Disjoint ((rightRibbons D m).image (cornerLift ω D m s))
        ((leftRibbons D m).image (cornerLift ω D m t)) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inl hcc) hph
  have hq0 : 0 < ω.period := by omega
  have hr1 : 1 ≤ (span D : ℤ) := by
    have : 0 < span D := Finset.card_pos.mpr (hD.2.1.image _)
    omega
  have hF : IsConnectedSkew (ω.compose D) := h.1.isConnectedSkew_compose hD
  have hminF := h.minContent_compose' hD
  have hspanF : (span (ω.compose D) : ℤ) = (span D : ℤ) * ω.period + ω.widthZ := by
    rw [h.span_compose_eq hD, span_eq_of_isConnectedSkew hD]
  have hN0 : 0 < m * ω.period.toNat := Nat.mul_pos hm (by omega)
  have hNcast : ((m * ω.period.toNat : ℕ) : ℤ) = m * ω.period := by
    push_cast; rw [Int.toNat_of_nonneg hq0.le]
  obtain ⟨hPs, hPt, hPer, hFq, hFw⟩ := corner_word_facts h hD hcc hph
  have hcl := fun {k : ℤ} => window_classification (q := ω.period) (w := ω.widthZ) (s := s)
    (t := t) (r := (span D : ℤ)) (m := (m : ℤ)) (B := wordB (ω.compose D)) (Bx := Bext D)
    (Ax := Aext D) hq0 hw hq ht1 hlt hs2 hr1 (by exact_mod_cast hm) (Bext_span hD)
    (Aext_zero D) (Aext_span hD) hPs hPt hPer hFq hFw (k := k)
  -- the windows of the composite
  have hwin : ∀ k0 : ℤ, windowRibbon (ω.compose D) (minContent (ω.compose D) + k0)
      (m * ω.period.toNat) ∈ rightRibbons (ω.compose D) (m * ω.period.toNat) ↔
      ((∃ j, k0 = j * ω.period + s ∧ 0 ≤ j ∧ j + m ≤ span D ∧ Bext D j = 0 ∧
          Bext D (j + m) = 1) ∨
        (∃ j, k0 = j * ω.period + t ∧ 0 ≤ j ∧ j + m ≤ span D ∧ Aext D j = 1 ∧
          Aext D (j + m) = 0)) := by
    intro k0
    rw [windowRibbon_mem_rightRibbons_iff hF hN0, window_conds_iff_word hF hN0 k0, hNcast,
      hspanF, ← hcl]
  have hmemF : ∀ Y, Y ∈ rightRibbons (ω.compose D) (m * ω.period.toNat) ↔
      ∃ k0 : ℤ, Y = windowRibbon (ω.compose D) (minContent (ω.compose D) + k0)
        (m * ω.period.toNat) ∧
        ((∃ j, k0 = j * ω.period + s ∧ 0 ≤ j ∧ j + m ≤ span D ∧ Bext D j = 0 ∧
          Bext D (j + m) = 1) ∨
        (∃ j, k0 = j * ω.period + t ∧ 0 ≤ j ∧ j + m ≤ span D ∧ Aext D j = 1 ∧
          Aext D (j + m) = 0)) := by
    intro Y
    constructor
    · intro hY
      obtain ⟨n0, -, -, -, -, hYw⟩ := rightRibbon_endpoints hF hN0 hY
      refine ⟨n0 - minContent (ω.compose D), ?_, ?_⟩
      · rw [hYw]; congr 1; ring
      · rw [← hwin]
        have e : minContent (ω.compose D) + (n0 - minContent (ω.compose D)) = n0 := by ring
        rw [e, ← hYw]; exact hY
    · rintro ⟨k0, rfl, hk⟩
      exact (hwin k0).mpr hk
  -- the lifts as border strips
  have hliftR : ∀ A ∈ rightRibbons D m, ∃ j : ℤ, 0 ≤ j ∧ j + m ≤ span D ∧ Bext D j = 0 ∧
      Bext D (j + m) = 1 ∧ minContent A = minContent D + j ∧
      cornerLift ω D m s A = windowRibbon (ω.compose D)
        (minContent (ω.compose D) + (j * ω.period + s)) (m * ω.period.toNat) := by
    intro A hA
    obtain ⟨j, h1, h2, h3, h4, h5⟩ := right_window_D_exists hD hm hA
    have hmc : minContent A = minContent D + j := by
      rw [h5, minContent_windowRibbon hm]
    refine ⟨j, h1, h2, h3, h4, hmc, ?_⟩
    unfold cornerLift
    rw [hmc, hminF]
    congr 1; ring
  have hliftL : ∀ A ∈ leftRibbons D m, ∃ j : ℤ, 0 ≤ j ∧ j + m ≤ span D ∧ Aext D j = 1 ∧
      Aext D (j + m) = 0 ∧ minContent A = minContent D + j ∧
      cornerLift ω D m t A = windowRibbon (ω.compose D)
        (minContent (ω.compose D) + (j * ω.period + t)) (m * ω.period.toNat) := by
    intro A hA
    obtain ⟨j, h1, h2, h3, h4, h5⟩ := left_window_D_mem hD hm hA
    refine ⟨j, h1, h2, h3, h4, h5, ?_⟩
    unfold cornerLift
    rw [h5, hminF]
    congr 1; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext Y
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image, hmemF]
    constructor
    · rintro ⟨k0, rfl, hk | hk⟩
      · obtain ⟨j, rfl, h1, h2, h3, h4⟩ := hk
        left
        have hmem : windowRibbon D (minContent D + j) m ∈ rightRibbons D m :=
          (right_window_D hD hm h1 h2).mpr ⟨h3, h4⟩
        refine ⟨_, hmem, ?_⟩
        obtain ⟨j', a1, a2, a3, a4, a5, a6⟩ := hliftR _ hmem
        rw [a6]
        have : minContent (windowRibbon D (minContent D + j) m) = minContent D + j :=
          minContent_windowRibbon hm
        rw [this] at a5
        have : j' = j := by omega
        rw [this]
      · obtain ⟨j, rfl, h1, h2, h3, h4⟩ := hk
        right
        obtain ⟨A, hA, hmc⟩ := left_window_D_exists hD hm h1 h2 h3 h4
        refine ⟨A, hA, ?_⟩
        obtain ⟨j', a1, a2, a3, a4, a5, a6⟩ := hliftL A hA
        rw [a6]
        have : j' = j := by omega
        rw [this]
    · rintro (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩)
      · obtain ⟨j, a1, a2, a3, a4, a5, a6⟩ := hliftR A hA
        exact ⟨_, a6, Or.inl ⟨j, rfl, a1, a2, a3, a4⟩⟩
      · obtain ⟨j, a1, a2, a3, a4, a5, a6⟩ := hliftL A hA
        exact ⟨_, a6, Or.inr ⟨j, rfl, a1, a2, a3, a4⟩⟩
  · intro A hA A' hA' hAA'
    obtain ⟨j, -, -, -, -, a5, -⟩ := hliftR A hA
    obtain ⟨j', -, -, -, -, a5', -⟩ := hliftR A' hA'
    have := cornerLift_inj hm hq0 hAA'
    obtain ⟨j1, -, -, -, -, e1⟩ := right_window_D_exists hD hm hA
    obtain ⟨j2, -, -, -, -, e2⟩ := right_window_D_exists hD hm hA'
    have m1 : minContent A = minContent D + j1 := by rw [e1, minContent_windowRibbon hm]
    have m2 : minContent A' = minContent D + j2 := by rw [e2, minContent_windowRibbon hm]
    have : j1 = j2 := by omega
    subst this
    rw [e1, e2]
  · intro A hA A' hA' hAA'
    exact left_window_D_unique hD hm hA hA' (cornerLift_inj hm hq0 hAA')
  · rw [Finset.disjoint_left]
    intro Y hY1 hY2
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hY1
    obtain ⟨A', hA', hAA'⟩ := Finset.mem_image.mp hY2
    have hN := windowRibbon_inj hN0 (by unfold cornerLift at hAA'; exact hAA')
    have e : (minContent A - minContent A') * ω.period = t - s := by
      have : minContent A' * ω.period + t = minContent A * ω.period + s := by linarith
      nlinarith
    rcases le_or_gt 0 (minContent A - minContent A') with hu | hu
    · nlinarith
    · nlinarith

end Corner

end Plan

end SkewMarkedFactor.Gluing
