/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/NoRightRibbons.lean
import SkewMarkedFactor.Gluing.Local
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.RibbonEnds

/-!
# No ribbon of size `μ q` is removable on the right: southeast-justified composites

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`) and «Diagonal geometry» (`lem:gluing-local`): the case-(d)
form of thesis Lemma 5.5.2 and of Lemma 5.5.7 (iii) (`OlsonHarris2024HopfApplications`), in the
rotated form needed for case (c).

For a diagram `F` presented by classes of diagonals (`ClassRows`) whose last rows are
`fHi j a = j p + h a` (the case-(d) composites, `mix_classRows`), with `h (w - 1) - h w = 1`
(the lower cap for a vertical lower attachment) and `h (q - 1) - h 0 - p = 0` (the upper cap for a
horizontal upper attachment), no ribbon of size `μ q`, `μ > 0`, is removable on the right from `F`.
The proof reads the ends of such a ribbon off the periodic word of steps `h_{n-1} - h_n` of the
southeast border (`rightRibbon_endpoints`).

* `rightRibbons_eq_empty_of_classRows`: the statement for presented diagrams;
* `corner_no_rightRibbons_d`: for a legal case-(d) mark and a connected outer, no ribbon of size
  `μ q` is removable on the right from `D ∘_ω E`;
* `leftRibbons_rotate_eq_empty`: left ribbons of `X*` are the rotations of the right ribbons of
  `X`;
* `corner_no_leftRibbons`: case (c), by rotation (`D ∘_ω E = (D* ∘_{ω*} E*)*`).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

open MarkedInner

/-- **No ribbon of size `μ q` is removable on the right** from a diagram with periodic southeast
border data.  See the module docstring. -/
theorem rightRibbons_eq_empty_of_classRows {F : Diagram} {c0 q w m M p : ℤ}
    {fLo fHi : ℤ → ℤ → ℤ} {h : ℤ → ℤ} (hc : ClassRows F c0 q w m M fLo fHi) (hw1 : 1 ≤ w)
    (hfHi : ∀ j a, fHi j a = j * p + h a) (hF1 : h (w - 1) - h w = 1)
    (hF2 : h (q - 1) - h 0 - p = 0) {Q μ : ℕ} (hQ : (Q : ℤ) = q) (hμ : 0 < μ) :
    rightRibbons F (μ * Q) = ∅ := by
  have hq := hc.hq
  have hwq := hc.hwq
  have hmM := hc.hmM
  have hFs := hc.isConnectedSkew
  refine Finset.eq_empty_of_forall_notMem fun Y hY => ?_
  have hN : 0 < μ * Q := Nat.mul_pos hμ (by omega)
  obtain ⟨n0, hn0, hn1, hS, hT, -⟩ := rightRibbon_endpoints hFs hN hY
  have hNz : ((μ * Q : ℕ) : ℤ) = μ * q := by push_cast; rw [hQ]
  rw [hNz] at hn1 hT
  have hdh : ∀ j a, 0 ≤ a → a < q → ValidClass m M w j a →
      diagHi F (c0 + (j * q + a)) = j * p + h a := by
    intro j a h0 h1 hv
    rw [hc.diagHi_eq h0 h1 hv, hfHi]
  have hcont : ∀ n, n ∈ contents F ↔ c0 + m * q ≤ n ∧ n ≤ c0 + M * q + q + w - 1 := by
    intro n
    obtain ⟨j, a, h0, h1, rfl⟩ := hc.decomp n
    rw [hc.mem_contents h0 h1, hc.valid_iff h0 h1]
    constructor <;> rintro ⟨x, y⟩ <;> exact ⟨by omega, by omega⟩
  obtain ⟨J, a, ha0, haq, hn0e⟩ := hc.decomp n0
  rw [hn0e] at hn0
  have hv0 : ValidClass m M w J a := (hc.mem_contents ha0 haq).mp hn0
  by_cases hm : n0 + μ * q ∈ contents F
  · -- the next window start is still in `F`
    have hT' : diagHi F (n0 + μ * q - 1) - diagHi F (n0 + μ * q) = 1 := by
      rcases hT with hT | hT
      · exact absurd (by simpa [hNz] using hm) hT
      · simpa [hNz] using hT
    have e1 : n0 + μ * q = c0 + ((J + μ) * q + a) := by rw [hn0e]; ring
    have hv1 : ValidClass m M w (J + μ) a := by
      rw [e1] at hm; exact (hc.mem_contents ha0 haq).mp hm
    rw [e1] at hT'
    by_cases ha : 1 ≤ a
    · have e2 : c0 + ((J + μ) * q + a) - 1 = c0 + ((J + μ) * q + (a - 1)) := by ring
      have hv2 : ValidClass m M w (J + μ) (a - 1) := by
        unfold ValidClass at hv1 ⊢
        omega
      rw [e2, hdh _ _ (by omega) (by omega) hv2, hdh _ _ ha0 haq hv1] at hT'
      have hv3 : ValidClass m M w J (a - 1) := by
        unfold ValidClass at hv0 ⊢
        omega
      have hmem : n0 - 1 ∈ contents F := by
        have e3 : n0 - 1 = c0 + (J * q + (a - 1)) := by rw [hn0e]; ring
        rw [e3]; exact (hc.mem_contents (by omega) (by omega)).mpr hv3
      rcases hS with hS | hS
      · exact hS hmem
      · have e3 : n0 - 1 = c0 + (J * q + (a - 1)) := by rw [hn0e]; ring
        rw [e3, hdh _ _ (by omega) (by omega) hv3, hn0e, hdh _ _ ha0 haq hv0] at hS
        omega
    · have ha' : a = 0 := by omega
      subst ha'
      have e2 : c0 + ((J + μ) * q + 0) - 1 = c0 + ((J + μ - 1) * q + (q - 1)) := by ring
      have hn1' : n0 + μ * q - 1 ∈ contents F := by
        have := hn1; rwa [show n0 + ↑μ * q - 1 = n0 + μ * q - 1 from rfl] at this
      have hv2 : ValidClass m M w (J + μ - 1) (q - 1) := by
        rw [e1, e2] at hn1'
        exact (hc.mem_contents (by omega) (by omega)).mp hn1'
      rw [e2, hdh _ _ (by omega) (by omega) hv2, hdh _ _ ha0 haq hv1] at hT'
      have : (J + μ - 1) * p = (J + μ) * p - p := by ring
      omega
  · -- `n0 + μ q` is just above the greatest content
    have hn1' := (hcont _).mp hn1
    have hn0' := (hcont _).mp hn0
    have hlt : c0 + M * q + q + w - 1 < n0 + μ * q := by
      by_contra hle
      exact hm ((hcont _).mpr ⟨by nlinarith, by omega⟩)
    have hn0w : n0 = c0 + ((M + 1 - μ) * q + w) := by
      have : (μ : ℤ) * q ≥ 0 := by positivity
      nlinarith
    have hJa : J * q + a = (M + 1 - μ) * q + w := by omega
    have hJ : J = M + 1 - μ ∧ a = w := by
      have h3 : (J - (M + 1 - μ)) * q = w - a := by linarith
      have hz : J - (M + 1 - μ) = 0 := by
        rcases lt_trichotomy (J - (M + 1 - μ)) 0 with hh | hh | hh
        · nlinarith
        · exact hh
        · nlinarith
      constructor <;> nlinarith
    obtain ⟨hJ1, hJ2⟩ := hJ
    subst hJ1
    rw [hJ2] at hv0 hn0e ha0 haq
    have hv3 : ValidClass m M w (M + 1 - μ) (w - 1) := by
      unfold ValidClass at hv0 ⊢
      have : (1 : ℤ) ≤ μ := by exact_mod_cast hμ
      omega
    have hmem : n0 - 1 ∈ contents F := by
      have e3 : n0 - 1 = c0 + ((M + 1 - μ) * q + (w - 1)) := by rw [hn0e]; ring
      rw [e3]; exact (hc.mem_contents (by omega) (by omega)).mpr hv3
    rcases hS with hS | hS
    · exact hS hmem
    · have e3 : n0 - 1 = c0 + ((M + 1 - μ) * q + (w - 1)) := by rw [hn0e]; ring
      rw [e3, hdh _ _ (by omega) (by omega) hv3, hn0e, hdh _ _ ha0 haq hv0] at hS
      omega

/-- A ribbon removable on the left from `X*` rotates to a ribbon removable on the right from
`X` of the same size. -/
theorem rotate_mem_rightRibbons {X Y : Diagram} {N : ℕ}
    (hY : Y ∈ leftRibbons (rotate X) N) : rotate Y ∈ rightRibbons X N := by
  obtain ⟨hYX, hcard, hrib, hdown⟩ := mem_leftRibbons.mp hY
  rw [mem_rightRibbons]
  have hinj : Function.Injective (fun x : ℤ × ℤ => -x) := neg_injective
  refine ⟨?_, ?_, ⟨isConnectedSkew_rotate hrib.1, ?_⟩, ?_⟩
  · intro z hz
    rw [mem_rotate] at hz
    have := hYX hz
    rw [mem_rotate, neg_neg] at this
    exact this
  · unfold rotate
    rw [Finset.card_image_of_injective _ hinj]
    exact hcard
  · unfold rotate
    rw [Finset.card_image_of_injective _ hinj]
    have := hrib.2
    rw [← span_rotate (D := Y)] at this
    unfold rotate at this
    exact this
  · refine ⟨?_, fun x hx y hy h1 h2 => ?_⟩
    · intro z hz
      rw [mem_rotate] at hz
      have := hYX hz
      rw [mem_rotate, neg_neg] at this
      exact this
    · rw [mem_rotate] at hy ⊢
      have hxr : -x ∈ rotate X := by rw [mem_rotate, neg_neg]; exact hx
      exact hdown.2 (-x) hxr (-y) hy (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)

/-- If no ribbon of size `N` is removable on the right from `X`, none is removable on the left
from `X*`. -/
theorem leftRibbons_rotate_eq_empty {X : Diagram} {N : ℕ} (h : rightRibbons X N = ∅) :
    leftRibbons (rotate X) N = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun Y hY => ?_
  have := rotate_mem_rightRibbons hY
  rw [h] at this
  exact absurd this (Finset.notMem_empty _)

/-- **Thesis Lemma 5.5.2 and Lemma 5.5.7 (iii), case (d).**  For a legal case-(d) mark and a
connected outer, no ribbon of size `μ q`, `μ > 0`, is removable on the right from `D ∘_ω E`. -/
theorem corner_no_rightRibbons_d {ω : MarkedInner} (hω : ω.IsLegal) (hd : ω.case = .d)
    {D : Diagram} (hD : IsConnectedSkew D) {μ : ℕ} (hμ : 0 < μ) :
    rightRibbons (ω.compose D) (μ * ω.period.toNat) = ∅ := by
  have hW : ω.W.Nonempty := by
    rcases hω.1.2 with h | h
    · have := h.2.2
      rw [hd] at this
      cases this
    · exact h.1
  have h : ω.IsLegalNonempty := ⟨hω, hW⟩
  obtain ⟨s, t, hph⟩ := h.exists_phases
  have hlt := h.phases_lt (Or.inr hd) hph
  have hc := mix_classRows h hD hd hph hlt
  obtain ⟨⟨-, hc1, -⟩, ⟨hc2, hc3, -⟩⟩ := d_caps h hd
  have hq := h.width_lt_period
  have hw := h.width_pos
  refine rightRibbons_eq_empty_of_classRows hc hw (h := ω.hi) (p := ω.rowShift)
    (fun j a => rfl) (by omega) ?_ (Q := ω.period.toNat) ?_ hμ
  · unfold MarkedInner.dHi at hc2
    simp only [zero_add] at hc2
    omega
  · omega

/-- **Thesis Lemma 5.5.2 and Lemma 5.5.7 (iii), case (c).**  For a legal mark of case (c) and a
connected outer, no ribbon of size `m q` is removable on the left from `D ∘_ω E`: by rotation
(`D ∘_ω E = (D* ∘_{ω*} E*)*`) this is `corner_no_rightRibbons_d` for the rotated mark, of case
(d). -/
theorem corner_no_leftRibbons {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c)
    {D : Diagram} (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) :
    leftRibbons (ω.compose D) (m * ω.period.toNat) = ∅ := by
  have hrot := MarkedInner.compose_rotate_c hc hD.2.1
  rw [hrot]
  exact leftRibbons_rotate_eq_empty (corner_no_rightRibbons_d (isLegal_rotate hω)
    (rotate_case_d hc) (isConnectedSkew_rotate hD) hm)

end Corner

end Plan

end SkewMarkedFactor.Gluing
