import SkewGluing.OlsonHarris.Plan.CornerCase.FWindows
import SkewGluing.OlsonHarris.Plan.CornerCase.NoRightRibbons

/-!
# Ribbons of the outer, read on its extended words

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`) as used
in thesis Lemma 5.5.7 (`OlsonHarris2024HopfApplications`).

For a connected skew diagram `D` of span `r` and `m > 0`:

* the ribbons of size `m` removable on the right are the border strips `windowRibbon D (c + j) m`
  with `c = minContent D`, `0 ≤ j`, `j + m ≤ r`, `Bext_j = 0` and `Bext_{j+m} = 1`
  (`right_window_D`);
* the ribbons of size `m` removable on the left are determined by their least content `c + j`, and
  occur exactly for `0 ≤ j`, `j + m ≤ r`, `Aext_j = 1`, `Aext_{j+m} = 0`
  (`left_window_D_mem`, `left_window_D_exists`, `left_window_D_unique`), by rotation.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

variable {D : Diagram}

theorem Bext_zero (D : Diagram) : Bext D 0 = 0 := by simp [Bext]

theorem Bext_span (hD : IsConnectedSkew D) : Bext D (span D) = 1 := by
  have : 0 < span D := Finset.card_pos.mpr (hD.2.1.image _)
  simp [Bext]
  omega

theorem Bext_of_mem {j : ℤ} (h1 : 1 ≤ j) (h2 : j < span D) : Bext D j = wordB D j := by
  have : j ≠ 0 := by omega
  have : j ≠ (span D : ℤ) := by omega
  simp [Bext, *]

theorem Aext_zero (D : Diagram) : Aext D 0 = 1 := by simp [Aext]

theorem Aext_span (hD : IsConnectedSkew D) : Aext D (span D) = 0 := by
  have : 0 < span D := Finset.card_pos.mpr (hD.2.1.image _)
  simp [Aext]
  omega

theorem Aext_of_mem {j : ℤ} (h1 : 1 ≤ j) (h2 : j < span D) : Aext D j = wordA D j := by
  have : j ≠ 0 := by omega
  have : j ≠ (span D : ℤ) := by omega
  simp [Aext, *]

theorem contents_iff (hD : IsConnectedSkew D) {k : ℤ} :
    k ∈ contents D ↔ minContent D ≤ k ∧ k < minContent D + span D := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hsp := span_eq_of_isConnectedSkew hD
  rw [hs.mem_contents_iff]
  omega

/-- **Right ribbons of the outer.** -/
theorem right_window_D (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) {j : ℤ} (hj0 : 0 ≤ j)
    (hjm : j + m ≤ span D) :
    windowRibbon D (minContent D + j) m ∈ rightRibbons D m ↔
      Bext D j = 0 ∧ Bext D (j + m) = 1 := by
  have hsp : (0 : ℤ) < span D := by
    have : 0 < span D := Finset.card_pos.mpr (hD.2.1.image _)
    omega
  rw [windowRibbon_mem_rightRibbons_iff hD hm]
  simp only [contents_iff hD]
  constructor
  · rintro ⟨-, -, hS, hT⟩
    constructor
    · by_cases hj : j = 0
      · subst hj; exact Bext_zero D
      · rw [Bext_of_mem (by omega) (by omega)]
        rcases hS with hS | hS
        · exfalso; omega
        · unfold wordB bitB
          rw [show minContent D + j - 1 = minContent D + j - 1 from rfl] at hS
          omega
    · by_cases hj : j + m = span D
      · rw [hj]; exact Bext_span hD
      · rw [Bext_of_mem (by omega) (by omega)]
        rcases hT with hT | hT
        · exfalso; omega
        · unfold wordB bitB
          have e : minContent D + (j + m) - 1 = minContent D + j + m - 1 := by ring
          have e2 : minContent D + (j + m) = minContent D + j + m := by ring
          rw [e, e2]
          exact hT
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, by omega, ?_, ?_⟩
    · by_cases hj : j = 0
      · left; omega
      · right
        rw [Bext_of_mem (by omega) (by omega)] at h1
        unfold wordB bitB at h1
        omega
    · by_cases hj : j + m = span D
      · left; omega
      · right
        rw [Bext_of_mem (by omega) (by omega)] at h2
        unfold wordB bitB at h2
        have e : minContent D + (j + m) - 1 = minContent D + j + m - 1 := by ring
        have e2 : minContent D + (j + m) = minContent D + j + m := by ring
        rw [e, e2] at h2
        exact h2

/-- Every ribbon of size `m` removable on the right from the outer is a border strip on a window
with `Bext_j = 0`, `Bext_{j+m} = 1`. -/
theorem right_window_D_exists (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) {A : Diagram}
    (hA : A ∈ rightRibbons D m) :
    ∃ j : ℤ, 0 ≤ j ∧ j + m ≤ span D ∧ Bext D j = 0 ∧ Bext D (j + m) = 1 ∧
      A = windowRibbon D (minContent D + j) m := by
  obtain ⟨n0, h1, h2, -, -, hY⟩ := rightRibbon_endpoints hD hm hA
  rw [contents_iff hD] at h1 h2
  have e : minContent D + (n0 - minContent D) = n0 := by ring
  have hmem : windowRibbon D (minContent D + (n0 - minContent D)) m ∈ rightRibbons D m := by
    rw [e, ← hY]; exact hA
  have := (right_window_D hD hm (j := n0 - minContent D) (by omega) (by omega)).mp hmem
  exact ⟨n0 - minContent D, by omega, by omega, this.1, this.2, by rw [e]; exact hY⟩

theorem minContent_windowRibbon {X : Diagram} {n0 : ℤ} {N : ℕ} (hN : 0 < N) :
    minContent (windowRibbon X n0 N) = n0 :=
  minContent_eq_of (contents_windowRibbon.mpr ⟨le_rfl, by omega⟩)
    fun k hk => (contents_windowRibbon.mp hk).1

theorem maxContent_windowRibbon {X : Diagram} {n0 : ℤ} {N : ℕ} (hN : 0 < N) :
    maxContent (windowRibbon X n0 N) = n0 + N - 1 :=
  maxContent_eq_of (contents_windowRibbon.mpr ⟨by omega, by omega⟩)
    fun k hk => by have := (contents_windowRibbon.mp hk).2; omega

/-- A ribbon removable on the right from `X*` rotates to a ribbon removable on the left from `X`. -/
theorem rotate_mem_leftRibbons {X Y : Diagram} {N : ℕ} (hY : Y ∈ rightRibbons (rotate X) N) :
    rotate Y ∈ leftRibbons X N := by
  obtain ⟨hYX, hcard, hrib, hup⟩ := mem_rightRibbons.mp hY
  rw [mem_leftRibbons]
  have hinj : Function.Injective (fun x : ℤ × ℤ => -x) := neg_injective
  have hsub : ∀ z, z ∈ rotate Y → z ∈ X := by
    intro z hz
    rw [mem_rotate] at hz
    have := hYX hz
    rw [mem_rotate, neg_neg] at this
    exact this
  refine ⟨hsub, ?_, ⟨isConnectedSkew_rotate hrib.1, ?_⟩, hsub, fun x hx y hy h1 h2 => ?_⟩
  · unfold rotate
    rw [Finset.card_image_of_injective _ hinj]
    exact hcard
  · unfold rotate
    rw [Finset.card_image_of_injective _ hinj]
    have := hrib.2
    rw [← span_rotate (D := Y)] at this
    unfold rotate at this
    exact this
  · rw [mem_rotate] at hy ⊢
    have hxr : -x ∈ rotate X := by rw [mem_rotate, neg_neg]; exact hx
    exact hup.2 (-x) hxr (-y) hy (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)

theorem Bext_rotate (hD : IsConnectedSkew D) {k : ℤ} (hk0 : 0 ≤ k) (hk1 : k ≤ span D) :
    Bext (rotate D) k = Aext D (span D - k) := by
  have hDr := isConnectedSkew_rotate hD
  have hsp : span (rotate D) = span D := span_rotate
  have hpos : 0 < span D := Finset.card_pos.mpr (hD.2.1.image _)
  by_cases h0 : k = 0
  · subst h0
    rw [Bext_zero, sub_zero]
    exact (Aext_span hD).symm
  · by_cases h1 : k = span D
    · rw [h1, sub_self, Aext_zero]
      have := Bext_span hDr
      rw [hsp] at this
      exact this
    · rw [Bext_of_mem (D := rotate D) (by omega) (by rw [hsp]; omega),
        Aext_of_mem (by omega) (by omega)]
      have := wordB_rotate hD k
      exact this

/-- A ribbon of size `m` removable on the left from `D` is the rotation of a border strip of `D*`
on a window of diagonals, and its least content is read off the window. -/
theorem left_eq_rotate_window (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) {A : Diagram}
    (hA : A ∈ leftRibbons D m) :
    ∃ j' : ℤ, 0 ≤ j' ∧ j' + m ≤ span D ∧ Bext (rotate D) j' = 0 ∧
      Bext (rotate D) (j' + m) = 1 ∧
      rotate A = windowRibbon (rotate D) (minContent (rotate D) + j') m := by
  have hDr := isConnectedSkew_rotate hD
  have hA' : rotate A ∈ rightRibbons (rotate D) m :=
    rotate_mem_rightRibbons (X := rotate D) (by rwa [rotate_rotate])
  obtain ⟨j', h1, h2, h3, h4, h5⟩ := right_window_D_exists hDr hm hA'
  rw [span_rotate] at h2
  exact ⟨j', h1, h2, h3, h4, h5⟩

theorem minContent_of_rotate_window (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) {A : Diagram}
    {j' : ℤ} (hA : rotate A = windowRibbon (rotate D) (minContent (rotate D) + j') m) :
    minContent A = minContent D + (span D - m - j') := by
  have hne : D.Nonempty := hD.2.1
  have hmax : maxContent D = minContent D + span D - 1 := by
    have := span_eq_of_isConnectedSkew hD
    omega
  have hAr : A = rotate (windowRibbon (rotate D) (minContent (rotate D) + j') m) := by
    rw [← hA, rotate_rotate]
  have hwne : (windowRibbon (rotate D) (minContent (rotate D) + j') m).Nonempty :=
    Finset.card_pos.mp (by rw [card_windowRibbon]; exact hm)
  rw [hAr, minContent_rotate hwne, maxContent_windowRibbon hm, minContent_rotate hne, hmax]
  ring

/-- **Left ribbons of the outer.** -/
theorem left_window_D_mem (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) {A : Diagram}
    (hA : A ∈ leftRibbons D m) :
    ∃ j : ℤ, 0 ≤ j ∧ j + m ≤ span D ∧ Aext D j = 1 ∧ Aext D (j + m) = 0 ∧
      minContent A = minContent D + j := by
  obtain ⟨j', h1, h2, h3, h4, h5⟩ := left_eq_rotate_window hD hm hA
  refine ⟨span D - m - j', by omega, by omega, ?_, ?_, minContent_of_rotate_window hD hm h5⟩
  · have := Bext_rotate hD (k := j' + m) (by omega) h2
    rw [h4] at this
    rw [this]; congr 1; ring
  · have := Bext_rotate hD (k := j') h1 (by omega)
    rw [h3] at this
    rw [this]; congr 1; ring

theorem left_window_D_exists (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) {j : ℤ} (hj0 : 0 ≤ j)
    (hjm : j + m ≤ span D) (h1 : Aext D j = 1) (h2 : Aext D (j + m) = 0) :
    ∃ A ∈ leftRibbons D m, minContent A = minContent D + j := by
  have hDr := isConnectedSkew_rotate hD
  have hsp : span (rotate D) = span D := span_rotate
  set j' : ℤ := span D - m - j with hj'
  have b1 : Bext (rotate D) j' = 0 := by
    rw [Bext_rotate hD (by omega) (by omega)]
    have : (span D : ℤ) - j' = j + m := by omega
    rw [this]; exact h2
  have b2 : Bext (rotate D) (j' + m) = 1 := by
    rw [Bext_rotate hD (by omega) (by omega)]
    have : (span D : ℤ) - (j' + m) = j := by omega
    rw [this]; exact h1
  have hW : windowRibbon (rotate D) (minContent (rotate D) + j') m ∈ rightRibbons (rotate D) m :=
    (right_window_D hDr hm (by omega) (by omega)).mpr ⟨b1, b2⟩
  refine ⟨rotate (windowRibbon (rotate D) (minContent (rotate D) + j') m),
    rotate_mem_leftRibbons hW, ?_⟩
  rw [minContent_of_rotate_window hD hm (A := rotate (windowRibbon (rotate D)
    (minContent (rotate D) + j') m)) (j' := j') (by rw [rotate_rotate])]
  congr 1; omega

theorem left_window_D_unique (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) {A A' : Diagram}
    (hA : A ∈ leftRibbons D m) (hA' : A' ∈ leftRibbons D m)
    (h : minContent A = minContent A') : A = A' := by
  obtain ⟨j1, -, -, -, -, e1⟩ := left_eq_rotate_window hD hm hA
  obtain ⟨j2, -, -, -, -, e2⟩ := left_eq_rotate_window hD hm hA'
  have m1 := minContent_of_rotate_window hD hm e1
  have m2 := minContent_of_rotate_window hD hm e2
  have : j1 = j2 := by omega
  subst this
  exact rotate_injective (e1.trans e2.symm)

end Corner

end Plan

end SkewGluing
