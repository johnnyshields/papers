/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/Ribbons.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Defs

/-!
# Ribbons removable on the left from a connected skew diagram

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-bits`, `def:gluing-graph`): the border-strip description underlying thesis
Lemma 5.2.8 and Lemma 5.4.2 (`OlsonHarris2024HopfApplications`).

For a connected skew diagram `X` with first-row function `ℓ = diagLo X` and steps
`A_c = ℓ_{c-1} - ℓ_c ∈ {0, 1}`, a ribbon of size `n` removable on the left is a segment of the
northwest border, one cell `(ℓ_c, ℓ_c + c)` on each of the contents `c₀ ≤ c < c₀ + n`, such that
the step entering the segment is a north step (`A_{c₀} = 1`) or `c₀` is the least content, and the
step leaving it is an east step (`A_{c₀+n} = 0`) or `c₀ + n - 1` is the greatest content
(`mem_leftRibbons_iff_segment`).  Its height is `ℓ_{c₀} - ℓ_{c₀+n-1}`.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewMarkedFactor.Gluing

namespace Plan

open scoped Classical

/-- The segment of the northwest border of `X` on the contents `c₀ ≤ c < c₀ + n`. -/
def segment (X : Diagram) (c0 : ℤ) (n : ℕ) : Diagram :=
  (Finset.Ico c0 (c0 + n)).image fun c => (diagLo X c, diagLo X c + c)

theorem mem_segment {X : Diagram} {c0 : ℤ} {n : ℕ} {z : ℤ × ℤ} :
    z ∈ segment X c0 n ↔ ∃ c, c0 ≤ c ∧ c < c0 + n ∧ z = (diagLo X c, diagLo X c + c) := by
  unfold segment
  simp only [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨c, ⟨h1, h2⟩, rfl⟩; exact ⟨c, h1, h2, rfl⟩
  · rintro ⟨c, h1, h2, rfl⟩; exact ⟨c, ⟨h1, h2⟩, rfl⟩

theorem card_segment (X : Diagram) (c0 : ℤ) (n : ℕ) : (segment X c0 n).card = n := by
  unfold segment
  rw [Finset.card_image_of_injective, Int.card_Ico]
  · omega
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    omega

theorem content_of_mem_segment {X : Diagram} {c0 : ℤ} {n : ℕ} {z : ℤ × ℤ}
    (hz : z ∈ segment X c0 n) : c0 ≤ content z ∧ content z < c0 + n := by
  obtain ⟨c, h1, h2, rfl⟩ := mem_segment.mp hz
  simp only [content]
  constructor <;> omega

theorem contents_segment (X : Diagram) (c0 : ℤ) (n : ℕ) :
    contents (segment X c0 n) = Finset.Ico c0 (c0 + n) := by
  ext k
  rw [mem_contents_iff, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi⟩
    have := content_of_mem_segment hi
    simp only [content] at this
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    exact ⟨diagLo X k, mem_segment.mpr ⟨k, h1, h2, rfl⟩⟩

theorem span_segment (X : Diagram) (c0 : ℤ) (n : ℕ) : span (segment X c0 n) = n := by
  unfold span
  rw [contents_segment, Int.card_Ico]
  omega

section Steps

variable {X : Diagram}

theorem bitA_mem (hs : HasDiagonalShape X) {c : ℤ} (h1 : c ∈ contents X)
    (h0 : c - 1 ∈ contents X) : bitA X c = 0 ∨ bitA X c = 1 := by
  have := (hs.2.2.2.1 c h1 h0).1
  simpa using this

/-- Along the northwest border, the first row decreases by at most one per content. -/
theorem diagLo_step (hs : HasDiagonalShape X) {a b : ℤ} (ha : a ∈ contents X)
    (hb : b ∈ contents X) (hab : a ≤ b) :
    diagLo X b ≤ diagLo X a ∧ diagLo X a ≤ diagLo X b + (b - a) :=
  hs.diagLo_anti ha hb hab

/-- If the first row drops by the full amount between `a` and `b`, every step is a north step. -/
theorem bitA_eq_one_of_drop (hs : HasDiagonalShape X) {a b : ℤ} (ha : a ∈ contents X)
    (hb : b ∈ contents X) (hab : a ≤ b) (h : diagLo X a = diagLo X b + (b - a)) :
    ∀ i, a < i → i ≤ b → bitA X i = 1 := by
  induction b, hab using Int.leInduction with
  | base => intro i h1 h2; omega
  | succ n hn ih =>
    intro i h1 h2
    have hn' : n ∈ contents X := hs.between ha hb hn (by omega)
    have hbit := bitA_mem hs hb (by simpa using hn')
    have hstep := diagLo_step hs ha hn' hn
    have hdef : bitA X (n + 1) = diagLo X n - diagLo X (n + 1) := by
      simp [bitA]
    by_cases hi : i = n + 1
    · subst hi; omega
    · exact ih hn' (by omega) i h1 (by omega)

/-- If the first row does not change between `a` and `b`, every step is an east step. -/
theorem bitA_eq_zero_of_flat (hs : HasDiagonalShape X) {a b : ℤ} (ha : a ∈ contents X)
    (hb : b ∈ contents X) (hab : a ≤ b) (h : diagLo X a = diagLo X b) :
    ∀ i, a < i → i ≤ b → bitA X i = 0 := by
  induction b, hab using Int.leInduction with
  | base => intro i h1 h2; omega
  | succ n hn ih =>
    intro i h1 h2
    have hn' : n ∈ contents X := hs.between ha hb hn (by omega)
    have hbit := bitA_mem hs hb (by simpa using hn')
    have hstep := diagLo_step hs ha hn' hn
    have hstep2 := diagLo_step hs hn' hb (by omega : n ≤ n + 1)
    have hdef : bitA X (n + 1) = diagLo X n - diagLo X (n + 1) := by
      simp [bitA]
    by_cases hi : i = n + 1
    · subst hi; omega
    · exact ih hn' (by omega) i h1 (by omega)

end Steps

section Segment

variable {X : Diagram}

theorem segment_subset (hs : HasDiagonalShape X) {c0 : ℤ} {n : ℕ} (h1 : minContent X ≤ c0)
    (h2 : c0 + n - 1 ≤ maxContent X) : segment X c0 n ⊆ X := by
  intro z hz
  obtain ⟨c, hc1, hc2, rfl⟩ := mem_segment.mp hz
  have hk : c ∈ contents X := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
  have := diagLo_mem hk
  simpa [add_comm] using this

theorem hasDiagonalShape_segment (hs : HasDiagonalShape X) {c0 : ℤ} {n : ℕ} (hn : 0 < n)
    (h1 : minContent X ≤ c0) (h2 : c0 + n - 1 ≤ maxContent X) :
    HasDiagonalShape (segment X c0 n) := by
  have hrow : ∀ k, c0 ≤ k → k < c0 + n →
      diagLo (segment X c0 n) k = diagLo X k ∧ diagHi (segment X c0 n) k = diagLo X k := by
    intro k hk1 hk2
    have hcell : (diagLo X k, diagLo X k + k) ∈ segment X c0 n :=
      mem_segment.mpr ⟨k, hk1, hk2, rfl⟩
    have huniq : ∀ i, (i, i + k) ∈ segment X c0 n → i = diagLo X k := by
      intro i hi
      obtain ⟨c, hc1, hc2, hz⟩ := mem_segment.mp hi
      simp only [Prod.mk.injEq] at hz
      have hkc : c = k := by omega
      subst hkc
      omega
    constructor
    · exact diagLo_eq_of (l := diagLo X k) hcell fun i hi => (huniq i hi).ge
    · exact diagHi_eq_of (l := diagLo X k) hcell fun i hi => (huniq i hi).le
  have hcont : ∀ k, k ∈ contents (segment X c0 n) ↔ c0 ≤ k ∧ k < c0 + n := by
    intro k; rw [contents_segment, Finset.mem_Ico]
  refine ⟨⟨(diagLo X c0, diagLo X c0 + c0), mem_segment.mpr ⟨c0, le_rfl, by omega, rfl⟩⟩, ?_, ?_,
    ?_, ?_⟩
  · intro x hx y hy k hk
    rw [Finset.mem_Icc] at hk
    have hx' := content_of_mem_segment hx
    have hy' := content_of_mem_segment hy
    rw [hcont]
    omega
  · intro x hx y hy hxy i hi
    obtain ⟨c, hc1, hc2, rfl⟩ := mem_segment.mp hx
    obtain ⟨c', hc1', hc2', rfl⟩ := mem_segment.mp hy
    simp only [content] at hxy
    have hcc : c = c' := by omega
    subst hcc
    simp only [Finset.mem_Icc] at hi
    have : i = diagLo X c := by omega
    subst this
    have e : content (diagLo X c, diagLo X c + c) = c := by simp [content]
    rw [e]
    exact mem_segment.mpr ⟨c, hc1, hc2, rfl⟩
  · intro k hk hk1
    rw [hcont] at hk hk1
    obtain ⟨r1, r2⟩ := hrow k hk.1 hk.2
    obtain ⟨r1', r2'⟩ := hrow (k - 1) hk1.1 hk1.2
    have hkX : k ∈ contents X := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
    have hk1X : k - 1 ∈ contents X := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
    have := bitA_mem hs hkX hk1X
    have hb := (hs.2.2.2.1 k hkX hk1X)
    simp only [bitA, bitB, r1, r2, r1', r2'] at this hb ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro k hk _
    rw [hcont] at hk
    obtain ⟨r1, r2⟩ := hrow k hk.1 hk.2
    rw [r1, r2]

end Segment

section Main

variable {X : Diagram}

/-- A segment of the northwest border that starts after a north step (or at the least content) and
ends before an east step (or at the greatest content) is a downset. -/
theorem isDownsetIn_segment (hs : HasDiagonalShape X) {c0 : ℤ} {n : ℕ}
    (h1 : minContent X ≤ c0) (h2 : c0 + n - 1 ≤ maxContent X)
    (hstart : c0 = minContent X ∨ bitA X c0 = 1)
    (hend : c0 + n - 1 = maxContent X ∨ bitA X (c0 + n) = 0) :
    IsDownsetIn X (segment X c0 n) := by
  refine ⟨segment_subset hs h1 h2, ?_⟩
  intro x hx y hy hxy1 hxy2
  obtain ⟨c, hc1, hc2, rfl⟩ := mem_segment.mp hy
  obtain ⟨i, j⟩ := x
  simp only at hxy1 hxy2
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = j - i := ⟨_, rfl⟩
  have hxe : (i, j) = (i, i + k) := by rw [hk]; ext <;> simp
  rw [hxe] at hx ⊢
  obtain ⟨hkc, hlo, -⟩ := hs.mem_iff.mp hx
  have hcc : c ∈ contents X := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
  rcases lt_trichotomy k c with hlt | heq | hgt
  · -- `x` lies on a diagonal before `c`
    have hstep := diagLo_step hs hkc hcc hlt.le
    have hrow : i = diagLo X k := by omega
    have hflat : diagLo X k = diagLo X c := by omega
    have hzero := bitA_eq_zero_of_flat hs hkc hcc hlt.le hflat
    have hk0 : c0 ≤ k := by
      by_contra hlt0
      rcases hstart with hst | hst
      · have := minContent_le hkc; omega
      · have := hzero c0 (by omega) (by omega); omega
    rw [hrow]
    exact mem_segment.mpr ⟨k, hk0, by omega, rfl⟩
  · subst heq
    have : i = diagLo X k := by omega
    rw [this]
    exact mem_segment.mpr ⟨k, hc1, hc2, rfl⟩
  · -- `x` lies on a diagonal after `c`
    have hstep := diagLo_step hs hcc hkc hgt.le
    have hdrop : diagLo X c = diagLo X k + (k - c) := by omega
    have hrow : i = diagLo X k := by omega
    have hone := bitA_eq_one_of_drop hs hcc hkc hgt.le hdrop
    have hk1 : k < c0 + n := by
      by_contra hge
      rcases hend with hen | hen
      · have := le_maxContent hkc; omega
      · have := hone (c0 + n) (by omega) (by omega); omega
    rw [hrow]
    exact mem_segment.mpr ⟨k, by omega, hk1, rfl⟩

/-- **Ribbons removable on the left from a connected skew diagram are border segments.** -/
theorem mem_leftRibbons_iff_segment (hX : IsConnectedSkew X) {n : ℕ} (hn : 0 < n) {Y : Diagram} :
    Y ∈ leftRibbons X n ↔ ∃ c0 : ℤ, minContent X ≤ c0 ∧ c0 + n - 1 ≤ maxContent X ∧
      (c0 = minContent X ∨ bitA X c0 = 1) ∧
      (c0 + n - 1 = maxContent X ∨ bitA X (c0 + n) = 0) ∧ Y = segment X c0 n := by
  have hs := isConnectedSkew_iff_diagonal.mp hX
  constructor
  · intro hY
    rw [mem_leftRibbons] at hY
    obtain ⟨hYX, hcard, hrib, hdown⟩ := hY
    have hsY := isConnectedSkew_iff_diagonal.mp hrib.1
    set c0 := minContent Y with hc0
    have hYne : Y.Nonempty := hrib.1.2.1
    have hspan : span Y = n := by rw [← hrib.2]; exact hcard
    have hmaxY : maxContent Y = c0 + n - 1 := by
      have h1 : contents Y = Finset.Icc (minContent Y) (maxContent Y) := hsY.contents_eq
      have h2 : span Y = (Finset.Icc (minContent Y) (maxContent Y)).card := by
        unfold span; rw [h1]
      rw [Int.card_Icc] at h2
      have hle : minContent Y ≤ maxContent Y := minContent_le (maxContent_mem hYne)
      omega
    have hinj : Set.InjOn content (Y : Set (ℤ × ℤ)) := by
      have : (Y.image content).card = Y.card := by
        unfold span at hspan; unfold contents at hspan; omega
      exact Finset.card_image_iff.mp this
    -- every cell of `Y` is the border cell of its diagonal
    have hborder : ∀ y ∈ Y, y = (diagLo X (content y), diagLo X (content y) + content y) := by
      intro y hy
      obtain ⟨i, j⟩ := y
      obtain ⟨k, hk⟩ : ∃ k : ℤ, k = j - i := ⟨_, rfl⟩
      have hye : (i, j) = (i, i + k) := by rw [hk]; ext <;> simp
      have hyX := hYX hy
      rw [hye] at hyX
      obtain ⟨hkc, hlo, hhi⟩ := hs.mem_iff.mp hyX
      have hck : content (i, j) = k := by simp [content, hk]
      rw [hck]
      by_contra hne
      have hgt : diagLo X k < i := by
        rcases lt_or_eq_of_le hlo with h | h
        · exact h
        · exfalso; exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
      have hzX : (i - 1, i - 1 + k) ∈ X := hs.mem_iff.mpr ⟨hkc, by omega, by omega⟩
      have hzY : (i - 1, i - 1 + k) ∈ Y :=
        hdown.2 _ hzX (i, j) hy (by change i - 1 ≤ i; omega) (by change i - 1 + k ≤ j; omega)
      have := hinj hzY hy (by simp [content, hk])
      simp only [Prod.mk.injEq] at this
      omega
    have hsub : Y ⊆ segment X c0 n := by
      intro y hy
      have hcy : content y ∈ contents Y := content_mem_contents hy
      rw [hsY.mem_contents_iff] at hcy
      rw [hborder y hy]
      exact mem_segment.mpr ⟨content y, by omega, by omega, rfl⟩
    have hYeq : Y = segment X c0 n :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_segment, hcard])
    have hmin : c0 ∈ contents X := by
      have : c0 ∈ contents Y := minContent_mem hYne
      obtain ⟨i, hi⟩ := mem_contents_iff.mp this
      exact mem_contents_iff.mpr ⟨i, hYX hi⟩
    have hmax : c0 + n - 1 ∈ contents X := by
      have : maxContent Y ∈ contents Y := maxContent_mem hYne
      obtain ⟨i, hi⟩ := mem_contents_iff.mp this
      rw [hmaxY] at hi
      exact mem_contents_iff.mpr ⟨i, hYX hi⟩
    have hmin' := hs.mem_contents_iff.mp hmin
    have hmax' := hs.mem_contents_iff.mp hmax
    refine ⟨c0, hmin'.1, hmax'.2, ?_, ?_, hYeq⟩
    · by_cases hc : c0 = minContent X
      · exact Or.inl hc
      · right
        have hcm1 : c0 - 1 ∈ contents X := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
        have hb := bitA_mem hs hmin hcm1
        rcases hb with hb | hb
        · exfalso
          have hy : (diagLo X c0, diagLo X c0 + c0) ∈ Y := by
            rw [hYeq]; exact mem_segment.mpr ⟨c0, le_rfl, by omega, rfl⟩
          have hz : (diagLo X c0, diagLo X c0 + (c0 - 1)) ∈ X := by
            have := diagLo_mem hcm1
            have e : diagLo X (c0 - 1) = diagLo X c0 := by unfold bitA at hb; omega
            rw [e] at this
            convert this using 2
          have hzY : (diagLo X c0, diagLo X c0 + (c0 - 1)) ∈ Y :=
            hdown.2 _ hz _ hy (by change diagLo X c0 ≤ diagLo X c0; omega)
              (by change diagLo X c0 + (c0 - 1) ≤ diagLo X c0 + c0; omega)
          have hcz : content (diagLo X c0, diagLo X c0 + (c0 - 1)) ∈ contents Y :=
            content_mem_contents hzY
          rw [hsY.mem_contents_iff] at hcz
          simp only [content] at hcz
          omega
        · exact hb
    · by_cases hc : c0 + n - 1 = maxContent X
      · exact Or.inl hc
      · right
        have hc1 : c0 + n ∈ contents X := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
        have hcm1 : c0 + n - 1 ∈ contents X := hmax
        have hb := bitA_mem hs hc1 (by simpa using hcm1)
        rcases hb with hb | hb
        · exact hb
        · exfalso
          have hy : (diagLo X (c0 + n - 1), diagLo X (c0 + n - 1) + (c0 + n - 1)) ∈ Y := by
            rw [hYeq]; exact mem_segment.mpr ⟨c0 + n - 1, by omega, by omega, rfl⟩
          have hz : (diagLo X (c0 + n), diagLo X (c0 + n) + (c0 + n)) ∈ X := by
            have := diagLo_mem hc1
            convert this using 2
          have hzY : (diagLo X (c0 + n), diagLo X (c0 + n) + (c0 + n)) ∈ Y :=
            hdown.2 _ hz _ hy
              (by change diagLo X (c0 + n) ≤ diagLo X (c0 + n - 1); unfold bitA at hb; omega)
              (by change diagLo X (c0 + n) + (c0 + n) ≤ diagLo X (c0 + n - 1) + (c0 + n - 1)
                  unfold bitA at hb; omega)
          have hcz : content (diagLo X (c0 + n), diagLo X (c0 + n) + (c0 + n)) ∈ contents Y :=
            content_mem_contents hzY
          rw [hsY.mem_contents_iff] at hcz
          simp only [content] at hcz
          omega
  · rintro ⟨c0, h1, h2, hst, hen, rfl⟩
    rw [mem_leftRibbons]
    have hseg := hasDiagonalShape_segment hs hn h1 h2
    refine ⟨segment_subset hs h1 h2, card_segment X c0 n, ⟨?_, ?_⟩,
      isDownsetIn_segment hs h1 h2 hst hen⟩
    · exact isConnectedSkew_iff_diagonal.mpr hseg
    · rw [card_segment, span_segment]

end Main

section Height

variable {X : Diagram}

theorem exists_diagLo_eq (hs : HasDiagonalShape X) {v : ℤ} :
    ∀ d : ℕ, ∀ c : ℤ, c ∈ contents X → c + d ∈ contents X → diagLo X (c + d) ≤ v →
      v ≤ diagLo X c → ∃ c', c ≤ c' ∧ c' ≤ c + d ∧ diagLo X c' = v := by
  intro d
  induction d with
  | zero =>
    intro c _ _ h1 h2
    have h3 : v = diagLo X c := by simpa using le_antisymm h2 (by simpa using h1)
    exact ⟨c, le_rfl, by simp, h3.symm⟩
  | succ d ih =>
    intro c hc hcd h1 h2
    have hc1 : c + 1 ∈ contents X := hs.between hc hcd (by omega) (by omega)
    have hstep := diagLo_step hs hc hc1 (by omega)
    by_cases hv : v ≤ diagLo X (c + 1)
    · obtain ⟨c', a, b, e⟩ := ih (c + 1) hc1 (by
        have : c + 1 + (d : ℤ) = c + ((d + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [this]; exact hcd) (by
        have : c + 1 + (d : ℤ) = c + ((d + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [this]; exact h1) hv
      exact ⟨c', by omega, by push_cast; omega, e⟩
    · exact ⟨c, le_rfl, by omega, by omega⟩

theorem ribbonHeight_segment (hs : HasDiagonalShape X) {c0 : ℤ} {n : ℕ} (hn : 0 < n)
    (h1 : minContent X ≤ c0) (h2 : c0 + n - 1 ≤ maxContent X) :
    (ribbonHeight (segment X c0 n) : ℤ) = diagLo X c0 - diagLo X (c0 + n - 1) := by
  have hc0 : c0 ∈ contents X := hs.mem_contents_iff.mpr ⟨h1, by omega⟩
  have hc1 : c0 + n - 1 ∈ contents X := hs.mem_contents_iff.mpr ⟨by omega, h2⟩
  have hstep := diagLo_step hs hc0 hc1 (by omega)
  have hrows : (segment X c0 n).image Prod.fst =
      Finset.Icc (diagLo X (c0 + n - 1)) (diagLo X c0) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨c, hc1', hc2', rfl⟩ := mem_segment.mp hz
      have a1 : c ∈ contents X := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
      have s1 := diagLo_step hs hc0 a1 hc1'
      have s2 := diagLo_step hs a1 hc1 (by omega)
      simp only
      omega
    · rintro ⟨hv1, hv2⟩
      obtain ⟨c', a, b, e⟩ := exists_diagLo_eq hs (v := v) (n - 1) c0 hc0
        (by have : c0 + ((n - 1 : ℕ) : ℤ) = c0 + n - 1 := by omega
            rw [this]; exact hc1)
        (by have : c0 + ((n - 1 : ℕ) : ℤ) = c0 + n - 1 := by omega
            rw [this]; exact hv1) hv2
      refine ⟨(diagLo X c', diagLo X c' + c'), mem_segment.mpr ⟨c', a, by omega, rfl⟩, ?_⟩
      simpa using e
  unfold ribbonHeight numRows rowSet
  rw [hrows, Int.card_Icc]
  have : 0 ≤ diagLo X c0 - diagLo X (c0 + n - 1) := by omega
  omega

end Height

end Plan

end SkewMarkedFactor.Gluing
