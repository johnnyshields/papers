/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Windows.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.RibbonEnds

/-!
# Ribbons removable on the right are the border strips on windows of diagonals

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the border-strip description of the ribbons removable on the
right (thesis §5.1, used in Lemmas 5.5.2, 5.5.3 and 5.5.7 of `OlsonHarris2024HopfApplications`).

For a connected skew diagram `X` and `N > 0`, a set `Y` is a ribbon of size `N` removable on the
right exactly when it is the border strip `windowRibbon X n₀ N` of the last cells of `N`
consecutive diagonals of `X`, the strip begins at the least content of `X` or after a step
`h_{n₀ - 1} = h_{n₀}` and ends at the greatest content of `X` or before a step
`h_{n₀+N-1} - h_{n₀+N} = 1` (`mem_rightRibbons_iff_window`).  Its height is the number of steps
`h_{j-1} - h_j = 1` inside the strip (`ribbonHeight_windowRibbon`).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

variable {X : Diagram}

theorem mem_contents_window (hs : HasDiagonalShape X) {n0 : ℤ} {N : ℕ} {k : ℤ}
    (h0 : n0 ∈ contents X) (h1 : n0 + N - 1 ∈ contents X) (hk : n0 ≤ k ∧ k < n0 + N) :
    k ∈ contents X :=
  hs.between h0 h1 hk.1 (by omega)

theorem contents_windowRibbon {n0 : ℤ} {N : ℕ} {k : ℤ} :
    k ∈ contents (windowRibbon X n0 N) ↔ n0 ≤ k ∧ k < n0 + N := by
  rw [mem_contents_iff]
  constructor
  · rintro ⟨i, hi⟩
    have := mem_windowRibbon.mp hi
    simp only [content] at this
    omega
  · rintro hk
    refine ⟨diagHi X k, mem_windowRibbon.mpr ⟨?_, ?_, ?_⟩⟩ <;> simp [content] <;> omega

theorem windowRibbon_row {n0 : ℤ} {N : ℕ} {i k : ℤ}
    (h : (i, i + k) ∈ windowRibbon X n0 N) : i = diagHi X k := by
  have := (mem_windowRibbon.mp h).2.2
  simpa [content] using this

/-- The converse of `rightRibbon_endpoints`: a border strip with the stated ends is a ribbon
removable on the right. -/
theorem windowRibbon_mem_rightRibbons (hX : IsConnectedSkew X) {N : ℕ} (hN : 0 < N) {n0 : ℤ}
    (h0 : n0 ∈ contents X) (h1 : n0 + N - 1 ∈ contents X)
    (hS : n0 - 1 ∉ contents X ∨ diagHi X (n0 - 1) = diagHi X n0)
    (hT : n0 + N ∉ contents X ∨ diagHi X (n0 + N - 1) - diagHi X (n0 + N) = 1) :
    windowRibbon X n0 N ∈ rightRibbons X N := by
  have hs := isConnectedSkew_iff_diagonal.mp hX
  have hcw := fun k => contents_windowRibbon (X := X) (n0 := n0) (N := N) (k := k)
  have hrow : ∀ k, n0 ≤ k → k < n0 + N → (diagHi X k, diagHi X k + k) ∈ windowRibbon X n0 N := by
    intro k hk1 hk2
    exact mem_windowRibbon.mpr
      ⟨by simp [content]; omega, by simp [content]; omega, by simp [content]⟩
  have hsub : windowRibbon X n0 N ⊆ X := by
    intro y hy
    obtain ⟨a, b⟩ := y
    have hy' := mem_windowRibbon.mp hy
    simp only [content] at hy'
    have hkX := mem_contents_window hs h0 h1 (k := b - a) ⟨hy'.1, hy'.2.1⟩
    have := diagHi_mem hkX
    rw [← hy'.2.2] at this
    convert this using 2
    omega
  have hdl : ∀ k, n0 ≤ k → k < n0 + N → diagLo (windowRibbon X n0 N) k = diagHi X k := by
    intro k hk1 hk2
    exact diagLo_eq_of (hrow k hk1 hk2) fun i hi => by rw [windowRibbon_row hi]
  have hdh : ∀ k, n0 ≤ k → k < n0 + N → diagHi (windowRibbon X n0 N) k = diagHi X k := by
    intro k hk1 hk2
    exact diagHi_eq_of (hrow k hk1 hk2) fun i hi => by rw [windowRibbon_row hi]
  have hshape : HasDiagonalShape (windowRibbon X n0 N) := by
    refine ⟨⟨_, hrow n0 le_rfl (by omega)⟩, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy k hk
      have hx' := (mem_windowRibbon.mp hx)
      have hy' := (mem_windowRibbon.mp hy)
      rw [Finset.mem_Icc] at hk
      exact (hcw k).mpr ⟨by omega, by omega⟩
    · intro x hx y hy hxy i hi
      have e1 := (mem_windowRibbon.mp hx).2.2
      have e2 := (mem_windowRibbon.mp hy).2.2
      rw [Finset.mem_Icc] at hi
      have : x.1 = y.1 := by rw [e1, e2, hxy]
      have hi' : i = x.1 := by omega
      subst hi'
      have e : (x.1, x.1 + content x) = x := Prod.ext rfl (by simp only [content]; ring)
      rw [e]; exact hx
    · intro k hk hk1
      rw [hcw] at hk hk1
      have hk2 := mem_contents_window hs h0 h1 (k := k) hk
      have hk3 := mem_contents_window hs h0 h1 (k := k - 1) ⟨by omega, by omega⟩
      have := (hs.2.2.2.1 k hk2 hk3).2
      simp only [bitA, bitB, hdl k hk.1 hk.2, hdl (k - 1) (by omega) (by omega),
        hdh k hk.1 hk.2, hdh (k - 1) (by omega) (by omega)] at this ⊢
      exact ⟨this, this⟩
    · intro k hk _
      rw [hcw] at hk
      rw [hdl k hk.1 hk.2, hdh k hk.1 hk.2]
  have hcard := card_windowRibbon X n0 N
  have hspan : span (windowRibbon X n0 N) = N := by
    calc span (windowRibbon X n0 N) = (windowRibbon X n0 N).card := by
          unfold span contents
          refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
          have e1 := (mem_windowRibbon.mp hx).2.2
          have e2 := (mem_windowRibbon.mp hy).2.2
          obtain ⟨a, b⟩ := x
          obtain ⟨c, d⟩ := y
          simp only [content] at hxy e1 e2
          simp only [Prod.mk.injEq]
          rw [hxy] at e1
          constructor <;> omega
      _ = N := hcard
  rw [mem_rightRibbons]
  refine ⟨hsub, hcard, ⟨isConnectedSkew_iff_diagonal.mpr hshape, by omega⟩, hsub, ?_⟩
  -- the upset property
  intro x hx y hy h1x h2x
  obtain ⟨a, b⟩ := y
  obtain ⟨i, c⟩ := x
  simp only at h1x h2x
  have hy' := mem_windowRibbon.mp hy
  simp only [content] at hy'
  obtain ⟨hy1, hy2, hyr⟩ := hy'
  set j := b - a with hj
  have hjX : j ∈ contents X := mem_contents_window hs h0 h1 ⟨hy1, hy2⟩
  have hyX : (a, b) ∈ X := hsub hy
  have hxk : c - i ∈ contents X := content_mem_contents hx
  have anti := fun {u v : ℤ} (hu : u ∈ contents X) (hv : v ∈ contents X) (huv : u ≤ v) =>
    hs.diagHi_anti hu hv huv
  have hXs : IsSkew X := hX.1
  have hwin : n0 ≤ c - i → c - i < n0 + N → i = diagHi X (c - i) →
      (i, c) ∈ windowRibbon X n0 N := by
    intro u1 u2 u3
    exact mem_windowRibbon.mpr ⟨u1, u2, u3⟩
  rcases le_total (i - a) (c - b) with hAB | hAB
  · -- `A ≤ B`: the cell `(a, c)` is on a diagonal at or above `j`
    have hz : (a, c) ∈ X := hXs.mem (a := a) (b := b) (c := i) (d := c) hyX hx h1x h2x
      le_rfl (by omega) h2x le_rfl
    have hzc : c - a ∈ contents X := content_mem_contents hz
    have hz1 : a ≤ diagHi X (c - a) := le_diagHi hz rfl
    have hjz : j ≤ c - a := by omega
    have hz2 := (anti hjX hzc hjz).1
    have hle : c - a < n0 + N := by
      by_contra hge
      have hge' : n0 + N ≤ c - a := by omega
      have hmem : (n0 : ℤ) + N ∈ contents X := hs.between hjX hzc (by omega) hge'
      rcases hT with hT | hT
      · exact hT hmem
      · have p1 := (anti hmem hzc hge').1
        have p2 := (anti hjX h1 (by omega : j ≤ n0 + N - 1)).1
        omega
    have hk : j ≤ c - i := by omega
    have hik := le_diagHi hx (k := c - i) rfl
    have hhk := (anti hjX hxk hk).1
    have hA : i = a := by omega
    subst hA
    exact hwin (by omega) (by omega) (by omega)
  · -- `B ≤ A`: the cell `(i, b)` is on a diagonal at or below `j`
    have hz : (i, b) ∈ X := hXs.mem (a := a) (b := b) (c := i) (d := c) hyX hx h1x h2x
      h1x le_rfl le_rfl h2x
    have hzc : b - i ∈ contents X := content_mem_contents hz
    have hz1 : i ≤ diagHi X (b - i) := le_diagHi hz rfl
    have hjz : b - i ≤ j := by omega
    have hz2 := anti hzc hjX hjz
    have hge : n0 ≤ b - i := by
      by_contra hlt
      have hmem : n0 - 1 ∈ contents X := hs.between hzc hjX (by omega) (by omega)
      rcases hS with hS | hS
      · exact hS hmem
      · have p1 := (anti hzc hmem (by omega : b - i ≤ n0 - 1)).2
        have p2 := (anti h0 hjX (by omega : n0 ≤ j)).2
        have p3 := (anti hmem h0 (by omega : n0 - 1 ≤ n0)).1
        omega
    have hk : c - i ≤ j := by omega
    have hik := le_diagHi hx (k := c - i) rfl
    have hhk := (anti hxk hjX hk).2
    have hB : c = b := by omega
    subst hB
    exact hwin (by omega) (by omega) (by omega)

theorem windowRibbon_inj {n0 n0' : ℤ} {N : ℕ} (hN : 0 < N)
    (h : windowRibbon X n0 N = windowRibbon X n0' N) : n0 = n0' := by
  have a1 : n0 ∈ contents (windowRibbon X n0 N) := (contents_windowRibbon).mpr ⟨le_rfl, by omega⟩
  have a2 : n0' ∈ contents (windowRibbon X n0' N) := (contents_windowRibbon).mpr ⟨le_rfl, by omega⟩
  rw [h] at a1
  rw [← h] at a2
  have b1 := (contents_windowRibbon.mp a1)
  have b2 := (contents_windowRibbon.mp a2)
  omega

/-- **Border strips and ribbons removable on the right.**  For `N > 0`, the border strip on the
diagonals `n₀, …, n₀ + N - 1` is a ribbon removable on the right exactly when it has the stated
ends, and every ribbon removable on the right is such a strip. -/
theorem windowRibbon_mem_rightRibbons_iff (hX : IsConnectedSkew X) {N : ℕ} (hN : 0 < N)
    {n0 : ℤ} :
    windowRibbon X n0 N ∈ rightRibbons X N ↔ n0 ∈ contents X ∧ n0 + N - 1 ∈ contents X ∧
      (n0 - 1 ∉ contents X ∨ diagHi X (n0 - 1) = diagHi X n0) ∧
      (n0 + N ∉ contents X ∨ diagHi X (n0 + N - 1) - diagHi X (n0 + N) = 1) := by
  constructor
  · intro h
    obtain ⟨n1, a1, a2, a3, a4, hY⟩ := rightRibbon_endpoints hX hN h
    have := windowRibbon_inj hN hY
    subst this
    exact ⟨a1, a2, a3, a4⟩
  · rintro ⟨a1, a2, a3, a4⟩
    exact windowRibbon_mem_rightRibbons hX hN a1 a2 a3 a4

end Corner

end Plan

end SkewMarkedFactor.Gluing
