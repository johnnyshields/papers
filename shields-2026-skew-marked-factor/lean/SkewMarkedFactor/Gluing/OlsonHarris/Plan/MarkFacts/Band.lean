/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/MarkFacts/Band.lean
import SkewMarkedFactor.Gluing.Diagram

/-!
# Skew diagrams cut by a band of contents

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local`), the
diagonal criterion for skew diagrams: three general facts used to show that the hatted shapes of
a legal mark are skew.

* `isSkew_hat`: for a skew diagram `F`, the cells `x` of `F` with `x + e ∈ F` form a skew
  diagram.
* `isSkew_filter_band`: a skew diagram cut to the contents `[lo, hi]` stays skew provided no
  two adjacent cells of the diagram straddle the cut.
* `hasDiagonalShape_of_intervals`: a diagram whose diagonals are the given row intervals with
  steps in `{0, 1}` and singleton end diagonals has diagonal shape.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan.MarkFacts

/-- For a skew diagram `F`, the cells `x ∈ F` with `x + e ∈ F` form a skew diagram. -/
theorem isSkew_hat {F : Diagram} (hF : IsSkew F) :
    IsSkew (F.filter fun x => x + eCell ∈ F) := by
  intro x hx y hy h1 h2 i hi j hj
  rw [Finset.mem_filter] at hx hy ⊢
  simp only [Finset.mem_Icc] at hi hj
  refine ⟨hF x hx.1 y hy.1 h1 h2 i (Finset.mem_Icc.mpr hi) j (Finset.mem_Icc.mpr hj), ?_⟩
  have := hF (x + eCell) hx.2 (y + eCell) hy.2 (by simp [eCell, h1]) (by simp [eCell, h2])
    (i + 1) (Finset.mem_Icc.mpr ⟨by simp [eCell]; omega, by simp [eCell]; omega⟩) (j + 1)
    (Finset.mem_Icc.mpr ⟨by simp [eCell]; omega, by simp [eCell]; omega⟩)
  simpa [eCell] using this

/-- **A skew diagram cut by a band of contents.**  If `D` is skew and no two edge-adjacent
cells of `D` lie on the contents `hi + 1` and `hi`, nor on `lo` and `lo - 1`, then the cells of
`D` with content in `[lo, hi]` form a skew diagram: a cell between two band cells that leaves the
band would give, in its rectangle, an adjacent pair crossing the cut. -/
theorem isSkew_filter_band {D : Diagram} (hD : IsSkew D) (lo hi : ℤ)
    (hup : ∀ u ∈ D, ∀ u' ∈ D, CellAdj u u' → content u = hi + 1 → content u' = hi → False)
    (hdown : ∀ u ∈ D, ∀ u' ∈ D, CellAdj u u' → content u = lo → content u' = lo - 1 → False) :
    IsSkew (D.filter fun x => lo ≤ content x ∧ content x ≤ hi) := by
  intro x hx y hy h1 h2 i hi' j hj'
  rw [Finset.mem_filter] at hx hy
  simp only [Finset.mem_Icc] at hi' hj'
  have hz : (i, j) ∈ D :=
    hD x hx.1 y hy.1 h1 h2 i (Finset.mem_Icc.mpr hi') j (Finset.mem_Icc.mpr hj')
  rw [Finset.mem_filter]
  refine ⟨hz, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    -- the column `j` from row `x.1` to row `i`
    have hxlo := hx.2.1
    simp only [content] at hxlo hlt
    have hmem : ∀ k : ℤ, x.1 ≤ k → k ≤ i → (k, x.2) ∈ D := fun k hk1 hk2 =>
      hD x hx.1 (i, j) hz hi'.1 hj'.1 k (Finset.mem_Icc.mpr ⟨hk1, hk2⟩) x.2
        (Finset.mem_Icc.mpr ⟨le_refl _, hj'.1⟩)
    have hjx : x.2 ≤ j := hj'.1
    have hi1 : x.1 ≤ i := hi'.1
    refine hdown (x.2 - lo, x.2) (hmem (x.2 - lo) (by omega) (by omega))
      (x.2 - lo + 1, x.2) (hmem (x.2 - lo + 1) (by omega) (by omega)) ?_ ?_ ?_
    · rw [cellAdj_iff]; right; exact ⟨rfl, Or.inr rfl⟩
    · simp [content]
    · simp only [content]; omega
  · by_contra hgt
    push Not at hgt
    have hylo := hy.2.2
    simp only [content] at hylo hgt
    have hmem : ∀ k : ℤ, i ≤ k → k ≤ y.1 → (k, j) ∈ D := fun k hk1 hk2 =>
      hD x hx.1 y hy.1 h1 h2 k (Finset.mem_Icc.mpr ⟨by omega, hk2⟩) j
        (Finset.mem_Icc.mpr hj')
    have hjy : j ≤ y.2 := hj'.2
    have hiy : i ≤ y.1 := hi'.2
    refine hup (j - (hi + 1), j) (hmem (j - (hi + 1)) (by omega) (by omega))
      (j - (hi + 1) + 1, j) (hmem (j - (hi + 1) + 1) (by omega) (by omega)) ?_ ?_ ?_
    · rw [cellAdj_iff]; right; exact ⟨rfl, Or.inr rfl⟩
    · simp only [content]; omega
    · simp only [content]; omega

/-- **Diagonal shape from interval data.**  Suppose the cells of `D` on the relative content `a`
(content `c + a`), for `0 ≤ a < n`, are exactly the rows `L a ≤ r ≤ R a`, `D` has no other cells,
the steps `L (a - 1) - L a` and `R (a - 1) - R a` lie in `{0, 1}`, and the first and last
diagonals are singletons.  Then `D` has diagonal shape. -/
theorem hasDiagonalShape_of_intervals {D : Diagram} {c : ℤ} {n : ℕ} {L R : ℤ → ℤ}
    (hn : 1 ≤ n)
    (hmem : ∀ a r : ℤ, (r, r + (c + a)) ∈ D ↔ 0 ≤ a ∧ a < n ∧ L a ≤ r ∧ r ≤ R a)
    (hLR : ∀ a : ℤ, 0 ≤ a → a < n → L a ≤ R a)
    (hL : ∀ a : ℤ, 1 ≤ a → a < n → L (a - 1) - L a = 0 ∨ L (a - 1) - L a = 1)
    (hR : ∀ a : ℤ, 1 ≤ a → a < n → R (a - 1) - R a = 0 ∨ R (a - 1) - R a = 1)
    (h0 : L 0 = R 0) (h1 : L (n - 1) = R (n - 1)) : HasDiagonalShape D := by
  have hm : ∀ k i : ℤ, (i, i + k) ∈ D ↔ 0 ≤ k - c ∧ k - c < n ∧ L (k - c) ≤ i ∧ i ≤ R (k - c) := by
    intro k i
    have := hmem (k - c) i
    rwa [show c + (k - c) = k by ring] at this
  have hcont : ∀ k : ℤ, k ∈ contents D ↔ 0 ≤ k - c ∧ k - c < n := by
    intro k
    rw [mem_contents_iff]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨((hm k i).mp hi).1, ((hm k i).mp hi).2.1⟩
    · rintro ⟨ha, hb⟩
      exact ⟨L (k - c), (hm k _).mpr ⟨ha, hb, le_refl _, hLR _ ha hb⟩⟩
  have hlo : ∀ a : ℤ, 0 ≤ a → a < n → diagLo D (c + a) = L a := by
    intro a ha hb
    apply diagLo_eq_of (l := L a)
    · rw [hm]; simp only [add_sub_cancel_left]; exact ⟨ha, hb, le_refl _, hLR _ ha hb⟩
    · intro i hi
      rw [hm] at hi
      simp only [add_sub_cancel_left] at hi
      exact hi.2.2.1
  have hhi : ∀ a : ℤ, 0 ≤ a → a < n → diagHi D (c + a) = R a := by
    intro a ha hb
    apply diagHi_eq_of (l := R a)
    · rw [hm]; simp only [add_sub_cancel_left]; exact ⟨ha, hb, hLR _ ha hb, le_refl _⟩
    · intro i hi
      rw [hm] at hi
      simp only [add_sub_cancel_left] at hi
      exact hi.2.2.2
  have hcell : ∀ x ∈ D, 0 ≤ content x - c ∧ content x - c < n ∧
      L (content x - c) ≤ x.1 ∧ x.1 ≤ R (content x - c) := by
    intro x hx
    obtain ⟨i, j⟩ := x
    have := (hm (j - i) i).mp (by convert hx using 2; ring)
    simpa [content] using this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(L 0, L 0 + (c + 0)), by
      rw [hmem]; exact ⟨le_refl _, by omega, le_refl _, by rw [h0]⟩⟩
  · intro x hx y hy k hk
    rw [Finset.mem_Icc] at hk
    have hx' := hcell x hx
    have hy' := hcell y hy
    rw [hcont]
    omega
  · intro x hx y hy hxy i hi
    rw [Finset.mem_Icc] at hi
    have hx' := hcell x hx
    have hy' := hcell y hy
    rw [hm]
    rw [← hxy] at hy'
    refine ⟨hx'.1, hx'.2.1, ?_, ?_⟩ <;> omega
  · intro k hk hk1
    rw [hcont] at hk hk1
    set a := k - c with ha
    have e1 : k = c + a := by omega
    have e2 : k - 1 = c + (a - 1) := by omega
    unfold bitA bitB
    rw [e2, e1, hlo (a - 1) (by omega) (by omega), hlo a (by omega) (by omega),
      hhi (a - 1) (by omega) (by omega), hhi a (by omega) (by omega)]
    have := hL a (by omega) hk.2
    have := hR a (by omega) hk.2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro k hk hend
    rw [hcont] at hk
    have hend' : k - c = 0 ∨ k - c = (n : ℤ) - 1 := by
      rcases hend with h | h
      · left
        by_contra hne
        exact h ((hcont _).mpr ⟨by omega, by omega⟩)
      · right
        by_contra hne
        exact h ((hcont _).mpr ⟨by omega, by omega⟩)
    have e1 : k = c + (k - c) := by ring
    rw [e1, hlo _ hk.1 hk.2, hhi _ hk.1 hk.2]
    rcases hend' with h | h
    · rw [h]; exact h0
    · rw [h]; exact h1

end Plan.MarkFacts

end SkewMarkedFactor.Gluing
