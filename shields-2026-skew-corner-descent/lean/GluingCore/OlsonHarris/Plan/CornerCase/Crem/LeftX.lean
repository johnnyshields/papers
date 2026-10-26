-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem/LeftX.lean
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.RightX
import GluingCore.OlsonHarris.Plan.CornerCase.Bookkeeping
import GluingCore.OlsonHarris.Plan.CornerCase.NoRightRibbons
import GluingCore.OlsonHarris.Plan.CornerCase.OuterWindows

/-!
# The outer after removing a ribbon removable on the left

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the outer `D \ A` of thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`) for a ribbon `A` of size `m` removable on the left from a
connected skew `D`.

A ribbon removable on the left is the strip `A = leftStrip D j₀ m` of the first cells of the
diagonals `j₀ ≤ j < j₀ + m` (`LeftWindow`, obtained by rotation from the right case); then
`D \ A` has the diagonals of `D` except those of the window with a single cell, the same last
rows, and the first rows raised by one on the window.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace Rem


open MarkedInner

/-- The strip of the first cells of the diagonals `j₀, …, j₀ + m - 1`. -/
def leftStrip (D : Diagram) (j0 : ℤ) (m : ℕ) : Diagram :=
  (Finset.Ico j0 (j0 + m)).image fun j => (diagLo D j, diagLo D j + j)

theorem mem_leftStrip {D : Diagram} {j0 : ℤ} {m : ℕ} {y : ℤ × ℤ} :
    y ∈ leftStrip D j0 m ↔ j0 ≤ content y ∧ content y < j0 + m ∧ y.1 = diagLo D (content y) := by
  unfold leftStrip
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_Ico] at hj
    simp only [content]
    refine ⟨by omega, by omega, ?_⟩
    have : diagLo D (diagLo D j + j - diagLo D j) = diagLo D j := by simp
    rw [this]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨content y, Finset.mem_Ico.mpr ⟨h1, h2⟩, ?_⟩
    obtain ⟨a, b⟩ := y
    simp only [content] at h3 ⊢
    rw [← h3]
    ext <;> simp

/-- The data of a ribbon `leftStrip D j₀ m` of size `m` removable on the left from `D`. -/
structure LeftWindow (D : Diagram) (j0 : ℤ) (m : ℕ) : Prop where
  conn : IsConnectedSkew D
  pos : 0 < m
  start : j0 ∈ contents D
  stop : j0 + m - 1 ∈ contents D
  startEnd : j0 - 1 ∉ contents D ∨ diagLo D (j0 - 1) - diagLo D j0 = 1
  stopEnd : j0 + m ∉ contents D ∨ diagLo D (j0 + m) = diagLo D (j0 + m - 1)
  mem : leftStrip D j0 m ∈ leftRibbons D m

theorem LeftWindow.of_mem {D A : Diagram} (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m)
    (hA : A ∈ leftRibbons D m) :
    ∃ j0 : ℤ, A = leftStrip D j0 m ∧ LeftWindow D j0 m := by
  have hDr := isConnectedSkew_rotate hD
  have hA' : rotate A ∈ rightRibbons (rotate D) m :=
    rotate_mem_rightRibbons (X := rotate D) (by rwa [rotate_rotate])
  obtain ⟨js, hrA, hw⟩ := RightWindow.of_mem hDr hm hA'
  have hAeq : A = leftStrip D (-(js + m - 1)) m := by
    ext y
    have h1 : y ∈ A ↔ -y ∈ rotate A := by
      rw [mem_rotate, neg_neg]
    rw [h1, hrA, mem_windowRibbon, mem_leftStrip]
    have hc : content (-y) = - content y := by simp [content]; ring
    rw [hc, diagHi_rotate]
    simp only [neg_neg, Prod.fst_neg]
    constructor
    · rintro ⟨a1, a2, a3⟩
      exact ⟨by omega, by omega, by omega⟩
    · rintro ⟨a1, a2, a3⟩
      exact ⟨by omega, by omega, by omega⟩
  refine ⟨-(js + m - 1), hAeq, ?_⟩
  have cm : ∀ k k' : ℤ, k = k' → (k ∈ contents D ↔ k' ∈ contents D) := fun k k' h => by rw [h]
  have dl : ∀ k k' : ℤ, k = k' → diagLo D k = diagLo D k' := fun k k' h => by rw [h]
  have hs := (mem_contents_rotate (D := D)).mp hw.start
  have he := (mem_contents_rotate (D := D)).mp hw.stop
  have hse := hw.startEnd
  have hte := hw.stopEnd
  refine ⟨hD, hm, (cm _ _ (by ring)).mp he, (cm _ _ (by ring)).mp hs, ?_, ?_, hAeq ▸ hA⟩
  · rcases hte with h | h
    · left
      rw [mem_contents_rotate] at h
      exact fun hh => h ((cm _ _ (by ring)).mp hh)
    · right
      rw [diagHi_rotate, diagHi_rotate] at h
      have a1 := dl (-(js + (m : ℤ) - 1) - 1) (-(js + m))  (by ring)
      have a2 := dl (-(js + (m : ℤ) - 1)) (-(js + m - 1)) (by ring)
      have a3 := dl (-(js + (m : ℤ) - 1) - 1) (- (js + m)) (by ring)
      omega
  · rcases hse with h | h
    · left
      rw [mem_contents_rotate] at h
      exact fun hh => h ((cm _ _ (by ring)).mp hh)
    · right
      rw [diagHi_rotate, diagHi_rotate] at h
      have a1 := dl (-(js + (m : ℤ) - 1) + m) (-(js - 1)) (by ring)
      have a2 := dl (-(js + (m : ℤ) - 1) + m - 1) (-js) (by ring)
      omega

variable {D : Diagram} {j0 : ℤ} {m : ℕ}

theorem LeftWindow.isSkew_X (hw : LeftWindow D j0 m) : IsSkew (D \ leftStrip D j0 m) :=
  isSkew_sdiff_of_isDownsetIn hw.conn.1 (mem_leftRibbons.mp hw.mem).2.2.2

theorem mem_sdiff_leftStrip {i j : ℤ} :
    (i, i + j) ∈ D \ leftStrip D j0 m ↔
      (i, i + j) ∈ D ∧ ¬ (j0 ≤ j ∧ j < j0 + m ∧ i = diagLo D j) := by
  rw [Finset.mem_sdiff, mem_leftStrip]
  simp only [content]
  have e : i + j - i = j := by ring
  rw [e]

theorem contents_XL (_hw : LeftWindow D j0 m) {j : ℤ} :
    j ∈ contents (D \ leftStrip D j0 m) ↔
      j ∈ contents D ∧ ¬ (j0 ≤ j ∧ j < j0 + m ∧ diagLo D j = diagHi D j) := by
  rw [mem_contents_iff]
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_sdiff_leftStrip] at hi
    refine ⟨mem_contents_iff.mpr ⟨i, hi.1⟩, fun ⟨h1, h2, h3⟩ => hi.2 ⟨h1, h2, ?_⟩⟩
    have := diagLo_le hi.1 (by ring : i + j - i = j)
    have := le_diagHi hi.1 (by ring : i + j - i = j)
    omega
  · rintro ⟨hj, hn⟩
    refine ⟨diagHi D j, ?_⟩
    rw [mem_sdiff_leftStrip]
    have := diagLo_le_diagHi hj
    refine ⟨diagHi_mem hj, fun ⟨h1, h2, h3⟩ => hn ⟨h1, h2, by omega⟩⟩

theorem diagHi_XL (hw : LeftWindow D j0 m) {j : ℤ}
    (hj : j ∈ contents (D \ leftStrip D j0 m)) :
    diagHi (D \ leftStrip D j0 m) j = diagHi D j := by
  have hj' := (contents_XL hw).mp hj
  have hle := diagLo_le_diagHi hj'.1
  refine diagHi_eq_of (l := diagHi D j) ?_ ?_
  · rw [mem_sdiff_leftStrip]
    refine ⟨diagHi_mem hj'.1, fun ⟨h1, h2, h3⟩ => hj'.2 ⟨h1, h2, by omega⟩⟩
  · intro i hi
    rw [mem_sdiff_leftStrip] at hi
    exact le_diagHi hi.1 (by ring)

theorem diagLo_XL (hw : LeftWindow D j0 m) {j : ℤ}
    (hj : j ∈ contents (D \ leftStrip D j0 m)) :
    diagLo (D \ leftStrip D j0 m) j =
      diagLo D j + (if j0 ≤ j ∧ j < j0 + m then 1 else 0) := by
  have hs := hw.conn.1
  have hj' := (contents_XL hw).mp hj
  have hle := diagLo_le_diagHi hj'.1
  by_cases hwin : j0 ≤ j ∧ j < j0 + m
  · have hlt : diagLo D j < diagHi D j := by
      by_contra hc
      exact hj'.2 ⟨hwin.1, hwin.2, by omega⟩
    simp only [hwin, and_self, ↓reduceIte]
    refine diagLo_eq_of (l := diagLo D j + 1) ?_ ?_
    · rw [mem_sdiff_leftStrip]
      exact ⟨(mem_skew_iff hs).mpr ⟨hj'.1, by omega, by omega⟩, fun ⟨_, _, h3⟩ => by omega⟩
    · intro i hi
      rw [mem_sdiff_leftStrip] at hi
      have := diagLo_le hi.1 (by ring : i + j - i = j)
      by_contra hc
      exact hi.2 ⟨hwin.1, hwin.2, by omega⟩
  · simp only [hwin, ↓reduceIte, add_zero]
    refine diagLo_eq_of (l := diagLo D j) ?_ ?_
    · rw [mem_sdiff_leftStrip]
      exact ⟨diagLo_mem hj'.1, fun ⟨h1, h2, _⟩ => hwin ⟨h1, h2⟩⟩
    · intro i hi
      rw [mem_sdiff_leftStrip] at hi
      exact diagLo_le hi.1 (by ring)


end Rem

end Corner

end Plan

end GluingCore
