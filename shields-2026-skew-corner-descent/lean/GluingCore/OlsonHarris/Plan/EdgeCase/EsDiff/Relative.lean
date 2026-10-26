-- TODO-COPIED from skew-factor-gluing/lean/
-- SkewGluing/OlsonHarris/Plan/EdgeCase/EsDiff/Relative.lean
import GluingCore.OlsonHarris.Plan.EdgeCase.EsDiff.Neighbors

/-!
# One removable cell: the other copies, seen from its copy

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.4.3
(`OlsonHarris2024HopfApplications`).

Cells are written relative to the copy at `b`, a cell of a skew diagram `X` with no cell of `X` to
its northwest.  The copies at the other cells `d` of `X` are `E + sigma b d`.  The key ribbon meets
none of them (`key_avoid`).  A cell of `E` outside the key ribbon and outside these copies lies in
the piece of a neighbor that `X` does not have (`not_covered_iff`), and no cell of such a piece is
adjacent to one of the copies (`not_adjacent`).

Sorry-free.
-/

set_option linter.style.openClassical false

namespace GluingCore

namespace Plan

namespace EsDiff

open scoped Classical

open GluingCore.MarkedInner

variable {ω : MarkedInner}

theorem sigma_east (ω : MarkedInner) (b : ℤ × ℤ) : sigma ω b (b.1, b.2 + 1) = ω.v := by
  unfold sigma content
  simp only
  rw [show b.2 + 1 - b.1 - (b.2 - b.1) = 1 by ring, show b.1 - b.1 = 0 by ring]
  simp

theorem sigma_south (ω : MarkedInner) (b : ℤ × ℤ) :
    sigma ω b (b.1 + 1, b.2) = -ω.v + eCell := by
  unfold sigma content
  simp only
  rw [show b.2 - (b.1 + 1) - (b.2 - b.1) = -1 by ring, show b.1 + 1 - b.1 = 1 by ring]
  simp

theorem sigma_southeast (ω : MarkedInner) (b : ℤ × ℤ) :
    sigma ω b (b.1 + 1, b.2 + 1) = eCell := by
  unfold sigma content
  simp only
  rw [show b.2 + 1 - (b.1 + 1) - (b.2 - b.1) = 0 by ring, show b.1 + 1 - b.1 = 1 by ring]
  simp

/-- The key ribbon avoids every shift of `E` by an allowed displacement. -/
theorem key_avoid_shift (hL : EdgeLocal ω) {ε s : ℤ}
    (hall : (ε = 1 ∧ 0 ≤ s) ∨ (ε = 0 ∧ 1 ≤ s) ∨ (ε = -1 ∧ 1 ≤ s)) {z : ℤ × ℤ}
    (hz : z ∈ keyRibbon ω) : z - (ε • ω.v + s • eCell) ∉ ω.E := by
  rcases hall with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩
  · simpa only [one_smul] using hL.key_east s hs z hz
  · simpa only [zero_smul, zero_add] using hL.key_same s hs z hz
  · simpa only [neg_smul, one_smul] using hL.key_south s hs z hz

/-- A copy at a cell whose content differs by two or more from that of `b` does not meet or touch
the copy at `b`. -/
theorem sigma_close (hω : ω.IsLegal) {b d z y n : ℤ × ℤ} (hz : z ∈ ω.E) (hy : y ∈ ω.E)
    (hn : n = y + sigma ω b d) (h1 : content n ≤ content z + 1) (h2 : content z ≤ content n + 1) :
    content d ≤ content b + 1 ∧ content b ≤ content d + 1 := by
  have hq : 0 < ω.period := hω.period_pos
  have hwq : (ω.width : ℤ) < ω.period := hω.2.2.1.2
  have c1 := hω.copy_content hz
  have c2 := hω.copy_content hy
  have c3 : content n = content y + (content d - content b) * ω.period := by
    rw [hn, content_add, content_sigma]
  constructor
  · by_contra hcon
    have : 2 * ω.period ≤ (content d - content b) * ω.period :=
      mul_le_mul_of_nonneg_right (by omega) hq.le
    nlinarith
  · by_contra hcon
    have : (content d - content b) * ω.period ≤ -2 * ω.period :=
      mul_le_mul_of_nonneg_right (by omega) hq.le
    nlinarith

variable {X : Diagram} {b : ℤ × ℤ}

/-- The key ribbon of the copy at `b` meets no other copy. -/
theorem key_avoid (hω : ω.IsLegal) (hL : EdgeLocal ω) (hX : IsSkew X) (hb : b ∈ X)
    (hmin : ∀ x ∈ X, x.1 ≤ b.1 → x.2 ≤ b.2 → x = b) {z : ℤ × ℤ} (hz : z ∈ keyRibbon ω) :
    ∀ d ∈ X.erase b, z - sigma ω b d ∉ ω.E := by
  intro d hd
  obtain ⟨hdb, hdX⟩ := Finset.mem_erase.mp hd
  rcases nbr_cases hX hb hmin hdX hdb with e | e | e | e | ⟨-, -, -, e⟩
  · rw [e, sigma_east]
    simpa using hL.key_east 0 le_rfl z hz
  · rw [e, sigma_south]
    simpa using hL.key_south 1 le_rfl z hz
  · intro hmem
    have := sigma_close hω (hL.key_sub z hz) hmem (n := z) (b := b) (d := d)
      (by rw [sub_add_cancel]) (by omega) (by omega)
    omega
  · intro hmem
    have := sigma_close hω (hL.key_sub z hz) hmem (n := z) (b := b) (d := d)
      (by rw [sub_add_cancel]) (by omega) (by omega)
    omega
  · exact key_avoid_shift hL (by omega) hz

/-- The cell `z` lies in a piece of `E` whose neighbor cell, east, south or southeast of `b`, is
not in `X`. -/
def AbsentPiece (ω : MarkedInner) (X : Diagram) (b z : ℤ × ℤ) : Prop :=
  (z ∈ pieceE ω ∧ (b.1, b.2 + 1) ∉ X) ∨ (z ∈ pieceS ω ∧ (b.1 + 1, b.2) ∉ X) ∨
    (z ∈ pieceSE ω ∧ (b.1 + 1, b.2 + 1) ∉ X)

theorem rel_content (hω : ω.IsLegal) {d z : ℤ × ℤ} (hmem : z - sigma ω b d ∈ ω.E) :
    minContent ω.E ≤ content z - (content d - content b) * ω.period ∧
      content z - (content d - content b) * ω.period ≤
        minContent ω.E + ω.period + ω.width - 1 := by
  have := hω.copy_content hmem
  rw [content_sub, content_sigma] at this
  exact this

theorem east_ne (b : ℤ × ℤ) : (b.1, b.2 + 1) ≠ b := by
  intro h; have := congrArg Prod.snd h; simp at this

theorem south_ne (b : ℤ × ℤ) : (b.1 + 1, b.2) ≠ b := by
  intro h; have := congrArg Prod.fst h; simp at this

theorem southeast_ne (b : ℤ × ℤ) : (b.1 + 1, b.2 + 1) ≠ b := by
  intro h; have := congrArg Prod.fst h; simp at this

theorem content_east (b : ℤ × ℤ) : content (b.1, b.2 + 1) = content b + 1 := by
  simp only [content]; ring

theorem content_south (b : ℤ × ℤ) : content (b.1 + 1, b.2) = content b - 1 := by
  simp only [content]; ring

/-- **The cells of the copy at `b` outside the key ribbon and outside the other copies** are the
cells of the pieces whose neighbor is missing. -/
theorem not_covered_iff (hω : ω.IsLegal) (hL : EdgeLocal ω) (hX : IsSkew X) (hb : b ∈ X)
    (hmin : ∀ x ∈ X, x.1 ≤ b.1 → x.2 ≤ b.2 → x = b) {z : ℤ × ℤ} (hzE : z ∈ ω.E)
    (hzK : z ∉ keyRibbon ω) :
    (∀ d ∈ X.erase b, z - sigma ω b d ∉ ω.E) ↔ AbsentPiece ω X b z := by
  have hq : 0 < ω.period := hω.period_pos
  have hwq : (ω.width : ℤ) < ω.period := hω.2.2.1.2
  constructor
  · intro hnc
    rcases hL.cover z hzE with hk | hP | hP | hP
    · exact absurd hk hzK
    · refine Or.inl ⟨hP, fun he => hnc _ (Finset.mem_erase.mpr ⟨east_ne b, he⟩) ?_⟩
      rw [sigma_east]; exact hL.pieceE_cover z hP
    · refine Or.inr (Or.inl ⟨hP, fun he => hnc _ (Finset.mem_erase.mpr ⟨south_ne b, he⟩) ?_⟩)
      rw [sigma_south]; exact hL.pieceS_cover z hP
    · refine Or.inr (Or.inr ⟨hP, fun he => hnc _ (Finset.mem_erase.mpr ⟨southeast_ne b, he⟩) ?_⟩)
      rw [sigma_southeast]; exact hL.pieceSE_cover z hP
  · intro hab d hd hmem
    obtain ⟨hdb, hdX⟩ := Finset.mem_erase.mp hd
    have hr := rel_content hω hmem
    rcases nbr_cases hX hb hmin hdX hdb with e | e | e | e | ⟨h1, h2, h3, -⟩
    · have hcd : content d - content b = 1 := by rw [e, content_east]; ring
      rw [hcd, one_mul] at hr
      rcases hab with ⟨hP, hf⟩ | ⟨hP, -⟩ | ⟨hP, -⟩
      · exact hf (e ▸ hdX)
      · have := hL.pieceS_content z hP; omega
      · have := hL.pieceSE_content z hP; omega
    · have hcd : content d - content b = -1 := by rw [e, content_south]; ring
      rw [hcd] at hr
      rcases hab with ⟨hP, -⟩ | ⟨hP, hf⟩ | ⟨hP, -⟩
      · have := hL.pieceE_content z hP; omega
      · exact hf (e ▸ hdX)
      · have := hL.pieceSE_content z hP; omega
    · have := sigma_close hω hzE hmem (n := z) (b := b) (d := d) (by rw [sub_add_cancel])
        (by omega) (by omega)
      omega
    · have := sigma_close hω hzE hmem (n := z) (b := b) (d := d) (by rw [sub_add_cancel])
        (by omega) (by omega)
      omega
    · rcases hab with ⟨-, hf⟩ | ⟨-, hf⟩ | ⟨-, hf⟩
      · exact hf h1
      · exact hf h2
      · exact hf h3

/-- **No cell of a piece whose neighbor is missing touches another copy.** -/
theorem not_adjacent (hω : ω.IsLegal) (hL : EdgeLocal ω) (hX : IsSkew X) (hb : b ∈ X)
    (hmin : ∀ x ∈ X, x.1 ≤ b.1 → x.2 ≤ b.2 → x = b) {z n : ℤ × ℤ} (hz : AbsentPiece ω X b z)
    {d : ℤ × ℤ} (hd : d ∈ X.erase b) (hn : n - sigma ω b d ∈ ω.E) : ¬ CellAdj z n := by
  have hq : 0 < ω.period := hω.period_pos
  have hwq : (ω.width : ℤ) < ω.period := hω.2.2.1.2
  intro hadj
  have hc := content_adj hadj
  have hzE : z ∈ ω.E := by
    rcases hz with ⟨hP, -⟩ | ⟨hP, -⟩ | ⟨hP, -⟩
    · exact hL.pieceE_sub z hP
    · exact hL.pieceS_sub z hP
    · exact hL.pieceSE_sub z hP
  obtain ⟨hdb, hdX⟩ := Finset.mem_erase.mp hd
  have hr := rel_content hω hn
  rcases nbr_cases hX hb hmin hdX hdb with e | e | e | e | ⟨h1, h2, h3, -⟩
  · have hcd : content d - content b = 1 := by rw [e, content_east]; ring
    rw [hcd, one_mul] at hr
    rcases hz with ⟨hP, hf⟩ | ⟨hP, -⟩ | ⟨hP, -⟩
    · exact hf (e ▸ hdX)
    · have := hL.pieceS_content z hP; omega
    · have := hL.pieceSE_content z hP; omega
  · have hcd : content d - content b = -1 := by rw [e, content_south]; ring
    rw [hcd] at hr
    rcases hz with ⟨hP, -⟩ | ⟨hP, hf⟩ | ⟨hP, -⟩
    · have := hL.pieceE_content z hP; omega
    · exact hf (e ▸ hdX)
    · have := hL.pieceSE_content z hP; omega
  · have := sigma_close hω hzE hn (n := n) (b := b) (d := d) (by rw [sub_add_cancel])
      (by omega) (by omega)
    omega
  · have := sigma_close hω hzE hn (n := n) (b := b) (d := d) (by rw [sub_add_cancel])
      (by omega) (by omega)
    omega
  · rcases hz with ⟨-, hf⟩ | ⟨-, hf⟩ | ⟨-, hf⟩
    · exact hf h1
    · exact hf h2
    · exact hf h3

end EsDiff

end Plan

end GluingCore
