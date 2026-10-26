/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationMarkedCells
import SkewClassInflation.HatMarkTranslation

/-!
# Empty hatted marks in the actual infinite general-inner chain

Hypothesis IV in `prop:saturation-chart` of
`shields-2026-skew-class-inflation.tex`.  On any marked content diagonal,
the bi-infinite union contains only the literal marked cell: only the
base and preceding copies can meet that diagonal, and their endpoint
marks coincide.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewGluing

variable (A : SaturationInner)

/-- The actual infinite union has no additional cell on a lower marked content diagonal. -/
theorem periodic_mark_diagonals (x : ℤ × ℤ) (hx : x ∈ A.markedInner.periodicUnion)
    (hlo : -(A.k : ℤ) ≤ content x) (hhi : content x < (A.d : ℤ) - A.k) :
    x ∈ A.lowerMark := by
  obtain ⟨t, ht⟩ := hx
  have hc := A.inner_content_bounds (x - t • A.markedInner.v) ht
  rw [MarkedInner.content_sub, MarkedInner.content_smul] at hc
  have hv : content A.markedInner.v = A.profile.xi 0 - A.d := A.markedInner_period
  rw [hv] at hc
  let q := A.profile.xi 0 - (A.d : ℤ)
  have hq : (A.d : ℤ) < q := by have hh := A.inner_span_gt_twice_seam; dsimp [q]; omega
  have hd : 0 < (A.d : ℤ) := by have hh := A.c_lt_d; omega
  have hq0 : 0 ≤ q := by omega
  have ht0 : t ≤ 0 := by
    by_contra he
    have h1 : 1 ≤ t := by omega
    have hm := mul_le_mul_of_nonneg_right h1 hq0
    simp only [one_mul] at hm
    change q ≤ t * q at hm
    change -(A.k : ℤ) ≤ content x - t * q ∧ content x - t * q < A.profile.xi 0 - A.k at hc
    dsimp only [q] at hm hc
    omega
  have ht1 : -1 ≤ t := by
    by_contra he
    have h2 : t ≤ -2 := by omega
    have hm := mul_le_mul_of_nonneg_right h2 hq0
    change t * q ≤ -2 * q at hm
    dsimp only [q] at hm
    omega
  rcases (show t = 0 ∨ t = -1 by omega) with rfl | rfl
  · simp only [zero_smul, sub_zero] at ht
    exact A.lower_mark_of_content x ht hhi
  · have hu : x - (-1 : ℤ) • A.markedInner.v ∈ A.markedInner.upper := by
      apply A.upper_mark_of_content _ ht
      rw [MarkedInner.content_sub, MarkedInner.content_smul, hv]
      omega
    rw [MarkedInner.upper, mem_translate] at hu
    have he : (x - (-1 : ℤ) • A.markedInner.v) - A.markedInner.v = x := by simp
    rw [he] at hu
    exact hu

/-- No marked cell has either diagonal neighbor anywhere in the actual infinite amalgamation. -/
theorem markedInner_hatMark_empty : A.markedInner.hatMark A.markedInner.W = ∅ := by
  ext x
  rw [Set.mem_empty_iff_false, iff_false]
  rcases x with ⟨a, b⟩
  intro hx
  rcases hx with hx | hx
  · have hw := hx.2
    change (a + 1, b + 1) ∈ A.lowerMark at hw
    have hw' := (A.mem_lowerMark (a + 1) (b + 1)).mp hw
    have hbounds : -(A.k : ℤ) ≤ content (a, b) ∧
        content (a, b) < (A.d : ℤ) - A.k := by
      simp only [content]
      omega
    have hh := A.periodic_mark_diagonals (a, b) hx.1 hbounds.1 hbounds.2
    rw [A.mem_lowerMark] at hh
    omega
  · have hw := hx.1
    change (a, b) ∈ A.lowerMark at hw
    have hw' := (A.mem_lowerMark a b).mp hw
    have hbounds : -(A.k : ℤ) ≤ content (a + 1, b + 1) ∧
        content (a + 1, b + 1) < (A.d : ℤ) - A.k := by
      simp only [content]
      omega
    have hh := A.periodic_mark_diagonals (a + 1, b + 1) hx.2 hbounds.1 hbounds.2
    rw [A.mem_lowerMark] at hh
    omega

/-- Hypothesis IV holds for every pair of actual translated marked and middle copies. -/
theorem markedInner_noHatAdjacency : A.markedInner.NoHatAdjacency :=
  noHatAdjacency_of_hatMark_empty _ A.markedInner_hatMark_empty

end SkewClassInflation.SaturationInner
