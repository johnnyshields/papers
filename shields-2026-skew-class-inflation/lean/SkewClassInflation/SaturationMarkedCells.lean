/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationPowers
import SkewClassInflation.CellProfiles
import SkewClassInflation.HorizontalCells
import SkewGluing.Mark

/-!
# Actual end-row marks of a general separated inner

The literal marked-cell data in `eq:saturation-marks` and
`eq:saturation-translations` of `shields-2026-skew-class-inflation.tex`.
The southwest cell is placed at row `k` and column zero, where `k`
is the Lean inner-gap count.  Both marks have the actual larger-seam
length, including when the internal gap is zero.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewGluing

variable (A : SaturationInner)

/-- The given original inner in the paper's southwest-normalized integer coordinates. -/
def innerCells : Diagram := translate (0, -(A.k : ℤ)) (profileCells A.profile)

/-- The actual lower marked interval has length equal to the larger seam. -/
def lowerMark : Diagram := translate ((A.k : ℤ), 0) (rowCells 0 A.d)

/-- The literal case-(a) marked inner, with both displayed translation coordinates. -/
def markedInner : MarkedInner where
  E := A.innerCells
  W := A.lowerMark
  v := (-(A.k : ℤ), A.profile.xi 0 - A.k - A.d)
  case := .a

/-- Actual membership in every normalized original row. -/
theorem mem_innerCells (a b : ℤ) :
    (a, b) ∈ A.innerCells ↔ ∃ i : Fin (A.k + 1), (i.val : ℤ) = a ∧
      A.profile.zeta i + i.val - A.k ≤ b ∧ b < A.profile.xi i + i.val - A.k := by
  rw [innerCells, mem_translate]
  have he : (a, b) - (0, -(A.k : ℤ)) = (a, b + A.k) := by ext <;> simp
  rw [he, mem_profileCells]
  constructor <;> rintro ⟨i, hi, hlo, hhi⟩ <;> exact ⟨i, hi, by omega, by omega⟩

/-- The lower mark is exactly the original bottom row's first distinguished cells. -/
theorem mem_lowerMark (a b : ℤ) :
    (a, b) ∈ A.lowerMark ↔ a = (A.k : ℤ) ∧ 0 ≤ b ∧ b < A.d := by
  rw [lowerMark, mem_translate]
  simp only [Prod.mk_sub_mk, sub_zero, mem_rowCells]
  omega

/-- The specified displacement gives exactly the original top row's last distinguished cells. -/
theorem mem_upperMark (a b : ℤ) :
    (a, b) ∈ A.markedInner.upper ↔ a = 0 ∧
      A.profile.xi 0 - A.k - A.d ≤ b ∧ b < A.profile.xi 0 - A.k := by
  rw [MarkedInner.upper, mem_translate]
  change (a - -(A.k : ℤ), b - (A.profile.xi 0 - A.k - A.d)) ∈ A.lowerMark ↔ _
  rw [A.mem_lowerMark]
  omega

/-- The actual normalized bottom row retains its original interval. -/
theorem mem_inner_bottom (b : ℤ) :
    ((A.k : ℤ), b) ∈ A.innerCells ↔ 0 ≤ b ∧ b < A.r (Fin.last A.k) := by
  have hr := A.profile.xi_sub_zeta (Fin.last A.k)
  rw [A.profile.zeta_last] at hr
  change A.profile.xi (Fin.last A.k) - 0 = (A.r (Fin.last A.k) : ℤ) at hr
  rw [A.mem_innerCells]
  constructor
  · rintro ⟨i, hi, hlo, hhi⟩
    have he : i = Fin.last A.k := Fin.ext (by exact_mod_cast hi)
    rw [he, A.profile.zeta_last] at hlo
    rw [he] at hhi
    simp only [Fin.val_last] at hlo hhi
    omega
  · rintro ⟨hlo, hhi⟩
    exact ⟨Fin.last A.k, rfl, by rw [A.profile.zeta_last]; simp; omega,
      by simp only [Fin.val_last]; omega⟩

/-- The actual normalized top row has its complete original endpoints. -/
theorem mem_inner_top (b : ℤ) :
    (0, b) ∈ A.innerCells ↔
      A.profile.zeta 0 - A.k ≤ b ∧ b < A.profile.xi 0 - A.k := by
  rw [A.mem_innerCells]
  constructor
  · rintro ⟨i, hi, hlo, hhi⟩
    have he : i = 0 := by
      apply Fin.ext
      change i.val = 0
      exact_mod_cast hi
    rw [he] at hlo hhi
    simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using And.intro hlo hhi
  · rintro ⟨hlo, hhi⟩
    exact ⟨0, rfl, by simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hlo,
      by simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hhi⟩

/-- The lower marked content interval is the actual translated horizontal interval. -/
theorem lowerMark_content_bounds (x : ℤ × ℤ) (hx : x ∈ A.lowerMark) :
    -(A.k : ℤ) ≤ content x ∧ content x < (A.d : ℤ) - A.k := by
  rcases x with ⟨a, b⟩
  rw [A.mem_lowerMark] at hx
  simp only [content]
  omega

/-- The upper marked content interval is exactly one actual period above the lower one. -/
theorem upperMark_content_bounds (x : ℤ × ℤ) (hx : x ∈ A.markedInner.upper) :
    A.profile.xi 0 - A.k - A.d ≤ content x ∧ content x < A.profile.xi 0 - A.k := by
  rcases x with ⟨a, b⟩
  rw [A.mem_upperMark] at hx
  simp only [content]
  omega

/-- Every nonterminal row starts strictly beyond the lower marked content interval. -/
theorem lower_content_margin (i : Fin (A.k + 1)) (hi : i.val < A.k) :
    (A.d : ℤ) < A.profile.zeta i := by
  let j : Fin A.k := ⟨A.k - 1, by have := A.k_pos; omega⟩
  have hsucc : j.succ = Fin.last A.k := Fin.ext (by dsimp [j]; have := A.k_pos; omega)
  have hle : i ≤ j.castSucc := by change i.val ≤ j.val; dsimp [j]; omega
  have hanti := A.profile.zeta_strictAnti.antitone hle
  have hgap := A.profile.xi_succ_sub_zeta_castSucc j
  rw [hsucc] at hgap
  have hrow := A.profile.xi_sub_zeta (Fin.last A.k)
  rw [A.profile.zeta_last] at hrow
  change A.profile.xi (Fin.last A.k) - A.profile.zeta j.castSucc = (A.c : ℤ) at hgap
  change A.profile.xi (Fin.last A.k) - 0 = (A.r (Fin.last A.k) : ℤ) at hrow
  have hb := A.last_bound
  omega

/-- Every nontop row ends strictly before the upper marked content interval. -/
theorem upper_content_margin (i : Fin (A.k + 1)) (hi : 0 < i.val) :
    A.profile.xi i < A.profile.xi 0 - (A.d : ℤ) := by
  let j : Fin A.k := ⟨0, A.k_pos⟩
  have hzero : j.castSucc = 0 := Fin.ext rfl
  have hle : j.succ ≤ i := by change j.val + 1 ≤ i.val; dsimp [j]; omega
  have hanti := A.profile.xi_strictAnti.antitone hle
  have hgap := A.profile.xi_succ_sub_zeta_castSucc j
  rw [hzero] at hgap
  have hrow := A.profile.xi_sub_zeta 0
  change A.profile.xi j.succ - A.profile.zeta 0 = (A.c : ℤ) at hgap
  change A.profile.xi 0 - A.profile.zeta 0 = (A.r 0 : ℤ) at hrow
  have ha := A.first_bound
  omega

/-- The two genuine terminal margins leave a strict full-span separation of the marks. -/
theorem inner_span_gt_twice_seam : 2 * (A.d : ℤ) < A.profile.xi 0 := by
  have hz := A.lower_content_margin 0 (by exact A.k_pos)
  have hrow := A.profile.xi_sub_zeta 0
  change A.profile.xi 0 - A.profile.zeta 0 = (A.r 0 : ℤ) at hrow
  have ha := A.first_bound
  omega

/-- Every normalized inner cell lies on the exact full content interval. -/
theorem inner_content_bounds (x : ℤ × ℤ) (hx : x ∈ A.innerCells) :
    -(A.k : ℤ) ≤ content x ∧ content x < A.profile.xi 0 - A.k := by
  obtain ⟨a, b⟩ := x
  obtain ⟨i, hi, hlo, hhi⟩ := (A.mem_innerCells a b).mp hx
  have hz := A.profile.zeta_nonneg i
  have ht := A.profile.xi_strictAnti.antitone (Fin.zero_le i)
  simp only [content]
  omega

/-- All inner cells on lower marked content diagonals already belong to the actual mark. -/
theorem lower_mark_of_content (x : ℤ × ℤ) (hx : x ∈ A.innerCells)
    (hc : content x < (A.d : ℤ) - A.k) : x ∈ A.lowerMark := by
  obtain ⟨a, b⟩ := x
  obtain ⟨i, hi, hlo, hhi⟩ := (A.mem_innerCells a b).mp hx
  have hilast : i.val = A.k := by
    by_contra he
    have hilt : i.val < A.k := by have := i.isLt; omega
    have hm := A.lower_content_margin i hilt
    simp only [content] at hc
    omega
  have heq : i = Fin.last A.k := Fin.ext hilast
  rw [heq, A.profile.zeta_last] at hlo
  have hbounds := A.inner_content_bounds (a, b) hx
  apply (A.mem_lowerMark a b).mpr
  simp only [content] at hc hbounds
  exact ⟨by omega, by omega, by omega⟩

/-- All inner cells on upper marked content diagonals belong to the actual translated mark. -/
theorem upper_mark_of_content (x : ℤ × ℤ) (hx : x ∈ A.innerCells)
    (hc : A.profile.xi 0 - A.k - A.d ≤ content x) : x ∈ A.markedInner.upper := by
  obtain ⟨a, b⟩ := x
  obtain ⟨i, hi, hlo, hhi⟩ := (A.mem_innerCells a b).mp hx
  have hi0 : i.val = 0 := by
    by_contra he
    have hip : 0 < i.val := Nat.pos_of_ne_zero he
    have hm := A.upper_content_margin i hip
    simp only [content] at hc
    omega
  apply (A.mem_upperMark a b).mpr
  have hbounds := A.inner_content_bounds (a, b) hx
  simp only [content] at hc hbounds
  exact ⟨by omega, by omega, by omega⟩

/-- Both displayed marks are literal subsets of the given full original inner. -/
theorem markedInner_subsets :
    A.markedInner.W ⊆ A.markedInner.E ∧ A.markedInner.upper ⊆ A.markedInner.E := by
  constructor
  · rintro ⟨a, b⟩ hx
    obtain ⟨ha, hb0, hbd⟩ := (A.mem_lowerMark a b).mp hx
    apply (A.mem_innerCells a b).mpr
    refine ⟨Fin.last A.k, by simp only [Fin.val_last]; omega, ?_, ?_⟩
    · rw [A.profile.zeta_last]
      simp only [Fin.val_last]
      omega
    · have hrow := A.profile.xi_sub_zeta (Fin.last A.k)
      rw [A.profile.zeta_last] at hrow
      change A.profile.xi (Fin.last A.k) - 0 = (A.r (Fin.last A.k) : ℤ) at hrow
      have hb := A.last_bound
      simp only [Fin.val_last]
      omega
  · rintro ⟨a, b⟩ hx
    obtain ⟨ha, hlo, hhi⟩ := (A.mem_upperMark a b).mp hx
    apply (A.mem_innerCells a b).mpr
    refine ⟨0, by simpa only [Fin.val_zero, Nat.cast_zero] using ha.symm, ?_, ?_⟩
    · have hrow := A.profile.xi_sub_zeta 0
      change A.profile.xi 0 - A.profile.zeta 0 = (A.r 0 : ℤ) at hrow
      have hb := A.first_bound
      simp only [Fin.val_zero, Nat.cast_zero, add_zero]
      omega
    · simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hhi

/-- The original normalized inner is a genuine connected skew cell diagram. -/
theorem innerCells_connected : IsConnectedSkew A.innerCells :=
  isConnectedSkew_translate _ (profileCells_connected _)

/-- The lower marked row is nonempty and connected on the full standing domain. -/
theorem lowerMark_connected : IsConnectedSkew A.lowerMark :=
  isConnectedSkew_translate _ (isConnectedSkew_rowCells (by have := A.c_lt_d; omega))

/-- The full mark width is the actual prescribed larger seam. -/
theorem markedInner_width : A.markedInner.width = A.d := by
  rw [MarkedInner.width, markedInner, lowerMark, span_translate, span_rowCells,
    sub_zero, Int.toNat_natCast]

/-- The actual content period is the full original span minus the mark width. -/
theorem markedInner_period : A.markedInner.period = A.profile.xi 0 - A.d := by
  simp only [MarkedInner.period, markedInner, content]
  ring

/-- Hypothesis II follows from the actual strict separation of both terminal margins. -/
theorem markedInner_narrow : A.markedInner.IsNarrow := by
  rw [MarkedInner.IsNarrow, A.markedInner_width, A.markedInner_period]
  have hh := A.inner_span_gt_twice_seam
  exact ⟨by positivity, by omega⟩

end SkewClassInflation.SaturationInner
