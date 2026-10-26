import SkewBase.ChartSize

/-!
# Completeness of the forward generation

Formalizes `shields-2026-skew-base-computational.tex`, «The geometry of a chart and two complete
searches» (`sec:roots`): the forward generation of `def:searches` and the last sentence of the
proof of `thm:searches`.

The forward generation with bound `n` runs over every connected inner `E` with
`2 ≤ |E| ≤ (2n - 1)/3`, every legal mark of `E` (period `q`, width `w`) and every connected outer
`D` with `2 ≤ |D| ≤ (n - w)/q`, and keeps each composition that is a connected skew diagram of at
most `n` cells.  `ForwardGeneration n` is the set of charts so kept, and
`mem_forwardGeneration_iff` shows it consists of exactly the proper charts of the connected
diagrams of at most `n` cells: the two size ranges lose no proper chart, by `lem:size` and
`lem:inner-size`.  The geometric completeness of searches S and B is not part of this module.

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-- The charts kept by the forward generation with bound `n`: inner and outer in their size
ranges, legal mark, composite a connected skew diagram of at most `n` cells. -/
def ForwardGeneration (n : ℕ) : Set Chart :=
  {χ | 2 ≤ χ.ω.E.card ∧ χ.ω.E.card ≤ (2 * n - 1) / 3 ∧ χ.ω.IsLegal ∧ IsConnectedSkew χ.D ∧
      2 ≤ χ.D.card ∧ χ.D.card ≤ (n - χ.ω.width) / χ.ω.period.toNat ∧
      IsConnectedSkew χ.parent ∧ χ.parent.card ≤ n}

/-- **Forward generation, soundness and completeness.**  The forward generation with bound `n`
keeps exactly the proper charts whose composite is a connected skew diagram of at most `n`
cells. -/
theorem mem_forwardGeneration_iff {n : ℕ} {χ : Chart} :
    χ ∈ ForwardGeneration n ↔
      χ.IsProperLegal ∧ IsConnectedSkew χ.parent ∧ χ.parent.card ≤ n := by
  constructor
  · rintro ⟨hE2, -, hω, hD, hD2, -, hP, hPn⟩
    exact ⟨⟨hD, hD2, hE2, hω⟩, hP, hPn⟩
  · rintro ⟨h, hP, hPn⟩
    obtain ⟨hD, hD2, hE2, hω⟩ := id h
    have hinner := inner_size h
    have hsize := size_of_proper h
    have hq := period_pos hω
    have hw0 : (0 : ℤ) ≤ χ.ω.width := by positivity
    refine ⟨hE2, ?_, hω, hD, hD2, ?_, hP, hPn⟩
    · apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
      omega
    · have hqn : (χ.ω.period.toNat : ℤ) = χ.ω.period := Int.toNat_of_nonneg hq.le
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      have : (χ.D.card : ℤ) * χ.ω.period.toNat + χ.ω.width ≤ n := by
        rw [hqn]
        have : (χ.parent.card : ℤ) ≤ n := by exact_mod_cast hPn
        linarith
      have hle : χ.ω.width ≤ n := by
        have : (0 : ℤ) ≤ χ.D.card * χ.ω.period.toNat := by positivity
        omega
      omega

/-- A proper chart of a connected diagram `F` of at most `n` cells is kept by the forward
generation with bound `n`. -/
theorem mem_forwardGeneration_of_isChartOf {n : ℕ} {χ : Chart} (h : χ.IsProperLegal)
    {F : Diagram} (hF : χ.IsChartOf F) (hFc : IsConnectedSkew F) (hFn : F.card ≤ n) :
    χ ∈ ForwardGeneration n := by
  rw [mem_forwardGeneration_iff]
  refine ⟨h, ?_, by rw [← card_of_isChartOf hF]; exact hFn⟩
  obtain ⟨t, rfl⟩ := hF
  have := isConnectedSkew_translate (-t) hFc
  rwa [translate_translate, neg_add_cancel, translate_zero] at this

end SkewBase
