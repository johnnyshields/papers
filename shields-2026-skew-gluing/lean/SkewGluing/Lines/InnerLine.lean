import SkewGluing.Lines.FirstWindow
import SkewGluing.Lines.Mates

/-!
# The inner of a root is a line when the first period of the parent is constant

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-lines`), first assertion: "the upper horizontal attachment therefore
completes a row inner" and "generic value one gives columns by the complementary argument".

If the first `q - 1` bits of the inner `E` of a legal mark are all `0` (both words), its first `q`
diagonals are single cells of one row (`first_window_row`); all of `E` is then in that row for the
empty mark and for a nonempty case-(a) mark with upper phase `t = 0`
(`IsLegalNonempty.isRowDiagram_of_prefix`, `IsLegalEmpty.isRowDiagram_of_prefix`).  The all-ones
case is the column version (`isColumnDiagram_of_prefix`), for case (b).

Sorry-free.
-/

namespace SkewGluing

namespace Lines

variable {E : Diagram}

/-- If the bits of `E` on `[1, n]` are all `ε`, then the rows of the diagonals `0, …, n` are
`r₀ - ε k`, where `r₀` is the row of the southwest cell. -/
theorem diag_of_prefix_const (hE : IsConnectedSkew E) {ε : ℤ} {n : ℕ}
    (hA : ∀ k ∈ Finset.Icc (1 : ℤ) n, wordA E k = ε)
    (hB : ∀ k ∈ Finset.Icc (1 : ℤ) n, wordB E k = ε) :
    diagLo E (minContent E + n) = diagLo E (minContent E) - n * ε ∧
      diagHi E (minContent E + n) = diagLo E (minContent E) - n * ε := by
  have h' := isConnectedSkew_iff_diagonal.mp hE
  have sing : diagLo E (minContent E) = diagHi E (minContent E) :=
    h'.2.2.2.2 _ (minContent_mem h'.1) (Or.inl (fun hm => by have := minContent_le hm; omega))
  have s1 := sum_wordA E n
  have s2 := sum_wordB E n
  rw [Finset.sum_congr rfl hA] at s1
  rw [Finset.sum_congr rfl hB] at s2
  simp only [Finset.sum_const, Int.card_Icc, nsmul_eq_mul] at s1 s2
  have hn : ((n : ℤ) + 1 - 1).toNat = n := by omega
  rw [hn] at s1 s2
  constructor <;> nlinarith

/-- **The first window of `E` in a row.**  If both words of `E` vanish on `[1, q - 1]`, every cell
of `E` of content at most `c₀ + q - 1` lies in the row of the southwest cell. -/
theorem first_window_row (hE : IsConnectedSkew E) {q : ℕ}
    (hbits : ∀ k ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), wordA E k = 0 ∧ wordB E k = 0) :
    ∀ y ∈ E, content y ≤ minContent E + q - 1 → y.1 = diagLo E (minContent E) := by
  intro y hy hc
  have hmin : minContent E ≤ content y := minContent_le (content_mem_contents hy)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ content y - minContent E by omega)
  have key := diag_of_prefix_const hE (ε := 0) (n := n)
    (fun k hk => (hbits k (by rw [Finset.mem_Icc] at hk ⊢; omega)).1)
    (fun k hk => (hbits k (by rw [Finset.mem_Icc] at hk ⊢; omega)).2)
  have e : minContent E + (n : ℤ) = content y := by omega
  rw [e] at key
  have h1 := diagLo_le (D := E) (k := content y) (i := y.1) (j := y.2) hy (by simp [content])
  have h2 := le_diagHi (D := E) (k := content y) (i := y.1) (j := y.2) hy (by simp [content])
  have : y.1 = y.1 := rfl
  simp only [mul_zero, sub_zero] at key
  omega

/-- **The first window of `E` in a column.**  If both words of `E` are `1` on `[1, q - 1]`, every
cell of `E` of content at most `c₀ + q - 1` lies in the column of the southwest cell. -/
theorem first_window_column (hE : IsConnectedSkew E) {q : ℕ}
    (hbits : ∀ k ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), wordA E k = 1 ∧ wordB E k = 1) :
    ∀ y ∈ E, content y ≤ minContent E + q - 1 →
      y.2 = diagLo E (minContent E) + minContent E := by
  intro y hy hc
  have hmin : minContent E ≤ content y := minContent_le (content_mem_contents hy)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ content y - minContent E by omega)
  have key := diag_of_prefix_const hE (ε := 1) (n := n)
    (fun k hk => (hbits k (by rw [Finset.mem_Icc] at hk ⊢; omega)).1)
    (fun k hk => (hbits k (by rw [Finset.mem_Icc] at hk ⊢; omega)).2)
  have e : minContent E + (n : ℤ) = content y := by omega
  rw [e] at key
  have h1 := diagLo_le (D := E) (k := content y) (i := y.1) (j := y.2) hy (by simp [content])
  have h2 := le_diagHi (D := E) (k := content y) (i := y.1) (j := y.2) hy (by simp [content])
  simp only [content] at hn e key h1 h2 hmin hc
  omega

end Lines

namespace MarkedInner

variable {ω : MarkedInner}

/-- For the empty mark, `E` is its own first window. -/
theorem IsLegalEmpty.content_le (h : ω.IsLegalEmpty) {y : ℤ × ℤ} (hy : y ∈ ω.E) :
    content y ≤ minContent ω.E + ω.period - 1 := by
  have hsp := span_eq_of_isConnectedSkew h.1.1.1
  have := h.span_eq
  have := le_maxContent (content_mem_contents hy)
  omega

theorem IsLegalEmpty.isRowDiagram_of_prefix (h : ω.IsLegalEmpty) {q : ℕ} (hq : (q : ℤ) = ω.period)
    (hbits : ∀ k ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), wordA ω.E k = 0 ∧ wordB ω.E k = 0) :
    IsRowDiagram ω.E :=
  ⟨diagLo ω.E (minContent ω.E), fun y hy =>
    Lines.first_window_row h.1.1.1 hbits y hy (by have := h.content_le hy; omega)⟩

theorem IsLegalEmpty.isColumnDiagram_of_prefix (h : ω.IsLegalEmpty) {q : ℕ}
    (hq : (q : ℤ) = ω.period)
    (hbits : ∀ k ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), wordA ω.E k = 1 ∧ wordB ω.E k = 1) :
    IsColumnDiagram ω.E :=
  ⟨diagLo ω.E (minContent ω.E) + minContent ω.E, fun y hy =>
    Lines.first_window_column h.1.1.1 hbits y hy (by have := h.content_le hy; omega)⟩

/-- A cell of the middle has content at most `c₀ + q + t - 1`. -/
theorem IsLegalNonempty.content_middle_le (h : ω.IsLegalNonempty) {s t : ℤ}
    (hph : ω.IsPhases s t) {y : ℤ × ℤ} (hy : y ∈ ω.middle) :
    content y ≤ minContent ω.E + ω.period + t - 1 := by
  have := h.contents_middle hph
  have h2 : content y ∈ contents ω.middle := content_mem_contents hy
  rw [this, Finset.mem_Icc] at h2
  exact h2.2

/-- **A case-(a) mark whose first period is a constant `0` row is a row.**  If both words of `E`
vanish on `[1, q - 1]` and the upper phase is `t = 0`, then `E` lies in one row: the first window is
in the row of the southwest cell, and the upper horizontal attachment puts the upper copy in the
same row. -/
theorem IsLegalNonempty.isRowDiagram_of_prefix (h : ω.IsLegalNonempty) (hc : ω.case = .a)
    {s t : ℤ} (hph : ω.IsPhases s t) (ht : t = 0) {q : ℕ} (hq : (q : ℤ) = ω.period)
    (hbits : ∀ k ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), wordA ω.E k = 0 ∧ wordB ω.E k = 0) :
    IsRowDiagram ω.E := by
  have hE := h.isConnectedSkew_E
  have hrow := Lines.first_window_row hE hbits
  have hnon := h.nonemptyMark
  have hb := hnon.content_bounds hE
  have hwq := h.width_lt_period
  have hwpos := h.width_pos
  set r0 := diagLo ω.E (minContent ω.E) with hr0
  have hW : ∀ y ∈ ω.W, y.1 = r0 := fun y hy => by
    have := (hb.1 y hy).2
    have : (ω.width : ℤ) = ω.widthZ := rfl
    exact hrow y (hnon.2.2.1 hy) (by omega)
  obtain ⟨-, hu⟩ := h.attach.1 hc
  obtain ⟨x, hx, -, hxu⟩ := hu
  have hxE : x ∈ ω.E := (Finset.mem_sdiff.mp hx).1
  have hx1 : x.1 = r0 := hrow x hxE (by have := h.content_middle_le hph hx; omega)
  have hxu' : (x.1, x.2 + 1) - ω.v ∈ ω.W := mem_translate.mp hxu
  have hv1 : ω.v.1 = 0 := by
    have := hW _ hxu'
    simp only [Prod.fst_sub] at this
    omega
  refine ⟨r0, fun y hy => ?_⟩
  by_cases hyW : y ∈ ω.W
  · exact hW y hyW
  by_cases hyU : y ∈ ω.upper
  · have := hW _ (mem_translate.mp hyU)
    simp only [Prod.fst_sub] at this
    omega
  · have hym : y ∈ ω.middle := Finset.mem_sdiff.mpr ⟨hy, by simp [hyW, hyU]⟩
    exact hrow y hy (by have := h.content_middle_le hph hym; omega)

/-- **A case-(b) mark whose first period is a constant `1` column is a column.** -/
theorem IsLegalNonempty.isColumnDiagram_of_prefix (h : ω.IsLegalNonempty) (hc : ω.case = .b)
    {s t : ℤ} (hph : ω.IsPhases s t) (ht : t = 0) {q : ℕ} (hq : (q : ℤ) = ω.period)
    (hbits : ∀ k ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), wordA ω.E k = 1 ∧ wordB ω.E k = 1) :
    IsColumnDiagram ω.E := by
  have hE := h.isConnectedSkew_E
  have hcol := Lines.first_window_column hE hbits
  have hnon := h.nonemptyMark
  have hb := hnon.content_bounds hE
  have hwq := h.width_lt_period
  have hwpos := h.width_pos
  set c0 := diagLo ω.E (minContent ω.E) + minContent ω.E with hc0
  have hW : ∀ y ∈ ω.W, y.2 = c0 := fun y hy => by
    have := (hb.1 y hy).2
    have : (ω.width : ℤ) = ω.widthZ := rfl
    exact hcol y (hnon.2.2.1 hy) (by omega)
  obtain ⟨-, hu⟩ := h.attach.2.1 hc
  obtain ⟨x, hx, -, hxu⟩ := hu
  have hxE : x ∈ ω.E := (Finset.mem_sdiff.mp hx).1
  have hx1 : x.2 = c0 := hcol x hxE (by have := h.content_middle_le hph hx; omega)
  have hxu' : (x.1 - 1, x.2) - ω.v ∈ ω.W := mem_translate.mp hxu
  have hv1 : ω.v.2 = 0 := by
    have := hW _ hxu'
    simp only [Prod.snd_sub] at this
    omega
  refine ⟨c0, fun y hy => ?_⟩
  by_cases hyW : y ∈ ω.W
  · exact hW y hyW
  by_cases hyU : y ∈ ω.upper
  · have := hW _ (mem_translate.mp hyU)
    simp only [Prod.snd_sub] at this
    omega
  · have hym : y ∈ ω.middle := Finset.mem_sdiff.mpr ⟨hy, by simp [hyW, hyU]⟩
    exact hcol y hy (by have := h.content_middle_le hph hym; omega)

end MarkedInner

end SkewGluing
