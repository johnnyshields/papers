import SkewGluing.Aligned.LowerLegal

/-!
# The lower attachment of the lower mark

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, ordinary case, `b > 0`: "the attachment case is fixed by which of the
joining constructions is skew").

For `GlueData V z`, the southwest cell `x₀` of the middle of `muOf V z cs` lies on the first
diagonal of the lower tail (or on the junction diagonal `b` when there is no tail).  A southeast
tail gives a horizontal lower attachment, a northwest tail a vertical one; without a tail the
junction bit decides.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {V : Diagram} {z : ℤ × ℤ}

namespace GlueData

theorem middle_content_ge (G : GlueData V z) (cs : AttachCase) {J0 : ℤ}
    (hJ0 : J0 ≤ maxContent V - content z + 1)
    (hno : ∀ J, minContent V ≤ J → J < J0 → ¬ (0 < gapLo V z J ∨ gapHi V z J < 0))
    {y : ℤ × ℤ} (hy : y ∈ (muOf V z cs).middle) : J0 ≤ content y := by
  have hV := G.conn
  by_contra hlt
  rw [mem_middle] at hy
  obtain ⟨hy1, hy2, -⟩ := hy
  obtain ⟨i, j⟩ := y
  have e : (i, j) = (i, i + content (i, j)) := by simp [content]
  have hy1' : (i, i + content (i, j)) ∈ V := by rw [← e]; exact hy1
  have hy2' : (i, i + content (i, j)) ∉ lowerCopy V z := by rw [← e]; exact hy2
  rw [mem_D hV] at hy1'
  rw [lowerCopy_row hV] at hy2'
  have hnt := hno (content (i, j)) hy1'.1 (by omega)
  simp only [gapLo, gapHi] at hnt
  have hα := G.alpha_pos
  apply hy2'
  refine ⟨hy1', ?_⟩
  omega

theorem middle_min_eq (G : GlueData V z) (cs : AttachCase) {J0 : ℤ}
    (hJ0 : J0 ≤ maxContent V - content z + 1)
    (hno : ∀ J, minContent V ≤ J → J < J0 → ¬ (0 < gapLo V z J ∨ gapHi V z J < 0))
    {x0 : ℤ × ℤ} (hx0 : x0 ∈ (muOf V z cs).middle) (hc : content x0 = J0) :
    content x0 = minContent (muOf V z cs).middle := by
  symm
  apply minContent_eq_of (D := (muOf V z cs).middle) (k := content x0)
  · exact content_mem_contents hx0
  · intro k hk
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
    have := G.middle_content_ge cs hJ0 hno hy
    omega

/-- The cell `(r, r + J)` is a middle cell of `μ` when it lies in `V`, outside `Z`, and the
diagonal `J` is below the upper marked diagonals. -/
theorem mem_middle_of (G : GlueData V z) (cs : AttachCase) {r J : ℤ}
    (h1 : minContent V ≤ J ∧ J ≤ maxContent V ∧ diagLo V J ≤ r ∧ r ≤ diagHi V J)
    (h2 : ¬ ((minContent V ≤ J + content z ∧ J + content z ≤ maxContent V ∧
        diagLo V (J + content z) ≤ r + z.1 ∧ r + z.1 ≤ diagHi V (J + content z))))
    (h3 : J < minContent V + content z) :
    (r, r + J) ∈ (muOf V z cs).middle := by
  have hV := G.conn
  rw [mem_middle]
  refine ⟨(mem_D hV).mpr h1, fun h => h2 ?_, fun h => ?_⟩
  · have := (lowerCopy_row hV).mp h
    exact this.2
  · have h' : (r, r + J) ∈ translate z (lowerCopy V z) := h
    have := (mem_upper_row hV).mp h'
    omega

theorem first_tail_pos (G : GlueData V z) {J0 : ℤ}
    (hJ0a : minContent V ≤ J0)
    (htail : 0 < gapLo V z J0 ∨ gapHi V z J0 < 0) : minContent V + 1 ≤ J0 := by
  by_contra h
  have h0 : J0 = minContent V := by omega
  have := G.nonempty (minContent V) le_rfl G.le_max
  have h1 := (D_ends G.conn).1
  rw [h0] at htail
  simp only [gapLo, gapHi] at htail
  omega

/-- A southeast first tail gives a horizontal lower attachment. -/
theorem lowerH_of_se (G : GlueData V z) (cs : AttachCase) {J0 : ℤ}
    (hno : ∀ J, minContent V ≤ J → J < J0 → ¬ (0 < gapLo V z J ∨ gapHi V z J < 0))
    (hJ0a : minContent V ≤ J0) (hJ0b : J0 ≤ maxContent V - content z)
    (hse : gapHi V z J0 < 0) : (muOf V z cs).LowerH := by
  have hV := G.conn
  have hα := G.alpha_pos
  have hle := G.le_max
  have hsh := isConnectedSkew_iff_diagonal.mp hV
  have hJ0c := G.first_tail_pos hJ0a (Or.inr hse)
  have hsp := G.span_eq
  have hsep := G.sep
  have t1 := G.thin_lo J0 hJ0a hJ0b
  have hne := G.nonempty J0 hJ0a hJ0b
  have bJ := D_bits hV (J := J0) hJ0c (by omega)
  have hno' := hno (J0 - 1) (by omega) (by omega)
  simp only [gapLo, gapHi] at hse t1 hno'
  have e0 : J0 - 1 + content z = J0 + content z - 1 := by ring
  rw [e0] at hno'
  have hmem : (diagHi V J0, diagHi V J0 + J0) ∈ (muOf V z cs).middle := by
    apply G.mem_middle_of
    · refine ⟨by omega, by omega, ?_, le_rfl⟩
      have := diagLo_le_diagHi (D := V) (k := J0) (by rw [hsh.mem_contents_iff]; omega)
      omega
    · omega
    · omega
  refine ⟨_, hmem, G.middle_min_eq cs (by omega) hno hmem (by simp [content]), ?_⟩
  have e : ((diagHi V J0, diagHi V J0 + J0).1, (diagHi V J0, diagHi V J0 + J0).2 - 1) =
      (diagHi V J0, diagHi V J0 + (J0 - 1)) := by
    ext
    · rfl
    · simp only; ring
  rw [e]
  change _ ∈ lowerCopy V z
  rw [lowerCopy_row hV, e0]
  omega

/-- A northwest first tail gives a vertical lower attachment. -/
theorem lowerV_of_nw (G : GlueData V z) (cs : AttachCase) {J0 : ℤ}
    (hno : ∀ J, minContent V ≤ J → J < J0 → ¬ (0 < gapLo V z J ∨ gapHi V z J < 0))
    (hJ0a : minContent V ≤ J0) (hJ0b : J0 ≤ maxContent V - content z)
    (hnw : 0 < gapLo V z J0) : (muOf V z cs).LowerV := by
  have hV := G.conn
  have hα := G.alpha_pos
  have hle := G.le_max
  have hsh := isConnectedSkew_iff_diagonal.mp hV
  have hJ0c := G.first_tail_pos hJ0a (Or.inl hnw)
  have hsp := G.span_eq
  have hsep := G.sep
  have t1 := G.thin_lo J0 hJ0a hJ0b
  have hne := G.nonempty J0 hJ0a hJ0b
  have bJ := D_bits hV (J := J0) hJ0c (by omega)
  have hno' := hno (J0 - 1) (by omega) (by omega)
  simp only [gapLo, gapHi] at hnw t1 hno'
  have e0 : J0 - 1 + content z = J0 + content z - 1 := by ring
  rw [e0] at hno'
  have hmem : (diagLo V J0, diagLo V J0 + J0) ∈ (muOf V z cs).middle := by
    apply G.mem_middle_of
    · refine ⟨by omega, by omega, le_rfl, ?_⟩
      have := diagLo_le_diagHi (D := V) (k := J0) (by rw [hsh.mem_contents_iff]; omega)
      omega
    · omega
    · omega
  refine ⟨_, hmem, G.middle_min_eq cs (by omega) hno hmem (by simp [content]), ?_⟩
  have e : ((diagLo V J0, diagLo V J0 + J0).1 + 1, (diagLo V J0, diagLo V J0 + J0).2) =
      (diagLo V J0 + 1, diagLo V J0 + 1 + (J0 - 1)) := by
    ext
    · rfl
    · simp only; ring
  rw [e]
  change _ ∈ lowerCopy V z
  rw [lowerCopy_row hV, e0]
  omega

/-- Without a tail, the junction diagonal `b = M - α + 1` is a singleton, and the first middle
cell is read against the single cell of `Z` on the diagonal `b - 1`. -/
theorem lowerH_of_junction (G : GlueData V z) (cs : AttachCase)
    (hnt : ∀ J, minContent V ≤ J → J ≤ maxContent V - content z →
      ¬ (0 < gapLo V z J ∨ gapHi V z J < 0))
    (hj : diagLo V (maxContent V - content z) = diagLo V (maxContent V - content z + 1)) :
    (muOf V z cs).LowerH := by
  have hV := G.conn
  have hα := G.alpha_pos
  have hle := G.le_max
  have hsh := isConnectedSkew_iff_diagonal.mp hV
  have hends := D_ends hV
  have hsp := G.span_eq
  have hsep := G.sep
  set J0 := maxContent V - content z + 1 with hJ0
  have sb := G.sing_b
  rw [← hJ0] at sb
  have hb1 := hnt (maxContent V - content z) hle le_rfl
  have hne := G.nonempty (maxContent V - content z) hle le_rfl
  simp only [gapLo, gapHi, sub_add_cancel] at hb1 hne
  have hmem : (diagLo V J0, diagLo V J0 + J0) ∈ (muOf V z cs).middle := by
    apply G.mem_middle_of
    · refine ⟨by omega, by omega, le_rfl, ?_⟩
      have := diagLo_le_diagHi (D := V) (k := J0) (by rw [hsh.mem_contents_iff]; omega)
      omega
    · intro h; omega
    · omega
  have hno : ∀ J, minContent V ≤ J → J < J0 → ¬ (0 < gapLo V z J ∨ gapHi V z J < 0) :=
    fun J h1 h2 => hnt J h1 (by omega)
  refine ⟨_, hmem, G.middle_min_eq cs (by omega) hno hmem (by simp [content]), ?_⟩
  have e : ((diagLo V J0, diagLo V J0 + J0).1, (diagLo V J0, diagLo V J0 + J0).2 - 1) =
      (diagLo V J0, diagLo V J0 + (J0 - 1)) := by
    ext
    · rfl
    · simp only; ring
  rw [e]
  change _ ∈ lowerCopy V z
  rw [lowerCopy_row hV]
  have e1 : J0 - 1 + content z = maxContent V := by omega
  have e3 : J0 - 1 = maxContent V - content z := by omega
  rw [e1, e3]
  omega

theorem lowerV_of_junction (G : GlueData V z) (cs : AttachCase)
    (hnt : ∀ J, minContent V ≤ J → J ≤ maxContent V - content z →
      ¬ (0 < gapLo V z J ∨ gapHi V z J < 0))
    (hj : diagLo V (maxContent V - content z) = diagLo V (maxContent V - content z + 1) + 1) :
    (muOf V z cs).LowerV := by
  have hV := G.conn
  have hα := G.alpha_pos
  have hle := G.le_max
  have hsh := isConnectedSkew_iff_diagonal.mp hV
  have hends := D_ends hV
  have hsp := G.span_eq
  have hsep := G.sep
  set J0 := maxContent V - content z + 1 with hJ0
  have sb := G.sing_b
  rw [← hJ0] at sb
  have hb1 := hnt (maxContent V - content z) hle le_rfl
  have hne := G.nonempty (maxContent V - content z) hle le_rfl
  simp only [gapLo, gapHi, sub_add_cancel] at hb1 hne
  have hmem : (diagLo V J0, diagLo V J0 + J0) ∈ (muOf V z cs).middle := by
    apply G.mem_middle_of
    · refine ⟨by omega, by omega, le_rfl, ?_⟩
      have := diagLo_le_diagHi (D := V) (k := J0) (by rw [hsh.mem_contents_iff]; omega)
      omega
    · intro h; omega
    · omega
  have hno : ∀ J, minContent V ≤ J → J < J0 → ¬ (0 < gapLo V z J ∨ gapHi V z J < 0) :=
    fun J h1 h2 => hnt J h1 (by omega)
  refine ⟨_, hmem, G.middle_min_eq cs (by omega) hno hmem (by simp [content]), ?_⟩
  have e : ((diagLo V J0, diagLo V J0 + J0).1 + 1, (diagLo V J0, diagLo V J0 + J0).2) =
      (diagLo V J0 + 1, diagLo V J0 + 1 + (J0 - 1)) := by
    ext
    · rfl
    · simp only; ring
  rw [e]
  change _ ∈ lowerCopy V z
  rw [lowerCopy_row hV]
  have e1 : J0 - 1 + content z = maxContent V := by omega
  have e3 : J0 - 1 = maxContent V - content z := by omega
  rw [e1, e3]
  omega

end GlueData

end MarkedInner

end SkewGluing
