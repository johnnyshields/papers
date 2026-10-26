/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Legal1.lean`. -/
import GluingCore.Aligned.CaseD.Legal0

/-!
# Aligned marks, case (d): the attachments of the lower mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`).

The lower attachment of `alD_mark V a θ cs` is horizontal or vertical: the southwest cell of the
middle is the first lower tail (or the singleton diagonal `b`), and one of its western and
southern neighbors lies in `Z`.  Dually the northeast cell of the middle has an eastern or
northern neighbor in `Z + z`.  `alD_case` chooses the attachment case accordingly.

Sorry-free.
-/

namespace GluingCore

section Attach

variable {V : Diagram} {a θ : ℤ} {cs : AttachCase}

theorem alD_cell_form (V : Diagram) (x : ℤ × ℤ) :
    x = (x.1, x.1 + (minContent V + (content x - minContent V))) := by
  obtain ⟨r, c⟩ := x
  ext <;> simp [content]

theorem alD_mem_middle_cell (x : ℤ × ℤ) :
    x ∈ (alD_mark V a θ cs).middle ↔
      (x ∈ V \ alD_Z V a θ) ∧ x ∉ (alD_mark V a θ cs).upper := by
  unfold MarkedInner.middle
  rw [Finset.mem_sdiff, Finset.mem_union, not_or, alD_mark_E, alD_mark_W]
  rw [Finset.mem_sdiff]
  tauto

theorem alD_c1_first (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {s : ℤ}
    (hs3 : s ≤ (span V : ℤ) - a) (hs0 : 0 ≤ s) :
    alD_c1Lo V a θ s = alD_c1Hi V a θ s ∧ alD_L V s ≤ alD_c1Lo V a θ s ∧
      alD_c1Lo V a θ s ≤ alD_H V s := by
  have hb := hD.hb
  have ha := hD.ha
  have l := alD_L_le_H hV (j := s) hs0 (by omega)
  unfold alD_c1Lo alD_c1Hi
  by_cases h : s < (span V : ℤ) - a
  · simp only [h, ↓reduceIte]
    unfold alD_tail
    by_cases hh : alD_L V s < alD_zl V a θ s
    · simp only [hh, ↓reduceIte]; refine ⟨trivial, ?_, ?_⟩ <;> omega
    · simp only [hh, ↓reduceIte]; refine ⟨trivial, ?_, ?_⟩ <;> omega
  · have : s = (span V : ℤ) - a := by omega
    simp only [h, ↓reduceIte]
    have h2 := hD.singleton_b
    rw [← this] at h2
    omega

theorem alD_lower_attach (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_mark V a θ cs).LowerH ∨ (alD_mark V a θ cs).LowerV := by
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := alD_s hV hD
  have hb := hD.hb
  have hba := hD.hba
  have ha := hD.ha
  have hf := alD_c1_first hV hD hs2 (by omega)
  set r0 := alD_c1Lo V a θ s with hr0
  have hc1 := alD_mem_compl1 hV hD (s := s) (by omega) hs2 hs3 hs4 r0 s
  have hxc : (r0, r0 + (minContent V + s)) ∈ V \ alD_Z V a θ := by
    rw [hc1]
    exact ⟨le_rfl, by omega, le_rfl, by omega⟩
  have hxu : (r0, r0 + (minContent V + s)) ∉ (alD_mark V a θ cs).upper := by
    intro h
    rw [alD_mem_upper hV ha.le] at h
    omega
  have hxm : (r0, r0 + (minContent V + s)) ∈ (alD_mark V a θ cs).middle :=
    (alD_mem_middle_cell _).mpr ⟨hxc, hxu⟩
  have hmin : minContent (alD_mark V a θ cs).middle = minContent V + s := by
    apply minContent_eq_of (k := minContent V + s)
    · have := content_mem_contents hxm
      simpa [content] using this
    · intro k hk
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
      have hy' := (alD_mem_middle_cell y).mp hy
      have := alD_cell_form V y
      have h3 := hy'.1
      rw [this, Finset.mem_sdiff] at h3
      have h4 := (alD_mem_compl1 hV hD (s := s) (by omega) hs2 hs3 hs4 y.1
        (content y - minContent V)).mp (by rw [Finset.mem_sdiff]; exact h3)
      omega
  -- the neighbors lie on the diagonal `s - 1`, whose copy of `Z` is all of `V`
  have z := alD_zrows hV hD (j := s - 1) (by omega) (by omega)
  have e1 := hs3 (s - 1) (by omega) (by omega)
  have z' := z.2.2.2.2.2.1 e1
  have st := alD_step hV (j := s) hs1 (by omega)
  have hmemZ : ∀ r, alD_L V (s - 1) ≤ r → r ≤ alD_H V (s - 1) →
      (r, r + (minContent V + (s - 1))) ∈ alD_Z V a θ := by
    intro r h1 h2
    rw [alD_mem_Z hV ha.le]
    omega
  by_cases hw : alD_L V (s - 1) ≤ r0
  · left
    refine ⟨_, hxm, ?_, ?_⟩
    · simp only [content]
      rw [hmin]; ring
    · have := hmemZ r0 hw (by omega)
      have e : r0 + (minContent V + s) - 1 = r0 + (minContent V + (s - 1)) := by ring
      change (r0, r0 + (minContent V + s) - 1) ∈ (alD_mark V a θ cs).W
      rw [e]; exact this
  · right
    refine ⟨_, hxm, ?_, ?_⟩
    · simp only [content]
      rw [hmin]; ring
    · have := hmemZ (r0 + 1) (by omega) (by omega)
      have e : r0 + 1 + (minContent V + (s - 1)) = r0 + (minContent V + s) := by ring
      change (r0 + 1, r0 + (minContent V + s)) ∈ (alD_mark V a θ cs).W
      rw [e] at this
      exact this

/-- The last row of the middle's northeast diagonal `a + t - 1`: the upper tail, or the
singleton `V_{a-1}` when `t = 0`. -/
def alD_lastRow (V : Diagram) (a θ t : ℤ) : ℤ :=
  if t = 0 then alD_L V (a - 1) else alD_utail V a θ (t - 1)

theorem alD_c2_last (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {t : ℤ} (ht0 : 0 ≤ t)
    (ht1 : t < (span V : ℤ) - a) :
    alD_c2Lo V a θ (a + t - 1) = alD_lastRow V a θ t ∧
      alD_c2Hi V a θ (a + t - 1) = alD_lastRow V a θ t ∧
      alD_L V (a + t - 1) ≤ alD_lastRow V a θ t ∧ alD_lastRow V a θ t ≤ alD_H V (a + t - 1) := by
  have hb := hD.hb
  have ha := hD.ha
  have hs := hD.singleton_a
  unfold alD_c2Lo alD_c2Hi alD_lastRow
  by_cases h : t = 0
  · subst h
    have : a + 0 - 1 < a := by omega
    simp only [this, ↓reduceIte]
    have e : a + 0 - 1 = a - 1 := by ring
    rw [e]
    have l := alD_L_le_H hV (j := a - 1) (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega
  · have : ¬ a + t - 1 < a := by omega
    simp only [this, h, ↓reduceIte]
    have e : a + t - 1 - a = t - 1 := by ring
    rw [e]
    have l := alD_L_le_H hV (j := a + t - 1) (by omega) (by omega)
    have e2 : t - 1 + a = a + t - 1 := by ring
    unfold alD_utail
    rw [e2]
    by_cases hh : alD_L V (a + t - 1) < alD_zl V a θ (t - 1) + θ
    · simp only [hh, ↓reduceIte]; refine ⟨?_, ?_, ?_, ?_⟩ <;> trivial
    · simp only [hh, ↓reduceIte]; refine ⟨?_, ?_, ?_, ?_⟩ <;> trivial

theorem alD_upper_attach (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_mark V a θ cs).UpperH ∨ (alD_mark V a θ cs).UpperV := by
  obtain ⟨t, ht0, ht1, ht2, ht3⟩ := alD_t hV hD
  have hb := hD.hb
  have hba := hD.hba
  have ha := hD.ha
  have hf := alD_c2_last hV hD ht0 ht1
  set r1 := alD_lastRow V a θ t with hr1
  have hc2 := alD_mem_compl2 hV hD (cs := cs) ht0 ht1 ht2 ht3 r1 (a + t - 1)
  have hxc : (r1, r1 + (minContent V + (a + t - 1))) ∈ V \ (alD_mark V a θ cs).upper := by
    rw [hc2]
    refine ⟨by omega, by omega, by omega, by omega⟩
  have hxz : (r1, r1 + (minContent V + (a + t - 1))) ∉ alD_Z V a θ := by
    intro h
    rw [alD_mem_Z hV ha.le] at h
    omega
  have hxm : (r1, r1 + (minContent V + (a + t - 1))) ∈ (alD_mark V a θ cs).middle := by
    rw [alD_mem_middle_cell]
    exact ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxc).1, hxz⟩, (Finset.mem_sdiff.mp hxc).2⟩
  have hmax : maxContent (alD_mark V a θ cs).middle = minContent V + (a + t - 1) := by
    apply maxContent_eq_of (k := minContent V + (a + t - 1))
    · have := content_mem_contents hxm
      simpa [content] using this
    · intro k hk
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
      have hy' := (alD_mem_middle_cell y).mp hy
      have hform := alD_cell_form V y
      have h5 : (y.1, y.1 + (minContent V + (content y - minContent V))) ∈
          V \ (alD_mark V a θ cs).upper := by
        rw [← hform]
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy'.1).1, hy'.2⟩
      have h4 := (alD_mem_compl2 hV hD (cs := cs) ht0 ht1 ht2 ht3 y.1
        (content y - minContent V)).mp h5
      omega
  have st := alD_step hV (j := a + t) (by omega) (by omega)
  have l5 := alD_L_le_H hV (j := a + t) (by omega) (by omega)
  have e1 : a + t - 1 + 1 = a + t := by ring
  have hge := ht3 t le_rfl ht1
  have hu := fun r (h : alD_L V (t + a) ≤ r ∧ r ≤ alD_H V (t + a)) =>
    alD_mem_upper_of (cs := cs) hV hD ht0 ht1 hge h
  have e2 : t + a = a + t := by ring
  by_cases hw : r1 ≤ alD_H V (a + t)
  · left
    refine ⟨_, hxm, ?_, ?_⟩
    · simp only [content]
      rw [hmax]; ring
    · have := hu r1 (by rw [e2]; omega)
      have e : r1 + (minContent V + (t + a)) = r1 + (minContent V + (a + t - 1)) + 1 := by ring
      rw [e] at this
      exact this
  · right
    refine ⟨_, hxm, ?_, ?_⟩
    · simp only [content]
      rw [hmax]; ring
    · have := hu (r1 - 1) (by rw [e2]; omega)
      have e : r1 - 1 + (minContent V + (t + a)) = r1 + (minContent V + (a + t - 1)) := by ring
      rw [e] at this
      exact this

end Attach

end GluingCore
