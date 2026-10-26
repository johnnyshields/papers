import SkewGluing.Antitranspose
import SkewGluing.Coding
import SkewGluing.OrdinaryFold.Antitranspose

/-!
# Antitransposition of a mixed composite keeps the outer

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`eq:gluing-offsets`), and the "by antitransposition, with the same outer" step to case (c) of
`lem:gluing-coding` (`eq:gluing-interface`).

For a mixed mark `ω` (case (c) or (d)) and a skew outer `D`,
`AT(D ∘_ω E) = D ∘_{ω^{AT}} AT(E)`: the same outer `D`.  On the content `j` the case-(d) origin
`j v - (h_j - i) e` at the cell `(i, i + j)` is the antitransposition of the case-(c) origin
`j v' + (i' - ℓ_j) e` at the reflected cell `i' = ℓ_j + h_j - i` of the same diagonal of `D`
(`reflectDiag`).

**Differs from the paper's route.**  The lower cells of the supplemental pairs of the two cases
are not in bijection under the reflection (the northwest rank condition of case (c) and the
southeast rank condition of case (d) select different pairs of `D`), so the supplemental copies
are not matched one by one.  Instead each supplemental copy is shown to lie in a marked copy
already present unless it sits at an end cell of a diagonal that steps by `(-1, -1)` to the next
one (`ShiftStep`); the reflection exchanges these exceptional supplemental copies of the two
cases (`mem_compose_c`, `mem_compose_d`).

The hypotheses on `ω` are `W₋ ⊆ E` and `W₊ ⊆ E` (conditions of a nonempty mark); without them the
supplemental copies are not controlled.  `antitranspose_compose_all` joins the ordinary case
`MarkedInner.antitranspose_compose`, and `interface_c_of_antitranspose` re-derives
`eq:gluing-interface` in case (c) from case (d).

Sorry-free.
-/

namespace SkewGluing

/-! ## Diagonals of a skew diagram -/

section SkewDiagonals

variable {D : Diagram}

/-- A skew diagram meets the diagonal of content `k` in a full interval of rows. -/
theorem IsSkew.mem_diag_iff (hs : IsSkew D) {k i : ℤ} :
    (i, i + k) ∈ D ↔ k ∈ contents D ∧ diagLo D k ≤ i ∧ i ≤ diagHi D k := by
  constructor
  · intro hi
    exact ⟨mem_contents_iff.mpr ⟨i, hi⟩, diagLo_le hi (by ring), le_diagHi hi (by ring)⟩
  · rintro ⟨hk, h1, h2⟩
    have hlh := diagLo_le_diagHi hk
    exact hs.mem (diagLo_mem hk) (diagHi_mem hk) (by omega) (by omega) h1 h2 (by omega)
      (by omega)

/-- The endpoints of the diagonals of two consecutive contents of a skew diagram move by `0` or
`-1` each. -/
theorem IsSkew.diag_step (hs : IsSkew D) {k : ℤ} (hk0 : k ∈ contents D)
    (hk : k + 1 ∈ contents D) :
    diagLo D k - 1 ≤ diagLo D (k + 1) ∧ diagLo D (k + 1) ≤ diagLo D k ∧
      diagHi D k - 1 ≤ diagHi D (k + 1) ∧ diagHi D (k + 1) ≤ diagHi D k := by
  have hl := diagLo_mem hk0
  have hl1 := diagLo_mem hk
  have hh := diagHi_mem hk0
  have hh1 := diagHi_mem hk
  have e1 : ∀ i, (i, i + k) ∈ D → diagLo D k ≤ i := fun i hi => diagLo_le hi (by ring)
  have e2 : ∀ i, (i, i + (k + 1)) ∈ D → diagLo D (k + 1) ≤ i :=
    fun i hi => diagLo_le hi (by ring)
  have e3 : ∀ i, (i, i + k) ∈ D → i ≤ diagHi D k := fun i hi => le_diagHi hi (by ring)
  have e4 : ∀ i, (i, i + (k + 1)) ∈ D → i ≤ diagHi D (k + 1) :=
    fun i hi => le_diagHi hi (by ring)
  have hlh := diagLo_le_diagHi hk0
  have hlh1 := diagLo_le_diagHi hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hlt
    have h5 := hs.mem hl1 hl (i := diagLo D (k + 1) + 1) (j := diagLo D (k + 1) + 1 + k)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have := e1 _ h5
    omega
  · by_contra hlt
    have h5 := hs.mem hl hl1 (i := diagLo D k) (j := diagLo D k + (k + 1)) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have := e2 (diagLo D k) (by convert h5 using 2)
    omega
  · by_contra hlt
    have h5 := hs.mem hh1 hh (i := diagHi D (k + 1) + 1) (j := diagHi D (k + 1) + 1 + (k + 1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have := e4 (diagHi D (k + 1) + 1) h5
    omega
  · by_contra hlt
    have h5 := hs.mem hh hh1 (i := diagHi D k + 1) (j := diagHi D k + 1 + k) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have := e3 (diagHi D k + 1) h5
    omega

/-- The reflection `i ↦ ℓ_j + h_j - i` of a cell of `D` within its own diagonal. -/
def reflectDiag (D : Diagram) (d : ℤ × ℤ) : ℤ × ℤ :=
  (diagLo D (content d) + diagHi D (content d) - d.1,
    diagLo D (content d) + diagHi D (content d) - d.1 + content d)

theorem content_reflectDiag (D : Diagram) (d : ℤ × ℤ) :
    content (reflectDiag D d) = content d := by
  simp [reflectDiag, content]

theorem reflectDiag_fst (D : Diagram) (d : ℤ × ℤ) :
    (reflectDiag D d).1 = diagLo D (content d) + diagHi D (content d) - d.1 := rfl

theorem reflectDiag_reflectDiag (D : Diagram) (d : ℤ × ℤ) :
    reflectDiag D (reflectDiag D d) = d := by
  have hc := content_reflectDiag D d
  have h1 : (reflectDiag D (reflectDiag D d)).1 = d.1 := by
    rw [reflectDiag_fst, hc, reflectDiag_fst]; ring
  have h2 : (reflectDiag D (reflectDiag D d)).2 = d.2 := by
    have : (reflectDiag D (reflectDiag D d)).2 =
        (reflectDiag D (reflectDiag D d)).1 + content (reflectDiag D (reflectDiag D d)) := by
      simp [content]
    rw [this, h1, content_reflectDiag, hc]
    simp [content]
  exact Prod.ext h1 h2

theorem reflectDiag_mem (hs : IsSkew D) {d : ℤ × ℤ} (hd : d ∈ D) : reflectDiag D d ∈ D := by
  obtain ⟨i, j, rfl⟩ : ∃ i j, d = (i, i + j) := ⟨d.1, content d, by ext <;> simp [content]⟩
  obtain ⟨hj, h1, h2⟩ := hs.mem_diag_iff.mp hd
  have : reflectDiag D (i, i + j) =
      (diagLo D j + diagHi D j - i, diagLo D j + diagHi D j - i + j) := by
    simp [reflectDiag, content]
  rw [this]
  exact hs.mem_diag_iff.mpr ⟨hj, by omega, by omega⟩

end SkewDiagonals

/-- The diagonals of contents `j` and `j + 1` of `D` both occur, and the next one starts and ends
one row earlier: `ℓ_{j+1} = ℓ_j - 1` and `h_{j+1} = h_j - 1`.  These are the steps at which a
supplemental copy of a mixed mark is not already contained in a marked copy. -/
def ShiftStep (D : Diagram) (j : ℤ) : Prop :=
  j ∈ contents D ∧ j + 1 ∈ contents D ∧ diagLo D (j + 1) = diagLo D j - 1 ∧
    diagHi D (j + 1) = diagHi D j - 1

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem origin_eq_c (h : ω.case = .c) (D : Diagram) (d : ℤ × ℤ) :
    ω.origin D d = content d • ω.v + (d.1 - diagLo D (content d)) • eCell := by
  unfold origin; rw [h]

theorem origin_eq_d (h : ω.case = .d) (D : Diagram) (d : ℤ × ℤ) :
    ω.origin D d = content d • ω.v - (diagHi D (content d) - d.1) • eCell := by
  unfold origin; rw [h]

theorem supplementalShift_c (h : ω.case = .c) : ω.supplementalShift = eCell := by
  unfold supplementalShift; rw [h]

theorem translate_subset_translate {A B : Diagram} {t t' : ℤ × ℤ} (ht : t = t') (h : A ⊆ B) :
    translate t A ⊆ translate t' B := by
  subst ht
  intro x hx
  rw [mem_translate] at hx ⊢
  exact h hx

theorem exists_mk (d : ℤ × ℤ) : ∃ i j, d = (i, i + j) :=
  ⟨d.1, content d, by ext <;> simp [content]⟩

/-- **The composite in case (c), with only the exceptional supplemental copies.**  A supplemental
copy of a case-(c) mark is contained in a marked copy unless it sits at the last cell of a
diagonal of `D` that is followed by a `ShiftStep`. -/
theorem mem_compose_c (hc : ω.case = .c) (hW : ω.W ⊆ ω.E) (hU : ω.upper ⊆ ω.E)
    (hs : IsSkew D) (hD : D.Nonempty) {x : ℤ × ℤ} :
    x ∈ ω.compose D ↔ (∃ d ∈ D, x ∈ translate (ω.origin D d) ω.E) ∨
      ∃ d ∈ D, d.1 = diagHi D (content d) ∧ ShiftStep D (content d) ∧
        x ∈ translate (ω.origin D d + eCell) ω.upper := by
  rw [mem_compose hD, supplementalShift_c hc]
  constructor
  · rintro (h | ⟨d, hd, hr, hx⟩)
    · exact Or.inl h
    · obtain ⟨i, j, rfl⟩ := exists_mk d
      simp only [SameRibbon, hc, content_mk_add] at hr
      obtain ⟨hN, hrank⟩ := hr
      have hN' : (i - 1, (i - 1) + (j + 1)) ∈ D := by convert hN using 2; ring
      obtain ⟨hj1, hlN, hhN⟩ := hs.mem_diag_iff.mp hN'
      obtain ⟨hj0, hlj, hhj⟩ := hs.mem_diag_iff.mp hd
      obtain ⟨-, -, hb1, hb2⟩ := hs.diag_step hj0 hj1
      have hlstep : diagLo D (j + 1) = diagLo D j - 1 := by omega
      by_cases hlt : i < diagHi D j
      · left
        refine ⟨(i + 1, i + 1 + j), hs.mem_diag_iff.mpr ⟨hj0, by omega, by omega⟩, ?_⟩
        have hsub : translate (ω.origin D (i, i + j) + eCell) ω.upper ⊆
            translate (ω.origin D (i + 1, i + 1 + j)) ω.E := by
          refine translate_subset_translate ?_ hU
          rw [origin_eq_c hc, origin_eq_c hc]
          simp only [content_mk_add]
          ext <;> simp [eCell] <;> ring
        exact hsub hx
      · have hi : i = diagHi D j := by omega
        by_cases hh : diagHi D (j + 1) = diagHi D j - 1
        · right
          exact ⟨(i, i + j), hd, by simpa only [content_mk_add] using hi,
            by simpa only [content_mk_add] using ⟨hj0, hj1, hlstep, hh⟩, hx⟩
        · left
          have hh' : diagHi D (j + 1) = diagHi D j := by omega
          refine ⟨(i, i + (j + 1)), hs.mem_diag_iff.mpr ⟨hj1, by omega, by omega⟩, ?_⟩
          have hsub : translate (ω.origin D (i, i + j) + eCell) ω.upper ⊆
              translate (ω.origin D (i, i + (j + 1))) ω.E := by
            unfold upper
            rw [translate_translate]
            refine translate_subset_translate ?_ hW
            rw [origin_eq_c hc, origin_eq_c hc]
            simp only [content_mk_add, hlstep]
            ext <;> simp [eCell, add_smul] <;> ring
          exact hsub hx
  · rintro (h | ⟨d, hd, hi, hst, hx⟩)
    · exact Or.inl h
    · refine Or.inr ⟨d, hd, ?_, hx⟩
      obtain ⟨i, j, rfl⟩ := exists_mk d
      simp only [content_mk_add] at hi hst
      obtain ⟨hj0, hj1, hl, hh⟩ := hst
      obtain ⟨-, hlj, hhj⟩ := hs.mem_diag_iff.mp hd
      simp only [SameRibbon, hc, content_mk_add]
      refine ⟨?_, by omega⟩
      have : (i - 1, i + j) = (i - 1, (i - 1) + (j + 1)) := by ext <;> simp
      rw [this]
      exact hs.mem_diag_iff.mpr ⟨hj1, by omega, by omega⟩

/-- **The composite in case (d), with only the exceptional supplemental copies.**  A supplemental
copy of a case-(d) mark is contained in a marked copy unless it sits at the first cell of a
diagonal of `D` that is followed by a `ShiftStep`. -/
theorem mem_compose_d (hc : ω.case = .d) (hU : ω.upper ⊆ ω.E)
    (hs : IsSkew D) (hD : D.Nonempty) {x : ℤ × ℤ} :
    x ∈ ω.compose D ↔ (∃ d ∈ D, x ∈ translate (ω.origin D d) ω.E) ∨
      ∃ d ∈ D, d.1 = diagLo D (content d) ∧ ShiftStep D (content d) ∧
        x ∈ translate (ω.origin D d + -eCell) ω.upper := by
  rw [mem_compose hD, supplementalShift_d hc]
  constructor
  · rintro (h | ⟨d, hd, hr, hx⟩)
    · exact Or.inl h
    · obtain ⟨i, j, rfl⟩ := exists_mk d
      simp only [SameRibbon, hc, content_mk_add] at hr
      obtain ⟨hN, hrank⟩ := hr
      have hN' : (i - 1, (i - 1) + (j + 1)) ∈ D := by convert hN using 2; ring
      obtain ⟨hj1, hlN, hhN⟩ := hs.mem_diag_iff.mp hN'
      obtain ⟨hj0, hlj, hhj⟩ := hs.mem_diag_iff.mp hd
      obtain ⟨hb1, hb2, -, -⟩ := hs.diag_step hj0 hj1
      have hhstep : diagHi D (j + 1) = diagHi D j - 1 := by omega
      by_cases hlt : diagLo D j < i
      · left
        refine ⟨(i - 1, i - 1 + j), hs.mem_diag_iff.mpr ⟨hj0, by omega, by omega⟩, ?_⟩
        have hsub : translate (ω.origin D (i, i + j) + -eCell) ω.upper ⊆
            translate (ω.origin D (i - 1, i - 1 + j)) ω.E := by
          refine translate_subset_translate ?_ hU
          rw [origin_eq_d hc, origin_eq_d hc]
          simp only [content_mk_add]
          ext <;> simp [eCell] <;> ring
        exact hsub hx
      · right
        have hi : i = diagLo D j := by omega
        refine ⟨(i, i + j), hd, by simpa only [content_mk_add] using hi, ?_, hx⟩
        simp only [content_mk_add]
        exact ⟨hj0, hj1, by omega, hhstep⟩
  · rintro (h | ⟨d, hd, hi, hst, hx⟩)
    · exact Or.inl h
    · refine Or.inr ⟨d, hd, ?_, hx⟩
      obtain ⟨i, j, rfl⟩ := exists_mk d
      simp only [content_mk_add] at hi hst
      obtain ⟨hj0, hj1, hl, hh⟩ := hst
      obtain ⟨-, hlj, hhj⟩ := hs.mem_diag_iff.mp hd
      simp only [SameRibbon, hc, content_mk_add]
      refine ⟨?_, by omega⟩
      have : (i - 1, i + j) = (i - 1, (i - 1) + (j + 1)) := by ext <;> simp
      rw [this]
      exact hs.mem_diag_iff.mpr ⟨hj1, by omega, by omega⟩

/-- Membership of an antitransposed cell in a translate: the translation vector is antitransposed
along with the diagram. -/
theorem mem_translate_atVec {t x : ℤ × ℤ} {S : Diagram} :
    atVec x ∈ translate t S ↔ x ∈ translate (atVec t) (antitranspose S) := by
  rw [← mem_antitranspose', antitranspose_translate]

/-- **The origins of the two cases correspond under reflection of the diagonal.**  The case-(d)
origin at the cell `d'` is the antitransposition of the case-(c) origin at the reflected cell. -/
theorem origin_anti_reflectDiag (hc : ω.case = .c) (D : Diagram) (d' : ℤ × ℤ) :
    ω.anti.origin D d' = atVec (ω.origin D (reflectDiag D d')) := by
  have hcd : ω.anti.case = .d := by rw [anti_case, hc]; rfl
  rw [origin_eq_d hcd, origin_eq_c hc]
  simp only [anti_v, content_reflectDiag, reflectDiag_fst, atVec_add, atVec_smul, atVec_eCell]
  ext <;> simp [eCell] <;> ring

/-- **`AT(D ∘_ω E) = D ∘_{ω^{AT}} AT(E)` for a case-(c) mark.** -/
theorem antitranspose_compose_c (hc : ω.case = .c) (hW : ω.W ⊆ ω.E) (hU : ω.upper ⊆ ω.E)
    (hs : IsSkew D) (hD : D.Nonempty) :
    antitranspose (ω.compose D) = ω.anti.compose D := by
  have hcd : ω.anti.case = .d := by rw [anti_case, hc]; rfl
  have hU' : ω.anti.upper ⊆ ω.anti.E := by
    rw [upper_anti, anti_E]; exact antitranspose_subset hU
  ext x
  rw [mem_antitranspose', mem_compose_c hc hW hU hs hD, mem_compose_d hcd hU' hs hD]
  have hshift : atVec eCell = -eCell := atVec_eCell
  constructor
  · rintro (⟨d, hd, hx⟩ | ⟨d, hd, hi, hst, hx⟩)
    · refine Or.inl ⟨reflectDiag D d, reflectDiag_mem hs hd, ?_⟩
      rw [origin_anti_reflectDiag hc, reflectDiag_reflectDiag, anti_E]
      exact mem_translate_atVec.mp hx
    · refine Or.inr ⟨reflectDiag D d, reflectDiag_mem hs hd, ?_, ?_, ?_⟩
      · rw [reflectDiag_fst, content_reflectDiag, hi]; ring
      · rw [content_reflectDiag]; exact hst
      · rw [origin_anti_reflectDiag hc, reflectDiag_reflectDiag, upper_anti, ← hshift,
          ← atVec_add]
        exact mem_translate_atVec.mp hx
  · rintro (⟨d, hd, hx⟩ | ⟨d, hd, hi, hst, hx⟩)
    · refine Or.inl ⟨reflectDiag D d, reflectDiag_mem hs hd, ?_⟩
      rw [origin_anti_reflectDiag hc, anti_E] at hx
      exact mem_translate_atVec.mpr hx
    · refine Or.inr ⟨reflectDiag D d, reflectDiag_mem hs hd, ?_, ?_, ?_⟩
      · rw [reflectDiag_fst, content_reflectDiag, hi]; ring
      · rw [content_reflectDiag]; exact hst
      · rw [origin_anti_reflectDiag hc, upper_anti, ← hshift, ← atVec_add] at hx
        exact mem_translate_atVec.mpr hx

/-- **`AT(D ∘_ω E) = D ∘_{ω^{AT}} AT(E)` for a mixed mark.**  For a mark of case (c) or (d) with
`W₋, W₊ ⊆ E` and a skew outer `D` (nonempty), the antitransposition of the composite is the
composite of the antitransposed mark on the *same* outer. -/
theorem antitranspose_compose_mixed (h : ω.case.IsMixed) (hW : ω.W ⊆ ω.E)
    (hU : ω.upper ⊆ ω.E) (hs : IsSkew D) (hD : D.Nonempty) :
    antitranspose (ω.compose D) = ω.anti.compose D := by
  rcases h with hc | hd
  · exact antitranspose_compose_c hc hW hU hs hD
  · have hc : ω.anti.case = .c := by rw [anti_case, hd]; rfl
    have hW' : ω.anti.W ⊆ ω.anti.E := antitranspose_subset hW
    have hU' : ω.anti.upper ⊆ ω.anti.E := by
      rw [upper_anti, anti_E]; exact antitranspose_subset hU
    have := antitranspose_compose_c hc hW' hU' hs hD
    rw [anti_anti] at this
    rw [← this, antitranspose_antitranspose]

/-- The well-formedness data of a mixed mark give the inclusions `W₋ ⊆ E`, `W₊ ⊆ E`. -/
theorem IsWellFormed.subset_of_mixed (h : ω.IsWellFormed) (hmix : ω.case.IsMixed) :
    ω.W ⊆ ω.E ∧ ω.upper ⊆ ω.E := by
  rcases h.2 with hemp | hnon
  · obtain ⟨-, -, hcase⟩ := hemp
    rcases hmix with hc | hd
    · rw [hcase] at hc; cases hc
    · rw [hcase] at hd; cases hd
  · exact ⟨hnon.2.2.1, hnon.2.2.2.1⟩

/-- **Antitransposition of a mixed composite keeps the outer**, for a legal mark and a connected
skew outer. -/
theorem antitranspose_compose_mixed_of_isLegal (hω : ω.IsLegal) (h : ω.case.IsMixed)
    (hD : IsConnectedSkew D) :
    antitranspose (ω.compose D) = ω.anti.compose D := by
  obtain ⟨hW, hU⟩ := hω.1.subset_of_mixed h
  exact antitranspose_compose_mixed h hW hU hD.1 hD.2.1

/-- **Antitransposition of a composite, all cases.**  For every attachment case and every
nonempty outer `D`, `AT(D ∘_ω E) = D ∘_{ω^{AT}} AT(E)`: the outer is unchanged.  In the ordinary
cases no hypothesis is needed; in the mixed cases the copies of `W` lie in `E` and `D` is
skew. -/
theorem antitranspose_compose_all (hD : D.Nonempty)
    (h : ω.case.IsMixed → ω.W ⊆ ω.E ∧ ω.upper ⊆ ω.E ∧ IsSkew D) :
    antitranspose (ω.compose D) = ω.anti.compose D := by
  by_cases hmix : ω.case.IsMixed
  · obtain ⟨hW, hU, hs⟩ := h hmix
    exact antitranspose_compose_mixed hmix hW hU hs hD
  · exact antitranspose_compose hmix hD

/-- `antitranspose_compose_all` for a legal mark and a connected skew outer. -/
theorem antitranspose_compose_of_isLegal (hω : ω.IsLegal) (hD : IsConnectedSkew D) :
    antitranspose (ω.compose D) = ω.anti.compose D :=
  antitranspose_compose_all hD.2.1 fun hmix =>
    ⟨(hω.1.subset_of_mixed hmix).1, (hω.1.subset_of_mixed hmix).2, hD.1⟩

/-! ## Case (c) of the interface from case (d), by antitransposition -/

theorem widthZ_anti (ω : MarkedInner) : ω.anti.widthZ = ω.widthZ := by
  unfold widthZ; rw [width_anti]

theorem IsLegalNonempty.contents_mem_of_marked (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) :
    minContent ω.E + a ∈ contents ω.E ∧ minContent ω.E + (a + ω.period) ∈ contents ω.E := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [h.contents_E, Finset.mem_Icc, Finset.mem_Icc]
  omega

/-- On the marked diagonals the lower tail of `ω^{AT}` is the antitransposition of the upper
tail: `dLo ω^{AT} a = -dHi ω a`. -/
theorem IsLegalNonempty.dLo_anti (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.anti.dLo a = -ω.dHi a := by
  obtain ⟨m0, m1⟩ := h.contents_mem_of_marked h0 h1
  have hq := period_eq ω
  have hrow : ω.anti.rowShift = -ω.v.2 := rfl
  unfold dLo dHi lo hi
  rw [hrow, period_anti, anti_E, minContent_antitranspose,
    ordFold_diagLo_antitranspose m0, ordFold_diagLo_antitranspose m1]
  unfold rowShift
  omega

/-- `dHi ω^{AT} a = -dLo ω a` on the marked diagonals. -/
theorem IsLegalNonempty.dHi_anti (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.anti.dHi a = -ω.dLo a := by
  obtain ⟨m0, m1⟩ := h.contents_mem_of_marked h0 h1
  have hq := period_eq ω
  have hrow : ω.anti.rowShift = -ω.v.2 := rfl
  unfold dLo dHi lo hi
  rw [hrow, period_anti, anti_E, minContent_antitranspose,
    ordFold_diagHi_antitranspose m0, ordFold_diagHi_antitranspose m1]
  unfold rowShift
  omega

/-- **`ω^{AT}` has the same phases as `ω`.**  The lower tail of `ω^{AT}` lives on the marked
residues where `ω` has its lower tail, and likewise for the upper tail. -/
theorem IsLegalNonempty.isPhases_anti (h : ω.IsLegalNonempty) {s t : ℤ}
    (hph : ω.IsPhases s t) : ω.anti.IsPhases s t := by
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  rw [IsPhases, widthZ_anti]
  refine ⟨hs1, hs2, ht1, ht2, fun a ha0 ha1 => ?_, fun a ha0 ha1 => ?_⟩
  · rw [← hS a ha0 ha1]
    unfold TailLower
    rw [h.dLo_anti ha0 ha1, h.dHi_anti ha0 ha1]
    omega
  · rw [← hT a ha0 ha1]
    unfold TailUpper
    rw [h.dLo_anti ha0 ha1, h.dHi_anti ha0 ha1]
    omega

/-- A legal mark with a nonempty copy has a legal antitransposed mark with a nonempty copy. -/
theorem IsLegalNonempty.anti (h : ω.IsLegalNonempty) : ω.anti.IsLegalNonempty :=
  ⟨isLegal_anti h.1 h.2, antitranspose_nonempty_iff.mpr h.2⟩

/-- **`eq:gluing-interface`, case (c), from case (d) by antitransposition.**  The paper's route
to case (c): `ω^{AT}` is a legal case-(d) mark with the same phases, and `AT(D ∘_ω E) =
D ∘_{ω^{AT}} AT(E)` has the same outer, so the case-(d) interface of `ω^{AT}` gives the case-(c)
interface of `ω` through `A_k(AT F) = 1 - B_k(F)`.  The statement is that of `interface_c`. -/
theorem IsLegalNonempty.interface_c_of_antitranspose (h : ω.IsLegalNonempty)
    (hD : IsConnectedSkew D) (hcc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) {j : ℤ}
    (hj1 : 1 ≤ j) (hj2 : j < (span D : ℤ)) :
    wordB (ω.compose D) (j * ω.period + s) = wordB D j ∧
    wordB (ω.compose D) (j * ω.period + t) = 1 - wordA D j := by
  have hcd : ω.anti.case = .d := by rw [anti_case, hcc]; rfl
  have hAT := antitranspose_compose_mixed (Or.inl hcc) h.nonemptyMark.2.2.1
    h.nonemptyMark.2.2.2.1 hD.1 hD.2.1
  have hleg := h.anti
  obtain ⟨i1, i2⟩ := hleg.interface_d hD hcd (h.isPhases_anti hph) hj1 hj2
  rw [period_anti] at i1 i2
  have hG : IsConnectedSkew (ω.anti.compose D) := hleg.isConnectedSkew_compose_d hD hcd
  have hF : IsConnectedSkew (ω.compose D) := by
    have := isConnectedSkew_antitranspose hG
    rwa [← hAT, antitranspose_antitranspose] at this
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hNr : (span (ω.compose D) : ℤ) = (span D : ℤ) * ω.period + ω.widthZ := by
    rw [h.span_compose_eq hD, span_eq_of_isConnectedSkew hD]
  have hjq : (j + 1) * ω.period ≤ (span D : ℤ) * ω.period :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hjq' : (j + 1) * ω.period = j * ω.period + ω.period := by ring
  have hj0 : ω.period ≤ j * ω.period := le_mul_of_one_le_left (by omega) hj1
  have key : ∀ k, 1 ≤ k → k < (span (ω.compose D) : ℤ) →
      wordB (ω.compose D) k = 1 - wordA (ω.anti.compose D) k := fun k h1 h2 => by
    have := ordFold_wordA_antitranspose hF h1 h2
    rw [hAT] at this
    omega
  constructor
  · rw [key (j * ω.period + s) (by omega) (by omega), i2]; ring
  · rw [key (j * ω.period + t) (by omega) (by omega), i1]

/-- **`lem:gluing-coding`, case (c): `A_w = 0` and `A_q = 1`.**  The northwest word of a case-(c)
composite has `A_w = 0` and `A_q = 1`.  These are the case-(d) bits `B_w = 1`, `B_q = 0` of
`IsLegalNonempty.caps_d`, carried over by antitransposition, which keeps the outer and the phases
and changes the bit pair to `(1 - B, 1 - A)`. -/
theorem IsLegalNonempty.caps_c_wq (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) :
    wordA (ω.compose D) ω.widthZ = 0 ∧ wordA (ω.compose D) ω.period = 1 := by
  have hcd : ω.anti.case = .d := by rw [anti_case, hcc]; rfl
  have hAT := antitranspose_compose_mixed (Or.inl hcc) h.nonemptyMark.2.2.1
    h.nonemptyMark.2.2.2.1 hD.1 hD.2.1
  have hleg := h.anti
  obtain ⟨-, -, -, -, b1, b2⟩ := hleg.caps_d hD hcd (h.isPhases_anti hph)
  rw [widthZ_anti] at b1
  rw [period_anti] at b2
  have hG : IsConnectedSkew (ω.anti.compose D) := hleg.isConnectedSkew_compose_d hD hcd
  have hFG : antitranspose (ω.anti.compose D) = ω.compose D := by
    rw [← hAT, antitranspose_antitranspose]
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hND : (1 : ℤ) ≤ span D := by
    have := span_eq_of_isConnectedSkew hD
    have := minContent_le (maxContent_mem hD.2.1)
    omega
  have hNG : (span (ω.anti.compose D) : ℤ) = (span D : ℤ) * ω.period + ω.widthZ := by
    rw [hleg.span_compose_eq hD, span_eq_of_isConnectedSkew hD, period_anti, widthZ_anti]
  have hqN : ω.period ≤ (span D : ℤ) * ω.period := le_mul_of_one_le_left (by omega) hND
  have key : ∀ k, 1 ≤ k → k < (span (ω.anti.compose D) : ℤ) →
      wordA (ω.compose D) k = 1 - wordB (ω.anti.compose D) k := fun k h1 h2 => by
    have := ordFold_wordA_antitranspose hG h1 h2
    rwa [hFG] at this
  constructor
  · rw [key _ (by omega) (by omega), b1]; norm_num
  · rw [key _ (by omega) (by omega), b2]; norm_num

end MarkedInner

/-! ## Checked examples -/

section Examples

open MarkedInner

/-- A legal case-(c) mark of width three and period four on an eight-cell skew diagram: its
copy `W₋` is the set of cells of `E` that stay in `E` after the translation by `v`. -/
def wideInnerC : MarkedInner where
  E := skewOf [4, 4, 4, 2] [3, 2, 1, 0]
  W := (skewOf [4, 4, 4, 2] [3, 2, 1, 0]).filter fun x =>
    x + (-2, 2) ∈ skewOf [4, 4, 4, 2] [3, 2, 1, 0]
  v := (-2, 2)
  case := .c

example : wideInnerC.IsLegal ∧ wideInnerC.width = 3 := by decide +kernel

/-- The mixed antitransposition on the singleton case-(d) hook mark. -/
example : antitranspose (compose (skewOf [3] []) hookInner) =
    compose (skewOf [3] []) hookInner.anti := by decide +kernel

example : antitranspose (compose (skewOf [3, 3, 2] [1, 1]) hookInner) =
    compose (skewOf [3, 3, 2] [1, 1]) hookInner.anti := by decide +kernel

example : antitranspose (compose (skewOf [4, 4, 2] [2, 1]) hookInner) =
    compose (skewOf [4, 4, 2] [2, 1]) hookInner.anti := by decide +kernel

example : antitranspose (compose (skewOf [3, 2] [1]) hookInner.rotate) =
    compose (skewOf [3, 2] [1]) hookInner.rotate.anti := by decide +kernel

example : antitranspose (compose (skewOf [4, 4, 2] [2, 1]) hookInner.rotate) =
    compose (skewOf [4, 4, 2] [2, 1]) hookInner.rotate.anti := by decide +kernel

/-- The wider case-(c) mark, on an outer with a vertical pair on a shift step. -/
example : antitranspose (compose (skewOf [3, 3, 2] [1, 1]) wideInnerC) =
    compose (skewOf [3, 3, 2] [1, 1]) wideInnerC.anti := by decide +kernel

example : antitranspose (compose (skewOf [5, 4, 4, 2] [3, 2, 1]) wideInnerC) =
    compose (skewOf [5, 4, 4, 2] [3, 2, 1]) wideInnerC.anti := by decide +kernel

/-- The inclusions `W₋ ⊆ E`, `W₊ ⊆ E` cannot be dropped: for the mark with `E = W₋ = {(0, 0)}`,
`v = (0, 5)` (so `W₊ ⊄ E`), the identity fails on the outer `(2, 2)`. -/
example : antitranspose (compose (skewOf [2, 2] []) (⟨{(0, 0)}, {(0, 0)}, (0, 5), .c⟩ :
    MarkedInner)) ≠ compose (skewOf [2, 2] []) (⟨{(0, 0)}, {(0, 0)}, (0, 5), .c⟩ :
    MarkedInner).anti := by decide +kernel

end Examples

end SkewGluing
