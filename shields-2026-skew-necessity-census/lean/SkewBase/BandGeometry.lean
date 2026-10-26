import SkewBase.CopyGeometry
import SkewBase.OuterHeights

/-!
# Bands of a composite: `lem:bands`, `cor:outer`

Formalizes `shields-2026-skew-base-computational.tex`, «The geometry of a chart and two complete
searches» (`sec:roots`): `lem:bands` (i) and (ii) and `cor:outer`.

The inner and the outer are translated so that their least contents are `0`
(`minContent ω.E = 0`, and the outer's contents are `[0, N_D - 1]`).  The *private* contents of
`F = D ∘_ω E` are `t q + w'` with `t` a content of the outer and `w ≤ w' ≤ q - 1`.

* `mem_compose_private_iff`: on a private content `t q + w'` the cells of `F` are the run of rows
  `[a_E(w') + κ_t, a_E(w') + κ_t + h_D(t) + h_E(w') - 2]`, where `κ_t = originRowLo` is the least
  row coordinate of the origins of the copies on content `t` of `D` (`lem:bands` (ii)).
* `height_private`, `diagLo_private`: the height and the least row of `F` on a private content.
* `private_height_eq`, `private_row_eq`: `eq:private`, the heights of the outer and the offsets
  `κ_t - κ_0` read off `F`, independently of `w'`.
* `mem_compose_lower_iff`, `mem_compose_upper_iff`: the bottom and top bands of `F` are the
  copies of the cells of `D` on its least and greatest contents (`lem:bands` (i)).

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-! ### Private contents -/

/-- The least row coordinate `κ_t` of the origins of the copies of the cells on content `t`. -/
def originRowLo (ω : MarkedInner) (D : Diagram) (t : ℤ) : ℤ :=
  t * ω.v.1 + originShiftLo ω D t

/-- On a private content `t q + w'`, a cell of the composite is in a copy of a cell on content
`t` of `D`, and only there. -/
theorem mem_compose_private_content {ω : MarkedInner} (hω : ω.IsLegal)
    (hE0 : minContent ω.E = 0) {D : Diagram} (hD : IsConnectedSkew D) {t w' : ℤ}
    (hw1 : (ω.width : ℤ) ≤ w') (hw2 : w' ≤ ω.period - 1) {x : ℤ × ℤ}
    (hx : content x = t * ω.period + w') :
    x ∈ ω.compose D ↔ ∃ d ∈ D, content d = t ∧ x - ω.origin D d ∈ ω.E := by
  have hq := period_pos hω
  have hw0 : (0 : ℤ) ≤ ω.width := by positivity
  rw [MarkedInner.mem_compose hD.2.1]
  constructor
  · rintro (⟨d, hd, hxd⟩ | ⟨d, hd, -, hxd⟩)
    · have h := content_mem_copy hω hE0 D d hxd
      have key : (content d - t) * ω.period = content d * ω.period - t * ω.period := by ring
      have := eq_zero_of_mul_bounds hq (a := content d - t) (by linarith) (by linarith)
      exact ⟨d, hd, by omega, mem_translate.mp hxd⟩
    · exfalso
      have h := content_mem_supplemental hω hE0 D d hxd
      have key : (content d - t) * ω.period = content d * ω.period - t * ω.period := by ring
      have := eq_zero_of_mul_bounds hq (a := content d - t) (by linarith) (by linarith)
      rw [this] at key
      linarith
  · rintro ⟨d, hd, -, hz⟩
    exact Or.inl ⟨d, hd, mem_translate.mpr hz⟩

/-- The same, by rows: the cell `(r, r + t q + w')` is in the composite iff some cell
`(i, i + t)` of the outer has `(r - L₁, r - L₁ + w') ∈ E`, with `L₁` the row of its origin. -/
theorem mem_compose_private_row {ω : MarkedInner} (hω : ω.IsLegal) (hE0 : minContent ω.E = 0)
    {D : Diagram} (hD : IsConnectedSkew D) {t w' : ℤ} (hw1 : (ω.width : ℤ) ≤ w')
    (hw2 : w' ≤ ω.period - 1) (r : ℤ) :
    (r, r + (t * ω.period + w')) ∈ ω.compose D ↔
      ∃ i, (i, i + t) ∈ D ∧
        (r - (ω.origin D (i, i + t)).1, r - (ω.origin D (i, i + t)).1 + w') ∈ ω.E := by
  rw [mem_compose_private_content hω hE0 hD (t := t) hw1 hw2 (by simp [content])]
  constructor
  · rintro ⟨⟨i, j⟩, hd, hdt, hz⟩
    have hj : j = i + t := by simp only [content] at hdt; omega
    subst hj
    refine ⟨i, hd, ?_⟩
    have hc := MarkedInner.content_origin ω D (i, i + t)
    simp only [content_mk_add] at hc
    have hc' : (ω.origin D (i, i + t)).2 - (ω.origin D (i, i + t)).1 = t * ω.period := hc
    convert hz using 2
    simp only [Prod.snd_sub]
    omega
  · rintro ⟨i, hd, hz⟩
    refine ⟨(i, i + t), hd, by simp [content], ?_⟩
    have hc := MarkedInner.content_origin ω D (i, i + t)
    simp only [content_mk_add] at hc
    have hc' : (ω.origin D (i, i + t)).2 - (ω.origin D (i, i + t)).1 = t * ω.period := hc
    convert hz using 2
    simp only [Prod.snd_sub]
    omega

/-- The row of an origin is `t v₁ + k` for the coefficient `k` of `e`. -/
theorem origin_fst_eq (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) :
    (ω.origin D d).1 = content d * ω.v.1 + originShift ω D d := by
  rw [origin_eq_smul]
  simp [eCell]

/-- The rows of the origins of the copies of the cells on content `t` of `D`: the interval
of `H_t` consecutive integers beginning at `κ_t`. -/
theorem origin_rows_iff {ω : MarkedInner} {D : Diagram} (hD : IsConnectedSkew D) {t : ℤ}
    (ht : t ∈ contents D) (P : ℤ → Prop) :
    (∃ i, (i, i + t) ∈ D ∧ P (ω.origin D (i, i + t)).1) ↔
      ∃ r, originRowLo ω D t ≤ r ∧ r ≤ originRowLo ω D t + height D t - 1 ∧ P r := by
  constructor
  · rintro ⟨i, hi, hP⟩
    refine ⟨_, ?_, ?_, hP⟩
    · have := (origin_mem_iff (ω := ω) hD ht (originShift ω D (i, i + t))).mp
        ⟨(i, i + t), hi, by simp [content], by rw [origin_eq_smul]; simp [content]⟩
      rw [origin_fst_eq]
      simp only [originRowLo, content_mk_add]
      omega
    · have := (origin_mem_iff (ω := ω) hD ht (originShift ω D (i, i + t))).mp
        ⟨(i, i + t), hi, by simp [content], by rw [origin_eq_smul]; simp [content]⟩
      rw [origin_fst_eq]
      simp only [originRowLo, content_mk_add]
      omega
  · rintro ⟨r, h1, h2, hP⟩
    obtain ⟨d, hd, hdt, hk⟩ := (origin_mem_iff (ω := ω) hD ht (r - t * ω.v.1)).mpr
      ⟨by unfold originRowLo at h1; omega, by unfold originRowLo at h2; omega⟩
    refine ⟨d.1, ?_, ?_⟩
    · have : d = (d.1, d.1 + t) := Prod.ext rfl (by simp only [content] at hdt; simp; omega)
      rwa [← this]
    · have e : (d.1, d.1 + t) = d := Prod.ext rfl (by simp only [content] at hdt; simp; omega)
      rw [e, hk]
      simpa [eCell] using hP

/-- **`lem:bands` (ii).**  On the private content `t q + w'` the cells of the composite are the
run of rows `[a_E(w') + κ_t, a_E(w') + κ_t + H_D(t) + H_E(w') - 2]`: `H_D(t) + H_E(w') - 1`
consecutive cells, the least row being `a_E(w') + κ_t`. -/
theorem mem_compose_private_iff {ω : MarkedInner} (hω : ω.IsLegal) (hE0 : minContent ω.E = 0)
    {D : Diagram} (hD : IsConnectedSkew D) {t w' : ℤ} (ht : t ∈ contents D)
    (hw1 : (ω.width : ℤ) ≤ w') (hw2 : w' ≤ ω.period - 1) (r : ℤ) :
    (r, r + (t * ω.period + w')) ∈ ω.compose D ↔
      diagLo ω.E w' + originRowLo ω D t ≤ r ∧
        r ≤ diagLo ω.E w' + originRowLo ω D t + height D t + height ω.E w' - 2 := by
  have hw0 : (0 : ℤ) ≤ ω.width := by positivity
  have hwE : w' ∈ contents ω.E := by
    rw [hω.1.contents_eq, hE0, Finset.mem_Icc]; omega
  have hsE := isConnectedSkew_iff_diagonal.mp hω.1.1
  have hEmem : ∀ j, (j, j + w') ∈ ω.E ↔ diagLo ω.E w' ≤ j ∧ j ≤ diagHi ω.E w' := fun j => by
    rw [hsE.mem_iff]; simp [hwE]
  have hD1 := diagLo_le_diagHi ht
  have hE1 := diagLo_le_diagHi hwE
  rw [mem_compose_private_row hω hE0 hD hw1 hw2,
    origin_rows_iff hD ht (fun o => (r - o, r - o + w') ∈ ω.E)]
  simp only [hEmem]
  unfold height at *
  constructor
  · rintro ⟨r', h1, h2, h3, h4⟩
    omega
  · intro h
    exact ⟨min (originRowLo ω D t + (diagHi D t - diagLo D t + 1) - 1)
      (r - diagLo ω.E w'), by omega, by omega, by omega, by omega⟩

variable {ω : MarkedInner} {D : Diagram}

/-- The private content `t q + w'` is a content of the composite. -/
theorem mem_contents_private (hω : ω.IsLegal) (hE0 : minContent ω.E = 0)
    (hD : IsConnectedSkew D) {t w' : ℤ} (ht : t ∈ contents D) (hw1 : (ω.width : ℤ) ≤ w')
    (hw2 : w' ≤ ω.period - 1) : t * ω.period + w' ∈ contents (ω.compose D) := by
  have hw0 : (0 : ℤ) ≤ ω.width := by positivity
  have hwE : w' ∈ contents ω.E := by
    rw [hω.1.contents_eq, hE0, Finset.mem_Icc]; omega
  have hD1 := diagLo_le_diagHi ht
  have hE1 := diagLo_le_diagHi hwE
  rw [mem_contents_iff]
  refine ⟨diagLo ω.E w' + originRowLo ω D t, ?_⟩
  rw [mem_compose_private_iff hω hE0 hD ht hw1 hw2]
  unfold height
  omega

/-- The least row of the composite on a private content. -/
theorem diagLo_private (hω : ω.IsLegal) (hE0 : minContent ω.E = 0) (hD : IsConnectedSkew D)
    {t w' : ℤ} (ht : t ∈ contents D) (hw1 : (ω.width : ℤ) ≤ w') (hw2 : w' ≤ ω.period - 1) :
    diagLo (ω.compose D) (t * ω.period + w') = diagLo ω.E w' + originRowLo ω D t := by
  have hw0 : (0 : ℤ) ≤ ω.width := by positivity
  have hwE : w' ∈ contents ω.E := by
    rw [hω.1.contents_eq, hE0, Finset.mem_Icc]; omega
  have hD1 := diagLo_le_diagHi ht
  have hE1 := diagLo_le_diagHi hwE
  apply diagLo_eq_of
  · rw [mem_compose_private_iff hω hE0 hD ht hw1 hw2]
    unfold height
    omega
  · intro i hi
    rw [mem_compose_private_iff hω hE0 hD ht hw1 hw2] at hi
    omega

/-- The greatest row of the composite on a private content. -/
theorem diagHi_private (hω : ω.IsLegal) (hE0 : minContent ω.E = 0) (hD : IsConnectedSkew D)
    {t w' : ℤ} (ht : t ∈ contents D) (hw1 : (ω.width : ℤ) ≤ w') (hw2 : w' ≤ ω.period - 1) :
    diagHi (ω.compose D) (t * ω.period + w') =
      diagLo ω.E w' + originRowLo ω D t + height D t + height ω.E w' - 2 := by
  have hw0 : (0 : ℤ) ≤ ω.width := by positivity
  have hwE : w' ∈ contents ω.E := by
    rw [hω.1.contents_eq, hE0, Finset.mem_Icc]; omega
  have hD1 := diagLo_le_diagHi ht
  have hE1 := diagLo_le_diagHi hwE
  apply diagHi_eq_of
  · rw [mem_compose_private_iff hω hE0 hD ht hw1 hw2]
    unfold height at *
    omega
  · intro i hi
    rw [mem_compose_private_iff hω hE0 hD ht hw1 hw2] at hi
    omega

/-- The number of cells of the composite on a private content: `H_D(t) + H_E(w') - 1`. -/
theorem height_private (hω : ω.IsLegal) (hE0 : minContent ω.E = 0) (hD : IsConnectedSkew D)
    {t w' : ℤ} (ht : t ∈ contents D) (hw1 : (ω.width : ℤ) ≤ w') (hw2 : w' ≤ ω.period - 1) :
    height (ω.compose D) (t * ω.period + w') = height D t + height ω.E w' - 1 := by
  unfold height
  rw [diagHi_private hω hE0 hD ht hw1 hw2, diagLo_private hω hE0 hD ht hw1 hw2]
  unfold height
  ring

theorem originRowLo_zero (ω : MarkedInner) {D : Diagram} (hlo : diagLo D 0 = 0)
    (hhi : diagHi D 0 = 0) : originRowLo ω D 0 = 0 := by
  unfold originRowLo originShiftLo
  cases ω.case <;> simp [hlo, hhi]

/-- **`eq:private`, heights.**  The heights of the outer are read off the composite by
`H_D(t) = H_F(t q + w') - H_F(w') + 1`, for every `w' ∈ [w, q - 1]`. -/
theorem private_height_eq (hω : ω.IsLegal) (hE0 : minContent ω.E = 0) (hD : IsConnectedSkew D)
    (h0 : minContent D = 0) {t w' : ℤ} (ht : t ∈ contents D) (hw1 : (ω.width : ℤ) ≤ w')
    (hw2 : w' ≤ ω.period - 1) :
    height D t =
      height (ω.compose D) (t * ω.period + w') - height (ω.compose D) w' + 1 := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hm : (0 : ℤ) ∈ contents D := by rw [← h0]; exact minContent_mem hs.1
  have h1 := height_private hω hE0 hD ht hw1 hw2
  have h2 := height_private hω hE0 hD hm hw1 hw2
  rw [zero_mul, zero_add, height_zero hD h0] at h2
  omega

/-- **`eq:private`, rows.**  The offsets `κ_t - κ_0` are read off the composite by
`a_F(t q + w') - a_F(w')`, for every `w' ∈ [w, q - 1]`. -/
theorem private_row_eq (hω : ω.IsLegal) (hE0 : minContent ω.E = 0) (hD : IsConnectedSkew D)
    (h0 : minContent D = 0) {t w' : ℤ} (ht : t ∈ contents D) (hw1 : (ω.width : ℤ) ≤ w')
    (hw2 : w' ≤ ω.period - 1) :
    diagLo (ω.compose D) (t * ω.period + w') - diagLo (ω.compose D) w' =
      originRowLo ω D t - originRowLo ω D 0 := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hm : (0 : ℤ) ∈ contents D := by rw [← h0]; exact minContent_mem hs.1
  have h1 := diagLo_private hω hE0 hD ht hw1 hw2
  have h2 := diagLo_private hω hE0 hD hm hw1 hw2
  rw [zero_mul, zero_add] at h2
  omega

/-! ### The bottom and top bands -/

/-- A connected outer with `sw D = (0, 0)` has least content `0` and a single cell, the origin, on
it. -/
theorem sw_zero_facts (hD : IsConnectedSkew D) (h : sw D = 0) :
    minContent D = 0 ∧ diagLo D 0 = 0 ∧ diagHi D 0 = 0 := by
  have h1 : diagLo D (minContent D) = 0 := by
    have := congrArg Prod.fst h
    simpa [sw] using this
  have h2 : minContent D = 0 := by
    have := congrArg Prod.snd h
    simp only [sw] at this
    simpa [h1] using this
  rw [h2] at h1
  refine ⟨h2, h1, ?_⟩
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hm : (0 : ℤ) ∈ contents D := by rw [← h2]; exact minContent_mem hs.1
  have := MarkedInner.eq_sw_of_content hD (diagHi_mem hm) (by simp [content, h2])
  rw [h] at this
  simpa using congrArg Prod.fst this

theorem origin_zero (ω : MarkedInner) {D : Diagram} (hlo : diagLo D 0 = 0)
    (hhi : diagHi D 0 = 0) : ω.origin D 0 = 0 := by
  unfold MarkedInner.origin
  cases ω.case <;> simp [content, hlo, hhi]

/-- **`lem:bands` (i), bottom.**  On the contents below `q`, the composite is the copy of the
cell of the outer on its least content, which is `E` itself when `sw D = (0, 0)`. -/
theorem mem_compose_lower_iff (hω : ω.IsLegal) (hE0 : minContent ω.E = 0)
    (hD : IsConnectedSkew D) (hsw : sw D = 0) {x : ℤ × ℤ} (hx : content x < ω.period) :
    x ∈ ω.compose D ↔ x ∈ ω.E := by
  have hq := period_pos hω
  obtain ⟨hm, hlo, hhi⟩ := sw_zero_facts hD hsw
  constructor
  · intro hxF
    rcases (MarkedInner.mem_compose hD.2.1).mp hxF with ⟨d, hd, hxd⟩ | ⟨d, hd, -, hxd⟩
    · have h := content_mem_copy hω hE0 D d hxd
      have hd0 : 0 ≤ content d := hm ▸ minContent_le (content_mem_contents hd)
      have : content d = 0 := by
        by_contra hne
        have : 1 ≤ content d := by omega
        nlinarith [h.1]
      have hdsw := MarkedInner.eq_sw_of_content hD hd (by omega)
      rw [hsw] at hdsw
      subst hdsw
      rw [origin_zero ω hlo hhi] at hxd
      simpa using mem_translate.mp hxd
    · have h := content_mem_supplemental hω hE0 D d hxd
      have hd0 : 0 ≤ content d := hm ▸ minContent_le (content_mem_contents hd)
      nlinarith [h.1]
  · intro hxE
    refine (MarkedInner.mem_compose hD.2.1).mpr (Or.inl ⟨0, ?_, ?_⟩)
    · rw [← hsw]; exact sw_mem hD.2.1
    · rw [origin_zero ω hlo hhi]; exact mem_translate.mpr (by simpa using hxE)

/-- **`lem:bands` (i), top.**  On the contents from `M q + w` up, with `M` the greatest content of
the outer, the composite is the copy of the cell `ne D`. -/
theorem mem_compose_upper_iff (hω : ω.IsLegal) (hE0 : minContent ω.E = 0)
    (hD : IsConnectedSkew D) {x : ℤ × ℤ}
    (hx : maxContent D * ω.period + ω.width ≤ content x) :
    x ∈ ω.compose D ↔ x - ω.origin D (ne D) ∈ ω.E := by
  have hq := period_pos hω
  have hw0 : (0 : ℤ) ≤ ω.width := by positivity
  constructor
  · intro hxF
    rcases (MarkedInner.mem_compose hD.2.1).mp hxF with ⟨d, hd, hxd⟩ | ⟨d, hd, hr, hxd⟩
    · have h := content_mem_copy hω hE0 D d hxd
      have hdM : content d ≤ maxContent D := le_maxContent (content_mem_contents hd)
      have : content d = maxContent D := by
        by_contra hne
        have : content d ≤ maxContent D - 1 := by omega
        nlinarith [h.2]
      have hdne := MarkedInner.eq_ne_of_content hD hd this
      rw [← hdne]
      exact mem_translate.mp hxd
    · exfalso
      have h := content_mem_supplemental hω hE0 D d hxd
      have hn : content (d.1 - 1, d.2) = content d + 1 := by simp [content]; ring
      have hle := le_maxContent (content_mem_contents hr.1)
      rw [hn] at hle
      nlinarith [h.2]
  · intro hxE
    refine (MarkedInner.mem_compose hD.2.1).mpr (Or.inl ⟨ne D, ne_mem hD.2.1, ?_⟩)
    exact mem_translate.mpr hxE

end SkewBase
