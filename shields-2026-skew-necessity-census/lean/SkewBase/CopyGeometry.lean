import SkewBase.ChartSize

/-!
# The copies of `E` in a composite: `lem:copies` (i), (ii)

Formalizes `shields-2026-skew-base-computational.tex`, «The geometry of a chart and two complete
searches» (`sec:roots`): `lem:copies` (i) and (ii), the content ranges of the copies and of the
supplemental copies, and the origins of the copies of the cells on one content of the outer.

Throughout, the inner is translated so that its least content is `0` (`minContent ω.E = 0`), as
in the paper.  A legal mark of period `q` and width `w` then has `E` on the contents
`[0, q + w - 1]`, `W₋` on `[0, w - 1]` and `W₊` on `[q, q + w - 1]`.

* `contents_copy`, `content_mem_supplemental`: the copy of `d` occupies the contents
  `[c(d) q, c(d) q + N_E - 1]` and a supplemental copy attached at `d` occupies contents in
  `[c(d) q + q, c(d) q + N_E - 1]`.
* `origin_mem_iff`: for each content `t` of `D`, the origins `L(d)` of the cells on that content
  are `t v + k e` for `k` in an interval of `h_D(t)` consecutive integers, beginning at
  `originShiftLo`: `[0, h_D(t) - 1]` in case (c) and `[1 - h_D(t), 0]` in case (d).

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-! ### The contents of a legal mark -/

/-- An integer multiple of `q` strictly between `-q` and `q` is zero. -/
theorem eq_zero_of_mul_bounds {a q : ℤ} (hq : 0 < q) (h1 : -q < a * q) (h2 : a * q < q) :
    a = 0 := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · nlinarith
  · nlinarith

/-- The cells of `E` have contents in `[0, q + w - 1]`, when the least content of `E` is `0`. -/
theorem content_bounds_E {ω : MarkedInner} (hω : ω.IsLegal) (hE0 : minContent ω.E = 0) :
    ∀ x ∈ ω.E, 0 ≤ content x ∧ content x ≤ ω.period + ω.width - 1 := by
  intro x hx
  have h := hω.1.contents_eq
  have hm : content x ∈ contents ω.E := content_mem_contents hx
  rw [h, hE0, Finset.mem_Icc] at hm
  omega

/-- The cells of `W₋` have contents in `[0, w - 1]`. -/
theorem content_bounds_W {ω : MarkedInner} (hω : ω.IsLegal) (hE0 : minContent ω.E = 0) :
    ∀ x ∈ ω.W, 0 ≤ content x ∧ content x ≤ ω.width - 1 := by
  intro x hx
  obtain ⟨hE, hm⟩ := hω.1
  rcases hm with ⟨h1, -⟩ | hnon
  · simp [h1] at hx
  · have := (hnon.content_bounds hE).1 x hx
    rw [hE0] at this
    omega

/-- The cells of `W₊` have contents in `[q, q + w - 1]`. -/
theorem content_bounds_upper {ω : MarkedInner} (hω : ω.IsLegal) (hE0 : minContent ω.E = 0) :
    ∀ x ∈ ω.upper, ω.period ≤ content x ∧ content x ≤ ω.period + ω.width - 1 := by
  intro x hx
  unfold MarkedInner.upper at hx
  have h := content_bounds_W hω hE0 (x - ω.v) (mem_translate.mp hx)
  rw [MarkedInner.content_sub] at h
  have hq : ω.period = content ω.v := rfl
  omega

/-! ### `lem:copies` (i) -/

/-- **`lem:copies` (i), first half.**  The copy of `d` occupies the contents
`[c(d) q, c(d) q + N_E - 1]`, with `N_E = q + w`. -/
theorem contents_copy {ω : MarkedInner} (hω : ω.IsLegal) (hE0 : minContent ω.E = 0)
    (D : Diagram) (d : ℤ × ℤ) :
    contents (translate (ω.origin D d) ω.E) =
      Finset.Icc (content d * ω.period) (content d * ω.period + ω.period + ω.width - 1) := by
  rw [contents_translate, hω.1.contents_eq, hE0, MarkedInner.content_origin]
  ext k
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨k - content d * ω.period, ⟨by omega, by omega⟩, by ring⟩

/-- **`lem:copies` (i), second half.**  A supplemental copy attached at `d` occupies contents in
`[c(d) q + q, c(d) q + N_E - 1]`. -/
theorem content_mem_supplemental {ω : MarkedInner} (hω : ω.IsLegal) (hE0 : minContent ω.E = 0)
    (D : Diagram) (d : ℤ × ℤ) {x : ℤ × ℤ}
    (hx : x ∈ translate (ω.origin D d + ω.supplementalShift) ω.upper) :
    content d * ω.period + ω.period ≤ content x ∧
      content x ≤ content d * ω.period + ω.period + ω.width - 1 := by
  have h := content_bounds_upper hω hE0 (x - (ω.origin D d + ω.supplementalShift))
    (mem_translate.mp hx)
  rw [MarkedInner.content_sub, content_add, MarkedInner.content_origin,
    MarkedInner.content_supplementalShift] at h
  omega

/-- The cells of the copy of `d` have contents in `[c(d) q, c(d) q + q + w - 1]`. -/
theorem content_mem_copy {ω : MarkedInner} (hω : ω.IsLegal) (hE0 : minContent ω.E = 0)
    (D : Diagram) (d : ℤ × ℤ) {x : ℤ × ℤ} (hx : x ∈ translate (ω.origin D d) ω.E) :
    content d * ω.period ≤ content x ∧
      content x ≤ content d * ω.period + ω.period + ω.width - 1 := by
  have := content_mem_contents hx
  rw [contents_copy hω hE0, Finset.mem_Icc] at this
  exact this

/-! ### `lem:copies` (ii) -/

/-- The coefficient `k` of `e` in the origin `L(d) = c(d) v + k e` of the cell `d`:
`i`, `-i`, `i - ℓ_t`, `-(h_t - i)` in cases (a)–(d), for `d = (i, i + t)`. -/
def originShift (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) : ℤ :=
  match ω.case with
  | .a => d.1
  | .b => -d.1
  | .c => d.1 - diagLo D (content d)
  | .d => -(diagHi D (content d) - d.1)

/-- The origin is `c(d) v + k e`, with `k = originShift`. -/
theorem origin_eq_smul (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) :
    ω.origin D d = content d • ω.v + originShift ω D d • eCell := by
  unfold MarkedInner.origin originShift
  cases ω.case
  · rfl
  · simp [sub_eq_add_neg, neg_smul]
  · simp [sub_eq_add_neg]
  · change content d • ω.v - (diagHi D (content d) - d.1) • eCell =
      content d • ω.v + (-(diagHi D (content d) - d.1)) • eCell
    rw [neg_smul, sub_eq_add_neg]

/-- The least coefficient `k` of `e` among the origins of the cells on content `t` of `D`:
`ℓ_t`, `-h_t`, `0`, `1 - H_t` in cases (a)–(d), where `H_t` is the height of the diagonal. -/
def originShiftLo (ω : MarkedInner) (D : Diagram) (t : ℤ) : ℤ :=
  match ω.case with
  | .a => diagLo D t
  | .b => -diagHi D t
  | .c => 0
  | .d => -(diagHi D t - diagLo D t)

/-- **`lem:copies` (ii).**  For each content `t` of `D`, the origins of the copies of the
cells on content `t` are `t v + k e` for the `k` in the interval of `H_t = height D t`
consecutive integers beginning at `originShiftLo`. -/
theorem origin_mem_iff {ω : MarkedInner} {D : Diagram} (hD : IsConnectedSkew D) {t : ℤ}
    (ht : t ∈ contents D) (k : ℤ) :
    (∃ d ∈ D, content d = t ∧ ω.origin D d = t • ω.v + k • eCell) ↔
      originShiftLo ω D t ≤ k ∧ k ≤ originShiftLo ω D t + height D t - 1 := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hmem : ∀ i, (i, i + t) ∈ D ↔ diagLo D t ≤ i ∧ i ≤ diagHi D t := fun i => by
    rw [hs.mem_iff]; simp [ht]
  have hlh := diagLo_le_diagHi ht
  have hinj : ∀ k k' : ℤ, t • ω.v + k • eCell = t • ω.v + k' • eCell → k = k' := by
    intro k k' h
    have := congrArg Prod.fst (add_left_cancel h)
    simpa [eCell] using this
  unfold originShiftLo height
  constructor
  · rintro ⟨d, hd, hdt, hk⟩
    rw [origin_eq_smul, hdt] at hk
    have hk' := hinj _ _ hk
    obtain ⟨i, j⟩ := d
    have hj : j = i + t := by simp only [content] at hdt; omega
    subst hj
    have h1 := (hmem i).mp hd
    unfold originShift at hk'
    simp only [content_mk_add] at hk'
    cases hc : ω.case <;> simp only [hc] at hk' ⊢ <;> omega
  · intro hk
    cases hc : ω.case
    · refine ⟨(k, k + t), (hmem k).mpr (by simp only [hc] at hk; omega), by simp [content], ?_⟩
      rw [origin_eq_smul]
      simp [originShift, hc, content]
    · refine ⟨(-k, -k + t), (hmem (-k)).mpr (by simp only [hc] at hk; omega), by simp [content], ?_⟩
      rw [origin_eq_smul]
      simp [originShift, hc, content]
    · refine ⟨(k + diagLo D t, k + diagLo D t + t), (hmem _).mpr (by simp only [hc] at hk; omega),
        by simp [content], ?_⟩
      rw [origin_eq_smul]
      simp [originShift, hc, content]
    · refine ⟨(diagHi D t + k, diagHi D t + k + t), (hmem _).mpr (by simp only [hc] at hk; omega),
        by simp [content], ?_⟩
      rw [origin_eq_smul]
      simp [originShift, hc, content]

/-- In case (c) the origins on content `t` are `t v + k e` with `k ∈ [0, H_t - 1]`. -/
theorem origin_mem_iff_c {ω : MarkedInner} {D : Diagram} (hD : IsConnectedSkew D) {t : ℤ}
    (ht : t ∈ contents D) (hc : ω.case = .c) (k : ℤ) :
    (∃ d ∈ D, content d = t ∧ ω.origin D d = t • ω.v + k • eCell) ↔
      0 ≤ k ∧ k ≤ height D t - 1 := by
  rw [origin_mem_iff hD ht]
  simp [originShiftLo, hc]

/-- In case (d) the origins on content `t` are `t v + k e` with `k ∈ [1 - H_t, 0]`. -/
theorem origin_mem_iff_d {ω : MarkedInner} {D : Diagram} (hD : IsConnectedSkew D) {t : ℤ}
    (ht : t ∈ contents D) (hc : ω.case = .d) (k : ℤ) :
    (∃ d ∈ D, content d = t ∧ ω.origin D d = t • ω.v + k • eCell) ↔
      1 - height D t ≤ k ∧ k ≤ 0 := by
  rw [origin_mem_iff hD ht]
  unfold originShiftLo height
  simp only [hc]
  constructor <;> intro h <;> omega

end SkewBase
