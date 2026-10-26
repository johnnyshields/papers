import SkewGluing.Aligned.Statement
import SkewGluing.Aligned.Lattice
import SkewGluing.Invariance

/-!
# Aligned marks, case (d): the upper mark and the profile of the composite

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-mixed-profile`).

Let `ω` be a legal mark of case (d), `V` a connected outer, `U = V ∘_ω E`, and `η` a legal mark
on `U` whose displacement has content `a q`.  With `b = N_V - a`, this file proves that the copies
of `η` are nonempty (`eta_legalNonempty`), that `a ≤ N_V < 2 a`, that the width of `η` is
`b q + w`, that its row displacement is `a p` so that both copies are southeast-justified
(`eta_rowShift`, `eta_dHi_zero`), and that its attachment case is (d) (`eta_case_d`, from
`case_d_of_justified`).

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

theorem aligned_legalNonempty (hω : ω.IsLegal) (hd : ω.case = .d) :
    ω.IsLegalNonempty := by
  refine ⟨hω, ?_⟩
  rcases hω.1.2 with h | h
  · exact absurd h.2.2 (by simp [hd])
  · exact h.1

/-- The least content of `U = V ∘_ω E`. -/
def alignedC0 (ω : MarkedInner) (V : Diagram) : ℤ :=
  minContent ω.E + minContent V * ω.period

/-- The southeast row of the composite `U` on its relative content `a' = j q + α`:
`(m + j) p + h_α`. -/
theorem U_diagHi (h : ω.IsLegalNonempty) (hd : ω.case = .d) (hV : IsConnectedSkew V) {a' : ℤ}
    (h0 : 0 ≤ a') (h1 : a' ≤ (span V : ℤ) * ω.period + ω.widthZ - 1) :
    diagHi (ω.compose V) (alignedC0 ω V + a') =
      (minContent V + a' / ω.period) * ω.rowShift + ω.hi (a' % ω.period) := by
  obtain ⟨s, t, hph⟩ := h.exists_phases
  have hlt := h.phases_lt (Or.inr hd) hph
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hq0 : 0 < ω.period := by omega
  have hsp := span_eq_of_isConnectedSkew hV
  have hdiv := Int.mul_ediv_add_emod a' ω.period
  have hm0 := Int.emod_nonneg a' hq0.ne'
  have hm1 := Int.emod_lt_of_pos a' hq0
  have hvalid : ValidClass (minContent V) (maxContent V) ω.widthZ
      (minContent V + a' / ω.period) (a' % ω.period) := by
    unfold ValidClass
    by_cases hc : a' / ω.period ≤ maxContent V - minContent V
    · left; have : 0 ≤ a' / ω.period := Int.ediv_nonneg h0 hq0.le
      omega
    · right
      have h2 : a' / ω.period = maxContent V - minContent V + 1 := by
        by_contra hne
        have : maxContent V - minContent V + 2 ≤ a' / ω.period := by omega
        have := mul_le_mul_of_nonneg_right this hq0.le
        nlinarith
      refine ⟨by omega, ?_⟩
      have : (a' / ω.period) * ω.period = (maxContent V - minContent V + 1) * ω.period := by
        rw [h2]
      nlinarith
  have := (h.mixed_profile hV hd hph hlt (J := minContent V + a' / ω.period)
    (a := a' % ω.period) hm0 hm1 hvalid).1
  have e : alignedC0 ω V + a' =
      minContent ω.E + ((minContent V + a' / ω.period) * ω.period + a' % ω.period) := by
    unfold alignedC0
    nlinarith
  rw [e, this]
  unfold hi
  ring


theorem eta_width_eq (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hη : η.IsLegal)
    (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    (η.width : ℤ) = ((span V : ℤ) - a) * ω.period + ω.width := by
  have h1 := hη.1.span_eq
  have h2 := span_compose hV hω
  rw [hU] at h1
  have hper : η.period = a * ω.period := ha
  rw [hper] at h1
  nlinarith

/-- `a ≤ N_V`: the width of `η` is `(N_V - a) q + w`, hence nonnegative. -/
theorem eta_le_span (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hη : η.IsLegal)
    (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    a ≤ (span V : ℤ) := by
  have h1 := hη.1.span_eq
  have h2 := span_compose hV hω
  rw [hU] at h1
  have hq := hω.period_pos
  have hwq := hω.2.2.1.2
  have hper : η.period = a * ω.period := ha
  by_contra hlt
  have h3 : (span V : ℤ) - a ≤ -1 := by omega
  have h4 : ((span V : ℤ) - a) * ω.period ≤ -ω.period := by nlinarith
  have : (0 : ℤ) ≤ (η.width : ℤ) := by positivity
  nlinarith

/-- `N_V < 2a`: upper separation. -/
theorem eta_lt_two_mul (hω : ω.IsLegal) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    (span V : ℤ) < 2 * a := by
  have h1 := hη.1.span_eq
  have h2 := span_compose hV hω
  rw [hU] at h1
  have hq := hω.period_pos
  have hper : η.period = a * ω.period := ha
  have hlt : (η.width : ℤ) < η.period := hη.2.2.1.2
  have hw0 : (0 : ℤ) ≤ (ω.width : ℤ) := by positivity
  by_contra hge
  have h3 : 2 * a ≤ (span V : ℤ) := by omega
  have h4 : 2 * a * ω.period ≤ (span V : ℤ) * ω.period := by nlinarith
  nlinarith

theorem eta_pos (hω : ω.IsLegal) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    0 < a := by
  have := eta_lt_two_mul hω hV hη hU ha
  have : (0 : ℤ) ≤ (span V : ℤ) := by positivity
  omega

theorem eta_width_ge (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hη : η.IsLegal)
    (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    (ω.width : ℤ) ≤ η.width := by
  have h1 := eta_width_eq hω hV hη hU ha
  have h2 := eta_le_span hω hV hη hU ha
  have hq := hω.period_pos
  nlinarith

theorem eta_legalNonempty (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    η.IsLegalNonempty := by
  refine ⟨hη, ?_⟩
  have hl := aligned_legalNonempty hω hd
  have hw := hl.width_pos
  have h1 := eta_width_ge hω hV hη hU ha
  have hwz : ω.widthZ = (ω.width : ℤ) := rfl
  by_contra hne
  have hW : η.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have : η.width = 0 := by simp [width, hW, span, contents]
  omega


/-- The height of the diagonal of `U = V ∘_ω E` at the relative content `x`. -/
def HU (ω : MarkedInner) (V : Diagram) (x : ℤ) : ℤ :=
  height (ω.compose V) (alignedC0 ω V + x)

theorem eta_minContent (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hU : η.E = ω.compose V) :
    minContent η.E = alignedC0 ω V := by
  rw [hU]; exact hω.minContent_compose hV

theorem eta_hi_eq (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hU : η.E = ω.compose V) (x : ℤ) :
    η.hi x = diagHi (ω.compose V) (alignedC0 ω V + x) := by
  unfold hi; rw [eta_minContent hω hV hU, hU]

theorem eta_lo_eq (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hU : η.E = ω.compose V) (x : ℤ) :
    η.lo x = diagLo (ω.compose V) (alignedC0 ω V + x) := by
  unfold lo; rw [eta_minContent hω hV hU, hU]

theorem eta_hi_formula (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hU : η.E = ω.compose V) {a' : ℤ} (h0 : 0 ≤ a')
    (h1 : a' ≤ (span V : ℤ) * ω.period + ω.width - 1) :
    η.hi a' = (minContent V + a' / ω.period) * ω.rowShift + ω.hi (a' % ω.period) := by
  rw [eta_hi_eq hω hV hU]
  exact U_diagHi (aligned_legalNonempty hω hd) hd hV h0 h1

theorem eta_dHi (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    {a' : ℤ} (h0 : 0 ≤ a') (h1 : a' ≤ (η.width : ℤ) - 1) :
    η.dHi a' = a * ω.rowShift - η.rowShift := by
  have hw := eta_width_eq hω hV hη hU ha
  have hq := hω.period_pos
  have hper : η.period = a * ω.period := ha
  have e1 : a' + η.period = a' + a * ω.period := by rw [hper]
  have hb := eta_le_span hω hV hη hU ha
  have hap := eta_pos hω hV hη hU ha
  have hwz : (ω.width : ℤ) = ω.widthZ := rfl
  have haq : 0 ≤ a * ω.period := by positivity
  have hsq : 0 ≤ ((span V : ℤ) - a) * ω.period := by
    have : 0 ≤ (span V : ℤ) - a := by omega
    positivity
  have r1 := eta_hi_formula hω hd hV hU h0 (by nlinarith)
  have r2 := eta_hi_formula (a' := a' + a * ω.period) hω hd hV hU (by omega) (by nlinarith)
  have e2 : (a' + a * ω.period) / ω.period = a' / ω.period + a := by
    rw [Int.add_mul_ediv_right _ _ hq.ne']
  have e3 : (a' + a * ω.period) % ω.period = a' % ω.period := by
    rw [Int.add_mul_emod_self_right]
  unfold dHi
  rw [e1, r1, r2, e2, e3]
  ring


theorem eta_rowShift (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    η.rowShift = a * ω.rowShift := by
  have hl := eta_legalNonempty hω hd hV hη hU ha
  have h1 := hl.dLo_zero_le
  have h2 := hl.last_dLo
  have hw := hl.width_pos
  have e1 := eta_dHi hω hd hV hη hU ha (a' := 0) (le_refl _) (by
    have : η.widthZ = (η.width : ℤ) := rfl
    omega)
  have e2 := eta_dHi hω hd hV hη hU ha (a' := η.widthZ - 1) (by omega) (by
    have : η.widthZ = (η.width : ℤ) := rfl
    omega)
  omega

theorem eta_dHi_zero (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    {a' : ℤ} (h0 : 0 ≤ a') (h1 : a' ≤ η.widthZ - 1) : η.dHi a' = 0 := by
  have := eta_dHi hω hd hV hη hU ha h0 (by have : η.widthZ = (η.width : ℤ) := rfl; omega)
  rw [this, eta_rowShift hω hd hV hη hU ha]; ring

theorem eta_lo_hi_height (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hU : η.E = ω.compose V)
    (x : ℤ) : η.lo x = η.hi x - HU ω V x + 1 := by
  rw [eta_lo_eq hω hV hU, eta_hi_eq hω hV hU]
  unfold HU height
  ring

/-- The northwest offset of the marked copies of `η` is the height difference of `U`:
`dLo^η(a') = H^U(a') - H^U(a' + a q)` on the marked diagonals of `η`
(`eq:gluing-walk-signs`, first form). -/
theorem eta_dLo (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    {a' : ℤ} (h0 : 0 ≤ a') (h1 : a' ≤ η.widthZ - 1) :
    η.dLo a' = HU ω V a' - HU ω V (a' + a * ω.period) := by
  have hper : η.period = a * ω.period := ha
  have hd0 := eta_dHi_zero hω hd hV hη hU ha h0 h1
  unfold dLo
  unfold dHi at hd0
  rw [hper] at hd0 ⊢
  rw [eta_lo_hi_height hω hV hU, eta_lo_hi_height hω hV hU]
  omega


/-! ### The case of a southeast-justified mark -/

/-- Lower end: if the middle begins on the private diagonal `w`, the cell of the middle on it
has its southern neighbor in `W₋` (the southeast bit between `w - 1` and `w` is one), so the
lower attachment is not horizontal. -/
theorem lowerH_false_of_no_tail (hl : η.IsLegalNonempty)
    (hdHi : ∀ x, 0 ≤ x → x ≤ η.widthZ - 1 → η.dHi x = 0)
    (hb1 : η.hi (η.widthZ - 1) - η.hi η.widthZ = 1) {s t : ℤ} (hph : η.IsPhases s t)
    (hs : s = η.widthZ) : ¬ η.LowerH := by
  rintro ⟨x, hx, hxc, hxW⟩
  have hq := hl.width_lt_period
  have hw := hl.width_pos
  have hcm := hl.contents_middle hph
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  have hmin : minContent η.middle = minContent η.E + η.widthZ := by
    have hk : minContent η.E + s ∈ contents η.middle := by
      rw [hcm, Finset.mem_Icc]; omega
    have := minContent_eq_of hk (fun k' hk' => by
      rw [hcm, Finset.mem_Icc] at hk'; omega)
    rw [this, hs]
  obtain ⟨a, r, rfl⟩ := η.exists_cell x
  have hca : a = η.widthZ := by
    have := hxc
    rw [content_cell, hmin] at this
    omega
  subst hca
  have hxm := (hl.mem_middle_lower hq).mp hx
  have hr : r = η.hi η.widthZ := by
    have := hl.lo_w_eq_hi_w
    omega
  have hA : (η.cell η.widthZ r).1 = r := rfl
  -- the south neighbor lies in `W₋`
  have hS : η.cell (η.widthZ - 1) (r + 1) ∈ η.W := by
    rw [hl.mem_W]
    have hd0 := hdHi (η.widthZ - 1) (by omega) (le_refl _)
    have l1 := hl.lo_le_hi (a := η.widthZ - 1) (by omega) (by omega)
    have l2 := hl.lo_le_hi (a := η.widthZ - 1 + η.period) (by omega) (by omega)
    unfold dHi at hd0
    refine ⟨by omega, le_refl _, by omega, by omega, by omega, by omega⟩
  have hWn : η.cell (η.widthZ - 1) r ∈ η.W := by
    have e : (η.cell η.widthZ r).1 = r := rfl
    have e2 : (η.cell η.widthZ r).2 - 1 = (η.cell (η.widthZ - 1) r).2 := by
      simp only [cell]; ring
    have := hxW
    rw [e, e2] at this
    exact this
  have hsk : IsSkew η.W := hl.nonemptyMark.2.1.1
  have hmem := hsk _ hWn _ hS (by simp [cell]) (by simp only [cell]; omega)
    r (by simp [cell]) (r + (minContent η.E + η.widthZ)) (by
      simp only [cell, Finset.mem_Icc]; omega)
  have hxW' : η.cell η.widthZ r ∈ η.W := hmem
  exact ((hl.mem_middle.mp hx).2.1) hxW'


/-- Upper end: if the middle ends on the private diagonal `q - 1`, the cell of the middle on it
has its eastern neighbor in `W₊` (the southeast bit between `q - 1` and `q` is zero), so the
upper attachment is not vertical. -/
theorem upperV_false_of_no_tail (hl : η.IsLegalNonempty)
    (hdHi : ∀ x, 0 ≤ x → x ≤ η.widthZ - 1 → η.dHi x = 0)
    (hb2 : η.hi (η.period - 1) = η.hi η.period) {s t : ℤ} (hph : η.IsPhases s t)
    (ht : t = 0) : ¬ η.UpperV := by
  rintro ⟨x, hx, hxc, hxW⟩
  have hq := hl.width_lt_period
  have hw := hl.width_pos
  have hcm := hl.contents_middle hph
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  have hmax : maxContent η.middle = minContent η.E + η.period - 1 := by
    have hk : minContent η.E + η.period + t - 1 ∈ contents η.middle := by
      rw [hcm, Finset.mem_Icc]; omega
    have := maxContent_eq_of hk (fun k' hk' => by
      rw [hcm, Finset.mem_Icc] at hk'; omega)
    rw [this, ht]; ring
  obtain ⟨a, r, rfl⟩ := η.exists_cell x
  have hca : a = η.period - 1 := by
    have := hxc
    rw [content_cell, hmax] at this
    omega
  subst hca
  have hxm := (hl.mem_middle_lower (by omega : η.period - 1 < η.period)).mp hx
  have hr : r = η.hi (η.period - 1) := by
    have := hl.lo_pred_period_eq_hi
    omega
  have hup : IsSkew η.upper := isSkew_translate _ hl.nonemptyMark.2.1.1
  -- the eastern neighbor lies in `W₊`
  have hE : η.cell η.period r ∈ η.upper := by
    have e : η.cell η.period r = η.cell (0 + η.period) r := by simp
    rw [e, hl.mem_upper, hl.mem_W]
    have hd0 := hdHi 0 (le_refl _) (by omega)
    have l1 := hl.lo_le_hi (a := 0) (le_refl _) (by omega)
    have l2 := hl.lo_le_hi (a := 0 + η.period) (by omega) (by omega)
    have l0 := hl.lo_zero
    unfold dHi at hd0
    simp only [zero_add] at hd0 l2 ⊢
    refine ⟨le_refl _, by omega, by omega, by omega, by omega, by omega⟩
  have hNn : η.cell η.period (r - 1) ∈ η.upper := by
    have e : (η.cell (η.period - 1) r).1 - 1 = r - 1 := rfl
    have e2 : (η.cell (η.period - 1) r).2 = (η.cell η.period (r - 1)).2 := by
      simp only [cell]; ring
    have := hxW
    rw [e, e2] at this
    exact this
  have hmem := hup _ hNn _ hE (by simp [cell]) (by simp only [cell]; omega)
    r (by simp [cell]) (r + (minContent η.E + (η.period - 1))) (by
      simp only [cell, Finset.mem_Icc]; omega)
  have hxU : η.cell (η.period - 1) r ∈ η.upper := by
    have : η.cell (η.period - 1) r = (r, r + (minContent η.E + (η.period - 1))) := rfl
    rw [this]; exact hmem
  exact ((hl.mem_middle.mp hx).2.2) hxU


/-- A legal mark with nonempty copies whose two copies are southeast-justified on every marked
diagonal, whose southeast row drops by one between the diagonals `w - 1` and `w`, and keeps its
value between the diagonals `q - 1` and `q`, has attachment case (d). -/
theorem case_d_of_justified (hl : η.IsLegalNonempty)
    (hdHi : ∀ x, 0 ≤ x → x ≤ η.widthZ - 1 → η.dHi x = 0)
    (hb1 : η.hi (η.widthZ - 1) - η.hi η.widthZ = 1)
    (hb2 : η.hi (η.period - 1) = η.hi η.period) : η.case = .d := by
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  have hph' := hph
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph'
  have hq := hl.width_lt_period
  have hw := hl.width_pos
  have att := hl.attach
  have hlow : η.case ≠ .a ∧ η.case ≠ .c := by
    by_cases hs' : s ≤ η.widthZ - 1
    · have h1 := (hS s (by omega) hs').mpr le_rfl
      have h2 := hdHi s (by omega) hs'
      unfold TailLower at h1
      constructor
      · intro hc
        have := hl.sides_a hc (a := s) (by omega) hs'
        omega
      · intro hc
        have := hl.sides_c hc (a := s) (by omega) hs'
        omega
    · have hs0 : s = η.widthZ := by omega
      have hnH := lowerH_false_of_no_tail hl hdHi hb1 hph hs0
      exact ⟨fun hc => hnH (att.1 hc).1, fun hc => hnH (att.2.2.1 hc).1⟩
  have hup : η.case ≠ .b ∧ η.case ≠ .c := by
    by_cases ht' : 1 ≤ t
    · have h1 := (hT (t - 1) (by omega) (by omega)).mpr (by omega)
      have h2 := hdHi (t - 1) (by omega) (by omega)
      unfold TailUpper at h1
      constructor
      · intro hc
        have := hl.sides_b hc (a := t - 1) (by omega) (by omega)
        omega
      · intro hc
        have := hl.sides_c hc (a := t - 1) (by omega) (by omega)
        omega
    · have ht0 : t = 0 := by omega
      have hnV := upperV_false_of_no_tail hl hdHi hb2 hph ht0
      exact ⟨fun hc => hnV (att.2.1 hc).2, fun hc => hnV (att.2.2.1 hc).2⟩
  cases hc : η.case <;> simp_all


theorem aligned_divmod_eq {q j r : ℤ} (hq : 0 < q) (h0 : 0 ≤ r) (h1 : r < q) :
    (j * q + r) / q = j ∧ (j * q + r) % q = r := by
  rw [Int.ediv_emod_unique hq]
  exact ⟨by ring, h0, h1⟩

/-- The case of `η` is (d): `lem:gluing-aligned`, case (d), the attachments of the upper mark. -/
theorem eta_case_d (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    η.case = .d := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hηl := eta_legalNonempty hω hd hV hη hU ha
  have hwe := eta_width_eq hω hV hη hU ha
  have hap := eta_pos hω hV hη hU ha
  have hle := eta_le_span hω hV hη hU ha
  have hper : η.period = a * ω.period := ha
  have hwz : η.widthZ = ((span V : ℤ) - a) * ω.period + ω.widthZ := by
    have : η.widthZ = (η.width : ℤ) := rfl
    rw [this, hwe]; rfl
  have hcaps := d_caps hl hd
  refine case_d_of_justified hηl (fun x h0 h1 => eta_dHi_zero hω hd hV hη hU ha h0 h1) ?_ ?_
  · -- the southeast bit at the private diagonal `w`
    have hsq : 0 ≤ ((span V : ℤ) - a) * ω.period := by
      have : 0 ≤ (span V : ℤ) - a := by omega
      positivity
    have haq : 1 ≤ a * ω.period := by nlinarith
    have e1 := aligned_divmod_eq (j := (span V : ℤ) - a) hq0 (by omega : 0 ≤ ω.widthZ - 1)
      (by omega)
    have e2 := aligned_divmod_eq (j := (span V : ℤ) - a) hq0 (by omega : 0 ≤ ω.widthZ) (by omega)
    have hwz' : (ω.width : ℤ) = ω.widthZ := rfl
    have r1 := eta_hi_formula (a' := η.widthZ - 1) hω hd hV hU (by omega) (by nlinarith)
    have r2 := eta_hi_formula (a' := η.widthZ) hω hd hV hU (by omega) (by nlinarith)
    have f1 : η.widthZ - 1 = ((span V : ℤ) - a) * ω.period + (ω.widthZ - 1) := by omega
    rw [r1, r2, f1, hwz, e1.1, e1.2, e2.1, e2.2]
    have := hcaps.1.2.1
    omega
  · have e1 := aligned_divmod_eq (j := a - 1) hq0 (by omega : 0 ≤ ω.period - 1) (by omega)
    have e2 := aligned_divmod_eq (j := a) hq0 (le_refl 0) hq0
    have hsq : 0 ≤ ((span V : ℤ) - a) * ω.period := by
      have : 0 ≤ (span V : ℤ) - a := by omega
      positivity
    have haq : 1 ≤ a * ω.period := by nlinarith
    have f1 : η.period - 1 = (a - 1) * ω.period + (ω.period - 1) := by rw [hper]; ring
    have f2 : η.period = a * ω.period + 0 := by rw [hper]; ring
    have hwz' : (ω.width : ℤ) = ω.widthZ := rfl
    have r1 := eta_hi_formula (a' := η.period - 1) hω hd hV hU (by omega)
      (by rw [hper]; nlinarith)
    have r2 := eta_hi_formula (a' := η.period) hω hd hV hU (by omega) (by rw [hper]; nlinarith)
    have q1 : (η.period - 1) / ω.period = a - 1 := by rw [f1]; exact e1.1
    have q2 : (η.period - 1) % ω.period = ω.period - 1 := by rw [f1]; exact e1.2
    have q3 : η.period / ω.period = a := by rw [f2]; exact e2.1
    have q4 : η.period % ω.period = 0 := by rw [f2]; exact e2.2
    rw [q1, q2] at r1
    rw [q3, q4] at r2
    have h4 := hcaps.2.1
    unfold dHi at h4
    simp only [zero_add] at h4
    have h5 : ω.hi (ω.period - 1) = ω.hi ω.period := hcaps.2.2.1
    rw [r1, r2]
    have : (minContent V + (a - 1)) * ω.rowShift + ω.hi (ω.period - 1) =
        (minContent V + a) * ω.rowShift + ω.hi 0 := by
      rw [h5]
      have : ω.hi ω.period = ω.rowShift + ω.hi 0 := by omega
      rw [this]; ring
    exact this

variable {V : Diagram}

theorem aligned_span_eq (hV : IsConnectedSkew V) :
    (span V : ℤ) = maxContent V - minContent V + 1 := span_eq_of_isConnectedSkew hV

theorem aligned_profM_eq {D : Diagram} {J : ℤ} (h : minContent D ≤ J ∧ J ≤ maxContent D) :
    profM D J = diagHi D J - diagLo D J + 1 := by
  unfold profM; simp only [h.1, h.2, and_self, ite_true]

theorem aligned_profM_eq_zero {D : Diagram} {J : ℤ}
    (h : ¬ (minContent D ≤ J ∧ J ≤ maxContent D)) :
    profM D J = 0 := by
  unfold profM; simp only [h, ite_false]

theorem aligned_profS_eq {D : Diagram} {J : ℤ}
    (h : minContent D + 1 ≤ J ∧ J ≤ maxContent D) :
    profS D J = diagHi D (J - 1) - diagLo D J + 1 := by
  unfold profS; simp only [h.1, h.2, and_self, ite_true]

theorem aligned_profS_eq_one {D : Diagram} {J : ℤ}
    (h : ¬ (minContent D + 1 ≤ J ∧ J ≤ maxContent D)) : profS D J = 1 := by
  unfold profS; exact (ite_eq_right_iff.mpr (fun hh => absurd hh h))


end MarkedInner
end SkewGluing
