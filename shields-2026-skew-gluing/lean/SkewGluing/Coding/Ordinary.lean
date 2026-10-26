import SkewGluing.Coding.Words

/-!
# Ordinary composites: class steps

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-holes`, `eq:gluing-caps`, `eq:gluing-ordinary-endpoints`).

For a legal ordinary mark (`ordT = 0` is case (a), `ordT = 1` is case (b)) the first and last rows
of the diagonal of `D ∘_ω E` on the class `(J, a)` have the closed forms `ordLo_formula`,
`ordHi_formula`, in which the outer enters only through `ordGLo`, `ordGHi`.  The class steps follow:
off the exceptional residues they do not depend on `J` (`ord_classBitLo`, `ord_classBitHi`), and at
the first and last block they give the caps (`ord_caps_lo`, `ord_caps_hi`).
`IsLegalNonempty.ordinary_endpoints_a` is `eq:gluing-ordinary-endpoints`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem D_end_singleton (hD : IsConnectedSkew D) {x : ℤ}
    (hx : x = minContent D ∨ x = maxContent D) : diagLo D x = diagHi D x := by
  have := D_ends hD
  rcases hx with rfl | rfl
  · exact this.1
  · exact this.2

/-- For an ordinary mark with phases `s, t`, the offsets `dLo`, `dHi` on the marked residues
(`ordT = 0` is case (a), `ordT = 1` is case (b)). -/
theorem ord_offsets (h : ω.IsLegalNonempty) (hmix : ¬ ω.case.IsMixed) {s t : ℤ}
    (hph : ω.IsPhases s t) {b : ℤ} (h0 : 0 ≤ b) (h1 : b ≤ ω.widthZ - 1) :
    (ω.ordT = 0 → (b < t → ω.dLo b = -1) ∧ (t ≤ b → ω.dLo b = 0) ∧
      (s ≤ b → ω.dHi b = -1) ∧ (b < s → ω.dHi b = 0)) ∧
    (ω.ordT = 1 → (b < t → ω.dHi b = 1) ∧ (t ≤ b → ω.dHi b = 0) ∧
      (s ≤ b → ω.dLo b = 1) ∧ (b < s → ω.dLo b = 0)) := by
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  have hE := (ord_E_facts h hmix).1 b h0 h1
  have e4 := hS b h0 h1
  have e5 := hT b h0 h1
  unfold TailLower at e4
  unfold TailUpper at e5
  refine ⟨fun h0' => ?_, fun h1' => ?_⟩
  · obtain ⟨hA, -, hC⟩ := hE
    have := hA h0'
    refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_, fun hh => ?_⟩
    · have := e5.mpr hh; omega
    · by_contra hn
      have := e5.mp (by omega); omega
    · have := e4.mpr hh; omega
    · by_contra hn
      have := e4.mp (by omega); omega
  · obtain ⟨-, hB, hC⟩ := hE
    have := hB h1'
    refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_, fun hh => ?_⟩
    · have := e5.mpr hh; omega
    · by_contra hn
      have := e5.mp (by omega); omega
    · have := e4.mpr hh; omega
    · by_contra hn
      have := e4.mp (by omega); omega

theorem ordT_eq_zero_iff (hmix : ¬ ω.case.IsMixed) : ω.ordT = 0 ↔ ω.case = .a := by
  unfold ordT
  have hcc : ω.case = .a ∨ ω.case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : ω.case <;> simp_all
  rcases hcc with hc | hc <;> simp [hc]

/-- The correction to the first row of an ordinary composite on the class `(J, a)`, beyond
`J v₁ + ℓ_a`: the closed form of `eq:gluing-ordinary-endpoints` (case (a)) and its analogue for
case (b), with the phases `s, t`.  The class `(M + 1, a)` has only the copy `M`. -/
def ordGLo (ω : MarkedInner) (D : Diagram) (s t J a : ℤ) : ℤ :=
  if ω.ordT = 0 then
    (if J ≤ maxContent D then
      (if minContent D < J ∧ a < ω.widthZ ∧ a < t then diagLo D (J - 1) - 1 else diagLo D J)
     else diagLo D (J - 1) - (if a < t then 1 else 0))
  else
    -(if J ≤ maxContent D then
      (if minContent D < J ∧ a < ω.widthZ ∧ a < s then diagHi D (J - 1) else diagHi D J)
     else diagHi D (J - 1) - (if s ≤ a then 1 else 0))

/-- The correction to the last row of an ordinary composite on the class `(J, a)`, beyond
`J v₁ + h_a`. -/
def ordGHi (ω : MarkedInner) (D : Diagram) (s t J a : ℤ) : ℤ :=
  if ω.ordT = 0 then
    (if J ≤ maxContent D then
      (if minContent D < J ∧ a < ω.widthZ ∧ a < s then diagHi D (J - 1) else diagHi D J)
     else diagHi D (J - 1) - (if s ≤ a then 1 else 0))
  else
    (if J ≤ maxContent D then
      (if minContent D < J ∧ a < ω.widthZ ∧ a < t then 1 - diagLo D (J - 1) else - diagLo D J)
     else - diagLo D (J - 1) + (if a < t then 1 else 0))

set_option maxHeartbeats 1600000 in
-- large linear arithmetic goal with many case splits
theorem ordLo_formula (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hmix : ¬ ω.case.IsMixed) {s t : ℤ} (hph : ω.IsPhases s t) {J a : ℤ} (ha0 : 0 ≤ a)
    (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a) :
    ω.ordLo D J a = J * ω.rowShift + ω.lo a + ω.ordGLo D s t J a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hb : minContent D + 1 ≤ J → J ≤ maxContent D → _ := fun h1 h2 => D_bits hD h1 h2
  have oa : a ≤ ω.widthZ - 1 → _ := fun h2 => ord_offsets h hmix hph (b := a) ha0 h2
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  have hz := ordT_eq_zero_iff hmix
  have ht := ordT_cases hmix
  unfold ValidClass at hv
  unfold dLo dHi at oa
  unfold ordLo ordGLo
  rcases ht with ht | ht
  · have hc := hz.mp ht
    simp only [oRowLo, hc, ht, hp]
    split_ifs <;> omega
  · have hc : ω.case = .b := by
      unfold AttachCase.IsMixed at hmix
      unfold ordT at ht
      cases hh : ω.case <;> simp_all
    simp only [oRowLo, hc, ht, hp, ite_false, one_ne_zero]
    split_ifs <;> omega

set_option maxHeartbeats 1600000 in
-- large linear arithmetic goal with many case splits
theorem ordHi_formula (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hmix : ¬ ω.case.IsMixed) {s t : ℤ} (hph : ω.IsPhases s t) {J a : ℤ} (ha0 : 0 ≤ a)
    (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a) :
    ω.ordHi D J a = J * ω.rowShift + ω.hi a + ω.ordGHi D s t J a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hb : minContent D + 1 ≤ J → J ≤ maxContent D → _ := fun h1 h2 => D_bits hD h1 h2
  have oa : a ≤ ω.widthZ - 1 → _ := fun h2 => ord_offsets h hmix hph (b := a) ha0 h2
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  have hz := ordT_eq_zero_iff hmix
  have ht := ordT_cases hmix
  unfold ValidClass at hv
  unfold dLo dHi at oa
  unfold ordHi ordGHi
  rcases ht with ht | ht
  · have hc := hz.mp ht
    simp only [oRowHi, hc, ht, hp]
    split_ifs <;> omega
  · have hc : ω.case = .b := by
      unfold AttachCase.IsMixed at hmix
      unfold ordT at ht
      cases hh : ω.case <;> simp_all
    simp only [oRowHi, hc, ht, hp, ite_false, one_ne_zero]
    split_ifs <;> omega

/-- **Class steps, first rows, ordinary marks.**  Off the exceptional residue (`t` in case (a), `s`
in case (b)), the step `ℓ_{k-1} - ℓ_k` of the composite on the class `(J, a)` does not depend on the
class `J`: it is `ℓ^E_{a-1} - ℓ^E_a`, and `1` at the residue `a = 0`. -/
theorem ord_classBitLo (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hmix : ¬ ω.case.IsMixed) {s t : ℤ} (hph : ω.IsPhases s t) {J a : ℤ} (ha0 : 0 ≤ a)
    (haq : a < ω.period) (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a)
    (hJ : a = 0 → minContent D + 1 ≤ J)
    (hex : (ω.ordT = 0 → a ≠ t) ∧ (ω.ordT = 1 → a ≠ s)) :
    classBitLo ω.period (ω.ordLo D) J a = if a = 0 then 1 else ω.lo (a - 1) - ω.lo a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hcaps := (ord_E_facts h hmix).2
  have hz := ordT_eq_zero_iff hmix
  have ht := ordT_cases hmix
  unfold classBitLo
  by_cases ha : a = 0
  · subst ha
    have hv' := validClass_prev (ω.period - 1) hv (hJ rfl)
    rw [ordLo_formula h hD hmix hph (by omega) hv', ordLo_formula h hD hmix hph (le_refl _) hv]
    unfold ValidClass at hv
    have hc1 := hcaps
    unfold dLo dHi at hc1
    simp only [zero_add] at hc1
    have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
    unfold ordGLo
    rcases ht with ht | ht
    · have := hex.1 ht
      simp only [ht, ite_true]
      split_ifs <;> omega
    · simp only [ht, one_ne_zero, ite_false]
      split_ifs <;> omega
  · have hv' := validClass_pred hv
    rw [ordLo_formula h hD hmix hph (by omega) hv', ordLo_formula h hD hmix hph ha0 hv]
    simp only [ha, ite_false]
    unfold ordGLo
    have := hex
    unfold ValidClass at hv
    rcases ht with ht | ht
    · have := hex.1 ht
      simp only [ht, ite_true]
      split_ifs <;> omega
    · have := hex.2 ht
      simp only [ht, one_ne_zero, ite_false]
      split_ifs <;> omega

/-- **Class steps, last rows, ordinary marks.**  Off the exceptional residue (`s` in case (a), `t`
in case (b)), the step `h_{k-1} - h_k` of the composite on the class `(J, a)` does not depend on the
class `J`: it is `h^E_{a-1} - h^E_a`, and `0` at the residue `a = 0`. -/
theorem ord_classBitHi (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hmix : ¬ ω.case.IsMixed) {s t : ℤ} (hph : ω.IsPhases s t) {J a : ℤ} (ha0 : 0 ≤ a)
    (haq : a < ω.period) (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a)
    (hJ : a = 0 → minContent D + 1 ≤ J)
    (hex : (ω.ordT = 0 → a ≠ s) ∧ (ω.ordT = 1 → a ≠ t)) :
    classBitHi ω.period (ω.ordHi D) J a = if a = 0 then 0 else ω.hi (a - 1) - ω.hi a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hcaps := (ord_E_facts h hmix).2
  have hz := ordT_eq_zero_iff hmix
  have ht := ordT_cases hmix
  unfold classBitHi
  by_cases ha : a = 0
  · subst ha
    have hv' := validClass_prev (ω.period - 1) hv (hJ rfl)
    rw [ordHi_formula h hD hmix hph (by omega) hv', ordHi_formula h hD hmix hph (le_refl _) hv]
    unfold ValidClass at hv
    have hc1 := hcaps
    unfold dLo dHi at hc1
    simp only [zero_add] at hc1
    have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
    unfold ordGHi
    rcases ht with ht | ht
    · have := hex.1 ht
      simp only [ht, ite_true]
      split_ifs <;> omega
    · simp only [ht, one_ne_zero, ite_false]
      split_ifs <;> omega
  · have hv' := validClass_pred hv
    rw [ordHi_formula h hD hmix hph (by omega) hv', ordHi_formula h hD hmix hph ha0 hv]
    simp only [ha, ite_false]
    unfold ordGHi
    have := hex
    unfold ValidClass at hv
    rcases ht with ht | ht
    · have := hex.1 ht
      simp only [ht, ite_true]
      split_ifs <;> omega
    · have := hex.2 ht
      simp only [ht, one_ne_zero, ite_false]
      split_ifs <;> omega

/-- The facts about `E` used to compute the class steps at the marked residues `a - 1`, `a`
(`1 ≤ a ≤ w`) of an ordinary mark: the bits of `E` and of its upper copy, the offsets read by
the phases, and the end caps. -/
theorem ord_data (h : ω.IsLegalNonempty) (hmix : ¬ ω.case.IsMixed) {s t : ℤ}
    (hph : ω.IsPhases s t) {a : ℤ} (h1 : 1 ≤ a) (h2 : a ≤ ω.widthZ) :
    (ω.lo (a - 1) - ω.lo a = 0 ∨ ω.lo (a - 1) - ω.lo a = 1) ∧
    (ω.hi (a - 1) - ω.hi a = 0 ∨ ω.hi (a - 1) - ω.hi a = 1) ∧
    (a ≤ ω.widthZ - 1 → ω.lo (a - 1 + ω.period) - ω.lo (a + ω.period) = 0 ∨
      ω.lo (a - 1 + ω.period) - ω.lo (a + ω.period) = 1) ∧
    (a ≤ ω.widthZ - 1 → ω.hi (a - 1 + ω.period) - ω.hi (a + ω.period) = 0 ∨
      ω.hi (a - 1 + ω.period) - ω.hi (a + ω.period) = 1) ∧
    (ω.ordT = 0 → (a - 1 < t → ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) = -1) ∧
      (t ≤ a - 1 → ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) = 0) ∧
      (s ≤ a - 1 → ω.hi (a - 1 + ω.period) - ω.rowShift - ω.hi (a - 1) = -1) ∧
      (a - 1 < s → ω.hi (a - 1 + ω.period) - ω.rowShift - ω.hi (a - 1) = 0)) ∧
    (ω.ordT = 1 → (a - 1 < t → ω.hi (a - 1 + ω.period) - ω.rowShift - ω.hi (a - 1) = 1) ∧
      (t ≤ a - 1 → ω.hi (a - 1 + ω.period) - ω.rowShift - ω.hi (a - 1) = 0) ∧
      (s ≤ a - 1 → ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) = 1) ∧
      (a - 1 < s → ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) = 0)) ∧
    (a ≤ ω.widthZ - 1 →
      (ω.ordT = 0 → (a < t → ω.lo (a + ω.period) - ω.rowShift - ω.lo a = -1) ∧
        (t ≤ a → ω.lo (a + ω.period) - ω.rowShift - ω.lo a = 0) ∧
        (s ≤ a → ω.hi (a + ω.period) - ω.rowShift - ω.hi a = -1) ∧
        (a < s → ω.hi (a + ω.period) - ω.rowShift - ω.hi a = 0)) ∧
      (ω.ordT = 1 → (a < t → ω.hi (a + ω.period) - ω.rowShift - ω.hi a = 1) ∧
        (t ≤ a → ω.hi (a + ω.period) - ω.rowShift - ω.hi a = 0) ∧
        (s ≤ a → ω.lo (a + ω.period) - ω.rowShift - ω.lo a = 1) ∧
        (a < s → ω.lo (a + ω.period) - ω.rowShift - ω.lo a = 0))) ∧
    (a = ω.widthZ →
      (ω.ordT = 0 → ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) = 0 ∧
        ω.lo (a - 1) = ω.lo a ∧
        ω.hi (a - 1 + ω.period) - ω.rowShift - ω.hi (a - 1) + (ω.hi (a - 1) - ω.hi a) = 0) ∧
      (ω.ordT = 1 → ω.hi (a - 1 + ω.period) - ω.rowShift - ω.hi (a - 1) = 0 ∧
        ω.hi (a - 1) - ω.hi a = 1 ∧
        ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) + (ω.lo (a - 1) - ω.lo a) = 1)) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have o1 := ord_offsets h hmix hph (b := a - 1) (by omega) (by omega)
  have hcaps := (ord_E_facts h hmix).2
  refine ⟨h.bit_lo' (a := a - 1) (b := a) (by ring) (by omega) (by omega),
    h.bit_hi' (a := a - 1) (b := a) (by ring) (by omega) (by omega),
    fun h3 => h.bit_lo' (a := a - 1 + ω.period) (b := a + ω.period) (by ring) (by omega) (by omega),
    fun h3 => h.bit_hi' (a := a - 1 + ω.period) (b := a + ω.period) (by ring) (by omega) (by omega),
    ?_, ?_, fun h3 => ?_, fun h3 => ?_⟩
  · intro h0
    unfold dLo dHi at o1
    have := o1.1 h0
    omega
  · intro h0
    unfold dLo dHi at o1
    have := o1.2 h0
    omega
  · have o2 := ord_offsets h hmix hph (b := a) (by omega) h3
    unfold dLo dHi at o2
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · have := o2.1 h0
      omega
    · have := o2.2 h0
      omega
  · subst h3
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · have := (hcaps.1 h0).1
      unfold dLo dHi at this
      omega
    · have := (hcaps.2 h0).1
      unfold dLo dHi at this
      omega

/-- The end caps of an ordinary composite for the first-row word (`eq:gluing-caps`). -/
theorem ord_caps_lo (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed)
    {s t : ℤ} (hph : ω.IsPhases s t) :
    (ω.ordT = 0 → 1 ≤ t →
      classBitLo ω.period (ω.ordLo D) (minContent D) t = 1) ∧
    (ω.ordT = 1 → classBitLo ω.period (ω.ordLo D) (minContent D) s = 1) ∧
    (ω.ordT = 0 → classBitLo ω.period (ω.ordLo D) (maxContent D + 1) t = 0) ∧
    (ω.ordT = 1 → s < ω.widthZ →
      classBitLo ω.period (ω.ordLo D) (maxContent D + 1) s = 0) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have he1 := D_end_singleton hD (x := minContent D) (Or.inl rfl)
  have he2 := D_end_singleton hD (x := maxContent D) (Or.inr rfl)
  have hcaps := (ord_E_facts h hmix).2
  have ht := ordT_cases hmix
  have hp : (maxContent D + 1) * ω.rowShift = maxContent D * ω.rowShift + ω.rowShift := by ring
  refine ⟨fun h0 h1 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 h1 => ?_⟩
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) t :=
      Or.inl ⟨le_refl _, hmM⟩
    unfold classBitLo
    simp only [show t ≠ 0 by omega, ite_false]
    rw [ordLo_formula h hD hmix hph (by omega) (validClass_pred hv),
      ordLo_formula h hD hmix hph (by omega) hv]
    have F := ord_data h hmix hph (a := t) h1 (by omega)
    unfold ordGLo
    simp only [h0, ite_true]
    split_ifs <;> omega
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) s :=
      Or.inl ⟨le_refl _, hmM⟩
    unfold classBitLo
    simp only [show s ≠ 0 by omega, ite_false]
    rw [ordLo_formula h hD hmix hph (by omega) (validClass_pred hv),
      ordLo_formula h hD hmix hph (by omega) hv]
    have F := ord_data h hmix hph (a := s) hs1 hs2
    unfold ordGLo
    simp only [h0, one_ne_zero, ite_false]
    split_ifs <;> omega
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D + 1) t :=
      Or.inr ⟨rfl, ht2⟩
    unfold classBitLo
    by_cases ht0 : t = 0
    · subst ht0
      have hv1 := validClass_prev (ω.period - 1) hv (by omega)
      simp only [ite_true]
      rw [ordLo_formula h hD hmix hph (by omega) hv1,
        ordLo_formula h hD hmix hph (le_refl _) hv]
      have hc1 := hcaps
      have o0 := ord_offsets h hmix hph (b := 0) (le_refl _) (by omega)
      unfold dLo dHi at hc1 o0
      simp only [zero_add] at hc1 o0
      unfold ordGLo
      simp only [h0, ite_true, add_sub_cancel_right, hp]
      split_ifs <;> omega
    · simp only [ht0, ite_false]
      rw [ordLo_formula h hD hmix hph (by omega) (validClass_pred hv),
        ordLo_formula h hD hmix hph (by omega) hv]
      have F := ord_data h hmix hph (a := t) (by omega) (by omega)
      unfold ordGLo
      simp only [h0, ite_true, add_sub_cancel_right]
      split_ifs <;> omega
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D + 1) s :=
      Or.inr ⟨rfl, h1⟩
    unfold classBitLo
    simp only [show s ≠ 0 by omega, ite_false]
    rw [ordLo_formula h hD hmix hph (by omega) (validClass_pred hv),
      ordLo_formula h hD hmix hph (by omega) hv]
    have F := ord_data h hmix hph (a := s) hs1 hs2
    unfold ordGLo
    simp only [h0, one_ne_zero, ite_false, add_sub_cancel_right]
    split_ifs <;> omega

/-- The end caps of an ordinary composite for the last-row word (`eq:gluing-caps`). -/
theorem ord_caps_hi (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed)
    {s t : ℤ} (hph : ω.IsPhases s t) :
    (ω.ordT = 0 → classBitHi ω.period (ω.ordHi D) (minContent D) s = 0) ∧
    (ω.ordT = 1 → 1 ≤ t → classBitHi ω.period (ω.ordHi D) (minContent D) t = 0) ∧
    (ω.ordT = 0 → s < ω.widthZ →
      classBitHi ω.period (ω.ordHi D) (maxContent D + 1) s = 1) ∧
    (ω.ordT = 1 → classBitHi ω.period (ω.ordHi D) (maxContent D + 1) t = 1) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have he1 := D_end_singleton hD (x := minContent D) (Or.inl rfl)
  have he2 := D_end_singleton hD (x := maxContent D) (Or.inr rfl)
  have hcaps := (ord_E_facts h hmix).2
  have ht := ordT_cases hmix
  have hp : (maxContent D + 1) * ω.rowShift = maxContent D * ω.rowShift + ω.rowShift := by ring
  refine ⟨fun h0 => ?_, fun h0 h1 => ?_, fun h0 h1 => ?_, fun h0 => ?_⟩
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) s :=
      Or.inl ⟨le_refl _, hmM⟩
    unfold classBitHi
    simp only [show s ≠ 0 by omega, ite_false]
    rw [ordHi_formula h hD hmix hph (by omega) (validClass_pred hv),
      ordHi_formula h hD hmix hph (by omega) hv]
    have F := ord_data h hmix hph (a := s) hs1 hs2
    unfold ordGHi
    simp only [h0, ite_true]
    split_ifs <;> omega
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) t :=
      Or.inl ⟨le_refl _, hmM⟩
    unfold classBitHi
    simp only [show t ≠ 0 by omega, ite_false]
    rw [ordHi_formula h hD hmix hph (by omega) (validClass_pred hv),
      ordHi_formula h hD hmix hph (by omega) hv]
    have F := ord_data h hmix hph (a := t) h1 (by omega)
    unfold ordGHi
    simp only [h0, one_ne_zero, ite_false]
    split_ifs <;> omega
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D + 1) s :=
      Or.inr ⟨rfl, h1⟩
    unfold classBitHi
    simp only [show s ≠ 0 by omega, ite_false]
    rw [ordHi_formula h hD hmix hph (by omega) (validClass_pred hv),
      ordHi_formula h hD hmix hph (by omega) hv]
    have F := ord_data h hmix hph (a := s) hs1 hs2
    unfold ordGHi
    simp only [h0, ite_true, add_sub_cancel_right]
    split_ifs <;> omega
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D + 1) t :=
      Or.inr ⟨rfl, ht2⟩
    unfold classBitHi
    by_cases ht0 : t = 0
    · subst ht0
      have hv1 := validClass_prev (ω.period - 1) hv (by omega)
      simp only [ite_true]
      rw [ordHi_formula h hD hmix hph (by omega) hv1,
        ordHi_formula h hD hmix hph (le_refl _) hv]
      have hc1 := hcaps
      have o0 := ord_offsets h hmix hph (b := 0) (le_refl _) (by omega)
      unfold dLo dHi at hc1 o0
      simp only [zero_add] at hc1 o0
      unfold ordGHi
      simp only [h0, one_ne_zero, ite_false, add_sub_cancel_right, hp]
      split_ifs <;> omega
    · simp only [ht0, ite_false]
      rw [ordHi_formula h hD hmix hph (by omega) (validClass_pred hv),
        ordHi_formula h hD hmix hph (by omega) hv]
      have F := ord_data h hmix hph (a := t) (by omega) (by omega)
      unfold ordGHi
      simp only [h0, one_ne_zero, ite_false, add_sub_cancel_right]
      split_ifs <;> omega

/-- **`eq:gluing-ordinary-endpoints`, case (a).**  Write `a_z = diagLo W₋` and `b_z = diagHi W₋` for
the rows of the lower copy on the residue `z < w`, `v₁` for the row of `v`, `[ℓ_j, h_j]` for the
rows of the outer.  On an interior marked band `m < J ≤ M`
`ℓ_F(Jq + z) = J v₁ + a_z + (ℓ_{J-1} - 1 if z < t, ℓ_J if z ≥ t)` and
`h_F(Jq + z) = J v₁ + b_z + (h_{J-1} if z < s, h_J + 1 if z ≥ s)`; on a private band
`w ≤ z < q`, `m ≤ J ≤ M`, both endpoints use the diagonal `J`; on the first band `J = m` the single
contributing copy gives `ℓ_m`, `h_m` (resp. `h_m + 1`), and on the last band `J = M + 1` it gives
`ℓ_M - 1` (resp. `ℓ_M`) and `h_M`. -/
theorem IsLegalNonempty.ordinary_endpoints_a (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t) {J z : ℤ} (hz0 : 0 ≤ z) :
    (z < ω.widthZ → minContent D + 1 ≤ J → J ≤ maxContent D →
      diagLo (ω.compose D) (minContent ω.E + (J * ω.period + z)) =
        J * ω.rowShift + diagLo ω.W (minContent ω.E + z) +
          (if z < t then diagLo D (J - 1) - 1 else diagLo D J) ∧
      diagHi (ω.compose D) (minContent ω.E + (J * ω.period + z)) =
        J * ω.rowShift + diagHi ω.W (minContent ω.E + z) +
          (if z < s then diagHi D (J - 1) else diagHi D J + 1)) ∧
    (ω.widthZ ≤ z → z < ω.period → minContent D ≤ J → J ≤ maxContent D →
      diagLo (ω.compose D) (minContent ω.E + (J * ω.period + z)) =
        J * ω.rowShift + ω.lo z + diagLo D J ∧
      diagHi (ω.compose D) (minContent ω.E + (J * ω.period + z)) =
        J * ω.rowShift + ω.hi z + diagHi D J) ∧
    (z < ω.widthZ → J = minContent D →
      diagLo (ω.compose D) (minContent ω.E + (J * ω.period + z)) =
        J * ω.rowShift + diagLo ω.W (minContent ω.E + z) + diagLo D J ∧
      diagHi (ω.compose D) (minContent ω.E + (J * ω.period + z)) =
        J * ω.rowShift + diagHi ω.W (minContent ω.E + z) +
          (if z < s then diagHi D J else diagHi D J + 1)) ∧
    (z < ω.widthZ → J = maxContent D + 1 →
      diagLo (ω.compose D) (minContent ω.E + (J * ω.period + z)) =
        J * ω.rowShift + diagLo ω.W (minContent ω.E + z) +
          (diagLo D (J - 1) - (if z < t then 1 else 0)) ∧
      diagHi (ω.compose D) (minContent ω.E + (J * ω.period + z)) =
        J * ω.rowShift + diagHi ω.W (minContent ω.E + z) + diagHi D (J - 1)) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := (ordT_eq_zero_iff hmix).mpr hca
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hc := ord_classRows h hD hmix
  have hF : ∀ (hq' : z < ω.period), ValidClass (minContent D) (maxContent D) ω.widthZ J z →
      diagLo (ω.compose D) (minContent ω.E + (J * ω.period + z)) =
        J * ω.rowShift + ω.lo z + ω.ordGLo D s t J z ∧
      diagHi (ω.compose D) (minContent ω.E + (J * ω.period + z)) =
        J * ω.rowShift + ω.hi z + ω.ordGHi D s t J z := fun hq' hv =>
    ⟨by rw [hc.diagLo_eq hz0 hq' hv]; exact ordLo_formula h hD hmix hph hz0 hv,
     by rw [hc.diagHi_eq hz0 hq' hv]; exact ordHi_formula h hD hmix hph hz0 hv⟩
  refine ⟨fun h1 h2 h3 => ?_, fun h1 h2 h3 h4 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J z := Or.inl ⟨by omega, h3⟩
    obtain ⟨e1, e2⟩ := hF (by omega) hv
    have hWl := h.diagLo_W hz0 (by omega : z ≤ ω.widthZ - 1)
    have hWh := h.diagHi_W hz0 (by omega : z ≤ ω.widthZ - 1)
    have o := (ord_offsets h hmix hph hz0 (by omega : z ≤ ω.widthZ - 1)).1 hz
    unfold dLo dHi at o
    rw [e1, e2, hWl, hWh]
    unfold ordGLo ordGHi
    simp only [hz, ite_true]
    split_ifs <;> omega
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J z := Or.inl ⟨h3, h4⟩
    obtain ⟨e1, e2⟩ := hF h2 hv
    rw [e1, e2]
    unfold ordGLo ordGHi
    simp only [hz, ite_true]
    split_ifs <;> omega
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J z := Or.inl ⟨by omega, by omega⟩
    obtain ⟨e1, e2⟩ := hF (by omega) hv
    have hWl := h.diagLo_W hz0 (by omega : z ≤ ω.widthZ - 1)
    have hWh := h.diagHi_W hz0 (by omega : z ≤ ω.widthZ - 1)
    have o := (ord_offsets h hmix hph hz0 (by omega : z ≤ ω.widthZ - 1)).1 hz
    unfold dLo dHi at o
    rw [e1, e2, hWl, hWh]
    unfold ordGLo ordGHi
    simp only [hz, ite_true]
    split_ifs <;> omega
  · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J z := Or.inr ⟨h2, h1⟩
    obtain ⟨e1, e2⟩ := hF (by omega) hv
    have hWl := h.diagLo_W hz0 (by omega : z ≤ ω.widthZ - 1)
    have hWh := h.diagHi_W hz0 (by omega : z ≤ ω.widthZ - 1)
    have o := (ord_offsets h hmix hph hz0 (by omega : z ≤ ω.widthZ - 1)).1 hz
    unfold dLo dHi at o
    rw [e1, e2, hWl, hWh]
    unfold ordGLo ordGHi
    simp only [hz, ite_true]
    split_ifs <;> omega

end MarkedInner

end SkewGluing
