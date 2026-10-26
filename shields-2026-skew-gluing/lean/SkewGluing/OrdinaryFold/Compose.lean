import SkewGluing.Coding

/-!
# Boundary words of a composite with an ordinary mark of case (a)

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-ordinary-endpoints`), in the form used by `prop:gluing-ordinary-fold`: the bits of the
boundary words of `D ∘_ω E` at the exceptional residues read the bits of the outer, and at the
other residues they are the bits of `E`.

For a legal nonempty case-(a) mark with phases `(s, t)`:

* `IsLegalNonempty.wordA_generic`, `wordB_generic`: off the exceptional residue the bit is the bit
  of `E`, and at the residue `0` it is `1` (northwest) and `0` (southeast);
* `IsLegalNonempty.wordA_slot`, `wordB_slot`: at the exceptional residue the bit is the bit of the
  outer, `A_{Jq+t} = A^D_J` and `B_{Jq+s} = B^D_J`, for `m < J ≤ M`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- The northwest word of an ordinary composite at a non-exceptional residue. -/
theorem IsLegalNonempty.wordA_generic (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t) {J a : ℤ} (ha0 : 0 ≤ a)
    (haq : a < ω.period)
    (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a)
    (hJ : a = 0 → minContent D + 1 ≤ J) (hat : a ≠ t) :
    wordA (ω.compose D) ((J - minContent D) * ω.period + a) =
      if a = 0 then 1 else ω.lo (a - 1) - ω.lo a := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := (ordT_eq_zero_iff hmix).mpr hca
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  rw [hc.wordA_class hmin ha0 haq hv hJ]
  exact ord_classBitLo h hD hmix hph ha0 haq hv hJ ⟨fun _ => hat, fun h1 => by
    simp [ordT, hca] at h1⟩

/-- The southeast word of an ordinary composite at a non-exceptional residue. -/
theorem IsLegalNonempty.wordB_generic (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t) {J a : ℤ} (ha0 : 0 ≤ a)
    (haq : a < ω.period)
    (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a)
    (hJ : a = 0 → minContent D + 1 ≤ J) (has : a ≠ s) :
    wordB (ω.compose D) ((J - minContent D) * ω.period + a) =
      if a = 0 then 0 else ω.hi (a - 1) - ω.hi a := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  rw [hc.wordB_class hmin ha0 haq hv hJ]
  exact ord_classBitHi h hD hmix hph ha0 haq hv hJ ⟨fun _ => has, fun h1 => by
    simp [ordT, hca] at h1⟩


/-- **The exceptional bit of the northwest word reads the outer** (case (a)).  For `m < J ≤ M`,
`A_{(J - m) q + t} = A^D_J`, where `m`, `M` are the least and greatest contents of `D`. -/
theorem IsLegalNonempty.wordA_slot (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t)
    (hWlo : ∀ z, 0 ≤ z → z < ω.widthZ → diagLo ω.W (minContent ω.E + z) = ω.lo z) {J : ℤ}
    (h1 : minContent D + 1 ≤ J) (h2 : J ≤ maxContent D) :
    wordA (ω.compose D) ((J - minContent D) * ω.period + t) = bitA D J := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := (ordT_eq_zero_iff hmix).mpr hca
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmin := h.minContent_compose' hD
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hbA : bitA D J = diagLo D (J - 1) - diagLo D J := rfl
  unfold wordA bitA
  rw [hmin]
  by_cases ht0 : t = 0
  · subst ht0
    have e1 : minContent ω.E + minContent D * ω.period + ((J - minContent D) * ω.period + 0) - 1 =
        minContent ω.E + ((J - 1) * ω.period + (ω.period - 1)) := by ring
    have e2 : minContent ω.E + minContent D * ω.period + ((J - minContent D) * ω.period + 0) =
        minContent ω.E + (J * ω.period + 0) := by ring
    rw [e1, e2]
    have F1 := (ordinary_endpoints_a h hD hca hph (J := J - 1) (z := ω.period - 1)
      (by omega)).2.1 (by omega) (by omega) (by omega) (by omega)
    have F2 := (ordinary_endpoints_a h hD hca hph (J := J) (z := 0) (le_refl _)).1 hw
      h1 h2
    have W0 := hWlo 0 (le_refl _) (by omega)
    have hcaps := (ord_E_facts h hmix).2.1 hz
    obtain ⟨-, -, hc3⟩ := hcaps.2
    unfold dLo at hc3
    rw [F1.1, F2.1, W0]
    simp only [show ¬ ((0 : ℤ) < 0) by omega, ite_false]
    have e3 : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
    rw [e3]
    simp only [zero_add] at hc3
    omega
  · have ht1' : 1 ≤ t := by omega
    have e1 : minContent ω.E + minContent D * ω.period + ((J - minContent D) * ω.period + t) - 1 =
        minContent ω.E + (J * ω.period + (t - 1)) := by ring
    have e2 : minContent ω.E + minContent D * ω.period + ((J - minContent D) * ω.period + t) =
        minContent ω.E + (J * ω.period + t) := by ring
    rw [e1, e2]
    have F1 := (ordinary_endpoints_a h hD hca hph (J := J) (z := t - 1) (by omega)).1
      (by omega) h1 h2
    have F2 := (ordinary_endpoints_a h hD hca hph (J := J) (z := t) (by omega)).1
      (by omega) h1 h2
    have W1 := hWlo (t - 1) (by omega) (by omega)
    have W2 := hWlo t (by omega) (by omega)
    have hd := ord_data h hmix hph (a := t) ht1' (by omega)
    obtain ⟨d1, -, d3, -, dE, -, dG, -⟩ := hd
    obtain ⟨c1, -, -, -⟩ := dE hz
    obtain ⟨-, c2, -, -⟩ := (dG (by omega)).1 hz
    have c1' := c1 (by omega)
    have c2' := c2 (le_refl _)
    have d3' := d3 (by omega)
    rw [F1.1, F2.1, W1, W2]
    simp only [show t - 1 < t by omega, show ¬ (t < t) by omega, ite_true, ite_false]
    omega


/-- **The exceptional bit of the southeast word reads the outer** (case (a)).  For `m < J ≤ M`,
`B_{(J - m) q + s} = B^D_J`. -/
theorem IsLegalNonempty.wordB_slot (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t)
    (hWhi : ∀ z, 0 ≤ z → z < ω.widthZ →
      diagHi ω.W (minContent ω.E + z) = ω.hi z - if s ≤ z then 1 else 0) {J : ℤ}
    (h1 : minContent D + 1 ≤ J) (h2 : J ≤ maxContent D) :
    wordB (ω.compose D) ((J - minContent D) * ω.period + s) = bitB D J := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := (ordT_eq_zero_iff hmix).mpr hca
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmin := h.minContent_compose' hD
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hbB : bitB D J = diagHi D (J - 1) - diagHi D J := rfl
  unfold wordB bitB
  rw [hmin]
  have e1 : minContent ω.E + minContent D * ω.period + ((J - minContent D) * ω.period + s) - 1 =
      minContent ω.E + (J * ω.period + (s - 1)) := by ring
  have e2 : minContent ω.E + minContent D * ω.period + ((J - minContent D) * ω.period + s) =
      minContent ω.E + (J * ω.period + s) := by ring
  rw [e1, e2]
  have F1 := (ordinary_endpoints_a h hD hca hph (J := J) (z := s - 1) (by omega)).1
    (by omega) h1 h2
  have W1 := hWhi (s - 1) (by omega) (by omega)
  have hd := ord_data h hmix hph (a := s) hs1 hs2
  obtain ⟨-, d2, -, d4, dE, -, dG, dH⟩ := hd
  obtain ⟨-, -, -, c4⟩ := dE hz
  have c4' := c4 (by omega)
  by_cases hsw : s < ω.widthZ
  · have F2 := (ordinary_endpoints_a h hD hca hph (J := J) (z := s) (by omega)).1 hsw h1 h2
    have W2 := hWhi s (by omega) hsw
    obtain ⟨-, -, g3, -⟩ := (dG (by omega)).1 hz
    have g3' := g3 (le_refl _)
    have d4' := d4 (by omega)
    rw [F1.2, F2.2, W1, W2]
    simp only [show s - 1 < s by omega, show ¬ (s < s) by omega, show ¬ (s ≤ s - 1) by omega,
      show s ≤ s by omega, ite_true, ite_false]
    omega
  · have hsw' : s = ω.widthZ := by omega
    have F2 := (ordinary_endpoints_a h hD hca hph (J := J) (z := s)
      (by omega)).2.1 (by omega) (by omega) (by omega) h2
    have F2' := F2
    rw [F1.2, F2.2, W1]
    simp only [show ¬ (s ≤ s - 1) by omega, ite_false]
    obtain ⟨-, -, hh⟩ := (dH hsw').1 hz
    have e3 : s - 1 + ω.period = (s - 1) + ω.period := rfl
    omega

end MarkedInner

end SkewGluing
