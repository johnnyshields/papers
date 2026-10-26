-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/Local/ComposeOrd.lean
import GluingCore.Local.ComposeRows

/-!
# Ordinary composites are connected skew

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3):
`D ∘_ω E` is a connected skew diagram, for a connected outer and a legal ordinary mark, together
with the formula `eq:gluing-ordinary-endpoints` for its diagonals).

The diagonal of the composite on the content `c₀ + (J q + a)` is the union of two row intervals,
the copy `J` on the diagonal `a` of `E` and the copy `J - 1` on the diagonal `a + q` (only for
`a < w`).  The stepping conditions of the diagonal criterion reduce to the end caps of the mark.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- `0` in case (a) and `1` in case (b): an integer flag for the two ordinary cases. -/
def ordT (ω : MarkedInner) : ℤ := if ω.case = .a then 0 else 1

theorem ordT_cases (_hmix : ¬ ω.case.IsMixed) : ω.ordT = 0 ∨ ω.ordT = 1 := by
  unfold ordT; split_ifs <;> simp

theorem oRow_le (hD : IsConnectedSkew D) {j : ℤ} (hj : minContent D ≤ j ∧ j ≤ maxContent D) :
    ω.oRowLo D j ≤ ω.oRowHi D j := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hne : diagLo D j ≤ diagHi D j := diagLo_le_diagHi (hs.mem_contents_iff.mpr hj)
  unfold oRowLo oRowHi
  cases ω.case <;> simp only <;> omega

theorem D_bits (hD : IsConnectedSkew D) {J : ℤ} (h1 : minContent D + 1 ≤ J)
    (h2 : J ≤ maxContent D) :
    (diagLo D (J - 1) - diagLo D J = 0 ∨ diagLo D (J - 1) - diagLo D J = 1) ∧
    (diagHi D (J - 1) - diagHi D J = 0 ∨ diagHi D (J - 1) - diagHi D J = 1) := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have m1 : J ∈ contents D := hs.mem_contents_iff.mpr ⟨by omega, h2⟩
  have m2 : J - 1 ∈ contents D := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
  have := hs.2.2.2.1 J m1 m2
  simp only [bitA, bitB, Finset.mem_insert, Finset.mem_singleton] at this
  exact this

theorem D_ends (hD : IsConnectedSkew D) :
    diagLo D (minContent D) = diagHi D (minContent D) ∧
      diagLo D (maxContent D) = diagHi D (maxContent D) := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hne := hD.2.1
  refine ⟨hs.2.2.2.2 _ (minContent_mem hne) (Or.inl ?_), hs.2.2.2.2 _ (maxContent_mem hne)
    (Or.inr ?_)⟩
  · intro hm; have := minContent_le hm; omega
  · intro hm; have := le_maxContent hm; omega

/-- The origin rows of the diagonals `J - 1` and `J` of `D` differ by a unit in the ordinary
cases: `oRowLo (J-1) - oRowLo J + p` and the analogue for `oRowHi` lie in `{0, 1}` in case (a) and
in `{-1, 0}` in case (b). -/
theorem oRow_diff (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed) {J : ℤ}
    (h1 : minContent D + 1 ≤ J) (h2 : J ≤ maxContent D) :
    (ω.ordT = 0 →
      0 ≤ ω.oRowLo D (J - 1) - ω.oRowLo D J + ω.rowShift ∧
      ω.oRowLo D (J - 1) - ω.oRowLo D J + ω.rowShift ≤ 1 ∧
      0 ≤ ω.oRowHi D (J - 1) - ω.oRowHi D J + ω.rowShift ∧
      ω.oRowHi D (J - 1) - ω.oRowHi D J + ω.rowShift ≤ 1) ∧
    (ω.ordT = 1 →
      -1 ≤ ω.oRowLo D (J - 1) - ω.oRowLo D J + ω.rowShift ∧
      ω.oRowLo D (J - 1) - ω.oRowLo D J + ω.rowShift ≤ 0 ∧
      -1 ≤ ω.oRowHi D (J - 1) - ω.oRowHi D J + ω.rowShift ∧
      ω.oRowHi D (J - 1) - ω.oRowHi D J + ω.rowShift ≤ 0) := by
  have hb := D_bits hD h1 h2
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  have hcc : ω.case = .a ∨ ω.case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : ω.case <;> simp_all
  rcases hcc with hc | hc
  · simp only [oRowLo, oRowHi, ordT, hc, hp]
    simp only [ite_true, zero_ne_one, false_implies, true_implies, and_true]
    omega
  · simp only [oRowLo, oRowHi, ordT, hc, hp]
    simp only [reduceCtorEq, ite_false, one_ne_zero, false_implies, true_implies,
      true_and]
    omega


theorem oRow_ends (hD : IsConnectedSkew D) :
    ω.oRowLo D (minContent D) = ω.oRowHi D (minContent D) ∧
      ω.oRowLo D (maxContent D) = ω.oRowHi D (maxContent D) := by
  have := D_ends hD
  unfold oRowLo oRowHi
  cases ω.case <;> simp only <;> omega

/-- The two lower end caps and the two upper end caps of an ordinary mark, and the bounds on the
offsets `dLo`, `dHi`, in the form used by the stepping conditions. -/
theorem ord_E_facts (h : ω.IsLegalNonempty) (hmix : ¬ ω.case.IsMixed) :
    (∀ a, 0 ≤ a → a ≤ ω.widthZ - 1 →
      (ω.ordT = 0 → ω.dLo a ≤ 0 ∧ ω.dHi a ≤ 0) ∧ (ω.ordT = 1 → 0 ≤ ω.dLo a ∧ 0 ≤ ω.dHi a) ∧
      (-1 ≤ ω.dLo a ∧ ω.dLo a ≤ 1 ∧ -1 ≤ ω.dHi a ∧ ω.dHi a ≤ 1)) ∧
    (ω.ordT = 0 →
      (ω.dLo (ω.widthZ - 1) = 0 ∧ ω.lo (ω.widthZ - 1) = ω.lo ω.widthZ ∧
        ω.dHi (ω.widthZ - 1) + (ω.hi (ω.widthZ - 1) - ω.hi ω.widthZ) = 0) ∧
      (ω.dHi 0 = 0 ∧ ω.hi (ω.period - 1) = ω.hi ω.period ∧
        ω.dLo 0 + (ω.lo (ω.period - 1) - ω.lo ω.period) = 0)) ∧
    (ω.ordT = 1 →
      (ω.dHi (ω.widthZ - 1) = 0 ∧ ω.hi (ω.widthZ - 1) - ω.hi ω.widthZ = 1 ∧
        ω.dLo (ω.widthZ - 1) + (ω.lo (ω.widthZ - 1) - ω.lo ω.widthZ) = 1) ∧
      (ω.dLo 0 = 0 ∧ ω.lo (ω.period - 1) - ω.lo ω.period = 1 ∧
        ω.dHi 0 + (ω.hi (ω.period - 1) - ω.hi ω.period) = 1)) := by
  have hcc : ω.case = .a ∨ ω.case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : ω.case <;> simp_all
  rcases hcc with hc | hc
  · have hT : ω.ordT = 0 := by simp [ordT, hc]
    obtain ⟨hl, hu⟩ := h.attach.1 hc
    refine ⟨fun a h0 h1 => ?_, fun _ => ⟨h.lower_caps_H hl, h.upper_caps_H hu⟩, fun h1 => ?_⟩
    · have s1 := h.sides_a hc h0 h1
      have s2 := h.thin_lower a h0 h1
      have s3 := h.thin_upper h0 h1
      refine ⟨fun _ => s1, fun h2 => by omega, by omega⟩
    · omega
  · have hT : ω.ordT = 1 := by simp [ordT, hc]
    obtain ⟨hl, hu⟩ := h.attach.2.1 hc
    refine ⟨fun a h0 h1 => ?_, fun h1 => by omega, fun _ => ⟨h.lower_caps_V hl, h.upper_caps_V hu⟩⟩
    · have s1 := h.sides_b hc h0 h1
      have s2 := h.thin_lower a h0 h1
      have s3 := h.thin_upper h0 h1
      refine ⟨fun h2 => by omega, fun _ => s1, by omega⟩

theorem ord_diff (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed)
    {J a : ℤ} (hJ1 : minContent D + 1 ≤ J) (hJ2 : J ≤ maxContent D) (ha0 : 0 ≤ a)
    (ha1 : a ≤ ω.widthZ - 1) :
    -1 ≤ (ω.oRowLo D (J - 1) + ω.lo (a + ω.period)) - (ω.oRowLo D J + ω.lo a) ∧
    (ω.oRowLo D (J - 1) + ω.lo (a + ω.period)) - (ω.oRowLo D J + ω.lo a) ≤ 1 ∧
    -1 ≤ (ω.oRowHi D (J - 1) + ω.hi (a + ω.period)) - (ω.oRowHi D J + ω.hi a) ∧
    (ω.oRowHi D (J - 1) + ω.hi (a + ω.period)) - (ω.oRowHi D J + ω.hi a) ≤ 1 := by
  have hD' := oRow_diff (ω := ω) hD hmix hJ1 hJ2
  have hE := (ord_E_facts h hmix).1 a ha0 ha1
  have ht := ordT_cases hmix
  unfold dLo dHi at hE
  omega

/-- The first row of the composite of an ordinary mark on the class `(J, a)`. -/
def ordLo (ω : MarkedInner) (D : Diagram) (J a : ℤ) : ℤ :=
  if minContent D ≤ J ∧ J ≤ maxContent D then
    (if a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D then
      min (ω.oRowLo D J + ω.lo a) (ω.oRowLo D (J - 1) + ω.lo (a + ω.period))
     else ω.oRowLo D J + ω.lo a)
  else ω.oRowLo D (J - 1) + ω.lo (a + ω.period)

/-- The last row of the composite of an ordinary mark on the class `(J, a)`. -/
def ordHi (ω : MarkedInner) (D : Diagram) (J a : ℤ) : ℤ :=
  if minContent D ≤ J ∧ J ≤ maxContent D then
    (if a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D then
      max (ω.oRowHi D J + ω.hi a) (ω.oRowHi D (J - 1) + ω.hi (a + ω.period))
     else ω.oRowHi D J + ω.hi a)
  else ω.oRowHi D (J - 1) + ω.hi (a + ω.period)

theorem ord_stepA_lo (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed)
    {J a : ℤ} (h1 : 1 ≤ a) (h2 : a < ω.period)
    (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a) :
    ω.ordLo D J (a - 1) - ω.ordLo D J a = 0 ∨ ω.ordLo D J (a - 1) - ω.ordLo D J a = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hcaps := (ord_E_facts h hmix).2
  have ht := ordT_cases hmix
  have b1 := h.bit_lo' (a := a - 1) (b := a) (by ring) (by omega) (by omega)
  have b2 : a < ω.widthZ → ω.lo (a - 1 + ω.period) - ω.lo (a + ω.period) = 0 ∨
      ω.lo (a - 1 + ω.period) - ω.lo (a + ω.period) = 1 := fun ha =>
    h.bit_lo' (a := a - 1 + ω.period) (b := a + ω.period) (by ring) (by omega) (by omega)
  have hdJ := oRow_diff (ω := ω) (D := D) hD hmix (J := J)
  unfold ValidClass at hv
  by_cases haw : a = ω.widthZ
  · subst haw
    have hc1 := hcaps
    unfold dLo dHi at hc1
    by_cases hJ : minContent D + 1 ≤ J ∧ J ≤ maxContent D
    · have := hdJ hJ.1 hJ.2
      unfold ordLo
      split_ifs <;> omega
    · unfold ordLo
      split_ifs <;> omega
  · unfold ordLo
    split_ifs <;> omega

theorem ord_stepA_hi (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed)
    {J a : ℤ} (h1 : 1 ≤ a) (h2 : a < ω.period)
    (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a) :
    ω.ordHi D J (a - 1) - ω.ordHi D J a = 0 ∨ ω.ordHi D J (a - 1) - ω.ordHi D J a = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hcaps := (ord_E_facts h hmix).2
  have ht := ordT_cases hmix
  have b1 := h.bit_hi' (a := a - 1) (b := a) (by ring) (by omega) (by omega)
  have b2 : a < ω.widthZ → ω.hi (a - 1 + ω.period) - ω.hi (a + ω.period) = 0 ∨
      ω.hi (a - 1 + ω.period) - ω.hi (a + ω.period) = 1 := fun ha =>
    h.bit_hi' (a := a - 1 + ω.period) (b := a + ω.period) (by ring) (by omega) (by omega)
  have hdJ := oRow_diff (ω := ω) (D := D) hD hmix (J := J)
  unfold ValidClass at hv
  by_cases haw : a = ω.widthZ
  · subst haw
    have hc1 := hcaps
    unfold dLo dHi at hc1
    by_cases hJ : minContent D + 1 ≤ J ∧ J ≤ maxContent D
    · have := hdJ hJ.1 hJ.2
      unfold ordHi
      split_ifs <;> omega
    · unfold ordHi
      split_ifs <;> omega
  · unfold ordHi
    split_ifs <;> omega

set_option maxHeartbeats 800000 in
-- the stepping conditions are large linear-arithmetic goals with many case splits
theorem ord_stepB_lo (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed)
    {J : ℤ} (hv1 : ValidClass (minContent D) (maxContent D) ω.widthZ J (ω.period - 1))
    (hv2 : ValidClass (minContent D) (maxContent D) ω.widthZ (J + 1) 0) :
    ω.ordLo D J (ω.period - 1) - ω.ordLo D (J + 1) 0 = 0 ∨
      ω.ordLo D J (ω.period - 1) - ω.ordLo D (J + 1) 0 = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hcaps := (ord_E_facts h hmix).2
  have ht := ordT_cases hmix
  have b1 := h.bit_lo' (a := ω.period - 1) (b := ω.period) (by ring) (by omega) (by omega)
  have hdJ := oRow_diff (ω := ω) (D := D) hD hmix (J := J + 1)
  simp only [add_sub_cancel_right] at hdJ
  unfold ValidClass at hv1 hv2
  have hc1 := hcaps
  unfold dLo dHi at hc1
  simp only [zero_add] at hc1
  unfold ordLo
  simp only [add_sub_cancel_right, zero_add]
  split_ifs <;> omega

set_option maxHeartbeats 800000 in
-- as for `ord_stepB_lo`
theorem ord_stepB_hi (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed)
    {J : ℤ} (hv1 : ValidClass (minContent D) (maxContent D) ω.widthZ J (ω.period - 1))
    (hv2 : ValidClass (minContent D) (maxContent D) ω.widthZ (J + 1) 0) :
    ω.ordHi D J (ω.period - 1) - ω.ordHi D (J + 1) 0 = 0 ∨
      ω.ordHi D J (ω.period - 1) - ω.ordHi D (J + 1) 0 = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hcaps := (ord_E_facts h hmix).2
  have ht := ordT_cases hmix
  have b1' := h.bit_hi' (a := ω.period - 1) (b := ω.period) (by ring) (by omega) (by omega)
  have hdJ := oRow_diff (ω := ω) (D := D) hD hmix (J := J + 1)
  simp only [add_sub_cancel_right] at hdJ
  unfold ValidClass at hv1 hv2
  have hc1 := hcaps
  unfold dLo dHi at hc1
  simp only [zero_add] at hc1
  unfold ordHi
  simp only [add_sub_cancel_right, zero_add]
  split_ifs <;> omega

theorem ord_classRows (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed) :
    ClassRows (ω.compose D) (minContent ω.E) ω.period ω.widthZ (minContent D) (maxContent D)
      (ω.ordLo D) (ω.ordHi D) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hcaps := (ord_E_facts h hmix).2
  have ht := ordT_cases hmix
  have hends := oRow_ends (ω := ω) hD
  refine ⟨by omega, by omega, hq, hmM, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro J a r h0 h1
    change ω.cell (J * ω.period + a) r ∈ ω.compose D ↔ _
    rw [h.cell_mem_compose_ord hD hmix h0 h1]
    have l1 := h.lo_le_hi (a := a) h0 (by omega)
    have l2 : a < ω.widthZ → ω.lo (a + ω.period) ≤ ω.hi (a + ω.period) :=
      fun ha => h.lo_le_hi (by omega) (by omega)
    have o1 := oRow_le (ω := ω) hD (j := J)
    have o2 := oRow_le (ω := ω) hD (j := J - 1)
    have hd : minContent D + 1 ≤ J ∧ J ≤ maxContent D ∧ a < ω.widthZ →
        (-1 ≤ (ω.oRowLo D (J - 1) + ω.lo (a + ω.period)) - (ω.oRowLo D J + ω.lo a) ∧
        (ω.oRowLo D (J - 1) + ω.lo (a + ω.period)) - (ω.oRowLo D J + ω.lo a) ≤ 1 ∧
        -1 ≤ (ω.oRowHi D (J - 1) + ω.hi (a + ω.period)) - (ω.oRowHi D J + ω.hi a) ∧
        (ω.oRowHi D (J - 1) + ω.hi (a + ω.period)) - (ω.oRowHi D J + ω.hi a) ≤ 1) :=
      fun hh => ord_diff h hD hmix hh.1 hh.2.1 h0 (by omega)
    unfold ValidClass ordLo ordHi
    split_ifs <;> omega
  · intro J a h0 h1 hv
    have l1 := h.lo_le_hi (a := a) h0 (by omega)
    have l2 : a < ω.widthZ → ω.lo (a + ω.period) ≤ ω.hi (a + ω.period) :=
      fun ha => h.lo_le_hi (by omega) (by omega)
    have o1 := oRow_le (ω := ω) hD (j := J)
    have o2 := oRow_le (ω := ω) hD (j := J - 1)
    unfold ValidClass at hv
    unfold ordLo ordHi
    split_ifs <;> omega
  · -- stepA
    intro J a h1 h2 hv
    refine ⟨ord_stepA_lo h hD hmix h1 h2 hv, ord_stepA_hi h hD hmix h1 h2 hv⟩
  · intro J hv1 hv2
    exact ⟨ord_stepB_lo h hD hmix hv1 hv2, ord_stepB_hi h hD hmix hv1 hv2⟩
  · -- first
    have := h.lo_zero
    have := hends.1
    unfold ordLo ordHi
    split_ifs <;> omega
  · intro hpos
    have hlast : ω.lo (ω.widthZ - 1 + ω.period) = ω.hi (ω.widthZ - 1 + ω.period) := by
      have e : ω.widthZ - 1 + ω.period = ω.period + ω.widthZ - 1 := by ring
      rw [e]; exact h.lo_last
    have := hends.2
    unfold ordLo ordHi
    simp only [add_sub_cancel_right]
    split_ifs <;> omega
  · intro h0
    omega


/-- **`lem:gluing-local` (3), connectedness, ordinary marks.**  For a legal ordinary mark with a
nonempty copy and a connected outer, `D ∘_ω E` is a connected skew diagram. -/
theorem IsLegalNonempty.isConnectedSkew_compose_ord (h : ω.IsLegalNonempty)
    (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed) : IsConnectedSkew (ω.compose D) :=
  (ord_classRows h hD hmix).isConnectedSkew

end MarkedInner

end GluingCore
