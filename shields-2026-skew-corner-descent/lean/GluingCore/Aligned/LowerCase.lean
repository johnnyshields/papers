/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/LowerCase.lean`. -/
import GluingCore.Aligned.LowerAttach

/-!
# The case of the lower mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, ordinary case, `b > 0`: "the attachment case is fixed by which of the
joining constructions is skew").

The case `lowerCase ω η` of the lower mark is (a) when `η` and `ω` have the same ordinary case and
(b) otherwise.  This file proves the lower attachment of `muOf V (zOf ω η a) (lowerCase ω η)`:
horizontal in the first case, vertical in the second.  With a tail, the side of the first lower
tail of `V` against `V - z` is read from the case of `η` at the sampled marked diagonal; without a
tail, the junction bit is read from the lower end caps of `η`.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram} {a : ℤ}

/-- The case of the lower mark: (a) when `η` and `ω` have the same case, (b) otherwise. -/
def lowerCase (ω η : MarkedInner) : AttachCase :=
  if η.ordSign = ω.ordSign then .a else .b

theorem ite_cases_eq {p q : ℤ} (h : p = q) : (if p = q then AttachCase.a else AttachCase.b) =
    AttachCase.a := by simp [h]

theorem ite_cases_ne {p q : ℤ} (h : p ≠ q) : (if p = q then AttachCase.a else AttachCase.b) =
    AttachCase.b := by simp [h]

theorem lowerCase_not_mixed (ω η : MarkedInner) : ¬ (lowerCase ω η).IsMixed := by
  unfold lowerCase AttachCase.IsMixed
  split_ifs <;> simp

/-- The diagonals of a mark `η` on `V ∘_ω E` on a valid class. -/
theorem eta_class (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed) (hV : IsConnectedSkew V)
    (hU : η.E = ω.compose V) {J a : ℤ} (ha0 : 0 ≤ a) (ha1 : a < ω.period)
    (hv : ValidClass (minContent V) (maxContent V) ω.widthZ J a) :
    η.lo ((J - minContent V) * ω.period + a) = ω.ordLo V J a ∧
      η.hi ((J - minContent V) * ω.period + a) = ω.ordHi V J a := by
  have hmin : minContent η.E = minContent ω.E + minContent V * ω.period := by
    rw [hU]; exact hω.minContent_compose hV
  have e : minContent η.E + ((J - minContent V) * ω.period + a) =
      minContent ω.E + (J * ω.period + a) := by
    rw [hmin]; ring
  have hw0 := widthZ_nonneg ω
  by_cases hW : ω.W = ∅
  · have hE : ω.IsLegalEmpty := ⟨hω, hW⟩
    have hc := hE.classRows hV
    have h1 := hc.diagLo_eq ha0 ha1 hv
    have h2 := hc.diagHi_eq ha0 ha1 hv
    have hwz := hE.width_zero
    have hJ : minContent V ≤ J ∧ J ≤ maxContent V := by
      unfold ValidClass at hv; omega
    unfold MarkedInner.lo MarkedInner.hi
    rw [e, hU, h1, h2]
    unfold ordLo ordHi
    have hn : ¬ (a < ω.widthZ ∧ minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V) := by omega
    simp only [hJ, and_self, ite_true, hn, ite_false]
  · have hn : ω.IsLegalNonempty := ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    have hc := ord_classRows hn hV hord
    have h1 := hc.diagLo_eq ha0 ha1 hv
    have h2 := hc.diagHi_eq ha0 ha1 hv
    unfold MarkedInner.lo MarkedInner.hi
    rw [e, hU]
    exact ⟨h1, h2⟩

theorem ordSign_eq_of_case_a {ρ : MarkedInner} (h : ρ.case = .a) : ρ.ordSign = 1 := by
  simp [ordSign, h]

theorem ordSign_eq_of_case_b {ρ : MarkedInner} (h : ρ.case = .b) : ρ.ordSign = -1 := by
  simp [ordSign, h]

theorem case_ab_of_not_mixed {ρ : MarkedInner} (h : ¬ ρ.case.IsMixed) :
    ρ.case = .a ∨ ρ.case = .b := by
  unfold AttachCase.IsMixed at h
  cases hh : ρ.case <;> simp_all

theorem ordLo_both {D : Diagram} {J a : ℤ} (hm : minContent D ≤ J - 1) (hM : J ≤ maxContent D)
    (ha : a < ω.widthZ) :
    ω.ordLo D J a = min (ω.oRowLo D J + ω.lo a) (ω.oRowLo D (J - 1) + ω.lo (a + ω.period)) := by
  unfold ordLo
  have h1 : minContent D ≤ J ∧ J ≤ maxContent D := ⟨by omega, hM⟩
  have h2 : a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D :=
    ⟨ha, hm, by omega⟩
  simp only [h1, h2, and_self, ite_true]

theorem ordHi_both {D : Diagram} {J a : ℤ} (hm : minContent D ≤ J - 1) (hM : J ≤ maxContent D)
    (ha : a < ω.widthZ) :
    ω.ordHi D J a = max (ω.oRowHi D J + ω.hi a) (ω.oRowHi D (J - 1) + ω.hi (a + ω.period)) := by
  unfold ordHi
  have h1 : minContent D ≤ J ∧ J ≤ maxContent D := ⟨by omega, hM⟩
  have h2 : a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D :=
    ⟨ha, hm, by omega⟩
  simp only [h1, h2, and_self, ite_true]

theorem ordLo_top {D : Diagram} {J a : ℤ} (hM : maxContent D < J) :
    ω.ordLo D J a = ω.oRowLo D (J - 1) + ω.lo (a + ω.period) := by
  unfold ordLo
  have h1 : ¬ (minContent D ≤ J ∧ J ≤ maxContent D) := by omega
  simp only [h1, ite_false]

theorem ordHi_top {D : Diagram} {J a : ℤ} (hM : maxContent D < J) :
    ω.ordHi D J a = ω.oRowHi D (J - 1) + ω.hi (a + ω.period) := by
  unfold ordHi
  have h1 : ¬ (minContent D ≤ J ∧ J ≤ maxContent D) := by omega
  simp only [h1, ite_false]

theorem ordLo_one {D : Diagram} {J a : ℤ} (hm : minContent D ≤ J) (hM : J ≤ maxContent D)
    (ha : ω.widthZ ≤ a) : ω.ordLo D J a = ω.oRowLo D J + ω.lo a := by
  unfold ordLo
  have h1 : minContent D ≤ J ∧ J ≤ maxContent D := ⟨hm, hM⟩
  have h2 : ¬ (a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D) := by omega
  simp only [h1, h2, and_self, ite_true, ite_false]

theorem ordHi_one {D : Diagram} {J a : ℤ} (hm : minContent D ≤ J) (hM : J ≤ maxContent D)
    (ha : ω.widthZ ≤ a) : ω.ordHi D J a = ω.oRowHi D J + ω.hi a := by
  unfold ordHi
  have h1 : minContent D ≤ J ∧ J ≤ maxContent D := ⟨hm, hM⟩
  have h2 : ¬ (a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D) := by omega
  simp only [h1, h2, and_self, ite_true, ite_false]

theorem caps_a {ρ : MarkedInner} (hρ : ρ.IsLegalNonempty) (hc : ρ.case = .a) :
    ρ.dLo (ρ.widthZ - 1) = 0 ∧ ρ.lo (ρ.widthZ - 1) = ρ.lo ρ.widthZ ∧
      ρ.dHi (ρ.widthZ - 1) + (ρ.hi (ρ.widthZ - 1) - ρ.hi ρ.widthZ) = 0 := by
  have hmix : ¬ ρ.case.IsMixed := by simp [AttachCase.IsMixed, hc]
  have hT : ρ.ordT = 0 := by simp [ordT, hc]
  exact ((ord_E_facts hρ hmix).2.1 hT).1

theorem caps_b {ρ : MarkedInner} (hρ : ρ.IsLegalNonempty) (hc : ρ.case = .b) :
    ρ.dHi (ρ.widthZ - 1) = 0 ∧ ρ.hi (ρ.widthZ - 1) - ρ.hi ρ.widthZ = 1 ∧
      ρ.dLo (ρ.widthZ - 1) + (ρ.lo (ρ.widthZ - 1) - ρ.lo ρ.widthZ) = 1 := by
  have hmix : ¬ ρ.case.IsMixed := by simp [AttachCase.IsMixed, hc]
  have hT : ρ.ordT = 1 := by simp [ordT, hc]
  exact ((ord_E_facts hρ hmix).2.2 hT).1

namespace LowerChart

variable (C : LowerChart ω η V a)
include C

/-- The side of a lower tail of `V` against `V - z` determines whether `η` and `ω` have the same
case: a southeast tail when they do, a northwest tail when they do not. -/
theorem tail_sign {J : ℤ} (hJ1 : minContent V ≤ J) (hJ2 : J ≤ maxContent V - a) :
    (gapHi V (zOf ω η a) J < 0 → η.ordSign = ω.ordSign) ∧
      (0 < gapLo V (zOf ω η a) J → η.ordSign ≠ ω.ordSign) := by
  have hηn := C.eta_nonempty
  have hr := C.sample_range hJ1 hJ2
  have hq := C.period_pos
  have h0 : 0 ≤ (J - minContent V) * ω.period + ω.widthZ := hr.1
  have h1 : (J - minContent V) * ω.period + ω.widthZ ≤ η.widthZ - 1 := by omega
  obtain ⟨d1, d2⟩ := C.dsample hJ1 hJ2
  have hcc := case_ab_of_not_mixed C.hord
  have hcc' := case_ab_of_not_mixed C.hηord
  rcases hcc with hc | hc <;> rcases hcc' with hc' | hc'
  · have s := hηn.sides_a hc' h0 h1
    obtain ⟨e1, e2⟩ := d1 hc
    rw [e1, e2] at s
    rw [ordSign_eq_of_case_a hc, ordSign_eq_of_case_a hc']
    exact ⟨fun _ => rfl, fun h => by omega⟩
  · have s := hηn.sides_b hc' h0 h1
    obtain ⟨e1, e2⟩ := d1 hc
    rw [e1, e2] at s
    rw [ordSign_eq_of_case_a hc, ordSign_eq_of_case_b hc']
    exact ⟨fun h => by omega, fun _ => by omega⟩
  · have s := hηn.sides_a hc' h0 h1
    obtain ⟨e1, e2⟩ := d2 hc
    rw [e1, e2] at s
    rw [ordSign_eq_of_case_b hc, ordSign_eq_of_case_a hc']
    exact ⟨fun h => by omega, fun _ => by omega⟩
  · have s := hηn.sides_b hc' h0 h1
    obtain ⟨e1, e2⟩ := d2 hc
    rw [e1, e2] at s
    rw [ordSign_eq_of_case_b hc, ordSign_eq_of_case_b hc']
    exact ⟨fun _ => rfl, fun h => by omega⟩

/-- The junction bit without a lower tail, for a nonempty `ω`: read from the lower end caps of
`η` at its last marked diagonal. -/
theorem junction_nonempty (hωn : ω.IsLegalNonempty)
    (hnt : ∀ J, minContent V ≤ J → J ≤ maxContent V - a →
      ¬ (0 < gapLo V (zOf ω η a) J ∨ gapHi V (zOf ω η a) J < 0)) :
    (η.ordSign = ω.ordSign → diagLo V (maxContent V - a) = diagLo V (maxContent V - a + 1)) ∧
      (η.ordSign ≠ ω.ordSign →
        diagLo V (maxContent V - a) = diagLo V (maxContent V - a + 1) + 1) := by
  have hηn := C.eta_nonempty
  have hq := hωn.width_lt_period
  have hw := hωn.width_pos
  have hα := C.alpha_pos
  have hpos := C.hpos
  have hV := C.hV
  have G := C.glueData
  have hsp := span_eq_of_isConnectedSkew hV
  have hle := G.le_max
  have hcz := content_zOf ω η a
  have hperη : η.period = a * ω.period := C.ha
  have hwη : η.widthZ = (maxContent V - a + 1 - minContent V) * ω.period + ω.widthZ := by
    rw [C.widthZ_eta, hsp]; ring
  have hK : η.widthZ - 1 = (maxContent V - a + 1 - minContent V) * ω.period + (ω.widthZ - 1) := by
    omega
  have hKp : η.widthZ - 1 + η.period =
      (maxContent V + 1 - minContent V) * ω.period + (ω.widthZ - 1) := by
    rw [hK, hperη]; ring
  have hM : minContent V ≤ maxContent V := by omega
  -- the three diagonals of `η`
  have l1 := eta_class C.hω C.hord hV C.hU (J := maxContent V - a + 1) (a := ω.widthZ - 1)
    (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)
  have l2 := eta_class C.hω C.hord hV C.hU (J := maxContent V - a + 1) (a := ω.widthZ)
    (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)
  have l3 := eta_class C.hω C.hord hV C.hU (J := maxContent V + 1) (a := ω.widthZ - 1)
    (by omega) (by omega) (Or.inr ⟨rfl, by omega⟩)
  rw [ordLo_both (by omega) (by omega) (by omega), ordHi_both (by omega) (by omega) (by omega)]
    at l1
  rw [ordLo_one (by omega) (by omega) le_rfl, ordHi_one (by omega) (by omega) le_rfl] at l2
  rw [ordLo_top (by omega), ordHi_top (by omega)] at l3
  have e1 : maxContent V - a + 1 - 1 = maxContent V - a := by ring
  have e2 : maxContent V + 1 - 1 = maxContent V := by ring
  rw [e1] at l1
  rw [e2] at l3
  have hsing := hωn.lo_w_eq_hi_w
  -- facts on `V`
  have hends := D_ends hV
  have sb := G.sing_b
  rw [hcz] at sb
  have hle' : minContent V ≤ maxContent V - a := by omega
  have hb1 := hnt (maxContent V - a) hle' (by omega)
  have hne := G.nonempty (maxContent V - a) hle' (by omega)
  simp only [gapLo, gapHi, hcz, sub_add_cancel] at hb1 hne
  have bJ := D_bits hV (J := maxContent V - a + 1) (by omega) (by omega)
  rw [e1] at bJ
  have hz1 : (zOf ω η a).1 = ω.ordSign * (η.rowShift - a * ω.rowShift) := rfl
  rw [hz1] at hb1 hne
  have p1 : (maxContent V - a + 1) * ω.rowShift =
      maxContent V * ω.rowShift - a * ω.rowShift + ω.rowShift := by ring
  have p2 : (maxContent V - a) * ω.rowShift = maxContent V * ω.rowShift - a * ω.rowShift := by
    ring
  have hcc := case_ab_of_not_mixed C.hord
  have hcc' := case_ab_of_not_mixed C.hηord
  have hdL : ∀ ρ : MarkedInner, ρ.IsLegalNonempty → ∀ k, ρ.dLo k =
      ρ.lo (k + ρ.period) - ρ.rowShift - ρ.lo k := fun _ _ _ => rfl
  have hdH : ∀ ρ : MarkedInner, ρ.IsLegalNonempty → ∀ k, ρ.dHi k =
      ρ.hi (k + ρ.period) - ρ.rowShift - ρ.hi k := fun _ _ _ => rfl
  have hqr : ω.widthZ - 1 + ω.period = ω.widthZ - 1 + ω.period := rfl
  rcases hcc with hc | hc <;> rcases hcc' with hc' | hc'
  · -- (a, a)
    have cω := caps_a hωn hc
    have cη := caps_a hηn hc'
    have e := ordSign_eq_of_case_a hc
    have e' := ordSign_eq_of_case_a hc'
    rw [hdL _ hωn, hdH _ hωn] at cω
    rw [hdL _ hηn, hdH _ hηn, hKp, hK, hwη] at cη
    simp only [oRowLo, oRowHi, hc, e] at l1 l2 l3 hb1 hne
    rw [l1.1, l1.2, l2.1, l2.2, l3.1, l3.2] at cη
    constructor
    · intro _
      omega
    · intro h
      omega
  · -- (a, b)
    have cω := caps_a hωn hc
    have cη := caps_b hηn hc'
    have e := ordSign_eq_of_case_a hc
    have e' := ordSign_eq_of_case_b hc'
    rw [hdL _ hωn, hdH _ hωn] at cω
    rw [hdL _ hηn, hdH _ hηn, hKp, hK, hwη] at cη
    simp only [oRowLo, oRowHi, hc, e] at l1 l2 l3 hb1 hne
    rw [l1.1, l1.2, l2.1, l2.2, l3.1, l3.2] at cη
    constructor
    · intro h
      omega
    · intro h
      omega
  · -- (b, a)
    have cω := caps_b hωn hc
    have cη := caps_a hηn hc'
    have e := ordSign_eq_of_case_b hc
    have e' := ordSign_eq_of_case_a hc'
    rw [hdL _ hωn, hdH _ hωn] at cω
    rw [hdL _ hηn, hdH _ hηn, hKp, hK, hwη] at cη
    simp only [oRowLo, oRowHi, hc, e] at l1 l2 l3 hb1 hne
    rw [l1.1, l1.2, l2.1, l2.2, l3.1, l3.2] at cη
    constructor
    · intro h
      omega
    · intro h
      omega
  · -- (b, b)
    have cω := caps_b hωn hc
    have cη := caps_b hηn hc'
    have e := ordSign_eq_of_case_b hc
    have e' := ordSign_eq_of_case_b hc'
    rw [hdL _ hωn, hdH _ hωn] at cω
    rw [hdL _ hηn, hdH _ hηn, hKp, hK, hwη] at cη
    simp only [oRowLo, oRowHi, hc, e] at l1 l2 l3 hb1 hne
    rw [l1.1, l1.2, l2.1, l2.2, l3.1, l3.2] at cη
    constructor
    · intro h
      omega
    · intro h
      omega

/-- The junction bit without a lower tail, for the empty `ω`. -/
theorem junction_empty (hωe : ω.IsLegalEmpty)
    (hnt : ∀ J, minContent V ≤ J → J ≤ maxContent V - a →
      ¬ (0 < gapLo V (zOf ω η a) J ∨ gapHi V (zOf ω η a) J < 0)) :
    (η.ordSign = ω.ordSign → diagLo V (maxContent V - a) = diagLo V (maxContent V - a + 1)) ∧
      (η.ordSign ≠ ω.ordSign →
        diagLo V (maxContent V - a) = diagLo V (maxContent V - a + 1) + 1) := by
  have hηn := C.eta_nonempty
  have hq := hωe.period_pos
  have hw0 := hωe.width_zero
  have hα := C.alpha_pos
  have hpos := C.hpos
  have hV := C.hV
  have G := C.glueData
  have hsp := span_eq_of_isConnectedSkew hV
  have hle := G.le_max
  have hcz := content_zOf ω η a
  have hperη : η.period = a * ω.period := C.ha
  have hwη : η.widthZ = (maxContent V - a + 1 - minContent V) * ω.period := by
    rw [C.widthZ_eta, hsp, hw0]; ring
  have hK : η.widthZ - 1 =
      (maxContent V - a - minContent V) * ω.period + (ω.period - 1) := by
    rw [hwη]; ring
  have hKp : η.widthZ - 1 + η.period =
      (maxContent V - minContent V) * ω.period + (ω.period - 1) := by
    rw [hK, hperη]; ring
  have hM : minContent V ≤ maxContent V := by omega
  have hle' : minContent V ≤ maxContent V - a := by omega
  have hcase : ω.case = .a := hωe.case_a
  -- the three diagonals of `η`
  have l1 := eta_class C.hω C.hord hV C.hU (J := maxContent V - a) (a := ω.period - 1)
    (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)
  have l2 := eta_class C.hω C.hord hV C.hU (J := maxContent V - a + 1) (a := 0)
    (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)
  have l3 := eta_class C.hω C.hord hV C.hU (J := maxContent V) (a := ω.period - 1)
    (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)
  rw [ordLo_one (by omega) (by omega) (by omega), ordHi_one (by omega) (by omega) (by omega)]
    at l1 l3
  rw [ordLo_one (by omega) (by omega) (by omega), ordHi_one (by omega) (by omega) (by omega)]
    at l2
  rw [add_zero] at l2
  have hends := D_ends hV
  have sb := G.sing_b
  rw [hcz] at sb
  have hb1 := hnt (maxContent V - a) hle' (by omega)
  have hne := G.nonempty (maxContent V - a) hle' (by omega)
  simp only [gapLo, gapHi, hcz, sub_add_cancel] at hb1 hne
  have bJ := D_bits hV (J := maxContent V - a + 1) (by omega) (by omega)
  have e1 : maxContent V - a + 1 - 1 = maxContent V - a := by ring
  rw [e1] at bJ
  have hz1 : (zOf ω η a).1 = ω.ordSign * (η.rowShift - a * ω.rowShift) := rfl
  rw [hz1] at hb1 hne
  have p1 : (maxContent V - a + 1) * ω.rowShift =
      maxContent V * ω.rowShift - a * ω.rowShift + ω.rowShift := by ring
  have p2 : (maxContent V - a) * ω.rowShift = maxContent V * ω.rowShift - a * ω.rowShift := by
    ring
  have hends' := hωe.ends
  have hp := hωe.rowShift_eq
  have hcc' := case_ab_of_not_mixed C.hηord
  have hdL : ∀ ρ : MarkedInner, ρ.IsLegalNonempty → ∀ k, ρ.dLo k =
      ρ.lo (k + ρ.period) - ρ.rowShift - ρ.lo k := fun _ _ _ => rfl
  have hdH : ∀ ρ : MarkedInner, ρ.IsLegalNonempty → ∀ k, ρ.dHi k =
      ρ.hi (k + ρ.period) - ρ.rowShift - ρ.hi k := fun _ _ _ => rfl
  have e := ordSign_eq_of_case_a hcase
  rcases hcc' with hc' | hc'
  · have e' := ordSign_eq_of_case_a hc'
    have cη := caps_a hηn hc'
    rw [hdL _ hηn, hdH _ hηn, hKp, hK, hwη] at cη
    simp only [oRowLo, oRowHi, hcase, e] at l1 l2 l3 hb1 hne
    rw [l1.1, l1.2, l2.1, l2.2, l3.1, l3.2] at cη
    constructor
    · intro h
      omega
    · intro h
      omega
  · have e' := ordSign_eq_of_case_b hc'
    have cη := caps_b hηn hc'
    rw [hdL _ hηn, hdH _ hηn, hKp, hK, hwη] at cη
    simp only [oRowLo, oRowHi, hcase, e] at l1 l2 l3 hb1 hne
    rw [l1.1, l1.2, l2.1, l2.2, l3.1, l3.2] at cη
    constructor
    · intro h
      omega
    · intro h
      omega

/-- **The lower attachment of the lower mark.**  The mark `μ = (V, V ∩ (V - z), z)` with case
`lowerCase ω η` has a horizontal lower attachment when `η` and `ω` have the same case, and a
vertical one otherwise. -/
theorem lowerAttach :
    (η.ordSign = ω.ordSign → (muOf V (zOf ω η a) (lowerCase ω η)).LowerH) ∧
      (η.ordSign ≠ ω.ordSign → (muOf V (zOf ω η a) (lowerCase ω η)).LowerV) := by
  have G := C.glueData
  have hcz := content_zOf ω η a
  have hle := G.le_max
  obtain ⟨J0, hJ0a, hJ0b, hno, hyes⟩ := G.exists_first_tail
  by_cases hc : J0 ≤ maxContent V - content (zOf ω η a)
  · have htl := hyes J0 le_rfl hc
    have t1 := G.thin_lo J0 hJ0a hc
    have ts := C.tail_sign hJ0a (by omega)
    rcases htl with h | h
    · have hne := ts.2 h
      refine ⟨fun h' => absurd h' hne, fun _ => ?_⟩
      unfold lowerCase
      rw [ite_cases_ne hne]
      exact G.lowerV_of_nw _ hno hJ0a hc h
    · have heq := ts.1 h
      refine ⟨fun _ => ?_, fun h' => absurd heq h'⟩
      unfold lowerCase
      rw [ite_cases_eq heq]
      exact G.lowerH_of_se _ hno hJ0a hc h
  · have hnt : ∀ J, minContent V ≤ J → J ≤ maxContent V - a →
        ¬ (0 < gapLo V (zOf ω η a) J ∨ gapHi V (zOf ω η a) J < 0) := fun J h1 h2 =>
      hno J h1 (by omega)
    have hnt' : ∀ J, minContent V ≤ J → J ≤ maxContent V - content (zOf ω η a) →
        ¬ (0 < gapLo V (zOf ω η a) J ∨ gapHi V (zOf ω η a) J < 0) := fun J h1 h2 =>
      hnt J h1 (by omega)
    have hj : (η.ordSign = ω.ordSign →
          diagLo V (maxContent V - a) = diagLo V (maxContent V - a + 1)) ∧
        (η.ordSign ≠ ω.ordSign →
          diagLo V (maxContent V - a) = diagLo V (maxContent V - a + 1) + 1) := by
      by_cases hW : ω.W = ∅
      · exact C.junction_empty ⟨C.hω, hW⟩ hnt
      · exact C.junction_nonempty ⟨C.hω, Finset.nonempty_iff_ne_empty.mpr hW⟩ hnt
    have e1 : maxContent V - content (zOf ω η a) = maxContent V - a := by omega
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · unfold lowerCase
      have := hj.1 h'
      rw [← e1] at this
      exact G.lowerH_of_junction _ hnt' this
    · unfold lowerCase
      have := hj.2 h'
      rw [← e1] at this
      exact G.lowerV_of_junction _ hnt' this

end LowerChart

end MarkedInner

end GluingCore
