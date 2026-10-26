/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/OrdinaryEdge.lean`. -/
import GluingCore.Aligned.Statement
import GluingCore.Aligned.Lattice
import Mathlib.Tactic.LinearCombination

/-!
# Ordinary charts: the extreme cells of a composite and the edge displacement

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, the case `b = 0` for ordinary marks).

The diagonals of an ordinary composite `V ∘_ω E` on its first and last windows
(`lo_hi_first`, `lo_hi_last`), the extreme cells of a composite (`sw_compose`, `ne_compose`), and
`ordinary_edge_displacement_proof`: the displacement of an ordinary mark `η` on `V ∘_ω E` whose
content is `N_V q` is `L_ω(v_H(V))` or `L_ω(v_H(V)) - ε e` (`ε = ±1` the sign of `ω`), with the
case of `η` that of `ω` or the opposite one.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

/-- The southwest cell of an ordinary composite is the southwest cell of the first copy. -/
theorem sw_compose (hω : ω.IsLegal) (hV : IsConnectedSkew V) :
    sw (ω.compose V) = sw ω.E + ω.origin V (sw V) := by
  have hVne := hV.2.1
  have hEne : ω.E.Nonempty := hω.1.1.2.1
  have hU := hω.isConnectedSkew_compose hV
  have hmem : sw ω.E + ω.origin V (sw V) ∈ ω.compose V := by
    rw [mem_compose hVne]
    left
    exact ⟨sw V, sw_mem hVne, mem_translate.mpr (by simpa using sw_mem hEne)⟩
  symm
  apply eq_sw_of_content hU hmem
  rw [hω.minContent_compose hV, content_add, content_origin, content_sw hVne, content_sw hEne]

/-- The northeast cell of a composite is the northeast cell of the last copy. -/
theorem ne_compose (hω : ω.IsLegal) (hV : IsConnectedSkew V) :
    ne (ω.compose V) = ne ω.E + ω.origin V (ne V) := by
  have hVne := hV.2.1
  have hEne : ω.E.Nonempty := hω.1.1.2.1
  have hU := hω.isConnectedSkew_compose hV
  have hmem : ne ω.E + ω.origin V (ne V) ∈ ω.compose V := by
    rw [mem_compose hVne]
    left
    exact ⟨ne V, ne_mem hVne, mem_translate.mpr (by simpa using ne_mem hEne)⟩
  symm
  apply eq_ne_of_content hU hmem
  rw [hω.maxContent_compose hV, content_add, content_origin, content_ne hVne, content_ne hEne]
  have := hω.1.span_eq
  have hsp := span_eq_of_isConnectedSkew hω.1.1
  omega

/-- The first rows of the diagonals of an ordinary composite, on the first window. -/
theorem lo_hi_first (h : ω.IsLegalNonempty) (hV : IsConnectedSkew V)
    (hord : ¬ ω.case.IsMixed) (hU : η.E = ω.compose V) {a : ℤ} (h0 : 0 ≤ a) (h1 : a < ω.period) :
    η.lo a = ω.oRowLo V (minContent V) + ω.lo a ∧
      η.hi a = ω.oRowHi V (minContent V) + ω.hi a := by
  have hc := ord_classRows h hV hord
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  have hmin : minContent η.E = minContent ω.E + minContent V * ω.period := by
    rw [hU]; exact h.1.minContent_compose hV
  have e : minContent η.E + a = minContent ω.E + (minContent V * ω.period + a) := by omega
  have hv : ValidClass (minContent V) (maxContent V) ω.widthZ (minContent V) a :=
    Or.inl ⟨le_refl _, hmM⟩
  have hl := hc.diagLo_eq h0 h1 hv
  have hh := hc.diagHi_eq h0 h1 hv
  unfold ordLo at hl
  unfold ordHi at hh
  unfold MarkedInner.lo MarkedInner.hi
  rw [e, hU]
  have hn : ¬ (minContent V ≤ minContent V - 1) := by omega
  simp only [hn, and_false, ite_false, le_refl, hmM, and_self, ite_true, false_and] at hl hh
  exact ⟨hl, hh⟩

/-- The first rows of the diagonals of an ordinary composite just past its last full block:
the diagonal of relative content `N q + a`, `a < w`, comes from the last copy alone. -/
theorem lo_hi_last (h : ω.IsLegalNonempty) (hV : IsConnectedSkew V)
    (hord : ¬ ω.case.IsMixed) (hU : η.E = ω.compose V) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a < ω.widthZ) :
    η.lo (a + (span V : ℤ) * ω.period) = ω.oRowLo V (maxContent V) + ω.lo (a + ω.period) ∧
      η.hi (a + (span V : ℤ) * ω.period) =
        ω.oRowHi V (maxContent V) + ω.hi (a + ω.period) := by
  have hc := ord_classRows h hV hord
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  have hmin : minContent η.E = minContent ω.E + minContent V * ω.period := by
    rw [hU]; exact h.1.minContent_compose hV
  have hsp := span_eq_of_isConnectedSkew hV
  have e : minContent η.E + (a + (span V : ℤ) * ω.period) =
      minContent ω.E + ((maxContent V + 1) * ω.period + a) := by
    rw [hmin, hsp]; ring
  have hv : ValidClass (minContent V) (maxContent V) ω.widthZ (maxContent V + 1) a :=
    Or.inr ⟨rfl, h1⟩
  have hl := hc.diagLo_eq h0 (by omega) hv
  have hh := hc.diagHi_eq h0 (by omega) hv
  unfold ordLo at hl
  unfold ordHi at hh
  unfold MarkedInner.lo MarkedInner.hi
  rw [e, hU]
  have hn : ¬ (minContent V ≤ maxContent V + 1 ∧ maxContent V + 1 ≤ maxContent V) := by omega
  simp only [hn, ite_false, add_sub_cancel_right] at hl hh
  exact ⟨hl, hh⟩

theorem lat_eq (ω : MarkedInner) (t : ℤ × ℤ) :
    ω.lat t = (content t * ω.v.1 + ω.ordSign * t.1, content t * ω.v.2 + ω.ordSign * t.1) := by
  unfold lat
  ext <;> simp [content, eCell]

theorem content_vH {V : Diagram} (hV : IsConnectedSkew V) : content (vH V) = (span V : ℤ) := by
  have hVne := hV.2.1
  have := span_eq_of_isConnectedSkew hV
  unfold vH
  rw [content_add, content_sub, content_ne hVne, content_sw hVne]
  simp [content]
  omega

theorem vH_fst (V : Diagram) : (vH V).1 = (ne V).1 - (sw V).1 := by
  simp [vH]

/-- `L_ω(v_H(V))` is the displacement from the origin of the first copy to that of the last copy
plus `v`. -/
theorem lat_vH (hord : ¬ ω.case.IsMixed) :
    ω.lat (vH V) = ω.origin V (ne V) - ω.origin V (sw V) + ω.v := by
  have hv : vH V = (ne V - sw V) + (0, 1) := rfl
  have h01 : ω.lat (0, 1) = ω.v := by
    rw [lat_eq]; ext <;> simp [content]
  have h3 : ω.lat (ne V - sw V) = ω.lat (ne V) - ω.lat (sw V) := by
    have := lat_add ω (ne V - sw V) (sw V)
    rw [sub_add_cancel] at this
    rw [this]; abel
  rw [hv, lat_add, h3, h01, origin_eq_lat hord V, origin_eq_lat hord V]

/-- The arithmetic of the edge displacement for nonempty marks: the first coordinate of the
displacement of `η` is that of `L_ω(v_H(V))`, or differs from it by `∓ 1` with the opposite
case. -/
theorem edge_nonempty (hω : ω.IsLegalNonempty) (hord : ¬ ω.case.IsMixed) (hV : IsConnectedSkew V)
    (hη : η.IsLegalNonempty) (hηord : ¬ η.case.IsMixed) (hU : η.E = ω.compose V)
    (ha : content η.v = (span V : ℤ) * ω.period) :
    (η.rowShift = (span V : ℤ) * ω.rowShift + ω.ordSign * ((ne V).1 - (sw V).1) ∧
        η.ordSign = ω.ordSign) ∨
      (η.rowShift = (span V : ℤ) * ω.rowShift + ω.ordSign * ((ne V).1 - (sw V).1) -
          ω.ordSign ∧ η.ordSign = -ω.ordSign) := by
  have hq := hω.width_lt_period
  have hw := hω.width_pos
  have hVne := hV.2.1
  have hsp := span_eq_of_isConnectedSkew hV
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hVne)
  have hper : η.period = (span V : ℤ) * ω.period := ha
  have hwid : η.widthZ = ω.widthZ := by
    have h1 := hη.span_eq
    have h2 := span_compose hV hω.1
    rw [hU] at h1
    unfold widthZ at *
    omega
  have hNp : (span V : ℤ) * ω.rowShift =
      maxContent V * ω.rowShift - minContent V * ω.rowShift + ω.rowShift := by
    rw [hsp]; ring
  have hends := D_ends hV
  have hswne : (sw V).1 = diagLo V (minContent V) := rfl
  have hnene : (ne V).1 = diagLo V (maxContent V) := rfl
  -- arrays
  obtain ⟨f0l, f0h⟩ := lo_hi_first hω hV hord hU (a := 0) le_rfl (by omega)
  obtain ⟨fw1l, fw1h⟩ := lo_hi_first hω hV hord hU (a := ω.widthZ - 1) (by omega) (by omega)
  obtain ⟨fwl, fwh⟩ := lo_hi_first hω hV hord hU (a := ω.widthZ) (by omega) (by omega)
  obtain ⟨l0l, l0h⟩ := lo_hi_last hω hV hord hU (a := 0) le_rfl (by omega)
  obtain ⟨lw1l, lw1h⟩ := lo_hi_last hω hV hord hU (a := ω.widthZ - 1) (by omega) (by omega)
  have hcapsω := ord_E_facts hω hord
  have hcapsη := ord_E_facts hη hηord
  have hz0 := hω.dLo_zero_le
  have hz0η := hη.dLo_zero_le
  have hsing := hω.lo_zero
  have hsingη := hη.lo_zero
  have hthin := hω.1.upper_start_thin hω.2
  have hcc : ω.case = .a ∨ ω.case = .b := by
    unfold AttachCase.IsMixed at hord
    cases hh : ω.case <;> simp_all
  have hηcc : η.case = .a ∨ η.case = .b := by
    unfold AttachCase.IsMixed at hηord
    cases hh : η.case <;> simp_all
  have hd0l : η.dLo 0 = (ω.oRowLo V (maxContent V) + ω.lo (0 + ω.period)) - η.rowShift -
      (ω.oRowLo V (minContent V) + ω.lo 0) := by
    unfold dLo; rw [hper, l0l, f0l]
  have hd0h : η.dHi 0 = (ω.oRowHi V (maxContent V) + ω.hi (0 + ω.period)) - η.rowShift -
      (ω.oRowHi V (minContent V) + ω.hi 0) := by
    unfold dHi; rw [hper, l0h, f0h]
  have hdwl : η.dLo (ω.widthZ - 1) = (ω.oRowLo V (maxContent V) + ω.lo (ω.widthZ - 1 + ω.period))
      - η.rowShift - (ω.oRowLo V (minContent V) + ω.lo (ω.widthZ - 1)) := by
    unfold dLo; rw [hper, lw1l, fw1l]
  have hdwh : η.dHi (ω.widthZ - 1) = (ω.oRowHi V (maxContent V) + ω.hi (ω.widthZ - 1 + ω.period))
      - η.rowShift - (ω.oRowHi V (minContent V) + ω.hi (ω.widthZ - 1)) := by
    unfold dHi; rw [hper, lw1h, fw1h]
  have e1 : η.lo (ω.widthZ - 1) = ω.oRowLo V (minContent V) + ω.lo (ω.widthZ - 1) := fw1l
  have e2 : η.lo ω.widthZ = ω.oRowLo V (minContent V) + ω.lo ω.widthZ := fwl
  have e3 : η.hi (ω.widthZ - 1) = ω.oRowHi V (minContent V) + ω.hi (ω.widthZ - 1) := fw1h
  have e4 : η.hi ω.widthZ = ω.oRowHi V (minContent V) + ω.hi ω.widthZ := fwh
  have hup : ω.hi (ω.period) ≤ ω.lo ω.period + 1 := hthin
  have hendsl := hends.1
  have hendsh := hends.2
  have hendsl := hends.1
  have hendsh := hends.2
  have hLoa : ω.case = .a → ∀ j, ω.oRowLo V j = j * ω.rowShift + diagLo V j := by
    intro hc j; simp [oRowLo, hc]
  have hHia : ω.case = .a → ∀ j, ω.oRowHi V j = j * ω.rowShift + diagHi V j := by
    intro hc j; simp [oRowHi, hc]
  have hLob : ω.case = .b → ∀ j, ω.oRowLo V j = j * ω.rowShift - diagHi V j := by
    intro hc j; simp [oRowLo, hc]
  have hHib : ω.case = .b → ∀ j, ω.oRowHi V j = j * ω.rowShift - diagLo V j := by
    intro hc j; simp [oRowHi, hc]
  have hcapa : ∀ ρ : MarkedInner, ρ.IsLegalNonempty → ρ.case = .a →
      ρ.dLo (ρ.widthZ - 1) = 0 ∧ ρ.lo (ρ.widthZ - 1) = ρ.lo ρ.widthZ ∧
        ρ.dHi (ρ.widthZ - 1) + (ρ.hi (ρ.widthZ - 1) - ρ.hi ρ.widthZ) = 0 := by
    intro ρ hρ hc
    have hmix : ¬ ρ.case.IsMixed := by simp [AttachCase.IsMixed, hc]
    have hT : ρ.ordT = 0 := by simp [ordT, hc]
    exact ((ord_E_facts hρ hmix).2.1 hT).1
  have hcapb : ∀ ρ : MarkedInner, ρ.IsLegalNonempty → ρ.case = .b →
      ρ.dHi (ρ.widthZ - 1) = 0 ∧ ρ.hi (ρ.widthZ - 1) - ρ.hi ρ.widthZ = 1 ∧
        ρ.dLo (ρ.widthZ - 1) + (ρ.lo (ρ.widthZ - 1) - ρ.lo ρ.widthZ) = 1 := by
    intro ρ hρ hc
    have hmix : ¬ ρ.case.IsMixed := by simp [AttachCase.IsMixed, hc]
    have hT : ρ.ordT = 1 := by simp [ordT, hc]
    exact ((ord_E_facts hρ hmix).2.2 hT).1
  have hdωl : ω.dLo (ω.widthZ - 1) = ω.lo (ω.widthZ - 1 + ω.period) - ω.rowShift -
      ω.lo (ω.widthZ - 1) := rfl
  have hdωh : ω.dHi (ω.widthZ - 1) = ω.hi (ω.widthZ - 1 + ω.period) - ω.rowShift -
      ω.hi (ω.widthZ - 1) := rfl
  rcases hcc with hc | hc <;> rcases hηcc with hc' | hc'
  · -- both case (a)
    have cω := hcapa ω hω hc
    have cη := hcapa η hη hc'
    rw [hwid] at cη
    rw [hdωl, hdωh] at cω
    rw [hLoa hc, hLoa hc] at hdwl
    have hε : ω.ordSign = 1 := by simp [ordSign, hc]
    have hε' : η.ordSign = 1 := by simp [ordSign, hc']
    left
    refine ⟨?_, by omega⟩
    rw [hε]
    omega
  · -- (a), (b)
    have cω := hcapa ω hω hc
    have cη := hcapb η hη hc'
    rw [hwid] at cη
    rw [hdωl, hdωh] at cω
    rw [hHia hc, hHia hc] at hdwh
    have hε : ω.ordSign = 1 := by simp [ordSign, hc]
    have hε' : η.ordSign = -1 := by simp [ordSign, hc']
    right
    refine ⟨?_, by omega⟩
    rw [hε]
    omega
  · -- (b), (a)
    have cω := hcapb ω hω hc
    have cη := hcapa η hη hc'
    rw [hwid] at cη
    rw [hdωl, hdωh] at cω
    rw [hLob hc, hLob hc] at hdwl
    have hε : ω.ordSign = -1 := by simp [ordSign, hc]
    have hε' : η.ordSign = 1 := by simp [ordSign, hc']
    right
    refine ⟨?_, by omega⟩
    rw [hε]
    omega
  · -- both case (b)
    have cω := hcapb ω hω hc
    have cη := hcapb η hη hc'
    rw [hwid] at cη
    rw [hdωl, hdωh] at cω
    rw [hHib hc, hHib hc] at hdwh
    have hε : ω.ordSign = -1 := by simp [ordSign, hc]
    have hε' : η.ordSign = -1 := by simp [ordSign, hc']
    left
    refine ⟨?_, by omega⟩
    rw [hε]
    omega

/-- The width of a legal mark on `η.E = ω.compose V` whose displacement has content
`N_V q` is the width of `ω`. -/
theorem width_eq_of_edge (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hη : η.IsLegal)
    (hU : η.E = ω.compose V) (ha : content η.v = (span V : ℤ) * ω.period) :
    η.width = ω.width := by
  have h1 := hη.1.span_eq
  have h2 := span_compose hV hω
  rw [hU] at h1
  have hper : η.period = (span V : ℤ) * ω.period := ha
  omega

theorem width_eq_zero_iff {ρ : MarkedInner} : ρ.width = 0 ↔ ρ.W = ∅ := by
  unfold width span contents
  rw [Finset.card_eq_zero, Finset.image_eq_empty]

/-- The edge displacement for the empty mark: `η` is the empty mark on `U`, and its
displacement is `L_ω(v_H(V))`. -/
theorem edge_empty (hω : ω.IsLegal) (hωW : ω.W = ∅) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) (ha : content η.v = (span V : ℤ) * ω.period) :
    η.v = ω.lat (vH V) ∧ η.case = .a := by
  have hwη : η.width = 0 := by
    rw [width_eq_of_edge hω hV hη hU ha]; exact width_eq_zero_iff.mpr hωW
  have hηW : η.W = ∅ := width_eq_zero_iff.mp hwη
  have hηe : η.IsEmptyMark := by
    rcases hη.1.2 with h | h
    · exact h
    · exact absurd hηW h.1.ne_empty
  have hωe : ω.IsEmptyMark := by
    rcases hω.1.2 with h | h
    · exact h
    · exact absurd hωW h.1.ne_empty
  have hord : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hωe.2.2]
  refine ⟨?_, hηe.2.2⟩
  have hv1 : η.v = vH (ω.compose V) := by rw [hηe.2.1, hU]
  have hv2 : ω.v = vH ω.E := hωe.2.1
  rw [hv1, lat_vH hord]
  conv_rhs => rw [hv2]
  unfold vH
  rw [ne_compose hω hV, sw_compose hω hV]
  abel

/-- **`lem:gluing-aligned`, ordinary case, `b = 0`.**  For an ordinary `ω` and an ordinary `η` on
`U = V ∘_ω E` with displacement content `N_V q`, the displacement of `η` is the image under
`L_ω` of one of the two edge readings `v_H`, `v_V = v_H - e` of `V`, and the case of `η` is
that of the product with the empty mark (horizontal reading) or the opposite one (vertical
reading, the gauge of `eq:gluing-gauge`).

The proof compares the two lower end caps of `ω` and `η` (the diagonals `w - 1` and `w`), read in
the diagonals of the composite given by the class rows of `ord_classRows`.

**Differs from the paper's route.**  The paper places the extreme singleton of the marked copy in
an interval with one or two cells (a deleted interior singleton would violate III); here the
displacement is read from the lower end caps of `η` against those of `ω`, which already encode
III and IV. -/
theorem ordinary_edge_displacement_proof (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed)
    (hV : IsConnectedSkew V) (hη : η.IsLegal) (hηord : ¬ η.case.IsMixed)
    (hU : η.E = ω.compose V) (ha : content η.v = (span V : ℤ) * ω.period) :
    (η.v = ω.lat (vH V) ∧ η.ordSign = ω.ordSign) ∨
      (η.v = ω.lat (vH V) - ω.ordSign • eCell ∧ η.ordSign = -ω.ordSign) := by
  by_cases hW : ω.W = ∅
  · obtain ⟨hv, hc⟩ := edge_empty hω hW hV hη hU ha
    have hωe : ω.IsEmptyMark := by
      rcases hω.1.2 with h | h
      · exact h
      · exact absurd hW h.1.ne_empty
    left
    refine ⟨hv, ?_⟩
    simp [ordSign, hc, hωe.2.2]
  · have hωn : ω.IsLegalNonempty := ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    have hwη : η.width = ω.width := width_eq_of_edge hω hV hη hU ha
    have hwpos : 1 ≤ ω.widthZ := hωn.width_pos
    have hηW : η.W.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, ← width_eq_zero_iff, hwη]
      unfold widthZ at hwpos
      omega
    have hηn : η.IsLegalNonempty := ⟨hη, hηW⟩
    have hsp := span_eq_of_isConnectedSkew hV
    have hper : ω.period = ω.v.2 - ω.v.1 := rfl
    have hvη : η.v.2 - η.v.1 = (span V : ℤ) * ω.period := ha
    have hlat := lat_eq ω (vH V)
    rw [content_vH hV, vH_fst] at hlat
    rcases edge_nonempty hωn hord hV hηn hηord hU ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨?_, h2⟩
      rw [hlat]
      have h1' : η.v.1 = (span V : ℤ) * ω.v.1 + ω.ordSign * ((ne V).1 - (sw V).1) := h1
      ext
      · exact h1'
      · dsimp only
        linear_combination h1' + hvη + (span V : ℤ) * hper
    · right
      refine ⟨?_, h2⟩
      rw [hlat]
      have h1' : η.v.1 = (span V : ℤ) * ω.v.1 + ω.ordSign * ((ne V).1 - (sw V).1) -
          ω.ordSign := h1
      ext
      · simp only [Prod.fst_sub, eCell, Prod.smul_mk, smul_eq_mul, mul_one]
        exact h1'
      · simp only [Prod.snd_sub, eCell, Prod.smul_mk, smul_eq_mul, mul_one]
        linear_combination h1' + hvη + (span V : ℤ) * hper

end MarkedInner

end GluingCore
