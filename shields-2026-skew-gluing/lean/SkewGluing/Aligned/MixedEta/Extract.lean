import SkewGluing.Aligned.CaseD.Eta
import SkewGluing.Aligned.MixedEta.Package

set_option linter.unusedSectionVars false

/-!
# The lower mark of an aligned pair: diagonal data from the upper mark

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-ordinary-endpoints`, `eq:gluing-walk-signs`), the private
sampling of the upper mark `η` at the singleton diagonal `w` of `E`.

For an ordinary `ω` and a case-(d) mark `η` on `U = V ∘_ω E`, the diagonals of `η` are read
through `eq:gluing-ordinary-endpoints` (`ordLo`, `ordHi`).  `Setup.private_sides` and
`Setup.private_tails` are the walk signs of `eq:gluing-walk-signs`, `Setup.package_a` gives the
diagonal package of `V` when `ω` is of case (a) and `Setup.b_pos_a` shows `b > 0`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

namespace MixedEta

variable {ω η : MarkedInner} {V : Diagram}

theorem ordLo_private {J ρ : ℤ} (hJ : minContent V ≤ J ∧ J ≤ maxContent V)
    (hρ : ω.widthZ ≤ ρ) : ω.ordLo V J ρ = ω.oRowLo V J + ω.lo ρ := by
  have : ¬ (ρ < ω.widthZ ∧ minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V) := by omega
  unfold ordLo
  rw [DPackage.ite_pos' hJ, DPackage.ite_neg' this]

theorem ordHi_private {J ρ : ℤ} (hJ : minContent V ≤ J ∧ J ≤ maxContent V)
    (hρ : ω.widthZ ≤ ρ) : ω.ordHi V J ρ = ω.oRowHi V J + ω.hi ρ := by
  have : ¬ (ρ < ω.widthZ ∧ minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V) := by omega
  unfold ordHi
  rw [DPackage.ite_pos' hJ, DPackage.ite_neg' this]

theorem ordLo_two {J ρ : ℤ} (hJ : minContent V ≤ J ∧ J ≤ maxContent V)
    (hJ1 : minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V) (hρ : ρ < ω.widthZ) :
    ω.ordLo V J ρ = min (ω.oRowLo V J + ω.lo ρ) (ω.oRowLo V (J - 1) + ω.lo (ρ + ω.period)) := by
  unfold ordLo
  rw [DPackage.ite_pos' hJ, DPackage.ite_pos' ⟨hρ, hJ1.1, hJ1.2⟩]

theorem ordHi_two {J ρ : ℤ} (hJ : minContent V ≤ J ∧ J ≤ maxContent V)
    (hJ1 : minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V) (hρ : ρ < ω.widthZ) :
    ω.ordHi V J ρ = max (ω.oRowHi V J + ω.hi ρ) (ω.oRowHi V (J - 1) + ω.hi (ρ + ω.period)) := by
  unfold ordHi
  rw [DPackage.ite_pos' hJ, DPackage.ite_pos' ⟨hρ, hJ1.1, hJ1.2⟩]

theorem ordLo_first {J ρ : ℤ} (hJ : minContent V ≤ J ∧ J ≤ maxContent V)
    (hJ1 : ¬ (minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V)) :
    ω.ordLo V J ρ = ω.oRowLo V J + ω.lo ρ := by
  have : ¬ (ρ < ω.widthZ ∧ minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V) := fun h => hJ1 h.2
  unfold ordLo
  rw [DPackage.ite_pos' hJ, DPackage.ite_neg' this]

theorem ordHi_first {J ρ : ℤ} (hJ : minContent V ≤ J ∧ J ≤ maxContent V)
    (hJ1 : ¬ (minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V)) :
    ω.ordHi V J ρ = ω.oRowHi V J + ω.hi ρ := by
  have : ¬ (ρ < ω.widthZ ∧ minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V) := fun h => hJ1 h.2
  unfold ordHi
  rw [DPackage.ite_pos' hJ, DPackage.ite_neg' this]

theorem ordLo_prev {J ρ : ℤ} (hJ : ¬ (minContent V ≤ J ∧ J ≤ maxContent V)) :
    ω.ordLo V J ρ = ω.oRowLo V (J - 1) + ω.lo (ρ + ω.period) := by
  unfold ordLo
  rw [DPackage.ite_neg' hJ]

theorem ordHi_prev {J ρ : ℤ} (hJ : ¬ (minContent V ≤ J ∧ J ≤ maxContent V)) :
    ω.ordHi V J ρ = ω.oRowHi V (J - 1) + ω.hi (ρ + ω.period) := by
  unfold ordHi
  rw [DPackage.ite_neg' hJ]

/-- The diagonals of `V ∘_ω E` for a legal ordinary `ω`, nonempty or empty. -/
theorem diag_compose_ord (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed) (hV : IsConnectedSkew V)
    {J ρ : ℤ} (h0 : 0 ≤ ρ) (h1 : ρ < ω.period)
    (hv : ValidClass (minContent V) (maxContent V) ω.widthZ J ρ) :
    diagLo (ω.compose V) (minContent ω.E + (J * ω.period + ρ)) = ω.ordLo V J ρ ∧
    diagHi (ω.compose V) (minContent ω.E + (J * ω.period + ρ)) = ω.ordHi V J ρ := by
  by_cases hW : ω.W = ∅
  · have hE : ω.IsLegalEmpty := ⟨hω, hW⟩
    have hc := hE.classRows hV
    have hw := hE.width_zero
    have hJ : minContent V ≤ J ∧ J ≤ maxContent V := by
      unfold ValidClass at hv
      omega
    refine ⟨?_, ?_⟩
    · rw [hc.diagLo_eq h0 h1 hv, ordLo_private hJ (by omega)]
    · rw [hc.diagHi_eq h0 h1 hv, ordHi_private hJ (by omega)]
  · have h : ω.IsLegalNonempty := ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    have hc := ord_classRows h hV hord
    exact ⟨hc.diagLo_eq h0 h1 hv, hc.diagHi_eq h0 h1 hv⟩

/-- The diagonals of the upper mark `η` on `U = V ∘_ω E`, in the diagonal classes of `U`. -/
theorem eta_lo_hi (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed) (hV : IsConnectedSkew V)
    (hU : η.E = ω.compose V) {J ρ : ℤ} (h0 : 0 ≤ ρ) (h1 : ρ < ω.period)
    (hv : ValidClass (minContent V) (maxContent V) ω.widthZ J ρ) :
    η.lo ((J - minContent V) * ω.period + ρ) = ω.ordLo V J ρ ∧
    η.hi ((J - minContent V) * ω.period + ρ) = ω.ordHi V J ρ := by
  have hmin := hω.minContent_compose hV
  have := diag_compose_ord hω hord hV h0 h1 hv
  unfold lo hi
  rw [hU, hmin]
  have e : minContent ω.E + minContent V * ω.period + ((J - minContent V) * ω.period + ρ) =
      minContent ω.E + (J * ω.period + ρ) := by ring
  rw [e]
  exact this


/-- The cells of `V ∘_ω E` in terms of the diagonal classes, for a legal ordinary `ω`. -/
theorem mem_compose_class (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed) (hV : IsConnectedSkew V)
    {J ρ r : ℤ} (h0 : 0 ≤ ρ) (h1 : ρ < ω.period) :
    (r, r + (minContent ω.E + (J * ω.period + ρ))) ∈ ω.compose V ↔
      ValidClass (minContent V) (maxContent V) ω.widthZ J ρ ∧ ω.ordLo V J ρ ≤ r ∧
        r ≤ ω.ordHi V J ρ := by
  by_cases hW : ω.W = ∅
  · have hE : ω.IsLegalEmpty := ⟨hω, hW⟩
    have hc := hE.classRows hV
    have hw := hE.width_zero
    rw [hc.rows J ρ r h0 h1]
    constructor
    · rintro ⟨hv, h2, h3⟩
      have hJ : minContent V ≤ J ∧ J ≤ maxContent V := by unfold ValidClass at hv; omega
      exact ⟨hv, by rw [ordLo_private hJ (by omega)]; exact h2,
        by rw [ordHi_private hJ (by omega)]; exact h3⟩
    · rintro ⟨hv, h2, h3⟩
      have hJ : minContent V ≤ J ∧ J ≤ maxContent V := by unfold ValidClass at hv; omega
      exact ⟨hv, by rw [ordLo_private hJ (by omega)] at h2; exact h2,
        by rw [ordHi_private hJ (by omega)] at h3; exact h3⟩
  · have h : ω.IsLegalNonempty := ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    exact (ord_classRows h hV hord).rows J ρ r h0 h1

/-! ### The upper mark `η` -/

theorem eta_nonempty (hη : η.IsLegal) (hηd : η.case = .d) : η.IsLegalNonempty := by
  refine ⟨hη, ?_⟩
  rcases hη.1.2 with hemp | hnon
  · exfalso
    have := hemp.2.2
    rw [hηd] at this
    exact absurd this (by decide)
  · exact hnon.1

theorem eta_widthZ (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hη : η.IsLegal)
    (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    η.widthZ = ((span V : ℤ) - a) * ω.period + ω.widthZ := by
  have h1 := hη.1.span_eq
  have h2 := span_compose hV hω
  rw [hU] at h1
  have hper : η.period = a * ω.period := ha
  unfold widthZ
  nlinarith

/-- The contents of `V` are `[m, m + N - 1]`. -/
theorem maxContent_eq_of_span (hV : IsConnectedSkew V) :
    maxContent V = minContent V + (span V : ℤ) - 1 := by
  have := span_eq_of_isConnectedSkew hV
  omega


/-- The standing hypotheses of the lemma for an ordinary `ω` and an upper mark `η` of case (d). -/
structure Setup (ω η : MarkedInner) (V : Diagram) (a : ℤ) : Prop where
  hω : ω.IsLegal
  hord : ¬ ω.case.IsMixed
  hV : IsConnectedSkew V
  hη : η.IsLegal
  hηd : η.case = .d
  hU : η.E = ω.compose V
  ha : content η.v = a * ω.period

namespace Setup

variable {a : ℤ} (S : Setup ω η V a)
include S

theorem q_pos : 0 < ω.period := S.hω.period_pos

theorem w_nonneg : 0 ≤ ω.widthZ := by unfold widthZ; positivity

theorem w_lt_q : ω.widthZ < ω.period := S.hω.2.2.1.2

theorem eta_period : η.period = a * ω.period := S.ha

theorem eta_rowShift : η.rowShift = η.v.1 := rfl

theorem a_le : a ≤ (span V : ℤ) := eta_le_span S.hω S.hV S.hη S.hU S.ha

theorem two_a_gt : (span V : ℤ) < 2 * a := eta_lt_two_mul S.hω S.hV S.hη S.hU S.ha

theorem eta_w : η.widthZ = ((span V : ℤ) - a) * ω.period + ω.widthZ :=
  eta_widthZ S.hω S.hV S.hη S.hU S.ha

theorem eta_ne : η.IsLegalNonempty := eta_nonempty S.hη S.hηd

theorem span_pos : 1 ≤ (span V : ℤ) := by
  have := span_eq_of_isConnectedSkew S.hV
  have h1 := minContent_le (maxContent_mem S.hV.2.1)
  omega

theorem a_pos : 1 ≤ a := by have := S.two_a_gt; have := S.span_pos; omega

theorem M_eq : maxContent V = minContent V + (span V : ℤ) - 1 := maxContent_eq_of_span S.hV

/-- Private sampling of the offsets of `η`: on the marked residue `(J - m) q + w`, with
`m ≤ J` and `J + a ≤ M`, `η.dHi` and `η.dLo` are the offsets of the origin rows. -/
theorem priv_dHi {J : ℤ} (h1 : minContent V ≤ J) (h2 : J + a ≤ maxContent V) :
    η.dHi ((J - minContent V) * ω.period + ω.widthZ) =
      ω.oRowHi V (J + a) - ω.oRowHi V J - η.v.1 := by
  have hq := S.q_pos
  have hw0 := S.w_nonneg
  have hwq := S.w_lt_q
  unfold dHi
  have e : (J - minContent V) * ω.period + ω.widthZ + η.period =
      (J + a - minContent V) * ω.period + ω.widthZ := by rw [S.eta_period]; ring
  rw [e]
  have b1 := (eta_lo_hi S.hω S.hord S.hV S.hU (J := J) (ρ := ω.widthZ) hw0 hwq
    (Or.inl ⟨h1, by have := S.a_pos; omega⟩)).2
  have b2 := (eta_lo_hi S.hω S.hord S.hV S.hU (J := J + a) (ρ := ω.widthZ) hw0 hwq
    (Or.inl ⟨by have := S.a_pos; have := S.M_eq; have := S.span_pos; omega, h2⟩)).2
  rw [b1, b2, ordHi_private ⟨h1, by have := S.a_pos; omega⟩ le_rfl,
    ordHi_private ⟨by have := S.a_pos; have := S.M_eq; have := S.span_pos; omega, h2⟩ le_rfl,
    S.eta_rowShift]
  ring

theorem priv_dLo {J : ℤ} (h1 : minContent V ≤ J) (h2 : J + a ≤ maxContent V) :
    η.dLo ((J - minContent V) * ω.period + ω.widthZ) =
      ω.oRowLo V (J + a) - ω.oRowLo V J - η.v.1 := by
  have hq := S.q_pos
  have hw0 := S.w_nonneg
  have hwq := S.w_lt_q
  unfold dLo
  have e : (J - minContent V) * ω.period + ω.widthZ + η.period =
      (J + a - minContent V) * ω.period + ω.widthZ := by rw [S.eta_period]; ring
  rw [e]
  have b1 := (eta_lo_hi S.hω S.hord S.hV S.hU (J := J) (ρ := ω.widthZ) hw0 hwq
    (Or.inl ⟨h1, by have := S.a_pos; omega⟩)).1
  have b2 := (eta_lo_hi S.hω S.hord S.hV S.hU (J := J + a) (ρ := ω.widthZ) hw0 hwq
    (Or.inl ⟨by have := S.a_pos; have := S.M_eq; have := S.span_pos; omega, h2⟩)).1
  rw [b1, b2, ordLo_private ⟨h1, by have := S.a_pos; omega⟩ le_rfl,
    ordLo_private ⟨by have := S.a_pos; have := S.M_eq; have := S.span_pos; omega, h2⟩ le_rfl,
    S.eta_rowShift]
  ring


theorem idx_range {j : ℤ} (_hb : 1 ≤ (span V : ℤ) - a) (h1 : minContent V ≤ j)
    (h2 : j ≤ minContent V + ((span V : ℤ) - a) - 1) :
    0 ≤ (j - minContent V) * ω.period + ω.widthZ ∧
      (j - minContent V) * ω.period + ω.widthZ ≤ η.widthZ - 1 := by
  have hq := S.q_pos
  have hw0 := S.w_nonneg
  have h3 : 0 ≤ (j - minContent V) * ω.period := mul_nonneg (by omega) hq.le
  have h4 : (j - minContent V) * ω.period ≤ (((span V : ℤ) - a) - 1) * ω.period :=
    mul_le_mul_of_nonneg_right (by omega) hq.le
  rw [S.eta_w]
  constructor <;> nlinarith

theorem private_sides {j : ℤ} (hb : 1 ≤ (span V : ℤ) - a) (h1 : minContent V ≤ j)
    (h2 : j ≤ minContent V + ((span V : ℤ) - a) - 1) :
    ω.oRowHi V (j + a) - ω.oRowHi V j - η.v.1 = 0 ∧
    -1 ≤ ω.oRowLo V (j + a) - ω.oRowLo V j - η.v.1 ∧
    ω.oRowLo V (j + a) - ω.oRowLo V j - η.v.1 ≤ 1 := by
  have hr := S.idx_range hb h1 h2
  have hj : j + a ≤ maxContent V := by have := S.M_eq; omega
  have e1 := S.priv_dHi h1 hj
  have e2 := S.priv_dLo h1 hj
  have s1 := S.eta_ne.sides_d S.hηd hr.1 hr.2
  have t1 := S.eta_ne.thin_lower _ hr.1 hr.2
  have t2 := S.eta_ne.thin_upper hr.1 hr.2
  rw [e1] at s1
  rw [e2] at t1 t2
  omega

theorem private_tails {j j' : ℤ} (hb : 1 ≤ (span V : ℤ) - a) (h1 : minContent V ≤ j) (hjj : j < j')
    (h2 : j' ≤ minContent V + ((span V : ℤ) - a) - 1) :
    (0 < ω.oRowLo V (j + a) - ω.oRowLo V j - η.v.1 →
      0 < ω.oRowLo V (j' + a) - ω.oRowLo V j' - η.v.1) ∧
    (ω.oRowLo V (j' + a) - ω.oRowLo V j' - η.v.1 < 0 →
      ω.oRowLo V (j + a) - ω.oRowLo V j - η.v.1 < 0) := by
  have hq := S.q_pos
  have hr := S.idx_range hb h1 (by omega)
  have hr' := S.idx_range hb (by omega) h2
  have hj : j + a ≤ maxContent V := by have := S.M_eq; omega
  have hj' : j' + a ≤ maxContent V := by have := S.M_eq; omega
  have e1 := S.priv_dHi h1 hj
  have e2 := S.priv_dLo h1 hj
  have e1' := S.priv_dHi (by omega) hj'
  have e2' := S.priv_dLo (by omega) hj'
  have s1 := S.eta_ne.sides_d S.hηd hr.1 hr.2
  have s1' := S.eta_ne.sides_d S.hηd hr'.1 hr'.2
  have hle : (j - minContent V) * ω.period + ω.widthZ ≤
      (j' - minContent V) * ω.period + ω.widthZ := by
    have := mul_le_mul_of_nonneg_right (show j - minContent V ≤ j' - minContent V by omega) hq.le
    omega
  rw [e1] at s1
  rw [e1'] at s1'
  constructor
  · intro hg
    have hT : η.TailLower ((j - minContent V) * ω.period + ω.widthZ) := by
      unfold TailLower; left; rw [e2]; exact hg
    have := S.eta_ne.tail_mono hr.1 hle hr'.2 hT
    unfold TailLower at this
    rw [e2'] at this
    rw [e1'] at this
    omega
  · intro hg
    have hT : η.TailUpper ((j' - minContent V) * ω.period + ω.widthZ) := by
      unfold TailUpper; left; rw [e2']; exact hg
    have := S.eta_ne.tail_mono_upper hr.1 hle hr'.2 hT
    unfold TailUpper at this
    rw [e2] at this
    rw [e1] at this
    omega


theorem lo_pred_eq_hi : ω.lo (ω.period - 1) = ω.hi (ω.period - 1) := by
  by_cases hW : ω.W = ∅
  · have h : ω.IsLegalEmpty := ⟨S.hω, hW⟩
    exact h.ends.2
  · have h : ω.IsLegalNonempty := ⟨S.hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    exact h.lo_pred_period_eq_hi

theorem lo_w_eq_hi_w' : ω.lo ω.widthZ = ω.hi ω.widthZ := lo_width_eq_hi_width S.hω

/-- The diagonal `m + b` of `V` has equal origin rows at both ends. -/
theorem single_lower (hb : 1 ≤ (span V : ℤ) - a) :
    ω.oRowLo V (minContent V + ((span V : ℤ) - a)) =
      ω.oRowHi V (minContent V + ((span V : ℤ) - a)) := by
  have hq := S.q_pos
  have hw0 := S.w_nonneg
  have hwq := S.w_lt_q
  have hJ : minContent V ≤ minContent V + ((span V : ℤ) - a) ∧
      minContent V + ((span V : ℤ) - a) ≤ maxContent V := by
    have := S.M_eq; have := S.a_pos; omega
  have h := S.eta_ne.lo_w_eq_hi_w
  have e : η.widthZ = (minContent V + ((span V : ℤ) - a) - minContent V) * ω.period + ω.widthZ := by
    rw [S.eta_w]; ring
  rw [e] at h
  have b := eta_lo_hi S.hω S.hord S.hV S.hU (J := minContent V + ((span V : ℤ) - a))
    (ρ := ω.widthZ) hw0 hwq (Or.inl hJ)
  rw [b.1, b.2, ordLo_private hJ le_rfl, ordHi_private hJ le_rfl] at h
  have := S.lo_w_eq_hi_w'
  omega

/-- The diagonal `m + a - 1` of `V` has equal origin rows at both ends. -/
theorem single_upper :
    ω.oRowLo V (minContent V + a - 1) = ω.oRowHi V (minContent V + a - 1) := by
  have hq := S.q_pos
  have hw0 := S.w_nonneg
  have hwq := S.w_lt_q
  have hJ : minContent V ≤ minContent V + a - 1 ∧ minContent V + a - 1 ≤ maxContent V := by
    have := S.M_eq; have := S.a_pos; have := S.a_le; have := S.span_pos; omega
  have h := S.eta_ne.lo_pred_period_eq_hi
  have e : η.period - 1 = (minContent V + a - 1 - minContent V) * ω.period + (ω.period - 1) := by
    rw [S.eta_period]; ring
  rw [e] at h
  have b := eta_lo_hi S.hω S.hord S.hV S.hU (J := minContent V + a - 1)
    (ρ := ω.period - 1) (by omega) (by omega) (Or.inl hJ)
  rw [b.1, b.2, ordLo_private hJ (by omega), ordHi_private hJ (by omega)] at h
  have := S.lo_pred_eq_hi
  omega


theorem oRowLo_a (hs : ω.case = .a) (J : ℤ) : ω.oRowLo V J = J * ω.rowShift + diagLo V J := by
  simp [oRowLo, hs]

theorem oRowHi_a (hs : ω.case = .a) (J : ℤ) : ω.oRowHi V J = J * ω.rowShift + diagHi V J := by
  simp [oRowHi, hs]

/-- Facts on the marked diagonals of an ordinary mark of case (a). -/
theorem omega_caps_a (hs : ω.case = .a) :
    ω.lo (ω.period - 1) = ω.lo 0 + ω.rowShift ∧
    (1 ≤ ω.widthZ → ω.lo (ω.widthZ - 1 + ω.period) = ω.rowShift + ω.lo ω.widthZ) ∧
    (1 ≤ ω.widthZ → ω.hi ω.period = ω.rowShift + ω.hi 0) := by
  have hord := S.hord
  by_cases hW : ω.W = ∅
  · have h : ω.IsLegalEmpty := ⟨S.hω, hW⟩
    have hw := h.width_zero
    refine ⟨?_, fun h1 => by omega, fun h1 => by omega⟩
    have := h.rowShift_eq
    omega
  · have h : ω.IsLegalNonempty := ⟨S.hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    have hT : ω.ordT = 0 := by simp [ordT, hs]
    obtain ⟨⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩⟩ := (ord_E_facts h hord).2.1 hT
    unfold dLo at c1 d3
    unfold dHi at d1
    simp only [zero_add] at d1 d3
    have hw := h.width_pos
    refine ⟨?_, fun _ => by omega, fun _ => by omega⟩
    omega


/-- The origin rows at the two end diagonals of `V` are those of singletons. -/
theorem ends_single : ω.oRowLo V (minContent V) = ω.oRowHi V (minContent V) ∧
    ω.oRowLo V (maxContent V) = ω.oRowHi V (maxContent V) := oRow_ends S.hV

theorem b_pos_a (hs : ω.case = .a) : 1 ≤ (span V : ℤ) - a := by
  have hq := S.q_pos
  have hwq := S.w_lt_q
  have hna := S.a_le
  by_contra hb
  have hb0 : (span V : ℤ) = a := by omega
  have hW := S.eta_w
  rw [hb0, sub_self, zero_mul, zero_add] at hW
  have hη1 := S.eta_ne.width_pos
  have hw1 : 1 ≤ ω.widthZ := by omega
  have hMa : maxContent V + 1 = minContent V + a := by have := S.M_eq; omega
  have hLowV := (S.eta_ne.attach.2.2.2 S.hηd).1
  obtain ⟨-, -, h3⟩ := S.eta_ne.lower_caps_V hLowV
  have hcapsU := (S.eta_ne.upper_caps_H (S.eta_ne.attach.2.2.2 S.hηd).2)
  have hsd0 := S.eta_ne.sides_d S.hηd (a := 0) (le_refl _) (by omega)
  unfold dLo at h3
  unfold dHi at hsd0
  have hper := S.eta_period
  have ωc := S.omega_caps_a hs
  have hends := S.ends_single
  -- lower side
  have e1 : η.widthZ - 1 + η.period = (minContent V + a - minContent V) * ω.period +
      (ω.widthZ - 1) := by rw [hW, hper]; ring
  have b1 := eta_lo_hi S.hω S.hord S.hV S.hU (J := minContent V + a) (ρ := ω.widthZ - 1)
    (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩)
  have e2 : η.widthZ = (minContent V - minContent V) * ω.period + ω.widthZ := by rw [hW]; ring
  have b2 := eta_lo_hi S.hω S.hord S.hV S.hU (J := minContent V) (ρ := ω.widthZ)
    (by omega) (by omega) (Or.inl ⟨le_refl _, by have := S.M_eq; have := S.a_pos; omega⟩)
  rw [e1, b1.1] at h3
  rw [e2, b2.1] at h3
  rw [ordLo_prev (by omega), ordLo_private ⟨le_refl _, by have := S.M_eq; have := S.a_pos; omega⟩
    le_rfl] at h3
  -- upper side
  have e3 : (0 : ℤ) + η.period = (minContent V + a - minContent V) * ω.period + 0 := by
    rw [hper]; ring
  have c1 := eta_lo_hi S.hω S.hord S.hV S.hU (J := minContent V + a) (ρ := 0)
    (le_refl _) (by omega) (Or.inr ⟨by omega, by omega⟩)
  have c2 := eta_lo_hi S.hω S.hord S.hV S.hU (J := minContent V) (ρ := 0)
    (le_refl _) (by omega) (Or.inl ⟨le_refl _, by have := S.M_eq; have := S.a_pos; omega⟩)
  rw [e3, c1.2] at hsd0
  have e4 : (0 : ℤ) = (minContent V - minContent V) * ω.period + 0 := by ring
  rw [e4, c2.2] at hsd0
  rw [ordHi_prev (by omega), ordHi_first ⟨le_refl _, by have := S.M_eq; have := S.a_pos; omega⟩
    (by omega)] at hsd0
  have hMM : minContent V + a - 1 = maxContent V := by omega
  rw [hMM] at h3 hsd0
  have c3 := ωc.2.1 hw1
  have c4 := ωc.2.2 hw1
  simp only [sub_self, zero_mul, zero_add] at h3 hsd0
  obtain ⟨hl0, hl1⟩ := hends
  omega


theorem eta_lo_last (hs : ω.case = .a) :
    η.lo (η.widthZ - 1 + η.period) =
      ω.oRowLo V (maxContent V) + ω.lo ω.widthZ + ω.rowShift := by
  have hq := S.q_pos
  have hwq := S.w_lt_q
  have hw0 := S.w_nonneg
  have hM := S.M_eq
  have hper := S.eta_period
  have hW := S.eta_w
  have ωc := S.omega_caps_a hs
  have hMV : minContent V ≤ maxContent V := by have := S.span_pos; omega
  have hN : maxContent V + 1 - minContent V = (span V : ℤ) := by omega
  by_cases hw1 : 1 ≤ ω.widthZ
  · have e1 : η.widthZ - 1 + η.period = (maxContent V + 1 - minContent V) * ω.period +
        (ω.widthZ - 1) := by rw [hW, hper, hN]; ring
    have b1 := eta_lo_hi S.hω S.hord S.hV S.hU (J := maxContent V + 1) (ρ := ω.widthZ - 1)
      (by omega) (by omega) (Or.inr ⟨rfl, by omega⟩)
    rw [e1, b1.1, ordLo_prev (by omega)]
    have := ωc.2.1 hw1
    simp only [add_sub_cancel_right]
    omega
  · have hw : ω.widthZ = 0 := by omega
    have e1 : η.widthZ - 1 + η.period = (maxContent V - minContent V) * ω.period +
        (ω.period - 1) := by
      have hN' : maxContent V - minContent V = (span V : ℤ) - 1 := by omega
      rw [hW, hper, hN', hw]; ring
    have b1 := eta_lo_hi S.hω S.hord S.hV S.hU (J := maxContent V) (ρ := ω.period - 1)
      (by omega) (by omega) (Or.inl ⟨hMV, le_refl _⟩)
    rw [e1, b1.1, ordLo_private ⟨hMV, le_refl _⟩ (by omega), hw]
    have := ωc.1
    omega

theorem eta_lo_W (hb : 0 ≤ (span V : ℤ) - a) :
    η.lo η.widthZ = ω.oRowLo V (minContent V + ((span V : ℤ) - a)) + ω.lo ω.widthZ := by
  have hq := S.q_pos
  have hwq := S.w_lt_q
  have hw0 := S.w_nonneg
  have hM := S.M_eq
  have hJ : minContent V ≤ minContent V + ((span V : ℤ) - a) ∧
      minContent V + ((span V : ℤ) - a) ≤ maxContent V := by
    have := S.a_pos; omega
  have e : η.widthZ = (minContent V + ((span V : ℤ) - a) - minContent V) * ω.period +
      ω.widthZ := by rw [S.eta_w]; ring
  have b := eta_lo_hi S.hω S.hord S.hV S.hU (J := minContent V + ((span V : ℤ) - a))
    (ρ := ω.widthZ) hw0 hwq (Or.inl hJ)
  rw [e, b.1, ordLo_private hJ le_rfl]

theorem eta_lo_zero :
    η.lo 0 = ω.oRowLo V (minContent V) + ω.lo 0 := by
  have hq := S.q_pos
  have hM := S.M_eq
  have hMV : minContent V ≤ maxContent V := by have := S.span_pos; omega
  have b := eta_lo_hi S.hω S.hord S.hV S.hU (J := minContent V) (ρ := 0) (le_refl _) hq
    (Or.inl ⟨le_refl _, hMV⟩)
  simp only [sub_self, zero_mul, add_zero] at b
  rw [b.1, ordLo_first ⟨le_refl _, hMV⟩ (by omega)]

theorem eta_lo_pred :
    η.lo (η.period - 1) = ω.oRowLo V (minContent V + a - 1) + ω.lo (ω.period - 1) := by
  have hq := S.q_pos
  have hwq := S.w_lt_q
  have hw0 := S.w_nonneg
  have hM := S.M_eq
  have hJ : minContent V ≤ minContent V + a - 1 ∧ minContent V + a - 1 ≤ maxContent V := by
    have := S.a_pos; have := S.a_le; have := S.span_pos; omega
  have e : η.period - 1 = (minContent V + a - 1 - minContent V) * ω.period + (ω.period - 1) := by
    rw [S.eta_period]; ring
  have b := eta_lo_hi S.hω S.hord S.hV S.hU (J := minContent V + a - 1) (ρ := ω.period - 1)
    (by omega) (by omega) (Or.inl hJ)
  rw [e, b.1, ordLo_private hJ (by omega)]

theorem package_a (hs : ω.case = .a) :
    DPackage V a ((span V : ℤ) - a) (η.v.1 - a * ω.rowShift) := by
  have hb := S.b_pos_a hs
  have hq := S.q_pos
  have hwq := S.w_lt_q
  have hw0 := S.w_nonneg
  have hM := S.M_eq
  have hna := S.two_a_gt
  have hapos := S.a_pos
  have hends := S.ends_single
  have ωc := S.omega_caps_a hs
  have hmul : ∀ j : ℤ, (j + a) * ω.rowShift = j * ω.rowShift + a * ω.rowShift := fun j => by ring
  have hL : ∀ j, ω.oRowLo V j = j * ω.rowShift + diagLo V j := S.oRowLo_a hs
  have hH : ∀ j, ω.oRowHi V j = j * ω.rowShift + diagHi V j := S.oRowHi_a hs
  have k1 : ∀ j, minContent V ≤ j → j ≤ minContent V + ((span V : ℤ) - a) - 1 →
      diagHi V (j + a) = diagHi V j + (η.v.1 - a * ω.rowShift) := by
    intro j h1 h2
    have h := (S.private_sides hb h1 h2).1
    rw [hH, hH, hmul] at h
    omega
  refine ⟨S.hV, by omega, hb, by omega, k1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j h1 h2
    have h := S.private_sides hb h1 h2
    rw [hL, hL, hmul] at h
    omega
  · intro j j' h1 hjj h2 hg
    have h := (S.private_tails hb h1 hjj h2).1
    rw [hL, hL, hmul, hL, hL, hmul] at h
    have := h (by omega)
    omega
  · intro j j' h1 hjj h2 hg
    have h := (S.private_tails hb h1 hjj h2).2
    rw [hL, hL, hmul, hL, hL, hmul] at h
    have := h (by omega)
    omega
  · have h := S.single_lower hb
    rw [hL, hH] at h
    omega
  · have h := S.single_upper
    rw [hL, hH] at h
    omega
  · intro _
    have hLowV := (S.eta_ne.attach.2.2.2 S.hηd).1
    obtain ⟨-, -, h3⟩ := S.eta_ne.lower_caps_V hLowV
    unfold dLo at h3
    rw [S.eta_lo_last hs, S.eta_lo_W (by omega)] at h3
    have hk := k1 (minContent V + ((span V : ℤ) - a) - 1) (by omega) (le_refl _)
    have e : minContent V + ((span V : ℤ) - a) - 1 + a = maxContent V := by omega
    rw [e] at hk
    have h4 := S.single_lower hb
    rw [hL, hH] at h4
    have h5 := hends.2
    rw [hL, hH] at h5
    simp only [hL] at h3
    have e2 : (minContent V + ((span V : ℤ) - a)) = maxContent V + 1 - a := by omega
    have e3 : (maxContent V) = (minContent V + ((span V : ℤ) - a) - 1) + a := by omega
    have hmul2 : maxContent V * ω.rowShift =
        (minContent V + ((span V : ℤ) - a) - 1) * ω.rowShift + a * ω.rowShift := by
      rw [e3]; ring
    have hmul3 : (minContent V + ((span V : ℤ) - a)) * ω.rowShift =
        (minContent V + ((span V : ℤ) - a) - 1) * ω.rowShift + ω.rowShift := by ring
    have := S.eta_rowShift
    omega
  · intro _
    have hUpH := (S.eta_ne.attach.2.2.2 S.hηd).2
    obtain ⟨-, -, h3⟩ := S.eta_ne.upper_caps_H hUpH
    unfold dLo at h3
    simp only [zero_add] at h3
    rw [S.eta_lo_pred, S.eta_lo_zero] at h3
    have ωc := S.omega_caps_a hs
    have hk := k1 (minContent V) (le_refl _) (by omega)
    have h4 := S.single_upper
    rw [hL, hH] at h4
    have h5 := hends.1
    rw [hL, hH] at h5
    rw [hL, hL] at h3
    have hmul2 : (minContent V + a - 1) * ω.rowShift =
        minContent V * ω.rowShift + a * ω.rowShift - ω.rowShift := by ring
    have := ωc.1
    have := S.eta_rowShift
    omega

end Setup





end MixedEta



end MarkedInner

end SkewGluing
