/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/LowerBridge.lean`. -/
import GluingCore.Aligned.LowerRows

/-!
# Sampling a mark on `V ∘_ω E` at the private residue `w`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, ordinary case, `b > 0`: "private sampling").

For an ordinary legal `ω` and a connected `V`, the diagonal of `V ∘_ω E` at the relative content
`(J - m) q + w` is the diagonal of `V` at `J`, shifted: `E` has a singleton diagonal at `w`.
Reading the diagonals of a legal `η` on `V ∘_ω E` at these contents gives the hypotheses
`GlueData` on `V` and the displacement `zOf ω η a` of the lower mark.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

theorem lo_w_eq_hi_w_of_legal (hω : ω.IsLegal) : ω.lo ω.widthZ = ω.hi ω.widthZ := by
  by_cases hW : ω.W = ∅
  · have hE : ω.IsLegalEmpty := ⟨hω, hW⟩
    rw [hE.width_zero]
    exact hE.ends.1
  · have hn : ω.IsLegalNonempty := ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    exact hn.lo_w_eq_hi_w

theorem lo_pred_period_eq_hi_of_legal (hω : ω.IsLegal) :
    ω.lo (ω.period - 1) = ω.hi (ω.period - 1) := by
  by_cases hW : ω.W = ∅
  · have hE : ω.IsLegalEmpty := ⟨hω, hW⟩
    exact hE.ends.2
  · have hn : ω.IsLegalNonempty := ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    exact hn.lo_pred_period_eq_hi

theorem widthZ_nonneg (ω : MarkedInner) : 0 ≤ ω.widthZ := by
  unfold widthZ; positivity

/-- The diagonals of an ordinary composite at a private residue `a ∈ [w, q - 1]`. -/
theorem diag_compose_private (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed)
    (hV : IsConnectedSkew V) {J a : ℤ} (hJ1 : minContent V ≤ J) (hJ2 : J ≤ maxContent V)
    (ha0 : ω.widthZ ≤ a) (ha1 : a < ω.period) :
    diagLo (ω.compose V) (minContent ω.E + (J * ω.period + a)) = ω.oRowLo V J + ω.lo a ∧
      diagHi (ω.compose V) (minContent ω.E + (J * ω.period + a)) =
        ω.oRowHi V J + ω.hi a := by
  have hw0 := widthZ_nonneg ω
  have hv : ValidClass (minContent V) (maxContent V) ω.widthZ J a := Or.inl ⟨hJ1, hJ2⟩
  by_cases hW : ω.W = ∅
  · have hE : ω.IsLegalEmpty := ⟨hω, hW⟩
    have hc := hE.classRows hV
    exact ⟨hc.diagLo_eq (by omega) ha1 hv, hc.diagHi_eq (by omega) ha1 hv⟩
  · have hn : ω.IsLegalNonempty := ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    have hc := ord_classRows hn hV hord
    have hl := hc.diagLo_eq (by omega) ha1 hv
    have hh := hc.diagHi_eq (by omega) ha1 hv
    unfold ordLo at hl
    unfold ordHi at hh
    have hn' : ¬ (ω.widthZ > a) := by omega
    simp only [not_lt.mpr ha0, false_and, ite_false, hJ1, hJ2, and_self, ite_true] at hl hh
    exact ⟨hl, hh⟩

/-- The diagonals of a mark `η` on `V ∘_ω E` at a private residue `a ∈ [w, q - 1]`. -/
theorem eta_sample_at (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed) (hV : IsConnectedSkew V)
    (hU : η.E = ω.compose V) {J a : ℤ} (hJ1 : minContent V ≤ J) (hJ2 : J ≤ maxContent V)
    (ha0 : ω.widthZ ≤ a) (ha1 : a < ω.period) :
    η.lo ((J - minContent V) * ω.period + a) = ω.oRowLo V J + ω.lo a ∧
      η.hi ((J - minContent V) * ω.period + a) = ω.oRowHi V J + ω.hi a := by
  have hmin : minContent η.E = minContent ω.E + minContent V * ω.period := by
    rw [hU]; exact hω.minContent_compose hV
  have e : minContent η.E + ((J - minContent V) * ω.period + a) =
      minContent ω.E + (J * ω.period + a) := by
    rw [hmin]; ring
  have := diag_compose_private hω hord hV hJ1 hJ2 ha0 ha1
  unfold MarkedInner.lo MarkedInner.hi
  rw [e, hU]
  exact this

/-- The sampled diagonals of a mark `η` on `V ∘_ω E`. -/
theorem eta_sample (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed) (hV : IsConnectedSkew V)
    (hU : η.E = ω.compose V) {J : ℤ} (hJ1 : minContent V ≤ J) (hJ2 : J ≤ maxContent V) :
    η.lo ((J - minContent V) * ω.period + ω.widthZ) = ω.oRowLo V J + ω.lo ω.widthZ ∧
      η.hi ((J - minContent V) * ω.period + ω.widthZ) = ω.oRowHi V J + ω.hi ω.widthZ := by
  have hwq : ω.widthZ < ω.period := by
    have := hω.2.2.1.2
    unfold widthZ; exact this
  exact eta_sample_at hω hord hV hU hJ1 hJ2 le_rfl hwq

/-- The data of an ordinary chart `U = V ∘_ω E` and an ordinary legal mark `η` on `U` whose
displacement has content `a q` with `a < N_V`: the hypotheses of `exists_lowerMark_ordinary`. -/
structure LowerChart (ω η : MarkedInner) (V : Diagram) (a : ℤ) : Prop where
  hω : ω.IsLegal
  hord : ¬ ω.case.IsMixed
  hV : IsConnectedSkew V
  hη : η.IsLegal
  hηord : ¬ η.case.IsMixed
  hU : η.E = ω.compose V
  ha : content η.v = a * ω.period
  hpos : a < (span V : ℤ)

/-- The displacement `z` of the lower mark, with `L_ω(z) = v_η`: `z = (θ, θ + a)`,
`θ = ±(p_η - a p)`. -/
def zOf (ω η : MarkedInner) (a : ℤ) : ℤ × ℤ :=
  (ω.ordSign * (η.rowShift - a * ω.rowShift), ω.ordSign * (η.rowShift - a * ω.rowShift) + a)

theorem content_zOf (ω η : MarkedInner) (a : ℤ) : content (zOf ω η a) = a := by
  simp [zOf, content]

theorem ordSign_mul_self (ω : MarkedInner) : ω.ordSign * ω.ordSign = 1 := by
  unfold ordSign; split_ifs <;> norm_num

theorem lat_zOf (ω η : MarkedInner) {a : ℤ} (ha : content η.v = a * ω.period) :
    ω.lat (zOf ω η a) = η.v := by
  have hε := ordSign_mul_self ω
  rw [lat_eq, content_zOf]
  have h1 : η.v.2 - η.v.1 = a * ω.period := ha
  have h2 : ω.period = ω.v.2 - ω.v.1 := rfl
  ext
  · simp only [zOf, rowShift]
    linear_combination (η.v.1 - a * ω.v.1) * hε
  · simp only [zOf, rowShift]
    linear_combination (η.v.1 - a * ω.v.1) * hε - h1 - a * h2

namespace LowerChart

variable {a : ℤ} (C : LowerChart ω η V a)
include C

theorem period_pos : 0 < ω.period := C.hω.period_pos

theorem sep : (span V : ℤ) < 2 * a := by
  have h1 := C.hη.1.span_eq
  have h2 := span_compose C.hV C.hω
  rw [C.hU] at h1
  have hq := C.hω.period_pos
  have hwq := C.hω.2.2.1.2
  have hper : η.period = a * ω.period := C.ha
  have hlt : (η.width : ℤ) < η.period := C.hη.2.2.1.2
  have hw0 : (0 : ℤ) ≤ (ω.width : ℤ) := by positivity
  by_contra hge
  have h3 : 2 * a ≤ (span V : ℤ) := by omega
  have h4 : 2 * a * ω.period ≤ (span V : ℤ) * ω.period := by nlinarith
  nlinarith

theorem alpha_pos : 0 < a := by
  have := C.sep
  have : 0 < (span V : ℤ) := by
    have h := C.hV.2.1
    have : 0 < (contents V).card := Finset.card_pos.mpr (h.image _)
    exact_mod_cast this
  omega

theorem width_eta : (η.width : ℤ) = ((span V : ℤ) - a) * ω.period + ω.width := by
  have h1 := C.hη.1.span_eq
  have h2 := span_compose C.hV C.hω
  rw [C.hU] at h1
  have hper : η.period = a * ω.period := C.ha
  have : (span V : ℤ) * ω.period = a * ω.period + ((span V : ℤ) - a) * ω.period := by ring
  omega

theorem eta_nonempty : η.IsLegalNonempty := by
  refine ⟨C.hη, ?_⟩
  rw [Finset.nonempty_iff_ne_empty, Ne, ← width_eq_zero_iff]
  have h1 := C.width_eta
  have hq := C.period_pos
  have h2 : (1 : ℤ) ≤ (span V : ℤ) - a := by have := C.hpos; omega
  have h3 : 1 * ω.period ≤ ((span V : ℤ) - a) * ω.period := by nlinarith
  have hw0 : (0 : ℤ) ≤ (ω.width : ℤ) := by positivity
  intro h0
  rw [h0] at h1
  simp at h1
  nlinarith

/-- The offsets `dLo`, `dHi` of `η` on the sampled marked diagonals are the gaps `gapLo`, `gapHi`
of `V` against `V - z` (exchanged and negated for a case-(b) mark `ω`). -/
theorem dsample {J : ℤ} (hJ1 : minContent V ≤ J) (hJ2 : J ≤ maxContent V - a) :
    (ω.case = .a →
      η.dLo ((J - minContent V) * ω.period + ω.widthZ) = gapLo V (zOf ω η a) J ∧
        η.dHi ((J - minContent V) * ω.period + ω.widthZ) = gapHi V (zOf ω η a) J) ∧
    (ω.case = .b →
      η.dLo ((J - minContent V) * ω.period + ω.widthZ) = - gapHi V (zOf ω η a) J ∧
        η.dHi ((J - minContent V) * ω.period + ω.widthZ) = - gapLo V (zOf ω η a) J) := by
  have hper : η.period = a * ω.period := C.ha
  have e : (J - minContent V) * ω.period + ω.widthZ + η.period =
      ((J + a) - minContent V) * ω.period + ω.widthZ := by rw [hper]; ring
  have hα := C.alpha_pos
  have s1 := eta_sample C.hω C.hord C.hV C.hU hJ1 (by omega)
  have s2 := eta_sample C.hω C.hord C.hV C.hU (J := J + a) (by omega) (by omega)
  have hm1 : (J + a) * ω.rowShift = J * ω.rowShift + a * ω.rowShift := by ring
  have hz1 : (zOf ω η a).1 = ω.ordSign * (η.rowShift - a * ω.rowShift) := rfl
  have hcz := content_zOf ω η a
  unfold gapLo gapHi
  rw [hcz, hz1]
  unfold dLo dHi
  rw [e, s1.1, s1.2, s2.1, s2.2]
  constructor
  · intro hc
    have hε : ω.ordSign = 1 := by simp [ordSign, hc]
    simp only [oRowLo, oRowHi, hc, hε, one_mul]
    simp only [rowShift] at hm1 ⊢
    omega
  · intro hc
    have hε : ω.ordSign = -1 := by simp [ordSign, hc]
    simp only [oRowLo, oRowHi, hc, hε]
    simp only [rowShift] at hm1 ⊢
    omega

end LowerChart

end MarkedInner

end GluingCore
