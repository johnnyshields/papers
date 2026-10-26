-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem/Glue.lean
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.ArithRight
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.Compose
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.Pieces

/-!
# The cells of a composite in the integer form `cellFormP`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`), for a legal mark of case (c).

* `mem_compose_cP`: a cell of `X ∘_ω E` on the diagonal `J q + a` in the form `cellFormP`;
* `Fp`: the composite of an outer that may be empty (`∅` for the empty outer);
* `mem_Fp`: its cells in the form `cellFormP`;
* `window_iff`: the window of diagonals of a lifted ribbon in the coordinates `(J, a)`;
* `eq_diagHi_iff`: the last cell of a diagonal.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace Rem


open MarkedInner

attribute [local instance 10] Classical.propDecidable

variable {ω : MarkedInner} {X : Diagram}

theorem cellFormP_congr {w a loa hia ρ dH sA : ℤ} {cJ cJ1 : Prop} {nJ nJ1 nJ' nJ1' : ℤ}
    {bit bit' : Prop} (hn : cJ → nJ = nJ') (hn1 : cJ1 → nJ1 = nJ1')
    (hb : cJ → cJ1 → (bit ↔ bit')) :
    cellFormP w a loa hia ρ dH sA cJ cJ1 nJ nJ1 bit ↔
      cellFormP w a loa hia ρ dH sA cJ cJ1 nJ' nJ1' bit' := by
  unfold cellFormP
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5, h6⟩)
    · have := hn h1
      exact Or.inl ⟨h1, h2, by omega⟩
    · have := hn1 h2
      exact Or.inr (Or.inl ⟨h1, h2, h3, by omega⟩)
    · have := hn h3
      have := hn1 h2
      exact Or.inr (Or.inr ⟨h1, h2, h3, (hb h3 h2).mp h4, h5, by omega⟩)
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5, h6⟩)
    · have := hn h1
      exact Or.inl ⟨h1, h2, by omega⟩
    · have := hn1 h2
      exact Or.inr (Or.inl ⟨h1, h2, h3, by omega⟩)
    · have := hn h3
      have := hn1 h2
      exact Or.inr (Or.inr ⟨h1, h2, h3, (hb h3 h2).mpr h4, h5, by omega⟩)

theorem mem_compose_cP (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hph : ω.IsPhases s t) (hX : IsSkew X) (hXne : X.Nonempty) {J a r : ℤ} (ha0 : 0 ≤ a)
    (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ ω.compose X ↔
      cellFormP ω.widthZ a (ω.lo a) (ω.hi a) (r - J * ω.rowShift)
        (if a < t then 1 else if a < s then 0 else -1) (if s ≤ a then 1 else 0)
        (J ∈ contents X) (J - 1 ∈ contents X) (height X J) (height X (J - 1))
        (diagLo X J + 1 = diagLo X (J - 1)) := by
  rw [mem_compose_c h hc hph hX hXne ha0 haq]
  unfold cellFormP
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5, h6⟩)
    · exact Or.inl ⟨h1, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨h1, h2, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, h3, h4, by omega, by omega⟩)
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5, h6⟩)
    · exact Or.inl ⟨h1, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨h1, h2, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, h3, h4, by omega, by omega⟩)

/-- The composite of an outer, the empty set for the empty outer. -/
noncomputable def Fp (ω : MarkedInner) (X : Diagram) : Diagram :=
  if X = ∅ then ∅ else ω.compose X

theorem mem_Fp (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hph : ω.IsPhases s t) (hX : IsSkew X) {J a r : ℤ} (ha0 : 0 ≤ a)
    (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ Fp ω X ↔
      cellFormP ω.widthZ a (ω.lo a) (ω.hi a) (r - J * ω.rowShift)
        (if a < t then 1 else if a < s then 0 else -1) (if s ≤ a then 1 else 0)
        (J ∈ contents X) (J - 1 ∈ contents X) (height X J) (height X (J - 1))
        (diagLo X J + 1 = diagLo X (J - 1)) := by
  by_cases hXe : X = ∅
  · subst hXe
    unfold Fp cellFormP
    simp [contents]
  · unfold Fp
    simp only [hXe, ↓reduceIte]
    exact mem_compose_cP h hc hph hX (Finset.nonempty_iff_ne_empty.mpr hXe) ha0 haq

/-- The window of diagonals of a lifted ribbon, in the coordinates `(J, a)`. -/
theorem window_iff {q off j0 m J a : ℤ} (hq : 0 < q) (_hm : 0 ≤ m) (hoff0 : 0 ≤ off)
    (hoff : off < q) (ha0 : 0 ≤ a) (haq : a < q) :
    (j0 * q + off ≤ J * q + a ∧ J * q + a < j0 * q + off + m * q) ↔
      (if off ≤ a then (j0 ≤ J ∧ J < j0 + m) else (j0 ≤ J - 1 ∧ J - 1 < j0 + m)) := by
  have key : ∀ (d e : ℤ), 0 ≤ e → e < q →
      ((0 ≤ d * q + e ∧ d * q + e < m * q) ↔ (0 ≤ d ∧ d < m)) := by
    intro d e he0 he1
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · by_contra hlt
        have := mul_le_mul_of_nonneg_right (by omega : d ≤ -1) hq.le
        omega
      · by_contra hge
        have := mul_le_mul_of_nonneg_right (by omega : m ≤ d) hq.le
        omega
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := mul_nonneg h1 hq.le
        omega
      · have := mul_le_mul_of_nonneg_right (by omega : d + 1 ≤ m) hq.le
        nlinarith
  by_cases hoa : off ≤ a
  · simp only [hoa, ↓reduceIte]
    have := key (J - j0) (a - off) (by omega) (by omega)
    have e1 : (J - j0) * q + (a - off) = J * q + a - (j0 * q + off) := by ring
    rw [e1] at this
    constructor
    · intro hh; have := this.mp ⟨by omega, by omega⟩; omega
    · intro hh; have := this.mpr ⟨by omega, by omega⟩; omega
  · simp only [hoa, ↓reduceIte]
    have := key (J - 1 - j0) (q + a - off) (by omega) (by omega)
    have e1 : (J - 1 - j0) * q + (q + a - off) = J * q + a - (j0 * q + off) := by ring
    rw [e1] at this
    constructor
    · intro hh; have := this.mp ⟨by omega, by omega⟩; omega
    · intro hh; have := this.mpr ⟨by omega, by omega⟩; omega

theorem eq_diagHi_iff {F : Diagram} (hF : HasDiagonalShape F) {x : ℤ × ℤ} (hx : x ∈ F) :
    x.1 = diagHi F (content x) ↔ x + eCell ∉ F := by
  obtain ⟨i, j⟩ := x
  have hk : j - i ∈ contents F := content_mem_contents hx
  have hxe : (i, j) = (i, i + (j - i)) := Prod.ext rfl (by ring)
  rw [hxe] at hx
  have hm := (hF.mem_iff (k := j - i) (i := i)).mp hx
  have hxe' : (i, j) + eCell = (i + 1, (i + 1) + (j - i)) :=
    Prod.ext (by simp [eCell]) (by simp [eCell]; ring)
  rw [hxe', hF.mem_iff]
  simp only [content]
  constructor
  · intro h
    rintro ⟨-, -, h3⟩
    omega
  · intro h
    by_contra hne
    apply h
    have := le_diagHi (D := F) hx (k := j - i) (by ring)
    exact ⟨hk, by omega, by omega⟩

end Rem

end Corner

end Plan

end GluingCore
