import SkewGluing.Decoder.Defs
import SkewGluing.AntitransposeMixed
import SkewGluing.Lines.FirstWindow

/-!
# Heights of the composite on the private diagonals

Formalizes `shields-2026-skew-gluing.tex`, «Reconstructing a chart from its two words»
(`ge:eq:sample`), the private diagonals.

The diagonals `w` and `q - 1` of a legal inner `E` are singletons, so the diagonal of the composite
`D ∘_ω E` at the position `j q + w` (and at `j q + q - 1`) has the height of the outer diagonal of
content `minContent D + j`.  Equivalently `hwd (ω.compose D)` at these positions is `hwd D j`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- The height of the composite on a private diagonal `z` of `E` that is a singleton, for every
case except (c). -/
theorem height_compose_private (h : ω.IsLegal) (hc : ω.case ≠ .c) (hD : IsConnectedSkew D)
    {j z : ℤ} (hj0 : 0 ≤ j) (hj : j < (span D : ℤ)) (hz0 : ω.widthZ ≤ z) (hz1 : z < ω.period)
    (hs : ω.lo z = ω.hi z) :
    height (ω.compose D) (minContent (ω.compose D) + (j * ω.period + z)) =
      height D (minContent D + j) := by
  have hq := h.period_pos
  have hw0 : 0 ≤ ω.widthZ := by unfold widthZ; positivity
  have hsp := span_eq_of_isConnectedSkew hD
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hmin := h.minContent_compose hD
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + j) z :=
    Or.inl ⟨by omega, by omega⟩
  have hpos : minContent (ω.compose D) + (j * ω.period + z) =
      minContent ω.E + ((minContent D + j) * ω.period + z) := by
    rw [hmin]; ring
  unfold height
  rw [hpos]
  by_cases hW : ω.W = ∅
  · have he : ω.IsLegalEmpty := ⟨h, hW⟩
    have hca := he.case_a
    have hcl := he.classRows hD
    have hR : ∀ J, ω.oRowLo D J = J * ω.rowShift + diagLo D J ∧
        ω.oRowHi D J = J * ω.rowShift + diagHi D J := by
      intro J; simp [oRowLo, oRowHi, hca]
    rw [hcl.diagLo_eq (by omega) hz1 hv, hcl.diagHi_eq (by omega) hz1 hv]
    have := hR (minContent D + j)
    have e0 := he.ends
    have hw00 := he.width_zero
    omega
  · have hl : ω.IsLegalNonempty := ⟨h, Finset.nonempty_iff_ne_empty.mpr hW⟩
    obtain ⟨s, t, hph⟩ := hl.exists_phases
    have hw := hl.width_pos
    by_cases hmix : ω.case.IsMixed
    · have hcd : ω.case = .d := by
        rcases hmix with h1 | h1
        · exact absurd h1 hc
        · exact h1
      have hlt := hl.phases_lt (Or.inr hcd) hph
      have hcl := mix_classRows hl hD hcd hph hlt
      rw [hcl.diagLo_eq (by omega) hz1 hv, hcl.diagHi_eq (by omega) hz1 hv,
        mixLo_formula hl hD hcd hph (by omega) hv]
      unfold mixGLo mixHi profM
      have hlt' : ¬ z < ω.widthZ := by omega
      simp only [hlt', ite_false]
      have hin : minContent D ≤ minContent D + j ∧ minContent D + j ≤ maxContent D :=
        ⟨by omega, by omega⟩
      simp only [hin, and_self, ite_true]
      omega
    · have hcl := ord_classRows hl hD hmix
      rw [hcl.diagLo_eq (by omega) hz1 hv, hcl.diagHi_eq (by omega) hz1 hv,
        ordLo_formula hl hD hmix hph (by omega) hv, ordHi_formula hl hD hmix hph (by omega) hv]
      unfold ordGLo ordGHi
      have hlt' : ¬ z < ω.widthZ := by omega
      have ht := ordT_cases hmix
      have hJ : minContent D + j ≤ maxContent D := by omega
      rcases ht with ht | ht
      · simp only [ht, ite_true, hlt', false_and, and_false, ite_false, hJ]
        omega
      · simp only [ht, one_ne_zero, ite_false, hlt', false_and, and_false, hJ, ite_true]
        omega

theorem hwd_compose_private_ne_c (h : ω.IsLegal) (hc : ω.case ≠ .c) (hD : IsConnectedSkew D)
    {j z : ℤ} (hj0 : 0 ≤ j) (hj : j < (span D : ℤ)) (hz0 : ω.widthZ ≤ z) (hz1 : z < ω.period)
    (hs : ω.lo z = ω.hi z) :
    hwd (ω.compose D) (j * ω.period + z) = hwd D j := by
  have hq := h.period_pos
  have hspc := MarkedInner.span_compose hD h
  have hspw : ((ω.width : ℕ) : ℤ) = ω.widthZ := rfl
  have hk : j * ω.period + z < (span (ω.compose D) : ℤ) := by
    rw [hspc, hspw]
    have : (j + 1) * ω.period ≤ (span D : ℤ) * ω.period :=
      mul_le_mul_of_nonneg_right (by omega) hq.le
    nlinarith
  have hk0 : 0 ≤ j * ω.period + z := by
    have := mul_nonneg hj0 hq.le
    omega
  rw [hwd_eq_height (h.isConnectedSkew_compose hD) hk0 hk, hwd_eq_height hD hj0 hj,
    height_compose_private h hc hD hj0 hj hz0 hz1 hs]

/-- The private diagonals `w` and `q - 1` of the inner of a legal mark are singletons. -/
theorem IsLegal.private_singletons (h : ω.IsLegal) :
    ω.lo ω.widthZ = ω.hi ω.widthZ ∧ ω.lo (ω.period - 1) = ω.hi (ω.period - 1) := by
  by_cases hW : ω.W = ∅
  · have he : ω.IsLegalEmpty := ⟨h, hW⟩
    have hw := he.width_zero
    rw [hw]
    exact he.ends
  · have hl : ω.IsLegalNonempty := ⟨h, Finset.nonempty_iff_ne_empty.mpr hW⟩
    exact ⟨hl.lo_w_eq_hi_w, hl.lo_pred_period_eq_hi⟩

/-- **The sampled heights** (`ge:eq:sample`).  For a legal mark of period `f ≥ 2` and a connected
outer `A`, the height `h_P` of the composite `P = A ∘_ω E` at the private positions `j f + w` and
`j f + f - 1` is the height `h_A(j)` of the outer. -/
theorem IsLegal.hwd_compose_private (hω : ω.IsLegal) (hf : 2 ≤ ω.period) {A : Diagram}
    (hA : IsConnectedSkew A) {j : ℤ} (hj0 : 0 ≤ j) (hj : j < (span A : ℤ)) :
    hwd (ω.compose A) (j * ω.period + ω.widthZ) = hwd A j ∧
      hwd (ω.compose A) (j * ω.period + ω.period - 1) = hwd A j := by
  have hw0 : 0 ≤ ω.widthZ := by unfold widthZ; positivity
  have hwq : ω.widthZ < ω.period := hω.2.2.1.2
  have e : j * ω.period + ω.period - 1 = j * ω.period + (ω.period - 1) := by ring
  rw [e]
  have key : ∀ ω' : MarkedInner, ω'.IsLegal → ω'.case ≠ .c → ω'.period = ω.period →
      ω'.widthZ = ω.widthZ →
      hwd (ω'.compose A) (j * ω.period + ω.widthZ) = hwd A j ∧
        hwd (ω'.compose A) (j * ω.period + (ω.period - 1)) = hwd A j := by
    intro ω' h' hc' hp hwd'
    have hwq' : ω'.widthZ < ω'.period := h'.2.2.1.2
    obtain ⟨s1, s2⟩ := h'.private_singletons
    have h1 := hwd_compose_private_ne_c h' hc' hA (z := ω'.widthZ) hj0 hj le_rfl
      (by omega) s1
    have h2 := hwd_compose_private_ne_c h' hc' hA (z := ω'.period - 1) hj0 hj
      (by rw [hwd']; omega) (by omega) s2
    rw [hp, hwd'] at h1
    rw [hp] at h2
    exact ⟨h1, h2⟩
  by_cases hc : ω.case = .c
  · have hW : ω.W.Nonempty := by
      rcases hω.1.2 with he | hn
      · have := he.2.2
        rw [hc] at this
        cases this
      · exact hn.1
    have hl : ω.IsLegalNonempty := ⟨hω, hW⟩
    have hanti : ω.anti.IsLegal := hl.anti.1
    have hAT := antitranspose_compose_of_isLegal hω hA
    have hC := hω.isConnectedSkew_compose hA
    have hcd : ω.anti.case ≠ .c := by
      rw [anti_case, hc]; intro hh; cases hh
    obtain ⟨k1, k2⟩ := key ω.anti hanti hcd (period_anti ω) (widthZ_anti ω)
    have hsp := MarkedInner.span_compose hA hω
    have hspw : ((ω.width : ℕ) : ℤ) = ω.widthZ := rfl
    have hq := hω.period_pos
    have bound : ∀ z, 0 ≤ z → z < ω.period → 0 ≤ j * ω.period + z ∧
        j * ω.period + z ≤ (span (ω.compose A) : ℤ) := by
      intro z hz0 hz1
      have := mul_nonneg hj0 hq.le
      have h3 : (j + 1) * ω.period ≤ (span A : ℤ) * ω.period :=
        mul_le_mul_of_nonneg_right (by omega) hq.le
      rw [hsp, hspw]
      constructor <;> nlinarith
    obtain ⟨b1, b2⟩ := bound ω.widthZ hw0 hwq
    obtain ⟨b3, b4⟩ := bound (ω.period - 1) (by omega) (by omega)
    constructor
    · rw [← hwd_antitranspose hC b1 b2, hAT]; exact k1
    · rw [← hwd_antitranspose hC b3 b4, hAT]; exact k2
  · exact key ω hω hc rfl rfl

end MarkedInner

end SkewGluing
