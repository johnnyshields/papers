/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/LowerGlue.lean`. -/
import GluingCore.Aligned.LowerBridge

/-!
# The hypotheses `GlueData` from a legal mark on `V ∘_ω E`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, ordinary case, `b > 0`: the lower mark `Z = V ∩ (V - z)`).

The tail structure of the middle of `η` (thinness, intervals, noncrossing), read at the sampled
marked diagonals, becomes the hypotheses `GlueData` of `V` and `z = zOf ω η a`.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

/-- A southeast tail propagates: once `dHi t < 0`, every later marked diagonal has a southeast
tail and no northwest tail. -/
theorem IsLegalNonempty.se_chain (h : ω.IsLegalNonempty) {t : ℤ} (h0 : 0 ≤ t)
    (hs : ω.dHi t < 0) :
    ∀ s : ℤ, t < s → s ≤ ω.widthZ - 1 → ω.dLo s ≤ 0 ∧ ω.dHi s < 0 := by
  intro s hts
  induction s, (show t + 1 ≤ s by omega) using Int.leInduction with
  | base =>
    intro hsw
    have h1 := h.noncross_se_nw h0 hsw hs
    have h3 := h.tail_mono h0 (by omega : t ≤ t + 1) hsw (Or.inr hs)
    unfold TailLower at h3
    omega
  | succ n hn ih =>
    intro hsw
    have ih' := ih (by omega) (by omega)
    have h1 := h.noncross_se_nw (b := n) (by omega) hsw ih'.2
    have h3 := h.tail_mono h0 (by omega : t ≤ n + 1) hsw (Or.inr hs)
    unfold TailLower at h3
    omega

/-- A northwest tail propagates. -/
theorem IsLegalNonempty.nw_chain (h : ω.IsLegalNonempty) {t : ℤ} (h0 : 0 ≤ t)
    (hs : 0 < ω.dLo t) :
    ∀ s : ℤ, t < s → s ≤ ω.widthZ - 1 → 0 ≤ ω.dHi s ∧ 0 < ω.dLo s := by
  intro s hts
  induction s, (show t + 1 ≤ s by omega) using Int.leInduction with
  | base =>
    intro hsw
    have h1 := h.noncross_nw_se h0 hsw hs
    have h3 := h.tail_mono h0 (by omega : t ≤ t + 1) hsw (Or.inl hs)
    unfold TailLower at h3
    omega
  | succ n hn ih =>
    intro hsw
    have ih' := ih (by omega) (by omega)
    have h1 := h.noncross_nw_se (b := n) (by omega) hsw ih'.2
    have h3 := h.tail_mono h0 (by omega : t ≤ n + 1) hsw (Or.inl hs)
    unfold TailLower at h3
    omega

namespace LowerChart

variable {a : ℤ} (C : LowerChart ω η V a)
include C

theorem widthZ_eta : η.widthZ = ((span V : ℤ) - a) * ω.period + ω.widthZ := by
  have := C.width_eta
  unfold widthZ
  exact this

/-- The sampled marked diagonals lie in the marked range of `η`. -/
theorem sample_range {J : ℤ} (hJ1 : minContent V ≤ J) (hJ2 : J ≤ maxContent V - a) :
    0 ≤ (J - minContent V) * ω.period + ω.widthZ ∧
      (J - minContent V) * ω.period + ω.widthZ ≤ η.widthZ - 1 - ω.period + 1 := by
  have hq := C.period_pos
  have hw0 := widthZ_nonneg ω
  have hsp := span_eq_of_isConnectedSkew C.hV
  have h1 := C.widthZ_eta
  have h2 : (J - minContent V) * ω.period ≤ (maxContent V - a - minContent V) * ω.period :=
    mul_le_mul_of_nonneg_right (by omega) hq.le
  have h3 : 0 ≤ (J - minContent V) * ω.period := mul_nonneg (by omega) hq.le
  have e : ((span V : ℤ) - a) * ω.period =
      (maxContent V - a - minContent V) * ω.period + ω.period := by rw [hsp]; ring
  constructor <;> omega

theorem sample_lt {J J' : ℤ} (hJ : J < J') :
    (J - minContent V) * ω.period + ω.widthZ + ω.period ≤
      (J' - minContent V) * ω.period + ω.widthZ := by
  have hq := C.period_pos
  have : (J + 1 - minContent V) * ω.period ≤ (J' - minContent V) * ω.period :=
    mul_le_mul_of_nonneg_right (by omega) hq.le
  have e : (J + 1 - minContent V) * ω.period = (J - minContent V) * ω.period + ω.period := by
    ring
  omega

/-- The marked-diagonal facts of `η` at the sampled index of `J`, in terms of the gaps. -/
theorem sample_facts (hηn : η.IsLegalNonempty) {J : ℤ} (hJ1 : minContent V ≤ J)
    (hJ2 : J ≤ maxContent V - a) :
    (gapLo V (zOf ω η a) J ≤ 1 ∧ -1 ≤ gapHi V (zOf ω η a) J ∧
      ¬ (0 < gapLo V (zOf ω η a) J ∧ gapHi V (zOf ω η a) J < 0)) ∧
    (-1 ≤ gapLo V (zOf ω η a) J ∧ gapHi V (zOf ω η a) J ≤ 1 ∧
      ¬ (gapLo V (zOf ω η a) J < 0 ∧ 0 < gapHi V (zOf ω η a) J)) := by
  have hr := C.sample_range hJ1 hJ2
  have hq := C.period_pos
  have h0 : 0 ≤ (J - minContent V) * ω.period + ω.widthZ := hr.1
  have h1 : (J - minContent V) * ω.period + ω.widthZ ≤ η.widthZ - 1 := by omega
  have a1 := hηn.thin_lower _ h0 h1
  have a2 := hηn.thin_upper h0 h1
  have a3 := hηn.interval_lower h0 h1
  have a4 := hηn.interval_upper h0 h1
  obtain ⟨d1, d2⟩ := C.dsample hJ1 hJ2
  have hcc : ω.case = .a ∨ ω.case = .b := by
    have := C.hord
    unfold AttachCase.IsMixed at this
    cases hh : ω.case <;> simp_all
  rcases hcc with hc | hc
  · obtain ⟨e1, e2⟩ := d1 hc
    rw [e1] at a1 a2 a3 a4
    rw [e2] at a1 a2 a3 a4
    exact ⟨by omega, by omega⟩
  · obtain ⟨e1, e2⟩ := d2 hc
    rw [e1] at a1 a2 a3 a4
    rw [e2] at a1 a2 a3 a4
    exact ⟨by omega, by omega⟩

/-- **The hypotheses `GlueData`, read from a legal mark on `V ∘_ω E`.** -/
theorem glueData : GlueData V (zOf ω η a) := by
  have hηn := C.eta_nonempty
  have hq := C.period_pos
  have hα := C.alpha_pos
  have hcz := content_zOf ω η a
  have hpos := C.hpos
  have hsp := span_eq_of_isConnectedSkew C.hV
  have hwq : ω.widthZ < ω.period := by
    have := C.hω.2.2.1.2
    unfold widthZ; exact this
  have hw0 := widthZ_nonneg ω
  have hsing := lo_w_eq_hi_w_of_legal C.hω
  have hcc : ω.case = .a ∨ ω.case = .b := by
    have := C.hord
    unfold AttachCase.IsMixed at this
    cases hh : ω.case <;> simp_all
  have hperη : η.period = a * ω.period := C.ha
  -- the sampled index of a diagonal, and its relation to the marked range
  have hrg : ∀ J, minContent V ≤ J → J ≤ maxContent V - a →
      0 ≤ (J - minContent V) * ω.period + ω.widthZ ∧
        (J - minContent V) * ω.period + ω.widthZ ≤ η.widthZ - 1 := by
    intro J h1 h2
    have := C.sample_range h1 h2
    omega
  have hshift : ∀ J, (J - minContent V) * ω.period + ω.widthZ + η.period =
      ((J + a) - minContent V) * ω.period + ω.widthZ := by
    intro J; rw [hperη]; ring
  have hM : minContent V ≤ maxContent V := minContent_le (maxContent_mem C.hV.2.1)
  refine ⟨C.hV, by rw [hcz]; exact C.hpos, by rw [hcz]; exact C.sep, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- the lower copy is nonempty on every diagonal
    intro J hJ1 hJ2
    rw [hcz] at hJ2 ⊢
    obtain ⟨h0, h1⟩ := hrg J hJ1 hJ2
    obtain ⟨r, r1, r2, r3, r4⟩ := hηn.W_row h0 h1
    obtain ⟨s1l, s1h⟩ := eta_sample C.hω C.hord C.hV C.hU hJ1 (by omega)
    obtain ⟨s2l, s2h⟩ := eta_sample C.hω C.hord C.hV C.hU (J := J + a) (by omega) (by omega)
    rw [hshift J, s2l] at r3
    rw [hshift J, s2h] at r4
    rw [s1l] at r1
    rw [s1h] at r2
    have hm1 : (J + a) * ω.rowShift = J * ω.rowShift + a * ω.rowShift := by ring
    have hz1 : (zOf ω η a).1 = ω.ordSign * (η.rowShift - a * ω.rowShift) := rfl
    rw [hz1]
    rcases hcc with hc | hc
    · have hε : ω.ordSign = 1 := by simp [ordSign, hc]
      simp only [oRowLo, oRowHi, rowShift, hc, hε, one_mul] at r1 r2 r3 r4 hm1 ⊢
      omega
    · have hε : ω.ordSign = -1 := by simp [ordSign, hc]
      simp only [oRowLo, oRowHi, rowShift, hc, hε] at r1 r2 r3 r4 hm1 ⊢
      omega
  · intro J hJ1 hJ2
    rw [hcz] at hJ2
    exact (C.sample_facts hηn hJ1 hJ2).1
  · intro J hJ1 hJ2
    rw [hcz] at hJ2
    exact (C.sample_facts hηn hJ1 hJ2).2
  · -- tails of the lower middle form a final interval
    intro J J' hJ1 hJJ hJ'2 htl
    rw [hcz] at hJ'2
    obtain ⟨d1, d2⟩ := C.dsample hJ1 (by omega : J ≤ maxContent V - a)
    obtain ⟨d1', d2'⟩ := C.dsample (by omega : minContent V ≤ J') hJ'2
    obtain ⟨h0, -⟩ := hrg J hJ1 (by omega)
    obtain ⟨-, h1'⟩ := hrg J' (by omega) hJ'2
    have hle : (J - minContent V) * ω.period + ω.widthZ ≤
        (J' - minContent V) * ω.period + ω.widthZ := by
      have := mul_le_mul_of_nonneg_right (show J - minContent V ≤ J' - minContent V by omega)
        hq.le
      omega
    have hT : η.TailLower ((J - minContent V) * ω.period + ω.widthZ) → 
        η.TailLower ((J' - minContent V) * ω.period + ω.widthZ) := fun ht =>
      hηn.tail_mono h0 hle h1' ht
    unfold TailLower at hT
    rcases hcc with hc | hc
    · obtain ⟨e1, e2⟩ := d1 hc
      obtain ⟨e1', e2'⟩ := d1' hc
      rw [e1, e2, e1', e2'] at hT
      omega
    · obtain ⟨e1, e2⟩ := d2 hc
      obtain ⟨e1', e2'⟩ := d2' hc
      rw [e1, e2, e1', e2'] at hT
      omega
  · intro J J' hJ1 hJJ hJ'2 htl
    rw [hcz] at hJ'2
    obtain ⟨d1, d2⟩ := C.dsample hJ1 (by omega : J ≤ maxContent V - a)
    obtain ⟨d1', d2'⟩ := C.dsample (by omega : minContent V ≤ J') hJ'2
    obtain ⟨h0, -⟩ := hrg J hJ1 (by omega)
    obtain ⟨-, h1'⟩ := hrg J' (by omega) hJ'2
    have hle : (J - minContent V) * ω.period + ω.widthZ ≤
        (J' - minContent V) * ω.period + ω.widthZ := by
      have := mul_le_mul_of_nonneg_right (show J - minContent V ≤ J' - minContent V by omega)
        hq.le
      omega
    have hT : η.TailUpper ((J' - minContent V) * ω.period + ω.widthZ) → 
        η.TailUpper ((J - minContent V) * ω.period + ω.widthZ) := fun ht =>
      hηn.tail_mono_upper h0 hle h1' ht
    unfold TailUpper at hT
    rcases hcc with hc | hc
    · obtain ⟨e1, e2⟩ := d1 hc
      obtain ⟨e1', e2'⟩ := d1' hc
      rw [e1, e2, e1', e2'] at hT
      omega
    · obtain ⟨e1, e2⟩ := d2 hc
      obtain ⟨e1', e2'⟩ := d2' hc
      rw [e1, e2, e1', e2'] at hT
      omega
  · -- noncrossing: southeast then northwest
    intro J hJ1 hJ2 hk
    rw [hcz] at hJ2
    obtain ⟨d1, d2⟩ := C.dsample hJ1 (by omega : J ≤ maxContent V - a)
    obtain ⟨d1', d2'⟩ := C.dsample (by omega : minContent V ≤ J + 1) hJ2
    obtain ⟨h0, -⟩ := hrg J hJ1 (by omega)
    obtain ⟨-, h1'⟩ := hrg (J + 1) (by omega) hJ2
    have hlt := C.sample_lt (show J < J + 1 by omega)
    rcases hcc with hc | hc
    · obtain ⟨e1, e2⟩ := d1 hc
      obtain ⟨e1', e2'⟩ := d1' hc
      have hk' : η.dHi ((J - minContent V) * ω.period + ω.widthZ) < 0 := by omega
      have := hηn.se_chain h0 hk' ((J + 1 - minContent V) * ω.period + ω.widthZ) (by omega) h1'
      omega
    · obtain ⟨e1, e2⟩ := d2 hc
      obtain ⟨e1', e2'⟩ := d2' hc
      have hk' : 0 < η.dLo ((J - minContent V) * ω.period + ω.widthZ) := by omega
      have := hηn.nw_chain h0 hk' ((J + 1 - minContent V) * ω.period + ω.widthZ) (by omega) h1'
      omega
  · intro J hJ1 hJ2 hk
    rw [hcz] at hJ2
    obtain ⟨d1, d2⟩ := C.dsample hJ1 (by omega : J ≤ maxContent V - a)
    obtain ⟨d1', d2'⟩ := C.dsample (by omega : minContent V ≤ J + 1) hJ2
    obtain ⟨h0, -⟩ := hrg J hJ1 (by omega)
    obtain ⟨-, h1'⟩ := hrg (J + 1) (by omega) hJ2
    have hlt := C.sample_lt (show J < J + 1 by omega)
    rcases hcc with hc | hc
    · obtain ⟨e1, e2⟩ := d1 hc
      obtain ⟨e1', e2'⟩ := d1' hc
      have hk' : 0 < η.dLo ((J - minContent V) * ω.period + ω.widthZ) := by omega
      have := hηn.nw_chain h0 hk' ((J + 1 - minContent V) * ω.period + ω.widthZ) (by omega) h1'
      omega
    · obtain ⟨e1, e2⟩ := d2 hc
      obtain ⟨e1', e2'⟩ := d2' hc
      have hk' : η.dHi ((J - minContent V) * ω.period + ω.widthZ) < 0 := by omega
      have := hηn.se_chain h0 hk' ((J + 1 - minContent V) * ω.period + ω.widthZ) (by omega) h1'
      omega
  · -- the junction diagonal `b` is a singleton
    rw [hcz]
    have hJ1 : minContent V ≤ maxContent V - a + 1 := by omega
    have hJ2 : maxContent V - a + 1 ≤ maxContent V := by omega
    have s := eta_sample C.hω C.hord C.hV C.hU hJ1 hJ2
    have hw := hηn.lo_w_eq_hi_w
    have e : η.widthZ = (maxContent V - a + 1 - minContent V) * ω.period + ω.widthZ := by
      rw [C.widthZ_eta, hsp]; ring
    rw [e, s.1, s.2] at hw
    rcases hcc with hc | hc
    · simp only [oRowLo, oRowHi, hc] at hw
      omega
    · simp only [oRowLo, oRowHi, hc] at hw
      omega
  · -- the junction diagonal `a - 1` is a singleton
    rw [hcz]
    have hJ1 : minContent V ≤ minContent V + a - 1 := by omega
    have hJ2 : minContent V + a - 1 ≤ maxContent V := by omega
    have s := eta_sample_at C.hω C.hord C.hV C.hU hJ1 hJ2 (a := ω.period - 1) (by omega)
      (by omega)
    have hw := hηn.lo_pred_period_eq_hi
    have e : η.period - 1 = (minContent V + a - 1 - minContent V) * ω.period + (ω.period - 1) := by
      rw [hperη]; ring
    have hp := lo_pred_period_eq_hi_of_legal C.hω
    rw [e, s.1, s.2] at hw
    rcases hcc with hc | hc
    · simp only [oRowLo, oRowHi, hc] at hw
      omega
    · simp only [oRowLo, oRowHi, hc] at hw
      omega

end LowerChart

end MarkedInner

end GluingCore
