-- TODO-COPIED from skew-factor-gluing/lean/
-- SkewGluing/OlsonHarris/Plan/EdgeCase/EdgeRibbon/Lift.lean
import GluingCore.OlsonHarris.Plan.EdgeCase.EdgeRibbon.Data

/-!
# The lift of a ribbon of the outer diagram to the composite

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`): the key ribbon `K↑(E)` of a mark of case (a) and the ribbon
`A ∘ K↑(E)` of thesis Lemma 5.4.5 (`OlsonHarris2024HopfApplications`).

The key ribbon is the segment of the northwest border of `E` on the `q` contents starting at the
phase `t` of the upper middle tail (`keyRibbon_eq_segment`), and the lift of the outer segment
on the contents `j₀ ≤ j < j₀ + n` is the segment of the northwest border of the composite on the
`n q` contents starting at `c₀ + t + j₀ q` (`liftRibbon_segment`).

Sorry-free.
-/

set_option linter.style.openClassical false

namespace GluingCore

namespace Plan

namespace EdgeRibbon

open scoped Classical

open GluingCore.MarkedInner

theorem keyRibbon_eq_segment {ω : MarkedInner} (hE : IsConnectedSkew ω.E) {t : ℤ}
    (hmax : maxContent ω.middle = minContent ω.E + ω.period + t - 1) (ht0 : 0 ≤ t)
    (hq : 0 < ω.period) (hmaxE : minContent ω.E + t + ω.period - 1 ≤ maxContent ω.E) :
    keyRibbon ω = segment ω.E (minContent ω.E + t) ω.period.toNat := by
  have hs := isConnectedSkew_iff_diagonal.mp hE
  have hqn : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg hq.le
  ext ⟨r, s⟩
  rw [mem_segment]
  unfold keyRibbon nwBorder
  simp only [Finset.mem_filter, hmax, hqn]
  constructor
  · rintro ⟨⟨hz, hnw⟩, h1, h2⟩
    obtain ⟨k, hk⟩ : ∃ k, k = s - r := ⟨_, rfl⟩
    have e : ((r, s) : ℤ × ℤ) = (r, r + k) := by rw [hk]; ext <;> simp
    have e2 : ((r, s) : ℤ × ℤ) - eCell = (r - 1, r - 1 + k) := by
      rw [hk]; ext <;> simp [eCell]
    rw [e] at hz
    rw [e2] at hnw
    obtain ⟨hkc, hlo, hhi⟩ := hs.mem_iff.mp hz
    have hr : r = diagLo ω.E k := by
      by_contra hne
      exact hnw (hs.mem_iff.mpr ⟨hkc, by omega, by omega⟩)
    have hck : content ((r, s) : ℤ × ℤ) = k := by simp [content, hk]
    rw [hck] at h1 h2
    refine ⟨k, by omega, by omega, ?_⟩
    rw [e, ← hr]
  · rintro ⟨c, hc1, hc2, hz⟩
    simp only [Prod.mk.injEq] at hz
    obtain ⟨hr, hs'⟩ := hz
    have hcc : c ∈ contents ω.E := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
    have hmem : (diagLo ω.E c, diagLo ω.E c + c) ∈ ω.E := diagLo_mem hcc
    have hrs : ((r, s) : ℤ × ℤ) = (diagLo ω.E c, diagLo ω.E c + c) := by
      ext <;> simp <;> omega
    rw [hrs]
    refine ⟨⟨hmem, ?_⟩, ?_, ?_⟩
    · have e2 : ((diagLo ω.E c, diagLo ω.E c + c) : ℤ × ℤ) - eCell =
          (diagLo ω.E c - 1, diagLo ω.E c - 1 + c) := by
        ext
        · simp [eCell]
        · simp only [eCell, Prod.snd_sub]; ring
      rw [e2]
      intro hh
      have := (hs.mem_iff.mp hh).2.1
      omega
    · simp only [content]; omega
    · simp only [content]; omega

theorem origin_a {ω : MarkedInner} (hc : ω.case = .a) (D : Diagram) (j l : ℤ) :
    ω.origin D (l, l + j) = (j * ω.rowShift + l, j * (ω.rowShift + ω.period) + l) := by
  have hv := ω.v_eq
  ext <;> simp [MarkedInner.origin, hc, content, eCell, hv]

theorem exists_class {q d n : ℤ} (hq : 0 < q) (hd0 : 0 ≤ d) (hd : d < n * q) :
    ∃ j i, d = j * q + i ∧ 0 ≤ j ∧ j < n ∧ 0 ≤ i ∧ i < q := by
  refine ⟨d / q, d % q, ?_, Int.ediv_nonneg hd0 hq.le, ?_, Int.emod_nonneg _ hq.ne',
    Int.emod_lt_of_pos _ hq⟩
  · have := Int.mul_ediv_add_emod d q
    linarith
  · by_contra hge
    push Not at hge
    have h1 : n * q ≤ d / q * q := mul_le_mul_of_nonneg_right hge hq.le
    have := Int.mul_ediv_add_emod d q
    have := Int.emod_nonneg d hq.ne'
    nlinarith

/-- **The lift of an outer segment is a segment of the border of the composite** (thesis Lemma 5.4.5
(1), the ribbon `A ∘ K↑(E)`): the copies of the key ribbon at the cells of the outer segment on
the contents `j₀ ≤ j < j₀ + n` form the segment of the northwest border of the composite on the
`n q` contents starting at `c₀ + t + j₀ q`. -/
theorem liftRibbon_segment {ω : MarkedInner} (hc : ω.case = .a) {C : Diagram} {t : ℤ}
    {fLo fHi : ℤ → ℤ → ℤ}
    (hM : BorderModel (ω.compose C) (minContent ω.E) ω.period ω.widthZ t (minContent C)
      (maxContent C) ω.rowShift (diagLo C) ω.lo fLo fHi)
    (hkey : keyRibbon ω = segment ω.E (minContent ω.E + t) ω.period.toNat)
    {j₀ : ℤ} {n : ℕ} (hj1 : minContent C ≤ j₀) (hj2 : j₀ + n - 1 ≤ maxContent C) :
    liftRibbon ω C (segment C j₀ n) =
      segment (ω.compose C) (minContent ω.E + t + j₀ * ω.period) (n * ω.period.toNat) := by
  have hq := hM.cr.hq
  have hqn : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg hq.le
  have ht0 := hM.t0
  have hnq : (((n * ω.period.toNat : ℕ)) : ℤ) = n * ω.period := by push_cast; rw [hqn]
  ext ⟨r, s⟩
  unfold liftRibbon
  rw [Finset.mem_biUnion, mem_segment]
  constructor
  · rintro ⟨b, hb, hz⟩
    obtain ⟨j, hj1', hj2', rfl⟩ := mem_segment.mp hb
    rw [hkey, mem_translate, mem_segment] at hz
    obtain ⟨c, hc1, hc2, hz⟩ := hz
    rw [origin_a hc] at hz
    simp only [Prod.mk_sub_mk, Prod.mk.injEq] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [hqn] at hc2
    have hjq1 : j₀ * ω.period ≤ j * ω.period := mul_le_mul_of_nonneg_right hj1' hq.le
    have hjq2 : (j + 1) * ω.period ≤ (j₀ + n) * ω.period :=
      mul_le_mul_of_nonneg_right (by omega) hq.le
    have hjq3 : (j + 1) * ω.period = j * ω.period + ω.period := by ring
    have hjq4 : (j₀ + n) * ω.period = j₀ * ω.period + n * ω.period := by ring
    refine ⟨c + j * ω.period, by omega, by rw [hnq]; omega, ?_⟩
    have hcore := hM.diagLo_core (j := j) (i := c - (minContent ω.E + t)) (by omega)
      (by omega) (by omega) (by omega)
    have e : minContent ω.E + t + j * ω.period + (c - (minContent ω.E + t)) =
        c + j * ω.period := by ring
    have e2 : ω.lo (t + (c - (minContent ω.E + t))) = diagLo ω.E c := by
      unfold MarkedInner.lo; congr 1; ring
    rw [e, e2] at hcore
    rw [hcore]
    have e3 : j * (ω.rowShift + ω.period) = j * ω.rowShift + j * ω.period := by ring
    ext
    · simp only; omega
    · simp only; omega
  · rintro ⟨k, hk1, hk2, hz⟩
    rw [hnq] at hk2
    obtain ⟨j', i, hd, hj0, hjn, hi0, hiq⟩ := exists_class (n := n) hq
      (d := k - (minContent ω.E + t + j₀ * ω.period)) (by omega) (by omega)
    have hjq : (j₀ + j') * ω.period = j₀ * ω.period + j' * ω.period := by ring
    have hjq2 : (j' + 1) * ω.period ≤ n * ω.period :=
      mul_le_mul_of_nonneg_right (by omega) hq.le
    have hjq3 : (j' + 1) * ω.period = j' * ω.period + ω.period := by ring
    have hcore := hM.diagLo_core (j := j₀ + j') (i := i) (by omega) (by omega) hi0 hiq
    have ek : k = minContent ω.E + t + (j₀ + j') * ω.period + i := by
      rw [hjq]; omega
    refine ⟨(diagLo C (j₀ + j'), diagLo C (j₀ + j') + (j₀ + j')),
      mem_segment.mpr ⟨j₀ + j', by omega, by omega, rfl⟩, ?_⟩
    rw [hkey, mem_translate, origin_a hc, mem_segment]
    refine ⟨minContent ω.E + t + i, by omega, by rw [hqn]; omega, ?_⟩
    rw [ek] at hz
    rw [hcore] at hz
    have e2 : ω.lo (t + i) = diagLo ω.E (minContent ω.E + t + i) := by
      unfold MarkedInner.lo; congr 1; ring
    rw [← e2]
    simp only [Prod.mk_sub_mk, Prod.mk.injEq] at hz ⊢
    obtain ⟨hz1, hz2⟩ := hz
    constructor
    · omega
    · have := hjq
      have : minContent ω.E + t + (j₀ + j') * ω.period + i = minContent ω.E + t + i +
          (j₀ + j') * ω.period := by ring
      have e3 : (j₀ + j') * (ω.rowShift + ω.period) = (j₀ + j') * ω.rowShift +
          (j₀ + j') * ω.period := by ring
      omega

end EdgeRibbon

end Plan

end GluingCore
