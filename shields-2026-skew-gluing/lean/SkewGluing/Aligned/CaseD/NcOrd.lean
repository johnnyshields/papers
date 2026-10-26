import SkewGluing.Aligned.CaseD.Nci

/-!
# Aligned marks, case (d): the nested count for an ordinary lower mark

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`eq:gluing-nested-count`: "for ordinary lower cases this follows by taking the minimum of the two
left endpoints and the maximum of the right endpoints").

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {V C : Diagram} {a θ : ℤ}

theorem alD_ord_rows (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hmix : ¬ (alD_lowerMark V a θ).case.IsMixed) {J i : ℤ} (h0 : 0 ≤ i) (h1 : i < a)
    (hv : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i) :
    diagLo ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      (alD_lowerMark V a θ).ordLo C J i ∧
    diagHi ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      (alD_lowerMark V a θ).ordHi C J i := by
  have hl := alD_hμ hV hD
  have hcr := ord_classRows hl hC hmix
  have hw := alD_μ_widthZ hV hD
  have hv' : ValidClass (minContent C) (maxContent C) (alD_lowerMark V a θ).widthZ J i := by
    rw [hw]; exact hv
  have hper := alD_lowerMark_period (V := V) (a := a) (θ := θ)
  have h1' : i < (alD_lowerMark V a θ).period := by rw [hper]; exact h1
  have e1 := hcr.diagLo_eq h0 h1' hv'
  have e2 := hcr.diagHi_eq h0 h1' hv'
  rw [hper] at e1 e2
  exact ⟨e1, e2⟩

theorem alD_C_facts (_hC : IsConnectedSkew C) (J : ℤ) :
    (minContent C ≤ J - 1 ∧ J - 1 ≤ maxContent C →
      profM C (J - 1) = diagHi C (J - 1) - diagLo C (J - 1) + 1) ∧
    (¬ (minContent C ≤ J - 1 ∧ J - 1 ≤ maxContent C) → profM C (J - 1) = 0) ∧
    (minContent C ≤ J ∧ J ≤ maxContent C → profM C J = diagHi C J - diagLo C J + 1) ∧
    (¬ (minContent C ≤ J ∧ J ≤ maxContent C) → profM C J = 0) ∧
    (minContent C + 1 ≤ J ∧ J ≤ maxContent C → profS C J = diagHi C (J - 1) - diagLo C J + 1) ∧
    (¬ (minContent C + 1 ≤ J ∧ J ≤ maxContent C) → profS C J = 1) := by
  refine ⟨fun h => aligned_profM_eq h, fun h => aligned_profM_eq_zero h,
    fun h => aligned_profM_eq h, fun h => aligned_profM_eq_zero h,
    fun h => aligned_profS_eq h, fun h => aligned_profS_eq_one h⟩

theorem alD_C_bits (hC : IsConnectedSkew C) {J : ℤ} :
    minContent C + 1 ≤ J → J ≤ maxContent C →
    (diagLo C (J - 1) - diagLo C J = 0 ∨ diagLo C (J - 1) - diagLo C J = 1) ∧
    (diagHi C (J - 1) - diagHi C J = 0 ∨ diagHi C (J - 1) - diagHi C J = 1) :=
  fun h1 h2 => D_bits hC h1 h2

theorem alD_C_ne (hC : IsConnectedSkew C) {J : ℤ} :
    minContent C ≤ J → J ≤ maxContent C → diagLo C J ≤ diagHi C J := by
  intro h1 h2
  have hs := isConnectedSkew_iff_diagonal.mp hC
  exact diagLo_le_diagHi (hs.mem_contents_iff.mpr ⟨h1, h2⟩)

theorem alD_C_range (hC : IsConnectedSkew C) {J : ℤ}
    (hv : (minContent C ≤ J ∧ J ≤ maxContent C) ∨ J = maxContent C + 1) :
    (minContent C + 1 ≤ J ∧ J ≤ maxContent C ∧
      profM C (J - 1) = diagHi C (J - 1) - diagLo C (J - 1) + 1 ∧
      profM C J = diagHi C J - diagLo C J + 1 ∧
      profS C J = diagHi C (J - 1) - diagLo C J + 1 ∧
      (diagLo C (J - 1) - diagLo C J = 0 ∨ diagLo C (J - 1) - diagLo C J = 1) ∧
      (diagHi C (J - 1) - diagHi C J = 0 ∨ diagHi C (J - 1) - diagHi C J = 1) ∧
      diagLo C J ≤ diagHi C J ∧ diagLo C (J - 1) ≤ diagHi C (J - 1)) ∨
    (J = minContent C ∧ J ≤ maxContent C ∧ profM C (J - 1) = 0 ∧
      profM C J = diagHi C J - diagLo C J + 1 ∧ profS C J = 1 ∧ diagLo C J = diagHi C J) ∨
    (J = maxContent C + 1 ∧ minContent C ≤ maxContent C ∧
      profM C (J - 1) = diagHi C (J - 1) - diagLo C (J - 1) + 1 ∧ profM C J = 0 ∧
      profS C J = 1 ∧ diagLo C (J - 1) = diagHi C (J - 1)) := by
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := alD_C_facts hC J
  have hends := D_ends hC
  by_cases h1 : J = maxContent C + 1
  · right; right
    refine ⟨h1, hmM, f1 (by omega), f4 (by omega), f6 (by omega), ?_⟩
    have : J - 1 = maxContent C := by omega
    rw [this]; exact hends.2
  · have hvv : minContent C ≤ J ∧ J ≤ maxContent C := by omega
    by_cases h2 : J = minContent C
    · right; left
      refine ⟨h2, hvv.2, f2 (by omega), f3 hvv, f6 (by omega), ?_⟩
      rw [h2]; exact hends.1
    · left
      have hb := alD_C_bits hC (J := J) (by omega) hvv.2
      exact ⟨by omega, hvv.2, f1 (by omega), f3 hvv, f5 ⟨by omega, hvv.2⟩, hb.1, hb.2,
        alD_C_ne hC hvv.1 hvv.2, alD_C_ne hC (by omega) (by omega)⟩

set_option maxHeartbeats 2000000 in
-- the stepping conditions are large linear-arithmetic goals with many case splits
theorem alD_NCM_ord (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hmix : ¬ (alD_lowerMark V a θ).case.IsMixed) {J i : ℤ} (h0 : 0 ≤ i)
    (h1 : i < (span V : ℤ) - a)
    (hv : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i) :
    profM ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      alD_Om V a θ i + alD_CT C (walkDelta V a (2 * (minContent V + i) + 1)) J := by
  have hl := alD_hμ hV hD
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  have hw := alD_μ_widthZ hV hD
  have hrows := alD_ord_rows hV hD hC hmix h0 (by omega) hv
  have hmem := alD_X_class_mem hV hD hC h0 (by omega) hv
  rw [alD_profM_eq_height hmem]
  unfold height
  rw [hrows.1, hrows.2]
  rw [alD_walk_odd_eq hV h0 hap.le (by have := aligned_span_eq hV; omega)]
  have hsides := (ord_E_facts hl hmix).1 i h0 (by omega)
  have hz := alD_zrows hV hD h0 h1
  have he := hD.e_bd i h0 h1
  have t1 := hD.th1 i h0 h1
  have hdl := alD_μ_dLo (V := V) (a := a) (θ := θ) i
  have hdh := alD_μ_dHi (V := V) (a := a) (θ := θ) i
  have hl0 := alD_L_le_H hV (j := i) h0 (by omega)
  have hl1 := alD_L_le_H hV (j := i + a) (by omega) (by omega)
  have hcc : (alD_lowerMark V a θ).case = .a ∨ (alD_lowerMark V a θ).case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : (alD_lowerMark V a θ).case <;> simp_all
  unfold ValidClass at hv
  have hrange := alD_C_range hC (J := J) (by
    rcases hv with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h)
  have hp : (J - 1) * θ = J * θ - θ := by ring
  have hzz : ((alD_H V i - alD_L V i - (alD_H V (i + a) - alD_L V (i + a)) ≤ 0 ∧
      alD_zl V a θ i = alD_L V i ∧ alD_zh V a θ i = alD_H V i) ∨
      (0 ≤ alD_H V i - alD_L V i - (alD_H V (i + a) - alD_L V (i + a)) ∧
      alD_zl V a θ i = alD_L V (i + a) - θ ∧ alD_zh V a θ i = alD_H V (i + a) - θ)) := by
    by_cases h : alD_H V i - alD_L V i - (alD_H V (i + a) - alD_L V (i + a)) ≤ 0
    · exact Or.inl ⟨h, hz.2.2.2.2.2.1 h⟩
    · exact Or.inr ⟨by omega, hz.2.2.2.2.2.2 (by omega)⟩
  have hE : alD_e V a i = (alD_H V i - alD_L V i) - (alD_H V (i + a) - alD_L V (i + a)) := rfl
  have hzb := hz.1
  have hzb2 := hz.2.1
  have hzb3 := hz.2.2.1
  have hzb4 := hz.2.2.2.1
  have hzb5 := hz.2.2.2.2.1
  clear hz hrows hmem hl
  unfold MarkedInner.ordLo MarkedInner.ordHi
  unfold alD_Om alD_CT
  simp only [alD_lowerMark_period, alD_μ_lo, alD_μ_hi, hw]
  rcases hcc with hc | hc
  · have hT : (alD_lowerMark V a θ).ordT = 0 := by simp [MarkedInner.ordT, hc]
    have hs := hsides.1 hT
    simp only [MarkedInner.oRowLo, MarkedInner.oRowHi, hc, alD_μ_rowShift, hp]
    rw [hdl, hdh] at hs
    rw [hdl, hdh] at hsides
    generalize J * θ = Q
    rcases hrange with hA | hB | hCc <;> split_ifs <;> omega
  · have hT : (alD_lowerMark V a θ).ordT = 1 := by simp [MarkedInner.ordT, hc]
    have hs := hsides.2.1 hT
    simp only [MarkedInner.oRowLo, MarkedInner.oRowHi, hc, alD_μ_rowShift, hp]
    rw [hdl, hdh] at hs
    rw [hdl, hdh] at hsides
    generalize J * θ = Q
    rcases hrange with hA | hB | hCc <;> split_ifs <;> omega

theorem alD_profS_V_eq (hV : IsConnectedSkew V) {j : ℤ} (h1 : 1 ≤ j) (h2 : j < (span V : ℤ)) :
    profS V (minContent V + j) = alD_H V (j - 1) - alD_L V j + 1 := by
  have hsp := aligned_span_eq hV
  rw [aligned_profS_eq (by omega)]
  unfold alD_H alD_L
  have e : minContent V + j - 1 = minContent V + (j - 1) := by ring
  rw [e]

set_option maxHeartbeats 1600000 in
-- the stepping conditions are large linear-arithmetic goals with many case splits
/-- The consecutive spans of the composite of an ordinary mark, inside the marked band
(`1 ≤ i < b`). -/
theorem alD_NCS_ord_mid (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hmix : ¬ (alD_lowerMark V a θ).case.IsMixed) {J i : ℤ} (h0 : 1 ≤ i)
    (h1 : i < (span V : ℤ) - a)
    (hv : (minContent C ≤ J ∧ J ≤ maxContent C) ∨ J = maxContent C + 1) :
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profS V (minContent V + i) -
        (if walkDelta V a (2 * (minContent V + i)) = 1 then 1 else 0) +
        alD_CT C (walkDelta V a (2 * (minContent V + i))) J := by
  have hl := alD_hμ hV hD
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  have hw := alD_μ_widthZ hV hD
  have hvc : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i := by
    unfold ValidClass
    rcases hv with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, h1⟩
  have hvp : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J (i - 1) := by
    unfold ValidClass
    rcases hv with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, by omega⟩
  have hrc := alD_ord_rows hV hD hC hmix (by omega) (by omega) hvc
  have hrp := alD_ord_rows hV hD hC hmix (by omega : 0 ≤ i - 1) (by omega) hvp
  have hmem := alD_X_class_mem hV hD hC (by omega) (by omega) hvc
  have hminX := alD_minContent_X hV hD hC
  have hmaxX := alD_maxContent_X hV hD hC
  have hrange : minContent ((alD_lowerMark V a θ).compose C) + 1 ≤ minContent V + (J * a + i) ∧
      minContent V + (J * a + i) ≤ maxContent ((alD_lowerMark V a θ).compose C) := by
    refine ⟨?_, hmem.2⟩
    have hJ : minContent C ≤ J := by rcases hv with h | h <;> omega
    have := mul_le_mul_of_nonneg_right hJ hap.le
    omega
  rw [aligned_profS_eq hrange]
  have e1 : minContent V + (J * a + i) - 1 = minContent V + (J * a + (i - 1)) := by ring
  have e2 : minContent V + i + a = minContent V + (i + a) := by ring
  rw [e1, hrp.2, hrc.1, alD_walk_even_eq, e2,
    alD_profS_V_eq hV h0 (by omega), alD_profS_V_eq hV (j := i + a) (by omega) (by omega)]
  have hs0 := (ord_E_facts hl hmix).1 (i - 1) (by omega) (by omega)
  have hs1 := (ord_E_facts hl hmix).1 i (by omega) (by omega)
  have hdl0 := alD_μ_dLo (V := V) (a := a) (θ := θ) (i - 1)
  have hdh0 := alD_μ_dHi (V := V) (a := a) (θ := θ) (i - 1)
  have hdl1 := alD_μ_dLo (V := V) (a := a) (θ := θ) i
  have hdh1 := alD_μ_dHi (V := V) (a := a) (θ := θ) i
  have t0 := hD.th1 (i - 1) (by omega) (by omega)
  have t1 := hD.th1 i (by omega) (by omega)
  have t2 := hD.th2 i h0 h1
  have hd := hD.d_bd i h0 h1
  have st0 := alD_step hV (j := i) h0 (by omega)
  have st1 := alD_step hV (j := i + a) (by omega) (by omega)
  have l0 := alD_L_le_H hV (j := i - 1) (by omega) (by omega)
  have l1 := alD_L_le_H hV (j := i) (by omega) (by omega)
  have l2 := alD_L_le_H hV (j := i - 1 + a) (by omega) (by omega)
  have l3 := alD_L_le_H hV (j := i + a) (by omega) (by omega)
  have e3 : i + a - 1 = i - 1 + a := by ring
  rw [e3] at st1
  simp only [e3]
  unfold alD_d at hd
  rw [e3] at hd
  unfold alD_e at hd
  have hrg := alD_C_range hC (J := J) hv
  have hp : (J - 1) * θ = J * θ - θ := by ring
  unfold MarkedInner.ordLo MarkedInner.ordHi alD_CT
  simp only [alD_lowerMark_period, alD_μ_lo, alD_μ_hi, hw]
  have hcc : (alD_lowerMark V a θ).case = .a ∨ (alD_lowerMark V a θ).case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : (alD_lowerMark V a θ).case <;> simp_all
  rcases hcc with hc | hc
  · have hT : (alD_lowerMark V a θ).ordT = 0 := by simp [MarkedInner.ordT, hc]
    have hsa := hs0.1 hT
    have hsb := hs1.1 hT
    simp only [MarkedInner.oRowLo, MarkedInner.oRowHi, hc, alD_μ_rowShift, hp]
    rw [hdl0, hdh0] at hsa hs0
    rw [hdl1, hdh1] at hsb hs1
    generalize J * θ = Q
    rcases hrg with hA | hB | hCc <;> split_ifs <;> omega
  · have hT : (alD_lowerMark V a θ).ordT = 1 := by simp [MarkedInner.ordT, hc]
    have hsa := hs0.2.1 hT
    have hsb := hs1.2.1 hT
    simp only [MarkedInner.oRowLo, MarkedInner.oRowHi, hc, alD_μ_rowShift, hp]
    rw [hdl0, hdh0] at hsa hs0
    rw [hdl1, hdh1] at hsb hs1
    generalize J * θ = Q
    rcases hrg with hA | hB | hCc <;> split_ifs <;> omega

/-- The heights on the private diagonals `b ≤ i < a` for an ordinary mark. -/
theorem alD_NCP_ord (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hmix : ¬ (alD_lowerMark V a θ).case.IsMixed) {J i : ℤ} (h0 : (span V : ℤ) - a ≤ i)
    (h1 : i < a) (hJ1 : minContent C ≤ J) (hJ2 : J ≤ maxContent C) :
    profM ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profM V (minContent V + i) + profM C J - 1 := by
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hw := alD_μ_widthZ hV hD
  have hvc : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i := by
    unfold ValidClass; exact Or.inl ⟨hJ1, hJ2⟩
  have hrc := alD_ord_rows hV hD hC hmix (by omega) h1 hvc
  have hmem := alD_X_class_mem hV hD hC (by omega) h1 hvc
  rw [alD_profM_eq_height hmem]
  unfold height
  rw [hrc.1, hrc.2, alD_profM_V hV (by omega) (by omega), aligned_profM_eq ⟨hJ1, hJ2⟩]
  have hl0 := alD_L_le_H hV (j := i) (by omega) (by omega)
  have hcc : (alD_lowerMark V a θ).case = .a ∨ (alD_lowerMark V a θ).case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : (alD_lowerMark V a θ).case <;> simp_all
  unfold MarkedInner.ordLo MarkedInner.ordHi
  simp only [alD_lowerMark_period, alD_μ_lo, alD_μ_hi, hw]
  have hn : ¬ (i < (span V : ℤ) - a ∧ minContent C ≤ J - 1 ∧ J - 1 ≤ maxContent C) := by omega
  have hy : minContent C ≤ J ∧ J ≤ maxContent C := ⟨hJ1, hJ2⟩
  simp only [hn, hy, and_self, ite_true, ite_false]
  rcases hcc with hc | hc <;>
    simp only [MarkedInner.oRowLo, MarkedInner.oRowHi, hc] <;> omega

/-- The consecutive spans on the private diagonals `b < i < a` for an ordinary mark. -/
theorem alD_NCS_ord_priv (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hmix : ¬ (alD_lowerMark V a θ).case.IsMixed) {J i : ℤ} (h0 : (span V : ℤ) - a < i)
    (h1 : i < a) (hJ1 : minContent C ≤ J) (hJ2 : J ≤ maxContent C) :
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profS V (minContent V + i) + profM C J - 1 := by
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hw := alD_μ_widthZ hV hD
  have hvc : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i := by
    unfold ValidClass; exact Or.inl ⟨hJ1, hJ2⟩
  have hvp : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J (i - 1) := by
    unfold ValidClass; exact Or.inl ⟨hJ1, hJ2⟩
  have hrc := alD_ord_rows hV hD hC hmix (by omega) h1 hvc
  have hrp := alD_ord_rows hV hD hC hmix (by omega : 0 ≤ i - 1) (by omega) hvp
  have hmem := alD_X_class_mem hV hD hC (by omega) h1 hvc
  have hminX := alD_minContent_X hV hD hC
  have hrange : minContent ((alD_lowerMark V a θ).compose C) + 1 ≤ minContent V + (J * a + i) ∧
      minContent V + (J * a + i) ≤ maxContent ((alD_lowerMark V a θ).compose C) := by
    refine ⟨?_, hmem.2⟩
    have := mul_le_mul_of_nonneg_right hJ1 hap.le
    omega
  rw [aligned_profS_eq hrange]
  have e1 : minContent V + (J * a + i) - 1 = minContent V + (J * a + (i - 1)) := by ring
  rw [e1, hrp.2, hrc.1, alD_profS_V_eq hV (by omega) (by omega), aligned_profM_eq ⟨hJ1, hJ2⟩]
  have l0 := alD_L_le_H hV (j := i - 1) (by omega) (by omega)
  have hcc : (alD_lowerMark V a θ).case = .a ∨ (alD_lowerMark V a θ).case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : (alD_lowerMark V a θ).case <;> simp_all
  unfold MarkedInner.ordLo MarkedInner.ordHi
  simp only [alD_lowerMark_period, alD_μ_lo, alD_μ_hi, hw]
  have hn : ¬ (i < (span V : ℤ) - a ∧ minContent C ≤ J - 1 ∧ J - 1 ≤ maxContent C) := by omega
  have hn' : ¬ (i - 1 < (span V : ℤ) - a ∧ minContent C ≤ J - 1 ∧ J - 1 ≤ maxContent C) := by
    omega
  have hy : minContent C ≤ J ∧ J ≤ maxContent C := ⟨hJ1, hJ2⟩
  simp only [hn, hn', hy, and_self, ite_true, ite_false]
  rcases hcc with hc | hc <;>
    simp only [MarkedInner.oRowLo, MarkedInner.oRowHi, hc] <;> omega

set_option maxHeartbeats 1600000 in
-- the stepping conditions are large linear-arithmetic goals with many case splits
/-- The consecutive span between the last marked diagonal `b - 1` and the first private diagonal
`b`, for an ordinary mark. -/
theorem alD_NCS_ord_b (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hmix : ¬ (alD_lowerMark V a θ).case.IsMixed) {J : ℤ}
    (hv : (minContent C ≤ J ∧ J ≤ maxContent C)) :
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + ((span V : ℤ) - a))) =
      profS V (minContent V + ((span V : ℤ) - a)) -
        (if walkDelta V a (2 * (minContent V + ((span V : ℤ) - a))) = 1 then 1 else 0) +
        alD_CT C (walkDelta V a (2 * (minContent V + ((span V : ℤ) - a)))) J := by
  have hl := alD_hμ hV hD
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hw := alD_μ_widthZ hV hD
  set b := (span V : ℤ) - a with hbdef
  have hvc : ValidClass (minContent C) (maxContent C) b J b := by
    unfold ValidClass; exact Or.inl hv
  have hvp : ValidClass (minContent C) (maxContent C) b J (b - 1) := by
    unfold ValidClass; exact Or.inl hv
  have hrc := alD_ord_rows hV hD hC hmix (by omega) (by omega) hvc
  have hrp := alD_ord_rows hV hD hC hmix (by omega : 0 ≤ b - 1) (by omega) hvp
  have hmem := alD_X_class_mem hV hD hC (by omega) (by omega) hvc
  have hminX := alD_minContent_X hV hD hC
  have hrange : minContent ((alD_lowerMark V a θ).compose C) + 1 ≤ minContent V + (J * a + b) ∧
      minContent V + (J * a + b) ≤ maxContent ((alD_lowerMark V a θ).compose C) := by
    refine ⟨?_, hmem.2⟩
    have := mul_le_mul_of_nonneg_right hv.1 hap.le
    omega
  rw [aligned_profS_eq hrange]
  have e1 : minContent V + (J * a + b) - 1 = minContent V + (J * a + (b - 1)) := by ring
  have e2 : minContent V + b + a = minContent V + (b + a) := by ring
  have hbaN : b + a = (span V : ℤ) := by omega
  rw [e1, hrp.2, hrc.1, alD_walk_even_eq, e2, hbaN]
  have hSb : profS V (minContent V + b) = alD_H V (b - 1) - alD_L V b + 1 :=
    alD_profS_V_eq hV (by omega) (by omega)
  have hSout : profS V (minContent V + (span V : ℤ)) = 1 := by
    apply aligned_profS_eq_one
    omega
  rw [hSb, hSout]
  have hs0 := (ord_E_facts hl hmix).1 (b - 1) (by omega) (by omega)
  have hcaps := (ord_E_facts hl hmix).2
  have hdl0 := alD_μ_dLo (V := V) (a := a) (θ := θ) (b - 1)
  have hdh0 := alD_μ_dHi (V := V) (a := a) (θ := θ) (b - 1)
  have t0 := hD.th1 (b - 1) (by omega) (by omega)
  have hsb := hD.singleton_b
  have st := alD_step hV (j := b) (by omega) (by omega)
  have l0 := alD_L_le_H hV (j := b - 1) (by omega) (by omega)
  have l2 := alD_L_le_H hV (j := b - 1 + a) (by omega) (by omega)
  have el := alD_e_last hV hD
  have hlast := hD.d_last
  have e5 : b - 1 + a = (span V : ℤ) - 1 := by omega
  rw [← hbdef] at hlast el hsb
  unfold alD_e at hlast el
  have hrg := alD_C_range hC (J := J) (Or.inl hv)
  have hp : (J - 1) * θ = J * θ - θ := by ring
  unfold MarkedInner.ordLo MarkedInner.ordHi alD_CT
  simp only [alD_lowerMark_period, alD_μ_lo, alD_μ_hi, hw]
  have hcc : (alD_lowerMark V a θ).case = .a ∨ (alD_lowerMark V a θ).case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : (alD_lowerMark V a θ).case <;> simp_all
  have hbb : ¬ (b < b) := lt_irrefl _
  have hbb' : b - 1 < b := by omega
  rcases hcc with hc | hc
  · have hT : (alD_lowerMark V a θ).ordT = 0 := by simp [MarkedInner.ordT, hc]
    have hsa := hs0.1 hT
    have hcp := hcaps.1 hT
    simp only [MarkedInner.oRowLo, MarkedInner.oRowHi, hc, alD_μ_rowShift, hp]
    rw [hdl0, hdh0] at hsa hs0
    have hc1 := hcp.1
    simp only [hw, alD_μ_lo, alD_μ_hi, hdl0, hdh0] at hc1
    generalize J * θ = Q
    rcases hrg with hA | hB | hCc <;> split_ifs <;> omega
  · have hT : (alD_lowerMark V a θ).ordT = 1 := by simp [MarkedInner.ordT, hc]
    have hsa := hs0.2.1 hT
    have hcp := hcaps.2 hT
    simp only [MarkedInner.oRowLo, MarkedInner.oRowHi, hc, alD_μ_rowShift, hp]
    rw [hdl0, hdh0] at hsa hs0
    have hc1 := hcp.1
    simp only [hw, alD_μ_lo, alD_μ_hi, hdl0, hdh0] at hc1
    generalize J * θ = Q
    rcases hrg with hA | hB | hCc <;> split_ifs <;> omega

set_option maxHeartbeats 1600000 in
-- the stepping conditions are large linear-arithmetic goals with many case splits
/-- The consecutive span between the last private diagonal `a - 1` of the previous period and the
first marked diagonal `0`, for an ordinary mark. -/
theorem alD_NCS_ord_zero (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hmix : ¬ (alD_lowerMark V a θ).case.IsMixed) {J : ℤ}
    (hv : (minContent C ≤ J ∧ J ≤ maxContent C) ∨ J = maxContent C + 1) :
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + 0)) =
      profS V (minContent V + 0) -
        (if walkDelta V a (2 * (minContent V + 0)) = 1 then 1 else 0) +
        alD_CT C (walkDelta V a (2 * (minContent V + 0))) J := by
  have hl := alD_hμ hV hD
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hw := alD_μ_widthZ hV hD
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  have hSa : profS V (minContent V + a) = alD_H V (a - 1) - alD_L V a + 1 :=
    alD_profS_V_eq hV (by omega) (by omega)
  have hS0 : profS V (minContent V + 0) = 1 := by
    apply aligned_profS_eq_one
    omega
  have e0 : minContent V + 0 + a = minContent V + a := by ring
  have hd0 : walkDelta V a (2 * (minContent V + 0)) = 1 - (alD_H V (a - 1) - alD_L V a + 1) := by
    rw [alD_walk_even_eq, e0, hSa, hS0]
  have hsa := hD.singleton_a
  have st := alD_step hV (j := a) (by omega) (by omega)
  have l0 := alD_L_le_H hV (j := a - 1) (by omega) (by omega)
  have l1 := alD_L_le_H hV (j := a) (by omega) (by omega)
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  by_cases hJm : J = minContent C
  · -- the first diagonal of `X`
    have hX : profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + 0)) = 1 := by
      apply aligned_profS_eq_one
      rw [alD_minContent_X hV hD hC, hJm]
      omega
    rw [hX, hS0, hd0]
    have hCm : profM C (J - 1) = 0 := alD_profM_before_min C _ (by omega)
    have hCs : profS C J = 1 := aligned_profS_eq_one (by omega)
    unfold alD_CT
    rw [hCm, hCs]
    split_ifs <;> omega
  · have hJ1 : minContent C + 1 ≤ J := by rcases hv with h | h <;> omega
    have hvc : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J 0 := by
      unfold ValidClass
      rcases hv with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hb⟩
    have hvp : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) (J - 1) (a - 1) := by
      unfold ValidClass
      rcases hv with h | h
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
    have hrc := alD_ord_rows hV hD hC hmix le_rfl hap hvc
    have hrp := alD_ord_rows hV hD hC hmix (by omega : 0 ≤ a - 1) (by omega) hvp
    have hmem := alD_X_class_mem hV hD hC le_rfl hap hvc
    have hminX := alD_minContent_X hV hD hC
    have hrange : minContent ((alD_lowerMark V a θ).compose C) + 1 ≤
        minContent V + (J * a + 0) ∧
        minContent V + (J * a + 0) ≤ maxContent ((alD_lowerMark V a θ).compose C) := by
      refine ⟨?_, hmem.2⟩
      have := mul_le_mul_of_nonneg_right hJ1 hap.le
      have e : (minContent C + 1) * a = minContent C * a + a := by ring
      omega
    rw [aligned_profS_eq hrange]
    have e1 : minContent V + (J * a + 0) - 1 = minContent V + ((J - 1) * a + (a - 1)) := by ring
    rw [e1, hrp.2, hrc.1, hS0, hd0]
    have hs1 := (ord_E_facts hl hmix).1 0 le_rfl (by omega)
    have hcaps := (ord_E_facts hl hmix).2
    have hdl1 := alD_μ_dLo (V := V) (a := a) (θ := θ) 0
    have hdh1 := alD_μ_dHi (V := V) (a := a) (θ := θ) 0
    have t1 := hD.th1 0 le_rfl hb
    have h00 := alD_end0 hV
    have h01 := alD_L_le_H hV (j := 0 + a) (by omega) (by omega)
    have hrg := alD_C_range hC (J := J) hv
    have hp : (J - 1) * θ = J * θ - θ := by ring
    unfold MarkedInner.ordLo MarkedInner.ordHi alD_CT
    simp only [alD_lowerMark_period, alD_μ_lo, alD_μ_hi, hw]
    have hcc : (alD_lowerMark V a θ).case = .a ∨ (alD_lowerMark V a θ).case = .b := by
      unfold AttachCase.IsMixed at hmix
      cases hh : (alD_lowerMark V a θ).case <;> simp_all
    rcases hcc with hc | hc
    · have hT : (alD_lowerMark V a θ).ordT = 0 := by simp [MarkedInner.ordT, hc]
      have hsb := hs1.1 hT
      have hcp := hcaps.1 hT
      simp only [MarkedInner.oRowLo, MarkedInner.oRowHi, hc, alD_μ_rowShift, hp]
      rw [hdl1, hdh1] at hsb hs1
      have hc2 := hcp.2
      simp only [alD_μ_lo, alD_μ_hi, hdl1, hdh1, alD_lowerMark_period] at hc2
      simp only [zero_add] at *
      generalize J * θ = Q
      rcases hrg with hA | hB | hCc <;> split_ifs <;> omega
    · have hT : (alD_lowerMark V a θ).ordT = 1 := by simp [MarkedInner.ordT, hc]
      have hsb := hs1.2.1 hT
      have hcp := hcaps.2 hT
      simp only [MarkedInner.oRowLo, MarkedInner.oRowHi, hc, alD_μ_rowShift, hp]
      rw [hdl1, hdh1] at hsb hs1
      have hc2 := hcp.2
      simp only [alD_μ_lo, alD_μ_hi, hdl1, hdh1, alD_lowerMark_period] at hc2
      simp only [zero_add] at *
      generalize J * θ = Q
      rcases hrg with hA | hB | hCc <;> split_ifs <;> omega

/-- **`eq:gluing-nested-count`** for an ordinary lower mark. -/
theorem alD_NC_ord (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hmix : ¬ (alD_lowerMark V a θ).case.IsMixed) : alD_NC V a θ C := by
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  refine ⟨fun J i h0 h1 hv => alD_NCM_ord hV hD hC hmix h0 h1 hv,
    fun J i h0 h1 hJ1 hJ2 => alD_NCP_ord hV hD hC hmix h0 h1 hJ1 hJ2, ?_,
    fun J i h0 h1 hJ1 hJ2 => alD_NCS_ord_priv hV hD hC hmix h0 h1 hJ1 hJ2⟩
  intro J i h0 h1 hv
  by_cases hi0 : i = 0
  · subst hi0
    exact alD_NCS_ord_zero hV hD hC hmix hv
  by_cases hib : i = (span V : ℤ) - a
  · subst hib
    rcases hv with hv | hv
    · exact alD_NCS_ord_b hV hD hC hmix hv
    · -- the class `(M + 1, b)` lies beyond the last diagonal of `X`
      have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
      have hX : profS ((alD_lowerMark V a θ).compose C)
          (minContent V + (J * a + ((span V : ℤ) - a))) = 1 := by
        apply aligned_profS_eq_one
        rw [alD_maxContent_X hV hD hC, hv]
        have e : (maxContent C + 1) * a = maxContent C * a + a := by ring
        omega
      have hSb : profS V (minContent V + ((span V : ℤ) - a)) =
          alD_H V ((span V : ℤ) - a - 1) - alD_L V ((span V : ℤ) - a) + 1 :=
        alD_profS_V_eq hV (by omega) (by omega)
      have hSout : profS V (minContent V + ((span V : ℤ) - a) + a) = 1 := by
        apply aligned_profS_eq_one
        omega
      have hlast := hD.d_last
      have hel := alD_e_last hV hD
      unfold alD_e at hlast hel
      have hCm : profM C J = 0 := alD_profM_after_max hC J (by omega)
      have hCs : profS C J = 1 := aligned_profS_eq_one (by omega)
      rw [hX, alD_walk_even_eq, hSout, hSb]
      unfold alD_CT
      rw [hCm, hCs]
      split_ifs <;> omega
  · have hib' : i < (span V : ℤ) - a := by omega
    exact alD_NCS_ord_mid hV hD hC hmix (by omega) hib' hv

end MarkedInner

end SkewGluing
