/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/Local/Injective.lean
import SkewMarkedFactor.Gluing.Local.Windows

/-!
# Fixed-chart injectivity

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (the paragraph after
`eq:gluing-mixed-profile`): composition with a fixed legal marked inner is injective on connected
outers (up to translation).  Ordinary marks are read on the private diagonal `w`, mixed marks on
the private diagonal `w` and on a marked residue meeting neither middle tail.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace MarkedInner

variable {ω : MarkedInner} {D D' : Diagram}

/-- The diagonal of `D ∘_ω E` on the private residue `w` of the class `J` is `[oRowLo J + ρ,
oRowHi J + ρ]` where `ρ` is the row of the private cell of `E` (ordinary marks). -/
theorem ord_rows_w (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hmix : ¬ ω.case.IsMixed)
    {J : ℤ} (hJ : minContent D ≤ J ∧ J ≤ maxContent D) :
    diagLo (ω.compose D) (minContent ω.E + (J * ω.period + ω.widthZ)) =
      ω.oRowLo D J + ω.lo ω.widthZ ∧
    diagHi (ω.compose D) (minContent ω.E + (J * ω.period + ω.widthZ)) =
      ω.oRowHi D J + ω.hi ω.widthZ := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J ω.widthZ := Or.inl hJ
  have hc := ord_classRows h hD hmix
  refine ⟨?_, ?_⟩
  · rw [hc.diagLo_eq (by omega) hq hv]
    unfold ordLo
    simp only [hJ, and_self, ite_true]
    have : ¬ (ω.widthZ < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D) := by omega
    simp
  · rw [hc.diagHi_eq (by omega) hq hv]
    unfold ordHi
    simp only [hJ, and_self, ite_true]
    have : ¬ (ω.widthZ < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D) := by omega
    simp


theorem IsLegal.shift_data (hω : ω.IsLegal) (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D')
    {t : ℤ × ℤ} (hF : ω.compose D' = translate t (ω.compose D)) :
    content t = (minContent D' - minContent D) * ω.period ∧
      maxContent D' - minContent D' = maxContent D - minContent D := by
  have hq := hω.period_pos
  have hFne : (ω.compose D).Nonempty := by
    obtain ⟨d, hd⟩ := hD.2.1
    obtain ⟨y, hy⟩ := hω.1.1.2.1
    exact ⟨y + ω.origin D d, (mem_compose hD.2.1).mpr
      (Or.inl ⟨d, hd, mem_translate.mpr (by simpa using hy)⟩)⟩
  have e1 := hω.minContent_compose hD
  have e1' := hω.minContent_compose hD'
  have e2 := hω.maxContent_compose hD
  have e2' := hω.maxContent_compose hD'
  rw [hF, minContent_translate hFne, e1] at e1'
  rw [hF, maxContent_translate hFne, e2] at e2'
  have h1 : (minContent D' - minContent D) * ω.period = content t := by
    have : (minContent D' - minContent D) * ω.period =
        minContent D' * ω.period - minContent D * ω.period := by ring
    omega
  refine ⟨h1.symm, ?_⟩
  have h2 : (maxContent D' - maxContent D) * ω.period = content t := by
    have : (maxContent D' - maxContent D) * ω.period =
        maxContent D' * ω.period - maxContent D * ω.period := by ring
    omega
  have : (maxContent D' - minContent D' - (maxContent D - minContent D)) * ω.period = 0 := by
    have : (maxContent D' - minContent D' - (maxContent D - minContent D)) * ω.period =
        (maxContent D' - maxContent D) * ω.period - (minContent D' - minContent D) * ω.period := by
      ring
    omega
  have := (mul_eq_zero.mp this).resolve_right hq.ne'
  omega


/-- The bits of `D` read from the origin rows (ordinary marks). -/
theorem bits_ord (hmix : ¬ ω.case.IsMixed) (D : Diagram) (J : ℤ) :
    (ω.ordT = 0 → bitA D J = ω.oRowLo D (J - 1) - ω.oRowLo D J + ω.rowShift ∧
      bitB D J = ω.oRowHi D (J - 1) - ω.oRowHi D J + ω.rowShift) ∧
    (ω.ordT = 1 → bitA D J = ω.oRowHi D J - ω.oRowHi D (J - 1) - ω.rowShift ∧
      bitB D J = ω.oRowLo D J - ω.oRowLo D (J - 1) - ω.rowShift) := by
  have hcc : ω.case = .a ∨ ω.case = .b := by
    unfold AttachCase.IsMixed at hmix
    cases hh : ω.case <;> simp_all
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  unfold bitA bitB
  rcases hcc with hc | hc
  · simp only [oRowLo, oRowHi, ordT, hc, hp]
    simp only [ite_true, zero_ne_one, false_implies, true_implies, and_true]
    omega
  · simp only [oRowLo, oRowHi, ordT, hc, hp]
    simp only [reduceCtorEq, ite_false, one_ne_zero, false_implies, true_implies, true_and]
    omega

/-- **Fixed-chart injectivity, ordinary marks.**  If `D' ∘_ω E` is a translate of `D ∘_ω E` for a
legal ordinary mark, then `D'` is a translate of `D`: the rows of the composite on the private
diagonals `J q + w` read the origin rows of `D`.  **Differs from the paper's route.**  The paper
reads the private cells `e_∘ + L_ω(D_j)`; here the first and last rows of each private diagonal
of the composite are read, which carries the same information. -/
theorem IsLegalNonempty.injective_ord (h : ω.IsLegalNonempty) (hmix : ¬ ω.case.IsMixed)
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') {t : ℤ × ℤ}
    (hF : ω.compose D' = translate t (ω.compose D)) : ∃ u, D' = translate u D := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hct, hsp⟩ := h.1.shift_data hD hD' hF
  have hcD := ord_classRows h hD hmix
  have key : ∀ J, minContent D ≤ J → J ≤ maxContent D →
      ω.oRowLo D' (J + (minContent D' - minContent D)) = ω.oRowLo D J + t.1 ∧
      ω.oRowHi D' (J + (minContent D' - minContent D)) = ω.oRowHi D J + t.1 := by
    intro J h1 h2
    have r1 := ord_rows_w h hD hmix (J := J) ⟨h1, h2⟩
    have r2 := ord_rows_w h hD' hmix (J := J + (minContent D' - minContent D))
      ⟨by omega, by omega⟩
    have hk : minContent ω.E + (J * ω.period + ω.widthZ) ∈ contents (ω.compose D) :=
      (hcD.mem_contents (by omega) hq).mpr (Or.inl ⟨h1, h2⟩)
    have e : minContent ω.E + ((J + (minContent D' - minContent D)) * ω.period + ω.widthZ) =
        (minContent ω.E + (J * ω.period + ω.widthZ)) + content t := by
      rw [hct]; ring
    have d1 := diagLo_translate t _ hk
    have d2 := diagHi_translate t _ hk
    rw [← hF, ← e] at d1 d2
    rw [r1.1] at d1
    rw [r1.2] at d2
    rw [r2.1] at d1
    rw [r2.2] at d2
    constructor <;> omega
  have ht := ordT_cases hmix
  have hsp1 := span_eq_of_isConnectedSkew hD
  have hsp2 := span_eq_of_isConnectedSkew hD'
  have hbits : ∀ k : ℕ, 1 ≤ k → k < span D →
      bitA D (minContent D + k) = bitA D' (minContent D' + k) ∧
      bitB D (minContent D + k) = bitB D' (minContent D' + k) := by
    intro k hk1 hk2
    have k1 := key (minContent D + k - 1) (by omega) (by omega)
    have k2 := key (minContent D + k) (by omega) (by omega)
    have e1 : minContent D' + (k : ℤ) = (minContent D + k) + (minContent D' - minContent D) := by
      ring
    have e2 : minContent D' + (k : ℤ) - 1 =
        (minContent D + k - 1) + (minContent D' - minContent D) := by ring
    have b1 := bits_ord hmix D (minContent D + k)
    have b2 := bits_ord hmix D' (minContent D' + k)
    rw [e2, e1] at b2
    rw [e1]
    constructor <;> omega
  exact eq_translate_of_bits hD hD' (by omega) (fun k hk1 hk2 => (hbits k hk1 hk2).1)
    (fun k hk1 hk2 => (hbits k hk1 hk2).2) |>.imp fun u hu => hu

/-- The overlap-type quantity `S_J - 1` of the outer: `h_{J-1} - ℓ_J` between two consecutive
diagonals, and `0` at the two ends (`S_0 = S_r = 1`). -/
def sigmaD (D : Diagram) (J : ℤ) : ℤ :=
  if minContent D + 1 ≤ J ∧ J ≤ maxContent D then diagHi D (J - 1) - diagLo D J else 0

theorem mix_rows_w (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {J : ℤ}
    (hJ : minContent D ≤ J ∧ J ≤ maxContent D) :
    diagLo (ω.compose D) (minContent ω.E + (J * ω.period + ω.widthZ)) =
      J * ω.rowShift - (diagHi D J - diagLo D J) + ω.lo ω.widthZ ∧
    diagHi (ω.compose D) (minContent ω.E + (J * ω.period + ω.widthZ)) =
      J * ω.rowShift + ω.hi ω.widthZ := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J ω.widthZ := Or.inl hJ
  have hcr := mix_classRows h hD hc hph hlt
  refine ⟨?_, ?_⟩
  · rw [hcr.diagLo_eq (by omega) hq hv, mixLo_P1 hJ (by omega)]
    simp only [oRowLo, hc]
  · rw [hcr.diagHi_eq (by omega) hq hv]
    rfl

theorem mix_rows_a0 (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {a J : ℤ} (ha0 : 0 ≤ a)
    (haw : a < ω.widthZ) (hdL : ω.dLo a = 0) (hJ : minContent D ≤ J ∧ J ≤ maxContent D + 1) :
    diagLo (ω.compose D) (minContent ω.E + (J * ω.period + a)) =
      J * ω.rowShift + ω.lo a - sigmaD D J ∧
    diagHi (ω.compose D) (minContent ω.E + (J * ω.period + a)) = J * ω.rowShift + ω.hi a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a := by
    unfold ValidClass; omega
  have hcr := mix_classRows h hD hc hph hlt
  have he := D_ends hD
  refine ⟨?_, hcr.diagHi_eq ha0 (by omega) hv⟩
  rw [hcr.diagLo_eq ha0 (by omega) hv]
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  unfold sigmaD
  unfold dLo at hdL
  by_cases hJm : J = minContent D
  · subst hJm
    rw [mixLo_P1 (by omega) (by omega)]
    simp only [oRowLo, hc]
    split_ifs <;> omega
  by_cases hJM : J = maxContent D + 1
  · subst hJM
    rw [mixLo_P2 (by omega)]
    have hp2 : (maxContent D + 1) * ω.rowShift = maxContent D * ω.rowShift + ω.rowShift := by ring
    simp only [oRowLo, hc, add_sub_cancel_right]
    split_ifs <;> omega
  have hJ' : minContent D + 1 ≤ J ∧ J ≤ maxContent D := by omega
  have hb := D_bits hD hJ'.1 hJ'.2
  have hdl := diagLo_le_diagHi (isConnectedSkew_iff_diagonal.mp hD |>.mem_contents_iff.mpr
    ⟨by omega, hJ'.2⟩ : J ∈ contents D)
  have hdl' := diagLo_le_diagHi (isConnectedSkew_iff_diagonal.mp hD |>.mem_contents_iff.mpr
    ⟨by omega, by omega⟩ : J - 1 ∈ contents D)
  by_cases hB : diagHi D (J - 1) - diagHi D J = 1
  · rw [mixLo_all1 (by omega) (by omega) hB]
    simp only [oRowLo, hc, hp]
    simp only [hJ', and_self, ite_true]
    omega
  · rw [mixLo_all0 (by omega) (by omega) hB]
    simp only [oRowLo, hc, hp]
    simp only [hJ', and_self, ite_true]
    omega


/-- **Fixed-chart injectivity, case (d)** (the paragraph after `eq:gluing-mixed-profile`).  The
private residue `w` reads every height `M_j` and a residue meeting neither middle tail reads every
`S_j`; these determine the bits of `D`. -/
theorem IsLegalNonempty.injective_d (h : ω.IsLegalNonempty) (hc : ω.case = .d)
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') {t : ℤ × ℤ}
    (hF : ω.compose D' = translate t (ω.compose D)) : ∃ u, D' = translate u D := by
  obtain ⟨s, t₀, hph⟩ := h.exists_phases
  have hlt := h.phases_lt (Or.inr hc) hph
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hct, hsp⟩ := h.1.shift_data hD hD' hF
  have hcr := mix_classRows h hD hc hph hlt
  have fa := d_E_facts h hc hph (a := s - 1) (by obtain ⟨h1, -⟩ := hph; omega)
    (by obtain ⟨-, h2, -⟩ := hph; omega)
  have hdL : ω.dLo (s - 1) = 0 := by omega
  have ha0 : 0 ≤ s - 1 := by obtain ⟨h1, -⟩ := hph; omega
  have haw : s - 1 < ω.widthZ := by obtain ⟨-, h2, -⟩ := hph; omega
  have key1 : ∀ J, minContent D ≤ J → J ≤ maxContent D →
      (diagHi D' (J + (minContent D' - minContent D)) -
        diagLo D' (J + (minContent D' - minContent D)) = diagHi D J - diagLo D J) ∧
      (minContent D' - minContent D) * ω.rowShift = t.1 := by
    intro J h1 h2
    have r1 := mix_rows_w h hD hc hph hlt (J := J) ⟨h1, h2⟩
    have r2 := mix_rows_w h hD' hc hph hlt (J := J + (minContent D' - minContent D))
      ⟨by omega, by omega⟩
    have hk : minContent ω.E + (J * ω.period + ω.widthZ) ∈ contents (ω.compose D) :=
      (hcr.mem_contents (by omega) hq).mpr (Or.inl ⟨h1, h2⟩)
    have e : minContent ω.E + ((J + (minContent D' - minContent D)) * ω.period + ω.widthZ) =
        (minContent ω.E + (J * ω.period + ω.widthZ)) + content t := by
      rw [hct]; ring
    have d1 := diagLo_translate t _ hk
    have d2 := diagHi_translate t _ hk
    rw [← hF, ← e] at d1 d2
    rw [r1.1, r2.1] at d1
    rw [r1.2, r2.2] at d2
    have hmp : (J + (minContent D' - minContent D)) * ω.rowShift =
        J * ω.rowShift + (minContent D' - minContent D) * ω.rowShift := by ring
    constructor <;> omega
  have key2 : ∀ J, minContent D ≤ J → J ≤ maxContent D + 1 →
      sigmaD D' (J + (minContent D' - minContent D)) = sigmaD D J := by
    intro J h1 h2
    have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
    have r1 := mix_rows_a0 h hD hc hph hlt ha0 haw hdL (J := J) ⟨h1, h2⟩
    have r2 := mix_rows_a0 h hD' hc hph hlt ha0 haw hdL
      (J := J + (minContent D' - minContent D)) ⟨by omega, by omega⟩
    have hk : minContent ω.E + (J * ω.period + (s - 1)) ∈ contents (ω.compose D) :=
      (hcr.mem_contents ha0 (by omega)).mpr (by unfold ValidClass; omega)
    have e : minContent ω.E + ((J + (minContent D' - minContent D)) * ω.period + (s - 1)) =
        (minContent ω.E + (J * ω.period + (s - 1))) + content t := by
      rw [hct]; ring
    have d1 := diagLo_translate t _ hk
    rw [← hF, ← e] at d1
    rw [r1.1, r2.1] at d1
    have hmp : (J + (minContent D' - minContent D)) * ω.rowShift =
        J * ω.rowShift + (minContent D' - minContent D) * ω.rowShift := by ring
    have := (key1 (minContent D) (le_refl _) (by omega)).2
    omega
  have hsp1 := span_eq_of_isConnectedSkew hD
  have hsp2 := span_eq_of_isConnectedSkew hD'
  have hbits : ∀ k : ℕ, 1 ≤ k → k < span D →
      bitA D (minContent D + k) = bitA D' (minContent D' + k) ∧
      bitB D (minContent D + k) = bitB D' (minContent D' + k) := by
    intro k hk1 hk2
    have e1 : minContent D' + (k : ℤ) = (minContent D + k) + (minContent D' - minContent D) := by
      ring
    have e2 : minContent D' + (k : ℤ) - 1 =
        (minContent D + k - 1) + (minContent D' - minContent D) := by ring
    have k1 := (key1 (minContent D + k - 1) (by omega) (by omega)).1
    have k2 := (key1 (minContent D + k) (by omega) (by omega)).1
    have k3 := key2 (minContent D + k) (by omega) (by omega)
    rw [e1]
    unfold sigmaD at k3
    have c1 : minContent D' + 1 ≤ minContent D + k + (minContent D' - minContent D) ∧
        minContent D + k + (minContent D' - minContent D) ≤ maxContent D' := by omega
    have c2 : minContent D + 1 ≤ minContent D + k ∧ minContent D + k ≤ maxContent D := by omega
    simp only [c1, c2, and_self, ite_true] at k3
    have e3 : minContent D + k + (minContent D' - minContent D) - 1 =
        minContent D + k - 1 + (minContent D' - minContent D) := by ring
    rw [e3] at k3
    unfold bitA bitB
    rw [e3]
    constructor <;> omega
  exact eq_translate_of_bits hD hD' (by omega) (fun k hk1 hk2 => (hbits k hk1 hk2).1)
    (fun k hk1 hk2 => (hbits k hk1 hk2).2) |>.imp fun u hu => hu


theorem rotate_translate_diagram (v : ℤ × ℤ) (A : Diagram) :
    SkewMarkedFactor.Gluing.rotate (translate v A) = translate (-v)
      (SkewMarkedFactor.Gluing.rotate A) := by
  ext y
  rw [mem_rotate, mem_translate, mem_translate, mem_rotate]
  have : -y - v = -(y - -v) := by abel
  rw [this]

/-- **Fixed-chart injectivity, case (c)**, by rotation to case (d). -/
theorem IsLegalNonempty.injective_c (h : ω.IsLegalNonempty) (hc : ω.case = .c)
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') {t : ℤ × ℤ}
    (hF : ω.compose D' = translate t (ω.compose D)) : ∃ u, D' = translate u D := by
  have e1 := compose_rotate_c hc hD.2.1
  have e2 := compose_rotate_c hc hD'.2.1
  have hF' : ω.rotate.compose (SkewMarkedFactor.Gluing.rotate D') =
      translate (-t) (ω.rotate.compose (SkewMarkedFactor.Gluing.rotate D)) := by
    have := congrArg SkewMarkedFactor.Gluing.rotate hF
    rw [e2, e1, SkewMarkedFactor.Gluing.rotate_rotate, rotate_translate_diagram,
      SkewMarkedFactor.Gluing.rotate_rotate] at this
    exact this
  obtain ⟨u, hu⟩ := h.rotate.injective_d (rotate_case_d hc) (isConnectedSkew_rotate hD)
    (isConnectedSkew_rotate hD') hF'
  refine ⟨-u, ?_⟩
  have := congrArg SkewMarkedFactor.Gluing.rotate hu
  rw [SkewMarkedFactor.Gluing.rotate_rotate, rotate_translate_diagram,
    SkewMarkedFactor.Gluing.rotate_rotate] at this
  exact this

/-- **Fixed-chart injectivity** for legal marks with a nonempty copy: composition with `ω` is
injective on connected outers, up to translation. -/
theorem IsLegalNonempty.injective_compose (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hD' : IsConnectedSkew D') {t : ℤ × ℤ} (hF : ω.compose D' = translate t (ω.compose D)) :
    ∃ u, D' = translate u D := by
  by_cases hmix : ω.case.IsMixed
  · rcases hmix with hc | hc
    · exact h.injective_c hc hD hD' hF
    · exact h.injective_d hc hD hD' hF
  · exact h.injective_ord hmix hD hD' hF

end MarkedInner

end SkewMarkedFactor.Gluing
