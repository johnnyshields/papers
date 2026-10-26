import SkewGluing.SmallOverlap.SingletonEnds

/-!
# The outer bits in the boundary words of a width-one composite

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-ordinary-endpoints`, `eq:gluing-interface`), at width one.

For a legal mark `ω` of width one (phases `s = 1`, `t = 0`) and a connected outer `D`, the
boundary words of `D ∘_ω E` at the positions `j q` and `j q + 1` read the outer bits:

* case (a): `A_{jq} = A^D_j` and `B_{jq+1} = B^D_j` (`ordinary_hole_a`);
* case (b): `A_{jq+1} = 1 - B^D_j` and `B_{jq} = 1 - A^D_j` (`ordinary_hole_b`);

for `1 ≤ j < N_D`, together with the values `A_{jq}`, `B_{jq}` at the other residue zero:
`B_{jq} = 0` in case (a) and `A_{jq} = 1` in case (b) (`ordinary_zero_a`, `ordinary_zero_b`).
Case (d) is `interface_d` of `lem:gluing-coding`.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem IsLegalNonempty.lo_period_eq (h : ω.IsLegalNonempty) (hw : ω.widthZ = 1) :
    ω.lo ω.period = ω.lo 0 + ω.rowShift ∧ ω.hi ω.period = ω.hi 0 + ω.rowShift := by
  have hs1 := h.sw_cell
  have hn := h.ne_cell_W
  rw [hw] at hn
  have hq := h.width_lt_period
  have hpos : ω.period + 1 - 1 = ω.period := by ring
  rw [hpos] at hn
  have e : (1 : ℤ) - 1 = 0 := by norm_num
  rw [e] at hn
  have hm1 := h.mem_W.mp hs1
  have hm2 := h.mem_W.mp hn
  have hwd : ω.lo 0 ≤ ω.hi 0 := h.lo_le_hi (by omega) (by omega)
  have hsing := h.lo_zero
  have hup := h.lo_last
  rw [hw] at hup
  rw [hpos] at hup
  have hlast : ω.lo ω.period = ω.hi ω.period := by
    have e2 : ω.period + 1 - 1 = ω.period := hpos
    simpa [hw, e2] using hup
  -- the singleton lower copy has one cell on the diagonal `0`
  have hhi0 : ω.hi 0 = ω.lo 0 := hsing.symm
  have hm1' := hm1
  have hm2' := hm2
  obtain ⟨-, -, a1, a2, a3, a4⟩ := hm1'
  obtain ⟨-, -, b1, b2, b3, b4⟩ := hm2'
  constructor <;> omega

/-- For a width-one mark the phases are `s = 1`, `t = 0`. -/
theorem IsLegalNonempty.isPhases_one (h : ω.IsLegalNonempty) (hw : ω.widthZ = 1) :
    ω.IsPhases 1 0 := by
  obtain ⟨s, t, hph⟩ := h.exists_phases
  obtain ⟨rfl, rfl⟩ := SmallOverlap.phases_one hph hw
  exact hph

/-- **Case (a), width one: the class steps of the composite at the holes.**  For
`1 ≤ J - m ≤ N_D - 1` (`J = m + j`) the step of the first rows at the position `j q` and that of
the last rows at the position `j q + 1`. -/
theorem IsLegalNonempty.ordinary_hole_a (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hca : ω.case = .a) (hw : ω.widthZ = 1) {J : ℤ} (hJ1 : minContent D + 1 ≤ J)
    (hJ2 : J ≤ maxContent D) :
    classBitLo ω.period (ω.ordLo D) J 0 =
      (ω.lo (ω.period - 1) - ω.lo ω.period) + (diagLo D (J - 1) - diagLo D J) ∧
    classBitHi ω.period (ω.ordHi D) J 1 =
      (ω.hi 0 - ω.hi 1) + (diagHi D (J - 1) - diagHi D J) ∧
    classBitHi ω.period (ω.ordHi D) J 0 = 0 := by
  have hq := h.width_lt_period
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hph := h.isPhases_one hw
  have hz := (ordT_eq_zero_iff hmix).mpr hca
  obtain ⟨hl1, hl2⟩ := h.lo_period_eq hw
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  have v1 : ValidClass (minContent D) (maxContent D) ω.widthZ J 0 := Or.inl ⟨by omega, hJ2⟩
  have v1' : ValidClass (minContent D) (maxContent D) ω.widthZ (J - 1) (ω.period - 1) :=
    Or.inl ⟨by omega, by omega⟩
  have v2 : ValidClass (minContent D) (maxContent D) ω.widthZ J 1 := Or.inl ⟨by omega, hJ2⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold classBitLo
    simp only [ite_true]
    rw [ordLo_formula h hD hmix hph (by omega) v1', ordLo_formula h hD hmix hph (le_refl _) v1]
    unfold ordGLo
    simp only [hz, ite_true]
    split_ifs <;> omega
  · unfold classBitHi
    simp only [show (1 : ℤ) ≠ 0 by omega, ite_false]
    rw [ordHi_formula h hD hmix hph (by omega) (validClass_pred v2),
      ordHi_formula h hD hmix hph (by omega) v2]
    unfold ordGHi
    simp only [hz, ite_true, sub_self]
    split_ifs <;> omega
  · unfold classBitHi
    simp only [ite_true]
    rw [ordHi_formula h hD hmix hph (by omega) v1', ordHi_formula h hD hmix hph (le_refl _) v1]
    unfold ordGHi
    simp only [hz, ite_true]
    have hc1 := ((ord_E_facts h hmix).2.1 hz).2
    unfold dLo dHi at hc1
    simp only [zero_add] at hc1
    split_ifs <;> omega

/-- **Case (b), width one: the class steps of the composite at the holes.** -/
theorem IsLegalNonempty.ordinary_hole_b (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcb : ω.case = .b) (hw : ω.widthZ = 1) {J : ℤ} (hJ1 : minContent D + 1 ≤ J)
    (hJ2 : J ≤ maxContent D) :
    classBitLo ω.period (ω.ordLo D) J 1 =
      (ω.lo 0 - ω.lo 1) - (diagHi D (J - 1) - diagHi D J) ∧
    classBitHi ω.period (ω.ordHi D) J 0 =
      (ω.hi (ω.period - 1) - ω.hi ω.period) - (diagLo D (J - 1) - diagLo D J) ∧
    classBitLo ω.period (ω.ordLo D) J 0 = 1 := by
  have hq := h.width_lt_period
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hcb]
  have hph := h.isPhases_one hw
  have hz : ω.ordT = 1 := by simp [ordT, hcb]
  obtain ⟨hl1, hl2⟩ := h.lo_period_eq hw
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  have v1 : ValidClass (minContent D) (maxContent D) ω.widthZ J 0 := Or.inl ⟨by omega, hJ2⟩
  have v1' : ValidClass (minContent D) (maxContent D) ω.widthZ (J - 1) (ω.period - 1) :=
    Or.inl ⟨by omega, by omega⟩
  have v2 : ValidClass (minContent D) (maxContent D) ω.widthZ J 1 := Or.inl ⟨by omega, hJ2⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold classBitLo
    simp only [show (1 : ℤ) ≠ 0 by omega, ite_false]
    rw [ordLo_formula h hD hmix hph (by omega) (validClass_pred v2),
      ordLo_formula h hD hmix hph (by omega) v2]
    unfold ordGLo
    simp only [hz, one_ne_zero, ite_false, sub_self]
    split_ifs <;> omega
  · unfold classBitHi
    simp only [ite_true]
    rw [ordHi_formula h hD hmix hph (by omega) v1', ordHi_formula h hD hmix hph (le_refl _) v1]
    unfold ordGHi
    simp only [hz, one_ne_zero, ite_false]
    split_ifs <;> omega
  · have := ord_classBitLo h hD hmix hph (J := J) (a := 0) (le_refl _) (by omega) v1
      (fun _ => hJ1) ⟨fun h0 => by omega, fun _ => by omega⟩
    simpa using this

/-- The words of `D ∘_ω E` read at a position of the class `(m + j, a)`, for width one. -/
theorem IsLegalNonempty.ordinary_word_hole_a (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hca : ω.case = .a) (hw : ω.widthZ = 1) {j : ℤ} (hj1 : 1 ≤ j) (hj2 : j < span D) :
    wordA (ω.compose D) (j * ω.period) =
      (ω.lo (ω.period - 1) - ω.lo ω.period) + wordA D j ∧
    wordB (ω.compose D) (j * ω.period + 1) = (ω.hi 0 - ω.hi 1) + wordB D j ∧
    wordB (ω.compose D) (j * ω.period) = 0 := by
  have hq := h.width_lt_period
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hsp := span_eq_of_isConnectedSkew hD
  have hmin := h.minContent_compose' hD
  have hc := ord_classRows h hD hmix
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  obtain ⟨c1, c2, c3⟩ := h.ordinary_hole_a hD hca hw (J := minContent D + j) (by omega) (by omega)
  have v0 : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + j) 0 :=
    Or.inl ⟨by omega, by omega⟩
  have v1 : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + j) 1 :=
    Or.inl ⟨by omega, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.wordA_class' hmin (J := minContent D + j) (a := 0) (by ring) (le_refl _) (by omega)
      v0 (fun _ => by omega), c1]
    unfold wordA bitA
    simp only []
  · rw [hc.wordB_class' hmin (J := minContent D + j) (a := 1) (by ring) (by omega) (by omega)
      v1 (fun _ => by omega), c2]
    unfold wordB bitB
    simp only []
  · rw [hc.wordB_class' hmin (J := minContent D + j) (a := 0) (by ring) (le_refl _) (by omega)
      v0 (fun _ => by omega), c3]

theorem IsLegalNonempty.ordinary_word_hole_b (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcb : ω.case = .b) (hw : ω.widthZ = 1) {j : ℤ} (hj1 : 1 ≤ j) (hj2 : j < span D) :
    wordA (ω.compose D) (j * ω.period + 1) = (ω.lo 0 - ω.lo 1) - wordB D j ∧
    wordB (ω.compose D) (j * ω.period) =
      (ω.hi (ω.period - 1) - ω.hi ω.period) - wordA D j ∧
    wordA (ω.compose D) (j * ω.period) = 1 := by
  have hq := h.width_lt_period
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hcb]
  have hsp := span_eq_of_isConnectedSkew hD
  have hmin := h.minContent_compose' hD
  have hc := ord_classRows h hD hmix
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  obtain ⟨c1, c2, c3⟩ := h.ordinary_hole_b hD hcb hw (J := minContent D + j) (by omega) (by omega)
  have v0 : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + j) 0 :=
    Or.inl ⟨by omega, by omega⟩
  have v1 : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + j) 1 :=
    Or.inl ⟨by omega, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.wordA_class' hmin (J := minContent D + j) (a := 1) (by ring) (by omega) (by omega)
      v1 (fun _ => by omega), c1]
    unfold wordB bitB
    simp only []
  · rw [hc.wordB_class' hmin (J := minContent D + j) (a := 0) (by ring) (le_refl _) (by omega)
      v0 (fun _ => by omega), c2]
    unfold wordA bitA
    simp only []
  · rw [hc.wordA_class' hmin (J := minContent D + j) (a := 0) (by ring) (le_refl _) (by omega)
      v0 (fun _ => by omega), c3]

end MarkedInner

end SkewGluing
