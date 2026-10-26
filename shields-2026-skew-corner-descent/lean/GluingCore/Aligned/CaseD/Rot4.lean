/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Rot4.lean`. -/
import GluingCore.Aligned.CaseD.Rot3

/-!
# Aligned marks, case (d): the nested count for a lower mark of case (c)

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-nested-count`, case (c) "by rotation").

`alD_NC_c` deduces `alD_NC V a θ C` for a lower mark of case (c) from the nested count of its
rotation `alD_NC (rotate V) a θ (rotate C)` (a lower mark of case (d)), by reflecting the profiles.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {V C : Diagram} {a θ : ℤ}

theorem alD_NCc_M (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .c)
    (hN : alD_NC (GluingCore.rotate V) a θ (GluingCore.rotate C)) {J i : ℤ} (h0 : 0 ≤ i)
    (h1 : i < (span V : ℤ) - a)
    (hv : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i) :
    profM ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      alD_Om V a θ i + alD_CT C (walkDelta V a (2 * (minContent V + i) + 1)) J := by
  have hb := hD.hb
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hCne := hC.2.1
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hCne)
  obtain ⟨hY, hX⟩ := alD_NCc_setup hV hD hC hc
  unfold alD_NC at hN
  simp only [alD_span_rotate (V := V)] at hN
  rw [hX, alD_profM_rotate hY]
  have hval : ValidClass (minContent (GluingCore.rotate C)) (maxContent (GluingCore.rotate C))
      ((span V : ℤ) - a) (1 - J) ((span V : ℤ) - a - 1 - i) := by
    unfold ValidClass at hv ⊢
    rw [minContent_rotate hCne, maxContent_rotate hCne]
    rcases hv with h | ⟨h, h2⟩
    · by_cases hJ : minContent C + 1 ≤ J
      · left; omega
      · right; omega
    · left; omega
  have hidx : -(minContent V + (J * a + i)) = minContent (GluingCore.rotate V) +
      ((1 - J) * a + ((span V : ℤ) - a - 1 - i)) := by
    rw [alD_minContent_rotate hV]; ring
  rw [hidx, hN.1 (1 - J) ((span V : ℤ) - a - 1 - i) (by omega) (by omega) hval,
    alD_Om_rotate hV hD h0 h1]
  have hw : walkDelta (GluingCore.rotate V) a
      (2 * (minContent (GluingCore.rotate V) + ((span V : ℤ) - a - 1 - i)) + 1) =
      - walkDelta V a (2 * (minContent V + i) + 1) := by
    rw [alD_walk_rotate hV]
    have : 2 - (2 * (minContent (GluingCore.rotate V) + ((span V : ℤ) - a - 1 - i)) + 1) -
        2 * a = 2 * (minContent V + i) + 1 := by
      rw [alD_minContent_rotate hV]; ring
    rw [this]
  rw [hw]
  have he := hD.e_bd i h0 h1
  have hwo := alD_walk_odd_eq hV h0 hap.le (by omega)
  rw [alD_CT_rotate hC (by rw [hwo]; exact he)]

theorem alD_NCc_P (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .c)
    (hN : alD_NC (GluingCore.rotate V) a θ (GluingCore.rotate C)) {J i : ℤ}
    (h0 : (span V : ℤ) - a ≤ i) (h1 : i < a) (hJ1 : minContent C ≤ J) (hJ2 : J ≤ maxContent C) :
    profM ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profM V (minContent V + i) + profM C J - 1 := by
  have hb := hD.hb
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hCne := hC.2.1
  obtain ⟨hY, hX⟩ := alD_NCc_setup hV hD hC hc
  unfold alD_NC at hN
  simp only [alD_span_rotate (V := V)] at hN
  rw [hX, alD_profM_rotate hY]
  have hidx : -(minContent V + (J * a + i)) = minContent (GluingCore.rotate V) +
      ((-J) * a + (a + ((span V : ℤ) - a) - 1 - i)) := by
    rw [alD_minContent_rotate hV]; ring
  rw [hidx, hN.2.1 (-J) (a + ((span V : ℤ) - a) - 1 - i) (by omega) (by omega) (by
    rw [minContent_rotate hCne]; omega) (by rw [maxContent_rotate hCne]; omega)]
  have e1 : minContent (GluingCore.rotate V) + (a + ((span V : ℤ) - a) - 1 - i) =
      -(minContent V + i) := by
    rw [alD_minContent_rotate hV]; ring
  rw [e1, alD_profM_rotate hV, alD_profM_rotate hC, neg_neg, neg_neg]

theorem alD_NCc_S (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .c)
    (hN : alD_NC (GluingCore.rotate V) a θ (GluingCore.rotate C)) {J i : ℤ} (h0 : 0 ≤ i)
    (h1 : i ≤ (span V : ℤ) - a)
    (hv : (minContent C ≤ J ∧ J ≤ maxContent C) ∨ J = maxContent C + 1) :
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profS V (minContent V + i) -
        (if walkDelta V a (2 * (minContent V + i)) = 1 then 1 else 0) +
        alD_CT C (walkDelta V a (2 * (minContent V + i))) J := by
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hCne := hC.2.1
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hCne)
  obtain ⟨hY, hX⟩ := alD_NCc_setup hV hD hC hc
  unfold alD_NC at hN
  simp only [alD_span_rotate (V := V)] at hN
  rw [hX, alD_profS_rotate hY]
  have hval : ((minContent (GluingCore.rotate C) ≤ 1 - J ∧ 1 - J ≤ maxContent (GluingCore.rotate C))
      ∨ 1 - J = maxContent (GluingCore.rotate C) + 1) := by
    rw [minContent_rotate hCne, maxContent_rotate hCne]
    rcases hv with h | h
    · by_cases hJ : minContent C + 1 ≤ J
      · left; omega
      · right; omega
    · left; omega
  have hidx : 1 - (minContent V + (J * a + i)) = minContent (GluingCore.rotate V) +
      ((1 - J) * a + ((span V : ℤ) - a - i)) := by
    rw [alD_minContent_rotate hV]; ring
  rw [hidx, hN.2.2.1 (1 - J) ((span V : ℤ) - a - i) (by omega) (by omega) hval]
  have hS : profS (GluingCore.rotate V) (minContent (GluingCore.rotate V) +
      ((span V : ℤ) - a - i)) = profS V (minContent V + i + a) := by
    rw [alD_profS_rotate hV]
    congr 1
    rw [alD_minContent_rotate hV]; ring
  have hw : walkDelta (GluingCore.rotate V) a
      (2 * (minContent (GluingCore.rotate V) + ((span V : ℤ) - a - i))) =
      - walkDelta V a (2 * (minContent V + i)) := by
    rw [alD_walk_rotate hV]
    have : 2 - 2 * (minContent (GluingCore.rotate V) + ((span V : ℤ) - a - i)) - 2 * a =
        2 * (minContent V + i) := by
      rw [alD_minContent_rotate hV]; ring
    rw [this]
  rw [hS, hw]
  have hd := alD_d_bounds hV hD h0 h1
  rw [alD_CT_rotate hC hd]
  have hdd := alD_walk_even_eq (V := V) (a := a) (j := i)
  rw [hdd] at hd ⊢
  split_ifs <;> omega

theorem alD_NCc_SP (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .c)
    (hN : alD_NC (GluingCore.rotate V) a θ (GluingCore.rotate C)) {J i : ℤ}
    (h0 : (span V : ℤ) - a < i) (h1 : i < a) (hJ1 : minContent C ≤ J) (hJ2 : J ≤ maxContent C) :
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profS V (minContent V + i) + profM C J - 1 := by
  have hb := hD.hb
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hCne := hC.2.1
  obtain ⟨hY, hX⟩ := alD_NCc_setup hV hD hC hc
  unfold alD_NC at hN
  simp only [alD_span_rotate (V := V)] at hN
  rw [hX, alD_profS_rotate hY]
  have hidx : 1 - (minContent V + (J * a + i)) = minContent (GluingCore.rotate V) +
      ((-J) * a + (a + ((span V : ℤ) - a) - i)) := by
    rw [alD_minContent_rotate hV]; ring
  rw [hidx, hN.2.2.2 (-J) (a + ((span V : ℤ) - a) - i) (by omega) (by omega) (by
    rw [minContent_rotate hCne]; omega) (by rw [maxContent_rotate hCne]; omega)]
  have e1 : minContent (GluingCore.rotate V) + (a + ((span V : ℤ) - a) - i) =
      1 - (minContent V + i) := by
    rw [alD_minContent_rotate hV]; ring
  rw [e1, alD_profS_rotate hV, alD_profM_rotate hC, neg_neg]
  have : 1 - (1 - (minContent V + i)) = minContent V + i := by ring
  rw [this]

/-- **`eq:gluing-nested-count`** for a lower mark of case (c), from the case (d) of its rotation. -/
theorem alD_NC_c (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .c)
    (hN : alD_NC (GluingCore.rotate V) a θ (GluingCore.rotate C)) : alD_NC V a θ C :=
  ⟨fun _J _i h0 h1 hv => alD_NCc_M hV hD hC hc hN h0 h1 hv,
    fun _J _i h0 h1 hJ1 hJ2 => alD_NCc_P hV hD hC hc hN h0 h1 hJ1 hJ2,
    fun _J _i h0 h1 hv => alD_NCc_S hV hD hC hc hN h0 h1 hv,
    fun _J _i h0 h1 hJ1 hJ2 => alD_NCc_SP hV hD hC hc hN h0 h1 hJ1 hJ2⟩

end MarkedInner

end GluingCore
