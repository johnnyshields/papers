/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.TwoSidedWeighted
import SkewMarkedFactor.AllTypeNormalization
import SkewMarkedFactor.MixedCovariance
import SkewMarkedFactor.RibbonDeletion
import SkewMarkedFactor.OrdinaryAction
import SkewMarkedFactor.WeightedHomogeneity

/-!
# Ordinary weighted and Hall covariance of the composition map

«Composition covariance» (`lem:covariance`, `eq:ordinary-covariance`) of
`shields-2026-skew-marked-factor.tex` for a legal ordinary mark.
On a row composite the only ribbons of `k p` cells removable on the left and on the right are the
lifts of the first and the last `k` cells of the row; the weighted Murnaghan–Nakayama rule then
gives `V_{kp} s_{F_m} = ((m - k) p + θ) δ_{kp} s_{F_m}` with `θ = p - N_O` for case (a).
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan Gluing.Plan.MN MvPolynomial

/-! ### Ribbons of a row -/

theorem rightRibbons_rowCells {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    rightRibbons (rowCells 0 (m : ℤ)) k = {rowCells ((m : ℤ) - k) m} := by
  ext Y
  rw [Finset.mem_singleton, mem_rightRibbons]
  constructor
  · rintro ⟨hsub, hcard, -, hup⟩
    have hsub' : Y ⊆ rowCells ((m : ℤ) - k) m := by
      rintro ⟨a, b⟩ hy
      have hy' := mem_rowCells.mp (hsub hy)
      obtain ⟨rfl, hb0, hbm⟩ := hy'
      have hcov : rowCells b m ⊆ Y := by
        rintro ⟨a', b'⟩ hx
        obtain ⟨rfl, h1, h2⟩ := mem_rowCells.mp hx
        exact hup.2 _ (hsub hy |> fun _ => mem_rowCells.mpr ⟨rfl, by omega, h2⟩) _ hy
          (by simp) (by simpa using h1)
      have := Finset.card_le_card hcov
      have hc : (rowCells b (m : ℤ)).card = m - b.toNat := by
        unfold rowCells
        rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Int.card_Ico]
        omega
      rw [hc, hcard] at this
      rw [mem_rowCells]
      refine ⟨rfl, ?_, hbm⟩
      omega
    have hc' : (rowCells ((m : ℤ) - k) m).card = k := by
      unfold rowCells
      rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Int.card_Ico]
      omega
    exact Finset.eq_of_subset_of_card_le hsub' (by rw [hc', hcard])
  · rintro rfl
    have hc' : (rowCells ((m : ℤ) - k) m).card = k := by
      unfold rowCells
      rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Int.card_Ico]
      omega
    refine ⟨?_, hc', ⟨isConnectedSkew_rowCells (by omega), ?_⟩, ?_, ?_⟩
    · rintro ⟨a, b⟩ hx
      obtain ⟨rfl, h1, h2⟩ := mem_rowCells.mp hx
      exact mem_rowCells.mpr ⟨rfl, by omega, h2⟩
    · rw [hc', span_rowCells]; omega
    · rintro ⟨a, b⟩ hx
      obtain ⟨rfl, h1, h2⟩ := mem_rowCells.mp hx
      exact mem_rowCells.mpr ⟨rfl, by omega, h2⟩
    · rintro ⟨a, b⟩ hx ⟨a', b'⟩ hy h1 h2
      obtain ⟨rfl, hy1, hy2⟩ := mem_rowCells.mp hy
      obtain ⟨hx0, hx1, hx2⟩ := mem_rowCells.mp hx
      simp only at h1 h2 hx0
      exact mem_rowCells.mpr ⟨hx0, by omega, hx2⟩

theorem rightRibbons_rowCells_of_lt {m k : ℕ} (hmk : m < k) :
    rightRibbons (rowCells 0 (m : ℤ)) k = ∅ := by
  apply right_ribbons_empty_of_span_lt
  rw [span_rowCells]; omega

theorem leftRibbons_rowCells {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    leftRibbons (rowCells 0 (m : ℤ)) k = {rowCells 0 k} := by
  ext Y
  rw [Finset.mem_singleton, mem_leftRibbons]
  have hc' : (rowCells 0 (k : ℤ)).card = k := card_rowCells k
  constructor
  · rintro ⟨hsub, hcard, -, hdn⟩
    have hsub' : Y ⊆ rowCells 0 k := by
      rintro ⟨a, b⟩ hy
      obtain ⟨rfl, hb0, hbm⟩ := mem_rowCells.mp (hsub hy)
      have hcov : rowCells 0 (b + 1) ⊆ Y := by
        rintro ⟨a', b'⟩ hx
        obtain ⟨rfl, h1, h2⟩ := mem_rowCells.mp hx
        exact hdn.2 _ (mem_rowCells.mpr ⟨rfl, h1, by omega⟩) _ hy (by simp) (by simp; omega)
      have := Finset.card_le_card hcov
      have hc : (rowCells 0 (b + 1)).card = (b + 1).toNat := by
        unfold rowCells
        rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Int.card_Ico]
        simp
      rw [hc, hcard] at this
      rw [mem_rowCells]
      exact ⟨rfl, hb0, by omega⟩
    exact Finset.eq_of_subset_of_card_le hsub' (by rw [hc', hcard])
  · rintro rfl
    refine ⟨?_, hc', ⟨isConnectedSkew_rowCells (by omega), ?_⟩, ?_⟩
    · rintro ⟨a, b⟩ hx
      obtain ⟨rfl, h1, h2⟩ := mem_rowCells.mp hx
      exact mem_rowCells.mpr ⟨rfl, h1, by omega⟩
    · rw [hc', span_rowCells]; omega
    · refine ⟨?_, ?_⟩
      · rintro ⟨a, b⟩ hx
        obtain ⟨rfl, h1, h2⟩ := mem_rowCells.mp hx
        exact mem_rowCells.mpr ⟨rfl, h1, by omega⟩
      · rintro ⟨a, b⟩ hx ⟨a', b'⟩ hy h1 h2
        obtain ⟨rfl, hy1, hy2⟩ := mem_rowCells.mp hy
        obtain ⟨hx0, hx1, hx2⟩ := mem_rowCells.mp hx
        simp only at h1 h2 hx0
        exact mem_rowCells.mpr ⟨hx0, hx1, by omega⟩


/-! ### Minimum contents of the two removable ribbons of a row composite -/

theorem maxContent_segment (X : Diagram) (c0 : ℤ) {n : ℕ} (hn : 0 < n) :
    maxContent (segment X c0 n) = c0 + n - 1 := by
  apply maxContent_eq_of
  · rw [contents_segment]; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro k hk
    rw [contents_segment, Finset.mem_Ico] at hk
    omega

/-- The border model of the composite of a connected outer, with the position of the key ribbon
read off the middle. -/
theorem exists_model_mid {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .a) {C : Diagram}
    (hC : IsConnectedSkew C) :
    ∃ t : ℤ, ∃ fLo fHi : ℤ → ℤ → ℤ,
      EdgeRibbon.BorderModel (ω.compose C) (minContent ω.E) ω.period ω.widthZ t (minContent C)
        (maxContent C) ω.rowShift (diagLo C) ω.lo fLo fHi ∧
      keyRibbon ω = segment ω.E (minContent ω.E + t) ω.period.toNat ∧
      maxContent ω.middle = minContent ω.E + ω.period + t - 1 := by
  have hq := hω.period_pos
  have hsp := span_eq_of_isConnectedSkew hω.1.1
  have hwf := hω.1.span_eq
  have hmodel : ∃ t : ℤ, ∃ fLo fHi : ℤ → ℤ → ℤ,
      EdgeRibbon.BorderModel (ω.compose C) (minContent ω.E) ω.period ω.widthZ t (minContent C)
        (maxContent C) ω.rowShift (diagLo C) ω.lo fLo fHi ∧
      maxContent ω.middle = minContent ω.E + ω.period + t - 1 := by
    by_cases hW : ω.W = ∅
    · exact EdgeRibbon.borderModel_empty ⟨hω, hW⟩ hC
    · exact EdgeRibbon.borderModel_nonempty ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩ hc hC
  obtain ⟨t, fLo, fHi, hM, hmax⟩ := hmodel
  refine ⟨t, fLo, fHi, hM, EdgeRibbon.keyRibbon_eq_segment hω.1.1 hmax hM.t0 hq ?_, hmax⟩
  have hw : ω.widthZ = (ω.width : ℤ) := rfl
  have := hM.t0
  rcases hM.tw with h1 | ⟨h1, h2⟩ <;> omega

theorem rowCells_eq_segment {m k : ℕ} (hkm : k ≤ m) :
    rowCells 0 (k : ℤ) = segment (rowCells 0 (m : ℤ)) 0 k := by
  ext ⟨a, b⟩
  rw [mem_rowCells, mem_segment]
  constructor
  · rintro ⟨rfl, h1, h2⟩
    refine ⟨b, h1, by omega, ?_⟩
    rw [diagLo_rowCells h1 (by omega)]
    simp
  · rintro ⟨c, h1, h2, he⟩
    have hd : diagLo (rowCells 0 (m : ℤ)) c = 0 := diagLo_rowCells h1 (by omega)
    rw [hd] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [zero_add] at *
    exact ⟨trivial, h1, by omega⟩

theorem rotate_rowCells_eq_segment {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    rotate (rowCells ((m : ℤ) - k) (m : ℤ)) =
      segment (rotate (rowCells 0 (m : ℤ))) (-((m : ℤ) - 1)) k := by
  ext ⟨a, b⟩
  rw [mem_rotate, mem_segment]
  constructor
  · intro h
    obtain ⟨h0, h1, h2⟩ := mem_rowCells.mp h
    simp only [Prod.fst_neg, Prod.snd_neg] at h0 h1 h2
    refine ⟨b, by omega, by omega, ?_⟩
    have hd : diagLo (rotate (rowCells 0 (m : ℤ))) b = 0 := by
      have := diagLo_rotate (D := rowCells 0 (m : ℤ)) (-b)
      rw [neg_neg] at this
      rw [this, rowCells_diagHi (by omega) (by omega)]
      simp
    rw [hd]
    ext
    · simp; omega
    · simp
  · rintro ⟨c, h1, h2, he⟩
    have hd : diagLo (rotate (rowCells 0 (m : ℤ))) c = 0 := by
      have := diagLo_rotate (D := rowCells 0 (m : ℤ)) (-c)
      rw [neg_neg] at this
      rw [this, rowCells_diagHi (by omega) (by omega)]
      simp
    rw [hd] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact mem_rowCells.mpr ⟨by simp, by simp; omega, by simp; omega⟩

/-- The position shift of the middle: `θ = min(middle) + p - 1 - max(middle)`. -/
def ordTheta (η : MarkedInner) : ℤ :=
  minContent η.middle + η.period - 1 - maxContent η.middle


theorem middle_nonempty {η : MarkedInner} (hη : η.IsLegal) : η.middle.Nonempty := by
  by_cases hW : η.W = ∅
  · have hmid : η.middle = η.E := by simp [Gluing.MarkedInner.middle, Gluing.MarkedInner.upper, hW,
      Gluing.translate]
    rw [hmid]
    exact hη.1.1.2.1
  · have h : η.IsLegalNonempty := ⟨hη, Finset.nonempty_iff_ne_empty.mpr hW⟩
    obtain ⟨s, t, hph⟩ := h.exists_phases
    have hc := h.contents_middle hph
    have hq := h.width_lt_period
    obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
    have : (contents η.middle).Nonempty := by
      rw [hc]
      exact ⟨minContent η.E + s, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    exact Finset.image_nonempty.mp this

theorem ordTheta_eq_zero_empty {η : MarkedInner} (h : η.IsLegalEmpty) : ordTheta η = 0 := by
  have hmid : η.middle = η.E := by simp [Gluing.MarkedInner.middle, Gluing.MarkedInner.upper, h.2,
      Gluing.translate]
  have hsp := span_eq_of_isConnectedSkew h.1.1.1
  have h2 := h.span_eq
  unfold ordTheta
  rw [hmid]
  omega

theorem ordTheta_eq_phases {η : MarkedInner} (h : η.IsLegalNonempty) {s t : ℤ}
    (hph : η.IsPhases s t) : ordTheta η = s - t := by
  have hc := h.contents_middle hph
  have hmn := middle_nonempty h.1
  have hq := h.width_lt_period
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmin : minContent η.middle = minContent η.E + s := by
    apply minContent_eq_of
    · rw [hc]; exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    · intro k hk; rw [hc, Finset.mem_Icc] at hk; exact hk.1
  have hmax : maxContent η.middle = minContent η.E + η.period + t - 1 := by
    apply maxContent_eq_of
    · rw [hc]; exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    · intro k hk; rw [hc, Finset.mem_Icc] at hk; exact hk.2
  unfold ordTheta
  omega

/-- Minimum content of the northwest ribbon removed from a row composite. -/
theorem minContent_liftRibbon_row {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a) {m k : ℕ}
    (hk : 1 ≤ k) (hkm : k ≤ m) :
    minContent (liftRibbon η (rowCells 0 (m : ℤ)) (rowCells 0 (k : ℤ))) =
      maxContent η.middle - η.period + 1 := by
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hpp := hη.period_pos
  obtain ⟨t, fLo, fHi, hM, hkey, hmax⟩ := exists_model_mid hη hc hD
  have hpn : 0 < k * η.period.toNat := Nat.mul_pos hk (by omega)
  rw [rowCells_eq_segment hkm, EdgeRibbon.liftRibbon_segment hc hM hkey
    (by rw [minContent_rowCells (by omega)]) (by rw [maxContent_rowCells (by omega)]; omega),
    minContent_segment _ _ hpn]
  omega

/-- Minimum content of the southeast ribbon removed from a row composite. -/
theorem minContent_bottomLift_row {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a) {m k : ℕ}
    (hk : 1 ≤ k) (hkm : k ≤ m) :
    minContent (bottomLift η (rowCells 0 (m : ℤ)) (rowCells ((m : ℤ) - k) m)) =
      minContent η.middle + ((m : ℤ) - k) * η.period := by
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hD' : IsConnectedSkew (rotate (rowCells 0 (m : ℤ))) := isConnectedSkew_rotate hD
  have hη' : η.rotate.IsLegal := Gluing.MarkedInner.isLegal_rotate hη
  have hc' : η.rotate.case = .a := by simp [Gluing.MarkedInner.rotate, hc, AttachCase.rotate]
  have hpp := hη.period_pos
  have hpp' : η.rotate.period = η.period := rfl
  obtain ⟨t, fLo, fHi, hM, hkey, hmax⟩ := exists_model_mid hη' hc' hD'
  have hmn := middle_nonempty hη
  have hmid : η.rotate.middle = rotate η.middle := Gluing.MarkedInner.middle_rotate η
  have hmaxr : maxContent η.rotate.middle = -minContent η.middle := by
    rw [hmid, maxContent_rotate hmn]
  have hDne : (rowCells 0 (m : ℤ)).Nonempty := hD.2.1
  have hminD' : minContent (rotate (rowCells 0 (m : ℤ))) = -((m : ℤ) - 1) := by
    rw [minContent_rotate hDne, maxContent_rowCells (by omega)]
  have hmaxD' : maxContent (rotate (rowCells 0 (m : ℤ))) = 0 := by
    rw [maxContent_rotate hDne, minContent_rowCells (by omega)]; simp
  have hpn : 0 < k * η.rotate.period.toNat := Nat.mul_pos hk (by omega)
  have hl1 := EdgeRibbon.liftRibbon_segment hc' hM hkey (j₀ := -((m : ℤ) - 1)) (n := k)
    (by rw [hminD']) (by rw [hmaxD']; omega)
  rw [← rotate_rowCells_eq_segment hk hkm] at hl1
  unfold bottomLift
  rw [hl1]
  have hseg : (segment (η.rotate.compose (rotate (rowCells 0 (m : ℤ))))
      (minContent η.rotate.E + t + -((m : ℤ) - 1) * η.rotate.period)
      (k * η.rotate.period.toNat)).Nonempty :=
    Finset.card_pos.mp (by rw [card_segment]; exact hpn)
  rw [minContent_rotate hseg, maxContent_segment _ _ hpn]
  have hpz : ((η.rotate.period.toNat : ℕ) : ℤ) = η.period := Int.toNat_of_nonneg hpp.le
  have hk' : ((k * η.rotate.period.toNat : ℕ) : ℤ) = k * η.period := by push_cast; rw [hpz]
  rw [hk']
  rw [hmaxr] at hmax
  have e : -(minContent η.rotate.E + t + -((m : ℤ) - 1) * η.rotate.period + k * η.period - 1) =
      minContent η.middle + ((m : ℤ) - k) * η.period := by
    have : η.rotate.period = η.period := hpp'
    rw [this]
    nlinarith
  exact e


theorem weighted_aux (P FR FL sR sL : Lambda) (cR cL : ℤ) (hP : P = sR * FR) (hP' : P = sL * FL) :
    sR * (cR : Lambda) * FR - sL * (cL : Lambda) * FL = ((cR - cL : ℤ) : Lambda) * P := by
  push_cast
  linear_combination (-(cR : Lambda)) * hP + (cL : Lambda) * hP'

/-- **Weighted derivative of a case-(a) row composite**: `V_{kp} s_{F_m} = ((m - k) p + θ) δ_{kp}
s_{F_m}` for `1 ≤ k ≤ m`, with `θ = ordTheta η`. -/
theorem wDeriv_rowComposite_a {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a) {m k : ℕ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    wDeriv (k * η.period.toNat) (cellSchur (η.compose (rowCells 0 (m : ℤ)))) =
      ((((m : ℤ) - k) * η.period + ordTheta η : ℤ) : Lambda) *
        pDeriv (k * η.period.toNat) (cellSchur (η.compose (rowCells 0 (m : ℤ)))) := by
  have ho : η.IsOrdinary := by simp [Gluing.MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hpp := hη.period_pos
  have hr : 0 < k * η.period.toNat := Nat.mul_pos hk (by omega)
  have hF : IsSkew (η.compose (rowCells 0 (m : ℤ))) := (hη.isConnectedSkew_compose hD).1
  have hFeq := Gluing.Plan.MarkedInner.compose_eq_copies ho hD.2.1
  obtain ⟨hLeft, -, -⟩ := northwest_ribbon_bijection hη hc hD.1 hk
  obtain ⟨hRight, -, -⟩ := southeast_ribbon_bijection_composite hη hc hD.1 hk
  rw [leftRibbons_rowCells hk hkm, Finset.image_singleton] at hLeft
  rw [rightRibbons_rowCells hk hkm, Finset.image_singleton] at hRight
  rw [← hFeq] at hLeft
  have h2 := wDeriv_cellSchur_skew hF hr
  have hR := pDeriv_cellSchur_right_of_isSkew hF hr
  have hL := pDeriv_cellSchur_left_of_isSkew hF hr
  unfold ribbonSumRight at hR
  unfold ribbonSumLeft at hL
  rw [hLeft, Finset.sum_singleton] at h2 hL
  rw [hRight, Finset.sum_singleton] at h2 hR
  rw [minContent_bottomLift_row hη hc hk hkm, minContent_liftRibbon_row hη hc hk hkm] at h2
  rw [h2]
  have hP : pDeriv (k * η.period.toNat) (cellSchur (η.compose (rowCells 0 (m : ℤ)))) =
      (ribbonSign (bottomLift η (rowCells 0 (m : ℤ)) (rowCells ((m : ℤ) - k) m)) : Lambda) *
        cellSchur (η.compose (rowCells 0 (m : ℤ)) \
          bottomLift η (rowCells 0 (m : ℤ)) (rowCells ((m : ℤ) - k) m)) := hR
  have hP' : pDeriv (k * η.period.toNat) (cellSchur (η.compose (rowCells 0 (m : ℤ)))) =
      (ribbonSign (liftRibbon η (rowCells 0 (m : ℤ)) (rowCells 0 k)) : Lambda) *
        cellSchur (η.compose (rowCells 0 (m : ℤ)) \
          liftRibbon η (rowCells 0 (m : ℤ)) (rowCells 0 k)) := hL
  have hcoef : (((m : ℤ) - k) * η.period + ordTheta η : ℤ) =
      (minContent η.middle + ((m : ℤ) - k) * η.period) -
        (maxContent η.middle - η.period + 1) := by
    unfold ordTheta; ring
  rw [hcoef]
  exact weighted_aux _ _ _ _ _ _ _ hP hP'


/-! ### Hall covariance on the generators -/

theorem numRows_rowCells' {a b : ℤ} (h : a < b) : numRows (rowCells a b) = 1 := by
  unfold numRows rowSet rowCells
  rw [Finset.image_image]
  have : ((Prod.fst : ℤ × ℤ → ℤ) ∘ fun x : ℤ => ((0 : ℤ), x)) = fun _ => (0 : ℤ) := rfl
  rw [this, Finset.image_const]
  · simp
  · exact ⟨a, Finset.mem_Ico.mpr ⟨le_rfl, h⟩⟩

theorem ribbonSign_rowCells {a b : ℤ} (h : a < b) : ribbonSign (rowCells a b) = 1 := by
  unfold ribbonSign ribbonHeight
  rw [numRows_rowCells' h]
  simp

theorem rowCells_sdiff {m k : ℕ} (hkm : k ≤ m) :
    rowCells 0 (m : ℤ) \ rowCells ((m : ℤ) - k) m = rowCells 0 ((m - k : ℕ) : ℤ) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_sdiff, mem_rowCells]
  constructor
  · rintro ⟨⟨h0, h1, h2⟩, h3⟩
    refine ⟨h0, h1, ?_⟩
    by_contra hc
    exact h3 ⟨h0, by push_cast [Nat.cast_sub hkm] at hc; omega, h2⟩
  · rintro ⟨h0, h1, h2⟩
    push_cast [Nat.cast_sub hkm] at h2
    exact ⟨⟨h0, h1, by omega⟩, fun h => by omega⟩

theorem modifiedValue_row {η : MarkedInner} (hη : η.IsLegal) {j : ℕ} (hj : 1 ≤ j) :
    modifiedValue η (rowCells 0 (j : ℤ)) = compositionMap η (hPos j) := by
  rw [modified_eq_mod_comp hη, modComp_connected (isConnectedSkew_rowCells (by omega)),
    componentT_row η hj]

theorem compositionMap_hPos_zero (η : MarkedInner) : compositionMap η (hPos 0) = 1 := by
  rw [hPos_zero, map_one]

/-- **Hall covariance on the generators** (`eq:ordinary-covariance`, first clause). -/
theorem pDeriv_compositionMap_hPos {η : MarkedInner} (hη : η.IsLegal) (ho : η.IsOrdinary)
    {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    pDeriv (k * η.period.toNat) (compositionMap η (hPos j)) =
      if k ≤ j then ordinarySign η k * xi η ^ k * compositionMap η (hPos (j - k)) else 0 := by
  have hjz : (0 : ℤ) < j := by exact_mod_cast hj
  have hD := isConnectedSkew_rowCells (s := 0) (e := (j : ℤ)) hjz
  rw [← modifiedValue_row hη hj, ordinary_action hη.readoutLegal ho hD.1 hk]
  by_cases hkj : k ≤ j
  · rw [if_pos hkj]
    unfold ribbonSumRight
    rw [rightRibbons_rowCells hk hkj, Finset.sum_singleton, rowCells_sdiff hkj,
      ribbonSign_rowCells (by omega)]
    by_cases hjk : j - k = 0
    · have e : j - k = 0 := hjk
      rw [e, rowCells_zero_zero, compositionMap_hPos_zero, modified_empty]
      simp
    · rw [modifiedValue_row hη (by omega)]
      simp
  · rw [if_neg hkj]
    unfold ribbonSumRight
    rw [rightRibbons_rowCells_of_lt (by omega)]
    simp


/-- **Hall covariance of the composition map** (`eq:ordinary-covariance`, first clause), for a
legal ordinary mark: `δ_{kp} Ψ_η = ± ξ^k Ψ_η δ_k`, the sign being `ordinarySign` (trivial in case
(a), `(-1)^{k-1}` in case (b)). -/
theorem ordinary_hall_covariance {η : MarkedInner} (hη : η.IsLegal) (ho : η.IsOrdinary)
    {k : ℕ} (hk : 1 ≤ k) (f : Lambda) :
    pDeriv (k * η.period.toNat) (compositionMap η f) =
      (ordinarySign η k * xi η ^ k) * compositionMap η (pDeriv k f) := by
  refine intertwine_of_generators (compositionMap η) (pDeriv (k * η.period.toNat)) (pDeriv k)
    (ordinarySign η k * xi η ^ k) (fun j => ?_) f
  obtain ⟨n, hn⟩ := j
  have hX : (X (⟨n, hn⟩ : ℕ+) : Lambda) = hPos n := (hPos_pnat ⟨n, hn⟩).symm
  rw [hX, pDeriv_compositionMap_hPos hη ho hn hk, pDeriv_hPos hk n]
  split_ifs <;> simp

/-- Past the span, `V_{kp}` kills a row composite of a legal mark. -/
theorem wDeriv_rowComposite_of_lt_legal {η : MarkedInner} (hη : η.IsLegal) {m k : ℕ} (hm : 1 ≤ m)
    (hmk : m < k) :
    wDeriv (k * η.period.toNat) (cellSchur (η.compose (rowCells 0 (m : ℤ)))) = 0 := by
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hF := hη.isConnectedSkew_compose hD
  apply wDeriv_cellSchur_of_span_le hF.1
  have hsp := Gluing.MarkedInner.span_compose hD hη
  have hsr : (span (rowCells 0 (m : ℤ)) : ℤ) = m := by rw [span_rowCells]; omega
  rw [hsr] at hsp
  have hq := hη.2.2.1.2
  have hpp : 0 < η.period := hη.period_pos
  have hkz : (m : ℤ) + 1 ≤ k := by exact_mod_cast hmk
  have hcast : ((k * η.period.toNat : ℕ) : ℤ) = (k : ℤ) * η.period := by
    push_cast; rw [Int.toNat_of_nonneg hpp.le]
  have : (span (η.compose (rowCells 0 (m : ℤ))) : ℤ) ≤ ((k * η.period.toNat : ℕ) : ℤ) := by
    rw [hsp, hcast]
    have : ((m : ℤ) + 1) * η.period ≤ k * η.period := mul_le_mul_of_nonneg_right hkz hpp.le
    have hw : (η.width : ℤ) < η.period := hq
    nlinarith
  exact_mod_cast this

/-- **Weighted covariance on the generators, case (a)**. -/
theorem wDeriv_compositionMap_hPos_a {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    wDeriv (k * η.period.toNat) (compositionMap η (hPos j)) =
      if k ≤ j then (((j : ℤ) - k) * η.period + ordTheta η : ℤ) * (xi η ^ k *
        compositionMap η (hPos (j - k))) else 0 := by
  have ho : η.IsOrdinary := by simp [Gluing.MarkedInner.IsOrdinary, AttachCase.IsMixed, hc]
  obtain ⟨hA, -, -⟩ := wDeriv_normalizers_eq_zero hη (by omega : 0 < k)
  obtain ⟨hAk, -, -⟩ := normalizers_killed hη.readoutLegal (m := k) (by omega)
  rw [compositionMap_hPos η hj, derivation_mul_killed _ hA]
  by_cases hkj : k ≤ j
  · rw [if_pos hkj, wDeriv_rowComposite_a hη hc hj hk hkj]
    have h1 := pDeriv_compositionMap_hPos hη ho hj hk
    rw [if_pos hkj, compositionMap_hPos η hj] at h1
    have hsign : ordinarySign η k = 1 := by simp [ordinarySign, hc]
    rw [hsign, one_mul, derivation_mul_killed _ hAk] at h1
    rw [← mul_assoc, mul_comm (normalizerRow η ^ (j - 1)), mul_assoc, h1]
  · rw [if_neg hkj, wDeriv_rowComposite_of_lt_legal hη hj (by omega)]
    simp


/-- **Weighted covariance of the composition map, case (a)** (`eq:ordinary-covariance`). -/
theorem ordinary_weighted_covariance_a {η : MarkedInner} (hη : η.IsLegal) (hc : η.case = .a)
    {k : ℕ} (hk : 1 ≤ k) (f : Lambda) :
    wDeriv (k * η.period.toNat) (compositionMap η f) =
      xi η ^ k * compositionMap η (mixedOp (η.period : ℚ) ((ordTheta η : ℤ) : ℚ) k f) := by
  refine intertwine_of_generators (compositionMap η) (wDeriv (k * η.period.toNat))
    (mixedOp (η.period : ℚ) ((ordTheta η : ℤ) : ℚ) k) (xi η ^ k) (fun j => ?_) f
  obtain ⟨n, hn⟩ := j
  have hX : (X (⟨n, hn⟩ : ℕ+) : Lambda) = hPos n := (hPos_pnat ⟨n, hn⟩).symm
  rw [hX, wDeriv_compositionMap_hPos_a hη hc hn hk, mixedOp_hPos _ _ (by omega)]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn, if_pos hkn, compositionMap_C_mul]
    have hsc : (C ((η.period : ℚ) * (((n : ℚ)) - k) + ((ordTheta η : ℤ) : ℚ)) : Lambda) =
        ((((n : ℤ) - k) * η.period + ordTheta η : ℤ) : Lambda) := by
      simp only [map_add, map_mul, map_sub, map_natCast, map_intCast]
      push_cast
      ring
    rw [hsc]
    ring
  · rw [if_neg hkn, if_neg hkn]; simp

/-- Transport across antitransposition: for an ordinary mark, `Ψ_{η^{AT}} = ι ∘ Ψ_η`
(`eq:physical-operator-transport`). -/
theorem compositionMap_anti {η : MarkedInner} (ho : η.IsOrdinary) (f : Lambda) :
    compositionMap η.anti f = schurInvolution (compositionMap η f) := by
  have hf : compositionMap η.anti = schurInvolution.comp (compositionMap η) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [compositionMap_X, AlgHom.comp_apply]
    unfold modifiedGen
    rw [map_mul, map_pow]
    congr 1
    · unfold normalizerRow
      rw [Gluing.MarkedInner.anti_W, cellSchur_antitranspose]
    · unfold rowComposite
      have hne : (skewOf [(j : ℕ)] []).Nonempty := by
        rw [skewOf_row]; exact rowCells_nonempty (by exact_mod_cast j.pos)
      rw [← Gluing.MarkedInner.antitranspose_compose ho hne, cellSchur_antitranspose]
  exact congrArg (fun g => g f) hf

/-- The composition map in the paper's read-outer convention: `Ψ_η` in the horizontal cases and
`Ψ_η ∘ ω` in the vertical ones. -/
def readoutMap (η : MarkedInner) : Lambda →ₐ[ℚ] Lambda :=
  if η.case = .b then (compositionMap η).comp schurInvolution else compositionMap η

/-- The offset `θ` of the read-outer convention: `θ` in case (a), `-θ(η^{AT})` in case (b). -/
def readoutOffset (η : MarkedInner) : ℤ :=
  if η.case = .b then -ordTheta η.anti else ordTheta η

theorem mixedOp_schurInvolution (p ρ : ℚ) {k : ℕ} (hk : 1 ≤ k) (f : Lambda) :
    mixedOp p ρ k (schurInvolution f) = (-1) ^ k * schurInvolution (mixedOp p (-ρ) k f) := by
  rw [mixedOp_apply, mixedOp_apply, wDeriv_schurInvolution, pDeriv_schurInvolution (by omega)]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hC : ∀ a : ℚ, schurInvolution (C a : Lambda) = C a := fun a => by
    rw [← MvPolynomial.algebraMap_eq]; exact AlgHom.commutes _ _
  simp only [map_add, map_mul, hC, map_neg, Nat.add_sub_cancel, pow_succ]
  ring


theorem sign_cancel (pp k : ℕ) (hpp : 1 ≤ pp) :
    (-1 : Lambda) ^ (k * pp) * ((-1 : Lambda) ^ (pp - 1)) ^ k * (-1 : Lambda) ^ k = 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, pp = q + 1 := ⟨pp - 1, by omega⟩
  rw [← pow_mul, ← pow_add, ← pow_add]
  have : k * (q + 1) + (q + 1 - 1) * k + k = 2 * (k * (q + 1)) := by
    simp only [Nat.add_sub_cancel]; ring
  rw [this, pow_mul]
  simp

theorem case_b_data {η : MarkedInner} (hη : η.IsLegal) (hb : η.case = .b) :
    η.anti.IsLegal ∧ η.anti.case = .a ∧ η.anti.anti = η := by
  refine ⟨Gluing.MarkedInner.isLegal_anti hη (Gluing.MarkedInner.W_nonempty_of_case_b hη hb), ?_,
    Gluing.MarkedInner.anti_anti η⟩
  rw [Gluing.MarkedInner.anti_case, hb]; rfl

/-- **Hall covariance in the read-outer convention** (`eq:ordinary-covariance`). -/
theorem readout_hall_covariance {η : MarkedInner} (hη : η.IsLegal) (ho : η.IsOrdinary) {k : ℕ}
    (hk : 1 ≤ k) (f : Lambda) :
    pDeriv (k * η.period.toNat) (readoutMap η f) = xi η ^ k * readoutMap η (pDeriv k f) := by
  unfold readoutMap
  by_cases hb : η.case = .b
  · simp only [hb, if_true, AlgHom.comp_apply]
    rw [ordinary_hall_covariance hη ho hk, pDeriv_schurInvolution (by omega)]
    simp only [ordinarySign, hb, if_true, map_mul, map_pow, map_neg, map_one]
    have : ((-1 : Lambda) ^ (k - 1)) * ((-1 : Lambda) ^ (k - 1)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    linear_combination (xi η ^ k * compositionMap η (schurInvolution (pDeriv k f))) * this
  · simp only [hb, if_false]
    have hsign : ordinarySign η k = 1 := by simp [ordinarySign, hb]
    rw [ordinary_hall_covariance hη ho hk, hsign, one_mul]

/-- **Weighted covariance in the read-outer convention** (`eq:ordinary-covariance`), with the
offset `θ = readoutOffset η`. -/
theorem readout_weighted_covariance {η : MarkedInner} (hη : η.IsLegal) (ho : η.IsOrdinary)
    {k : ℕ} (hk : 1 ≤ k) (f : Lambda) :
    wDeriv (k * η.period.toNat) (readoutMap η f) =
      xi η ^ k * readoutMap η (mixedOp (η.period : ℚ) ((readoutOffset η : ℤ) : ℚ) k f) := by
  by_cases hb : η.case = .b
  · obtain ⟨hl0, hc0, hanti⟩ := case_b_data hη hb
    have ho0 : η.anti.IsOrdinary := by
      unfold Gluing.MarkedInner.IsOrdinary
      rw [hc0]
      simp [AttachCase.IsMixed]
    have hpp : 1 ≤ η.period.toNat := by have := hη.period_pos; omega
    have hper : η.anti.period = η.period := Gluing.MarkedInner.period_anti η
    have key : ∀ g, readoutMap η g = schurInvolution (compositionMap η.anti (schurInvolution g)) := by
      intro g
      unfold readoutMap
      simp only [hb, if_true, AlgHom.comp_apply]
      have := compositionMap_anti ho0 (schurInvolution g)
      rw [hanti] at this
      exact this
    have hE : η.E = antitranspose η.anti.E := by
      have := Gluing.MarkedInner.anti_E η.anti
      rw [hanti] at this
      exact this
    have hxi : xi η = (-1) ^ (η.period.toNat - 1) * schurInvolution (xi η.anti) := by
      unfold xi
      rw [hE, cellSchur_antitranspose, pDeriv_schurInvolution (by omega), hper]
    have hinv : schurInvolution (xi η.anti) = (-1) ^ (η.period.toNat - 1) * xi η := by
      rw [hxi, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
    have hw := ordinary_weighted_covariance_a hl0 hc0 hk (schurInvolution f)
    rw [hper] at hw
    rw [key f, wDeriv_schurInvolution, hw, mixedOp_schurInvolution _ _ hk]
    simp only [readoutOffset, hb, if_true, hanti, key]
    push_cast
    have hC1 : ∀ x : Lambda, compositionMap η.anti ((-1 : Lambda) ^ k * x) =
        (-1 : Lambda) ^ k * compositionMap η.anti x := fun x => by
      simp only [map_mul, map_pow, map_neg, map_one]
    have hC2 : ∀ x : Lambda, schurInvolution ((-1 : Lambda) ^ k * x) =
        (-1 : Lambda) ^ k * schurInvolution x := fun x => by
      simp only [map_mul, map_pow, map_neg, map_one]
    rw [hC1, map_mul, map_pow, hC2, hinv, mul_pow]
    have hs := sign_cancel η.period.toNat k hpp
    linear_combination (xi η ^ k * schurInvolution (compositionMap η.anti
      (schurInvolution (mixedOp (η.period : ℚ) (-(ordTheta η.anti : ℚ)) k f)))) * hs
  · have hsign : ordinarySign η k = 1 := by simp [ordinarySign, hb]
    have hca : η.case = .a := by
      unfold Gluing.MarkedInner.IsOrdinary at ho
      cases hcc : η.case <;> simp_all [AttachCase.IsMixed]
    simp only [readoutMap, readoutOffset, hb, if_false]
    exact ordinary_weighted_covariance_a hη hca hk f


/-- `ordTheta` is bounded by the period for a case-(a) mark, and vanishes at the empty edge. -/
theorem ordTheta_bound {η : MarkedInner} (hη : η.IsLegal) :
    -η.period < ordTheta η ∧ ordTheta η < η.period := by
  by_cases hW : η.W = ∅
  · rw [ordTheta_eq_zero_empty ⟨hη, hW⟩]
    have := hη.period_pos
    omega
  · have h : η.IsLegalNonempty := ⟨hη, Finset.nonempty_iff_ne_empty.mpr hW⟩
    obtain ⟨s, t, hph⟩ := h.exists_phases
    rw [ordTheta_eq_phases h hph]
    have hq := h.width_lt_period
    obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
    omega

/-- **The offset `θ = V_p s_E / ξ`** (`lem:covariance`): an integer, with `|θ| < p`. -/
theorem wDeriv_period_inner_ordinary {η : MarkedInner} (hη : η.IsLegal) (ho : η.IsOrdinary) :
    wDeriv η.period.toNat (cellSchur η.E) = C ((readoutOffset η : ℤ) : ℚ) * xi η ∧
      -η.period < readoutOffset η ∧ readoutOffset η < η.period := by
  have hone : ∀ ω : MarkedInner, ω.IsLegal → ω.case = .a →
      wDeriv ω.period.toNat (cellSchur ω.E) = C ((ordTheta ω : ℤ) : ℚ) * xi ω := by
    intro ω hω hcω
    have h := wDeriv_rowComposite_a hω hcω (m := 1) (k := 1) le_rfl le_rfl le_rfl
    have e : rowCells 0 (((1 : ℕ)) : ℤ) = {((0 : ℤ), (0 : ℤ))} := by
      ext ⟨a, b⟩; simp [rowCells]; omega
    rw [e, cellSchur_compose_single] at h
    simp only [one_mul, Nat.cast_one, sub_self, zero_mul, zero_add] at h
    rw [h]
    rfl
  by_cases hb : η.case = .b
  · obtain ⟨hl0, hc0, hanti⟩ := case_b_data hη hb
    have hper : η.anti.period = η.period := Gluing.MarkedInner.period_anti η
    have hE : η.E = antitranspose η.anti.E := by
      have := Gluing.MarkedInner.anti_E η.anti
      rw [hanti] at this
      exact this
    have hpp : 1 ≤ η.period.toNat := by have := hη.period_pos; omega
    have hxi : xi η = (-1) ^ (η.period.toNat - 1) * schurInvolution (xi η.anti) := by
      unfold xi
      rw [hE, cellSchur_antitranspose, pDeriv_schurInvolution (by omega), hper]
    have h0 := hone η.anti hl0 hc0
    rw [hper] at h0
    have hb' := ordTheta_bound hl0
    rw [hper] at hb'
    refine ⟨?_, ?_, ?_⟩
    · rw [hE, cellSchur_antitranspose, wDeriv_schurInvolution, h0, hxi]
      simp only [readoutOffset, hb, if_true, map_mul, map_neg, Int.cast_neg]
      have hC : schurInvolution (C ((ordTheta η.anti : ℤ) : ℚ) : Lambda) =
          C ((ordTheta η.anti : ℤ) : ℚ) := by
        rw [← MvPolynomial.algebraMap_eq]; exact AlgHom.commutes _ _
      rw [hC]
      have hs : (-1 : Lambda) ^ η.period.toNat = -((-1) ^ (η.period.toNat - 1)) := by
        obtain ⟨q, hq⟩ : ∃ q, η.period.toNat = q + 1 := ⟨η.period.toNat - 1, by omega⟩
        rw [hq, Nat.add_sub_cancel, pow_succ]
        ring
      linear_combination (C ((ordTheta η.anti : ℤ) : ℚ) * schurInvolution (xi η.anti)) * hs
    · simp only [readoutOffset, hb, if_true]; omega
    · simp only [readoutOffset, hb, if_true]; omega
  · have hca : η.case = .a := by
      unfold Gluing.MarkedInner.IsOrdinary at ho
      cases hcc : η.case <;> simp_all [AttachCase.IsMixed]
    have hb' := ordTheta_bound hη
    simp only [readoutOffset, hb, if_false]
    exact ⟨hone η hη hca, hb'.1, hb'.2⟩

end SkewMarkedFactor
