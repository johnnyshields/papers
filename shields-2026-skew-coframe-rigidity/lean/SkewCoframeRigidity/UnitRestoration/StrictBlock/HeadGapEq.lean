/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadDescent
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadExtend
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadGap

/-!
# The gap equation

The gap case of the head step of `sc:linearized-cap` in `shields-2026-skew-coframe-rigidity.tex`
(`sc:gap-coface`).  Let `b` be the largest weighted vacancy, lying in a gap: the rows
`X_0, …, X_p` and the columns `Y_0, …, Y_{p-1}` are exactly the labels above `b`, so the proper
matrix `T` of `B` has the closed prefix `P` (rows `X_1, …, X_p`, columns `Y_0, …, Y_{p-1}`) in its
upper left corner and a zero block below it.

* `numerator_sub_letter_mem`: for a position `x ≤ b`, the numerator coefficient `P_x = [HG]_x`
  is `h_x` plus an element of `ℚ(h_0, …, h_{b-1})`.  The prefix columns lie above `b` and do not
  contribute, and the lower native coefficients use only the lower rows.
* `firstVar_ceiling` (`HeadDescent.lean`) then brings every coefficient of the first variation
  `Q` into `ℚ(h_0, …, h_b)`, and the zero range gives `Q_{x-b} = 0` for `x ≤ span B`.
* Differentiating `Q` in `h_b` therefore gives a vacancy-pulse tangent with the single surviving
  weight `-ρ_b` at the vacancy `b`.  By `pulse_tangent_unique` it is `-ρ_b` times the vacancy
  pulse at `b`.  The top equation `[HQ]_{span B} = 0`, differentiated, becomes
  `h_{m-b} - H_{m,cols P} P⁻¹ H_{rows P,b} = 0`, since the inverse column `T⁻¹ H_{·,b}` has no
  component below the cut (`inv_mulVec_eq_extZero`).
* `gapNumOf` is the numerator `h_{m-b} det P - H_{m,cols P} adj(P) H_{rows P,b}` over an arbitrary
  letter family; the identity over the coherent letters passes to the physical unit by
  `deh` (`gap_equation_proof`).

Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.FixedCap Polynomial Matrix

variable {k n p : ℕ}

section Generic

variable {R : Type*} [CommRing R]

/-- The prefix matrix `P = (h_{X_i - Y_j})`, rows `X_1, …, X_p`, columns `Y_0, …, Y_{p-1}`. -/
def gapPrefixOf (h : ℕ → R) (B : BetaDiagram (n + 1)) (hp : p ≤ n) : Matrix (Fin p) (Fin p) R :=
  Matrix.of fun i j => letterOf h (B.row ⟨i.val + 1, by omega⟩ - B.col ⟨j.val, by omega⟩)

/-- The row `H_{m, cols P}`, `m = X_0`. -/
def gapRowOf (h : ℕ → R) (B : BetaDiagram (n + 1)) (hp : p ≤ n) : Fin p → R :=
  fun j => letterOf h (B.row 0 - B.col ⟨j.val, by omega⟩)

/-- The column `H_{rows P, b}`. -/
def gapColOf (h : ℕ → R) (B : BetaDiagram (n + 1)) (hp : p ≤ n) (b : ℤ) : Fin p → R :=
  fun i => letterOf h (B.row ⟨i.val + 1, by omega⟩ - b)

/-- `h_{m-b} det P - H_{m,cols P} adj(P) H_{rows P,b}` over an arbitrary letter family. -/
def gapNumOf (h : ℕ → R) (B : BetaDiagram (n + 1)) (hp : p ≤ n) (b : ℤ) : R :=
  letterOf h (B.row 0 - b) * (gapPrefixOf h B hp).det -
    gapRowOf h B hp ⬝ᵥ ((gapPrefixOf h B hp).adjugate *ᵥ gapColOf h B hp b)

theorem gapNumerator_eq (B : BetaDiagram (n + 1)) (hp : p ≤ n) (b : ℤ) :
    gapNumerator B hp b = gapNumOf (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) B hp b := by
  have hl : ∀ z : ℤ, letterOf (fun k : ℕ => (complete (k : ℤ) : CompleteRing)) z = complete z := by
    intro z
    unfold letterOf
    split_ifs with h
    · exact (complete_of_neg h).symm
    · change complete ((z.toNat : ℕ) : ℤ) = complete z
      rw [Int.toNat_of_nonneg (by omega)]
  unfold gapNumerator gapNumOf gapPrefixOf gapRowOf gapColOf gapPrefixMat gapRowVec gapColVec
  simp only [hl]

theorem map_gapNumOf {S : Type*} [CommRing S] (f : R →+* S) (h : ℕ → R) (B : BetaDiagram (n + 1))
    (hp : p ≤ n) (b : ℤ) :
    f (gapNumOf h B hp b) = gapNumOf (fun k => f (h k)) B hp b := by
  have hl : ∀ z : ℤ, f (letterOf h z) = letterOf (fun k => f (h k)) z := by
    intro z; unfold letterOf; split_ifs <;> simp
  have hM : (gapPrefixOf h B hp).map f = gapPrefixOf (fun k => f (h k)) B hp := by
    refine Matrix.ext fun i j => ?_
    simp [gapPrefixOf, hl]
  have hadj : ((gapPrefixOf h B hp).adjugate).map f =
      (gapPrefixOf (fun k => f (h k)) B hp).adjugate := by
    rw [← hM]
    have := RingHom.map_adjugate f (gapPrefixOf h B hp)
    simpa [RingHom.mapMatrix_apply] using this
  have hdet : f (gapPrefixOf h B hp).det = (gapPrefixOf (fun k => f (h k)) B hp).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
  have hv1 : (f ∘ gapRowOf h B hp) = gapRowOf (fun k => f (h k)) B hp := funext fun j => hl _
  have hv2 : (f ∘ gapColOf h B hp b) = gapColOf (fun k => f (h k)) B hp b := funext fun i => hl _
  have hmv : f ∘ ((gapPrefixOf h B hp).adjugate *ᵥ gapColOf h B hp b) =
      ((gapPrefixOf h B hp).adjugate).map f *ᵥ (f ∘ gapColOf h B hp b) :=
    funext fun i => RingHom.map_mulVec f _ _ i
  unfold gapNumOf
  rw [map_sub, map_mul, hl, hdet, RingHom.map_dotProduct, hv1, hmv, hadj, hv2]

end Generic

section Numerator

variable (B : BetaDiagram (n + 1))

/-- **The numerator coefficients below the gap are lower.**  For a position `x ≤ b` with `b` below
the prefix columns and above the lower rows, `P_x = [HG]_x` is `h_x` plus an element of
`ℚ(h_0, …, h_{b-1})`. -/
theorem numerator_sub_letter_mem (hB : IsNorm B) (hBc : B.Connected) (b : ℤ) (hb0 : 0 < b)
    (hrow' : ∀ i : Fin (n + 1), p < i.val → B.row i < b)
    (hcol : ∀ j : Fin (n + 1), j.val < p → b < B.col j)
    (hcut : ∀ hp : p + 1 ≤ n, PrefixCut B p hp) (x : ℕ) (hx : (x : ℤ) ≤ b) :
    PowerSeries.coeff x (letterSeries * (coframe B : PowerSeries CohField)) - cohLetters x ∈
      letterField b.toNat := by
  have hbN : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb0.le
  have h0 : B.col (Fin.last n) = 0 := hB
  have hP : PowerSeries.coeff x (letterSeries * (coframe B : PowerSeries CohField)) =
      letterOf cohLetters ((x : ℤ) - B.col (Fin.last n)) +
        (fun j : Fin n => letterOf cohLetters ((x : ℤ) - B.col j.castSucc)) ⬝ᵥ
          coframeVecOf cohLetters B :=
    coeff_coframe_vac cohLetters B hB x
  rw [hP, h0, sub_zero]
  have hx0 : letterOf cohLetters (x : ℤ) = cohLetters x := by simp [letterOf]
  rw [hx0, add_sub_cancel_left]
  unfold dotProduct
  refine Subfield.sum_mem _ fun j _ => ?_
  by_cases hj : j.val < p
  · have hlt : (x : ℤ) - B.col j.castSucc < 0 := by
      have := hcol j.castSucc (by simpa using hj)
      omega
    simp [letterOf, hlt]
  · have hpn : p + 1 ≤ n := by have := j.isLt; omega
    have hcp : 0 < B.col j.castSucc :=
      col_pos_of_ne_last B hB j.castSucc (Fin.castSucc_lt_last j).ne
    refine Subfield.mul_mem _ (letterOf_mem_letterField (by omega)) ?_
    exact lower_coframe_mem B hpn hB hBc (hcut hpn) b.toNat (fun i hi => by
      have := hrow' i.succ (by simp only [Fin.val_succ]; omega)
      omega) j (by omega)

end Numerator

/-- **The gap equation.**  For the largest weighted vacancy `b` lying in a gap, the `h_b`-derivative
of the top equation `[HQ]_m = 0` gives
`ρ_b · (h_{X_0-b} det P - H_{X_0,cols P} adj(P) H_{rows P,b}) = 0` (`sc:gap-coface`, times
`det P`). -/
theorem gap_equation_proof {k n : ℕ} (K : BetaDiagram (k + 1)) (B : BetaDiagram (n + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected)
    (hKz : ZeroFree K) (hBz : ZeroFree B) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (h1 : dotW B ρ = 0)
    (h2 : dotW (splice K B hK hB) ρ = 0) (p : ℕ) (hp : p ≤ n) (b : ℤ) (hρb : ρ b ≠ 0)
    (hmax : ∀ x ∈ ρ.support, x ≤ b) (hrow : ∀ i : Fin (n + 1), i.val ≤ p → b < B.row i)
    (hrow' : ∀ i : Fin (n + 1), p < i.val → B.row i < b)
    (hcol : ∀ j : Fin (n + 1), j.val < p → b < B.col j)
    (hcol' : ∀ j : Fin (n + 1), p ≤ j.val → B.col j < b)
    (hcut : ∀ hp : p + 1 ≤ n, PrefixCut B p hp) :
    MvPolynomial.C (ρ b) * gapNumerator B hp b = 0 := by
  classical
  have hbmem : b ∈ ρ.support := Finsupp.mem_support_iff.mpr hρb
  obtain ⟨hb0, hbL, hbr, hbc⟩ := hρ b hbmem
  have hbN : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb0.le
  set bN := b.toNat with hbNdef
  have hbp : b < B.row ⟨p, by omega⟩ := hrow ⟨p, by omega⟩ le_rfl
  obtain ⟨hpos, hinj, hbS⟩ := firstVar_hyps B hB ρ hρ
  have hT : (properMat cohLetters (rowPos B) (colPos B)).det ≠ 0 := by
    rw [properMat_eq]; exact properDet_cohLetters_ne_zero hBc
  -- the vacancy `b`
  let v₀ : Fin ρ.support.card := ρ.support.equivFin ⟨b, hbmem⟩
  have hv₀pos : vacPos ρ v₀ = bN := by simp [vacPos, v₀, bN]
  have hρb0 : vacWt ρ v₀ ≠ 0 := by
    simp only [vacWt, v₀, Equiv.symm_apply_apply]
    exact (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2
      ((MvPolynomial.C_ne_zero).2 hρb)
  -- numerator coefficients at the weighted vacancies
  have hxle : ∀ v, ((vacPos ρ v : ℕ) : ℤ) ≤ b := fun v => by
    have h := hρ _ (ρ.support.equivFin.symm v).2
    have h' := hmax _ (ρ.support.equivFin.symm v).2
    unfold vacPos
    rw [Int.toNat_of_nonneg h.1.le]
    exact h'
  have hsub : ∀ v, PowerSeries.coeff (vacPos ρ v) (letterSeries *
      (coframe B : PowerSeries CohField)) - cohLetters (vacPos ρ v) ∈ letterField bN := fun v =>
    numerator_sub_letter_mem B hB hBc b hb0 hrow' hcol hcut _ (hxle v)
  have hP : ∀ v, PowerSeries.coeff (vacPos ρ v) (letterSeries *
      (coframe B : PowerSeries CohField)) ∈ letterField (bN + 1) := fun v => by
    have hx : vacPos ρ v < bN + 1 := by have := hxle v; omega
    have := Subfield.add_mem _ (letterField_mono (Nat.le_succ bN) (hsub v))
      (cohLetters_mem_letterField hx)
    simpa using this
  have hQ : ∀ s, (firstVar B ρ).coeff s ∈ letterField (bN + 1) :=
    firstVar_ceiling K B hK hB hKc hBc ρ hρ h1 h2 (bN + 1) hP
  have hzr : ∀ x : ℕ, x ≤ span B → bN ≤ x → (firstVar B ρ).coeff (x - bN) = 0 := fun x hx hbx =>
    firstVar_zero_range K B hK hB hKc hBc ρ hρ h1 h2 bN hQ (x - bN) (by
      have := span_pos K
      omega)
  have hspec := pulseSum_spec cohLetters (rowPos B) (colPos B) hT (vacPos ρ)
    (fun v => PowerSeries.coeff (vacPos ρ v) (letterSeries * (coframe B : PowerSeries CohField)))
    (vacWt ρ) (colPos_pos B) (fun v => (hpos v).1) hinj hbS
  -- the differentiated first variation is a multiple of the vacancy pulse at `b`
  set W : CohField[X] := pulse cohLetters (rowPos B) (colPos B) (-1) bN with hW
  set ρb : CohField := vacWt ρ v₀ with hρbdef
  have hWcoeff : ∀ j, W.coeff j = (if j = bN then 1 else 0) -
      ∑ s, ((properMat cohLetters (rowPos B) (colPos B))⁻¹ *ᵥ
        vacancyVec cohLetters (rowPos B) bN) s * (if j = colPos B s then 1 else 0) := by
    intro j
    rw [hW, coeff_pulse]
    ring
  have hdP : ∀ v, dRaw bN (PowerSeries.coeff (vacPos ρ v) (letterSeries *
      (coframe B : PowerSeries CohField))) = if vacPos ρ v = bN then 1 else 0 := by
    intro v
    have e : PowerSeries.coeff (vacPos ρ v) (letterSeries * (coframe B : PowerSeries CohField)) =
        (PowerSeries.coeff (vacPos ρ v) (letterSeries * (coframe B : PowerSeries CohField)) -
          cohLetters (vacPos ρ v)) + cohLetters (vacPos ρ v) := by ring
    rw [e, dRaw_add, dRaw_eq_zero_of_mem_letterField bN (hsub v), dRaw_letter, zero_add]
  have hRzero : dPoly bN (firstVar B ρ) + Polynomial.C ρb * W = 0 := by
    refine pulse_tangent_unique cohLetters (rowPos B) (colPos B) hT (colPos_injective B hB)
      (vacPos ρ) _ ?_ ?_ ?_
    · intro j hj
      by_contra hno
      push Not at hno
      refine hj ?_
      have hQj : (firstVar B ρ).coeff j = 0 := by
        unfold firstVar
        exact pulseSum_coeff_eq_zero _ _ _ _ _ _ j (fun v => (hno.2 v)) (fun s => hno.1 s)
      have hjb : j ≠ bN := fun h => hno.2 v₀ (by rw [hv₀pos]; exact h)
      rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_dPoly, hQj, dRaw_zero, hWcoeff,
        if_neg hjb, Finset.sum_eq_zero (fun s _ => by rw [if_neg (hno.1 s), mul_zero])]
      ring
    · intro v
      rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_dPoly, hWcoeff]
      have hvv : (firstVar B ρ).coeff (vacPos ρ v) = -(vacWt ρ v * PowerSeries.coeff (vacPos ρ v)
          (letterSeries * (coframe B : PowerSeries CohField))) := hspec.2.2 v
      rw [hvv, dRaw_neg, dRaw_mul, dRaw_eq_zero_of_mem_letterField bN (vacWt_mem ρ bN v), hdP v,
        Finset.sum_eq_zero (fun s _ => by rw [if_neg (hbS v s), mul_zero])]
      by_cases hv : vacPos ρ v = bN
      · have : v = v₀ := hinj (hv.trans hv₀pos.symm)
        subst this
        simp [hv, hρbdef]
      · simp [hv]
    · intro i
      have hrow := hspec.2.1 i
      have hmain : PowerSeries.coeff (rowPos B i)
          (letterSeries * (firstVar B ρ : PowerSeries CohField)) = 0 := hrow
      have key := coeff_letterSeries_mul_dPoly bN (firstVar B ρ) (rowPos B i)
      rw [hmain, dRaw_zero] at key
      have hd : PowerSeries.coeff (rowPos B i)
          (PowerSeries.mk cohLetters * ((dPoly bN (firstVar B ρ) : CohField[X]) :
            PowerSeries CohField)) = 0 := by
        change PowerSeries.coeff (rowPos B i) (letterSeries *
          ((dPoly bN (firstVar B ρ) : CohField[X]) : PowerSeries CohField)) = 0
        rw [key]
        split_ifs with hle
        · rw [hzr (rowPos B i) (rowPos_lt_span B i).le hle]; simp
        · simp
      rw [Polynomial.coe_add, mul_add, map_add, hd, Polynomial.coe_mul, Polynomial.coe_C,
        mul_left_comm, PowerSeries.coeff_C_mul, hW, coeff_row_pulse cohLetters (rowPos B)
          (colPos B) hT, mul_zero, zero_add]
  -- the differentiated top equation
  have htop := (firstVar_observations K B hK hB hKc hBc ρ hρ h1 h2).1
  have hd := coeff_letterSeries_mul_dPoly bN (firstVar B ρ) (span B)
  rw [htop, dRaw_zero] at hd
  have hdtop : PowerSeries.coeff (span B) (letterSeries *
      ((dPoly bN (firstVar B ρ) : CohField[X]) : PowerSeries CohField)) = 0 := by
    rw [hd]
    split_ifs with hle
    · rw [hzr (span B) le_rfl hle]; simp
    · simp
  have hWm : PowerSeries.coeff (span B) (PowerSeries.mk cohLetters * (W : PowerSeries CohField)) =
      0 := by
    have h0 : PowerSeries.coeff (span B) (letterSeries *
        (((dPoly bN (firstVar B ρ) + Polynomial.C ρb * W : CohField[X])) :
          PowerSeries CohField)) = 0 := by
      rw [hRzero]; simp
    rw [Polynomial.coe_add, mul_add, map_add, hdtop, zero_add, Polynomial.coe_mul,
      Polynomial.coe_C, mul_left_comm, PowerSeries.coeff_C_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left hρb0
  rw [hW, coeff_series_mul_pulse] at hWm
  have hcoef : letterOf cohLetters ((span B : ℤ) - bN) = ∑ s,
      ((properMat cohLetters (rowPos B) (colPos B))⁻¹ *ᵥ
        vacancyVec cohLetters (rowPos B) bN) s *
          letterOf cohLetters ((span B : ℤ) - colPos B s) := by
    have := (mul_eq_zero.mp hWm).resolve_left (by norm_num)
    exact sub_eq_zero.mp this
  rw [properMat_eq, vacancyVec_eq cohLetters B hB] at hcoef
  -- the inverse column has no component below the cut
  set ε : Fin p → Fin n := Fin.castLE hp with hε
  have hεinj : Function.Injective ε := Fin.castLE_injective hp
  have hrange : ∀ i : Fin n, i.val < p ↔ ∃ a, ε a = i := fun i =>
    ⟨fun h => ⟨⟨i.val, h⟩, Fin.ext rfl⟩, by rintro ⟨a, rfl⟩; exact a.isLt⟩
  have hTcut : ∀ i j : Fin n, p ≤ i.val → j.val < p →
      properMatrixOf cohLetters B i j = 0 := by
    intro i j hi hj
    have hpn : p + 1 ≤ n := by have := i.isLt; omega
    exact properMatrix_lowerLeft B hpn (hcut hpn) i j hi hj
  have hsubA : (properMatrixOf cohLetters B).submatrix ε ε = gapPrefixOf cohLetters B hp := by
    ext i j
    rfl
  have hdetA : (gapPrefixOf cohLetters B hp).det ≠ 0 := by
    have hc := gapBoard_connected B hp b hcol hbp hBc
    have := properDet_cohLetters_ne_zero hc
    rwa [show properMatrixOf cohLetters (gapBoard B hp b hcol hbp) =
      gapPrefixOf cohLetters B hp from by
        ext i j
        simp [properMatrixOf, gapPrefixOf, gapBoard, gapCol]] at this
  have hr0 : ∀ i : Fin n, p ≤ i.val →
      (fun i : Fin n => letterOf cohLetters (B.row i.succ - bN)) i = 0 := by
    intro i hi
    have := hrow' i.succ (by simp only [Fin.val_succ]; omega)
    simp only [letterOf]
    rw [if_pos (by omega)]
  have hy := inv_mulVec_eq_extZero hεinj hrange (properMatrixOf cohLetters B)
    (properDet_cohLetters_ne_zero hBc) (by rw [hsubA]; exact hdetA) hTcut
    (fun i : Fin n => letterOf cohLetters (B.row i.succ - bN)) hr0
  rw [hsubA] at hy
  rw [hy] at hcoef
  have hsum := sum_extZero hεinj ((gapPrefixOf cohLetters B hp)⁻¹ *ᵥ
    (fun a => (fun i : Fin n => letterOf cohLetters (B.row i.succ - bN)) (ε a)))
    (fun s => letterOf cohLetters ((span B : ℤ) - colPos B s))
  simp only [mul_comm _ (letterOf cohLetters _)] at hcoef
  rw [hsum] at hcoef
  have hrowspan : (span B : ℤ) = B.row 0 := (row_zero_eq B hB).symm
  have hcolpos : ∀ s : Fin n, (colPos B s : ℤ) = B.col s.castSucc := colPos_cast_of_norm hB
  have hcoef' : letterOf cohLetters (B.row 0 - b) =
      gapRowOf cohLetters B hp ⬝ᵥ ((gapPrefixOf cohLetters B hp)⁻¹ *ᵥ
        gapColOf cohLetters B hp b) := by
    have e1 : (span B : ℤ) - bN = B.row 0 - b := by rw [hrowspan, hbN]
    rw [e1] at hcoef
    rw [hcoef]
    unfold dotProduct
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [gapRowOf, hrowspan, hcolpos, hbN]
    rfl
  have hadj : ∀ w, (gapPrefixOf cohLetters B hp).det • ((gapPrefixOf cohLetters B hp)⁻¹ *ᵥ w) =
      (gapPrefixOf cohLetters B hp).adjugate *ᵥ w := by
    intro w
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec, smul_smul,
      mul_inv_cancel₀ hdetA, one_smul]
  have hnum : gapNumOf cohLetters B hp b = 0 := by
    unfold gapNumOf
    rw [← hadj, dotProduct_smul, smul_eq_mul, hcoef']
    ring
  -- from the coherent letters to the physical unit
  have hX : gapNumOf (fun k : ℕ => (MvPolynomial.X k : CohRing)) B hp b = 0 := by
    apply IsFractionRing.injective CohRing CohField
    have := map_gapNumOf (algebraMap CohRing CohField) (fun k : ℕ => (MvPolynomial.X k : CohRing))
      B hp b
    rw [map_zero, this]
    exact hnum
  have hphys : gapNumerator B hp b = 0 := by
    have := map_gapNumOf deh (fun k : ℕ => (MvPolynomial.X k : CohRing)) B hp b
    rw [hX, map_zero] at this
    have hfun : (fun k : ℕ => deh (MvPolynomial.X k : CohRing)) =
        fun k : ℕ => (complete (k : ℤ) : CompleteRing) := funext fun k => deh_X k
    rw [hfun] at this
    rw [gapNumerator_eq]
    exact this.symm
  rw [hphys, mul_zero]

end SkewCoframeRigidity.UnitRestoration
