/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.Ratio
import SkewCoframeRigidity.Stationary.DerivSeries
import SkewCoframeRigidity.Stationary.LowerSeries

/-!
# Highest-component matching

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:top-matching`: the derivative in the top
proper letter of the first endpoint equation produces the ratio equation
`[H^p g]_L / k_E = [H^p c]_{L'} / k_F`, and the pole comparison of `sc:component-remainder`
forces the two highest strict components to have the same span and top quotient.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem coeff_mul_shift_poly (φ g : PowerSeries CohField) (u : CohField) (a N : ℕ) (h : a ≤ N) :
    PowerSeries.coeff N (φ * ((Polynomial.C u * Polynomial.X ^ a : CohField[X]) :
      PowerSeries CohField) * g) = u * PowerSeries.coeff (N - a) (φ * g) := by
  have e : φ * ((Polynomial.C u * Polynomial.X ^ a : CohField[X]) : PowerSeries CohField) * g =
      PowerSeries.C u * PowerSeries.X ^ a * (φ * g) := by
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
    ring
  rw [e, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos h]

/-- The top data of a diagram whose first proper row sits at `M - 1`. -/
structure TopSide (D : BetaDiagram (n + 1)) (p : ℕ) where
  a : ℕ
  c : CompData p
  ha : 1 ≤ a
  hsum : a + c.L = span D - 1
  hd : dS (span D - 1) (coframe D : PowerSeries CohField) =
    ((-(Polynomial.C c.k⁻¹ * Polynomial.X ^ a * c.g) : CohField[X]) : PowerSeries CohField)
  hflags : TopFlags D a c.L c.g

theorem topSide_exists {D : BetaDiagram (n + 1)} (hD : D.Connected) (hn : 0 < n)
    (htop : TopRow D hn) (p : ℕ) : Nonempty (TopSide D p) := by
  obtain ⟨a, L, g, k, hk, ha, hsum, hg0, hd, hkd, hshape, hfl⟩ := top_data hD hn htop
  exact ⟨⟨a, ⟨L, g, k, hk, hg0, hkd, hshape⟩, ha, hsum, hd, hfl⟩⟩

theorem coe_mul_poly (u : CohField) (a : ℕ) (g : CohField[X]) :
    ((Polynomial.C u * Polynomial.X ^ a * g : CohField[X]) : PowerSeries CohField) =
      ((Polynomial.C u * Polynomial.X ^ a : CohField[X]) : PowerSeries CohField) * g := by
  rw [Polynomial.coe_mul]

/-- The coefficient of `H^p` times the derivative of a coframe along its top component. -/
theorem coeff_pow_mul_dS {D : BetaDiagram (n + 1)} {p : ℕ} (s : TopSide D p) :
    PowerSeries.coeff (span D - 1) (letterSeries ^ p *
        dS (span D - 1) (coframe D : PowerSeries CohField)) = -(s.c.ratio) := by
  rw [s.hd, Polynomial.coe_neg, coe_mul_poly, mul_neg, ← mul_assoc, map_neg,
    coeff_mul_shift_poly _ _ _ _ _ (by have := s.hsum; omega)]
  have : span D - 1 - s.a = s.c.L := by have := s.hsum; omega
  rw [this, CompData.ratio]
  field_simp [s.c.hk]

theorem dS_difference {D E : BetaDiagram (n + 1)} (hs : span D = span E) {p : ℕ}
    (sD : TopSide D p) (sE : TopSide E p) :
    dS (span D - 1) ((coframe E - coframe D : CohField[X]) : PowerSeries CohField) =
      ((-(Polynomial.C sE.c.k⁻¹ * Polynomial.X ^ sE.a * sE.c.g) : CohField[X]) :
        PowerSeries CohField) -
      ((-(Polynomial.C sD.c.k⁻¹ * Polynomial.X ^ sD.a * sD.c.g) : CohField[X]) :
        PowerSeries CohField) := by
  rw [Polynomial.coe_sub, dS_sub, sD.hd, hs, sE.hd]

theorem constantCoeff_letterSeries : PowerSeries.constantCoeff letterSeries = cohLetters 0 := by
  simp [letterSeries, seriesOf, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The derivative in `H_{M-1}` of the first endpoint equation gives the ratio equation. -/
theorem ratio_eq_of_endpoint {D E : BetaDiagram (n + 1)} (hs : span D = span E) {p : ℕ}
    (hp : 1 ≤ p) (sD : TopSide D p) (sE : TopSide E p)
    (h0 : PowerSeries.coeff (span D - 1)
      (letterSeries ^ p * ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) = 0) :
    sD.c.ratio = sE.c.ratio := by
  have hd := congrArg (dRaw (span D - 1)) h0
  have hLs : dS (span D - 1) letterSeries = PowerSeries.X ^ (span D - 1) := dS_mk_letters _
  rw [dRaw_zero, ← coeff_dS, dS_mul, dS_pow', hLs, dS_difference hs sD sE] at hd
  have hΔ0 : PowerSeries.constantCoeff ((coframe E - coframe D : CohField[X]) :
      PowerSeries CohField) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_sub, coeff_zero_coframe, coeff_zero_coframe, sub_self]
  have e1 : PowerSeries.coeff (span D - 1) (PowerSeries.C (p : CohField) *
      (letterSeries ^ (p - 1) * PowerSeries.X ^ (span D - 1)) *
      ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) = 0 := by
    have : PowerSeries.C (p : CohField) *
        (letterSeries ^ (p - 1) * PowerSeries.X ^ (span D - 1)) *
        ((coframe E - coframe D : CohField[X]) : PowerSeries CohField) =
        PowerSeries.C (p : CohField) * (PowerSeries.X ^ (span D - 1) * (letterSeries ^ (p - 1) *
          ((coframe E - coframe D : CohField[X]) : PowerSeries CohField))) := by ring
    rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, hΔ0, mul_zero, mul_zero]
  rw [map_add] at hd
  rw [e1, zero_add] at hd
  have h2 := coeff_pow_mul_dS sD
  have h3 := coeff_pow_mul_dS sE
  rw [← hs] at h3
  rw [sD.hd] at h2
  have hE' := sE.hd
  rw [← hs] at hE'
  rw [hE'] at h3
  rw [mul_sub, map_sub, h2, h3] at hd
  linear_combination hd

theorem coeff_one_mul_of_zero {R : Type*} [CommRing R] (φ ψ : PowerSeries R)
    (hψ : PowerSeries.constantCoeff ψ = 0) :
    PowerSeries.coeff 1 (φ * ψ) = PowerSeries.constantCoeff φ * PowerSeries.coeff 1 ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, Finset.sum_cons,
    Finset.Nat.antidiagonal_zero, Finset.map_singleton, Finset.sum_singleton]
  simp only [Function.Embedding.coe_prodMap, Prod.map_apply, Function.Embedding.coeFn_mk,
    Nat.succ_eq_add_one, zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have e : PowerSeries.coeff 0 ψ = 0 := by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hψ
  simp [e]

/-- The pair of sides with equal data, as in the conclusion of the pole comparison. -/
structure Matched {D E : BetaDiagram (n + 1)} {p : ℕ} (sD : TopSide D p) (sE : TopSide E p) :
    Prop where
  ha : sD.a = sE.a
  hk : sD.c.k = sE.c.k
  hL : sD.c.L = sE.c.L

theorem dS_difference_matched {D E : BetaDiagram (n + 1)} (hs : span D = span E) {p : ℕ}
    {sD : TopSide D p} {sE : TopSide E p} (hm : Matched sD sE) :
    dS (span D - 1) ((coframe E - coframe D : CohField[X]) : PowerSeries CohField) =
      -(((Polynomial.C sD.c.k⁻¹ * Polynomial.X ^ sD.a : CohField[X]) : PowerSeries CohField) *
        ((sE.c.g - sD.c.g : CohField[X]) : PowerSeries CohField)) := by
  rw [dS_difference hs sD sE, ← hm.ha, ← hm.hk, Polynomial.coe_neg, Polynomial.coe_neg,
    coe_mul_poly, coe_mul_poly, Polynomial.coe_sub]
  ring

theorem delta_zero (E D : BetaDiagram (n + 1)) :
    PowerSeries.constantCoeff ((coframe E - coframe D : CohField[X]) : PowerSeries CohField) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    Polynomial.coeff_sub, coeff_zero_coframe, coeff_zero_coframe, sub_self]

theorem dRaw_endpoint_one {D E : BetaDiagram (n + 1)} (hs : span D = span E) {p : ℕ}
    {sD : TopSide D p} {sE : TopSide E p} (hm : Matched sD sE) (q : ℕ) :
    dRaw (span D - 1) (PowerSeries.coeff (span D)
        (letterSeries ^ q * ((coframe E - coframe D : CohField[X]) : PowerSeries CohField))) =
      q * cohLetters 0 ^ (q - 1) * (coframe E - coframe D).coeff 1 -
        sD.c.k⁻¹ * PowerSeries.coeff (sD.c.L + 1) (letterSeries ^ q *
          ((sE.c.g - sD.c.g : CohField[X]) : PowerSeries CohField)) := by
  have hpos := span_pos D
  have hLs : dS (span D - 1) letterSeries = PowerSeries.X ^ (span D - 1) := dS_mk_letters _
  rw [← coeff_dS, dS_mul, dS_pow', hLs, dS_difference_matched hs hm, map_add]
  congr 1
  · have e : PowerSeries.C (q : CohField) * (letterSeries ^ (q - 1) * PowerSeries.X ^ (span D - 1)) *
        ((coframe E - coframe D : CohField[X]) : PowerSeries CohField) =
        PowerSeries.C (q : CohField) * (PowerSeries.X ^ (span D - 1) * (letterSeries ^ (q - 1) *
          ((coframe E - coframe D : CohField[X]) : PowerSeries CohField))) := by ring
    rw [e, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      if_pos (by omega), show span D - (span D - 1) = 1 by omega,
      coeff_one_mul_of_zero _ _ (delta_zero E D), map_pow, constantCoeff_letterSeries,
      Polynomial.coeff_coe]
    ring
  · have e : letterSeries ^ q * -(((Polynomial.C sD.c.k⁻¹ * Polynomial.X ^ sD.a : CohField[X]) :
        PowerSeries CohField) * ((sE.c.g - sD.c.g : CohField[X]) : PowerSeries CohField)) =
        -(letterSeries ^ q * ((Polynomial.C sD.c.k⁻¹ * Polynomial.X ^ sD.a : CohField[X]) :
          PowerSeries CohField) * ((sE.c.g - sD.c.g : CohField[X]) : PowerSeries CohField)) := by
      ring
    rw [e, map_neg, coeff_mul_shift_poly _ _ _ _ _ (by have := sD.hsum; omega)]
    have : span D - sD.a = sD.c.L + 1 := by have := sD.hsum; omega
    rw [this]

theorem dRaw_endpoint_G {D : BetaDiagram (n + 1)} {p : ℕ} (sD : TopSide D p) :
    dRaw (span D - 1) (PowerSeries.coeff (span D - 1)
        (letterSeries ^ p * (coframe D : PowerSeries CohField))) =
      p * cohLetters 0 ^ (p - 1) - sD.c.ratio := by
  have hLs : dS (span D - 1) letterSeries = PowerSeries.X ^ (span D - 1) := dS_mk_letters _
  rw [← coeff_dS, dS_mul, dS_pow', hLs, map_add, coeff_pow_mul_dS sD]
  have e : PowerSeries.C (p : CohField) * (letterSeries ^ (p - 1) * PowerSeries.X ^ (span D - 1)) *
      (coframe D : PowerSeries CohField) = PowerSeries.C (p : CohField) *
        (PowerSeries.X ^ (span D - 1) * (letterSeries ^ (p - 1) * (coframe D : PowerSeries
          CohField))) := by ring
  rw [e, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, constantCoeff_letterSeries,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, coeff_zero_coframe]
  ring

theorem dRaw_delta_one {D E : BetaDiagram (n + 1)} (hs : span D = span E) {p : ℕ}
    {sD : TopSide D p} {sE : TopSide E p} (hm : Matched sD sE) :
    dRaw (span D - 1) ((coframe E - coframe D).coeff 1) = 0 := by
  rw [← Polynomial.coeff_coe, ← coeff_dS, dS_difference_matched hs hm, map_neg,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  have hd0 : PowerSeries.coeff 0 ((sE.c.g - sD.c.g : CohField[X]) : PowerSeries CohField) = 0 := by
    rw [Polynomial.coeff_coe, Polynomial.coeff_sub, sE.c.g0, sD.c.g0, sub_self]
  split_ifs with h
  · have : sD.a = 1 := by have := sD.ha; omega
    rw [this, Nat.sub_self, hd0]; simp
  · simp

theorem V_relation {D E : BetaDiagram (n + 1)} (hs : span D = span E) {p : ℕ}
    {sD : TopSide D p} {sE : TopSide E p} (hm : Matched sD sE)
    (htq : topQuotient D = topQuotient E) :
    (coframe E - coframe D).coeff 1 * sD.c.k =
      PowerSeries.coeff (sD.c.L + 1) (letterSeries * ((sE.c.g - sD.c.g : CohField[X]) :
        PowerSeries CohField)) := by
  have h := dRaw_endpoint_one hs hm 1
  have h0 : PowerSeries.coeff (span D) (letterSeries ^ 1 *
      ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) = 0 := by
    rw [pow_one, Polynomial.coe_sub, mul_sub, map_sub]
    have e1 : PowerSeries.coeff (span D) (letterSeries * (coframe E : PowerSeries CohField)) =
        topQuotient E := by show _ = PowerSeries.coeff (span E) _; rw [← hs]; rfl
    have e2 : PowerSeries.coeff (span D) (letterSeries * (coframe D : PowerSeries CohField)) =
        topQuotient D := rfl
    rw [e1, e2, htq, sub_self]
  rw [h0, dRaw_zero, pow_one] at h
  simp only [Nat.cast_one, pow_zero, mul_one, one_mul, Nat.sub_self] at h
  have hk := sD.c.hk
  field_simp at h
  linear_combination -h

theorem B_relation {D E : BetaDiagram (n + 1)} (hs : span D = span E) {p : ℕ}
    {sD : TopSide D p} {sE : TopSide E p} (hm : Matched sD sE)
    (h1 : dRaw (span D - 1) (PowerSeries.coeff (span D)
        (letterSeries ^ p * ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) -
      (coframe E - coframe D).coeff 1 * PowerSeries.coeff (span D - 1)
        (letterSeries ^ p * (coframe D : PowerSeries CohField))) = 0) :
    PowerSeries.coeff (sD.c.L + 1) (letterSeries ^ p *
        ((sE.c.g - sD.c.g : CohField[X]) : PowerSeries CohField)) =
      (coframe E - coframe D).coeff 1 *
        PowerSeries.coeff sD.c.L (letterSeries ^ p * (sD.c.g : PowerSeries CohField)) := by
  rw [dRaw_sub, dRaw_mul, dRaw_delta_one hs hm, dRaw_endpoint_one hs hm, dRaw_endpoint_G sD] at h1
  have hk := sD.c.hk
  have hr : sD.c.ratio = PowerSeries.coeff sD.c.L (letterSeries ^ p * (sD.c.g : PowerSeries
      CohField)) / sD.c.k := rfl
  rw [hr] at h1
  field_simp at h1
  linear_combination -h1

theorem compData_coeff_mem {p : ℕ} (c : CompData p) (hL : 1 ≤ c.L) (j : ℕ) :
    c.g.coeff j ∈ lowerField c.L := by
  rcases c.shape with ⟨h0, _⟩ | ⟨_, n', E, hE, hs, hg, hk⟩
  · omega
  · rw [← hg, ← hs]
    exact coframe_coeff_mem E (lowerField (span E)) (fun k hk => letter_mem_lowerField hk) j

theorem V_eq_delta_one_mul_k {D E : BetaDiagram (n + 1)} (hs : span D = span E) {p : ℕ}
    (hp : 2 ≤ p) {sD : TopSide D p} {sE : TopSide E p} (hm : Matched sD sE)
    (htq : topQuotient D = topQuotient E) (hL : 2 ≤ sD.c.L)
    (h1 : dRaw (span D - 1) (PowerSeries.coeff (span D)
        (letterSeries ^ p * ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) -
      (coframe E - coframe D).coeff 1 * PowerSeries.coeff (span D - 1)
        (letterSeries ^ p * (coframe D : PowerSeries CohField))) = 0) :
    PowerSeries.coeff (sD.c.L + 1) (letterSeries * ((sE.c.g - sD.c.g : CohField[X]) :
        PowerSeries CohField)) = (sE.c.g - sD.c.g).coeff 1 * sD.c.k := by
  have hVr := V_relation hs hm htq
  have hBr := B_relation hs hm h1
  obtain ⟨k₀, α, hk₀, hα, hα0, hk, hr⟩ := ratio_big sD.c hL hp
  have hkne := sD.c.hk
  have hA : PowerSeries.coeff sD.c.L (letterSeries ^ p * (sD.c.g : PowerSeries CohField)) =
      p * cohLetters 0 ^ (p - 1) * sD.c.k + α := by
    unfold CompData.ratio at hr
    field_simp at hr
    linear_combination hr
  have hδ0 : (sE.c.g - sD.c.g).coeff 0 = 0 := by
    rw [Polynomial.coeff_sub, sE.c.g0, sD.c.g0, sub_self]
  have hδmem : ∀ j, (sE.c.g - sD.c.g).coeff j ∈ lowerField sD.c.L := fun j => by
    rw [Polynomial.coeff_sub]
    refine (lowerField _).sub_mem ?_ (compData_coeff_mem sD.c (by omega) j)
    have := compData_coeff_mem sE.c (by rw [← hm.hL]; omega) j
    rwa [← hm.hL] at this
  generalize sD.c.L = L at *
  generalize hδd : (sE.c.g - sD.c.g) = δ at *
  generalize hΔ1 : (coframe E - coframe D).coeff 1 = Δ1 at *
  generalize sD.c.k = k at *
  generalize hx : cohLetters L = x at *
  have hxF : x ∉ (lowerField L).toSubfield := by rw [← hx]; exact letter_notMem_lowerField L
  have hθ : cohLetters 0 ∈ lowerField L := letter_mem_lowerField (by omega)
  let δ' : PowerSeries CohField := PowerSeries.mk fun i => δ.coeff (i + 1)
  have hshift : (δ : PowerSeries CohField) = PowerSeries.X * δ' := by
    ext i
    rcases i with _ | i
    · simp [hδ0, Polynomial.coeff_coe]
    · rw [PowerSeries.coeff_succ_X_mul, Polynomial.coeff_coe]
      simp [δ']
  have hδ'mem : δ' ∈ seriesOverRange (lowerField L) := by
    rw [mem_seriesOverRange_iff]; intro i; exact hδmem _
  have hshiftcoeff : ∀ q, PowerSeries.coeff (L + 1) (letterSeries ^ q * (δ : PowerSeries CohField))
      = PowerSeries.coeff L (letterSeries ^ q * δ') := by
    intro q
    rw [hshift, mul_left_comm, PowerSeries.coeff_succ_X_mul]
  have hδ'0 : PowerSeries.constantCoeff δ' = δ.coeff 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [δ']
  obtain ⟨wB, hwB, hB⟩ := coeff_pow_mul_decomp L (by omega) p δ' hδ'mem
  obtain ⟨wV, hwV, hV⟩ := coeff_pow_mul_decomp L (by omega) 1 δ' hδ'mem
  rw [hδ'0, hx] at hB hV
  have hBr' : PowerSeries.coeff L (letterSeries ^ p * δ') = Δ1 * PowerSeries.coeff L
      (letterSeries ^ p * (sD.c.g : PowerSeries CohField)) := by rw [← hshiftcoeff]; exact hBr
  have hVr' : Δ1 * k = PowerSeries.coeff L (letterSeries ^ 1 * δ') := by
    rw [← hshiftcoeff 1, pow_one]; exact hVr
  rw [hB, hA] at hBr'
  rw [hV] at hVr'
  simp only [pow_one, Nat.cast_one, Nat.sub_self, pow_zero, mul_one, one_mul] at hVr' hV
  have hgoal : PowerSeries.coeff (L + 1) (letterSeries * (δ : PowerSeries CohField)) =
      wV + x * δ.coeff 1 := by
    rw [← pow_one letterSeries, hshiftcoeff 1, pow_one]; exact hV
  rw [hgoal]
  have hcF : (p : CohField) * cohLetters 0 ^ (p - 1) ∈ lowerField L :=
    (lowerField L).mul_mem ((lowerField L).natCast_mem p) (pow_mem hθ _)
  have hβ : wB - (p * cohLetters 0 ^ (p - 1)) * wV ∈ lowerField L :=
    (lowerField L).sub_mem hwB ((lowerField L).mul_mem hcF hwV)
  have hδ1 : δ.coeff 1 ∈ lowerField L := hδmem 1
  have key : (x + k₀) * (wB - (p * cohLetters 0 ^ (p - 1)) * wV) =
      α * wV + α * δ.coeff 1 * x := by
    have e : k * wB + (p * cohLetters 0 ^ (p - 1)) * x * δ.coeff 1 * k =
        (wV + x * δ.coeff 1) * ((p * cohLetters 0 ^ (p - 1)) * k + α) := by
      linear_combination k * hBr' + ((p * cohLetters 0 ^ (p - 1)) * k + α) * hVr'
    rw [hk] at e
    linear_combination e
  have h2 : (wB - (p * cohLetters 0 ^ (p - 1)) * wV - α * δ.coeff 1) * x +
      (k₀ * (wB - (p * cohLetters 0 ^ (p - 1)) * wV) - α * wV) = 0 := by linear_combination key
  obtain ⟨h3, h4⟩ := eq_zero_of_mul_add_eq_zero (F := (lowerField L).toSubfield) hxF
    ((lowerField L).sub_mem hβ ((lowerField L).mul_mem hα hδ1))
    ((lowerField L).sub_mem ((lowerField L).mul_mem hk₀ hβ) ((lowerField L).mul_mem hα hwV)) h2
  have hβeq : wB - (p * cohLetters 0 ^ (p - 1)) * wV = α * δ.coeff 1 := sub_eq_zero.1 h3
  rw [hβeq] at h4
  have : α * (k₀ * δ.coeff 1 - wV) = 0 := by linear_combination h4
  have hw : wV = k₀ * δ.coeff 1 := by
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hα0
    · linear_combination -h
  rw [hk, hw]; ring

end SkewCoframeRigidity.Coframe
