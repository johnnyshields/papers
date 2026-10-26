/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.UnitCase.Setup
import SkewCoframeRigidity.Stationary.UnitCase.Algebra
import SkewCoframeRigidity.Stationary.NeitherCase

/-!
# The `ε`-adic bookkeeping of the unit case

Pure algebra over `A = CohField[ε]` for the unit case of `sc:positive-power` in
`shields-2026-skew-coframe-rigidity.tex`.  Polynomials `Gt`, `Ct` over `A` that agree with constant
polynomials at `ε = 0` to first order, satisfy the two retained maximal-row equations and the
one-power equation through degree `2M`, are compared at the first and second orders in `ε`.
-/

namespace SkewCoframeRigidity.UnitCase

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.UnitRestoration Polynomial


section Helpers

/-- Lifting a polynomial to constant coefficients commutes with the series coercion. -/
theorem coe_liftK (f : CohField[X]) :
    ((liftK f : Polynomial CohField[X]) : PowerSeries CohField[X]) =
      PowerSeries.map Polynomial.C (f : PowerSeries CohField) := by
  ext n
  simp [liftK, Polynomial.coeff_coe, PowerSeries.coeff_map]

/-- Truncation commutes with coefficientwise mapping. -/
theorem trunc_map' (φ : CohField →+* CohField[X]) (M : ℕ) (f : PowerSeries CohField) :
    PowerSeries.trunc M (PowerSeries.map φ f) = (PowerSeries.trunc M f).map φ := by
  ext n
  simp only [PowerSeries.coeff_trunc, Polynomial.coeff_map, PowerSeries.coeff_map]
  split_ifs <;> simp

/-- The clipped operator commutes with lifting to constant coefficients. -/
theorem clippedOp_liftK (M : ℕ) (f h : CohField[X]) (u : PowerSeries CohField) :
    clippedOp M (liftK f) (liftK h) (PowerSeries.map Polynomial.C u) =
      liftK (clippedOp M f h u) := by
  unfold clippedOp liftK
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul]
  have e1 : ((f.map Polynomial.C : Polynomial CohField[X]) : PowerSeries CohField[X]) =
      PowerSeries.map Polynomial.C (f : PowerSeries CohField) := coe_liftK f
  have e2 : ((h.map Polynomial.C : Polynomial CohField[X]) : PowerSeries CohField[X]) =
      PowerSeries.map Polynomial.C (h : PowerSeries CohField) := coe_liftK h
  rw [e1, e2, ← map_mul, ← map_mul, trunc_map', trunc_map']

/-- A constant polynomial factor in the first slot passes through the clipped operator. -/
theorem clippedOp_C_poly (M : ℕ) (c : CohField) (G C : CohField[X]) (u : PowerSeries CohField) :
    clippedOp M (Polynomial.C c * G) C u = Polynomial.C c * clippedOp M G C u := by
  unfold clippedOp
  have : u * ((Polynomial.C c * G : CohField[X]) : PowerSeries CohField) =
      PowerSeries.C c * (u * (G : PowerSeries CohField)) := by
    rw [Polynomial.coe_mul, Polynomial.coe_C]; ring
  rw [this, PowerSeries.trunc_C_mul]
  ring

/-- Powers of `AH` expand to second order in `ε`. -/
theorem AH_pow_expand (p : ℕ) : ∃ R : PowerSeries CohField[X],
    AH ^ p = 1 + PowerSeries.C (Polynomial.X : CohField[X]) *
      (PowerSeries.C (Polynomial.C (p : CohField)) * PowerSeries.map Polynomial.C Ubar) +
      PowerSeries.C (Polynomial.X : CohField[X]) ^ 2 * R := by
  induction p with
  | zero => exact ⟨0, by simp⟩
  | succ p ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨PowerSeries.C (Polynomial.C (p : CohField)) * PowerSeries.map Polynomial.C Ubar *
      PowerSeries.map Polynomial.C Ubar + R +
      PowerSeries.C (Polynomial.X : CohField[X]) * R * PowerSeries.map Polynomial.C Ubar, ?_⟩
    rw [pow_succ, hR]
    unfold AH
    simp only [Nat.cast_succ, map_add, map_one]
    ring

/-- The first `ε`-coefficient of a coefficient of `W * D`, where `W = 1 + ε n Ū + ε² R` and
`D = f + ε d` with `f` constant in `ε`. -/
theorem coeff_one_mul (W : PowerSeries CohField[X]) (n : CohField) (R : PowerSeries CohField[X])
    (hW : W = 1 + PowerSeries.C (Polynomial.X : CohField[X]) *
      (PowerSeries.C (Polynomial.C n) * PowerSeries.map Polynomial.C Ubar) +
      PowerSeries.C (Polynomial.X : CohField[X]) ^ 2 * R)
    (Q : CohField[X]) (d : Polynomial CohField[X]) (k : ℕ) :
    (PowerSeries.coeff k (W * ((liftK Q + Polynomial.C Polynomial.X * d :
        Polynomial CohField[X]) : PowerSeries CohField[X]))).coeff 1 =
      (d.coeff k).coeff 0 + n * PowerSeries.coeff k (Ubar * (Q : PowerSeries CohField))
      := by
  have hD : ((liftK Q + Polynomial.C Polynomial.X * d : Polynomial CohField[X]) :
      PowerSeries CohField[X]) = PowerSeries.map Polynomial.C (Q : PowerSeries CohField) +
      PowerSeries.C (Polynomial.X : CohField[X]) * (d : PowerSeries CohField[X]) := by
    rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, coe_liftK]
  have hUQ : PowerSeries.map Polynomial.C Ubar * PowerSeries.map Polynomial.C
      (Q : PowerSeries CohField) = PowerSeries.map Polynomial.C
        (Ubar * (Q : PowerSeries CohField)) := by rw [map_mul]
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries CohField[X], S = R * PowerSeries.map Polynomial.C
      (Q : PowerSeries CohField) + R * PowerSeries.C (Polynomial.X : CohField[X]) *
      (d : PowerSeries CohField[X]) + PowerSeries.map Polynomial.C Ubar *
      (d : PowerSeries CohField[X]) * PowerSeries.C (Polynomial.C n) :=
    ⟨_, rfl⟩
  have hexp : W * ((liftK Q + Polynomial.C Polynomial.X * d : Polynomial CohField[X]) :
      PowerSeries CohField[X]) = PowerSeries.map Polynomial.C (Q : PowerSeries CohField) +
      PowerSeries.C (Polynomial.X : CohField[X]) * ((d : PowerSeries CohField[X]) +
        PowerSeries.C (Polynomial.C n) * PowerSeries.map Polynomial.C
          (Ubar * (Q : PowerSeries CohField))) +
      PowerSeries.C (Polynomial.X : CohField[X]) ^ 2 * S := by
    rw [hD, hW, hS, ← hUQ]; ring
  rw [hexp, ← map_pow]
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, Polynomial.coeff_coe,
    Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul]
  simp [Polynomial.coeff_X_pow_mul']


/-- `AH` is `1 + ε Ū` modulo `ε²`. -/
theorem AH_expand : ∃ R : PowerSeries CohField[X],
    AH = 1 + PowerSeries.C (Polynomial.X : CohField[X]) *
      (PowerSeries.C (Polynomial.C ((1 : ℕ) : CohField)) * PowerSeries.map Polynomial.C Ubar) +
      PowerSeries.C (Polynomial.X : CohField[X]) ^ 2 * R := by
  obtain ⟨R, hR⟩ := AH_pow_expand 1
  exact ⟨R, by rw [← pow_one AH]; exact hR⟩

/-- A constant factor in the polynomial passes through the series product. -/
theorem coeff_Ubar_C_mul (β : CohField) (q : CohField[X]) (k : ℕ) :
    PowerSeries.coeff k (Ubar * ((Polynomial.C β * q : CohField[X]) : PowerSeries CohField)) =
      β * PowerSeries.coeff k (Ubar * (q : PowerSeries CohField)) := by
  rw [Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm, PowerSeries.coeff_C_mul]

/-- The `ε`-coefficient of the first order of a maximal row. -/
theorem row_first {β : CohField} (g : CohField[X]) (a : Polynomial CohField[X]) (k : ℕ)
    (Gt : Polynomial CohField[X])
    (hG : Gt = liftK (Polynomial.C β * g) + Polynomial.C Polynomial.X * a) :
    (PowerSeries.coeff k (AH * (Gt : PowerSeries CohField[X]))).coeff 1 =
      (a.coeff k).coeff 0 + β * PowerSeries.coeff k (Ubar * (g : PowerSeries CohField)) := by
  obtain ⟨R, hR⟩ := AH_expand
  have := coeff_one_mul AH ((1 : ℕ) : CohField) R hR (Polynomial.C β * g) a k
  rw [← hG, coeff_Ubar_C_mul] at this
  rw [this]
  simp

/-- Every polynomial over `CohField[ε]` splits into its `ε = 0` part and `ε` times a remainder. -/
theorem exists_split (q : Polynomial CohField[X]) :
    ∃ e : Polynomial CohField[X],
      q = liftK (q.map Polynomial.constantCoeff) + Polynomial.C Polynomial.X * e := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ h₁ h₂ =>
    obtain ⟨e₁, h₁⟩ := h₁
    obtain ⟨e₂, h₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    unfold liftK at *
    rw [Polynomial.map_add, Polynomial.map_add]
    calc q₁ + q₂ = (q₁.map Polynomial.constantCoeff).map Polynomial.C +
          Polynomial.C Polynomial.X * e₁ + ((q₂.map Polynomial.constantCoeff).map Polynomial.C +
          Polynomial.C Polynomial.X * e₂) := by rw [← h₁, ← h₂]
      _ = _ := by ring
  | monomial n r =>
    refine ⟨Polynomial.monomial n (Polynomial.divX r), ?_⟩
    unfold liftK
    rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.C_mul_monomial,
      ← map_add]
    congr 1
    rw [Polynomial.constantCoeff_apply]
    exact (Polynomial.divX_mul_X_add r).symm.trans (by ring)

/-- A series-coefficient of a lifted clipped operator is the lift of the coefficient. -/
theorem coeff_zero_liftK_coeff (Q : CohField[X]) (k : ℕ) :
    ((liftK Q).coeff k).coeff 0 = Q.coeff k := by
  simp [liftK, Polynomial.coeff_map]

end Helpers

/-- First order: the equations `[H^p Δ]_{M-1} = 0 = [H Δ]_{M-1}` force `[Ū (c - g)]_{M-1} = 0`
(`sc:unit-first-cap`). -/
theorem cap_first_order {M p : ℕ} (hM : 2 ≤ M) (hp : 2 ≤ p) {β : CohField} (hβ : β ≠ 0)
    (g c : CohField[X]) (Gt Ct a b : Polynomial CohField[X])
    (hG : Gt = liftK (Polynomial.C β * g) + Polynomial.C Polynomial.X * a)
    (hC : Ct = liftK (Polynomial.C β * c) + Polynomial.C Polynomial.X * b)
    (hrowG : PowerSeries.coeff (M - 1) (AH * (Gt : PowerSeries CohField[X])) = 0)
    (hrowC : PowerSeries.coeff (M - 1) (AH * (Ct : PowerSeries CohField[X])) = 0)
    (hE0 : PowerSeries.coeff (M - 1) (AH ^ p * ((Ct - Gt : Polynomial CohField[X]) :
      PowerSeries CohField[X])) = 0) :
    PowerSeries.coeff (M - 1) (Ubar * ((c - g : CohField[X]) : PowerSeries CohField)) = 0 := by
  have hl : liftK (Polynomial.C β * c) - liftK (Polynomial.C β * g) =
      liftK (Polynomial.C β * (c - g)) := by
    unfold liftK; rw [← Polynomial.map_sub, mul_sub]
  have hD : Ct - Gt = liftK (Polynomial.C β * (c - g)) +
      Polynomial.C Polynomial.X * (b - a) := by
    rw [hG, hC, ← hl]; ring
  obtain ⟨R, hR⟩ := AH_pow_expand p
  have e1 := congrArg (fun f => f.coeff 1) hrowG
  have e2 := congrArg (fun f => f.coeff 1) hrowC
  have e3 := congrArg (fun f => f.coeff 1) hE0
  simp only [Polynomial.coeff_zero] at e1 e2 e3
  rw [row_first g a _ Gt hG] at e1
  rw [row_first c b _ Ct hC] at e2
  rw [hD] at e3
  rw [coeff_one_mul (AH ^ p) (p : CohField) R (by simpa using hR) (Polynomial.C β * (c - g))
    (b - a) (M - 1), Polynomial.coeff_sub, Polynomial.coeff_sub, coeff_Ubar_C_mul] at e3
  have hx : PowerSeries.coeff (M - 1) (Ubar * ((c - g : CohField[X]) : PowerSeries CohField)) =
      PowerSeries.coeff (M - 1) (Ubar * (c : PowerSeries CohField)) -
        PowerSeries.coeff (M - 1) (Ubar * (g : PowerSeries CohField)) := by
    rw [Polynomial.coe_sub, mul_sub, map_sub]
  have hp1 : ((p : CohField) - 1) ≠ 0 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    have : ((q + 2 : ℕ) : CohField) - 1 = ((q + 1 : ℕ) : CohField) := by push_cast; ring
    rw [this]
    exact Nat.cast_ne_zero.mpr (by omega)
  rw [hx] at e3 ⊢
  have key : ((p : CohField) - 1) * β * (PowerSeries.coeff (M - 1) (Ubar * (c : PowerSeries
      CohField)) - PowerSeries.coeff (M - 1) (Ubar * (g : PowerSeries CohField))) = 0 := by
    linear_combination e3 - e2 + e1
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (mul_eq_zero.mp h) (by tauto)
  · exact h

/-- Second order: with equal cores, the one-power equation gives a polynomial `δ` (the first
`ε`-coefficient of `Ct - Gt`) with `𝒯_{g,δ}(z Ū) = 0`. -/
theorem second_order_vanishing {M p : ℕ} (hM : 3 ≤ M) (hp : 2 ≤ p) {β : CohField} (hβ : β ≠ 0)
    (g : CohField[X]) (Gt Ct a b : Polynomial CohField[X])
    (hG : Gt = liftK (Polynomial.C β * g) + Polynomial.C Polynomial.X * a)
    (hC : Ct = liftK (Polynomial.C β * g) + Polynomial.C Polynomial.X * b)
    (hdegG : Gt.natDegree < M) (hdegC : Ct.natDegree < M)
    (hrowG : PowerSeries.coeff (M - 1) (AH * (Gt : PowerSeries CohField[X])) = 0)
    (hrowC : PowerSeries.coeff (M - 1) (AH * (Ct : PowerSeries CohField[X])) = 0)
    (hPE : ∀ k < 2 * M, PowerSeries.coeff k
      (((clippedOp M Gt Ct (PowerSeries.X * AH ^ p) : Polynomial CohField[X]) :
          PowerSeries CohField[X]) -
        PowerSeries.X * ((clippedOp M Gt Ct AH : Polynomial CohField[X]) :
          PowerSeries CohField[X]) * AH ^ (p - 1)) = 0) :
    ∃ δ : CohField[X], (∀ s, δ.coeff s = ((Ct - Gt).coeff s).coeff 1) ∧
      clippedOp M g δ (PowerSeries.X * Ubar) = 0 := by
  have hD : Ct - Gt = Polynomial.C Polynomial.X * (b - a) := by rw [hG, hC]; ring
  obtain ⟨e, he⟩ := exists_split (b - a)
  obtain ⟨δ0, hδ0⟩ : ∃ δ0 : CohField[X], δ0 = (b - a).map Polynomial.constantCoeff := ⟨_, rfl⟩
  rw [← hδ0] at he
  have hcoef : ∀ s, δ0.coeff s = ((Ct - Gt).coeff s).coeff 1 := by
    intro s
    rw [hD, Polynomial.coeff_C_mul, show (1 : ℕ) = 0 + 1 from rfl, Polynomial.coeff_X_mul,
      hδ0, Polynomial.coeff_map]
    rfl
  have hid := second_order_identity (Polynomial.X : CohField[X]) M p (by omega) (by omega)
    (liftK (Polynomial.C β * g)) (liftK δ0) Gt Ct a b e (PowerSeries.map Polynomial.C Ubar)
    hG hC he hdegG hdegC hrowG hrowC hPE
  have hmapX : PowerSeries.X * PowerSeries.map Polynomial.C Ubar =
      PowerSeries.map Polynomial.C (PowerSeries.X * Ubar) := by
    rw [map_mul, PowerSeries.map_X]
  have hp1 : ((p - 1 : ℕ) : CohField) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- degrees
  have hgdeg : g.natDegree ≤ M - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro s hs
    have h0 : Gt.coeff s = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h1 := congrArg (fun f => f.coeff 0) h0
    simp only [hG, Polynomial.coeff_add, liftK, Polynomial.coeff_map, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_zero] at h1
    simp at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hβ
    · exact h1
  have hδdeg : δ0.natDegree ≤ M - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro s hs
    have hdd : (Ct - Gt).natDegree < M :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hdegC hdegG)
    have h0 : (Ct - Gt).coeff s = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hcoef, h0]
    simp
  refine ⟨δ0, hcoef, ?_⟩
  have hvan : ∀ k < 2 * M, (clippedOp M g δ0 (PowerSeries.X * Ubar)).coeff k = 0 := by
    intro k hk
    obtain ⟨ρ, hρ⟩ := hid k hk
    rw [hmapX, clippedOp_liftK, clippedOp_C_poly] at hρ
    have hcancel : (((p - 1 : ℕ) : CohField[X]) *
        (liftK (Polynomial.C β * clippedOp M g δ0 (PowerSeries.X * Ubar))).coeff k) =
        Polynomial.X * ρ := by
      refine mul_left_cancel₀ (pow_ne_zero 2 (Polynomial.X_ne_zero)) ?_
      rw [hρ]; ring
    have h0 := congrArg (fun f => f.coeff 0) hcancel
    simp only [Polynomial.coeff_X_mul_zero] at h0
    rw [show (((p - 1 : ℕ) : CohField[X])) = Polynomial.C ((p - 1 : ℕ) : CohField) by simp,
      Polynomial.coeff_C_mul, coeff_zero_liftK_coeff, Polynomial.coeff_C_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hp1
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hβ
      · exact h
  have hle := natDegree_clippedOp_le M g δ0 (PowerSeries.X * Ubar) hgdeg hδdeg (by omega)
  ext k
  rw [Polynomial.coeff_zero]
  by_cases hk : k < 2 * M
  · exact hvan k hk
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end SkewCoframeRigidity.UnitCase
