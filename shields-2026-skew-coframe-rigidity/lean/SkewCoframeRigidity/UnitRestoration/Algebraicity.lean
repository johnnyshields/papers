/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# A divisor with coefficients in a subfield makes a free coordinate algebraic

Algebraic input of `sc:finite-injectivity` in `shields-2026-skew-coframe-rigidity.tex`
(«The complete unit expansion and finite injectivity», coprimality of `g` with `z^a P_{<M-a}`).
If a polynomial `g` with constant term one and positive degree, whose coefficients lie in a
subfield `L`, divides `Q' + x z^i` with `Q'` also over `L`, then `x` is algebraic over `L`.
Sorry-free.
-/

namespace SkewCoframeRigidity

open Polynomial

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra F K]

theorem isAlgebraic_of_dvd_add (L : IntermediateField F K) (g Q : K[X]) (x : K) (i : ℕ)
    (hg0 : g.coeff 0 = 1) (hdeg : 0 < g.natDegree)
    (hgL : ∀ k, g.coeff k ∈ L) (hQL : ∀ k, Q.coeff k ∈ L)
    (hdvd : g ∣ Q + C x * X ^ i) : IsAlgebraic L x := by
  classical
  have liftP : ∀ p : K[X], (∀ k, p.coeff k ∈ L) → ∃ q : L[X], q.map (algebraMap L K) = p := by
    intro p hp
    have : p ∈ Polynomial.lifts (algebraMap L K) :=
      (Polynomial.lifts_iff_coeff_lifts p).mpr fun k => ⟨⟨_, hp k⟩, rfl⟩
    exact this
  obtain ⟨gL, hgL'⟩ := liftP g hgL
  obtain ⟨QL, hQL'⟩ := liftP Q hQL
  have hgLne : gL ≠ 0 := by
    rintro rfl
    simp at hgL'; rw [← hgL'] at hg0; simp at hg0
  set c := gL.leadingCoeff with hc
  have hcne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hgLne
  set gm : L[X] := C c⁻¹ * gL with hgm
  have hmon : gm.Monic := by
    unfold Polynomial.Monic
    rw [hgm, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, ← hc, inv_mul_cancel₀ hcne]
  have hmap : gm.map (algebraMap L K) = C (algebraMap L K c⁻¹) * g := by
    rw [hgm, Polynomial.map_mul, Polynomial.map_C, hgL']
  have hmdvd : gm.map (algebraMap L K) ∣ Q + C x * X ^ i := by
    refine dvd_trans ?_ hdvd
    rw [hmap]
    have hu : algebraMap L K c⁻¹ ≠ 0 :=
      (map_ne_zero_iff (algebraMap L K) (algebraMap L K).injective).mpr (inv_ne_zero hcne)
    exact ⟨C (algebraMap L K c⁻¹)⁻¹, by
      rw [mul_comm (C _) g, mul_assoc, ← C_mul, mul_inv_cancel₀ hu, C_1, mul_one]⟩
  have hmmon : (gm.map (algebraMap L K)).Monic := hmon.map _
  have h0 := (Polynomial.modByMonic_eq_zero_iff_dvd hmmon).mpr hmdvd
  set ρ : L[X] := X ^ i %ₘ gm with hρ
  set σ : L[X] := QL %ₘ gm with hσ
  have hsplit : (Q + C x * X ^ i) %ₘ gm.map (algebraMap L K) =
      σ.map (algebraMap L K) + C x * ρ.map (algebraMap L K) := by
    rw [Polynomial.add_modByMonic, hσ, hρ, Polynomial.map_modByMonic _ hmon,
      Polynomial.map_modByMonic _ hmon, hQL', ← Polynomial.smul_eq_C_mul,
      Polynomial.smul_modByMonic, Polynomial.smul_eq_C_mul]
    simp
  rw [hsplit] at h0
  have hρne : ρ ≠ 0 := by
    intro hρ0
    have hd : gm ∣ X ^ i := (Polynomial.modByMonic_eq_zero_iff_dvd hmon).mp hρ0
    have hd' : g ∣ X ^ i := by
      have := Polynomial.map_dvd (algebraMap L K) hd
      rw [hmap, Polynomial.map_pow, Polynomial.map_X] at this
      exact dvd_trans ⟨C (algebraMap L K c⁻¹), by
        rw [mul_comm]⟩ this
    have hcop : IsCoprime g X := by
      obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := g)
      rw [hg0, map_one] at hq
      exact ⟨1, -q, by linear_combination hq⟩
    have hu := (hcop.pow_right (n := i)).isUnit_of_dvd' (dvd_refl g) hd'
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨k, hk⟩ : ∃ k, ρ.coeff k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hρne (Polynomial.ext fun k => by simpa using h k)
  have hkc := congrArg (fun p => p.coeff k) h0
  simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_C_mul,
    Polynomial.coeff_zero] at hkc
  refine ⟨C (ρ.coeff k) * X + C (σ.coeff k), ?_, ?_⟩
  · intro h
    have := congrArg (fun p => p.coeff 1) h
    simp at this
    exact hk this
  · simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp only [IntermediateField.algebraMap_apply] at *
    linear_combination hkc

end SkewCoframeRigidity
