/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.ClippedOperator
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination

/-!
# The second-order identity of the unit case

Formalizes the last step of the unit case in the proof of `sc:positive-power` of
`shields-2026-skew-coframe-rigidity.tex`: with `H = 1 + ε U`, the one-power equation and the exact
shift identity agree at order `ε²` through the common whole polynomial
`𝒯_{g,δ}(z U)`, which is therefore killed by `(p - 1) ε²` up to `ε³`.
-/

namespace SkewCoframeRigidity.UnitCase

open Polynomial PowerSeries

section Helpers

variable {A : Type*} [CommRing A]

/-- The clipped operator is additive in the series. -/
theorem clippedOp_add' (M : ℕ) (G C : Polynomial A) (u v : PowerSeries A) :
    clippedOp M G C (u + v) = clippedOp M G C u + clippedOp M G C v := by
  unfold clippedOp
  rw [add_mul, add_mul, map_add, map_add]
  ring

/-- A constant series factor passes through the clipped operator. -/
theorem clippedOp_C_mul' (M : ℕ) (G C : Polynomial A) (c : A) (u : PowerSeries A) :
    clippedOp M G C (PowerSeries.C c * u) = Polynomial.C c * clippedOp M G C u := by
  unfold clippedOp
  rw [mul_assoc, mul_assoc, PowerSeries.trunc_C_mul, PowerSeries.trunc_C_mul]
  ring

/-- The clipped operator kills the constant series `1` on polynomials of degree below the cutoff. -/
theorem clippedOp_one' (M : ℕ) (G C : Polynomial A) (hG : G.natDegree < M)
    (hC : C.natDegree < M) : clippedOp M G C 1 = 0 := by
  unfold clippedOp
  rw [one_mul, one_mul, PowerSeries.trunc_coe_eq_self hC, PowerSeries.trunc_coe_eq_self hG]
  ring

/-- Clipping `F * (x + ε y)` splits linearly. -/
theorem trunc_lin' (M : ℕ) (ε : A) (F : PowerSeries A) (x y : Polynomial A) :
    PowerSeries.trunc M (F * ((x + Polynomial.C ε * y : Polynomial A) : PowerSeries A)) =
      PowerSeries.trunc M (F * (x : PowerSeries A)) +
        Polynomial.C ε * PowerSeries.trunc M (F * (y : PowerSeries A)) := by
  rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, mul_add, map_add,
    mul_left_comm, PowerSeries.trunc_C_mul]

/-- Clipping `F * (x + y)` is additive. -/
theorem trunc_add' (M : ℕ) (F : PowerSeries A) (x y : Polynomial A) :
    PowerSeries.trunc M (F * ((x + y : Polynomial A) : PowerSeries A)) =
      PowerSeries.trunc M (F * (x : PowerSeries A)) +
        PowerSeries.trunc M (F * (y : PowerSeries A)) := by
  rw [Polynomial.coe_add, mul_add, map_add]

/-- Expansion of the clipped operator on `G = g + ε a`, `C = g + ε b` with `b - a = δ + ε e`. -/
theorem clippedOp_decomp (M : ℕ) (ε : A) (g δ G C a b e : Polynomial A)
    (hG : G = g + Polynomial.C ε * a) (hC : C = g + Polynomial.C ε * b)
    (hba : b - a = δ + Polynomial.C ε * e) (F : PowerSeries A) :
    clippedOp M G C F = Polynomial.C ε * clippedOp M g δ F +
      Polynomial.C ε ^ 2 * (clippedOp M g e F + clippedOp M a b F) := by
  have hb : b = a + δ + Polynomial.C ε * e := by linear_combination hba
  have h1 : PowerSeries.trunc M (F * (G : PowerSeries A)) =
      PowerSeries.trunc M (F * (g : PowerSeries A)) +
        Polynomial.C ε * PowerSeries.trunc M (F * (a : PowerSeries A)) := by
    rw [hG]; exact trunc_lin' M ε F g a
  have h3 : PowerSeries.trunc M (F * (b : PowerSeries A)) =
      PowerSeries.trunc M (F * (a : PowerSeries A)) +
        PowerSeries.trunc M (F * (δ : PowerSeries A)) +
        Polynomial.C ε * PowerSeries.trunc M (F * (e : PowerSeries A)) := by
    conv_lhs => rw [hb]
    rw [trunc_lin', trunc_add']
  have h2 : PowerSeries.trunc M (F * (C : PowerSeries A)) =
      PowerSeries.trunc M (F * (g : PowerSeries A)) +
        Polynomial.C ε * PowerSeries.trunc M (F * (b : PowerSeries A)) := by
    rw [hC]; exact trunc_lin' M ε F g b
  unfold clippedOp
  rw [h1, h2, h3]
  rw [hG, hC, hb]
  ring

end Helpers

theorem second_order_identity {A : Type*} [CommRing A] (ε : A) (M p : ℕ) (hM : 1 ≤ M)
    (hp : 1 ≤ p) (g δ G C a b e : Polynomial A) (U : PowerSeries A)
    (hG : G = g + Polynomial.C ε * a) (hC : C = g + Polynomial.C ε * b)
    (hba : b - a = δ + Polynomial.C ε * e)
    (hdegG : G.natDegree < M) (hdegC : C.natDegree < M)
    (hrowG : PowerSeries.coeff (M - 1) ((1 + PowerSeries.C ε * U) * (G : PowerSeries A)) = 0)
    (hrowC : PowerSeries.coeff (M - 1) ((1 + PowerSeries.C ε * U) * (C : PowerSeries A)) = 0)
    (hPE : ∀ k < 2 * M, PowerSeries.coeff k
      (((clippedOp M G C (PowerSeries.X * (1 + PowerSeries.C ε * U) ^ p) : Polynomial A) :
          PowerSeries A) -
        PowerSeries.X * ((clippedOp M G C (1 + PowerSeries.C ε * U) : Polynomial A) :
          PowerSeries A) * (1 + PowerSeries.C ε * U) ^ (p - 1)) = 0) :
    ∀ k < 2 * M, ∃ ρ : A,
      ε ^ 2 * (((p - 1 : ℕ) : A) * (clippedOp M g δ (PowerSeries.X * U)).coeff k) = ε ^ 3 * ρ :=
  by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hPE ⊢
  obtain ⟨H, hH⟩ : ∃ H : PowerSeries A, H = 1 + PowerSeries.C ε * U := ⟨_, rfl⟩
  rw [← hH] at hrowG hrowC hPE
  have hpow : ∀ j : ℕ, ∃ R : PowerSeries A, H ^ j = 1 + PowerSeries.C ε * R := by
    intro j
    induction j with
    | zero => exact ⟨0, by simp⟩
    | succ j ih =>
      obtain ⟨R, hR⟩ := ih
      refine ⟨U + R + PowerSeries.C ε * U * R, ?_⟩
      rw [pow_succ, hR, hH]; ring
  have hsum : ∀ m : ℕ, ∃ R : PowerSeries A,
      (∑ i ∈ Finset.range m, H ^ i) = PowerSeries.C (m : A) + PowerSeries.C ε * R := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨R, hR⟩ := ih
      obtain ⟨R', hR'⟩ := hpow m
      refine ⟨R + R', ?_⟩
      rw [Finset.sum_range_succ, hR, hR']
      simp only [Nat.cast_succ, map_add, map_one]; ring
  obtain ⟨R, hR⟩ := hsum n
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries A, S = ∑ i ∈ Finset.range n, H ^ i := ⟨_, rfl⟩
  rw [← hS] at hR
  have hH1 : H - 1 = PowerSeries.C ε * U := by rw [hH]; ring
  have hgeom : H ^ n - 1 = S * (PowerSeries.C ε * U) := by
    rw [← hH1, hS]; exact (geom_sum_mul H n).symm
  obtain ⟨R2, hR2⟩ : ∃ R2 : PowerSeries A, H * S = PowerSeries.C (n : A) + PowerSeries.C ε * R2 :=
    ⟨PowerSeries.C (n : A) * U + R + PowerSeries.C ε * U * R, by rw [hH, hR]; ring⟩
  have hshift : PowerSeries.X * (H ^ (n + 1) - H) =
      PowerSeries.C ε * (PowerSeries.C (n : A) * (PowerSeries.X * U)) +
        PowerSeries.C ε * (PowerSeries.C ε * (PowerSeries.X * U * R2)) := by
    have e1 : PowerSeries.X * (H ^ (n + 1) - H) = PowerSeries.X * (H * (H ^ n - 1)) := by ring
    rw [e1, hgeom]
    linear_combination (PowerSeries.X * PowerSeries.C ε * U) * hR2
  have hdec := clippedOp_decomp M ε g δ G C a b e hG hC hba
  have hQ1 : clippedOp M G C 1 = 0 := clippedOp_one' M G C hdegG hdegC
  have hQH : clippedOp M G C H = Polynomial.C ε ^ 2 *
      (clippedOp M g δ U + Polynomial.C ε * (clippedOp M g e U + clippedOp M a b U)) := by
    rw [hH, clippedOp_add', clippedOp_C_mul', hQ1, zero_add, hdec]; ring
  have hshiftQ : clippedOp M G C (PowerSeries.X * H) = Polynomial.X * clippedOp M G C H := by
    have h0 : clippedOp M G C (PowerSeries.X * H) - Polynomial.X * clippedOp M G C H = 0 := by
      rw [clippedOp_X_mul M hM G C H, hrowG, hrowC]; simp
    linear_combination h0
  obtain ⟨Zp, hZp⟩ : ∃ Zp : Polynomial A, Zp =
      Polynomial.C (n : A) * (clippedOp M g e (PowerSeries.X * U) +
        clippedOp M a b (PowerSeries.X * U)) +
      (clippedOp M g δ (PowerSeries.X * U * R2) + Polynomial.C ε *
        (clippedOp M g e (PowerSeries.X * U * R2) + clippedOp M a b (PowerSeries.X * U * R2))) :=
    ⟨_, rfl⟩
  have hQX : clippedOp M G C (PowerSeries.X * H ^ (n + 1)) =
      Polynomial.C ε ^ 2 * (Polynomial.C (n : A) * clippedOp M g δ (PowerSeries.X * U)) +
        Polynomial.C ε ^ 3 * Zp + Polynomial.X * clippedOp M G C H := by
    have e2 : PowerSeries.X * H ^ (n + 1) =
        PowerSeries.X * (H ^ (n + 1) - H) + PowerSeries.X * H := by ring
    rw [e2, clippedOp_add', hshift, clippedOp_add', clippedOp_C_mul', clippedOp_C_mul',
      clippedOp_C_mul', clippedOp_C_mul', hshiftQ, hdec (PowerSeries.X * U),
      hdec (PowerSeries.X * U * R2), hZp]
    ring
  obtain ⟨P, hP⟩ : ∃ P : Polynomial A, P =
      clippedOp M g δ U + Polynomial.C ε * (clippedOp M g e U + clippedOp M a b U) := ⟨_, rfl⟩
  rw [← hP] at hQH
  have hser : (((clippedOp M G C (PowerSeries.X * H ^ (n + 1)) : Polynomial A) : PowerSeries A) -
      PowerSeries.X * ((clippedOp M G C H : Polynomial A) : PowerSeries A) * H ^ n) =
      PowerSeries.C (ε ^ 2 * (n : A)) * ((clippedOp M g δ (PowerSeries.X * U) : Polynomial A) :
        PowerSeries A) +
      PowerSeries.C (ε ^ 3) *
        ((Zp : PowerSeries A) - PowerSeries.X * (P : PowerSeries A) * U * S) := by
    rw [hQX, hQH]
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C,
      Polynomial.coe_X, map_mul, map_pow]
    linear_combination (-(PowerSeries.X * PowerSeries.C ε ^ 2 * (P : PowerSeries A))) * hgeom
  intro k hk
  have h := hPE k hk
  rw [hser, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, Polynomial.coeff_coe] at h
  exact ⟨-(PowerSeries.coeff k ((Zp : PowerSeries A) -
    PowerSeries.X * (P : PowerSeries A) * U * S)), by linear_combination h⟩

end SkewCoframeRigidity.UnitCase
