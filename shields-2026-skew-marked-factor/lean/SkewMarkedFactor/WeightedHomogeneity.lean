/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.WeightedOperator
import SkewMarkedFactor.CharacterExpansion
import SkewMarkedFactor.TriangularReadout

/-!
# Weighted degree of the weighted derivation

«The algebra map and the weighted operator» (`eq:weighted-operator`) of
`shields-2026-skew-marked-factor.tex`.
`V_k` lowers the weighted degree by `k`, and kills every function of degree below `k`.  Hence the
mixed operator `B_k = p V_k + ρ δ_k` does as well, and the homogeneous functions of degree one
are the multiples of `h_1`.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

theorem weight_sub_single (d : ℕ+ →₀ ℕ) (i : ℕ+) (hi : i ∈ d.support) :
    Finsupp.weight degWeight d = Finsupp.weight degWeight (d - Finsupp.single i 1) + (i : ℕ) := by
  have h1 : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have h2 : Finsupp.single i 1 ≤ d := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using h1
    · simp [Finsupp.single_apply, Ne.symm hj]
  have h3 : d = (d - Finsupp.single i 1) + Finsupp.single i 1 := (tsub_add_cancel_of_le h2).symm
  conv_lhs => rw [h3]
  rw [map_add]
  simp [Finsupp.weight_apply, Finsupp.sum_single_index, degWeight]

/-- One term of `V_k` on a monomial of weight `a`. -/
theorem wDeriv_term {k a : ℕ} (d : ℕ+ →₀ ℕ) (hd : Finsupp.weight degWeight d = a) (i : ℕ+)
    (hi : i ∈ d.support) :
    (monomial (d - Finsupp.single i 1) ((d i : ℕ) : ℚ) *
        (C (((i : ℕ) : ℚ) - k) * hh ((i : ℤ) - k)) : Lambda) = 0 ∨
      ((k : ℕ) < (i : ℕ) ∧ (i : ℕ) ≤ a ∧
        IsWeightedHomogeneous degWeight
          (monomial (d - Finsupp.single i 1) ((d i : ℕ) : ℚ) *
            (C (((i : ℕ) : ℚ) - k) * hh ((i : ℤ) - k)) : Lambda) (a - k)) := by
  have hw := weight_sub_single d i hi
  have hia : (i : ℕ) ≤ a := by omega
  rcases lt_trichotomy (i : ℕ) k with h | h | h
  · left
    have : hh ((i : ℤ) - k) = 0 := hh_of_neg (by omega)
    simp [this]
  · left
    have : ((i : ℕ) : ℚ) - k = 0 := by rw [h]; simp
    simp [this]
  · right
    refine ⟨h, hia, ?_⟩
    have hhh : hh ((i : ℤ) - k) = X (⟨(i : ℕ) - k, by omega⟩ : ℕ+) := by
      have e : ((i : ℤ) - k) = (((i : ℕ) - k : ℕ) : ℤ) := by omega
      have h1 := hPos_pnat (⟨(i : ℕ) - k, by omega⟩ : ℕ+)
      simp only [PNat.mk_coe] at h1
      rw [e, hh_natCast, h1]; rfl
    rw [hhh]
    have h1 : IsWeightedHomogeneous degWeight
        (monomial (d - Finsupp.single i 1) ((d i : ℕ) : ℚ)) (a - (i : ℕ)) :=
      isWeightedHomogeneous_monomial _ _ _ (by omega)
    have h2 : IsWeightedHomogeneous degWeight
        (C (((i : ℕ) : ℚ) - k) * X (⟨(i : ℕ) - k, by omega⟩ : ℕ+) : Lambda) ((i : ℕ) - k) := by
      refine (isWeightedHomogeneous_X ℚ degWeight (⟨(i : ℕ) - k, by omega⟩ : ℕ+)).C_mul _
    have := h1.mul h2
    have e : a - (i : ℕ) + ((i : ℕ) - k) = a - k := by omega
    rw [e] at this
    exact this

/-- `V_k` on a monomial of weight `a`: every term has weight `a - k`, and the whole is zero when
`a < k`. -/
theorem wDeriv_monomial {k a : ℕ} (d : ℕ+ →₀ ℕ) (c : ℚ) (hd : Finsupp.weight degWeight d = a) :
    IsWeightedHomogeneous degWeight (wDeriv k (monomial d c)) (a - k) ∧
      (a < k → wDeriv k (monomial d c) = 0) := by
  classical
  unfold wDeriv
  rw [MvPolynomial.mkDerivation_monomial]
  have hsum : (d.sum fun i m => (monomial (d - Finsupp.single i 1) (m : ℚ)) •
      (C (((i : ℕ) : ℚ) - k) * hh ((i : ℤ) - k) : Lambda)) =
      ∑ i ∈ d.support, (monomial (d - Finsupp.single i 1) ((d i : ℕ) : ℚ) *
        (C (((i : ℕ) : ℚ) - k) * hh ((i : ℤ) - k)) : Lambda) := by
    simp only [Finsupp.sum, smul_eq_mul]
  rw [hsum]
  constructor
  · rw [MvPolynomial.smul_eq_C_mul]
    refine IsWeightedHomogeneous.C_mul ?_ c
    refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
    rcases wDeriv_term (k := k) d hd i hi with h | ⟨-, -, h⟩
    · rw [h]; exact (isWeightedHomogeneous_zero ℚ (degWeight : ℕ+ → ℕ) _)
    · exact h
  · intro hak
    rw [Finset.sum_eq_zero, smul_zero]
    intro i hi
    rcases wDeriv_term (k := k) d hd i hi with h | ⟨h1, h2, -⟩
    · exact h
    · omega


theorem wDeriv_homogeneous {k a : ℕ} {f : Lambda} (hf : IsWeightedHomogeneous degWeight f a) :
    IsWeightedHomogeneous degWeight (wDeriv k f) (a - k) ∧ (a < k → wDeriv k f = 0) := by
  classical
  have hmono : f = ∑ d ∈ f.support, monomial d (f.coeff d) := MvPolynomial.as_sum f
  have hd : ∀ d ∈ f.support, Finsupp.weight degWeight d = a := fun d hd =>
    hf (MvPolynomial.mem_support_iff.mp hd)
  constructor
  · rw [hmono, map_sum]
    exact IsWeightedHomogeneous.sum _ _ _ fun d hdm => (wDeriv_monomial d _ (hd d hdm)).1
  · intro hak
    rw [hmono, map_sum]
    exact Finset.sum_eq_zero fun d hdm => (wDeriv_monomial d _ (hd d hdm)).2 hak

theorem mixedOp_homogeneous (p ρ : ℚ) {k a : ℕ} (hk : 0 < k) {f : Lambda}
    (hf : IsWeightedHomogeneous degWeight f a) :
    IsWeightedHomogeneous degWeight (mixedOp p ρ k f) (a - k) ∧
      (a < k → mixedOp p ρ k f = 0) := by
  obtain ⟨h1, h2⟩ := wDeriv_homogeneous (k := k) hf
  have h3 := homogeneous_pDeriv hf hk
  have h4 := pDeriv_eq_zero_of_weight_lt (k := k) hf
  rw [mixedOp_apply]
  refine ⟨(h1.C_mul p).add (h3.C_mul ρ), fun hak => ?_⟩
  rw [h2 hak, h4 hak]; simp

/-- The word `B_{w₁}` first, then `B_{w₂}`, … lowers the weight by the sum of its parts. -/
theorem mixedWord_homogeneous (p ρ : ℚ) : ∀ (w : List ℕ) {a : ℕ} {f : Lambda},
    (∀ x ∈ w, 0 < x) → IsWeightedHomogeneous degWeight f a →
    IsWeightedHomogeneous degWeight (mixedWord p ρ w f) (a - w.sum) ∧
      (a < w.sum → mixedWord p ρ w f = 0)
  | [], a, f, _, hf => ⟨by simpa [mixedWord] using hf, fun h => by simp at h⟩
  | x :: w, a, f, hw, hf => by
    have hx := hw x (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := mixedOp_homogeneous p ρ hx hf
    obtain ⟨h3, h4⟩ := mixedWord_homogeneous p ρ w (fun y hy => hw y (List.mem_cons_of_mem _ hy)) h1
    rw [mixedWord_cons]
    refine ⟨by simpa [List.sum_cons, Nat.sub_sub, add_comm] using h3, fun hlt => ?_⟩
    by_cases hax : a < x
    · rw [h2 hax]; simp
    · apply h4
      simp only [List.sum_cons] at hlt
      omega

end SkewMarkedFactor
