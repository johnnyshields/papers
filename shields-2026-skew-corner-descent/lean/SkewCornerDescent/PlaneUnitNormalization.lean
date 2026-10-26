/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularProductUnits

/-!
# The rational leading unit equals the original monic-product unit

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Exact full monic factors determine
which scalar survives the cleared rational-plane equation.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

variable {k σ : Type*} [Field k] [LinearOrder σ]

/-- Monic full-response products identify the rational leading scalar with the original unit.
**Differs from the paper's route.** Unique full monic representatives of normalized
prime factors replace a multivariate leading-term comparison. -/
theorem planeFactor_unit_normalization {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (J : ι → σ) (B : ι → MvPolynomial σ k) (L : κ → σ) (D : κ → MvPolynomial σ k)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (hD : ∀ i ∈ t, ∀ j ∈ (D i).vars, j < L i)
    {K J₀ L₀ : σ} (hJ : J₀ < K) (hL : L₀ < K)
    {A B₀ D₀ c : MvPolynomial σ k} (hA : ∀ j ∈ A.vars, j < K)
    (hB₀ : ∀ j ∈ B₀.vars, j < J₀) (hD₀ : ∀ j ∈ D₀.vars, j < L₀)
    (hc : IsUnit c) {p q : Polynomial k} (hp : p.Splits) (hq : q.Splits)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (v b d : ℕ)
    (heq : let F := (X J₀ + B₀) * (X L₀ + D₀)
      triangularPlanePolynomial K p A F *
          ((∏ i ∈ t, (X (L i) + D i)) ^ b * F ^ (q.natDegree + d)) =
        c * triangularPlanePolynomial K q A F *
          ((∏ i ∈ s, (X (J i) + B i)) ^ v * F ^ p.natDegree)) :
    c = C (p.leadingCoeff / q.leadingCoeff) := by
  classical
  let U := s.val.map (fun i => X (J i) + B i)
  let W := t.val.map (fun i => X (L i) + D i)
  let caps : Multiset (MvPolynomial σ k) := {X J₀ + B₀, X L₀ + D₀}
  let F := (X J₀ + B₀) * (X L₀ + D₀)
  let roots (r : Polynomial k) := r.roots.map (fun α => X K + (A - C α * F))
  let S := roots p + b • W + (q.natDegree + d) • caps
  let T := roots q + v • U + p.natDegree • caps
  let Good (z : MvPolynomial σ k) := ∃ H E, (∀ i ∈ E.vars, i < H) ∧ z = X H + E
  have hF : ∀ j ∈ F.vars, j < K := by
    intro j hj
    rcases Finset.mem_union.mp (vars_mul _ _ hj) with h | h
    · exact monicTriangularPolynomial_vars_below hJ hB₀ j h
    · exact monicTriangularPolynomial_vars_below hL hD₀ j h
  have hcaps : ∀ z ∈ caps, Good z := by
    intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, caps] at hz
    rcases hz with rfl | rfl
    · exact ⟨J₀, B₀, hB₀, rfl⟩
    · exact ⟨L₀, D₀, hD₀, rfl⟩
  have hU : ∀ z ∈ U, Good z := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hz
    exact ⟨J i, B i, hB i hi, rfl⟩
  have hW : ∀ z ∈ W, Good z := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hz
    exact ⟨L i, D i, hD i hi, rfl⟩
  have hcombined (r : Polynomial k) (w : Multiset (MvPolynomial σ k))
      (hw : ∀ z ∈ w, Good z) (n m : ℕ) :
      ∀ z ∈ roots r + n • w + m • caps, Good z := by
    intro z hz
    rcases Multiset.mem_add.mp hz with hz | hz
    · rcases Multiset.mem_add.mp hz with hr | hn
      · obtain ⟨α, _, rfl⟩ := Multiset.mem_map.mp hr
        exact ⟨K, A - C α * F, triangularPlaneRoot_lower hA hF α, rfl⟩
      · exact hw z (Multiset.mem_of_mem_nsmul hn)
    · exact hcaps z (Multiset.mem_of_mem_nsmul hz)
  have hpLC := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hqLC := Polynomial.leadingCoeff_ne_zero.mpr hq0
  have hup : IsUnit (C p.leadingCoeff : MvPolynomial σ k) :=
    (isUnit_iff_ne_zero.mpr hpLC).map MvPolynomial.C
  have huq : IsUnit (C q.leadingCoeff : MvPolynomial σ k) :=
    (isUnit_iff_ne_zero.mpr hqLC).map MvPolynomial.C
  have hscalar : C p.leadingCoeff * S.prod = (c * C q.leadingCoeff) * T.prod := by
    change triangularPlanePolynomial K p A F *
      ((∏ i ∈ t, (X (L i) + D i)) ^ b * F ^ (q.natDegree + d)) =
        c * triangularPlanePolynomial K q A F *
          ((∏ i ∈ s, (X (J i) + B i)) ^ v * F ^ p.natDegree) at heq
    rw [triangularPlanePolynomial_roots K p hp A F,
      triangularPlanePolynomial_roots K q hq A F] at heq
    simp only [S, T, Multiset.prod_add, Multiset.prod_nsmul, caps, Multiset.prod_pair]
    change C p.leadingCoeff * ((roots p).prod * W.prod ^ b * F ^ (q.natDegree + d)) =
      (c * C q.leadingCoeff) * ((roots q).prod * U.prod ^ v * F ^ p.natDegree)
    simpa only [roots, U, W, Finset.prod, mul_assoc] using heq
  have hunit := triangularProducts_scalar_eq S T
    (hcombined p W hW b (q.natDegree + d)) (hcombined q U hU v p.natDegree)
    hup (hc.mul huq) hscalar
  calc
    c = (c * C q.leadingCoeff) * C q.leadingCoeff⁻¹ := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hqLC, map_one, mul_one]
    _ = C p.leadingCoeff * C q.leadingCoeff⁻¹ := by rw [← hunit]
    _ = C (p.leadingCoeff / q.leadingCoeff) := by rw [← map_mul, div_eq_mul_inv]

end SkewCornerDescent
