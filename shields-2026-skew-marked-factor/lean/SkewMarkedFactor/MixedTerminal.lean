/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.WeightedOperator

/-!
# Terminal evaluation of the mixed operator

«Recovering mixed ribbon factors» (`sec:mixed-extraction`,
`eq:mixed-terminal-evaluation`) of `shields-2026-skew-marked-factor.tex`.
For a homogeneous symmetric function `Q` of weight `m`, the `m`-fold iterate of
`B₁ = p V₁ + ρ δ₁` is the constant `m! p^m Q(1^{ρ/p})`, where `Q(1^x)` is the
specialization `p_j ↦ x` in the power-sum coordinates.
The proof uses the general Leibniz rule for the iterates of the derivation `B₁`
and the explicit action of `B₁` on the Newton power sums.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial Finset

/-- The general Leibniz rule for the iterates of a derivation. -/
theorem derivation_iterate_mul (D : Derivation ℚ Lambda Lambda) (n : ℕ) (f g : Lambda) :
    D^[n] (f * g) =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • (D^[ij.1] f * D^[ij.2] g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := Lambda)
      (fun i j => D^[i] f * D^[j] g) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, Derivation.leibniz,
      smul_eq_mul, smul_add, sum_add_distrib]
    refine congrArg₂ _ (sum_congr rfl fun ⟨i, j⟩ hij => ?_) (sum_congr rfl fun ⟨i, j⟩ hij => ?_)
    · simp only [nsmul_eq_mul]; try ring
    · rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]
      simp only [nsmul_eq_mul]; ring

/-- The action of `B_k` on the Newton power sums. -/
theorem mixedOp_pPoly (p ρ : ℚ) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    mixedOp p ρ k (pPoly j) =
      if k < j then C (p * j) * pPoly (j - k)
      else if k = j then C (ρ * k) else 0 := by
  rw [mixedOp_apply, wDeriv_pPoly, pDeriv_pPoly hk]
  by_cases h1 : k < j
  · have : ¬ k = j := by omega
    simp [h1, this, mul_assoc]
  · by_cases h2 : k = j
    · subst h2; simp [mul_comm]
    · simp [h1, h2]

variable (p ρ : ℚ)

/-- The iterates of `B₁` on a power sum below its own weight. -/
theorem iterate_mixedOp_pPoly_lt {j : ℕ} :
    ∀ i, i < j → (mixedOp p ρ 1)^[i] (pPoly j) =
      C (p ^ i * (j.descFactorial i : ℚ)) * pPoly (j - i)
  | 0, _ => by simp
  | i + 1, hi => by
    have ih := iterate_mixedOp_pPoly_lt (j := j) i (by omega)
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz]
    have h0 : mixedOp p ρ 1 (C (p ^ i * (j.descFactorial i : ℚ)) : Lambda) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
    have h1 : 1 < j - i := by omega
    rw [mixedOp_pPoly p ρ one_pos, ite_eq_left h1, h0]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rw [show j - i - 1 = j - (i + 1) by omega, Nat.descFactorial_succ, ← mul_assoc,
      ← map_mul]
    congr 2
    rw [Nat.cast_mul]
    ring

/-- The statement that the `b`-fold iterate of `B₁` is the constant `b! p^b v`. -/
abbrev Terminal (R : Lambda) (b : ℕ) (v : ℚ) : Prop :=
  (mixedOp p ρ 1)^[b] R = C ((b.factorial : ℚ) * p ^ b * v)

variable {p ρ}

theorem iterate_mixedOp_const (c : ℚ) {t : ℕ} (ht : 0 < t) :
    (mixedOp p ρ 1)^[t] (C c : Lambda) = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  have h0 : mixedOp p ρ 1 (C c : Lambda) = 0 := by
    rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
  rw [h0]
  clear ht
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, map_zero]; exact ih

theorem Terminal.vanish {R : Lambda} {b : ℕ} {v : ℚ} (h : Terminal p ρ R b v) {i : ℕ}
    (hi : b < i) : (mixedOp p ρ 1)^[i] R = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, i = t + b := ⟨i - b, by omega⟩
  rw [Function.iterate_add_apply, h]
  exact iterate_mixedOp_const _ (by omega)

theorem Terminal.mul {R S : Lambda} {a b : ℕ} {u v : ℚ} (hR : Terminal p ρ R a u)
    (hS : Terminal p ρ S b v) : Terminal p ρ (R * S) (a + b) (u * v) := by
  unfold Terminal
  rw [derivation_iterate_mul]
  rw [sum_eq_single (a, b)]
  · simp only [nsmul_eq_mul]
    rw [hR, hS,
      ← map_mul, ← map_natCast (C : ℚ →+* Lambda), ← map_mul]
    congr 1
    have : ((a + b).choose a : ℚ) * a.factorial * b.factorial = (a + b).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
      rw [Nat.add_sub_cancel_left] at this
      exact_mod_cast this
    rw [pow_add, ← this]
    ring
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    simp only [nsmul_eq_mul]
    rcases lt_trichotomy i a with h | h | h
    · rw [show (mixedOp p ρ 1)^[j] S = 0 from hS.vanish (by simp at hij; omega)]; simp
    · exfalso; apply hne; ext <;> simp at hij ⊢ <;> omega
    · rw [show (mixedOp p ρ 1)^[i] R = 0 from hR.vanish h]; simp
  · intro h; exfalso; apply h; simp

theorem Terminal.pow {R : Lambda} {b : ℕ} {v : ℚ} (h : Terminal p ρ R b v) (n : ℕ) :
    Terminal p ρ (R ^ n) (n * b) (v ^ n) := by
  induction n with
  | zero => simp [Terminal]
  | succ n ih =>
    have := ih.mul h
    rwa [pow_succ, show (n + 1) * b = n * b + b by ring, pow_succ]

theorem Terminal.prod {ι : Type*} (s : Finset ι) (R : ι → Lambda) (b : ι → ℕ) (v : ι → ℚ)
    (h : ∀ i ∈ s, Terminal p ρ (R i) (b i) (v i)) :
    Terminal p ρ (∏ i ∈ s, R i) (∑ i ∈ s, b i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Terminal]
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, prod_insert hi]
    exact (h i (mem_insert_self i s)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

theorem Terminal.add {R S : Lambda} {b : ℕ} {u v : ℚ} (hR : Terminal p ρ R b u)
    (hS : Terminal p ρ S b v) : Terminal p ρ (R + S) b (u + v) := by
  unfold Terminal at *
  rw [iterate_map_add, hR,
    hS, ← map_add]
  congr 1; ring

theorem iterate_mixedOp_smul (c : ℚ) (n : ℕ) (R : Lambda) :
    (mixedOp p ρ 1)^[n] (c • R) = c • (mixedOp p ρ 1)^[n] R := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Derivation.map_smul, ih]

theorem Terminal.smul {R : Lambda} {b : ℕ} {v : ℚ} (h : Terminal p ρ R b v) (c : ℚ) :
    Terminal p ρ (C c * R) b (c * v) := by
  have : (C c : Lambda) * R = c • R := by rw [MvPolynomial.smul_eq_C_mul]
  dsimp only [Terminal] at h ⊢
  rw [this, iterate_mixedOp_smul, h, MvPolynomial.smul_eq_C_mul, ← map_mul]
  congr 1; ring

theorem terminal_pPoly (hp : p ≠ 0) {j : ℕ} (hj : 0 < j) :
    Terminal p ρ (pPoly j) j (ρ / p) := by
  dsimp only [Terminal]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Function.iterate_succ_apply', iterate_mixedOp_pPoly_lt p ρ i (by omega),
    Derivation.leibniz]
  have h0 : mixedOp p ρ 1 (C (p ^ i * ((i + 1).descFactorial i : ℚ)) : Lambda) = 0 := by
    rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
  have e : i + 1 - i = 1 := by omega
  have hd : (i + 1).descFactorial i = (i + 1).factorial := by
    have := Nat.descFactorial_succ (i + 1) i
    rw [Nat.descFactorial_self] at this
    rw [show i + 1 - i = 1 by omega, one_mul] at this
    exact this.symm
  rw [h0, e, mixedOp_pPoly p ρ one_pos]
  simp only [lt_irrefl, ↓reduceIte, smul_eq_mul, mul_zero, add_zero, hd]
  rw [← map_mul]
  congr 1
  push_cast
  field_simp
  ring

theorem Terminal.sum {ι : Type*} (s : Finset ι) (R : ι → Lambda) (b : ℕ) (v : ι → ℚ)
    (h : ∀ i ∈ s, Terminal p ρ (R i) b (v i)) :
    Terminal p ρ (∑ i ∈ s, R i) b (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    dsimp only [Terminal]
    rw [Function.iterate_fixed (map_zero _)]
    simp
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (h i (mem_insert_self i s)).add (ih fun j hj => h j (mem_insert_of_mem hj))

/-- The specialization `Q(1^x)`: `p_j ↦ x` in the power-sum coordinates. -/
def powerSumSpecialize (x : ℚ) (Q : Lambda) : ℚ :=
  aeval (fun _ : ℕ+ => x) (powerSumEquiv.symm Q)

/-- **Terminal evaluation** (`eq:mixed-terminal-evaluation`): for homogeneous `Q` of weight
`m` and a nonzero period `p`, the `m`-fold iterate of `B₁ = p V₁ + ρ δ₁` is the constant
`m! p^m Q(1^{ρ/p})`. -/
theorem mixedOp_iterate_terminal (hp : p ≠ 0) {m : ℕ} {Q : Lambda}
    (hQ : IsWeightedHomogeneous degWeight Q m) :
    (mixedOp p ρ 1)^[m] Q =
      C ((m.factorial : ℚ) * p ^ m * powerSumSpecialize (ρ / p) Q) := by
  have hg := homogeneous_powerSumEquiv_symm hQ
  set g := powerSumEquiv.symm Q with hgdef
  have hQg : Q = powerSumEquiv g := by simp [hgdef]
  have hmono : ∀ d ∈ g.support, Terminal p ρ (powerSumEquiv (MvPolynomial.monomial d (g.coeff d))) m
      (g.coeff d * ∏ k ∈ d.support, (ρ / p) ^ d k) := by
    intro d hd
    have hw := hg (MvPolynomial.mem_support_iff.mp hd)
    rw [MvPolynomial.monomial_eq, map_mul, map_finsuppProd]
    have hsplit : powerSumEquiv (C (g.coeff d)) = C (g.coeff d) := powerSumEquiv.commutes _
    rw [hsplit]
    refine Terminal.smul ?_ _
    have hP := Terminal.prod (p := p) (ρ := ρ) d.support
      (fun k => (pPoly k) ^ d k) (fun k => d k * (k : ℕ)) (fun k => (ρ / p) ^ d k)
      (fun k _ => (terminal_pPoly hp k.pos).pow (d k))
    have hsum : ∑ k ∈ d.support, d k * (k : ℕ) = m := by
      simpa [Finsupp.weight_apply, Finsupp.sum, degWeight, smul_eq_mul] using hw
    rw [hsum] at hP
    simpa [Finsupp.prod, powerSumEquiv_X] using hP
  have hT := Terminal.sum (p := p) (ρ := ρ) g.support
    (fun d => powerSumEquiv (MvPolynomial.monomial d (g.coeff d))) m _ hmono
  rw [← map_sum, ← MvPolynomial.as_sum] at hT
  rw [hQg]
  have hv : powerSumSpecialize (ρ / p) Q = ∑ d ∈ g.support, g.coeff d * ∏ k ∈ d.support,
      (ρ / p) ^ d k := by
    unfold powerSumSpecialize
    rw [← hgdef]
    rw [← MvPolynomial.eval_eq (fun _ : ℕ+ => ρ / p) g]
    rfl
  rw [hv, show powerSumEquiv g = Q from hQg.symm] at *
  exact hT

end SkewMarkedFactor
