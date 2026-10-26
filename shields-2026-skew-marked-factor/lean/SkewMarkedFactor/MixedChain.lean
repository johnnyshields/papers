/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.WeightedHomogeneity
import SkewMarkedFactor.MixedTerminal
import SkewMarkedFactor.ModifiedMap

/-!
# The weighted chain of a covariant parent

«Recovering mixed ribbon factors» (`sec:mixed-extraction`, `eq:mixed-terminal-ratio`,
`rt:outer-triangle`) of `shields-2026-skew-marked-factor.tex`.
Abstract part of the argument: let `Φ` be an algebra map with
`V_{k q} Φ = χ^k Φ ∘ B_k` for all `k ≥ 1`, with `χ` and a normalizer `N` killed by every `V_{k q}`,
and let `N P = Φ s` for a homogeneous `s` of weight `m ≥ 1`.  Then the iterated derivatives of `P`
along `V_q` have terminal order `m`, with penultimate and terminal derivatives in the ratio
`Φ(h_1) / (ρ χ)`, and every word `V_{qν}`, `ν ⊢ m`, is a scalar multiple of the terminal
derivative, with the ratio of the constants `B_ν s`.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

/-- The word `V_{ν₁ q}` first, then `V_{ν₂ q}`, and so on. -/
def wWord (q : ℕ) : List ℕ → Lambda →ₗ[ℚ] Lambda
  | [] => LinearMap.id
  | a :: w => (wWord q w).comp (wDeriv (a * q)).toLinearMap

theorem wWord_cons (q a : ℕ) (w : List ℕ) (f : Lambda) :
    wWord q (a :: w) f = wWord q w (wDeriv (a * q) f) := rfl

theorem wWord_replicate_one (q : ℕ) : ∀ (j : ℕ) (f : Lambda),
    wWord q (List.replicate j 1) f = (wDeriv q)^[j] f
  | 0, f => rfl
  | j + 1, f => by
    rw [List.replicate_succ, wWord_cons, one_mul, Function.iterate_succ_apply]
    exact wWord_replicate_one q j _

theorem mixedWord_replicate_one (p ρ : ℚ) : ∀ (j : ℕ) (f : Lambda),
    mixedWord p ρ (List.replicate j 1) f = (mixedOp p ρ 1)^[j] f
  | 0, f => rfl
  | j + 1, f => by
    rw [List.replicate_succ, mixedWord_cons, Function.iterate_succ_apply]
    exact mixedWord_replicate_one p ρ j _

/-- `c` is killed by every `V_{a q}`, `a ≥ 1`. -/
def VKilled (q : ℕ) (c : Lambda) : Prop := ∀ a : ℕ, 0 < a → wDeriv (a * q) c = 0

theorem VKilled.mul {q : ℕ} {c d : Lambda} (hc : VKilled q c) (hd : VKilled q d) :
    VKilled q (c * d) := fun a ha => by
  rw [Derivation.leibniz, hc a ha, hd a ha]; simp

theorem VKilled.pow {q : ℕ} {c : Lambda} (hc : VKilled q c) (n : ℕ) : VKilled q (c ^ n) :=
  fun a ha => by rw [Derivation.leibniz_pow, hc a ha]; simp

theorem VKilled.one (q : ℕ) : VKilled q 1 := fun a _ => Derivation.map_one_eq_zero _

theorem VKilled.neg_one_pow (q n : ℕ) : VKilled q ((-1 : Lambda) ^ n) :=
  fun a _ => wDeriv_neg_one_pow _ _

theorem VKilled.C (q : ℕ) (c : ℚ) : VKilled q (MvPolynomial.C c : Lambda) := fun a _ => by
  rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _

theorem compositionMap_C' (Φ : Lambda →ₐ[ℚ] Lambda) (q : ℚ) :
    Φ (MvPolynomial.C q) = MvPolynomial.C q := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

/-- **Iterated covariance.**  If `N P = c Φ g` with `N` and `c` killed, then
`N V_{qν} P = c χ^{|ν|} Φ(B_ν g)`. -/
theorem wWord_cov (q : ℕ) (p ρ : ℚ) (Φ : Lambda →ₐ[ℚ] Lambda) (χ N : Lambda)
    (hχ : VKilled q χ) (hN : VKilled q N)
    (hcov : ∀ k : ℕ, 1 ≤ k → ∀ f : Lambda,
      wDeriv (k * q) (Φ f) = χ ^ k * Φ (mixedOp p ρ k f)) :
    ∀ (ν : List ℕ), (∀ a ∈ ν, 0 < a) → ∀ (g P c : Lambda), VKilled q c → N * P = c * Φ g →
      N * wWord q ν P = c * χ ^ ν.sum * Φ (mixedWord p ρ ν g)
  | [], _, g, P, c, _, h => by simpa [wWord, mixedWord] using h
  | a :: ν, hν, g, P, c, hc, h => by
    have ha : 0 < a := hν a (List.mem_cons_self ..)
    have hν' : ∀ b ∈ ν, 0 < b := fun b hb => hν b (List.mem_cons_of_mem _ hb)
    have h1 : N * wDeriv (a * q) P = (c * χ ^ a) * Φ (mixedOp p ρ a g) := by
      have e1 : N * wDeriv (a * q) P = wDeriv (a * q) (N * P) := by
        rw [Derivation.leibniz, hN a ha]; simp
      rw [e1, h, Derivation.leibniz, hc a ha, hcov a ha]
      simp only [smul_zero, add_zero, smul_eq_mul]
      ring
    have := wWord_cov q p ρ Φ χ N hχ hN hcov ν hν' (mixedOp p ρ a g) (wDeriv (a * q) P)
      (c * χ ^ a) (hc.mul (hχ.pow a)) h1
    rw [wWord_cons, mixedWord_cons, this, List.sum_cons, pow_add]
    ring

/-- Two homogeneous coefficients: a homogeneous function of weight one is a multiple of `h₁`. -/
theorem homogeneous_one {f : Lambda} (hf : IsWeightedHomogeneous degWeight f 1) :
    ∃ c : ℚ, f = C c * hPos 1 := by
  classical
  refine ⟨f.coeff (Finsupp.single 1 1), ?_⟩
  have h1 : hPos 1 = (X 1 : Lambda) := hPos_pnat 1
  rw [h1]
  ext d
  rw [coeff_C_mul, coeff_X']
  by_cases hd : d = Finsupp.single 1 1
  · subst hd; simp
  · rw [if_neg (Ne.symm hd), mul_zero]
    by_contra hne
    have hw : Finsupp.weight degWeight d = 1 := hf hne
    apply hd
    have h1 : ∀ j : ℕ+, j ≠ 1 → d j = 0 := by
      intro j hj
      by_contra hdj
      have := Finsupp.le_weight_of_ne_zero' (w := degWeight) hdj
      rw [hw] at this
      have hj2 : 2 ≤ (j : ℕ) := by
        have := j.pos
        have : (j : ℕ) ≠ 1 := fun h => hj (PNat.coe_eq_one_iff.mp h)
        omega
      simp only [degWeight] at this
      omega
    have h2 : d 1 = 1 := by
      have hle := Finsupp.le_weight degWeight (s := (1 : ℕ+)) (by simp [degWeight]) d
      rw [hw] at hle
      have hne1 : d 1 ≠ 0 := by
        intro h0
        have hd0 : d = 0 := by
          ext j
          by_cases hj : j = 1
          · subst hj; simpa using h0
          · simp [h1 j hj]
        rw [hd0, map_zero] at hw
        exact zero_ne_one hw
      omega
    ext j
    by_cases hj : j = 1
    · subst hj; simp [h2]
    · simp [h1 j hj, Finsupp.single_apply, Ne.symm hj]


theorem Phi_const (Φ : Lambda →ₐ[ℚ] Lambda) (q : ℚ) : Φ (C q) = C q := compositionMap_C' Φ q

theorem derivation_iterate_zero (D : Derivation ℚ Lambda Lambda) : ∀ j : ℕ, D^[j] (0 : Lambda) = 0
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply, Derivation.map_zero, derivation_iterate_zero D j]

theorem derivation_iterate_const (D : Derivation ℚ Lambda Lambda) (q : ℚ) :
    ∀ j : ℕ, 0 < j → D^[j] (C q) = 0
  | 0, h => absurd h (lt_irrefl _)
  | j + 1, _ => by
    rw [Function.iterate_succ_apply]
    have : D (C q) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
    rw [this]
    exact derivation_iterate_zero D j

/-- **The weighted chain of a covariant parent** (`eq:mixed-terminal-ratio`, `rt:outer-triangle`):
terminal order `m`, penultimate-to-terminal ratio, and the word quotients. -/
theorem weighted_chain (q : ℕ) (p ρ : ℚ) (hp : p ≠ 0) (hρ : ρ ≠ 0)
    (Φ : Lambda →ₐ[ℚ] Lambda) (χ N : Lambda) (hχ : VKilled q χ) (hN : VKilled q N)
    (hN0 : N ≠ 0) (hχ0 : χ ≠ 0)
    (hcov : ∀ k : ℕ, 1 ≤ k → ∀ f : Lambda,
      wDeriv (k * q) (Φ f) = χ ^ k * Φ (mixedOp p ρ k f))
    (P s : Lambda) {m : ℕ} (hm : 1 ≤ m) (hs : IsWeightedHomogeneous degWeight s m)
    (hκ : powerSumSpecialize (ρ / p) s ≠ 0) (hNP : N * P = Φ s) :
    ∃ κ : ℚ, κ ≠ 0 ∧ mixedWord p ρ (List.replicate m 1) s = C κ ∧
      (wDeriv q)^[m] P ≠ 0 ∧ (∀ j, m < j → (wDeriv q)^[j] P = 0) ∧
      (wDeriv q)^[m - 1] P * (C ρ * χ) = (wDeriv q)^[m] P * Φ (hPos 1) ∧
      ∀ ν : List ℕ, (∀ a ∈ ν, 0 < a) → ν.sum = m → ∃ c : ℚ,
        mixedWord p ρ ν s = C c ∧
        C κ * wWord q ν P = C c * (wDeriv q)^[m] P := by
  have hcovW := wWord_cov q p ρ Φ χ N hχ hN hcov
  have hc1 : ∀ j : ℕ, N * (wDeriv q)^[j] P =
      χ ^ j * Φ (mixedWord p ρ (List.replicate j 1) s) := by
    intro j
    have := hcovW (List.replicate j 1) (fun a ha => by rw [List.eq_of_mem_replicate ha]; omega)
      s P 1 (VKilled.one q) (by rw [hNP, one_mul])
    rw [wWord_replicate_one, one_mul, List.sum_replicate, smul_eq_mul, mul_one] at this
    exact this
  have hB := mixedOp_iterate_terminal (ρ := ρ) hp hs
  have hBm : mixedWord p ρ (List.replicate m 1) s =
      C ((m.factorial : ℚ) * p ^ m * powerSumSpecialize (ρ / p) s) := by
    rw [mixedWord_replicate_one]; exact hB
  set κ : ℚ := (m.factorial : ℚ) * p ^ m * powerSumSpecialize (ρ / p) s with hκdef
  have hκ0 : κ ≠ 0 := by
    have : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    exact mul_ne_zero (mul_ne_zero this (pow_ne_zero _ hp)) hκ
  have hCκ : (C κ : Lambda) ≠ 0 := fun h => hκ0 (MvPolynomial.C_injective _ _ (h.trans (map_zero C).symm))
  have hVm : N * (wDeriv q)^[m] P = χ ^ m * C κ := by rw [hc1, hBm, Phi_const]
  have hVm0 : (wDeriv q)^[m] P ≠ 0 := by
    intro h
    rw [h, mul_zero] at hVm
    exact mul_ne_zero (pow_ne_zero _ hχ0) hCκ hVm.symm
  have hVm1 : (wDeriv q)^[m + 1] P = 0 := by
    have h0 : mixedWord p ρ (List.replicate (m + 1) 1) s = 0 := by
      rw [mixedWord_replicate_one, Function.iterate_succ_apply', ← mixedWord_replicate_one, hBm]
      rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
    have := hc1 (m + 1)
    rw [h0, map_zero, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hN0
  refine ⟨κ, hκ0, hBm, hVm0, fun j hj => ?_, ?_, ?_⟩
  · have : j = (j - (m + 1)) + (m + 1) := by omega
    rw [this, Function.iterate_add_apply, hVm1, derivation_iterate_zero]
  · -- the penultimate ratio
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hw1 : IsWeightedHomogeneous degWeight (mixedWord p ρ (List.replicate m' 1) s) 1 := by
      have := (mixedWord_homogeneous p ρ (List.replicate m' 1)
        (fun x hx => by rw [List.eq_of_mem_replicate hx]; omega) hs).1
      simpa [List.sum_replicate] using this
    obtain ⟨c, hcdef⟩ := homogeneous_one hw1
    have hstep : mixedWord p ρ (List.replicate (m' + 1) 1) s = C (c * ρ) := by
      rw [mixedWord_replicate_one, Function.iterate_succ_apply', ← mixedWord_replicate_one,
        hcdef, Derivation.leibniz, mixedOp_hPos _ _ one_pos]
      have hc0 : mixedOp p ρ 1 (C c : Lambda) = 0 := by
        rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
      rw [hc0]
      simp only [le_refl, if_true, Nat.sub_self, hPos_zero, mul_one, smul_eq_mul, smul_zero,
        add_zero, Nat.cast_one, sub_self, mul_zero, zero_add, map_mul]
    have hκc : κ = c * ρ := by
      have := hBm.symm.trans hstep
      exact MvPolynomial.C_injective _ _ this
    have hN1 : N * (wDeriv q)^[m'] P = χ ^ m' * (C c * Φ (hPos 1)) := by
      rw [hc1, hcdef, map_mul, Phi_const]
    apply mul_left_cancel₀ hN0
    calc N * ((wDeriv q)^[m'] P * (C ρ * χ))
        = (N * (wDeriv q)^[m'] P) * (C ρ * χ) := by ring
      _ = χ ^ (m' + 1) * (C (c * ρ) * Φ (hPos 1)) := by rw [hN1, map_mul]; ring
      _ = (N * (wDeriv q)^[m' + 1] P) * Φ (hPos 1) := by rw [hVm, hκc]; ring
      _ = N * ((wDeriv q)^[m' + 1] P * Φ (hPos 1)) := by ring
  · intro ν hν hsum
    obtain ⟨hh1, -⟩ := mixedWord_homogeneous p ρ ν hν hs
    rw [hsum, Nat.sub_self] at hh1
    have hc := homogeneous_zero_eq_C hh1
    refine ⟨_, hc, ?_⟩
    have h2 := hcovW ν hν s P 1 (VKilled.one q) (by rw [hNP, one_mul])
    rw [hsum, hc, Phi_const, one_mul] at h2
    apply mul_left_cancel₀ hN0
    calc N * (C κ * wWord q ν P) = C κ * (N * wWord q ν P) := by ring
      _ = C κ * (χ ^ m * C ((mixedWord p ρ ν s).coeff 0)) := by rw [h2]
      _ = C ((mixedWord p ρ ν s).coeff 0) * (N * (wDeriv q)^[m] P) := by rw [hVm]; ring
      _ = N * (C ((mixedWord p ρ ν s).coeff 0) * (wDeriv q)^[m] P) := by ring

end SkewMarkedFactor
