/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.ClippedOperator
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# The degree argument of finite injectivity

Formalizes the second half of the proof of `sc:finite-injectivity` in
`shields-2026-skew-coframe-rigidity.tex`, «The complete unit expansion and finite injectivity»,
over an arbitrary field and an arbitrary series `W` (the letter series `H` or its zero-free
variant `U`).  If `g(0) = 1`, `g` is coprime to the shifted clipped numerator
`[z^a W g]_{<M}`, and `δ` has no constant term and satisfies the row condition
`[W δ]_i = 0` wherever the numerator `[W g]_i` vanishes, then the clipped operator
`g [z^a W δ]_{<M} - δ [z^a W g]_{<M}` vanishes only for `δ = 0`.  Sorry-free.
-/

namespace SkewCoframeRigidity

open PowerSeries Polynomial

variable {F : Type*} [Field F]

/-- The coefficient of the clipped shifted product is the shifted coefficient below the cutoff. -/
theorem coeff_trunc_shift (M a k : ℕ) (W f : F⟦X⟧) :
    (trunc M (PowerSeries.X ^ a * W * f)).coeff (a + k) =
      if a + k < M then PowerSeries.coeff k (W * f) else 0 := by
  rw [coeff_trunc, mul_assoc, PowerSeries.coeff_X_pow_mul']
  by_cases h : a + k < M <;> simp [h]

/-- The shifted clipped numerator vanishes above `a + j` when the numerator vanishes above `j`. -/
theorem coeff_trunc_shift_of_lt (M a k : ℕ) (W f : F⟦X⟧) (h : M ≤ a + k) :
    (trunc M (PowerSeries.X ^ a * W * f)).coeff (a + k) = 0 := by
  simp [coeff_trunc, show ¬ a + k < M by omega]

/-- **Finite injectivity, degree argument** (`sc:finite-injectivity`). -/
theorem eq_zero_of_clippedOp_eq_zero (M a : ℕ) (g δ : F[X]) (W : F⟦X⟧)
    (hg0 : g.coeff 0 = 1) (hδ0 : δ.coeff 0 = 0)
    (hcop : IsCoprime g (trunc M (PowerSeries.X ^ a * W * (g : F⟦X⟧))))
    (hex : ∃ j, a + j < M ∧ PowerSeries.coeff j (W * (g : F⟦X⟧)) ≠ 0)
    (hrow : ∀ i, 0 < i → a + i < M → PowerSeries.coeff i (W * (g : F⟦X⟧)) = 0 →
      PowerSeries.coeff i (W * (δ : F⟦X⟧)) = 0)
    (hT : clippedOp M g δ (PowerSeries.X ^ a * W) = 0) : δ = 0 := by
  classical
  set A := trunc M (PowerSeries.X ^ a * W * (g : F⟦X⟧)) with hA
  set B := trunc M (PowerSeries.X ^ a * W * (δ : F⟦X⟧)) with hB
  have hgne : g ≠ 0 := fun h => by simp [h] at hg0
  have hT' : g * B = δ * A := by
    have : g * B - δ * A = 0 := hT
    exact sub_eq_zero.mp this
  have hdvd : g ∣ δ := by
    have : g ∣ δ * A := ⟨B, hT'.symm⟩
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨R, hR⟩ := hdvd
  have hBR : B = R * A := by
    apply mul_left_cancel₀ hgne
    rw [hT', hR]; ring
  by_contra hδne
  have hRne : R ≠ 0 := fun h => hδne (by simp [hR, h])
  have hR0 : R.coeff 0 = 0 := by
    have := hδ0
    rw [hR, Polynomial.mul_coeff_zero, hg0, one_mul] at this
    exact this
  have he : 1 ≤ R.natDegree := by
    by_contra h
    have h0 : R.natDegree = 0 := by omega
    apply hRne
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hR0]; simp
  -- the largest index with nonzero numerator coefficient
  obtain ⟨j0, hj0a, hj0⟩ := hex
  set j := Nat.findGreatest (fun k => a + k < M ∧ PowerSeries.coeff k (W * (g : F⟦X⟧)) ≠ 0) (M - a)
    with hj
  have hjspec : a + j < M ∧ PowerSeries.coeff j (W * (g : F⟦X⟧)) ≠ 0 :=
    Nat.findGreatest_spec (P := fun k => a + k < M ∧ PowerSeries.coeff k (W * (g : F⟦X⟧)) ≠ 0)
      (show j0 ≤ M - a by omega) ⟨hj0a, hj0⟩
  have hjmax : ∀ k, j < k → a + k < M → PowerSeries.coeff k (W * (g : F⟦X⟧)) = 0 := by
    intro k hk hkM
    by_contra hne
    have := Nat.le_findGreatest (P := fun k => a + k < M ∧ PowerSeries.coeff k (W * (g : F⟦X⟧)) ≠ 0)
      (show k ≤ M - a by omega) ⟨hkM, hne⟩
    omega
  have hAcoef : A.coeff (a + j) ≠ 0 := by
    rw [hA, coeff_trunc_shift]; simpa [hjspec.1] using hjspec.2
  have hAdeg : A.natDegree = a + j := by
    apply le_antisymm
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      by_cases hkM : k < M
      · obtain ⟨k', rfl⟩ : ∃ k', k = a + k' := ⟨k - a, by omega⟩
        rw [hA, coeff_trunc_shift]
        simpa [hkM] using hjmax k' (by omega) hkM
      · simp [hA, coeff_trunc, hkM]
    · exact Polynomial.le_natDegree_of_ne_zero hAcoef
  have hAne : A ≠ 0 := fun h => hAcoef (by simp [h])
  have hlead : (R * A).coeff (R.natDegree + (a + j)) ≠ 0 := by
    rw [← hAdeg, Polynomial.coeff_mul_degree_add_degree]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hRne)
      (Polynomial.leadingCoeff_ne_zero.mpr hAne)
  have hBne : B.coeff (R.natDegree + (a + j)) ≠ 0 := by rw [hBR]; exact hlead
  have hlt : R.natDegree + (a + j) < M := by
    by_contra h
    exact hBne (by simp [hB, coeff_trunc, h])
  have hidx : R.natDegree + (a + j) = a + (j + R.natDegree) := by ring
  rw [hidx] at hBne
  apply hBne
  rw [hB, coeff_trunc_shift]
  have hi := hrow (j + R.natDegree) (by omega) (by omega) (hjmax _ (by omega) (by omega))
  simp [hi]

end SkewCoframeRigidity
