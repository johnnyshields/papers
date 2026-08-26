/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.BesselLaw
import TuranBessel.Phase

/-!
# Microcanonical Bessel fibers

Formalizes `shields-2026-turan-bessel.tex`, «Microcanonical Bessel fibers and
canonical averaging» (`subsec:microcanonical`, `thm:ensemble-hierarchy`,
`eq:pair-total-law`, `eq:microcanonical-schur`, `eq:finite-law-entries`,
`eq:microcanonical-covariance-deficit`, `eq:canonical-fiber-average`).

The pair total `R = Y₁+Y₂` of two independent copies of `eq:bessel-law` has law
`S_mλ^m/Z²` (`pairPMF_eq_conv`, `hasSum_pairPMF`), and dividing by it leaves the
`λ`-free conditional index law `condPMF` of `eq:pair-total-law`.  Both halves are
`lem:convolution`: the numerator sums to `S_m` by the diagonal case, and the
pair law sums to one because `Z²` is that same Cauchy square (`Zseries.Zfun_sq`).

The three entries of the normalized fiber are then fiber moments
(`eq:finite-law-entries`), each closed by a different mechanism:

* `α_m = ½E(Σ_m - Ξ_m²)` is `eq:F-second-delta` divided by `S_m`, so it reuses
  `AlphaCoeff.convolution_second_variation` unchanged.
* `β_m = 1 - ½E(D_mΞ_m)` needs the new closed form `Ifirst_eq_closed` for
  `∑_i i w_i(δ)` — `lem:convolution` at `(α,β) = (a+1+δ, a-δ)` with `m-1` in
  place of `m` — whose `δ`-derivative at the origin is `eq:EDXi`.
* `c_m^{(κ)} = κm/2 - ½E D_m²` needs no calculus at all: `(m-2i)² = m²-4i(m-i)`,
  and canceling `i(m-i)` against the two factorials turns `∑_i i(m-i)w_i` into
  the diagonal convolution at `a+1` and `m-2`, which is `S_{m-2}(a+1)`.

`E Ξ_m = E D_m = 0` comes from the reflection `i ↦ m-i`, under which the weights
are invariant and both variables change sign; regrouping the three entries around
it gives `eq:microcanonical-covariance-deficit`.  Weighting `eq:ABC-expansions` by
the pair law gives `eq:canonical-fiber-average`, whose canonical side is
`BesselLaw.normalizedTuran`.

`eq:microcanonical-schur` is the same three entries as second derivatives of
`ℓ_m = log F_m` at the origin (`NmatKT_eq_ellUV`).  All three reduce to the fiber
moments above: the `u`-slice of `F_m` is `Fdelta` at `δ = u/√2`, the `v`-slice is
a finite exponential sum, and the mixed partial is the `u`-derivative of the
`v`-score `-∑_i D_iw_i(u/√2)/F_m(u/√2)`.  What each needs beyond the moments is
`deriv_deriv_log_eq`, the second logarithmic derivative of a positive function,
which is where the score enters quadratically.

Sorry-free.
-/

open Filter Topology

open scoped BigOperators
open Finset

namespace TuranBessel

variable {a lam : ℝ}

/-! ### The pair total law `eq:pair-total-law` -/

/-- `P_λ(R = m)` for the pair total `R = Y₁+Y₂` (`eq:pair-total-law`). -/
noncomputable def pairPMF (a lam : ℝ) (m : ℕ) : ℝ := sweight a m * lam ^ m / Zfun a lam ^ 2

/-- The unnormalized fiber weight `[i!(m-i)!Γ(a+i)Γ(a+m-i)]⁻¹` of
`eq:pair-total-law`. -/
noncomputable def fibWeight (a : ℝ) (m i : ℕ) : ℝ :=
  1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)
        * Real.Gamma (a + (i : ℝ)) * Real.Gamma (a + ((m - i : ℕ) : ℝ)))

/-- `∑_i w_i = S_m`: the diagonal case of `lem:convolution`. -/
theorem sum_fibWeight (ha : 0 < a) (m : ℕ) :
    ∑ i ∈ range (m + 1), fibWeight a m i = sweight a m := by
  rw [sweight]
  exact gamma_convolution_diag ha m

theorem fibWeight_pos (ha : 0 < a) (m i : ℕ) : 0 < fibWeight a m i := by
  have hGi : 0 < Real.Gamma (a + (i : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hGmi : 0 < Real.Gamma (a + ((m - i : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - i)
  rw [fibWeight]
  positivity

/-- The `λ`-free content of the term product: `z_i z_{m-i} = λ^m w_i`. -/
theorem zterm_mul_eq (a lam : ℝ) {m i : ℕ} (him : i ≤ m) :
    zterm a lam i * zterm a lam (m - i) = lam ^ m * fibWeight a m i := by
  have hpow : lam ^ i * lam ^ (m - i) = lam ^ m := by
    rw [← pow_add, Nat.add_sub_cancel' him]
  simp only [zterm, fibWeight]
  rw [div_mul_div_comm, hpow]
  ring

/-- The Cauchy square of `eq:bessel-law`'s term: `∑_i z_i z_{m-i} = S_m λ^m`. -/
theorem sum_zterm_conv (ha : 0 < a) (lam : ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), zterm a lam i * zterm a lam (m - i) = sweight a m * lam ^ m := by
  have hterm : ∀ i ∈ range (m + 1),
      zterm a lam i * zterm a lam (m - i) = lam ^ m * fibWeight a m i := fun i hi =>
    zterm_mul_eq a lam (Nat.lt_succ_iff.mp (mem_range.mp hi))
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_fibWeight ha]
  ring

/-- **`eq:pair-total-law`, first identity.**  The pair total `R = Y₁+Y₂` of two
independent copies of `eq:bessel-law` has `P_λ(R=m) = S_m λ^m/Z(a,λ)²`. -/
theorem pairPMF_eq_conv (ha : 0 < a) (hlam : 0 ≤ lam) (m : ℕ) :
    ∑ i ∈ range (m + 1), besselPMF a lam i * besselPMF a lam (m - i) = pairPMF a lam m := by
  have hZ := (Zfun_pos ha hlam).ne'
  have hterm : ∀ i ∈ range (m + 1),
      besselPMF a lam i * besselPMF a lam (m - i)
        = (zterm a lam i * zterm a lam (m - i)) / Zfun a lam ^ 2 := by
    intro i _
    rw [besselPMF, besselPMF, div_mul_div_comm, sq]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, sum_zterm_conv ha, pairPMF]

theorem pairPMF_nonneg (ha : 0 < a) (hlam : 0 ≤ lam) (m : ℕ) : 0 ≤ pairPMF a lam m := by
  have hZ := Zfun_pos ha hlam
  rw [pairPMF]
  exact div_nonneg (mul_nonneg (sweight_pos ha m).le (pow_nonneg hlam m)) (by positivity)

/-- **`eq:pair-total-law` is a probability law.**  `∑_m S_m λ^m/Z² = 1`, which is
`Zseries.Zfun_sq`.  Summability comes from that identity itself: a nonsummable
family has `tsum` zero, while `Z² > 0`. -/
theorem hasSum_pairPMF (ha : 0 < a) (hlam : 0 ≤ lam) : HasSum (pairPMF a lam) 1 := by
  have hZ := Zfun_pos ha hlam
  have hsq := Zfun_sq ha lam
  have hsummable : Summable (fun m : ℕ => sweight a m * lam ^ m) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hsq
    exact absurd hsq (pow_ne_zero 2 hZ.ne')
  have h := hsummable.hasSum.div_const (Zfun a lam ^ 2)
  rw [← hsq, div_self (pow_ne_zero 2 hZ.ne')] at h
  exact h

/-! ### The conditional index law -/

/-- `P(I_m = i)` (`eq:pair-total-law`), independent of `λ`. -/
noncomputable def condPMF (a : ℝ) (m i : ℕ) : ℝ := fibWeight a m i / sweight a m

/-- **`eq:pair-total-law`, second identity.**  The conditional law of `Y₁` given
`R = m` is `condPMF`, which carries no `λ`. -/
theorem besselPMF_div_pairPMF (ha : 0 < a) (hlam : 0 < lam) {m i : ℕ} (him : i ≤ m) :
    besselPMF a lam i * besselPMF a lam (m - i) / pairPMF a lam m = condPMF a m i := by
  have hZ : Zfun a lam ≠ 0 := (Zfun_pos ha hlam.le).ne'
  have hS : sweight a m ≠ 0 := (sweight_pos ha m).ne'
  have hpow : lam ^ m ≠ 0 := pow_ne_zero m hlam.ne'
  rw [besselPMF, besselPMF, div_mul_div_comm, ← sq, zterm_mul_eq a lam him, pairPMF, condPMF]
  rw [div_div_div_eq]
  field_simp

theorem condPMF_pos (ha : 0 < a) (m i : ℕ) : 0 < condPMF a m i :=
  div_pos (fibWeight_pos ha m i) (sweight_pos ha m)

/-- The conditional law of `eq:pair-total-law` sums to one, which is
`lem:convolution` again. -/
theorem sum_condPMF (ha : 0 < a) (m : ℕ) : ∑ i ∈ range (m + 1), condPMF a m i = 1 := by
  simp only [condPMF]
  rw [← Finset.sum_div, sum_fibWeight ha, div_self (sweight_pos ha m).ne']

/-- `w_{m-i} = w_i`: the fiber weight is symmetric under `i ↦ m-i`. -/
theorem fibWeight_reflect {m i : ℕ} (him : i ≤ m) :
    fibWeight a m (m - i) = fibWeight a m i := by
  rw [fibWeight, fibWeight, Nat.sub_sub_self him]
  ring

theorem condPMF_reflect {m i : ℕ} (him : i ≤ m) : condPMF a m (m - i) = condPMF a m i := by
  rw [condPMF, condPMF, fibWeight_reflect him]

/-! ### Fiber expectations and the three fiber variables -/

/-- `E f(I_m)` under the conditional law of `eq:pair-total-law`. -/
noncomputable def condExp (a : ℝ) (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (m + 1), f i * condPMF a m i

/-- `D_m = m - 2I_m` (`subsec:microcanonical`). -/
def dfin (m i : ℕ) : ℝ := (m : ℝ) - 2 * (i : ℝ)

/-- `Ξ_m = ψ(a+m-I_m) - ψ(a+I_m)` (`subsec:microcanonical`), the fiber score. -/
noncomputable def xiScore (a : ℝ) (m i : ℕ) : ℝ :=
  realDigamma (a + ((m - i : ℕ) : ℝ)) - realDigamma (a + (i : ℝ))

/-- `Σ_m = ψ₁(a+I_m) + ψ₁(a+m-I_m)` (`subsec:microcanonical`), the fiber
curvature. -/
noncomputable def sigmaCurv (a : ℝ) (m i : ℕ) : ℝ :=
  trigamma (a + (i : ℝ)) + trigamma (a + ((m - i : ℕ) : ℝ))

theorem condExp_const (ha : 0 < a) (m : ℕ) (c : ℝ) :
    condExp a m (fun _ => c) = c := by
  rw [condExp, ← Finset.mul_sum, sum_condPMF ha, mul_one]

theorem condExp_add (a : ℝ) (m : ℕ) (f g : ℕ → ℝ) :
    condExp a m (fun i => f i + g i) = condExp a m f + condExp a m g := by
  rw [condExp, condExp, condExp, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem condExp_smul (a : ℝ) (m : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    condExp a m (fun i => c * f i) = c * condExp a m f := by
  rw [condExp, condExp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Reindexing the fiber expectation by `i ↦ m-i`. -/
theorem condExp_reflect (a : ℝ) (m : ℕ) (f : ℕ → ℝ) :
    condExp a m (fun i => f (m - i)) = condExp a m f := by
  rw [condExp, condExp]
  have h := Finset.sum_range_reflect (fun j => f (m - j) * condPMF a m j) (m + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [Nat.sub_sub_self hjm, condPMF_reflect hjm]

/-- An `i ↦ m-i` antisymmetric variable has fiber mean zero. -/
theorem condExp_eq_zero_of_odd (a : ℝ) (m : ℕ) {f : ℕ → ℝ}
    (hf : ∀ i ≤ m, f (m - i) = -f i) : condExp a m f = 0 := by
  have h := Finset.sum_range_reflect (fun j => f j * condPMF a m j) (m + 1)
  simp only [Nat.add_sub_cancel] at h
  have h2 : ∑ j ∈ range (m + 1), f (m - j) * condPMF a m (m - j)
      = ∑ j ∈ range (m + 1), -(f j * condPMF a m j) :=
    Finset.sum_congr rfl fun j hj => by
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
      rw [hf j hjm, condPMF_reflect hjm]; ring
  have h3 : ∑ j ∈ range (m + 1), -(f j * condPMF a m j)
      = -∑ j ∈ range (m + 1), f j * condPMF a m j := by simp
  rw [h2, h3] at h
  rw [condExp]
  linarith

/-- `E D_m = 0` (`thm:ensemble-hierarchy`). -/
theorem condExp_dfin (a : ℝ) (m : ℕ) : condExp a m (dfin m) = 0 :=
  condExp_eq_zero_of_odd a m fun i him => by
    rw [dfin, dfin, Nat.cast_sub him]; ring

/-- `E Ξ_m = 0` (`thm:ensemble-hierarchy`). -/
theorem condExp_xiScore (a : ℝ) (m : ℕ) : condExp a m (xiScore a m) = 0 :=
  condExp_eq_zero_of_odd a m fun i him => by
    rw [xiScore, xiScore, Nat.sub_sub_self him]; ring

/-! ### `E D_m²`: the second fiber moment

Purely algebraic: `(m-2i)² = m² - 4i(m-i)`, and canceling `i(m-i)` against the
two factorials turns `∑_i i(m-i)w_i` into the diagonal convolution at `a+1` and
`m-2`, which is `S_{m-2}(a+1)` (in the proof of `thm:coefficients`). -/

/-- `S_m(a) E[I_m(m-I_m)] = S_{m-2}(a+1)`: the `i(m-i)` cancellation of the proof
of `thm:coefficients`. -/
theorem sum_idx_mul (ha : 0 < a) (k : ℕ) :
    ∑ i ∈ range (k + 3), ((i : ℝ) * (((k + 2 - i : ℕ)) : ℝ)) * fibWeight a (k + 2) i
      = sweight (a + 1) k := by
  have ha1 : 0 < a + 1 := by linarith
  rw [Finset.sum_range_succ']
  have hzero : ((0 : ℕ) : ℝ) * (((k + 2 - 0 : ℕ)) : ℝ) * fibWeight a (k + 2) 0 = 0 := by
    simp
  rw [hzero, add_zero, Finset.sum_range_succ]
  have hlast : (((k + 1 : ℕ) + 1 : ℕ) : ℝ) * (((k + 2 - ((k + 1) + 1) : ℕ)) : ℝ)
      * fibWeight a (k + 2) ((k + 1) + 1) = 0 := by
    rw [show k + 2 - ((k + 1) + 1) = 0 from by omega]
    simp
  rw [hlast, add_zero, ← sum_fibWeight ha1 k]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hsub : k + 2 - (i + 1) = (k - i) + 1 := by omega
  have hi1 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  have hGi : (0 : ℝ) < Real.Gamma (a + 1 + (i : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hGki : (0 : ℝ) < Real.Gamma (a + 1 + ((k - i : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (k - i); linarith)
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfki : (0 : ℝ) < (Nat.factorial (k - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k - i)
  have hki : (0 : ℝ) < ((k - i : ℕ) : ℝ) + 1 := by positivity
  simp only [fibWeight, hsub]
  rw [Nat.factorial_succ, Nat.factorial_succ,
    show a + ((i + 1 : ℕ) : ℝ) = a + 1 + (i : ℝ) from by push_cast; ring,
    show a + (((k - i) + 1 : ℕ) : ℝ) = a + 1 + ((k - i : ℕ) : ℝ) from by push_cast; ring]
  push_cast
  field_simp

/-- `E[I_m(m-I_m)] = 0` for the two exceptional fibers `m = 0, 1`. -/
theorem condExp_idx_mul_le_one (a : ℝ) {m : ℕ} (hm : m ≤ 1) :
    condExp a m (fun i => (i : ℝ) * (((m - i : ℕ)) : ℝ)) = 0 := by
  interval_cases m
  · simp [condExp]
  · rw [condExp, Finset.sum_range_succ, Finset.sum_range_succ]
    norm_num

/-- `E[I_m(m-I_m)] = S_{m-2}(a+1)/S_m(a)` for `m ≥ 2`. -/
theorem condExp_idx_mul (ha : 0 < a) (k : ℕ) :
    condExp a (k + 2) (fun i => (i : ℝ) * (((k + 2 - i : ℕ)) : ℝ))
      = sweight (a + 1) k / sweight a (k + 2) := by
  rw [condExp, ← sum_idx_mul ha k, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [condPMF]
  ring

/-- The weight ratio `S_{m-2}(a+1)/S_m(a) = m(m-1)(a+m-1)/(2(2a+2m-3))`, in the
proof of `thm:coefficients`. -/
theorem sweight_ratio (ha : 0 < a) (k : ℕ) :
    sweight (a + 1) k / sweight a (k + 2)
      = ((k : ℝ) + 2) * ((k : ℝ) + 1) * (a + (k : ℝ) + 1) / (2 * (2 * a + 2 * (k : ℝ) + 1)) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hG1 : Real.Gamma (a + 1 + (k : ℝ)) = Real.Gamma (a + (k : ℝ) + 1) := by
    rw [show a + 1 + (k : ℝ) = a + (k : ℝ) + 1 from by ring]
  have hGrec : Real.Gamma (a + (k : ℝ) + 2)
      = (a + (k : ℝ) + 1) * Real.Gamma (a + (k : ℝ) + 1) := by
    rw [show a + (k : ℝ) + 2 = (a + (k : ℝ) + 1) + 1 from by ring,
      Real.Gamma_add_one (by linarith : a + (k : ℝ) + 1 ≠ 0)]
  have hGpos : 0 < Real.Gamma (a + (k : ℝ) + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hpoch : poch (2 * a + ((k + 2 : ℕ) : ℝ) - 1) (k + 2)
      = poch (2 * (a + 1) + (k : ℝ) - 1) k
        * ((2 * a + 2 * (k : ℝ) + 1) * (2 * a + 2 * (k : ℝ) + 2)) := by
    have e : 2 * a + ((k + 2 : ℕ) : ℝ) - 1 = 2 * (a + 1) + (k : ℝ) - 1 := by push_cast; ring
    rw [e, poch_succ, poch_succ]
    push_cast
    ring
  have hfac : ((Nat.factorial (k + 2) : ℕ) : ℝ)
      = ((k : ℝ) + 2) * (((k : ℝ) + 1) * (Nat.factorial k : ℝ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hden : (0 : ℝ) < 2 * a + 2 * (k : ℝ) + 1 := by linarith
  rw [sweight, sweight, hpoch, hfac, hG1, show a + ((k + 2 : ℕ) : ℝ) = a + (k : ℝ) + 2
      from by push_cast; ring, hGrec]
  have hnum : 0 < poch (2 * (a + 1) + (k : ℝ) - 1) k :=
    poch_pos (fun i hi => by
      have hle : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
      nlinarith [ha, hle, Nat.cast_nonneg (α := ℝ) i])
  field_simp

/-- `E D_m² = m² - 4E[I_m(m-I_m)]`, from `(m-2i)² = m² - 4i(m-i)`. -/
theorem condExp_dfin_sq_eq (ha : 0 < a) (m : ℕ) :
    condExp a m (fun i => dfin m i ^ 2)
      = (m : ℝ) ^ 2 - 4 * condExp a m (fun i => (i : ℝ) * (((m - i : ℕ)) : ℝ)) := by
  rw [condExp, condExp, Finset.mul_sum, eq_sub_iff_add_eq, ← Finset.sum_add_distrib,
    show ((m : ℝ) ^ 2 : ℝ) = (m : ℝ) ^ 2 * 1 from by ring, ← sum_condPMF ha m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hc : ((m - i : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := Nat.cast_sub him
  rw [dfin, hc]
  ring

/-- **`eq:finite-law-entries`, third identity.**  `c_m^{(κ)} = κm/2 - ½E D_m²`, for
every `m ≥ 0` including the two exceptional fibers. -/
theorem ckappa_eq_condExp (ha : 0 < a) (κ : ℝ) (m : ℕ) :
    ckappa a κ m = κ * (m : ℝ) / 2 - (1 / 2) * condExp a m (fun i => dfin m i ^ 2) := by
  rw [condExp_dfin_sq_eq ha m]
  match m with
  | 0 => rw [condExp_idx_mul_le_one a (by omega)]; simp
  | 1 =>
      rw [condExp_idx_mul_le_one a (by omega), ckappa_one]
      push_cast
      ring
  | (k + 2) =>
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hden : (2 * a + 2 * (k : ℝ) + 1) ≠ 0 :=
        (by linarith : (0 : ℝ) < 2 * a + 2 * (k : ℝ) + 1).ne'
      have hden' : (1 + a * 2 + (k : ℝ) * 2) ≠ 0 :=
        (by linarith : (0 : ℝ) < 1 + a * 2 + (k : ℝ) * 2).ne'
      have hden'' : (2 * a + 2 * ((k : ℝ) + 2) - 3) ≠ 0 :=
        (by linarith : (0 : ℝ) < 2 * a + 2 * ((k : ℝ) + 2) - 3).ne'
      rw [condExp_idx_mul ha k, sweight_ratio ha k]
      unfold ckappa
      rw [if_neg (by omega : ¬(k + 2 = 0)), if_neg (by omega : ¬(k + 2 = 1))]
      push_cast
      rw [show (2 : ℝ) * (2 * a + 2 * ((k : ℝ) + 2) - 3) = 2 * (2 * a + 2 * (k : ℝ) + 1)
          from by ring]
      field

/-! ### `eq:finite-law-entries`, the `α` entry

`AlphaCoeff` already carries the two-center deformed weight `gammaPairInv2`, the
finite sum `Fdelta` of `eq:Fdelta`, its closed form, and the second variation
`convolution_second_variation`, which is exactly `∑_i w_i(Ξ_i² - Σ_i) =
-2S_mψ₁(a+m)`.  Dividing by `S_m` turns it into the fiber-law statement. -/

theorem condExp_eq_div (a : ℝ) (m : ℕ) (f : ℕ → ℝ) :
    condExp a m f = (∑ i ∈ range (m + 1), f i * fibWeight a m i) / sweight a m := by
  rw [condExp, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by rw [condPMF]; ring

/-- `∑_i w_i(Σ_i - Ξ_i²) = 2S_mψ₁(a+m)`, which is `eq:F-second-delta` with the
sign of `AlphaCoeff.convolution_second_variation` flipped. -/
theorem sum_curvature (ha : 0 < a) (m : ℕ) :
    ∑ i ∈ range (m + 1), (sigmaCurv a m i - xiScore a m i ^ 2) * fibWeight a m i
      = 2 * (sweight a m * trigamma (a + (m : ℝ))) := by
  have h := convolution_second_variation ha m
  have hneg : ∀ g : ℕ → ℝ, ∑ i ∈ range (m + 1), -(g i) = -∑ i ∈ range (m + 1), g i :=
    fun g => by simp
  have e : ∀ i ∈ range (m + 1),
      (sigmaCurv a m i - xiScore a m i ^ 2) * fibWeight a m i
        = -(((realDigamma (a + ((m - i : ℕ) : ℝ)) - realDigamma (a + (i : ℝ))) ^ 2
              - trigamma (a + (i : ℝ)) - trigamma (a + ((m - i : ℕ) : ℝ)))
            / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)
                * Real.Gamma (a + (i : ℝ)) * Real.Gamma (a + ((m - i : ℕ) : ℝ)))) := by
    intro i _
    rw [sigmaCurv, xiScore, fibWeight]
    ring
  rw [Finset.sum_congr rfl e, hneg, h]
  ring

/-- **`eq:finite-law-entries`, first identity.**  `α_m = ½E(Σ_m - Ξ_m²)`. -/
theorem alpha_eq_condExp (ha : 0 < a) (m : ℕ) :
    αcoef a m = (1 / 2) * condExp a m (fun i => sigmaCurv a m i - xiScore a m i ^ 2) := by
  have hS := (sweight_pos ha m).ne'
  rw [condExp_eq_div, sum_curvature ha m, αcoef]
  field_simp

/-! ### `eq:EDXi` and the `β` entry

The paper differentiates `E_δ D = mδ/(a+m-1)` (`eq:EDdelta`) at `δ = 0`.  The same
step here: `∑_i i w_i(δ)` is `lem:convolution` at `(α,β) = (a+1+δ, a-δ)` with `m-1`
in place of `m`, so its `δ`-derivative at the origin is available in closed form,
and termwise it is `∑_i i Ξ_i w_i`. -/

/-- `∑_i i w_i(δ)`, the first index moment of the deformed weight of
`eq:Fdelta`. -/
noncomputable def Ifirst (a : ℝ) (m : ℕ) (d : ℝ) : ℝ :=
  ∑ i ∈ range (m + 1), (i : ℝ)
    * ((1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
        * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) d)

/-- The closed form of `∑_i i w_i(δ)`: `lem:convolution` at
`(α,β) = (a+1+δ, a-δ)` and `m-1` in place of `m`, which is the step
`eq:EDdelta` rests on. -/
theorem Ifirst_eq_closed (k : ℕ) {a d : ℝ} (hd : d ∈ Set.Ioo (-a) a) :
    Ifirst a (k + 1) d
      = poch (2 * a + (k : ℝ)) k / (Nat.factorial k : ℝ)
        * gammaPairInv2 (a + (k : ℝ) + 1) (a + (k : ℝ)) d := by
  have h1 : 0 < a + 1 + d := by linarith [hd.1]
  have h2 : 0 < a - d := by linarith [hd.2]
  have hconv := gamma_convolution h1 h2 k
  rw [Ifirst, Finset.sum_range_succ']
  have hzero : ((0 : ℕ) : ℝ)
      * ((1 / ((Nat.factorial 0 : ℝ) * (Nat.factorial (k + 1 - 0) : ℝ)))
          * gammaPairInv2 (a + ((0 : ℕ) : ℝ)) (a + ((k + 1 - 0 : ℕ) : ℝ)) d) = 0 := by simp
  rw [hzero, add_zero]
  have hterm : ∀ i ∈ range (k + 1),
      ((i + 1 : ℕ) : ℝ)
          * ((1 / ((Nat.factorial (i + 1) : ℝ) * (Nat.factorial (k + 1 - (i + 1)) : ℝ)))
              * gammaPairInv2 (a + ((i + 1 : ℕ) : ℝ)) (a + ((k + 1 - (i + 1) : ℕ) : ℝ)) d)
        = 1 / ((Nat.factorial i : ℝ) * (Nat.factorial (k - i) : ℝ)
              * Real.Gamma ((a + 1 + d) + (i : ℝ))
              * Real.Gamma ((a - d) + ((k - i : ℕ) : ℝ))) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hsub : k + 1 - (i + 1) = k - i := by omega
    have hGi : (0 : ℝ) < Real.Gamma (a + 1 + d + (i : ℝ)) :=
      Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
    have hGki : (0 : ℝ) < Real.Gamma (a - d + ((k - i : ℕ) : ℝ)) :=
      Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (k - i); linarith)
    have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hfki : (0 : ℝ) < (Nat.factorial (k - i) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (k - i)
    rw [hsub, gammaPairInv2, Nat.factorial_succ,
      show a + ((i + 1 : ℕ) : ℝ) + d = (a + 1 + d) + (i : ℝ) from by push_cast; ring,
      show a + ((k - i : ℕ) : ℝ) - d = (a - d) + ((k - i : ℕ) : ℝ) from by ring]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm, hconv, gammaPairInv2,
    show (a + 1 + d) + (a - d) + (k : ℝ) - 1 = 2 * a + (k : ℝ) from by ring,
    show (a + 1 + d) + (k : ℝ) = (a + (k : ℝ) + 1) + d from by ring,
    show (a - d) + (k : ℝ) = (a + (k : ℝ)) - d from by ring]
  have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  field_simp

/-- The termwise `δ`-derivative of `∑_i i w_i(δ)` at the origin: `∑_i i Ξ_i w_i`. -/
theorem deriv_Ifirst_termwise (ha : 0 < a) (m : ℕ) :
    deriv (Ifirst a m) 0
      = ∑ i ∈ range (m + 1), (i : ℝ) * (xiScore a m i * fibWeight a m i) := by
  have hsum : HasDerivAt (Ifirst a m)
      (∑ i ∈ range (m + 1), (i : ℝ)
        * ((1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
            * ((-realDigamma (a + (i : ℝ) + 0) + realDigamma (a + ((m - i : ℕ) : ℝ) - 0))
                * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) 0))) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hmi : (0 : ℝ) ≤ ((m - i : ℕ) : ℝ) := Nat.cast_nonneg (m - i)
    exact (((hasDerivAt_gammaPairInv2 (u := a + (i : ℝ)) (v := a + ((m - i : ℕ) : ℝ)) (d := 0)
      (by linarith) (by linarith)).const_mul
        (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))).const_mul (i : ℝ))
  rw [hsum.deriv]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (0 : ℝ) < Real.Gamma (a + (i : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hmi : (0 : ℝ) < Real.Gamma (a + ((m - i : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - i)
  rw [xiScore, fibWeight, gammaPairInv2, add_zero, sub_zero]
  field

/-- `∑_i i Ξ_i w_i` in closed form: the `δ`-derivative of `Ifirst_eq_closed` at the
origin, where the score of the two-center weight is `ψ(a+m-1) - ψ(a+m) =
-(a+m-1)⁻¹`. -/
theorem sum_idx_xi (ha : 0 < a) (k : ℕ) :
    ∑ i ∈ range (k + 1 + 1), (i : ℝ) * (xiScore a (k + 1) i * fibWeight a (k + 1) i)
      = poch (2 * a + (k : ℝ)) k / (Nat.factorial k : ℝ)
        * (-(a + (k : ℝ))⁻¹ * gammaPairInv2 (a + (k : ℝ) + 1) (a + (k : ℝ)) 0) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hak : 0 < a + (k : ℝ) := by linarith
  have hclosed : Ifirst a (k + 1) =ᶠ[nhds (0 : ℝ)]
      fun d : ℝ => poch (2 * a + (k : ℝ)) k / (Nat.factorial k : ℝ)
        * gammaPairInv2 (a + (k : ℝ) + 1) (a + (k : ℝ)) d := by
    filter_upwards [Ioo_mem_nhds (show -a < (0 : ℝ) by linarith) ha] with d hd
    exact Ifirst_eq_closed k hd
  have hg : HasDerivAt (gammaPairInv2 (a + (k : ℝ) + 1) (a + (k : ℝ)))
      ((-realDigamma (a + (k : ℝ) + 1 + 0) + realDigamma (a + (k : ℝ) - 0))
        * gammaPairInv2 (a + (k : ℝ) + 1) (a + (k : ℝ)) 0) 0 :=
    hasDerivAt_gammaPairInv2 (by linarith) (by linarith)
  have hpsi : -realDigamma (a + (k : ℝ) + 1 + 0) + realDigamma (a + (k : ℝ) - 0)
      = -(a + (k : ℝ))⁻¹ := by
    rw [add_zero, sub_zero, realDigamma_add_one hak, one_div]
    ring
  rw [← deriv_Ifirst_termwise ha (k + 1), hclosed.deriv_eq, (hg.const_mul _).deriv, hpsi]

/-- **`eq:EDXi`.**  `E(D_mΞ_m) = m/(a+m-1)` for `m ≥ 1`. -/
theorem condExp_dfin_mul_xi (ha : 0 < a) (k : ℕ) :
    condExp a (k + 1) (fun i => dfin (k + 1) i * xiScore a (k + 1) i)
      = ((k : ℝ) + 1) / (a + (k : ℝ)) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hak : 0 < a + (k : ℝ) := by linarith
  have hGk : 0 < Real.Gamma (a + (k : ℝ)) := Real.Gamma_pos_of_pos hak
  have hGk1 : Real.Gamma (a + (k : ℝ) + 1) = (a + (k : ℝ)) * Real.Gamma (a + (k : ℝ)) :=
    Real.Gamma_add_one hak.ne'
  have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hfk1 : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k + 1)
  have hpoch : 0 < poch (2 * a + (k : ℝ)) k :=
    poch_pos fun i _ => by have := Nat.cast_nonneg (α := ℝ) i; linarith
  have hpochS : poch (2 * a + ((k + 1 : ℕ) : ℝ) - 1) (k + 1)
      = poch (2 * a + (k : ℝ)) k * (2 * a + 2 * (k : ℝ)) := by
    rw [show 2 * a + ((k + 1 : ℕ) : ℝ) - 1 = 2 * a + (k : ℝ) from by push_cast; ring, poch_succ]
    ring
  have hxi0 : ∑ i ∈ range (k + 1 + 1), xiScore a (k + 1) i * fibWeight a (k + 1) i = 0 := by
    have h := condExp_xiScore a (k + 1)
    rw [condExp_eq_div, div_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · exact absurd h (sweight_pos ha (k + 1)).ne'
  have hsplit : ∑ i ∈ range (k + 1 + 1),
      (dfin (k + 1) i * xiScore a (k + 1) i) * fibWeight a (k + 1) i
      = ((k : ℝ) + 1) * (∑ i ∈ range (k + 1 + 1), xiScore a (k + 1) i * fibWeight a (k + 1) i)
        - 2 * ∑ i ∈ range (k + 1 + 1),
            (i : ℝ) * (xiScore a (k + 1) i * fibWeight a (k + 1) i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dfin]
    push_cast
    ring
  rw [condExp_eq_div, hsplit, hxi0, sum_idx_xi ha k, gammaPairInv2_zero, hGk1, sweight,
    show a + ((k + 1 : ℕ) : ℝ) = a + (k : ℝ) + 1 from by push_cast; ring, hGk1, hpochS,
    Nat.factorial_succ]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field

/-- **`eq:finite-law-entries`, second identity.**  `β_m = 1 - ½E(D_mΞ_m)`. -/
theorem beta_eq_condExp (ha : 0 < a) (m : ℕ) :
    βcoef a m = 1 - (1 / 2) * condExp a m (fun i => dfin m i * xiScore a m i) := by
  match m with
  | 0 =>
      have h : condExp a 0 (fun i => dfin 0 i * xiScore a 0 i) = 0 := by
        rw [condExp, Finset.sum_range_succ]
        simp [dfin]
      rw [h, βcoef_zero]
      ring
  | (k + 1) =>
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hak : (a + (k : ℝ)) ≠ 0 := (by linarith : (0 : ℝ) < a + (k : ℝ)).ne'
      have hak' : (a + ((k : ℝ) + 1) - 1) ≠ 0 :=
        (by linarith : (0 : ℝ) < a + ((k : ℝ) + 1) - 1).ne'
      rw [condExp_dfin_mul_xi ha k, βcoef, if_neg (by omega : ¬(k + 1 = 0))]
      push_cast
      field

/-! ### `eq:microcanonical-schur` and `eq:microcanonical-covariance-deficit` -/

/-- The fiber variance of a variable under the conditional law of
`eq:pair-total-law`. -/
noncomputable def condVar (a : ℝ) (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  condExp a m (fun i => f i ^ 2) - condExp a m f ^ 2

/-- The fiber covariance of two variables under the conditional law of
`eq:pair-total-law`. -/
noncomputable def condCov (a : ℝ) (m : ℕ) (f g : ℕ → ℝ) : ℝ :=
  condExp a m (fun i => f i * g i) - condExp a m f * condExp a m g

/-- The baseline matrix of `eq:microcanonical-covariance-deficit`. -/
noncomputable def fiberBaseline (a κ τ : ℝ) (m : ℕ) : SymMat :=
  ⟨(1 / 2) * condExp a m (fun i => sigmaCurv a m i), 1,
    τ / trigamma a + κ * (m : ℝ) / 2⟩

/-- The fiber score covariance of `eq:microcanonical-covariance-deficit`. -/
noncomputable def fiberCovMat (a : ℝ) (m : ℕ) : SymMat :=
  ⟨condVar a m (xiScore a m), condCov a m (xiScore a m) (dfin m), condVar a m (dfin m)⟩

/-- **`eq:microcanonical-schur`.**  The three entries of the normalized fiber
`N̂_m^{(κ,τ)}` are the finite-law expressions of `eq:finite-law-entries`. -/
theorem NmatKT_eq_condExp (ha : 0 < a) (κ τ : ℝ) (m : ℕ) :
    NmatKT a κ τ m
      = ⟨(1 / 2) * condExp a m (fun i => sigmaCurv a m i - xiScore a m i ^ 2),
          1 - (1 / 2) * condExp a m (fun i => dfin m i * xiScore a m i),
          τ / trigamma a
            + (κ * (m : ℝ) / 2 - (1 / 2) * condExp a m (fun i => dfin m i ^ 2))⟩ :=
  SymMat.ext (alpha_eq_condExp ha m) (beta_eq_condExp ha m)
    (by change τ / trigamma a + ckappa a κ m = _; rw [ckappa_eq_condExp ha κ m])

/-- **`eq:microcanonical-covariance-deficit`.**  Since `E Ξ_m = E D_m = 0`, the same
three entries are a baseline minus half the covariance matrix of the fiber scores
`(Ξ_m, D_m)`. -/
theorem NmatKT_eq_baseline_sub_cov (ha : 0 < a) (κ τ : ℝ) (m : ℕ) :
    NmatKT a κ τ m
      = ⟨(fiberBaseline a κ τ m).a11 - (1 / 2) * (fiberCovMat a m).a11,
          (fiberBaseline a κ τ m).a12 - (1 / 2) * (fiberCovMat a m).a12,
          (fiberBaseline a κ τ m).a22 - (1 / 2) * (fiberCovMat a m).a22⟩ := by
  have hxi := condExp_xiScore a m
  have hd := condExp_dfin a m
  have h11 : (fiberBaseline a κ τ m).a11 - (1 / 2) * (fiberCovMat a m).a11
      = (1 / 2) * condExp a m (fun i => sigmaCurv a m i - xiScore a m i ^ 2) := by
    have hsub : condExp a m (fun i => sigmaCurv a m i - xiScore a m i ^ 2)
        = condExp a m (fun i => sigmaCurv a m i) - condExp a m (fun i => xiScore a m i ^ 2) := by
      rw [condExp, condExp, condExp, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [fiberBaseline, fiberCovMat, condVar]
    rw [hsub, hxi]
    ring
  have h12 : (fiberBaseline a κ τ m).a12 - (1 / 2) * (fiberCovMat a m).a12
      = 1 - (1 / 2) * condExp a m (fun i => dfin m i * xiScore a m i) := by
    have hsymm : condExp a m (fun i => xiScore a m i * dfin m i)
        = condExp a m (fun i => dfin m i * xiScore a m i) := by
      rw [condExp, condExp]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [fiberBaseline, fiberCovMat, condCov]
    rw [hsymm, hxi]
    ring
  have h22 : (fiberBaseline a κ τ m).a22 - (1 / 2) * (fiberCovMat a m).a22
      = τ / trigamma a
        + (κ * (m : ℝ) / 2 - (1 / 2) * condExp a m (fun i => dfin m i ^ 2)) := by
    simp only [fiberBaseline, fiberCovMat, condVar]
    rw [hd]
    ring
  rw [NmatKT_eq_condExp ha κ τ m]
  exact SymMat.ext h11.symm h12.symm h22.symm

/-! ### `eq:canonical-fiber-average`

`eq:ABC-expansions` gives each entry of the Turánian as `∑_m S_m(entry)λ^m`, so
dividing by `Z²` is exactly weighting the fibers by `eq:pair-total-law`. -/

/-- `E_λ f(R)` under `eq:pair-total-law`. -/
noncomputable def pairExp (a lam : ℝ) (f : ℕ → ℝ) : ℝ := ∑' m : ℕ, f m * pairPMF a lam m

theorem pairExp_eq_div (ha : 0 < a) (hlam : 0 ≤ lam) (f : ℕ → ℝ) :
    pairExp a lam f = (∑' m : ℕ, sweight a m * f m * lam ^ m) / Zfun a lam ^ 2 := by
  have hZ : Zfun a lam ^ 2 ≠ 0 := pow_ne_zero 2 (Zfun_pos ha hlam).ne'
  rw [pairExp, ← tsum_div_const]
  exact tsum_congr fun m => by rw [pairPMF]; ring

/-- **`eq:canonical-fiber-average`, entry `(1,1)`.** -/
theorem pairExp_alpha (ha : 0 < a) (hlam : 0 ≤ lam) :
    pairExp a lam (fun m => αcoef a m) = Afun a lam / Zfun a lam ^ 2 := by
  rw [pairExp_eq_div ha hlam, Afun_eq_tsum ha lam]
  exact congrArg (· / Zfun a lam ^ 2) (tsum_congr fun m => by rw [αcoef])

/-- **`eq:canonical-fiber-average`, entry `(1,2)`.** -/
theorem pairExp_beta (ha : 0 < a) (hlam : 0 ≤ lam) :
    pairExp a lam (fun m => βcoef a m) = Bseries a lam / Zfun a lam ^ 2 := by
  rw [pairExp_eq_div ha hlam, Bseries_eq_tsum ha lam]

/-- **`eq:canonical-fiber-average`, entry `(2,2)`.** -/
theorem pairExp_gamma (ha : 0 < a) (hlam : 0 ≤ lam) (κ τ : ℝ) :
    pairExp a lam (fun m => τ / trigamma a + ckappa a κ m)
      = Cseries a (trigamma a) κ τ lam / (trigamma a * Zfun a lam ^ 2) := by
  have hg : trigamma a ≠ 0 := (trigamma_pos ha).ne'
  have hZ : Zfun a lam ^ 2 ≠ 0 := pow_ne_zero 2 (Zfun_pos ha hlam).ne'
  rw [pairExp_eq_div ha hlam, Cseries_eq_tsum ha (trigamma a) κ τ lam, ← tsum_div_const,
    ← tsum_div_const]
  exact tsum_congr fun m => by field_simp

/-- **`eq:canonical-fiber-average`.**  The normalized Turánian
`(1/Z²)diag(1,g^{-1/2})𝒯_{κ,τ}diag(1,g^{-1/2})` is the canonical average
`E_λ N̂_R^{(κ,τ)}` of the microcanonical fibers. -/
theorem normalizedTuran_eq_pairExp (ha : 0 < a) (hlam : 0 ≤ lam) (κ τ : ℝ) :
    normalizedTuran a κ τ lam
      = ⟨pairExp a lam (fun m => (NmatKT a κ τ m).a11),
          pairExp a lam (fun m => (NmatKT a κ τ m).a12),
          pairExp a lam (fun m => (NmatKT a κ τ m).a22)⟩ :=
  SymMat.ext (pairExp_alpha ha hlam).symm (pairExp_beta ha hlam).symm
    (pairExp_gamma ha hlam κ τ).symm

/-! ### `eq:microcanonical-schur` as the log-derivative of `F_m(u,v)`

`thm:ensemble-hierarchy` states the three entries as second derivatives of
`ℓ_m = log F_m` at the origin, with
```
  F_m(u,v) = ∑_i exp{-v(m-2i)/√2} / (i!(m-i)!Γ(a+u/√2+i)Γ(a-u/√2+m-i)) .
```
The `v`-dependence is a finite exponential sum, and the `u`-dependence is the
`Fdelta` of `eq:Fdelta` at `δ = u/√2`, so all three derivatives reduce to
quantities already computed above.  What is needed beyond them is the second
logarithmic derivative of a positive function, which is where the score
covariance enters. -/

/-! #### Two fiber sums in unnormalized form -/

theorem sum_xi_fibWeight (ha : 0 < a) (m : ℕ) :
    ∑ i ∈ range (m + 1), xiScore a m i * fibWeight a m i = 0 := by
  have h := condExp_xiScore a m
  rw [condExp_eq_div, div_eq_zero_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd h (sweight_pos ha m).ne'

theorem sum_dfin_fibWeight (ha : 0 < a) (m : ℕ) :
    ∑ i ∈ range (m + 1), dfin m i * fibWeight a m i = 0 := by
  have h := condExp_dfin a m
  rw [condExp_eq_div, div_eq_zero_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd h (sweight_pos ha m).ne'

theorem sum_weighted_eq_condExp (ha : 0 < a) (m : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ range (m + 1), f i * fibWeight a m i = sweight a m * condExp a m f := by
  have hS : sweight a m ≠ 0 := (sweight_pos ha m).ne'
  rw [condExp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [condPMF]
  field_simp

/-- The second logarithmic derivative of a positive function on an interval about
the origin: `(log f)''(0) = f''(0)/f(0) - (f'(0)/f(0))²`. -/
theorem deriv_deriv_log_eq {f f' : ℝ → ℝ} {r V : ℝ} (hr : 0 < r)
    (hf : ∀ x ∈ Set.Ioo (-r) r, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Set.Ioo (-r) r, 0 < f x)
    (hf' : HasDerivAt f' V 0) :
    deriv (deriv fun x => Real.log (f x)) 0 = V / f 0 - (f' 0 / f 0) ^ 2 := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr⟩
  have hev : (deriv fun x => Real.log (f x)) =ᶠ[nhds (0 : ℝ)] fun x => f' x / f x := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with x hx
    exact ((hf x hx).log (hpos x hx).ne').deriv
  have hq : HasDerivAt (fun x => f' x / f x)
      ((V * f 0 - f' 0 * f' 0) / f 0 ^ 2) 0 := hf'.div (hf 0 h0) (hpos 0 h0).ne'
  have hfne : f 0 ≠ 0 := (hpos 0 h0).ne'
  rw [hev.deriv_eq, hq.deriv]
  field_simp

/-- `F_m(u,v)` of `thm:ensemble-hierarchy`. -/
noncomputable def Fuv (a : ℝ) (m : ℕ) (u v : ℝ) : ℝ :=
  ∑ i ∈ range (m + 1),
    Real.exp (-(v * dfin m i / Real.sqrt 2))
      * ((1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
          * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) (u / Real.sqrt 2))

/-- `ℓ_m = log F_m` of `thm:ensemble-hierarchy`. -/
noncomputable def ellUV (a : ℝ) (m : ℕ) (u v : ℝ) : ℝ := Real.log (Fuv a m u v)

theorem sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

theorem sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

/-- Every summand of `Fdelta` is positive on `|δ| < a`, so `F_m(δ) > 0` there. -/
theorem Fdelta_pos (m : ℕ) {d : ℝ} (hd : d ∈ Set.Ioo (-a) a) :
    0 < Fdelta a m d := by
  rw [Fdelta]
  refine Finset.sum_pos (fun i hi => ?_) ⟨0, mem_range.mpr (Nat.succ_pos m)⟩
  have h1 : (0 : ℝ) < a + (i : ℝ) + d := by
    have := Nat.cast_nonneg (α := ℝ) i; linarith [hd.1]
  have h2 : (0 : ℝ) < a + ((m - i : ℕ) : ℝ) - d := by
    have := Nat.cast_nonneg (α := ℝ) (m - i); linarith [hd.2]
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - i)
  have hG1 : 0 < Real.Gamma (a + (i : ℝ) + d) := Real.Gamma_pos_of_pos h1
  have hG2 : 0 < Real.Gamma (a + ((m - i : ℕ) : ℝ) - d) := Real.Gamma_pos_of_pos h2
  rw [gammaPairInv2]
  positivity

/-- The termwise first `δ`-derivative of `Fdelta`, named so that `Fuv`'s slices can
carry it through the chain rule. -/
noncomputable def FdeltaScore (a : ℝ) (m : ℕ) (d : ℝ) : ℝ :=
  ∑ i ∈ range (m + 1),
    (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
      * ((-realDigamma (a + (i : ℝ) + d) + realDigamma (a + ((m - i : ℕ) : ℝ) - d))
          * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) d)

theorem hasDerivAt_Fdelta_score {a : ℝ} (m : ℕ) {d : ℝ} (hd : d ∈ Set.Ioo (-a) a) :
    HasDerivAt (Fdelta a m) (FdeltaScore a m d) d := hasDerivAt_Fdelta m hd

/-- `F_m(0) = S_m`, the diagonal case of `lem:convolution`. -/
theorem Fdelta_zero_eq (ha : 0 < a) (m : ℕ) : Fdelta a m 0 = sweight a m := by
  rw [Fdelta, ← sum_fibWeight ha m]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (0 : ℝ) < Real.Gamma (a + (i : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hmi : (0 : ℝ) < Real.Gamma (a + ((m - i : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - i)
  rw [fibWeight, gammaPairInv2_zero]
  field_simp

theorem hasDerivAt_FdeltaScore (ha : 0 < a) (m : ℕ) :
    HasDerivAt (FdeltaScore a m)
      (∑ i ∈ range (m + 1), (xiScore a m i ^ 2 - sigmaCurv a m i) * fibWeight a m i) 0 := by
  have h : HasDerivAt (FdeltaScore a m)
      (∑ i ∈ range (m + 1),
        (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
          * (((realDigamma (a + ((m - i : ℕ) : ℝ)) - realDigamma (a + (i : ℝ))) ^ 2
                - trigamma (a + (i : ℝ)) - trigamma (a + ((m - i : ℕ) : ℝ)))
              * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) 0)) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    exact (hasDerivAt_scoreMul_gammaPairInv2
      (u := a + (i : ℝ)) (v := a + ((m - i : ℕ) : ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
      (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)).const_mul _
  refine h.congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
  have hi : (0 : ℝ) < Real.Gamma (a + (i : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hmi : (0 : ℝ) < Real.Gamma (a + ((m - i : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - i)
  rw [xiScore, sigmaCurv, fibWeight, gammaPairInv2_zero]
  field

theorem FdeltaScore_zero (ha : 0 < a) (m : ℕ) : FdeltaScore a m 0 = 0 := by
  have e : ∀ i ∈ range (m + 1),
      (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
        * ((-realDigamma (a + (i : ℝ) + 0) + realDigamma (a + ((m - i : ℕ) : ℝ) - 0))
            * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) 0)
      = xiScore a m i * fibWeight a m i := by
    intro i _
    have hi : (0 : ℝ) < Real.Gamma (a + (i : ℝ)) :=
      Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
    have hmi : (0 : ℝ) < Real.Gamma (a + ((m - i : ℕ) : ℝ)) :=
      Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)
    have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (m - i)
    rw [xiScore, fibWeight, gammaPairInv2, add_zero, sub_zero]
    field
  rw [FdeltaScore, Finset.sum_congr rfl e, sum_xi_fibWeight ha m]

/-! #### The `u`-slice: `-ℓ_{m,uu}(0,0) = α_m` -/

theorem Fuv_v_arg_zero (a : ℝ) (m : ℕ) (u : ℝ) :
    Fuv a m u 0 = Fdelta a m (u / Real.sqrt 2) := by
  simp only [Fuv, Fdelta]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- **`eq:microcanonical-schur`, entry `(1,1)`.**  `-ℓ_{m,uu}(0,0) = α_m`. -/
theorem deriv_deriv_ellUV_uu (ha : 0 < a) (m : ℕ) :
    deriv (deriv fun u => ellUV a m u 0) 0 = -αcoef a m := by
  have hs2 := sqrt_two_pos
  have hs2sq := sqrt_two_mul_self
  have hr : 0 < Real.sqrt 2 * a := by positivity
  have hmem : ∀ x ∈ Set.Ioo (-(Real.sqrt 2 * a)) (Real.sqrt 2 * a),
      x / Real.sqrt 2 ∈ Set.Ioo (-a) a := by
    intro x hx
    exact ⟨by rw [lt_div_iff₀ hs2]; nlinarith [hx.1],
      by rw [div_lt_iff₀ hs2]; nlinarith [hx.2]⟩
  have hf : ∀ x ∈ Set.Ioo (-(Real.sqrt 2 * a)) (Real.sqrt 2 * a),
      HasDerivAt (fun u : ℝ => Fdelta a m (u / Real.sqrt 2))
        (FdeltaScore a m (x / Real.sqrt 2) * (1 / Real.sqrt 2)) x := by
    intro x hx
    have hin : HasDerivAt (fun u : ℝ => u / Real.sqrt 2) (1 / Real.sqrt 2) x :=
      (hasDerivAt_id x).div_const (Real.sqrt 2)
    simpa [Function.comp_def] using (hasDerivAt_Fdelta_score m (hmem x hx)).comp x hin
  have hpos : ∀ x ∈ Set.Ioo (-(Real.sqrt 2 * a)) (Real.sqrt 2 * a),
      0 < Fdelta a m (x / Real.sqrt 2) := fun x hx => Fdelta_pos m (hmem x hx)
  have hf' : HasDerivAt (fun x : ℝ => FdeltaScore a m (x / Real.sqrt 2) * (1 / Real.sqrt 2))
      ((∑ i ∈ range (m + 1), (xiScore a m i ^ 2 - sigmaCurv a m i) * fibWeight a m i)
        * (1 / Real.sqrt 2) * (1 / Real.sqrt 2)) 0 := by
    have hin : HasDerivAt (fun u : ℝ => u / Real.sqrt 2) (1 / Real.sqrt 2) 0 :=
      (hasDerivAt_id (0 : ℝ)).div_const (Real.sqrt 2)
    have hout : HasDerivAt (FdeltaScore a m)
        (∑ i ∈ range (m + 1), (xiScore a m i ^ 2 - sigmaCurv a m i) * fibWeight a m i)
        ((0 : ℝ) / Real.sqrt 2) := by
      rw [zero_div]; exact hasDerivAt_FdeltaScore ha m
    have hcomp := hout.comp (0 : ℝ) hin
    simp only [Function.comp_def] at hcomp
    exact hcomp.mul_const (1 / Real.sqrt 2)
  have hell : (fun u : ℝ => ellUV a m u 0)
      = fun u : ℝ => Real.log (Fdelta a m (u / Real.sqrt 2)) := by
    funext u; rw [ellUV, Fuv_v_arg_zero]
  have hcurv : ∑ i ∈ range (m + 1), (xiScore a m i ^ 2 - sigmaCurv a m i) * fibWeight a m i
      = -(2 * (sweight a m * trigamma (a + (m : ℝ)))) := by
    have h := sum_curvature ha m
    have hneg : ∀ g : ℕ → ℝ, ∑ i ∈ range (m + 1), -(g i) = -∑ i ∈ range (m + 1), g i :=
      fun g => by simp
    rw [show ∑ i ∈ range (m + 1), (xiScore a m i ^ 2 - sigmaCurv a m i) * fibWeight a m i
        = ∑ i ∈ range (m + 1), -((sigmaCurv a m i - xiScore a m i ^ 2) * fibWeight a m i) from
      Finset.sum_congr rfl fun i _ => by ring, hneg, h]
  have hS : sweight a m ≠ 0 := (sweight_pos ha m).ne'
  rw [hell, deriv_deriv_log_eq hr hf hpos hf', hcurv, zero_div, Fdelta_zero_eq ha m,
    FdeltaScore_zero ha m, αcoef]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-! #### The `v`-slice: `ℓ_{m,vv}(0,0) = ½E D_m²` -/

/-- The `v`-slice of `F_m` against an arbitrary fiber weight, so that one
differentiation stays inside the same family. -/
noncomputable def Fvslice (m : ℕ) (g : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ i ∈ range (m + 1), Real.exp (-(v * dfin m i / Real.sqrt 2)) * g i

theorem Fvslice_zero (m : ℕ) (g : ℕ → ℝ) :
    Fvslice m g 0 = ∑ i ∈ range (m + 1), g i := by
  rw [Fvslice]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- One `v`-derivative brings down `-D_i/√2`, so the slice family is closed under
differentiation. -/
theorem hasDerivAt_Fvslice (m : ℕ) (g : ℕ → ℝ) (v : ℝ) :
    HasDerivAt (Fvslice m g)
      (Fvslice m (fun i => -(dfin m i / Real.sqrt 2) * g i) v) v := by
  simp only [Fvslice]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hlin : HasDerivAt (fun w : ℝ => -(w * dfin m i / Real.sqrt 2))
      (-(dfin m i / Real.sqrt 2)) v := by
    have h : HasDerivAt (fun w : ℝ => w * (-(dfin m i / Real.sqrt 2)))
        (1 * (-(dfin m i / Real.sqrt 2))) v := (hasDerivAt_id v).mul_const _
    refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
    filter_upwards with w
    ring
  refine ((hlin.exp).mul_const (g i)).congr_deriv ?_
  ring

theorem Fvslice_pos (ha : 0 < a) (m : ℕ) (v : ℝ) : 0 < Fvslice m (fibWeight a m) v := by
  rw [Fvslice]
  refine Finset.sum_pos (fun i _ => ?_) ⟨0, mem_range.mpr (Nat.succ_pos m)⟩
  exact mul_pos (Real.exp_pos _) (fibWeight_pos ha m i)

theorem Fuv_u_arg_zero (ha : 0 < a) (m : ℕ) (v : ℝ) :
    Fuv a m 0 v = Fvslice m (fibWeight a m) v := by
  rw [Fuv, Fvslice]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (0 : ℝ) < Real.Gamma (a + (i : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hmi : (0 : ℝ) < Real.Gamma (a + ((m - i : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - i)
  rw [fibWeight, gammaPairInv2, zero_div, add_zero, sub_zero]
  field_simp

/-- **`eq:microcanonical-schur`, entry `(2,2)`.**  `ℓ_{m,vv}(0,0) = ½E D_m²`, so the
`(2,2)` entry `τ/g + κm/2 - ℓ_{m,vv}` of `eq:microcanonical-schur` is
`τ/g + c_m^{(κ)}`. -/
theorem deriv_deriv_ellUV_vv (ha : 0 < a) (m : ℕ) :
    deriv (deriv fun v => ellUV a m 0 v) 0
      = (1 / 2) * condExp a m (fun i => dfin m i ^ 2) := by
  have hs2 := sqrt_two_pos
  have hs2sq := sqrt_two_mul_self
  have hS : sweight a m ≠ 0 := (sweight_pos ha m).ne'
  have hell : (fun v : ℝ => ellUV a m 0 v)
      = fun v : ℝ => Real.log (Fvslice m (fibWeight a m) v) := by
    funext v; rw [ellUV, Fuv_u_arg_zero ha]
  have hkey := deriv_deriv_log_eq (f := Fvslice m (fibWeight a m))
    (f' := Fvslice m (fun i => -(dfin m i / Real.sqrt 2) * fibWeight a m i))
    one_pos (fun x _ => hasDerivAt_Fvslice m (fibWeight a m) x)
    (fun x _ => Fvslice_pos ha m x)
    (hasDerivAt_Fvslice m (fun i => -(dfin m i / Real.sqrt 2) * fibWeight a m i) 0)
  have h0 : Fvslice m (fibWeight a m) 0 = sweight a m := by
    rw [Fvslice_zero, sum_fibWeight ha]
  have h1 : Fvslice m (fun i => -(dfin m i / Real.sqrt 2) * fibWeight a m i) 0 = 0 := by
    rw [Fvslice_zero,
      show ∑ i ∈ range (m + 1), (-(dfin m i / Real.sqrt 2) * fibWeight a m i)
        = (-(1 / Real.sqrt 2)) * ∑ i ∈ range (m + 1), dfin m i * fibWeight a m i from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring, sum_dfin_fibWeight ha m, mul_zero]
  have h2 : Fvslice m (fun i => -(dfin m i / Real.sqrt 2)
        * (-(dfin m i / Real.sqrt 2) * fibWeight a m i)) 0
      = (1 / 2) * (sweight a m * condExp a m (fun i => dfin m i ^ 2)) := by
    rw [Fvslice_zero, ← sum_weighted_eq_condExp ha m (fun i => dfin m i ^ 2), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hell, hkey, h0, h1, h2]
  field

/-! #### The mixed partial: `1 + ℓ_{m,uv}(0,0) = β_m` -/

/-- `∑_i D_i w_i(δ)`, the `D_m`-weighted first moment of the deformed weight. -/
noncomputable def Gsum (a : ℝ) (m : ℕ) (d : ℝ) : ℝ :=
  ∑ i ∈ range (m + 1), dfin m i
    * ((1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
        * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) d)

theorem Gsum_zero (ha : 0 < a) (m : ℕ) : Gsum a m 0 = 0 := by
  have e : ∀ i ∈ range (m + 1),
      dfin m i * ((1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
          * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) 0)
        = dfin m i * fibWeight a m i := by
    intro i _
    have hi : (0 : ℝ) < Real.Gamma (a + (i : ℝ)) :=
      Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
    have hmi : (0 : ℝ) < Real.Gamma (a + ((m - i : ℕ) : ℝ)) :=
      Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)
    have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (m - i)
    rw [fibWeight, gammaPairInv2_zero]
    field_simp
  rw [Gsum, Finset.sum_congr rfl e, sum_dfin_fibWeight ha m]

theorem hasDerivAt_Gsum (ha : 0 < a) (m : ℕ) :
    HasDerivAt (Gsum a m)
      (sweight a m * condExp a m (fun i => dfin m i * xiScore a m i)) 0 := by
  have h : HasDerivAt (Gsum a m)
      (∑ i ∈ range (m + 1), dfin m i
        * ((1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
            * ((-realDigamma (a + (i : ℝ) + 0) + realDigamma (a + ((m - i : ℕ) : ℝ) - 0))
                * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) 0))) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    exact ((hasDerivAt_gammaPairInv2 (u := a + (i : ℝ)) (v := a + ((m - i : ℕ) : ℝ)) (d := 0)
      (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
      (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)).const_mul
        (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))).const_mul (dfin m i)
  refine h.congr_deriv ?_
  rw [← sum_weighted_eq_condExp ha m (fun i => dfin m i * xiScore a m i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (0 : ℝ) < Real.Gamma (a + (i : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hmi : (0 : ℝ) < Real.Gamma (a + ((m - i : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (m - i); linarith)
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - i)
  rw [xiScore, fibWeight, gammaPairInv2, add_zero, sub_zero]
  field

/-- `F_m(u,·)` is the `v`-slice against the `u`-deformed weight. -/
theorem Fuv_eq_Fvslice (a : ℝ) (m : ℕ) (u : ℝ) :
    (fun v : ℝ => Fuv a m u v)
      = Fvslice m (fun i => (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
          * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) (u / Real.sqrt 2)) := rfl

/-- `∂_v ℓ_m(u,0)`, the inner derivative of the mixed partial. -/
theorem deriv_v_ellUV (m : ℕ) {u : ℝ} (hu : u / Real.sqrt 2 ∈ Set.Ioo (-a) a) :
    deriv (fun v => ellUV a m u v) 0
      = (-(1 / Real.sqrt 2) * Gsum a m (u / Real.sqrt 2))
        / Fdelta a m (u / Real.sqrt 2) := by
  set g : ℕ → ℝ := fun i => (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
    * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) (u / Real.sqrt 2) with hg
  have hzero : Fvslice m g 0 = Fdelta a m (u / Real.sqrt 2) := by
    rw [Fvslice_zero, hg, Fdelta]
  have hpos : 0 < Fvslice m g 0 := by rw [hzero]; exact Fdelta_pos m hu
  have hd : HasDerivAt (fun v : ℝ => Real.log (Fvslice m g v))
      (Fvslice m (fun i => -(dfin m i / Real.sqrt 2) * g i) 0 / Fvslice m g 0) 0 :=
    (hasDerivAt_Fvslice m g 0).log hpos.ne'
  have hnum : Fvslice m (fun i => -(dfin m i / Real.sqrt 2) * g i) 0
      = -(1 / Real.sqrt 2) * Gsum a m (u / Real.sqrt 2) := by
    rw [Fvslice_zero, Gsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hg]; ring
  have hell : (fun v : ℝ => ellUV a m u v) = fun v : ℝ => Real.log (Fvslice m g v) := by
    funext v
    rw [ellUV, hg]
    rfl
  rw [hell, hd.deriv, hnum, hzero]

/-- **`eq:microcanonical-schur`, entry `(1,2)`.**  `ℓ_{m,uv}(0,0) = -½E(D_mΞ_m)`, so
the off-diagonal entry `1 + ℓ_{m,uv}` of `eq:microcanonical-schur` is
`eq:finite-law-entries`'s `β_m`. -/
theorem deriv_deriv_ellUV_uv (ha : 0 < a) (m : ℕ) :
    deriv (fun u => deriv (fun v => ellUV a m u v) 0) 0
      = -(1 / 2) * condExp a m (fun i => dfin m i * xiScore a m i) := by
  have hs2 := sqrt_two_pos
  have hs2sq := sqrt_two_mul_self
  have hS : sweight a m ≠ 0 := (sweight_pos ha m).ne'
  have hr : 0 < Real.sqrt 2 * a := by positivity
  have hmem : ∀ x ∈ Set.Ioo (-(Real.sqrt 2 * a)) (Real.sqrt 2 * a),
      x / Real.sqrt 2 ∈ Set.Ioo (-a) a := by
    intro x hx
    exact ⟨by rw [lt_div_iff₀ hs2]; nlinarith [hx.1],
      by rw [div_lt_iff₀ hs2]; nlinarith [hx.2]⟩
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-(Real.sqrt 2 * a)) (Real.sqrt 2 * a) := ⟨by linarith, hr⟩
  have hin : HasDerivAt (fun u : ℝ => u / Real.sqrt 2) (1 / Real.sqrt 2) 0 :=
    (hasDerivAt_id (0 : ℝ)).div_const (Real.sqrt 2)
  -- numerator and denominator of the inner derivative
  have hN : HasDerivAt (fun u : ℝ => -(1 / Real.sqrt 2) * Gsum a m (u / Real.sqrt 2))
      (-(1 / Real.sqrt 2)
        * ((sweight a m * condExp a m (fun i => dfin m i * xiScore a m i))
            * (1 / Real.sqrt 2))) 0 := by
    have hout : HasDerivAt (Gsum a m)
        (sweight a m * condExp a m (fun i => dfin m i * xiScore a m i))
        ((0 : ℝ) / Real.sqrt 2) := by
      rw [zero_div]; exact hasDerivAt_Gsum ha m
    have hcomp := hout.comp (0 : ℝ) hin
    simp only [Function.comp_def] at hcomp
    exact hcomp.const_mul _
  have hD : HasDerivAt (fun u : ℝ => Fdelta a m (u / Real.sqrt 2))
      (FdeltaScore a m ((0 : ℝ) / Real.sqrt 2) * (1 / Real.sqrt 2)) 0 := by
    simpa [Function.comp_def] using
      (hasDerivAt_Fdelta_score m (hmem 0 h0mem)).comp (0 : ℝ) hin
  have hDpos : 0 < Fdelta a m ((0 : ℝ) / Real.sqrt 2) := Fdelta_pos m (hmem 0 h0mem)
  have hquot : HasDerivAt (fun u : ℝ => (-(1 / Real.sqrt 2) * Gsum a m (u / Real.sqrt 2))
        / Fdelta a m (u / Real.sqrt 2))
      ((-(1 / Real.sqrt 2)
          * ((sweight a m * condExp a m (fun i => dfin m i * xiScore a m i))
              * (1 / Real.sqrt 2)) * Fdelta a m ((0 : ℝ) / Real.sqrt 2)
          - (-(1 / Real.sqrt 2) * Gsum a m ((0 : ℝ) / Real.sqrt 2))
              * (FdeltaScore a m ((0 : ℝ) / Real.sqrt 2) * (1 / Real.sqrt 2)))
        / Fdelta a m ((0 : ℝ) / Real.sqrt 2) ^ 2) 0 := hN.div hD hDpos.ne'
  have hev : (fun u => deriv (fun v => ellUV a m u v) 0) =ᶠ[nhds (0 : ℝ)]
      fun u : ℝ => (-(1 / Real.sqrt 2) * Gsum a m (u / Real.sqrt 2))
        / Fdelta a m (u / Real.sqrt 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0mem] with x hx
    exact deriv_v_ellUV m (hmem x hx)
  rw [hev.deriv_eq, hquot.deriv, zero_div, Gsum_zero ha m, Fdelta_zero_eq ha m,
    FdeltaScore_zero ha m]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-! #### `eq:microcanonical-schur` -/

/-- **`eq:microcanonical-schur`.**  The normalized coefficient matrix
`N̂_m^{(κ,τ)} = diag(1,g^{-1/2})M_m^{(κ,τ)}diag(1,g^{-1/2})` is the microcanonical
differential matrix of `thm:ensemble-hierarchy`:
```
  N̂_m^{(κ,τ)} = [[-ℓ_{m,uu}, 1+ℓ_{m,uv}], [1+ℓ_{m,uv}, τ/g+κm/2-ℓ_{m,vv}]]
```
at `(u,v) = (0,0)`. -/
theorem NmatKT_eq_ellUV (ha : 0 < a) (κ τ : ℝ) (m : ℕ) :
    NmatKT a κ τ m
      = ⟨-deriv (deriv fun u => ellUV a m u 0) 0,
          1 + deriv (fun u => deriv (fun v => ellUV a m u v) 0) 0,
          τ / trigamma a + κ * (m : ℝ) / 2
            - deriv (deriv fun v => ellUV a m 0 v) 0⟩ := by
  refine SymMat.ext ?_ ?_ ?_
  · rw [NmatKT_a11, deriv_deriv_ellUV_uu ha m, neg_neg]
  · rw [NmatKT_a12, deriv_deriv_ellUV_uv ha m, beta_eq_condExp ha m]
    ring
  · change τ / trigamma a + ckappa a κ m = _
    rw [deriv_deriv_ellUV_vv ha m, ckappa_eq_condExp ha κ m]
    ring

end TuranBessel
