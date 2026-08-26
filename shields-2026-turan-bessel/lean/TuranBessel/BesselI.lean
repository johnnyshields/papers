/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Hypergeometric

/-!
# The modified Bessel function `I_ν` and the identity `eq:I-Z`

Formalizes `shields-2026-turan-bessel.tex`, «Classical scalar Bessel
directions» (`sec:scalar`), the identity
```
  I_{a-1}(2√λ) = λ^{(a-1)/2} Z(a,λ)                                    (eq:I-Z)
```
and the structural facts about `I_ν` that it rests on.

Mathlib carries no modified Bessel function, and the vendored PR defers it
(the name `I` clashes with `Complex.I`), so it is defined here from the same
regularized `₀F₁` the PR uses for `J`:
```
  I_a(x) = (x/2)^a · ₀F̃₁(;a+1;(x/2)²),
```
i.e. `besselJ` with the sign of the hypergeometric argument flipped.  That is
the *only* difference between the two, which is why every structural result
below is the `J`-result with its sign bookkeeping changed — and why the parity
in integer order comes out as `I_{-n} = I_n` rather than `J_{-n} = (-1)^n J_n`.
`regularizedHGFun_zero_singleton_neg_nat_add_one` converts the order `-n` into a
factor `w^n`, where `w` is the hypergeometric argument; on the `J` side
`w = -(x/2)²` contributes the `(-1)^n`, and on the `I` side `w = (x/2)²`
contributes nothing.

`besselIReal` is the real-variable function of a real order, which is what the
`sec:scalar` functionals `G_ν, P_ν, H_ν` are built from; `ofReal_besselIReal`
identifies it with the complex one on the positive axis.

## Proved here

* `besselI`, `besselIReal` and their agreement on `x > 0`;
* `besselJ_mul_I`: `J_n(ix) = i^n I_n(x)` for natural `n`;
* analyticity on `slitPlane`, and everywhere for integer order;
* the value at `0`, and the parities `I_n(-x) = (-1)^n I_n(x)`, `I_{-n} = I_n`;
* `eq:I-Z`, both in the `(x/2)²` form (`besselI_eq_Zfun`) and in the paper's
  `2√λ` form (`besselIReal_eq_rpow_mul_Zfun`, `ofReal_besselI_eq_Zfun`);
* `besselIReal_pos`: `I_ν(x) > 0` for `ν > -1`, `x > 0`;
* `log_besselIReal`, `log_besselIReal_eq_Zfun`: the logarithm of `eq:I-Z`, which
  is the identity the `sec:scalar` dictionary `eq:U-L`, `eq:G-L` differentiates.

Sorry-free.
-/

namespace TuranBessel

open Complex

/-! ### Definition -/

/-- Modified Bessel function of the first kind,
`I_a(x) = (x/2)^a · ₀F̃₁(;a+1;(x/2)²)`.  This is `Complex.besselJ` with the sign
of the hypergeometric argument flipped. -/
noncomputable def besselI (a x : ℂ) : ℂ :=
  (x / 2) ^ a * regularizedHGFun 0 {a + 1} ((x / 2) ^ 2)

theorem besselI_def :
    besselI = fun a x => (x / 2) ^ a * regularizedHGFun 0 {a + 1} ((x / 2) ^ 2) := rfl

/-- `I_a` is `J_a` on the rotated axis: `J_n(ix) = i^n I_n(x)`.  Stated for
natural `n` so that both prefactors are `Monoid.npow` and no branch of the
complex power is involved. -/
theorem besselJ_mul_I (n : ℕ) (x : ℂ) :
    besselJ (n : ℂ) (Complex.I * x) = Complex.I ^ n * besselI (n : ℂ) x := by
  rw [besselJ, besselI, cpow_natCast, cpow_natCast]
  have h : -(Complex.I * x / 2) ^ 2 = (x / 2) ^ 2 := by
    have : (Complex.I * x / 2) ^ 2 = Complex.I ^ 2 * (x / 2) ^ 2 := by ring
    rw [this, Complex.I_sq]
    ring
  rw [h, mul_div_assoc, mul_pow]
  ring

/-! ### Parity -/

/-- `I_n` is even or odd according to the parity of the integer `n`. -/
theorem besselI_int_neg (a : ℤ) (x : ℂ) :
    besselI (a : ℂ) (-x) = (-1) ^ a * besselI (a : ℂ) x := by
  simp [besselI_def, ← mul_assoc, neg_div, ← mul_zpow]

theorem odd_besselI {a : ℤ} (ha : Odd a) : Function.Odd (besselI (a : ℂ)) := by
  intro x
  simp [besselI_int_neg, ha.neg_zpow]

theorem even_besselI {a : ℤ} (ha : Even a) : Function.Even (besselI (a : ℂ)) := by
  intro x
  simp [besselI_int_neg, ha.neg_zpow]

/-- `I_{-n} = I_n` for integer `n`.  Unlike `J`, no sign appears: the `(-1)^n`
that `besselJ_neg_int` picks up comes from `(-(x/2)²)^n`, and the modified
function has no such sign to contribute. -/
theorem besselI_neg_int (a : ℤ) (x : ℂ) : besselI (-(a : ℂ)) x = besselI (a : ℂ) x := by
  wlog! ha : 0 ≤ a
  · have := this (-a) x (by simpa using ha.le)
    simp only [Int.cast_neg, neg_neg] at this
    exact this.symm
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  push_cast
  have h : (x / 2) ^ (a : ℂ) = (x / 2) ^ (-a : ℂ) * ((x / 2) ^ 2) ^ a := by
    by_cases hx : x = 0
    · by_cases ha : a = 0 <;> simp [hx, ha]
    rw [← pow_mul, ← cpow_natCast, ← cpow_add _ _ (by simpa using hx)]
    grind
  unfold besselI
  rw [regularizedHGFun_zero_singleton_neg_nat_add_one, h]
  ring

/-! ### Analyticity -/

/-- `I_a` is analytic outside of the branch cut on the negative real axis. -/
theorem analyticAt_besselI (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    AnalyticAt ℂ (besselI a) x := by
  have hs : x / 2 ∈ slitPlane := by
    simp only [mem_slitPlane_iff, div_re, div_im] at *
    norm_num at *
    tauto
  have hb : AnalyticAt ℂ (fun z : ℂ => z / 2) x := analyticAt_id.div_const
  exact (hb.cpow analyticAt_const hs).mul
    ((analyticAt_regularizedHGFun_zero _).comp (hb.pow 2))

theorem analyticOnNhd_besselI (a : ℂ) : AnalyticOnNhd ℂ (besselI a) slitPlane :=
  fun _ hz => analyticAt_besselI a hz

/-- For integer order there is no branch cut: `I_n` is entire. -/
theorem analyticAt_besselI_int (a : ℤ) (x : ℂ) : AnalyticAt ℂ (besselI (a : ℂ)) x := by
  wlog! ha : 0 ≤ a
  · have h := this (-a) x (by simpa using ha.le)
    rw [Int.cast_neg] at h
    rwa [← funext (besselI_neg_int a)]
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have hb : AnalyticAt ℂ (fun z : ℂ => z / 2) x := analyticAt_id.div_const
  have : AnalyticAt ℂ (fun x => (x / 2) ^ a * regularizedHGFun 0 {(a : ℂ) + 1} ((x / 2) ^ 2)) x :=
    (hb.pow a).mul ((analyticAt_regularizedHGFun_zero _).comp (hb.pow 2))
  simpa [besselI_def] using this

theorem analyticOnNhd_besselI_int (a : ℤ) : AnalyticOnNhd ℂ (besselI (a : ℂ)) .univ :=
  fun z _ => analyticAt_besselI_int a z

/-! ### Value at the origin -/

theorem besselI_zero (a : ℂ) : besselI a 0 = if a = 0 then 1 else 0 := by
  split_ifs with h <;> simp [besselI, h, regularizedHGFunCoeff]

/-! ### `eq:I-Z` -/

/-- **`eq:I-Z`, hypergeometric form.**  `I_{a-1}(x) = (x/2)^{a-1} Z(a,(x/2)²)`.
The index drops by one because the hypergeometric factor of `I_ν` sits at
`ν+1`; at `x = 2√λ` this is the paper's identity, proved as
`besselIReal_eq_rpow_mul_Zfun` below. -/
theorem besselI_eq_Zfun (a x : ℝ) :
    besselI ((a : ℂ) - 1) (x : ℂ)
      = ((x : ℂ) / 2) ^ ((a : ℂ) - 1) * ((Zfun a ((x / 2) ^ 2) : ℝ) : ℂ) := by
  rw [ofReal_Zfun, besselI]
  push_cast
  ring_nf

section BesselIReal

variable {ν x : ℝ}

/-! ### The real-variable modified Bessel function -/

/-- `I_ν(x)` for real order and real argument, `I_ν(x) = (x/2)^ν Z(ν+1,(x/2)²)`,
with `(x/2)^ν` the real power.  This is the function the `sec:scalar`
functionals `G_ν`, `P_ν`, `H_ν^{(κ)}` of `eq:Gnu`--`eq:Hnu-kappa` differentiate. -/
noncomputable def besselIReal (ν x : ℝ) : ℝ :=
  (x / 2) ^ ν * Zfun (ν + 1) ((x / 2) ^ 2)

/-- On the positive axis the real and complex definitions agree. -/
theorem ofReal_besselIReal (hx : 0 < x) :
    ((besselIReal ν x : ℝ) : ℂ) = besselI (ν : ℂ) (x : ℂ) := by
  rw [besselIReal, besselI]
  push_cast [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ x / 2), ofReal_Zfun]
  norm_num

/-- **`eq:I-Z`.**  `I_{a-1}(2√λ) = λ^{(a-1)/2} Z(a,λ)` for `λ > 0`. -/
theorem besselIReal_eq_rpow_mul_Zfun (a : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    besselIReal (a - 1) (2 * Real.sqrt lam) = lam ^ ((a - 1) / 2) * Zfun a lam := by
  have hs : 2 * Real.sqrt lam / 2 = Real.sqrt lam := by ring
  have hsq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
  have h1 : a - 1 + 1 = a := by ring
  have h2 : 1 / (2 : ℝ) * (a - 1) = (a - 1) / 2 := by ring
  rw [besselIReal, hs, hsq, Real.sqrt_eq_rpow, ← Real.rpow_mul hlam.le, h1, h2]

/-- **`eq:I-Z`, complex form.**  The same identity read off the complex `besselI`
on the positive axis. -/
theorem ofReal_besselI_eq_Zfun (a : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    besselI ((a : ℂ) - 1) ((2 * Real.sqrt lam : ℝ) : ℂ)
      = ((lam ^ ((a - 1) / 2) * Zfun a lam : ℝ) : ℂ) := by
  have hx : 0 < 2 * Real.sqrt lam := by positivity
  rw [← besselIReal_eq_rpow_mul_Zfun a hlam, ofReal_besselIReal hx]
  push_cast
  ring_nf

/-! ### Positivity -/

/-- `I_ν(x) > 0` for `ν > -1` and `x > 0`: at a nonnegative argument `Z(ν+1,·)`
has nonnegative terms and a positive constant term, and the prefactor `(x/2)^ν`
is a real power of a positive base. -/
theorem besselIReal_pos (hν : -1 < ν) (hx : 0 < x) : 0 < besselIReal ν x :=
  mul_pos (Real.rpow_pos_of_pos (by linarith) ν)
    (Zfun_pos (by linarith) (by positivity))

theorem besselIReal_ne_zero (hν : -1 < ν) (hx : 0 < x) : besselIReal ν x ≠ 0 :=
  (besselIReal_pos hν hx).ne'

/-! ### Logarithmic form: the input to the `sec:scalar` dictionary -/

/-- `log I_ν(x) = ν log(x/2) + log Z(ν+1,(x/2)²)`.  The order dependence of
`log I_ν` splits into a term affine in `ν` and `log Z`, so every second-order
`ν`-derivative of `log I_ν` — in particular `G_ν = -∂_ν² log I_ν` of `eq:Gnu` —
is the corresponding derivative of `log Z` alone, which is `eq:G-L`'s `-L_aa`. -/
theorem log_besselIReal (hν : -1 < ν) (hx : 0 < x) :
    Real.log (besselIReal ν x)
      = ν * Real.log (x / 2) + Real.log (Zfun (ν + 1) ((x / 2) ^ 2)) := by
  have hz : Zfun (ν + 1) ((x / 2) ^ 2) ≠ 0 :=
    (Zfun_pos (by linarith) (by positivity)).ne'
  rw [besselIReal, Real.log_mul (by positivity) hz, Real.log_rpow (by positivity)]

/-- The logarithm of `eq:I-Z` in the paper's variables `ν = a-1`, `z = 2√λ`:
`log I_ν(2√λ) = (a-1)/2 · log λ + log Z(a,λ)`.  This is the identity that
`eq:U-L` and `eq:G-L` differentiate. -/
theorem log_besselIReal_eq_Zfun {a lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    Real.log (besselIReal (a - 1) (2 * Real.sqrt lam))
      = (a - 1) / 2 * Real.log lam + Real.log (Zfun a lam) := by
  rw [besselIReal_eq_rpow_mul_Zfun a hlam,
    Real.log_mul (by positivity) (Zfun_pos ha hlam.le).ne', Real.log_rpow hlam]

end BesselIReal

end TuranBessel
