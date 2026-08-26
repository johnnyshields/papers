/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.WeightedDominance
import ForgacsTran.SignAlternation

/-!
# The phase count

`thm:weighted-dominance` exists to supply one thing to the count: the sign of the
normalized coefficient at each phase point.  This module takes it from there.

## Main statements

* `principal_sign_at_phase_point` — at a phase point `Φ_M(θ) = kπ` of
  `eq:Phi-def`, `eq:principal-decomposition`'s principal term is `2(-1)^k|W|` and
  `eq:dominance-bound` leaves the whole normalized coefficient with that sign and
  magnitude at least `\tfrac32|W|`.
* `phase_alternating`, `alternating_of_consecutive_signs` — consecutive phase
  points have opposite parity, hence opposite sign.
* `exists_phase_points` — a continuous strictly increasing `Φ` whose range covers
  `[k_0π, (k_0+n)π]` meets `πℤ` at `n+1` increasing points.
* `exists_phase_points_of_length` — the count: an increase of at least `L` gives
  `n ≥ L/π - 2` gaps.
* `exists_alternating_phase_points` — the assembly, and the deliverable: from
  `eq:dominance-bound` on a retained component, `n+1` strictly increasing points
  at which the coefficient polynomial alternates in sign, with
  `L/π - 2 ≤ n`.  This is exactly the `x`/`hx`/`hmem`/`halt` supply that
  `Bridge.FTInputs.ofSignAlternation` takes as a hypothesis.
* `exists_interiorZeros_of_dominance` — the same fed through
  `SignAlternation.exists_interiorZeros_of_alternating`, giving the `Finset` of
  distinct complex zeros directly.
* `card_le_natDegree_of_isRoot`, `count_add_card_le_natDegree` — the counting
  step behind the upper half of `eq:angular-discrepancy`: zeros with
  multiplicity inside an angular window, plus distinct zeros supplied outside it
  by `eq:angular-distinct-lower` on the two complementary intervals, cannot
  exceed the degree.

## Implementation notes

**Scope.**  Three inputs are carried as explicit named hypotheses on given
functions rather than derived, because the manuscript imports them from
`Forgacs2017RationalDenominator` through `thm:FT-geometry`: the spectral
coordinate `z` and its strict monotonicity, the principal amplitude `W` with a
continuous branch `ψ` of its argument in polar form, and
`eq:principal-decomposition` itself, which is `lem:contour-separation`.  The
strict monotonicity of `Φ` is `eq:phase-derivative-bound` for large `M`, also a
hypothesis.  What is derived is everything downstream of them: the phase points,
their count, the sign at each, the alternation, and the zeros.

The paper's count is `L/π - 1` where this proves `L/π - 2`; the extra unit is
the cost of not assuming where `Φ(a)` sits relative to `πℤ`, and it is
absorbed into `prop:angular-discrepancy`'s `C_0`.  Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Angular discrepancy
and proof of the main theorem» (`subsec:proof`, `prop:angular-discrepancy`,
`eq:Phi-def`, `eq:angular-distinct-lower`).

## Tags

phase count, angular discrepancy, interior zeros
-/

namespace ForgacsTran

open Complex

/-! ### The sign at a phase point -/

/-- **Paper `subsec:proof`, `prop:angular-discrepancy` — the sign at a phase
point.**  Let `ψ` be a continuous branch of `arg W`, so `W = |W|e^{iψ}`, and let
`θ` be a phase point of `eq:Phi-def`: `Φ_M(θ) = (M+1)θ - ψ(θ) = kπ`.  Then the
principal term of `eq:principal-decomposition` is `2(-1)^k|W|`, and
`eq:dominance-bound` leaves the normalized coefficient with that sign and
magnitude at least `\tfrac32|W|`.

This is the step `thm:weighted-dominance` exists to supply and that
`Bridge.FTInputs.ofSignAlternation` currently takes as its `halt` hypothesis. -/
theorem principal_sign_at_phase_point {W : ℂ} {ψ φ Rm G : ℝ} {k : ℤ}
    (hpolar : W = (‖W‖ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
    (hphase : φ - ψ = (k : ℝ) * Real.pi)
    (hdec : G = 2 * (W * Complex.exp (-(φ : ℂ) * Complex.I)).re + Rm)
    (hR : |Rm| ≤ ‖W‖ / 2) :
    3 / 2 * ‖W‖ ≤ (-1 : ℝ) ^ k * G := by
  have hkey : (W * Complex.exp (-(φ : ℂ) * Complex.I)).re = ‖W‖ * (-1 : ℝ) ^ k := by
    have hprod : W * Complex.exp (-(φ : ℂ) * Complex.I)
        = (‖W‖ : ℂ) * Complex.exp (((ψ - φ : ℝ) : ℂ) * Complex.I) := by
      conv_lhs => rw [hpolar]
      rw [mul_assoc, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hprod, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    congr 1
    have : (ψ - φ : ℝ) = -((k : ℝ) * Real.pi) := by linarith
    rw [this, Real.cos_neg, Real.cos_int_mul_pi]
  have hsq : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    rw [show k + k = 2 * k by ring, zpow_mul]
    norm_num
  have hsgn : |(-1 : ℝ) ^ k| = 1 := by
    rcases Int.even_or_odd k with he | ho
    · rw [he.neg_one_zpow]; norm_num
    · rw [ho.neg_one_zpow]; norm_num
  have hRm : (-1 : ℝ) ^ k * Rm ≥ -(‖W‖ / 2) := by
    have h1 : |(-1 : ℝ) ^ k * Rm| ≤ ‖W‖ / 2 := by
      rw [abs_mul, hsgn, one_mul]; exact hR
    linarith [neg_abs_le ((-1 : ℝ) ^ k * Rm), h1]
  rw [hdec, mul_add, hkey]
  have hexp : (-1 : ℝ) ^ k * (2 * (‖W‖ * (-1 : ℝ) ^ k)) = 2 * ‖W‖ := by
    have : (-1 : ℝ) ^ k * (2 * (‖W‖ * (-1 : ℝ) ^ k))
        = 2 * ‖W‖ * ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) := by ring
    rw [this, hsq, mul_one]
  rw [hexp]
  linarith [hRm]

/-! ### Alternation along the phase points -/

/-- **Paper `subsec:proof`, `prop:angular-discrepancy` — consecutive phase points
alternate.**  If the `i`-th value carries the sign `(-1)^{k_0+i}` with a strictly
positive margin, then consecutive values have opposite signs, which is the
`halt` hypothesis of `Bridge.FTInputs.ofSignAlternation`. -/
theorem phase_alternating {G c : ℕ → ℝ} {k₀ : ℤ}
    (h : ∀ i, 0 < c i ∧ c i ≤ (-1 : ℝ) ^ (k₀ + (i : ℤ)) * G i) (i : ℕ) :
    G i * G (i + 1) < 0 := by
  have hne : (-1 : ℝ) ≠ 0 := by norm_num
  set s : ℝ := (-1 : ℝ) ^ (k₀ + (i : ℤ)) with hs
  have hsucc : (-1 : ℝ) ^ (k₀ + ((i + 1 : ℕ) : ℤ)) = -s := by
    rw [hs, show k₀ + ((i + 1 : ℕ) : ℤ) = (k₀ + (i : ℤ)) + 1 by push_cast; ring,
      zpow_add₀ hne, zpow_one]
    ring
  have hsq : s * s = 1 := by
    rw [hs, ← zpow_add₀ hne, show (k₀ + (i : ℤ)) + (k₀ + (i : ℤ)) = 2 * (k₀ + (i : ℤ)) by ring,
      zpow_mul]
    norm_num
  have h1 : 0 < s * G i := lt_of_lt_of_le (h i).1 (h i).2
  have h2 : 0 < -s * G (i + 1) := by
    have := lt_of_lt_of_le (h (i + 1)).1 (h (i + 1)).2
    rwa [hsucc] at this
  nlinarith [h1, h2, hsq]

/-! ### The phase points exist -/

/-- **Paper `subsec:proof`, `prop:angular-discrepancy` — the phase points.**
A continuous, strictly increasing `Φ` on `[a,b]` whose range covers
`[k_0π, (k_0+n)π]` meets `πℤ` at `n+1` strictly increasing points.
In the paper `Φ = Φ_M` of `eq:Phi-def`, whose strict monotonicity for large `M`
is `eq:phase-derivative-bound`. -/
theorem exists_phase_points {Φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn Φ (Set.Icc a b)) (hmono : StrictMonoOn Φ (Set.Icc a b))
    (n : ℕ) (k₀ : ℤ)
    (hlo : Φ a ≤ (k₀ : ℝ) * Real.pi)
    (hhi : ((k₀ + (n : ℤ) : ℤ) : ℝ) * Real.pi ≤ Φ b) :
    ∃ x : Fin (n + 1) → ℝ, StrictMono x ∧ (∀ i, x i ∈ Set.Icc a b) ∧
      ∀ i : Fin (n + 1), Φ (x i) = ((k₀ + (i : ℕ) : ℤ) : ℝ) * Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmem : ∀ i : Fin (n + 1),
      ((k₀ + (i : ℕ) : ℤ) : ℝ) * Real.pi ∈ Set.Icc (Φ a) (Φ b) := by
    intro i
    have hin : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    constructor
    · refine le_trans hlo ?_
      have : (k₀ : ℝ) ≤ ((k₀ + (i : ℕ) : ℤ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      exact mul_le_mul_of_nonneg_right this hpi.le
    · refine le_trans ?_ hhi
      have : ((k₀ + (i : ℕ) : ℤ) : ℝ) ≤ ((k₀ + (n : ℤ) : ℤ) : ℝ) := by
        have hle : ((i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hin
        push_cast
        linarith
      exact mul_le_mul_of_nonneg_right this hpi.le
  choose x hx hΦx using fun i : Fin (n + 1) =>
    intermediate_value_Icc hab hcont (hmem i)
  refine ⟨x, ?_, hx, hΦx⟩
  intro i j hij
  have hlt : Φ (x i) < Φ (x j) := by
    rw [hΦx i, hΦx j]
    have : ((k₀ + (i : ℕ) : ℤ) : ℝ) < ((k₀ + (j : ℕ) : ℤ) : ℝ) := by
      have hij' : (i : ℕ) < (j : ℕ) := hij
      have h2 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij'
      push_cast
      linarith
    exact mul_lt_mul_of_pos_right this hpi
  exact (hmono.lt_iff_lt (hx i) (hx j)).mp hlt

/-- The two-point form of `phase_alternating`: consecutive phase points, whose
parities differ, give values of opposite sign. -/
theorem alternating_of_consecutive_signs {G₀ G₁ c₀ c₁ : ℝ} {k : ℤ}
    (h0 : 0 < c₀) (h1 : 0 < c₁)
    (hg0 : c₀ ≤ (-1 : ℝ) ^ k * G₀) (hg1 : c₁ ≤ (-1 : ℝ) ^ (k + 1) * G₁) :
    G₀ * G₁ < 0 := by
  have hne : (-1 : ℝ) ≠ 0 := by norm_num
  set s : ℝ := (-1 : ℝ) ^ k with hs
  have hsucc : (-1 : ℝ) ^ (k + 1) = -s := by rw [hs, zpow_add₀ hne, zpow_one]; ring
  have hsq : s * s = 1 := by
    rw [hs, ← zpow_add₀ hne, show k + k = 2 * k by ring, zpow_mul]
    norm_num
  rw [hsucc] at hg1
  nlinarith [lt_of_lt_of_le h0 hg0, lt_of_lt_of_le h1 hg1, hsq]

/-- **Paper `subsec:proof`, `prop:angular-discrepancy` — how many phase points an
interval carries.**  If `Φ` increases by at least `L ≥ π` across `[a,b]`,
then `πℤ` is met at `n+1` points with `L/π - 2 ≤ n`.

**Differs from the paper's route.**  The paper counts `L/π - 1` phase points,
reading the first one off the position of `Φ(a)`.  Here the endpoints of the
integer range are taken as `⌈ Φ(a)/π⌉` and `⌊ Φ(b)/π⌋`,
which assumes nothing about where `Φ(a)` sits relative to `πℤ` and costs
one unit; it is absorbed into `prop:angular-discrepancy`'s `C_0`. -/
theorem exists_phase_points_of_length {Φ : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn Φ (Set.Icc a b)) (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hL : Real.pi ≤ L) (hΦ : L ≤ Φ b - Φ a) :
    ∃ (n : ℕ) (k₀ : ℤ) (x : Fin (n + 1) → ℝ),
      L / Real.pi - 2 ≤ (n : ℝ) ∧ StrictMono x ∧ (∀ i, x i ∈ Set.Icc a b) ∧
      ∀ i : Fin (n + 1), Φ (x i) = ((k₀ + (i : ℕ) : ℤ) : ℝ) * Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set k₀ : ℤ := ⌈Φ a / Real.pi⌉ with hk₀
  set m : ℤ := ⌊Φ b / Real.pi⌋ with hm
  have hceil : Φ a / Real.pi ≤ (k₀ : ℝ) := Int.le_ceil _
  have hceil' : (k₀ : ℝ) < Φ a / Real.pi + 1 := Int.ceil_lt_add_one _
  have hfloor : (m : ℝ) ≤ Φ b / Real.pi := Int.floor_le _
  have hfloor' : Φ b / Real.pi - 1 < (m : ℝ) := Int.sub_one_lt_floor _
  have hdiv : Φ a / Real.pi + 1 ≤ Φ b / Real.pi := by
    rw [div_add' _ _ _ (ne_of_gt hpi), div_le_div_iff_of_pos_right hpi]
    linarith
  have hkm : k₀ ≤ m := by
    rw [hm, Int.le_floor]
    linarith
  set n : ℕ := (m - k₀).toNat with hn
  have hnval : ((n : ℕ) : ℤ) = m - k₀ := Int.toNat_of_nonneg (by omega)
  have hnr : (n : ℝ) = (m : ℝ) - (k₀ : ℝ) := by
    have := congrArg (fun t : ℤ => (t : ℝ)) hnval
    push_cast at this
    exact this
  have hcount : L / Real.pi - 2 ≤ (n : ℝ) := by
    rw [hnr]
    have hLpi : L / Real.pi ≤ (Φ b - Φ a) / Real.pi := by gcongr
    rw [sub_div] at hLpi
    linarith
  have hlo : Φ a ≤ (k₀ : ℝ) * Real.pi := by
    rw [div_le_iff₀ hpi] at hceil; linarith
  have hhi : ((k₀ + (n : ℤ) : ℤ) : ℝ) * Real.pi ≤ Φ b := by
    have : ((k₀ + (n : ℤ) : ℤ) : ℝ) = (m : ℝ) := by
      have : k₀ + ((n : ℕ) : ℤ) = m := by omega
      exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) this
    rw [this, ← le_div_iff₀ hpi]
    exact hfloor
  obtain ⟨x, hxmono, hxmem, hxΦ⟩ := exists_phase_points hab hcont hmono n k₀ hlo hhi
  exact ⟨n, k₀, x, hcount, hxmono, hxmem, hxΦ⟩

/-! ### From `eq:dominance-bound` to a supply of interior zeros -/

/-- **Paper `subsec:proof`, `prop:angular-discrepancy` — the alternating phase
points.**  Everything the count needs, assembled: a strictly increasing phase
function `Φ = φ - ψ` on a retained component `[a,b]`, a strictly increasing
spectral coordinate `z`, `eq:principal-decomposition` for the real coefficient
polynomial `P` normalized by a positive `τ`, and `eq:dominance-bound`
`|R_M| ≤ |W|/2`.

Out come `n+1` strictly increasing points of `S` at which `P` alternates in sign,
with `L/π - 2 ≤ n`.  That is precisely the `x`/`hx`/`hmem`/`halt` supply of
`Bridge.FTInputs.ofSignAlternation`, which `thm:weighted-dominance` exists to
produce and which that constructor currently takes as a hypothesis.

`ψ` is a continuous branch of `arg W` — the hypothesis is the polar form
`W = |W|e^{iψ}` — and `φ` is `(M+1)θ`; neither is constrained further, so
the statement is about any phase function of that shape. -/
theorem exists_alternating_phase_points
    {Φ φ ψ z τ Rm : ℝ → ℝ} {W : ℝ → ℂ} {P : Polynomial ℝ} {S : Set ℝ}
    {a b L : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn Φ (Set.Icc a b)) (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hL : Real.pi ≤ L) (hΦ : L ≤ Φ b - Φ a)
    (hΦdef : ∀ θ ∈ Set.Icc a b, Φ θ = φ θ - ψ θ)
    (hzmono : StrictMonoOn z (Set.Icc a b))
    (hzS : ∀ θ ∈ Set.Icc a b, z θ ∈ S)
    (hτ : ∀ θ ∈ Set.Icc a b, 0 < τ θ)
    (hWne : ∀ θ ∈ Set.Icc a b, W θ ≠ 0)
    (hpolar : ∀ θ ∈ Set.Icc a b,
      W θ = (‖W θ‖ : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I))
    (hdec : ∀ θ ∈ Set.Icc a b, τ θ * P.eval (z θ)
      = 2 * (W θ * Complex.exp (-(φ θ : ℂ) * Complex.I)).re + Rm θ)
    (hdom : ∀ θ ∈ Set.Icc a b, |Rm θ| ≤ ‖W θ‖ / 2) :
    ∃ (n : ℕ) (y : Fin (n + 1) → ℝ), L / Real.pi - 2 ≤ (n : ℝ) ∧ StrictMono y ∧
      (∀ i, y i ∈ S) ∧
      ∀ i : Fin n, P.eval (y i.castSucc) * P.eval (y i.succ) < 0 := by
  obtain ⟨n, k₀, x, hcount, hxmono, hxmem, hxΦ⟩ :=
    exists_phase_points_of_length hab hcont hmono hL hΦ
  -- the sign of the normalized coefficient at each phase point
  have hsign : ∀ i : Fin (n + 1),
      3 / 2 * ‖W (x i)‖ ≤ (-1 : ℝ) ^ (k₀ + (i : ℕ) : ℤ) * (τ (x i) * P.eval (z (x i))) := by
    intro i
    refine principal_sign_at_phase_point (hpolar (x i) (hxmem i)) ?_
      (hdec (x i) (hxmem i)) (hdom (x i) (hxmem i))
    have hthis := hxΦ i
    rw [hΦdef (x i) (hxmem i)] at hthis
    exact hthis
  have hWpos : ∀ i : Fin (n + 1), 0 < 3 / 2 * ‖W (x i)‖ := by
    intro i
    have hne := hWne (x i) (hxmem i)
    have : 0 < ‖W (x i)‖ := norm_pos_iff.mpr hne
    linarith
  refine ⟨n, fun i => z (x i), hcount,
    fun i j hij => hzmono (hxmem i) (hxmem j) (hxmono hij),
    fun i => hzS (x i) (hxmem i), ?_⟩
  intro i
  have hk : ((k₀ + (i.succ : ℕ) : ℤ)) = (k₀ + (i.castSucc : ℕ) : ℤ) + 1 := by
    simp [Fin.val_succ, Fin.val_castSucc]
    ring
  have h0 := hsign i.castSucc
  have h1 := hsign i.succ
  rw [hk] at h1
  have hprod := alternating_of_consecutive_signs (hWpos i.castSucc) (hWpos i.succ) h0 h1
  have hτ0 := hτ (x i.castSucc) (hxmem i.castSucc)
  have hτ1 := hτ (x i.succ) (hxmem i.succ)
  have hττ : 0 < τ (x i.castSucc) * τ (x i.succ) := mul_pos hτ0 hτ1
  by_contra hcon
  have hcon' : 0 ≤ P.eval (z (x i.castSucc)) * P.eval (z (x i.succ)) := not_lt.mp hcon
  nlinarith [hprod, mul_nonneg hττ.le hcon']

/-- **Paper `subsec:proof`, `prop:angular-discrepancy`, `eq:angular-distinct-lower`.**
The alternating phase points fed through the intermediate-value count: from
`eq:dominance-bound` on a retained component, a `Finset` of at least
`L/π - 2` distinct complex zeros of the coefficient polynomial inside the image
of that component. -/
theorem exists_interiorZeros_of_dominance
    {Φ φ ψ z τ Rm : ℝ → ℝ} {W : ℝ → ℂ} {P : Polynomial ℝ} {S : Set ℝ}
    {a b L : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn Φ (Set.Icc a b)) (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hL : Real.pi ≤ L) (hΦ : L ≤ Φ b - Φ a)
    (hΦdef : ∀ θ ∈ Set.Icc a b, Φ θ = φ θ - ψ θ)
    (hzmono : StrictMonoOn z (Set.Icc a b))
    (hS : S.OrdConnected) (hzS : ∀ θ ∈ Set.Icc a b, z θ ∈ S)
    (hτ : ∀ θ ∈ Set.Icc a b, 0 < τ θ)
    (hWne : ∀ θ ∈ Set.Icc a b, W θ ≠ 0)
    (hpolar : ∀ θ ∈ Set.Icc a b,
      W θ = (‖W θ‖ : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I))
    (hdec : ∀ θ ∈ Set.Icc a b, τ θ * P.eval (z θ)
      = 2 * (W θ * Complex.exp (-(φ θ : ℂ) * Complex.I)).re + Rm θ)
    (hdom : ∀ θ ∈ Set.Icc a b, |Rm θ| ≤ ‖W θ‖ / 2) :
    ∃ (n : ℕ) (Z : Finset ℂ), L / Real.pi - 2 ≤ (n : ℝ) ∧ n ≤ Z.card ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' S) := by
  obtain ⟨n, y, hcount, hymono, hymem, halt⟩ :=
    exists_alternating_phase_points hab hcont hmono hL hΦ hΦdef hzmono hzS hτ hWne hpolar
      hdec hdom
  obtain ⟨Z, hZcard, hZroot, hZmem⟩ :=
    exists_interiorZeros_of_alternating P hS y hymono hymem halt
  exact ⟨n, Z, hcount, hZcard, hZroot, hZmem⟩


/-! ### The zeros land strictly inside the block

`exists_interiorZeros_of_alternating` reports the zeros as members of the
order-connected set the phase points were drawn from.  Summing across the blocks
of `eq:Omega-M` needs more than that: two neighbouring blocks share an endpoint
whenever the window between them is empty, so a bound that puts both blocks'
zeros in their closed `z`-images cannot separate them and the sum
`∑ᵢ nᵢ` collapses.

The zeros are strictly interior — `exists_strictMono_zeros_of_alternating`
already places each one *inside* its gap — so the strict form costs nothing but
saying so.  It is what `AngularBlocks.exists_blockZeros` uses, and it is why the
block family there needs only `Rᵢ ≤ L_{i+1}` rather than a strict separation
that the empty window does not supply. -/

/-- **`eq:angular-distinct-lower` with the zeros strictly inside.**  The
alternation count of `SignAlternation.exists_interiorZeros_of_alternating`,
reporting the zeros in the *open* interval spanned by the points rather than in
a set carried along. -/
theorem exists_interiorZeros_of_alternating_Ioo
    (P : Polynomial ℝ) {u v : ℝ} {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hmem : ∀ k, x k ∈ Set.Icc u v)
    (halt : ∀ k : Fin n, P.eval (x k.castSucc) * P.eval (x k.succ) < 0) :
    ∃ Z : Finset ℂ, n ≤ Z.card ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' Set.Ioo u v) := by
  classical
  obtain ⟨w, hwmono, hwzero, hwmem⟩ :=
    exists_strictMono_zeros_of_alternating P.continuous x hx halt
  have hwS : ∀ k, w k ∈ Set.Ioo u v := by
    intro k
    exact ⟨lt_of_le_of_lt (hmem k.castSucc).1 (hwmem k).1,
      lt_of_lt_of_le (hwmem k).2 (hmem k.succ).2⟩
  refine ⟨Finset.image (fun k : Fin n => ((w k : ℝ) : ℂ)) Finset.univ, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
    exact fun k l hkl => hwmono.injective (Complex.ofReal_inj.mp hkl)
  · rintro z hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
    have hcast : ((w k : ℝ) : ℂ) = algebraMap ℝ ℂ (w k) := rfl
    rw [Polynomial.IsRoot, hcast, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      hwzero k, map_zero]
  · rintro z hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨w k, hwS k, rfl⟩

/-- **`eq:dominance-bound` on one retained block, with the zeros strictly
inside.**  `exists_interiorZeros_of_dominance` with the ambient set removed: the
zeros are reported in `z((a,b))`'s span `(z a, z b)`, which is what separates one
block's zeros from the next block's. -/
theorem exists_interiorZeros_of_dominance_Ioo
    {Φ φ ψ z τ Rm : ℝ → ℝ} {W : ℝ → ℂ} {P : Polynomial ℝ}
    {a b L : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn Φ (Set.Icc a b)) (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hL : Real.pi ≤ L) (hΦ : L ≤ Φ b - Φ a)
    (hΦdef : ∀ θ ∈ Set.Icc a b, Φ θ = φ θ - ψ θ)
    (hzmono : StrictMonoOn z (Set.Icc a b))
    (hτ : ∀ θ ∈ Set.Icc a b, 0 < τ θ)
    (hWne : ∀ θ ∈ Set.Icc a b, W θ ≠ 0)
    (hpolar : ∀ θ ∈ Set.Icc a b,
      W θ = (‖W θ‖ : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I))
    (hdec : ∀ θ ∈ Set.Icc a b, τ θ * P.eval (z θ)
      = 2 * (W θ * Complex.exp (-(φ θ : ℂ) * Complex.I)).re + Rm θ)
    (hdom : ∀ θ ∈ Set.Icc a b, |Rm θ| ≤ ‖W θ‖ / 2) :
    ∃ (n : ℕ) (Z : Finset ℂ), L / Real.pi - 2 ≤ (n : ℝ) ∧ n ≤ Z.card ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' Set.Ioo (z a) (z b)) := by
  have hzmem : ∀ θ ∈ Set.Icc a b, z θ ∈ Set.Icc (z a) (z b) := by
    intro θ hθ
    exact ⟨hzmono.monotoneOn ⟨le_rfl, hab⟩ hθ hθ.1,
      hzmono.monotoneOn hθ ⟨hab, le_rfl⟩ hθ.2⟩
  obtain ⟨n, y, hcount, hymono, hymem, halt⟩ :=
    exists_alternating_phase_points hab hcont hmono hL hΦ hΦdef hzmono hzmem hτ hWne
      hpolar hdec hdom
  obtain ⟨Z, hZcard, hZroot, hZmem⟩ :=
    exists_interiorZeros_of_alternating_Ioo P y hymono hymem halt
  exact ⟨n, Z, hcount, hZcard, hZroot, hZmem⟩


/-! ### The upper half of `eq:angular-discrepancy` -/

/-- **The lower half of `eq:angular-discrepancy`, as a root count.**  A finite set
of distinct roots lying inside `A` is a lower bound for the multiplicity-counted
number of roots in `A`.  This is what turns the *distinct* zeros
`exists_interiorZeros_of_dominance` produces into the count
`count_add_card_le_natDegree` compares against the degree. -/
theorem card_le_count_filter {P : Polynomial ℂ} (hP : P ≠ 0) (A : Set ℂ)
    [DecidablePred (· ∈ A)] {Z : Finset ℂ}
    (hZ : ∀ w ∈ Z, P.IsRoot w) (hmem : ∀ w ∈ Z, w ∈ A) :
    Z.card ≤ Multiset.card (P.roots.filter (· ∈ A)) := by
  classical
  have hle : Z.val ≤ P.roots.filter (· ∈ A) := by
    refine (Finset.val_le_iff_val_subset).mpr ?_
    intro w hw
    rw [Multiset.mem_filter, Polynomial.mem_roots hP]
    exact ⟨hZ w hw, hmem w hw⟩
  simpa using Multiset.card_le_card hle

/-- A finite set of distinct roots of a nonzero polynomial has at most `deg`
elements. -/
theorem card_le_natDegree_of_isRoot {P : Polynomial ℂ} (hP : P ≠ 0) {Z : Finset ℂ}
    (hZ : ∀ w ∈ Z, P.IsRoot w) : Z.card ≤ P.natDegree := by
  classical
  have hsub : Z ⊆ P.roots.toFinset := by
    intro w hw
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hZ w hw
  calc Z.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := P.roots.toFinset_card_le
    _ ≤ P.natDegree := P.card_roots'

/-- **Paper `subsec:proof`, `prop:angular-discrepancy` — the counting step behind
`eq:angular-discrepancy`.**  Zeros counted with multiplicity inside an angular
window, plus distinct zeros supplied outside it, cannot exceed the degree.  This
is what turns `eq:angular-distinct-lower` on the two complementary intervals into
the upper bound on `Z_M(α,β)`. -/
theorem count_add_card_le_natDegree {P : Polynomial ℂ} (hP : P ≠ 0) (A : Set ℂ)
    [DecidablePred (· ∈ A)] {Zout : Finset ℂ}
    (hout : ∀ w ∈ Zout, P.IsRoot w) (hdisj : ∀ w ∈ Zout, w ∉ A) :
    Multiset.card (P.roots.filter (· ∈ A)) + Zout.card ≤ P.natDegree := by
  classical
  have hle : Zout.val ≤ P.roots.filter (fun w => w ∉ A) := by
    refine (Finset.val_le_iff_val_subset).mpr ?_
    intro w hw
    rw [Multiset.mem_filter, Polynomial.mem_roots hP]
    exact ⟨hout w hw, hdisj w hw⟩
  have hcard : Zout.card ≤ Multiset.card (P.roots.filter (fun w => w ∉ A)) :=
    Multiset.card_le_card hle
  have hsplit : Multiset.card (P.roots.filter (· ∈ A))
      + Multiset.card (P.roots.filter (fun w => w ∉ A)) = Multiset.card P.roots := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  calc Multiset.card (P.roots.filter (· ∈ A)) + Zout.card
      ≤ Multiset.card (P.roots.filter (· ∈ A))
        + Multiset.card (P.roots.filter (fun w => w ∉ A)) := by omega
    _ = Multiset.card P.roots := hsplit
    _ ≤ P.natDegree := P.card_roots'


end ForgacsTran
