/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchRegularity
import ForgacsTran.PencilIndex

/-!
# The closing step of Forgács–Tran Proposition 1

`Forgacs2017RationalDenominator` Proposition 1 ends by taking the argument `θ*`
of a hypothetical zero inside the disk, reading a branch index `l` off their
Eqs. (6)--(8), and squeezing `τ(θ*; l) ≤ τ ≤ τ(θ; l)` against the monotonicity of
`z(·; l)` to force `θ* = θ`.  This module is that squeeze.

## Main statements

* `ftChordProd` — `∏_k |τ e^{iψ} - τ_k|`, the chord product at *fixed* radius, and
  `ftChordProd_strictMonoOn`: it increases strictly in the angle.  This is the
  content of their displayed `z(θ̃; l) ≥ z(θ)` step.
* `ftBranchZ` — the real branch value `z(θ; l)` of their Eq. (21), tied to the
  pencil by `ftBranch_ftArcPoint_eq_ftBranchZ`.
* `ftProp1_closing` — the closing step.

## Implementation notes

**Differs from the paper's route.**  Their "We conclude that in fact `θ̃ = θ* = θ`"
compresses a two-case argument, and the non-strict equivalences it displays do
not by themselves close it: from `θ̃ ≥ θ ↔ θ̃ ≥ θ*` and `θ̃` between `θ` and `θ*`
one gets only `θ̃ = θ*` (or `θ̃ = θ`), not `θ* = θ`.  What closes it is the
*strict* form of the same two equivalences, which then contradicts `θ̃` lying in
the closed interval.  Both cases are carried here explicitly.

The two inputs the argument takes from outside this module are supplied as
hypotheses: the containment `τ(θ*; l) ≤ τ ≤ τ(θ; l)`, which comes from
`t* ∈ C₁ ∩ C₂` and their Remark 4, and the strict monotonicity of `z(·; l)`,
which is their Lemma 4(ii) — not formalized in this lane.

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

Forgacs-Tran, minimum modulus, real-rootedness
-/

namespace ForgacsTran

open Real Set Filter Topology

/-- `∏_k |τ e^{iψ} - τ_k|`, the chord product at a *fixed* radius `τ`. -/
noncomputable def ftChordProd {n : ℕ} (a : Fin n → ℝ) (τ ψ : ℝ) : ℝ :=
  ∏ k, Real.sqrt (a k ^ 2 - 2 * a k * τ * Real.cos ψ + τ ^ 2)

theorem normSq_exp_neg_ofReal_mul_I (φ : ℝ) :
    Complex.normSq (Complex.exp (-(φ : ℂ) * Complex.I)) = 1 := by
  simp only [exp_neg_ofReal_mul_I, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring_nf
  linear_combination Real.sin_sq_add_cos_sq φ

theorem normSq_sub_ftArcPoint (a τ ψ : ℝ) :
    Complex.normSq ((a : ℂ) - ftArcPoint τ ψ) = a ^ 2 - 2 * a * τ * Real.cos ψ + τ ^ 2 := by
  simp only [ftArcPoint, exp_neg_ofReal_mul_I, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring_nf
  linear_combination (τ ^ 2) * Real.sin_sq_add_cos_sq ψ

/-- **The chord's radicand, split at the zero.**  `a² - 2aτcos θ + τ² =
(a - τ)² + 2aτ(1 - cos θ)`: the radial displacement squared plus the angular one.
The split is what makes a chord to the point the branch converges to first order
in `θ` — the first term is `(τ - a)²` and the second is `O(θ²)`. -/
theorem chordSq_eq_sub_sq_add (a τ θ : ℝ) :
    a ^ 2 - 2 * a * τ * Real.cos θ + τ ^ 2
      = (a - τ) ^ 2 + 2 * a * τ * (1 - Real.cos θ) := by ring

/-- The chord's radicand is a modulus squared, hence nonnegative for every `a`,
`τ` and `ψ` — no sign hypothesis on any of the three. -/
theorem chordSq_nonneg (a τ ψ : ℝ) : 0 ≤ a ^ 2 - 2 * a * τ * Real.cos ψ + τ ^ 2 := by
  rw [← normSq_sub_ftArcPoint]
  exact Complex.normSq_nonneg _

/-- The chord of `Forgacs2017RationalDenominator` (13) is the ordinary distance. -/
theorem ftChord_eq_sqrt {a τ ψ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hψ : ψ ∈ Ioo 0 π) :
    ftChord a ψ (ftAngle a τ ψ) = Real.sqrt (a ^ 2 - 2 * a * τ * Real.cos ψ + τ ^ 2) := by
  have hsq : (ftChord a ψ (ftAngle a τ ψ)) ^ 2 = a ^ 2 - 2 * a * τ * Real.cos ψ + τ ^ 2 := by
    have h13 := sub_ftArcPoint_eq (a := a) (τ := τ) (θ := ψ) (φ := ftAngle a τ ψ) hψ
      (ftAngle_mem_Ioo ha hτ hψ) (ftAngle_spec (ne_of_gt hτ) hψ)
    have := congrArg Complex.normSq h13
    rw [normSq_sub_ftArcPoint] at this
    rw [this, Complex.normSq_mul, Complex.normSq_neg, normSq_exp_neg_ofReal_mul_I,
      Complex.normSq_ofReal]
    ring
  rw [← hsq, Real.sqrt_sq (ftChord_pos ha hψ (ftAngle_mem_Ioo ha hτ hψ)).le]

theorem prod_ftChord_eq_ftChordProd {n : ℕ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) {τ ψ : ℝ}
    (hτ : 0 < τ) (hψ : ψ ∈ Ioo 0 π) :
    (∏ k, ftChord (a k) ψ (ftAngle (a k) τ ψ)) = ftChordProd a τ ψ :=
  Finset.prod_congr rfl fun k _ => ftChord_eq_sqrt (ha k) hτ hψ

private theorem ftCos_lt_one {ψ : ℝ} (hψ : ψ ∈ Ioo 0 π) : Real.cos ψ < 1 := by
  rcases (Real.cos_le_one ψ).lt_or_eq with h | h
  · exact h
  · exact absurd (Real.sin_eq_zero_iff_cos_eq.2 (Or.inl h))
      (ne_of_gt (sin_pos_of_pos_of_lt_pi hψ.1 hψ.2))

private theorem ftQuad_pos {a τ ψ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hψ : ψ ∈ Ioo 0 π) :
    0 < a ^ 2 - 2 * a * τ * Real.cos ψ + τ ^ 2 :=
  by nlinarith [sq_nonneg (a - τ), mul_pos (mul_pos ha hτ) (sub_pos.2 (ftCos_lt_one hψ))]

theorem ftChordProd_pos {n : ℕ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) {τ ψ : ℝ} (hτ : 0 < τ)
    (hψ : ψ ∈ Ioo 0 π) : 0 < ftChordProd a τ ψ :=
  Finset.prod_pos fun k _ => Real.sqrt_pos.2 (ftQuad_pos (ha k) hτ hψ)

/-- **The step their display asserts.**  At a fixed radius the chord product is
strictly increasing in the angle, so `z(θ̃; l) ≥ z(θ)` really is equivalent to
`θ̃ ≥ θ`. -/
theorem ftChordProd_strictMonoOn {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} (ha : ∀ k, 0 < a k)
    {τ : ℝ} (hτ : 0 < τ) : StrictMonoOn (ftChordProd a τ) (Ioo 0 π) := by
  intro x hx y hy hxy
  have hcos : Real.cos y < Real.cos x :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hx.1.le hy.2.le hxy
  refine Finset.prod_lt_prod_of_nonempty (fun k _ => Real.sqrt_pos.2 (ftQuad_pos (ha k) hτ hx))
    (fun k _ => ?_) (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  refine Real.sqrt_lt_sqrt (ftQuad_pos (ha k) hτ hx).le ?_
  nlinarith [mul_pos (mul_pos (ha k) hτ) (sub_pos.2 hcos)]

/-- `z(θ; l)` of `Forgacs2017RationalDenominator` Eq. (21), as a real number. -/
noncomputable def ftBranchZ {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) (θ : ℝ) : ℝ :=
  (-1) ^ (n + l + 1) * c * (∏ k, ftChord (a k) θ (ftBranchAngle a r l k θ))
    / ftTau a r l θ ^ r

/-- `ftBranchZ` is the branch value of the pencil. -/
theorem ftBranch_ftArcPoint_eq_ftBranchZ {n r l : ℕ} {a : Fin n → ℝ} (c : ℝ) (ha : ∀ k, 0 < a k)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (h : FTBranchAt a r l θ) :
    -((c : ℂ) * ∏ k, ((a k : ℂ) - ftArcPoint (ftTau a r l θ) θ))
        / (ftArcPoint (ftTau a r l θ) θ) ^ r
      = ((ftBranchZ a c r l θ : ℝ) : ℂ) := by
  obtain ⟨hmem, hsum, hratio⟩ := ftBranchAngle_spec ha hθ h
  exact ftBranch_ftArcPoint_eq (a := a) (φ := fun k => ftBranchAngle a r l k θ) (c := c)
    (r := r) (l := l) (ftTau_pos h) hθ hmem hratio hsum

/-- With `n - l - 1` even the branch value is the chord product at its own
radius, which is what makes the two sides of their display comparable. -/
theorem ftBranchZ_eq_chordProd {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (ha : ∀ k, 0 < a k)
    (hpar : Even (n + l + 1)) {θ τ : ℝ} (hθ : θ ∈ Ioo 0 π) (h : FTBranchAt a r l θ)
    (hτ : ftTau a r l θ = τ) :
    ftBranchZ a c r l θ = c * ftChordProd a τ θ / τ ^ r := by
  have hτ0 : 0 < τ := hτ ▸ ftTau_pos h
  rw [ftBranchZ, hpar.neg_one_pow, one_mul]
  rw [show (∏ k, ftChord (a k) θ (ftBranchAngle a r l k θ))
      = ∏ k, ftChord (a k) θ (ftAngle (a k) τ θ) from
    Finset.prod_congr rfl fun k _ => by rw [ftBranchAngle, hτ]]
  rw [prod_ftChord_eq_ftChordProd ha hτ0 hθ, hτ]

/-- **The closing step of `Forgacs2017RationalDenominator` Proposition 1.**
Given the containment `τ(θ*; l) ≤ τ ≤ τ(θ; l)` and the monotonicity of
`z(·; l)`, the hypothetical zero's argument must be `θ`. -/
theorem ftProp1_closing {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (hpar : Even (n + l + 1))
    {θ θ' : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) (hθ' : θ' ∈ Ioo 0 (π / r))
    (hbl : ∀ ψ ∈ Ioo 0 (π / r), FTBranchAt a r l ψ)
    (hzmono : StrictMonoOn (ftBranchZ a c r l) (Ioo 0 (π / r)))
    (hlo : ftTau a r l θ' ≤ ftTau a r (n - 1) θ)
    (hhi : ftTau a r (n - 1) θ ≤ ftTau a r l θ)
    (hzeq : ftBranchZ a c r l θ' = ftBranchZ a c r (n - 1) θ) :
    θ' = θ := by
  set τ : ℝ := ftTau a r (n - 1) θ with hτdef
  have hbp : FTBranchAt a r (n - 1) θ := ftBranchAt_of_arc_principal hn ha hr hnr hθ
  have hτ0 : 0 < τ := ftTau_pos hbp
  have hτr : (0 : ℝ) < τ ^ r := by positivity
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  -- the arc is order-connected, so the whole segment between the two angles is inside it
  have huIcc : uIcc θ' θ ⊆ Ioo 0 (π / r) :=
    (Set.ordConnected_Ioo).uIcc_subset hθ' hθ
  -- the intermediate angle of their "By continuity" step
  have hcont : ContinuousOn (ftTau a r l) (uIcc θ' θ) := fun x hx =>
    (continuousAt_ftTau hn ha hr (huIcc hx) hbl).continuousWithinAt
  obtain ⟨w, hw, hwτ⟩ := intermediate_value_uIcc hcont
    (by rw [Set.mem_uIcc]; exact Or.inl ⟨hlo, hhi⟩)
  have hwarc : w ∈ Ioo 0 (π / r) := huIcc hw
  have hwπ : w ∈ Ioo 0 π := ftArc_subset hr hwarc
  -- both sides of their display are the chord product at the *same* radius `τ`
  have hparp : Even (n + (n - 1) + 1) := even_add_pred_add_one (by omega)
  have hZw : ftBranchZ a c r l w = c * ftChordProd a τ w / τ ^ r :=
    ftBranchZ_eq_chordProd ha hpar hwπ (hbl w hwarc) hwτ
  have hZθ : ftBranchZ a c r (n - 1) θ = c * ftChordProd a τ θ / τ ^ r :=
    ftBranchZ_eq_chordProd ha hparp hθπ hbp rfl
  have hFmono : StrictMonoOn (fun ψ => c * ftChordProd a τ ψ / τ ^ r) (Ioo 0 π) := by
    intro x hx y hy hxy
    have hlt := (ftChordProd_strictMonoOn hn ha hτ0) hx hy hxy
    change c * ftChordProd a τ x / τ ^ r < c * ftChordProd a τ y / τ ^ r
    rw [div_lt_div_iff_of_pos_right hτr]
    exact mul_lt_mul_of_pos_left hlt hc
  -- the two equivalences, in both the strict directions
  have hE1 : ∀ x ∈ Ioo (0 : ℝ) π, ∀ y ∈ Ioo (0 : ℝ) π,
      (c * ftChordProd a τ x / τ ^ r < c * ftChordProd a τ y / τ ^ r ↔ x < y) :=
    fun x hx y hy => hFmono.lt_iff_lt hx hy
  have hE2 : ∀ x ∈ Ioo (0 : ℝ) (π / r), ∀ y ∈ Ioo (0 : ℝ) (π / r),
      (ftBranchZ a c r l x < ftBranchZ a c r l y ↔ x < y) :=
    fun x hx y hy => hzmono.lt_iff_lt hx hy
  have hZθ' : ftBranchZ a c r l θ' = c * ftChordProd a τ θ / τ ^ r := by rw [hzeq, hZθ]
  -- `w < θ ↔ w < θ'` and `θ < w ↔ θ' < w`
  have hlow : w < θ ↔ w < θ' := by
    rw [← hE1 w hwπ θ hθπ, ← hZw, ← hZθ', hE2 w hwarc θ' hθ']
  have hhiw : θ < w ↔ θ' < w := by
    rw [← hE1 θ hθπ w hwπ, ← hZw, ← hZθ', hE2 θ' hθ' w hwarc]
  rcases lt_trichotomy θ' θ with hlt | heq | hgt
  · -- `θ' < θ`: `w ∈ [θ', θ]`, and both equivalences cannot hold
    rw [uIcc_of_le hlt.le] at hw
    have hwθ : w = θ := by
      by_contra hne
      exact absurd (hlow.1 (lt_of_le_of_ne hw.2 hne)) (not_lt.2 hw.1)
    exact absurd (hhiw.2 (by rw [hwθ]; exact hlt)) (by rw [hwθ]; exact lt_irrefl θ)
  · exact heq
  · -- `θ < θ'`: symmetric
    rw [uIcc_comm, uIcc_of_le hgt.le] at hw
    have hwθ : w = θ := by
      by_contra hne
      exact absurd (hhiw.1 (lt_of_le_of_ne hw.1 (Ne.symm hne))) (not_lt.2 hw.2)
    exact absurd (hlow.2 (by rw [hwθ]; exact hgt)) (by rw [hwθ]; exact lt_irrefl θ)

/-! ### Supplying the hypotheses -/

/-- The range condition on the whole arc, for a general index `l`.  This is the
general form of `ftAngleSum_range_of_eq_sub_one`, which is its `l = n - 1` case:
the branch at index `l` exists across `(0, π/r)` exactly when `n ≤ (l+1)r`, with
`l = 0` additionally needing `n < r`. -/
theorem ftRange_of_le {n r l : ℕ} (hr : 1 ≤ r) (hle : n ≤ (l + 1) * r) (hpos : 1 ≤ l ∨ n < r)
    {ψ : ℝ} (hψ0 : 0 < ψ) (hψr : ψ < π / r) : (n : ℝ) * ψ < r * ψ + l * π := by
  have hπ := pi_pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hψπ : (r : ℝ) * ψ < π := by rw [lt_div_iff₀ hr0] at hψr; linarith
  rcases lt_or_ge n r with hnr | hnr
  · have h1 : (n : ℝ) < r := by exact_mod_cast hnr
    have h2 : (0 : ℝ) ≤ l * π := by positivity
    have h3 : (n : ℝ) * ψ < (r : ℝ) * ψ := mul_lt_mul_of_pos_right h1 hψ0
    linarith
  · have hl1 : 1 ≤ l := hpos.resolve_right (by omega)
    have hl1' : (1 : ℝ) ≤ l := by exact_mod_cast hl1
    have hnl : (n : ℝ) - r ≤ (l : ℝ) * r := by
      have h : (n : ℝ) ≤ ((l : ℝ) + 1) * r := by exact_mod_cast hle
      nlinarith [h]
    have h1 : ((n : ℝ) - r) * ψ ≤ ((l : ℝ) * r) * ψ := mul_le_mul_of_nonneg_right hnl hψ0.le
    have h2 : ((l : ℝ) * r) * ψ < (l : ℝ) * π := by
      rw [mul_assoc]
      exact mul_lt_mul_of_pos_left hψπ (by linarith)
    nlinarith [h1, h2]

/-- Solvability across the arc at a general index, from the range condition. -/
theorem ftBranchAt_of_arc_range {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hl : l < n) (hle : n ≤ (l + 1) * r) (hpos : 1 ≤ l ∨ n < r) :
    ∀ ψ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r l ψ :=
  fun _ψ hψ => ftBranchAt_of_arc hn ha hr hl hψ (ftRange_of_le hr hle hpos hψ.1 hψ.2)

/-- **The displayed step of their proof is not sufficient as written.**  Their
closing paragraph derives `θ̃ ≥ θ ↔ z(θ̃;l) ≥ z(θ)` and `θ̃ ≥ θ* ↔ z(θ̃;l) ≥ z(θ)`,
hence `θ̃ ≥ θ ↔ θ̃ ≥ θ*`, and concludes `θ̃ = θ* = θ`.  That inference does not
hold: the equivalence together with `θ̃` lying between `θ` and `θ*` is satisfiable
with `θ* ≠ θ`.  `ftProp1_closing` uses the *strict* form of the same two
equivalences instead, which is available because both monotonicities are
strict. -/
theorem ftProp1_nonstrict_insufficient :
    ∃ θ θ' w : ℝ, w ∈ uIcc θ' θ ∧ ((θ ≤ w) ↔ (θ' ≤ w)) ∧ θ' ≠ θ :=
  ⟨0, 1, 1, by norm_num, by norm_num, by norm_num⟩

end ForgacsTran
