/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.SpecialFunctions.Trigonometric.TangentSuperadditive
import ForgacsTran.FTBranchAngle

/-!
# The curvature target, for any weights summing to `r`

The curvature hypothesis `PhaseTangency` still carries splits into two halves at the free
critical point of `∑_k w_k² cot θ_k` on `{∑_k w_k = r}`.  **This module proves both, and
assembles them.**  What is left outside it is the reduction of `wedge (γ'') (γ')` to that
sum through the cotangent chart, which is geometry rather than combinatorics.

The first half is about the angles alone.  With `θ_k` the branch angles and
`φ_k = π - θ_k`, the branch equation is `∑_k φ_k = π - rθ`, and the half proved here is

    T · (T · cot θ + r) > 0,       T = ∑_k tan φ_k,

which in the branch angles reads `r/S < cot θ` for `S = ∑_k tan θ_k = -T`.  It carries no
derivatives, no weights and no pencil: only the branch equation and the ranges.

**Everything runs on one identity.**

    tan(a+b) - tan a - tan b = sin a · sin b · sin(a+b) / (cos a · cos b · cos(a+b)),

positive on `(0, π/2)`, so the tangent is superadditive there.  Two consequences carry the
proof: a sum of tangents is at most the tangent of the sum, and `tan(rθ) ≥ r · tan θ`.

**The case split is on the sign of `T`, and it is real.**  `T` is positive when every `φ_k`
is below `π/2` and negative when one exceeds it — and at most one can, since two would sum
past `π > π - rθ`.  In the second case `π - rθ > π/2` forces `θ < π/(2r)`, so `cot θ > 0` and
the comparison is between quantities of known sign; in the first, `cot θ` may be negative, and
that happens only at `r = 1`, where `n ≥ 2` and the superadditive bound closes it.  There is no
uniform division-free form: the two cases give opposite inequalities between `T cot θ` and
`-r`, which is exactly what dividing by `T` does.

## Main statements

* `tan_add_sub`, `tan_add_lt`, `tan_add_le`, `sum_tan_le_tan_sum`, `tan_nat_mul_ge` — the
  identity, superadditivity on `(0, π/2)`, the summed form and `tan(rθ) ≥ r · tan θ`, all
  re-exported from `Shields.Analysis.SpecialFunctions.Trigonometric.TangentSuperadditive`;
  none of them mentions a pencil.
* `tan_sum_viewing` — the half of the curvature split that is about the angles alone.
* `at_most_one_big`, `tan_sum_neg_of_big` — the two positional facts both halves run on.
* `sum_sq_cot_nonpos` — the other half: the deviation from the critical point costs nothing.
* `sum_sq_cot_lt_of_branch` — the two assembled, which is the curvature target
  `∑_k w_k² cot θ_k < r cot θ` for **any** weights summing to `r`.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, `thm:FT-geometry`.
* `Forgacs2017RationalDenominator`, Lemma 2, whose branch equation is the constraint used.
* `../scripts/check_branch_convexity.py`, block X11.

## Tags

tangent, superadditivity, branch angles, angle sum, curvature
-/

namespace ForgacsTran

open Real Set

/-! ### Superadditivity of the tangent

The tangent lemmas below are `_lean_shared/Shields`'s, re-exported so that the assembly
reads unqualified. -/

export Shields (sum_tan_le_tan_sum tan_add_le tan_add_lt tan_add_sub tan_nat_mul_ge
  tan_nat_mul_gt)

/-! ### The half of the curvature split that is about the angles alone -/

private theorem tan_pi_sub' (x : ℝ) : Real.tan (π - x) = -Real.tan x := by
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.sin_pi_sub, Real.cos_pi_sub]
  ring

private theorem tan_mul_cot {x : ℝ} (hs : Real.sin x ≠ 0) (hc : Real.cos x ≠ 0) :
    Real.tan x * (Real.cos x / Real.sin x) = 1 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- **At most one reflected angle is past `π/2`**, since two would sum past `π`, and the
branch equation caps the total at `π - rθ < π`. -/
theorem at_most_one_big {n r : ℕ} {θ : ℝ} (hθ0 : 0 < θ) {φ : Fin n → ℝ}
    (hpos : ∀ k, 0 < φ k) (hsum : ∑ k, φ k = π - (r : ℝ) * θ)
    {i j : Fin n} (hij : i ≠ j) (hi : π / 2 < φ i) : φ j ≤ π / 2 := by
  classical
  have hrθ : 0 ≤ (r : ℝ) * θ := mul_nonneg (Nat.cast_nonneg r) hθ0.le
  by_contra hj
  push Not at hj
  have hpair : φ i + φ j ≤ ∑ k, φ k := by
    have hsplit := Finset.add_sum_erase Finset.univ φ (Finset.mem_univ i)
    have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩
    have hle : φ j ≤ ∑ k ∈ Finset.univ.erase i, φ k :=
      Finset.single_le_sum (f := φ) (fun k _ => (hpos k).le) hmem
    linarith
  rw [hsum] at hpair
  linarith

/-- **`T·(T·cot θ + r) > 0` for `T = ∑_k tan φ_k`.**  In the branch angles `θ_k = π - φ_k`
this is `r/S < cot θ` with `S = ∑_k tan θ_k`, the half of the curvature split that mentions
no derivative, no weight and no pencil.

The hypothesis `φ k ≠ π/2` is where `S` is defined at all: a branch angle at `π/2` sends its
tangent to infinity and the critical point the split is taken at runs off with it.  At most
one `φ k` can be there, since two would sum past `π`. -/
theorem tan_sum_viewing {n r : ℕ} (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) {φ : Fin n → ℝ} (hpos : ∀ k, 0 < φ k)
    (hne : ∀ k, φ k ≠ π / 2) (hsum : ∑ k, φ k = π - r * θ) :
    0 < (∑ k, Real.tan (φ k)) * ((∑ k, Real.tan (φ k)) * (Real.cos θ / Real.sin θ) + r) := by
  classical
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrθ : (r : ℝ) * θ < π := by
    rw [mul_comm]; exact (lt_div_iff₀ hrR).1 hθ.2
  have hθlt : θ < π := by nlinarith [hθ.1]
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθlt
  have hΦpos : 0 < π - (r : ℝ) * θ := by linarith
  set T := ∑ k, Real.tan (φ k) with hTdef
  have hle : ∀ k, φ k ≤ π - (r : ℝ) * θ := by
    intro k
    rw [← hsum]
    exact Finset.single_le_sum (f := φ) (fun i _ => (hpos i).le) (Finset.mem_univ k)
  have hTsplit : ∀ j : Fin n,
      T = Real.tan (φ j) + ∑ k ∈ Finset.univ.erase j, Real.tan (φ k) := by
    intro j
    rw [hTdef, ← Finset.add_sum_erase _ (fun k => Real.tan (φ k)) (Finset.mem_univ j)]
  by_cases hbig : ∃ j, π / 2 < φ j
  · -- one angle past `π/2`: then `rθ < π/2`, `cot θ > 0`, and `-T > r tan θ`
    obtain ⟨j, hj⟩ := hbig
    have hΦbig : π / 2 < π - (r : ℝ) * θ := lt_of_lt_of_le hj (hle j)
    have hrθ2 : (r : ℝ) * θ < π / 2 := by linarith
    have hθ2 : θ < π / 2 := by
      nlinarith [hθ.1, hr1, hrθ2, mul_nonneg (sub_nonneg.2 hr1) hθ.1.le]
    have hcθ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ2⟩
    have htθ : 0 < Real.tan θ := by rw [Real.tan_eq_sin_div_cos]; positivity
    have hcot : 0 < Real.cos θ / Real.sin θ := div_pos hcθ hsθ
    set ρ := ∑ k ∈ Finset.univ.erase j, φ k with hρdef
    have hsplit : φ j + ρ = π - (r : ℝ) * θ := by
      rw [hρdef, Finset.add_sum_erase _ _ (Finset.mem_univ j), hsum]
    have hρnn : 0 ≤ ρ := Finset.sum_nonneg fun i _ => (hpos i).le
    have hrθnn : (0 : ℝ) ≤ (r : ℝ) * θ := mul_nonneg hrR.le hθ.1.le
    have hρlt : ρ < π / 2 := by linarith
    have hrρ : (r : ℝ) * θ + ρ < π / 2 := by linarith
    have htanj : Real.tan (φ j) = -Real.tan ((r : ℝ) * θ + ρ) := by
      rw [show φ j = π - ((r : ℝ) * θ + ρ) by linarith, tan_pi_sub']
    have hothers : ∑ k ∈ Finset.univ.erase j, Real.tan (φ k) ≤ Real.tan ρ := by
      rw [hρdef]
      exact sum_tan_le_tan_sum _ φ (fun i _ => (hpos i).le) (by rw [← hρdef]; exact hρlt)
    have hmain : (r : ℝ) * Real.tan θ < -T := by
      rcases Finset.eq_empty_or_nonempty (Finset.univ.erase j) with hempty | hnonempty
      · have hρ0 : ρ = 0 := by rw [hρdef, hempty, Finset.sum_empty]
        have hn1 : n = 1 := by
          have h1 : (Finset.univ.erase j).card = n - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
              Fintype.card_fin]
          rw [hempty, Finset.card_empty] at h1
          have hn0 : 0 < n := j.pos
          omega
        have hr2 : 2 ≤ r := by omega
        have hgt := tan_nat_mul_gt hr2 hθ.1 (by rw [hρ0] at hrρ; linarith)
        rw [hTsplit j, htanj, hempty, Finset.sum_empty, hρ0, add_zero, add_zero]
        linarith
      · have hρpos : 0 < ρ := by
          rw [hρdef]; exact Finset.sum_pos (fun i _ => hpos i) hnonempty
        have hstep : Real.tan ((r : ℝ) * θ) + Real.tan ρ < Real.tan ((r : ℝ) * θ + ρ) :=
          tan_add_lt (mul_pos hrR hθ.1) hρpos hrρ
        have hlin := tan_nat_mul_ge r hθ.1 (by linarith)
        rw [hTsplit j, htanj]
        linarith
    have hTneg : T < 0 := by nlinarith [mul_pos hrR htθ]
    have hkey : T * (Real.cos θ / Real.sin θ) + r < 0 := by
      have h1 : T < -((r : ℝ) * Real.tan θ) := by linarith
      have h2 := mul_lt_mul_of_pos_right h1 hcot
      rw [show -((r : ℝ) * Real.tan θ) * (Real.cos θ / Real.sin θ)
          = -(r : ℝ) * (Real.tan θ * (Real.cos θ / Real.sin θ)) by ring,
        tan_mul_cot hsθ.ne' hcθ.ne', mul_one] at h2
      linarith
    exact mul_pos_of_neg_of_neg hTneg hkey
  · -- every angle below `π/2`: then `T > 0`
    push Not at hbig
    have hsmall : ∀ k, φ k < π / 2 := fun k => lt_of_le_of_ne (hbig k) (hne k)
    have hn : 0 < n := by
      by_contra hn0
      have hz : n = 0 := by omega
      subst hz
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
      nlinarith [hθ.1]
    have hTpos : 0 < T := by
      rw [hTdef]
      refine Finset.sum_pos (fun k _ => ?_) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      rw [Real.tan_eq_sin_div_cos]
      have h1 : 0 < Real.sin (φ k) :=
        Real.sin_pos_of_pos_of_lt_pi (hpos k) (by linarith [hsmall k])
      have h2 : 0 < Real.cos (φ k) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos k], hsmall k⟩
      positivity
    have hkey : 0 < T * (Real.cos θ / Real.sin θ) + r := by
      rcases le_or_gt θ (π / 2) with hθ2 | hθ2
      · have hcθ : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ2⟩
        have hnn : 0 ≤ T * (Real.cos θ / Real.sin θ) :=
          mul_nonneg hTpos.le (div_nonneg hcθ hsθ.le)
        linarith
      · have hr1' : r = 1 := by
          by_contra hne1
          have hr2 : (2 : ℝ) ≤ r := by
            have : 2 ≤ r := by omega
            exact_mod_cast this
          nlinarith [hrθ, hθ2, hr2, hθ.1, mul_nonneg (by linarith : (0:ℝ) ≤ (r:ℝ) - 2) hθ.1.le]
        subst hr1'
        have hn2 : 2 ≤ n := by
          rcases hnr with h | h
          · exact h
          · omega
        have hΦ : ∑ k, φ k = π - θ := by rw [hsum]; push_cast; ring
        obtain ⟨j⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        set ρ := ∑ k ∈ Finset.univ.erase j, φ k with hρdef
        have hsplit : φ j + ρ = π - θ := by
          rw [hρdef, Finset.add_sum_erase _ _ (Finset.mem_univ j), hΦ]
        have hnonempty : (Finset.univ.erase j).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j),
            Finset.card_univ, Fintype.card_fin]
          omega
        have hρpos : 0 < ρ := by
          rw [hρdef]; exact Finset.sum_pos (fun i _ => hpos i) hnonempty
        have hρlt : ρ < π / 2 := by linarith [hpos j]
        have hothers : ∑ k ∈ Finset.univ.erase j, Real.tan (φ k) ≤ Real.tan ρ := by
          rw [hρdef]
          exact sum_tan_le_tan_sum _ φ (fun i _ => (hpos i).le) (by rw [← hρdef]; exact hρlt)
        have hstep : Real.tan (φ j) + Real.tan ρ < Real.tan (φ j + ρ) :=
          tan_add_lt (hpos j) hρpos (by rw [hsplit]; linarith)
        have hTlt : T < Real.tan (φ j + ρ) := by
          have h := hTsplit j
          linarith
        rw [hsplit, tan_pi_sub'] at hTlt
        have hcθ : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hθ2 (by linarith)
        have hcot : Real.cos θ / Real.sin θ < 0 := div_neg_of_neg_of_pos hcθ hsθ
        have h2 := mul_lt_mul_of_neg_right hTlt hcot
        rw [show -Real.tan θ * (Real.cos θ / Real.sin θ)
            = -(Real.tan θ * (Real.cos θ / Real.sin θ)) by ring,
          tan_mul_cot hsθ.ne' hcθ.ne] at h2
        push_cast
        linarith
    exact mul_pos hTpos hkey

/-- **The hypotheses of `tan_sum_viewing` are satisfiable**, so the conclusion is not
vacuous: `n = 2`, `r = 1`, `θ = π/4`, `φ = (π/3, 5π/12)`, which sums to `3π/4 = π - θ` with
neither angle at `π/2`. -/
theorem tan_sum_viewing_witness :
    ∃ (n r : ℕ) (θ : ℝ) (φ : Fin n → ℝ), 1 ≤ r ∧ (2 ≤ n ∨ 2 ≤ r) ∧ θ ∈ Ioo 0 (π / r)
      ∧ (∀ k, 0 < φ k) ∧ (∀ k, φ k ≠ π / 2) ∧ ∑ k, φ k = π - (r : ℝ) * θ := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  refine ⟨2, 1, π / 4, ![π / 3, 5 * π / 12], le_rfl, Or.inl le_rfl, ⟨by linarith, ?_⟩,
    ?_, ?_, ?_⟩
  · norm_num
    linarith
  · rw [Fin.forall_fin_two]
    constructor <;> simp <;> linarith
  · rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩ <;>
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, ne_eq] <;>
      intro h <;> linarith
  · rw [Fin.sum_univ_two]
    simp
    ring


/-! ### The deviation form

The curvature target splits at the free critical point of `∑_k w_k² cot θ_k` on
`{∑_k w_k = r}` into `(ii)` above and the statement that the deviation from that critical
point costs nothing:

    ∑_k δ_k² cot θ_k ≤ 0,      ∑_k δ_k = 0.

**It follows from the positions alone**, and the weights never enter.  At most one `θ_k`
lies below `π/2`, so at most one cotangent is positive; and when one does, `∑_k tan θ_k ≥ 0`
— which is *exactly* the Cauchy–Schwarz condition
`cot θ_j · ∑_{k≠j} (-tan θ_k) ≤ cot θ_j · tan θ_j = 1`.  So the form is negative semidefinite
on the whole hyperplane, not merely at the deviation the branch produces. -/

/-- **The deviation form is negative semidefinite.**  `hone` is that at most one angle lies
below `π/2` (and the rest strictly above), `hS` that the tangent sum is nonnegative when one
does.  Both come from the branch equation; neither mentions a weight. -/
theorem sum_sq_cot_nonpos {n : ℕ} {ψ : Fin n → ℝ} (hmem : ∀ k, ψ k ∈ Ioo 0 π)
    (hone : ∀ j k : Fin n, j ≠ k → ψ j < π / 2 → π / 2 < ψ k)
    (hS : ∀ j, ψ j < π / 2 → 0 ≤ ∑ k, Real.tan (ψ k))
    {δ : Fin n → ℝ} (hδ : ∑ k, δ k = 0) :
    ∑ k, (δ k) ^ 2 * (Real.cos (ψ k) / Real.sin (ψ k)) ≤ 0 := by
  classical
  have hsin : ∀ k, 0 < Real.sin (ψ k) := fun k =>
    Real.sin_pos_of_pos_of_lt_pi (hmem k).1 (hmem k).2
  by_cases hbig : ∃ j, ψ j < π / 2
  · obtain ⟨j, hj⟩ := hbig
    have hcj : 0 < Real.cos (ψ j) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [(hmem j).1], hj⟩
    have hcotj : 0 < Real.cos (ψ j) / Real.sin (ψ j) := div_pos hcj (hsin j)
    -- every other angle is past `π/2`, so its cotangent is negative
    have hother : ∀ k ∈ Finset.univ.erase j, Real.cos (ψ k) / Real.sin (ψ k) < 0 := by
      intro k hk
      have hkj : j ≠ k := fun h => (Finset.ne_of_mem_erase hk) h.symm
      have := hone j k hkj hj
      exact div_neg_of_neg_of_pos
        (Real.cos_neg_of_pi_div_two_lt_of_lt this (by linarith [(hmem k).2, Real.pi_pos])) (hsin k)
    set u : Fin n → ℝ := fun k => -(Real.cos (ψ k) / Real.sin (ψ k)) with hudef
    have hupos : ∀ k ∈ Finset.univ.erase j, 0 < u k := fun k hk => by
      simp only [hudef]; linarith [hother k hk]
    -- the reciprocal of `u` is minus the tangent
    have hrecip : ∀ k ∈ Finset.univ.erase j, 1 / u k = -Real.tan (ψ k) := by
      intro k hk
      have hkj : j ≠ k := fun h => (Finset.ne_of_mem_erase hk) h.symm
      have hck : Real.cos (ψ k) < 0 :=
        Real.cos_neg_of_pi_div_two_lt_of_lt (hone j k hkj hj)
          (by linarith [(hmem k).2, Real.pi_pos])
      rw [hudef, Real.tan_eq_sin_div_cos]
      field_simp
    -- Cauchy–Schwarz on the complement of `j`
    have hcs : (∑ k ∈ Finset.univ.erase j, δ k) ^ 2
        ≤ (∑ k ∈ Finset.univ.erase j, u k * (δ k) ^ 2)
          * (∑ k ∈ Finset.univ.erase j, 1 / u k) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase j)
        (fun k => Real.sqrt (u k) * δ k) (fun k => 1 / Real.sqrt (u k))
      have e1 : ∀ k ∈ Finset.univ.erase j,
          (Real.sqrt (u k) * δ k) * (1 / Real.sqrt (u k)) = δ k := by
        intro k hk
        have : Real.sqrt (u k) ≠ 0 := (Real.sqrt_pos.2 (hupos k hk)).ne'
        field_simp
      have e2 : ∀ k ∈ Finset.univ.erase j,
          (Real.sqrt (u k) * δ k) ^ 2 = u k * (δ k) ^ 2 := by
        intro k hk
        rw [mul_pow, Real.sq_sqrt (hupos k hk).le]
      have e3 : ∀ k ∈ Finset.univ.erase j, (1 / Real.sqrt (u k)) ^ 2 = 1 / u k := by
        intro k hk
        rw [div_pow, one_pow, Real.sq_sqrt (hupos k hk).le]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
      exact h
    -- the Cauchy–Schwarz condition is exactly `∑_k tan ψ_k ≥ 0`
    have hcond : (Real.cos (ψ j) / Real.sin (ψ j))
        * (∑ k ∈ Finset.univ.erase j, 1 / u k) ≤ 1 := by
      have hsum := hS j hj
      rw [← Finset.add_sum_erase _ (fun k => Real.tan (ψ k)) (Finset.mem_univ j)] at hsum
      have hrw : ∑ k ∈ Finset.univ.erase j, 1 / u k
          = -∑ k ∈ Finset.univ.erase j, Real.tan (ψ k) := by
        rw [Finset.sum_congr rfl hrecip, Finset.sum_neg_distrib]
      rw [hrw]
      have hle : -∑ k ∈ Finset.univ.erase j, Real.tan (ψ k) ≤ Real.tan (ψ j) := by linarith
      calc (Real.cos (ψ j) / Real.sin (ψ j)) * -∑ k ∈ Finset.univ.erase j, Real.tan (ψ k)
          ≤ (Real.cos (ψ j) / Real.sin (ψ j)) * Real.tan (ψ j) :=
            mul_le_mul_of_nonneg_left hle hcotj.le
        _ = 1 := by rw [mul_comm]; exact tan_mul_cot (hsin j).ne' hcj.ne'
    -- assemble
    have hδj : δ j = -∑ k ∈ Finset.univ.erase j, δ k := by
      have := Finset.add_sum_erase _ δ (Finset.mem_univ j)
      rw [hδ] at this
      linarith
    have hQnn : 0 ≤ ∑ k ∈ Finset.univ.erase j, u k * (δ k) ^ 2 :=
      Finset.sum_nonneg fun k hk => mul_nonneg (hupos k hk).le (sq_nonneg _)
    have hRnn : 0 ≤ ∑ k ∈ Finset.univ.erase j, 1 / u k :=
      Finset.sum_nonneg fun k hk => (one_div_pos.2 (hupos k hk)).le
    have hstep : (Real.cos (ψ j) / Real.sin (ψ j)) * (δ j) ^ 2
        ≤ ∑ k ∈ Finset.univ.erase j, u k * (δ k) ^ 2 := by
      rw [hδj, neg_pow, neg_one_pow_two, one_mul]
      calc (Real.cos (ψ j) / Real.sin (ψ j)) * (∑ k ∈ Finset.univ.erase j, δ k) ^ 2
          ≤ (Real.cos (ψ j) / Real.sin (ψ j))
            * ((∑ k ∈ Finset.univ.erase j, u k * (δ k) ^ 2)
              * (∑ k ∈ Finset.univ.erase j, 1 / u k)) :=
            mul_le_mul_of_nonneg_left hcs hcotj.le
        _ = ((Real.cos (ψ j) / Real.sin (ψ j)) * (∑ k ∈ Finset.univ.erase j, 1 / u k))
            * (∑ k ∈ Finset.univ.erase j, u k * (δ k) ^ 2) := by ring
        _ ≤ 1 * (∑ k ∈ Finset.univ.erase j, u k * (δ k) ^ 2) :=
            mul_le_mul_of_nonneg_right hcond hQnn
        _ = ∑ k ∈ Finset.univ.erase j, u k * (δ k) ^ 2 := one_mul _
    rw [← Finset.add_sum_erase _ (fun k => (δ k) ^ 2 * (Real.cos (ψ k) / Real.sin (ψ k)))
      (Finset.mem_univ j)]
    have hneg : ∑ k ∈ Finset.univ.erase j, (δ k) ^ 2 * (Real.cos (ψ k) / Real.sin (ψ k))
        = -∑ k ∈ Finset.univ.erase j, u k * (δ k) ^ 2 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hudef]
      ring
    rw [hneg]
    nlinarith [hstep]
  · push Not at hbig
    refine Finset.sum_nonpos fun k _ => ?_
    have hck : Real.cos (ψ k) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (hbig k) (by linarith [(hmem k).2, Real.pi_pos])
    have : Real.cos (ψ k) / Real.sin (ψ k) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hck (hsin k).le
    nlinarith [sq_nonneg (δ k)]

/-- **One reflected angle past `π/2` makes the tangent sum negative.**  The angle's own
tangent is `-tan(rθ + ρ)` and the rest sum to at most `tan ρ`, and `tan(rθ + ρ) > tan ρ`. -/
theorem tan_sum_neg_of_big {n r : ℕ} (hr : 1 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    {φ : Fin n → ℝ} (hpos : ∀ k, 0 < φ k) (hsum : ∑ k, φ k = π - (r : ℝ) * θ)
    {j : Fin n} (hj : π / 2 < φ j) : ∑ k, Real.tan (φ k) < 0 := by
  classical
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrθ : (r : ℝ) * θ < π := by
    rw [mul_comm]; exact (lt_div_iff₀ hrR).1 hθ.2
  have hrθpos : 0 < (r : ℝ) * θ := mul_pos hrR hθ.1
  have hle : φ j ≤ π - (r : ℝ) * θ := by
    rw [← hsum]
    exact Finset.single_le_sum (f := φ) (fun i _ => (hpos i).le) (Finset.mem_univ j)
  have hrθ2 : (r : ℝ) * θ < π / 2 := by linarith
  set ρ := ∑ k ∈ Finset.univ.erase j, φ k with hρdef
  have hsplit : φ j + ρ = π - (r : ℝ) * θ := by
    rw [hρdef, Finset.add_sum_erase _ _ (Finset.mem_univ j), hsum]
  have hρnn : 0 ≤ ρ := Finset.sum_nonneg fun i _ => (hpos i).le
  have hρlt : ρ < π / 2 := by linarith
  have hrρ : (r : ℝ) * θ + ρ < π / 2 := by linarith
  have htanj : Real.tan (φ j) = -Real.tan ((r : ℝ) * θ + ρ) := by
    rw [show φ j = π - ((r : ℝ) * θ + ρ) by linarith, tan_pi_sub']
  have hothers : ∑ k ∈ Finset.univ.erase j, Real.tan (φ k) ≤ Real.tan ρ := by
    rw [hρdef]
    exact sum_tan_le_tan_sum _ φ (fun i _ => (hpos i).le) (by rw [← hρdef]; exact hρlt)
  have hstep : Real.tan ((r : ℝ) * θ) + Real.tan ρ ≤ Real.tan ((r : ℝ) * θ + ρ) :=
    tan_add_le hrθpos.le hρnn hrρ
  have hrpos : 0 < Real.tan ((r : ℝ) * θ) := by
    rw [Real.tan_eq_sin_div_cos]
    have h1 : 0 < Real.sin ((r : ℝ) * θ) :=
      Real.sin_pos_of_pos_of_lt_pi hrθpos (by linarith)
    have h2 : 0 < Real.cos ((r : ℝ) * θ) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hrθ2⟩
    positivity
  rw [← Finset.add_sum_erase _ (fun k => Real.tan (φ k)) (Finset.mem_univ j), htanj]
  linarith

/-! ### The curvature target's combinatorial core

Both halves assemble.  With `ψ_k = π - φ_k` the branch angles, `S = ∑_k tan ψ_k` and any
weights summing to `r`, the free critical point of `∑_k w_k² cot ψ_k` sits at
`w_k = (r/S) tan ψ_k` with value `r²/S`, the cross term cancels identically, and

    ∑_k w_k² cot ψ_k  =  r²/S + ∑_k δ_k² cot ψ_k  ≤  r²/S  <  r cot θ

by `sum_sq_cot_nonpos` and `tan_sum_viewing`.  Nothing about the pencil enters beyond the
branch equation. -/

/-- **The curvature target, for any weights summing to `r`.**  This is what the curvature
inequality reduces to once the geometry is stripped: `∑_k w_k² cot θ_k < r cot θ`, needing
only `∑_k w_k = r` and the branch equation on the angles. -/
theorem sum_sq_cot_lt_of_branch {n r : ℕ} (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) {φ : Fin n → ℝ} (hpos : ∀ k, 0 < φ k)
    (hne : ∀ k, φ k ≠ π / 2) (hsum : ∑ k, φ k = π - (r : ℝ) * θ)
    {w : Fin n → ℝ} (hw : ∑ k, w k = (r : ℝ)) :
    ∑ k, (w k) ^ 2 * (Real.cos (π - φ k) / Real.sin (π - φ k))
      < (r : ℝ) * (Real.cos θ / Real.sin θ) := by
  classical
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrθ : (r : ℝ) * θ < π := by
    rw [mul_comm]; exact (lt_div_iff₀ hrR).1 hθ.2
  have hrθpos : 0 < (r : ℝ) * θ := mul_pos hrR hθ.1
  have hsθ : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by nlinarith [hθ.1, (by exact_mod_cast hr : (1:ℝ) ≤ r)])
  -- the reflected angles
  set ψ : Fin n → ℝ := fun k => π - φ k with hψdef
  have hφlt : ∀ k, φ k < π := by
    intro k
    have : φ k ≤ π - (r : ℝ) * θ := by
      rw [← hsum]
      exact Finset.single_le_sum (f := φ) (fun i _ => (hpos i).le) (Finset.mem_univ k)
    linarith
  have hmem : ∀ k, ψ k ∈ Ioo 0 π := fun k => ⟨by simp only [hψdef]; linarith [hφlt k],
    by simp only [hψdef]; linarith [hpos k]⟩
  have hsinψ : ∀ k, 0 < Real.sin (ψ k) := fun k =>
    Real.sin_pos_of_pos_of_lt_pi (hmem k).1 (hmem k).2
  have hcosψ : ∀ k, Real.cos (ψ k) ≠ 0 := by
    intro k
    have hck : Real.cos (φ k) ≠ 0 := by
      rcases lt_trichotomy (φ k) (π / 2) with h | h | h
      · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos k], h⟩).ne'
      · exact absurd h (hne k)
      · exact (Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [hφlt k])).ne
    simp only [hψdef, Real.cos_pi_sub]
    simpa using hck
  have hψpt : ∀ k, ψ k = π - φ k := fun _ => rfl
  set c : Fin n → ℝ := fun k => Real.cos (ψ k) / Real.sin (ψ k) with hcdef
  have hcpt : ∀ k, c k = Real.cos (ψ k) / Real.sin (ψ k) := fun _ => rfl
  set t : Fin n → ℝ := fun k => Real.tan (ψ k) with htdef
  have htc : ∀ k, t k * c k = 1 := fun k => by
    simp only [htdef, hcdef]; exact tan_mul_cot (hsinψ k).ne' (hcosψ k)
  have hrefl : ∀ k, t k = -Real.tan (φ k) := by
    intro k; simp only [htdef, hψdef]; exact tan_pi_sub' _
  set S := ∑ k, t k with hSdef
  set T := ∑ k, Real.tan (φ k) with hTdef
  have hST : S = -T := by
    rw [hSdef, hTdef, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hrefl k
  -- (ii)
  have hii := tan_sum_viewing hr hnr hθ hpos hne hsum
  rw [← hTdef] at hii
  have hTne : T ≠ 0 := by
    intro h; rw [h] at hii; simp at hii
  have hSne : S ≠ 0 := by rw [hST]; simpa using hTne
  have hSii : 0 < S * (S * (Real.cos θ / Real.sin θ) - r) := by
    rw [hST]; nlinarith [hii]
  have hcrit : (r : ℝ) ^ 2 / S < (r : ℝ) * (Real.cos θ / Real.sin θ) := by
    rcases lt_or_gt_of_ne hSne with hneg | hpos'
    · rw [div_lt_iff_of_neg hneg]; nlinarith [hSii]
    · rw [div_lt_iff₀ hpos']; nlinarith [hSii]
  -- the deviation and the identity
  set δ : Fin n → ℝ := fun k => w k - ((r : ℝ) / S) * t k with hδdef
  have hδpt : ∀ k, δ k = w k - ((r : ℝ) / S) * t k := fun _ => rfl
  have hδsum : ∑ k, δ k = 0 := by
    have h1 : ∑ k, δ k = (∑ k, w k) - ((r : ℝ) / S) * (∑ k, t k) := by
      simp only [hδpt, Finset.sum_sub_distrib, Finset.mul_sum]
    have h2 : (∑ k, t k) = S := hSdef.symm
    rw [h1, hw, h2]
    field
  have hid : ∑ k, (w k) ^ 2 * c k = (r : ℝ) ^ 2 / S + ∑ k, (δ k) ^ 2 * c k := by
    have hpt : ∀ k, (w k) ^ 2 * c k
        = (δ k) ^ 2 * c k + (2 * ((r : ℝ) / S)) * δ k + (((r : ℝ) / S) ^ 2) * t k := by
      intro k
      have h1 : w k = δ k + ((r : ℝ) / S) * t k := by rw [hδpt]; ring
      have h2 := htc k
      rw [h1, show (δ k + ((r : ℝ) / S) * t k) ^ 2 * c k
          = (δ k) ^ 2 * c k + (2 * ((r : ℝ) / S)) * (δ k * (t k * c k))
            + (((r : ℝ) / S) ^ 2) * (t k * (t k * c k)) by ring, h2]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hδsum, ← hSdef]
    field
  -- (i)
  have hone : ∀ i j : Fin n, i ≠ j → ψ i < π / 2 → π / 2 < ψ j := by
    intro i j hij hi
    have hbi : π / 2 < φ i := by rw [hψpt] at hi; linarith
    have hb := at_most_one_big hθ.1 hpos hsum hij hbi
    have hlt : φ j < π / 2 := lt_of_le_of_ne hb (hne j)
    rw [hψpt]; linarith
  have hSnn : ∀ j, ψ j < π / 2 → 0 ≤ S := by
    intro j hj
    have hbj : π / 2 < φ j := by rw [hψpt] at hj; linarith
    have hneg : T < 0 := by rw [hTdef]; exact tan_sum_neg_of_big hr hθ hpos hsum hbj
    rw [hST]
    linarith
  have hi := sum_sq_cot_nonpos hmem hone hSnn hδsum
  simp only [← hcpt] at hi
  simp only [← hψpt, ← hcpt]
  linarith [hid, hi, hcrit]

/-- **The right-angle case, where `S` is undefined and the split does not apply.**  If some
`φ_j = π/2` then no other can exceed `π/2` — two would sum past `π > π - rθ` — so every
`cot θ_k ≤ 0`; and `π/2 ≤ π - rθ` forces `θ < π/2`, so `cot θ > 0`.  The inequality holds
termwise, with nothing to divide by.

This is the case `sum_sq_cot_lt_of_branch` excludes by hypothesis: a branch angle at `π/2`
sends `∑_k tan θ_k` to infinity and the critical point with it.  Together the two cover every
admissible configuration, which is what `sum_sq_cot_lt_of_branch_of_pos` records. -/
theorem sum_sq_cot_lt_of_right_angle {n r : ℕ} (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) {φ : Fin n → ℝ} (hpos : ∀ k, 0 < φ k)
    (hsum : ∑ k, φ k = π - (r : ℝ) * θ) {j : Fin n} (hj : φ j = π / 2) (w : Fin n → ℝ) :
    ∑ k, (w k) ^ 2 * (Real.cos (π - φ k) / Real.sin (π - φ k))
      < (r : ℝ) * (Real.cos θ / Real.sin θ) := by
  classical
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrθ : (r : ℝ) * θ < π := by
    rw [mul_comm]; exact (lt_div_iff₀ hrR).1 hθ.2
  have hrθpos : 0 < (r : ℝ) * θ := mul_pos hrR hθ.1
  have hall : ∀ k, φ k ≤ π / 2 := by
    intro k
    by_cases hkj : k = j
    · exact le_of_eq (hkj ▸ hj)
    · by_contra hgt
      push Not at hgt
      have hle : φ j + φ k ≤ ∑ i, φ i := by
        have hmem : k ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hkj, Finset.mem_univ k⟩
        have h1 := Finset.add_sum_erase Finset.univ φ (Finset.mem_univ j)
        have h2 := Finset.single_le_sum (f := φ) (fun i _ => (hpos i).le) hmem
        linarith
      rw [hsum, hj] at hle
      linarith [hrθpos]
  have hjle : π / 2 ≤ π - (r : ℝ) * θ := by
    rw [← hsum, ← hj]
    exact Finset.single_le_sum (f := φ) (fun i _ => (hpos i).le) (Finset.mem_univ j)
  have hθ2 : θ < π / 2 := by
    rcases lt_or_eq_of_le hjle with hlt | heq
    · nlinarith [hθ.1, hr1, mul_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) - 1) hθ.1.le]
    · have hzero : ∑ i ∈ Finset.univ.erase j, φ i = 0 := by
        have h1 := Finset.add_sum_erase Finset.univ φ (Finset.mem_univ j)
        rw [hsum, hj] at h1
        linarith
      have hempty : Finset.univ.erase j = ∅ := by
        by_contra hne'
        obtain ⟨k, hk⟩ := Finset.nonempty_of_ne_empty hne'
        have h2 := Finset.single_le_sum (f := φ) (fun i _ => (hpos i).le) hk
        rw [hzero] at h2
        linarith [hpos k]
      have hn1 : n = 1 := by
        have h1 : (Finset.univ.erase j).card = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
            Fintype.card_fin]
        rw [hempty, Finset.card_empty] at h1
        have hn0 : 0 < n := j.pos
        omega
      have hr2 : 2 ≤ r := by
        rcases hnr with h | h
        · omega
        · exact h
      have hr2R : (2 : ℝ) ≤ r := by exact_mod_cast hr2
      have hrθ2 : (r : ℝ) * θ = π / 2 := by linarith
      nlinarith [hθ.1, hr2R, hrθ2]
  have hcθ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ2⟩
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith)
  have hnonpos : ∑ k, (w k) ^ 2 * (Real.cos (π - φ k) / Real.sin (π - φ k)) ≤ 0 := by
    refine Finset.sum_nonpos fun k _ => ?_
    have hφπ : φ k < π := lt_of_le_of_lt (hall k) (by linarith)
    have hs : 0 < Real.sin (π - φ k) := by
      rw [Real.sin_pi_sub]
      exact Real.sin_pos_of_pos_of_lt_pi (hpos k) hφπ
    have hc : Real.cos (π - φ k) ≤ 0 := by
      rw [Real.cos_pi_sub, neg_nonpos]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hpos k], hall k⟩
    have hq : Real.cos (π - φ k) / Real.sin (π - φ k) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hc hs.le
    nlinarith [sq_nonneg (w k)]
  have hpos' : 0 < (r : ℝ) * (Real.cos θ / Real.sin θ) := by positivity
  linarith

/-- **The curvature target with no right-angle hypothesis.**  The two cases together cover
every admissible configuration of branch angles. -/
theorem sum_sq_cot_lt_of_branch_of_pos {n r : ℕ} (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) {φ : Fin n → ℝ} (hpos : ∀ k, 0 < φ k)
    (hsum : ∑ k, φ k = π - (r : ℝ) * θ) {w : Fin n → ℝ} (hw : ∑ k, w k = (r : ℝ)) :
    ∑ k, (w k) ^ 2 * (Real.cos (π - φ k) / Real.sin (π - φ k))
      < (r : ℝ) * (Real.cos θ / Real.sin θ) := by
  classical
  by_cases hne : ∃ j, φ j = π / 2
  · obtain ⟨j, hj⟩ := hne
    exact sum_sq_cot_lt_of_right_angle hr hnr hθ hpos hsum hj w
  · push Not at hne
    exact sum_sq_cot_lt_of_branch hr hnr hθ hpos hne hsum hw

end ForgacsTran
