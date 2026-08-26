/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ZeroCount

/-!
# Interior zeros from sign alternation

The paper's `subsec:proof` count is an intermediate-value argument, not a contour count.  At
a phase point `ϑ_k` the principal term of `eq:principal-decomposition` is
`2(-1)^k |W(ϑ_k)|`, and `eq:dominance-bound` forces `F_M(z(ϑ_k))` to carry that
sign; consecutive phase points therefore enclose a zero, and the strict
monotonicity of `z` keeps the enclosed zeros distinct.  Every step of that is
elementary once the sign pattern is given, and it is proven here without a
`sorry`.

## Main statements

* `exists_zero_Ioo` — a continuous function of opposite signs at `u < v`
  vanishes strictly between them.
* `exists_strictMono_zeros_of_alternating` — from `n + 1` increasing points at
  which `f` alternates, a strictly increasing family of `n` zeros, one in each
  gap.
* `exists_interiorZeros_of_alternating` — the polynomial form used by the
  paper: `n` distinct complex roots of the complexified polynomial, all lying in
  the image of the real interval, delivered as the `Finset ℂ` that `FTInputs`
  wants.

## Implementation notes

What this buys is a narrower hypothesis bundle.  `FTInputs.ofSignAlternation`
(in `Bridge`) posits only the sign alternation and derives `interiorZeros`,
`interiorZeros_root`, `interiorZeros_mem` and `bulk_zero_count`, where the plain
constructor posits the zero set itself.  Sorry-free.

## References

Formalizes the intermediate-value step of
`../shields-2026-forgacs-tran-numerators.tex`, «Angular discrepancy and
proof of the main theorem» (`subsec:proof`, `prop:angular-discrepancy`): the passage from the sign
pattern
that `thm:weighted-dominance` establishes at the phase points to a supply of
distinct interior zeros.

## Tags

sign alternation, interior zeros, intermediate value theorem
-/

open Set

namespace ForgacsTran

/-- Paper `subsec:proof`, `prop:angular-discrepancy` — the intermediate-value step.
A continuous function taking values of opposite sign at `u < v` vanishes
strictly between them.  Strict inequality on the product is what puts the zero
in the *open* interval, which is what keeps the zeros of neighbouring gaps
distinct. -/
theorem exists_zero_Ioo {f : ℝ → ℝ} {u v : ℝ} (huv : u < v)
    (hf : ContinuousOn f (Set.Icc u v)) (h : f u * f v < 0) :
    ∃ w ∈ Set.Ioo u v, f w = 0 := by
  rcases mul_neg_iff.mp h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact intermediate_value_Ioo' huv.le hf ⟨hv, hu⟩
  · exact intermediate_value_Ioo huv.le hf ⟨hu, hv⟩

/-- **Paper `subsec:proof`, `prop:angular-discrepancy` — the phase-point count.**
Given `n + 1` strictly increasing points at which `f` alternates in sign, `f`
has a strictly increasing family of `n` zeros, the `k`-th lying strictly inside
the `k`-th gap.  In the paper the points are the images `z(ϑ_k)` of the phase
points and the alternation is `eq:dominance-bound`. -/
theorem exists_strictMono_zeros_of_alternating
    {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x)
    (halt : ∀ k : Fin n, f (x k.castSucc) * f (x k.succ) < 0) :
    ∃ w : Fin n → ℝ, StrictMono w ∧ (∀ k, f (w k) = 0) ∧
      (∀ k, w k ∈ Set.Ioo (x k.castSucc) (x k.succ)) := by
  choose w hw hfw using fun k : Fin n =>
    exists_zero_Ioo (hx (Fin.castSucc_lt_succ (i := k))) hf.continuousOn (halt k)
  refine ⟨w, ?_, hfw, hw⟩
  intro k l hkl
  have hstep : (k.succ : Fin (n + 1)) ≤ l.castSucc := by
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    omega
  calc w k < x k.succ := (hw k).2
    _ ≤ x l.castSucc := hx.monotone hstep
    _ < w l := (hw l).1

/-- **Paper `subsec:proof`, `prop:angular-discrepancy` — the interior-zero supply.**
A real polynomial alternating in sign along `n + 1` increasing points of an
order-connected set `S` has at least `n` distinct zeros in `S`.  Delivered
complexified, as the `Finset ℂ` of roots of `P.map (algebraMap ℝ ℂ)` inside
`Complex.ofReal '' S` — the shape `FTInputs.interiorZeros` takes, since
`thm:main` counts zeros in `ℂ`. -/
theorem exists_interiorZeros_of_alternating
    (P : Polynomial ℝ) {S : Set ℝ} (hS : S.OrdConnected)
    {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : StrictMono x) (hmem : ∀ k, x k ∈ S)
    (halt : ∀ k : Fin n, P.eval (x k.castSucc) * P.eval (x k.succ) < 0) :
    ∃ Z : Finset ℂ, n ≤ Z.card ∧
      (∀ z ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot z) ∧
      (∀ z ∈ Z, z ∈ Complex.ofReal '' S) := by
  obtain ⟨w, hwmono, hwzero, hwmem⟩ :=
    exists_strictMono_zeros_of_alternating P.continuous x hx halt
  -- Each zero inherits membership in `S` from order-connectedness.
  have hwS : ∀ k, w k ∈ S := by
    intro k
    exact hS.out (hmem k.castSucc) (hmem k.succ) ⟨(hwmem k).1.le, (hwmem k).2.le⟩
  classical
  refine ⟨Finset.image (fun k : Fin n => ((w k : ℝ) : ℂ)) Finset.univ, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
    exact fun k l hkl => hwmono.injective (Complex.ofReal_inj.mp hkl)
  · rintro z hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
    have : ((w k : ℝ) : ℂ) = algebraMap ℝ ℂ (w k) := rfl
    rw [Polynomial.IsRoot, this, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      hwzero k, map_zero]
  · rintro z hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨w k, hwS k, rfl⟩

end ForgacsTran
