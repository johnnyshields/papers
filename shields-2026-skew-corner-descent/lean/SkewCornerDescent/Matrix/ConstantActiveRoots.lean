/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.AnchorSliceOrder

/-!
# Actual roots with constant active labels

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`, `lem:exposure`).
The active response identity gives the original rational root as a positive cap product
times the rational label, minus the common correction. This preserves active-label order
across chambers with different lower-generator assignments. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- The original rational anchor root of an active affine class is its constant label
scaled by the cap product, minus the shared closure correction. -/
theorem actual_anchor_root_eq_affine_label
    (p q base cap scaleDen : MvPolynomial ℕ ℝ) (label : ℚ) (x : ℕ → ℝ)
    (hidentity : p * scaleDen = (base - MvPolynomial.C (label : ℝ) * cap) * q)
    (hq : MvPolynomial.eval x q ≠ 0) (hscale : MvPolynomial.eval x scaleDen ≠ 0) :
    -MvPolynomial.eval x p / MvPolynomial.eval x q =
      (label : ℝ) * (MvPolynomial.eval x cap / MvPolynomial.eval x scaleDen) -
        MvPolynomial.eval x base / MvPolynomial.eval x scaleDen := by
  have he := congrArg (MvPolynomial.eval x) hidentity
  simp only [map_mul, map_sub, MvPolynomial.eval_C] at he
  field_simp [hq, hscale]
  nlinarith [he]

/-- Positive cap products preserve the strict order of active labels at each actual
chamber point; no equality between the two assignments is needed. -/
theorem actual_anchor_root_order_of_labels
    (pa qa pb qb base cap scaleDen : MvPolynomial ℕ ℝ) (la lb : ℚ) (x : ℕ → ℝ)
    (ha : pa * scaleDen = (base - MvPolynomial.C (la : ℝ) * cap) * qa)
    (hb : pb * scaleDen = (base - MvPolynomial.C (lb : ℝ) * cap) * qb)
    (hqa : MvPolynomial.eval x qa ≠ 0) (hqb : MvPolynomial.eval x qb ≠ 0)
    (hscale : MvPolynomial.eval x scaleDen ≠ 0)
    (hcap : 0 < MvPolynomial.eval x cap / MvPolynomial.eval x scaleDen) (hlab : la < lb) :
    -MvPolynomial.eval x pa / MvPolynomial.eval x qa <
      -MvPolynomial.eval x pb / MvPolynomial.eval x qb := by
  rw [actual_anchor_root_eq_affine_label pa qa base cap scaleDen la x ha hqa hscale,
    actual_anchor_root_eq_affine_label pb qb base cap scaleDen lb x hb hqb hscale]
  exact sub_lt_sub_right (mul_lt_mul_of_pos_right (by exact_mod_cast hlab) hcap) _

end SkewCornerDescent.Matrix.SelectedCoordinate
