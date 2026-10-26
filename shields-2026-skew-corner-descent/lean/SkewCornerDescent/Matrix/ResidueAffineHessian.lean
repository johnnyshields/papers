/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueGeneratorDerivation

/-!
# Rational affine planes preserve actual mixed higher jets

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`, `cor:row-pencil`).
The actual residue-field derivations annihilate rational labels. Mixed jets of
an actual rational affine plane therefore retain its exact cap-product factor,
without replacing any source response by an independent affine variable.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Every actual surviving-generator derivative annihilates rational constants. -/
theorem residueGeneratorDeriv_ratCast (N : ℕ+) (j : {j : ℕ+ // j ≠ N}) (a : ℚ) :
    residueGeneratorDeriv N j (a : OtherField N) = 0 := by
  simpa using (residueGeneratorDeriv N j).map_algebraMap a

/-- Two actual higher-generator derivatives of a rational affine plane give
its exact mixed linear relation in the unchanged original residue field. -/
theorem residue_mixed_jet_affine (N : ℕ+) (j k : {j : ℕ+ // j ≠ N})
    (a : ℚ) (S T : OtherField N) :
    residueGeneratorDeriv N j (residueGeneratorDeriv N k (S - (a : OtherField N) * T)) =
      residueGeneratorDeriv N j (residueGeneratorDeriv N k S) -
        (a : OtherField N) * residueGeneratorDeriv N j (residueGeneratorDeriv N k T) := by
  simp only [map_sub, Derivation.leibniz, smul_eq_mul, residueGeneratorDeriv_ratCast,
    mul_zero, add_zero]

/-- Exact integer mixed jets in an actual rational affine plane recover the
rational label itself. The nonzero cap jet cancels in the unchanged field. -/
theorem residue_affine_label_of_integer_mixed_jets (N : ℕ+)
    (j k : {j : ℕ+ // j ≠ N}) (a : ℚ) (S S₀ T w : OtherField N) (hw : w ≠ 0)
    (m n : ℕ) (haffine : S = S₀ - (a : OtherField N) * T)
    (hS : residueGeneratorDeriv N j (residueGeneratorDeriv N k S) = -w * (n : OtherField N))
    (hS₀ : residueGeneratorDeriv N j (residueGeneratorDeriv N k S₀) = -w * (m : OtherField N))
    (hT : residueGeneratorDeriv N j (residueGeneratorDeriv N k T) = w) :
    a = (n : ℚ) - (m : ℚ) := by
  have h := congrArg (fun x : OtherField N =>
    residueGeneratorDeriv N j (residueGeneratorDeriv N k x)) haffine
  rw [residue_mixed_jet_affine, hS, hS₀, hT] at h
  have hp : (a : OtherField N) * w =
      ((n : OtherField N) - (m : OtherField N)) * w := by
    linear_combination h
  have he := mul_right_cancel₀ hw hp
  exact_mod_cast he

/-- A mixed jet of the difference from the actual reference recovers the
rational affine label without requiring the two individual Hessians to vanish. -/
theorem residue_affine_label_of_mixed_difference (N : ℕ+)
    (j k : {j : ℕ+ // j ≠ N}) (a e : ℚ) (S S₀ T w : OtherField N) (hw : w ≠ 0)
    (haffine : S = S₀ - (a : OtherField N) * T)
    (hdiff : residueGeneratorDeriv N j (residueGeneratorDeriv N k (S - S₀)) =
      -(e : OtherField N) * w)
    (hT : residueGeneratorDeriv N j (residueGeneratorDeriv N k T) = w) : a = e := by
  have he : S - S₀ = 0 - (a : OtherField N) * T := by rw [haffine]; ring
  rw [he, residue_mixed_jet_affine, hT] at hdiff
  simp only [map_zero, zero_sub, neg_mul] at hdiff
  have hm : (a : OtherField N) * w = (e : OtherField N) * w := neg_injective hdiff
  have hcast := mul_right_cancel₀ hw hm
  exact_mod_cast hcast

end SkewCornerDescent.Matrix
