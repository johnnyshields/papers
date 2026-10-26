/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.UniversalOmegaAlphabet
import Shields.Combinatorics.Young.ElementarySymmetric

/-!
# Elementary tableau coefficients on independent alphabets

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The column-tableau coefficient agrees with the finite elementary polynomial
at every degree, including the exhausted-alphabet regime. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial

/-- Column tableaux specialize to the elementary symmetric polynomial. -/
theorem elemHom_varAlphabet (a q : ℕ) :
    Shields.elemHom a q (varAlphabet a) = esymm (Fin a) ℚ q := by
  classical
  rw [Shields.elemHom_eq_sum_powersetCard]
  have hr : Finset.range a = (Finset.univ : Finset (Fin a)).map Fin.valEmbedding := by
    ext i
    simp only [Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨⟨i, h⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [hr, Finset.powersetCard_map, Finset.sum_map]
  change (∑ S ∈ Finset.powersetCard q (Finset.univ : Finset (Fin a)),
    ∏ i ∈ S.map Fin.valEmbedding, varAlphabet a i) = _
  simp only [Finset.prod_map, Fin.valEmbedding_apply, varAlphabet_val]
  rfl

/-- Complete specialization after universal omega is exactly the tableau
column specialization, with no cutoff in the original generator ring. -/
theorem evalComplete_comp_schurInvolution_elemHom (a : ℕ) :
    (evalComplete a (varAlphabet a)).comp schurInvolution =
      aeval (fun n : ℕ+ => Shields.elemHom a n (varAlphabet a)) := by
  rw [evalComplete_comp_schurInvolution]
  congr 1
  funext n
  exact (elemHom_varAlphabet a n).symm

end SkewCornerDescent
