/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPurePrefixCases
import SkewCornerDescent.Matrix.OriginalPureCoefficientSupport
import SkewCornerDescent.Matrix.PureBinaryProfileData

/-!
# Binary first differences produced from complete original pure profiles

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The complete inverse equations supply the two possible incoming coefficients.
A genuine first discrepancy then supplies nonconstant bits, normalized at
any actual baseline, and a nonzero amplitude in the strict lower field of
the resolving generator. Earlier-prefix equality and the discrepancy remain
explicit inputs for the first-discrepancy construction. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual visible pure incoming profiles produce the nonzero binary alphabet
and its protected-field support, rather than assuming either of them. The
baseline may itself contain the corresponding physical unit vertex. -/
theorem originalPure_binary_first_differences {n : ℕ} {I : Type*}
    (P : Profile n) (k : ℕ)
    (hK : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ k)
    (idx : I → Fin (originalSelectedCount (hD := hD) P - 1)) (base : I)
    (w : ℕ) (hN : (c.top : ℕ) < w)
    (hw : ∀ i, 2 * (w : ℤ) < originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P (idx i)) (originalInternalStateIndex P (idx i)))
    (H : ℕ+) (hwH : w < (H : ℕ))
    (hprefix : ∀ i j, j < w →
      ((c.originalInternalEndpointProfiles P (idx i)).1).coeff j =
      ((c.originalInternalEndpointProfiles P (idx base)).1).coeff j)
    (hne : ∃ i, ((c.originalInternalEndpointProfiles P (idx i)).1).coeff w ≠
      ((c.originalInternalEndpointProfiles P (idx base)).1).coeff w) :
    ∃ η : OtherField c.top, η ≠ 0 ∧ η ∈ residueLowerField c.top H ∧
      ∃ bits : I → Bool, bits base = false ∧ (∃ i j, bits i ≠ bits j) ∧
        ∀ i, ((c.originalInternalEndpointProfiles P (idx i)).1).coeff w -
          ((c.originalInternalEndpointProfiles P (idx base)).1).coeff w =
          if bits i then η else 0 := by
  let A := fun i => (c.originalInternalEndpointProfiles P (idx i)).1
  obtain ⟨η, hη, _, bits, hbase, hbits⟩ :=
    polynomial_prefix_binary_differences c.residueMap A base w hprefix
      (fun i => c.originalPure_visible_left_coefficient_cases P k hK (idx i) w hN (hw i)) hne
  obtain ⟨i, hi⟩ := hne
  have hdiff : (A i).coeff w - (A base).coeff w ≠ 0 := sub_ne_zero.mpr hi
  have hbit : bits i = true := by
    cases hb : bits i
    · have he := hbits i
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at he
      exact False.elim (hdiff he)
    · rfl
  have hηmem : η ∈ residueLowerField c.top H := by
    have he := hbits i
    simp only [hbit, ↓reduceIte] at he
    rw [← he]
    exact (residueLowerField c.top H).sub_mem
      (c.originalPure_visible_left_coefficient_mem_lower P k hK (idx i) w hN (hw i) H hwH)
      (c.originalPure_visible_left_coefficient_mem_lower P k hK (idx base) w hN (hw base) H hwH)
  refine ⟨η, hη, hηmem, bits, hbase, ⟨i, base, ?_⟩, hbits⟩
  simp only [hbit, hbase, ne_eq, Bool.true_eq_false, not_false_eq_true]

end SkewCornerDescent.Matrix.SelectedCoordinate
