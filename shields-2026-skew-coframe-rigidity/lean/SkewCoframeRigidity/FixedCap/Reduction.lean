/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.SpliceIdentity
import SkewCoframeRigidity.FixedCap.LeftCoframe
import SkewCoframeRigidity.RowDegree
import SkewCoframeRigidity.Coframe.Coherent
import SkewCoframeRigidity.Coframe.CoequalData

/-!
# Fixed-cap rigidity: the coherent form of the two observations

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Rigidity with the same literal cap»
(`sec:fixed-caps`, `sc:fixed-cap`, equation `sc:fcp-observations`).  For connected normalized
`B, B'` and a fixed connected normalized cap `K`, equality of the two functions
`s_B = s_{B'}` and `s_{K ◁ B} = s_{K ◁ B'}` is equivalent, over the raw field of the coherent
letters, to the two linear observations
`[z^c] H (G_B - G_{B'}) = 0` and `[z^{c+a}] H C_K (G_B - G_{B'}) = 0`, together with equal
span, row count and signed corner.  Sorry-free, modulo the statements of `Coframe` on which it
rests.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {k : ℕ}

/-- The two observations of `sc:fcp-observations`, as the statement that they force the complete
right coframes of two connected normalized diagrams with the same span and signed corner to
coincide.  This is the content of the descent in the proof of `sc:fixed-cap`; it is equivalent
to Theorem `sc:fixed-cap` for the cap `K` once the two observations are identified with the
equalities `s_B = s_{B'}` and `s_{K ◁ B} = s_{K ◁ B'}` (`cap_observations`). -/
def CapVanishing (K : BetaDiagram (k + 1)) : Prop :=
  ∀ {b : ℕ} (B B' : BetaDiagram (b + 1)), IsNorm B → IsNorm B' → B.Connected → B'.Connected →
    span B = span B' → cohCorner B = cohCorner B' →
    PowerSeries.coeff (span B) (letterSeries *
      ((coframe B - coframe B' : CohField[X]) : PowerSeries CohField)) = 0 →
    PowerSeries.coeff (span B + span K) (letterSeries *
      ((leftCoframe K * (coframe B - coframe B') : CohField[X]) : PowerSeries CohField)) = 0 →
    coframe B = coframe B'

theorem span_eq_of_norm {n : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D) :
    span D = (D.row 0).toNat := by
  unfold span BetaDiagram.largestLabel
  have : D.col (Fin.last n) = 0 := hD
  rw [this, sub_zero]

/-- The determinant of the splice, in the raw field, via the splice identity. -/
theorem splice_schur_cohLetters {b : ℕ} (K : BetaDiagram (k + 1)) (hK : IsNorm K)
    (hKc : K.Connected) (B : BetaDiagram (b + 1)) (hB : IsNorm B) (hBc : B.Connected) :
    schurOf cohLetters (splice K B hK hB) = cornerOf cohLetters K * cornerOf cohLetters B *
      PowerSeries.coeff (span B + span K) (letterSeries *
        ((leftCoframe K * coframe B : CohField[X]) : PowerSeries CohField)) := by
  have hKu : IsUnit (properMatrixOf cohLetters K).det :=
    isUnit_iff_ne_zero.mpr (properDet_cohLetters_ne_zero hKc)
  have hBt : (properMatrixOf cohLetters B).det ≠ 0 := properDet_cohLetters_ne_zero hBc
  rw [schurOf_splice (h := cohLetters) (hK := hK) (hB := hB) (leftVecOf cohLetters K)
    (coframeVecOf cohLetters B) (leftVecOf_vecMul cohLetters K hKu)
    (properMatrix_mulVec_coframeVecOf cohLetters B hBt) hKu]
  have hn : (B.row 0 + K.row 0).toNat = span B + span K := by
    rw [span_eq_of_norm B hB, span_eq_of_norm K hK]
    have := top_pos B hB
    have := top_pos K hK
    omega
  rw [hn]
  rfl

theorem cornerOf_cohLetters {n : ℕ} (D : BetaDiagram (n + 1)) :
    cornerOf cohLetters D = algebraMap CohRing CohField (cohCorner D) := by
  unfold cornerOf cohCorner
  rw [properMatrix_cohLetters, ← RingHom.map_det]
  simp only [cornerOf, map_mul, map_pow, map_neg, map_one]

/-- `s_B = s_{B'}` and `s_{K ◁ B} = s_{K ◁ B'}` yield equal span and signed corner and the two
observations of `sc:fcp-observations`. -/
theorem cap_observations {b : ℕ} (K : BetaDiagram (k + 1)) (hK : IsNorm K) (hKc : K.Connected)
    (B B' : BetaDiagram (b + 1)) (hB : IsNorm B) (hB' : IsNorm B') (hBc : B.Connected)
    (hB'c : B'.Connected) (h1 : B.schur = B'.schur)
    (h2 : (splice K B hK hB).schur = (splice K B' hK hB').schur) :
    span B = span B' ∧ cohCorner B = cohCorner B' ∧
      PowerSeries.coeff (span B) (letterSeries *
        ((coframe B - coframe B' : CohField[X]) : PowerSeries CohField)) = 0 ∧
      PowerSeries.coeff (span B + span K) (letterSeries *
        ((leftCoframe K * (coframe B - coframe B') : CohField[X]) : PowerSeries CohField)) = 0 := by
  obtain ⟨-, hcorner, hspan, hquot, -, -⟩ := coequal_data hBc h1
  refine ⟨hspan, hcorner, ?_, ?_⟩
  · have : PowerSeries.coeff (span B) (letterSeries * (coframe B : PowerSeries CohField)) =
        PowerSeries.coeff (span B') (letterSeries * (coframe B' : PowerSeries CohField)) := hquot
    rw [← hspan] at this
    rw [Polynomial.coe_sub, mul_sub, map_sub, sub_eq_zero]
    exact this
  · have hS := cohSchur_eq_of_schur_eq h2
    have hS' : schurOf cohLetters (splice K B hK hB) = schurOf cohLetters (splice K B' hK hB') := by
      have e : ∀ D : BetaDiagram (k + b + 1),
          schurOf cohLetters D = algebraMap CohRing CohField (cohSchur D) := fun D => by
        unfold schurOf cohSchur
        rw [fullMatrix_cohLetters, ← RingHom.map_det]
        rfl
      rw [e, e, hS]
    rw [splice_schur_cohLetters K hK hKc B hB hBc, splice_schur_cohLetters K hK hKc B' hB'
      hB'c] at hS'
    have hKne : cornerOf cohLetters K ≠ 0 := by
      unfold cornerOf
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (properDet_cohLetters_ne_zero hKc)
    have hBne : cornerOf cohLetters B ≠ 0 := by
      unfold cornerOf
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (properDet_cohLetters_ne_zero hBc)
    have hcc : cornerOf cohLetters B = cornerOf cohLetters B' := by
      rw [cornerOf_cohLetters, cornerOf_cohLetters, hcorner]
    rw [← hcc] at hS'
    have := mul_left_cancel₀ (mul_ne_zero hKne hBne) hS'
    rw [← hspan] at this
    rw [mul_sub, Polynomial.coe_sub, mul_sub, map_sub, sub_eq_zero]
    exact this

/-- **Fixed-cap rigidity** (`sc:fixed-cap`), for a cap `K` whose descent `CapVanishing K` holds.
Two connected normalized diagrams with the same function and the same function after the same
`00`-splice with `K` are the same diagram. -/
theorem fixed_cap_rigidity (K : BetaDiagram (k + 1)) (hK : IsNorm K) (hKc : K.Connected)
    (hcap : CapVanishing K) {b b' : ℕ} (B : BetaDiagram (b + 1)) (B' : BetaDiagram (b' + 1))
    (hB : IsNorm B) (hB' : IsNorm B') (hBc : B.Connected) (hB'c : B'.Connected)
    (h1 : B.schur = B'.schur)
    (h2 : (splice K B hK hB).schur = (splice K B' hK hB').schur) : b = b' ∧ HEq B B' := by
  have hb : b = b' := by
    have e1 := BetaDiagram.rowDegree B
    have e2 := BetaDiagram.rowDegree B'
    rw [h1] at e1
    omega
  subst hb
  obtain ⟨hspan, hcorner, e1, e2⟩ := cap_observations K hK hKc B B' hB hB' hBc hB'c h1 h2
  have hcof := hcap B B' hB hB' hBc hB'c hspan hcorner e1 e2
  exact eq_of_coframe_eq hB hB' hBc hB'c hspan hcof

end SkewCoframeRigidity.FixedCap
