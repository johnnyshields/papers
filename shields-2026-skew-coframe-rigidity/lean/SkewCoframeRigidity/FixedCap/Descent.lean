/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.Reduction
import SkewCoframeRigidity.FixedCap.StageOne

/-!
# Fixed-cap rigidity: the ceiling and the descent

Formalizes `sc:fixed-cap` of `shields-2026-skew-coframe-rigidity.tex`.  The raw ceiling of the two
right coframes is the first index above every letter they use; once the prefix of zero
coefficients (`prefix_zero`) is in hand, the descent in the proof is needed only when that ceiling
exceeds the span `a` of the cap.  This file proves the rigidity when the ceiling does not exceed
`a`, and states the remaining case as the property `CapDescent`, which `CapDescent.lean` proves
for every connected normalized cap.  Sorry-free, modulo the statements of `Coframe` on which
`Reduction` rests.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {k : ℕ}

/-- The raw ceiling of a diagram: one more than the largest proper row. -/
def ceil {b : ℕ} (B : BetaDiagram (b + 1)) : ℕ :=
  Finset.univ.sup fun i : Fin b => (B.row i.succ).toNat + 1

theorem row_lt_ceil {b : ℕ} (B : BetaDiagram (b + 1)) (i : Fin b) : B.row i.succ < ceil B := by
  have : (B.row i.succ).toNat + 1 ≤ ceil B :=
    Finset.le_sup (f := fun i : Fin b => (B.row i.succ).toNat + 1) (Finset.mem_univ i)
  omega

/-- The coefficients of the right coframe of a normalized diagram vanish from its span on. -/
theorem coframe_coeff_eq_zero {b : ℕ} (B : BetaDiagram (b + 1)) (hB : IsNorm B) {i : ℕ}
    (hi : span B ≤ i) : (coframe B).coeff i = 0 := by
  have hc := top_pos B hB
  have hspan := span_eq_of_norm B hB
  unfold coframe coframeOf
  rw [Polynomial.coeff_add, Polynomial.finset_sum_coeff, Polynomial.coeff_one,
    if_neg (by omega), zero_add]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h1 := colPos_cast_of_norm hB j
  have h2 := B.row_nonempty j.castSucc
  have h3 : B.row j.castSucc ≤ B.row 0 := B.row_strictAnti.antitone (Fin.zero_le _)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

/-- If the raw ceilings of `B`, `B'` do not exceed the span of the cap, the second observation
alone makes the right coframes agree. -/
theorem coframe_eq_of_low (K : BetaDiagram (k + 1)) (hK : IsNorm K) {b : ℕ}
    (B B' : BetaDiagram (b + 1)) (hB : IsNorm B) (hB' : IsNorm B') (hspan : span B = span B')
    (e2 : PowerSeries.coeff (span B + span K) (letterSeries *
      ((leftCoframe K * (coframe B - coframe B') : CohField[X]) : PowerSeries CohField)) = 0)
    (hlow : ceil B ≤ span K) (hlow' : ceil B' ≤ span K) : coframe B = coframe B' := by
  have hKa := span_eq_of_norm K hK
  have hKp := top_pos K hK
  have hpre : ∀ i, i + span K ≤ span B + span K → (coframe B - coframe B').coeff i = 0 := by
    intro i hi
    refine prefix_zero K hK B B' hB hB' (span K) (by omega) (fun i => ?_) (fun i => ?_) e2 i hi
    · have := row_lt_ceil B i
      omega
    · have := row_lt_ceil B' i
      omega
  ext i
  rw [← sub_eq_zero, ← Polynomial.coeff_sub]
  by_cases hi : i ≤ span B
  · exact hpre i (by omega)
  · rw [Polynomial.coeff_sub, coframe_coeff_eq_zero B hB (by omega),
      coframe_coeff_eq_zero B' hB' (by omega), sub_zero]

/-- **The descent**: the case of `sc:fixed-cap` in which the raw ceiling of `B`, `B'` exceeds the
span of the cap.  The hypotheses are the two observations, the
equal span and signed corner, and the prefix of zero coefficients of `prefix_zero`; the
conclusion is the equality of the complete right coframes. -/
def CapDescent (K : BetaDiagram (k + 1)) : Prop :=
  ∀ {b : ℕ} (B B' : BetaDiagram (b + 1)), IsNorm B → IsNorm B' → B.Connected → B'.Connected →
    span B = span B' → cohCorner B = cohCorner B' →
    PowerSeries.coeff (span B) (letterSeries *
      ((coframe B - coframe B' : CohField[X]) : PowerSeries CohField)) = 0 →
    PowerSeries.coeff (span B + span K) (letterSeries *
      ((leftCoframe K * (coframe B - coframe B') : CohField[X]) : PowerSeries CohField)) = 0 →
    (∀ i, i + max (span K) (max (ceil B) (ceil B')) ≤ span B + span K →
      (coframe B - coframe B').coeff i = 0) →
    span K < max (ceil B) (ceil B') →
    coframe B = coframe B'

theorem capVanishing_of_descent (K : BetaDiagram (k + 1)) (hK : IsNorm K)
    (hd : CapDescent K) : CapVanishing K := by
  intro b B B' hB hB' hBc hB'c hspan hcorner e1 e2
  set m := max (span K) (max (ceil B) (ceil B')) with hm
  have hpre : ∀ i, i + m ≤ span B + span K → (coframe B - coframe B').coeff i = 0 := by
    intro i hi
    refine prefix_zero K hK B B' hB hB' m ?_ (fun i => ?_) (fun i => ?_) e2 i hi
    · have := span_eq_of_norm K hK
      have := top_pos K hK
      omega
    · have := row_lt_ceil B i
      omega
    · have := row_lt_ceil B' i
      omega
  by_cases hlow : span K < max (ceil B) (ceil B')
  · exact hd B B' hB hB' hBc hB'c hspan hcorner e1 e2 hpre hlow
  · exact coframe_eq_of_low K hK B B' hB hB' hspan e2 (by omega) (by omega)

/-- **Fixed-cap rigidity** (`sc:fixed-cap`), for every cap whose descent `CapDescent K` holds.
When the raw ceiling of `B`, `B'` does not exceed the span of the cap, the descent is not used
(`capVanishing_of_descent`). -/
theorem fixed_cap_rigidity_of_descent (K : BetaDiagram (k + 1)) (hK : IsNorm K)
    (hKc : K.Connected) (hd : CapDescent K) {b b' : ℕ} (B : BetaDiagram (b + 1))
    (B' : BetaDiagram (b' + 1)) (hB : IsNorm B) (hB' : IsNorm B') (hBc : B.Connected)
    (hB'c : B'.Connected) (h1 : B.schur = B'.schur)
    (h2 : (splice K B hK hB).schur = (splice K B' hK hB').schur) : b = b' ∧ HEq B B' :=
  fixed_cap_rigidity K hK hKc (capVanishing_of_descent K hK hd) B B' hB hB' hBc hB'c h1 h2

/-- **Unconditional fixed-cap rigidity for short children.**  If the raw ceilings of `B` and `B'`
do not exceed the span of the cap, then `s_B = s_{B'}` and `s_{K ◁ B} = s_{K ◁ B'}` force
`B = B'`; no descent is needed. -/
theorem fixed_cap_rigidity_low (K : BetaDiagram (k + 1)) (hK : IsNorm K) (hKc : K.Connected)
    {b b' : ℕ} (B : BetaDiagram (b + 1)) (B' : BetaDiagram (b' + 1)) (hB : IsNorm B)
    (hB' : IsNorm B') (hBc : B.Connected) (hB'c : B'.Connected) (h1 : B.schur = B'.schur)
    (h2 : (splice K B hK hB).schur = (splice K B' hK hB').schur)
    (hlow : ceil B ≤ span K) (hlow' : ceil B' ≤ span K) : b = b' ∧ HEq B B' := by
  have hb : b = b' := by
    have e1 := BetaDiagram.rowDegree B
    have e2 := BetaDiagram.rowDegree B'
    rw [h1] at e1
    omega
  subst hb
  obtain ⟨hspan, -, -, e2⟩ := cap_observations K hK hKc B B' hB hB' hBc hB'c h1 h2
  exact eq_of_coframe_eq hB hB' hBc hB'c hspan
    (coframe_eq_of_low K hK B B' hB hB' hspan e2 hlow hlow')

end SkewCoframeRigidity.FixedCap
