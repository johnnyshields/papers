/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Shift

/-!
# Definitions of the unshifted exclusion

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`sec:unshifted`, `ph:unshifted-exclusion`): the objects `m = M - 1`, `y = H_m`, `G = G₀ + y a`,
`C = C₀ + y b`, `Δ = G₀ - C₀`, the defect operators `ℰ^M_{A,B}` and the three coefficients of the
expansion of the unshifted identity in `y`.  The hypotheses of the lemma are bundled in
`ExclusionHyp`, together with the contradiction hypothesis `V ≠ W`.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- `ℰ^M_{A,B}(u) = 𝒯^M_{A,B}(u^p) - p u^{p-1} 𝒯^M_{A,B}(u)`, as a power series. -/
noncomputable def Eop (p M : ℕ) (A B : K[X]) (u : PowerSeries K) : PowerSeries K :=
  ((clippedOp M A B (u ^ p) : K[X]) : PowerSeries K) -
    PowerSeries.C (p : K) * u ^ (p - 1) * ((clippedOp M A B u : K[X]) : PowerSeries K)

/-- The unshifted identity `𝒯_{G,C}(H^p) = p [H^{p-1} D]_{<2M}` at precision `2M` for the
letter sequence `h`, with `G, C` the coframes of `V, W` and `D = 𝒯_{G,C}(H)`. -/
def UnshiftedEq (p : ℕ) (h : ℕ → K) (V W : BetaDiagram (n + 1)) : Prop :=
  ∀ k < 2 * span V,
    (clippedOp (span V) (coframeOf h V) (coframeOf h W) (seriesOf h ^ p)).coeff k =
      (p : K) * PowerSeries.coeff k (seriesOf h ^ (p - 1) *
        ((clippedOp (span V) (coframeOf h V) (coframeOf h W) (seriesOf h) : K[X]) :
          PowerSeries K))

/-- The hypotheses of `ph:unshifted-exclusion`, with the contradiction hypothesis `V ≠ W`. -/
structure ExclusionHyp (V W : BetaDiagram (n + 1)) (p : ℕ) : Prop where
  conn : V.Connected
  colV : V.col (Fin.last n) = 0
  colW : W.col (Fin.last n) = 0
  rot : V.RotationEquivalent W
  span3 : 3 ≤ span V
  hp : 2 ≤ p
  eq : UnshiftedEq p cohLetters V W
  ne : V ≠ W

/-- The letters with the top letter `y = H_m`, `m = M - 1`, set to zero. -/
noncomputable def zeroTop (V : BetaDiagram (n + 1)) : ℕ → CohField :=
  Function.update cohLetters (span V - 1) 0

/-- The letter series `h` with `h_m = 0`. -/
noncomputable def hSer (V : BetaDiagram (n + 1)) : PowerSeries CohField := seriesOf (zeroTop V)

/-- The top letter `y = H_m`. -/
noncomputable def topY (V : BetaDiagram (n + 1)) : CohField := cohLetters (span V - 1)

/-- `G₀`: the coframe of `V` with `y = 0`. -/
noncomputable def G0 (V : BetaDiagram (n + 1)) : CohField[X] := coframeOf (zeroTop V) V

/-- `C₀`: the coframe of the rotation `W` with `y = 0`. -/
noncomputable def C0 (V W : BetaDiagram (n + 1)) : CohField[X] := coframeOf (zeroTop V) W

/-- The endpoint column `a`, the slope of `G` in `y`. -/
noncomputable def aVec (V : BetaDiagram (n + 1)) : CohField[X] := endpointA (zeroTop V) V

/-- The endpoint column `b`, the slope of `C` in `y`. -/
noncomputable def bVec (V : BetaDiagram (n + 1)) : CohField[X] := endpointB (zeroTop V) V

/-- `Δ = G₀ - C₀`. -/
noncomputable def Delta (V W : BetaDiagram (n + 1)) : CohField[X] := G0 V - C0 V W

/-- The factor `p (ϑ^{p-1} - h^{p-1}) z^m` of the explicit-`y` terms. -/
noncomputable def pDiff (p : ℕ) (V : BetaDiagram (n + 1)) : PowerSeries CohField :=
  PowerSeries.C (p : CohField) *
    (PowerSeries.C (cohLetters 0) ^ (p - 1) - hSer V ^ (p - 1)) *
      PowerSeries.X ^ (span V - 1)

/-- `[y^0]ℰ = ℰ^M_{W₀}`. -/
noncomputable def coefY0 (p : ℕ) (V W : BetaDiagram (n + 1)) : PowerSeries CohField :=
  Eop p (span V) (G0 V) (C0 V W) (hSer V)

/-- `[y^1]ℰ = ℰ^M_{W₁} + p (ϑ^{p-1} - h^{p-1}) z^m Δ`, `W₁ = a ∧ C₀ + G₀ ∧ b`. -/
noncomputable def coefY1 (p : ℕ) (V W : BetaDiagram (n + 1)) : PowerSeries CohField :=
  Eop p (span V) (aVec V) (C0 V W) (hSer V) + Eop p (span V) (G0 V) (bVec V) (hSer V) +
    pDiff p V * ((Delta V W : CohField[X]) : PowerSeries CohField)

/-- `[y^2]ℰ = ℰ^M_{W₂} + p (ϑ^{p-1} - h^{p-1}) z^m (a - b)`, `W₂ = a ∧ b`. -/
noncomputable def coefY2 (p : ℕ) (V W : BetaDiagram (n + 1)) : PowerSeries CohField :=
  Eop p (span V) (aVec V) (bVec V) (hSer V) +
    pDiff p V * ((aVec V - bVec V : CohField[X]) : PowerSeries CohField)

variable {V W : BetaDiagram (n + 1)} {p : ℕ}

end SkewCoframeRigidity.Unshifted
