/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.UnitRegularity
import SkewCoframeRigidity.UnitRestoration.ZeroFree

/-!
# Shared setup of the unit case

Formalizes the common objects of the unit case of `sc:positive-power` in
`shields-2026-skew-coframe-rigidity.tex`.  The positive generic letters are scaled by a new
variable `ε`: the field `Eps` is the fraction field of `CohField[ε]`, the letters `H_k / ϑ` are the
normalized letters (the coherent unit becomes one), `epsH` is the scaled letter series
`1 + ε Ū` over `Eps`, and `hatCoframe D` is the complete coframe of `D` for the scaled letters.
Over the polynomial ring `CohField[ε]` the same series is `AH`.
-/

namespace SkewCoframeRigidity.UnitCase

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.UnitRestoration Polynomial

/-- The field of rational functions in `ε` over the generic letters. -/
abbrev Eps : Type := EpsField CohField

/-- The normalized letters `H_k / ϑ`, so that the coherent unit is one. -/
noncomputable def normLetters : ℕ → CohField := fun k => cohLetters k / cohLetters 0

/-- The scaled normalized letters in `Eps`: the unit is one, a positive letter carries `ε`. -/
noncomputable def epsSeq : ℕ → Eps := scaledSeq normLetters

/-- The scaled letter series over `Eps`. -/
noncomputable def epsH : PowerSeries Eps := PowerSeries.mk epsSeq

/-- The complete coframe of a diagram for the scaled normalized letters. -/
noncomputable def hatCoframe {n : ℕ} (D : BetaDiagram (n + 1)) : Eps[X] := coframeOf epsSeq D

/-- The positive part `Ū = ∑_{k ≥ 1} (H_k / ϑ) z^k` of the normalized letter series. -/
noncomputable def Ubar : PowerSeries CohField :=
  PowerSeries.mk fun k => if k = 0 then 0 else normLetters k

/-- The scaled letter series `1 + ε Ū` over the polynomial ring `CohField[ε]`. -/
noncomputable def AH : PowerSeries CohField[X] :=
  1 + PowerSeries.C (Polynomial.X : CohField[X]) * PowerSeries.map Polynomial.C Ubar

/-- A polynomial over `CohField` as a polynomial over `CohField[ε]` with constant coefficients. -/
noncomputable def liftK (f : CohField[X]) : Polynomial CohField[X] := f.map Polynomial.C

end SkewCoframeRigidity.UnitCase
