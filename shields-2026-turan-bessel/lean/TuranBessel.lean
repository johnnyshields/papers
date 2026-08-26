/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.MatrixMD
import TuranBessel.Trigamma
import TuranBessel.Coefficients
import TuranBessel.Convolution
import TuranBessel.Zseries
import TuranBessel.Hypergeometric
import TuranBessel.BesselI
import TuranBessel.ParameterCalculus
import TuranBessel.DetAssembly
import TuranBessel.AlphaCoeff
import TuranBessel.BetaGammaCoeff
import TuranBessel.TuranDet
import TuranBessel.BesselDict
import TuranBessel.BesselDictPH
import TuranBessel.BesselLaw
import TuranBessel.ScalarH
import TuranBessel.Gram
import TuranBessel.Anomaly
import TuranBessel.Degree
import TuranBessel.Main
import TuranBessel.Threshold
import TuranBessel.NegativeOrder
import TuranBessel.Bridge
import TuranBessel.Phase
import TuranBessel.Boundary
import TuranBessel.WallOrder
import TuranBessel.Scaling
import TuranBessel.Digamma
import TuranBessel.CriticalConstant
import TuranBessel.GammaRatio
import TuranBessel.GramRep
import TuranBessel.Microcanonical
import TuranBessel.FourCopy
import TuranBessel.TuranDetKT
import TuranBessel.Sharpness
import TuranBessel.SectorAverage
import TuranBessel.ZeroCount
import TuranBessel.AxiomCheck

/-!
# Canonical--microcanonical positivity for a Bessel--₀F₁ matrix Turán determinant

The root of the formalization of `shields-2026-turan-bessel.tex`.  It imports
every module, so `import TuranBessel` brings the whole development into scope
and the axiom guard of `AxiomCheck.lean` runs with it.

The paper's object is the symmetric matrix built from the order curvature
`G_ν`, the mixed order--argument derivative `P_ν`, and the classical Turánian,
corrected by a trigamma term forced by the vacuum limit (`eq:Gnu`--`eq:Hnu-kappa`).
`thm:bessel` is its positive definiteness on `ν > -1`, `z > 0`.  The route
through the modules is the paper's own: replace the Bessel functions by the
reciprocal-gamma series `Z` of `eq:Zdef`, read the coefficient matrices as Schur
deficits of conditioned discrete Bessel ensembles, and polarize.

* **The substrate.**  `MatrixMD` is the mixed discriminant `MD` and wedge
  positivity (`lem:MD-positive`); `Trigamma` and `Tetragamma` build `ψ₁` and `ψ₂`
  from their series, since Mathlib has no polygamma; `Zseries`, `Hypergeometric`
  and `BesselI` identify `Z` with Mathlib's regularized `₀F₁` and split
  `log I_ν` along `eq:I-Z`.
* **The coefficient calculus.**  `Convolution` proves `lem:convolution`;
  `ParameterCalculus` differentiates `Z` in the order under the sum;
  `AlphaCoeff`, `BetaGammaCoeff` and `Coefficients` give the entries of
  `eq:ABC-expansions`; `DetAssembly` and `TuranDet` assemble `eq:Delta-n-MD`.
* **The dictionary.**  `BesselDict`, `BesselDictPH` and `Bridge` carry the
  series statements back to `G_ν`, `P_ν`, `H_ν^{(κ)}` and `det 𝒮_ν`, which is
  where `thm:bessel` and `cor:bessel-matrix` are stated.
* **The endpoint.**  `Gram` and `GramRep` prove `thm:gram`; `Anomaly` isolates
  the exceptional `M_1` of `lem:M1-indefinite`; `Degree`, `Threshold` and `Main`
  close `thm:coefficientwise`, and `Boundary` proves `lem:boundary-positivity`
  in full.
* **The ensembles.**  `BesselLaw`, `Microcanonical`, `FourCopy` and
  `SectorAverage` are `thm:ensemble-hierarchy` and `prop:four-copy`: the fiber
  laws, their moments, and the defect as a canonical sector average.
* **The phase diagram.**  `Phase`, `WallOrder`, `TuranDetKT`, `Sharpness` and
  `ZeroCount` run the two-parameter family `(κ,τ)` of `eq:Tkt`, giving
  `thm:two-parameter-coeff` as an iff in `τ` and the sharp quadrant of
  `prop:bessel-sharpness`.
* **The scaling limit.**  `Scaling`, `Digamma`, `GammaRatio` and
  `CriticalConstant` are `sec:scaling`: `eq:Sm-gamma-ratio`, the asymptotics of
  `eq:Sm-asymptotic`, and `prop:c-monotone` with the exact range of `c(a)`.
* **`NegativeOrder`** is `app:continuation`, the failure `Δ_2 < 0` outside the
  positive-series domain.

The development is sorry-free and carries no project axiom; `AxiomCheck` pins
that for every result `README.md` claims.
-/
