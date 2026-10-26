/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.CornerMinors
import SkewCofactorIndependence.ConnectedIrreducibility
import SkewCoframeRigidity.ClippedOperator
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Coherent letters, the complete right coframe and the defect

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Diagrams, full flags, and coherent units»
and «The complete boundary solve» (`sec:coframe-coordinates`, `sc:coframe-definition`,
`sc:finite-operator`).

Everything is stated for an arbitrary letter sequence `h : ℕ → L` in a field (or commutative
ring) `L`, with `h 0` the coherent unit `ϑ` and negative indices equal to zero.  The generic
letters are those of the polynomial ring `ℚ[ϑ, H₁, H₂, …] = MvPolynomial ℕ ℚ`, embedded in its
fraction field `CohField`.  A diagram needs no normalization: positions are measured from the
last column beta, which is zero for a normalized diagram.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {L : Type*}

/-- The Jacobi–Trudi letter `H_k` of a letter sequence, with `H_k = 0` for `k < 0`. -/
def letterOf [Zero L] (h : ℕ → L) (k : ℤ) : L := if k < 0 then 0 else h k.toNat

section Diagram

variable {n : ℕ}

/-- The complete coherent Jacobi–Trudi matrix `(H_{X_i - Y_j})`. -/
def fullMatrixOf [Zero L] (h : ℕ → L) (D : BetaDiagram n) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => letterOf h (D.row i - D.col j)

/-- The coherent Jacobi–Trudi determinant `s_A`. -/
def schurOf [CommRing L] (h : ℕ → L) (D : BetaDiagram n) : L := (fullMatrixOf h D).det

/-- The proper matrix `T_A`: the top row beta and the column beta zero are deleted. -/
def properMatrixOf [Zero L] (h : ℕ → L) (D : BetaDiagram (n + 1)) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => letterOf h (D.row i.succ - D.col j.castSucc)

/-- The signed proper corner `κ_A = (-1)^{r-1} det T_A`. -/
def cornerOf [CommRing L] (h : ℕ → L) (D : BetaDiagram (n + 1)) : L :=
  (-1) ^ n * (properMatrixOf h D).det

/-- The column `(H_i)_{i ∈ I_A}` of the right-hand side of the coframe equation. -/
def topVecOf [Zero L] (h : ℕ → L) (D : BetaDiagram (n + 1)) : Fin n → L :=
  fun i => letterOf h (D.row i.succ - D.col (Fin.last n))

/-- The span `M` of a diagram: the largest label `X₁ - Y_r`. -/
def span (D : BetaDiagram (n + 1)) : ℕ := D.largestLabel.toNat

/-- The position `s ∈ S_A` of the `j`-th column beta, measured from the last column beta. -/
def colPos (D : BetaDiagram (n + 1)) (j : Fin n) : ℕ :=
  (D.col j.castSucc - D.col (Fin.last n)).toNat

/-- The position `i ∈ I_A` of the `i`-th row beta (below the top one). -/
def rowPos (D : BetaDiagram (n + 1)) (i : Fin n) : ℕ :=
  (D.row i.succ - D.col (Fin.last n)).toNat

/-- The set `S_A` of interior column positions. -/
def colSet (D : BetaDiagram (n + 1)) : Finset ℕ := Finset.univ.image (colPos D)

/-- The set `I_A` of interior row positions. -/
def rowSet (D : BetaDiagram (n + 1)) : Finset ℕ := Finset.univ.image (rowPos D)

end Diagram

section Coframe

variable {n : ℕ} [Field L]

/-- The native coefficients `(G_s)_{s ∈ S_A} = -T⁻¹ (H_i)_{i ∈ I_A}`, indexed by the columns. -/
noncomputable def coframeVecOf (h : ℕ → L) (D : BetaDiagram (n + 1)) : Fin n → L :=
  -((properMatrixOf h D)⁻¹ *ᵥ topVecOf h D)

/-- The complete right coframe `G(z) = 1 + ∑_{s ∈ S_A} G_s z^s`
(`sc:coframe-definition`). -/
noncomputable def coframeOf (h : ℕ → L) (D : BetaDiagram (n + 1)) : L[X] :=
  1 + ∑ j : Fin n, C (coframeVecOf h D j) * X ^ colPos D j

/-- The letter series `H = ϑ + ∑ H_i z^i`. -/
noncomputable def seriesOf (h : ℕ → L) : PowerSeries L := PowerSeries.mk h

/-- The numerator `P = [HG]_{<M}`. -/
noncomputable def numeratorOf (h : ℕ → L) (D : BetaDiagram (n + 1)) : L[X] :=
  PowerSeries.trunc (span D) (seriesOf h * (coframeOf h D : PowerSeries L))

/-- The degree-`M` coefficient `[HG]_M` of the product, the monic top quotient. -/
noncomputable def topQuotientOf (h : ℕ → L) (D : BetaDiagram (n + 1)) : L :=
  PowerSeries.coeff (span D) (seriesOf h * (coframeOf h D : PowerSeries L))

end Coframe

/-! ### The generic letters -/

/-- The coherent ring `ℚ[ϑ, H₁, H₂, …]`; the variable `0` is `ϑ = H₀`. -/
abbrev CohRing : Type := MvPolynomial ℕ ℚ

/-- The full raw field of rational functions in the coherent letters. -/
abbrev CohField : Type := FractionRing CohRing

/-- The generic letters as elements of the raw field. -/
noncomputable def cohLetters : ℕ → CohField :=
  fun k => algebraMap CohRing CohField (MvPolynomial.X k)

/-- The coherent Jacobi–Trudi polynomial `s_A` over `ℚ[ϑ, H₁, …]`. -/
noncomputable def cohSchur {n : ℕ} (D : BetaDiagram n) : CohRing := schurOf MvPolynomial.X D

/-- The coherent signed proper corner. -/
noncomputable def cohCorner {n : ℕ} (D : BetaDiagram (n + 1)) : CohRing :=
  cornerOf MvPolynomial.X D

section Generic

variable {n : ℕ}

/-- The complete right coframe over the raw field. -/
noncomputable def coframe (D : BetaDiagram (n + 1)) : CohField[X] := coframeOf cohLetters D

/-- The native coefficients of the complete right coframe, indexed by the columns. -/
noncomputable def coframeVec (D : BetaDiagram (n + 1)) : Fin n → CohField :=
  coframeVecOf cohLetters D

/-- The numerator `P = [HG]_{<M}`. -/
noncomputable def numerator (D : BetaDiagram (n + 1)) : CohField[X] := numeratorOf cohLetters D

/-- The letter series `H` over the raw field. -/
noncomputable def letterSeries : PowerSeries CohField := seriesOf cohLetters

/-- The top quotient `[HG]_M`. -/
noncomputable def topQuotient (D : BetaDiagram (n + 1)) : CohField := topQuotientOf cohLetters D

/-- The defect `D = 𝒯_{G,C}(H)` of two diagrams of the same span `M = span D`. -/
noncomputable def defect {m : ℕ} (D : BetaDiagram (n + 1)) (E : BetaDiagram (m + 1)) :
    CohField[X] :=
  clippedOp (span D) (coframe D) (coframe E) letterSeries

/-- The positions `0 < i < M` outside `I_A`: the available numerator coefficients. -/
abbrev FreeRows (D : BetaDiagram (n + 1)) : Type :=
  {i : ℕ // 0 < i ∧ i < span D ∧ i ∉ rowSet D}

/-- The index set of the atlas coordinates: `ϑ`, the native coefficients, the available
numerator coefficients. -/
abbrev AtlasIdx (D : BetaDiagram (n + 1)) : Type := Option (Fin n ⊕ FreeRows D)

/-- The atlas coordinates of `sc:atlas`. -/
noncomputable def atlasCoords (D : BetaDiagram (n + 1)) : AtlasIdx D → CohField
  | none => cohLetters 0
  | some (Sum.inl j) => coframeVec D j
  | some (Sum.inr i) => (numerator D).coeff i.1

end Generic

end SkewCoframeRigidity.Coframe
