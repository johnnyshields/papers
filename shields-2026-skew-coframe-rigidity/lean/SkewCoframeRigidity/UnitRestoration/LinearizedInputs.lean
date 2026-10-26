/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadData
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadIdentity
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadSelect
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadGap
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadObs
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadDeriv
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadUnique
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadField
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadMain
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadGapEq

/-!
# The head step of the linearized fixed-cap induction

The part of the proof of `sc:linearized-cap` in `shields-2026-skew-coframe-rigidity.tex` that
runs through the first variation `Q` of the complete coframe: the bordered solve
`sc:linearized-coframe`, the observations `sc:linearized-observations`, the zero range
`sc:linearized-zero-range`, the prefix compensation `sc:linearized-prefix`, and the two
next-head cases.  What the induction consumes from it is one dichotomy for the highest
restored vacancy `b` carrying a nonzero weight, every higher weight being zero:

* the gap case, `sc:gap-coface`, where `ρ_b` multiplies a Schur function of an actual
  connected diagram, and
* the strict-block case, `sc:strict-block-variation`, where `b` lies in a strict block `E`
  with cap `K_E`, and the differentiated top equation reads `s_E ṡ_N = s_N ṡ_E` for
  `N = K_E ◁ E`, with the weights restricted to `E`.

The induction in `Linearized.lean` needs nothing else from `Q`.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence MvPolynomial

/-- **The gap equation.**  For the largest weighted vacancy `b` lying in a gap, the `h_b`-derivative
of the top equation `[HQ]_m = 0` gives `ρ_b · (h_{X_0-b} det P - H_{X_0,cols P} adj(P) H_{rows P,b}) = 0`
(`sc:gap-coface`, times `det P`).  This is the first of the two derivative statements left to
prove in the head step; the interface is that of `head_select` (`HeadSelect.lean`) and
`gap_disjunct` (`HeadGap.lean`). -/
theorem gap_equation {k n : ℕ} (K : BetaDiagram (k + 1)) (B : BetaDiagram (n + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected)
    (hKz : ZeroFree K) (hBz : ZeroFree B) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (h1 : dotW B ρ = 0)
    (h2 : dotW (splice K B hK hB) ρ = 0) (p : ℕ) (hp : p ≤ n) (b : ℤ) (hρb : ρ b ≠ 0)
    (hmax : ∀ x ∈ ρ.support, x ≤ b) (hrow : ∀ i : Fin (n + 1), i.val ≤ p → b < B.row i)
    (hrow' : ∀ i : Fin (n + 1), p < i.val → B.row i < b)
    (hcol : ∀ j : Fin (n + 1), j.val < p → b < B.col j)
    (hcol' : ∀ j : Fin (n + 1), p ≤ j.val → B.col j < b)
    (hcut : ∀ hp : p + 1 ≤ n, PrefixCut B p hp) :
    C (ρ b) * gapNumerator B hp b = 0 :=
  gap_equation_proof K B hK hB hKc hBc hKz hBz ρ hρ h1 h2 p hp b hρb hmax hrow hrow' hcol hcol' hcut

/-- **The surviving derivative.**  For the first block with nonzero restricted weights, the
`h_t`-derivative of the top equation `[HQ]_m = 0` gives `∑ ρ_x · survive(x) = 0`.  This is the
second derivative statement left to prove in the head step. -/
theorem block_survive {k n : ℕ} (K : BetaDiagram (k + 1)) (B : BetaDiagram (n + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected)
    (hKz : ZeroFree K) (hBz : ZeroFree B) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (h1 : dotW B ρ = 0)
    (h2 : dotW (splice K B hK hB) ρ = 0) (p e : ℕ) (hpe : p + e + 1 ≤ n)
    (hcut : PrefixCut B p (by omega)) (hin : BlockInside B p e hpe)
    (hq : ∀ hq : p + e + 1 < n, B.row ⟨p + e + 2, by omega⟩ < B.col ⟨p + e, by omega⟩)
    (hρt : ∀ x ∈ ρ.support, x < blockHead B hpe) :
    (ρ.sum fun x r => C r * survive B hpe x) = 0 :=
  block_survive_proof K B hK hB hKc hBc ρ hρ h1 h2 p e hpe hcut hq hρt

/-- The head dichotomy of `sc:linearized-cap`: the next head, for nonzero weights on genuine
vacancies with both whole variations zero, is either a gap (an equation `ρ_b · s_G = 0` with `G`
an actual diagram) or a strict block (a closed prefix and the block `E` with every weight below
its head row, the restricted weights not all zero, and `∑ ρ_x · survive(x) = 0`).  The selection
is `head_select`; the two equations are `gap_equation` and `block_survive`. -/
theorem linearized_head_step {k b : ℕ} (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected)
    (hKz : ZeroFree K) (hBz : ZeroFree B) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (hne : ρ ≠ 0)
    (h1 : dotW B ρ = 0) (h2 : dotW (splice K B hK hB) ρ = 0) :
    (∃ (g : ℕ) (G : BetaDiagram (g + 1)) (x : ℤ),
        ρ x ≠ 0 ∧ C (ρ x) * G.schur = 0) ∨
    (∃ (p e : ℕ) (hpe : p + e + 1 ≤ b) (hcut : PrefixCut B p (by omega))
        (hin : BlockInside B p e hpe),
        restrictBlock ρ (blockLeast B hpe) (blockHead B hpe) ≠ 0 ∧
        (∀ x ∈ ρ.support, x < blockHead B hpe) ∧
        (ρ.sum fun x r => C r * survive B hpe x) = 0) := by
  rcases head_select B hB hBc hBz ρ hρ hne with
    ⟨p, β, hp, hρβ, hmax, hrow, hrow', hcol, hcol', hcut⟩ | ⟨p, e, hpe, hcut, hin, hne', hρt, hq⟩
  · left
    have heq := gap_equation K B hK hB hKc hBc hKz hBz ρ hρ h1 h2 p hp β hρβ hmax hrow hrow' hcol
      hcol' hcut
    exact gap_disjunct (B := B) (hp := hp) β ρ hρβ hcol (hrow ⟨p, by omega⟩ le_rfl) heq
  · right
    exact ⟨p, e, hpe, hcut, hin, hne', hρt,
      block_survive K B hK hB hKc hBc hKz hBz ρ hρ h1 h2 p e hpe hcut hin hq hρt⟩

end SkewCoframeRigidity.UnitRestoration
