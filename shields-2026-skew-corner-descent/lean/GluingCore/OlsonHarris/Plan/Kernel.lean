-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/Kernel.lean
import GluingCore.OlsonHarris.Plan.Defs
import GluingCore.OlsonHarris.Plan.Kernel.Main

/-!
# The shape algebra, the two actions, and the kernel of `schur`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.1–§5.2 (`OlsonHarris2024HopfApplications`), in
particular Thm. 5.2.2: the kernel of `schur : S → Sym` is spanned by the elements
`f ⇀ h - h ↼ f`.

It uses the Murnaghan–Nakayama results of `Plan.MurnaghanNakayama`: `pDeriv_cellSchur_left`,
`pDeriv_cellSchur_right`, `pPoly_mul_cellSchur_ferrers` and `exists_pProd_expansion`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

/-- Removing a ribbon removable on the left from a skew diagram leaves a skew diagram
(the complement of a downset of a convex set is convex). -/
theorem isSkew_sdiff_leftRibbon {X Y : Diagram} {m : ℕ} (hX : IsSkew X)
    (hY : Y ∈ leftRibbons X m) : IsSkew (X \ Y) :=
  KernelAux.isSkew_sdiff_of_mem_leftRibbons hX hY

/-- Removing a ribbon removable on the right from a skew diagram leaves a skew diagram. -/
theorem isSkew_sdiff_rightRibbon {X Y : Diagram} {m : ℕ} (hX : IsSkew X)
    (hY : Y ∈ rightRibbons X m) : IsSkew (X \ Y) :=
  KernelAux.isSkew_sdiff_of_mem_rightRibbons hX hY

/-- **The left and right removals commute** (the left and right actions of `Sym` on `S` commute,
thesis §5.2: they are induced by one bicomodule structure).  Combinatorially: a ribbon of size `m`
that is a downset of `X` and a ribbon of size `n` that is an upset of `X \ Y` (with the
converse) are the same pairs `(Y, Z)`, with the same sign. -/
theorem leftOp_rightOp_comm {X : Diagram} (_hX : IsSkew X) (m n : ℕ) :
    leftOp m (rightOp n (shape X)) = rightOp n (leftOp m (shape X)) :=
  KernelAux.leftOp_rightOp_comm_shape m n

/-- **Thesis Thm. 5.2.2.**  An element of the shape space supported on skew diagrams that has
Schur function zero is a combination of translation relations `[X] = [X + v]` and of the
relations `p_ν ⇀ [Z] = [Z] ↼ p_ν`.

The route: (1) the Schur functions of the Ferrers shapes are linearly independent
(`KernelAux.linearIndependent_ferrersSchur`); (2) every skew diagram is a translate of some
`λ / μ`; (3) with `s_μ = Σ a_ν p_ν` (the `p_ν` span `Λ`), `Σ a_ν (↼ p_ν)[λ] = [λ / μ]`
(iterated Murnaghan–Nakayama in multiplication form and independence), while
`Σ a_ν (p_ν ⇀)[λ]` is a combination of Ferrers shapes; (4) `schur` kills the relations
(`pDeriv_cellSchur_left`, `pDeriv_cellSchur_right`).  The orthonormality of Schur functions and the
Hall inner product are not used. -/
theorem kernel_schur {h : ShapeSpace} (hh : IsSkewSupported h) (h0 : shapeSchur h = 0) :
    h ∈ shapeKernelSpan :=
  KernelAux.kernel_schur_aux hh h0

end Plan

end GluingCore
