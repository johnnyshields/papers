/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.Linearized
import SkewCoframeRigidity.FixedCap.CellExample
import SkewCoframeRigidity.FixedCap.Reduction
import SkewCoframeRigidity.Unshifted.Components

/-!
# The two cell-splice deductions of `sc:splice-nonzero`

Formalizes the two places where the proof of `sc:splice-nonzero` in
`shields-2026-skew-coframe-rigidity.tex` calls the rigidity theorems with the one-cell cap:

* `cell_splice_ne_of_not_symmetric`: if the zero-free core `B` is not its own half-turn, the
  leading cell-splice grade cannot vanish, because it would give equal functions of the cell
  extensions of `B` and `B*`, and `B` and `B*` already have equal functions; fixed-cap rigidity
  for the cell cap then gives `B = B*`.
* `cell_splice_dotW_ne_zero`: if the core is its own half-turn, the next grade involves the
  restoration weights; with `ṡ_B = 0`, vanishing of the cell-splice grade would give
  `ṡ_{CELL ◁ B} = 0`, and `linearized_cap` forces every weight to vanish.

Both are stated for the diagram at its own normalization.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity.FixedCap

theorem cellCap_zeroFree : ZeroFree cellCap := fun i j => by
  simp [cellCap]

/-- **Non-self-rotating core** (`sc:splice-nonzero`, first case).  If the cell extensions of a
connected zero-free core `B` and of its half-turn have the same function, and the cell cap
separates coequal diagrams, then `B` is its own half-turn. -/
theorem cell_splice_ne_of_not_symmetric (hcap : CapVanishing cellCap) {b : ℕ}
    (B : BetaDiagram (b + 1)) (hB : IsNorm B) (hBc : B.Connected)
    (hBr : IsNorm B.rotation)
    (h : (splice cellCap B cellCap_isNorm hB).schur =
      (splice cellCap B.rotation cellCap_isNorm hBr).schur) : B.rotation = B := by
  have h1 : B.schur = B.rotation.schur := (BetaDiagram.schur_rotation B).symm
  obtain ⟨-, hheq⟩ := fixed_cap_rigidity cellCap cellCap_isNorm cellCap_connected hcap B B.rotation
    hB hBr hBc hBc.rotation h1 h
  exact (eq_of_heq hheq).symm

/-- **Self-rotating core** (`sc:splice-nonzero`, second case).  For a connected zero-free core
with `ṡ_B = 0`, nonzero constant weights on its genuine vacancies cannot also annihilate the
cell extension: `ṡ_{CELL ◁ B} ≠ 0`. -/
theorem cell_splice_dotW_ne_zero {b : ℕ} (B : BetaDiagram (b + 1)) (hB : IsNorm B)
    (hBc : B.Connected) (hBz : ZeroFree B) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (hne : ρ ≠ 0) (h1 : dotW B ρ = 0) :
    dotW (splice cellCap B cellCap_isNorm hB) ρ ≠ 0 := fun h2 =>
  hne (linearized_cap cellCap B cellCap_isNorm hB cellCap_connected hBc cellCap_zeroFree hBz ρ hρ
    h1 h2)

end SkewCoframeRigidity.UnitRestoration
