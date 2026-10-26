/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TransposeResidueMatch
import SkewCornerDescent.Matrix.RegularResidue

/-!
# Whole-diagram transpose on genuine selected-prime local rings

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The exact prime-complement denominator sets construct an isomorphism of the
actual local rings. Both the full original-field embedding and the produced
residue-field transport commute with it. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)
variable (d : SelectedCoordinate (transpose D) (isConnectedSkew_transpose hD))

/-- The actual selected-prime complements transport exactly, including every
regular denominator rather than only those in a lower-generator band. -/
theorem selected_primeCompl_transpose :
    c.selectedIdeal.primeCompl.map schurInvolutionEquiv.toRingEquiv.toMonoidHom =
      d.selectedIdeal.primeCompl := by
  ext f
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, c.mem_selectedIdeal, d.mem_selectedIdeal]
  change (∃ g, ¬ cellSchur D hD.1 ∣ g ∧ schurInvolution g = f) ↔
    ¬ cellSchur (transpose D) (isSkew_transpose hD.1) ∣ f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (selected_prime_regularity_transpose hD g).mpr hg
  · intro hf
    refine ⟨schurInvolution f, ?_, schurInvolution_involutive f⟩
    apply (selected_prime_regularity_transpose hD (schurInvolution f)).mp
    rwa [schurInvolution_involutive f]

/-- The complete actual selected-prime local rings are isomorphic under
whole-diagram transpose. -/
noncomputable def regularTransposeEquiv : c.RegularRing ≃+* d.RegularRing :=
  IsLocalization.ringEquivOfRingEquiv c.RegularRing d.RegularRing
    schurInvolutionEquiv.toRingEquiv (c.selected_primeCompl_transpose d)

/-- The local-ring isomorphism transports the actual original polynomial embedding. -/
theorem regularTransposeEquiv_polynomial (f : Lambda) :
    c.regularTransposeEquiv d (algebraMap Lambda c.RegularRing f) =
      algebraMap Lambda d.RegularRing (schurInvolution f) := by
  exact IsLocalization.ringEquivOfRingEquiv_eq (c.selected_primeCompl_transpose d) f

/-- The genuine local residue commutes with the produced full residue-field map. -/
theorem regularTransposeEquiv_residue (f : c.RegularRing) :
    d.regularResidue (c.regularTransposeEquiv d f) =
      c.residueTranspose d (c.regularResidue f) := by
  have h : d.regularResidue.comp (c.regularTransposeEquiv d).toRingHom =
      (c.residueTranspose d).comp c.regularResidue := by
    apply IsLocalization.ringHom_ext c.selectedIdeal.primeCompl
    apply RingHom.ext
    intro g
    simp only [RingHom.comp_apply]
    change d.regularResidue (c.regularTransposeEquiv d
      (algebraMap Lambda c.RegularRing g)) =
      c.residueTranspose d (c.regularResidue (algebraMap Lambda c.RegularRing g))
    rw [c.regularTransposeEquiv_polynomial d, d.regularResidue_polynomial,
      c.regularResidue_polynomial, c.residueTranspose_residueMap d]
  exact RingHom.congr_fun h f

/-- The same local-ring isomorphism commutes with the complete original
rational field, so no alternate fractions are substituted for actual responses. -/
theorem regularTransposeEquiv_originalField (f : c.RegularRing) :
    d.regularEmbedding (c.regularTransposeEquiv d f) =
      originalSchurFieldEquiv (c.regularEmbedding f) := by
  have h : d.regularEmbedding.comp (c.regularTransposeEquiv d).toRingHom =
      originalSchurFieldEquiv.toRingHom.comp c.regularEmbedding := by
    apply IsLocalization.ringHom_ext c.selectedIdeal.primeCompl
    apply RingHom.ext
    intro g
    simp only [RingHom.comp_apply]
    change d.regularEmbedding (c.regularTransposeEquiv d
      (algebraMap Lambda c.RegularRing g)) =
      originalSchurFieldEquiv (c.regularEmbedding (algebraMap Lambda c.RegularRing g))
    rw [c.regularTransposeEquiv_polynomial d, d.regularEmbedding_polynomial,
      c.regularEmbedding_polynomial, originalSchurFieldEquiv_originalMap]
  exact RingHom.congr_fun h f

end SkewCornerDescent.Matrix.SelectedCoordinate
