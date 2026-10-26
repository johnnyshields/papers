/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueProtectedTop
import SkewCornerDescent.Matrix.EndpointVisibleSupport

/-!
# Original block grouping from visible protected endpoint coefficients

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Visible
positions are matched by their nonzero full coefficients, then the genuine
protected generator identifies each position's original block top. Coefficients
may depend on every earlier original block. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Equal visible profiles match both original endpoint distances and protected
block tops. Nonvanishing and top recognition are produced in the actual residue
field, not assumed of opaque profile coefficients. -/
theorem protected_profile_visible_match {ι κ : Type*} [Fintype ι] [Fintype κ]
    (left : ι → ℤ) (right : κ → ℤ)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hleftpos : ∀ i, 0 < left i) (hrightpos : ∀ j, 0 < right j)
    (J : ι → ℕ+) (K : κ → ℕ+) (hJ : ∀ i, c.top < J i) (hK : ∀ j, c.top < K j)
    (a R : ι → OtherField c.top) (b T : κ → OtherField c.top)
    (ha : ∀ i, a i ∈ residueLowerField c.top (J i)) (ha0 : ∀ i, a i ≠ 0)
    (hR : ∀ i, R i ∈ residueLowerField c.top (J i))
    (hb : ∀ j, b j ∈ residueLowerField c.top (K j)) (hb0 : ∀ j, b j ≠ 0)
    (hT : ∀ j, T j ∈ residueLowerField c.top (K j))
    (visible : ℤ → Prop)
    (hcoeff : ∀ z, 0 ≤ z → visible z →
      (endpointProfile left (fun i =>
        residueGenerator c.top ⟨J i, ne_of_gt (hJ i)⟩ * a i + R i)).coeff z =
      (endpointProfile right (fun j =>
        residueGenerator c.top ⟨K j, ne_of_gt (hK j)⟩ * b j + T j)).coeff z)
    (i : ι) (hi : visible (left i)) :
    ∃ j, right j = left i ∧ K j = J i := by
  classical
  let v := fun i => residueGenerator c.top ⟨J i, ne_of_gt (hJ i)⟩ * a i + R i
  let w := fun j => residueGenerator c.top ⟨K j, ne_of_gt (hK j)⟩ * b j + T j
  have hv (i) : v i ≠ 0 := c.residue_protected_affine_ne_zero (J i) (hJ i)
    (a i) (R i) (ha i) (ha0 i) (hR i)
  have hw (j) : w j ≠ 0 := c.residue_protected_affine_ne_zero (K j) (hK j)
    (b j) (T j) (hb j) (hb0 j) (hT j)
  have hs := endpointProfile_visible_support_eq left right hleft hright v w hv hw
    hleftpos hrightpos visible hcoeff
  have hmem : left i ∈ (Finset.univ.filter fun j => visible (left j)).image left :=
    Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  rw [hs] at hmem
  obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hmem
  have he := hcoeff (left i) (hleftpos i).le hi
  change (endpointProfile left v).coeff (left i) = (endpointProfile right w).coeff (left i) at he
  rw [endpointProfile_coeff_at_index left hleft v i (hleftpos i), ← hji,
    endpointProfile_coeff_at_index right hright w j (hrightpos j)] at he
  have hvalue : v i = w j := neg_inj.mp he
  have htop := c.residue_protected_affine_top_unique (J i) (K j) (hJ i) (hK j)
    (a i) (R i) (b j) (T j) (ha i) (ha0 i) (hR i) (hb j) (hb0 j) (hT j) hvalue
  exact ⟨j, hji, htop.symm⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
