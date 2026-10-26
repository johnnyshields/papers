/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalEndpointProfileSupport
import SkewCornerDescent.Matrix.OriginalIntervalUnitEquivalence

/-!
# Paired original component matches assemble literal prefix indices

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Point matches from reconstructed earlier or later components assemble into
a whole original prefix or suffix equivalence. Source injectivity supplies
coherence and bijectivity; no matrix or inverse compatibility is assumed.
The component point matches are the explicit recursive recovery inputs.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

private theorem paired_coordinate_equiv {ν μ : Type*}
    (row col : ν → ℤ) (row' col' : μ → ℤ) (shift : ℤ)
    (hinj : Function.Injective row) (hinj' : Function.Injective row')
    (hf : ∀ i, ∃ j, row' j = row i + shift ∧ col' j = col i + shift)
    (hb : ∀ j, ∃ i, row' j = row i + shift ∧ col' j = col i + shift) :
    ∃ e : ν ≃ μ, ∀ i, row' (e i) = row i + shift ∧ col' (e i) = col i + shift := by
  classical
  let f := fun i => Classical.choose (hf i)
  have hspec (i) : row' (f i) = row i + shift ∧ col' (f i) = col i + shift :=
    Classical.choose_spec (hf i)
  have hfi : Function.Injective f := by
    intro i j he
    apply hinj
    exact add_right_cancel ((hspec i).1.symm.trans ((congrArg row' he).trans (hspec j).1))
  have hfs : Function.Surjective f := by
    intro j
    obtain ⟨i, hi, _⟩ := hb j
    refine ⟨i, hinj' ?_⟩
    exact (hspec i).1.trans hi.symm
  exact ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, hspec⟩

namespace SelectedCoordinate
variable {D : SkewGluing.Diagram} {hD : SkewGluing.IsConnectedSkew D}

/-- Pointwise earlier-component endpoint matches assemble into a whole genuine
prefix equivalence. Original source injectivity supplies coherence and bijectivity. -/
theorem original_interval_prefix_equiv_of_matches {n m : ℕ}
    (P : SkewGluing.Profile n) (Q : SkewGluing.Profile m)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (b' d' : Option (OriginalSelectedBlocks (hD := hD) Q)) (v : OriginalBlocks Q)
    (shift : ℤ)
    (hf : ∀ i : OriginalIntervalUnitPrefix (hD := hD) P b d u,
      ∃ j : OriginalIntervalUnitPrefix (hD := hD) Q b' d' v,
        originalResponseRows Q j.1.1.1 = originalResponseRows P i.1.1.1 + shift ∧
        originalResponseCols Q j.1.1.1 = originalResponseCols P i.1.1.1 + shift)
    (hb : ∀ j : OriginalIntervalUnitPrefix (hD := hD) Q b' d' v,
      ∃ i : OriginalIntervalUnitPrefix (hD := hD) P b d u,
        originalResponseRows Q j.1.1.1 = originalResponseRows P i.1.1.1 + shift ∧
        originalResponseCols Q j.1.1.1 = originalResponseCols P i.1.1.1 + shift) :
    ∃ e : OriginalIntervalUnitPrefix (hD := hD) P b d u ≃
        OriginalIntervalUnitPrefix (hD := hD) Q b' d' v,
      ∀ i, originalResponseRows Q (e i).1.1.1 = originalResponseRows P i.1.1.1 + shift ∧
        originalResponseCols Q (e i).1.1.1 = originalResponseCols P i.1.1.1 + shift := by
  apply paired_coordinate_equiv _ _ _ _ shift ?_ ?_ hf hb
  · intro i j he
    exact Subtype.ext (Subtype.ext (Subtype.ext (original_response_rows_injective P he)))
  · intro i j he
    exact Subtype.ext (Subtype.ext (Subtype.ext (original_response_rows_injective Q he)))

/-- The symmetric later-component matches assemble the complete actual suffix
without any supplied matrix or inverse-entry equivalence. -/
theorem original_interval_suffix_equiv_of_matches {n m : ℕ}
    (P : SkewGluing.Profile n) (Q : SkewGluing.Profile m)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (b' d' : Option (OriginalSelectedBlocks (hD := hD) Q)) (v : OriginalBlocks Q)
    (shift : ℤ)
    (hf : ∀ i : OriginalIntervalUnitSuffix (hD := hD) P b d u,
      ∃ j : OriginalIntervalUnitSuffix (hD := hD) Q b' d' v,
        originalResponseRows Q j.1.1.1 = originalResponseRows P i.1.1.1 + shift ∧
        originalResponseCols Q j.1.1.1 = originalResponseCols P i.1.1.1 + shift)
    (hb : ∀ j : OriginalIntervalUnitSuffix (hD := hD) Q b' d' v,
      ∃ i : OriginalIntervalUnitSuffix (hD := hD) P b d u,
        originalResponseRows Q j.1.1.1 = originalResponseRows P i.1.1.1 + shift ∧
        originalResponseCols Q j.1.1.1 = originalResponseCols P i.1.1.1 + shift) :
    ∃ e : OriginalIntervalUnitSuffix (hD := hD) P b d u ≃
        OriginalIntervalUnitSuffix (hD := hD) Q b' d' v,
      ∀ i, originalResponseRows Q (e i).1.1.1 = originalResponseRows P i.1.1.1 + shift ∧
        originalResponseCols Q (e i).1.1.1 = originalResponseCols P i.1.1.1 + shift := by
  apply paired_coordinate_equiv _ _ _ _ shift ?_ ?_ hf hb
  · intro i j he
    exact Subtype.ext (Subtype.ext (Subtype.ext (original_response_rows_injective P he)))
  · intro i j he
    exact Subtype.ext (Subtype.ext (Subtype.ext (original_response_rows_injective Q he)))

/-- Point matches in both directions determine a complete paired equivalence
of arbitrary retained parts of the actual intervals.  Source row injectivity
supplies coherence, including after a midpoint vertex is excluded. -/
theorem original_interval_kept_equiv_of_matches {n m : ℕ}
    (P : SkewGluing.Profile n) (Q : SkewGluing.Profile m)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (b' d' : Option (OriginalSelectedBlocks (hD := hD) Q))
    (keep : OriginalResponseInterval (hD := hD) P b d → Prop)
    (keep' : OriginalResponseInterval (hD := hD) Q b' d' → Prop) (shift : ℤ)
    (hf : ∀ i : {i // keep i}, ∃ j : {j // keep' j},
      originalResponseRows Q j.1.1.1 = originalResponseRows P i.1.1.1 + shift ∧
        originalResponseCols Q j.1.1.1 = originalResponseCols P i.1.1.1 + shift)
    (hb : ∀ j : {j // keep' j}, ∃ i : {i // keep i},
      originalResponseRows Q j.1.1.1 = originalResponseRows P i.1.1.1 + shift ∧
        originalResponseCols Q j.1.1.1 = originalResponseCols P i.1.1.1 + shift) :
    ∃ e : {i // keep i} ≃ {j // keep' j},
      ∀ i, originalResponseRows Q (e i).1.1.1 = originalResponseRows P i.1.1.1 + shift ∧
        originalResponseCols Q (e i).1.1.1 = originalResponseCols P i.1.1.1 + shift := by
  apply paired_coordinate_equiv _ _ _ _ shift ?_ ?_ hf hb
  · intro i j he
    exact Subtype.ext (Subtype.ext (Subtype.ext (original_response_rows_injective P he)))
  · intro i j he
    exact Subtype.ext (Subtype.ext (Subtype.ext (original_response_rows_injective Q he)))

/-- Complete point matches in both directions determine a paired equivalence
of the full actual original intervals. -/
theorem original_interval_equiv_of_matches {n m : ℕ}
    (P : SkewGluing.Profile n) (Q : SkewGluing.Profile m)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (b' d' : Option (OriginalSelectedBlocks (hD := hD) Q)) (shift : ℤ)
    (hf : ∀ i : OriginalResponseInterval (hD := hD) P b d,
      ∃ j : OriginalResponseInterval (hD := hD) Q b' d',
        originalResponseRows Q j.1.1 = originalResponseRows P i.1.1 + shift ∧
          originalResponseCols Q j.1.1 = originalResponseCols P i.1.1 + shift)
    (hb : ∀ j : OriginalResponseInterval (hD := hD) Q b' d',
      ∃ i : OriginalResponseInterval (hD := hD) P b d,
        originalResponseRows Q j.1.1 = originalResponseRows P i.1.1 + shift ∧
          originalResponseCols Q j.1.1 = originalResponseCols P i.1.1 + shift) :
    ∃ e : OriginalResponseInterval (hD := hD) P b d ≃
        OriginalResponseInterval (hD := hD) Q b' d',
      ∀ i, originalResponseRows Q (e i).1.1 = originalResponseRows P i.1.1 + shift ∧
        originalResponseCols Q (e i).1.1 = originalResponseCols P i.1.1 + shift := by
  apply paired_coordinate_equiv _ _ _ _ shift ?_ ?_ hf hb
  · intro i j he
    exact Subtype.ext (Subtype.ext (original_response_rows_injective P he))
  · intro i j he
    exact Subtype.ext (Subtype.ext (original_response_rows_injective Q he))

end SelectedCoordinate
end SkewCornerDescent.Matrix
