/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.UnboundedSplitting
import SkewClassInflation.SaturationClassCounts

/-!
# Exact class counts in the worked examples

The class counts asserted in `sec:examples` of `shields-2026-skew-class-inflation.tex`.
The outer ribbon class of `(1, 2)` is exactly `{(1, 2), (2, 1)}`.  At threshold two the
four-member class of `G_{(1,2)}` survives the first inflation and its images split into two
rotation classes at the second.  For `e = 2` the eight constructed members become exactly
four rotation pairs, and the whole class and image are counted exactly.  Sorry-free.
-/

namespace SkewClassInflation

/-- The outer ribbon class of `(1, 2)` has exactly the two orientations of the word. -/
theorem outer_one_two_class_card : (ribbonClass outerOneTwo).ncard = 2 := by
  have h := binaryRibbon_class_card 1
  have he : outerOneTwo = binaryRibbon 1 (fun _ => false) :=
    composition_ext_of_blocks _ _ (by decide)
  rw [he]
  simpa using h

/-- The four-member class of `G_{(1, 2)}` at threshold two and no inflation. -/
theorem threshold_two_class_card :
    (ConnectedProfile.schurClass (thresholdTwo.diagram outerOneTwo (by decide))).ncard = 4 := by
  rw [thresholdTwo.thin_full_class_card, outer_one_two_class_card]

/-- The class survives the first positive inflation with all four members. -/
theorem threshold_two_class_card_one :
    (ConnectedProfile.schurClass
      (ConnectedProfile.inflate 1 (thresholdTwo.diagram outerOneTwo (by decide)))).ncard = 4 := by
  rw [thresholdTwo.subthreshold_full_class outerOneTwo (by decide) 1 (by decide),
    Set.ncard_image_of_injective _ (ConnectedProfile.inflate_injective 1),
    thresholdTwo.thin_full_class_card, outer_one_two_class_card]

/-- At the second inflation every class collapses to a rotation pair. -/
theorem threshold_two_class_card_two :
    (ConnectedProfile.schurClass
      (ConnectedProfile.inflate 2 (thresholdTwo.diagram outerOneTwo (by decide)))).ncard = 2 :=
  thresholdTwo.superthreshold_class_card outerOneTwo (by decide) 2 (by decide)

/-- For `e = 2` the source class has exactly eight members. -/
theorem splitting_two_source_card : (splittingSource 2).schurClass.ncard = 8 := by
  simpa using splittingSource_class_card 2

/-- For `e = 2` the first-inflation image has exactly eight members. -/
theorem splitting_two_image_card :
    (ConnectedProfile.inflate 1 '' (splittingSource 2).schurClass).ncard = 8 := by
  simpa using splittingSource_image_card 2

/-- For `e = 2` the eight image members form exactly four rotation classes. -/
theorem splitting_two_class_count :
    {C : Set ConnectedProfile | ∃ H ∈ ConnectedProfile.inflate 1 '' (splittingSource 2).schurClass,
      C = H.schurClass}.ncard = 4 := by
  simpa using splittingSource_image_class_count 2

/-- The asymmetric inner `(4, 5; 1)` at `d = 2`. -/
def asymmetricInner : SaturationInner where
  k := 1
  k_pos := by decide
  r := ![4, 5]
  c := 1
  d := 2
  c_lt_d := by decide
  first_bound := by decide
  last_bound := by decide
  interior_bound i hi hl := by fin_cases i <;> simp_all

/-- The symmetric inner `(4, 4; 1)` at `d = 2`. -/
def symmetricInner : SaturationInner where
  k := 1
  k_pos := by decide
  r := ![4, 4]
  c := 1
  d := 2
  c_lt_d := by decide
  first_bound := by decide
  last_bound := by decide
  interior_bound i hi hl := by fin_cases i <;> simp_all

/-- The asymmetric inner gives four class members for the outer ribbon `(1, 2)`. -/
theorem asymmetric_inner_class_card :
    (ConnectedProfile.schurClass (asymmetricInner.diagram outerOneTwo (by decide))).ncard = 4 := by
  rw [asymmetricInner.full_class_card outerOneTwo (by decide), outer_one_two_class_card]
  have hne : asymmetricInner.profile.rotate ≠ asymmetricInner.profile := by
    rw [Ne, asymmetricInner.inner_symmetric_iff]
    decide
  rw [if_neg hne]

/-- The symmetric inner gives two class members for the same outer ribbon. -/
theorem symmetric_inner_class_card :
    (ConnectedProfile.schurClass (symmetricInner.diagram outerOneTwo (by decide))).ncard = 2 := by
  rw [symmetricInner.full_class_card outerOneTwo (by decide), outer_one_two_class_card]
  have hs : symmetricInner.profile.rotate = symmetricInner.profile := by
    rw [symmetricInner.inner_symmetric_iff]
    decide
  rw [if_pos hs]

end SkewClassInflation
