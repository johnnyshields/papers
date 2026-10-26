/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BinaryRibbonCensus
import SkewClassInflation.SharpExamples

/-!
# Arbitrarily large classes split into rotation pairs at the first inflation

Formalizes `cor:unbounded-class-splitting` of
`shields-2026-skew-class-inflation.tex`.  The exact census of the iterated weight-three
family gives source and image classes of exactly \(2^{e+1}\) members and exactly \(2^e\)
rotation classes in the image.  The full thin-class theorem and arbitrary-mate boundary
theorem apply to every member of the source class, not only the binary subfamily.
Sorry-free.
-/

namespace SkewClassInflation

/-- Every member of a thin full class has a two-element rotation class above the threshold. -/
theorem ThinParameters.all_mates_superthreshold_class (B : ThinParameters)
    {M : ℕ} (α : Composition M) (hM : 0 < M) (t : ℕ) (ht : B.boundary.p ≤ t)
    (H : ConnectedProfile) (hH : H ∈ (B.diagram α hM).schurClass) :
    (ConnectedProfile.inflate t H).schurClass =
        {ConnectedProfile.inflate t H, (ConnectedProfile.inflate t H).rotate} ∧
      (ConnectedProfile.inflate t H).schurClass.ncard = 2 := by
  rw [B.thin_full_class α hM] at hH
  rcases hH with ⟨β, _, rfl⟩ | ⟨β, _, rfl⟩
  · exact ⟨B.superthreshold_full_class β hM t ht, B.superthreshold_class_card β hM t ht⟩
  · rw [← ConnectedProfile.inflate_rotate]
    constructor
    · rw [ConnectedProfile.schurClass_rotate, B.superthreshold_full_class β hM t ht,
        ConnectedProfile.rotate_rotate]
      exact Set.pair_comm _ _
    · rw [ConnectedProfile.schurClass_rotate]
      exact B.superthreshold_class_card β hM t ht

/-- The actual connected source assigned to the binary ribbon family at threshold one. -/
def splittingSource (e : ℕ) : ConnectedProfile :=
  thresholdOne.diagram (binaryRibbon e (fun _ => false)) (pow_pos (by decide) _)

/-- The source class is finite on the unrestricted connected-profile domain. -/
theorem splittingSource_class_finite (e : ℕ) : (splittingSource e).schurClass.Finite :=
  thresholdOne.thin_full_class_finite _ (pow_pos (by decide) _)

/-- Both orientations of every binary ribbon choice give the exponential source lower bound. -/
theorem splittingSource_class_lower_bound (e : ℕ) :
    2 ^ (e + 1) ≤ (splittingSource e).schurClass.ncard := by
  change 2 ^ (e + 1) ≤
    (thresholdOne.diagram (binaryRibbon e (fun _ => false)) _).schurClass.ncard
  rw [thresholdOne.thin_full_class_card, pow_succ]
  have hh := binaryRibbon_class_lower_bound e
  omega

/-- The entire actual image has the same cardinality, since inflation is globally injective. -/
theorem splittingSource_image_lower_bound (e : ℕ) :
    2 ^ (e + 1) ≤ (ConnectedProfile.inflate 1 '' (splittingSource e).schurClass).ncard := by
  rw [Set.ncard_image_of_injective _ (ConnectedProfile.inflate_injective 1)]
  exact splittingSource_class_lower_bound e

/-- Every actual first-inflation image has exactly its two literal rotations as all its mates. -/
theorem splittingSource_image_classes (e : ℕ) (H : ConnectedProfile)
    (hH : H ∈ ConnectedProfile.inflate 1 '' (splittingSource e).schurClass) :
    H.schurClass = {H, H.rotate} ∧ H.schurClass.ncard = 2 := by
  obtain ⟨E, hE, rfl⟩ := hH
  exact thresholdOne.all_mates_superthreshold_class _ (pow_pos (by decide) _) 1
    (by decide) E hE

/-- These are whole rotation classes inside the image, not only pairs in the ambient space. -/
theorem splittingSource_image_closed (e : ℕ) (H : ConnectedProfile)
    (hH : H ∈ ConnectedProfile.inflate 1 '' (splittingSource e).schurClass) :
    H.schurClass ⊆ ConnectedProfile.inflate 1 '' (splittingSource e).schurClass := by
  have hp := (splittingSource_image_classes e H hH).1
  rw [hp]
  have hr : H.rotate ∈ ConnectedProfile.inflate 1 '' (splittingSource e).schurClass := by
    obtain ⟨E, hE, rfl⟩ := hH
    refine ⟨E.rotate, ?_, (ConnectedProfile.inflate_rotate 1 E).symm⟩
    change E.rotate.schur = (splittingSource e).schur
    rw [ConnectedProfile.schur_rotate]
    exact hE
  exact Set.insert_subset hH (Set.singleton_subset_iff.mpr hr)

/-- The source class has exactly \(2^{e+1}\) members. -/
theorem splittingSource_class_card (e : ℕ) :
    (splittingSource e).schurClass.ncard = 2 ^ (e + 1) := by
  change (thresholdOne.diagram (binaryRibbon e (fun _ => false)) _).schurClass.ncard = _
  rw [thresholdOne.thin_full_class_card, binaryRibbon_class_card, pow_succ]
  ring

/-- The first-inflation image has exactly \(2^{e+1}\) members. -/
theorem splittingSource_image_card (e : ℕ) :
    (ConnectedProfile.inflate 1 '' (splittingSource e).schurClass).ncard = 2 ^ (e + 1) := by
  rw [Set.ncard_image_of_injective _ (ConnectedProfile.inflate_injective 1),
    splittingSource_class_card]

/-- The image splits into exactly \(2^e\) distinct rotation classes. -/
theorem splittingSource_image_class_count (e : ℕ) :
    {C : Set ConnectedProfile | ∃ H ∈ ConnectedProfile.inflate 1 '' (splittingSource e).schurClass,
      C = H.schurClass}.ncard = 2 ^ e := by
  have hM : 0 < 3 ^ e := pow_pos (by decide) e
  let f : Composition (3 ^ e) → Set ConnectedProfile := fun β =>
    (ConnectedProfile.inflate 1 (thresholdOne.diagram β hM)).schurClass
  have hset : {C : Set ConnectedProfile | ∃ H ∈ ConnectedProfile.inflate 1 ''
      (splittingSource e).schurClass, C = H.schurClass} =
      f '' ribbonClass (binaryRibbon e (fun _ => false)) := by
    ext C
    constructor
    · rintro ⟨H, ⟨E, hE, rfl⟩, rfl⟩
      have hE' : E ∈ (thresholdOne.diagram (binaryRibbon e (fun _ => false)) hM).schurClass := hE
      rw [thresholdOne.thin_full_class _ hM] at hE'
      rcases hE' with ⟨β, hβ, rfl⟩ | ⟨β, hβ, rfl⟩
      · exact ⟨β, hβ, rfl⟩
      · refine ⟨β, hβ, ?_⟩
        change _ = (ConnectedProfile.inflate 1 (thresholdOne.diagram β hM).rotate).schurClass
        rw [← ConnectedProfile.inflate_rotate, ConnectedProfile.schurClass_rotate]
    · rintro ⟨β, hβ, rfl⟩
      refine ⟨ConnectedProfile.inflate 1 (thresholdOne.diagram β hM), ⟨_, ?_, rfl⟩, rfl⟩
      change _ ∈ (thresholdOne.diagram (binaryRibbon e (fun _ => false)) hM).schurClass
      rw [thresholdOne.thin_full_class _ hM]
      exact Or.inl ⟨β, hβ, rfl⟩
  have hinj : Set.InjOn f (ribbonClass (binaryRibbon e (fun _ => false))) := by
    intro β hβ γ hγ hf
    have hmem : ConnectedProfile.inflate 1 (thresholdOne.diagram β hM) ∈ f γ := by
      rw [← hf]
      rfl
    change _ ∈ (ConnectedProfile.inflate 1 (thresholdOne.diagram γ hM)).schurClass at hmem
    rw [thresholdOne.superthreshold_full_class γ hM 1 (by decide)] at hmem
    rcases hmem with h | h
    · exact thresholdOne.diagram_injective hM (ConnectedProfile.inflate_injective 1 h)
    · rw [ConnectedProfile.inflate_rotate] at h
      have hd := ConnectedProfile.inflate_injective 1 h
      exact (Set.disjoint_left.mp
        (thresholdOne.thin_orientations_disjoint
          (binaryRibbon e (fun _ => false)) hM) ⟨β, hβ, rfl⟩ ⟨γ, hγ, hd.symm⟩).elim
  rw [hset, hinj.ncard_image, binaryRibbon_class_card]

/-- Arbitrarily large actual connected classes split entirely into two-element rotation classes.

**Differs from the paper's route.** The exact census of the binary family comes from
unconditional factor transport and small-weight reconstruction of the weight-three factors
(`binaryRibbon_census`), not from the full factor-reversal classification. -/
theorem unbounded_class_splitting (N : ℕ) :
    ∃ D : ConnectedProfile, D.schurClass.Finite ∧ N ≤ D.schurClass.ncard ∧
      N ≤ (ConnectedProfile.inflate 1 '' D.schurClass).ncard ∧
      ∀ H ∈ ConnectedProfile.inflate 1 '' D.schurClass,
        H.schurClass = {H, H.rotate} ∧ H.schurClass.ncard = 2 ∧
          H.schurClass ⊆ ConnectedProfile.inflate 1 '' D.schurClass := by
  refine ⟨splittingSource N, splittingSource_class_finite N, ?_, ?_, ?_⟩
  · have hh := splittingSource_class_lower_bound N
    have hn := Nat.lt_two_pow_self (n := N + 1)
    omega
  · have hh := splittingSource_image_lower_bound N
    have hn := Nat.lt_two_pow_self (n := N + 1)
    omega
  · intro H hH
    exact ⟨(splittingSource_image_classes N H hH).1,
      (splittingSource_image_classes N H hH).2, splittingSource_image_closed N H hH⟩

end SkewClassInflation
